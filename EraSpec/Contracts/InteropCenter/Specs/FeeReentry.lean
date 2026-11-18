import Mathlib.Tactic
import EraSpec.Contracts.InteropCenter.Specs.FeeState

/-!
# Model: `InteropCenter` fee state with nested calls — is the shared lock needed for the backing?

Source: era-contracts draft/v0.35.0 head **`b17415d20`**, `l1-contracts/contracts/interop/InteropCenter.sol`
(a bare `:N` is a line of that file) and `common/ReentrancyGuard.sol`. This refines
`Specs/FeeState.lean`, whose state, send inputs and checks it reuses.

**This file is definitions only.** The results are in
`EraSpec.Contracts.InteropCenter.Properties.FeeReentry` and are proved in
`EraSpec.Contracts.InteropCenter.Proofs.FeeReentry`.

## Why a second model

`FeeState` takes one transaction as one step. That is sound for the deployed code because the
shared `nonReentrant` lock (`ReentrancyGuard.sol:72-98`) stops a send or claim from starting
inside a send or claim. The center forwards indirect value out of its own balance (:788-790)
before it checks `msg.value` (:433-434, :442-443), so whether the lock is also what keeps the
accrued fees backed is a separate question. Here the external calls run arbitrary nested calls
into the center:

    // inside _buildInteropBundle, per indirect starter (:679, :788-790)
    IL2CrossChainSender(recipientAddress).initiateIndirectCall{value: ...}(...);  // nested calls
    // inside _ensureCorrectTotalValue, different base token (:446-451)
    IAssetRouterShared(L2_ASSET_ROUTER_ADDR).bridgehubDepositBaseToken(...);       // nested calls
    // claimProtocolFees (:896-909)
    accumulatedProtocolFees[msg.sender] = 0;                                         // :902
    (bool success, ) = _receiver.call{value: amount}("");                            // :905, nested calls

The asset router's `initiateIndirectCall` reaches the vault and a token's `bridgeBurn` or
`transferFrom`; an L2-native token may run arbitrary code there, and a claim receiver is arbitrary
code. The ZK token is a standard ERC-20 (`StandardTokens` in the results that need it), whose
`transferFrom`/`transfer` call nothing.

## Modelling choices

* A transaction or nested call is an `NTx`; `NRun` is a sequence of them; `Cbs` holds one `NRun`
  per call starter of a send, the `i`-th run executing inside the `i`-th starter's
  `initiateIndirectCall` (and ignored for a direct starter, which makes no call). A nested call
  that reverts and is caught has no effect, so a run lists only the nested calls that succeed;
  if one fails, so does its caller.
* **Three switches** (`Guards`): `nonReentrant` on the sends (:201, :252), `nonReentrant` on the
  claims (:896, :912), and the order of `claimProtocolFees`' write (:902) and call (:905). The
  deployed code has all three (`deployedGuards`). A function without `nonReentrant` neither reads
  nor writes the lock slot.
* The send runs in code order: lock entry; `msg.value` credited; the destination and starter
  checks of `sendStatic`; per starter, the forward (paid from the balance as it then
  is) and its nested run; the ZK fee; the `msg.value` equality on the state at that point
  (`interopProtocolFee` read then, :428-430); the burn (same base token) or the deposit request
  with its nested run (different base token); the fee credit (:456-459); the counter (:749); lock
  exit. `msg.value` is fixed for the frame, so no nested call can satisfy the equality for its
  caller.
* Every other entry point and inflow (`NTx.other`) runs as in `FeeState.exec` and makes no call
  that can re-enter; `other` of a send or claim is not a transaction (use the dedicated
  constructors).
-/

namespace Contracts.InteropCenter.FeeState.Reentry

open Contracts.InteropCenter (Word Address CallStarter totalBurnedCallsValue)

/-- Which reentrancy defences the code has. -/
structure Guards where
  /-- `nonReentrant` on `sendMessage` and `sendBundle` (:201, :252). -/
  sendLock : Bool
  /-- `nonReentrant` on `claimProtocolFees` and `claimZKFees` (:896, :912). -/
  claimLock : Bool
  /-- `claimProtocolFees` zeroes the entry (:902) before it calls the receiver (:905). -/
  writeFirst : Bool

/-- The deployed code. -/
def deployedGuards : Guards := ⟨true, true, true⟩

/-- The deployed code without `nonReentrant` on the claims. -/
def withoutClaimLock : Guards := ⟨true, false, true⟩

/-- The deployed code without `nonReentrant` on the claims and with the write after the call. -/
def withoutClaimLockPayFirst : Guards := ⟨true, false, false⟩

/-- The deployed locks, with `claimProtocolFees`' write after its call. -/
def payFirst : Guards := ⟨true, true, false⟩

/-- `nonReentrant` on the claims only (not on the sends), with `claimProtocolFees`' write after
its call. -/
def withoutSendLockPayFirst : Guards := ⟨false, true, false⟩

/-- `nonReentrant` entry (`ReentrancyGuard.sol:73-89`): with the modifier, the slot must hold `1`
and holds `2` during the call. -/
def enterLock (on : Bool) (S : State) : Option State :=
  if on = true then (if S.lock = 1 then some { S with lock := 2 } else none) else some S

/-- `nonReentrant` exit (`ReentrancyGuard.sol:95-97`): the slot returns to `1`. -/
def exitLock (on : Bool) (S : State) : State := if on = true then { S with lock := 1 } else S

/-- The forwards of the starters without nested runs: each is paid from the balance as it then
is. -/
def forwardPlain : List CallStarter → State → Option State
  | [], S => some S
  | cs :: rest, S =>
    if cs.callAttributes.indirectCall = true then
      if cs.callAttributes.indirectCallMessageValue ≤ S.bal then
        forwardPlain rest { S with bal := S.bal - cs.callAttributes.indirectCallMessageValue }
      else none
    else forwardPlain rest S

/-- The fixed-ZK-fee branch (:579-583) on `S`: as `FeeState.afterSend`'s ZK fields, with the
checks of `SendOk`. -/
def zkFeeStep (P : Params) (S : State) (inp : SendInput) : Option State :=
  if fixedFeePath S inp = true then
    if zkTokenFor S inp.zkResolved ≠ 0 ∧
        (P.tokenCode (zkTokenFor S inp.zkResolved)).hasTransfer = true ∧ inp.sender ≠ P.center then
      some { S with
        zkToken := zkTokenFor S inp.zkResolved
        tokBal := Function.update S.tokBal (zkTokenFor S inp.zkResolved)
          (S.tokBal (zkTokenFor S inp.zkResolved) +
            (P.tokenCode (zkTokenFor S inp.zkResolved)).credited (zkFeeOf S inp))
        zkFees := Function.update S.zkFees inp.coinbase (S.zkFees inp.coinbase + zkFeeOf S inp) }
    else none
  else some S

/-- The same-base-token burn (:436-440): `burnAndStartBridging{value: total}`. -/
def burnStep (inp : SendInput) (S : State) : Option State :=
  if totalBurnedCallsValue inp.starters ≤ S.bal then
    some { S with bal := S.bal - totalBurnedCallsValue inp.starters }
  else none

/-- The tail of a send after the value has been settled: the protocol fee `pf` read at the
equality (:428-430) is credited (:456-459), the counter grows (:749) under its checked `+=`, the
log records the send, and the lock is released. -/
def finishSend (G : Guards) (inp : SendInput) (pf : ℕ) (rec : SendRecord)
    (S : State) : Option State :=
  if inp.dest ≠ S.l1ChainId → S.feeUnits + inp.calls < UInt256.size then
    some (exitLock G.sendLock { S with
      protocolFees := Function.update S.protocolFees inp.coinbase (S.protocolFees inp.coinbase + pf)
      feeUnits := if inp.dest = S.l1ChainId then S.feeUnits else S.feeUnits + inp.calls
      leaves := if inp.dest = S.l1ChainId then S.leaves else S.leaves ++ [inp.calls]
      log := S.log ++ [rec] })
  else none

/-- The destination and starter checks of a send (`FeeState.SendOk` without the lock, the
balance, the equality, the ZK and the counter checks). -/
def sendStatic (P : Params) (S : State) (inp : SendInput) : Prop :=
  S.l1ChainId ≠ P.chainId ∧ inp.dest ≠ P.chainId ∧
  (inp.dest = S.l1ChainId → inp.calls = 1 ∧ ∀ cs ∈ inp.starters, ToL1Starter P cs) ∧
  (∀ cs ∈ inp.starters, cs.callAttributes.indirectCall = true →
    cs.target = P.router ∧ cs.callAttributes.interopCallValue = 0)

instance (P : Params) (S : State) (inp : SendInput) : Decidable (sendStatic P S inp) := by
  unfold sendStatic; infer_instance

mutual
/-- A transaction or a nested call into the center, with the calls its external calls make. -/
inductive NTx where
  /-- `sendBundle` / `sendMessage`. -/
  | send (inp : SendInput) (onForward : Cbs) (onDeposit : NRun)
  /-- `claimProtocolFees(receiver)` by `caller`; `onReceive` runs inside `_receiver.call`. -/
  | claimProtocolFees (caller receiver : Address) (onReceive : NRun)
  /-- `claimZKFees(receiver)` by `caller`. -/
  | claimZKFees (caller receiver zkResolved : Address)
  /-- Any other transaction of `FeeState`, which makes no call that can re-enter. -/
  | other (tx : Tx)
/-- Nested calls, in order. -/
inductive NRun where
  | nil
  | cons (t : NTx) (rest : NRun)
/-- One nested run per call starter. -/
inductive Cbs where
  | nil
  | cons (r : NRun) (rest : Cbs)
end

mutual
/-- The successor state of a (nested) call, `none` if it reverts. -/
def execN (G : Guards) (K : Checks) (P : Params) : NTx → State → Option State
  | .send inp cbs dcb, S =>
    match enterLock G.sendLock S with
    | none => none
    | some S0 =>
      if sendStatic P S0 inp then
        match buildN G K P cbs inp.starters { S0 with bal := S0.bal + inp.msgValue } with
        | none => none
        | some S2 =>
          match zkFeeStep P S2 inp with
          | none => none
          | some S3 =>
            if K.valueCheck = true → inp.msgValue = expectedValue P S3 inp then
              match (if totalBurnedCallsValue inp.starters = 0 then some S3
                  else if sameBase P inp = true then burnStep inp S3
                  else execRun G K P dcb S3) with
              | none => none
              | some S4 => finishSend G inp (protocolFeeOf S3 inp) (sendRecord P S3 inp) S4
            else none
      else none
  | .claimProtocolFees c r cb, S =>
    match enterLock G.claimLock S with
    | none => none
    | some S0 =>
      if S0.protocolFees c = 0 then some (exitLock G.claimLock S0)
      else
        if S0.protocolFees c ≤ S0.bal ∧ r ≠ P.center then
          match execRun G K P cb
              { S0 with
                protocolFees := if G.writeFirst = true then Function.update S0.protocolFees c 0
                  else S0.protocolFees
                bal := S0.bal - S0.protocolFees c
                claims := S0.claims ++ [⟨false, c, r, S0.protocolFees c⟩] } with
          | none => none
          | some S3 =>
            some (exitLock G.claimLock
              (if G.writeFirst = true then S3
                else { S3 with protocolFees := Function.update S3.protocolFees c 0 }))
        else none
  | .claimZKFees c r z, S =>
    match enterLock G.claimLock S with
    | none => none
    | some S0 => (claimZKFeesBody P S0 c r z).map (exitLock G.claimLock)
  | .other tx, S => if tx.isSendOrClaim = true then none else exec K P tx S
/-- A sequence of nested calls, all of which succeed. -/
def execRun (G : Guards) (K : Checks) (P : Params) : NRun → State → Option State
  | .nil, S => some S
  | .cons t rest, S =>
    match execN G K P t S with
    | none => none
    | some S1 => execRun G K P rest S1
/-- The starters' forwards, each with its nested run. -/
def buildN (G : Guards) (K : Checks) (P : Params) : Cbs → List CallStarter → State → Option State
  | .nil, starters, S => forwardPlain starters S
  | .cons _ _, [], S => some S
  | .cons r rest, cs :: css, S =>
    if cs.callAttributes.indirectCall = true then
      if cs.callAttributes.indirectCallMessageValue ≤ S.bal then
        match execRun G K P r { S with bal := S.bal - cs.callAttributes.indirectCallMessageValue } with
        | none => none
        | some S1 => buildN G K P rest css S1
      else none
    else buildN G K P rest css S
end

/-- A `FeeState` transaction as a call with no nested calls. -/
def liftTx : Tx → NTx
  | .send inp => .send inp .nil .nil
  | .claimProtocolFees c r => .claimProtocolFees c r .nil
  | .claimZKFees c r z => .claimZKFees c r z
  | tx => .other tx

/-- A sequence of top-level transactions, all of which succeed. -/
def runN (G : Guards) (K : Checks) (P : Params) : List NTx → State → Option State
  | [], S => some S
  | t :: ts, S =>
    match execN G K P t S with
    | some S' => runN G K P ts S'
    | none => none

/-- `S'` is reachable from `S` with nested calls. -/
def ReachN (G : Guards) (K : Checks) (P : Params) (S S' : State) : Prop :=
  ∃ ts, runN G K P ts S = some S'

/-! ## Witness data -/

/-- `FeeState.wSendA` with coinbase `0x78`. -/
def wSendA78 : SendInput := { wSendA with coinbase := 0x78 }

/-- `initL2`, the fee setting, then two plain sends crediting coinbases `0x77` and `0x78` with `6`
each, as `FeeState` transactions (`liftTx` makes them calls with no nested calls). -/
def wSetupTxs : List Tx := [wInit, wSetFee, .send wSendA, .send wSendA78]

/-- Coinbase `0x77` claims to a receiver whose code re-enters `claimProtocolFees` once for the
same coinbase. -/
def wReenteringClaim : NTx :=
  .claimProtocolFees 0x77 0x88 (.cons (.claimProtocolFees 0x77 0x88 .nil) .nil)

/-- The deployed send `wSendA` of `FeeState`, whose indirect starter's call re-enters
`claimProtocolFees` for coinbase `0x77`. -/
def wSendWithNestedClaim : NTx :=
  .send wSendA (.cons .nil (.cons (.cons (.claimProtocolFees 0x77 0x88 .nil) .nil) .nil)) .nil

/-- Coinbase `0x77` claims to a receiver whose code forces `1` of native value into the center. -/
def wClaimWithNestedInflow : NTx :=
  .claimProtocolFees 0x77 0x88 (.cons (.other (.nativeInflow 1)) .nil)

/-- Coinbase `0x77` claims to a receiver whose code makes the L2→L2 send `FeeState.wSendA` (whose
coinbase is `0x77`), with no nested calls of its own. -/
def wClaimWithNestedSend : NTx :=
  .claimProtocolFees 0x77 0x88 (.cons (.send wSendA .nil .nil) .nil)

end Contracts.InteropCenter.FeeState.Reentry
