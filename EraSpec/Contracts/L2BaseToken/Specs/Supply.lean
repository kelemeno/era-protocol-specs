import EraSpec.Core.Word
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Model: ZKsync OS base-token supply — `L2BaseToken`, `BaseTokenHolder` and the native ledger

Local specification at era-contracts `draft/v0.35.0`, commit
`d9f678900e1bc8286412b78f56d4a9f443983c29`. Files (under `l1-contracts/contracts/`):

* `l2-system/zksync-os/L2BaseToken.sol` (cited `BT`),
* `l2-system/BaseTokenHolder.sol` (cited `BTH`),
* `common/Config.sol:312` (`INITIAL_BASE_TOKEN_HOLDER_BALANCE = 2^127 - 1`),
* `common/l2-helpers/L2ContractAddresses.sol` (cited `ADDR`),
* `bridge/asset-tracker/L2AssetTracker.sol` (cited `AT`), only for the three entry points the
  holder calls, which are kept abstract (`Tracker`).

**This file is definitions only.** Statements are in
`EraSpec.Contracts.L2BaseToken.Properties.Supply`, proofs in
`EraSpec.Contracts.L2BaseToken.Proofs.Supply`.

## What the source does

On ZKsync OS the base token is the VM's native value. Balances live in account state, not in a
contract mapping (`BT:36-39`: `__DEPRECATED_eraAccountBalance` is a retained, unused slot).

* `L2BaseToken.initL2(_l1ChainId)` (`BT:64-77`): `onlyComplexUpgrader` (`BT:29-34`), then reverts
  with `BaseTokenHolderAlreadyInitialized` if the flag is set (`BT:65-67`), sets the flag (`:68`)
  and `L1_CHAIN_ID` (`:69`), calls `MINT_BASE_TOKEN_HOOK` with `INITIAL_BASE_TOKEN_HOLDER_BALANCE`
  (`:71-74`; the hook credits that much new native value to the calling contract), and sends that
  amount to `L2_BASE_TOKEN_HOLDER_ADDR` with `Address.sendValue` (`:76`).
* `L2BaseToken.totalSupply()` (`BT:59-61`) is a view:
  `zkosPreV31TotalSupply + INITIAL_BASE_TOKEN_HOLDER_BALANCE - L2_BASE_TOKEN_HOLDER_ADDR.balance`,
  checked 0.8 arithmetic. `zkosPreV31TotalSupply` (`BT:56`) has no writer in the source; the
  interface says it is "backfilled during v31" (`IL2BaseToken.sol:20`).
* `BaseTokenHolder.give(_to, _amount, _fromChainId)` (`BTH:67-76`): `onlyInteropHandler`
  (`BTH:30-35`); returns early when `_amount == 0` (`:68-70`); calls the tracker's
  `handleFinalizeBaseTokenBridgingOnL2(_fromChainId, _amount)` (`:73`); `sendValue(_to, _amount)`
  (`:74`).
* `BaseTokenHolder.recoverBaseToken(_to, _amount, _toChainId)` (`BTH:79-87`):
  `onlyNativeTokenVault` (`BTH:48-53`); early return on zero (`:80-82`); the tracker's view check
  `assertBaseTokenRecoveryIsAccountingNeutral(_toChainId)` (`:84`); `sendValue` (`:85`).
* `BaseTokenHolder.burnAndStartBridging(_toChainId)` (`BTH:93-96`), `payable`:
  `onlyBridgingCaller` (`BTH:40-45`, InteropCenter or NativeTokenVault); the tracker's
  `handleInitiateBaseTokenBridgingOnL2(_toChainId, msg.value)` (`:94`).
* `receive()` (`BTH:100`) is `onlyL2BaseToken` (`BTH:57-62`).
* "The VM may also move its balance directly via storage" (`BTH:65-66`): L1 deposits are paid out
  of the holder by the VM, with no contract call (`IBaseTokenHolder.sol:12-13`).

## What is modelled

`State` is the whole native ledger (`bal : Address → ℕ`), the two `L2BaseToken` slots that are
written or read (`initialized`, `l1ChainId`, `preV31`), the tracker's state (abstract `T`), and
ghost counters. `Call` is every way the ledger can move, as seen from these contracts:

* the two state-changing entry points of `L2BaseToken` and the four of `BaseTokenHolder`;
* `transfer`: any other value movement between accounts — calls with value, fee payments,
  refunds. It never moves value *out of* the holder or out of `L2BaseToken` (neither has a code
  path that sends value other than the ones modelled), and never *into* the holder (a call with
  value into the holder runs `receive`, modelled separately);
* `forceToHolder`: value forced into the holder without running its code (`SELFDESTRUCT`
  beneficiary);
* `vmRelease`: the VM paying out of the holder directly (L1 deposits).

A revert is the absence of a step (`exec … = none`). `Run` is any interleaving of successful
calls. The tracker is the `Tracker` interface: two state-changing calls that may revert, one view
check. The holder's tracker calls are logged in the ghost `calls`.

## Model boundary (see `ASSUMPTIONS.md`, `MODEL-ZKOS-SUPPLY`, `VM-ZKOS-HOOKS`)

* `MINT_BASE_TOKEN_HOOK` is the only way native value is created, and it credits only
  `L2BaseToken` (the Rust hook; not in this repository). The VM's own native-mint paths of the
  pre-V31 protocol are outside the model (they are what `zkosPreV31TotalSupply` records).
  A hook failure reverts `initL2` (`BT:72-74`) and is no step.
* A recipient's code run by `sendValue` (`Address.sendValue`, OpenZeppelin v4) is not modelled
  inside the step. Neither `give` nor `recoverBaseToken` writes state after the send, so effects
  of a re-entrant recipient are the same as later steps. A rejecting recipient is no step. The
  holder itself and `L2BaseToken` always reject: the holder's `receive` is `onlyL2BaseToken`, and
  `L2BaseToken` has neither `receive` nor `fallback`.
* Balances are `ℕ` with a finite sum over all `2^160` addresses (`MODEL-LEDGER`); the 256-bit bound
  is a theorem (`NoBalanceOverflows`), not an assumption of the step.
* The tracker's own accounting (`AT:169-173`, `AT:188-190`, `AT:277-298`) is abstract; only its
  revert behaviour and the calls the holder makes are modelled. Its own L1-deposit accounting is
  not.
-/

namespace Contracts.L2BaseToken

/-- A 160-bit address. -/
abbrev Address := Fin (2 ^ 160)

/-! ## Constants -/

/-- `INITIAL_BASE_TOKEN_HOLDER_BALANCE = (2 ** 127) - 1` (`common/Config.sol:312`). -/
def INITIAL : ℕ := 2 ^ 127 - 1

/-- `L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR = SYSTEM_CONTRACTS_OFFSET + 0x0a` (`ADDR:6,59`). -/
def baseTokenAddr : Address := 0x800a
/-- `L2_COMPLEX_UPGRADER_ADDR = SYSTEM_CONTRACTS_OFFSET + 0x0f` (`ADDR:6,65`). -/
def complexUpgraderAddr : Address := 0x800f
/-- `L2_NATIVE_TOKEN_VAULT_ADDR = BUILT_IN_CONTRACTS_OFFSET + 0x04` (`ADDR:12,89`). -/
def ntvAddr : Address := 0x10004
/-- `L2_INTEROP_CENTER_ADDR = BUILT_IN_CONTRACTS_OFFSET + 0x0d` (`ADDR:12,118`). -/
def interopCenterAddr : Address := 0x1000d
/-- `L2_INTEROP_HANDLER_ADDR = BUILT_IN_CONTRACTS_OFFSET + 0x0e` (`ADDR:12,121`). -/
def interopHandlerAddr : Address := 0x1000e
/-- `L2_BASE_TOKEN_HOLDER_ADDR = BUILT_IN_CONTRACTS_OFFSET + 0x11` (`ADDR:12,133`). -/
def holderAddr : Address := 0x10011

/-! ## The tracker interface -/

/-- The three `L2AssetTracker` entry points `BaseTokenHolder` calls, on an abstract tracker state.
`none` is a revert. -/
structure Tracker (T : Type) where
  /-- `handleFinalizeBaseTokenBridgingOnL2(_fromChainId, _amount)` (`AT:277-298`), called by
  `give`. -/
  finalize : T → UInt256 → ℕ → Option T
  /-- `handleInitiateBaseTokenBridgingOnL2(_toChainId, _amount)` (`AT:169-173`), called by
  `burnAndStartBridging`. -/
  initiate : T → UInt256 → ℕ → Option T
  /-- `assertBaseTokenRecoveryIsAccountingNeutral(_toChainId)` (`AT:188-190`), a view that reverts
  (`false`) or not. -/
  recoveryNeutral : T → UInt256 → Bool

/-- One state-changing tracker call made by the holder. -/
inductive TrackerCall where
  | finalize (fromChain : UInt256) (amount : ℕ)
  | initiate (toChain : UInt256) (amount : ℕ)
deriving DecidableEq

/-- Replay logged tracker calls on a tracker state (`none` if any of them reverts). -/
def replay {T : Type} (tr : Tracker T) : T → List TrackerCall → Option T
  | t, [] => some t
  | t, .finalize c a :: rest => (tr.finalize t c a).bind (fun t' => replay tr t' rest)
  | t, .initiate c a :: rest => (tr.initiate t c a).bind (fun t' => replay tr t' rest)

/-- Total amount reported through `finalize` calls. -/
def finalizedTotal : List TrackerCall → ℕ
  | [] => 0
  | .finalize _ a :: rest => a + finalizedTotal rest
  | .initiate _ _ :: rest => finalizedTotal rest

/-- Total amount reported through `initiate` calls. -/
def initiatedTotal : List TrackerCall → ℕ
  | [] => 0
  | .finalize _ _ :: rest => initiatedTotal rest
  | .initiate _ a :: rest => a + initiatedTotal rest

/-! ## State -/

/-- The native ledger, the `L2BaseToken` slots this file reads or writes, the tracker, and
ghosts. -/
structure State (T : Type) where
  /-- Native balances (VM account state). -/
  bal : Address → ℕ
  /-- `baseTokenHolderBalanceInitialized` (`BT:46`). -/
  initialized : Bool
  /-- `L1_CHAIN_ID` (`BT:49`). -/
  l1ChainId : UInt256
  /-- `zkosPreV31TotalSupply` (`BT:56`). No writer in the source. -/
  preV31 : ℕ
  /-- The tracker's state. -/
  trk : T
  /-- Ghost: the holder's tracker calls, in order. -/
  calls : List TrackerCall
  /-- Ghost: native value created by `MINT_BASE_TOKEN_HOOK`. -/
  minted : ℕ
  /-- Ghost: paid out by `give`. -/
  given : ℕ
  /-- Ghost: paid out by `recoverBaseToken`. -/
  recovered : ℕ
  /-- Ghost: paid into the holder by `burnAndStartBridging`. -/
  burnt : ℕ
  /-- Ghost: paid out of the holder by the VM directly. -/
  released : ℕ
  /-- Ghost: forced into the holder. -/
  forced : ℕ

/-! ## Ledger operations -/

/-- Add `amt` to `a`. -/
def credit (b : Address → ℕ) (a : Address) (amt : ℕ) : Address → ℕ :=
  Function.update b a (b a + amt)

/-- Subtract `amt` from `a` (callers check `amt ≤ b a` first). -/
def debit (b : Address → ℕ) (a : Address) (amt : ℕ) : Address → ℕ :=
  Function.update b a (b a - amt)

/-- Move `amt` from `f` to `t`. -/
def xfer (b : Address → ℕ) (f t : Address) (amt : ℕ) : Address → ℕ :=
  credit (debit b f amt) t amt

/-- Total native supply: the sum of all balances. -/
def supply {T : Type} (s : State T) : ℕ := ∑ a : Address, s.bal a

/-- Circulating supply: every balance except the holder's reserve. -/
def circulating {T : Type} (s : State T) : ℕ := supply s - s.bal holderAddr

/-- `Address.sendValue(payable(_to), amount)` from `src`: reverts if the sender lacks the balance,
or if `_to` is the holder (its `receive` is `onlyL2BaseToken`, and `src` is never `L2BaseToken`
here) or `L2BaseToken` (no `receive`/`fallback`). -/
def sendValue (b : Address → ℕ) (src dst : Address) (amt : ℕ) : Option (Address → ℕ) :=
  if amt ≤ b src ∧ dst ≠ holderAddr ∧ dst ≠ baseTokenAddr then some (xfer b src dst amt)
  else none

/-! ## Entry points -/

/-- Every way the native ledger moves, with the `msg.sender` of contract calls. -/
inductive Call where
  /-- Any other value movement between accounts (not out of the holder or `L2BaseToken`, not
  into the holder). -/
  | transfer (src dst : Address) (amt : ℕ)
  /-- Value forced into the holder without running its code. -/
  | forceToHolder (src : Address) (amt : ℕ)
  /-- A plain call with value into the holder: `receive()` (`BTH:100`). -/
  | holderReceive (caller : Address) (amt : ℕ)
  /-- `L2BaseToken.initL2(_l1ChainId)` (`BT:64-77`). -/
  | initL2 (caller : Address) (l1 : UInt256)
  /-- `BaseTokenHolder.give(_to, _amount, _fromChainId)` (`BTH:67-76`). -/
  | give (caller dst : Address) (amt : ℕ) (fromChain : UInt256)
  /-- `BaseTokenHolder.recoverBaseToken(_to, _amount, _toChainId)` (`BTH:79-87`). -/
  | recover (caller dst : Address) (amt : ℕ) (toChain : UInt256)
  /-- `BaseTokenHolder.burnAndStartBridging{value: value}(_toChainId)` (`BTH:93-96`). -/
  | burn (caller : Address) (value : ℕ) (toChain : UInt256)
  /-- The VM pays `amt` out of the holder to `dst ≠ holder` (`BTH:65-66`). -/
  | vmRelease (dst : Address) (amt : ℕ)

section exec
variable {T : Type}

/-- The effect of `initL2` past its guards: the hook mints `INITIAL` to `L2BaseToken`
(`BT:71`), which sends it to the holder (`BT:76`; the holder's `receive` accepts `L2BaseToken`,
`BTH:100`). -/
def initL2Effect (s : State T) (l1 : UInt256) : State T :=
  { s with
    bal := xfer (credit s.bal baseTokenAddr INITIAL) baseTokenAddr holderAddr INITIAL
    initialized := true
    l1ChainId := l1
    minted := s.minted + INITIAL }

/-- `initL2`, guards in source order. -/
def execInitL2 (s : State T) (caller : Address) (l1 : UInt256) : Option (State T) :=
  if caller ≠ complexUpgraderAddr then none                                -- BT:29-34
  else if s.initialized = true then none                                     -- BT:65-67
  else some (initL2Effect s l1)                                              -- BT:68-76

/-- `give`, guards in source order. -/
def execGive (tr : Tracker T) (s : State T) (caller dst : Address) (amt : ℕ) (fromChain : UInt256) :
    Option (State T) :=
  if caller ≠ interopHandlerAddr then none                                   -- BTH:30-35
  else if amt = 0 then some s                                                -- BTH:68-70
  else
    match tr.finalize s.trk fromChain amt with                               -- BTH:73
    | none => none
    | some t' =>
      match sendValue s.bal holderAddr dst amt with                           -- BTH:74
      | none => none
      | some b' => some { s with bal := b', trk := t',
                                 calls := s.calls ++ [.finalize fromChain amt],
                                 given := s.given + amt }

/-- `recoverBaseToken`, guards in source order. -/
def execRecover (tr : Tracker T) (s : State T) (caller dst : Address) (amt : ℕ) (toChain : UInt256) :
    Option (State T) :=
  if caller ≠ ntvAddr then none                                              -- BTH:48-53
  else if amt = 0 then some s                                                -- BTH:80-82
  else if tr.recoveryNeutral s.trk toChain = false then none                 -- BTH:84
  else
    match sendValue s.bal holderAddr dst amt with                             -- BTH:85
    | none => none
    | some b' => some { s with bal := b', recovered := s.recovered + amt }

/-- `burnAndStartBridging`: the value moves with the call, then the modifier and body run. -/
def execBurn (tr : Tracker T) (s : State T) (caller : Address) (value : ℕ) (toChain : UInt256) :
    Option (State T) :=
  if value > s.bal caller then none                                          -- call value
  else if caller ≠ interopCenterAddr ∧ caller ≠ ntvAddr then none            -- BTH:40-45
  else
    match tr.initiate s.trk toChain value with                               -- BTH:94
    | none => none
    | some t' => some { s with bal := xfer s.bal caller holderAddr value, trk := t',
                               calls := s.calls ++ [.initiate toChain value],
                               burnt := s.burnt + value }

/-- One call. `none` is a revert. -/
def exec (tr : Tracker T) (s : State T) : Call → Option (State T)
  | .transfer f t amt =>
      if f = holderAddr ∨ f = baseTokenAddr ∨ t = holderAddr ∨ amt > s.bal f then none
      else some { s with bal := xfer s.bal f t amt }
  | .forceToHolder f amt =>
      if f = holderAddr ∨ f = baseTokenAddr ∨ amt > s.bal f then none
      else some { s with bal := xfer s.bal f holderAddr amt, forced := s.forced + amt }
  | .holderReceive _ _ =>
      -- BTH:57-62,100: only L2BaseToken may send with a plain call, and L2BaseToken's only such
      -- call is the one inside `initL2` (BT:76), modelled there. So as a call of its own this
      -- always reverts.
      none
  | .initL2 caller l1 => execInitL2 s caller l1
  | .give caller dst amt c => execGive tr s caller dst amt c
  | .recover caller dst amt c => execRecover tr s caller dst amt c
  | .burn caller v c => execBurn tr s caller v c
  | .vmRelease dst amt =>
      if dst = holderAddr ∨ amt > s.bal holderAddr then none
      else some { s with bal := xfer s.bal holderAddr dst amt, released := s.released + amt }

/-- Runs: any interleaving of successful calls from `s₀`, with their labels. -/
inductive Run (tr : Tracker T) (s₀ : State T) : List Call → State T → Prop
  | nil : Run tr s₀ [] s₀
  | snoc {cs : List Call} {s s' : State T} {c : Call} :
      Run tr s₀ cs s → exec tr s c = some s' → Run tr s₀ (cs ++ [c]) s'

end exec

/-- A pre-`initL2` starting state: the flag is clear, the ghosts are zero, no tracker calls. -/
structure Genesis {T : Type} (s₀ : State T) : Prop where
  notInit : s₀.initialized = false
  noCalls : s₀.calls = []
  minted : s₀.minted = 0
  given : s₀.given = 0
  recovered : s₀.recovered = 0
  burnt : s₀.burnt = 0
  released : s₀.released = 0
  forced : s₀.forced = 0

/-- `totalSupply()` (`BT:59-61`) in checked uint256 arithmetic: `none` is a revert (overflow of
the addition or underflow of the subtraction). -/
def totalSupplyView {T : Type} (s : State T) : Option ℕ :=
  if s.preV31 + INITIAL ≥ 2 ^ 256 then none
  else if s.bal holderAddr > s.preV31 + INITIAL then none
  else some (s.preV31 + INITIAL - s.bal holderAddr)

/-- Is this call an `initL2`? -/
def Call.isInitL2 : Call → Bool
  | .initL2 _ _ => true
  | _ => false

/-- The tracker call a successful call makes, if any. -/
def Call.trackerCall : Call → Option TrackerCall
  | .give _ _ amt c => if amt = 0 then none else some (.finalize c amt)
  | .burn _ v c => some (.initiate c v)
  | _ => none

/-! ## Countermodel machines -/

/-- `initL2` with the `baseTokenHolderBalanceInitialized` check (`BT:65-67`) deleted. -/
def execInitL2NoFlag {T : Type} (s : State T) (caller : Address) (l1 : UInt256) :
    Option (State T) :=
  if caller ≠ complexUpgraderAddr then none
  else some (initL2Effect s l1)

/-- `give` with `onlyInteropHandler` (`BTH:30-35`) deleted. -/
def execGiveNoGuard {T : Type} (tr : Tracker T) (s : State T) (dst : Address) (amt : ℕ)
    (fromChain : UInt256) : Option (State T) :=
  execGive tr s interopHandlerAddr dst amt fromChain

/-! ## Witness data -/

/-- A tracker that accepts every call. -/
def acceptAll : Tracker Unit where
  finalize := fun _ _ _ => some ()
  initiate := fun _ _ _ => some ()
  recoveryNeutral := fun _ _ => true

/-- A genesis state with no native value anywhere and a (correct) zero backfill. -/
def emptyGenesis : State Unit where
  bal := fun _ => 0
  initialized := false
  l1ChainId := 0
  preV31 := 0
  trk := ()
  calls := []
  minted := 0
  given := 0
  recovered := 0
  burnt := 0
  released := 0
  forced := 0

/-- A user address for witnesses. -/
def userAddr : Address := 0xdead

/-- `emptyGenesis` after the upgrader's `initL2(1)`. -/
def witness₁ : State Unit := initL2Effect emptyGenesis 1

/-- …after the InteropHandler's `give(InteropCenter, 100, 5)`. -/
def witness₂ : State Unit :=
  { witness₁ with bal := xfer witness₁.bal holderAddr interopCenterAddr 100, trk := (),
                  calls := witness₁.calls ++ [.finalize 5 100], given := witness₁.given + 100 }

/-- …after the InteropCenter's `burnAndStartBridging{value: 40}(9)`. -/
def witness₃ : State Unit :=
  { witness₂ with bal := xfer witness₂.bal interopCenterAddr holderAddr 40, trk := (),
                  calls := witness₂.calls ++ [.initiate 9 40], burnt := witness₂.burnt + 40 }

/-- …after the VM releases 7 to `userAddr`. -/
def witness₄ : State Unit :=
  { witness₃ with bal := xfer witness₃.bal holderAddr userAddr 7,
                  released := witness₃.released + 7 }

end Contracts.L2BaseToken
