import EraSpec.Contracts.InteropCenter.Specs.FeeState

/-!
# Properties: the `InteropCenter` fee state at draft/v0.35.0

Statements about `EraSpec.Contracts.InteropCenter.Specs.FeeState` (`b17415d20`). Proofs are in
`EraSpec.Contracts.InteropCenter.Proofs.FeeState`. Runs start from fresh storage (`init`) on one
chain; `deployed` is the code with both of its switches on.

## (1) Backing

With the `msg.value` equalities (:433-434, :442-443), the native balance of the center is exactly
the sum of all coinbases' accrued protocol fees plus the native value forced into it
(`NativeBalanceIsFeesPlusForced`), so the fees are backed (`ProtocolFeesBacked`). Under the
standard-token premise the center's balance in its cached ZK token is at least the sum of the
accrued ZK fees, and no ZK fee accrues before the token is cached (`ZkFeesBacked`). Per
transaction, neither excess shrinks (`BackingNeverShrinks`). The equalities are load-bearing:
without them a withdrawal pays its indirect value out of a coinbase's accrued fees, whose claim
then reverts (`WithoutValueCheckFeesFundAWithdrawal`). The standard-token premise is load-bearing
(`NonStandardZkTokenUnbacked`). Whether the shared reentrancy lock is needed for the backing is
the subject of `FeeReentry`.

## (2) One send

With the equalities, a successful send adds exactly its protocol fee to the native balance,
credited to the coinbase alone (`SendAccruesExactProtocolFee`). Under the standard-token premise, on
the fixed-fee path it adds exactly `ZK_INTEROP_FEE * calls` to the center's balance in the ZK token
and to the coinbase's ZK entry, and off that path it changes neither (`SendAccruesExactZkFee`). Its
payments are a forward to the asset router per indirect starter, totalling
`Σ indirectCallMessageValue`; then one burn of the direct calls' total value through the holder
toward the destination exactly when the base tokens agree and that total is nonzero, and one
value-free deposit request of that total toward the destination (for the destination's base-token
asset id, with the sender as original caller) exactly when they differ and it is nonzero; with the
equalities `msg.value` is the native value paid out plus the protocol fee (`SendPaymentsExact`).

## (3) Claims

A successful claim pays exactly the claimant's entry and zeroes it, changing no other entry
(`ClaimProtocolFeesExact`, `ClaimZkFeesExact`).

## (4) Writers

Only the bootloader changes `interopProtocolFee` (`ProtocolFeeSetOnlyByBootloader`). Only the
upgrader's `initL2` changes `L1_CHAIN_ID`, `ZK_INTEROP_FEE` and `ZK_TOKEN_ASSET_ID`
(`InitFieldsOnlyByInitL2`); a run from fresh storage has at most one `initL2`, and every send or
claim of it comes after that `initL2` (`InitL2AtMostOnceAndFirst`). `zkToken` changes only from
unset (`ZkTokenSetOnce`). The pause flag is never written (`PausedNeverWritten`). The ownership
entry points change only the two ownership fields, and every other transaction except `initL2` has
the same outcome whoever holds them and leaves them unchanged (`OwnerHasNoFeePower`).

## (5) The fee-unit counter

Each transaction changes the counter by exactly `Tx.unitsFrom`: an L2→L2 send's call count, `0`
otherwise (`FeeUnitsDeltaExact`), so it never decreases. With `onlyInteropCenter`, a step appends
an IMT leaf only as an L2→L2 send that adds that bundle's call count in the same step
(`EveryLeafCounted`), and along any run the counter grows by the call count of the run's L2→L2
sends, which is the sum over the leaves the run appends (`FeeUnitsAreL2Calls`). A zero-call bundle
appends a leaf and adds nothing (`ZeroCallBundleAddsLeafNoUnits`, the case
`protocol-docs/interop-fee.md:9-10` documents). Without `onlyInteropCenter` a leaf for a bundle
with calls is appended uncounted (`WithoutOnlyInteropCenterUncountedLeaf`).

## Non-vacuity

`FeeStateWitness` is a run of the deployed code meeting the premises of the headlines with nonzero
protocol fees, ZK fees, forced value, counter and an L1 send. `SendWitness`, `ClaimWitness`,
`WriterWitness` and `OwnershipWitness` meet the per-step premises with nonzero amounts.
-/

namespace Contracts.InteropCenter.FeeState

open Contracts.InteropCenter (Word Address CallStarter totalBurnedCallsValue)

/-! ## (1) Backing -/

/-- **THE NATIVE BALANCE IS THE ACCRUED FEES PLUS THE FORCED VALUE.** Along any run from fresh
storage of code with the `msg.value` equalities, the center's native balance equals the sum over
all addresses of `accumulatedProtocolFees` plus the native value forced into the center. -/
def Properties.NativeBalanceIsFeesPlusForced : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), K.valueCheck = true → Reach K P init S →
    S.bal = (∑ c : Address, S.protocolFees c) + S.forcedIn

/-- **HEADLINE (1a): ACCRUED PROTOCOL FEES ARE BACKED.** Along any run from fresh storage of code
with the `msg.value` equalities, the sum of all `accumulatedProtocolFees` is at most the center's
native balance. -/
def Properties.ProtocolFeesBacked : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), K.valueCheck = true → Reach K P init S →
    (∑ c : Address, S.protocolFees c) ≤ S.bal

/-- **HEADLINE (1b): ACCRUED ZK FEES ARE BACKED.** Under the standard-token premise, along any run
from fresh storage (either switch on or off): while `zkToken` is unset every `accumulatedZKFees`
entry is `0`, and the sum of all entries is at most the center's balance in the cached ZK token. -/
def Properties.ZkFeesBacked : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), StandardTokens P → Reach K P init S →
    (S.zkToken = 0 → ∀ c, S.zkFees c = 0) ∧ (∑ c : Address, S.zkFees c) ≤ zkBalance S

/-- **NO TRANSACTION SHRINKS THE BACKING.** For every successful transaction from every state:
with the `msg.value` equalities, `bal - Σ accumulatedProtocolFees` does not decrease; under the
standard-token premise, `zkBalance - Σ accumulatedZKFees` does not decrease. -/
def Properties.BackingNeverShrinks : Prop :=
  ∀ (K : Checks) (P : Params) (tx : Tx) (S S' : State), exec K P tx S = some S' →
    (K.valueCheck = true →
      (S.bal : ℤ) - ∑ c : Address, (S.protocolFees c : ℤ) ≤
        (S'.bal : ℤ) - ∑ c : Address, (S'.protocolFees c : ℤ)) ∧
    (StandardTokens P →
      (zkBalance S : ℤ) - ∑ c : Address, (S.zkFees c : ℤ) ≤
        (zkBalance S' : ℤ) - ∑ c : Address, (S'.zkFees c : ℤ))

/-- **WITHOUT THE `msg.value` EQUALITIES, A WITHDRAWAL IS FUNDED FROM ACCRUED FEES.** On the
witness chain, after `initL2`, a fee setting and one fully paid send, coinbase `0x77` has `6`
accrued and the balance is `6`. The deployed code rejects an L2→L1 withdrawal that forwards `6`
to the asset router with `msg.value = 0`; the code without the equalities accepts it, leaving a
balance below the accrued fees, and the coinbase's claim then reverts. -/
def Properties.WithoutValueCheckFeesFundAWithdrawal : Prop :=
  ∃ S S', Reach deployed wP init S ∧ Reach withoutValueCheck wP init S ∧
    S.protocolFees 0x77 = 6 ∧
    exec deployed wP (.send wSendUnderpaid) S = none ∧
    exec withoutValueCheck wP (.send wSendUnderpaid) S = some S' ∧
    S'.bal < ∑ c : Address, S'.protocolFees c ∧
    exec withoutValueCheck wP (.claimProtocolFees 0x77 0x88) S' = none

/-- **WITH A TOKEN THAT DOES NOT CREDIT, THE ZK FEES ARE UNBACKED.** On the witness chain with the
token at `wZk` crediting nothing on `transferFrom`, a fixed-fee send of the deployed code accrues
a nonzero ZK fee while the center's ZK balance stays below the accrued sum. -/
def Properties.NonStandardZkTokenUnbacked : Prop :=
  ∃ S, Reach deployed wPBadZk init S ∧ zkBalance S < ∑ c : Address, S.zkFees c

/-! ## (2) One send -/

/-- **(2a) A SEND ADDS EXACTLY ITS PROTOCOL FEE, CREDITED TO THE COINBASE ALONE.** For a successful
send of code with the `msg.value` equalities: the native balance grows by exactly
`protocolFeeOf S inp` (`interopProtocolFee * calls`, or `0` with `useFixedFee` or to L1), the
coinbase's entry grows by the same amount, and no other entry changes. -/
def Properties.SendAccruesExactProtocolFee : Prop :=
  ∀ (K : Checks) (P : Params) (S : State) (inp : SendInput) (S' : State),
    K.valueCheck = true → exec K P (.send inp) S = some S' →
    S'.bal = S.bal + protocolFeeOf S inp ∧
    S'.protocolFees inp.coinbase = S.protocolFees inp.coinbase + protocolFeeOf S inp ∧
    ∀ c, c ≠ inp.coinbase → S'.protocolFees c = S.protocolFees c

/-- **(2b) THE ZK FEE OF ONE SEND.** Under the standard-token premise, for a successful send: on the
fixed-fee path (`useFixedFee`, not to L1) the cached ZK token is the resolved one and nonzero, the
center's balance in it grows by exactly `ZK_INTEROP_FEE * calls`, no other token balance changes,
and the coinbase's ZK entry grows by the same amount, no other entry changing; off that path
`zkToken`, the token balances and the ZK entries are unchanged. -/
def Properties.SendAccruesExactZkFee : Prop :=
  ∀ (K : Checks) (P : Params) (S : State) (inp : SendInput) (S' : State),
    StandardTokens P → exec K P (.send inp) S = some S' →
    (fixedFeePath S inp = true →
      S'.zkToken = zkTokenFor S inp.zkResolved ∧ S'.zkToken ≠ 0 ∧
      S'.tokBal = Function.update S.tokBal S'.zkToken
        (S.tokBal S'.zkToken + S.zkInteropFee * inp.calls) ∧
      S'.zkFees = Function.update S.zkFees inp.coinbase
        (S.zkFees inp.coinbase + S.zkInteropFee * inp.calls)) ∧
    (fixedFeePath S inp = false →
      S'.zkToken = S.zkToken ∧ S'.tokBal = S.tokBal ∧ S'.zkFees = S.zkFees)

/-- **(2c) WHERE A SEND'S VALUE GOES.** For a successful send: the log gains its record, whose
payments are `sendPayments P inp`; every forward among them is to the asset router, the forwards
(`forwardPayments`, one per indirect starter) are made to the asset router alone and total
`Σ indirectCallMessageValue` over the indirect starters; the calls' value `totalBurnedCallsValue`
is the sum over the direct starters; the payments contain a burn through the holder toward the
destination exactly when the base tokens agree and that value is nonzero, a value-free deposit
request toward the destination exactly when they differ and it is nonzero. Every burn among the
payments is toward the destination for exactly `totalBurnedCallsValue`, and that burn occurs once
when the base tokens agree and the value is nonzero, never otherwise; every deposit request among
them is toward the destination for the destination's base-token asset id, with the sender as
original caller and exactly `totalBurnedCallsValue`, and that request occurs once when the base
tokens differ and the value is nonzero, never otherwise. With the `msg.value` equalities,
`msg.value` is the native value paid out plus the protocol fee. -/
def Properties.SendPaymentsExact : Prop :=
  ∀ (K : Checks) (P : Params) (S : State) (inp : SendInput) (S' : State),
    exec K P (.send inp) S = some S' →
    S'.log = S.log ++ [sendRecord P S inp] ∧
    (sendRecord P S inp).payments = sendPayments P inp ∧
    (∀ s v, Payment.forward s v ∈ sendPayments P inp → s = P.router) ∧
    (∀ p ∈ forwardPayments inp.starters, ∃ v, p = .forward P.router v) ∧
    nativeOut (forwardPayments inp.starters) = indirectTotal inp.starters ∧
    totalBurnedCallsValue inp.starters =
      ((inp.starters.filter fun cs => !cs.callAttributes.indirectCall).map
        fun cs => cs.callAttributes.interopCallValue).sum ∧
    ((∃ v, Payment.burn inp.dest v ∈ sendPayments P inp) ↔
      (sameBase P inp = true ∧ totalBurnedCallsValue inp.starters ≠ 0)) ∧
    ((∃ a o v, Payment.deposit inp.dest a o v ∈ sendPayments P inp) ↔
      (sameBase P inp = false ∧ totalBurnedCallsValue inp.starters ≠ 0)) ∧
    (∀ d v, Payment.burn d v ∈ sendPayments P inp →
      d = inp.dest ∧ v = totalBurnedCallsValue inp.starters) ∧
    (sendPayments P inp).count (.burn inp.dest (totalBurnedCallsValue inp.starters)) =
      (if sameBase P inp = true ∧ totalBurnedCallsValue inp.starters ≠ 0 then 1 else 0) ∧
    (∀ d a o v, Payment.deposit d a o v ∈ sendPayments P inp →
      d = inp.dest ∧ a = inp.destBase ∧ o = inp.sender ∧ v = totalBurnedCallsValue inp.starters) ∧
    (sendPayments P inp).count
        (.deposit inp.dest inp.destBase inp.sender (totalBurnedCallsValue inp.starters)) =
      (if sameBase P inp = false ∧ totalBurnedCallsValue inp.starters ≠ 0 then 1 else 0) ∧
    (K.valueCheck = true → inp.msgValue = nativeOut (sendPayments P inp) + protocolFeeOf S inp)

/-! ## (3) Claims -/

/-- **(3a) A PROTOCOL-FEE CLAIM PAYS EXACTLY THE CLAIMANT'S ENTRY AND ZEROES IT.** For a
successful `claimProtocolFees(r)` by `c`: the ledger is the old one with `c`'s entry zeroed, the
native balance drops by exactly that entry, which it covered; with a zero entry nothing changes;
with a nonzero one the receiver is not the center and the claim log gains `(c, r, entry)`. -/
def Properties.ClaimProtocolFeesExact : Prop :=
  ∀ (K : Checks) (P : Params) (S : State) (c r : Address) (S' : State),
    exec K P (.claimProtocolFees c r) S = some S' →
    S'.protocolFees = Function.update S.protocolFees c 0 ∧
    S'.bal = S.bal - S.protocolFees c ∧ S.protocolFees c ≤ S.bal ∧
    (S.protocolFees c = 0 → S' = S) ∧
    (S.protocolFees c ≠ 0 →
      r ≠ P.center ∧ S'.claims = S.claims ++ [⟨false, c, r, S.protocolFees c⟩])

/-- **(3b) A ZK-FEE CLAIM PAYS EXACTLY THE CLAIMANT'S ENTRY AND ZEROES IT.** For a successful
`claimZKFees(r)` by `c`: the ZK ledger is the old one with `c`'s entry zeroed; with a zero entry
nothing changes; with a nonzero one the token used is the resolved ZK token, now cached, whose
balance covered the entry, the claim log gains `(c, r, entry)`, and the center's balance in that
token drops by exactly the entry, unless the receiver is the center itself, in which case no
balance changes. -/
def Properties.ClaimZkFeesExact : Prop :=
  ∀ (K : Checks) (P : Params) (S : State) (c r z : Address) (S' : State),
    exec K P (.claimZKFees c r z) S = some S' →
    S'.zkFees = Function.update S.zkFees c 0 ∧
    (S.zkFees c = 0 → S' = S) ∧
    (S.zkFees c ≠ 0 →
      S'.zkToken = zkTokenFor S z ∧ S.zkFees c ≤ S.tokBal S'.zkToken ∧
      S'.claims = S.claims ++ [⟨true, c, r, S.zkFees c⟩] ∧
      (r ≠ P.center →
        S'.tokBal = Function.update S.tokBal S'.zkToken (S.tokBal S'.zkToken - S.zkFees c)) ∧
      (r = P.center → S'.tokBal = S.tokBal))

/-! ## (4) Writers -/

/-- **(4a) ONLY THE BOOTLOADER SETS THE PROTOCOL FEE.** Every successful transaction leaves
`interopProtocolFee` unchanged, or is `setInteropFee(f)` called by the bootloader and sets it to
`f`. -/
def Properties.ProtocolFeeSetOnlyByBootloader : Prop :=
  ∀ (K : Checks) (P : Params) (tx : Tx) (S S' : State), exec K P tx S = some S' →
    S'.interopProtocolFee = S.interopProtocolFee ∨
      ∃ f, tx = .setInteropFee P.bootloader f ∧ S'.interopProtocolFee = f

/-- **(4b) ONLY THE UPGRADER'S `initL2` WRITES THE INIT FIELDS.** Every successful transaction
leaves `L1_CHAIN_ID`, `ZK_INTEROP_FEE` and `ZK_TOKEN_ASSET_ID` unchanged, or is `initL2(l, o, z)`
called by the upgrader on the uninitialised lock with `z ≠ 0`, writing `l`, `10e18` and `z`. -/
def Properties.InitFieldsOnlyByInitL2 : Prop :=
  ∀ (K : Checks) (P : Params) (tx : Tx) (S S' : State), exec K P tx S = some S' →
    (S'.l1ChainId = S.l1ChainId ∧ S'.zkInteropFee = S.zkInteropFee ∧
      S'.zkTokenAssetId = S.zkTokenAssetId) ∨
    ∃ l o z, tx = .initL2 P.upgrader l o z ∧ S.lock = 0 ∧ z ≠ 0 ∧
      S'.l1ChainId = l ∧ S'.zkInteropFee = defaultZkInteropFee ∧ S'.zkTokenAssetId = z

/-- **(4c) `initL2` RUNS AT MOST ONCE, AND BEFORE EVERY SEND AND CLAIM.** In every run from fresh
storage, at most one transaction is an `initL2`, and every send or claim of the run comes after
it. -/
def Properties.InitL2AtMostOnceAndFirst : Prop :=
  ∀ (K : Checks) (P : Params) (txs : List Tx) (S : State), run K P txs init = some S →
    (txs.filter Tx.isInitL2).length ≤ 1 ∧
    ∀ (i : ℕ) (hi : i < txs.length), txs[i].isSendOrClaim = true →
      ∃ (j : ℕ) (hj : j < i), (txs[j]'(Nat.lt_trans hj hi)).isInitL2 = true

/-- **(4d) `zkToken` CHANGES ONLY FROM UNSET.** No successful transaction changes a set
`zkToken`. -/
def Properties.ZkTokenSetOnce : Prop :=
  ∀ (K : Checks) (P : Params) (tx : Tx) (S S' : State), exec K P tx S = some S' →
    S.zkToken ≠ 0 → S'.zkToken = S.zkToken

/-- **(4e) THE PAUSE FLAG IS NEVER WRITTEN.** No successful transaction changes `_paused`. -/
def Properties.PausedNeverWritten : Prop :=
  ∀ (K : Checks) (P : Params) (tx : Tx) (S S' : State), exec K P tx S = some S' →
    S'.paused = S.paused

/-- **(4f) THE OWNER HAS NO POWER OVER THE FEE STATE.** The three ownership entry points change
nothing but the owner and pending owner; every other transaction except `initL2` has the same
outcome whoever the owner and pending owner are, and does not change them. -/
def Properties.OwnerHasNoFeePower : Prop :=
  (∀ (K : Checks) (P : Params) (tx : Tx) (S S' : State), tx.isOwnership = true →
    exec K P tx S = some S' → ∃ o p, S' = S.withOwners o p) ∧
  (∀ (K : Checks) (P : Params) (tx : Tx) (S : State) (o p : Address),
    tx.isOwnership = false → tx.isInitL2 = false →
    exec K P tx (S.withOwners o p) = (exec K P tx S).map fun S' => S'.withOwners o p)

/-! ## (5) The fee-unit counter -/

/-- **(5a) EACH TRANSACTION MOVES THE COUNTER BY EXACTLY ITS L2→L2 CALL COUNT.** A successful
transaction from `S` changes `INTEROP_FEE_UNITS_SLOT` by exactly `tx.unitsFrom S`: the call count
of an L2→L2 send, `0` for an L2→L1 send, a claim, a fee setting, `initL2` and every other
transaction (a preview never commits). So the counter never decreases. -/
def Properties.FeeUnitsDeltaExact : Prop :=
  ∀ (K : Checks) (P : Params) (tx : Tx) (S S' : State), exec K P tx S = some S' →
    S'.feeUnits = S.feeUnits + tx.unitsFrom S ∧ S.feeUnits ≤ S'.feeUnits

/-- **(5b) EVERY IMT LEAF IS COUNTED WITH ITS BUNDLE'S CALLS.** With `onlyInteropCenter`, a
successful transaction either appends no leaf and leaves the counter unchanged, or is an L2→L2 send
that appends one leaf for its bundle and adds that bundle's call count to the counter. -/
def Properties.EveryLeafCounted : Prop :=
  ∀ (K : Checks) (P : Params) (tx : Tx) (S S' : State), K.onlyInteropCenter = true →
    exec K P tx S = some S' →
    (S'.leaves = S.leaves ∧ S'.feeUnits = S.feeUnits) ∨
    ∃ inp, tx = .send inp ∧ inp.dest ≠ S.l1ChainId ∧ S'.leaves = S.leaves ++ [inp.calls] ∧
      S'.feeUnits = S.feeUnits + inp.calls

/-- **HEADLINE (5): THE COUNTER IS THE CALL COUNT OF THE L2→L2 SENDS.** With
`onlyInteropCenter`, along any run the log and the leaf list are extended, and the counter grows by
exactly the summed call count of the run's L2→L2 sends, which equals the summed call count of the
leaves the run appends. (The bootloader's saturating `end - begin` is therefore exact.) -/
def Properties.FeeUnitsAreL2Calls : Prop :=
  ∀ (K : Checks) (P : Params) (txs : List Tx) (S S' : State), K.onlyInteropCenter = true →
    run K P txs S = some S' →
    ∃ (new : List SendRecord) (newLeaves : List ℕ), S'.log = S.log ++ new ∧
      S'.leaves = S.leaves ++ newLeaves ∧ S'.feeUnits = S.feeUnits + l2Calls new ∧
      newLeaves.sum = l2Calls new ∧ S'.feeUnits - S.feeUnits = l2Calls new

/-- **A ZERO-CALL BUNDLE APPENDS A LEAF AND ADDS NO UNIT.** A run of the deployed code from fresh
storage, `initL2` then an L2→L2 send of a bundle with no calls, ending with one IMT leaf, one
logged L2→L2 send and the counter at `0`. -/
def Properties.ZeroCallBundleAddsLeafNoUnits : Prop :=
  ∃ S, Reach deployed wP init S ∧ S.leaves = [0] ∧ S.feeUnits = 0 ∧
    S.log.map (fun r => (r.toL1, r.input.calls)) = [(false, 0)]

/-- **THE COUNTER'S SLOT IS SEPARATE FROM THE FIXED SLOTS.** `INTEROP_FEE_UNITS_SLOT`
(`Config.sol:147`) differs from the reentrancy lock slot, the two EIP-1967 proxy slots, and every
slot below `2^64`. Mapping entries are not covered (their slots are keccak outputs). -/
def Properties.FeeUnitsSlotSeparate : Prop :=
  feeUnitsSlot ≠ lockSlot ∧ feeUnitsSlot ≠ eip1967ImplSlot ∧ feeUnitsSlot ≠ eip1967AdminSlot ∧
    ∀ n < 2 ^ 64, n ≠ feeUnitsSlot

/-- **WITHOUT `onlyInteropCenter`, A LEAF WITH CALLS IS UNCOUNTED.** A run of the code without the
`append` gate in which another account appends a leaf for a bundle with `3` calls and the counter
stays `0`. -/
def Properties.WithoutOnlyInteropCenterUncountedLeaf : Prop :=
  ∃ S, Reach withoutOnlyInteropCenter wP init S ∧ S.leaves = [3] ∧ S.feeUnits = 0

/-! ## Non-vacuity -/

/-- The witness run `wTxs` of the deployed code (`initL2`, a fee setting, a same-base L2→L2 send
paying a protocol fee, a fixed-fee L2→L2 send, an L2→L1 withdrawal, a forced inflow) succeeds on a
chain meeting the standard-token premise, ending with protocol fees `6`, ZK fees `10e18`, forced
value `2`, balance `8`, counter `3` over two leaves, and one L1 send logged. -/
def Properties.FeeStateWitness : Prop :=
  ∃ S, run deployed wP wTxs init = some S ∧ StandardTokens wP ∧
    S.bal = 8 ∧ (∑ c : Address, S.protocolFees c) = 6 ∧ S.forcedIn = 2 ∧
    (∑ c : Address, S.zkFees c) = defaultZkInteropFee ∧ zkBalance S = defaultZkInteropFee ∧
    S.zkToken = wZk ∧ S.feeUnits = 3 ∧ S.leaves = [2, 1] ∧
    S.log.map (fun r => (r.toL1, r.protocolFee, r.zkFee)) =
      [(false, 6, 0), (false, 0, defaultZkInteropFee), (true, 0, 0)] ∧
    l2Calls S.log = 3 ∧ S.lock = 1 ∧ S.l1ChainId = 1

/-- The three sends of the witness run meet the per-send premises non-trivially: the first pays a
protocol fee `6` and both a forward and a burn, the second takes the fixed-fee path with a different
base token and a deposit, the third goes to L1. -/
def Properties.SendWitness : Prop :=
  ∃ S2 S3 S4 S5, run deployed wP [wInit, wSetFee] init = some S2 ∧
    exec deployed wP (.send wSendA) S2 = some S3 ∧
    exec deployed wP (.send wSendB) S3 = some S4 ∧
    exec deployed wP (.send wSendC) S4 = some S5 ∧
    protocolFeeOf S2 wSendA = 6 ∧
    sendPayments wP wSendA = [.forward 0x10003 5, .burn 272 4] ∧
    fixedFeePath S3 wSendB = true ∧ zkFeeOf S3 wSendB = defaultZkInteropFee ∧
    sendPayments wP wSendB = [.deposit 272 wOtherBase 0x51 7] ∧
    wSendC.dest = S4.l1ChainId ∧ sendPayments wP wSendC = [.forward 0x10003 8]

/-- From the witness state both claims succeed and pay nonzero amounts; the ZK claim runs with
`zkToken` already set. -/
def Properties.ClaimWitness : Prop :=
  ∃ S S' S'', run deployed wP wTxs init = some S ∧
    exec deployed wP (.claimProtocolFees 0x77 0x88) S = some S' ∧ S.protocolFees 0x77 = 6 ∧
    exec deployed wP (.claimZKFees 0x77 0x88 0) S' = some S'' ∧
    S'.zkFees 0x77 = defaultZkInteropFee ∧ S'.zkToken = wZk ∧ S''.claims.length = 2

/-- `initL2` by the upgrader and `setInteropFee` by the bootloader succeed from fresh storage and
write their fields. -/
def Properties.WriterWitness : Prop :=
  ∃ S1 S2, exec deployed wP wInit init = some S1 ∧ exec deployed wP wSetFee S1 = some S2 ∧
    S1.l1ChainId = 1 ∧ S1.zkTokenAssetId = 0x2a ∧ S1.zkInteropFee = defaultZkInteropFee ∧
    S1.lock = 1 ∧ S2.interopProtocolFee = 3

/-- From the witness state the owner nominates `0xaa`, which accepts. -/
def Properties.OwnershipWitness : Prop :=
  ∃ S S' S'', run deployed wP wTxs init = some S ∧ S.owner = 0x99 ∧
    exec deployed wP (.transferOwnership 0x99 0xaa) S = some S' ∧
    exec deployed wP (.acceptOwnership 0xaa) S' = some S'' ∧ S''.owner = 0xaa

end Contracts.InteropCenter.FeeState
