import EraSpec.Contracts.InteropCenter.Specs.FeeReentry

/-!
# Properties: the fee backing with nested calls

Statements about `EraSpec.Contracts.InteropCenter.Specs.FeeReentry` (`b17415d20`). Proofs are in
`EraSpec.Contracts.InteropCenter.Proofs.FeeReentry`.

## The question

A send forwards indirect value from the center's balance (:788-790) before checking `msg.value`
(:433-434, :442-443), and the forwarded call may run code that calls back into the center, while
the balance is transiently below the accrued fees. The question is whether the claims'
`nonReentrant` (:896, :912) is what keeps the accrued fees backed against such a call.

## Answers

With the `msg.value` equalities, no call — top-level or nested at any depth inside sends' forwards,
deposits and claim receivers — lowers `bal - Σ accumulatedProtocolFees`, provided **either**
`claimProtocolFees` zeroes the entry before paying (the deployed order, :902 before :905) **or**
the claims hold the lock (`NestedBackingNeverShrinks`). So the accrued protocol fees stay backed
along every nested run from fresh storage in both cases (`NestedProtocolFeesBacked`); in
particular the deployed code without the claims' lock keeps them backed. (In the model `msg.value`
is an input of the send's frame, so a send that misses the equality reverts whatever its nested
calls did.) Under the standard-token premise the ZK fees stay backed whatever the switches
(`NestedZkFeesBacked`). With **neither** defence, a receiver that re-enters the claim makes it pay
twice, below another coinbase's accrued fees (`NoLockNoWriteFirstDrainsFees`); with the deployed
code the same re-entering claim reverts, and with the write first and no lock it pays once.

A `FeeState` transaction is exactly the corresponding call with no nested calls, with the sends'
lock and, for a claim, the claims' lock (`FlatIsNestedWithoutCalls`). With the deployed locks no
send or claim succeeds from a state whose lock slot holds `2`, the slot's value inside a send or
claim (`HeldLockBlocksSendsAndClaims`).

## Non-vacuity

`NestedClaimInsideSendWitness`: with the deployed code minus the claims' lock, a claim runs inside
a send's indirect call and pays `6`, and the run, reachable from fresh storage, ends with nonzero
accrued fees; with the deployed code the same send reverts. Its run meets the premises of the
three backing results (`FeeState.wP_standard` gives the standard-token premise).
-/

namespace Contracts.InteropCenter.FeeState.Reentry

open Contracts.InteropCenter (Word Address CallStarter totalBurnedCallsValue)

/-- **HEADLINE: NO NESTED CALL SHRINKS THE NATIVE BACKING, IF EITHER CLAIM DEFENCE IS PRESENT.**
With the `msg.value` equalities and with `claimProtocolFees` either writing before it pays or
holding the lock, every successful call from every state, including all calls nested in it,
leaves `bal - Σ accumulatedProtocolFees` at least as large. -/
def Properties.NestedBackingNeverShrinks : Prop :=
  ∀ (G : Guards) (K : Checks) (P : Params), K.valueCheck = true →
    (G.writeFirst = true ∨ G.claimLock = true) →
    ∀ (t : NTx) (S S' : State), execN G K P t S = some S' →
      (S.bal : ℤ) - ∑ c : Address, (S.protocolFees c : ℤ) ≤
        (S'.bal : ℤ) - ∑ c : Address, (S'.protocolFees c : ℤ)

/-- **THE PROTOCOL FEES STAY BACKED UNDER NESTED CALLS.** With the `msg.value` equalities and
either claim defence, along every nested run from fresh storage the sum of
`accumulatedProtocolFees` is at most the native balance. This covers the deployed code without the
claims' `nonReentrant` (`withoutClaimLock`). -/
def Properties.NestedProtocolFeesBacked : Prop :=
  ∀ (G : Guards) (K : Checks) (P : Params) (S : State), K.valueCheck = true →
    (G.writeFirst = true ∨ G.claimLock = true) → ReachN G K P init S →
    (∑ c : Address, S.protocolFees c) ≤ S.bal

/-- **THE ZK FEES STAY BACKED UNDER NESTED CALLS.** Under the standard-token premise, whatever the
switches, along every nested run from fresh storage: while `zkToken` is unset no ZK fee is
accrued, and the sum of `accumulatedZKFees` is at most the balance in the cached token. -/
def Properties.NestedZkFeesBacked : Prop :=
  ∀ (G : Guards) (K : Checks) (P : Params) (S : State), StandardTokens P → ReachN G K P init S →
    (S.zkToken = 0 → ∀ c, S.zkFees c = 0) ∧ (∑ c : Address, S.zkFees c) ≤ zkBalance S

/-- **WITH NEITHER DEFENCE, A RE-ENTERING RECEIVER DRAINS ANOTHER COINBASE'S FEES.** After the
same setup in all three codes (coinbases `0x77` and `0x78` each accrue `6`, the balance is `12`),
coinbase `0x77` claims to a receiver that re-enters `claimProtocolFees` once. The deployed code
reverts the claim; with the write first and no lock it pays `6` once; with neither it pays `6`
twice, leaving a balance below the accrued fees. -/
def Properties.NoLockNoWriteFirstDrainsFees : Prop :=
  ∃ S S1 S2, ReachN deployedGuards deployed wP init S ∧
    ReachN withoutClaimLock deployed wP init S ∧ ReachN withoutClaimLockPayFirst deployed wP init S ∧
    S.bal = 12 ∧ S.protocolFees 0x77 = 6 ∧ S.protocolFees 0x78 = 6 ∧
    execN deployedGuards deployed wP wReenteringClaim S = none ∧
    execN withoutClaimLock deployed wP wReenteringClaim S = some S1 ∧ S1.bal = 6 ∧
    execN withoutClaimLockPayFirst deployed wP wReenteringClaim S = some S2 ∧ S2.bal = 0 ∧
    S2.bal < ∑ c : Address, S2.protocolFees c

/-- **A CALL WITH NO NESTED CALLS IS THE `FeeState` TRANSACTION.** With the sends' lock, and the
claims' lock when `tx` is a claim, every `FeeState` transaction has exactly the outcome of the
corresponding call with no nested calls (`liftTx`), success and successor state included; in
particular with the deployed locks every `FeeState` run is a run of this model. -/
def Properties.FlatIsNestedWithoutCalls : Prop :=
  ∀ (G : Guards) (K : Checks) (P : Params) (tx : Tx) (S : State), G.sendLock = true →
    (tx.isClaim = true → G.claimLock = true) → execN G K P (liftTx tx) S = exec K P tx S

/-- **A HELD LOCK BLOCKS SENDS AND CLAIMS.** With the deployed locks, from any state whose lock
slot holds `2` (inside a send or claim), every send and claim reverts. -/
def Properties.HeldLockBlocksSendsAndClaims : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), S.lock = 2 →
    (∀ inp cbs dcb, execN deployedGuards K P (.send inp cbs dcb) S = none) ∧
    (∀ c r cb, execN deployedGuards K P (.claimProtocolFees c r cb) S = none) ∧
    (∀ c r z, execN deployedGuards K P (.claimZKFees c r z) S = none)

/-- On the witness chain, after `initL2`, a fee setting and one send credit coinbase `0x77` with
`6`, a send whose indirect call re-enters `claimProtocolFees` for `0x77`: the deployed code reverts
it; without the claims' lock the nested claim pays `6` and the send succeeds, ending with accrued
fees `6` and a balance `6`. -/
def Properties.NestedClaimInsideSendWitness : Prop :=
  ∃ S S', ReachN deployedGuards deployed wP init S ∧ ReachN withoutClaimLock deployed wP init S ∧
    S.protocolFees 0x77 = 6 ∧
    execN deployedGuards deployed wP wSendWithNestedClaim S = none ∧
    execN withoutClaimLock deployed wP wSendWithNestedClaim S = some S' ∧
    S'.claims.length = 1 ∧ S'.protocolFees 0x77 = 6 ∧ S'.bal = 6 ∧
    ReachN withoutClaimLock deployed wP init S'

end Contracts.InteropCenter.FeeState.Reentry
