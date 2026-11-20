import EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryLimitsFaithful

/-!
# Properties: the refund loop's external call at `draft/v0.35.0`

Statements about `EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryLimitsFaithful` (era-contracts
`b17415d20`). Proofs are in `EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryLimitsFaithful`. The
statements about the pin's loop (`c67894b9`, which called each call's `to`) are records in
`History/Properties/RecoveryLimitsFaithful.lean`.

* **One call.** A call to an account that runs no code returns no data and changes nothing
  (`CodelessCallReturnsNoData`). Fewer than 32 bytes do not decode as a `bool`
  (`ShortReturnDataDoesNotDecode`), and a well-formed `bool` decodes whatever follows it
  (`AbiBoolDecodes`).
* **The loop.** The claim reads the source chain's code at the router only
  (`V35ClaimReadsOnlyRouterCode`), calls nothing for a zero-value call whose `from` is not the
  router (`V35SkipsZeroValueNonRouterCalls`), succeeds when the router conforms and the base-token
  refund does not revert (`V35ClaimSucceedsWithConformingRouter`), and rejects an L1 destination
  (`V35ClaimRejectsL1Destination`).

Witnesses: `DecodeBoolWitness`, `V35ClaimWitness` (a direct call that carries value),
`V35ClaimSucceedsOnMixedBundle` (a router call and a zero-value direct call to an address that runs
no code). No property takes a hash premise: the claim is stated for the bundle presented.
-/

namespace Contracts.AtomicFlowManager.RecoveryLimitsFaithful

open AttackVectors.RecoveryLimits (Outcome ClaimAccepted)
open Contracts.InteropCenter (Address Word InteropCall Bundle CallStarter Dispatch FormsCall
  FormedBy)

/-! ## One call -/

/-- **AN ACCOUNT THAT RUNS NO CODE RETURNS NO DATA AND CHANGES NOTHING** (`VM-CALL`). Witnessed by
`DecodeBoolWitness`. -/
def Properties.CodelessCallReturnsNoData : Prop :=
  ∀ (W : Type) (S : SourceChain W) (w : W) (a : Address) (dest : Word) (data : List UInt8),
    S.runsCode w a = false → S.call w a dest data = .returned [] w

/-- **FEWER THAN 32 BYTES DO NOT DECODE AS A `bool`**, so a caller expecting one reverts. Witnessed
by `DecodeBoolWitness`. -/
def Properties.ShortReturnDataDoesNotDecode : Prop :=
  ∀ rd : List UInt8, rd.length < 32 → decodeBool rd = none

/-- **A WELL-FORMED `bool` DECODES, WHATEVER FOLLOWS IT.** -/
def Properties.AbiBoolDecodes : Prop :=
  ∀ (b : Bool) (rest : List UInt8), decodeBool (abiBool b ++ rest) = some b

/-- **THE DECODER'S PREMISES ARE MET.** On `wSource` the account `5` runs no code, and the call of
`recoverAtomicCall` on it returns the empty return data, which is shorter than 32 bytes and does
not decode. A 32-byte word other than `0` or `1` does not decode either, and a `true` word followed
by one more byte decodes as `true`. -/
def Properties.DecodeBoolWitness : Prop :=
  wSource.runsCode () 5 = false
  ∧ wSource.call () 5 325 [] = .returned [] ()
  ∧ ([] : List UInt8).length < 32
  ∧ decodeBool [] = none
  ∧ decodeBool (List.replicate 32 7) = none
  ∧ decodeBool (abiBool true ++ [7]) = some true

/-! ## The loop at `draft/v0.35.0` (b17415d) -/

/-- **THE `draft/v0.35.0` CLAIM READS THE SOURCE CHAIN'S CODE AT THE ROUTER ONLY.** Two source
chains that agree at the router give the same claim, whatever the source-chain parameter `S` runs
at any other address. That includes every call's `to`, and the `from` of every call not sent by the
router. The base-token refund step `baseRecover` is held fixed: in the contract it calls further
contracts (the base token, the asset tracker), and this statement says nothing about them. The
independence from `S` off the router holds by how `v35Step` is built. Witnessed by
`V35ClaimSucceedsOnMixedBundle` (any `S'` agreeing with `wSource` at the router) and by the History
witness `DirectTargetCodeDecidesOnlyThePinnedClaim`. -/
def Properties.V35ClaimReadsOnlyRouterCode : Prop :=
  ∀ (W : Type) (S S' : SourceChain W) (router : Address) (l1ChainId : Word)
    (baseRecover : W → Word → Word → Address → ℕ → Option W) (s : LegState) (w : W) (b : Bundle),
    (∀ w, S.runsCode w router = S'.runsCode w router) →
    (∀ w dest data, S.exec w router dest data = S'.exec w router dest data) →
      claimRefundV35 S router l1ChainId baseRecover s w b
        = claimRefundV35 S' router l1ChainId baseRecover s w b

/-- **A ZERO-VALUE CALL NOT SENT BY THE ROUTER CALLS NOTHING.** At `draft/v0.35.0`, the loop's step
for a call whose `from` is not the router and whose `value` is `0` leaves the world as it was.
Witnessed by `V35ClaimWitness`. -/
def Properties.V35SkipsZeroValueNonRouterCalls : Prop :=
  ∀ (W : Type) (S : SourceChain W) (router : Address)
    (baseRecover : W → Word → Word → Address → ℕ → Option W) (dest baseAsset : Word) (w : W)
    (c : InteropCall),
    c.fromAddr ≠ router → c.value = 0 → v35Step S router baseRecover dest baseAsset w c = some w

/-- **CONFORMING CODE AT THE ROUTER IS ENOUGH AT `draft/v0.35.0`.** If the router's code runs and
answers every call with a well-formed `bool`, the base-token refund never reverts, and the
destination is not L1, the claim of a `Revertable` leg succeeds, whatever the bundle's calls and
whatever runs at any other address. No call needs to recover. Witnessed by `V35ClaimWitness`. -/
def Properties.V35ClaimSucceedsWithConformingRouter : Prop :=
  ∀ (W : Type) (S : SourceChain W) (router : Address) (l1ChainId : Word)
    (baseRecover : W → Word → Word → Address → ℕ → Option W) (w : W) (b : Bundle),
    b.destinationChainId ≠ l1ChainId → Conforms S router →
    (∀ w dest asset receiver amount, (baseRecover w dest asset receiver amount).isSome = true) →
      ∃ w', claimRefundV35 S router l1ChainId baseRecover .Revertable w b = some (.Reverted, w')

/-- **THE `draft/v0.35.0` CLAIM REJECTS AN L1 DESTINATION** (`RecoverToL1NotSupported`,
`AtomicFlowManager.sol:299` at `b17415d20`), from every leg state and in every world. Witnessed by
`V35ClaimWitness`. -/
def Properties.V35ClaimRejectsL1Destination : Prop :=
  ∀ (W : Type) (S : SourceChain W) (router : Address) (l1ChainId : Word)
    (baseRecover : W → Word → Word → Address → ℕ → Option W) (s : LegState) (w : W) (b : Bundle),
    b.destinationChainId = l1ChainId → claimRefundV35 S router l1ChainId baseRecover s w b = none

/-- **THE `draft/v0.35.0` PREMISES ARE MET, WITH A VALUE-CARRYING DIRECT CALL.** The world is a
counter of refunded base token. The router `9` conforms on `wSourceOver ℕ`, and the base-token
refund adds its amount to the counter and never reverts. The bundle `wValueBundle` goes to chain
`325`, not to L1. Its claim succeeds and refunds the direct call's value `3`. The zero-value direct
call `wDirectCall` is skipped. The same bundle sent to L1 is rejected. -/
def Properties.V35ClaimWitness : Prop :=
  wValueBundle.destinationChainId ≠ wL1
  ∧ Conforms (wSourceOver ℕ) 9
  ∧ (∀ w dest asset receiver amount, (wBaseRecover w dest asset receiver amount).isSome = true)
  ∧ claimRefundV35 (wSourceOver ℕ) 9 wL1 wBaseRecover .Revertable 0 wValueBundle
      = some (.Reverted, 3)
  ∧ wDirectCall.fromAddr ≠ 9 ∧ wDirectCall.value = 0
  ∧ v35Step (wSourceOver ℕ) 9 wBaseRecover 325 1 4 wDirectCall = some 4
  ∧ claimRefundV35 (wSourceOver ℕ) 9 wL1 wBaseRecover .Revertable 0
      { wValueBundle with destinationChainId := wL1 } = none

/-- **THE `draft/v0.35.0` CLAIM OF THE TWO-CALL BUNDLE SUCCEEDS ON `wSource`**, whatever the
base-token refund would do. The bundle carries no value, so that refund is never called. On the
same source chain every claim of that bundle under the pin's loop reverts
(`History.Properties.DirectCallWithoutSourceCodeBlocksClaimWitness`). -/
def Properties.V35ClaimSucceedsOnMixedBundle : Prop :=
  ∀ baseRecover : Unit → Word → Word → Address → ℕ → Option Unit,
    claimRefundV35 wSource 9 wL1 baseRecover .Revertable () mixD.bundle = some (.Reverted, ())

end Contracts.AtomicFlowManager.RecoveryLimitsFaithful
