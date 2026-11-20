import EraSpec.Contracts.InteropHandlerBase.Specs.Reentrancy

/-!
# Model: which entry-point calls consult the inclusion proof or the flow gate

Source: era-contracts `draft/v0.35.0` at `b17415d20`, `l1-contracts/contracts/interop/interop-handler/`
(`IHB` = `InteropHandlerBase.sol`, `L1` = `L1InteropHandler.sol`, `L2` = `L2InteropHandler.sol`).

**This file is definitions only.** The statements are in
`EraSpec.Contracts.InteropHandlerBase.Properties.BundleStatusMachineFaithful` and are proved in
`EraSpec.Contracts.InteropHandlerBase.Proofs.BundleStatusMachineFaithful`.

## What is modelled

Gate predicates over the engine `Contracts.InteropHandler.exec` (topic `Reentrancy`: re-entrant,
every target behaviour, every depth), whose entry points carry their verdict as an input bit:

* `ProvesInclusion h e`: entry-point call `e` is the engine's `executeBundle` or `verifyBundle` of a
  bundle with hash `h` with verdict `true`. At `b17415d20` that is L1's message-inclusion check
  (`_verifyBundle`, `L1:203-224`: the sender check `:213-216` and `_proveInclusion` `:221`), reached
  from `executeBundle` for an `Unreceived` bundle (`L1:92-95`) and from `verifyBundle` (`L1:109`).
* `PassesFlowGate h e`: `e` is the engine's `executeAtomicBundle` of a bundle with hash `h` whose
  `requireFlowFinalized` verdict is `true`.
* `TxAll P t`: every entry-point call of transaction `t`, its own and every one its targets make at
  any depth, satisfies `P`.

The engine's entry points are `b17415d20`'s through the translation of topic `Reentrancy`
(`EntryAtV35.toPin`): both layers' `execute` and `verify` become the engine's `executeBundle` and
`verifyBundle` carrying the layer's verdict (on L2 the flow gate's, `L2:73-75`, `:89`), so at
`b17415d20` the verdict of `ProvesInclusion` is the layer's gate. The engine's
`executeAtomicBundle` is the pin `c67894b9`'s L2 entry point; the statements that rest on its
pin-only behaviour, and the labelled machine of the pin's edges, are in
`History/{Specs,Properties,Proofs}/BundleStatusMachineFaithful.lean`. The `b17415d20` gate
statement built on this file is `Reentrancy`'s `DeliveryNeedsTheGateAtV35`.
-/



namespace Contracts.InteropHandler.Faithful

open AttackVectors.BundleStatusMachine (Status)

/-- Every entry-point call a target makes, at every depth, satisfies `P`. -/
inductive CalleeAll (P : Entry → Prop) : Callee → Prop
  | returns : CalleeAll P .returns
  | reverts : CalleeAll P .reverts
  | calls {e : Entry} {inner : List Callee} {caught : Bool} {next : Callee} :
      P e → (∀ c ∈ inner, CalleeAll P c) → CalleeAll P next →
        CalleeAll P (.calls e inner caught next)

/-- Every entry-point call of transaction `t` satisfies `P`: its own entry, and every one its
targets make, at every depth. -/
def TxAll (P : Entry → Prop) (t : Tx) : Prop :=
  P t.entry ∧ ∀ c ∈ t.callees, CalleeAll P c

/-- Entry-point call `e` presents a proof its layer's gate accepts for a bundle with hash `h`:
`executeBundle` or `verifyBundle` of such a bundle with verdict `true`. On L1 at `b17415d20` that verdict
is `_verifyBundle` (`L1:203-224`, `_proveInclusion` at `L1:221`), reached from `executeBundle` for an
`Unreceived` bundle (`L1:92-95`) and from `verifyBundle` (`L1:109`); on L2 it is the flow gate
(`L2:74`, `L2:89`) through `EntryAtV35.toPin`. -/
def ProvesInclusion (h : BundleHash) : Entry → Prop
  | .executeBundle b ok => b.hash = h ∧ ok = true
  | .verifyBundle b ok => b.hash = h ∧ ok = true
  | .unbundleBundle _ _ => False
  | .executeAtomicBundle _ _ => False

/-- Entry-point call `e` passes the atomicity gate for hash `h`: the engine's `executeAtomicBundle` of
a bundle with that hash whose `requireFlowFinalized` verdict is `true`. This constructor is the pin's
(`c67894b9`) separate atomic entry point and its gate line there; no `b17415d20` entry translates to it
(`EntryAtV35.toPin`). At `b17415d20` the `requireFlowFinalized` calls are `L2:74` (`executeAtomicBundle`,
skipped for an already `Verified` bundle) and `L2:89` (`verifyAtomicBundle`), and they are carried as the
verdict of `ProvesInclusion`'s entries. -/
def PassesFlowGate (h : BundleHash) : Entry → Prop
  | .executeAtomicBundle b ok => b.hash = h ∧ ok = true
  | .executeBundle _ _ => False
  | .verifyBundle _ _ => False
  | .unbundleBundle _ _ => False

/-- `executeBundle(b)` with an accepted inclusion proof, every target returning. -/
def freshPublicRun (b : Bundle) : Tx :=
  ⟨b.calls + 2, .executeBundle b true, List.replicate b.calls .returns⟩

/-- `executeBundle(b)` with no accepted proof, every target returning. -/
def provelessPublicRun (b : Bundle) : Tx :=
  ⟨b.calls + 2, .executeBundle b false, List.replicate b.calls .returns⟩

/-! ## Witness data -/

/-- `unbundleBundle` of `wC` (bundle `3`, one call) executing its call, the target returning. -/
def wUnbundleC : Tx := ⟨4, .unbundleBundle wC [.Executed], []⟩

/-- `executeBundle` of `wC` with no accepted proof. -/
def wProvelessC : Tx := ⟨4, .executeBundle wC false, []⟩

/-- `executeBundle` of `wC` with an accepted proof. -/
def wFreshC : Tx := ⟨4, .executeBundle wC true, []⟩

/-- `executeAtomicBundle` of `wC` with a passing flow gate. -/
def wAtomicC : Tx := ⟨4, .executeAtomicBundle wC true, []⟩

end Contracts.InteropHandler.Faithful
