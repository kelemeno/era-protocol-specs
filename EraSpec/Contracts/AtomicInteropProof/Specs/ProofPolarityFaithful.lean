import Mathlib.Tactic

/-!
# Proof polarity, with the DECLARED source chain kept apart from the REAL one

`AttackVectors.ProofPolarity` writes a leg's chain as one value, `srcOf v` (the chain
baked into the commit value), and reads the refund-path pin `c = srcOf v` as "the
leg's declared chain".  The contract keeps two values there.  This file models both, and the
results in `../Properties/ProofPolarityFaithful.lean` say what follows.

## What the source does (era-contracts `b17415d20`)

Paths are under `l1-contracts/contracts/`.

* `InteropCenter._dispatchBundle` (`interop/InteropCenter.sol:727-750`) computes
  `bundleHash = keccak256(abi.encode(bundle))` (`:690-692`), with `bundle.sourceChainId =
  block.chainid` (`:634`), and calls `append` with the sender's flow preimage (`:742-746`).
* `AtomicFlowManager.append` (`atomic-interop/AtomicFlowManager.sol:104-173`) finds the leg
  whose bundle hash is `_bundleHash` (`:130-139`) and reverts with
  `ManagerCommittedLegSourceChainMismatch` unless that leg's declared chain
  `legSourceChainIds[legIndex]` is `block.chainid` (`:140-146`); then it checks the leg is
  `Unset` and inserts `commitValue(flowId, _bundleHash)` (`:162-170`).  So a leg is committed
  only on the chain its flow declares for it.
* `requireFlowFinalized` (`:176-213`), per leg: check A
  `if (_finality.proofs[i].sourceChainId != preimage.legSourceChainIds[i]) revert
  ProofSourceChainMismatch(...)` (`:198-200`), then `verifyInclusion` against the tree of
  chain `proofs[i].sourceChainId` (`:203-208`).
* `authorizeRefund` (`:216-247`): check B
  `if (_absence.sourceChainId != missingLegChainId) revert ProofSourceChainMismatch(...)`
  (`:228-230`) with `missingLegChainId = preimage.legSourceChainIds[_missingLegIndex]`, then
  `verifyTimeoutAbsence` against the tree of that chain (`:233-234`); then every leg of the flow
  that this chain committed is marked `Revertable` (`:236-246`), whichever leg was proved missing.

Both gates pin the proof to the DECLARED chain `legSourceChainIds[i]`; the real source chain
(`block.chainid` at dispatch, inside `bundleHash`) is a different value, and `append` is what ties
them.  The source comment at `AtomicFlowManager.sol:191-192` ("defense-in-depth here (inclusion
self-binds via the chain-specific commit value)") reads the two as one, which `append`'s binding
makes true on trees it wrote.

At the extraction pin `c67894b9` `append` did not read `legSourceChainIds` at all, so a leg could be
committed on chain `S` under a flow declaring `X ≠ S`.  That pinned `append` and what it reaches
are the History record `../History/Specs/ProofPolarityFaithful.lean` (H1).

## The model

* `srcOf v` — the chain baked into commit value `v` (as in `ProofPolarity`).
* `decl v` — the chain the flow's `legSourceChainIds` assigns to the leg whose commit
  value is `v`.  Modelling it as a function of `v` assumes that the leg's bundle hash
  occurs at ONE position of the flow, so that the position and hence the declared chain
  are determined.  `_validateAndComputeFlowId` (`:360-379`), run by `append`, `requireFlowFinalized`
  and `authorizeRefund`, reverts with `ManagerBundleHashesNotSorted` unless `legBundleHashes` is
  strictly ascending (`:371-373`), so a flow preimage that passes has no repeated bundle hash.
  Beyond that it rests on the same keccak idealization that makes `srcOf` a function
  (`v = keccak(TAG, flowId, bundleHash)`, and `flowId` hashes the leg list, so two
  preimages with one `flowId` are a collision).  A model indexed by leg position would
  not need either; the results here do not depend on which `decl` is chosen, only on
  its value at the legs they mention.
* `tree c` — the set of commit values in chain `c`'s IMT.
* `appendAt`, `UpgradeReach` — the commitment states honest chains reach under the binding
  `append` of `b17415d20` (named for the upgrade tree `e561b9cc2` that introduced it).
* `FinalityChecked` / `FinalityUnchecked` — one leg of `requireFlowFinalized` with
  and without check A; `RefundChecked` — `authorizeRefund` for the missing leg
  (check B is never dropped here).

Model boundaries.  A proof is identified with the set fact it proves (`v ∈ tree c`,
`v ∉ tree c`), and each chain has ONE timeless tree.  On chain the finality gate reads
the batch-END IMT root of an on-time batch (`atomic-interop/libraries/AtomicInteropProof.sol:44-68`),
and the refund gate the BEGIN root of a late batch or the END root of the last in-time batch of
a post-deadline root (`:77-124`): different snapshots, each read through an IMT proof.
Those snapshots, the deadline and timeout branches (`TimeoutSoundness`,
`StaleSnapshotBranches`), the Merkle authentication of roots and the IMT proofs
themselves are not modelled here.

**This file is definitions only.**
-/

namespace AttackVectors.ProofPolarityFaithful

variable {Chain Value : Type}

/-- **HONEST INSERTION**, as in `ProofPolarity`: every value in chain `c`'s tree was
committed BY chain `c` (its bundle hash bakes in `c`). -/
def HonestInsertion (srcOf : Value → Chain) (tree : Chain → Set Value) : Prop :=
  ∀ c v, v ∈ tree c → srcOf v = c

/-- **DECLARED INSERTION**: every value in chain `c`'s tree belongs to a leg its flow
DECLARES on chain `c`.  This is the binding the `b17415d20` `append` enforces
(`legSourceChainIds[legIndex] == block.chainid`); the extraction pin's `append` did not (History). -/
def DeclaredInsertion (decl : Value → Chain) (tree : Chain → Set Value) : Prop :=
  ∀ c v, v ∈ tree c → decl v = c

/-- The commitment state after chain `c` inserts `v` into its own tree. -/
def appendAt (tree : Chain → Set Value) (c : Chain) (v : Value) : Chain → Set Value :=
  fun c' => {w | w ∈ tree c' ∨ (c' = c ∧ w = v)}

/-- The states honest chains reach under the `b17415d20` `append`
(`AtomicFlowManager.sol:140-146`; first introduced in the upgrade tree `e561b9cc2`, hence the
name), which requires the leg to be declared on the committing chain (`decl v = c`).

Scope: it starts from empty trees, so it covers histories in which every tree was
written only by the binding `append` (for example a fresh deployment).  Values from a
binding-free `append`, if any chain carries them, are outside it, and check A stays
load-bearing for flows that use them. -/
inductive UpgradeReach (srcOf decl : Value → Chain) : (Chain → Set Value) → Prop
  | genesis : UpgradeReach srcOf decl (fun _ => ∅)
  | append {tree : Chain → Set Value} (c : Chain) (v : Value) :
      UpgradeReach srcOf decl tree → srcOf v = c → decl v = c →
      UpgradeReach srcOf decl (appendAt tree c v)

/-- One leg of `requireFlowFinalized` as deployed: the proof names chain `c`, check A
forces `c` to be the leg's DECLARED chain, and membership is checked in `c`'s tree. -/
def FinalityChecked (decl : Value → Chain) (tree : Chain → Set Value) (v : Value) (c : Chain) :
    Prop :=
  c = decl v ∧ v ∈ tree c

/-- The same leg with check A removed — the reading under which the source comment
calls that check "defense-in-depth". -/
def FinalityUnchecked (tree : Chain → Set Value) (v : Value) (c : Chain) : Prop :=
  v ∈ tree c

/-- `authorizeRefund` for missing leg `v`: check B pins the absence proof to the leg's
DECLARED chain, and absence is checked in that chain's tree. -/
def RefundChecked (decl : Value → Chain) (tree : Chain → Set Value) (v : Value) (c : Chain) :
    Prop :=
  c = decl v ∧ v ∉ tree c

/-- `requireFlowFinalized` over a whole leg list, as deployed: the proof for leg `v`
names chain `pc v`, and every leg passes. -/
def FlowFinalizedChecked (decl : Value → Chain) (tree : Chain → Set Value) (legs : List Value)
    (pc : Value → Chain) : Prop :=
  ∀ v ∈ legs, FinalityChecked decl tree v (pc v)

/-- The flow gate with check A removed. -/
def FlowFinalizedUnchecked (tree : Chain → Set Value) (legs : List Value) (pc : Value → Chain) :
    Prop :=
  ∀ v ∈ legs, FinalityUnchecked tree v (pc v)

/-- Some leg of the flow passes `authorizeRefund` as the missing leg.  The chain running
`authorizeRefund` then marks every leg it committed under the flow `Revertable`
(`AtomicFlowManager.sol:153-161`), whether or not that leg is the one proved missing. -/
def FlowRefunded (decl : Value → Chain) (tree : Chain → Set Value) (legs : List Value) : Prop :=
  ∃ v ∈ legs, ∃ c, RefundChecked decl tree v c

/-! ## The concrete countermodel

Two chains (`true` is the real source `S`, `false` the declared chain `X`) and one leg
value.  `S` commits the leg under a flow that declares `X`; the pinned `append`
accepts that. -/

/-- The real source of the single leg: chain `true`. -/
def cmSrc : Unit → Bool := fun _ => true

/-- The chain the flow declares for it: chain `false`. -/
def cmDecl : Unit → Bool := fun _ => false

/-- The state after chain `true` commits the leg. -/
def cmTree : Bool → Set Unit := appendAt (fun _ => ∅) true ()

end AttackVectors.ProofPolarityFaithful
