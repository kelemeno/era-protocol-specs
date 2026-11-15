import Mathlib.Tactic

/-!
# Proof polarity, with the DECLARED source chain kept apart from the REAL one

`AttackVectors.ProofPolarity` writes a leg's chain as one value, `srcOf v` (the chain
baked into the commit value), and reads the refund-path pin `c = srcOf v` as "the
leg's declared chain".  The pinned contract keeps two values there, and nothing on
the send path ties them together.  This file models both, and the results in
`../Properties/ProofPolarityFaithful.lean` say what follows.

## What the pinned source does (era-contracts `c67894b9`)

* `InteropCenter._dispatchBundle` (`interop/InteropCenter.sol:644-655`) computes
  `bundleHash = encodeInteropBundleHash(block.chainid, abi.encode(_bundle))` and calls
  `append({_flowId: _atomicSend.flowId, ...})` with the sender-chosen `flowId`.
* `AtomicFlowManager.append` (`atomic-interop/AtomicFlowManager.sol:87-102`) checks
  only `_state[_flowId][_bundleHash] == Unset`, then inserts
  `commitValue(_flowId, _bundleHash)`.  It never reads the flow's
  `legSourceChainIds`, which `IAtomicInterop.sol:71-72` documents as "aligned 1:1 ...
  May repeat and need not be ascending".  So a leg can be committed on chain `S`
  under a flow that declares chain `X ≠ S` for it.
* `requireFlowFinalized` (`AtomicFlowManager.sol:122-129`), per leg: check A
  `if (_finality.proofs[i].sourceChainId != flow.legSourceChainIds[i]) revert
  ProofSourceChainMismatch(...)`, then `verifyInclusion` against the tree of chain
  `proofs[i].sourceChainId`.
* `authorizeRefund` (`AtomicFlowManager.sol:142-151`): check B
  `if (_absence.sourceChainId != missingLegChainId) revert ProofSourceChainMismatch(...)`
  with `missingLegChainId = _flow.legSourceChainIds[_missingLegIndex]`, then
  `verifyTimeoutAbsence` against the tree of that chain; then every leg this chain
  committed is marked `Revertable` (`:155-161`) and `claimRefund` (`:165-180`) pays it.

So both gates pin the proof to the DECLARED chain `legSourceChainIds[i]`; the real
source chain (`block.chainid` at dispatch, inside `bundleHash`) is a different
value.  The source comment at `AtomicFlowManager.sol:117-119` ("defense-in-depth here
(membership already self-binds via the chain-specific `commitValue`)") reads the two
as one.

The upgrade tree (era-contracts `e561b9cc2`) adds the missing binding:
`AtomicFlowManager.append` (`:125-145`) reverts with
`ManagerCommittedLegSourceChainMismatch` unless
`_flowPreimage.legSourceChainIds[legIndex] == block.chainid`.

## The model

* `srcOf v` — the chain baked into commit value `v` (as in `ProofPolarity`).
* `decl v` — the chain the flow's `legSourceChainIds` assigns to the leg whose commit
  value is `v`.  Modelling it as a function of `v` assumes that the leg's bundle hash
  occurs at ONE position of the flow, so that the position and hence the declared chain
  are determined.  At the pin this is enforced on the gates, not on the send path:
  `_checkFlowId` (`AtomicFlowManager.sol:247-259`), called by `requireFlowFinalized` and
  `authorizeRefund`, reverts with `ManagerBundleHashesNotSorted` unless
  `legBundleHashes` is strictly ascending, so a flow preimage that passes a gate has no
  repeated bundle hash; `append` (`:87-102`) reads no preimage at all.  Beyond that it
  rests on the same keccak idealization that makes `srcOf` a function
  (`v = keccak(TAG, flowId, bundleHash)`, and `flowId` hashes the leg list, so two
  preimages with one `flowId` are a collision).  A model indexed by leg position would
  not need either; the results here do not depend on which `decl` is chosen, only on
  its value at the legs they mention.
* `tree c` — the set of commit values in chain `c`'s IMT.
* `appendAt`, `PinnedReach`, `UpgradeReach` — the commitment states honest chains
  reach under the pinned and the upgraded `append`.
* `FinalityChecked` / `FinalityUnchecked` — one leg of `requireFlowFinalized` with
  and without check A; `RefundChecked` — `authorizeRefund` for the missing leg
  (check B is present at both pins and is never dropped here).

**This file is definitions only.**
-/

namespace AttackVectors.ProofPolarityFaithful

variable {Chain Value : Type}

/-- **HONEST INSERTION**, as in `ProofPolarity`: every value in chain `c`'s tree was
committed BY chain `c` (its bundle hash bakes in `c`). -/
def HonestInsertion (srcOf : Value → Chain) (tree : Chain → Set Value) : Prop :=
  ∀ c v, v ∈ tree c → srcOf v = c

/-- **DECLARED INSERTION**: every value in chain `c`'s tree belongs to a leg its flow
DECLARES on chain `c`.  This is the binding the upgrade's `append` enforces
(`legSourceChainIds[legIndex] == block.chainid`); the pinned `append` does not. -/
def DeclaredInsertion (decl : Value → Chain) (tree : Chain → Set Value) : Prop :=
  ∀ c v, v ∈ tree c → decl v = c

/-- The commitment state after chain `c` inserts `v` into its own tree. -/
def appendAt (tree : Chain → Set Value) (c : Chain) (v : Value) : Chain → Set Value :=
  fun c' => {w | w ∈ tree c' ∨ (c' = c ∧ w = v)}

/-- The states honest chains reach under the PINNED `append`: chain `c` inserts a
commit value whose bundle hash it computed with its own `block.chainid`
(`srcOf v = c`), under any sender-chosen flow, so with no condition on `decl v`. -/
inductive PinnedReach (srcOf : Value → Chain) : (Chain → Set Value) → Prop
  | genesis : PinnedReach srcOf (fun _ => ∅)
  | append {tree : Chain → Set Value} (c : Chain) (v : Value) :
      PinnedReach srcOf tree → srcOf v = c → PinnedReach srcOf (appendAt tree c v)

/-- The states honest chains reach under the UPGRADED `append`, which also requires
the leg to be declared on the committing chain (`decl v = c`). -/
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

/-- Some leg of the flow passes `authorizeRefund`; its source chain then marks it
`Revertable` and `claimRefund` pays it. -/
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
