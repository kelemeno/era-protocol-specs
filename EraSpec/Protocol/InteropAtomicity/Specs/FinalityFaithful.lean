import EraSpec.Protocol.InteropAtomicity.Specs.Timeout

/-!
# Model: finalizability at a destination that has to authenticate the roots

`Contracts.Atomicity.LegFinalizableBy` says a leg CAN be finalized when there is an on-time
batch, a presentable IMT proof for it (`DataAvailable`), and IMT acceptance against that
batch's END root.  Its docstrings read that as "every leg's destination can run
`requireFlowFinalized` and pass".  The contract asks for more, on the destination's side.

**This file is definitions only.**  Statements are in
`EraSpec.Protocol.InteropAtomicity.Properties.FinalityFaithful`, proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.FinalityFaithful`.

## What the destination checks

`AtomicInteropProof.verifyInclusion` (`libraries/AtomicInteropProof.sol:113-139`, pin
`c67894b9`) first runs `_authenticateRoot` (`:256-290`):

* the leaf-to-batch-root section must be exactly `ChainBatchRootTree.TREE_DEPTH` long;
* `L2_MESSAGE_VERIFICATION.proveL2LeafInclusionShared` must accept the claimed IMT root as a
  leaf of the source chain's batch.  It recurses to the settlement layer and ends at
  `L2_INTEROP_ROOT_STORAGE.interopRoots(chainId, blockNumber).root`, which must be nonzero
  and equal (`interop/L2MessageVerification.sol:29-33`): the VERIFYING chain must already
  have imported a settlement-layer root that aggregates the source batch;
* a final-node (single-level) proof is rejected (`ProofMissingSettlementLayerBatch`), so the
  proof must be multi-hop.

None of this is in `LegFinalizableBy`.  `Access` is indexed by (source chain, batch, IMT
proof) only, so `DataAvailable` covers the honest IMT proofs and nothing about settlement
proofs or the destination's root storage.  The executed leg's own destination has passed
these checks; each sibling leg's destination needs its own imported root.

## What this file adds

* `Imports d R`: destination `d` holds the settlement-layer root `R` in
  `L2_INTEROP_ROOT_STORAGE`.  `CanAuthenticate I d c n`: `d` holds a root that aggregates
  chain `c`'s batch `n` (`n ≤ R.upTo c`).  This abstracts both the import and the existence
  of the multi-hop settlement proof through that root.
* `LegFinalizableAt` / `FlowFinalizableAt`: `LegFinalizableBy` / `FlowFinalizableBy` at a
  named destination, with `CanAuthenticate` for the batch used.
* `PostDeadlineRootAt S I d D`: the root-availability assumption, next to `DataAvailable`:
  `d` has imported a root created at or after the deadline that aggregates honestly
  (`Timeout.Aggregates`).  It is an assumption about the world (the destination keeps
  importing settlement-layer roots, and the settlement layer aggregates honestly), not a
  property of the contracts.

## Model boundary

Root import is modelled as a relation on the fixed history, with no time of import; that
the imported root is the one the settlement layer published is the same trust in the
settlement layer that `Timeout.Aggregates` already records.
-/

namespace Contracts.FinalityFaithful

open MerkleSpec Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout

/-- The settlement-layer roots each chain has imported: `I d R` says destination `d` holds
`R` in `L2_INTEROP_ROOT_STORAGE` (nonzero, so `proveL2LeafInclusionShared` can end there). -/
abbrev Imports := Chain → SlRoot → Prop

/-- **DESTINATION `d` CAN AUTHENTICATE CHAIN `c`'S BATCH `n`.**  It holds an imported root
that aggregates that batch, so a multi-hop settlement proof from the batch's IMT root to
that root exists and `_authenticateRoot` can pass. -/
def CanAuthenticate (I : Imports) (d c : Chain) (n : ℕ) : Prop :=
  ∃ R, I d R ∧ n ≤ R.upTo c

/-- **THE LEG CAN BE FINALIZED AT DESTINATION `d`.**  `LegFinalizableBy` plus the
destination-side condition: `d` can authenticate the batch the proof is against. -/
def LegFinalizableAt (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (S : System) (A : Access) (I : Imports) (d : Chain) (F : Flow) (leg : FlowLeg) : Prop :=
  ∃ (n : ℕ) (p : ImtProof),
    S.time leg.chain n ≤ F.deadline ∧ A leg.chain n p ∧ CanAuthenticate I d leg.chain n
      ∧ Accepts h z0 hl S leg.chain n (legValue cv F leg) p

/-- **`requireFlowFinalized` CAN PASS AT DESTINATION `d`.**  Every leg of the flow is
finalizable at `d`: the gate loops over all legs, on the destination it runs on. -/
def FlowFinalizableAt (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (S : System) (A : Access) (I : Imports) (d : Chain) (F : Flow) : Prop :=
  ∀ leg ∈ F.legs, LegFinalizableAt h z0 hl cv S A I d F leg

/-- **EXECUTED AT DESTINATION `d`.**  `ExecutedViaBy`, and `d` authenticated the root of
every batch its gate evidence used. -/
def ExecutedAtBy (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (I : Imports) (d : Chain) (F : Flow) (ev : GateEvidence) (leg : FlowLeg) : Prop :=
  ExecutedViaBy h z0 hl cv fh S F ev leg ∧ ∀ l ∈ F.legs, CanAuthenticate I d l.chain (ev l).1

/-- **THE ROOT-AVAILABILITY ASSUMPTION AT `d` FOR DEADLINE `D`.**  `d` has imported a
settlement-layer root created at or after `D` that aggregates honestly.  Stated next to
`DataAvailable`: an assumption about the world, which nothing in the protocol makes
true. -/
def PostDeadlineRootAt (S : System) (I : Imports) (d : Chain) (D : ℕ) : Prop :=
  ∃ R, I d R ∧ D ≤ R.created ∧ Aggregates S R

/-! ## Concrete configurations -/

/-- Every chain holds `setup; insert a; insert b` from batch 0 on, at height 2; batch
numbers are timestamps. -/
def everyChainSystem (a b : UInt256) : System where
  tree := fun _ _ => threeLeafTree a b
  time := fun _ n => n
  height := fun _ _ => 2

/-- A two-leg flow: bundle `1` from chain `0` and bundle `2` from chain `1`, deadline `0`.
With commit value `fun _ bh => bh`, the legs' values are `1` and `2`. -/
def twoChainFlow : Flow where
  flowId := 0
  legs := [⟨0, 1⟩, ⟨1, 2⟩]
  deadline := 0

/-- Destination `5` has imported `Timeout.timeOneRoot`; no other chain has imported
anything. -/
def importsAtFive : Imports := fun d R => d = 5 ∧ R = timeOneRoot

end Contracts.FinalityFaithful
