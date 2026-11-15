import EraSpec.Examples.BurnMintBridge.Specs.EndBranch

/-!
# Spec: definitions for the pinned END-branch witnesses

Definitions used by `../Properties/EndBranchStrong.lean`; proofs in
`../Proofs/EndBranchStrong.lean`.

* `endFormEvidence` is the adapter's evidence with refunds on the abstract END form only. It
  is the second disjunct of `evidenceEither`'s recovery, and the §1 counterpart of
  `beginOnlyEvidence` (in `EndBranch.lean`).
* `splitHistory`, `chainOneLeg`, `gapTransfer` and `splitFlow` form a two-chain instance. On
  it, the unpinned `Properties.BeginBranchRefundWitness` holds through a run that refunds a
  different transfer, authorized by the END branch only.

**This file is definitions only.**
-/

namespace Applications.BurnMintBridge.EndBranch

open IMTAbstract Properties.PreparedBridge

/-- **REFUNDS ON THE ABSTRACT END FORM ONLY.**  Execution needs every prerequisite on time, as in
`evidenceEither`.  Recovery needs one prerequisite with a `MissingEnd`, not the adapter's
successor-pinned `Missing`.  Every run of this evidence is a run of `evidenceEither`, which
accepts a recovery on either form. -/
def endFormEvidence (H : History) (flow : Transfer → List Leg) : Evidence where
  finalize := fun i => ∀ l ∈ flow i, OnTime H l
  recover := fun i => ∃ l ∈ flow i, MissingEnd H l

/-! ## A second transfer, and a two-chain world

`splitHistory` runs chain `0` on the late clock and every other chain on the halted clock.
Chain `0` is therefore the BEGIN branch's world: batch `1` settles late, inside
`Contracts.Timeout.demoRoot`.  Every other chain is the END branch's world: batches `0` and `1`
are in time and every later batch is outside every imported root.  No chain ever commits a
value. -/

/-- A one-unit transfer distinct from `sampleTransfer` (another flow id). -/
def gapTransfer : Transfer := ⟨2, 1, 1⟩

/-- Chain `0` on `lateTime`, every other chain on `demoTime`; every snapshot is the genesis
leaf set. -/
def splitHistory : History where
  tree := fun _ _ => {⟨0, 0⟩}
  settledAt := fun c n => if c = 0 then lateTime n else demoTime n

/-- The leg on chain `1`: commit value `1`, deadline `0`. -/
def chainOneLeg : Leg := ⟨1, 1, 0⟩

/-- `sampleTransfer` needs `demoLeg` (chain `0`); every other transfer needs `chainOneLeg`
(chain `1`). -/
def splitFlow : Transfer → List Leg :=
  fun t => if t = sampleTransfer then [demoLeg] else [chainOneLeg]

end Applications.BurnMintBridge.EndBranch
