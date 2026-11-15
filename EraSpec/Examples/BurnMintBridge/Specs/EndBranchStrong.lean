import EraSpec.Examples.BurnMintBridge.Specs.EndBranch

/-!
# Spec: definitions for the pinned END-branch witnesses

Definitions used by `../Properties/EndBranchStrong.lean`; proofs in
`../Proofs/EndBranchStrong.lean`.

* `endFormEvidence` is the §1 END-form mirror of the adapter's `evidence`: the same
  finalization, and refunds on the abstract END form only (`MissingEnd` in place of
  `Missing`). Its recovery is the second disjunct of `evidenceEither`'s. Unlike
  `beginOnlyEvidence` (in `EndBranch.lean`), which accepts refunds on the BEGIN branch as run
  only, it pins no branch: in §1 every `MissingEnd` is a `Missing`
  (`MissingEndImpliesMissing`).
* `splitHistory`, `chainOneLeg`, `gapTransfer` and `splitFlow` form a two-chain instance. On
  it, the unpinned `Properties.BeginBranchRefundWitness` holds through a run that refunds a
  different transfer, authorized by the END branch only.
* `twoRootHistory`, `earlyRoot`, `laterRoot` and `twoRoots` form an instance with two imported
  roots and one clock for every chain. Against one root the demo leg has an END-branch
  timeout, against the other a BEGIN-branch timeout.

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

/-! ## Two imported roots for one leg

`twoRootHistory` settles batch `0` at time `0`, batch `1` at time `2` and every later batch at
time `5`, on every chain, and never commits a value.  `earlyRoot` is created at time `1` and
holds batch `0`; `laterRoot` is created at time `3` and holds batches `0` and `1`.  Each holds
exactly the batches that settled by its creation.  For the demo leg (deadline `0`) the last
batch of `earlyRoot`, `0`, is in time: an END-branch timeout.  Batch `1` is late and inside
`laterRoot`: a BEGIN-branch timeout. -/

/-- Batch `0` at time `0`, batch `1` at time `2`, later batches at time `5`. -/
def twoRootTime (n : ℕ) : UInt256 := if n = 0 then 0 else if n = 1 then 2 else 5

/-- Every chain on `twoRootTime`; every snapshot is the genesis leaf set. -/
def twoRootHistory : History where
  tree := fun _ _ => {⟨0, 0⟩}
  settledAt := fun _ n => twoRootTime n

/-- Created at time `1`, after the demo deadline `0`; holds every chain's batch `0`. -/
def earlyRoot : Contracts.Timeout.SlRoot where
  created := 1
  upTo := fun _ => 0

/-- Created at time `3`; holds every chain's batches `0` and `1`. -/
def laterRoot : Contracts.Timeout.SlRoot where
  created := 3
  upTo := fun _ => 1

/-- Root `0` is `earlyRoot`; every other root is `laterRoot`. -/
def twoRoots : Roots := fun k => if k = 0 then earlyRoot else laterRoot

end Applications.BurnMintBridge.EndBranch
