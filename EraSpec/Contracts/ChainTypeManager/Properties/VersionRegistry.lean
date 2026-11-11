import EraSpec.Contracts.ChainTypeManager.Specs.VersionRegistry

/-!
# Properties: the CTM's protocol version and transition registry

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.VersionRegistry`. Proofs are
in `EraSpec.Contracts.ChainTypeManager.Proofs.VersionRegistry`.

## What holds

* The current release is always the release of the current version
  (`CurrentReleaseIsVersionsRelease`), as the source claims at `ChainTypeManager.sol:162-163`
  ("always the release OF `protocolVersion`").
* The version never decreases, every version edge strictly increases it, and so a run
  containing an edge ends strictly higher (`VersionStrictlyIncreasesOnEdges`,
  `VersionsIncreaseAlongRuns`).
* Each `upgradeTransition[v]` is written by **at most one commit** in any run, and that
  commit finds it empty (`CommitWritesEachSlotOnce`, `CommitWritesOnlyEmptySlots`).
  It is **not** write-once outright: `replaceUpgradeTransition` rewrites a committed slot
  by design, and it is the only other writer (`OnlyCommitOrReplaceWritesSlots`;
  `VersionRegistryWitness` shows a replacement firing).
* Committed transitions chain: the transition in slot `v` departs from `R_v` and lands
  on `R_w` for a reached `w > v`, and the transition in slot `w`, if any, departs from
  that same `R_w` (`TransitionsChain`). This survives replacement.

## What needs more than the CTM checks

That the transition in slot `v` *reports* `oldProtocolVersion() = v` holds for a
committed transition (the commit checks it) but is not checked for a replacement:
`_requireSameDeparture` compares `fromRelease()` only. It holds when every replacement
is a genuine `CTMTransition` (`SlotsDepartFromTheirVersion`), and fails otherwise
(`NonGenuineReplacementBreaksSlotVersion`).
-/

namespace Contracts.ChainTypeManager

/-! ## Starting states -/

/-- **`initialize` ESTABLISHES THE INVARIANT.** -/
def Properties.InitSatisfiesInvariant : Prop :=
  ∀ (W : World) (R : Address), R ≠ 0 → CtmInv W (initState W R)

/-- **THE BOOTSTRAP ESTABLISHES THE INVARIANT.** A legacy CTM at `old` that crosses the
bootstrap edge to a genesis release `R` at a higher version is a registry CTM satisfying
the invariant. -/
def Properties.BootstrapSatisfiesInvariant : Prop :=
  ∀ (W : World) (old : ℕ) (R : Address), R ≠ 0 → old < W.relVersion R →
    CtmInv W (bootstrapState W old R)

/-- **EVERY WRITER PRESERVES THE INVARIANT.** -/
def Properties.StepPreservesInvariant : Prop :=
  ∀ (W : World) (s s' : CTM) (op : Op), CtmInv W s → CStep W s op s' → CtmInv W s'

/-! ## The current release -/

/-- **THE CTM'S CURRENT VERSION IS ITS CURRENT RELEASE'S VERSION.** Along every run from
an invariant state, `currentRelease` is nonzero and
`ICTMRelease(currentRelease).protocolVersion() == protocolVersion`. -/
def Properties.CurrentReleaseIsVersionsRelease : Prop :=
  ∀ (W : World) (s s' : CTM) (ops : List Op), CtmInv W s → CRun W s ops s' →
    s'.cur ≠ 0 ∧ W.relVersion s'.cur = s'.pv

/-! ## Versions only go up -/

/-- **NO WRITER LOWERS THE VERSION; EVERY EDGE RAISES IT.** Both commits go through
`_commitVersionEdge`, whose `_newProtocolVersion <= _oldProtocolVersion` check
(`ChainTypeManager.sol:537-539`) is what makes the increase strict. -/
def Properties.VersionStrictlyIncreasesOnEdges : Prop :=
  ∀ (W : World) (s s' : CTM) (op : Op), CStep W s op s' →
    s.pv ≤ s'.pv ∧ (op.isEdge = true → s.pv < s'.pv) ∧ (op.isEdge = false → s'.pv = s.pv)

/-- **ALONG ANY RUN THE VERSION ONLY GOES UP, STRICTLY IF THE RUN CROSSES AN EDGE.** -/
def Properties.VersionsIncreaseAlongRuns : Prop :=
  ∀ (W : World) (s s' : CTM) (ops : List Op), CRun W s ops s' →
    s.pv ≤ s'.pv ∧ (ops.any Op.isEdge = true → s.pv < s'.pv)

/-! ## Writing `upgradeTransition` -/

/-- **A COMMIT FINDS ITS SLOT EMPTY.** `setNewVersionUpgradeFromTransition` never
overwrites a committed transition: it writes slot `protocolVersion`, and every committed
slot lies below it. -/
def Properties.CommitWritesOnlyEmptySlots : Prop :=
  ∀ (W : World) (s s' : CTM) (t : Address), CtmInv W s → CStep W s (.commit t) s' →
    s.ut (W.tr t).old = 0

/-- **EACH SLOT IS COMMITTED AT MOST ONCE IN ANY RUN.** For every version `v`, at most one
of a run's operations is a successful commit writing `upgradeTransition[v]`. No premise:
a commit writes the slot of the current version and then moves past it. -/
def Properties.CommitWritesEachSlotOnce : Prop :=
  ∀ (W : World) (s s' : CTM) (ops : List Op), CRun W s ops s' →
    ∀ v, ops.countP (fun op => decide (op.commitDeparture W = some v)) ≤ 1

/-- **ONLY A COMMIT OR A REPLACEMENT CHANGES A SLOT.** A commit fills an empty slot; a
replacement swaps the committed transition `e` it names for a different nonzero `r`.
No other writer touches `upgradeTransition`. -/
def Properties.OnlyCommitOrReplaceWritesSlots : Prop :=
  ∀ (W : World) (s s' : CTM) (op : Op) (v : ℕ), CtmInv W s → CStep W s op s' →
    s'.ut v ≠ s.ut v →
      (∃ t, op = .commit t ∧ (W.tr t).old = v ∧ s.ut v = 0 ∧ s'.ut v = t) ∨
      (∃ e r, op = .replace e r ∧ (W.tr e).old = v ∧ s.ut v = e ∧ s'.ut v = r ∧ r ≠ 0)

/-! ## Transitions chain -/

/-- **COMMITTED TRANSITIONS CHAIN.** In every invariant state, for every committed slot
`v` holding `t`:

* `t` departs from `R_v` (the release of version `v`), whose version is `v`;
* `t` lands on a version `w` with `v < w ≤ protocolVersion`, on release `R_w`, whose
  version is `w` — so the executor's "a committed edge's target is never ahead of
  `protocolVersion`" (`CTMUpgradeExecutor.sol:112-115`) always holds;
* if `w` is the current version, `t` lands on `currentRelease`;
* if slot `w` holds a transition, it departs from exactly the release `t` lands on.

The last clause is the chaining: a chain that crosses `v`'s edge is handed to `w`'s
edge at the release that edge was derived from. -/
def Properties.TransitionsChain : Prop :=
  ∀ (W : World) (s : CTM), CtmInv W s → ∀ v, s.ut v ≠ 0 →
    (W.tr (s.ut v)).fromRel = s.relAt v ∧ W.relVersion (W.tr (s.ut v)).fromRel = v ∧
    v < (W.tr (s.ut v)).new ∧ (W.tr (s.ut v)).new ≤ s.pv ∧
    (W.tr (s.ut v)).newRel = s.relAt (W.tr (s.ut v)).new ∧
    W.relVersion (W.tr (s.ut v)).newRel = (W.tr (s.ut v)).new ∧
    ((W.tr (s.ut v)).new = s.pv → (W.tr (s.ut v)).newRel = s.cur) ∧
    (s.ut (W.tr (s.ut v)).new ≠ 0 →
      (W.tr (s.ut (W.tr (s.ut v)).new)).fromRel = (W.tr (s.ut v)).newRel)

/-- **THE EXECUTOR'S POST-CHECK CANNOT FAIL.** After a successful commit of `t`,
`upgradeTransition[t.oldProtocolVersion()] == t` and `protocolVersion >= t.newProtocolVersion()`,
which is all `CTMUpgradeExecutor._requireTransitionApplied` (`CTMUpgradeExecutor.sol:104-116`)
checks. -/
def Properties.ExecutorPostcheckPasses : Prop :=
  ∀ (W : World) (s s' : CTM) (t : Address), CStep W s (.commit t) s' →
    s'.ut (W.tr t).old = t ∧ (W.tr t).new ≤ s'.pv

/-- **SLOT `v` REPORTS DEPARTURE `v`, IF REPLACEMENTS ARE GENUINE.** Starting from a
state where every committed transition reports its slot as `oldProtocolVersion()` (for
example a starting state, where no slot is committed), every later state does too,
provided each replacement in the run reports its departing release's version — which
every `CTMTransition` does by construction. -/
def Properties.SlotsDepartFromTheirVersion : Prop :=
  ∀ (W : World) (s s' : CTM) (ops : List Op), CtmInv W s →
    (∀ v, s.ut v ≠ 0 → (W.tr (s.ut v)).old = v) →
    (∀ e r, Op.replace e r ∈ ops → (W.tr r).old = W.relVersion (W.tr r).fromRel) →
    CRun W s ops s' →
    ∀ v, s'.ut v ≠ 0 → (W.tr (s'.ut v)).old = v

/-! ## Witnesses -/

/-- **THE REGISTRY RUNS AS DESCRIBED.** From `initialize` with release `100`, the run
"commit `300` (1→2), commit `600` (2→3), replace `300` by `400`" succeeds. At its end two
slots are committed and chained (slot 1's transition lands on release `200`, from which
slot 2's departs), slot 1 has been rewritten by the replacement, and the version is 3.
This shows the premises of the properties above are met by real runs, and that the
replacement rewrite in `OnlyCommitOrReplaceWritesSlots` is not dead. -/
def Properties.VersionRegistryWitness : Prop :=
  ∃ s', CRun wWorld (initState wWorld 100) [.commit 300, .commit 600, .replace 300 400] s' ∧
    CtmInv wWorld (initState wWorld 100) ∧
    s'.pv = 3 ∧ s'.cur = 250 ∧ s'.ut 1 = 400 ∧ s'.ut 2 = 600 ∧
    (wWorld.tr (s'.ut 1)).newRel = (wWorld.tr (s'.ut 2)).fromRel ∧
    wWorld.Genuine 400 ∧ (wWorld.tr (s'.ut 1)).old = 1

/-- **A REPLACEMENT NEED NOT REPORT ITS SLOT.** From `initialize` with release `100`, commit
`300` (1→2) and replace it by `500`, which departs from the same release `100` and lands on
the same release `200`, but reports `oldProtocolVersion() = 7`. Every check of
`replaceUpgradeTransition` passes, and slot `1` now holds a transition reporting
departure `7`. So `SlotsDepartFromTheirVersion` needs its genuineness premise; the
guarantee rests on `CTMTransition`'s constructor, not on the CTM. -/
def Properties.NonGenuineReplacementBreaksSlotVersion : Prop :=
  ∃ s', CRun wWorld (initState wWorld 100) [.commit 300, .replace 300 500] s' ∧
    s'.ut 1 = 500 ∧ (wWorld.tr (s'.ut 1)).old ≠ 1 ∧ ¬ wWorld.Genuine 500

end Contracts.ChainTypeManager
