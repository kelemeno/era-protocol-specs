import EraSpec.Contracts.ChainTypeManager.Specs.L2Convergence

/-!
# Properties: the L2 implementations of the chains on a `ChainTypeManager`

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.L2Convergence` (pin `b17415d20`).
Proofs are in `EraSpec.Contracts.ChainTypeManager.Proofs.L2Convergence`.

## What holds

* **One crossing.** Crossing an L2-genuine transition with its L2 transaction executed points
  the proxy at each fixed address of a new or changed row at the target row, and changes nothing
  else of the chain's L2 state, nor any other chain (`CrossingWritesExactlyTheChangedRows`). So an
  edge never writes a member without a fixed address.
* **Convergence.** Along runs from an invariant state with no break-glass step, every L2 upgrade
  transaction executed, every crossed transition L2-genuine and every release the CTM records
  having a genesis image that holds its table: every chain at a version the CTM has a release
  for runs that release's implementation at every member with a fixed address and a nonempty row,
  or some crossing of the run is of a transition whose two releases have a member whose rows
  clash under the hash (`ChainsRunTheirVersionsL2Rows`). This covers replacements, including a
  skip that lands a chain several versions on in one crossing. Two chains on one version then
  agree on those members however they got there (`ChainsOnOneVersionRunOneL2`).
* **Start states** satisfy the invariant: a fresh CTM, and the bootstrap with pre-registry chains
  at or below its departing version (`FreshL2SysSatisfiesInvariant`,
  `BootstrapL2SysSatisfiesInvariant`). `L2ConvergenceWitness` (fresh, with a skip) and
  `BootstrapConvergenceWitness` (a pre-registry chain crossing the bootstrap edge) meet every
  premise of the headline.
* **Rows along CTM runs.** Along CTM runs with no legacy commit and L2-genuine commits, nonempty
  rows of the current release stay nonempty (`NonemptyRowsStayNonemptyAlongRegistryRuns`), and a
  nonempty row at a member with no fixed address also keeps its hash, so it is equal or a commit
  of the run has a row clash (`NoFixedAddressRowFrozenAlongRegistryRuns`); the legacy
  `setNewVersionUpgrade` can still move it (`LegacyCommitMovesTheFrozenRow`).

## What does not

* The proxy shell does not converge: on one version, a chain created there and a chain that
  crossed to it run the same implementations behind different shells (`ShellsDoNotConverge`).
* Each premise of the headline about crossings and genesis is needed: an unexecuted L2
  transaction (`UnexecutedL2TxLeavesTheOldRow`) and a plan the constructor did not derive
  (`NonGenuinePlanLeavesTheOldRow`) each leave a chain on its old implementation, and a genesis
  image that does not hold its release's table splits a version between a crossed chain and a
  new one (`StaleGenesisImageSplitsAVersion`), each with an injective hash.
-/

namespace Contracts.ChainTypeManager.L2Tables

/-! ## Starting states -/

/-- **`initialize` ESTABLISHES THE INVARIANT.** -/
def Properties.FreshL2SysSatisfiesInvariant : Prop :=
  ∀ (W : L2World) (R : Address), R ≠ 0 → L2Inv W (freshL2Sys W R)

/-- **THE BOOTSTRAP ESTABLISHES THE INVARIANT**, with any pre-registry chains at or below the
departing version, whatever their L2 state. -/
def Properties.BootstrapL2SysSatisfiesInvariant : Prop :=
  ∀ (W : L2World) (old : ℕ) (R : Address) (pre : ChainId → Option L2Chain),
    R ≠ 0 → old < W.base.relVersion R → (∀ cid c, pre cid = some c → c.pv ≤ old) →
    L2Inv W (bootstrapL2Sys W old R pre)

/-! ## One crossing -/

/-- **A CROSSING WRITES EXACTLY THE CHANGED ROWS.** If `t` is L2-genuine and chain `cid` crosses
it with its L2 transaction executed, then, for the chain's state `c` before and `c'` after:
`c'` is at `t.newProtocolVersion()`; at the fixed address of every member whose row is new or
changed by keccak between `t`'s releases, the proxy points at the target row; at every other
address the L2 state is unchanged; every other chain is unchanged. -/
def Properties.CrossingWritesExactlyTheChangedRows : Prop :=
  ∀ {H : Type} [DecidableEq H] (kec : Bytes → H) (rnd : Bytes → L2Addr) (W : L2World)
    (s s' : L2Sys) (cid : ChainId) (t : Address),
    L2Genuine kec rnd W t → L2Step W s (.cross cid t true) s' →
    ∃ c c', s.chains cid = some c ∧ s'.chains cid = some c' ∧ c'.pv = (W.base.tr t).new ∧
      (∀ a, (∀ i, fixedAddress i = some a →
          RowChanged kec (W.rel (W.base.tr t).fromRel).table (W.rel (W.base.tr t).newRel).table i →
          (c'.l2 a).map Prod.snd = some (rowAt (W.rel (W.base.tr t).newRel).table i)) ∧
        ((¬ ∃ i, fixedAddress i = some a ∧
          RowChanged kec (W.rel (W.base.tr t).fromRel).table (W.rel (W.base.tr t).newRel).table i) →
          c'.l2 a = c.l2 a)) ∧
      ∀ cid', cid' ≠ cid → s'.chains cid' = s.chains cid'

/-! ## Convergence -/

/-- **ONE STEP KEEPS THE INVARIANT, OR NAMES A ROW CLASH.** From an invariant state, a step that
is not break-glass and executes its L2 transaction keeps the invariant, provided a crossed
transition is L2-genuine and a created chain's release has a genesis image holding its table;
or the step crosses a transition whose two releases have a member whose rows clash. -/
def Properties.L2StepPreservesInvariant : Prop :=
  ∀ {H : Type} [DecidableEq H] (kec : Bytes → H) (rnd : Bytes → L2Addr) (W : L2World)
    (s s' : L2Sys) (l : L2Label),
    L2Inv W s → L2Step W s l s' → ¬ l.IsBreakGlass → l.L2Executed →
    (∀ cid t b, l = .cross cid t b → L2Genuine kec rnd W t) →
    (∀ cid, l = .genesis cid → GenesisImageHolds W s.ctm.cur) →
    L2Inv W s' ∨ ∃ cid t, l = .cross cid t true ∧ CrossClash kec W t

/-- **CHAINS RUN THEIR VERSION'S L2 IMPLEMENTATIONS.** Along every run from a state satisfying
`L2Inv`, with no break-glass step, every L2 upgrade transaction executed, every crossed
transition L2-genuine, and a genesis image holding its table for every release the CTM has
recorded at the end: every chain at a version `v` for which the CTM has a release `R_v` has, at
every member with a fixed address and a nonempty row in `R_v`'s table, a system proxy pointing at
that row; or the run crosses a transition whose two releases have a member whose rows clash under
`kec`. A pre-registry chain's crossing of an opaque legacy cut is a break-glass step in this
model, so the premise excludes it too. -/
def Properties.ChainsRunTheirVersionsL2Rows : Prop :=
  ∀ {H : Type} [DecidableEq H] (kec : Bytes → H) (rnd : Bytes → L2Addr) (W : L2World)
    (s s' : L2Sys) (ls : List L2Label),
    L2Inv W s → L2Run W s ls s' →
    (∀ l ∈ ls, ¬ l.IsBreakGlass) → (∀ l ∈ ls, l.L2Executed) →
    (∀ cid t b, L2Label.cross cid t b ∈ ls → L2Genuine kec rnd W t) →
    (∀ v, s'.ctm.relAt v ≠ 0 → GenesisImageHolds W (s'.ctm.relAt v)) →
    (∀ cid c, s'.chains cid = some c → s'.ctm.relAt c.pv ≠ 0 →
        RunsReleaseL2 W (s'.ctm.relAt c.pv) c.l2) ∨
      ∃ cid t, L2Label.cross cid t true ∈ ls ∧ CrossClash kec W t

/-- **CHAINS ON ONE VERSION RUN ONE L2.** Under the premises of `ChainsRunTheirVersionsL2Rows`:
for any two chains on the same version `v` for which the CTM has a release, and every member with
a fixed address and a nonempty row in that release, both chains have a system proxy at that
address pointing at the same implementation row, however each reached `v`; or the run crosses a
transition with a row clash. -/
def Properties.ChainsOnOneVersionRunOneL2 : Prop :=
  ∀ {H : Type} [DecidableEq H] (kec : Bytes → H) (rnd : Bytes → L2Addr) (W : L2World)
    (s s' : L2Sys) (ls : List L2Label),
    L2Inv W s → L2Run W s ls s' →
    (∀ l ∈ ls, ¬ l.IsBreakGlass) → (∀ l ∈ ls, l.L2Executed) →
    (∀ cid t b, L2Label.cross cid t b ∈ ls → L2Genuine kec rnd W t) →
    (∀ v, s'.ctm.relAt v ≠ 0 → GenesisImageHolds W (s'.ctm.relAt v)) →
    (∀ cid₁ cid₂ c₁ c₂ i a, s'.chains cid₁ = some c₁ → s'.chains cid₂ = some c₂ →
        c₁.pv = c₂.pv → s'.ctm.relAt c₁.pv ≠ 0 → fixedAddress i = some a →
        rowAt (W.rel (s'.ctm.relAt c₁.pv)).table i ≠ [] →
        (c₁.l2 a).map Prod.snd = (c₂.l2 a).map Prod.snd ∧ (c₁.l2 a).isSome = true) ∨
      ∃ cid t, L2Label.cross cid t true ∈ ls ∧ CrossClash kec W t

/-! ## Rows along CTM runs -/

/-- **NONEMPTY ROWS STAY NONEMPTY ALONG REGISTRY RUNS.** Along every run of CTM writers with no
legacy commit (`setNewVersionUpgrade`) whose commits are of L2-genuine transitions, every member
with a nonempty row in the current release at the start has a nonempty row in the current release
at the end. -/
def Properties.NonemptyRowsStayNonemptyAlongRegistryRuns : Prop :=
  ∀ {H : Type} [DecidableEq H] (kec : Bytes → H) (rnd : Bytes → L2Addr) (W : L2World)
    (c c' : CTM) (ops : List Op),
    CRun W.base c ops c' →
    (∀ R b, Op.legacyCommit R b ∉ ops) →
    (∀ t, Op.commit t ∈ ops → L2Genuine kec rnd W t) →
    ∀ i, rowAt (W.rel c.cur).table i ≠ [] → rowAt (W.rel c'.cur).table i ≠ []

/-- **A ROW WITHOUT A FIXED ADDRESS STAYS FROZEN ALONG REGISTRY RUNS.** Along every run of CTM
writers with no legacy commit (`setNewVersionUpgrade`) whose commits are of L2-genuine
transitions: if the current release at the start has a nonempty row at a member with no fixed
address, the current release at the end has a nonempty row there with the same hash, and the two
rows are equal or some commit of the run is of a transition whose two releases have a member
whose rows clash. -/
def Properties.NoFixedAddressRowFrozenAlongRegistryRuns : Prop :=
  ∀ {H : Type} [DecidableEq H] (kec : Bytes → H) (rnd : Bytes → L2Addr) (W : L2World)
    (c c' : CTM) (ops : List Op),
    CRun W.base c ops c' →
    (∀ R b, Op.legacyCommit R b ∉ ops) →
    (∀ t, Op.commit t ∈ ops → L2Genuine kec rnd W t) →
    ∀ i, fixedAddress i = none → rowAt (W.rel c.cur).table i ≠ [] →
      rowAt (W.rel c'.cur).table i ≠ [] ∧
      kec (rowAt (W.rel c'.cur).table i) = kec (rowAt (W.rel c.cur).table i) ∧
      (rowAt (W.rel c'.cur).table i = rowAt (W.rel c.cur).table i ∨
        ∃ t, Op.commit t ∈ ops ∧ CrossClash kec W t)

/-! ## Witnesses and boundaries -/

/-- **THE HEADLINE'S PREMISES, MET BY A RUN WITH A SKIP.** The run `cvLabels` from a fresh CTM on
release `100` succeeds and meets every premise of `ChainsRunTheirVersionsL2Rows` with the
identity as hash. Each of its three crossings has a new or changed row. At its end slot `2^32`
holds the skip `700` (landing on version `3·2^32`), and chains `0` (two crossings), `1` (the skip)
and `2` (genesis) are all at version `3·2^32` with proxies at the three members' fixed addresses
pointing at the same rows. -/
def Properties.L2ConvergenceWitness : Prop :=
  ∃ s', L2Run cvWorld cvSys0 cvLabels s' ∧ L2Inv cvWorld cvSys0 ∧
    (∀ l ∈ cvLabels, ¬ l.IsBreakGlass) ∧ (∀ l ∈ cvLabels, l.L2Executed) ∧
    (∀ cid t b, L2Label.cross cid t b ∈ cvLabels → L2Genuine (fun x : Bytes => x) wRnd cvWorld t) ∧
    (∀ v, s'.ctm.relAt v ≠ 0 → GenesisImageHolds cvWorld (s'.ctm.relAt v)) ∧
    (∀ t ∈ ([300, 600, 700] : List Address), ∃ i,
      RowChanged (fun x : Bytes => x) (cvRel (cvTr t).fromRel).table (cvRel (cvTr t).newRel).table i) ∧
    s'.ctm.ut (cvV 1) = 700 ∧ (cvTr 700).new = cvV 3 ∧
    ∃ c₀ c₁ c₂, s'.chains 0 = some c₀ ∧ s'.chains 1 = some c₁ ∧ s'.chains 2 = some c₂ ∧
      c₀.pv = cvV 3 ∧ c₁.pv = cvV 3 ∧ c₂.pv = cvV 3 ∧
      ∀ a ∈ ([0x10002, 0x10003, 0x10004] : List L2Addr),
        (c₀.l2 a).map Prod.snd = (c₁.l2 a).map Prod.snd ∧
        (c₁.l2 a).map Prod.snd = (c₂.l2 a).map Prod.snd ∧ (c₀.l2 a).isSome = true

/-- **THE HEADLINE'S PREMISES, MET BY A BOOTSTRAP RUN.** From the bootstrap of a legacy CTM at
version 0 onto release `100`, with pre-registry chain `5` at version 0 (`cvPre`): the premises of
`BootstrapL2SysSatisfiesInvariant` hold, and the run "chain `5` crosses the bootstrap edge, the
CTM commits `300`, chain `5` crosses it" succeeds and meets every premise of
`ChainsRunTheirVersionsL2Rows` with the identity hash. At its end chain `5` is at version
`2·2^32` and runs release `200`, behind its pre-registry shell at member 0's address. -/
def Properties.BootstrapConvergenceWitness : Prop :=
  ∃ s', L2Run cvWorld (bootstrapL2Sys cvWorld 0 100 cvPre)
      [.bootstrapCross 5 true, .ctm (.commit 300), .cross 5 300 true] s' ∧
    (100 : Address) ≠ 0 ∧ 0 < cvWorld.base.relVersion 100 ∧
    (∀ cid c, cvPre cid = some c → c.pv ≤ 0) ∧
    L2Inv cvWorld (bootstrapL2Sys cvWorld 0 100 cvPre) ∧
    L2Genuine (fun x : Bytes => x) wRnd cvWorld 300 ∧
    (∀ v, s'.ctm.relAt v ≠ 0 → GenesisImageHolds cvWorld (s'.ctm.relAt v)) ∧
    ∃ c, s'.chains 5 = some c ∧ c.pv = cvV 2 ∧ s'.ctm.relAt c.pv = 200 ∧
      RunsReleaseL2 cvWorld 200 c.l2 ∧ (c.l2 0x10002).map Prod.fst = some (wDesc 60)

/-- **THE SHELL DOES NOT CONVERGE** (`TransitionDerivationLib.sol:91-94`: a shell change reaches
only addresses with no code). At the end of the witness run `cvLabels`, chains `0` and `2` are on
the same version and their proxies at member 0's fixed address point at the same implementation
row, behind different shells: chain `0`'s from release `100`, chain `2`'s from release `250`. -/
def Properties.ShellsDoNotConverge : Prop :=
  ∃ s', L2Run cvWorld cvSys0 cvLabels s' ∧
    ∃ c₀ c₂, s'.chains 0 = some c₀ ∧ s'.chains 2 = some c₂ ∧ c₀.pv = c₂.pv ∧
      (c₀.l2 0x10002).map Prod.snd = (c₂.l2 0x10002).map Prod.snd ∧
      (c₀.l2 0x10002).map Prod.fst = some (cvRel 100).shell ∧
      (c₂.l2 0x10002).map Prod.fst = some (cvRel 250).shell ∧
      (cvRel 100).shell ≠ (cvRel 250).shell

/-- **COUNTERMODEL: AN UNEXECUTED L2 TRANSACTION LEAVES THE OLD ROW.** A run that meets every
premise of `ChainsRunTheirVersionsL2Rows` except that its one crossing does not execute its L2
transaction ends with chain `0` at a version whose release it does not run, and no transition has
a row clash under the identity hash. -/
def Properties.UnexecutedL2TxLeavesTheOldRow : Prop :=
  ∃ s', L2Run cvWorld cvSys0 [.genesis 0, .ctm (.commit 300), .cross 0 300 false] s' ∧
    L2Inv cvWorld cvSys0 ∧ L2Genuine (fun x : Bytes => x) wRnd cvWorld 300 ∧
    (∀ v, s'.ctm.relAt v ≠ 0 → GenesisImageHolds cvWorld (s'.ctm.relAt v)) ∧
    (∀ t, ¬ CrossClash (fun x : Bytes => x) cvWorld t) ∧
    ∃ c, s'.chains 0 = some c ∧ s'.ctm.relAt c.pv ≠ 0 ∧
      ¬ RunsReleaseL2 cvWorld (s'.ctm.relAt c.pv) c.l2

/-- **COUNTERMODEL: A PLAN THE CONSTRUCTOR DID NOT DERIVE LEAVES THE OLD ROW.** In
`cvWorldStalePlan`, object `300` reports genuine versions but its `l2Plan()` omits the derived
deployment, so it is not L2-genuine. A run that meets every other premise of
`ChainsRunTheirVersionsL2Rows` ends with chain `0` at a version whose release it does not run, and
no transition has a row clash under the identity hash. -/
def Properties.NonGenuinePlanLeavesTheOldRow : Prop :=
  ∃ s', L2Run cvWorldStalePlan (freshL2Sys cvWorldStalePlan 100)
      [.genesis 0, .ctm (.commit 300), .cross 0 300 true] s' ∧
    L2Inv cvWorldStalePlan (freshL2Sys cvWorldStalePlan 100) ∧
    cvWorldStalePlan.base.Genuine 300 ∧ ¬ L2Genuine (fun x : Bytes => x) wRnd cvWorldStalePlan 300 ∧
    (∀ v, s'.ctm.relAt v ≠ 0 → GenesisImageHolds cvWorldStalePlan (s'.ctm.relAt v)) ∧
    (∀ t, ¬ CrossClash (fun x : Bytes => x) cvWorldStalePlan t) ∧
    ∃ c, s'.chains 0 = some c ∧ s'.ctm.relAt c.pv ≠ 0 ∧
      ¬ RunsReleaseL2 cvWorldStalePlan (s'.ctm.relAt c.pv) c.l2

/-- **COUNTERMODEL: A GENESIS IMAGE THAT DOES NOT HOLD ITS TABLE SPLITS A VERSION.** In
`cvWorldStaleImage`, release `200`'s genesis image is release `100`'s whole-table install, so
`GenesisImageHolds` fails for `200`. A run that meets every other premise of
`ChainsRunTheirVersionsL2Rows` ends with chain `0` (which crossed `300`) and chain `1` (created
at that version) on one version, their proxies at member 0's fixed address pointing at different
rows, and no transition has a row clash under the identity hash. -/
def Properties.StaleGenesisImageSplitsAVersion : Prop :=
  ∃ s', L2Run cvWorldStaleImage (freshL2Sys cvWorldStaleImage 100)
      [.genesis 0, .ctm (.commit 300), .cross 0 300 true, .genesis 1] s' ∧
    L2Inv cvWorldStaleImage (freshL2Sys cvWorldStaleImage 100) ∧
    L2Genuine (fun x : Bytes => x) wRnd cvWorldStaleImage 300 ∧
    ¬ GenesisImageHolds cvWorldStaleImage 200 ∧
    (∀ t, ¬ CrossClash (fun x : Bytes => x) cvWorldStaleImage t) ∧
    ∃ c₀ c₁, s'.chains 0 = some c₀ ∧ s'.chains 1 = some c₁ ∧ c₀.pv = c₁.pv ∧
      (c₀.l2 0x10002).map Prod.snd ≠ (c₁.l2 0x10002).map Prod.snd

/-- **THE FROZEN ROW ALONG A RUN.** From `initialize` on release `100`, whose row 14
(`BeaconProxy`, no fixed address) is nonempty, the registry commit of the L2-genuine `300`, which
changes row 0, succeeds and lands on release `200`, whose row 14 is the same. This meets the
premises of `NonemptyRowsStayNonemptyAlongRegistryRuns` and
`NoFixedAddressRowFrozenAlongRegistryRuns`. -/
def Properties.FrozenRowAlongRunsWitness : Prop :=
  ∃ c', CRun fzBase (initState fzBase 100) [.commit 300] c' ∧
    L2Genuine (fun x : Bytes => x) wRnd fzWorld 300 ∧
    fixedAddress 14 = none ∧ rowAt (fzRel 100).table 14 ≠ [] ∧
    RowChanged (fun x : Bytes => x) (fzRel 100).table (fzRel 200).table 0 ∧
    c'.cur = 200 ∧ rowAt (fzRel c'.cur).table 14 = rowAt (fzRel 100).table 14

/-- **THE LEGACY COMMIT MOVES THE FROZEN ROW.** From the same state, the legacy cut-taking commit
`setNewVersionUpgrade` installing release `250` succeeds, and `250`'s row 14 differs from
`100`'s. So `NoFixedAddressRowFrozenAlongRegistryRuns` needs its no-legacy-commit premise. -/
def Properties.LegacyCommitMovesTheFrozenRow : Prop :=
  ∃ c', CRun fzBase (initState fzBase 100) [.legacyCommit 250 false] c' ∧
    c'.cur = 250 ∧ rowAt (fzRel c'.cur).table 14 ≠ [] ∧
    rowAt (fzRel c'.cur).table 14 ≠ rowAt (fzRel 100).table 14

end Contracts.ChainTypeManager.L2Tables
