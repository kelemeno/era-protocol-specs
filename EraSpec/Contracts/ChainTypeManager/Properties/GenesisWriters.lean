import EraSpec.Contracts.ChainTypeManager.Specs.GenesisWriters

/-!
# Properties: chain creation is `ChainRouting`'s genesis step

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.GenesisWriters`. Proofs are in
`EraSpec.Contracts.ChainTypeManager.Proofs.GenesisWriters`.

## The two writers

* **`DiamondInit` writes exactly the release and the version.** Its only write to
  `Diamond.DiamondStorage` is `newChainInstallations(currentRelease)`. Of the modelled
  `ZKChainStorage` it writes only the chain id, the CTM binding, the version, the verifier and
  the admin (`DiamondInitWrites`). On a new proxy the routing it leaves is exactly the release's
  flattened rows, the result of `ChainRouting`'s `addAll`, and the version is the CTM's
  (`DiamondInitInstallsTheRelease`). It cannot run twice in one diamond
  (`DiamondInitCannotRerun`).
* **The genesis upgrade writes no diamond storage.** The cut `Admin.genesisUpgrade` builds has
  no facet cuts (`GenesisUpgradeCutIsEmpty`). Its init, `L1GenesisUpgrade`, leaves
  `Diamond.DiamondStorage`, the version, the CTM binding, the admin and the verifier as they
  were, and writes only the L2 upgrade transaction hash (`GenesisUpgradeWritesNoDiamondStorage`).
  This holds on any diamond. The genesis upgrade goes through the shared
  `BaseZkSyncUpgrade._upgrade`, which could in principle write diamond storage; at `e561b9cc2`
  it writes only the version (back to its own value) and that hash.
* **The diamond library's `Add` cuts are `ChainRouting`'s `addAll`.** A successful list of
  `Add` facet cuts changes the routing exactly as `addAll` of its flattened rows does
  (`AddCutsRefineAddAll`). This is what ties the facet-level cut to the flattened model.

## The genesis step is a theorem

* **Soundness.** A chain created by `createNewChain`, or deployed by `forwardedBridgeMint`, is a
  `ChainRouting` step: `Step.genesis`, respectively `Step.migrateIn`
  (`CodeCreationIsAStep`). The premise is that the release's members are the code they are
  named for (`GenuineRelease`).
* **Exactness.** For a release that also passes `CTMRelease`'s checks (`ReleaseWf`) and routes
  the entry points the path calls, `createNewChain` and `forwardedBridgeMint` succeed
  (`ValidatedReleaseCreatesChains`, `ValidatedReleaseMigratesChainsIn`). Code-level creation
  and the model's step then relate exactly the same systems (`GenesisStepIsExact`,
  `MigrateInStepIsExact`), and so does every other step (`CodeStepIsExact`).
* **The headline with code-level creation.** Along any run whose chain creations are run as
  code and in which every release the CTM installs is genuine, the run is a `ChainRouting` run
  (`CodeRunIsARun`). So every chain at a version `v` with a release `R_v` routes exactly `R_v`
  (`CodeRunsKeepChainsOnTheirRelease`).

## What is load-bearing

* **Genuine members.** A release whose `diamondInit()` is other code
  (`ForeignDiamondInitBreaksGenesis`), or whose genesis upgrade is other code
  (`ForeignGenesisUpgradeBreaksGenesis`), creates a chain that does not route its release.
  The system invariant fails after one creation from the fresh system. Nothing on chain checks
  these members; governance's review does.
* **`validate()`'s nonempty rows.** The flattened step admits a release with a selector-less
  facet row, which the code refuses (`SelectorlessRowRevertsCreation`). So the step
  over-approximates creation, and exactness needs `ReleaseWf`.
-/

namespace Contracts.ChainTypeManager.GenesisWriters

/-! ## The diamond library -/

/-- **`Add` CUTS ARE `ChainRouting`'S `addAll`.** If a list of `Add` facet cuts succeeds on a
diamond, then `addAll` of the cuts' flattened rows succeeds on the diamond's routing and gives
the routing afterwards; the freeze flag is untouched. The one premise is that address zero has
no code, which the library itself relies on (`Diamond.sol:144-146`): a facet with code is then
nonzero, so the selectors it is given become routed. -/
def Properties.AddCutsRefineAddAll : Prop :=
  ∀ (hasCode : Address → Bool) (ds ds' : DiamondStorage) (cs : List FacetCut),
    hasCode 0 = false → (∀ c ∈ cs, c.action = .add) →
    applyFacetCuts hasCode ds cs = some ds' →
    addAll ds.routing (flattenCuts cs) = some ds'.routing ∧ ds'.isFrozen = ds.isFrozen

/-! ## `DiamondInit` -/

/-- **DIAMONDINIT'S WRITES.** On any diamond: a successful `DiamondInit.initialize(id, admin)`
found the lock clear and the CTM's current release nonzero. Its diamond storage afterwards is
what the cuts `newChainInstallations(currentRelease)` leave on the storage before. Of the
modelled `ZKChainStorage` it writes exactly the chain id, the CTM (`msg.sender`), the CTM's
version, the release's verifier and the admin. It sets the lock. -/
def Properties.DiamondInitWrites : Prop :=
  ∀ (E : Env) (c : CTM) (id : ChainId) (admin : Address) (st st' : ChainState),
    diamondInitialize E c id admin st = some st' →
    st.lock = 0 ∧ c.cur ≠ 0 ∧
    applyFacetCuts E.hasCode st.diamond (newChainInstallations E c.cur) = some st'.diamond ∧
    st'.app = { st.app with
      chainId := id, chainTypeManager := E.ctm, protocolVersion := c.pv,
      verifier := E.verifierOf c.cur, admin := admin } ∧
    st'.lock = 1

/-- **DIAMONDINIT INSTALLS EXACTLY THE CTM'S CURRENT RELEASE, AT THE CTM'S VERSION.** On a new
proxy, if address zero has no code: after a successful `DiamondInit.initialize(id, admin)`, the
diamond routes exactly the current release's flattened rows. That routing is the result of
`ChainRouting`'s `addAll` on the empty routing. The diamond is not frozen. The chain is at the
CTM's version and bound to the CTM, and the fields the genesis upgrade checks are still zero. -/
def Properties.DiamondInitInstallsTheRelease : Prop :=
  ∀ (E : Env) (c : CTM) (id : ChainId) (admin : Address) (st : ChainState),
    E.code 0 = .none →
    diamondInitialize E c id admin ChainState.fresh = some st →
    addAll emptyRouting (releaseRows E c.cur) = some st.diamond.routing ∧
    st.diamond.routing = rowsRouting (releaseRows E c.cur) ∧ st.diamond.isFrozen = false ∧
    st.app.protocolVersion = c.pv ∧ st.app.chainTypeManager = E.ctm ∧
    st.app.settlementLayer = 0 ∧ st.app.l2SystemContractsUpgradeTxHash = 0 ∧
    st.app.l2SystemContractsUpgradeBatchNumber = 0 ∧ st.app.pausedDepositsTimestamp = 0

/-- **DIAMONDINIT CANNOT RUN TWICE IN ONE DIAMOND.** With the lock set, which the first run does
(`DiamondInitWrites`), `initialize` reverts `SlotOccupied` (`ReentrancyGuard.sol:59-62`), so a
later cut cannot re-install a release through it. -/
def Properties.DiamondInitCannotRerun : Prop :=
  ∀ (E : Env) (c : CTM) (id : ChainId) (admin : Address) (st : ChainState),
    st.lock ≠ 0 → diamondInitialize E c id admin st = none

/-! ## The genesis upgrade -/

/-- **THE GENESIS UPGRADE'S CUT HAS NO FACET CUTS.** `Admin.genesisUpgrade` builds
`{facetCuts: emptyArray, initAddress: l1GenesisUpgrade, ...}` (`Admin.sol:570-575`), with the
current release's genesis upgrade as init. -/
def Properties.GenesisUpgradeCutIsEmpty : Prop :=
  ∀ (E : Env) (c : CTM),
    (genesisUpgradeCut E c).facetCuts = [] ∧
    (genesisUpgradeCut E c).initAddress = E.genesisUpgradeOf c.cur ∧
    (genesisUpgradeCut E c).initCalldata = .genesisUpgrade

/-- **THE GENESIS UPGRADE WRITES NO DIAMOND STORAGE.** On any diamond: if the current release's
genesis upgrade is `L1GenesisUpgrade`, a successful `Admin.genesisUpgrade()` leaves
`Diamond.DiamondStorage` and the lock as they were. Of the modelled `ZKChainStorage` it writes
only `l2SystemContractsUpgradeTxHash`, so the version, the CTM binding, the admin and the
verifier are unchanged. -/
def Properties.GenesisUpgradeWritesNoDiamondStorage : Prop :=
  ∀ (E : Env) (c : CTM) (st st' : ChainState),
    E.code (E.genesisUpgradeOf c.cur) = .l1GenesisUpgrade →
    adminGenesisUpgrade E c st = some st' →
    st'.diamond = st.diamond ∧ st'.lock = st.lock ∧
    st'.app = { st.app with
      l2SystemContractsUpgradeTxHash := E.genesisTxHash c.cur st.app.chainId st.app.protocolVersion }

/-! ## Soundness: code-level creation is a `ChainRouting` step -/

/-- **A CHAIN CREATED BY THE CODE IS A `ChainRouting` STEP.** If address zero has no code and the
CTM's current release is genuine: a successful `createNewChain` for an unregistered id relates
the system exactly as `Step.genesis` does, and a successful `forwardedBridgeMint` deploying a
new diamond exactly as `Step.migrateIn` does. In both, the new chain is at the CTM's version
and routes exactly the release's rows. -/
def Properties.CodeCreationIsAStep : Prop :=
  ∀ (W : World) (E : Env) (s s' : Sys) (l : Label),
    E.code 0 = .none → GenuineRelease E W s.ctm.cur →
    CodeCreation E s l s' → Step W s l s'

/-! ## Exactness on a validated release -/

/-- **A VALIDATED, GENUINE RELEASE CREATES CHAINS.** If address zero has no code, the CTM's
current release is nonzero, genuine and passes `CTMRelease`'s checks, and it routes
`genesisUpgrade()` to the Admin facet and `pauseDepositsBeforeInitiatingMigration()` to the
Migrator facet: `createNewChain` succeeds for every id, admin and timestamp. -/
def Properties.ValidatedReleaseCreatesChains : Prop :=
  ∀ (W : World) (E : Env) (c : CTM) (id : ChainId) (admin : Address) (ts : ℕ),
    E.code 0 = .none → c.cur ≠ 0 → GenuineRelease E W c.cur → ReleaseWf E c.cur →
    RoutesTo E c.cur selGenesisUpgrade .adminFacet →
    RoutesTo E c.cur selPauseDeposits .migratorFacet →
    ∃ st, createNewChain E c id admin ts = some st

/-- **A VALIDATED, GENUINE RELEASE TAKES CHAINS IN.** Under the same premises, with
`forwardedBridgeMint` routed to the Migrator facet: a chain arriving at the CTM's version gets
a new diamond, for every id, admin and commitment. -/
def Properties.ValidatedReleaseMigratesChainsIn : Prop :=
  ∀ (W : World) (E : Env) (c : CTM) (id : ChainId) (admin : Address) (txHash batch : ℕ),
    E.code 0 = .none → c.cur ≠ 0 → GenuineRelease E W c.cur → ReleaseWf E c.cur →
    RoutesTo E c.cur selForwardedBridgeMint .migratorFacet →
    ∃ st, migrateInNewChain E c c.pv id admin txHash batch = some st

/-- **THE GENESIS STEP IS EXACTLY WHAT THE CODE DOES.** Under the premises of
`ValidatedReleaseCreatesChains` for the CTM's current release: a code-level `createNewChain`
and `Step.genesis` relate exactly the same systems. So `ChainRouting`'s genesis label is a
theorem about this code, not a modelling choice. -/
def Properties.GenesisStepIsExact : Prop :=
  ∀ (W : World) (E : Env) (s s' : Sys) (id : ChainId),
    E.code 0 = .none → s.ctm.cur ≠ 0 → GenuineRelease E W s.ctm.cur → ReleaseWf E s.ctm.cur →
    RoutesTo E s.ctm.cur selGenesisUpgrade .adminFacet →
    RoutesTo E s.ctm.cur selPauseDeposits .migratorFacet →
    (CodeCreation E s (.genesis id) s' ↔ Step W s (.genesis id) s')

/-- **THE MIGRATE-IN STEP IS EXACTLY WHAT THE CODE DOES.** Under the premises of
`ValidatedReleaseMigratesChainsIn` for the CTM's current release: a code-level
`forwardedBridgeMint` that deploys a new diamond and `Step.migrateIn` relate exactly the same
systems. -/
def Properties.MigrateInStepIsExact : Prop :=
  ∀ (W : World) (E : Env) (s s' : Sys) (id : ChainId),
    E.code 0 = .none → s.ctm.cur ≠ 0 → GenuineRelease E W s.ctm.cur → ReleaseWf E s.ctm.cur →
    RoutesTo E s.ctm.cur selForwardedBridgeMint .migratorFacet →
    (CodeCreation E s (.migrateIn id) s' ↔ Step W s (.migrateIn id) s')

/-- **WITH CREATION RUN AS CODE, THE SYSTEM HAS EXACTLY `ChainRouting`'S STEPS.** If address zero
has no code and the CTM's current release is nonzero, genuine, validated and routes the three
entry points: for every label, a step of the system that creates chains as the code does and a
`ChainRouting` step relate exactly the same systems. -/
def Properties.CodeStepIsExact : Prop :=
  ∀ (W : World) (E : Env) (s s' : Sys) (l : Label),
    E.code 0 = .none → s.ctm.cur ≠ 0 → GenuineRelease E W s.ctm.cur → ReleaseWf E s.ctm.cur →
    RoutesTo E s.ctm.cur selGenesisUpgrade .adminFacet →
    RoutesTo E s.ctm.cur selPauseDeposits .migratorFacet →
    RoutesTo E s.ctm.cur selForwardedBridgeMint .migratorFacet →
    (CodeStep W E s l s' ↔ Step W s l s')

/-! ## Runs -/

/-- **A RUN WITH CODE-LEVEL CREATION IS A `ChainRouting` RUN.** If address zero has no code and
every release the CTM has recorded at the end of the run is genuine, then from a state whose CTM
satisfies `CtmInv`, a run that creates chains as the code does relates the same systems as a
`ChainRouting` run with the same labels. The recorded releases (`relAt`) include every release
that was current at some point of the run. -/
def Properties.CodeRunIsARun : Prop :=
  ∀ (W : World) (E : Env) (s s' : Sys) (ls : List Label),
    E.code 0 = .none → CtmInv W s.ctm → CodeRun W E s ls s' →
    (∀ w, s'.ctm.relAt w ≠ 0 → GenuineRelease E W (s'.ctm.relAt w)) →
    Run W s ls s'

/-- **HEADLINE WITH CODE-LEVEL CREATION: EVERY CHAIN AT VERSION `v` HAS EXACTLY `R_v`'S
ROUTING.** If address zero has no code and every release the CTM has recorded at the end of the
run is genuine: along any run from an invariant state that creates chains as the code does and
uses no break-glass cut, every chain at a version `v` for which the CTM has a release `R_v`
routes exactly `R_v`'s rows, and `R_v` is a release of version `v`. -/
def Properties.CodeRunsKeepChainsOnTheirRelease : Prop :=
  ∀ (W : World) (E : Env) (s s' : Sys) (ls : List Label),
    E.code 0 = .none → SysInv W s → CodeRun W E s ls s' → (∀ l ∈ ls, ¬ l.isArbitrary) →
    (∀ w, s'.ctm.relAt w ≠ 0 → GenuineRelease E W (s'.ctm.relAt w)) →
    ∀ id c, s'.chains id = some c → s'.ctm.relAt c.pv ≠ 0 →
      W.relVersion (s'.ctm.relAt c.pv) = c.pv ∧
      c.routing = rowsRouting (W.relRows (s'.ctm.relAt c.pv))

/-! ## Countermodels -/

/-- **A FOREIGN `diamondInit()` BREAKS THE GENESIS STEP.** `fInitEnv` is the witness
environment with `foreignInit` at release `100`'s `diamondInit()` address. Every other part of
`GenuineRelease` holds for release `100`. From the fresh witness system, which satisfies the
invariant, `createNewChain` succeeds. The new chain is at version 1, whose release is `100`,
but it does not route release `100`'s rows. So the system no longer satisfies `SysInv`, and
no `Step.genesis` leads to it. -/
def Properties.ForeignDiamondInitBreaksGenesis : Prop :=
  fInitEnv.code 0 = .none ∧
  fInitEnv.code (fInitEnv.genesisUpgradeOf 100) = .l1GenesisUpgrade ∧
  (∀ f b, rowsRouting (releaseRows fInitEnv 100) selGenesisUpgrade = some (f, b) →
    fInitEnv.code f = .adminFacet) ∧
  (∀ x, (x = selPauseDeposits ∨ x = selForwardedBridgeMint) →
    ∀ f b, rowsRouting (releaseRows fInitEnv 100) x = some (f, b) → fInitEnv.code f = .migratorFacet) ∧
  gWorld.relRows 100 = releaseRows fInitEnv 100 ∧
  SysInv gWorld gSys0 ∧
  ∃ s', CodeCreation fInitEnv gSys0 (.genesis 0) s' ∧
    (∃ c, s'.chains 0 = some c ∧ c.pv = 1 ∧ s'.ctm.relAt 1 = 100 ∧
      c.routing ≠ rowsRouting (gWorld.relRows 100)) ∧
    ¬ SysInv gWorld s' ∧ ¬ Step gWorld gSys0 (.genesis 0) s'

/-- **A FOREIGN GENESIS UPGRADE BREAKS THE GENESIS STEP.** `fUpgradeEnv` is the witness
environment with `foreignUpgrade` at release `100`'s genesis-upgrade address, which routes an
extra selector `9`. Every other part of `GenuineRelease` holds for release `100`. From the
fresh witness system `createNewChain` succeeds, and the new chain at version 1 routes selector
`9`, which release `100` does not. So `SysInv` fails, and no `Step.genesis` leads to the
result. -/
def Properties.ForeignGenesisUpgradeBreaksGenesis : Prop :=
  fUpgradeEnv.code 0 = .none ∧
  fUpgradeEnv.code (fUpgradeEnv.diamondInitOf 100) = .diamondInit ∧
  (∀ f b, rowsRouting (releaseRows fUpgradeEnv 100) selGenesisUpgrade = some (f, b) →
    fUpgradeEnv.code f = .adminFacet) ∧
  (∀ x, (x = selPauseDeposits ∨ x = selForwardedBridgeMint) →
    ∀ f b, rowsRouting (releaseRows fUpgradeEnv 100) x = some (f, b) →
      fUpgradeEnv.code f = .migratorFacet) ∧
  gWorld.relRows 100 = releaseRows fUpgradeEnv 100 ∧
  SysInv gWorld gSys0 ∧
  ∃ s', CodeCreation fUpgradeEnv gSys0 (.genesis 0) s' ∧
    (∃ c, s'.chains 0 = some c ∧ c.pv = 1 ∧ c.routing 9 = some (99, false) ∧
      rowsRouting (gWorld.relRows 100) 9 = none) ∧
    ¬ SysInv gWorld s' ∧ ¬ Step gWorld gSys0 (.genesis 0) s'

/-- **THE FLATTENED GENESIS STEP ADMITS A RELEASE THE CODE REFUSES.** In `eEnv`, release `100`
has a third facet row whose facet describes no selector. The release is genuine and routes both
entry points, and its rows are unchanged. `Step.genesis` exists on the fresh system, but
`createNewChain` reverts for every id, admin and timestamp, at the cut with no selectors
(`NoFunctionsForDiamondCut`, `Diamond.sol:120-122`). So the converse of
`CodeCreationIsAStep` needs `ReleaseWf`, whose nonempty-selectors part is
`CTMRelease.validate()`'s refusal (`CTMRelease.sol:121-123`). -/
def Properties.SelectorlessRowRevertsCreation : Prop :=
  eEnv.code 0 = .none ∧ GenuineRelease eEnv eWorld 100 ∧
  RoutesTo eEnv 100 selGenesisUpgrade .adminFacet ∧ RoutesTo eEnv 100 selPauseDeposits .migratorFacet ∧
  releaseRows eEnv 100 = releaseRows gEnv 100 ∧
  (∃ s', Step eWorld ⟨initState eWorld 100, fun _ => none⟩ (.genesis 0) s') ∧
  ∀ id admin ts, createNewChain eEnv (initState eWorld 100) id admin ts = none

/-! ## Witnesses -/

/-- **THE COMPONENT PREMISES ARE SATISFIABLE.** On the witness environment: address zero has no
code, and release `100` is nonzero, genuine, validated, and routes the three entry points. Its
installation cuts are all `Add` cuts and succeed on a new proxy. On the fresh CTM over release
`100`, `DiamondInit` succeeds on a new proxy, and after the deployment the genesis upgrade
succeeds. -/
def Properties.GenesisWritersWitness : Prop :=
  gEnv.code 0 = .none ∧ (initState gWorld 100).cur = 100 ∧ GenuineRelease gEnv gWorld 100 ∧
  ReleaseWf gEnv 100 ∧ RoutesTo gEnv 100 selGenesisUpgrade .adminFacet ∧
  RoutesTo gEnv 100 selPauseDeposits .migratorFacet ∧
  RoutesTo gEnv 100 selForwardedBridgeMint .migratorFacet ∧
  (∀ c ∈ newChainInstallations gEnv 100, c.action = .add) ∧
  (∃ ds, applyFacetCuts gEnv.hasCode DiamondStorage.empty (newChainInstallations gEnv 100) = some ds) ∧
  (∃ st, diamondInitialize gEnv (initState gWorld 100) 0 1 ChainState.fresh = some st) ∧
  ∃ st st', deployNewChain gEnv (initState gWorld 100) 0 1 = some st ∧
    adminGenesisUpgrade gEnv (initState gWorld 100) st = some st'

/-- **THE RUN-LEVEL HEADLINE IS NOT VACUOUS.** From the fresh witness system, which satisfies the
invariant: create chain `0` as the code does, commit `300` (1→2), upgrade chain `0`, and create
chain `1`. The run uses no break-glass cut, and every release the CTM has recorded at the end
is genuine. Both chains end at version 2 routing release `200`'s rows, which differ from
release `100`'s. -/
def Properties.CodeRunWitness : Prop :=
  gEnv.code 0 = .none ∧ SysInv gWorld gSys0 ∧
  ∃ s, CodeRun gWorld gEnv gSys0 [.genesis 0, .ctm (.commit 300), .transition 0, .genesis 1] s ∧
    (∀ w, s.ctm.relAt w ≠ 0 → GenuineRelease gEnv gWorld (s.ctm.relAt w)) ∧
    (∃ c, s.chains 0 = some c ∧ c.pv = 2 ∧ c.routing = rowsRouting (gWorld.relRows 200)) ∧
    (∃ c, s.chains 1 = some c ∧ c.pv = 2 ∧ c.routing = rowsRouting (gWorld.relRows 200)) ∧
    rowsRouting (gWorld.relRows 200) ≠ rowsRouting (gWorld.relRows 100)

end Contracts.ChainTypeManager.GenesisWriters
