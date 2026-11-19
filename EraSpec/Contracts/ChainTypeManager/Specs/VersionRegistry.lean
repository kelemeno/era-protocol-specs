import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: `ChainTypeManager` — the protocol version and the transition registry

Source: branch `draft/v0.35.0` of `matter-labs/era-contracts`, commit `b17415d20`
(2026-11-16). Every `file:line` below is at that commit. Paths are relative to
`l1-contracts/contracts/`.

The model was first written against commit `e561b9cc2` (2026-10-19) of branch
`feat/upgrade-simplification` of the zksync-era `contracts` repository; `draft/v0.35.0` took
that `l1-contracts/contracts` tree unchanged by the squash-merge `ccf00623c`. It was re-read
at `b17415d20`, where nothing modelled here changed: `ChainTypeManager.sol` lost the
`INTEROP_CENTER` immutable and its constructor argument (so its lines moved), `CTMRelease.sol`
gained constructor checks on the L2 table and on zero facet addresses (none on the getters read
here), and `CTMTransition.sol`'s constructor still derives the two versions (:61-64).

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.VersionRegistry` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.VersionRegistry`.

## The state

Three storage variables of `state-transition/ChainTypeManager.sol` carry the version
state of the registry-driven upgrade system:

    uint256 public protocolVersion;                                               // :90
    address public currentRelease;                                                // :161
    mapping(uint256 oldProtocolVersion => address transition) public upgradeTransition;  // :167

plus the legacy commitment `__LEGACY_upgradeCutHash` (:110), which the one remaining
cut-taking edge (the registry bootstrap) still writes. The model adds one **ghost**
map, `relAt`, which is not a storage slot: the release that was installed when the CTM
reached each version. `_setCurrentRelease` is the only place a release is installed
and it is always called right after `protocolVersion` moved, so `relAt v` is the
release "of" version `v`. It is what lets the properties say "R_v".

## The writers

Only these entry points change these variables (everything else on the CTM —
deadlines, validators, freezing, chain creation — leaves them alone):

* `initialize` (:270-293): `protocolVersion = ICTMRelease(R).protocolVersion();` (:288),
  then `_setCurrentRelease(R)` (:292). This is `initState`.
* `setNewVersionUpgradeFromTransition(T)` (:403-418), the registry commit — `Op.commit`.
* `replaceUpgradeTransition(E, R')` (:424-443) — `Op.replace`.
* `setNewVersionUpgrade(cut, old, deadline, R)` (:794-813), the legacy cut-taking
  commit, kept for the bootstrap edge — `Op.legacyCommit`; and its repair
  `setUpgradeDiamondCut` (:837-850) — `Op.legacyRecut`.

`_setCurrentRelease` (:300-318) is shared by the first, second and fourth:

    if (_release == address(0)) { revert ZeroAddress(); }                         // :301-303
    release.validate();                                                           // :305
    if (releaseProtocolVersion != protocolVersion) { revert ReleaseProtocolVersionMismatch(...); } // :307-309
    currentRelease = _release;                                                    // :316

and `_commitVersionEdge` (:523-537) is shared by both commits:

    if (previousProtocolVersion != _oldProtocolVersion) { revert OutdatedProtocolVersion(...); } // :526-528
    if (_newProtocolVersion <= _oldProtocolVersion) { revert ProtocolVersionTooSmall(...); }       // :532-534
    protocolVersion = _newProtocolVersion;                                        // :535

## Modelling choices

* **A revert is the absence of a step**, as in `ProxyUpgradeRowLib`.
* **Objects are their getters.** A `CTMRelease` or `CTMTransition` is write-once: "There
  is NO state-mutating function on this contract" (`upgrades/registry/objects/CTMRelease.sol:32-34`,
  `CTMTransition.sol:48-49`). The CTM only reads them, so each is modelled by the values
  its getters return, as fixed functions of its address (`World`). A transition's
  getters are *independent* fields here: the CTM never sees how they were computed. The
  constructor's derivation `derivedOldProtocolVersion = ICTMRelease(fromRelease).protocolVersion()`
  (`CTMTransition.sol:61-64`) is the predicate `World.Genuine`, used only where a result
  needs it.
* **Checks that only reject, and read nothing the model tracks, are omitted**:
  `_requireExecutable` (`T.validate()` and published L2 bytecodes, :449-452),
  `release.validate()` (:305), the genesis-batch-hash check (:311-314) and the deadline
  equality of a replacement (:483-489). Omitting a rejecting check only adds runs, so
  every safety result holds a fortiori. The two countermodels that need a step to
  *exist* use objects that can meet each omitted check (deployed code, equal deadlines,
  nonzero genesis hash), since those checks constrain fields the model does not read.
* **The caller is not modelled.** Every writer is `onlyOwner` (the bound
  `CTMUpgradeExecutor`); the model admits any caller, which again only adds runs.
* **A call to address zero reverts**: it has no code, and the getters' return data
  cannot be decoded. This is why the commit and replacement steps require the
  transition addresses to be nonzero.
* **Versions are `ℕ`.** The source compares them and never does arithmetic on them.
* **A legacy cut is abstract** (`LegacyCut`): either the bootstrap migration's cut,
  which names the very release the same call installs, or an opaque cut.
* **Pre-registry states.** The registry setters exist only on the new CTM
  implementation, and the bootstrap swaps that implementation in and calls
  `setNewVersionUpgrade` in one transaction (`bootstrap/RegistryBootstrapMigration.sol:258-259,
  279-295`). So a registry CTM is first observable either just after `initialize` or
  just after the bootstrap's legacy commit: `initState` and `bootstrapState`. In both,
  `currentRelease` is nonzero.
-/

namespace Contracts.ChainTypeManager

open Clear

/-- Addresses as 256-bit words; `0` is the zero address. -/
abbrev Address := UInt256

/-- Point update of a mapping. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

/-! ## Facet routing, as releases describe it

A release's facet set is `genesisFacets()` (rows of facet address and freezability),
each facet's selectors read from its own `selectors()` self-description
(`libraries/TransitionDerivationLib.sol:172-183`). The model flattens it to one entry
per selector: the selector and the `(facet, isFreezable)` it routes to. -/

/-- A function selector (`bytes4`); only equality matters. -/
abbrev Selector := ℕ

/-- Where a diamond routes a selector: the facet address and its freezability
(`Diamond.SelectorToFacet`). -/
abbrev Route := Address × Bool

/-- A release's routing, flattened in row order. -/
abbrev ReleaseRows := List (Selector × Route)

/-- The getters of a transition object that the CTM and the chains read:
`oldProtocolVersion()`, `newProtocolVersion()`, `fromRelease()`, `newRelease()`. -/
structure TransitionView where
  /-- `oldProtocolVersion()`. -/
  old : ℕ
  /-- `newProtocolVersion()`; also the version `upgradeTarget()` lands a chain on. -/
  new : ℕ
  /-- `fromRelease()`. -/
  fromRel : Address
  /-- `newRelease()`. -/
  newRel : Address
deriving DecidableEq

/-- The deployed write-once objects, read through their getters. -/
structure World where
  /-- `ICTMRelease(R).protocolVersion()`. -/
  relVersion : Address → ℕ
  /-- A release's flattened routing (`genesisFacets()` and each facet's `selectors()`). -/
  relRows : Address → ReleaseRows
  /-- A transition's getters. -/
  tr : Address → TransitionView

/-- What `CTMTransition`'s constructor establishes about its edge
(`upgrades/registry/objects/CTMTransition.sol:61-64`):

    uint256 oldVersion = ICTMRelease(_manifest.fromRelease).protocolVersion();
    uint256 newVersion = ICTMRelease(_manifest.newRelease).protocolVersion();
    derivedOldProtocolVersion = oldVersion;
    derivedNewProtocolVersion = newVersion;

The CTM itself never checks the first equation on a replacement; see
`Properties.NonGenuineReplacementBreaksSlotVersion`. -/
def World.Genuine (W : World) (t : Address) : Prop :=
  (W.tr t).old = W.relVersion (W.tr t).fromRel ∧ (W.tr t).new = W.relVersion (W.tr t).newRel

/-- The value of `__LEGACY_upgradeCutHash[v]`, abstracted to what a chain crossing that
edge will execute. -/
inductive LegacyCut
  /-- Nothing committed (`bytes32(0)`). -/
  | none
  /-- `CTMUpgradeComposer.buildBootstrapUpgradeCutData(migration)` for a bootstrap
  migration whose genesis release is `release` — the cut
  `RegistryBootstrapMigration.migrate` passes together with that same release
  (`bootstrap/RegistryBootstrapMigration.sol:290-295`). -/
  | bootstrap (release : Address)
  /-- Any other cut. -/
  | opaque
deriving DecidableEq

/-- The CTM's version state. -/
structure CTM where
  /-- `protocolVersion` (:90). -/
  pv : ℕ
  /-- `currentRelease` (:161). -/
  cur : Address
  /-- `upgradeTransition` (:167); zero means nothing committed. -/
  ut : ℕ → Address
  /-- `__LEGACY_upgradeCutHash` (:110), abstracted. -/
  legacy : ℕ → LegacyCut
  /-- Ghost: the release installed when the CTM reached each version; zero if none. -/
  relAt : ℕ → Address

/-- The writers of the version state. -/
inductive Op
  /-- `setNewVersionUpgradeFromTransition(t)`. -/
  | commit (t : Address)
  /-- `replaceUpgradeTransition(e, r)`. -/
  | replace (e r : Address)
  /-- `setNewVersionUpgrade(cut, protocolVersion, deadline, R)`; the flag says whether
  `cut` is the bootstrap migration's cut for `R`. -/
  | legacyCommit (R : Address) (bootstrapForm : Bool)
  /-- `setUpgradeDiamondCut(cut, v)`. -/
  | legacyRecut (v : ℕ)
deriving DecidableEq

/-- The version edges: the operations that move `protocolVersion`. -/
def Op.isEdge : Op → Bool
  | .commit _ => true
  | .legacyCommit _ _ => true
  | _ => false

/-- The slot a registry commit writes: `upgradeTransition[t.oldProtocolVersion()]`. -/
def Op.commitDeparture (W : World) : Op → Option ℕ
  | .commit t => some (W.tr t).old
  | _ => none

/-- One successful call of a writer. -/
inductive CStep (W : World) : CTM → Op → CTM → Prop
  /-- `setNewVersionUpgradeFromTransition` (:403-418):

        if (fromRelease != currentRelease) { revert TransitionReleaseMismatch(...); }  // :405-408
        _commitVersionEdge(oldProtocolVersion, newProtocolVersion);                    // :412
        _recordTransition(oldProtocolVersion, newProtocolVersion, _transition);        // :416
        _setCurrentRelease(_transition.newRelease());                                  // :417

  `_recordTransition` writes `upgradeTransition[_oldProtocolVersion] = address(_transition)`
  (:464). `_setCurrentRelease` compares the new release's version against
  `protocolVersion` *after* `_commitVersionEdge` set it to the new version. -/
  | commit {s : CTM} {t : Address} :
      t ≠ 0 →
      (W.tr t).fromRel = s.cur →
      s.pv = (W.tr t).old →
      (W.tr t).old < (W.tr t).new →
      (W.tr t).newRel ≠ 0 →
      W.relVersion (W.tr t).newRel = (W.tr t).new →
      CStep W s (.commit t)
        { s with pv := (W.tr t).new, cur := (W.tr t).newRel,
                 ut := upd s.ut (W.tr t).old t,
                 relAt := upd s.relAt (W.tr t).new (W.tr t).newRel }
  /-- `replaceUpgradeTransition` (:424-443):

        address committed = upgradeTransition[oldProtocolVersion];                // :429
        if (committed != address(_expectedTransition)) { revert TransitionNotCommitted(...); } // :430-432
        if (address(_replacement) == committed) { revert UpgradeTransitionUnchanged(committed); } // :433-435
        _requireSameDeparture(_expectedTransition, _replacement);               // :437 → :472-478
        _requireOnwardDestination(_expectedTransition, _replacement);           // :439 → :498-518
        _recordTransition(oldProtocolVersion, _replacement.newProtocolVersion(), _replacement); // :442

  where `oldProtocolVersion = _expectedTransition.oldProtocolVersion()` (:428). The
  onward-destination check:

        if (targetVersion < replacedTargetVersion) { revert ProtocolVersionTooSmall(...); } // :501-503
        if (targetVersion == protocolVersion) { continuation = currentRelease; }            // :506-507
        else { address onward = upgradeTransition[targetVersion];
               if (onward == address(0)) { revert NoCommittedUpgradeCutForVersion(...); }  // :510-512
               continuation = ICTMTransition(onward).fromRelease(); }                       // :513
        if (destination != continuation) { revert TransitionReleaseMismatch(...); }        // :515-517

  Nothing compares `_replacement.oldProtocolVersion()` with the slot it is written to. -/
  | replace {s : CTM} {e r : Address} :
      e ≠ 0 → r ≠ 0 →
      s.ut (W.tr e).old = e →
      r ≠ e →
      (W.tr r).fromRel = (W.tr e).fromRel →
      (W.tr e).new ≤ (W.tr r).new →
      ((W.tr r).new = s.pv → (W.tr r).newRel = s.cur) →
      ((W.tr r).new ≠ s.pv →
        s.ut (W.tr r).new ≠ 0 ∧ (W.tr r).newRel = (W.tr (s.ut (W.tr r).new)).fromRel) →
      CStep W s (.replace e r) { s with ut := upd s.ut (W.tr e).old r }
  /-- `setNewVersionUpgrade` (:794-813), whose `_oldProtocolVersion` must be the current
  version (:804 → :526-528):

        if (_newRelease == address(0)) { revert ZeroAddress(); }                 // :800-802
        uint256 newProtocolVersion = ICTMRelease(_newRelease).protocolVersion(); // :803
        _commitVersionEdge(_oldProtocolVersion, newProtocolVersion);             // :804
        setUpgradeDiamondCutInner(_cutData, _oldProtocolVersion);                // :809
        _setCurrentRelease(_newRelease);                                         // :812

  It does not touch `upgradeTransition`. -/
  | legacyCommit {s : CTM} {R : Address} {b : Bool} :
      R ≠ 0 →
      s.pv < W.relVersion R →
      CStep W s (.legacyCommit R b)
        { s with pv := W.relVersion R, cur := R,
                 legacy := upd s.legacy s.pv (if b then LegacyCut.bootstrap R else LegacyCut.opaque),
                 relAt := upd s.relAt (W.relVersion R) R }
  /-- `setUpgradeDiamondCut` (:837-850): refused for a registry-committed version
  (:843-845) and for a version with no legacy cut (:846-848). The new cut is arbitrary. -/
  | legacyRecut {s : CTM} {v : ℕ} :
      s.ut v = 0 →
      s.legacy v ≠ LegacyCut.none →
      CStep W s (.legacyRecut v) { s with legacy := upd s.legacy v LegacyCut.opaque }

/-- A sequence of successful calls. -/
inductive CRun (W : World) : CTM → List Op → CTM → Prop
  | nil {s : CTM} : CRun W s [] s
  | cons {s s' s'' : CTM} {op : Op} {ops : List Op} :
      CStep W s op s' → CRun W s' ops s'' → CRun W s (op :: ops) s''

/-- The state `initialize(R)` leaves (:270-293). -/
def initState (W : World) (R : Address) : CTM where
  pv := W.relVersion R
  cur := R
  ut := fun _ => 0
  legacy := fun _ => LegacyCut.none
  relAt := upd (fun _ => 0) (W.relVersion R) R

/-- The state `RegistryBootstrapMigration.migrate` leaves on a legacy CTM that was at
version `old`: the legacy commit of the bootstrap cut, installing the genesis release
`R`. Older versions carry pre-registry legacy cuts, which are opaque. -/
def bootstrapState (W : World) (old : ℕ) (R : Address) : CTM where
  pv := W.relVersion R
  cur := R
  ut := fun _ => 0
  legacy := upd (fun v => if v < old then LegacyCut.opaque else LegacyCut.none) old (LegacyCut.bootstrap R)
  relAt := upd (fun _ => 0) (W.relVersion R) R

/-- The invariant of the version state. `relAt v` is "R_v". -/
structure CtmInv (W : World) (s : CTM) : Prop where
  /-- A registry CTM always has a release. -/
  curNonzero : s.cur ≠ 0
  /-- The current release is the release of the current version. -/
  curAtVersion : s.relAt s.pv = s.cur
  /-- Releases are recorded only at versions reached, each at its own version. -/
  relAtSound : ∀ w, s.relAt w ≠ 0 → w ≤ s.pv ∧ W.relVersion (s.relAt w) = w
  /-- Every committed slot departs from the release of its version and lands on the
  release of a later, reached version. -/
  slots : ∀ v, s.ut v ≠ 0 →
    v < s.pv ∧ (W.tr (s.ut v)).fromRel = s.relAt v ∧ s.relAt v ≠ 0 ∧
    v < (W.tr (s.ut v)).new ∧ (W.tr (s.ut v)).newRel = s.relAt (W.tr (s.ut v)).new ∧
    s.relAt (W.tr (s.ut v)).new ≠ 0
  /-- A bootstrap cut names the release installed at its target version. -/
  bootstraps : ∀ v R, s.legacy v = LegacyCut.bootstrap R →
    v < W.relVersion R ∧ s.relAt (W.relVersion R) = R ∧ R ≠ 0

/-! ## Witness data

A concrete world for the witnesses and the countermodel. Releases `100`, `200`, `250`
at versions `1`, `2`, `3`; transitions `300` (`1 → 2`), `600` (`2 → 3`), the genuine
replacement `400` of `300`, and `500`, which departs from release `100` but reports
`oldProtocolVersion() = 7`. -/

/-- Release versions. -/
def wRelVersion : Address → ℕ := fun a =>
  if a = 100 then 1 else if a = 200 then 2 else if a = 250 then 3 else 0

/-- Release routing: two selectors, each release on its own facet. -/
def wRows : Address → ReleaseRows := fun a =>
  if a = 100 then [(1, (11, false)), (2, (11, false))]
  else if a = 200 then [(1, (21, false)), (2, (21, false))]
  else if a = 250 then [(1, (31, false)), (2, (31, false))]
  else []

/-- Transition getters. -/
def wTr : Address → TransitionView := fun a =>
  if a = 300 then ⟨1, 2, 100, 200⟩
  else if a = 400 then ⟨1, 2, 100, 200⟩
  else if a = 500 then ⟨7, 2, 100, 200⟩
  else if a = 600 then ⟨2, 3, 200, 250⟩
  else ⟨0, 0, 0, 0⟩

/-- The witness world. -/
def wWorld : World := ⟨wRelVersion, wRows, wTr⟩

end Contracts.ChainTypeManager
