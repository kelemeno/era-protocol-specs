import EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTiming
import EraSpec.Contracts.ChainTypeManager.Specs.Enabledness

/-!
# Model: the second-proof gate on every chain upgrade (draft/v0.35.0)

Source: era-contracts branch `draft/v0.35.0` at commit
**`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`** (2026-11-16). Every `file:line` below is at that
commit; paths are relative to `l1-contracts/contracts/` unless they start with `protocol-docs/` or
`protocol-ops/`. The model was first written at `d9f678900` (2026-11-06). Between the two commits,
of the files cited here only `upgrades/registry/objects/CTMRelease.sol` and `CTMTransition.sol`
changed (new constructor checks on the L2 bytecode table, a member-wise L2 table comparison, and
shifted lines; the verifier getter, the code-existence checks of `validate()` and
`upgradeTarget()` are unchanged), and `protocol-docs/interop-gating.md` gained :43-48 (commit
`9775be946`), quoted under "The release policy" below.

**This file is definitions only.** The results are in
`EraSpec.Contracts.SecondProofSystem.Properties.UpgradeGateV35` and are proved in
`EraSpec.Contracts.SecondProofSystem.Proofs.UpgradeGateV35`.

## The flag and the gate

A chain's admin may make the chain require its second proof system, once and for good
(`state-transition/chain-deps/facets/Admin.sol:453-465`):

    function permanentlyRequireSecondProofSystem() external onlyAdmin onlySettlementLayer {
        if (s.secondProofSystemRequired) { revert SecondProofSystemAlreadyRequired(); }   // :455-457
        uint256 proofMode = _getProofMode();                                               // :458
        if (proofMode != ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE) { revert NotMultiProofMode(proofMode); } // :459-461
        s.secondProofSystemRequired = true;                                                // :463

`_getProofMode()` is `IZKsyncOSVerifier(address(s.verifier)).getProofMode(s.disabledProofSystems)`
(`state-transition/chain-deps/facets/ZKChainBase.sol:188-190`). A search of
`l1-contracts/contracts/` finds one writer of the flag (`Admin.sol:463`, which writes `true`),
one of the mask (`Admin.sol:430`) and two of `s.verifier` (`upgrades/BaseZkSyncUpgrade.sol:151`,
`state-transition/chain-deps/DiamondInit.sol:118`), besides code that a cut's init
delegatecalls.

Every diamond cut a v35 Admin facet executes goes through `_executeDiamondCut`
(`Admin.sol:116-128`):

    Diamond.diamondCut(_diamondCut);                                                       // :118
    // Repeats the check of `BaseZkSyncUpgrade._setVerifier`, for an upgrade that sets the verifier without it.
    if (s.secondProofSystemRequired) {
        uint256 proofMode = IZKsyncOSVerifier(address(s.verifier)).getProofMode(0);         // :122
        if (proofMode != ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE) { revert NotMultiProofMode(proofMode); } // :123-125
    }

It is reached by `upgradeChainFromVersion` (:558-590, cut at :586), `executeUpgrade`
(:592-595, the CTM owner's break-glass cut through `ChainTypeManager.executeUpgrade`,
`state-transition/ChainTypeManager.sol:626-628`) and `genesisUpgrade` (:597-609). The check reads
the **post-cut** state with the mask **`0`**, not the chain's `s.disabledProofSystems`.

The engine repeats it where it installs a verifier (`BaseZkSyncUpgrade.sol:133-153`):

    if (_newVerifier == IVerifier(address(0))) { revert ZeroAddress(); }                    // :138-140
    if (s.secondProofSystemRequired) {
        uint256 proofMode = IZKsyncOSVerifier(address(_newVerifier)).getProofMode(0);       // :144
        if (proofMode != ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE) { revert NotMultiProofMode(proofMode); } // :145-147
    }
    s.verifier = _newVerifier;                                                             // :151

A registry edge installs the **target release's** verifier
(`upgrades/DefaultUpgrade.sol:65-84`):

    (uint256 newProtocolVersion, uint256 upgradeTimestamp, address newRelease) = _object.upgradeTarget(); // :66
    address newVerifier = ICTMRelease(newRelease).verifier();                              // :67
    if (newVerifier == address(0)) { revert ZeroAddress(); }                               // :69-71
    _upgrade({ ..., _verifier: newVerifier, ... });                                        // :72-83

and `_upgrade` calls `_setVerifier` for a nonzero verifier (`BaseZkSyncUpgrade.sol:97-99`),
whether or not the diamond is on its settlement layer. `CTMTransition.upgradeTarget()` returns the
manifest's `newRelease` (`upgrades/registry/objects/CTMTransition.sol:223-226`).
`BootstrapUpgrade.upgradeFromBootstrap` ends in the same `_upgradeFromCommittedObject`
(`upgrades/BootstrapUpgrade.sol:42`). The genesis upgrade passes `_verifier: address(0)`
(`upgrades/L1GenesisUpgrade.sol:42-47`): `DiamondInit` has already installed the current
release's verifier (`DiamondInit.sol:112-118`, nonzero at :115-117) and writes neither the flag
nor the mask.

A release's verifier is a field of its write-once manifest (`ICTMRelease.verifier()`,
`CTMRelease.sol:86-89`; "There is NO state-mutating function on this contract", :32-34), nonzero
by construction (:35-42).

## The verifiers

`MultiProofVerifier.getProofMode` (`state-transition/verifiers/MultiProofVerifier.sol:100-109`):

    if (_disabledProofSystems & ~uint8(1 << uint8(ProofSystem.Zisk)) != 0) {
        revert InvalidDisabledProofSystemsMask(_disabledProofSystems); }                   // :102-104
    return _disabledProofSystems & uint8(1 << uint8(ProofSystem.Zisk)) == 0
        ? ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE : ZKSYNC_OS_PLONK_VERIFICATION_TYPE;     // :105-108

with `ProofSystem { Boojum, Airbender, Zisk }` (`common/Config.sol:126-130`), so the Zisk bit
is `4`, `ZKSYNC_OS_PLONK_VERIFICATION_TYPE = 2` (:105) and
`ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE = 5` (:108). The single-proof
`ZKsyncOSVerifier.getProofMode(uint8)` returns `ZKSYNC_OS_PLONK_VERIFICATION_TYPE` for every
mask (`state-transition/verifiers/ZKsyncOSVerifier.sol:103-106`). The testnet wrapper
`MultiProofTestnetVerifier` forwards to its inner verifier
(`state-transition/verifiers/MultiProofTestnetVerifier.sol:51-54`).

## The emergency switch

`setProofSystemStatus(ProofSystem.Zisk, enabled)` (`Admin.sol:415-432`) clears or sets the Zisk
bit of `s.disabledProofSystems` (:425-430). Enabling is the chain admin's; disabling a flagged
chain's Zisk is the bridgehub owner's (:417-420). Any other proof system reverts (:421-423).

## What the CTM checks when it commits

`setNewVersionUpgradeFromTransition` (`ChainTypeManager.sol:403-418`) checks the departing release
(:405-408), `_requireExecutable` (:449-452: `_transition.validate()`, which checks code existence
of the engine and the delegate composer, `CTMTransition.sol:248-254`, and the L2 bytecodes'
publication), the version edge (:412, :523-537), and installs the target release through
`_setCurrentRelease` (:300-318), whose `release.validate()` (:305) checks that the verifier
**has code** (`CTMRelease.sol:122`). Nothing on that path calls `getProofMode`.
`replaceUpgradeTransition` (:424-443) adds `_requireSameDeparture` (:472-478),
`_requireSameDeadline` (:483-489) and `_requireOnwardDestination` (:498-518), which pins a
replacement landing at the CTM's current version to `currentRelease` (:506-507) and otherwise to
the departing release of the edge committed at its target (:508-514). It does not call
`getProofMode` either.

## The release policy

So a flagged chain refuses a committed edge whose target release ships a verifier that fails the
gate, and nothing on L1 prevents such a commit. The source documents this
(`protocol-docs/interop-gating.md:43-48`): "every later release of that CTM must ship a multi-proof
verifier, or the CTM commits an edge those chains can never cross. Nothing on L1 knows about the
lock, so `protocol-ops` package verification enforces it before the vote". That check is
`judge_proof_mode_kept` (`protocol-ops/src/upgrade_verification/registry/upgrade.rs:915-955`), run
on every transition the package verifies (`upgrade.rs:856-860`), a commit's (`upgrade.rs:193-204`)
and a replacement's (`protocol-ops/src/upgrade_verification/registry/replacement.rs:100-111`). It
reports an error exactly when the departing release's verifier answers MULTI to `getProofMode(0)`
and the arriving release's does not (or cannot be read); an unreadable departing mode is only a
warning. `KeepsProofMode` is that condition.

## Modelling choices

* **The rest is `ChainTypeManager.UpgradeTiming`.** That model (written at `e561b9cc2`) is
  reused unchanged for the routing, the CTM, the callers, the block time, the notifier and the
  batch/settlement-layer gates. At `b17415d20` its checks are at these lines, where the code is
  what `UpgradeTiming`'s docstrings quote (checked by diffing `e561b9cc2` against `b17415d20`:
  apart from the gate additions and `setProofSystemStatus`'s authorisation, the changes in these
  files are comments, the `INTEROP_CENTER` immutable and the executor base refactor):
  `Admin.upgradeChainFromVersion` — modifier :562 (`ZKChainBase.sol:127-132`), cut lookup
  :566-568, version :570-572, notifier gate :577-585, cut :586, version increase :587-589;
  `DefaultUpgrade.upgradeFromTransition` — batches :30, routing guard :36, derived cuts :40;
  `BaseZkSyncUpgrade._upgrade` — manifest time :82-84, settlement layer :87-94;
  `CTMUpgradeExecutor.upgradeChain` (`upgrades/registry/executors/CTMUpgradeExecutor.sol:92-107`);
  `ChainTypeManager.upgradeChainFromVersion` (:618-621);
  `ServerNotifier.setUpgradeTimestamp` (`governance/ServerNotifier.sol:113-132`).
  `UpgradeTiming` omits the nonzero-verifier check (`DefaultUpgrade.sol:69-71`); this model
  adds it back (`VerifierGate.nonzero`).
* **Per chain, three more storage fields** (`GateState`): `s.secondProofSystemRequired`
  (`state-transition/chain-deps/ZKChainStorage.sol:304`), `s.verifier` and
  `s.disabledProofSystems` (:290, a `uint8`, here a natural number).
* **`getProofMode` is configuration** (`GateConfig.proofMode`): the answer of the code at each
  verifier address for each mask, `none` for a revert. Verifiers are external contracts, so it is
  arbitrary; `multiProofMode` and `singleProofMode` transcribe the two deployed verifiers.
* **`ICTMRelease(R).verifier()` is configuration** (`GateConfig.relVerifier`), fixed because the
  release is write-once. Nothing forces it nonzero; results that need a nonzero target verifier
  say so.
* **A revert is the absence of a step.** Every registry or bootstrap cut step carries both
  checks (`VerifierGate`): the engine's `_setVerifier` check and `_executeDiamondCut`'s post-cut
  check. Those engines do not write the flag (their derived facet cuts carry no init), so both
  read the same flag and the same verifier: the two fields of `VerifierGate` are the same
  condition.
* **The break-glass cut** (`GLabel.breakGlass`) runs an arbitrary init, which can write any
  storage slot, the flag included. It is `ChainRouting`'s `arbitraryCut` plus an arbitrary new
  `GateState`, subject only to the post-cut check. So it can install a MULTI verifier, or clear
  the flag.
* **Every cut is checked as if by the v35 Admin facet** (`MODEL-SECOND-PROOF-GATE` in
  `ASSUMPTIONS.md`). The post-cut check is code of `Admin._executeDiamondCut`. A break-glass cut
  may replace the Admin facet by one without the check, and a chain crossing an opaque legacy
  edge runs a pre-v35 Admin facet. The model gates those cuts and every later one as if the v35
  facet were still routed. So the results that a flagged chain's verifier passes the gate
  (`FlaggedCutsKeepMultiProof`, `FlaggedChainsStayMultiProof`) hold for chains that keep the
  v35 Admin facet, and so does the last item of `EscapesUnlockTheLockedChain` (no break-glass cut
  leaves a flagged chain on a verifier that fails the gate). The lock results
  (`LockedChainCannotUpgrade`, `StuckChainCannotUpgrade` and those built on them) use only the
  engine's own check (`BaseZkSyncUpgrade.sol:143-148`, `VerifierGate.setVerifier`), which runs
  whatever Admin facet executes the cut. A chain crossing the bootstrap edge also runs a pre-v35
  Admin facet, whose `_executeDiamondCut` has no post-cut check; there the engine's
  `_setVerifier` check (v35 code) reads the same slot and is the same condition, so the model's
  bootstrap step admits exactly the crossings the engine admits. As in `UpgradeTiming`, the
  engine of a registry edge is `DefaultUpgrade`.
* **The mask is a natural number.** The source's `uint8` is below `256`. `freshGate` and
  `setProofSystemStatus` keep a mask below `256`; a break-glass cut may write any value, which
  only adds runs. The statement about `MultiProofVerifier.getProofMode` carries the bound as a
  premise.
* **Genesis and migration in** deploy a fresh diamond: `DiamondInit` installs the current
  release's verifier and leaves the flag and the mask zero. A migrated chain's commitment
  (`ZKChainCommitment`, `common/Config.sol:233-261`) carries neither the flag nor the mask.
  The genesis cut then runs `_executeDiamondCut` with the flag unset, so the gate passes.
  `ChainRouting`'s migration in deploys a diamond for a chain id that has none on this CTM; a
  chain returning to a diamond it kept is outside this model. At `b17415d20` chain migrations are
  disabled in production (`CHAIN_MIGRATIONS_ENABLED = false`, `common/Config.sol:320`): the
  `whenMigrationsEnabled` modifier (`core/chain-asset-handler/ChainAssetHandlerBase.sol:151-155`)
  reverts `bridgeMint` (:365) and `bridgeBurn` (:201), so migration in cannot happen there. The
  step is kept as an over-approximation, which only adds runs.
* **The bootstrap reset** installs the migration's genesis release's verifier through
  `_upgradeFromCommittedObject` (`BootstrapUpgrade.sol:42`), with the engine's check.
* **`setProofSystemStatus`'s argument** is always `ProofSystem.Zisk`: any other reverts.
* **The settlement-layer test** of `onlySettlementLayer` (`ZKChainBase.sol:141-146`,
  `s.settlementLayer == address(0)`) is `DiamondAux.slVersion = none`, as in `UpgradeTiming`.
* **Omitted reject-only checks**, as in `UpgradeTiming`: the L2 upgrade transaction, the semver
  shape, the precondition checker, code existence, the `onlyL1` modifiers. Omitting them only
  adds runs, so a negative result (a step cannot happen) holds at the source within the bounds
  of the Admin-facet item above; a positive result (a step exists) means no check the model
  keeps blocks it.
-/

namespace Contracts.SecondProofSystem.UpgradeGateV35

open Contracts.ChainTypeManager

/-! ## Constants and the two verifiers -/

/-- `ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE` (`common/Config.sol:108`). -/
def MULTI : ℕ := 5

/-- `ZKSYNC_OS_PLONK_VERIFICATION_TYPE` (`common/Config.sol:105`). -/
def PLONK : ℕ := 2

/-- `uint8(1 << uint8(ProofSystem.Zisk))`: `Zisk` is the third member of `ProofSystem`
(`common/Config.sol:126-130`). -/
def ziskBit : ℕ := 4

/-- `~uint8(1 << uint8(ProofSystem.Zisk))` as a `uint8`: `0xFB`. -/
def notZiskBit : ℕ := 251

/-- `MultiProofVerifier.getProofMode(_disabledProofSystems)`
(`state-transition/verifiers/MultiProofVerifier.sol:100-109`), for a `uint8` mask `m`; `none`
is the revert `InvalidDisabledProofSystemsMask`. -/
def multiProofMode (m : ℕ) : Option ℕ :=
  if m &&& notZiskBit ≠ 0 then none
  else if m &&& ziskBit = 0 then some MULTI else some PLONK

/-- `ZKsyncOSVerifier.getProofMode(uint8)` (`state-transition/verifiers/ZKsyncOSVerifier.sol:103-106`):
`ZKSYNC_OS_PLONK_VERIFICATION_TYPE` whatever the mask. -/
def singleProofMode (_ : ℕ) : Option ℕ := some PLONK

/-! ## Configuration and state -/

/-- The gated model's configuration. -/
structure GateConfig where
  /-- `UpgradeTiming`'s configuration: the deployed objects, the executor, the CTM, the owners,
  the transition schedules. -/
  T : TimedConfig
  /-- `ICTMRelease(R).verifier()` (`CTMRelease.sol:86-89`), fixed: the manifest is write-once. -/
  relVerifier : Address → Address
  /-- `IZKsyncOSVerifier(a).getProofMode(mask)` of the code at verifier address `a`; `none` is a
  revert. -/
  proofMode : Address → ℕ → Option ℕ
  /-- `IOwnable(s.bridgehub).owner()` (`Admin.sol:417`). -/
  bridgehubOwner : Address

/-- The gate's test of a verifier: `getProofMode(0) == ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE`
(`Admin.sol:122-125`, `BaseZkSyncUpgrade.sol:144-147`). A revert of `getProofMode` fails it. -/
def IsMulti (G : GateConfig) (a : Address) : Prop :=
  G.proofMode a 0 = some MULTI

/-- The three diamond-storage fields the gate reads. -/
structure GateState where
  /-- `s.secondProofSystemRequired` (`ZKChainStorage.sol:304`). -/
  flag : Bool
  /-- `s.verifier`. -/
  verifier : Address
  /-- `s.disabledProofSystems` (`ZKChainStorage.sol:290`), a `uint8`. -/
  disabled : ℕ

/-- `UpgradeTiming`'s system together with each chain's `GateState` (meaningful where a chain is
registered). -/
structure GSys where
  /-- The routing system, each chain's `DiamondAux`, and the notifier. -/
  ts : TimedSys
  /-- Each chain's gate fields. -/
  gate : ChainId → GateState

/-- A fresh diamond on release `R`: `DiamondInit` installs `R`'s verifier
(`DiamondInit.sol:112-118`); the flag and the mask are unwritten. -/
def freshGate (G : GateConfig) (R : Address) : GateState := ⟨false, G.relVerifier R, 0⟩

/-- The version a path departs from: the argument of `upgradeChainFromVersion`, or the
transition's `oldProtocolVersion()` (`CTMUpgradeExecutor.sol:96`). -/
def departure (W : World) : UpgradePath → ℕ
  | .direct v => v
  | .ctm v => v
  | .executor t => (W.tr t).old

/-- The verifier a registry crossing of the edge committed at `v` installs: the verifier of that
transition's `newRelease()` (`DefaultUpgrade.sol:66-67`, `CTMTransition.sol:223-226`). -/
def edgeVerifier (G : GateConfig) (s : GSys) (v : ℕ) : Address :=
  G.relVerifier (s.ts.sys.edge G.T.X.W v).newRel

/-- The checks a cut that installs verifier `a` passes on a chain whose flag is `flag`. -/
structure VerifierGate (G : GateConfig) (flag : Bool) (a : Address) : Prop where
  /-- `if (newVerifier == address(0)) { revert ZeroAddress(); }` (`DefaultUpgrade.sol:69-71`). -/
  nonzero : a ≠ 0
  /-- `_setVerifier`'s check (`BaseZkSyncUpgrade.sol:143-148`). -/
  setVerifier : flag = true → IsMulti G a
  /-- `_executeDiamondCut`'s post-cut check (`Admin.sol:121-126`); the cut did not write the flag
  and `_setVerifier` wrote `a`. -/
  postCut : flag = true → IsMulti G a

/-! ## Steps -/

/-- The labels of `UpgradeTiming` that touch no gate field: the notifier, the `DiamondAux`
writes, and the CTM's own writers. -/
def GateFree : TimedLabel → Prop
  | .base (.ctm _) => True
  | .setUpgradeTimestamp _ _ _ => True
  | .swapNotifier _ => True
  | .setAux _ _ => True
  | _ => False

/-- What happens. -/
inductive GLabel
  /-- `UpgradeTiming`'s upgrade of chain `id` through `path`, by `caller`, at block time `τ`. -/
  | upgrade (id : ChainId) (path : UpgradePath) (caller : Address) (τ : ℕ)
  /-- `createNewChain` and its `genesisUpgrade` (`ChainTypeManager.sol:703-711`). -/
  | genesis (id : ChainId)
  /-- `forwardedBridgeMint` (`ChainTypeManager.sol:746-758`). -/
  | migrateIn (id : ChainId)
  /-- Crossing the bootstrap edge. -/
  | bootstrapReset (id : ChainId)
  /-- The CTM owner's `executeUpgrade(id, cut)` (`ChainTypeManager.sol:626-628`,
  `Admin.sol:592-595`), or crossing an opaque legacy edge: any version, routing and gate fields. -/
  | breakGlass (id : ChainId) (v : ℕ) (ρ : Routing) (g : GateState)
  /-- A gate-free label of `UpgradeTiming`. -/
  | other (l : TimedLabel)
  /-- `permanentlyRequireSecondProofSystem()` on chain `id` by `caller`. -/
  | requireSecondProof (id : ChainId) (caller : Address)
  /-- `setProofSystemStatus(ProofSystem.Zisk, enabled)` on chain `id` by `caller`. -/
  | setProofSystemStatus (id : ChainId) (caller : Address) (enabled : Bool)

/-- One successful transaction. -/
inductive GStep (G : GateConfig) : GSys → GLabel → GSys → Prop
  /-- `upgradeChainFromVersion` by any of the three paths: `UpgradeTiming`'s step, then the
  target release's verifier is installed through both checks. -/
  | upgrade {s : GSys} {id : ChainId} {path : UpgradePath} {caller : Address} {τ : ℕ}
      {ts' : TimedSys} :
      TimedStep G.T s.ts (.upgrade id path caller τ) ts' →
      VerifierGate G (s.gate id).flag (edgeVerifier G s (departure G.T.X.W path)) →
      GStep G s (.upgrade id path caller τ)
        ⟨ts', upd s.gate id { s.gate id with verifier := edgeVerifier G s (departure G.T.X.W path) }⟩
  /-- `createNewChain`: `DiamondInit` with a nonzero release verifier (`DiamondInit.sol:115-117`),
  then `genesisUpgrade`, whose post-cut check reads an unset flag. -/
  | genesis {s : GSys} {id : ChainId} {ts' : TimedSys} :
      TimedStep G.T s.ts (.base (.genesis id)) ts' →
      G.relVerifier s.ts.sys.ctm.cur ≠ 0 →
      GStep G s (.genesis id) ⟨ts', upd s.gate id (freshGate G s.ts.sys.ctm.cur)⟩
  /-- `forwardedBridgeMint`: a fresh diamond as at genesis. -/
  | migrateIn {s : GSys} {id : ChainId} {ts' : TimedSys} :
      TimedStep G.T s.ts (.base (.migrateIn id)) ts' →
      G.relVerifier s.ts.sys.ctm.cur ≠ 0 →
      GStep G s (.migrateIn id) ⟨ts', upd s.gate id (freshGate G s.ts.sys.ctm.cur)⟩
  /-- The bootstrap reset onto release `R`: installs `R`'s verifier through both checks (at the
  source only the engine's runs; it is the same condition). -/
  | bootstrapReset {s : GSys} {id : ChainId} {c : Chain} {R : Address} {ts' : TimedSys} :
      s.ts.sys.chains id = some c →
      s.ts.sys.ctm.legacy c.pv = LegacyCut.bootstrap R →
      TimedStep G.T s.ts (.base (.bootstrapReset id)) ts' →
      VerifierGate G (s.gate id).flag (G.relVerifier R) →
      GStep G s (.bootstrapReset id)
        ⟨ts', upd s.gate id { s.gate id with verifier := G.relVerifier R }⟩
  /-- The break-glass cut: any version, routing and gate fields, subject to the post-cut check
  on the state the cut leaves (`Admin.sol:121-126`). -/
  | breakGlass {s : GSys} {id : ChainId} {v : ℕ} {ρ : Routing} {g : GateState} {ts' : TimedSys} :
      TimedStep G.T s.ts (.base (.arbitraryCut id v ρ)) ts' →
      (g.flag = true → IsMulti G g.verifier) →
      GStep G s (.breakGlass id v ρ g) ⟨ts', upd s.gate id g⟩
  /-- A gate-free step of `UpgradeTiming`. -/
  | other {s : GSys} {l : TimedLabel} {ts' : TimedSys} :
      GateFree l → TimedStep G.T s.ts l ts' →
      GStep G s (.other l) ⟨ts', s.gate⟩
  /-- `permanentlyRequireSecondProofSystem()` (`Admin.sol:453-465`): `onlyAdmin`,
  `onlySettlementLayer`, not yet set, and `_getProofMode()` is MULTI under the chain's own mask. -/
  | requireSecondProof {s : GSys} {id : ChainId} {caller : Address} {c : Chain} :
      s.ts.sys.chains id = some c →
      caller = (s.ts.aux id).admin →
      (s.ts.aux id).slVersion = none →
      (s.gate id).flag = false →
      G.proofMode (s.gate id).verifier (s.gate id).disabled = some MULTI →
      GStep G s (.requireSecondProof id caller)
        ⟨s.ts, upd s.gate id { s.gate id with flag := true }⟩
  /-- `setProofSystemStatus(ProofSystem.Zisk, enabled)` (`Admin.sol:415-432`). -/
  | setProofSystemStatus {s : GSys} {id : ChainId} {caller : Address} {enabled : Bool}
      {c : Chain} :
      s.ts.sys.chains id = some c →
      caller = (if enabled = false ∧ (s.gate id).flag = true then G.bridgehubOwner
        else (s.ts.aux id).admin) →
      GStep G s (.setProofSystemStatus id caller enabled)
        ⟨s.ts, upd s.gate id { s.gate id with
          disabled := if enabled then (s.gate id).disabled &&& notZiskBit
            else (s.gate id).disabled ||| ziskBit }⟩

/-- A sequence of successful transactions. -/
inductive GRun (G : GateConfig) : GSys → List GLabel → GSys → Prop
  | nil {s : GSys} : GRun G s [] s
  | cons {s s' s'' : GSys} {l : GLabel} {ls : List GLabel} :
      GStep G s l s' → GRun G s' ls s'' → GRun G s (l :: ls) s''

/-- What a gated label is in `UpgradeTiming`: the cuts are their timed steps (a break-glass cut
is `arbitraryCut`), a gate-free label is itself, and the two gate-field writers are no timed
step at all. -/
def GLabel.timed : GLabel → List TimedLabel
  | .upgrade id path caller τ => [.upgrade id path caller τ]
  | .genesis id => [.base (.genesis id)]
  | .migrateIn id => [.base (.migrateIn id)]
  | .bootstrapReset id => [.base (.bootstrapReset id)]
  | .breakGlass id v ρ _ => [.base (.arbitraryCut id v ρ)]
  | .other l => [l]
  | .requireSecondProof _ _ => []
  | .setProofSystemStatus _ _ _ => []

/-- The labels that cut chain `id`'s diamond. -/
def GLabel.CutsChain (id : ChainId) : GLabel → Prop
  | .upgrade i _ _ _ => i = id
  | .genesis i => i = id
  | .migrateIn i => i = id
  | .bootstrapReset i => i = id
  | .breakGlass i _ _ _ => i = id
  | _ => False

/-- The break-glass steps, on any chain. -/
def GLabel.IsBreakGlass : GLabel → Prop
  | .breakGlass _ _ _ _ => True
  | _ => False

/-- The labels that can free a locked chain `id`: a break-glass cut of `id`, or a CTM writer
that moves the CTM's version (a registry or legacy commit). -/
def GLabel.Escapes (id : ChainId) : GLabel → Prop
  | .breakGlass i _ _ _ => i = id
  | .other (.base (.ctm op)) => op.isEdge = true
  | _ => False

/-- Every flagged chain's verifier passes the gate. -/
def GateInv (G : GateConfig) (s : GSys) : Prop :=
  ∀ id, (s.gate id).flag = true → IsMulti G (s.gate id).verifier

/-- A verifier that answers MULTI under some mask answers MULTI under mask `0`. Both deployed
verifiers satisfy it (`MaskMonotoneHoldsForDeployedVerifiers`). -/
def MaskMonotone (G : GateConfig) : Prop :=
  ∀ a d, G.proofMode a d = some MULTI → G.proofMode a 0 = some MULTI

/-- The state with chain `id`'s emergency mask set to `d`. -/
def GSys.withMask (s : GSys) (id : ChainId) (d : ℕ) : GSys :=
  ⟨s.ts, upd s.gate id { s.gate id with disabled := d }⟩

/-- `replaceUpgradeTransition(e, r)`'s checks **without** the `currentRelease` pin
(`ChainTypeManager.sol:506-507`): `CStep.replace`'s premises minus
`(W.tr r).new = s.pv → (W.tr r).newRel = s.cur`. -/
def ReplaceUnpinned (W : World) (s : CTM) (e r : Address) : Prop :=
  e ≠ 0 ∧ r ≠ 0 ∧ s.ut (W.tr e).old = e ∧ r ≠ e ∧ (W.tr r).fromRel = (W.tr e).fromRel ∧
    (W.tr e).new ≤ (W.tr r).new ∧
    ((W.tr r).new ≠ s.pv →
      s.ut (W.tr r).new ≠ 0 ∧ (W.tr r).newRel = (W.tr (s.ut (W.tr r).new)).fromRel)

/-- **A locked chain.** Chain `id` is at version `v` and flagged; the edge committed at `v`
lands at the CTM's own version on its current release, whose verifier fails the gate; nothing
is committed at or above the CTM's version; and no legacy cut is recorded at `v`. -/
structure Locked (G : GateConfig) (s : GSys) (id : ChainId) (v : ℕ) : Prop where
  /-- The chain is at `v`. -/
  chain : ∃ c, s.ts.sys.chains id = some c ∧ c.pv = v
  /-- The chain is flagged. -/
  flagged : (s.gate id).flag = true
  /-- An edge is committed at `v`. -/
  committed : s.ts.sys.ctm.ut v ≠ 0
  /-- It lands at the CTM's version. -/
  targetVersion : (G.T.X.W.tr (s.ts.sys.ctm.ut v)).new = s.ts.sys.ctm.pv
  /-- It lands on the current release. -/
  targetRelease : (G.T.X.W.tr (s.ts.sys.ctm.ut v)).newRel = s.ts.sys.ctm.cur
  /-- The current release's verifier fails the gate. -/
  notMulti : ¬ IsMulti G (G.relVerifier s.ts.sys.ctm.cur)
  /-- Nothing is committed at or above the CTM's version. -/
  noSlotsAhead : ∀ w, s.ts.sys.ctm.pv ≤ w → s.ts.sys.ctm.ut w = 0
  /-- No legacy cut at `v`. -/
  noLegacy : s.ts.sys.ctm.legacy v = LegacyCut.none

/-! ## The general lock

`Locked` asks that the CTM still sits at the edge's target version. `Stuck` drops that: the CTM
may have moved on any number of versions, as long as no release it has installed from the
edge's target on ships a verifier that passes the gate. -/

/-- **A stuck chain.** Chain `id` is at version `v` and flagged; an edge is committed at `v`; the
CTM satisfies its invariant; no release recorded at the edge's target version or later ships a
verifier that passes the gate; and no legacy cut is recorded at `v`. -/
structure Stuck (G : GateConfig) (s : GSys) (id : ChainId) (v : ℕ) : Prop where
  /-- The chain is at `v`. -/
  chain : ∃ c, s.ts.sys.chains id = some c ∧ c.pv = v
  /-- The chain is flagged. -/
  flagged : (s.gate id).flag = true
  /-- An edge is committed at `v`. -/
  committed : s.ts.sys.ctm.ut v ≠ 0
  /-- The CTM's version state satisfies its invariant. -/
  inv : CtmInv G.T.X.W s.ts.sys.ctm
  /-- No release installed at the edge's target version or later passes the gate. -/
  noMultiAhead : ∀ w, (G.T.X.W.tr (s.ts.sys.ctm.ut v)).new ≤ w → s.ts.sys.ctm.relAt w ≠ 0 →
    ¬ IsMulti G (G.relVerifier (s.ts.sys.ctm.relAt w))
  /-- No legacy cut at `v`. -/
  noLegacy : s.ts.sys.ctm.legacy v = LegacyCut.none

/-- The CTM writers that install a release whose verifier passes the gate: a registry commit
onto such a release, or a legacy commit of one. -/
def GLabel.InstallsMulti (G : GateConfig) : GLabel → Prop
  | .other (.base (.ctm (.commit t))) => IsMulti G (G.relVerifier (G.T.X.W.tr t).newRel)
  | .other (.base (.ctm (.legacyCommit R _))) => IsMulti G (G.relVerifier R)
  | _ => False

/-- A break-glass cut of chain `id`. -/
def GLabel.BreakGlassOf (id : ChainId) : GLabel → Prop
  | .breakGlass i _ _ _ => i = id
  | _ => False

/-! ## The release policy -/

/-- **The `protocol-ops` proof-mode check of transition `t`**
(`protocol-ops/src/upgrade_verification/registry/upgrade.rs:915-955`): if the departing release's
verifier passes the gate, so does the arriving release's. The check refuses exactly the
transitions that fail this. -/
def KeepsProofMode (G : GateConfig) (t : Address) : Prop :=
  IsMulti G (G.relVerifier (G.T.X.W.tr t).fromRel) → IsMulti G (G.relVerifier (G.T.X.W.tr t).newRel)

/-- A label that passed the release policy: a registry commit of, or a replacement by, a
transition that keeps the proof mode. Every other label carries no transition and passes
trivially (the legacy commit, kept for the bootstrap edge, names no departing release). -/
def GLabel.PassesReleasePolicy (G : GateConfig) : GLabel → Prop
  | .other (.base (.ctm (.commit t))) => UpgradeGateV35.KeepsProofMode G t
  | .other (.base (.ctm (.replace _ r))) => UpgradeGateV35.KeepsProofMode G r
  | _ => True

/-- **The invariant the release policy maintains.** The routing system satisfies `SysInv`; every
flagged chain's verifier passes the gate; every chain at a version with a recorded release runs
that release's verifier; and every committed transition keeps the proof mode. -/
structure PolicyInv (G : GateConfig) (s : GSys) : Prop where
  /-- `ChainRouting`'s invariant: `CtmInv`, and no chain ahead of the CTM. -/
  sys : SysInv G.T.X.W s.ts.sys
  /-- Every flagged chain's verifier passes the gate. -/
  gate : GateInv G s
  /-- Every chain at a version with a recorded release runs that release's verifier. -/
  onRelease : ∀ id c, s.ts.sys.chains id = some c → s.ts.sys.ctm.relAt c.pv ≠ 0 →
    (s.gate id).verifier = G.relVerifier (s.ts.sys.ctm.relAt c.pv)
  /-- Every committed transition keeps the proof mode. -/
  slotsKeep : ∀ v, s.ts.sys.ctm.ut v ≠ 0 → KeepsProofMode G (s.ts.sys.ctm.ut v)

/-! ## Witness data

The `ChainRouting` witness world extended by release `210` (version 2, release `200`'s routing,
another object), the same-target replacement `410` (1→2 onto `210`), and the skip transition
`420` (1→3 onto `250`). Verifier `700` is a `MultiProofVerifier`, `701` a single-proof
`ZKsyncOSVerifier`; every other address reverts on `getProofMode`. In `gCfg` releases `100`,
`210` and `250` ship `700` and release `200` ships `701`. Chain admins are `3`, the bridgehub
owner is `9`. -/

/-- Release versions. -/
def gRelVersion : Address → ℕ := fun a => if a = 210 then 2 else wRelVersion a

/-- Release routing. -/
def gRows : Address → ReleaseRows := fun a => if a = 210 then wRows 200 else wRows a

/-- Transition getters. -/
def gTr : Address → TransitionView := fun a =>
  if a = 410 then ⟨1, 2, 100, 210⟩ else if a = 420 then ⟨1, 3, 100, 250⟩ else wTr a

/-- The extended world. -/
def gWorld : World := ⟨gRelVersion, gRows, gTr⟩

/-- `UpgradeTiming`'s witness configuration over the extended world. -/
def gTiming : TimedConfig := { wTiming with X := { wX with W := gWorld } }

/-- The verifiers' `getProofMode`. -/
def gProofMode : Address → ℕ → Option ℕ := fun a =>
  if a = 700 then multiProofMode else if a = 701 then singleProofMode else fun _ => none

/-- The countermodel's release verifiers: release `200` ships the single-proof verifier. -/
def gRelVerifier : Address → Address := fun a => if a = 200 then 701 else 700

/-- The countermodel configuration. -/
def gCfg : GateConfig := ⟨gTiming, gRelVerifier, gProofMode, 9⟩

/-- The same configuration with every release shipping the multi-proof verifier. -/
def gCfgMulti : GateConfig := { gCfg with relVerifier := fun _ => 700 }

/-- The same configuration with only release `100` shipping the multi-proof verifier: releases
`200`, `210` and `250` all ship the single-proof one. -/
def gCfgSingle : GateConfig := { gCfg with relVerifier := fun a => if a = 100 then 700 else 701 }

/-- A fresh CTM on release `100`, no chains, empty notifier, unset gate fields. -/
def gSys0 : GSys :=
  ⟨⟨⟨initState gWorld 100, fun _ => none⟩, fun _ => ⟨0, fun _ => false, 0, 0, none⟩,
    fun _ _ => 0⟩, fun _ => ⟨false, 0, 0⟩⟩

/-- Chains `0` and `1` are created and configured; chain `0`'s admin flags it; the CTM commits
`300` (1→2, onto release `200`). -/
def gLockRun : List GLabel :=
  [.genesis 0, .other (.setAux 0 wTimingAux), .genesis 1, .other (.setAux 1 wTimingAux),
    .requireSecondProof 0 3, .other (.base (.ctm (.commit 300)))]

/-- The routing system `gLockRun` reaches. -/
def gLockSys : Sys :=
  ⟨⟨2, 200, upd (fun _ => 0) 1 300, fun _ => LegacyCut.none,
      upd (upd (fun _ => 0) 1 100) 2 200⟩,
    upd (upd (fun _ => none) 0 (some ⟨1, rowsRouting (wRows 100)⟩)) 1
      (some ⟨1, rowsRouting (wRows 100)⟩)⟩

/-- The state `gLockRun` reaches: both chains at version 1 on release `100` with verifier `700`;
chain `0` flagged, chain `1` not. -/
def gLock : GSys :=
  ⟨⟨gLockSys, upd (upd (fun _ => ⟨0, fun _ => false, 0, 0, none⟩) 0 wTimingAux) 1 wTimingAux,
      fun _ _ => 0⟩,
    upd (upd (upd (fun _ => ⟨false, 0, 0⟩) 0 ⟨false, 700, 0⟩) 1 ⟨false, 700, 0⟩) 0 ⟨true, 700, 0⟩⟩

end Contracts.SecondProofSystem.UpgradeGateV35
