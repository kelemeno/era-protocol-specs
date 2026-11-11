import EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTiming
import EraSpec.Contracts.ChainTypeManager.Specs.ProofGateAtV35

/-!
# Model: who may upgrade a chain, and when, at `draft/v0.35.0`

Source: era-contracts branch `draft/v0.35.0` at commit **`d9f678900`** (`d9f6789`), as for
`EraSpec.Contracts.ChainTypeManager.Specs.ProofGateAtV35`. Every `file:line` below is at
`d9f6789` unless it names `e561b9cc2`. Paths are relative to `l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.UpgradeTimingAtV35` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTimingAtV35`. Namespace:
`Contracts.ChainTypeManager.UpgradeTimingAtV35`.

## The `upgradeChain` NatSpec and the timed model at v35

`upgrades/registry/executors/ICTMUpgradeExecutor.sol` is byte-identical at `e561b9cc2` and
`d9f6789`. So the NatSpec `UpgradeTiming` checks is the same text at the same lines
(`:47-56`):

    /// @dev Callers:
    ///      - the OWNER may upgrade any chain at any time;
    ///      - a CHAIN'S OWN ADMIN may upgrade that chain at any time — ...
    ///      The chain's own `upgradeTimestamp` gate does NOT apply here: the chain sees the CTM as
    ///      the caller, and the CTM is exempt from it.

The code `UpgradeTiming` models, re-diffed function by function (comments stripped), at
`d9f6789`:

* **Byte-identical files:** `governance/ServerNotifier.sol` (`setUpgradeTimestamp` still
  `:113-131`), `upgrades/registry/libraries/VersionEdgeLib.sol`,
  `state-transition/chain-deps/facets/Committer.sol` and `ICTMUpgradeExecutor.sol`.
* **Same bodies at new lines:**
  * `CTMUpgradeExecutor.upgradeChain`, now `upgrades/registry/executors/CTMUpgradeExecutor.sol:92-107`
    (was `:87-102`): caller check `:93-95`, the `oldProtocolVersion()` lookup `:96-102`, the
    CTM call `:105`.
  * `ChainTypeManager.upgradeChainFromVersion`, now `state-transition/ChainTypeManager.sol:618-621`
    (was `:623-626`), and `protocolVersionDeadline` / `setProtocolVersionDeadline` /
    `protocolVersionIsActive`, now `:545-572` (was `:550-577`).
  * `Admin.upgradeChainFromVersion`, now `state-transition/chain-deps/facets/Admin.sol:559-590`
    (was `:528-559`): the cut lookup `:566-568`, the version check `:570-572`, the notifier
    gate for callers other than the admin and the CTM `:577-585`, the cut `:586`, the version
    increase `:587-589`.
  * `onlyAdminOrChainTypeManagerOrValidator`, now `facets/ZKChainBase.sol:127-132`.
  * `BaseZkSyncUpgrade._upgrade`, now `upgrades/BaseZkSyncUpgrade.sol:72-108`: the
    manifest's time gate `:82-84`, the settlement-layer order `:87-94`.
    `_requireAllBatchesExecuted` is now `:115-119`.
  * `DefaultUpgrade.upgradeFromTransition`, now `upgrades/DefaultUpgrade.sol:29-43`, with
    `_requireAllBatchesExecuted()` at `:30`.
* **Changed:** `Admin._executeDiamondCut`, which `Admin.upgradeChainFromVersion` calls at
  `:586`, and `BaseZkSyncUpgrade._setVerifier`. Both now refuse to leave a chain that requires
  its second proof system with a verifier outside multi-proof mode (#2628;
  `ProofGateAtV35` has the code). That is one more reject-only check on every upgrade path.
  It reads state `UpgradeTiming` does not track and does not read the notifier.

So this file is `UpgradeTiming` with the proof-system fields of `ProofGateAtV35` added: each
timed step carries its routing step's `ProofEffect`. The two new writers are steps of their
own, and here they carry their callers.

## Modelling choices

* **`UpgradeTiming` is kept whole.** A v35 timed step is an `UpgradeTiming.TimedStep` together
  with the proof-system effect of its routing step (`TimedProofEffect`): an upgrade has the
  transition's, a base step its own, and the notifier and `DiamondAux` writes have none. All
  of `UpgradeTiming`'s modelling choices and omitted checks are unchanged, and so is
  `ProofGateAtV35`'s reading of the proof-system checks.
* **`permanentlyRequireSecondProofSystem`** keeps its two modifiers: `onlyAdmin`
  (`facets/ZKChainBase.sol:46-51`), the caller is `(s.aux id).admin`; `onlySettlementLayer`
  (`:141-146`), the diamond is on its settlement layer, `slVersion = none`.
* **`setProofSystemStatus`** is an arbitrary write of the mask, as in `ProofGateAtV35`. Its
  caller rule (`Admin.sol:417-420`) is not modelled.
-/

namespace Contracts.ChainTypeManager.UpgradeTimingAtV35

open Contracts.ChainTypeManager
open Contracts.ChainTypeManager.ProofGateAtV35

/-- The timed system with each chain's proof-system fields. -/
structure TimedSys35 where
  /-- `UpgradeTiming`'s state. -/
  timed : TimedSys
  /-- Each chain's proof-system fields. -/
  proof : ChainId → ProofState

/-- **What a timed step does to the proof-system fields**: an upgrade has the effect of
`ChainRouting`'s transition, whatever its path; a base step has its own; writes of the notifier
and of a chain's `DiamondAux` touch no proof-system field. -/
inductive TimedProofEffect (T : TimedConfig) (P : ProofWorld) (s : TimedSys)
    (pr : ChainId → ProofState) : TimedLabel → (ChainId → ProofState) → Prop
  | upgrade {id : ChainId} {path : UpgradePath} {caller : Address} {τ : ℕ}
      {pr' : ChainId → ProofState} :
      ProofEffect T.X.W P s.sys pr (.transition id) pr' →
      TimedProofEffect T P s pr (.upgrade id path caller τ) pr'
  | base {l : Label} {pr' : ChainId → ProofState} :
      ProofEffect T.X.W P s.sys pr l pr' → TimedProofEffect T P s pr (.base l) pr'
  | setUpgradeTimestamp {id : ChainId} {caller : Address} {ts : ℕ} :
      TimedProofEffect T P s pr (.setUpgradeTimestamp id caller ts) pr
  | swapNotifier {n : ChainId → ℕ → ℕ} : TimedProofEffect T P s pr (.swapNotifier n) pr
  | setAux {id : ChainId} {a : DiamondAux} : TimedProofEffect T P s pr (.setAux id a) pr

/-- What happens at v35. -/
inductive TimedLabel35
  /-- An `UpgradeTiming` transaction. -/
  | timed (l : TimedLabel)
  /-- `Admin.permanentlyRequireSecondProofSystem()` on chain `id`, called by `caller`. -/
  | requireSecondProofSystem (id : ChainId) (caller : Address)
  /-- `Admin.setProofSystemStatus` on chain `id`, leaving the mask `m`. -/
  | setProofSystems (id : ChainId) (m : ℕ)

/-- One successful transaction at v35. -/
inductive TimedStep35 (T : TimedConfig) (P : ProofWorld) : TimedSys35 → TimedLabel35 →
    TimedSys35 → Prop
  /-- An `UpgradeTiming` step with its proof-system effect. -/
  | timed {s : TimedSys35} {l : TimedLabel} {t' : TimedSys} {pr' : ChainId → ProofState} :
      TimedStep T s.timed l t' → TimedProofEffect T P s.timed s.proof l pr' →
      TimedStep35 T P s (.timed l) ⟨t', pr'⟩
  /-- `permanentlyRequireSecondProofSystem` (`Admin.sol:454-465`), by the chain's admin, on its
  settlement layer. -/
  | requireSecondProofSystem {s : TimedSys35} {id : ChainId} {caller : Address} {c : Chain} :
      s.timed.sys.chains id = some c →
      caller = (s.timed.aux id).admin →
      (s.timed.aux id).slVersion = none →
      (s.proof id).required = false →
      P.multi (s.proof id).verifier (s.proof id).disabled = true →
      TimedStep35 T P s (.requireSecondProofSystem id caller)
        ⟨s.timed, upd s.proof id { s.proof id with required := true }⟩
  /-- `setProofSystemStatus` (`Admin.sol:416-432`), as an arbitrary write of the mask. -/
  | setProofSystems {s : TimedSys35} {id : ChainId} {c : Chain} {m : ℕ} :
      s.timed.sys.chains id = some c →
      TimedStep35 T P s (.setProofSystems id m)
        ⟨s.timed, upd s.proof id { s.proof id with disabled := m }⟩

/-- A sequence of successful transactions at v35. -/
inductive TimedRun35 (T : TimedConfig) (P : ProofWorld) : TimedSys35 → List TimedLabel35 →
    TimedSys35 → Prop
  | nil {s : TimedSys35} : TimedRun35 T P s [] s
  | cons {s s' s'' : TimedSys35} {l : TimedLabel35} {ls : List TimedLabel35} :
      TimedStep35 T P s l s' → TimedRun35 T P s' ls s'' → TimedRun35 T P s (l :: ls) s''

/-- The `UpgradeTiming` transactions a v35 label is: itself for a timed one, none for the two
proof-system writers. -/
def TimedLabel35.timedSteps : TimedLabel35 → List TimedLabel
  | .timed l => [l]
  | .requireSecondProofSystem _ _ => []
  | .setProofSystems _ _ => []

/-- The break-glass steps. -/
def TimedLabel35.isArbitrary : TimedLabel35 → Prop
  | .timed l => l.isArbitrary
  | _ => False

/-- The routing view of a timed v35 state. -/
def TimedSys35.routing (s : TimedSys35) : Sys35 := ⟨s.timed.sys, s.proof⟩

/-- **The condition a v35 timed step adds to the `UpgradeTiming` step it extends**: that of its
routing step (`ProofGateAtV35.GateHolds`). An upgrade by any path is gated as a transition; the
notifier and `DiamondAux` writes add nothing. -/
def TimedGateHolds (T : TimedConfig) (P : ProofWorld) (s : TimedSys35) : TimedLabel → Prop
  | .upgrade id _ _ _ => GateHolds T.X.W P s.routing (.transition id)
  | .base l => GateHolds T.X.W P s.routing l
  | _ => True

/-! ## Witness data

`UpgradeTiming`'s witness configuration `wTiming`. Chain `0`'s admin is `3`. The setup is
`UpgradeTiming`'s `wTimingSetup` with chain `0`'s admin requiring its second proof system right
after configuring the chain. -/

/-- `wTimingSys0` with the requirement off everywhere. -/
def wTimingSys35 : TimedSys35 := ⟨wTimingSys0, fun _ => ⟨false, 0, 0⟩⟩

/-- Chain `0` is created and configured, its admin `3` requires its second proof system, the
CTM commits `300`, and the admin sets the chain's own upgrade time for version 1 to `12`. -/
def wTimingGateSetup : List TimedLabel35 :=
  [.timed (.base (.genesis 0)), .timed (.setAux 0 wTimingAux), .requireSecondProofSystem 0 3,
    .timed (.base (.ctm (.commit 300))), .timed (.setUpgradeTimestamp 0 3 12)]

end Contracts.ChainTypeManager.UpgradeTimingAtV35
