import EraSpec.Contracts.ChainTypeManager.Specs.ChainLocal
import EraSpec.Contracts.ChainTypeManager.Specs.Enabledness

/-!
# Model: the routing system at `draft/v0.35.0`, with the second-proof-system gate

Source: era-contracts branch `draft/v0.35.0` at commit **`d9f678900`** (`d9f6789`). That
branch carries the `e561b9cc2` tree of `feat/upgrade-simplification` (squash-merged as
`ccf00623c`, #2525) and later commits. Every `file:line` below is at `d9f6789` unless it
names `e561b9cc2`. Paths are relative to `l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.ProofGateAtV35` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.ProofGateAtV35`. Namespace:
`Contracts.ChainTypeManager.ProofGateAtV35`.

## What changed on the routing paths between `e561b9cc2` and `d9f6789`

A function-by-function diff, comments stripped, of every file that `ChainRouting`,
`ChainMigration`, `ChainLocal` and `Enabledness` cite finds two changed bodies on the chain
side. Both come from commit `2d08bdaba` (#2628, "interop gating").

1. `Admin._executeDiamondCut` (`state-transition/chain-deps/facets/Admin.sol:117-128`; it was
   `:112-115` at `e561b9cc2`) now checks the state the cut leaves:

        Diamond.diamondCut(_diamondCut);                                                // :118
        if (s.secondProofSystemRequired) {                                              // :121
            uint256 proofMode = IZKsyncOSVerifier(address(s.verifier)).getProofMode(0);  // :122
            if (proofMode != ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE) {                  // :123
                revert NotMultiProofMode(proofMode);                                     // :124
            }
        }

   Every diamond cut of a running chain goes through it:
   * the transition, `upgradeChainFromVersion` (`:586`);
   * the break-glass `executeUpgrade` (`:594`);
   * `genesisUpgrade` (`:608`).
2. `BaseZkSyncUpgrade._setVerifier` (`upgrades/BaseZkSyncUpgrade.sol:133-153`; `:127-142` at
   `e561b9cc2`) refuses, on a chain that requires its second proof system, a new verifier
   that does not report multi-proof mode (`:143-148`). The registry engines install the
   arriving release's verifier through it:
   * `DefaultUpgrade._upgradeFromCommittedObject` reads `ICTMRelease(newRelease).verifier()`
     (`upgrades/DefaultUpgrade.sol:67`) and passes it to `_upgrade` (`:72-83`);
   * `_upgrade` calls `_setVerifier` when that verifier is nonzero
     (`BaseZkSyncUpgrade.sol:97-99`);
   * `BootstrapUpgrade.upgradeFromBootstrap` ends with the same call
     (`upgrades/BootstrapUpgrade.sol:42`, unchanged since `e561b9cc2`).

   So on a transition and on the bootstrap crossing both checks read one address: the
   arriving release's verifier.

No other body these models cite changed its logic. That covers the routing guard, the derived
cuts, `Diamond.sol`, `DiamondInit`, `BootstrapUpgrade`, `Migrator` and every
`ChainTypeManager` function the models use. What else differs in the cited files:

* a rename: the manifest field and getter `upgradeEngine` are `chainUpgradeEngine` at
  `d9f6789` (`upgrades/registry/RegistryTypes.sol:144`, `:271`,
  `upgrades/registry/objects/CTMTransition.sol:189-191`,
  `upgrades/registry/libraries/CTMUpgradeComposer.sol:40`, `:52`). The cut still delegatecalls
  the engine the manifest names;
* line numbers: `-5` in `ChainTypeManager.sol` after its constructor (#2626 removed
  `INTEROP_CENTER`), `+31` for the upgrade entry points of `Admin.sol`;
* in `Admin.sol`, off the routing paths: `setProofSystemStatus` was `onlyAdmin` and now has
  the caller rule of `:417-420`, and `permanentlyRequireSecondProofSystem` is new (both below).

So a `ChainRouting` step is still what the source does to the version and the routing. What is
new is the state the two checks read, and its writers.

## The new state

* `bool secondProofSystemRequired` (`state-transition/chain-deps/ZKChainStorage.sol:301-304`,
  storage slot 70). In the source its only writer is
  `Admin.permanentlyRequireSecondProofSystem` (`Admin.sol:454-465`):

      function permanentlyRequireSecondProofSystem() external onlyAdmin onlySettlementLayer {
          if (s.secondProofSystemRequired) { revert SecondProofSystemAlreadyRequired(); } // :455-457
          uint256 proofMode = _getProofMode();                                            // :458
          if (proofMode != ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE) { revert NotMultiProofMode(...); } // :459-461
          s.secondProofSystemRequired = true;                                             // :463

  `_getProofMode()` is `IZKsyncOSVerifier(address(s.verifier)).getProofMode(s.disabledProofSystems)`
  (`state-transition/chain-deps/facets/ZKChainBase.sol:188-190`). Its NatSpec says "once
  activated, there is no way back!" (`state-transition/chain-interfaces/IAdmin.sol:137-140`).
  Code a break-glass init delegatecalls runs in the diamond's storage and can write the field
  too.
* `s.verifier`. `DiamondInit` writes the current release's verifier
  (`state-transition/chain-deps/DiamondInit.sol:114-118`), and `_setVerifier` writes later ones
  (`BaseZkSyncUpgrade.sol:150-151`).
* `s.disabledProofSystems`. `setProofSystemStatus` toggles its ZiSK bit (`Admin.sol:416-432`);
  disabling on a chain that requires its second proof system is reserved for the Bridgehub
  owner (`:417-420`).

## Modelling choices

* **`ChainRouting` is kept whole.** A v35 step is either a `ChainRouting.Step` together with
  what that step does to the chain's proof-system fields and the gate it must pass
  (`ProofEffect`), or one of the two new writers (`Step35`). Nothing of `ChainRouting`'s
  boundaries changes. The routing guard keeps its documented meaning, the engine is
  `DefaultUpgrade`/`BootstrapUpgrade`, and other reject-only checks stay omitted.
* **The engine boundary covers the proof-system fields too.** `ProofEffect.transition` and
  `.bootstrapReset` are what `DefaultUpgrade` and `BootstrapUpgrade` do: install the arriving
  release's verifier and leave the requirement and the mask alone. The manifest names the
  engine (`chainUpgradeEngine`), and another engine runs in the diamond's storage like a
  break-glass init. Of such a cut the source guarantees only the final check, which is what
  `ProofEffect.arbitraryCut` records. So the results that separate transitions from
  break-glass cuts (`RequirementWriters`, `RequirementIsPermanentWithoutBreakGlass`) are
  about the two in-tree engines.
* **Verifiers are their getters.** `getProofMode(m)` is a fixed function of the verifier and
  the mask (`ProofWorld.multi`): whether it returns `ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE`
  (`= 5`, `common/Config.sol:108`) without reverting. The in-tree implementations are `pure`
  or delegate to an immutable inner verifier:
  * `state-transition/verifiers/MultiProofVerifier.sol:101-109` gives multi-proof mode for
    mask `0` and PLONK mode once the ZiSK bit is set, and reverts on any other bit;
  * `ZKsyncOSVerifier.sol:104-106` always gives the PLONK type `2`;
  * `MultiProofTestnetVerifier.sol:52-54` delegates.

  A release's `verifier()` is a fixed function of the release (`ProofWorld.relVerifier`),
  since releases are write-once.
* **One gate per cut.** `_executeDiamondCut` checks the verifier the cut leaves. On a
  transition and on the bootstrap crossing that is the arriving release's verifier, which
  `_setVerifier` has just checked the same way. So the step is gated once, on it.
* **Break-glass.** The CTM owner's cut runs an arbitrary init in the diamond's storage, so it
  may leave any proof-system state that passes the final check (`ProofEffect.arbitraryCut`).
* **New diamonds.** Genesis and migration in deploy a fresh proxy (`ChainTypeManager.sol:674-692`,
  `:703-711`, `:746-758`): requirement off, the current release's verifier, nothing disabled
  (`ProofState.fresh`). `genesisUpgrade`'s cut then passes the check vacuously.
  `L1GenesisUpgrade` and `DiamondInit` write none of the three fields except the verifier, and
  `Migrator.forwardedBridgeMint` writes none of them.
* **Omitted**, as reject-only or as callers: `onlyAdmin` and `onlySettlementLayer` of
  `permanentlyRequireSecondProofSystem`, and the caller rule of `setProofSystemStatus` (see
  `UpgradeTimingAtV35` for the timed model with callers). Also the zero check on the
  release's verifier (`DefaultUpgrade.sol:69-71`), present at `e561b9cc2` too and omitted there
  too. `setProofSystemStatus` is modelled as an arbitrary write of the mask
  (`Step35.setProofSystems`), which only adds runs. The mask is read only by
  `permanentlyRequireSecondProofSystem`.
* **Migration out** is no step, as in `ChainRouting`. A returning chain keeps its diamond, and
  with it its proof-system fields.
* **One CTM's diamonds.** The three fields belong to a diamond. The migration commitment does
  not carry them (`Migrator.sol:221-241` reads the batch counters and `isPermanentRollup` from
  it), so the diamond that migration deploys for a chain on another settlement layer starts
  with its own fields, as `ProofEffect.migrateIn` says. Every result here is about the
  diamonds registered on the one modelled CTM, not about a chain across settlement layers.
-/

namespace Contracts.ChainTypeManager.ProofGateAtV35

open Contracts.ChainTypeManager

/-! ## The proof-system state -/

/-- The getters the v35 checks read, as fixed functions. -/
structure ProofWorld where
  /-- `ICTMRelease(R).verifier()`. -/
  relVerifier : Address → Address
  /-- `IZKsyncOSVerifier(v).getProofMode(m) == ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE`
  (`common/Config.sol:108`); `false` where the call reverts. -/
  multi : Address → ℕ → Bool

/-- The proof-system fields of a chain's `ZKChainStorage`. -/
structure ProofState where
  /-- `s.secondProofSystemRequired` (`ZKChainStorage.sol:304`). -/
  required : Bool
  /-- `s.verifier`. -/
  verifier : Address
  /-- `s.disabledProofSystems`. -/
  disabled : ℕ
deriving DecidableEq

/-- A freshly deployed diamond on release `R`: requirement off, `R`'s verifier
(`DiamondInit.sol:114-118`), nothing disabled. -/
def ProofState.fresh (P : ProofWorld) (R : Address) : ProofState :=
  ⟨false, P.relVerifier R, 0⟩

/-- `_setVerifier(v)` (`BaseZkSyncUpgrade.sol:150-151`): the verifier field becomes `v`. -/
def ProofState.install (p : ProofState) (v : Address) : ProofState :=
  { p with verifier := v }

/-- **The check `_executeDiamondCut` makes on the state a cut leaves** (`Admin.sol:121-126`): if
the chain requires its second proof system, its verifier reports multi-proof mode with nothing
disabled. `_setVerifier`'s check (`BaseZkSyncUpgrade.sol:143-148`) is the same condition on the
verifier it installs. -/
def ProofGate (P : ProofWorld) (p : ProofState) : Prop :=
  p.required = true → P.multi p.verifier 0 = true

/-- The verifier a transition installs on chain `c`: that of the release the edge committed at
`c`'s version arrives at (`DefaultUpgrade.sol:66-67`). -/
def arrivingVerifier (W : World) (P : ProofWorld) (s : Sys) (c : Chain) : Address :=
  P.relVerifier (s.edge W c.pv).newRel

/-! ## The v35 system -/

/-- The CTM and its chains, with each chain's proof-system fields. The fields of an id without
a diamond are meaningless. -/
structure Sys35 where
  /-- The `ChainRouting` system. -/
  sys : Sys
  /-- Each chain's proof-system fields. -/
  proof : ChainId → ProofState

/-- **What a `ChainRouting` step does to the proof-system fields at v35, and the check it must
pass.** `ProofEffect W P s pr l pr'` says the step `l`, taken from routing system `s` with
proof-system fields `pr`, leaves `pr'`. -/
inductive ProofEffect (W : World) (P : ProofWorld) (s : Sys) (pr : ChainId → ProofState) :
    Label → (ChainId → ProofState) → Prop
  /-- A CTM writer touches no diamond. -/
  | ctm {op : Op} : ProofEffect W P s pr (.ctm op) pr
  /-- `createNewChain`: a fresh diamond on the current release. `genesisUpgrade`'s check passes,
  since the requirement is off. -/
  | genesis {id : ChainId} :
      ProofEffect W P s pr (.genesis id) (upd pr id (ProofState.fresh P s.ctm.cur))
  /-- `forwardedBridgeMint`: a fresh diamond, as at genesis. -/
  | migrateIn {id : ChainId} :
      ProofEffect W P s pr (.migrateIn id) (upd pr id (ProofState.fresh P s.ctm.cur))
  /-- `upgradeChainFromVersion`: the arriving release's verifier is installed, and the chain's
  requirement, if set, needs it to report multi-proof mode. -/
  | transition {id : ChainId} {c : Chain} :
      s.chains id = some c →
      ProofGate P ((pr id).install (arrivingVerifier W P s c)) →
      ProofEffect W P s pr (.transition id) (upd pr id ((pr id).install (arrivingVerifier W P s c)))
  /-- The bootstrap crossing installs the genesis release's verifier under the same check. -/
  | bootstrapReset {id : ChainId} {c : Chain} {R : Address} :
      s.chains id = some c → s.ctm.legacy c.pv = LegacyCut.bootstrap R →
      ProofGate P ((pr id).install (P.relVerifier R)) →
      ProofEffect W P s pr (.bootstrapReset id) (upd pr id ((pr id).install (P.relVerifier R)))
  /-- Break-glass: the init may leave any proof-system fields that pass the final check. -/
  | arbitraryCut {id : ChainId} {v : ℕ} {ρ : Routing} {p : ProofState} :
      ProofGate P p → ProofEffect W P s pr (.arbitraryCut id v ρ) (upd pr id p)

/-- What happens at v35. -/
inductive Label35
  /-- A `ChainRouting` step. -/
  | routing (l : Label)
  /-- `Admin.permanentlyRequireSecondProofSystem()` on chain `id`. -/
  | requireSecondProofSystem (id : ChainId)
  /-- `Admin.setProofSystemStatus` on chain `id`, leaving the mask `m`. -/
  | setProofSystems (id : ChainId) (m : ℕ)

/-- One successful call at v35. -/
inductive Step35 (W : World) (P : ProofWorld) : Sys35 → Label35 → Sys35 → Prop
  /-- A `ChainRouting` step, with its proof-system effect. -/
  | routing {s : Sys35} {l : Label} {sys' : Sys} {pr' : ChainId → ProofState} :
      Step W s.sys l sys' → ProofEffect W P s.sys s.proof l pr' →
      Step35 W P s (.routing l) ⟨sys', pr'⟩
  /-- `permanentlyRequireSecondProofSystem` (`Admin.sol:454-465`): not yet required (`:455-457`),
  and the verifier in multi-proof mode under the chain's current mask (`:458-461`). -/
  | requireSecondProofSystem {s : Sys35} {id : ChainId} {c : Chain} :
      s.sys.chains id = some c → (s.proof id).required = false →
      P.multi (s.proof id).verifier (s.proof id).disabled = true →
      Step35 W P s (.requireSecondProofSystem id)
        ⟨s.sys, upd s.proof id { s.proof id with required := true }⟩
  /-- `setProofSystemStatus` (`Admin.sol:416-432`), as an arbitrary write of the mask. -/
  | setProofSystems {s : Sys35} {id : ChainId} {c : Chain} {m : ℕ} :
      s.sys.chains id = some c →
      Step35 W P s (.setProofSystems id m) ⟨s.sys, upd s.proof id { s.proof id with disabled := m }⟩

/-- A sequence of successful calls at v35. -/
inductive Run35 (W : World) (P : ProofWorld) : Sys35 → List Label35 → Sys35 → Prop
  | nil {s : Sys35} : Run35 W P s [] s
  | cons {s s' s'' : Sys35} {l : Label35} {ls : List Label35} :
      Step35 W P s l s' → Run35 W P s' ls s'' → Run35 W P s (l :: ls) s''

/-- The `ChainRouting` steps a v35 label is: itself for a routing step, none for the two
proof-system writers. -/
def Label35.routingSteps : Label35 → List Label
  | .routing l => [l]
  | .requireSecondProofSystem _ => []
  | .setProofSystems _ _ => []

/-- The break-glass steps. -/
def Label35.isArbitrary : Label35 → Prop
  | .routing l => l.isArbitrary
  | _ => False

/-- **The condition a v35 step adds to the `ChainRouting` step it extends**, on the state
before it. It is about the chain the step writes, and only when that chain requires its second
proof system: a transition needs the arriving release's verifier, and the bootstrap crossing the
genesis release's, to report multi-proof mode. Every other step adds nothing. A break-glass cut
can always leave a state that passes the check. -/
def GateHolds (W : World) (P : ProofWorld) (s : Sys35) : Label → Prop
  | .transition id => ∀ c, s.sys.chains id = some c →
      (s.proof id).required = true → P.multi (arrivingVerifier W P s.sys c) 0 = true
  | .bootstrapReset id => ∀ c R, s.sys.chains id = some c →
      s.sys.ctm.legacy c.pv = LegacyCut.bootstrap R →
      (s.proof id).required = true → P.multi (P.relVerifier R) 0 = true
  | _ => True

/-- Every registered chain that requires its second proof system has a verifier in
multi-proof mode with nothing disabled: what #2628 is for
(`protocol-docs/interop-gating.md:39-42`). -/
def ProofInv (P : ProofWorld) (s : Sys35) : Prop :=
  ∀ id c, s.sys.chains id = some c → ProofGate P (s.proof id)

/-- No chain requires its second proof system. Every pre-v35 diamond is in this state: slot 70
did not exist before #2628. -/
def NoChainRequires (s : Sys35) : Prop :=
  ∀ id, (s.proof id).required = false

/-- **A verifier that is in multi-proof mode with some proof systems disabled is also in it
with none disabled.** It relates the mask `permanentlyRequireSecondProofSystem` reads to the
mask `0` the cut check reads. Every in-tree verifier satisfies it (`MultiProofVerifier.sol:101-109`:
multi-proof only for mask `0`; `ZKsyncOSVerifier.sol:104-106`: never). -/
def DisablingNeverEnablesMultiProof (P : ProofWorld) : Prop :=
  ∀ v m, P.multi v m = true → P.multi v 0 = true

/-- **The ZiSK bit of `s.disabledProofSystems`**: `1 << uint8(ProofSystem.Zisk)` (`Admin.sol:425`),
with `ProofSystem { Boojum, Airbender, Zisk }` (`common/Config.sol:126-130`), so `4`. It is the
only bit `setProofSystemStatus` writes, so in the source a diamond's mask is `0` or `4`. -/
def ziskBit : ℕ := 4

/-! ## Witness data

On the `ChainRouting` witness world (`wWorld`: releases `100`, `200`, `250` at versions 1, 2, 3;
transition `300` from 1 to 2). Verifier `51` behaves like `MultiProofVerifier`: multi-proof mode
exactly with nothing disabled. Verifier `52` behaves like `ZKsyncOSVerifier`: never. The witness
runs write only the masks the source can reach, `0` and `ziskBit`. -/

/-- Release `200` ships the PLONK-only verifier `52`; the others ship `51`. -/
def wProofPlonk : ProofWorld where
  relVerifier := fun a => if a = 200 then 52 else 51
  multi := fun v m => decide (v = 51 ∧ m = 0)

/-- Every release ships a multi-proof verifier: `200` ships `53`, the others `51`. -/
def wProofMulti : ProofWorld where
  relVerifier := fun a => if a = 200 then 53 else 51
  multi := fun v m => decide ((v = 51 ∨ v = 53) ∧ m = 0)

/-- Verifier `54` reports multi-proof mode exactly when the mask is `ziskBit` (ZiSK disabled),
which no in-tree verifier does. Every release ships it. -/
def wProofOdd : ProofWorld where
  relVerifier := fun _ => 54
  multi := fun v m => decide (v = 54 ∧ m = ziskBit)

/-- The fresh witness system at v35: `wSys0`, no chain, no requirement anywhere. -/
def wSys35 : Sys35 := ⟨wSys0, fun _ => ⟨false, 0, 0⟩⟩

/-- Chains `0` and `1` are created at version 1 on release `100`, chain `0`'s admin requires its
second proof system, and the CTM commits `300` (1→2). -/
def wGateSetup : List Label35 :=
  [.routing (.genesis 0), .routing (.genesis 1), .requireSecondProofSystem 0,
    .routing (.ctm (.commit 300))]

/-- `wGateSetup`, then chains `0` and `1` cross `300`. -/
def wGateRun : List Label35 :=
  wGateSetup ++ [.routing (.transition 0), .routing (.transition 1)]

/-- Chain `0` is created, requires its second proof system, and then has ZiSK switched off: its
mask becomes `ziskBit`. -/
def wZiskOffRun : List Label35 :=
  [.routing (.genesis 0), .requireSecondProofSystem 0, .setProofSystems 0 ziskBit]

/-- Chain `0` is created, has ZiSK switched off, and then requires its second proof system. -/
def wZiskOffFirstRun : List Label35 :=
  [.routing (.genesis 0), .setProofSystems 0 ziskBit, .requireSecondProofSystem 0]

end Contracts.ChainTypeManager.ProofGateAtV35
