import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: the second-proof-system flag and the ZiSK switch of one diamond (draft/v0.35.0)

Source: era-contracts branch `draft/v0.35.0` at commit
**`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`** (`b17415d20`). Every `file:line` below is at
that commit. Paths are relative to `l1-contracts/contracts/`; `protocol-docs/` is at the
repository root.

The model was first written against `d9f678900e1bc8286412b78f56d4a9f443983c29`. None of the
Solidity files cited here differs between the two commits. `protocol-docs/interop-gating.md`
gained six lines (`:43-48`, "Releases keep the second proof system too"), which moved its
citations after `:42`; they are given here at `b17415d20`.

**This file is definitions only.** The statements are in
`EraSpec.Contracts.SecondProofSystem.Properties.FlagAuthorityV35` and are proved in
`EraSpec.Contracts.SecondProofSystem.Proofs.FlagAuthorityV35`.

## What is modelled

One ZK chain diamond, projected onto the storage the requirement reads and writes
(`state-transition/chain-deps/ZKChainStorage.sol`):

* `verifier` (`:89`), `admin` (`:166`), `pendingAdmin` (`:169`), `chainTypeManager` (`:187`),
  `settlementLayer` (`:218`);
* `disabledProofSystems` (`:290`), a `uint8` bit mask, bit `1 << uint8(p)` for proof system `p`;
* `secondProofSystemRequired` (`:301-304`), the flag.

`IOwnable(s.bridgehub).owner()` is read live by `setProofSystemStatus` (`Admin.sol:417`). The
model keeps that answer as the field `bridgehubOwner`. It is Bridgehub storage, not diamond
storage (`core/bridgehub/BridgehubBase.sol:52`, `Ownable2StepUpgradeable`); the model lets it
change to any address at any time (`Call.bridgehubOwnerChanged`), which only adds runs.
`s.bridgehub` itself is written only at creation (`state-transition/chain-deps/DiamondInit.sol:90`).
The read is assumed to return: a reverting `owner()` would make the disable call on a flagged
diamond revert for everyone, which the model does not have. That matters for the statements
that say a call succeeds (`OwnerDisablesOnFlagged`, the success half of
`ZiskOffAuthorityExact`), not for the safety statements.

The writers of the flag and of the mask in the whole `l1-contracts/contracts` tree at
`b17415d20` (`grep secondProofSystemRequired`, `grep disabledProofSystems`) are exactly:

* `Admin.setProofSystemStatus` (`state-transition/chain-deps/facets/Admin.sol:416-432`), the
  only write of the mask (`:430`):

        address authorized = !_enabled && s.secondProofSystemRequired
            ? IOwnable(s.bridgehub).owner() : s.admin;                         // :417
        if (msg.sender != authorized) revert Unauthorized(msg.sender);        // :418-420
        if (_proofSystem != ProofSystem.Zisk) revert InvalidProofSystem(..);  // :421-423
        uint8 proofSystemMask = uint8(1 << uint8(_proofSystem));               // :425
        s.disabledProofSystems = _enabled ? old & ~proofSystemMask
                                          : old | proofSystemMask;           // :426-430

  It has no modifier (`:416`).

* `Admin.permanentlyRequireSecondProofSystem` (`Admin.sol:454-465`), `onlyAdmin`
  (`state-transition/chain-deps/facets/ZKChainBase.sol:46-51`) and `onlySettlementLayer`
  (`ZKChainBase.sol:141-146`, `s.settlementLayer == address(0)`), the only write of the flag
  (`:463`), and only to `true`:

        if (s.secondProofSystemRequired) revert SecondProofSystemAlreadyRequired(); // :455-457
        uint256 proofMode = _getProofMode();                                      // :458
        if (proofMode != ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE) revert ..;      // :459-461
        s.secondProofSystemRequired = true;                                       // :463

  where `_getProofMode()` is `s.verifier.getProofMode(s.disabledProofSystems)`
  (`ZKChainBase.sol:188-190`).

Any other write would come from code delegatecalled by a diamond cut's init
(`state-transition/libraries/Diamond.sol:109-137, 310-340`). The cut entry points are
`upgradeChainFromVersion` (`Admin.sol:559-590`; the cut is the one the chain's CTM composes for
the edge, `:566-568`), `executeUpgrade` (`Admin.sol:593-595`, `onlyChainTypeManager`, reached
from the CTM owner's `ChainTypeManager.executeUpgrade`,
`state-transition/ChainTypeManager.sol:626-628`, with an arbitrary cut) and `genesisUpgrade`
(`Admin.sol:599-609`, `onlyChainTypeManager`, init the CTM's `l1GenesisUpgrade()`). All three end
in `_executeDiamondCut` (`Admin.sol:117-128`), which after the cut re-checks a flagged diamond's
verifier:

        Diamond.diamondCut(_diamondCut);                                              // :118
        if (s.secondProofSystemRequired) {                                            // :121
            uint256 proofMode = IZKsyncOSVerifier(address(s.verifier)).getProofMode(0); // :122
            if (proofMode != ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE) revert ..;      // :123-125
        }

The flag it reads is the one the init left.

## Inits

An init is one of three things (`Init`):

* `none`: no init (`initAddress == address(0)`, `Diamond.sol:311-315`); the cut changes only
  `Diamond.DiamondStorage`.
* `genuine g`: the registry engines (`upgrades/DefaultUpgrade.sol:29-43`,
  `upgrades/BootstrapUpgrade.sol:29-44`) or `L1GenesisUpgrade`
  (`upgrades/L1GenesisUpgrade.sol:31-53`). Of the projected storage these write only the
  verifier, through `BaseZkSyncUpgrade._setVerifier` (`upgrades/BaseZkSyncUpgrade.sol:133-153`),
  and only when `_upgrade` is given a nonzero verifier (`:97-99`; `L1GenesisUpgrade.sol:42-47`
  passes `address(0)`, `DefaultUpgrade.sol:67-71` a nonzero one):

        if (_newVerifier == IVerifier(address(0))) revert ZeroAddress();          // :138-140
        if (s.secondProofSystemRequired) {                                        // :143
            uint256 proofMode = IZKsyncOSVerifier(address(_newVerifier)).getProofMode(0); // :144
            if (proofMode != ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE) revert ..;  // :145-147
        }
        s.verifier = _newVerifier;                                                // :151

  `g.newVerifier = none` is the `address(0)` case; `some v` is any address the engine reads,
  so the model does not assume which verifier a release ships. The rest of what these inits
  write (the protocol version, the L2 upgrade transaction hash, facet routing) is outside the
  projection. Their reject-only checks (batches executed, timestamps, settlement-layer order,
  release routing) are omitted, which only adds runs. Their own facet cuts carry no init
  (`BaseZkSyncUpgrade.sol:124-129`), and the external calls they make are to functions declared
  `view`.
* `arbitrary f`: any other delegatecalled code, as a function of the projected storage, chosen
  per call. This is the CTM owner's break-glass cut, and any cut whose init is not a genuine
  engine. The init address of an `upgradeChainFromVersion` cut is the engine the committed
  transition names (`upgrades/registry/libraries/CTMUpgradeComposer.sol:37-43`), so it is
  `genuine` exactly when that transition names a genuine engine. The statements say "no
  break-glass cut" for "no cut with an `arbitrary` init".

## The verifier

`Env.proofMode v m` is what `getProofMode(m)` at address `v` returns (`none`: it reverts). In
`Reach` an `Env` is fixed for a whole run. In `ReachEnvs` every call carries its own, so a
verifier whose answers change over time is covered there; the safety statements whose
conclusions do not mention the verifier are also proved along those runs (`…AnyVerifiers`). Two
genuine verifiers are transcribed, both `pure` in the source:

* `MultiProofVerifier.getProofMode` (`state-transition/verifiers/MultiProofVerifier.sol:101-109`)
  as `multiProofGetProofMode`. `ReportsZisk` is the property of it that matters: it reports
  multi-proof mode only for a mask with the ZiSK bit clear.
* `ZKsyncOSVerifier.getProofMode` (`state-transition/verifiers/ZKsyncOSVerifier.sol:104-106`),
  the Airbender-only verifier, as `airbenderGetProofMode`: PLONK mode for every mask.

## Not modelled

* **Facet replacement.** The entry points are the `AdminFacet`'s at `b17415d20`, and the other
  facets are those at `b17415d20` (which write none of the projected fields, below). A cut that
  replaces facets with other code (the genuine engines do, with the next release's) leaves this
  model: every statement is about runs in which the installed facets are these.
* **Dispatch.** The diamond proxy's routing and freeze check
  (`state-transition/chain-deps/DiamondProxy.sol:25-60`; `:36` makes a facet marked freezable
  unreachable while the diamond is frozen) are not modelled: a call reaches the facet. For the
  safety statements this only adds runs. The statements that say a call succeeds are about the
  facet code, for a call that reaches it.
* **Senders.** The model excludes no address as a sender, the zero address included.
* **Other storage and other facets.** `AdminFacet` has 27 selectors (`Admin.sol:646-702`): two
  views (`getRollupDAManager`, `ROLLUP_DA_MANAGER`), the seven entry points transcribed here,
  and eighteen that write none of the projected fields (`OtherAdminEntry`, each with its lines).
  Outside `AdminFacet` the only writers of a projected field at `b17415d20` are `Migrator`
  (`s.settlementLayer`, `state-transition/chain-deps/facets/Migrator.sol:207, 299, 332`,
  `Call.migratorSetsSettlementLayer`) and the creation-time `DiamondInit`
  (`state-transition/chain-deps/DiamondInit.sol:89-119`, which writes neither the flag nor the
  mask). `Call.otherFacet` stands for every other entry point of every other facet. That those
  write none of the projected fields is a source reading (`grep` for the assignments; no
  `sstore` in `state-transition` or `upgrades`), not a theorem.
* **Guards over storage outside the projection.** The eighteen other `AdminFacet` entry points,
  `Migrator`, and the callers of `upgradeChainFromVersion`
  (`onlyAdminOrChainTypeManagerOrValidator`, `Admin.sol:562`) and its version and timestamp
  checks (`:570-589`) are not checked. The model lets these calls succeed for any caller, which
  only adds runs.
* **Reentrancy.** A call is one atomic step. None of the transcribed entry points makes a
  state-changing external call: `owner()` and `getProofMode` are declared `view`
  (`common/interfaces/IOwnable.sol:8`,
  `state-transition/chain-interfaces/IZKsyncOSVerifier.sol:12`).
* **Other diamonds of the same chain.** The model is one diamond. Nothing here is about the
  flag or the mask of any other diamond of the same chain.
-/

namespace Contracts.SecondProofSystem.FlagAuthorityV35

open Clear

/-- Addresses as 256-bit words; `0` is the zero address. -/
abbrev Address := UInt256

/-- `enum ProofSystem { Boojum, Airbender, Zisk }` (`common/Config.sol:126-130`). -/
inductive ProofSystem
  | boojum
  | airbender
  | zisk
  deriving DecidableEq, Repr

/-- `uint8(_proofSystem)`. -/
def ProofSystem.toUInt8 : ProofSystem → UInt8
  | .boojum => 0
  | .airbender => 1
  | .zisk => 2

/-- `uint8(1 << uint8(_proofSystem))` (`Admin.sol:425`;
`state-transition/chain-deps/facets/Getters.sol:123-125`). -/
def ProofSystem.bit (p : ProofSystem) : UInt8 := (1 : UInt8) <<< p.toUInt8

/-- The ZiSK bit of the mask. -/
abbrev ziskBit : UInt8 := ProofSystem.zisk.bit

/-- `ZKSYNC_OS_PLONK_VERIFICATION_TYPE` (`common/Config.sol:105`). -/
def PLONK_TYPE : ℕ := 2

/-- `ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE` (`common/Config.sol:108`). -/
def MULTI_PROOF_TYPE : ℕ := 5

/-- The verifier code: `proofMode v m` is the result of `getProofMode(m)` on the verifier at `v`;
`none` is a revert. -/
structure Env where
  proofMode : Address → UInt8 → Option ℕ

/-- The projected `ZKChainStorage` of one diamond, plus the Bridgehub's owner. -/
structure St where
  admin : Address
  pendingAdmin : Address
  chainTypeManager : Address
  bridgehubOwner : Address
  settlementLayer : Address
  verifier : Address
  secondProofSystemRequired : Bool
  disabledProofSystems : UInt8
  deriving DecidableEq, Repr

/-- `Getters.disabledProofSystems().zisk` (`Getters.sol:119-126`): the ZiSK bit is set. -/
def ziskOff (s : St) : Prop := s.disabledProofSystems &&& ziskBit ≠ 0

/-- ZiSK is enabled: the ZiSK bit is clear. -/
def ziskOn (s : St) : Prop := s.disabledProofSystems &&& ziskBit = 0

instance (s : St) : Decidable (ziskOff s) := by unfold ziskOff; infer_instance
instance (s : St) : Decidable (ziskOn s) := by unfold ziskOn; infer_instance

/-- The diamond requires its second proof system and has ZiSK switched off. Governance reaches
it on purpose, with the emergency ZiSK-off (`interop-gating.md:37-38`); the statements of (c)
are about whether anyone else can. -/
def FlaggedZiskOff (s : St) : Prop := s.secondProofSystemRequired = true ∧ ziskOff s

/-! ## The verifier -/

/-- `MultiProofVerifier.getProofMode` (`MultiProofVerifier.sol:101-109`):

    if (_disabledProofSystems & ~uint8(1 << uint8(ProofSystem.Zisk)) != 0) revert ..;   // :102-104
    return _disabledProofSystems & uint8(1 << uint8(ProofSystem.Zisk)) == 0              // :105-108
        ? ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE : ZKSYNC_OS_PLONK_VERIFICATION_TYPE; -/
def multiProofGetProofMode (m : UInt8) : Option ℕ :=
  if m &&& ~~~ziskBit ≠ 0 then none
  else if m &&& ziskBit = 0 then some MULTI_PROOF_TYPE else some PLONK_TYPE

/-- `ZKsyncOSVerifier.getProofMode` (`ZKsyncOSVerifier.sol:104-106`), the Airbender-only
verifier: `return ZKSYNC_OS_PLONK_VERIFICATION_TYPE;` for every mask. -/
def airbenderGetProofMode (_m : UInt8) : Option ℕ := some PLONK_TYPE

/-- The verifier at `v` reports multi-proof mode only for a mask whose ZiSK bit is clear.
`multiProofGetProofMode` has it (`MultiProofVerifierReportsZisk`). -/
def ReportsZisk (E : Env) (v : Address) : Prop :=
  ∀ m, E.proofMode v m = some MULTI_PROOF_TYPE → m &&& ziskBit = 0

/-- An environment in which every address runs the genuine `MultiProofVerifier.getProofMode`. -/
def multiProofEnv : Env := ⟨fun _ m => multiProofGetProofMode m⟩

/-- The second-proof checks of `L1MessageRoot.enableInterop(_chainId, true)`
(`core/message-root/L1MessageRoot.sol:81-85`), read off this diamond:

    require(IGetters(zkChain).isSecondProofSystemRequired(), SecondProofSystemNotRequired(..)); // :82
    uint256 proofMode = IGetters(zkChain).getProofMode();                                      // :83
    require(proofMode == ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE, NotMultiProofMode(..));      // :84

`getProofMode()` is `_getProofMode()` (`Getters.sol:109-111`). This is the predicate the checks
evaluate; `enableInterop` itself runs once per chain (`L1MessageRoot.sol:76`). -/
def InteropSecondProofGate (E : Env) (s : St) : Prop :=
  s.secondProofSystemRequired = true ∧
    E.proofMode s.verifier s.disabledProofSystems = some MULTI_PROOF_TYPE

/-! ## Diamond cuts -/

/-- What a genuine engine init writes to the projection: possibly a new verifier. -/
structure GenuineInit where
  /-- `none` is `_verifier == address(0)` (`BaseZkSyncUpgrade.sol:97`), as in `L1GenesisUpgrade`. -/
  newVerifier : Option Address
  deriving DecidableEq, Repr

/-- The init of a diamond cut. -/
inductive Init
  | none
  | genuine (g : GenuineInit)
  | arbitrary (f : St → Option St)

/-- The init is not genuine code. -/
def Init.isArbitrary : Init → Bool
  | .arbitrary _ => true
  | _ => false

/-- `BaseZkSyncUpgrade._setVerifier` (`BaseZkSyncUpgrade.sol:133-153`), reached from `_upgrade`
only for a nonzero verifier (`:97-99`). -/
def genuineInit (E : Env) (g : GenuineInit) (s : St) : Option St :=
  match g.newVerifier with
  | none => some s
  | some v =>
    if v = 0 then none
    else if s.secondProofSystemRequired = true ∧ E.proofMode v 0 ≠ some MULTI_PROOF_TYPE then none
    else some { s with verifier := v }

/-- The init's effect on the projection. -/
def runInit (E : Env) : Init → St → Option St
  | .none, s => some s
  | .genuine g, s => genuineInit E g s
  | .arbitrary f, s => f s

/-- `AdminFacet._executeDiamondCut` (`Admin.sol:117-128`): the cut (facets, then init), then the
verifier re-check on the flag the init left (`:121-126`). -/
def executeDiamondCut (E : Env) (i : Init) (s : St) : Option St :=
  match runInit E i s with
  | none => none
  | some s' =>
    if s'.secondProofSystemRequired = true ∧ E.proofMode s'.verifier 0 ≠ some MULTI_PROOF_TYPE
    then none
    else some s'

/-! ## Entry points -/

/-- The eighteen `AdminFacet` entry points that write none of the projected fields
(`Admin.sol`). -/
inductive OtherAdminEntry
  /-- `:156-159`. -/
  | setValidator
  /-- `:162-170`. -/
  | setPriorityTxMaxGasLimit
  /-- `:173-187`. -/
  | setZKsyncOSMaxTxGasLimit
  /-- `:190-199`. -/
  | setZKsyncOSL1TxFiltering
  /-- `:202-208`. -/
  | setZKsyncOSLargeContractsEnabled
  /-- `:218-264`. -/
  | changeFeeParams
  /-- `:267-295`. -/
  | setTokenMultiplier
  /-- `:359-365`. -/
  | setPubdataPricingMode
  /-- `:368-373`. -/
  | setTransactionFilterer
  /-- `:387-401`. -/
  | setDAValidatorPair
  /-- `:404-413`. -/
  | setPubdataContent
  /-- `:435-451`. -/
  | makePermanentRollup
  /-- `:468-479`. -/
  | setPriorityModeTransactionFilterer
  /-- `:482-515`. -/
  | permanentlyAllowPriorityMode
  /-- `:518-521`. -/
  | deactivatePriorityMode
  /-- `:524-552`. -/
  | activatePriorityMode
  /-- `:616-626`. -/
  | freezeDiamond
  /-- `:629-639`. -/
  | unfreezeDiamond
  deriving DecidableEq, Repr

/-- The calls of the model: every state-changing `AdminFacet` entry point, and what else can
change the projection. -/
inductive Call
  /-- `Admin.setPendingAdmin` (`Admin.sol:131-137`). -/
  | setPendingAdmin (a : Address)
  /-- `Admin.acceptAdmin` (`Admin.sol:140-153`). -/
  | acceptAdmin
  /-- `Admin.setProofSystemStatus` (`Admin.sol:416-432`). -/
  | setProofSystemStatus (p : ProofSystem) (enabled : Bool)
  /-- `Admin.permanentlyRequireSecondProofSystem` (`Admin.sol:454-465`). -/
  | permanentlyRequireSecondProofSystem
  /-- `Admin.upgradeChainFromVersion` (`Admin.sol:559-590`); `i` is the init of the CTM's cut. -/
  | upgradeChainFromVersion (i : Init)
  /-- `Admin.executeUpgrade` (`Admin.sol:593-595`), from `ChainTypeManager.executeUpgrade`
  (`ChainTypeManager.sol:626-628`, `onlyOwner`). -/
  | executeUpgrade (i : Init)
  /-- `Admin.genesisUpgrade` (`Admin.sol:599-609`); `i` is the code at the CTM's
  `l1GenesisUpgrade()`, genuinely `L1GenesisUpgrade` (`.genuine ⟨none⟩`). -/
  | genesisUpgrade (i : Init)
  /-- One of the other eighteen `AdminFacet` entry points. -/
  | adminOther (e : OtherAdminEntry)
  /-- `Migrator` moving the settlement layer (`Migrator.sol:207, 299, 332`). Not `AdminFacet`. -/
  | migratorSetsSettlementLayer (sl : Address)
  /-- The Bridgehub's owner changes. Not the diamond. -/
  | bridgehubOwnerChanged (o : Address)
  /-- Every other entry point of every other facet. Not `AdminFacet`. -/
  | otherFacet

/-- The call runs non-genuine init code: the break-glass cut. -/
def Call.isBreakGlass : Call → Bool
  | .upgradeChainFromVersion i => i.isArbitrary
  | .executeUpgrade i => i.isArbitrary
  | .genesisUpgrade i => i.isArbitrary
  | _ => false

/-- The call is `setProofSystemStatus`. -/
def Call.isSetStatus : Call → Bool
  | .setProofSystemStatus _ _ => true
  | _ => false

/-- The caller rule of `setProofSystemStatus` (`Admin.sol:417`). -/
def callerRule (s : St) (enabled : Bool) : Address :=
  if (!enabled && s.secondProofSystemRequired) = true then s.bridgehubOwner else s.admin

/-- The countermodel's caller rule: `Admin.sol:417` replaced by `s.admin`. -/
def adminOnlyRule (s : St) (_enabled : Bool) : Address := s.admin

/-- The mask `setProofSystemStatus` writes (`Admin.sol:425-430`). -/
def newMask (old : UInt8) (p : ProofSystem) (enabled : Bool) : UInt8 :=
  if enabled = true then old &&& ~~~p.bit else old ||| p.bit

/-- `setProofSystemStatus` under a caller rule (`Admin.sol:416-432`). -/
def setProofSystemStatusWith (rule : St → Bool → Address) (c : Address) (p : ProofSystem)
    (enabled : Bool) (s : St) : Option St :=
  if c ≠ rule s enabled then none                            -- :417-420
  else if p ≠ .zisk then none                                -- :421-423
  else some { s with disabledProofSystems := newMask s.disabledProofSystems p enabled } -- :425-430

/-- `permanentlyRequireSecondProofSystem` (`Admin.sol:454-465`) with its modifiers. -/
def permanentlyRequire (E : Env) (c : Address) (s : St) : Option St :=
  if c ≠ s.admin then none                                   -- onlyAdmin, ZKChainBase.sol:46-51
  else if s.settlementLayer ≠ 0 then none                    -- onlySettlementLayer, :141-146
  else if s.secondProofSystemRequired = true then none       -- Admin.sol:455-457
  else if E.proofMode s.verifier s.disabledProofSystems ≠ some MULTI_PROOF_TYPE then none -- :458-461
  else some { s with secondProofSystemRequired := true }     -- :463

/-- One call by `c`, under a caller rule for `setProofSystemStatus`. `none` is a revert. -/
def stepWith (rule : St → Bool → Address) (E : Env) (c : Address) : Call → St → Option St
  | .setPendingAdmin a, s => if c ≠ s.admin then none else some { s with pendingAdmin := a }
  | .acceptAdmin, s =>
    if c ≠ s.pendingAdmin then none else some { s with admin := s.pendingAdmin, pendingAdmin := 0 }
  | .setProofSystemStatus p en, s => setProofSystemStatusWith rule c p en s
  | .permanentlyRequireSecondProofSystem, s => permanentlyRequire E c s
  | .upgradeChainFromVersion i, s => executeDiamondCut E i s
  | .executeUpgrade i, s => if c ≠ s.chainTypeManager then none else executeDiamondCut E i s
  | .genesisUpgrade i, s => if c ≠ s.chainTypeManager then none else executeDiamondCut E i s
  | .adminOther _, s => some s
  | .migratorSetsSettlementLayer sl, s => some { s with settlementLayer := sl }
  | .bridgehubOwnerChanged o, s => some { s with bridgehubOwner := o }
  | .otherFacet, s => some s

/-- The source: `stepWith callerRule`. -/
def step : Env → Address → Call → St → Option St := stepWith callerRule

/-- Runs: successful calls, each allowed by `ok` in the state it starts from. -/
inductive ReachWith (rule : St → Bool → Address) (E : Env) (ok : St → Address → Call → Prop) :
    St → St → Prop
  | refl (s : St) : ReachWith rule E ok s s
  | step {s s' s'' : St} (c : Address) (call : Call) :
      ok s c call → stepWith rule E c call s = some s' → ReachWith rule E ok s' s'' →
      ReachWith rule E ok s s''

/-- Runs of the source. -/
abbrev Reach (E : Env) (ok : St → Address → Call → Prop) : St → St → Prop :=
  ReachWith callerRule E ok

/-- Runs of the source in which every call may see its own verifier answers: each step carries
an `Env`, which `ok` may read. A run of `Reach E (ok E)` is one, with `E` at every step
(`ReachEnvsExtendsReach`). -/
inductive ReachEnvs (ok : Env → St → Address → Call → Prop) : St → St → Prop
  | refl (s : St) : ReachEnvs ok s s
  | step {s s' s'' : St} (E : Env) (c : Address) (call : Call) :
      ok E s c call → stepWith callerRule E c call s = some s' → ReachEnvs ok s' s'' →
      ReachEnvs ok s s''

/-! ## Run predicates -/

/-- Every call, by anyone. -/
def AnyCall (_s : St) (_c : Address) (_call : Call) : Prop := True

/-- No break-glass cut. -/
def NoBreakGlass (_s : St) (_c : Address) (call : Call) : Prop := call.isBreakGlass = false

/-- Everyone but governance: no break-glass cut, and no `setProofSystemStatus` by whoever owns
the Bridgehub at that moment. Every other call, by anyone, is allowed (the Bridgehub owner's
other calls and the CTM's genuine cuts included). It allows every call a chain admin who is not
the Bridgehub owner can make. -/
def AdminSide (s : St) (c : Address) (call : Call) : Prop :=
  call.isBreakGlass = false ∧ (call.isSetStatus = true → c ≠ s.bridgehubOwner)

/-- `AdminSide`, and the verifier in use when the flag is set reports ZiSK honestly. -/
def AdminSideHonest (E : Env) (s : St) (c : Address) (call : Call) : Prop :=
  AdminSide s c call ∧ (call = .permanentlyRequireSecondProofSystem → ReportsZisk E s.verifier)

/-- `AdminSide` without its first half: the break-glass cut is allowed, and the Bridgehub owner
still never calls `setProofSystemStatus`. For the countermodel `BreakGlassDropsSecondProof`. -/
def NotOwnerStatus (s : St) (c : Address) (call : Call) : Prop :=
  call.isSetStatus = true → c ≠ s.bridgehubOwner

/-- Everyone but the chain admin: no break-glass cut, and no `setProofSystemStatus` by the chain
admin of that moment. Every other call, by anyone, is allowed. It allows every call a Bridgehub
owner who is not the chain admin can make. -/
def OwnerSide (s : St) (c : Address) (call : Call) : Prop :=
  call.isBreakGlass = false ∧ (call.isSetStatus = true → c ≠ s.admin)

/-! ## Witness data -/

/-- A diamond on its settlement layer, with the verifier at address `10`, admin `1`,
Bridgehub owner `2`, CTM `3`, ZiSK on and the flag not yet set. Which code runs at `10` is the
`Env`'s choice. -/
def w0 : St :=
  { admin := 1, pendingAdmin := 0, chainTypeManager := 3, bridgehubOwner := 2,
    settlementLayer := 0, verifier := 10, secondProofSystemRequired := false,
    disabledProofSystems := 0 }

/-- `w0` after the admin's `permanentlyRequireSecondProofSystem`. -/
def w1 : St := { w0 with secondProofSystemRequired := true }

/-- `w1` after a genuine upgrade to the verifier at `11`. -/
def w2 : St := { w1 with verifier := 11 }

/-- `w1` after the Bridgehub owner's emergency ZiSK-off. -/
def w3 : St := { w1 with disabledProofSystems := ziskBit }

/-- `w0` with ZiSK off: the unflagged diamond's admin switched it off. -/
def w4 : St := { w0 with disabledProofSystems := ziskBit }

/-- `w2` after an admin handover to `4` and a Bridgehub ownership change to `5`. -/
def w5 : St := { w2 with admin := 4, bridgehubOwner := 5 }

/-- `w1` with the Boojum bit of the mask set (mask `1`), for the frame of the other bits. -/
def w6 : St := { w1 with disabledProofSystems := ProofSystem.boojum.bit }

/-- A verifier that reports multi-proof mode for every mask. -/
def lyingEnv : Env := ⟨fun _ _ => some MULTI_PROOF_TYPE⟩

/-- The verifier at `10` reports multi-proof mode for every mask; every other address runs the
genuine `MultiProofVerifier.getProofMode`. -/
def mixedEnv : Env :=
  ⟨fun v m => if v = 10 then some MULTI_PROOF_TYPE else multiProofGetProofMode m⟩

/-- The address `12` runs the Airbender-only `ZKsyncOSVerifier.getProofMode`; every other
address runs the genuine `MultiProofVerifier.getProofMode`. -/
def airbenderAt12Env : Env :=
  ⟨fun v m => if v = 12 then airbenderGetProofMode m else multiProofGetProofMode m⟩

/-- The break-glass init that clears the flag. -/
def clearFlagInit : Init := .arbitrary fun s => some { s with secondProofSystemRequired := false }

/-- The break-glass init that switches ZiSK off and keeps the flag. -/
def ziskOffInit : Init := .arbitrary fun s => some { s with disabledProofSystems := ziskBit }

/-- The break-glass init that clears the mask. -/
def clearMaskInit : Init := .arbitrary fun s => some { s with disabledProofSystems := 0 }

/-- The break-glass init that writes the verifier slot directly, without `_setVerifier`. -/
def writeVerifierInit (v : Address) : Init := .arbitrary fun s => some { s with verifier := v }

end Contracts.SecondProofSystem.FlagAuthorityV35
