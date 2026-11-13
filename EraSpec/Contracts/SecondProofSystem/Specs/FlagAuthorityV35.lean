import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: the second-proof-system flag and the ZiSK switch of one diamond (draft/v0.35.0)

Source: era-contracts `draft/v0.35.0` at commit `d9f678900e1bc8286412b78f56d4a9f443983c29`.
Paths are relative to `l1-contracts/contracts/`; `protocol-docs/` is at the repository root.

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
model keeps the Bridgehub owner as the field `bridgehubOwner`, changed only by the owner
(`core/bridgehub/BridgehubBase.sol:52` is `Ownable2StepUpgradeable`; the two-step accept is
collapsed into one step, `Call.transferBridgehubOwnership`).

The writers of the flag and of the mask in the whole `l1-contracts/contracts` tree at `d9f6789`
(`grep secondProofSystemRequired`, `grep disabledProofSystems`) are exactly:

* `Admin.setProofSystemStatus` (`state-transition/chain-deps/facets/Admin.sol:416-432`), the
  only write of the mask (`:430`):

        address authorized = !_enabled && s.secondProofSystemRequired
            ? IOwnable(s.bridgehub).owner() : s.admin;                         // :417
        if (msg.sender != authorized) revert Unauthorized(msg.sender);        // :418-420
        if (_proofSystem != ProofSystem.Zisk) revert InvalidProofSystem(..);  // :421-423
        uint8 proofSystemMask = uint8(1 << uint8(_proofSystem));               // :425
        s.disabledProofSystems = _enabled ? old & ~proofSystemMask
                                          : old | proofSystemMask;           // :426-430

* `Admin.permanentlyRequireSecondProofSystem` (`Admin.sol:454-465`), `onlyAdmin`
  (`ZKChainBase.sol:46-51`) and `onlySettlementLayer` (`ZKChainBase.sol:141-146`,
  `s.settlementLayer == address(0)`), the only write of the flag (`:463`), and only to `true`:

        if (s.secondProofSystemRequired) revert SecondProofSystemAlreadyRequired(); // :455-457
        uint256 proofMode = _getProofMode();                                      // :458
        if (proofMode != ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE) revert ..;      // :459-461
        s.secondProofSystemRequired = true;                                       // :463

  where `_getProofMode()` is `s.verifier.getProofMode(s.disabledProofSystems)`
  (`ZKChainBase.sol:187-190`).

Everything else that can write them is code delegatecalled by a diamond cut's init. The cut entry
points are `upgradeChainFromVersion` (`Admin.sol:559-591`, the cut the CTM composed for the
edge), `executeUpgrade` (`Admin.sol:593-595`, `onlyChainTypeManager`, reached from the CTM
owner's `ChainTypeManager.executeUpgrade`, `state-transition/ChainTypeManager.sol:626-628`, with
an arbitrary cut) and `genesisUpgrade` (`Admin.sol:599-610`, init `L1GenesisUpgrade`). All
three end in `_executeDiamondCut` (`Admin.sol:117-129`), which after the cut re-checks a flagged
diamond's verifier:

        Diamond.diamondCut(_diamondCut);                                              // :118
        if (s.secondProofSystemRequired) {                                            // :121
            uint256 proofMode = IZKsyncOSVerifier(address(s.verifier)).getProofMode(0); // :122
            if (proofMode != ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE) revert ..;      // :123-125
        }

The flag it reads is the one the init left.

## Inits

An init is one of three things (`Init`):

* `none`: no init (`initAddress == address(0)`); the cut changes only `Diamond.DiamondStorage`.
* `genuine g`: the registry engine (`upgrades/DefaultUpgrade.sol:29-43`,
  `upgrades/BootstrapUpgrade.sol:29-44`) or `L1GenesisUpgrade` (`upgrades/L1GenesisUpgrade.sol`).
  Of the modelled storage these write only the verifier, through
  `BaseZkSyncUpgrade._setVerifier` (`upgrades/BaseZkSyncUpgrade.sol:133-153`), and only when
  `_upgrade` is given a nonzero verifier (`:97-99`; `L1GenesisUpgrade.sol:42-47` passes
  `address(0)`, `DefaultUpgrade.sol:67-71` a nonzero one):

        if (_newVerifier == IVerifier(address(0))) revert ZeroAddress();          // :139-141
        if (s.secondProofSystemRequired) {                                        // :143
            uint256 proofMode = IZKsyncOSVerifier(address(_newVerifier)).getProofMode(0); // :144
            if (proofMode != ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE) revert ..;  // :145-147
        }
        s.verifier = _newVerifier;                                                // :151

  `g.newVerifier = none` is the `address(0)` case. The rest of what these inits write (the
  protocol version, the L2 upgrade transaction hash, facet cuts) is outside the projection.
  Their reject-only checks (batches executed, timestamps, settlement-layer order) are omitted,
  which only adds runs.
* `arbitrary f`: any other delegatecalled code, as a function of the projected storage. This is
  the CTM owner's break-glass cut, and any cut whose init is not the genuine engine.

## The verifier

`Env.proofMode v m` is what `getProofMode(m)` at address `v` returns (`none`: it reverts). The
genuine `MultiProofVerifier.getProofMode` (`state-transition/verifiers/MultiProofVerifier.sol:101-109`)
is transcribed as `multiProofGetProofMode`. `ReportsZisk` is the property of it that matters:
it reports multi-proof mode only for a mask with the ZiSK bit clear.

## Not modelled

* Facet cuts are taken to leave the entry points modelled here as they are at `d9f6789`
  (the genuine release's facets). What other installed code does is covered only by `arbitrary`.
* The rest of the diamond's storage, events, and the other facets' entry points. None of them
  writes the projected fields except `Migrator` (`s.settlementLayer`,
  `state-transition/chain-deps/facets/Migrator.sol:207, 299, 332`, `Call.setSettlementLayer`)
  and the creation-time `DiamondInit` (`state-transition/chain-deps/DiamondInit.sol:90-119`,
  which writes neither the flag nor the mask). `Call.otherEntryPoint` stands for all of them.
* Callers of `upgradeChainFromVersion` (`onlyAdminOrChainTypeManagerOrValidator`) and of
  `setSettlementLayer` are not checked, which only adds runs.
* The model is one diamond. `ZKChainCommitment` (`common/Config.sol:234-262`), which carries a
  chain's state to the diamond on its next settlement layer, has no field for the flag or the
  mask, and `Migrator.forwardedBridgeMint` (`Migrator.sol:213-300`) writes neither. Nothing here
  speaks about another diamond of the same chain.
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

/-- `uint8(1 << uint8(_proofSystem))` (`Admin.sol:425`, `Getters.sol:121-125`). -/
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

/-! ## The verifier -/

/-- `MultiProofVerifier.getProofMode` (`MultiProofVerifier.sol:101-109`):

    if (_disabledProofSystems & ~uint8(1 << uint8(ProofSystem.Zisk)) != 0) revert ..;   // :102-104
    return _disabledProofSystems & uint8(1 << uint8(ProofSystem.Zisk)) == 0              // :105-108
        ? ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE : ZKSYNC_OS_PLONK_VERIFICATION_TYPE; -/
def multiProofGetProofMode (m : UInt8) : Option ℕ :=
  if m &&& ~~~ziskBit ≠ 0 then none
  else if m &&& ziskBit = 0 then some MULTI_PROOF_TYPE else some PLONK_TYPE

/-- The verifier at `v` reports multi-proof mode only for a mask whose ZiSK bit is clear.
`multiProofGetProofMode` has it (`MultiProofVerifierReportsZisk`). -/
def ReportsZisk (E : Env) (v : Address) : Prop :=
  ∀ m, E.proofMode v m = some MULTI_PROOF_TYPE → m &&& ziskBit = 0

/-- An environment in which every address runs the genuine `MultiProofVerifier.getProofMode`. -/
def multiProofEnv : Env := ⟨fun _ m => multiProofGetProofMode m⟩

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

/-- `AdminFacet._executeDiamondCut` (`Admin.sol:117-129`): the cut (facets, then init), then the
verifier re-check on the flag the init left (`:121-126`). -/
def executeDiamondCut (E : Env) (i : Init) (s : St) : Option St :=
  match runInit E i s with
  | none => none
  | some s' =>
    if s'.secondProofSystemRequired = true ∧ E.proofMode s'.verifier 0 ≠ some MULTI_PROOF_TYPE
    then none
    else some s'

/-! ## Entry points -/

/-- The calls that can touch the projection. -/
inductive Call
  /-- `Admin.setPendingAdmin` (`Admin.sol:131-137`). -/
  | setPendingAdmin (a : Address)
  /-- `Admin.acceptAdmin` (`Admin.sol:140-152`). -/
  | acceptAdmin
  /-- `Admin.setProofSystemStatus` (`Admin.sol:416-432`). -/
  | setProofSystemStatus (p : ProofSystem) (enabled : Bool)
  /-- `Admin.permanentlyRequireSecondProofSystem` (`Admin.sol:454-465`). -/
  | permanentlyRequireSecondProofSystem
  /-- `Admin.upgradeChainFromVersion` (`Admin.sol:559-591`) with the CTM's cut for the edge. -/
  | upgradeChainFromVersion (i : Init)
  /-- `Admin.executeUpgrade` (`Admin.sol:593-595`), from `ChainTypeManager.executeUpgrade`
  (`ChainTypeManager.sol:626-628`, `onlyOwner`). -/
  | executeUpgrade (i : Init)
  /-- `Admin.genesisUpgrade` (`Admin.sol:599-610`), init `L1GenesisUpgrade`. -/
  | genesisUpgrade
  /-- `Migrator` moving the settlement layer (`Migrator.sol:207, 299, 332`). -/
  | setSettlementLayer (sl : Address)
  /-- The Bridgehub's ownership transfer. -/
  | transferBridgehubOwnership (o : Address)
  /-- Every other entry point of every facet: none writes the projection. -/
  | otherEntryPoint

/-- The call runs non-genuine init code: the break-glass cut. -/
def Call.isBreakGlass : Call → Bool
  | .upgradeChainFromVersion i => i.isArbitrary
  | .executeUpgrade i => i.isArbitrary
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
  if c ≠ rule s enabled then none
  else if p ≠ .zisk then none
  else some { s with disabledProofSystems := newMask s.disabledProofSystems p enabled }

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
  | .genesisUpgrade, s =>
    if c ≠ s.chainTypeManager then none else executeDiamondCut E (.genuine ⟨none⟩) s
  | .setSettlementLayer sl, s => some { s with settlementLayer := sl }
  | .transferBridgehubOwnership o, s =>
    if c ≠ s.bridgehubOwner then none else some { s with bridgehubOwner := o }
  | .otherEntryPoint, s => some s

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

/-! ## Run predicates -/

/-- No break-glass cut. -/
def NoBreakGlass (_s : St) (_c : Address) (call : Call) : Prop := call.isBreakGlass = false

/-- The chain admin's side of the system: no break-glass cut, and no `setProofSystemStatus` by
whoever owns the Bridgehub at that moment. Every other call, by anyone, is allowed. -/
def AdminSide (s : St) (c : Address) (call : Call) : Prop :=
  call.isBreakGlass = false ∧ (call.isSetStatus = true → c ≠ s.bridgehubOwner)

/-- `AdminSide`, and the verifier in use when the flag is set reports ZiSK honestly. -/
def AdminSideHonest (E : Env) (s : St) (c : Address) (call : Call) : Prop :=
  AdminSide s c call ∧ (call = .permanentlyRequireSecondProofSystem → ReportsZisk E s.verifier)

/-- Every call made by the chain admin of that moment, who is not the Bridgehub owner, and no
break-glass cut. -/
def ByAdmin (s : St) (c : Address) (call : Call) : Prop :=
  call.isBreakGlass = false ∧ c = s.admin ∧ s.admin ≠ s.bridgehubOwner

/-- Allowed in the countermodel `BreakGlassThenAdminDrops`: the break-glass cut is allowed, the
Bridgehub owner still never calls `setProofSystemStatus`. -/
def NotOwnerStatus (s : St) (c : Address) (call : Call) : Prop :=
  call.isSetStatus = true → c ≠ s.bridgehubOwner

/-- The Bridgehub's side: no break-glass cut, and no `setProofSystemStatus` by the chain admin
of that moment. -/
def OwnerSide (s : St) (c : Address) (call : Call) : Prop :=
  call.isBreakGlass = false ∧ (call.isSetStatus = true → c ≠ s.admin)

/-! ## Witness data -/

/-- A diamond on its settlement layer, with the genuine verifier at `10`, admin `1`,
Bridgehub owner `2`, CTM `3`, ZiSK on and the flag not yet set. -/
def w0 : St :=
  { admin := 1, pendingAdmin := 0, chainTypeManager := 3, bridgehubOwner := 2,
    settlementLayer := 0, verifier := 10, secondProofSystemRequired := false,
    disabledProofSystems := 0 }

/-- `w0` after the admin's `permanentlyRequireSecondProofSystem`. -/
def w1 : St := { w0 with secondProofSystemRequired := true }

/-- `w1` after a genuine upgrade to the verifier at `11`. -/
def w2 : St := { w1 with verifier := 11 }

/-- A verifier that reports multi-proof mode for every mask. -/
def lyingEnv : Env := ⟨fun _ _ => some MULTI_PROOF_TYPE⟩

/-- The break-glass init that clears the flag. -/
def clearFlagInit : Init := .arbitrary fun s => some { s with secondProofSystemRequired := false }

end Contracts.SecondProofSystem.FlagAuthorityV35
