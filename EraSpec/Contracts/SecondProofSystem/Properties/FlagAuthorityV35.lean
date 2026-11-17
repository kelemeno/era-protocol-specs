import EraSpec.Contracts.SecondProofSystem.Specs.FlagAuthorityV35

/-!
# Properties: the second-proof-system flag is one-way, and ZiSK-off is the Bridgehub owner's

Statements over `EraSpec.Contracts.SecondProofSystem.Specs.FlagAuthorityV35` (era-contracts
`draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`). Proofs are in
`EraSpec.Contracts.SecondProofSystem.Proofs.FlagAuthorityV35`.

Every statement is about **one diamond** whose `AdminFacet` is the one at `d9f6789`, projected
onto eight fields. "No break-glass cut" means no diamond cut whose init is code other than the
genuine engines. The frame for the other facets is a source reading, not a theorem (see the
Specs header, "Not modelled").

## (a) The flag is one-way (`IAdmin.sol:137-140`, "once activated, there is no way back")

* `PermanentlyRequireExact`: when the call succeeds, and what it writes.
* `PermanentlyRequireOnce`: on a flagged diamond it reverts for every caller.
* `FlagMonotoneStep`, `FlagMonotone`: no call other than a break-glass cut clears the flag.
* `FlagSetOnlyByAdmin`: outside break-glass, only the admin's
  `permanentlyRequireSecondProofSystem` sets it.
* `BreakGlassCutIsCtmOnly`: `executeUpgrade` is the CTM's.
* `DiamondCutRecheck`: what every cut, break-glass included, cannot do (`Admin.sol:119-126`).
* `InitClearsFlag` (countermodel): a break-glass init clears it, so `FlagMonotone` needs its
  premise.

## (b) The caller rule of `setProofSystemStatus` (`IAdmin.sol:122-128`, `Admin.sol:417`)

* `ZiskOffAuthorityExact`: who the call succeeds for.
* `SetProofSystemStatusEffect`: what it writes.
* `MaskWrittenOnlyBySetStatus`, `NonZiskBitsFrozen`: nothing else writes the mask, and only
  the ZiSK bit moves (`ZKChainStorage.sol:287-288`).
* `OwnerDisablesOnFlagged`: the emergency switch works.
* `AdminOnlyRuleLetsAdminDrop` (countermodel): with `s.admin` in place of the ternary the admin
  switches ZiSK off on a flagged diamond.

## (c) The chain admin cannot drop the second proof system (`interop-gating.md:37-45`)

* `ZiskOffOnFlaggedIsOwners`: one step.
* `AdminCannotDropSecondProof`: along runs, from a flagged diamond with ZiSK on.
* `AdminNeverReachesFlaggedZiskOff`: along runs, from any diamond that is not flagged with ZiSK
  off; needs an honest verifier at the moment the flag is set.
* `InteropGatePersists`, `InteropGatePersistsMultiProof`: the second-proof checks of
  `L1MessageRoot.enableInterop` keep passing.
* `LyingVerifierFlagsWithZiskOff`, `BreakGlassDropsSecondProof`, `InteropGateNeedsZeroMask`
  (countermodels).

## (d) Re-enabling is the chain admin's (`interop-gating.md:38`)

* `ReenableIsAdmins`, `BridgehubOwnerCannotReenable`, `AdminReenables`,
  `ZiskStaysOffWithoutAdmin`, `BreakGlassReenables` (countermodel).

## (e) The premises can hold

* `MultiProofVerifierReportsZisk`, `PremisesSatisfiable`.
-/

namespace Contracts.SecondProofSystem.FlagAuthorityV35

open Clear

/-! ## (a) The flag is one-way -/

/-- **`permanentlyRequireSecondProofSystem`, exactly** (`Admin.sol:454-465`). The call succeeds
iff the caller is the admin, the diamond is on its settlement layer, the flag is not set, and
the diamond's verifier reports multi-proof mode for the current mask. It then sets the flag and
changes nothing else in the projection. -/
def Properties.PermanentlyRequireExact : Prop :=
  ∀ (E : Env) (c : Address) (s s' : St),
    step E c .permanentlyRequireSecondProofSystem s = some s' ↔
      (c = s.admin ∧ s.settlementLayer = 0 ∧ s.secondProofSystemRequired = false ∧
        E.proofMode s.verifier s.disabledProofSystems = some MULTI_PROOF_TYPE ∧
        s' = { s with secondProofSystemRequired := true })

/-- **A second call reverts** (`SecondProofSystemAlreadyRequired`, `Admin.sol:455-457`;
`interop-gating.md:34-35`): for every caller and verifier. -/
def Properties.PermanentlyRequireOnce : Prop :=
  ∀ (E : Env) (c : Address) (s : St),
    s.secondProofSystemRequired = true → step E c .permanentlyRequireSecondProofSystem s = none

/-- **No call other than a break-glass cut clears the flag.** One successful call, by any
caller, with any verifier: an `AdminFacet` entry point (a cut with no init or a genuine init
included) or one of the model's other calls. -/
def Properties.FlagMonotoneStep : Prop :=
  ∀ (E : Env) (c : Address) (call : Call) (s s' : St),
    call.isBreakGlass = false → step E c call s = some s' →
    s.secondProofSystemRequired = true → s'.secondProofSystemRequired = true

/-- **The flag is one-way** (`IAdmin.sol:137-140`). Along every run with no break-glass cut, a
set flag stays set. -/
def Properties.FlagMonotone : Prop :=
  ∀ (E : Env) (s s' : St),
    Reach E NoBreakGlass s s' →
    s.secondProofSystemRequired = true → s'.secondProofSystemRequired = true

/-- **Only the admin sets the flag.** A successful call that is not a break-glass cut and after
which the flag is newly set is the admin's `permanentlyRequireSecondProofSystem`, on the
settlement layer, in multi-proof mode. -/
def Properties.FlagSetOnlyByAdmin : Prop :=
  ∀ (E : Env) (c : Address) (call : Call) (s s' : St),
    call.isBreakGlass = false → step E c call s = some s' →
    s.secondProofSystemRequired = false → s'.secondProofSystemRequired = true →
    call = .permanentlyRequireSecondProofSystem ∧ c = s.admin ∧ s.settlementLayer = 0 ∧
      E.proofMode s.verifier s.disabledProofSystems = some MULTI_PROOF_TYPE

/-- **`executeUpgrade` is the CTM's** (`onlyChainTypeManager`, `Admin.sol:593`), whatever the
init. -/
def Properties.BreakGlassCutIsCtmOnly : Prop :=
  ∀ (E : Env) (c : Address) (i : Init) (s s' : St),
    step E c (.executeUpgrade i) s = some s' → c = s.chainTypeManager

/-- **What no cut can do** (`Admin.sol:119-126`; `interop-gating.md:41-42`: "The `AdminFacet`
checks the chain's verifier the same way after every diamond cut, so an upgrade that sets the
verifier another way can't drop it either"). After a successful `upgradeChainFromVersion`,
`executeUpgrade` or `genesisUpgrade`, with any init (a break-glass one included), a diamond
that is still flagged has a verifier that reports multi-proof mode for the zero mask. This is
all the re-check gives: it reads the flag the init left (`InitClearsFlag`) and asks about the
zero mask, not the diamond's (`BreakGlassDropsSecondProof`). -/
def Properties.DiamondCutRecheck : Prop :=
  ∀ (E : Env) (c : Address) (i : Init) (s s' : St),
    (step E c (.upgradeChainFromVersion i) s = some s' ∨
      step E c (.executeUpgrade i) s = some s' ∨ step E c (.genesisUpgrade i) s = some s') →
    s'.secondProofSystemRequired = true → E.proofMode s'.verifier 0 = some MULTI_PROOF_TYPE

/-- **Countermodel: a break-glass init clears the flag.** The CTM's `executeUpgrade` with an
init that writes the flag `false` succeeds on the flagged diamond `w1` (the re-check of
`Admin.sol:121-126` reads the cleared flag and is skipped), and leaves it unflagged. So
`FlagMonotoneStep` and `FlagMonotone` are false without their "no break-glass cut" premise. -/
def Properties.InitClearsFlag : Prop :=
  (∃ s', step multiProofEnv w1.chainTypeManager (.executeUpgrade clearFlagInit) w1 = some s' ∧
      w1.secondProofSystemRequired = true ∧ s'.secondProofSystemRequired = false) ∧
  ¬ (∀ (E : Env) (c : Address) (call : Call) (s s' : St),
      step E c call s = some s' →
      s.secondProofSystemRequired = true → s'.secondProofSystemRequired = true) ∧
  ¬ (∀ (E : Env) (s s' : St),
      Reach E AnyCall s s' →
      s.secondProofSystemRequired = true → s'.secondProofSystemRequired = true)

/-! ## (b) The caller rule -/

/-- **The authorised caller of `setProofSystemStatus`, exactly** (`Admin.sol:417-423`;
`IAdmin.sol:122-128`).

* The call for ZiSK succeeds for exactly one caller: the Bridgehub owner when it disables on a
  flagged diamond, the chain admin otherwise.
* When the two are different addresses, the Bridgehub owner is authorised iff the call disables
  and the flag is set, and the chain admin is authorised iff not (it enables, or the flag is
  not set).
* For any other proof system it reverts for every caller (`InvalidProofSystem`). -/
def Properties.ZiskOffAuthorityExact : Prop :=
  ∀ (E : Env) (c : Address) (enabled : Bool) (s : St),
    ((∃ s', step E c (.setProofSystemStatus .zisk enabled) s = some s') ↔
        c = if enabled = false ∧ s.secondProofSystemRequired = true
            then s.bridgehubOwner else s.admin) ∧
    (s.admin ≠ s.bridgehubOwner →
      ((∃ s', step E s.bridgehubOwner (.setProofSystemStatus .zisk enabled) s = some s') ↔
        (enabled = false ∧ s.secondProofSystemRequired = true)) ∧
      ((∃ s', step E s.admin (.setProofSystemStatus .zisk enabled) s = some s') ↔
        ¬ (enabled = false ∧ s.secondProofSystemRequired = true))) ∧
    (∀ p, p ≠ ProofSystem.zisk → step E c (.setProofSystemStatus p enabled) s = none)

/-- **What `setProofSystemStatus` writes** (`Admin.sol:425-430`). A successful call writes only
the mask. Enabling clears the ZiSK bit, disabling sets it, and the other bits keep their
values. -/
def Properties.SetProofSystemStatusEffect : Prop :=
  ∀ (E : Env) (c : Address) (p : ProofSystem) (enabled : Bool) (s s' : St),
    step E c (.setProofSystemStatus p enabled) s = some s' →
    s' = { s with disabledProofSystems := newMask s.disabledProofSystems .zisk enabled } ∧
    (enabled = true → ziskOn s') ∧ (enabled = false → ziskOff s') ∧
    s'.disabledProofSystems &&& ~~~ziskBit = s.disabledProofSystems &&& ~~~ziskBit

/-- **Nothing else writes the mask.** A successful call that is not a break-glass cut and that
changes the mask is `setProofSystemStatus` for ZiSK. -/
def Properties.MaskWrittenOnlyBySetStatus : Prop :=
  ∀ (E : Env) (c : Address) (call : Call) (s s' : St),
    call.isBreakGlass = false → step E c call s = some s' →
    s'.disabledProofSystems ≠ s.disabledProofSystems →
    ∃ enabled, call = .setProofSystemStatus .zisk enabled

/-- **Only the ZiSK bit moves** (`ZKChainStorage.sol:287-288`: "A ZKsync OS chain accepts only
the `ProofSystem.Zisk` disable bit, so its Airbender lane can not be switched off"). Along every
run with no break-glass cut the mask's other bits keep their values; in particular a clear
Airbender bit stays clear. -/
def Properties.NonZiskBitsFrozen : Prop :=
  ∀ (E : Env) (s s' : St),
    Reach E NoBreakGlass s s' →
    s'.disabledProofSystems &&& ~~~ziskBit = s.disabledProofSystems &&& ~~~ziskBit ∧
    (s.disabledProofSystems &&& ProofSystem.airbender.bit = 0 →
      s'.disabledProofSystems &&& ProofSystem.airbender.bit = 0)

/-- **The emergency switch works** (`interop-gating.md:37-38`; `Admin.sol:424`). On a flagged
diamond the Bridgehub owner's ZiSK-off succeeds in every state, whatever the verifier, the
settlement layer or the batches. It leaves ZiSK off and the flag set. -/
def Properties.OwnerDisablesOnFlagged : Prop :=
  ∀ (E : Env) (s : St),
    s.secondProofSystemRequired = true →
    ∃ s', step E s.bridgehubOwner (.setProofSystemStatus .zisk false) s = some s' ∧
      ziskOff s' ∧ s'.secondProofSystemRequired = true

/-- **Countermodel: the caller rule is what stops the admin.** Replace the ternary of
`Admin.sol:417` by `s.admin` (`adminOnlyRule`). Then on the flagged diamond `w1`, whose admin is
not the Bridgehub owner, the admin's ZiSK-off succeeds and reaches a flagged diamond with ZiSK
off; under the source's rule the same call reverts. So (b) and (c) rest on the rule. -/
def Properties.AdminOnlyRuleLetsAdminDrop : Prop :=
  w1.admin ≠ w1.bridgehubOwner ∧ w1.secondProofSystemRequired = true ∧ ziskOn w1 ∧
  stepWith adminOnlyRule multiProofEnv w1.admin (.setProofSystemStatus .zisk false) w1 = some w3 ∧
  FlaggedZiskOff w3 ∧
  ReachWith adminOnlyRule multiProofEnv (AdminSideHonest multiProofEnv) w1 w3 ∧
  step multiProofEnv w1.admin (.setProofSystemStatus .zisk false) w1 = none

/-! ## (c) The chain admin cannot drop the second proof system -/

/-- **ZiSK-off on a flagged diamond is the Bridgehub owner's.** A successful call that is not a
break-glass cut, from a flagged diamond with ZiSK on to one with ZiSK off, is
`setProofSystemStatus(Zisk, false)` by the Bridgehub owner of that moment. -/
def Properties.ZiskOffOnFlaggedIsOwners : Prop :=
  ∀ (E : Env) (c : Address) (call : Call) (s s' : St),
    call.isBreakGlass = false → step E c call s = some s' →
    s.secondProofSystemRequired = true → ziskOn s → ziskOff s' →
    call = .setProofSystemStatus .zisk false ∧ c = s.bridgehubOwner

/-- **The admin cannot drop the second proof system** (`interop-gating.md:44-45`: the
requirement "takes the way back to a single proof system out of the chain admin's hands").
Along every run with no break-glass cut and no `setProofSystemStatus` by the Bridgehub owner of
that moment (every other call, by anyone, is allowed), a flagged diamond with ZiSK on stays
flagged with ZiSK on. No premise on the verifier. -/
def Properties.AdminCannotDropSecondProof : Prop :=
  ∀ (E : Env) (s s' : St),
    Reach E AdminSide s s' →
    s.secondProofSystemRequired = true → ziskOn s →
    s'.secondProofSystemRequired = true ∧ ziskOn s'

/-- **The admin never reaches a flagged diamond with ZiSK off.** Along every run with no
break-glass cut and no `setProofSystemStatus` by the Bridgehub owner of that moment, in which
the verifier installed when the flag is set reports ZiSK honestly (`ReportsZisk`), a diamond
that is not flagged-with-ZiSK-off never becomes so. This also covers the order "ZiSK off first,
flag second": `permanentlyRequireSecondProofSystem` reverts while ZiSK is off. -/
def Properties.AdminNeverReachesFlaggedZiskOff : Prop :=
  ∀ (E : Env) (s s' : St),
    Reach E (AdminSideHonest E) s s' → ¬ FlaggedZiskOff s → ¬ FlaggedZiskOff s'

/-- **The interop gate keeps passing** (`L1MessageRoot.sol:81-85`). If the second-proof checks
of `enableInterop(_, true)` pass on a diamond whose mask is zero, they pass, with the mask still
zero, in every state of every run with no break-glass cut and no `setProofSystemStatus` by the
Bridgehub owner of that moment: across the admin's calls and across genuine upgrades that
install new verifiers. About this diamond only. -/
def Properties.InteropGatePersists : Prop :=
  ∀ (E : Env) (s s' : St),
    Reach E AdminSide s s' →
    InteropSecondProofGate E s → s.disabledProofSystems = 0 →
    InteropSecondProofGate E s' ∧ s'.disabledProofSystems = 0

/-- **The interop gate under the genuine verifier.** When every verifier is the genuine
`MultiProofVerifier`, the gate passes exactly on a flagged diamond with a zero mask, so it
passes "not during an emergency ZiSK-off" (`interop-gating.md:54-56`), and once it passes it
keeps passing along the runs of `InteropGatePersists`. -/
def Properties.InteropGatePersistsMultiProof : Prop :=
  (∀ s : St, InteropSecondProofGate multiProofEnv s ↔
      (s.secondProofSystemRequired = true ∧ s.disabledProofSystems = 0)) ∧
  (∀ s : St, ziskOff s → ¬ InteropSecondProofGate multiProofEnv s) ∧
  (∀ s s' : St, Reach multiProofEnv AdminSide s s' →
      InteropSecondProofGate multiProofEnv s → InteropSecondProofGate multiProofEnv s')

/-- **Countermodel: the verifier premise of `AdminNeverReachesFlaggedZiskOff` is needed.**
With a verifier that reports multi-proof mode for every mask, the admin of `w0` switches ZiSK
off while unflagged and then sets the flag: a run allowed by `AdminSide`, from a diamond that is
not flagged-with-ZiSK-off to one that is. Such a verifier makes the check of `Admin.sol:458-461`
pass for every mask, so this is also what that check rules out under the genuine verifier.
`AdminCannotDropSecondProof` is not contradicted: it starts from a flagged diamond. -/
def Properties.LyingVerifierFlagsWithZiskOff : Prop :=
  ¬ FlaggedZiskOff w0 ∧ ¬ ReportsZisk lyingEnv w0.verifier ∧
  ∃ s', Reach lyingEnv AdminSide w0 s' ∧ FlaggedZiskOff s'

/-- **Countermodel: "no break-glass cut" is needed in (c).** The CTM's `executeUpgrade` with an
init that sets the ZiSK bit succeeds on the flagged diamond `w1` (the re-check of
`Admin.sol:121-126` asks `getProofMode(0)`, not the mask) and leaves it flagged with ZiSK off,
with no `setProofSystemStatus` call at all. -/
def Properties.BreakGlassDropsSecondProof : Prop :=
  w1.secondProofSystemRequired = true ∧ ziskOn w1 ∧
  step multiProofEnv w1.chainTypeManager (.executeUpgrade ziskOffInit) w1 = some w3 ∧
  FlaggedZiskOff w3 ∧
  Reach multiProofEnv NotOwnerStatus w1 w3 ∧
  ¬ Reach multiProofEnv AdminSide w1 w3

/-- **Countermodel: the zero-mask premise of `InteropGatePersists` is needed.** A genuine
upgrade checks the new verifier against the zero mask (`BaseZkSyncUpgrade.sol:144`,
`Admin.sol:122`), not against the diamond's. Take the verifier at `10` to report multi-proof
mode for every mask and the one at `11` to be the genuine `MultiProofVerifier` (`mixedEnv`). On
the flagged diamond `w3` (ZiSK off, verifier `10`) the gate passes. The genuine upgrade to `11`
succeeds, a run allowed by `AdminSide`, and the gate then fails. Under the genuine verifier
everywhere the premise is implied by the gate (`InteropGatePersistsMultiProof`). -/
def Properties.InteropGateNeedsZeroMask : Prop :=
  InteropSecondProofGate mixedEnv w3 ∧ w3.disabledProofSystems ≠ 0 ∧
  ∃ s', step mixedEnv w3.admin (.upgradeChainFromVersion (.genuine ⟨some 11⟩)) w3 = some s' ∧
    Reach mixedEnv AdminSide w3 s' ∧ ¬ InteropSecondProofGate mixedEnv s'

/-! ## (d) Re-enabling is the chain admin's -/

/-- **Re-enabling is the admin's** (`Admin.sol:417`, the `_enabled` branch;
`interop-gating.md:38`). A successful `setProofSystemStatus(_, true)` is by the chain admin,
flagged or not. -/
def Properties.ReenableIsAdmins : Prop :=
  ∀ (E : Env) (c : Address) (p : ProofSystem) (s s' : St),
    step E c (.setProofSystemStatus p true) s = some s' → c = s.admin

/-- **The Bridgehub owner cannot re-enable.** When it is not the chain admin, its
`setProofSystemStatus(_, true)` reverts in every state. -/
def Properties.BridgehubOwnerCannotReenable : Prop :=
  ∀ (E : Env) (p : ProofSystem) (s : St),
    s.bridgehubOwner ≠ s.admin → step E s.bridgehubOwner (.setProofSystemStatus p true) s = none

/-- **The admin can always re-enable.** The admin's `setProofSystemStatus(Zisk, true)` succeeds
in every state, flagged or not, and leaves ZiSK on with the flag unchanged. In particular the
admin can undo governance's emergency ZiSK-off at once. -/
def Properties.AdminReenables : Prop :=
  ∀ (E : Env) (s : St),
    ∃ s', step E s.admin (.setProofSystemStatus .zisk true) s = some s' ∧ ziskOn s' ∧
      s'.secondProofSystemRequired = s.secondProofSystemRequired

/-- **Without the admin, ZiSK stays off.** Along every run with no break-glass cut and no
`setProofSystemStatus` by the chain admin of that moment (every other call, by anyone, the
Bridgehub owner included, is allowed), ZiSK off stays off. -/
def Properties.ZiskStaysOffWithoutAdmin : Prop :=
  ∀ (E : Env) (s s' : St), Reach E OwnerSide s s' → ziskOff s → ziskOff s'

/-- **Countermodel: "no break-glass cut" is needed in (d).** The CTM's `executeUpgrade` with an
init that clears the mask turns ZiSK back on, on `w3`, with no call by the admin. -/
def Properties.BreakGlassReenables : Prop :=
  ziskOff w3 ∧
  step multiProofEnv w3.chainTypeManager (.executeUpgrade clearMaskInit) w3 = some w1 ∧
  ziskOn w1 ∧ w3.chainTypeManager ≠ w3.admin

/-! ## (e) The premises can hold -/

/-- **The genuine verifier reports ZiSK honestly** (`MultiProofVerifier.sol:101-109`): it
reports multi-proof mode exactly for the zero mask. -/
def Properties.MultiProofVerifierReportsZisk : Prop :=
  (∀ v, ReportsZisk multiProofEnv v) ∧
  (∀ m, multiProofGetProofMode m = some MULTI_PROOF_TYPE ↔ m = 0)

/-- **The premise bundles are satisfiable, by runs that do something.**

* `AdminSideHonest` (so also `AdminSide` and `NoBreakGlass`): from `w0`, not flagged-with-ZiSK-off,
  the admin sets the flag (`w1`), then a genuine upgrade installs the verifier at `11` (`w2`).
  The run ends flagged with ZiSK on, and the interop gate passes at `w1` and at `w2`.
* `OwnerSide`: from `w1` the Bridgehub owner switches ZiSK off (`w3`), which ends flagged with
  ZiSK off; the gate fails there.
* The admin then re-enables: `w3` back to `w1`, a run allowed by `AdminSideHonest`.
* The admin and the Bridgehub owner of the witnesses are different addresses. -/
def Properties.PremisesSatisfiable : Prop :=
  (¬ FlaggedZiskOff w0 ∧
    step multiProofEnv w0.admin .permanentlyRequireSecondProofSystem w0 = some w1 ∧
    step multiProofEnv w1.admin (.upgradeChainFromVersion (.genuine ⟨some 11⟩)) w1 = some w2 ∧
    Reach multiProofEnv (AdminSideHonest multiProofEnv) w0 w2 ∧
    Reach multiProofEnv AdminSide w0 w2 ∧ Reach multiProofEnv NoBreakGlass w0 w2 ∧
    w2.secondProofSystemRequired = true ∧ ziskOn w2 ∧
    InteropSecondProofGate multiProofEnv w1 ∧ InteropSecondProofGate multiProofEnv w2) ∧
  (step multiProofEnv w1.bridgehubOwner (.setProofSystemStatus .zisk false) w1 = some w3 ∧
    Reach multiProofEnv OwnerSide w1 w3 ∧ FlaggedZiskOff w3 ∧
    ¬ InteropSecondProofGate multiProofEnv w3) ∧
  (step multiProofEnv w3.admin (.setProofSystemStatus .zisk true) w3 = some w1 ∧
    Reach multiProofEnv (AdminSideHonest multiProofEnv) w3 w1) ∧
  w0.admin ≠ w0.bridgehubOwner

end Contracts.SecondProofSystem.FlagAuthorityV35
