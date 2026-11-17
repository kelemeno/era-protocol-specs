import EraSpec.Contracts.SecondProofSystem.Specs.FlagAuthorityV35

/-!
# Properties: the second-proof-system flag is one-way, and ZiSK-off is the Bridgehub owner's

Statements over `EraSpec.Contracts.SecondProofSystem.Specs.FlagAuthorityV35` (era-contracts
`draft/v0.35.0` at `b17415d20`). Proofs are in
`EraSpec.Contracts.SecondProofSystem.Proofs.FlagAuthorityV35`.

Every statement is about **one diamond** whose facets are those at `b17415d20`, projected onto
seven storage fields plus the Bridgehub's owner. "No break-glass cut" means no diamond cut
whose init is code other than the genuine engines. The frame for the other facets is a source
reading, not a theorem, and dispatch through the diamond proxy is not modelled (see the Specs
header, "Not modelled"). No statement has a hash premise.

## (a) The flag is one-way (`IAdmin.sol:137-140`: "once activated, there is no way back")

* `PermanentlyRequireExact`: when the call succeeds, and what it writes.
* `PermanentlyRequireOnce`: on a flagged diamond it reverts for every caller.
* `FlagMonotoneStep`, `FlagMonotone`: no call other than a break-glass cut clears the flag.
* `FlagSetOnlyByAdmin`: outside break-glass, only the admin's
  `permanentlyRequireSecondProofSystem` sets it.
* `CtmCutEntryPointsAreCtmOnly`: `executeUpgrade` and `genesisUpgrade` are the CTM's.
* `DiamondCutRecheck`: what every cut, break-glass included, leaves behind
  (`Admin.sol:121-126`).
* `InitClearsFlag` (countermodel): a break-glass init clears it, so `FlagMonotone` needs its
  premise.
* Witnesses: `PermanentlyRequireGuardsWitness`, `FlagMonotoneRunWitness`,
  `VerifierChecksWitness`.

## (b) The caller rule of `setProofSystemStatus` (`IAdmin.sol:122-128`, `Admin.sol:417`)

* `ZiskOffAuthorityExact`: who the call succeeds for.
* `SetProofSystemStatusEffect`: what it writes.
* `MaskWrittenOnlyBySetStatus`, `NonZiskBitsFrozen`: nothing else writes the mask, and only
  the ZiSK bit moves (`ZKChainStorage.sol:287-288`).
* `OwnerDisablesOnFlagged`: the emergency switch, in the model.
* `AdminOnlyRuleLetsAdminDrop` (countermodel): with `s.admin` in place of the ternary the admin
  switches ZiSK off on a flagged diamond.
* Witnesses: `CallerRuleWitness`, `NonZiskBitsWitness`.

## (c) The chain admin cannot drop the second proof system (`interop-gating.md:37-38, 50-51`)

* `ZiskOffOnFlaggedIsOwners`: one step.
* `AdminCannotDropSecondProof`: along runs, from a flagged diamond with ZiSK on.
* `AdminNeverReachesFlaggedZiskOff`: along runs, from any diamond that is not flagged with ZiSK
  off; needs an honest verifier at the moment the flag is set.
* `InteropGatePersists`, `InteropGatePersistsMultiProof`: the second-proof checks of
  `L1MessageRoot.enableInterop` keep passing.
* `LyingVerifierFlagsWithZiskOff`, `BreakGlassDropsSecondProof`, `InteropGateNeedsZeroMask`
  (countermodels).
* Witnesses: `AdminSideRunWitness`, `HonestRunWitness`.

## (d) Re-enabling is the chain admin's (`interop-gating.md:38`)

* `ReenableIsAdmins`, `BridgehubOwnerCannotReenable`, `AdminReenables`,
  `ZiskStaysOffWithoutAdmin`, `BreakGlassReenables` (countermodel).
* Witness: `OwnerSideRunWitness`.

## (e) The genuine verifier

* `MultiProofVerifierReportsZisk`.

## (f) Verifier answers that change between calls

* `ReachEnvsExtendsReach`: a run with fixed verifier answers is a run of `ReachEnvs`.
* `FlagMonotoneAnyVerifiers`, `AdminCannotDropSecondProofAnyVerifiers`,
  `AdminNeverReachesFlaggedZiskOffAnyVerifiers`, `ZiskStaysOffWithoutAdminAnyVerifiers`: the
  run statements of (a)-(d) whose conclusions do not mention the verifier, along runs in which
  every call may see its own `getProofMode` answers.
* Witness: `AnyVerifiersRunWitness`.
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
`interop-gating.md:34-35`): on a flagged diamond, for every caller and every verifier. -/
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

/-- **`executeUpgrade` and `genesisUpgrade` are the CTM's** (`onlyChainTypeManager`,
`Admin.sol:593`, `:599`): a successful call, whatever its init, is by `s.chainTypeManager`. The
third cut entry point, `upgradeChainFromVersion`, runs the cut the CTM composed for the edge; its
caller is not checked in the model (the source's `onlyAdminOrChainTypeManagerOrValidator`,
`:562`, is omitted). -/
def Properties.CtmCutEntryPointsAreCtmOnly : Prop :=
  ∀ (E : Env) (c : Address) (i : Init) (s s' : St),
    (step E c (.executeUpgrade i) s = some s' → c = s.chainTypeManager) ∧
    (step E c (.genesisUpgrade i) s = some s' → c = s.chainTypeManager)

/-- **What every cut leaves behind** (`Admin.sol:119-126`; `interop-gating.md:41-42`: "The
`AdminFacet` checks the chain's verifier the same way after every diamond cut, so an upgrade
that sets the verifier another way can't drop it either"). After a successful
`upgradeChainFromVersion`, `executeUpgrade` or `genesisUpgrade`, with any init (a break-glass one
included), a diamond that is still flagged has a verifier that reports multi-proof mode for the
zero mask. This is all the re-check gives: it reads the flag the init left (`InitClearsFlag`)
and asks about the zero mask, not the diamond's (`BreakGlassDropsSecondProof`). -/
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

/-- **Witness: each guard of `permanentlyRequireSecondProofSystem` decides a call**
(premises of `PermanentlyRequireExact`, `PermanentlyRequireOnce`, `FlagSetOnlyByAdmin`). Under
the genuine `MultiProofVerifier` everywhere, the admin's call on `w0` succeeds and gives `w1`.
Changing one thing makes it revert: the caller (the Bridgehub owner), the settlement layer
(`7`), the flag (`w1`, the admin's second call), the mask (`w4`, ZiSK off: PLONK mode), or the
verifier (the Airbender-only `ZKsyncOSVerifier` at `12`, under `airbenderAt12Env`). -/
def Properties.PermanentlyRequireGuardsWitness : Prop :=
  step multiProofEnv w0.admin .permanentlyRequireSecondProofSystem w0 = some w1 ∧
  w0.bridgehubOwner ≠ w0.admin ∧
  step multiProofEnv w0.bridgehubOwner .permanentlyRequireSecondProofSystem w0 = none ∧
  step multiProofEnv w0.admin .permanentlyRequireSecondProofSystem
    { w0 with settlementLayer := 7 } = none ∧
  step multiProofEnv w1.admin .permanentlyRequireSecondProofSystem w1 = none ∧
  step multiProofEnv w4.admin .permanentlyRequireSecondProofSystem w4 = none ∧
  step airbenderAt12Env w0.admin .permanentlyRequireSecondProofSystem
    { w0 with verifier := 12 } = none

/-- **Witness: a run with no break-glass cut, from a flagged diamond, that moves the mask and
the verifier** (premises of `FlagMonotoneStep` and `FlagMonotone`). From `w1` the Bridgehub
owner switches ZiSK off (`w3`), the admin switches it back on (`w1`), and the admin's genuine
upgrade installs the verifier at `11` (`w2`). Each step is a successful call by the caller the
source requires, and the flag is set at both ends. -/
def Properties.FlagMonotoneRunWitness : Prop :=
  step multiProofEnv w1.bridgehubOwner (.setProofSystemStatus .zisk false) w1 = some w3 ∧
  step multiProofEnv w3.admin (.setProofSystemStatus .zisk true) w3 = some w1 ∧
  step multiProofEnv w1.admin (.upgradeChainFromVersion (.genuine ⟨some 11⟩)) w1 = some w2 ∧
  Reach multiProofEnv NoBreakGlass w1 w2 ∧
  w1.secondProofSystemRequired = true ∧ w2.secondProofSystemRequired = true ∧
  w2.verifier ≠ w1.verifier

/-- **Witness: the verifier checks decide calls** (premises of `DiamondCutRecheck`). Under the
genuine `MultiProofVerifier` everywhere, the admin's genuine upgrade of the flagged `w1` to the
verifier at `11` succeeds and leaves it flagged. Under `airbenderAt12Env` (the Airbender-only
`ZKsyncOSVerifier` at `12`), on the flagged `w1`:

* the genuine upgrade to `12` reverts, at `_setVerifier` (`BaseZkSyncUpgrade.sol:143-148`); the
  re-check after the cut would refuse it as well;
* the CTM's cut whose init writes the verifier slot to `12` directly, bypassing `_setVerifier`,
  reverts at the re-check (`Admin.sol:121-126`), which is the check that refuses it.

On the unflagged `w0` both calls succeed and install `12`. -/
def Properties.VerifierChecksWitness : Prop :=
  step multiProofEnv w1.admin (.upgradeChainFromVersion (.genuine ⟨some 11⟩)) w1 = some w2 ∧
  w2.secondProofSystemRequired = true ∧
  step airbenderAt12Env w1.admin (.upgradeChainFromVersion (.genuine ⟨some 12⟩)) w1 = none ∧
  step airbenderAt12Env w1.chainTypeManager (.executeUpgrade (writeVerifierInit 12)) w1 = none ∧
  step airbenderAt12Env w0.admin (.upgradeChainFromVersion (.genuine ⟨some 12⟩)) w0 =
    some { w0 with verifier := 12 } ∧
  step airbenderAt12Env w0.chainTypeManager (.executeUpgrade (writeVerifierInit 12)) w0 =
    some { w0 with verifier := 12 }

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

/-- **What `setProofSystemStatus` writes** (`Admin.sol:425-430`). A successful call is for ZiSK
and writes only the mask. Enabling clears the ZiSK bit, disabling sets it, and the other bits
keep their values. -/
def Properties.SetProofSystemStatusEffect : Prop :=
  ∀ (E : Env) (c : Address) (p : ProofSystem) (enabled : Bool) (s s' : St),
    step E c (.setProofSystemStatus p enabled) s = some s' →
    p = .zisk ∧
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

/-- **The emergency switch, in the model** (`interop-gating.md:37-38`). On a flagged diamond the
model's `setProofSystemStatus(Zisk, false)` by `s.bridgehubOwner` succeeds in every state,
whatever the verifier and the settlement layer, and leaves ZiSK off with the flag set. The
source function reads no batch counter (`Admin.sol:416-432`; the comment at `:424`), a source
reading: the model has no batches. This is about the facet code for a call that reaches it,
with `owner()` returning (Specs, "Not modelled"). -/
def Properties.OwnerDisablesOnFlagged : Prop :=
  ∀ (E : Env) (s : St),
    s.secondProofSystemRequired = true →
    ∃ s', step E s.bridgehubOwner (.setProofSystemStatus .zisk false) s = some s' ∧
      ziskOff s' ∧ s'.secondProofSystemRequired = true

/-- **Countermodel: the caller rule is what stops the admin.** Replace the ternary of
`Admin.sol:417` by `s.admin` (`adminOnlyRule`). Then on the flagged diamond `w1`, whose admin is
not the Bridgehub owner, the admin's ZiSK-off succeeds and reaches a flagged diamond with ZiSK
off, in a run allowed by `AdminSideHonest`; under the source's rule the same call reverts. So
`AdminCannotDropSecondProof` and `AdminNeverReachesFlaggedZiskOff` rest on the rule. -/
def Properties.AdminOnlyRuleLetsAdminDrop : Prop :=
  w1.admin ≠ w1.bridgehubOwner ∧ w1.secondProofSystemRequired = true ∧ ziskOn w1 ∧
  stepWith adminOnlyRule multiProofEnv w1.admin (.setProofSystemStatus .zisk false) w1 = some w3 ∧
  FlaggedZiskOff w3 ∧
  ReachWith adminOnlyRule multiProofEnv (AdminSideHonest multiProofEnv) w1 w3 ∧
  step multiProofEnv w1.admin (.setProofSystemStatus .zisk false) w1 = none

/-- **Witness: the caller rule decides calls in both directions** (premises of
`ZiskOffAuthorityExact`, `SetProofSystemStatusEffect`, `OwnerDisablesOnFlagged`). The admin
`1` and the Bridgehub owner `2` are different addresses. On the flagged `w1`: the owner's
ZiSK-off succeeds (giving `w3`) and the admin's reverts; the admin's ZiSK-on succeeds and the
owner's reverts. On the unflagged `w0`: the admin's ZiSK-off succeeds (giving `w4`) and the
owner's reverts. For Airbender or Boojum the admin's call reverts on `w0`. -/
def Properties.CallerRuleWitness : Prop :=
  w1.admin ≠ w1.bridgehubOwner ∧
  step multiProofEnv w1.bridgehubOwner (.setProofSystemStatus .zisk false) w1 = some w3 ∧
  step multiProofEnv w1.admin (.setProofSystemStatus .zisk false) w1 = none ∧
  step multiProofEnv w1.admin (.setProofSystemStatus .zisk true) w1 = some w1 ∧
  step multiProofEnv w1.bridgehubOwner (.setProofSystemStatus .zisk true) w1 = none ∧
  step multiProofEnv w0.admin (.setProofSystemStatus .zisk false) w0 = some w4 ∧
  step multiProofEnv w0.bridgehubOwner (.setProofSystemStatus .zisk false) w0 = none ∧
  step multiProofEnv w0.admin (.setProofSystemStatus .airbender false) w0 = none ∧
  step multiProofEnv w0.admin (.setProofSystemStatus .boojum false) w0 = none

/-- **Witness: runs that move the ZiSK bit next to another set bit** (premises of
`NonZiskBitsFrozen` and `MaskWrittenOnlyBySetStatus`). `w6` is flagged with mask `1` (the Boojum
bit). The Bridgehub owner's ZiSK-off gives mask `5`, and the admin's ZiSK-on gives mask `1`
again. Each is a one-call run with no break-glass cut that changes the mask; across both the
bits other than ZiSK stay `1`, and the Airbender bit is clear. -/
def Properties.NonZiskBitsWitness : Prop :=
  w6.disabledProofSystems = 1 ∧
  step multiProofEnv w6.bridgehubOwner (.setProofSystemStatus .zisk false) w6 =
    some { w6 with disabledProofSystems := 5 } ∧
  step multiProofEnv w6.admin (.setProofSystemStatus .zisk true)
    { w6 with disabledProofSystems := 5 } = some w6 ∧
  Reach multiProofEnv NoBreakGlass w6 { w6 with disabledProofSystems := 5 } ∧
  Reach multiProofEnv NoBreakGlass { w6 with disabledProofSystems := 5 } w6 ∧
  w6.disabledProofSystems &&& ProofSystem.airbender.bit = 0 ∧
  (5 : UInt8) &&& ~~~ziskBit = w6.disabledProofSystems &&& ~~~ziskBit

/-! ## (c) The chain admin cannot drop the second proof system -/

/-- **ZiSK-off on a flagged diamond is the Bridgehub owner's.** A successful call that is not a
break-glass cut, from a flagged diamond with ZiSK on to one with ZiSK off, is
`setProofSystemStatus(Zisk, false)` by the Bridgehub owner of that moment. -/
def Properties.ZiskOffOnFlaggedIsOwners : Prop :=
  ∀ (E : Env) (c : Address) (call : Call) (s s' : St),
    call.isBreakGlass = false → step E c call s = some s' →
    s.secondProofSystemRequired = true → ziskOn s → ziskOff s' →
    call = .setProofSystemStatus .zisk false ∧ c = s.bridgehubOwner

/-- **The admin cannot drop the second proof system** (`interop-gating.md:50-51`: the
requirement "only takes the way back to a single proof system out of the chain admin's hands").
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
the verifier in use whenever `permanentlyRequireSecondProofSystem` is called reports ZiSK
honestly (`ReportsZisk`), a diamond that is not flagged-with-ZiSK-off never becomes so. This
covers the order "ZiSK off first, flag second": with such a verifier,
`permanentlyRequireSecondProofSystem` reverts while ZiSK is off. -/
def Properties.AdminNeverReachesFlaggedZiskOff : Prop :=
  ∀ (E : Env) (s s' : St),
    Reach E (AdminSideHonest E) s s' → ¬ FlaggedZiskOff s → ¬ FlaggedZiskOff s'

/-- **The interop gate keeps passing** (`L1MessageRoot.sol:81-85`). If the second-proof checks
of `enableInterop(_, true)` pass on a diamond whose mask is zero, they pass, with the mask still
zero, in every state of every run with no break-glass cut and no `setProofSystemStatus` by the
Bridgehub owner of that moment: across the admin's calls and across genuine upgrades that
install new verifiers. About the checks' predicate on this diamond only. -/
def Properties.InteropGatePersists : Prop :=
  ∀ (E : Env) (s s' : St),
    Reach E AdminSide s s' →
    InteropSecondProofGate E s → s.disabledProofSystems = 0 →
    InteropSecondProofGate E s' ∧ s'.disabledProofSystems = 0

/-- **The interop gate under the genuine verifier.** When every verifier is the genuine
`MultiProofVerifier`, the gate passes exactly on a flagged diamond with a zero mask, so it fails
during an emergency ZiSK-off (`interop-gating.md:60-62`: "so not during an emergency ZiSK-off"),
and once it passes it keeps passing along the runs of `InteropGatePersists`. -/
def Properties.InteropGatePersistsMultiProof : Prop :=
  (∀ s : St, InteropSecondProofGate multiProofEnv s ↔
      (s.secondProofSystemRequired = true ∧ s.disabledProofSystems = 0)) ∧
  (∀ s : St, ziskOff s → ¬ InteropSecondProofGate multiProofEnv s) ∧
  (∀ s s' : St, Reach multiProofEnv AdminSide s s' →
      InteropSecondProofGate multiProofEnv s → InteropSecondProofGate multiProofEnv s')

/-- **Countermodel: the verifier premise of `AdminNeverReachesFlaggedZiskOff` is needed.**
With a verifier that reports multi-proof mode for every mask (`lyingEnv`, which is not
`ReportsZisk`), some run allowed by `AdminSide` leads from `w0`, which is not
flagged-with-ZiSK-off, to a state that is (the proof's run: the admin switches ZiSK off while
unflagged, then sets the flag). Under the genuine `MultiProofVerifier` the admin's ZiSK-off on
`w0` gives `w4`, and setting the flag on `w4` reverts (PLONK mode). `AdminCannotDropSecondProof`
is not contradicted: it starts from a flagged diamond. -/
def Properties.LyingVerifierFlagsWithZiskOff : Prop :=
  ¬ FlaggedZiskOff w0 ∧ ¬ ReportsZisk lyingEnv w0.verifier ∧
  (∃ s', Reach lyingEnv AdminSide w0 s' ∧ FlaggedZiskOff s') ∧
  step multiProofEnv w0.admin (.setProofSystemStatus .zisk false) w0 = some w4 ∧
  step multiProofEnv w4.admin .permanentlyRequireSecondProofSystem w4 = none

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
the flagged diamond `w3` (ZiSK off, verifier `10`) the gate passes. The admin's genuine upgrade
to `11` succeeds, a run allowed by `AdminSide`, and the gate then fails. Under the genuine
verifier everywhere the premise is implied by the gate (`InteropGatePersistsMultiProof`). -/
def Properties.InteropGateNeedsZeroMask : Prop :=
  InteropSecondProofGate mixedEnv w3 ∧ w3.disabledProofSystems ≠ 0 ∧
  ∃ s', step mixedEnv w3.admin (.upgradeChainFromVersion (.genuine ⟨some 11⟩)) w3 = some s' ∧
    Reach mixedEnv AdminSide w3 s' ∧ ¬ InteropSecondProofGate mixedEnv s'

/-- **Witness: an admin-side run from a flagged diamond that changes the admin, the Bridgehub
owner and the verifier** (premises of
`AdminCannotDropSecondProof`, `InteropGatePersists`, `InteropGatePersistsMultiProof`). Under the
genuine `MultiProofVerifier` everywhere, from `w1` (flagged, ZiSK on, mask zero, gate passing):
the admin `1` nominates `4`, `4` accepts, the Bridgehub owner becomes `5`, and the new admin's
genuine upgrade installs the verifier at `11`, giving `w5`. The run is allowed by `AdminSide`.
At `w5` the diamond is flagged with ZiSK on and the gate passes; the new admin's ZiSK-off
reverts and the new owner's succeeds. -/
def Properties.AdminSideRunWitness : Prop :=
  InteropSecondProofGate multiProofEnv w1 ∧ w1.disabledProofSystems = 0 ∧ ziskOn w1 ∧
  Reach multiProofEnv AdminSide w1 w5 ∧
  w5.admin ≠ w1.admin ∧ w5.bridgehubOwner ≠ w1.bridgehubOwner ∧ w5.verifier ≠ w1.verifier ∧
  w5.secondProofSystemRequired = true ∧ ziskOn w5 ∧ InteropSecondProofGate multiProofEnv w5 ∧
  step multiProofEnv w5.admin (.setProofSystemStatus .zisk false) w5 = none ∧
  (∃ s', step multiProofEnv w5.bridgehubOwner (.setProofSystemStatus .zisk false) w5 = some s')

/-- **Witness: honest admin-side runs through ZiSK-off to the flag** (premises of
`AdminNeverReachesFlaggedZiskOff`). Under the genuine `MultiProofVerifier` everywhere: from
`w0` the admin switches ZiSK off (`w4`, unflagged); from `w4` it switches ZiSK back on (`w0`),
sets the flag (`w1`), and its genuine upgrade installs the verifier at `11` (`w2`). Both runs
are allowed by `AdminSideHonest` and start in a state that is not flagged-with-ZiSK-off (`w4`
has ZiSK off); the second ends flagged with ZiSK on. -/
def Properties.HonestRunWitness : Prop :=
  ¬ FlaggedZiskOff w0 ∧ ziskOff w4 ∧
  Reach multiProofEnv (AdminSideHonest multiProofEnv) w0 w4 ∧
  Reach multiProofEnv (AdminSideHonest multiProofEnv) w4 w2 ∧
  w2.secondProofSystemRequired = true ∧ ziskOn w2

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

/-- **The admin can always re-enable, in the model.** The model's
`setProofSystemStatus(Zisk, true)` by `s.admin` succeeds in every state, flagged or not, and
leaves ZiSK on with the flag unchanged. In particular the admin can undo governance's emergency
ZiSK-off at once. As for `OwnerDisablesOnFlagged`, this is about the facet code for a call that
reaches it. -/
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

/-- **Witness: an owner-side run from ZiSK off** (premises of `ZiskStaysOffWithoutAdmin`,
`BridgehubOwnerCannotReenable`, `ReenableIsAdmins`). Under the genuine `MultiProofVerifier`
everywhere, from `w3` (flagged, ZiSK off): the admin's genuine upgrade installs the verifier at
`11`, the Bridgehub owner `2` switches ZiSK off again, the owner becomes `5`, and `5` switches it
off again. The run is allowed by `OwnerSide` and ends with ZiSK off. On `w3` the owner's ZiSK-on
reverts and the admin's succeeds, giving `w1`. -/
def Properties.OwnerSideRunWitness : Prop :=
  ziskOff w3 ∧
  Reach multiProofEnv OwnerSide w3 { w3 with verifier := 11, bridgehubOwner := 5 } ∧
  ziskOff { w3 with verifier := 11, bridgehubOwner := 5 } ∧
  w3.bridgehubOwner ≠ w3.admin ∧
  step multiProofEnv w3.bridgehubOwner (.setProofSystemStatus .zisk true) w3 = none ∧
  step multiProofEnv w3.admin (.setProofSystemStatus .zisk true) w3 = some w1

/-! ## (e) The genuine verifier -/

/-- **The genuine verifier reports ZiSK honestly** (`MultiProofVerifier.sol:101-109`): it
reports multi-proof mode exactly for the zero mask. -/
def Properties.MultiProofVerifierReportsZisk : Prop :=
  (∀ v, ReportsZisk multiProofEnv v) ∧
  (∀ m, multiProofGetProofMode m = some MULTI_PROOF_TYPE ↔ m = 0)

/-! ## (f) Verifier answers that change between calls -/

/-- **Fixed verifier answers are a special case.** Every run of `Reach E (ok E)` is a run of
`ReachEnvs ok`, with `E` at every call. So each `…AnyVerifiers` statement below implies the
fixed-`Env` statement it is named after. -/
def Properties.ReachEnvsExtendsReach : Prop :=
  ∀ (E : Env) (ok : Env → St → Address → Call → Prop) (s s' : St),
    Reach E (ok E) s s' → ReachEnvs ok s s'

/-- **`FlagMonotone` and `NonZiskBitsFrozen`, with changing verifier answers.** Along every run
with no break-glass cut in which every call may see its own `getProofMode` answers
(`ReachEnvs`), a set flag stays set and the mask's bits other than ZiSK keep their values. -/
def Properties.FlagMonotoneAnyVerifiers : Prop :=
  ∀ s s' : St, ReachEnvs (fun _ => NoBreakGlass) s s' →
    (s.secondProofSystemRequired = true → s'.secondProofSystemRequired = true) ∧
    s'.disabledProofSystems &&& ~~~ziskBit = s.disabledProofSystems &&& ~~~ziskBit

/-- **`AdminCannotDropSecondProof`, with changing verifier answers.** Along every run with no
break-glass cut and no `setProofSystemStatus` by the Bridgehub owner of that moment, in which
every call may see its own `getProofMode` answers, a flagged diamond with ZiSK on stays flagged
with ZiSK on. -/
def Properties.AdminCannotDropSecondProofAnyVerifiers : Prop :=
  ∀ s s' : St, ReachEnvs (fun _ => AdminSide) s s' →
    s.secondProofSystemRequired = true → ziskOn s →
    s'.secondProofSystemRequired = true ∧ ziskOn s'

/-- **`AdminNeverReachesFlaggedZiskOff`, with changing verifier answers.** As that statement,
along runs in which every call may see its own `getProofMode` answers; the honesty premise is on
the answers each `permanentlyRequireSecondProofSystem` call sees. -/
def Properties.AdminNeverReachesFlaggedZiskOffAnyVerifiers : Prop :=
  ∀ s s' : St, ReachEnvs AdminSideHonest s s' → ¬ FlaggedZiskOff s → ¬ FlaggedZiskOff s'

/-- **`ZiskStaysOffWithoutAdmin`, with changing verifier answers.** Along every run with no
break-glass cut and no `setProofSystemStatus` by the chain admin of that moment, in which every
call may see its own `getProofMode` answers, ZiSK off stays off. -/
def Properties.ZiskStaysOffWithoutAdminAnyVerifiers : Prop :=
  ∀ s s' : St, ReachEnvs (fun _ => OwnerSide) s s' → ziskOff s → ziskOff s'

/-- **Witness: runs whose calls see different verifier answers** (premises of the four
statements above).

* `AdminSideHonest`, from `w0`, which is not flagged-with-ZiSK-off: the admin switches ZiSK off
  and back on with every verifier lying (`lyingEnv`), sets the flag under the genuine
  `MultiProofVerifier` (`multiProofEnv`), and upgrades to the verifier at `11` under
  `airbenderAt12Env`, ending at `w2`, flagged with ZiSK on.
* `AdminSide`, from `w1`: a genuine upgrade to `11` under `multiProofEnv`, then one to `12` under
  `lyingEnv`, whose verifier at `12` is not `ReportsZisk`; the end state is flagged with ZiSK on.
* `OwnerSide`, from `w3`: the same two upgrades, ending with ZiSK off.
* No break-glass cut, from `w6` (mask `1`): the Bridgehub owner's ZiSK-off under `lyingEnv`,
  then a genuine upgrade to `11` under `multiProofEnv`, ending at mask `5`. -/
def Properties.AnyVerifiersRunWitness : Prop :=
  ¬ FlaggedZiskOff w0 ∧ ReachEnvs AdminSideHonest w0 w2 ∧
  w2.secondProofSystemRequired = true ∧ ziskOn w2 ∧
  ReachEnvs (fun _ => AdminSide) w1 { w1 with verifier := 12 } ∧
  ¬ ReportsZisk lyingEnv 12 ∧
  ziskOn { w1 with verifier := 12 } ∧
  ReachEnvs (fun _ => OwnerSide) w3 { w3 with verifier := 12 } ∧
  ziskOff { w3 with verifier := 12 } ∧
  ReachEnvs (fun _ => NoBreakGlass) w6 { w6 with disabledProofSystems := 5, verifier := 11 }

end Contracts.SecondProofSystem.FlagAuthorityV35
