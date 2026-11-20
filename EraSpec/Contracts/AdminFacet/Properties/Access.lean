import EraSpec.Contracts.AdminFacet.Specs.AdminFacet
import EraSpec.Core.Headline

/-!
# Properties: who may call what, and who can change the chain's authorities

Statements about `EraSpec.Contracts.AdminFacet.Specs.AdminFacet`; proofs in
`EraSpec.Contracts.AdminFacet.Proofs.Access`.

* `EveryEntryChecksItsRole`: each of the 25 entries succeeds only for a caller in its `Role`.
* `CallerMattersOnlyThroughRole`: the caller enters a call only through that role check (and,
  for `upgradeChainFromVersion`, the notifier gate that admin and CTM skip).
* `ValidatorUpgradeWaitsForSchedule`: a validator's `upgradeChainFromVersion` needs the chain's
  `ServerNotifier` timestamp to be set and reached.
* `AdminHandoverIsTwoStep`: `setPendingAdmin` and `acceptAdmin`, exactly.
* `AdminChangesOnlyByAcceptance` (run): without cuts, a new admin has sent `acceptAdmin` and was
  either the pending admin at the start or named by a `setPendingAdmin`.
* `ValidatorsChangeOnlyByCTM` (run): without cuts, every changed validator bit was set by the
  CTM's `setValidator` with its final value.
* `FreezeOnlyByCTM` (run): without cuts, the freeze flag moves only by the CTM's
  `freezeDiamond`/`unfreezeDiamond`.
* `FreezeUnfreezeExact`: `freezeDiamond` succeeds iff the caller is the CTM and the diamond is
  unfrozen; `unfreezeDiamond` iff the caller is the CTM, the diamond is frozen and the selector of
  `unfreezeDiamond` is not itself freezable.
* `FreezableUnfreezeStrandsTheChain` (run): if `unfreezeDiamond` and the three cut entries are all
  marked freezable, a frozen diamond stays frozen forever.
* Witnesses: `EveryEntrySucceedsSomewhere`, `ValidatorUpgradeWitness`, `AdminHandoverWitness`,
  `ValidatorChangeWitness`, `FreezeWitness`, `StrandedChainWitness`.
-/

namespace Contracts.AdminFacet

/-- **EVERY ENTRY CHECKS ITS ROLE.** A successful call through the diamond, to any of the 25
state-changing functions, was sent by an address in that function's `Role`, evaluated in the
state before the call: the admin, the pending admin, the CTM, a validator, or (for disabling a
proof system on a chain that requires its second one) the Bridgehub owner. `activatePriorityMode`
has no caller check. -/
@[headline] def Properties.EveryEntryChecksItsRole : Prop :=
  ∀ (K : Config) (e : Env) (s s' : State) (c : Call),
    call K e s c = some s' → Role e s c.sender c.entry

/-- **THE CALLER ENTERS ONLY THROUGH ITS ROLE.** If a call succeeds, the same call from any other
address with the same role succeeds with the same result. For `upgradeChainFromVersion` the
replacement must be the admin or the CTM, which skip the notifier gate. (The model's cut
semantics `Config.runCut` does not see the caller; see the module docstring of the spec.) -/
def Properties.CallerMattersOnlyThroughRole : Prop :=
  ∀ (K : Config) (e : Env) (s s' : State) (c : Call) (b : Address),
    call K e s c = some s' → Role e s b c.entry →
    ((∀ ch v, c.entry ≠ .upgradeChainFromVersion ch v) ∨ b = s.admin ∨ b = s.chainTypeManager) →
    call K e s { c with sender := b } = some s'

/-- **A VALIDATOR'S UPGRADE WAITS FOR THE CHAIN'S SCHEDULE.** If `upgradeChainFromVersion(_, v)`
succeeds for a caller that is neither the admin nor the CTM, that caller is a validator and the
`ServerNotifier` timestamp for `(chainId, v)` is set and has been reached (`Admin.sol:577-585`). -/
@[headline] def Properties.ValidatorUpgradeWaitsForSchedule : Prop :=
  ∀ (K : Config) (e : Env) (s s' : State) (a : Address) (τ : ℕ) (ch : Address) (v : ℕ),
    call K e s ⟨a, τ, .upgradeChainFromVersion ch v⟩ = some s' →
    a ≠ s.admin → a ≠ s.chainTypeManager →
    s.validators a = true ∧ e.upgradeTimestamp s.chainTypeManager v ≠ 0 ∧
      e.upgradeTimestamp s.chainTypeManager v ≤ τ

/-- **THE ADMIN HANDOVER IS TWO-STEP, EXACTLY.** When the diamond does not block the selector:

* `setPendingAdmin(p)` succeeds iff the caller is the admin, and then writes only
  `pendingAdmin := p`;
* `acceptAdmin()` succeeds iff the caller is the pending admin, and then writes only
  `admin := pendingAdmin` and `pendingAdmin := 0`. -/
def Properties.AdminHandoverIsTwoStep : Prop :=
  ∀ (K : Config) (e : Env) (s : State) (a : Address) (τ : ℕ),
    ¬ (s.frozen = true ∧ s.freezable (Entry.setPendingAdmin 0).sel = true) →
    ¬ (s.frozen = true ∧ s.freezable Entry.acceptAdmin.sel = true) →
    (∀ p, call K e s ⟨a, τ, .setPendingAdmin p⟩ =
        if a = s.admin then some { s with pendingAdmin := p } else none)
    ∧ call K e s ⟨a, τ, .acceptAdmin⟩ =
        if a = s.pendingAdmin then some { s with admin := s.pendingAdmin, pendingAdmin := 0 }
        else none

/-- **WITHOUT CUTS, A NEW ADMIN WAS NOMINATED AND ACCEPTED.** Along any run of calls (any
senders except the zero address, any times), environment changes and foreign writes that runs no
cut: if the admin at the end differs from the admin at the start, then the final admin itself sent
`acceptAdmin` during the run, and it was either the pending admin at the start or the argument of
a `setPendingAdmin` in the run (which only the then-admin can send,
`EveryEntryChecksItsRole`). -/
@[headline] def Properties.AdminChangesOnlyByAcceptance : Prop :=
  ∀ (K : Config) (w w' : World) (ls : List Label),
    Run K w ls w' → (∀ l ∈ ls, l.runsCut = false) →
    (∀ c, Label.call c ∈ ls → c.sender ≠ 0) →
    w'.st.admin ≠ w.st.admin →
    (∃ τ, Label.call ⟨w'.st.admin, τ, .acceptAdmin⟩ ∈ ls) ∧
    (w'.st.admin = w.st.pendingAdmin ∨
      ∃ a τ, Label.call ⟨a, τ, .setPendingAdmin w'.st.admin⟩ ∈ ls)

/-- **WITHOUT CUTS, ONLY THE CTM CHANGES VALIDATORS.** Along any run that runs no cut, the CTM
address stays fixed, and every validator bit that differs at the end was written to its final
value by a `setValidator` call from that CTM in the run. -/
@[headline] def Properties.ValidatorsChangeOnlyByCTM : Prop :=
  ∀ (K : Config) (w w' : World) (ls : List Label),
    Run K w ls w' → (∀ l ∈ ls, l.runsCut = false) →
    w'.st.chainTypeManager = w.st.chainTypeManager ∧
    ∀ x, w'.st.validators x ≠ w.st.validators x →
      ∃ τ, Label.call ⟨w.st.chainTypeManager, τ, .setValidator x (w'.st.validators x)⟩ ∈ ls

/-- **WITHOUT CUTS, ONLY THE CTM FREEZES AND UNFREEZES.** Along any run that runs no cut: if the
diamond ends frozen having started unfrozen, the CTM sent `freezeDiamond` in the run; if it ends
unfrozen having started frozen, the CTM sent `unfreezeDiamond`. -/
def Properties.FreezeOnlyByCTM : Prop :=
  ∀ (K : Config) (w w' : World) (ls : List Label),
    Run K w ls w' → (∀ l ∈ ls, l.runsCut = false) →
    (w.st.frozen = false → w'.st.frozen = true →
      ∃ τ, Label.call ⟨w.st.chainTypeManager, τ, .freezeDiamond⟩ ∈ ls) ∧
    (w.st.frozen = true → w'.st.frozen = false →
      ∃ τ, Label.call ⟨w.st.chainTypeManager, τ, .unfreezeDiamond⟩ ∈ ls)

/-- **FREEZE AND UNFREEZE, EXACTLY.** Through the diamond, for any caller `a` at any time:

* `freezeDiamond()` succeeds iff `a` is the CTM and the diamond is not frozen, and then writes
  only `frozen := true` (the proxy's freeze check cannot fire on an unfrozen diamond);
* `unfreezeDiamond()` succeeds iff `a` is the CTM, the diamond is frozen **and the selector of
  `unfreezeDiamond` is not marked freezable**, and then writes only `frozen := false`. -/
@[headline] def Properties.FreezeUnfreezeExact : Prop :=
  ∀ (K : Config) (e : Env) (s : State) (a : Address) (τ : ℕ),
    call K e s ⟨a, τ, .freezeDiamond⟩ =
        (if a = s.chainTypeManager ∧ s.frozen = false then some { s with frozen := true }
         else none)
    ∧ call K e s ⟨a, τ, .unfreezeDiamond⟩ =
        (if a = s.chainTypeManager ∧ s.frozen = true ∧
            s.freezable Entry.unfreezeDiamond.sel = false then
          some { s with frozen := false }
         else none)

/-- **A FREEZABLE UNFREEZE STRANDS THE CHAIN.** If the diamond is frozen and the selectors of
`unfreezeDiamond`, `upgradeChainFromVersion`, `executeUpgrade` and `genesisUpgrade` are all marked
freezable, then every run — any calls, environment changes and foreign writes, cuts included —
ends frozen. (`FreezeUnfreezeExact` gives the one-call form: on a frozen diamond `unfreezeDiamond`
succeeds only if its selector is not freezable. The CTM deployment scripts register the Admin
facet non-freezable: `l1-contracts/deploy-scripts/ctm/DeployCTMUtils.s.sol:103`,
`l1-contracts/deploy-scripts/gateway/GatewayCTMDeployerHelper.sol:358`.) -/
def Properties.FreezableUnfreezeStrandsTheChain : Prop :=
  ∀ (K : Config) (w w' : World) (ls : List Label),
    Run K w ls w' → w.st.frozen = true →
    w.st.freezable Entry.unfreezeDiamond.sel = true →
    w.st.freezable (Entry.upgradeChainFromVersion 0 0).sel = true →
    w.st.freezable (Entry.executeUpgrade ⟨[], 0, 0⟩).sel = true →
    w.st.freezable Entry.genesisUpgrade.sel = true →
    w'.st.frozen = true

/-! ## Witnesses -/

/-- **WITNESS: EVERY ENTRY CAN SUCCEED.** For each of the 25 entries, identified by its selector,
there are arguments, a deployment, an environment, a state, a caller and a time at which the call
through the diamond succeeds. So no entry of the model reverts unconditionally, and
`EveryEntryChecksItsRole` constrains a satisfiable success of every entry. -/
@[witness] def Properties.EveryEntrySucceedsSomewhere : Prop :=
  ∀ en : Entry, ∃ (en' : Entry) (K : Config) (e : Env) (s s' : State) (a : Address) (τ : ℕ),
    en'.sel = en.sel ∧ call K e s ⟨a, τ, en'⟩ = some s'

/-- **WITNESS: A VALIDATOR'S SCHEDULED UPGRADE, AND THE SAME CALL FROM THE ADMIN.** A call to
`upgradeChainFromVersion` from an address that is neither the admin nor the CTM succeeds and raises
the version (the premises of `ValidatorUpgradeWaitsForSchedule`), and the admin, a different
address with the role, makes the same call with the same result (the premises and conclusion of
`CallerMattersOnlyThroughRole` with a replacement caller). -/
@[witness] def Properties.ValidatorUpgradeWitness : Prop :=
  ∃ (K : Config) (e : Env) (s s' : State) (a : Address) (τ : ℕ) (ch : Address) (v : ℕ),
    call K e s ⟨a, τ, .upgradeChainFromVersion ch v⟩ = some s' ∧
    a ≠ s.admin ∧ a ≠ s.chainTypeManager ∧ s.protocolVersion < s'.protocolVersion ∧
    Role e s s.admin (.upgradeChainFromVersion ch v) ∧
    call K e s ⟨s.admin, τ, .upgradeChainFromVersion ch v⟩ = some s'

/-- **WITNESS: AN ADMIN HANDOVER ON A FROZEN DIAMOND.** On a frozen diamond whose `setPendingAdmin`
and `acceptAdmin` selectors are not freezable (the premises of `AdminHandoverIsTwoStep`, with the
diamond frozen), a run without cuts and with nonzero senders, starting from admin `1`, ends with
admin `2` and no pending admin (the premises of `AdminChangesOnlyByAcceptance`, with the admin
changed). -/
@[witness] def Properties.AdminHandoverWitness : Prop :=
  ∃ (K : Config) (w w' : World) (ls : List Label),
    Run K w ls w' ∧ (∀ l ∈ ls, l.runsCut = false) ∧ (∀ c, Label.call c ∈ ls → c.sender ≠ 0) ∧
    w.st.frozen = true ∧
    w.st.freezable (Entry.setPendingAdmin 0).sel = false ∧
    w.st.freezable Entry.acceptAdmin.sel = false ∧
    w.st.admin = 1 ∧ w'.st.admin = 2 ∧ w'.st.pendingAdmin = 0

/-- **WITNESS: A VALIDATOR IS ADDED.** A run without cuts, containing an environment change and a
foreign write, in which some validator bit goes from off to on (the premises of
`ValidatorsChangeOnlyByCTM`, with a bit changed). -/
@[witness] def Properties.ValidatorChangeWitness : Prop :=
  ∃ (K : Config) (w w' : World) (ls : List Label) (x : Address),
    Run K w ls w' ∧ (∀ l ∈ ls, l.runsCut = false) ∧
    (∃ e, Label.env e ∈ ls) ∧ (∃ s', Label.foreign s' ∈ ls) ∧
    w.st.validators x = false ∧ w'.st.validators x = true

/-- **WITNESS: FREEZE, THEN UNFREEZE.** Two consecutive runs without cuts: in the first the
diamond goes from unfrozen to frozen; the second, of at least two steps, takes it back to
unfrozen. Together they meet the antecedents of both halves of `FreezeOnlyByCTM`. -/
@[witness] def Properties.FreezeWitness : Prop :=
  ∃ (K : Config) (w w₁ w₂ : World) (ls₁ ls₂ : List Label),
    Run K w ls₁ w₁ ∧ Run K w₁ ls₂ w₂ ∧
    (∀ l ∈ ls₁ ++ ls₂, l.runsCut = false) ∧ 2 ≤ ls₂.length ∧
    w.st.frozen = false ∧ w₁.st.frozen = true ∧ w₂.st.frozen = false

/-- **WITNESS: A STRANDED CHAIN.** A frozen diamond with the selectors of `unfreezeDiamond` and
the three cut entries all marked freezable (the premises of `FreezableUnfreezeStrandsTheChain`)
on which a run with an environment change and a foreign write changing
`pausedDepositsTimestamp` takes place. -/
@[witness] def Properties.StrandedChainWitness : Prop :=
  ∃ (K : Config) (w w' : World) (ls : List Label),
    Run K w ls w' ∧ w.st.frozen = true ∧
    w.st.freezable Entry.unfreezeDiamond.sel = true ∧
    w.st.freezable (Entry.upgradeChainFromVersion 0 0).sel = true ∧
    w.st.freezable (Entry.executeUpgrade ⟨[], 0, 0⟩).sel = true ∧
    w.st.freezable Entry.genesisUpgrade.sel = true ∧
    (∃ e, Label.env e ∈ ls) ∧ (∃ s', Label.foreign s' ∈ ls) ∧
    w'.st.pausedDepositsTimestamp ≠ w.st.pausedDepositsTimestamp

end Contracts.AdminFacet
