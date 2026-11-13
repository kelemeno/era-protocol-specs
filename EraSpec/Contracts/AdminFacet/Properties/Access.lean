import EraSpec.Contracts.AdminFacet.Specs.AdminFacet

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
* `FreezableUnfreezeStrandsTheChain` (run): if `unfreezeDiamond` and the three cut entries are all
  marked freezable, a frozen diamond stays frozen forever. That the facet is registered
  non-freezable is load-bearing.
* `AdminHandoverWitness`: a concrete run hands the admin role over.
-/

namespace Contracts.AdminFacet

/-- **EVERY ENTRY CHECKS ITS ROLE.** A successful call through the diamond, to any of the 25
state-changing functions, was sent by an address in that function's `Role`, evaluated in the
state before the call: the admin, the pending admin, the CTM, a validator, or (for disabling a
proof system on a chain that requires its second one) the Bridgehub owner. `activatePriorityMode`
has no caller check. -/
def Properties.EveryEntryChecksItsRole : Prop :=
  ∀ (K : Config) (e : Env) (s s' : State) (c : Call),
    call K e s c = some s' → Role e s c.sender c.entry

/-- **THE CALLER ENTERS ONLY THROUGH ITS ROLE.** If a call succeeds, the same call from any other
address with the same role succeeds with the same result. For `upgradeChainFromVersion` the
replacement must be the admin or the CTM, which skip the notifier gate. -/
def Properties.CallerMattersOnlyThroughRole : Prop :=
  ∀ (K : Config) (e : Env) (s s' : State) (c : Call) (b : Address),
    call K e s c = some s' → Role e s b c.entry →
    ((∀ ch v, c.entry ≠ .upgradeChainFromVersion ch v) ∨ b = s.admin ∨ b = s.chainTypeManager) →
    call K e s { c with sender := b } = some s'

/-- **A VALIDATOR'S UPGRADE WAITS FOR THE CHAIN'S SCHEDULE.** If `upgradeChainFromVersion(_, v)`
succeeds for a caller that is neither the admin nor the CTM, that caller is a validator and the
`ServerNotifier` timestamp for `(chainId, v)` is set and has been reached (`Admin.sol:577-585`). -/
def Properties.ValidatorUpgradeWaitsForSchedule : Prop :=
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
def Properties.AdminChangesOnlyByAcceptance : Prop :=
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
def Properties.ValidatorsChangeOnlyByCTM : Prop :=
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

/-- **A FREEZABLE UNFREEZE STRANDS THE CHAIN.** If the diamond is frozen and the selectors of
`unfreezeDiamond`, `upgradeChainFromVersion`, `executeUpgrade` and `genesisUpgrade` are all marked
freezable, then every run — any calls, environment changes and foreign writes — ends frozen. So the
deployment's choice to register the admin facet non-freezable is load-bearing for
`unfreezeDiamond` to be reachable at all. -/
def Properties.FreezableUnfreezeStrandsTheChain : Prop :=
  ∀ (K : Config) (w w' : World) (ls : List Label),
    Run K w ls w' → w.st.frozen = true →
    w.st.freezable Entry.unfreezeDiamond.sel = true →
    w.st.freezable (Entry.upgradeChainFromVersion 0 0).sel = true →
    w.st.freezable (Entry.executeUpgrade ⟨[], 0, 0⟩).sel = true →
    w.st.freezable Entry.genesisUpgrade.sel = true →
    w'.st.frozen = true

/-- **WITNESS: AN ADMIN HANDOVER.** A run from a state with admin `1` in which the admin nominates
`2` and `2` accepts ends with admin `2` and no pending admin. -/
def Properties.AdminHandoverWitness : Prop :=
  ∃ (K : Config) (w w' : World) (ls : List Label),
    Run K w ls w' ∧ w.st.admin = 1 ∧ w'.st.admin = 2 ∧ w'.st.pendingAdmin = 0 ∧
    (∀ l ∈ ls, l.runsCut = false)

end Contracts.AdminFacet
