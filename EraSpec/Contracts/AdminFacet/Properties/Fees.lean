import EraSpec.Contracts.AdminFacet.Specs.AdminFacet
import EraSpec.Core.Headline

/-!
# Properties: fee inputs (pricing mode, fee parameters, token multiplier)

Statements about `EraSpec.Contracts.AdminFacet.Specs.AdminFacet`; proofs in
`EraSpec.Contracts.AdminFacet.Proofs.Fees`. The fields of the fee parameters that priority mode
fixes are in `OneWayFlagsAlongRuns` (`Properties/PriorityMode.lean`).

* `SetPubdataPricingModeExact`: `setPubdataPricingMode`, exactly.
* `FeeUpdatesAtLeastADayApart` (run): without cuts, after a successful `changeFeeParams` or
  `setTokenMultiplier` at a nonzero time, every later one in the run is at least
  `PRICE_UPDATE_INTERVAL` (one day) later.
* `StageOneFeeUpdateWithinPriceBound`: on a chain with priority mode allowed, a successful
  `changeFeeParams` or `setTokenMultiplier` moves the derived L2 gas price by at most the ratio
  13/10 either way (rounded down), unless that price was zero with no unprocessed priority
  transaction.
* `StageOneFeeInputsMoveOnlyByFeeUpdates` (run): without cuts, on a chain with priority mode
  allowed, a run with no `changeFeeParams` or `setTokenMultiplier` leaves the fee parameters, the
  multiplier and so the derived price unchanged. With the two results above, on such a chain the
  price moves only by fee updates, each within the bound (or under its exemption) and at least a
  day after any earlier one made at a nonzero time.
* Witnesses: `PricingModeChangeWitness`, `FeeUpdatesWitness`, `StageOneFeeUpdateWitness`,
  `StageOneFeeInputsWitness`.
* Countermodels: `FeeUpdateAtTimeZeroNotSpaced` (the nonzero-time premise is needed),
  `PriceBoundNeedsPriorityModeAllowed`, `PricingModeMovesPriceWithoutPriorityMode` (the
  allowed-priority-mode premises are needed).
-/

namespace Contracts.AdminFacet

/-- **`setPubdataPricingMode`, EXACTLY.** When the diamond does not block its selector, the call
succeeds iff the caller is the admin, the chain is on L1 and priority mode is not allowed
(`Admin.sol:359-365`); it then writes only the pricing mode. -/
def Properties.SetPubdataPricingModeExact : Prop :=
  ∀ (K : Config) (e : Env) (s : State) (a : Address) (τ m : ℕ),
    ¬ (s.frozen = true ∧ s.freezable (Entry.setPubdataPricingMode 0).sel = true) →
    call K e s ⟨a, τ, .setPubdataPricingMode m⟩ =
      if a = s.admin ∧ K.onL1 = true ∧ s.priorityMode.canBeActivated = false then
        some { s with feeParams := { s.feeParams with pricingMode := m } }
      else none

/-- **FEE UPDATES ARE AT LEAST A DAY APART.** Let a `changeFeeParams` or `setTokenMultiplier`
call at time `τ₁ ≠ 0` succeed, and continue with any run that runs no cut (calls by anyone,
environment changes, foreign writes). Every `changeFeeParams` or `setTokenMultiplier` call in that
run has time at least `τ₁ + PRICE_UPDATE_INTERVAL` (`_enforceMinUpdateInterval`,
`Admin.sol:298-307`, reading both update stamps). -/
@[headline] def Properties.FeeUpdatesAtLeastADayApart : Prop :=
  ∀ (K : Config) (w w' : World) (c : Call) (ls : List Label),
    c.entry.isFeeUpdate = true → c.time ≠ 0 →
    Run K w (.call c :: ls) w' → (∀ l ∈ ls, l.runsCut = false) →
    ∀ d, Label.call d ∈ ls → d.entry.isFeeUpdate = true →
      c.time + PRICE_UPDATE_INTERVAL ≤ d.time

/-- **ON A CHAIN WITH PRIORITY MODE ALLOWED, A FEE UPDATE MOVES THE PRICE BY AT MOST 13/10.** If
priority mode is allowed and a `changeFeeParams` or `setTokenMultiplier` call succeeds, write `p`
and `p'` for the derived L2 gas price (`State.derivedGasPrice`: `_safeDerivedL2GasPrice` of the
fee parameters and the base-token multiplier at the reference L1 gas price, `Admin.sol:339-356`)
before and after the call. Then either `p = 0` and no priority transaction is unprocessed (the
early return, `Admin.sol:320-322`), or `p * 10 / 13 ≤ p' ≤ p * 13 / 10` in integer division
(`Admin.sol:328-336`). -/
@[headline] def Properties.StageOneFeeUpdateWithinPriceBound : Prop :=
  ∀ (K : Config) (e : Env) (s s' : State) (c : Call),
    call K e s c = some s' → c.entry.isFeeUpdate = true →
    s.priorityMode.canBeActivated = true →
    (s.derivedGasPrice = 0 ∧ s.priorityTreeSize = 0) ∨
    (s'.derivedGasPrice ≤ s.derivedGasPrice * MAX_PRICE_CHANGE_NUMERATOR /
        MAX_PRICE_CHANGE_DENOMINATOR ∧
     s.derivedGasPrice * MAX_PRICE_CHANGE_DENOMINATOR / MAX_PRICE_CHANGE_NUMERATOR ≤
        s'.derivedGasPrice)

/-- **ON A CHAIN WITH PRIORITY MODE ALLOWED, ONLY FEE UPDATES MOVE THE FEE INPUTS.** Along any run
without cuts from a state with priority mode allowed, in which no call is a `changeFeeParams` or
a `setTokenMultiplier`, the fee parameters, the base-token multiplier and the derived L2 gas price
(`State.derivedGasPrice`) at the end equal those at the start. (The other writer of the fee
parameters, `setPubdataPricingMode`, reverts once priority mode is allowed, `Admin.sol:360-362`.)
-/
def Properties.StageOneFeeInputsMoveOnlyByFeeUpdates : Prop :=
  ∀ (K : Config) (w w' : World) (ls : List Label),
    Run K w ls w' → (∀ l ∈ ls, l.runsCut = false) →
    w.st.priorityMode.canBeActivated = true →
    (∀ c, Label.call c ∈ ls → c.entry.isFeeUpdate = false) →
    w'.st.feeParams = w.st.feeParams ∧ w'.st.multNominator = w.st.multNominator ∧
      w'.st.multDenominator = w.st.multDenominator ∧
      w'.st.derivedGasPrice = w.st.derivedGasPrice

/-! ## Witnesses -/

/-- **WITNESS: THE ADMIN CHANGES THE PRICING MODE ON A FROZEN DIAMOND.** On a frozen diamond whose
`setPubdataPricingMode` selector is not freezable (the premise of `SetPubdataPricingModeExact`,
with the diamond frozen), the admin's `setPubdataPricingMode` succeeds and changes the pricing
mode. -/
@[witness] def Properties.PricingModeChangeWitness : Prop :=
  ∃ (K : Config) (e : Env) (s s' : State) (τ m : ℕ),
    s.frozen = true ∧ s.freezable (Entry.setPubdataPricingMode 0).sel = false ∧
    call K e s ⟨s.admin, τ, .setPubdataPricingMode m⟩ = some s' ∧
    s'.feeParams.pricingMode ≠ s.feeParams.pricingMode

/-- **WITNESS: TWO FEE UPDATES A DAY APART.** A successful fee update at a nonzero time is
followed by a run without cuts, containing an environment change and a foreign write, that
contains a further fee update exactly `PRICE_UPDATE_INTERVAL` after the first (the premises of
`FeeUpdatesAtLeastADayApart`, with its conclusion met with equality). -/
@[witness] def Properties.FeeUpdatesWitness : Prop :=
  ∃ (K : Config) (w w' : World) (c d : Call) (ls : List Label),
    c.entry.isFeeUpdate = true ∧ c.time ≠ 0 ∧
    Run K w (.call c :: ls) w' ∧ (∀ l ∈ ls, l.runsCut = false) ∧
    (∃ e, Label.env e ∈ ls) ∧ (∃ s', Label.foreign s' ∈ ls) ∧
    Label.call d ∈ ls ∧ d.entry.isFeeUpdate = true ∧
    d.time = c.time + PRICE_UPDATE_INTERVAL

/-- **WITNESS: A BOUNDED FEE UPDATE ON A CHAIN WITH PRIORITY MODE ALLOWED.** With priority mode
allowed and a nonzero derived price, a `changeFeeParams` and a `setTokenMultiplier` from the same
state both succeed and both change the derived price (the premises of
`StageOneFeeUpdateWithinPriceBound` for each of the two entries; the price being nonzero, the
first disjunct of its conclusion is false). -/
@[witness] def Properties.StageOneFeeUpdateWitness : Prop :=
  ∃ (K : Config) (e : Env) (s s₁ s₂ : State) (a : Address) (τ : ℕ) (fp : FeeParams) (n d : ℕ),
    s.priorityMode.canBeActivated = true ∧ s.derivedGasPrice ≠ 0 ∧
    call K e s ⟨a, τ, .changeFeeParams fp⟩ = some s₁ ∧
    s₁.derivedGasPrice ≠ s.derivedGasPrice ∧
    call K e s ⟨a, τ, .setTokenMultiplier n d⟩ = some s₂ ∧
    s₂.derivedGasPrice ≠ s.derivedGasPrice

/-- **WITNESS: A STAGE-1 RUN WITHOUT FEE UPDATES.** From a state with priority mode allowed and a
nonzero derived price, a run without cuts and without fee updates, containing a call, an
environment change and a foreign write, ends with a different number of unprocessed priority
transactions (the premises of `StageOneFeeInputsMoveOnlyByFeeUpdates`). -/
@[witness] def Properties.StageOneFeeInputsWitness : Prop :=
  ∃ (K : Config) (w w' : World) (ls : List Label),
    Run K w ls w' ∧ (∀ l ∈ ls, l.runsCut = false) ∧
    w.st.priorityMode.canBeActivated = true ∧ w.st.derivedGasPrice ≠ 0 ∧
    (∀ c, Label.call c ∈ ls → c.entry.isFeeUpdate = false) ∧
    (∃ c, Label.call c ∈ ls) ∧ (∃ e, Label.env e ∈ ls) ∧ (∃ s', Label.foreign s' ∈ ls) ∧
    w'.st.priorityTreeSize ≠ w.st.priorityTreeSize

/-! ## Countermodels -/

/-- **COUNTERMODEL: AN UPDATE AT TIME ZERO STAMPS NOTHING.** `_enforceMinUpdateInterval` treats a
zero stamp as "never updated" (`Admin.sol:304`), so after a fee update at `block.timestamp = 0` a
second one succeeds at once. The premise `c.time ≠ 0` of `FeeUpdatesAtLeastADayApart` is needed. -/
@[countermodel] def Properties.FeeUpdateAtTimeZeroNotSpaced : Prop :=
  ∃ (K : Config) (w w' : World) (c d : Call),
    c.entry.isFeeUpdate = true ∧ d.entry.isFeeUpdate = true ∧ c.time = 0 ∧
    Run K w [.call c, .call d] w' ∧ d.time < c.time + PRICE_UPDATE_INTERVAL

/-- **COUNTERMODEL: WITHOUT PRIORITY MODE ALLOWED, THE PRICE IS UNBOUNDED.** The bound is enforced
only when priority mode is allowed (`Admin.sol:236, 276`). On a chain where it is not, with a
nonzero derived price and an unprocessed priority transaction, the admin's `changeFeeParams`
succeeds and raises the derived price above `p * 13 / 10`. So the allowed-priority-mode premise of
`StageOneFeeUpdateWithinPriceBound` is needed. -/
@[countermodel] def Properties.PriceBoundNeedsPriorityModeAllowed : Prop :=
  ∃ (K : Config) (e : Env) (s s' : State) (τ : ℕ) (fp : FeeParams),
    s.priorityMode.canBeActivated = false ∧ s.derivedGasPrice ≠ 0 ∧ s.priorityTreeSize ≠ 0 ∧
    call K e s ⟨s.admin, τ, .changeFeeParams fp⟩ = some s' ∧
    s.derivedGasPrice * MAX_PRICE_CHANGE_NUMERATOR / MAX_PRICE_CHANGE_DENOMINATOR <
      s'.derivedGasPrice

/-- **COUNTERMODEL: WITHOUT PRIORITY MODE ALLOWED, THE PRICING MODE MOVES THE PRICE.** On a chain
where priority mode is not allowed, a run without cuts and without fee updates, containing the
admin's `setPubdataPricingMode`, changes the derived L2 gas price. So the allowed-priority-mode
premise of `StageOneFeeInputsMoveOnlyByFeeUpdates` is needed. -/
@[countermodel] def Properties.PricingModeMovesPriceWithoutPriorityMode : Prop :=
  ∃ (K : Config) (w w' : World) (ls : List Label),
    Run K w ls w' ∧ (∀ l ∈ ls, l.runsCut = false) ∧
    w.st.priorityMode.canBeActivated = false ∧
    (∀ c, Label.call c ∈ ls → c.entry.isFeeUpdate = false) ∧
    (∃ τ m, Label.call ⟨w.st.admin, τ, .setPubdataPricingMode m⟩ ∈ ls) ∧
    w'.st.derivedGasPrice ≠ w.st.derivedGasPrice

end Contracts.AdminFacet
