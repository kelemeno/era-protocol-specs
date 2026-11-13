import EraSpec.Contracts.L2BaseToken.Specs.Supply

/-!
# Properties: base-token supply on ZKsync OS

Statements about `EraSpec.Contracts.L2BaseToken.Specs.Supply`. Proofs are in
`EraSpec.Contracts.L2BaseToken.Proofs.Supply`. Every run-level statement quantifies over all
tracker implementations, every `Genesis` start and every interleaving of successful calls of
every modelled entry point (`Run`).

* `SupplyOnlyMintedByInitL2` (headline): native supply changes only by the one `initL2` mint of
  exactly `2^127 - 1`; `initL2` succeeds at most once.
* `InitL2OnlyByUpgraderOnce`: every successful `initL2` was sent by the complex upgrader;
  `L1_CHAIN_ID` is the argument of that one call; `zkosPreV31TotalSupply` never changes.
* `HolderAndCirculatingLedger` (headline): exact ledgers of the holder's reserve and of the
  circulating supply in terms of the six movement totals.
* `TrackerSeesEveryBridgeMovement`: the tracker's state is the replay of exactly the holder's
  bridge movements (`give` with non-zero amount, `burnAndStartBridging`), with matching totals.
* `CirculatingRisesOnlyByInboundPaths`, `CirculatingFallsOnlyByOutboundPaths`: per call over all
  entry points, who can move the circulating supply, by how much, and which tracker check passed.
* `TotalSupplyIsCirculating`, `TotalSupplyErrorIsConstant`: after `initL2`, `totalSupply()`
  returns exactly the circulating supply when `zkosPreV31TotalSupply` was backfilled correctly,
  and is off by a constant otherwise.
* `TotalSupplyOverstatedBeforeInitL2` (**source NatSpec refuted**): before `initL2`,
  `totalSupply()` returns the circulating supply plus `2^127 - 1`.
* `NoBalanceOverflows` (source NatSpec confirmed): no balance, and not the sum, reaches `2^256`.
* Countermodels: `InitL2FlagIsLoadBearing`, `GiveGuardIsLoadBearing`.
* Witness: `SupplyWitness`.
-/

namespace Contracts.L2BaseToken

/-- **HEADLINE: NATIVE SUPPLY IS MINTED ONLY BY THE ONE `initL2`.** Along any run from a
`Genesis` state, the sum of all native balances equals the starting sum plus what the mint hook
created; the hook created exactly `INITIAL = 2^127 - 1` if `initL2` has succeeded and nothing
otherwise; and the run contains exactly one successful `initL2` if the flag is set, none
otherwise. No other entry point, transfer, forced send or VM release changes the sum. -/
def Properties.SupplyOnlyMintedByInitL2 : Prop :=
  ∀ (T : Type) (tr : Tracker T) (s₀ s : State T) (cs : List Call),
    Genesis s₀ → Run tr s₀ cs s →
      supply s = supply s₀ + s.minted
      ∧ s.minted = (if s.initialized then INITIAL else 0)
      ∧ cs.countP Call.isInitL2 = (if s.initialized then 1 else 0)

/-- **`initL2` IS THE UPGRADER'S, ONCE.** Along any run from `Genesis`: every successful `initL2`
in the run was sent by `L2_COMPLEX_UPGRADER_ADDR`; once the flag is set, `L1_CHAIN_ID` is the
argument of an upgrader `initL2` in the run (by the headline, the only one); and
`zkosPreV31TotalSupply` is never written. -/
def Properties.InitL2OnlyByUpgraderOnce : Prop :=
  ∀ (T : Type) (tr : Tracker T) (s₀ s : State T) (cs : List Call),
    Genesis s₀ → Run tr s₀ cs s →
      (∀ caller l1, Call.initL2 caller l1 ∈ cs → caller = complexUpgraderAddr)
      ∧ (s.initialized = true → ∃ l1, Call.initL2 complexUpgraderAddr l1 ∈ cs ∧ s.l1ChainId = l1)
      ∧ s.preV31 = s₀.preV31

/-- **HEADLINE: THE HOLDER AND CIRCULATING LEDGERS.** Along any run from `Genesis`:

* the holder's balance plus everything paid out of it (`give`, `recoverBaseToken`, VM releases)
  equals its starting balance plus the mint, the `burnAndStartBridging` inflows and forced
  inflows;
* the circulating supply (all balances but the holder's) plus the bridged-out and forced amounts
  equals its starting value plus the given, recovered and released amounts.

So circulating supply moves only through the holder, and only by these six named flows. -/
def Properties.HolderAndCirculatingLedger : Prop :=
  ∀ (T : Type) (tr : Tracker T) (s₀ s : State T) (cs : List Call),
    Genesis s₀ → Run tr s₀ cs s →
      s.bal holderAddr + s.given + s.recovered + s.released
          = s₀.bal holderAddr + s.minted + s.burnt + s.forced
      ∧ circulating s + s.burnt + s.forced
          = circulating s₀ + s.given + s.recovered + s.released

/-- **THE TRACKER SEES EVERY BRIDGE MOVEMENT OF THE HOLDER.** Along any run from `Genesis`, the
holder's tracker calls are exactly one `finalize(fromChain, amount)` per successful non-zero
`give` and one `initiate(toChain, value)` per successful `burnAndStartBridging`, in run order; the
tracker's state is the replay of those calls from its starting state; and the reported totals
equal the amounts given out and burnt. -/
def Properties.TrackerSeesEveryBridgeMovement : Prop :=
  ∀ (T : Type) (tr : Tracker T) (s₀ s : State T) (cs : List Call),
    Genesis s₀ → Run tr s₀ cs s →
      s.calls = cs.filterMap Call.trackerCall
      ∧ replay tr s₀.trk s.calls = some s.trk
      ∧ finalizedTotal s.calls = s.given
      ∧ initiatedTotal s.calls = s.burnt

/-- **CIRCULATING SUPPLY RISES ONLY THROUGH THE INBOUND PATHS.** For any state and any call of
any modelled entry point: if the circulating supply rises, the call is `give` sent by the
InteropHandler whose tracker `finalize` succeeded, `recoverBaseToken` sent by the
NativeTokenVault whose tracker neutrality check passed, or a VM release; and it rose by exactly
the call's amount. -/
def Properties.CirculatingRisesOnlyByInboundPaths : Prop :=
  ∀ (T : Type) (tr : Tracker T) (s s' : State T) (c : Call),
    exec tr s c = some s' → circulating s < circulating s' →
      (∃ dst amt ch, c = .give interopHandlerAddr dst amt ch ∧ tr.finalize s.trk ch amt ≠ none
          ∧ circulating s' = circulating s + amt)
      ∨ (∃ dst amt ch, c = .recover ntvAddr dst amt ch ∧ tr.recoveryNeutral s.trk ch = true
          ∧ circulating s' = circulating s + amt)
      ∨ (∃ dst amt, c = .vmRelease dst amt ∧ circulating s' = circulating s + amt)

/-- **CIRCULATING SUPPLY FALLS ONLY THROUGH THE OUTBOUND PATHS.** For any state and any call: if
the circulating supply falls, the call is `burnAndStartBridging` sent by the InteropCenter or the
NativeTokenVault whose tracker `initiate` succeeded, or a forced send into the holder; and it fell
by exactly the value moved. -/
def Properties.CirculatingFallsOnlyByOutboundPaths : Prop :=
  ∀ (T : Type) (tr : Tracker T) (s s' : State T) (c : Call),
    exec tr s c = some s' → circulating s' < circulating s →
      (∃ caller v ch, c = .burn caller v ch ∧ (caller = interopCenterAddr ∨ caller = ntvAddr)
          ∧ tr.initiate s.trk ch v ≠ none ∧ circulating s' + v = circulating s)
      ∨ (∃ src amt, c = .forceToHolder src amt ∧ circulating s' + amt = circulating s)

/-- **AFTER `initL2`, `totalSupply()` IS THE CIRCULATING SUPPLY.** Along any run from `Genesis`
where `zkosPreV31TotalSupply` equals the starting native supply (a correct backfill) and that
supply is below `2^256 - INITIAL`: once the flag is set, `totalSupply()` does not revert and
returns exactly the sum of all balances other than the holder's. -/
def Properties.TotalSupplyIsCirculating : Prop :=
  ∀ (T : Type) (tr : Tracker T) (s₀ s : State T) (cs : List Call),
    Genesis s₀ → Run tr s₀ cs s → s₀.preV31 = supply s₀ → supply s₀ + INITIAL < 2 ^ 256 →
      s.initialized = true → totalSupplyView s = some (circulating s)

/-- **…AND WITHOUT THE BACKFILL PREMISE, OFF BY A CONSTANT.** Along any run from `Genesis`, once
the flag is set, the unchecked value of `totalSupply()`'s expression, as an integer, is the
circulating supply plus `zkosPreV31TotalSupply − (starting native supply)`: the error is fixed at
`initL2` and no later call changes it. -/
def Properties.TotalSupplyErrorIsConstant : Prop :=
  ∀ (T : Type) (tr : Tracker T) (s₀ s : State T) (cs : List Call),
    Genesis s₀ → Run tr s₀ cs s → s.initialized = true →
      (s.preV31 : ℤ) + INITIAL - s.bal holderAddr
        = (circulating s : ℤ) + ((s₀.preV31 : ℤ) - supply s₀)

/-- **SOURCE NATSPEC REFUTED: `totalSupply()` OVERSTATES BY `2^127 - 1` BEFORE `initL2`.**
`IL2BaseToken.totalSupply` is documented as "the total circulating supply of base tokens"
(`IL2BaseToken.sol:12`). Along any run from `Genesis` with a correct backfill and no overflow,
while the flag is clear, `totalSupply()` returns the circulating supply plus `INITIAL`. The
genesis state itself is such a state. (Internal finding; the window is the part of the V31
upgrade / genesis before `initL2` runs.) -/
def Properties.TotalSupplyOverstatedBeforeInitL2 : Prop :=
  ∀ (T : Type) (tr : Tracker T) (s₀ s : State T) (cs : List Call),
    Genesis s₀ → Run tr s₀ cs s → s₀.preV31 = supply s₀ → supply s₀ + INITIAL < 2 ^ 256 →
      s.initialized = false → totalSupplyView s = some (circulating s + INITIAL)

/-- **SOURCE NATSPEC CONFIRMED: NO BALANCE OVERFLOWS.** `BaseTokenHolder`'s NatSpec says "No
balance can overflow (users only gain what the holder loses)" (`BTH:24-25`). Along any run from
`Genesis` whose starting native supply is below `2^256 - INITIAL`, the total supply and every
single balance stay below `2^256`. -/
def Properties.NoBalanceOverflows : Prop :=
  ∀ (T : Type) (tr : Tracker T) (s₀ s : State T) (cs : List Call),
    Genesis s₀ → Run tr s₀ cs s → supply s₀ + INITIAL < 2 ^ 256 →
      supply s < 2 ^ 256 ∧ ∀ a, s.bal a < 2 ^ 256

/-- **COUNTERMODEL: THE `initL2` FLAG CHECK IS LOAD-BEARING.** With
`BaseTokenHolderAlreadyInitialized` (`BT:65-67`) deleted (`execInitL2NoFlag`), the upgrader's
second `initL2` mints `INITIAL` again: from an empty genesis with a correct (zero) backfill, the
native supply becomes `2 · INITIAL` and `totalSupply()` no longer returns the circulating supply
(it reverts). With the check, the second call reverts. -/
def Properties.InitL2FlagIsLoadBearing : Prop :=
  ∃ (s₀ s₁ s₂ : State Unit),
    Genesis s₀ ∧ s₀.preV31 = supply s₀
    ∧ execInitL2NoFlag s₀ complexUpgraderAddr 1 = some s₁
    ∧ execInitL2NoFlag s₁ complexUpgraderAddr 1 = some s₂
    ∧ supply s₂ = supply s₀ + 2 * INITIAL
    ∧ totalSupplyView s₂ ≠ some (circulating s₂)
    ∧ execInitL2 s₀ complexUpgraderAddr 1 = some s₁
    ∧ execInitL2 s₁ complexUpgraderAddr 1 = none

/-- **COUNTERMODEL: `give`'S CALLER CHECK IS LOAD-BEARING.** With `onlyInteropHandler`
(`BTH:30-35`) deleted (`execGiveNoGuard`), a caller other than the InteropHandler pays itself a
positive amount out of the reserve (with an accepting tracker). With the check the same call
reverts. -/
def Properties.GiveGuardIsLoadBearing : Prop :=
  ∃ (tr : Tracker Unit) (s s' : State Unit) (attacker : Address) (amt : ℕ),
    attacker ≠ interopHandlerAddr ∧ 0 < amt
    ∧ execGiveNoGuard tr s attacker amt 0 = some s'
    ∧ s'.bal attacker = s.bal attacker + amt
    ∧ circulating s' = circulating s + amt
    ∧ exec tr s (.give attacker attacker amt 0) = none

/-- **THE PREMISES ARE SATISFIABLE, NONTRIVIALLY.** A concrete run from a `Genesis` state with a
correct backfill: `initL2` by the upgrader, a `burnAndStartBridging` by the InteropCenter, a
`give` by the InteropHandler and a VM release. Every one of the given, burnt and released totals is
positive, the circulating supply changed, and `totalSupply()` returns it. -/
def Properties.SupplyWitness : Prop :=
  ∃ (tr : Tracker Unit) (s₀ s : State Unit) (cs : List Call),
    Genesis s₀ ∧ s₀.preV31 = supply s₀ ∧ supply s₀ + INITIAL < 2 ^ 256 ∧ Run tr s₀ cs s
    ∧ s.initialized = true ∧ 0 < s.given ∧ 0 < s.burnt ∧ 0 < s.released
    ∧ circulating s ≠ circulating s₀
    ∧ totalSupplyView s = some (circulating s)

end Contracts.L2BaseToken
