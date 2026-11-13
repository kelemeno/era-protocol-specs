import EraSpec.Contracts.ChainAssetHandler.Specs.Migration

/-!
# Properties: the migration pauses

Statements about the three pause switches of `EraSpec.Contracts.ChainAssetHandler.Specs.Migration`:
`ecosystemMigrationPaused` (owner), `ctmMigrationPaused[ctm]` (that CTM's owner), and
`PausableUpgradeable.paused()` (owner). Proofs are in
`EraSpec.Contracts.ChainAssetHandler.Proofs.Pause`.

* Every burn and mint on a hub requires all three switches of that hub off, for the CTM its
  asset id names, and migrations enabled (`PauseBlocksMigrationSteps`); that CTM is the
  chain's own (`PausedCTMChainsDoNotMove`).
* Along any run, a set switch keeps blocking those steps until a step that clears it
  (`PauseHoldsUntilUnpaused`), and only the right owner writes a switch
  (`OnlyOwnersTogglePauses`).
* Failed-migration recovery is enabled whatever the switches and the release flag say
  (`RecoveryIgnoresPauses`).

Every switch is per hub: `Properties.EcosystemPauseIsPerHub` in `Properties/Findings.lean`
shows what that means for the NatSpec's "ecosystem-wide".
-/

namespace Contracts.ChainAssetHandler

/-- **PAUSES BLOCK MIGRATION STEPS.** A successful burn or mint on hub `h` whose asset id maps
to CTM `x` happens only with migrations enabled, `paused()` off on `h`, the ecosystem pause
off on `h`, and `x`'s pause off on `h`. -/
def Properties.PauseBlocksMigrationSteps : Prop :=
  ∀ (W : World) (s s' : Sys) (l : Label) (h : ChainId) (x : Address), Step W s l s' →
    l.movesUnder W h x →
    W.migrationsEnabled = true ∧ s.paused h = false ∧ s.ecoPaused h = false ∧
      s.ctmPaused h x = false

/-- **A PAUSED CTM'S CHAINS DO NOT MOVE.** A burn of chain `c` on hub `h` requires the pause
of `c`'s CTM there to be off, provided the bridgehub's asset-id registry maps that CTM's asset
id back to it (`ctmAssetIdToAddress[ctmAssetIdFromAddress[x]] == x`, a premise about this one
CTM, not an injectivity assumption). A mint of `c` on `h` requires the pause of the CTM the
chain gets on `h` to be off. -/
def Properties.PausedCTMChainsDoNotMove : Prop :=
  ∀ (W : World) (s s' : Sys),
    (∀ h c t a orig, Step W s (.burn h c t a orig) s' →
      W.ctmOfAsset (W.assetOfCTM (s.ctm h c)) = s.ctm h c → s.ctmPaused h (s.ctm h c) = false) ∧
    (∀ h i c a, Step W s (.mint h i c a) s' → s.ctmPaused h (s'.ctm h c) = false)

/-- **A PAUSE HOLDS UNTIL IT IS LIFTED.** Along any run: if CTM `x`'s pause is set on hub `h`
and no step unpauses `x` on `h`, no step burns or mints under `x` on `h`; if the ecosystem
pause is set on `h` and no step lifts it, no step burns or mints on `h`; likewise for
`paused()`. -/
def Properties.PauseHoldsUntilUnpaused : Prop :=
  ∀ (W : World) (s s' : Sys) (ls : List Label) (h : ChainId), Run W s ls s' →
    (∀ x, s.ctmPaused h x = true → (∀ l ∈ ls, ¬ l.unpausesCTM h x) →
      ∀ l ∈ ls, ¬ l.movesUnder W h x) ∧
    (s.ecoPaused h = true → (∀ l ∈ ls, ¬ l.unpausesEcosystem h) → ∀ l ∈ ls, ¬ l.movesOn h) ∧
    (s.paused h = true → (∀ l ∈ ls, ¬ l.unpausesHub h) → ∀ l ∈ ls, ¬ l.movesOn h)

/-- **ONLY OWNERS TOGGLE PAUSES.** Along any run, if CTM `x`'s pause on hub `h` ends different,
`x` is registered on `h` and some step was a pause or unpause of `x` on `h` sent by `x`'s
owner; if the ecosystem pause on `h` ends different, some step was a pause or unpause sent by
`h`'s handler owner. -/
def Properties.OnlyOwnersTogglePauses : Prop :=
  ∀ (W : World) (s s' : Sys) (ls : List Label) (h : ChainId), Run W s ls s' →
    (∀ x, s'.ctmPaused h x ≠ s.ctmPaused h x →
      W.ctmRegistered h x = true ∧ ∃ l ∈ ls, l.togglesCTMPause h x (W.ctmOwner x)) ∧
    (s'.ecoPaused h ≠ s.ecoPaused h → ∃ l ∈ ls, l.togglesEcosystemPause h (W.owner h))

/-- **RECOVERY IGNORES PAUSES.** If L1's `bridgeConfirmTransferResult` succeeds, it also
succeeds, with the same effect, when every pause switch of every hub is set and
`CHAIN_MIGRATIONS_ENABLED` is `false`. -/
def Properties.RecoveryIgnoresPauses : Prop :=
  ∀ (W : World) (s s' : Sys) (i : ℕ) (c : ChainId) (failure : Bool),
    Step W s (.confirm i c failure) s' →
    Step { W with migrationsEnabled := false } (pauseAll s) (.confirm i c failure) (pauseAll s')

end Contracts.ChainAssetHandler
