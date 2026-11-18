import EraSpec.Contracts.ChainAssetHandler.Specs.Migration

/-!
# Properties: the migration pauses

Statements about the three pause switches of the chain asset handler in
`EraSpec.Contracts.ChainAssetHandler.Specs.Migration` (`draft/v0.35.0` at `b17415d20`):
`ecosystemMigrationPaused` (the handler's owner), `ctmMigrationPaused[ctm]` (that CTM's owner,
for a registered CTM), and `PausableUpgradeable.paused()` (the handler's owner). Proofs are in
`EraSpec.Contracts.ChainAssetHandler.Proofs.Pause`. Every switch is a field of one hub's
handler.

* Every burn and mint on a hub requires all three switches of that hub off, for the CTM its
  asset id names in that hub's registry, and migrations enabled
  (`PauseBlocksMigrationSteps`); for a burn that CTM is the chain's own, provided the registry
  maps the chain's CTM's asset id back to it, and for a mint it is the CTM the chain gets
  (`PausedCTMChainsDoNotMove`).
* Along any run, a set switch keeps blocking those steps until a step that clears it
  (`PauseHoldsUntilUnpaused`), and only the right owner writes a switch
  (`OnlyOwnersTogglePauses`).
* A burn or mint on hub `h` reads no other hub's switches (`PausesArePerHub`).
* Failed-migration recovery on L1 is enabled whatever the handler's switches and the release
  flag say (`RecoveryIgnoresPauses`); the L1 asset router's and nullifier's own `whenNotPaused`
  are outside the model.

Witnesses: `CahCTMPauseWitness` (a CTM pause blocks a burn, its owner lifts it, and the burn
goes through), `CahPausedHubWitness` (L1 paused, the gateway still burns, and the returning
mint waits on L1), `CahFailedAttemptWitness` in `Properties/Migration.lean` (a confirmation
step). `CahMismatchedRegistryReadsAnotherPause` shows the registry premise of
`PausedCTMChainsDoNotMove` is needed.
-/

namespace Contracts.ChainAssetHandler

/-- **PAUSES BLOCK MIGRATION STEPS.** A successful burn or mint on hub `h` whose asset id `h`'s
registry maps to CTM `x` happens only with migrations enabled, `paused()` off on `h`, the
ecosystem pause off on `h`, and `x`'s pause off on `h`. -/
def Properties.PauseBlocksMigrationSteps : Prop :=
  ∀ (W : World) (s s' : Sys) (l : Label) (h : ChainId) (x : Address), Step W s l s' →
    l.movesUnder W h x →
    W.migrationsEnabled = true ∧ s.paused h = false ∧ s.ecoPaused h = false ∧
      s.ctmPaused h x = false

/-- **A PAUSED CTM'S CHAINS DO NOT MOVE.** A burn of chain `c` on hub `h` requires the pause
of `c`'s CTM there to be off, provided `h`'s asset-id registry maps that CTM's asset id back to
it (`ctmAssetIdToAddress[ctmAssetIdFromAddress[x]] == x` for this one CTM `x`, not an
injectivity assumption). A mint of `c` on `h` requires the pause of the CTM the chain gets on
`h`'s bridgehub to be off. -/
def Properties.PausedCTMChainsDoNotMove : Prop :=
  ∀ (W : World) (s s' : Sys),
    (∀ h c t a, Step W s (.burn h c t a) s' →
      W.ctmOfAsset h (W.assetOfCTM h (s.ctm h c)) = s.ctm h c →
      s.ctmPaused h (s.ctm h c) = false) ∧
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
owner there; if the ecosystem pause on `h` ends different, some step was a pause or unpause
sent by `h`'s handler owner. (`paused()` is written only by `pause()`/`unpause()`, both
`onlyOwner`; that is not part of this statement.) -/
def Properties.OnlyOwnersTogglePauses : Prop :=
  ∀ (W : World) (s s' : Sys) (ls : List Label) (h : ChainId), Run W s ls s' →
    (∀ x, s'.ctmPaused h x ≠ s.ctmPaused h x →
      W.ctmRegistered h x = true ∧ ∃ l ∈ ls, l.togglesCTMPause h x (W.ctmOwner h x)) ∧
    (s'.ecoPaused h ≠ s.ecoPaused h → ∃ l ∈ ls, l.togglesEcosystemPause h (W.owner h))

/-- **PAUSES ARE PER HUB.** A successful burn or mint on hub `h` is also a step, with the same
effect on every other field, when every switch of every other hub's handler is set. -/
def Properties.PausesArePerHub : Prop :=
  ∀ (W : World) (s s' : Sys) (l : Label) (h : ChainId), Step W s l s' → l.movesOn h →
    Step W (pauseAllBut h s) l (pauseAllBut h s')

/-- **RECOVERY IGNORES PAUSES.** If L1's `bridgeConfirmTransferResult` succeeds, it also
succeeds, with the same effect on every other field, when every switch of every hub's chain
asset handler is set and `CHAIN_MIGRATIONS_ENABLED` is `false`. The L1 asset router's and the
L1 nullifier's own pauses, which the call passes through
(`bridge/asset-router/L1AssetRouter.sol:312`, `bridge/L1Nullifier.sol:220`), are not
modelled. -/
def Properties.RecoveryIgnoresPauses : Prop :=
  ∀ (W : World) (s s' : Sys) (i : ℕ) (c : ChainId) (failure : Bool),
    Step W s (.confirm i c failure) s' →
    Step { W with migrationsEnabled := false } (pauseAll s) (.confirm i c failure) (pauseAll s')

/-! ## Witnesses -/

/-- **A CTM PAUSE, LIFTED.** After the setup and CTM `7`'s owner pausing it on L1 (a run, so
the state is reachable and the pause changed), L1's burn of chain `3` is not a step; after the
owner's `unpauseCTMMigration(7)` it is, and L1's registry maps CTM `7`'s asset id back to `7`.
This instantiates `PauseBlocksMigrationSteps`, `PausedCTMChainsDoNotMove` (burn), and
`OnlyOwnersTogglePauses`. -/
def Properties.CahCTMPauseWitness : Prop :=
  ∃ s, Run cahWorld cahInit (cahSetup ++ [.pauseCTM 1 7 11]) s ∧ Reach cahWorld s ∧
    s.ctmPaused 1 7 = true ∧ cahInit.ctmPaused 1 7 = false ∧
    (¬ ∃ s', Step cahWorld s (.burn 1 3 2 5) s') ∧
    ∃ s1 s2, Step cahWorld s (.unpauseCTM 1 7 11) s1 ∧ Step cahWorld s1 (.burn 1 3 2 5) s2 ∧
      cahWorld.ctmOfAsset 1 (cahWorld.assetOfCTM 1 (s1.ctm 1 3)) = s1.ctm 1 3 ∧
      Label.movesUnder cahWorld 1 7 (.burn 1 3 2 5)

/-- **L1 PAUSED, THE GATEWAY STILL BURNS.** With chain `3` on the gateway and L1's `paused()`
set (a reachable state), the run `[burn on the gateway, ecosystem pause on the gateway]` is a
run (neither step unpauses L1, and the burn is on another hub), and at its end L1's mint of the
returning chain is not a step. This instantiates `PauseHoldsUntilUnpaused` (the `paused()`
clause, non-empty run), `PausesArePerHub` (a burn on the gateway) and the mint half of
`PausedCTMChainsDoNotMove` on the gateway mint of the setup. -/
def Properties.CahPausedHubWitness : Prop :=
  ∃ s, Run cahWorld cahInit (cahSetup ++ [.burn 1 3 2 5, .mint 2 0 3 5, .pause 1 10]) s ∧
    Reach cahWorld s ∧ s.paused 1 = true ∧
    ∃ s', Run cahWorld s [.burn 2 3 1 5, .pauseMigration 2 10] s' ∧
      Label.movesOn 2 (.burn 2 3 1 5) ∧
      ¬ ∃ s'', Step cahWorld s' (.mint 1 1 3 5) s''

/-- **THE REGISTRY PREMISE IS NEEDED.** In `cahWorldMismatched` (L1's registry maps asset id
`5` to CTM `8` while CTM `7`'s asset id is still `5`), after the setup and CTM `7`'s owner
pausing it (a reachable state), chain `3` is under CTM `7`, CTM `7`'s pause is set, the
registry premise of `PausedCTMChainsDoNotMove` fails for CTM `7`, and L1's burn of chain `3`
is a step: the check reads CTM `8`'s pause. -/
def Properties.CahMismatchedRegistryReadsAnotherPause : Prop :=
  ∃ s s', Run cahWorldMismatched cahInit (cahSetup ++ [.pauseCTM 1 7 11]) s ∧
    Reach cahWorldMismatched s ∧ s.ctm 1 3 = 7 ∧ s.ctmPaused 1 7 = true ∧
    cahWorldMismatched.ctmOfAsset 1 (cahWorldMismatched.assetOfCTM 1 7) ≠ 7 ∧
    Step cahWorldMismatched s (.burn 1 3 2 5) s'

end Contracts.ChainAssetHandler
