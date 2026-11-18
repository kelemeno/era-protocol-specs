import EraSpec.Protocol.NativeValueLegs.Specs.RouterRecoveryFrame

/-!
# Properties: the head router recovery satisfies the frame premises through the vault

Statements about `EraSpec.Protocol.NativeValueLegs.Specs.RouterRecoveryFrame` (head `b17415d20`).
Proofs are in `EraSpec.Protocol.NativeValueLegs.Proofs.RouterRecoveryFrame`.

* The vault's refund of an asset other than `A` leaves `A`'s footprint and registration alone, so
  `recoverAtomicCall` at head satisfies `RecoveryFramesOthers` for `A` whenever the handlers other
  than the vault and the vault's deploy branch do (`HeadRouterRecoveryFramesOthers`), and
  `CodeFrames` whenever they also clear no registration, nor does the custom burn
  (`HeadCodeFrames`).
* So `LegConservation`'s refund result holds with the head router recovery and the premise only on
  the remaining abstract code (`ClaimReturnsCollectedHeadRouter`; witness
  `HeadRouterClaimWitness`, whose router-produced call is recovered through the vault).
-/

namespace Contracts.NativeValueLegs

/-- **THE VAULT FRAMES OTHER ASSETS.**  If the handlers other than the vault and the vault's deploy
branch leave `A` alone when they recover another asset, then so does the head `recoverAtomicCall`
on every call data not naming `A`. -/
def Properties.HeadRouterRecoveryFramesOthers : Prop :=
  ∀ (cfg : Config) (code : RecoveryCode)
    (customBurn : Address → World → Chain → AssetId → Address → ℕ → Option World) (A : AssetId),
    CodeFramesOthers cfg code A → RecoveryFramesOthers (headParams cfg code customBurn) A

/-- **THE RUN-LEVEL FRAME PREMISE, REDUCED.**  If the handlers other than the vault and the vault's
deploy branch leave every other asset alone and clear no registration, and the custom burn clears no
registration, then the head parameters satisfy `CodeFrames`. -/
def Properties.HeadCodeFrames : Prop :=
  ∀ (cfg : Config) (code : RecoveryCode)
    (customBurn : Address → World → Chain → AssetId → Address → ℕ → Option World),
    (∀ A, CodeFramesOthers cfg code A) → CodeRegMono code →
    (∀ h w d a u v w', customBurn h w d a u v = some w' → RegMono w w') →
    CodeFrames (headParams cfg code customBurn)

/-- **(2) WITH THE HEAD ROUTER RECOVERY.**  `ClaimReturnsCollected` with the router recovery at head
and the frame premise only on the handlers other than the vault and the vault's deploy branch. -/
def Properties.ClaimReturnsCollectedHeadRouter : Prop :=
  ∀ (cfg : Config) (code : RecoveryCode)
    (customBurn : Address → World → Chain → AssetId → Address → ℕ → Option World)
    (u : Address) (starters : List Starter) (B : Bundle) (w w' : World),
    u ≠ cfg.router →
    (∀ s ∈ starters, StarterPasses deployed cfg s) →
    List.Forall₂ (FormsCall cfg B.destBaseAsset u) starters B.calls →
    CodeFramesOthers cfg code B.destBaseAsset →
    (0 < collected starters →
      B.destBaseAsset = cfg.baseAsset ∨ w.registered B.destBaseAsset = true) →
    claimRefund (headParams cfg code customBurn) w B = some w' →
    Shifted cfg B.destBaseAsset u (collected starters) w w'

/-- **WITNESS.**  Every premise of `ClaimReturnsCollectedHeadRouter` and of `HeadCodeFrames` holds,
with abstract code that writes the world (mints), a router-produced call whose asset the source
router routes to the vault, a value call of `collected > 0`, and the refund succeeds. -/
def Properties.HeadRouterClaimWitness : Prop :=
  ∃ (cfg : Config) (code : RecoveryCode)
    (customBurn : Address → World → Chain → AssetId → Address → ℕ → Option World)
    (u : Address) (starters : List Starter) (B : Bundle) (w : World),
    (∀ A, CodeFramesOthers cfg code A) ∧ CodeRegMono code ∧
      (∀ h w d a u v w', customBurn h w d a u v = some w' → RegMono w w') ∧
      u ≠ cfg.router ∧ (∀ s ∈ starters, StarterPasses deployed cfg s) ∧
      List.Forall₂ (FormsCall cfg B.destBaseAsset u) starters B.calls ∧
      CodeFramesOthers cfg code B.destBaseAsset ∧ w.registered B.destBaseAsset = true ∧
      (∃ c ∈ B.calls, c.fromAddr = cfg.router ∧
        ∃ src a m, c.data = .finalizeDeposit src a m ∧ w.handler a = cfg.ntv) ∧
      0 < collected starters ∧ (claimRefund (headParams cfg code customBurn) w B).isSome

end Contracts.NativeValueLegs
