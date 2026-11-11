import EraSpec.Contracts.AssetRouterBase.Specs.PausedRecovery
import EraSpec.Contracts.NativeTokenVaultBase.Specs.RepresentationPreparation

/-!
# Properties: a paused vault blocks the atomic refund, and unpausing restores it

Statements about `EraSpec.Contracts.AssetRouterBase.Specs.PausedRecovery`.  Proofs are in
`EraSpec.Contracts.AssetRouterBase.Proofs.PausedRecovery`.

* **Every router deposit reverts while the vault is paused** (`PausedVaultRevertsRouterDeposit`).
  This holds whatever the asset, the data and the hooks.  The outcome is `reverts`, not
  `declined`, so by `AttackVectors.RecoveryLimits`' limit 2 it blocks the whole claim wherever it
  sits (`PausedRouterDepositBlocksClaim`).
* **So `claimRefund` reverts on any bundle with a router deposit** (headline
  `PausedVaultBlocksClaim`).  This holds statefully, over the calls before and after it, for every
  behaviour of the other targets that leaves the flag alone.  `claimRefund` is one transaction, so
  the leg keeps its state (`Revertable`), and so does everything the earlier calls wrote.
* **Pausing affects exactly those bundles** (`PauseIrrelevantWithoutRouterDeposit`).  This needs
  targets that neither read nor write the flag.  A bundle with no router deposit has the same
  claim result paused and unpaused, so the protocol-level refund gate
  (`Contracts.InteropPause.RecoverOpen`, read through `recoversViaVault`) is exact.
* **A pause delays a refund and does not cancel it** (headline `PausedClaimRetriedAfterUnpause`).
  A claim that succeeds on an unpaused world reverts once the vault is paused.  A pause and an
  unpause return exactly that world, where the same claim succeeds with the same result.
  `PausedPreparedBurnRefundDelayed` gives the outcome concretely for a burn the vault prepared:
  it reverts while paused, and after unpausing the depositor is re-minted the burned amount.

Every property with premises has a witness below (`PausedRecoveryWitness`).
-/

namespace Contracts.AssetRouter.PausedRecovery

open Contracts.AssetRouter.AtomicRecovery
open AttackVectors.RecoveryLimits (Outcome LegState ClaimAccepted)

/-! ## One call -/

/-- **EVERY ROUTER DEPOSIT REVERTS WHILE THE VAULT IS PAUSED.**  The manager's
`recoverAtomicCall` on any `finalizeDeposit` call reverts, whatever the asset, mint data, hooks
and destination; its outcome is `reverts`, not `declined`. -/
def Properties.PausedVaultRevertsRouterDeposit : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (dest src : Chain) (a : AssetId) (m : Option MintData),
    w.paused = true →
      recoverAtomicCall enc cfg hk w cfg.manager dest (.finalizeDeposit src a m) = none
      ∧ outcomeOf (recoverAtomicCall enc cfg hk w cfg.manager dest (.finalizeDeposit src a m))
          = Outcome.reverts

/-- **…SO IT BLOCKS THE CLAIM WHEREVER IT SITS.**  Composed with
`AttackVectors.RecoveryLimits.revert_anywhere_blocks`: whatever the other calls' outcomes, a
bundle containing a router deposit is not accepted while the vault is paused. -/
def Properties.PausedRouterDepositBlocksClaim : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (dest src : Chain) (a : AssetId) (m : Option MintData) (pre post : List Outcome),
    w.paused = true →
      ¬ ClaimAccepted
        (pre ++ outcomeOf (recoverAtomicCall enc cfg hk w cfg.manager dest
          (.finalizeDeposit src a m)) :: post)

/-- **A RETURNING ROUTER REFUND LEAVES THE FLAG ALONE.**  `recoverAtomicCall` writes only the
vault's registry and the rest of the world. -/
def Properties.RouterRefundLeavesPause : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w w' : World X)
    (caller : Address) (dest : Chain) (d : CallData) (b : Bool),
    recoverAtomicCall enc cfg hk w caller dest d = some (w', b) → w'.paused = w.paused

/-! ## The claim -/

/-- **HEADLINE: A PAUSED VAULT BLOCKS THE CLAIM.**  If the vault is paused, the other targets
leave its flag alone, and the bundle has a router deposit, then `claimRefund` reverts, for any
leg state and on the state the earlier calls actually leave.  The transaction reverts as a whole
(`AtomicFlowManager.sol:165-180`), so the leg stays `Revertable` and can be claimed again. -/
def Properties.PausedVaultBlocksClaim : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w : World X) (st : LegState) (calls : List Call),
    w.paused = true → OthersLeavePause other → HasRouterDeposit cfg calls →
      claimRefund (recoverCall enc cfg hk other dest) st w calls = none

/-- **PAUSING AFFECTS EXACTLY THE BUNDLES WITH A ROUTER DEPOSIT.**  If the other targets neither
read nor write the vault's flag and the bundle has no router deposit, the claim on a world with
the flag set to any `p` is the claim on the original world with the flag set to `p` after. -/
def Properties.PauseIrrelevantWithoutRouterDeposit : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w : World X) (st : LegState) (calls : List Call) (p : Bool),
    OthersIgnorePause other → ¬ HasRouterDeposit cfg calls →
      claimRefund (recoverCall enc cfg hk other dest) st { w with paused := p } calls
        = (claimRefund (recoverCall enc cfg hk other dest) st w calls).map
            (fun r => (r.1, { r.2 with paused := p }))

/-- **PAUSE AND UNPAUSE CHANGE ONLY THE FLAG.**  Pausing an unpaused vault and then unpausing it
returns exactly the original world; neither step succeeds from the wrong state. -/
def Properties.PauseUnpauseRoundTrip : Prop :=
  ∀ (X : Type) (w : World X),
    (w.paused = false → pauseVault w = some { w with paused := true }
        ∧ unpauseVault { w with paused := true } = some w ∧ unpauseVault w = none)
    ∧ (w.paused = true → pauseVault w = none)

/-- **HEADLINE: A PAUSE DELAYS A REFUND AND DOES NOT CANCEL IT.**  Take a claim that succeeds on
an unpaused world `w` with result `r`, on a bundle with a router deposit, with other targets that
leave the flag alone.  Once the vault is paused (`pauseVault w = some w₁`) the claim reverts.
Unpausing (`unpauseVault w₁ = some w₂`) returns exactly `w`, where the claim gives `r` again. -/
def Properties.PausedClaimRetriedAfterUnpause : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w : World X) (st : LegState) (calls : List Call)
    (r : LegState × World X),
    OthersLeavePause other → HasRouterDeposit cfg calls → w.paused = false →
    claimRefund (recoverCall enc cfg hk other dest) st w calls = some r →
      ∃ w₁ w₂, pauseVault w = some w₁
        ∧ claimRefund (recoverCall enc cfg hk other dest) st w₁ calls = none
        ∧ unpauseVault w₁ = some w₂ ∧ w₂ = w
        ∧ claimRefund (recoverCall enc cfg hk other dest) st w₂ calls = some r

/-- **A PREPARED BURN'S REFUND, PAUSED AND UNPAUSED.**  The setting of
`Contracts.AssetRouter.AtomicRecovery.Properties.PreparedBurnRefundsDepositor`: the vault prepared
a burn, the refund world knows the asset as bridged, and its tracker hook returns.  While the
vault is paused, the router call carrying the burn's mint data reverts.  On the same world
unpaused, it re-mints exactly the burned amount to the depositor. -/
def Properties.PausedPreparedBurnRefundDelayed : Prop :=
  ∀ (Acc : Type) (prepHooks : NativeTokenVaultBase.Hooks Acc) (s : NativeTokenVaultBase.State Acc)
    (r : NativeTokenVaultBase.Request) (out : NativeTokenVaultBase.Result Acc),
    NativeTokenVaultBase.WellFormed s → NativeTokenVaultBase.prepare prepHooks s r = some out →
    ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
      (other : Address → World X → Chain → CallData → Option (World X × Bool))
      (dest : Chain) (w : World X) (x₁ : X),
      w.vault.originChain r.assetId ≠ cfg.thisChain → w.vault.token r.assetId ≠ 0 →
      hk.fromChain w.rest dest r.assetId r.data.amount = some x₁ →
        recoverCall enc cfg hk other dest { w with paused := true }
            (routerCall cfg r.assetId out.data) = none
        ∧ recoverCall enc cfg hk other dest { w with paused := false }
            (routerCall cfg r.assetId out.data)
          = (hk.mint x₁ (w.vault.token r.assetId) r.depositor r.data.amount).map
              (fun x₂ => ({ w with paused := false, rest := x₂ }, true))

/-! ## Witness -/

/-- **THE PREMISES ARE JOINTLY SATISFIABLE.**  B1's concrete world (`wWorld`, unpaused), and other
targets that recover, change nothing and ignore the flag (`pauseIgnoringOther`, which meets both
`OthersLeavePause` and `OthersIgnorePause`).

* The one-call bundle of the vault-known asset's router deposit is claimed successfully, so
  `PausedClaimRetriedAfterUnpause`'s premises hold.  Its paused claim reverts, unlike its
  unpaused one.
* A one-call bundle with no router deposit, a call to another target, is claimed successfully
  both paused and unpaused, so `PauseIrrelevantWithoutRouterDeposit` compares two successful
  claims. -/
def Properties.PausedRecoveryWitness : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w : World X) (calls calls' : List Call) (r : LegState × World X),
    OthersLeavePause other ∧ OthersIgnorePause other
      ∧ HasRouterDeposit cfg calls ∧ w.paused = false
      ∧ claimRefund (recoverCall enc cfg hk other dest) LegState.Revertable w calls = some r
      ∧ claimRefund (recoverCall enc cfg hk other dest) LegState.Revertable
          { w with paused := true } calls = none
      ∧ ¬ HasRouterDeposit cfg calls'
      ∧ (claimRefund (recoverCall enc cfg hk other dest) LegState.Revertable
            { w with paused := true } calls').isSome = true
      ∧ (claimRefund (recoverCall enc cfg hk other dest) LegState.Revertable w calls').isSome
          = true

end Contracts.AssetRouter.PausedRecovery
