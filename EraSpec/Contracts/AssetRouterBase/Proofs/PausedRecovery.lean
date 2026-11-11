import EraSpec.Contracts.AssetRouterBase.Properties.PausedRecovery
import EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecovery

/-!
# Proofs: a paused vault blocks the atomic refund, and unpausing restores it

Proofs of `EraSpec.Contracts.AssetRouterBase.Properties.PausedRecovery`.  The blocking result is
`AtomicRecovery.recoverBundle_eq_none_of_blocking` with the invariant "the vault is paused":
every returning call keeps it, and every router deposit reverts under it (`vaultRefund_guard`).
The exactness result is an induction over the bundle that commutes setting the flag with each
call.
-/

namespace Contracts.AssetRouter.PausedRecovery

open Contracts.AssetRouter.AtomicRecovery
open AttackVectors.RecoveryLimits (Outcome LegState ClaimAccepted)

variable {X : Type}

/-! ## One call -/

theorem recoverAtomicCall_paused_deposit {enc : AssetIdOf} {cfg : Config} {hk : Hooks X}
    {w : World X} (hp : w.paused = true) (dest src : Chain) (a : AssetId) (m : Option MintData) :
    recoverAtomicCall enc cfg hk w cfg.manager dest (.finalizeDeposit src a m) = none := by
  rw [recoverAtomicCall_finalize]
  unfold ntvRecover
  rw [vaultRefund_guard (Or.inr (Or.inr hp))]
  rfl

theorem recoverAtomicCall_keeps_paused {enc : AssetIdOf} {cfg : Config} {hk : Hooks X}
    {w w' : World X} {caller : Address} {dest : Chain} {d : CallData} {b : Bool}
    (h : recoverAtomicCall enc cfg hk w caller dest d = some (w', b)) : w'.paused = w.paused := by
  unfold recoverAtomicCall at h
  by_cases hc : caller ≠ cfg.manager
  · rw [ite_eq_left hc] at h; cases h
  rw [ite_eq_right hc] at h
  rcases d with ⟨src, a, m⟩ | _ | _
  · obtain ⟨w'', hn, hp⟩ := Option.map_eq_some_iff.mp h
    cases hp
    unfold ntvRecover at hn
    obtain ⟨⟨V', x'⟩, _, rfl⟩ := Option.map_eq_some_iff.mp hn
    rfl
  · cases h
  · cases h; rfl

/-- A router call that is not a `finalizeDeposit` commutes with setting the flag. -/
theorem recoverAtomicCall_setPaused {enc : AssetIdOf} {cfg : Config} {hk : Hooks X}
    (w : World X) (caller : Address) (dest : Chain) {d : CallData}
    (hd : ∀ src a m, d ≠ .finalizeDeposit src a m) (p : Bool) :
    recoverAtomicCall enc cfg hk { w with paused := p } caller dest d
      = (recoverAtomicCall enc cfg hk w caller dest d).map
          (fun r => ({ r.1 with paused := p }, r.2)) := by
  unfold recoverAtomicCall
  by_cases hc : caller ≠ cfg.manager
  · rw [ite_eq_left hc, ite_eq_left hc]; rfl
  rw [ite_eq_right hc, ite_eq_right hc]
  rcases d with ⟨src, a, m⟩ | _ | _
  · exact absurd rfl (hd src a m)
  · rfl
  · rfl

/-- One iteration of the loop on a call that is not a router deposit commutes with setting the
flag, given other targets that ignore it. -/
theorem recoverCall_setPaused {enc : AssetIdOf} {cfg : Config} {hk : Hooks X}
    {other : Address → World X → Chain → CallData → Option (World X × Bool)} {dest : Chain}
    (ho : OthersIgnorePause other) (w : World X) {c : Call}
    (hc : ¬ (c.target = cfg.router ∧ ∃ src a m, c.data = .finalizeDeposit src a m)) (p : Bool) :
    recoverCall enc cfg hk other dest { w with paused := p } c
      = (recoverCall enc cfg hk other dest w c).map (fun r => ({ r.1 with paused := p }, r.2)) := by
  unfold recoverCall
  by_cases ht : c.target = cfg.router
  · rw [ite_eq_left ht, ite_eq_left ht]
    exact recoverAtomicCall_setPaused w cfg.manager dest
      (fun src a m hd => hc ⟨ht, src, a, m, hd⟩) p
  · rw [ite_eq_right ht, ite_eq_right ht]
    exact ho _ _ _ _ p

/-! ## The loop and the claim -/

/-- **A PAUSED VAULT BLOCKS THE CLAIM.** -/
theorem paused_vault_blocks_claim {enc : AssetIdOf} {cfg : Config} {hk : Hooks X}
    {other : Address → World X → Chain → CallData → Option (World X × Bool)} {dest : Chain}
    {w : World X} {st : LegState} {calls : List Call} (hp : w.paused = true)
    (ho : OthersLeavePause other) (hhas : HasRouterDeposit cfg calls) :
    claimRefund (recoverCall enc cfg hk other dest) st w calls = none := by
  apply claimRefund_eq_none
  refine recoverBundle_eq_none_of_blocking (fun u => u.paused = true)
    (fun c => c.target = cfg.router ∧ ∃ src a m, c.data = .finalizeDeposit src a m) calls w
    ?_ ?_ hhas hp
  · intro c _ u u' b hu hs
    unfold recoverCall at hs
    by_cases ht : c.target = cfg.router
    · rw [ite_eq_left ht] at hs
      rw [recoverAtomicCall_keeps_paused hs]; exact hu
    · rw [ite_eq_right ht] at hs
      rw [ho _ _ _ _ _ _ hs]; exact hu
  · rintro c _ ⟨ht, src, a, m, hd⟩ u hu
    unfold recoverCall
    rw [ite_eq_left ht, hd]
    exact recoverAtomicCall_paused_deposit hu dest src a m

/-- The loop on a bundle with no router deposit commutes with setting the flag. -/
theorem recoverBundle_setPaused {enc : AssetIdOf} {cfg : Config} {hk : Hooks X}
    {other : Address → World X → Chain → CallData → Option (World X × Bool)} {dest : Chain}
    (ho : OthersIgnorePause other) (p : Bool) :
    ∀ (calls : List Call) (w : World X), ¬ HasRouterDeposit cfg calls →
      recoverBundle (recoverCall enc cfg hk other dest) { w with paused := p } calls
        = (recoverBundle (recoverCall enc cfg hk other dest) w calls).map
            (fun r => ({ r.1 with paused := p }, r.2))
  | [], w, _ => rfl
  | c :: cs, w, hno => by
    have hc : ¬ (c.target = cfg.router ∧ ∃ src a m, c.data = .finalizeDeposit src a m) :=
      fun hc => hno ⟨c, List.mem_cons_self, hc⟩
    have hcs : ¬ HasRouterDeposit cfg cs :=
      fun ⟨c', hc', hb⟩ => hno ⟨c', List.mem_cons_of_mem _ hc', hb⟩
    unfold recoverBundle
    rw [recoverCall_setPaused ho w hc p]
    rcases hs : recoverCall enc cfg hk other dest w c with _ | ⟨w', b⟩
    · rfl
    · dsimp only [Option.map_some]
      rw [recoverBundle_setPaused ho p cs w' hcs]
      rcases recoverBundle (recoverCall enc cfg hk other dest) w' cs with _ | ⟨w'', n⟩
      · rfl
      · rfl

/-- **PAUSING AFFECTS EXACTLY THE BUNDLES WITH A ROUTER DEPOSIT.** -/
theorem pause_irrelevant_without_router_deposit {enc : AssetIdOf} {cfg : Config} {hk : Hooks X}
    {other : Address → World X → Chain → CallData → Option (World X × Bool)} {dest : Chain}
    (w : World X) (st : LegState) {calls : List Call} (p : Bool) (ho : OthersIgnorePause other)
    (hno : ¬ HasRouterDeposit cfg calls) :
    claimRefund (recoverCall enc cfg hk other dest) st { w with paused := p } calls
      = (claimRefund (recoverCall enc cfg hk other dest) st w calls).map
          (fun r => (r.1, { r.2 with paused := p })) := by
  unfold claimRefund
  by_cases hst : st ≠ LegState.Revertable
  · rw [ite_eq_left hst, ite_eq_left hst]; rfl
  rw [ite_eq_right hst, ite_eq_right hst, recoverBundle_setPaused ho p calls w hno]
  rcases recoverBundle (recoverCall enc cfg hk other dest) w calls with _ | ⟨w', n⟩
  · rfl
  · dsimp only [Option.map_some]
    by_cases hn : n = 0
    · rw [ite_eq_left hn, ite_eq_left hn]; rfl
    · rw [ite_eq_right hn, ite_eq_right hn]; rfl

/-- **PAUSE AND UNPAUSE CHANGE ONLY THE FLAG.** -/
theorem pause_unpause_round_trip (w : World X) :
    (w.paused = false → pauseVault w = some { w with paused := true }
        ∧ unpauseVault { w with paused := true } = some w ∧ unpauseVault w = none)
    ∧ (w.paused = true → pauseVault w = none) := by
  refine ⟨fun hp => ⟨?_, ?_, ?_⟩, fun hp => ?_⟩
  · unfold pauseVault; rw [hp]; rfl
  · unfold unpauseVault
    dsimp only
    rw [ite_eq_left rfl]
    cases w
    simp_all
  · unfold unpauseVault; rw [hp]; rfl
  · unfold pauseVault; rw [hp]; rfl

/-- **A PAUSE DELAYS A REFUND AND DOES NOT CANCEL IT.** -/
theorem paused_claim_retried_after_unpause {enc : AssetIdOf} {cfg : Config} {hk : Hooks X}
    {other : Address → World X → Chain → CallData → Option (World X × Bool)} {dest : Chain}
    {w : World X} {st : LegState} {calls : List Call} {r : LegState × World X}
    (ho : OthersLeavePause other) (hhas : HasRouterDeposit cfg calls) (hp : w.paused = false)
    (hr : claimRefund (recoverCall enc cfg hk other dest) st w calls = some r) :
    ∃ w₁ w₂, pauseVault w = some w₁
      ∧ claimRefund (recoverCall enc cfg hk other dest) st w₁ calls = none
      ∧ unpauseVault w₁ = some w₂ ∧ w₂ = w
      ∧ claimRefund (recoverCall enc cfg hk other dest) st w₂ calls = some r := by
  obtain ⟨hpause, hunpause, _⟩ := (pause_unpause_round_trip w).1 hp
  exact ⟨_, _, hpause, paused_vault_blocks_claim rfl ho hhas, hunpause, rfl, hr⟩

/-- **A PREPARED BURN'S REFUND, PAUSED AND UNPAUSED.** -/
theorem paused_prepared_burn_refund_delayed {Acc : Type}
    {prepHooks : NativeTokenVaultBase.Hooks Acc} {s : NativeTokenVaultBase.State Acc}
    {r : NativeTokenVaultBase.Request} {out : NativeTokenVaultBase.Result Acc}
    (hw : NativeTokenVaultBase.WellFormed s) (hprep : NativeTokenVaultBase.prepare prepHooks s r = some out)
    {enc : AssetIdOf} {cfg : Config} {hk : Hooks X}
    {other : Address → World X → Chain → CallData → Option (World X × Bool)} {dest : Chain}
    {w : World X} {x₁ : X} (hn : w.vault.originChain r.assetId ≠ cfg.thisChain)
    (ht : w.vault.token r.assetId ≠ 0) (hf : hk.fromChain w.rest dest r.assetId r.data.amount = some x₁) :
    recoverCall enc cfg hk other dest { w with paused := true } (routerCall cfg r.assetId out.data) = none
    ∧ recoverCall enc cfg hk other dest { w with paused := false }
        (routerCall cfg r.assetId out.data)
      = (hk.mint x₁ (w.vault.token r.assetId) r.depositor r.data.amount).map
          (fun x₂ => ({ w with paused := false, rest := x₂ }, true)) := by
  refine ⟨?_, ?_⟩
  · unfold recoverCall routerCall
    dsimp only
    rw [ite_eq_left rfl]
    exact recoverAtomicCall_paused_deposit rfl dest _ _ _
  · exact PreparedBurnRefundsDepositor Acc prepHooks s r out hw hprep X enc cfg hk other dest
      { w with paused := false } x₁ rfl hn ht hf

/-! ## Witness -/

/-- Targets other than the router recover, change nothing, and ignore the flag. -/
def pauseIgnoringOther {X : Type} : Address → World X → Chain → CallData → Option (World X × Bool) :=
  fun _ w _ _ => some (w, true)

theorem pauseIgnoringOther_leaves {X : Type} : OthersLeavePause (pauseIgnoringOther (X := X)) := by
  intro _ _ _ _ _ _ h; cases h; rfl

theorem pauseIgnoringOther_ignores {X : Type} : OthersIgnorePause (pauseIgnoringOther (X := X)) :=
  fun _ _ _ _ _ => rfl

/-- A call to a target other than the router (`99`). -/
def otherTargetCall : Call := ⟨99, 99, 0, .other⟩

theorem paused_recovery_witness : Properties.PausedRecoveryWitness := by
  have hvault : claimRefund (recoverCall wEnc wCfg okHooks pauseIgnoringOther 8) LegState.Revertable
      wWorld [routerCall wCfg 1 wMd] = some (LegState.Reverted, { wWorld with rest := () }) :=
    (DirectCallIsRefunded Unit wEnc wCfg okHooks pauseIgnoringOther 8 wCfg.thisChain wWorld
      wCfg.router 1 wMd () () rfl wVault_known_one.1 wVault_known_one.2 rfl rfl).2
  have hhas : HasRouterDeposit wCfg [routerCall wCfg 1 wMd] :=
    ⟨routerCall wCfg 1 wMd, List.mem_cons_self, rfl, wCfg.thisChain, 1, some wMd, rfl⟩
  have hno : ¬ HasRouterDeposit wCfg [otherTargetCall] := by
    rintro ⟨c, hc, ht, _⟩
    rw [List.mem_singleton] at hc
    subst hc
    exact absurd ht (by decide)
  have hother : ∀ (w : World Unit), claimRefund (recoverCall wEnc wCfg okHooks pauseIgnoringOther 8)
      LegState.Revertable w [otherTargetCall] = some (LegState.Reverted, w) := by
    intro w
    unfold claimRefund recoverBundle recoverCall
    rw [ite_eq_right (by decide), ite_eq_right (by decide)]
    rfl
  refine ⟨Unit, wEnc, wCfg, okHooks, pauseIgnoringOther, 8, wWorld, [routerCall wCfg 1 wMd],
    [otherTargetCall], _, pauseIgnoringOther_leaves, pauseIgnoringOther_ignores, hhas, rfl, hvault,
    paused_vault_blocks_claim rfl pauseIgnoringOther_leaves hhas, hno, ?_, ?_⟩
  · rw [hother]; rfl
  · rw [hother]; rfl

end Contracts.AssetRouter.PausedRecovery

/-! ## Certificates -/

namespace Contracts.AssetRouter.PausedRecovery

open Contracts.AssetRouter.AtomicRecovery

theorem PausedVaultRevertsRouterDeposit : Properties.PausedVaultRevertsRouterDeposit := by
  intro X enc cfg hk w dest src a m hp
  rw [recoverAtomicCall_paused_deposit hp dest src a m]
  exact ⟨rfl, rfl⟩

theorem PausedRouterDepositBlocksClaim : Properties.PausedRouterDepositBlocksClaim := by
  intro X enc cfg hk w dest src a m pre post hp
  rw [recoverAtomicCall_paused_deposit hp dest src a m]
  exact AttackVectors.RecoveryLimits.revert_anywhere_blocks pre post

theorem RouterRefundLeavesPause : Properties.RouterRefundLeavesPause :=
  fun _ _ _ _ _ _ _ _ _ _ h => recoverAtomicCall_keeps_paused h

theorem PausedVaultBlocksClaim : Properties.PausedVaultBlocksClaim :=
  fun _ _ _ _ _ _ _ _ _ hp ho hhas => paused_vault_blocks_claim hp ho hhas

theorem PauseIrrelevantWithoutRouterDeposit : Properties.PauseIrrelevantWithoutRouterDeposit :=
  fun _ _ _ _ _ _ w st _ p ho hno => pause_irrelevant_without_router_deposit w st p ho hno

theorem PauseUnpauseRoundTrip : Properties.PauseUnpauseRoundTrip :=
  fun _ w => pause_unpause_round_trip w

theorem PausedClaimRetriedAfterUnpause : Properties.PausedClaimRetriedAfterUnpause :=
  fun _ _ _ _ _ _ _ _ _ _ ho hhas hp hr => paused_claim_retried_after_unpause ho hhas hp hr

theorem PausedPreparedBurnRefundDelayed : Properties.PausedPreparedBurnRefundDelayed :=
  fun _ _ _ _ _ hw hprep _ _ _ _ _ _ _ _ hn ht hf =>
    paused_prepared_burn_refund_delayed hw hprep hn ht hf

theorem PausedRecoveryWitness : Properties.PausedRecoveryWitness := paused_recovery_witness

end Contracts.AssetRouter.PausedRecovery
