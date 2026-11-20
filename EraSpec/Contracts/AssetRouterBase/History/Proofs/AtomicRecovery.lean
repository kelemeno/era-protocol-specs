import EraSpec.Contracts.AssetRouterBase.History.Properties.AtomicRecovery
import EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecovery

/-!
# History proofs: the atomic refund at the pin `c67894b9`

Certificates of `EraSpec.Contracts.AssetRouterBase.History.Properties.AtomicRecovery`.  The
lemmas and the concrete instances they use stay in `EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecovery`.
History is the record of an older commit, not a claim about `b17415d20`.
-/

namespace Contracts.AssetRouter.AtomicRecovery.History

open AttackVectors.RecoveryLimits (Outcome LegState LoopCompletes recoveredCount ClaimAccepted)

variable {X : Type}

/-! ## Certificates -/

theorem RecoveryCallsTheVault : Properties.RecoveryCallsTheVault :=
  fun _ enc cfg hk w dest src a m => recoverAtomicCall_finalize enc cfg hk w dest src a m

theorem RecoveryIgnoresHandler : Properties.RecoveryIgnoresHandler :=
  fun _ enc cfg hk w R caller dest d => recoverAtomicCall_router enc cfg hk w R caller dest d

theorem UnknownAssetRecoveryReverts : Properties.UnknownAssetRecoveryReverts := by
  intro X enc cfg hk w dest src a m hU hF
  rw [recoverAtomicCall_unaware hU hF]
  exact ⟨rfl, rfl⟩

theorem CustomAssetRecoveryRevertsOrCollision :
    Properties.CustomAssetRecoveryRevertsOrCollision := by
  intro X enc cfg hk w dest src c₀ s d m hU
  by_cases hF : FailsAssetIdCheck enc cfg (enc c₀ s d) m
  · exact Or.inl (recoverAtomicCall_unaware hU hF)
  · right
    unfold FailsAssetIdCheck at hF
    push Not at hF
    obtain ⟨md, hm, c, hc, he⟩ := hF
    exact ⟨md, c, hm, hc, he⟩

theorem CustomHandlerDepositRefundReverts : Properties.CustomHandlerDepositRefundReverts := by
  intro X enc cfg hk w log audit dest src c₀ s d m hc hs hh0 hhn hr hlog hdec
  refine ⟨?_, ?_⟩
  · unfold burnHandler
    rw [ite_eq_right hh0]
    exact hhn
  · exact recoverAtomicCall_unaware (customId_unknown_along hc hs hr hlog)
      (CustomIdFailsAssetIdCheckOn enc cfg c₀ s d m hs hdec)

theorem UnknownAssetOutcomeBlocksClaim : Properties.UnknownAssetOutcomeBlocksClaim := by
  intro X enc cfg hk w dest src a m pre post hU hF
  rw [recoverAtomicCall_unaware hU hF]
  exact AttackVectors.RecoveryLimits.revert_anywhere_blocks pre post

theorem ClaimRevertsWithUnknownAssetCall : Properties.ClaimRevertsWithUnknownAssetCall :=
  fun _ _ _ _ _ _ _ _ _ _ hU ho hhas hfail => claimRevertsWithUnknownAssetCall hU ho hhas hfail

theorem RefundOfOtherAssetLeavesAlone : Properties.RefundOfOtherAssetLeavesAlone :=
  fun _ _ _ _ _ _ _ _ _ _ _ hd h => recoverAtomicCall_frame hd h

theorem OtherClaimLeavesAlone : Properties.OtherClaimLeavesAlone := by
  intro X enc cfg hk other dest w w' st st' calls a ho hnot h
  unfold claimRefund at h
  by_cases hst : st ≠ LegState.Revertable
  · rw [ite_eq_left hst] at h; cases h
  rw [ite_eq_right hst] at h
  rcases hr : recoverBundle (recoverCall enc cfg hk other dest) w calls with _ | ⟨w₁, n⟩ <;>
    rw [hr] at h
  · cases h
  dsimp only at h
  by_cases hn : n = 0
  · rw [ite_eq_left hn] at h; cases h
  rw [ite_eq_right hn] at h
  have hw : w₁ = w' := (Prod.mk.inj (Option.some.inj h)).2
  rw [← hw]
  refine recoverBundle_leavesAlone calls w w₁ n ?_ hr
  intro c hc u u' b hs
  refine recoverCall_frame ho ?_ hs
  intro ht src m hd
  exact hnot ⟨c, hc, ht, src, m, hd⟩

theorem LegNeverRefunded : Properties.LegNeverRefunded := by
  intro X enc cfg hk other dest w w' calls a hU ho hhas hfail hreach
  have hU' : VaultUnaware cfg w'.vault a := by
    induction hreach with
    | refl => exact hU
    | tail _ hstep ih => exact leavesAlone_unaware ih hstep
  exact claimRevertsWithUnknownAssetCall hU' ho hhas hfail

theorem CustomHandlerBundleNeverRefunded : Properties.CustomHandlerBundleNeverRefunded := by
  intro X enc cfg hk other dest w log audit calls c₀ s d hc hs hr hlog ho hhas hdec
  refine claimRevertsWithUnknownAssetCall (customId_unknown_along hc hs hr hlog) ho hhas ?_
  intro c hcm ht src m hd
  exact CustomIdFailsAssetIdCheckOn enc cfg c₀ s d m hs (hdec c hcm ht src m hd)

theorem RecoveryOnlyByManager : Properties.RecoveryOnlyByManager := by
  intro X enc cfg hk w caller dest d h
  unfold recoverAtomicCall
  rw [ite_eq_left h]

theorem ClaimSucceedsIffAccepted : Properties.ClaimSucceedsIffAccepted :=
  fun _ step w calls => claimSucceedsIffAccepted step w calls

theorem KnownBridgedAssetRefundsOriginalCaller :
    Properties.KnownBridgedAssetRefundsOriginalCaller :=
  fun _ _ _ _ _ _ _ _ _ _ hp hn ht hf => recoverAtomicCall_known hp hn ht hf

theorem NativeAssetRefundsOriginalCaller : Properties.NativeAssetRefundsOriginalCaller :=
  fun _ _ _ _ _ _ _ _ _ _ hp hn hf => recoverAtomicCall_native hp hn hf

theorem RefundIgnoresRemoteReceiver : Properties.RefundIgnoresRemoteReceiver :=
  fun _ _ _ _ _ _ _ _ _ _ _ => rfl

theorem PreparedBurnRefundsDepositor : Properties.PreparedBurnRefundsDepositor := by
  intro Acc prepHooks s r out hw hprep X enc cfg hk other dest w x₁ hp hn ht hf
  obtain ⟨hoc, -, -, hamt, -, -⟩ := NativeTokenVaultBase.preparation_payload hw hprep
  unfold recoverCall routerCall
  dsimp only
  rw [ite_eq_left rfl]
  rw [← hamt] at hf
  rw [recoverAtomicCall_known hp hn ht hf, hoc, hamt]

theorem RefundIgnoresCallSender : Properties.RefundIgnoresCallSender :=
  fun _ _ _ _ _ _ _ _ _ _ => rfl

theorem DirectCallIsRefunded : Properties.DirectCallIsRefunded := by
  intro X enc cfg hk other dest src w sender a md x₁ x₂ hp hn ht hf hm
  refine ⟨?_, ?_⟩
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    rfl
  · have hcall : recoverCall enc cfg hk other dest w
        (directCall cfg.router sender (.finalizeDeposit src a (some md)))
        = some ({ w with rest := x₂ }, true) := by
      unfold recoverCall directCall
      dsimp only
      rw [ite_eq_left rfl, recoverAtomicCall_known hp hn ht hf, hm]
      rfl
    unfold claimRefund
    rw [ite_eq_right (by simp)]
    unfold recoverBundle
    rw [hcall]
    rfl

/-! ## Concrete instances

Chain `7`; router `3`, vault `4`, manager `5`; every metadata decodes to origin chain `1`.
Under `wEnc` every id hashed from the vault is `1` and every other id is `2`, so `wEnc` is
injective on any pair of one vault triple and one other triple.  The vault has registered one
bridged asset, `1` (origin chain `1`, origin token `9`, local token `6`); asset `2` has the
custom handler `11`. -/

theorem wVaultCall_refunded :
    claimRefund (recoverCall wEnc wCfg okHooks declineOther 8) LegState.Revertable wWorld
      [routerCall wCfg 1 wMd] = some (LegState.Reverted, { wWorld with rest := () }) :=
  (DirectCallIsRefunded Unit wEnc wCfg okHooks declineOther 8 wCfg.thisChain wWorld wCfg.router 1 wMd
    () () rfl wVault_known_one.1 wVault_known_one.2 rfl rfl).2

theorem VaultRejectsUnknownAssetSatisfiable : Properties.VaultRejectsUnknownAssetSatisfiable :=
  ⟨Unit, wEnc, wCfg, okHooks, wWorld, 8, 2, wMd, 1, wVault_unaware_two, wFails _, rfl, rfl,
    by decide, fun _ _ _ _ => Option.some_ne_none _, fun _ _ _ _ => Option.some_ne_none _,
    fun _ _ _ _ => Option.some_ne_none _, recoverAtomicCall_unaware wVault_unaware_two (wFails _)⟩

theorem CustomHandlerDepositRefundRevertsSatisfiable :
    Properties.CustomHandlerDepositRefundRevertsSatisfiable := by
  refine ⟨Unit, wEnc, wCfg, okHooks, wWorld, [wOp], NativeTokenVault.empty.audit, 0, 9, 0, wMd,
    by decide, by decide, ?_, ?_, wReach, ?_, fun p _ => wEnc_injOn _ _ _ _,
    fun _ _ => wEnc_injOn _ _ _ _, ⟨1, rfl⟩, rfl, fun _ _ _ _ => Option.some_ne_none _,
    fun _ _ _ _ => Option.some_ne_none _, fun _ _ _ _ => Option.some_ne_none _⟩
  · show wRouter.handler (wEnc 0 9 0) ≠ 0
    unfold wRouter wEnc; decide
  · show wRouter.handler (wEnc 0 9 0) ≠ 4
    unfold wRouter wEnc; decide
  · exact ⟨(1, 9), (NativeTokenVault.MemRegisteredPairs _ _ _).mpr ⟨wOp, List.mem_cons_self, rfl⟩⟩

theorem FramePremisesSatisfiable : Properties.FramePremisesSatisfiable := by
  have hg : NativeTokenVault.RegisterBridgedGuard (ntvId wEnc wCfg) wCfg.thisChain
      NativeTokenVault.empty.vault 1 6 9 1 :=
    ⟨by decide, by decide, by unfold ntvId wEnc; decide, by decide, rfl, fun h => h rfl⟩
  refine ⟨Unit, wEnc, wCfg, okHooks, declineOther, 8, wWorld, 2, wOp, NativeTokenVault.empty, _,
    .finalizeDeposit 7 1 (some wMd), { wWorld with rest := () }, true, [routerCall wCfg 1 wMd],
    LegState.Reverted, { wWorld with rest := () },
    ⟨NativeTokenVault.StepOp.registerBridged hg, ⟨(1, 9), rfl⟩, ?_⟩, ⟨?_, ?_⟩,
    ⟨declineOther_leaves 2, ?_, wVaultCall_refunded⟩⟩
  · intro p hp
    cases hp
    show wEnc 1 4 9 ≠ 2
    unfold wEnc; decide
  · intro src m h
    injection h with _ h2
    exact absurd h2 (by decide)
  · rw [recoverAtomicCall_known rfl wVault_known_one.1 wVault_known_one.2 rfl]
    rfl
  · rintro ⟨c, hc, _, src, m, hd⟩
    rw [List.mem_singleton] at hc
    subst hc
    injection hd with _ h2
    exact absurd h2 (by decide)

theorem CollisionLetsVaultMintCustomAsset : Properties.CollisionLetsVaultMintCustomAsset := by
  refine ⟨Unit, cEnc, wCfg, okHooks, ⟨wRouter, NativeTokenVault.empty.vault, false, ()⟩, 8, 7,
    0, 9, 0, wMd, by decide, ⟨rfl, by decide⟩, ?_⟩
  rfl

theorem CustomCollisionNotTautology : Properties.CustomCollisionNotTautology :=
  ⟨wEnc, wCfg, 0, 9, 0, wMd, 1, by decide, rfl, wEnc_custom_ne_vault _ _ _ _⟩

theorem KnownAssetRefundSatisfiable : Properties.KnownAssetRefundSatisfiable := by
  refine ⟨Unit, wEnc, wCfg, okHooks, wWorld, 8, 7, 1, wMd, (), rfl, wVault_known_one.1,
    wVault_known_one.2, rfl, ?_⟩
  rw [recoverAtomicCall_known rfl wVault_known_one.1 wVault_known_one.2 rfl]
  rfl

theorem NativeAssetRefundSatisfiable : Properties.NativeAssetRefundSatisfiable := by
  have hn : nVault.originChain (ntvId wEnc wCfg 7 6) = wCfg.thisChain :=
    NativeTokenVault.sn_originChain_self _ _ _ _ _
  refine ⟨Unit, wEnc, wCfg, okHooks, ⟨wRouter, nVault, false, ()⟩, 8, 7, ntvId wEnc wCfg 7 6, wMd,
    (), rfl, hn, rfl, ?_⟩
  rw [recoverAtomicCall_native (w := ⟨wRouter, nVault, false, ()⟩) rfl hn rfl]
  rfl

theorem PreparedBurnRefundSatisfiable : Properties.PreparedBurnRefundSatisfiable := by
  open NativeTokenVaultBase in
  have hw : WellFormed witnessPrepState := ⟨witnessToken_ledger, witnessPrep_rc⟩
  have htok : witnessPrepState.registry.tokenForAsset (2 + 1) = 5 := witnessPrep_token
  have hs : InScope witnessPrepState witnessRequest := by
    refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    show (if (0 : NativeTokenVaultBase.Address) = 0 then
      witnessPrepState.registry.tokenForAsset (2 + 1) else 0) = 5
    rw [ite_eq_left rfl, htok]
  have hsel : selectedToken witnessPrepState witnessRequest = 5 := hs.2.2.2.2
  have he : EntryAllowed witnessPrepState witnessRequest := by
    refine ⟨rfl, rfl, rfl, ?_, ?_, by decide⟩
    · rw [hsel]; decide
    · rw [hsel]; exact witnessPrep_asset
  have hb : witnessRequest.data.amount.val ≤ witnessPrepState.token.balances 11 := by
    show (1 : UInt256).val ≤ Function.update (fun _ => 0) (11 : NativeTokenVaultBase.Address)
      (0 + (1 : UInt256).val) 11
    rw [Function.update_self]
    decide
  obtain ⟨out, hout⟩ := preparation_enabled (hooks := witnessPrepHooks) (accounted := ())
    (metadata := []) hw hs he rfl (by decide) hb (by decide) (by decide) rfl rfl
  have ho : pVault.originChain (2 + 1) = 1 := NativeTokenVault.sn_originChain_self _ _ _ _ _
  have htk : pVault.token (2 + 1) = 6 := NativeTokenVault.sn_token_self _ _ _ _ _
  have hn : pVault.originChain (2 + 1) ≠ wCfg.thisChain := by rw [ho]; decide
  have ht : pVault.token (2 + 1) ≠ 0 := by rw [htk]; decide
  refine ⟨Unit, witnessPrepHooks, witnessPrepState, witnessRequest, out, Unit, wEnc, wCfg,
    okHooks, declineOther, 8, ⟨wRouter, pVault, false, ()⟩, (), hw, hout, by decide, rfl, hn, ht, rfl, ?_⟩
  rw [PreparedBurnRefundsDepositor Unit witnessPrepHooks witnessPrepState witnessRequest out hw hout
    Unit wEnc wCfg okHooks declineOther 8 ⟨wRouter, pVault, false, ()⟩ () rfl hn ht rfl]
  rfl

theorem ClaimRevertsWithUnknownAssetCallSatisfiable :
    Properties.ClaimRevertsWithUnknownAssetCallSatisfiable :=
  ⟨Unit, wEnc, wCfg, okHooks, declineOther, 8, wWorld, [routerCall wCfg 2 wMd, routerCall wCfg 1 wMd],
    2, wVault_unaware_two, declineOther_leaves 2, wBundleHas, wBundleFails, rfl,
    ⟨routerCall wCfg 1 wMd, List.mem_cons_of_mem _ List.mem_cons_self,
      by rw [wVaultCall_refunded]; rfl⟩⟩

theorem CustomHandlerBundleIsStranded : Properties.CustomHandlerBundleIsStranded := by
  refine ⟨Unit, wEnc, wCfg, okHooks, declineOther, 8, wWorld, 2, 1, wMd, wMd, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · rfl
    · rw [List.mem_singleton] at hc; subst hc; rfl
  · show (if wRouter.handler 2 = 0 then (4 : Address) else wRouter.handler 2) ≠ 4
    unfold wRouter; decide
  · show (if wRouter.handler 1 = 0 then (4 : Address) else wRouter.handler 1) = 4
    unfold wRouter; decide
  · rw [wVaultCall_refunded]; rfl
  · intro w' hr
    exact LegNeverRefunded Unit wEnc wCfg okHooks declineOther 8 wWorld w' _ 2 wVault_unaware_two
      (declineOther_leaves 2) wBundleHas wBundleFails hr

theorem CustomHandlerBundleNeverRefundedSatisfiable :
    Properties.CustomHandlerBundleNeverRefundedSatisfiable := by
  refine ⟨Unit, wEnc, wCfg, okHooks, declineOther, 8, wWorld, [wOp], NativeTokenVault.empty.audit,
    [routerCall wCfg 2 wMd, routerCall wCfg 1 wMd], 0, 9, 0, by decide, by decide, wReach, ?_,
    fun _ _ => wEnc_injOn _ _ _ _, declineOther_leaves _, fun _ u _ _ => ⟨(u, false), rfl⟩, ?_,
    fun _ _ _ _ _ _ _ _ _ _ => wEnc_injOn _ _ _ _, ?_⟩
  · exact ⟨(1, 9), (NativeTokenVault.MemRegisteredPairs _ _ _).mpr ⟨wOp, List.mem_cons_self, rfl⟩⟩
  · rw [wEnc_custom]; exact wBundleHas
  · exact ⟨routerCall wCfg 1 wMd, List.mem_cons_of_mem _ List.mem_cons_self,
      by rw [wVaultCall_refunded]; rfl⟩

theorem DirectCallMintsUnbacked : Properties.DirectCallMintsUnbacked := by
  obtain ⟨hvalid, hclaim⟩ := DirectCallIsRefunded (Addr160 → ℕ) wEnc wCfg ledgerHooks declineOther 8 0
    ledgerWorld 13 1 wMd (fun _ => 0)
    (Function.update (fun _ => 0) wMd.originalCaller (0 + wMd.amount.val)) rfl
    wVault_known_one.1 wVault_known_one.2 rfl rfl
  refine ⟨wEnc, wCfg, ledgerHooks, declineOther, 8, 0, ledgerWorld, 13, 1, wMd, _, by decide, hvalid,
    hclaim, rfl, ?_⟩
  show 0 < Function.update (fun _ => 0) wMd.originalCaller (0 + wMd.amount.val) wMd.originalCaller
  rw [Function.update_self]
  decide

end Contracts.AssetRouter.AtomicRecovery.History
