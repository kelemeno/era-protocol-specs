import EraSpec.Contracts.L2AssetTracker.Properties.LaterHeads
import EraSpec.Contracts.L2AssetTracker.Proofs.Accounting
import EraSpec.Contracts.L2AssetTracker.Proofs.HookOrdering
import EraSpec.Contracts.L2AssetTracker.Proofs.NativeEscrow
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.TrackerHooks

/-! # Proofs: the tracker results at the current heads, and the recovery guard -/

namespace Contracts.L2AssetTracker

open Contracts.NativeTokenVaultBase (State Request Result prepare ResolutionCall L2Accounting
  l2Hooks l2ResolutionHooks bridgeRecoverFailedTransfer recoveryCall WellFormed Bytes
  preparation_accounting)

/-! ## Calls at the heads -/

/-- A call at the heads leaves the backfill flag alone and never clears the guard. -/
theorem laterHeads_execHead_flags {cfg : Config} {sys sys' : Sys} {op : HeadOp}
    (h : execHead cfg sys op = some sys') :
    sys'.st.needBaseTokenTotalSupplyBackfill = sys.st.needBaseTokenTotalSupplyBackfill ∧
    (sys.st.guardInitialized = true → sys'.st.guardInitialized = true) := by
  have flow : ∀ {st' : Storage} {x : AssetId}, Frame sys.st st' x →
      st'.needBaseTokenTotalSupplyBackfill = sys.st.needBaseTokenTotalSupplyBackfill ∧
      (sys.st.guardInitialized = true → st'.guardInitialized = true) :=
    fun hf => ⟨hf.need, fun hg => hf.guard.trans hg⟩
  cases op with
  | registerNewToken x =>
    simp only [execHead, exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold registerNewTokenIfNeeded at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    by_cases hx : sys.st.isAssetRegistered x = true
    · rw [ite_eq_left hx] at h; cases h; exact ⟨rfl, id⟩
    rw [ite_eq_right hx] at h
    by_cases hc : cfg.ntvOriginChainId x = cfg.thisChain
    · rw [ite_eq_left hc] at h; cases h; exact ⟨rfl, id⟩
    · rw [ite_eq_right hc] at h; cases h; exact ⟨rfl, id⟩
  | registerLegacy reads x =>
    simp only [execHead, exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    exact flow (registerLegacyTokenIfNeeded_frame (registerLegacyToken_eq h))
  | initiate reads toChain x amount =>
    simp only [execHead, exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleInitiateBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    exact flow (initiateInner_frame h)
  | initiateBase reads toChain amount =>
    simp only [execHead, exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleInitiateBaseTokenBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    exact flow (initiateInner_frame h)
  | finalize reads fromChain x amount =>
    simp only [execHead, exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleFinalizeBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    exact flow (finalizeInner_frame h)
  | finalizeBase reads caller fromChain amount =>
    simp only [execHead, exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleFinalizeBaseTokenBridgingOnL2 at h
    by_cases hc : caller ≠ cfg.baseTokenHolder ∧ caller ≠ cfg.l2BaseToken
    · rw [ite_eq_left hc] at h; cases h
    rw [ite_eq_right hc] at h
    by_cases h0 : amount = 0
    · rw [ite_eq_left h0] at h; cases h; exact ⟨rfl, id⟩
    rw [ite_eq_right h0] at h
    by_cases hb : sys.st.baseTokenAssetId = 0
    · rw [ite_eq_left hb] at h; cases h
    rw [ite_eq_right hb] at h
    exact flow (finalizeInner_frame h)
  | initL2 =>
    simp only [execHead, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold initL2Head at h
    by_cases hg : sys.st.guardInitialized = true
    · rw [ite_eq_left hg] at h; cases h
    rw [ite_eq_right hg, ite_eq_right (not_not.2 rfl)] at h
    cases h
    exact ⟨rfl, fun _ => rfl⟩
  | setSettlementLayer c =>
    simp only [execHead, exec, Option.some.injEq] at h
    subst h
    exact ⟨rfl, id⟩

/-- The pin operation a call at the heads is: the same call, and for `initL2` the pin's `initL2`
with a clear flag. -/
private def headOpPin : HeadOp → Op
  | .registerNewToken a => .registerNewToken a
  | .registerLegacy reads a => .registerLegacy reads a
  | .initiate reads toChain a amount => .initiate reads toChain a amount
  | .initiateBase reads toChain amount => .initiateBase reads toChain amount
  | .finalize reads fromChain a amount => .finalize reads fromChain a amount
  | .finalizeBase reads caller fromChain amount => .finalizeBase reads caller fromChain amount
  | .initL2 => .initL2 false
  | .setSettlementLayer c => .setSettlementLayer c

private theorem headOpPin_touches (a : AssetId) (op : HeadOp) :
    (headOpPin op).TouchesAsset a ↔ op.TouchesAsset a := by
  cases op <;> exact Iff.rfl

/-- From a state whose backfill flag is clear while `initL2` has not run, a call at the heads is
its pin operation. -/
private theorem execHead_headOpPin {cfg : Config} {sys sys' : Sys} {op : HeadOp}
    (hflag : sys.st.guardInitialized = false → sys.st.needBaseTokenTotalSupplyBackfill = false)
    (h : execHead cfg sys op = some sys') : exec cfg sys (headOpPin op) = some sys' := by
  cases op with
  | registerNewToken a => exact h
  | registerLegacy reads a => exact h
  | initiate reads toChain a amount => exact h
  | initiateBase reads toChain amount => exact h
  | finalize reads fromChain a amount => exact h
  | finalizeBase reads caller fromChain amount => exact h
  | setSettlementLayer c => exact h
  | initL2 =>
    simp only [execHead, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold initL2Head at h
    by_cases hg : sys.st.guardInitialized = true
    · rw [ite_eq_left hg] at h; cases h
    rw [ite_eq_right hg, ite_eq_right (not_not.2 rfl)] at h
    cases h
    have hf : sys.st.needBaseTokenTotalSupplyBackfill = false := hflag (by simpa using hg)
    simp only [headOpPin, exec, initL2, Option.map_eq_some_iff]
    refine ⟨_, by rw [ite_eq_right hg, ite_eq_right (not_not.2 rfl)], ?_⟩
    obtain ⟨⟨cb, reg, l1, base, info, snap, need, guard⟩, sl, au⟩ := sys
    simp only at hf
    subst hf
    rfl

theorem HeadStepIsPinStep : Properties.HeadStepIsPinStep := by
  intro cfg sys sys' hflag ⟨op, h⟩
  exact ⟨headOpPin op, execHead_headOpPin hflag h⟩

theorem HeadRunIsPinRun : Properties.HeadRunIsPinRun := by
  intro cfg sys₀ sys hflag hreach
  have key : Reach cfg sys₀ sys ∧
      (sys.st.guardInitialized = false → sys.st.needBaseTokenTotalSupplyBackfill = false) := by
    induction hreach with
    | refl => exact ⟨Relation.ReflTransGen.refl, hflag⟩
    | @tail b c _ hstep ih =>
      obtain ⟨hr, hf⟩ := ih
      obtain ⟨op, hop⟩ := hstep
      refine ⟨hr.tail (HeadStepIsPinStep cfg b c hf ⟨op, hop⟩), fun hg => ?_⟩
      obtain ⟨hneed, hguard⟩ := laterHeads_execHead_flags hop
      rw [hneed]
      apply hf
      cases hb : b.st.guardInitialized with
      | false => rfl
      | true => rw [hguard hb] at hg; cases hg
  exact key.1

theorem HeadAccountingInvariant : Properties.HeadAccountingInvariant :=
  fun cfg sys₀ sys hinv hreach =>
    AccountingInvariant cfg sys₀ sys hinv
      (HeadRunIsPinRun cfg sys₀ sys hinv.backfillNeedsInit hreach)

theorem HeadNativeSentinel : Properties.HeadNativeSentinel :=
  fun cfg sys₀ sys a hinv hreach =>
    NativeSentinel cfg sys₀ sys a hinv (HeadRunIsPinRun cfg sys₀ sys hinv.backfillNeedsInit hreach)

theorem HeadInflowOverflowIsCap : Properties.HeadInflowOverflowIsCap :=
  fun cfg sys₀ sys reads fromChain a amount hinv hreach =>
    InflowOverflowIsCap cfg sys₀ sys reads fromChain a amount hinv
      (HeadRunIsPinRun cfg sys₀ sys hinv.backfillNeedsInit hreach)

theorem HeadOutflowIffNetOutFits : Properties.HeadOutflowIffNetOutFits :=
  fun cfg sys₀ sys reads toChain a amount hinv hreach =>
    OutflowIffNetOutFits cfg sys₀ sys reads toChain a amount hinv
      (HeadRunIsPinRun cfg sys₀ sys hinv.backfillNeedsInit hreach)

theorem HeadBaseNeverTakesLegacyPath : Properties.HeadBaseNeverTakesLegacyPath :=
  fun cfg sys₀ sys h hg hr =>
    BaseNeverTakesLegacyPath cfg sys₀ sys
      (HeadRunIsPinRun cfg sys₀ sys (fun hg' => by rw [hg] at hg'; cases hg') h) hg hr

/-! ## The composed run with a native token, at the heads -/

/-- A composed step at the heads leaves the backfill flag alone and never clears the guard. -/
private theorem headEscrowStep_flags {cfg : Config} {a : AssetId} {e e' : EscrowSys}
    (h : HeadEscrowStep cfg a e e') :
    e'.sys.st.needBaseTokenTotalSupplyBackfill = e.sys.st.needBaseTokenTotalSupplyBackfill ∧
    (e.sys.st.guardInitialized = true → e'.sys.st.guardInitialized = true) := by
  cases h with
  | nativeOut chain account amount hp =>
    obtain ⟨hh, _⟩ := escrow_runPath_eq_some.1 hp
    rw [escrow_pathHook_nativeOut] at hh
    have hf := initiateInner_frame hh
    exact ⟨hf.need, fun hg => hf.guard.trans hg⟩
  | nativeIn chain account amount hp =>
    obtain ⟨hh, _⟩ := escrow_runPath_eq_some.1 hp
    rw [escrow_pathHook_nativeIn] at hh
    have hf := finalizeInner_frame hh
    exact ⟨hf.need, fun hg => hf.guard.trans hg⟩
  | registerLegacy h => exact laterHeads_execHead_flags h
  | tracker op _ h => exact laterHeads_execHead_flags h
  | token _ => exact ⟨rfl, id⟩

/-- From a state whose backfill flag is clear while `initL2` has not run, a composed step at the
heads is a composed step of the pin model. -/
private theorem headEscrowStep_escrowStep {cfg : Config} {a : AssetId} {e e' : EscrowSys}
    (hflag : e.sys.st.guardInitialized = false → e.sys.st.needBaseTokenTotalSupplyBackfill = false)
    (h : HeadEscrowStep cfg a e e') : EscrowStep cfg a e e' := by
  cases h with
  | nativeOut chain account amount hp => exact EscrowStep.nativeOut chain account amount hp
  | nativeIn chain account amount hp => exact EscrowStep.nativeIn chain account amount hp
  | registerLegacy h => exact EscrowStep.registerLegacy h
  | tracker op hn h =>
    exact EscrowStep.tracker (headOpPin op) (fun ht => hn ((headOpPin_touches a op).1 ht))
      (execHead_headOpPin hflag h)
  | token ht => exact EscrowStep.token ht

theorem HeadEscrowRunIsEscrowRun : Properties.HeadEscrowRunIsEscrowRun := by
  intro cfg a e₀ e hflag hreach
  have key : EscrowReach cfg a e₀ e ∧
      (e.sys.st.guardInitialized = false → e.sys.st.needBaseTokenTotalSupplyBackfill = false) := by
    induction hreach with
    | refl => exact ⟨Relation.ReflTransGen.refl, hflag⟩
    | @tail b c _ hstep ih =>
      obtain ⟨hr, hf⟩ := ih
      refine ⟨hr.tail (headEscrowStep_escrowStep hf hstep), fun hg => ?_⟩
      obtain ⟨hneed, hguard⟩ := headEscrowStep_flags hstep
      rw [hneed]
      apply hf
      cases hb : b.sys.st.guardInitialized with
      | false => rfl
      | true => rw [hguard hb] at hg; cases hg
  exact key.1

theorem HeadEscrowInvariant : Properties.HeadEscrowInvariant :=
  fun cfg a e₀ e hn hinv h =>
    EscrowInvariant cfg a e₀ e hn hinv
      (HeadEscrowRunIsEscrowRun cfg a e₀ e hinv.inv.backfillNeedsInit h)

theorem HeadNativeReleasesAreEscrowed : Properties.HeadNativeReleasesAreEscrowed :=
  fun cfg a e₀ e hn hinv h =>
    NativeReleasesAreEscrowed cfg a e₀ e hn hinv
      (HeadEscrowRunIsEscrowRun cfg a e₀ e hinv.inv.backfillNeedsInit h)

theorem HeadNativeInboundIffCap : Properties.HeadNativeInboundIffCap :=
  fun cfg a e₀ e chain account amount hn hinv h =>
    NativeInboundIffCap cfg a e₀ e chain account amount hn hinv
      (HeadEscrowRunIsEscrowRun cfg a e₀ e hinv.inv.backfillNeedsInit h)

theorem HeadFundedNativeOutboundSucceeds : Properties.HeadFundedNativeOutboundSucceeds :=
  fun cfg a e₀ e chain account amount hn hinv h =>
    FundedNativeOutboundSucceeds cfg a e₀ e chain account amount hn hinv
      (HeadEscrowRunIsEscrowRun cfg a e₀ e hinv.inv.backfillNeedsInit h)

/-! ## The recovery guard -/

theorem HeadRecoveryRestoresVaultAndTracker : Properties.HeadRecoveryRestoresVaultAndTracker := by
  intro cfg metadata s r out sl₂ hw hp
  -- the outbound hook the preparation ran
  have hacc := preparation_accounting hp
  change (handleInitiateBridgingOnL2 cfg s.accounting.st s.accounting.sl
    (tokenReads cfg s.token) cfg.ntv r.destinationChain r.assetId r.data.amount
    (cfg.ntvOriginChainId r.assetId)).map (fun st => { s.accounting with st := st }) =
      some out.state.accounting at hacc
  rw [Option.map_eq_some_iff] at hacc
  obtain ⟨st', hinit, hacc'⟩ := hacc
  have hinner : initiateInner cfg s.accounting.st s.accounting.sl (tokenReads cfg s.token)
      r.destinationChain r.assetId r.data.amount (cfg.ntvOriginChainId r.assetId) = some st' := by
    unfold handleInitiateBridgingOnL2 at hinit
    rwa [ite_eq_right (not_not.2 rfl)] at hinit
  obtain ⟨_, st₀, hreg, _⟩ := initiateInner_spec hinner
  have hf := initiateInner_frame hinner
  refine ⟨st₀, hreg, fun hr => ?_, ?_⟩
  · rw [registerLegacyTokenIfNeeded_of_registered hr] at hreg
    exact (Option.some.inj hreg).symm
  have hst' : out.state.accounting.st = st' := by rw [← hacc']
  -- the guard reads the tracker storage after the burn, which agrees on `L1_CHAIN_ID` and the base
  -- asset with the starting one
  have hguard : RecoveryAccountingNeutral cfg out.state.accounting.st r.assetId r.destinationChain ↔
      RecoveryAccountingNeutral cfg s.accounting.st r.assetId r.destinationChain := by
    rw [hst']
    unfold RecoveryAccountingNeutral
    rw [hf.l1, hf.base]
  have hhead : headRecover cfg { out.state with accounting := { out.state.accounting with sl := sl₂ } }
      (recoveryCall s.config.router r out.data) =
      if RecoveryAccountingNeutral cfg out.state.accounting.st r.assetId r.destinationChain then
        bridgeRecoverFailedTransfer (l2ResolutionHooks cfg)
          { out.state with accounting := { out.state.accounting with sl := sl₂ } }
          (recoveryCall s.config.router r out.data)
      else none := rfl
  rw [hhead]
  by_cases hg : RecoveryAccountingNeutral cfg s.accounting.st r.assetId r.destinationChain
  · rw [ite_eq_left (hguard.2 hg), ite_eq_left hg]
    -- the guard says the destination is not L1: the pin's recovery restores on any layer
    obtain ⟨st₁, hreg₁, hrec⟩ := Contracts.NativeTokenVaultBase.AtomicRecoveryAcrossSettlementLayersL2
      cfg metadata s r out sl₂ hw hp hg.1
    have h₁₀ : st₁ = st₀ := Option.some.inj (hreg₁.symm.trans hreg)
    rw [hrec, h₁₀]
  · rw [ite_eq_right (fun h => hg (hguard.1 h)), ite_eq_right hg]

/-! ## Witnesses -/

open AccountingExample in
theorem HeadRunSatisfiable : Properties.HeadRunSatisfiable :=
  ⟨cfgEx, 100, _, ⟨0, 0⟩, 8, 6, 12, 13, cfgEx_fresh_inv 100,
    Relation.ReflTransGen.tail (Relation.ReflTransGen.tail (Relation.ReflTransGen.tail
      Relation.ReflTransGen.refl ⟨.initL2, rfl⟩) ⟨.initiate ⟨0, 10⟩ 8 6 4, rfl⟩)
      ⟨.finalize ⟨0, 0⟩ 8 6 2, rfl⟩,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    ⟨_, rfl⟩, by decide⟩

namespace LaterHeadsExample

open AccountingExample (cfgEx)

/-- After the heads' `initL2` and the vault's `registerNewTokenIfNeeded(5, 9)` of the base asset
`5`, which comes from chain `9`. -/
def headBaseRegSys : Sys :=
  ((execHead cfgEx (Sys.fresh 100) .initL2).bind fun s =>
    execHead cfgEx s (.registerNewToken 5)).getD (Sys.fresh 100)

open NativeEscrowExample in
/-- `NativeEscrowExample`'s composed run, with the heads' `initL2`: a direct vault balance, a legacy
first touch, a deposit, a direct transfer into the vault and a withdrawal. -/
theorem headEsc_reach₅ : HeadEscrowReach cfgEx 6 ⟨Sys.fresh 100, escTok₀⟩ escE₅ := by
  have s₁ : HeadEscrowStep cfgEx 6 ⟨Sys.fresh 100, escTok₀⟩ escE₁ :=
    HeadEscrowStep.tracker (e := ⟨Sys.fresh 100, escTok₀⟩) .initL2 (fun h => h) rfl
  have s₂ : HeadEscrowStep cfgEx 6 escE₁ escE₂ := HeadEscrowStep.registerLegacy (e := escE₁) rfl
  have s₃ : HeadEscrowStep cfgEx 6 escE₂ escE₃ :=
    HeadEscrowStep.nativeOut (e := escE₂) (st' := escOut.1) (tok' := escOut.2) 8 30 4 rfl
  have hw₃ := (EscrowInvariant cfgEx 6 _ _ (by decide) escE₀_inv esc_reach₃).ledger
  have ht : Contracts.BridgedStandardERC20.transfer escE₃.tok 30 1 2 =
      some (Contracts.BridgedStandardERC20.transferEffect escE₃.tok 30 1 2) :=
    escrow_transfer_eq_some.2 ⟨by decide, rfl⟩
  have hw₄ := (Contracts.BridgedStandardERC20.transfer_preserves_ledger hw₃ ht).1
  have s₄ : HeadEscrowStep cfgEx 6 escE₃ escE₄ :=
    HeadEscrowStep.token (e := escE₃)
      (tok' := Contracts.BridgedStandardERC20.transferEffect escE₃.tok 30 1 2) ⟨hw₄, by decide⟩
  have s₅ : HeadEscrowStep cfgEx 6 escE₄ escE₅ :=
    HeadEscrowStep.nativeIn (e := escE₄) (st' := escIn.1) (tok' := escIn.2) 8 40 3 rfl
  exact ((((Relation.ReflTransGen.single s₁).tail s₂).tail s₃).tail s₄).tail s₅

end LaterHeadsExample

open AccountingExample LaterHeadsExample in
theorem HeadBaseNeverLegacySatisfiable : Properties.HeadBaseNeverLegacySatisfiable :=
  ⟨cfgEx, 100, headBaseRegSys, _, _, ⟨0, 0⟩, 8, cfgEx_fresh_inv 100,
    Relation.ReflTransGen.tail (Relation.ReflTransGen.tail Relation.ReflTransGen.refl
      ⟨.initL2, rfl⟩) ⟨.registerNewToken 5, rfl⟩,
    by decide, by decide, rfl, rfl,
    Relation.ReflTransGen.tail (Relation.ReflTransGen.tail Relation.ReflTransGen.refl
      ⟨.initiateBase ⟨0, 0⟩ 8 1, rfl⟩) ⟨.finalizeBase ⟨0, 0⟩ cfgEx.baseTokenHolder 8 1, rfl⟩⟩

open NativeEscrowExample AccountingExample LaterHeadsExample in
theorem HeadNativeEscrowSatisfiable : Properties.HeadNativeEscrowSatisfiable :=
  ⟨cfgEx, 6, 100, escTok₀, escE₅, 8, 30, 40, 1, by decide, by decide, by decide, by decide,
    escE₀_inv, headEsc_reach₅, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

open Contracts.NativeTokenVaultBase Contracts.NativeTokenVaultBase.ResolutionExample
  Contracts.NativeTokenVaultBase.TrackerHooksExample in
theorem HeadRecoverySatisfiable : Properties.HeadRecoverySatisfiable :=
  ⟨l2Cfg 9, md0, l2State false 9 9, prepRequest 12, _, 7, _, stateWith_wf (by decide) 4 _, rfl,
    by decide, by decide, by decide, by decide, by decide, rfl,
    trackerHooks_ne_of_field (fun st : Storage => st.isAssetRegistered 3) (by decide)⟩

open Contracts.NativeTokenVaultBase Contracts.NativeTokenVaultBase.ResolutionExample
  Contracts.NativeTokenVaultBase.TrackerHooksExample in
theorem HeadGuardRejectsPinDivergence : Properties.HeadGuardRejectsPinDivergence :=
  ⟨l2Cfg 6, md0, l2State true 6 6, prepRequest 12, l2Out true 6 6,
    l2Rec 6 (l2Out true 6 6).state (l2Out true 6 6), stateWith_wf (by decide) 4 _, rfl, rfl, rfl,
    rfl, by decide, rfl,
    trackerHooks_ne_of_field
      (fun x : State L2Accounting => (x.accounting.st.interopInfo 3).totalWithdrawalsToL1.val)
      (by decide), rfl⟩

end Contracts.L2AssetTracker
