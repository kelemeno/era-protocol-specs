import EraSpec.Contracts.L2AssetTracker.Properties.HookOrdering
import EraSpec.Contracts.L2AssetTracker.Proofs.Accounting
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.TrackerHooks

/-! # Proofs: hook ordering and first-touch snapshots -/

namespace Contracts.L2AssetTracker

open Contracts.NativeTokenVaultBase (State Request Result prepare bridgeMint
  bridgeRecoverFailedTransfer ResolutionCall L2Accounting l2Hooks l2ResolutionHooks WellFormed Bytes)

/-! ## The bridged paths of the vault model -/

theorem runPath_of_hook {cfg : Config} {p : VaultPath} {st st' : Storage} {sl : ChainId}
    {tok tok' : Contracts.BridgedStandardERC20.State} {chain : ChainId} {a : AssetId}
    {account : Address} {amount : UInt256}
    (hh : pathHook cfg p st sl (tokenReads cfg tok) chain a amount = some st')
    (he : pathEffect cfg p tok account amount = some tok') :
    runPath cfg p st sl tok chain a account amount = some (st', tok') := by
  unfold runPath
  rw [hh, he]
  rfl

theorem HookPrecedesEffect : Properties.HookPrecedesEffect := by
  intro cfg metadata s hntv
  refine ⟨fun r out hw hp => ?_, fun c t h => ?_, fun c t h => ?_⟩
  · have hacc : (l2Hooks cfg metadata).account s.accounting s.token r.destinationChain r.assetId
        r.data.amount = some out.state.accounting :=
      Contracts.NativeTokenVaultBase.preparation_accounting hp
    have hburn := (Contracts.NativeTokenVaultBase.preparation_backed hw hp).1
    change (handleInitiateBridgingOnL2 cfg s.accounting.st s.accounting.sl (tokenReads cfg s.token)
      cfg.ntv r.destinationChain r.assetId r.data.amount (cfg.ntvOriginChainId r.assetId)).map
        (fun st => { s.accounting with st := st }) = some out.state.accounting at hacc
    rw [Option.map_eq_some_iff] at hacc
    obtain ⟨st', hst', hacc'⟩ := hacc
    rw [← hacc']
    exact runPath_of_hook hst' (by rw [← hntv] at hburn; exact hburn)
  · obtain ⟨_, _, hhook, hmint, _⟩ :=
      Contracts.NativeTokenVaultBase.BridgeMintExact L2Accounting _ s t c h
    change (handleFinalizeBridgingOnL2 cfg s.accounting.st s.accounting.sl (tokenReads cfg s.token)
      cfg.ntv c.chain c.assetId c.data.amount (cfg.ntvOriginChainId c.assetId)
      (cfg.ntvTokenAddress c.assetId)).map (fun st => { s.accounting with st := st }) =
        some t.accounting at hhook
    rw [Option.map_eq_some_iff] at hhook
    obtain ⟨st', hst', hacc'⟩ := hhook
    rw [← hacc']
    exact runPath_of_hook hst' (by rw [← hntv] at hmint; exact hmint)
  · obtain ⟨_, _, hhook, hmint, _⟩ :=
      Contracts.NativeTokenVaultBase.RecoverExact L2Accounting _ s t c h
    change (handleFinalizeBridgingOnL2 cfg s.accounting.st s.accounting.sl (tokenReads cfg s.token)
      cfg.ntv c.chain c.assetId c.data.amount (cfg.ntvOriginChainId c.assetId)
      (cfg.ntvTokenAddress c.assetId)).map (fun st => { s.accounting with st := st }) =
        some t.accounting at hhook
    rw [Option.map_eq_some_iff] at hhook
    obtain ⟨st', hst', hacc'⟩ := hhook
    rw [← hacc']
    exact runPath_of_hook hst' (by rw [← hntv] at hmint; exact hmint)

/-! ## First-touch snapshots -/

/-- The snapshot a first-touch registration of an unregistered asset writes. -/
theorem registerLegacyTokenIfNeeded_snapshot {cfg : Config} {st st₁ : Storage}
    {reads : TokenReads} {a : AssetId} {token : Address} (hr : st.isAssetRegistered a = false)
    (h : registerLegacyTokenIfNeeded cfg st reads a token = some st₁) :
    st₁.totalPreV31TotalSupply a =
      if Native cfg a then ⟨true, maxMinus reads.ntvBalance⟩ else ⟨true, reads.totalSupply⟩ := by
  rcases registerLegacyTokenIfNeeded_cases h with
    ⟨hr', _⟩ | ⟨_, _, _, ⟨hn, _, rfl⟩ | ⟨hn, rfl⟩⟩
  · rw [hr] at hr'; cases hr'
  · rw [ite_eq_left hn]; simp
  · rw [ite_eq_right hn]; simp

/-- What a path's hook does to an unregistered asset. -/
theorem pathHook_first_touch {cfg : Config} {p : VaultPath} {st st' : Storage} {sl : ChainId}
    {reads : TokenReads} {chain : ChainId} {a : AssetId} {amount : UInt256}
    (hr : st.isAssetRegistered a = false)
    (h : pathHook cfg p st sl reads chain a amount = some st') :
    st'.isAssetRegistered a = true ∧
    st'.totalPreV31TotalSupply a =
      if Native cfg a then ⟨true, maxMinus reads.ntvBalance⟩ else ⟨true, reads.totalSupply⟩ := by
  unfold pathHook at h
  cases hp : p.outbound with
  | true =>
    rw [hp, ite_eq_left rfl] at h
    unfold handleInitiateBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    obtain ⟨_, st₁, h₁, _, hreg', hsnap', _⟩ := initiateInner_spec h
    exact ⟨hreg', by rw [hsnap']; exact registerLegacyTokenIfNeeded_snapshot hr h₁⟩
  | false =>
    rw [hp, ite_eq_right (by decide)] at h
    unfold handleFinalizeBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    obtain ⟨st₁, h₁, _, hreg', hsnap', _⟩ := finalizeInner_spec h
    exact ⟨hreg', by rw [hsnap']; exact registerLegacyTokenIfNeeded_snapshot hr h₁⟩

theorem FirstTouchSnapshotIsPreOp : Properties.FirstTouchSnapshotIsPreOp := by
  intro cfg p st sl tok chain a account amount st' tok' hr h
  unfold runPath at h
  cases hh : pathHook cfg p st sl (tokenReads cfg tok) chain a amount with
  | none => rw [hh] at h; cases h
  | some st₁ =>
    rw [hh, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hpair⟩ := h
    cases hpair
    exact pathHook_first_touch hr hh

theorem SnapshotIndependentOfEntry : Properties.SnapshotIndependentOfEntry := by
  intro cfg p q st sl sl' tok chain chain' a account account' amount amount' st₁ st₂ tok₁ tok₂
    hr h₁ h₂
  rw [(FirstTouchSnapshotIsPreOp cfg p st sl tok chain a account amount st₁ tok₁ hr h₁).2,
    (FirstTouchSnapshotIsPreOp cfg q st sl' tok chain' a account' amount' st₂ tok₂ hr h₂).2]

/-! ## The base token -/

/-- Once `initL2` has run, every step keeps it so and keeps the base asset id. -/
theorem exec_keeps_base {cfg : Config} {sys sys' : Sys} {op : Op}
    (h : exec cfg sys op = some sys') (hg : sys.st.guardInitialized = true) :
    sys'.st.guardInitialized = true ∧ sys'.st.baseTokenAssetId = sys.st.baseTokenAssetId := by
  have flow : ∀ {st' : Storage} {x : AssetId}, Frame sys.st st' x →
      st'.guardInitialized = true ∧ st'.baseTokenAssetId = sys.st.baseTokenAssetId :=
    fun hf => ⟨hf.guard.trans hg, hf.base⟩
  cases op with
  | registerNewToken x =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold registerNewTokenIfNeeded at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    by_cases hx : sys.st.isAssetRegistered x = true
    · rw [ite_eq_left hx] at h; cases h; exact ⟨hg, rfl⟩
    rw [ite_eq_right hx] at h
    by_cases hc : cfg.ntvOriginChainId x = cfg.thisChain
    · rw [ite_eq_left hc] at h; cases h; exact ⟨hg, rfl⟩
    · rw [ite_eq_right hc] at h; cases h; exact ⟨hg, rfl⟩
  | registerBaseDuringUpgrade =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold registerBaseTokenDuringUpgrade at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    by_cases hx : sys.st.isAssetRegistered sys.st.baseTokenAssetId = true
    · rw [ite_eq_left hx] at h; cases h
    rw [ite_eq_right hx] at h
    cases h
    exact ⟨hg, rfl⟩
  | registerLegacy reads x =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    exact flow (registerLegacyTokenIfNeeded_frame (registerLegacyToken_eq h))
  | initiate reads toChain x amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleInitiateBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    exact flow (initiateInner_frame h)
  | initiateBase reads toChain amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleInitiateBaseTokenBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    exact flow (initiateInner_frame h)
  | finalize reads fromChain x amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleFinalizeBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    exact flow (finalizeInner_frame h)
  | finalizeBase reads caller fromChain amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleFinalizeBaseTokenBridgingOnL2 at h
    by_cases hc : caller ≠ cfg.baseTokenHolder ∧ caller ≠ cfg.l2BaseToken
    · rw [ite_eq_left hc] at h; cases h
    rw [ite_eq_right hc] at h
    by_cases h0 : amount = 0
    · rw [ite_eq_left h0] at h; cases h; exact ⟨hg, rfl⟩
    rw [ite_eq_right h0] at h
    by_cases hb : sys.st.baseTokenAssetId = 0
    · rw [ite_eq_left hb] at h; cases h
    rw [ite_eq_right hb] at h
    exact flow (finalizeInner_frame h)
  | backfill amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold backFillZKSyncOSBaseTokenV31MigrationData at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    by_cases h1 : sys.st.needBaseTokenTotalSupplyBackfill = false
    · rw [ite_eq_left h1] at h; cases h
    rw [ite_eq_right h1] at h
    by_cases h2 : sys.st.isAssetRegistered sys.st.baseTokenAssetId = false
    · rw [ite_eq_left h2] at h; cases h
    rw [ite_eq_right h2] at h
    by_cases h3 : (sys.st.totalPreV31TotalSupply sys.st.baseTokenAssetId).isSaved = false
    · rw [ite_eq_left h3] at h; cases h
    rw [ite_eq_right h3] at h
    by_cases h4 : (sys.st.totalPreV31TotalSupply sys.st.baseTokenAssetId).amount ≠ 0
    · rw [ite_eq_left h4] at h; cases h
    rw [ite_eq_right h4] at h
    cases h
    exact ⟨hg, rfl⟩
  | initL2 need =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold initL2 at h
    rw [ite_eq_left hg] at h
    cases h
  | setSettlementLayer c =>
    simp only [exec, Option.some.injEq] at h
    subst h
    exact ⟨hg, rfl⟩

theorem BaseNeverTakesLegacyPath : Properties.BaseNeverTakesLegacyPath := by
  intro cfg sys₀ sys hreach hg hr
  have hkeep : sys.st.guardInitialized = true ∧
      sys.st.baseTokenAssetId = sys₀.st.baseTokenAssetId := by
    induction hreach with
    | refl => exact ⟨hg, rfl⟩
    | tail _ hstep ih =>
      obtain ⟨op, hop⟩ := hstep
      obtain ⟨hg', hb'⟩ := exec_keeps_base hop ih.1
      exact ⟨hg', hb'.trans ih.2⟩
  have hreg := (RegistrationMonotone cfg).1 sys₀ sys _ hreach hr
  rw [← hkeep.2] at hreg
  exact ⟨hkeep.2, hreg, fun _ _ => registerLegacyTokenIfNeeded_of_registered hreg⟩

/-! ## Witnesses -/

namespace HookOrderingExample

/-- A bridged token of the vault `1` (asset `5`), with `10` units held by `30`. -/
def tokB : Contracts.BridgedStandardERC20.State :=
  ⟨⟨1, 77, 5⟩, fun a => if a = 30 then 10 else 0, 10⟩

/-- A native token (asset `6`) with `10` units at `30` and `10` held by the vault `1`. -/
def tokN : Contracts.BridgedStandardERC20.State :=
  ⟨⟨1, 78, 6⟩, fun a => if a = 30 then 10 else if a = 1 then 10 else 0, 20⟩

/-- After `initL2` and the upgrade registration of the base asset `5`. -/
def postGenesisSys : Sys :=
  ((exec AccountingExample.cfgEx (Sys.fresh 100) (.initL2 false)).bind fun s =>
    exec AccountingExample.cfgEx s .registerBaseDuringUpgrade).getD (Sys.fresh 100)

end HookOrderingExample

open AccountingExample HookOrderingExample in
theorem HookAfterEffectSkews : Properties.HookAfterEffectSkews :=
  ⟨cfgEx, Storage.fresh, 100, tokB, tokN, 8, 5, 6, 30, 1, _, _, _, _, _, _, _, _, by decide,
    by decide, by decide, rfl, rfl, by decide, by decide, by decide, ⟨_, rfl⟩, ⟨_, rfl⟩,
    by decide, by decide, rfl, rfl, by decide, by decide, by decide, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

open AccountingExample HookOrderingExample in
theorem FirstTouchSatisfiable : Properties.FirstTouchSatisfiable :=
  ⟨cfgEx, Storage.fresh, 100, tokB, tokN, 8, 5, 6, 30, 1, _, _, _, _, by decide, by decide,
    by decide, by decide, by decide, rfl, rfl, rfl, rfl⟩

open Contracts.NativeTokenVaultBase.ResolutionExample
  Contracts.NativeTokenVaultBase.TrackerHooksExample in
theorem HookPrecedesEffectSatisfiable : Properties.HookPrecedesEffectSatisfiable :=
  ⟨l2Cfg, md0, l2State true 9 9, prepRequest 12, _, mintCall, _, rfl,
    stateWith_wf (by decide) 4 _, rfl, rfl⟩

open AccountingExample HookOrderingExample in
theorem BaseNeverLegacySatisfiable : Properties.BaseNeverLegacySatisfiable :=
  ⟨cfgEx, postGenesisSys, _, _, ⟨0, 0⟩, 8, by decide, by decide, rfl, rfl,
    Relation.ReflTransGen.tail (Relation.ReflTransGen.tail Relation.ReflTransGen.refl
      ⟨.initiateBase ⟨0, 0⟩ 8 1, rfl⟩) ⟨.finalizeBase ⟨0, 0⟩ cfgEx.baseTokenHolder 8 1, rfl⟩⟩

end Contracts.L2AssetTracker
