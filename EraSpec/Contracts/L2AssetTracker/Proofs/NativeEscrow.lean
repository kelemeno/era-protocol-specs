import EraSpec.Contracts.L2AssetTracker.Properties.NativeEscrow
import EraSpec.Contracts.L2AssetTracker.Proofs.HookOrdering

/-! # Proofs: the chain balance of a native token and the vault's escrow of it -/

namespace Contracts.L2AssetTracker

open Contracts.BridgedStandardERC20 (WellFormed transfer transferEffect TransferAllowed)

/-! ## The token ledger -/

theorem escrow_transfer_eq_some {s t : Contracts.BridgedStandardERC20.State} {o r : Address}
    {amount : UInt256} :
    transfer s o r amount = some t ↔ TransferAllowed s o r amount ∧ t = transferEffect s o r amount := by
  unfold transfer
  split
  · rename_i hg
    exact ⟨fun h => ⟨hg, (Option.some.inj h).symm⟩, fun h => by rw [h.2]⟩
  · rename_i hg
    exact ⟨fun h => (by cases h), fun h => absurd h.1 hg⟩

/-- The balance of `x` after a transfer from `o` to `r`. -/
theorem escrow_transferEffect_balance (s : Contracts.BridgedStandardERC20.State) (o r x : Address)
    (amount : UInt256) :
    (transferEffect s o r amount).balances x =
      if x = r then (if r = o then s.balances o - amount.val else s.balances r) + amount.val
      else if x = o then s.balances o - amount.val else s.balances x := by
  unfold transferEffect
  by_cases hxr : x = r
  · subst hxr
    by_cases hro : x = o
    · subst hro; simp
    · simp [hro]
  · by_cases hxo : x = o
    · subst hxo; simp [hxr]
    · simp [hxr, hxo]

/-- Two distinct balances of a well-formed ledger fit in its supply. -/
theorem escrow_pair_le_supply {s : Contracts.BridgedStandardERC20.State} (hw : WellFormed s)
    {x y : Address} (hxy : x ≠ y) : s.balances x + s.balances y ≤ s.totalSupply := by
  rw [← hw.1, ← Finset.sum_pair hxy]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- A balance of a well-formed ledger is below `2^256`. -/
theorem escrow_balance_lt {s : Contracts.BridgedStandardERC20.State} (hw : WellFormed s)
    (x : Address) : s.balances x < UInt256.size :=
  (Contracts.BridgedStandardERC20.balance_bounded hw x).2

/-- The vault's balance as the tracker reads it is exact for a well-formed ledger. -/
theorem escrow_tokenReads_ntvBalance (cfg : Config) {tok : Contracts.BridgedStandardERC20.State}
    (hw : WellFormed tok) : (tokenReads cfg tok).ntvBalance.val = tok.balances cfg.ntv := by
  show ((tok.balances cfg.ntv : ℕ) : UInt256).val = tok.balances cfg.ntv
  rw [Fin.val_natCast]
  exact Nat.mod_eq_of_lt (escrow_balance_lt hw cfg.ntv)

/-! ## The two vault paths -/

theorem escrow_runPath_eq_some {cfg : Config} {p : VaultPath} {st st' : Storage} {sl : ChainId}
    {tok tok' : Contracts.BridgedStandardERC20.State} {chain : ChainId} {a : AssetId}
    {account : Address} {amount : UInt256} :
    runPath cfg p st sl tok chain a account amount = some (st', tok') ↔
      pathHook cfg p st sl (tokenReads cfg tok) chain a amount = some st' ∧
      pathEffect cfg p tok account amount = some tok' := by
  unfold runPath
  cases pathHook cfg p st sl (tokenReads cfg tok) chain a amount with
  | none => simp
  | some s₁ =>
    simp only [Option.map_eq_some_iff, Prod.mk.injEq, Option.some.injEq]
    constructor
    · rintro ⟨t, ht, rfl, rfl⟩
      exact ⟨rfl, ht⟩
    · rintro ⟨rfl, ht⟩
      exact ⟨tok', ht, rfl, rfl⟩

theorem escrow_pathHook_nativeOut (cfg : Config) (st : Storage) (sl : ChainId) (reads : TokenReads)
    (chain : ChainId) (a : AssetId) (amount : UInt256) :
    pathHook cfg .nativeOut st sl reads chain a amount =
      initiateInner cfg st sl reads chain a amount (cfg.ntvOriginChainId a) := by
  simp [pathHook, VaultPath.outbound, handleInitiateBridgingOnL2]

theorem escrow_pathHook_nativeIn (cfg : Config) (st : Storage) (sl : ChainId) (reads : TokenReads)
    (chain : ChainId) (a : AssetId) (amount : UInt256) :
    pathHook cfg .nativeIn st sl reads chain a amount =
      finalizeInner cfg st sl reads chain a amount (decide (cfg.ntvOriginChainId a = cfg.thisChain))
        (cfg.ntvTokenAddress a) := by
  simp [pathHook, VaultPath.outbound, handleFinalizeBridgingOnL2]

/-- A successful deposit is the transfer into the vault, which raises the vault's balance by
exactly the amount. -/
theorem escrow_depositFunds_eq_some {cfg : Config} {tok tok' : Contracts.BridgedStandardERC20.State}
    {account : Address} {amount : UInt256} (h : depositFunds cfg tok account amount = some tok') :
    transfer tok account cfg.ntv amount = some tok' ∧
    tok'.balances cfg.ntv = tok.balances cfg.ntv + amount.val := by
  unfold depositFunds at h
  cases ht : transfer tok account cfg.ntv amount with
  | none => rw [ht] at h; cases h
  | some t =>
    rw [ht] at h
    dsimp only at h
    split at h
    · rename_i hc
      cases h
      exact ⟨rfl, by omega⟩
    · cases h

/-- A funded deposit by someone other than the vault succeeds. -/
theorem escrow_depositFunds_of_funded {cfg : Config} {tok : Contracts.BridgedStandardERC20.State}
    {account : Address} {amount : UInt256} (hntv : cfg.ntv ≠ 0) (ha : account ≠ 0)
    (hne : account ≠ cfg.ntv) (hb : amount.val ≤ tok.balances account) :
    depositFunds cfg tok account amount = some (transferEffect tok account cfg.ntv amount) := by
  have ht : transfer tok account cfg.ntv amount = some (transferEffect tok account cfg.ntv amount) :=
    escrow_transfer_eq_some.2 ⟨⟨ha, hntv, hb⟩, rfl⟩
  have hbal : (transferEffect tok account cfg.ntv amount).balances cfg.ntv =
      tok.balances cfg.ntv + amount.val := by
    rw [escrow_transferEffect_balance, ite_eq_left rfl, ite_eq_right (Ne.symm hne)]
  unfold depositFunds
  rw [ht]
  dsimp only
  rw [ite_eq_left ⟨by omega, by omega⟩]

/-- A successful withdrawal leaves the vault at least its balance minus the amount. -/
theorem escrow_withdraw_balance {cfg : Config} {tok tok' : Contracts.BridgedStandardERC20.State}
    {account : Address} {amount : UInt256} (h : transfer tok cfg.ntv account amount = some tok') :
    tok.balances cfg.ntv - amount.val ≤ tok'.balances cfg.ntv := by
  obtain ⟨⟨_, _, hb⟩, rfl⟩ := escrow_transfer_eq_some.1 h
  rw [escrow_transferEffect_balance]
  by_cases hr : cfg.ntv = account
  · rw [ite_eq_left hr, ite_eq_left hr.symm]
    omega
  · rw [ite_eq_right hr, ite_eq_left rfl]

/-! ## The tracker part of a composed run -/

/-- One composed step is a tracker step or leaves the tracker alone. -/
theorem escrowStep_sys {cfg : Config} {a : AssetId} {e e' : EscrowSys}
    (h : EscrowStep cfg a e e') : e'.sys = e.sys ∨ Step cfg e.sys e'.sys := by
  cases h with
  | nativeOut chain account amount hp =>
    obtain ⟨hh, _⟩ := escrow_runPath_eq_some.1 hp
    refine Or.inr ⟨.initiate (tokenReads cfg e.tok) chain a amount, ?_⟩
    simp only [pathHook, VaultPath.outbound, ite_true] at hh
    simp [exec, hh]
  | nativeIn chain account amount hp =>
    obtain ⟨hh, _⟩ := escrow_runPath_eq_some.1 hp
    refine Or.inr ⟨.finalize (tokenReads cfg e.tok) chain a amount, ?_⟩
    simp only [pathHook, VaultPath.outbound, Bool.false_eq_true, ite_false] at hh
    simp [exec, hh]
  | registerLegacy h => exact Or.inr ⟨_, h⟩
  | tracker op _ h => exact Or.inr ⟨op, h⟩
  | token _ => exact Or.inl rfl

theorem EscrowRunIsTrackerRun : Properties.EscrowRunIsTrackerRun := by
  intro cfg a e₀ e h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    rcases escrowStep_sys hstep with heq | hs
    · rw [heq]; exact ih
    · exact ih.tail hs

/-! ## The escrow invariant -/

/-- After a first-touch registration that reads the token as it is, `MAX - chainBalance` is at
most the vault's balance: with equality if the call registered `a`, and by the invariant before if
`a` was registered already. -/
theorem escrow_register_escrowed {cfg : Config} {st st₁ : Storage}
    {tok : Contracts.BridgedStandardERC20.State} {a : AssetId} {token : Address}
    (hn : Native cfg a) (hw : WellFormed tok)
    (hesc : st.isAssetRegistered a = true →
      MAX_TOKEN_BALANCE.val - (st.chainBalance cfg.thisChain a).val ≤ tok.balances cfg.ntv)
    (h : registerLegacyTokenIfNeeded cfg st (tokenReads cfg tok) a token = some st₁) :
    MAX_TOKEN_BALANCE.val - (st₁.chainBalance cfg.thisChain a).val ≤ tok.balances cfg.ntv := by
  rcases registerLegacyTokenIfNeeded_cases h with
    ⟨hr, rfl⟩ | ⟨_, _, _, ⟨_, _, rfl⟩ | ⟨hn', _⟩⟩
  · exact hesc hr
  · have hb := escrow_tokenReads_ntvBalance cfg hw
    have hlt := escrow_balance_lt hw cfg.ntv
    simp only [markRegistered_chainBalance, setChainBalance_chainBalance, and_self, ite_true,
      maxMinus_val, hb, MAX_TOKEN_BALANCE_val]
    omega
  · exact absurd hn hn'

/-- A tracker call that does not touch `a`, when `a` is not the base asset, either leaves `a`'s
registration and chain balance alone or (`registerNewTokenIfNeeded(a)` on a native `a`) sets the
chain balance to `MAX`. -/
theorem escrow_exec_other {cfg : Config} {sys sys' : Sys} {op : Op} {a : AssetId}
    (hn : Native cfg a) (hop : ¬ op.TouchesAsset a) (hbase : sys.st.baseTokenAssetId ≠ a)
    (h : exec cfg sys op = some sys') :
    (sys'.st.isAssetRegistered a = true →
      sys.st.isAssetRegistered a = true ∧
        sys'.st.chainBalance cfg.thisChain a = sys.st.chainBalance cfg.thisChain a) ∨
    sys'.st.chainBalance cfg.thisChain a = MAX_TOKEN_BALANCE := by
  have viaFrame : ∀ {st' : Storage} {x : AssetId}, Frame sys.st st' x → x ≠ a →
      (st'.isAssetRegistered a = true → sys.st.isAssetRegistered a = true ∧
        st'.chainBalance cfg.thisChain a = sys.st.chainBalance cfg.thisChain a) := by
    intro st' x hf hx hr
    have hax : a ≠ x := fun h => hx h.symm
    exact ⟨by rw [← hf.reg a hax]; exact hr, hf.cb _ a hax⟩
  have same : ∀ {st' : Storage}, st'.isAssetRegistered = sys.st.isAssetRegistered →
      st'.chainBalance = sys.st.chainBalance →
      (st'.isAssetRegistered a = true → sys.st.isAssetRegistered a = true ∧
        st'.chainBalance cfg.thisChain a = sys.st.chainBalance cfg.thisChain a) := by
    intro st' hr hc h'
    rw [hr] at h'
    exact ⟨h', by rw [hc]⟩
  cases op with
  | registerNewToken b =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold registerNewTokenIfNeeded at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    by_cases hr : sys.st.isAssetRegistered b = true
    · rw [ite_eq_left hr] at h; cases h; exact Or.inl fun h => ⟨h, rfl⟩
    rw [ite_eq_right hr] at h
    by_cases hc : cfg.ntvOriginChainId b = cfg.thisChain
    · rw [ite_eq_left hc] at h
      cases h
      by_cases hb : b = a
      · subst hb
        right
        simp
      · exact Or.inl (viaFrame ((frame_setChainBalance _ _ _ _).trans (frame_markRegistered _ _ _)) hb)
    · rw [ite_eq_right hc] at h
      cases h
      by_cases hb : b = a
      · subst hb; exact absurd hn hc
      · exact Or.inl (viaFrame (frame_markRegistered _ _ _) hb)
  | registerBaseDuringUpgrade =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold registerBaseTokenDuringUpgrade at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    by_cases hr : sys.st.isAssetRegistered sys.st.baseTokenAssetId = true
    · rw [ite_eq_left hr] at h; cases h
    rw [ite_eq_right hr] at h
    cases h
    exact Or.inl (viaFrame (frame_markRegistered _ _ _) hbase)
  | registerLegacy reads b =>
    have hb : b ≠ a := hop
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    exact Or.inl (viaFrame (registerLegacyTokenIfNeeded_frame (registerLegacyToken_eq h)) hb)
  | initiate reads toChain b amount =>
    have hb : b ≠ a := hop
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleInitiateBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    exact Or.inl (viaFrame (initiateInner_frame h) hb)
  | initiateBase reads toChain amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleInitiateBaseTokenBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    exact Or.inl (viaFrame (initiateInner_frame h) hbase)
  | finalize reads fromChain b amount =>
    have hb : b ≠ a := hop
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleFinalizeBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    exact Or.inl (viaFrame (finalizeInner_frame h) hb)
  | finalizeBase reads caller fromChain amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleFinalizeBaseTokenBridgingOnL2 at h
    by_cases hc : caller ≠ cfg.baseTokenHolder ∧ caller ≠ cfg.l2BaseToken
    · rw [ite_eq_left hc] at h; cases h
    rw [ite_eq_right hc] at h
    by_cases h0 : amount = 0
    · rw [ite_eq_left h0] at h; cases h; exact Or.inl fun h => ⟨h, rfl⟩
    rw [ite_eq_right h0] at h
    by_cases hb : sys.st.baseTokenAssetId = 0
    · rw [ite_eq_left hb] at h; cases h
    rw [ite_eq_right hb] at h
    exact Or.inl (viaFrame (finalizeInner_frame h) hbase)
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
    exact Or.inl (same rfl rfl)
  | initL2 need =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold initL2 at h
    by_cases hg : sys.st.guardInitialized = true
    · rw [ite_eq_left hg] at h; cases h
    rw [ite_eq_right hg, ite_eq_right (not_not.2 rfl)] at h
    cases h
    exact Or.inl (same rfl rfl)
  | setSettlementLayer c =>
    simp only [exec, Option.some.injEq] at h
    subst h
    exact Or.inl fun h => ⟨h, rfl⟩

/-- **ONE COMPOSED STEP KEEPS THE INVARIANT.** -/
theorem escrowStep_inv {cfg : Config} {a : AssetId} {e e' : EscrowSys} (hn : Native cfg a)
    (hinv : EscrowInv cfg a e) (h : EscrowStep cfg a e e') : EscrowInv cfg a e' := by
  have hsys : Inv cfg e'.sys := by
    rcases escrowStep_sys h with heq | ⟨op, hop⟩
    · rw [heq]; exact hinv.inv
    · exact exec_inv hinv.inv hop
  cases h with
  | nativeOut chain account amount hp =>
    obtain ⟨hh, hd⟩ := escrow_runPath_eq_some.1 hp
    obtain ⟨htr, hbal⟩ := escrow_depositFunds_eq_some hd
    refine ⟨hsys, (Contracts.BridgedStandardERC20.transfer_preserves_ledger hinv.ledger htr).1,
      fun _ => ?_⟩
    rw [escrow_pathHook_nativeOut] at hh
    obtain ⟨_, st₁, h₁, _, _, _, _, hdec, _⟩ := initiateInner_spec hh
    have h₁' := escrow_register_escrowed hn hinv.ledger hinv.escrowed h₁
    obtain ⟨hle, hcb⟩ := hdec hn
    have hmax := val_le_max (st₁.chainBalance cfg.thisChain a)
    show MAX_TOKEN_BALANCE.val - _ ≤ _
    rw [hcb, hbal]
    omega
  | nativeIn chain account amount hp =>
    obtain ⟨hh, hw⟩ := escrow_runPath_eq_some.1 hp
    have hbal := escrow_withdraw_balance hw
    refine ⟨hsys, (Contracts.BridgedStandardERC20.transfer_preserves_ledger hinv.ledger hw).1,
      fun _ => ?_⟩
    rw [escrow_pathHook_nativeIn] at hh
    obtain ⟨st₁, h₁, _, _, _, _, hinc, _⟩ := finalizeInner_spec hh
    have h₁' := escrow_register_escrowed hn hinv.ledger hinv.escrowed h₁
    obtain ⟨_, hcb⟩ := hinc (decide_eq_true hn)
    dsimp only
    rw [hcb]
    omega
  | registerLegacy hreg =>
    refine ⟨hsys, hinv.ledger, fun _ => ?_⟩
    simp only [exec, Option.map_eq_some_iff] at hreg
    obtain ⟨st', hreg, rfl⟩ := hreg
    exact escrow_register_escrowed hn hinv.ledger hinv.escrowed (registerLegacyToken_eq hreg)
  | tracker op hop hexec =>
    refine ⟨hsys, hinv.ledger, fun hr => ?_⟩
    have hbase : e.sys.st.baseTokenAssetId ≠ a := fun hb => hinv.inv.baseNotNative.2 (hb ▸ hn)
    rcases escrow_exec_other hn hop hbase hexec with hsame | hmax
    · obtain ⟨hr₀, hcb⟩ := hsame hr
      show MAX_TOKEN_BALANCE.val - _ ≤ _
      rw [hcb]
      exact hinv.escrowed hr₀
    · show MAX_TOKEN_BALANCE.val - _ ≤ _
      rw [hmax]
      simp
  | token hmove =>
    exact ⟨hinv.inv, hmove.1, fun hr => (hinv.escrowed hr).trans hmove.2⟩

theorem EscrowInvariant : Properties.EscrowInvariant := by
  intro cfg a e₀ e hn hinv h
  induction h with
  | refl => exact hinv
  | tail _ hstep ih => exact escrowStep_inv hn ih hstep

theorem FreshEscrowSatisfiesInv : Properties.FreshEscrowSatisfiesInv := by
  intro cfg a sl tok hbase h0 hw
  exact ⟨FreshTrackerSatisfiesInv cfg sl hbase h0, hw, fun h => by cases h⟩

/-! ## The headlines -/

theorem NativeReleasesAreEscrowed : Properties.NativeReleasesAreEscrowed := by
  intro cfg a e₀ e hn hinv h hr
  have hesc := (EscrowInvariant cfg a e₀ e hn hinv h).escrowed hr
  obtain ⟨hsent, _, _⟩ :=
    NativeSentinel cfg e₀.sys e.sys a hinv.inv (EscrowRunIsTrackerRun cfg a e₀ e h) hr hn
  have hcb := val_le_max (e.sys.st.chainBalance cfg.thisChain a)
  have hsn := val_le_max (e.sys.st.totalPreV31TotalSupply a).amount
  exact ⟨hesc, by omega⟩

theorem NativeInboundFailsOnlyAtTheHook : Properties.NativeInboundFailsOnlyAtTheHook := by
  intro cfg a e₀ e chain account amount hn hinv h hntv hacc
  have hinvE := EscrowInvariant cfg a e₀ e hn hinv h
  constructor
  · rintro ⟨⟨st', tok'⟩, hp⟩
    exact ⟨st', (escrow_runPath_eq_some.1 hp).1⟩
  · rintro ⟨st', hh⟩
    have hh' := hh
    rw [escrow_pathHook_nativeIn] at hh'
    obtain ⟨st₁, h₁, _, _, _, _, hinc, _⟩ := finalizeInner_spec hh'
    have h₁' := escrow_register_escrowed hn hinvE.ledger hinvE.escrowed h₁
    obtain ⟨hlt, _⟩ := hinc (decide_eq_true hn)
    have hle : amount.val ≤ e.tok.balances cfg.ntv := by
      have := MAX_TOKEN_BALANCE_val
      omega
    exact ⟨(st', transferEffect e.tok cfg.ntv account amount),
      escrow_runPath_eq_some.2 ⟨hh, escrow_transfer_eq_some.2 ⟨⟨hntv, hacc, hle⟩, rfl⟩⟩⟩

/-- The inbound hook of the vault path is the tracker's `.finalize` call. -/
theorem escrow_pathHook_nativeIn_iff_exec {cfg : Config} {sys : Sys} {reads : TokenReads}
    {chain : ChainId} {a : AssetId} {amount : UInt256} :
    (∃ st', pathHook cfg .nativeIn sys.st sys.sl reads chain a amount = some st') ↔
      ∃ sys', exec cfg sys (.finalize reads chain a amount) = some sys' := by
  simp only [pathHook, VaultPath.outbound, Bool.false_eq_true, ite_false, exec]
  rw [exists_map_eq_some]

theorem NativeInboundIffCap : Properties.NativeInboundIffCap := by
  intro cfg a e₀ e chain account amount hn hinv h hr hntv hacc hoff
  rw [NativeInboundFailsOnlyAtTheHook cfg a e₀ e chain account amount hn hinv h hntv hacc,
    escrow_pathHook_nativeIn_iff_exec]
  exact InflowOverflowIsCap cfg e₀.sys e.sys (tokenReads cfg e.tok) chain a amount hinv.inv
    (EscrowRunIsTrackerRun cfg a e₀ e h) hr hn hoff

theorem FundedNativeOutboundSucceeds : Properties.FundedNativeOutboundSucceeds := by
  intro cfg a e₀ e chain account amount hn hinv h h0 htok hntv hacc hne hfund hctr
  have hinvE := EscrowInvariant cfg a e₀ e hn hinv h
  -- the first-touch registration, if any, succeeds
  obtain ⟨st₁, h₁⟩ : ∃ st₁, registerLegacyTokenIfNeeded cfg e.sys.st (tokenReads cfg e.tok) a
      (cfg.ntvTokenAddress a) = some st₁ := by
    by_cases hr : e.sys.st.isAssetRegistered a = true
    · exact ⟨_, registerLegacyTokenIfNeeded_of_registered hr⟩
    · have hr' : e.sys.st.isAssetRegistered a = false := by simpa using hr
      have hcb0 := (hinvE.inv.unregisteredQuiet a hr').2.2
      have horig : cfg.ntvOriginChainId a ≠ 0 := by rw [hn]; exact h0
      refine ⟨markRegistered (setChainBalance e.sys.st cfg.thisChain a
        (maxMinus (tokenReads cfg e.tok).ntvBalance)) a
        ⟨true, maxMinus (tokenReads cfg e.tok).ntvBalance⟩, ?_⟩
      unfold registerLegacyTokenIfNeeded registerLegacyTokenInner
      rw [ite_eq_right hr, ite_eq_right horig, ite_eq_right htok, ite_eq_left hn,
        ite_eq_right (not_not.2 hcb0)]
  have h₁' := escrow_register_escrowed hn hinvE.ledger hinvE.escrowed h₁
  have hpair := escrow_pair_le_supply hinvE.ledger hne
  have hsup := hinvE.ledger.2.1
  have hmax := MAX_TOKEN_BALANCE_val
  have hle : amount.val ≤ (st₁.chainBalance cfg.thisChain a).val := by omega
  -- the hook succeeds
  obtain ⟨v, hv, hvval⟩ := checkedSub_some_of_le hle
  have hdec : decreaseChainBalance st₁ cfg.thisChain a amount =
      some (setChainBalance st₁ cfg.thisChain a v) :=
    decreaseChainBalance_eq_some.2 ⟨v, hle, hvval, rfl⟩
  have hinfo : (setChainBalance st₁ cfg.thisChain a v).interopInfo = e.sys.st.interopInfo := by
    rw [setChainBalance_interopInfo, registerLegacyTokenIfNeeded_info h₁]
  obtain ⟨st', hh⟩ : ∃ st', initiateInner cfg e.sys.st e.sys.sl (tokenReads cfg e.tok) chain a
      amount (cfg.ntvOriginChainId a) = some st' := by
    have hn' : cfg.ntvOriginChainId a = cfg.thisChain := hn
    rw [initiateInner_eq, ite_eq_right htok, h₁, Option.bind_some, ite_eq_left hn', hdec,
      Option.bind_some]
    by_cases hc : chain = e.sys.st.l1ChainId ∧ e.sys.sl = e.sys.st.l1ChainId
    · rw [ite_eq_left hc]
      have hfit := hctr hc
      rw [← hinfo] at hfit
      obtain ⟨w, hw, hwval⟩ := checkedAdd_some_of_lt hfit
      exact ⟨_, addWithdrawalToL1_eq_some.2 ⟨w, hfit, hwval, rfl⟩⟩
    · rw [ite_eq_right hc]
      exact ⟨_, rfl⟩
  exact ⟨(st', transferEffect e.tok account cfg.ntv amount),
    escrow_runPath_eq_some.2 ⟨by rw [escrow_pathHook_nativeOut]; exact hh,
      escrow_depositFunds_of_funded hntv hacc hne hfund⟩⟩

/-! ## Witnesses -/

namespace NativeEscrowExample

open AccountingExample (cfgEx)
open Contracts.BridgedStandardERC20 (mintEffect burnEffect empty)

/-- The empty ledger of the token of asset `6` (minter `99`). -/
def escTokEmpty : Contracts.BridgedStandardERC20.State := empty ⟨99, 0, 6⟩

theorem escTokEmpty_wf : WellFormed escTokEmpty := by
  refine ⟨Finset.sum_const_zero, ?_, rfl⟩
  norm_num [escTokEmpty, empty, UInt256.size]

/-- Minting by the token's own minter keeps the ledger well-formed. -/
theorem escMint_wf {s : Contracts.BridgedStandardERC20.State} (hw : WellFormed s) (x : Address)
    (amount : UInt256) (hm : Contracts.BridgedStandardERC20.MintAllowed s 99 x amount) :
    WellFormed (mintEffect s x amount) := by
  have h : Contracts.BridgedStandardERC20.mint s 99 x amount = some (mintEffect s x amount) := by
    unfold Contracts.BridgedStandardERC20.mint
    rw [ite_eq_left hm]
  exact Contracts.BridgedStandardERC20.mint_preserves_ledger hw h

/-- The token of asset `6` (native here under `cfgEx`, whose vault is `1`): `10` units at the
vault, sent there directly before the tracker registered the asset, and `10` at holder `30`. -/
def escTok₀ : Contracts.BridgedStandardERC20.State := mintEffect (mintEffect escTokEmpty 1 10) 30 10

theorem escTok₀_wf : WellFormed escTok₀ :=
  escMint_wf (escMint_wf escTokEmpty_wf 1 10 (by decide)) 30 10 (by decide)

/-- After `initL2` (L1 is chain `100`, the chain settles on `100`). -/
def escE₁ : EscrowSys :=
  ⟨(exec cfgEx (Sys.fresh 100) (.initL2 false)).getD (Sys.fresh 100), escTok₀⟩

/-- After anyone's `registerLegacyToken(6)`, reading the vault's balance `10`. -/
def escE₂ : EscrowSys :=
  ⟨(exec cfgEx escE₁.sys (.registerLegacy (tokenReads cfgEx escTok₀) 6)).getD escE₁.sys, escTok₀⟩

/-- The outbound native path: holder `30` moves `4` towards chain `8`. -/
def escOut : Storage × Contracts.BridgedStandardERC20.State :=
  (runPath cfgEx .nativeOut escE₂.sys.st escE₂.sys.sl escE₂.tok 8 6 30 4).getD
    (escE₂.sys.st, escE₂.tok)

def escE₃ : EscrowSys :=
  ⟨{ escE₂.sys with st := escOut.1, audit := escE₂.sys.audit.addOut 6 4 }, escOut.2⟩

/-- Holder `30` sends `2` straight to the vault. -/
def escE₄ : EscrowSys := ⟨escE₃.sys, transferEffect escE₃.tok 30 1 2⟩

/-- The inbound native path: `3` from chain `8` to receiver `40`. -/
def escIn : Storage × Contracts.BridgedStandardERC20.State :=
  (runPath cfgEx .nativeIn escE₄.sys.st escE₄.sys.sl escE₄.tok 8 6 40 3).getD
    (escE₄.sys.st, escE₄.tok)

def escE₅ : EscrowSys :=
  ⟨{ escE₄.sys with st := escIn.1, audit := escE₄.sys.audit.addIn 6 3 }, escIn.2⟩

theorem escE₀_inv : EscrowInv cfgEx 6 ⟨Sys.fresh 100, escTok₀⟩ :=
  FreshEscrowSatisfiesInv cfgEx 6 100 escTok₀ (by decide) (by decide) escTok₀_wf

theorem esc_reach₃ : EscrowReach cfgEx 6 ⟨Sys.fresh 100, escTok₀⟩ escE₃ := by
  have s₁ : EscrowStep cfgEx 6 ⟨Sys.fresh 100, escTok₀⟩ escE₁ :=
    EscrowStep.tracker (e := ⟨Sys.fresh 100, escTok₀⟩) (.initL2 false) (fun h => h) rfl
  have s₂ : EscrowStep cfgEx 6 escE₁ escE₂ := EscrowStep.registerLegacy (e := escE₁) rfl
  have s₃ : EscrowStep cfgEx 6 escE₂ escE₃ :=
    EscrowStep.nativeOut (e := escE₂) (st' := escOut.1) (tok' := escOut.2) 8 30 4 rfl
  exact ((Relation.ReflTransGen.single s₁).tail s₂).tail s₃

theorem esc_reach₅ : EscrowReach cfgEx 6 ⟨Sys.fresh 100, escTok₀⟩ escE₅ := by
  have hw₃ := (EscrowInvariant cfgEx 6 _ _ (by decide) escE₀_inv esc_reach₃).ledger
  have ht : transfer escE₃.tok 30 1 2 = some (transferEffect escE₃.tok 30 1 2) :=
    escrow_transfer_eq_some.2 ⟨by decide, rfl⟩
  have hw₄ := (Contracts.BridgedStandardERC20.transfer_preserves_ledger hw₃ ht).1
  have s₄ : EscrowStep cfgEx 6 escE₃ escE₄ :=
    EscrowStep.token (e := escE₃) (tok' := transferEffect escE₃.tok 30 1 2) ⟨hw₄, by decide⟩
  have s₅ : EscrowStep cfgEx 6 escE₄ escE₅ :=
    EscrowStep.nativeIn (e := escE₄) (st' := escIn.1) (tok' := escIn.2) 8 40 3 rfl
  exact (esc_reach₃.tail s₄).tail s₅

/-- The countermodel's token: `10` units at holder `30`, nothing at the vault. -/
def cmTok₀ : Contracts.BridgedStandardERC20.State := mintEffect escTokEmpty 30 10

theorem cmTok₀_wf : WellFormed cmTok₀ := escMint_wf escTokEmpty_wf 30 10 (by decide)

/-- After `initL2`. -/
def cmE₁ : EscrowSys :=
  ⟨(exec cfgEx (Sys.fresh 100) (.initL2 false)).getD (Sys.fresh 100), cmTok₀⟩

/-- After the vault's `registerNewTokenIfNeeded(6, 7)`: chain balance `MAX`. -/
def cmE₂ : EscrowSys := ⟨(exec cfgEx cmE₁.sys (.registerNewToken 6)).getD cmE₁.sys, cmTok₀⟩

/-- Holder `30` moves `5` out towards chain `8`. -/
def cmOut : Storage × Contracts.BridgedStandardERC20.State :=
  (runPath cfgEx .nativeOut cmE₂.sys.st cmE₂.sys.sl cmE₂.tok 8 6 30 5).getD
    (cmE₂.sys.st, cmE₂.tok)

def cmE₃ : EscrowSys :=
  ⟨{ cmE₂.sys with st := cmOut.1, audit := cmE₂.sys.audit.addOut 6 5 }, cmOut.2⟩

theorem cm_reach₃ : EscrowReach cfgEx 6 ⟨Sys.fresh 100, cmTok₀⟩ cmE₃ := by
  have s₁ : EscrowStep cfgEx 6 ⟨Sys.fresh 100, cmTok₀⟩ cmE₁ :=
    EscrowStep.tracker (e := ⟨Sys.fresh 100, cmTok₀⟩) (.initL2 false) (fun h => h) rfl
  have s₂ : EscrowStep cfgEx 6 cmE₁ cmE₂ :=
    EscrowStep.tracker (e := cmE₁) (.registerNewToken 6) (fun h => h) rfl
  have s₃ : EscrowStep cfgEx 6 cmE₂ cmE₃ :=
    EscrowStep.nativeOut (e := cmE₂) (st' := cmOut.1) (tok' := cmOut.2) 8 30 5 rfl
  exact ((Relation.ReflTransGen.single s₁).tail s₂).tail s₃

end NativeEscrowExample

open NativeEscrowExample AccountingExample in
theorem EscrowNeedsVaultOnlyOutflow : Properties.EscrowNeedsVaultOnlyOutflow := by
  have hinv₀ : EscrowInv cfgEx 6 ⟨Sys.fresh 100, cmTok₀⟩ :=
    FreshEscrowSatisfiesInv cfgEx 6 100 cmTok₀ (by decide) (by decide) cmTok₀_wf
  have hw₃ := (EscrowInvariant cfgEx 6 _ _ (by decide) hinv₀ cm_reach₃).ledger
  -- the token itself burns the vault's `5`: the vault's balance falls, the ledger stays well-formed
  have hb : Contracts.BridgedStandardERC20.burn cmE₃.tok 99 1 5 =
      some (Contracts.BridgedStandardERC20.burnEffect cmE₃.tok 1 5) := by
    unfold Contracts.BridgedStandardERC20.burn
    rw [ite_eq_left (by decide)]
  have hw' := (Contracts.BridgedStandardERC20.burn_preserves_ledger hw₃ hb)
  exact ⟨cfgEx, 6, _, cmE₃, Contracts.BridgedStandardERC20.burnEffect cmE₃.tok 1 5, 8, 40, 5, _,
    by decide, hinv₀, cm_reach₃,
    by decide, by decide, by decide, by decide, hw', by decide, rfl, by decide⟩

open NativeEscrowExample AccountingExample in
theorem NativeEscrowSatisfiable : Properties.NativeEscrowSatisfiable :=
  ⟨cfgEx, 6, 100, escTok₀, escE₅, 8, 30, 40, 1, by decide, by decide, by decide, by decide,
    escE₀_inv, esc_reach₅, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

end Contracts.L2AssetTracker
