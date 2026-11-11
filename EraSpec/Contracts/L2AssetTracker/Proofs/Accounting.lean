import EraSpec.Contracts.L2AssetTracker.Properties.Accounting

/-! # Proofs: the L2 asset tracker's accounting -/

namespace Contracts.L2AssetTracker

/-! ## Checked arithmetic -/

theorem MAX_TOKEN_BALANCE_val : MAX_TOKEN_BALANCE.val = UInt256.size - 1 := rfl

theorem maxMinus_val (x : UInt256) : (maxMinus x).val = MAX_TOKEN_BALANCE.val - x.val := rfl

theorem val_le_max (x : UInt256) : x.val ≤ MAX_TOKEN_BALANCE.val := by
  have := x.isLt
  rw [MAX_TOKEN_BALANCE_val]
  omega

theorem checkedAdd_eq_some {a b c : UInt256} :
    checkedAdd a b = some c ↔ a.val + b.val < UInt256.size ∧ c.val = a.val + b.val := by
  unfold checkedAdd
  split
  · rename_i hlt
    constructor
    · intro h
      exact ⟨hlt, by rw [← Option.some.inj h]⟩
    · rintro ⟨_, hc⟩
      exact congrArg some (Fin.ext hc.symm)
  · rename_i hlt
    constructor
    · intro h
      cases h
    · rintro ⟨h, _⟩
      exact absurd h hlt

theorem checkedAdd_eq_none {a b : UInt256} :
    checkedAdd a b = none ↔ UInt256.size ≤ a.val + b.val := by
  unfold checkedAdd
  split
  · rename_i hlt
    constructor
    · intro h
      cases h
    · intro h
      omega
  · rename_i hlt
    exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem checkedSub_eq_some {a b c : UInt256} :
    checkedSub a b = some c ↔ b.val ≤ a.val ∧ c.val = a.val - b.val := by
  unfold checkedSub
  split
  · rename_i hle
    constructor
    · intro h
      exact ⟨hle, by rw [← Option.some.inj h]⟩
    · rintro ⟨_, hc⟩
      exact congrArg some (Fin.ext hc.symm)
  · rename_i hle
    constructor
    · intro h
      cases h
    · rintro ⟨h, _⟩
      exact absurd h hle

theorem checkedSub_eq_none {a b : UInt256} : checkedSub a b = none ↔ a.val < b.val := by
  unfold checkedSub
  split
  · rename_i hle
    constructor
    · intro h
      cases h
    · intro h
      omega
  · rename_i hle
    exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem checkedAdd_some_of_lt {a b : UInt256} (h : a.val + b.val < UInt256.size) :
    ∃ c, checkedAdd a b = some c ∧ c.val = a.val + b.val :=
  ⟨⟨a.val + b.val, h⟩, checkedAdd_eq_some.2 ⟨h, rfl⟩, rfl⟩

theorem checkedSub_some_of_le {a b : UInt256} (h : b.val ≤ a.val) :
    ∃ c, checkedSub a b = some c ∧ c.val = a.val - b.val :=
  ⟨⟨a.val - b.val, by have := a.isLt; omega⟩, checkedSub_eq_some.2 ⟨h, rfl⟩, rfl⟩

/-- Adding then subtracting the same amount, both checked, is the identity. -/
theorem checkedSub_of_checkedAdd {a b c : UInt256} (h : checkedAdd a b = some c) :
    checkedSub c b = some a := by
  obtain ⟨_, hc⟩ := checkedAdd_eq_some.1 h
  exact checkedSub_eq_some.2 ⟨by omega, by omega⟩

/-- Subtracting then adding the same amount, both checked, is the identity. -/
theorem checkedAdd_of_checkedSub {a b c : UInt256} (h : checkedSub a b = some c) :
    checkedAdd c b = some a := by
  obtain ⟨hle, hc⟩ := checkedSub_eq_some.1 h
  have := a.isLt
  exact checkedAdd_eq_some.2 ⟨by omega, by omega⟩

/-! ## The storage writes -/

@[simp] theorem setChainBalance_chainBalance (st : Storage) (c : ChainId) (a : AssetId)
    (v : UInt256) (c' : ChainId) (b : AssetId) :
    (setChainBalance st c a v).chainBalance c' b =
      if c' = c ∧ b = a then v else st.chainBalance c' b := by
  unfold setChainBalance
  by_cases hc : c' = c
  · subst hc
    by_cases hb : b = a
    · subst hb; simp
    · simp [hb]
  · simp [hc]

@[simp] theorem setChainBalance_isAssetRegistered (st : Storage) (c a v) :
    (setChainBalance st c a v).isAssetRegistered = st.isAssetRegistered := rfl
@[simp] theorem setChainBalance_totalPreV31 (st : Storage) (c a v) :
    (setChainBalance st c a v).totalPreV31TotalSupply = st.totalPreV31TotalSupply := rfl
@[simp] theorem setChainBalance_interopInfo (st : Storage) (c a v) :
    (setChainBalance st c a v).interopInfo = st.interopInfo := rfl
@[simp] theorem setChainBalance_l1ChainId (st : Storage) (c a v) :
    (setChainBalance st c a v).l1ChainId = st.l1ChainId := rfl
@[simp] theorem setChainBalance_baseTokenAssetId (st : Storage) (c a v) :
    (setChainBalance st c a v).baseTokenAssetId = st.baseTokenAssetId := rfl
@[simp] theorem setChainBalance_need (st : Storage) (c a v) :
    (setChainBalance st c a v).needBaseTokenTotalSupplyBackfill =
      st.needBaseTokenTotalSupplyBackfill := rfl
@[simp] theorem setChainBalance_guard (st : Storage) (c a v) :
    (setChainBalance st c a v).guardInitialized = st.guardInitialized := rfl

@[simp] theorem markRegistered_isAssetRegistered (st : Storage) (a : AssetId)
    (snap : SavedTotalSupply) (b : AssetId) :
    (markRegistered st a snap).isAssetRegistered b = if b = a then true else st.isAssetRegistered b := by
  unfold markRegistered
  by_cases hb : b = a
  · subst hb; simp
  · simp [hb]

@[simp] theorem markRegistered_totalPreV31 (st : Storage) (a : AssetId) (snap : SavedTotalSupply)
    (b : AssetId) :
    (markRegistered st a snap).totalPreV31TotalSupply b =
      if b = a then snap else st.totalPreV31TotalSupply b := by
  unfold markRegistered
  by_cases hb : b = a
  · subst hb; simp
  · simp [hb]

@[simp] theorem markRegistered_chainBalance (st : Storage) (a snap) :
    (markRegistered st a snap).chainBalance = st.chainBalance := rfl
@[simp] theorem markRegistered_interopInfo (st : Storage) (a snap) :
    (markRegistered st a snap).interopInfo = st.interopInfo := rfl
@[simp] theorem markRegistered_l1ChainId (st : Storage) (a snap) :
    (markRegistered st a snap).l1ChainId = st.l1ChainId := rfl
@[simp] theorem markRegistered_baseTokenAssetId (st : Storage) (a snap) :
    (markRegistered st a snap).baseTokenAssetId = st.baseTokenAssetId := rfl
@[simp] theorem markRegistered_need (st : Storage) (a snap) :
    (markRegistered st a snap).needBaseTokenTotalSupplyBackfill =
      st.needBaseTokenTotalSupplyBackfill := rfl
@[simp] theorem markRegistered_guard (st : Storage) (a snap) :
    (markRegistered st a snap).guardInitialized = st.guardInitialized := rfl

@[simp] theorem setInterop_interopInfo (st : Storage) (a : AssetId) (info : InteropL2Info)
    (b : AssetId) :
    (setInterop st a info).interopInfo b = if b = a then info else st.interopInfo b := by
  unfold setInterop
  by_cases hb : b = a
  · subst hb; simp
  · simp [hb]

@[simp] theorem setInterop_chainBalance (st : Storage) (a info) :
    (setInterop st a info).chainBalance = st.chainBalance := rfl
@[simp] theorem setInterop_isAssetRegistered (st : Storage) (a info) :
    (setInterop st a info).isAssetRegistered = st.isAssetRegistered := rfl
@[simp] theorem setInterop_totalPreV31 (st : Storage) (a info) :
    (setInterop st a info).totalPreV31TotalSupply = st.totalPreV31TotalSupply := rfl
@[simp] theorem setInterop_l1ChainId (st : Storage) (a info) :
    (setInterop st a info).l1ChainId = st.l1ChainId := rfl
@[simp] theorem setInterop_baseTokenAssetId (st : Storage) (a info) :
    (setInterop st a info).baseTokenAssetId = st.baseTokenAssetId := rfl
@[simp] theorem setInterop_need (st : Storage) (a info) :
    (setInterop st a info).needBaseTokenTotalSupplyBackfill =
      st.needBaseTokenTotalSupplyBackfill := rfl
@[simp] theorem setInterop_guard (st : Storage) (a info) :
    (setInterop st a info).guardInitialized = st.guardInitialized := rfl

@[simp] theorem Audit.addOut_outflow (au : Audit) (a : AssetId) (amount : UInt256) (b : AssetId) :
    (au.addOut a amount).outflow b = if b = a then au.outflow a + amount.val else au.outflow b := by
  unfold Audit.addOut
  by_cases hb : b = a
  · subst hb; simp
  · simp [hb]

@[simp] theorem Audit.addOut_inflow (au : Audit) (a amount) :
    (au.addOut a amount).inflow = au.inflow := rfl

@[simp] theorem Audit.addIn_inflow (au : Audit) (a : AssetId) (amount : UInt256) (b : AssetId) :
    (au.addIn a amount).inflow b = if b = a then au.inflow a + amount.val else au.inflow b := by
  unfold Audit.addIn
  by_cases hb : b = a
  · subst hb; simp
  · simp [hb]

@[simp] theorem Audit.addIn_outflow (au : Audit) (a amount) :
    (au.addIn a amount).outflow = au.outflow := rfl

/-! ## The frame: what a write at one asset leaves alone -/

/-- `st'` agrees with `st` everywhere except at asset `x`. -/
structure Frame (st st' : Storage) (x : AssetId) : Prop where
  reg : ∀ b, b ≠ x → st'.isAssetRegistered b = st.isAssetRegistered b
  cb : ∀ c b, b ≠ x → st'.chainBalance c b = st.chainBalance c b
  snap : ∀ b, b ≠ x → st'.totalPreV31TotalSupply b = st.totalPreV31TotalSupply b
  info : ∀ b, b ≠ x → st'.interopInfo b = st.interopInfo b
  l1 : st'.l1ChainId = st.l1ChainId
  base : st'.baseTokenAssetId = st.baseTokenAssetId
  need : st'.needBaseTokenTotalSupplyBackfill = st.needBaseTokenTotalSupplyBackfill
  guard : st'.guardInitialized = st.guardInitialized

theorem Frame.refl (st : Storage) (x : AssetId) : Frame st st x :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Frame.trans {st₁ st₂ st₃ : Storage} {x : AssetId} (h₁ : Frame st₁ st₂ x)
    (h₂ : Frame st₂ st₃ x) : Frame st₁ st₃ x :=
  ⟨fun b hb => (h₂.reg b hb).trans (h₁.reg b hb), fun c b hb => (h₂.cb c b hb).trans (h₁.cb c b hb),
    fun b hb => (h₂.snap b hb).trans (h₁.snap b hb), fun b hb => (h₂.info b hb).trans (h₁.info b hb),
    h₂.l1.trans h₁.l1, h₂.base.trans h₁.base, h₂.need.trans h₁.need, h₂.guard.trans h₁.guard⟩

theorem frame_setChainBalance (st : Storage) (c : ChainId) (x : AssetId) (v : UInt256) :
    Frame st (setChainBalance st c x v) x :=
  ⟨fun _ _ => rfl, fun c' b hb => by simp [hb], fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem frame_markRegistered (st : Storage) (x : AssetId) (snap : SavedTotalSupply) :
    Frame st (markRegistered st x snap) x :=
  ⟨fun b hb => by simp [hb], fun _ _ _ => rfl, fun b hb => by simp [hb], fun _ _ => rfl,
    rfl, rfl, rfl, rfl⟩

theorem frame_setInterop (st : Storage) (x : AssetId) (info : InteropL2Info) :
    Frame st (setInterop st x info) x :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun b hb => by simp [hb], rfl, rfl, rfl, rfl⟩

/-! ## The composite functions as binds -/

theorem initiateInner_eq (cfg : Config) (st : Storage) (sl : ChainId) (reads : TokenReads)
    (toChain : ChainId) (a : AssetId) (amount : UInt256) (tokenOrigin : ChainId) :
    initiateInner cfg st sl reads toChain a amount tokenOrigin =
      if cfg.ntvTokenAddress a = 0 then none else
      (registerLegacyTokenIfNeeded cfg st reads a (cfg.ntvTokenAddress a)).bind fun st₁ =>
        (if tokenOrigin = cfg.thisChain then decreaseChainBalance st₁ cfg.thisChain a amount
          else some st₁).bind fun st₂ =>
        if toChain = st.l1ChainId ∧ sl = st.l1ChainId then addWithdrawalToL1 st₂ a amount
        else some st₂ := by
  unfold initiateInner
  split
  · rfl
  · cases registerLegacyTokenIfNeeded cfg st reads a (cfg.ntvTokenAddress a) with
    | none => rfl
    | some st₁ =>
      simp only [Option.bind_some]
      cases (if tokenOrigin = cfg.thisChain then decreaseChainBalance st₁ cfg.thisChain a amount
        else some st₁) <;> rfl

theorem finalizeInner_eq (cfg : Config) (st : Storage) (sl : ChainId) (reads : TokenReads)
    (fromChain : ChainId) (a : AssetId) (amount : UInt256) (isNative : Bool) (token : Address) :
    finalizeInner cfg st sl reads fromChain a amount isNative token =
      (registerLegacyTokenIfNeeded cfg st reads a token).bind fun st₁ =>
        (if isNative then increaseChainBalance st₁ cfg.thisChain a amount else some st₁).bind
          fun st₂ =>
        if fromChain = st.l1ChainId ∧ sl = st.l1ChainId then addDepositFromL1 st₂ a amount
        else some st₂ := by
  unfold finalizeInner
  cases registerLegacyTokenIfNeeded cfg st reads a token with
  | none => rfl
  | some st₁ =>
    simp only [Option.bind_some]
    cases (if isNative then increaseChainBalance st₁ cfg.thisChain a amount else some st₁) <;> rfl

/-! ## The first-touch registration -/

theorem registerLegacyTokenIfNeeded_of_registered {cfg : Config} {st : Storage}
    {reads : TokenReads} {a : AssetId} {token : Address} (h : st.isAssetRegistered a = true) :
    registerLegacyTokenIfNeeded cfg st reads a token = some st := by
  simp [registerLegacyTokenIfNeeded, h]

/-- The two ways a first-touch registration can succeed. -/
theorem registerLegacyTokenIfNeeded_cases {cfg : Config} {st st₁ : Storage} {reads : TokenReads}
    {a : AssetId} {token : Address}
    (h : registerLegacyTokenIfNeeded cfg st reads a token = some st₁) :
    (st.isAssetRegistered a = true ∧ st₁ = st) ∨
    (st.isAssetRegistered a = false ∧ cfg.ntvOriginChainId a ≠ 0 ∧ token ≠ 0 ∧
      ((Native cfg a ∧ st.chainBalance cfg.thisChain a = 0 ∧
          st₁ = markRegistered (setChainBalance st cfg.thisChain a (maxMinus reads.ntvBalance)) a
            ⟨true, maxMinus reads.ntvBalance⟩) ∨
        (¬ Native cfg a ∧ st₁ = markRegistered st a ⟨true, reads.totalSupply⟩))) := by
  unfold registerLegacyTokenIfNeeded at h
  by_cases hr : st.isAssetRegistered a = true
  · rw [ite_eq_left hr] at h
    exact Or.inl ⟨hr, (Option.some.inj h).symm⟩
  · rw [ite_eq_right hr] at h
    refine Or.inr ⟨by simpa using hr, ?_⟩
    unfold registerLegacyTokenInner at h
    by_cases h0 : cfg.ntvOriginChainId a = 0
    · rw [ite_eq_left h0] at h; cases h
    · rw [ite_eq_right h0] at h
      by_cases ht : token = 0
      · rw [ite_eq_left ht] at h; cases h
      · rw [ite_eq_right ht] at h
        refine ⟨h0, ht, ?_⟩
        by_cases hn : Native cfg a
        · rw [ite_eq_left hn] at h
          by_cases hz : st.chainBalance cfg.thisChain a ≠ 0
          · rw [ite_eq_left hz] at h; cases h
          · rw [ite_eq_right hz] at h
            exact Or.inl ⟨hn, not_not.1 hz, (Option.some.inj h).symm⟩
        · rw [ite_eq_right hn] at h
          exact Or.inr ⟨hn, (Option.some.inj h).symm⟩

theorem registerLegacyTokenIfNeeded_frame {cfg : Config} {st st₁ : Storage} {reads : TokenReads}
    {a : AssetId} {token : Address}
    (h : registerLegacyTokenIfNeeded cfg st reads a token = some st₁) : Frame st st₁ a := by
  rcases registerLegacyTokenIfNeeded_cases h with ⟨_, rfl⟩ | ⟨_, _, _, ⟨_, _, rfl⟩ | ⟨_, rfl⟩⟩
  · exact Frame.refl _ _
  · exact (frame_setChainBalance _ _ _ _).trans (frame_markRegistered _ _ _)
  · exact frame_markRegistered _ _ _

theorem registerLegacyTokenIfNeeded_registered {cfg : Config} {st st₁ : Storage}
    {reads : TokenReads} {a : AssetId} {token : Address}
    (h : registerLegacyTokenIfNeeded cfg st reads a token = some st₁) :
    st₁.isAssetRegistered a = true := by
  rcases registerLegacyTokenIfNeeded_cases h with ⟨hr, rfl⟩ | ⟨_, _, _, ⟨_, _, rfl⟩ | ⟨_, rfl⟩⟩
  · exact hr
  · simp
  · simp

theorem registerLegacyTokenIfNeeded_info {cfg : Config} {st st₁ : Storage} {reads : TokenReads}
    {a : AssetId} {token : Address}
    (h : registerLegacyTokenIfNeeded cfg st reads a token = some st₁) :
    st₁.interopInfo = st.interopInfo := by
  rcases registerLegacyTokenIfNeeded_cases h with ⟨_, rfl⟩ | ⟨_, _, _, ⟨_, _, rfl⟩ | ⟨_, rfl⟩⟩ <;> rfl

/-- A first-touch registration of a non-native asset leaves every chain balance alone. -/
theorem registerLegacyTokenIfNeeded_cb_of_not_native {cfg : Config} {st st₁ : Storage}
    {reads : TokenReads} {a : AssetId} {token : Address} (hn : ¬ Native cfg a)
    (h : registerLegacyTokenIfNeeded cfg st reads a token = some st₁) :
    st₁.chainBalance = st.chainBalance := by
  rcases registerLegacyTokenIfNeeded_cases h with ⟨_, rfl⟩ | ⟨_, _, _, ⟨hn', _, _⟩ | ⟨_, rfl⟩⟩
  · rfl
  · exact absurd hn' hn
  · rfl

/-! ## The flow primitives -/

theorem decreaseChainBalance_eq_some {st st' : Storage} {c : ChainId} {a : AssetId}
    {amount : UInt256} :
    decreaseChainBalance st c a amount = some st' ↔
      ∃ v : UInt256, amount.val ≤ (st.chainBalance c a).val ∧
        v.val = (st.chainBalance c a).val - amount.val ∧ st' = setChainBalance st c a v := by
  unfold decreaseChainBalance
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨hle, hval⟩ := checkedSub_eq_some.1 hv
    exact ⟨v, hle, hval, rfl⟩
  · rintro ⟨v, hle, hval, rfl⟩
    exact ⟨v, checkedSub_eq_some.2 ⟨hle, hval⟩, rfl⟩

theorem increaseChainBalance_eq_some {st st' : Storage} {c : ChainId} {a : AssetId}
    {amount : UInt256} :
    increaseChainBalance st c a amount = some st' ↔
      ∃ v : UInt256, (st.chainBalance c a).val + amount.val < UInt256.size ∧
        v.val = (st.chainBalance c a).val + amount.val ∧ st' = setChainBalance st c a v := by
  unfold increaseChainBalance
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨hlt, hval⟩ := checkedAdd_eq_some.1 hv
    exact ⟨v, hlt, hval, rfl⟩
  · rintro ⟨v, hlt, hval, rfl⟩
    exact ⟨v, checkedAdd_eq_some.2 ⟨hlt, hval⟩, rfl⟩

theorem addWithdrawalToL1_eq_some {st st' : Storage} {a : AssetId} {amount : UInt256} :
    addWithdrawalToL1 st a amount = some st' ↔
      ∃ w : UInt256, (st.interopInfo a).totalWithdrawalsToL1.val + amount.val < UInt256.size ∧
        w.val = (st.interopInfo a).totalWithdrawalsToL1.val + amount.val ∧
        st' = setInterop st a { st.interopInfo a with totalWithdrawalsToL1 := w } := by
  unfold addWithdrawalToL1
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hlt, hval⟩ := checkedAdd_eq_some.1 hw
    exact ⟨w, hlt, hval, rfl⟩
  · rintro ⟨w, hlt, hval, rfl⟩
    exact ⟨w, checkedAdd_eq_some.2 ⟨hlt, hval⟩, rfl⟩

theorem addDepositFromL1_eq_some {st st' : Storage} {a : AssetId} {amount : UInt256} :
    addDepositFromL1 st a amount = some st' ↔
      ∃ d : UInt256,
        (st.interopInfo a).totalSuccessfulDepositsFromL1.val + amount.val < UInt256.size ∧
        d.val = (st.interopInfo a).totalSuccessfulDepositsFromL1.val + amount.val ∧
        st' = setInterop st a { st.interopInfo a with totalSuccessfulDepositsFromL1 := d } := by
  unfold addDepositFromL1
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨hlt, hval⟩ := checkedAdd_eq_some.1 hd
    exact ⟨d, hlt, hval, rfl⟩
  · rintro ⟨d, hlt, hval, rfl⟩
    exact ⟨d, checkedAdd_eq_some.2 ⟨hlt, hval⟩, rfl⟩

/-! ## What one outbound or inbound call did, at its asset -/

/-- The anatomy of a successful outbound call: registration, then the native debit, then the
withdrawal counter. -/
theorem initiateInner_spec {cfg : Config} {st st' : Storage} {sl : ChainId} {reads : TokenReads}
    {toChain : ChainId} {a : AssetId} {amount : UInt256} {tokenOrigin : ChainId}
    (h : initiateInner cfg st sl reads toChain a amount tokenOrigin = some st') :
    cfg.ntvTokenAddress a ≠ 0 ∧ ∃ st₁,
      registerLegacyTokenIfNeeded cfg st reads a (cfg.ntvTokenAddress a) = some st₁ ∧
      Frame st₁ st' a ∧ st'.isAssetRegistered a = true ∧
      st'.totalPreV31TotalSupply a = st₁.totalPreV31TotalSupply a ∧
      (∀ c, c ≠ cfg.thisChain → st'.chainBalance c a = st₁.chainBalance c a) ∧
      (tokenOrigin = cfg.thisChain →
        amount.val ≤ (st₁.chainBalance cfg.thisChain a).val ∧
        (st'.chainBalance cfg.thisChain a).val =
          (st₁.chainBalance cfg.thisChain a).val - amount.val) ∧
      (tokenOrigin ≠ cfg.thisChain →
        st'.chainBalance cfg.thisChain a = st₁.chainBalance cfg.thisChain a) ∧
      (toChain = st.l1ChainId ∧ sl = st.l1ChainId →
        (st'.interopInfo a).totalWithdrawalsToL1.val =
          (st₁.interopInfo a).totalWithdrawalsToL1.val + amount.val ∧
        (st'.interopInfo a).totalSuccessfulDepositsFromL1 =
          (st₁.interopInfo a).totalSuccessfulDepositsFromL1) ∧
      (¬ (toChain = st.l1ChainId ∧ sl = st.l1ChainId) → st'.interopInfo a = st₁.interopInfo a) := by
  rw [initiateInner_eq] at h
  by_cases ht : cfg.ntvTokenAddress a = 0
  · rw [ite_eq_left ht] at h; cases h
  rw [ite_eq_right ht, Option.bind_eq_some_iff] at h
  obtain ⟨st₁, h₁, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨st₂, h₂, h₃⟩ := h
  have hreg₁ := registerLegacyTokenIfNeeded_registered h₁
  -- the debit step
  have hdeb : Frame st₁ st₂ a ∧ st₂.isAssetRegistered a = true ∧
      st₂.totalPreV31TotalSupply a = st₁.totalPreV31TotalSupply a ∧
      st₂.interopInfo = st₁.interopInfo ∧
      (∀ c, c ≠ cfg.thisChain → st₂.chainBalance c a = st₁.chainBalance c a) ∧
      (tokenOrigin = cfg.thisChain →
        amount.val ≤ (st₁.chainBalance cfg.thisChain a).val ∧
        (st₂.chainBalance cfg.thisChain a).val =
          (st₁.chainBalance cfg.thisChain a).val - amount.val) ∧
      (tokenOrigin ≠ cfg.thisChain →
        st₂.chainBalance cfg.thisChain a = st₁.chainBalance cfg.thisChain a) := by
    by_cases ho : tokenOrigin = cfg.thisChain
    · rw [ite_eq_left ho] at h₂
      obtain ⟨v, hle, hv, rfl⟩ := decreaseChainBalance_eq_some.1 h₂
      refine ⟨frame_setChainBalance _ _ _ _, hreg₁, rfl, rfl, fun c hc => by simp [hc],
        fun _ => ⟨hle, by simp [hv]⟩, fun h => absurd ho h⟩
    · rw [ite_eq_right ho] at h₂
      cases h₂
      exact ⟨Frame.refl _ _, hreg₁, rfl, rfl, fun _ _ => rfl, fun h => absurd h ho, fun _ => rfl⟩
  obtain ⟨hf₂, hreg₂, hsnap₂, hinfo₂, hcbo₂, hdec₂, hnd₂⟩ := hdeb
  refine ⟨ht, st₁, h₁, ?_⟩
  by_cases hc : toChain = st.l1ChainId ∧ sl = st.l1ChainId
  · rw [ite_eq_left hc] at h₃
    obtain ⟨w, hlt, hw, rfl⟩ := addWithdrawalToL1_eq_some.1 h₃
    refine ⟨hf₂.trans (frame_setInterop _ _ _), by simpa using hreg₂, by simpa using hsnap₂,
      fun c hc' => by simpa using hcbo₂ c hc', fun ho => by simpa using hdec₂ ho,
      fun ho => by simpa using hnd₂ ho, fun _ => ?_, fun h => absurd hc h⟩
    simp only [setInterop_interopInfo, ite_true]
    exact ⟨by rw [hw, hinfo₂], by rw [hinfo₂]⟩
  · rw [ite_eq_right hc] at h₃
    cases h₃
    exact ⟨hf₂, hreg₂, hsnap₂, hcbo₂, hdec₂, hnd₂, fun h => absurd h hc,
      fun _ => by rw [hinfo₂]⟩

/-- The anatomy of a successful inbound call: registration, then the native credit, then the
deposit counter. -/
theorem finalizeInner_spec {cfg : Config} {st st' : Storage} {sl : ChainId} {reads : TokenReads}
    {fromChain : ChainId} {a : AssetId} {amount : UInt256} {isNative : Bool} {token : Address}
    (h : finalizeInner cfg st sl reads fromChain a amount isNative token = some st') :
    ∃ st₁, registerLegacyTokenIfNeeded cfg st reads a token = some st₁ ∧
      Frame st₁ st' a ∧ st'.isAssetRegistered a = true ∧
      st'.totalPreV31TotalSupply a = st₁.totalPreV31TotalSupply a ∧
      (∀ c, c ≠ cfg.thisChain → st'.chainBalance c a = st₁.chainBalance c a) ∧
      (isNative = true →
        (st₁.chainBalance cfg.thisChain a).val + amount.val < UInt256.size ∧
        (st'.chainBalance cfg.thisChain a).val =
          (st₁.chainBalance cfg.thisChain a).val + amount.val) ∧
      (isNative = false → st'.chainBalance cfg.thisChain a = st₁.chainBalance cfg.thisChain a) ∧
      (fromChain = st.l1ChainId ∧ sl = st.l1ChainId →
        (st'.interopInfo a).totalSuccessfulDepositsFromL1.val =
          (st₁.interopInfo a).totalSuccessfulDepositsFromL1.val + amount.val ∧
        (st'.interopInfo a).totalWithdrawalsToL1 = (st₁.interopInfo a).totalWithdrawalsToL1) ∧
      (¬ (fromChain = st.l1ChainId ∧ sl = st.l1ChainId) →
        st'.interopInfo a = st₁.interopInfo a) := by
  rw [finalizeInner_eq, Option.bind_eq_some_iff] at h
  obtain ⟨st₁, h₁, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨st₂, h₂, h₃⟩ := h
  have hreg₁ := registerLegacyTokenIfNeeded_registered h₁
  have hcred : Frame st₁ st₂ a ∧ st₂.isAssetRegistered a = true ∧
      st₂.totalPreV31TotalSupply a = st₁.totalPreV31TotalSupply a ∧
      st₂.interopInfo = st₁.interopInfo ∧
      (∀ c, c ≠ cfg.thisChain → st₂.chainBalance c a = st₁.chainBalance c a) ∧
      (isNative = true →
        (st₁.chainBalance cfg.thisChain a).val + amount.val < UInt256.size ∧
        (st₂.chainBalance cfg.thisChain a).val =
          (st₁.chainBalance cfg.thisChain a).val + amount.val) ∧
      (isNative = false → st₂.chainBalance cfg.thisChain a = st₁.chainBalance cfg.thisChain a) := by
    cases isNative with
    | true =>
      rw [ite_eq_left rfl] at h₂
      obtain ⟨v, hlt, hv, rfl⟩ := increaseChainBalance_eq_some.1 h₂
      exact ⟨frame_setChainBalance _ _ _ _, hreg₁, rfl, rfl, fun c hc => by simp [hc],
        fun _ => ⟨hlt, by simp [hv]⟩, fun h => Bool.noConfusion h⟩
    | false =>
      rw [ite_eq_right (by decide)] at h₂
      cases h₂
      exact ⟨Frame.refl _ _, hreg₁, rfl, rfl, fun _ _ => rfl, fun h => Bool.noConfusion h,
        fun _ => rfl⟩
  obtain ⟨hf₂, hreg₂, hsnap₂, hinfo₂, hcbo₂, hinc₂, hni₂⟩ := hcred
  refine ⟨st₁, h₁, ?_⟩
  by_cases hc : fromChain = st.l1ChainId ∧ sl = st.l1ChainId
  · rw [ite_eq_left hc] at h₃
    obtain ⟨d, hlt, hd, rfl⟩ := addDepositFromL1_eq_some.1 h₃
    refine ⟨hf₂.trans (frame_setInterop _ _ _), by simpa using hreg₂, by simpa using hsnap₂,
      fun c hc' => by simpa using hcbo₂ c hc', fun hn => by simpa using hinc₂ hn,
      fun hn => by simpa using hni₂ hn, fun _ => ?_, fun h => absurd hc h⟩
    simp only [setInterop_interopInfo, ite_true]
    exact ⟨by rw [hd, hinfo₂], by rw [hinfo₂]⟩
  · rw [ite_eq_right hc] at h₃
    cases h₃
    exact ⟨hf₂, hreg₂, hsnap₂, hcbo₂, hinc₂, hni₂, fun h => absurd h hc,
      fun _ => by rw [hinfo₂]⟩

/-! ## The invariant, asset by asset -/

/-- `Inv`'s per-asset part. -/
def AssetOK (cfg : Config) (st : Storage) (au : Audit) (a : AssetId) : Prop :=
  (st.isAssetRegistered a = false →
    au.outflow a = 0 ∧ au.inflow a = 0 ∧ st.chainBalance cfg.thisChain a = 0) ∧
  (st.isAssetRegistered a = true → Native cfg a →
    (st.chainBalance cfg.thisChain a).val + au.outflow a =
      (st.totalPreV31TotalSupply a).amount.val + au.inflow a ∧
    (st.totalPreV31TotalSupply a).isSaved = true)

theorem inv_iff {cfg : Config} {sys : Sys} :
    Inv cfg sys ↔ (∀ a, AssetOK cfg sys.st sys.audit a) ∧
      (sys.st.guardInitialized = false → sys.st.needBaseTokenTotalSupplyBackfill = false) ∧
      BaseNotSelfNative cfg sys := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun a => ⟨h1 a, h2 a⟩, h3, h4⟩
  · rintro ⟨h1, h3, h4⟩
    exact ⟨fun a => (h1 a).1, fun a => (h1 a).2, h3, h4⟩

theorem assetOK_congr {cfg : Config} {st st' : Storage} {au au' : Audit} {a : AssetId}
    (h : AssetOK cfg st au a)
    (hr : st'.isAssetRegistered a = st.isAssetRegistered a)
    (hc : st'.chainBalance cfg.thisChain a = st.chainBalance cfg.thisChain a)
    (hs : st'.totalPreV31TotalSupply a = st.totalPreV31TotalSupply a)
    (ho : au'.outflow a = au.outflow a) (hi : au'.inflow a = au.inflow a) :
    AssetOK cfg st' au' a := by
  unfold AssetOK at *
  rw [hr, hc, hs, ho, hi]
  exact h

theorem assetOK_frame {cfg : Config} {st st' : Storage} {au au' : Audit} {x b : AssetId}
    (hf : Frame st st' x) (hb : b ≠ x) (ho : au'.outflow b = au.outflow b)
    (hi : au'.inflow b = au.inflow b) (h : AssetOK cfg st au b) : AssetOK cfg st' au' b :=
  assetOK_congr h (hf.reg b hb) (hf.cb _ b hb) (hf.snap b hb) ho hi

/-- The first-touch registration keeps the asset's invariant (and registers it). -/
theorem registerLegacyTokenIfNeeded_assetOK {cfg : Config} {st st₁ : Storage}
    {reads : TokenReads} {au : Audit} {a : AssetId} {token : Address}
    (h : registerLegacyTokenIfNeeded cfg st reads a token = some st₁) (hok : AssetOK cfg st au a) :
    AssetOK cfg st₁ au a := by
  rcases registerLegacyTokenIfNeeded_cases h with
    ⟨_, rfl⟩ | ⟨hr, _, _, ⟨hn, _, rfl⟩ | ⟨hn, rfl⟩⟩
  · exact hok
  · obtain ⟨ho, hi, _⟩ := hok.1 hr
    refine ⟨fun h => by simp at h, fun _ _ => ?_⟩
    simp [ho, hi]
  · refine ⟨fun h => by simp at h, fun _ h => absurd h hn⟩

/-- An outbound call keeps its asset's invariant, with the audit recording the outflow. -/
theorem initiateInner_assetOK {cfg : Config} {st st' : Storage} {sl : ChainId}
    {reads : TokenReads} {au : Audit} {toChain : ChainId} {a : AssetId} {amount : UInt256}
    {tokenOrigin : ChainId} (horig : Native cfg a → tokenOrigin = cfg.thisChain)
    (h : initiateInner cfg st sl reads toChain a amount tokenOrigin = some st')
    (hok : AssetOK cfg st au a) : AssetOK cfg st' (au.addOut a amount) a := by
  obtain ⟨_, st₁, h₁, _, hreg', hsnap', _, hdec, _, _, _⟩ := initiateInner_spec h
  have hok₁ := registerLegacyTokenIfNeeded_assetOK h₁ hok
  have hreg₁ := registerLegacyTokenIfNeeded_registered h₁
  refine ⟨fun h => (by rw [hreg'] at h; cases h), fun _ hn => ?_⟩
  obtain ⟨hsent, hsaved⟩ := hok₁.2 hreg₁ hn
  obtain ⟨hle, hcb⟩ := hdec (horig hn)
  refine ⟨?_, by rw [hsnap']; exact hsaved⟩
  simp only [Audit.addOut_outflow, Audit.addOut_inflow, hsnap', hcb, ite_true]
  omega

/-- An inbound call keeps its asset's invariant, with the audit recording the inflow. -/
theorem finalizeInner_assetOK {cfg : Config} {st st' : Storage} {sl : ChainId}
    {reads : TokenReads} {au : Audit} {fromChain : ChainId} {a : AssetId} {amount : UInt256}
    {isNative : Bool} {token : Address} (hnat : Native cfg a → isNative = true)
    (h : finalizeInner cfg st sl reads fromChain a amount isNative token = some st')
    (hok : AssetOK cfg st au a) : AssetOK cfg st' (au.addIn a amount) a := by
  obtain ⟨st₁, h₁, _, hreg', hsnap', _, hinc, _, _, _⟩ := finalizeInner_spec h
  have hok₁ := registerLegacyTokenIfNeeded_assetOK h₁ hok
  have hreg₁ := registerLegacyTokenIfNeeded_registered h₁
  refine ⟨fun h => (by rw [hreg'] at h; cases h), fun _ hn => ?_⟩
  obtain ⟨hsent, hsaved⟩ := hok₁.2 hreg₁ hn
  obtain ⟨_, hcb⟩ := hinc (hnat hn)
  refine ⟨?_, by rw [hsnap']; exact hsaved⟩
  simp only [Audit.addIn_inflow, Audit.addIn_outflow, hsnap', hcb, ite_true]
  omega

/-- The frame of a successful outbound call. -/
theorem initiateInner_frame {cfg : Config} {st st' : Storage} {sl : ChainId} {reads : TokenReads}
    {toChain : ChainId} {a : AssetId} {amount : UInt256} {tokenOrigin : ChainId}
    (h : initiateInner cfg st sl reads toChain a amount tokenOrigin = some st') :
    Frame st st' a := by
  obtain ⟨_, st₁, h₁, hf, _⟩ := initiateInner_spec h
  exact (registerLegacyTokenIfNeeded_frame h₁).trans hf

/-- The frame of a successful inbound call. -/
theorem finalizeInner_frame {cfg : Config} {st st' : Storage} {sl : ChainId} {reads : TokenReads}
    {fromChain : ChainId} {a : AssetId} {amount : UInt256} {isNative : Bool} {token : Address}
    (h : finalizeInner cfg st sl reads fromChain a amount isNative token = some st') :
    Frame st st' a := by
  obtain ⟨st₁, h₁, hf, _⟩ := finalizeInner_spec h
  exact (registerLegacyTokenIfNeeded_frame h₁).trans hf

/-- A flow at asset `x` keeps the whole invariant, given its effect at `x`. -/
theorem inv_of_flow {cfg : Config} {sys : Sys} {st' : Storage} {au' : Audit} {x : AssetId}
    (hinv : Inv cfg sys) (hf : Frame sys.st st' x)
    (ho : ∀ b, b ≠ x → au'.outflow b = sys.audit.outflow b)
    (hi : ∀ b, b ≠ x → au'.inflow b = sys.audit.inflow b)
    (hx : AssetOK cfg sys.st sys.audit x → AssetOK cfg st' au' x) :
    Inv cfg { sys with st := st', audit := au' } := by
  rw [inv_iff] at hinv ⊢
  obtain ⟨hok, hbf, hbase⟩ := hinv
  refine ⟨fun b => ?_, ?_, ?_⟩
  · by_cases hb : b = x
    · subst hb; exact hx (hok b)
    · exact assetOK_frame hf hb (ho b hb) (hi b hb) (hok b)
  · show st'.guardInitialized = false → st'.needBaseTokenTotalSupplyBackfill = false
    rw [hf.guard, hf.need]
    exact hbf
  · exact ⟨hbase.1, by show ¬ Native cfg st'.baseTokenAssetId; rw [hf.base]; exact hbase.2⟩

theorem addOut_other (au : Audit) (x : AssetId) (amount : UInt256) :
    (∀ b, b ≠ x → (au.addOut x amount).outflow b = au.outflow b) ∧
    (∀ b, b ≠ x → (au.addOut x amount).inflow b = au.inflow b) :=
  ⟨fun b hb => by simp [hb], fun _ _ => rfl⟩

theorem addIn_other (au : Audit) (x : AssetId) (amount : UInt256) :
    (∀ b, b ≠ x → (au.addIn x amount).outflow b = au.outflow b) ∧
    (∀ b, b ≠ x → (au.addIn x amount).inflow b = au.inflow b) :=
  ⟨fun _ _ => rfl, fun b hb => by simp [hb]⟩

/-- `registerLegacyToken` is the first-touch registration at the vault's token address. -/
theorem registerLegacyToken_eq {cfg : Config} {st st' : Storage} {reads : TokenReads}
    {a : AssetId} (h : registerLegacyToken cfg st reads a = some st') :
    registerLegacyTokenIfNeeded cfg st reads a (cfg.ntvTokenAddress a) = some st' := by
  unfold registerLegacyToken at h
  unfold registerLegacyTokenIfNeeded
  by_cases hr : st.isAssetRegistered a = true
  · rw [ite_eq_left hr] at h ⊢; exact h
  · rw [ite_eq_right hr] at h ⊢
    by_cases ht : cfg.ntvTokenAddress a = 0
    · rw [ite_eq_left ht] at h; cases h
    · rw [ite_eq_right ht] at h; exact h

/-- **ONE STEP KEEPS THE INVARIANT.** -/
theorem exec_inv {cfg : Config} {sys sys' : Sys} {op : Op} (hinv : Inv cfg sys)
    (h : exec cfg sys op = some sys') : Inv cfg sys' := by
  cases op with
  | registerNewToken a =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold registerNewTokenIfNeeded at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    by_cases hr : sys.st.isAssetRegistered a = true
    · rw [ite_eq_left hr] at h
      cases h
      exact hinv
    · rw [ite_eq_right hr] at h
      have hr' : sys.st.isAssetRegistered a = false := by simpa using hr
      by_cases hn : cfg.ntvOriginChainId a = cfg.thisChain
      · rw [ite_eq_left hn] at h
        cases h
        refine inv_of_flow (au' := sys.audit) hinv
          ((frame_setChainBalance _ _ _ _).trans (frame_markRegistered _ _ _))
          (fun _ _ => rfl) (fun _ _ => rfl) fun hok => ⟨fun h => by simp at h, fun _ _ => ?_⟩
        obtain ⟨ho, hi, _⟩ := hok.1 hr'
        simp [ho, hi]
      · rw [ite_eq_right hn] at h
        cases h
        exact inv_of_flow (au' := sys.audit) hinv (frame_markRegistered _ _ _)
          (fun _ _ => rfl) (fun _ _ => rfl)
          fun _ => ⟨fun h => by simp at h, fun _ h => absurd h hn⟩
  | registerBaseDuringUpgrade =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold registerBaseTokenDuringUpgrade at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    by_cases hr : sys.st.isAssetRegistered sys.st.baseTokenAssetId = true
    · rw [ite_eq_left hr] at h; cases h
    · rw [ite_eq_right hr] at h
      cases h
      exact inv_of_flow (au' := sys.audit) hinv (frame_markRegistered _ _ _)
        (fun _ _ => rfl) (fun _ _ => rfl)
        fun _ => ⟨fun h => by simp at h, fun _ h => absurd h hinv.baseNotNative.2⟩
  | registerLegacy reads a =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    have h' := registerLegacyToken_eq h
    exact inv_of_flow (au' := sys.audit) hinv (registerLegacyTokenIfNeeded_frame h')
      (fun _ _ => rfl) (fun _ _ => rfl) (registerLegacyTokenIfNeeded_assetOK h')
  | initiate reads toChain a amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleInitiateBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    exact inv_of_flow hinv (initiateInner_frame h) (addOut_other _ _ _).1 (addOut_other _ _ _).2
      (initiateInner_assetOK id h)
  | initiateBase reads toChain amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleInitiateBaseTokenBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    exact inv_of_flow hinv (initiateInner_frame h) (addOut_other _ _ _).1 (addOut_other _ _ _).2
      (initiateInner_assetOK id h)
  | finalize reads fromChain a amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleFinalizeBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    exact inv_of_flow hinv (finalizeInner_frame h) (addIn_other _ _ _).1 (addIn_other _ _ _).2
      (finalizeInner_assetOK (fun hn => decide_eq_true hn) h)
  | finalizeBase reads caller fromChain amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleFinalizeBaseTokenBridgingOnL2 at h
    by_cases hc : caller ≠ cfg.baseTokenHolder ∧ caller ≠ cfg.l2BaseToken
    · rw [ite_eq_left hc] at h; cases h
    rw [ite_eq_right hc] at h
    by_cases h0 : amount = 0
    · rw [ite_eq_left h0] at h
      cases h
      subst h0
      refine inv_of_flow hinv (Frame.refl _ sys.st.baseTokenAssetId) (addIn_other _ _ _).1
        (addIn_other _ _ _).2 fun hok => assetOK_congr hok rfl rfl rfl rfl ?_
      simp
    rw [ite_eq_right h0] at h
    by_cases hb : sys.st.baseTokenAssetId = 0
    · rw [ite_eq_left hb] at h; cases h
    rw [ite_eq_right hb] at h
    exact inv_of_flow hinv (finalizeInner_frame h) (addIn_other _ _ _).1 (addIn_other _ _ _).2
      (finalizeInner_assetOK (fun hn => absurd hn hinv.baseNotNative.2) h)
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
    rw [inv_iff] at hinv ⊢
    obtain ⟨hok, _, hbase⟩ := hinv
    refine ⟨fun b => ?_, fun _ => rfl, hbase⟩
    by_cases hb : b = sys.st.baseTokenAssetId
    · subst hb
      exact ⟨(hok _).1, fun _ hn => absurd hn hbase.2⟩
    · exact assetOK_congr (hok b) rfl rfl (by simp [hb]) rfl rfl
  | initL2 need =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold initL2 at h
    by_cases hg : sys.st.guardInitialized = true
    · rw [ite_eq_left hg] at h; cases h
    rw [ite_eq_right hg, ite_eq_right (not_not.2 rfl)] at h
    cases h
    rw [inv_iff] at hinv ⊢
    obtain ⟨hok, _, hbase⟩ := hinv
    exact ⟨fun b => assetOK_congr (hok b) rfl rfl rfl rfl rfl, fun h => (by cases h),
      hbase.1, hbase.1⟩
  | setSettlementLayer c =>
    simp only [exec, Option.some.injEq] at h
    subst h
    exact ⟨hinv.1, hinv.2, hinv.3, hinv.4⟩

theorem AccountingInvariant : Properties.AccountingInvariant := by
  intro cfg sys₀ sys hinv hreach
  induction hreach with
  | refl => exact hinv
  | tail _ hstep ih =>
    obtain ⟨op, hop⟩ := hstep
    exact exec_inv ih hop

theorem FreshTrackerSatisfiesInv : Properties.FreshTrackerSatisfiesInv := by
  intro cfg sl hbase h0
  exact ⟨fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ h => (by cases h), fun _ => rfl, hbase, h0⟩

theorem NativeSentinel : Properties.NativeSentinel := by
  intro cfg sys₀ sys a hinv hreach hr hn
  obtain ⟨hsent, _⟩ := (AccountingInvariant cfg sys₀ sys hinv hreach).sentinel a hr hn
  have hcb := val_le_max (sys.st.chainBalance cfg.thisChain a)
  have hsn := val_le_max (sys.st.totalPreV31TotalSupply a).amount
  unfold ChainBalanceSentinel at hsent
  refine ⟨hsent, by omega, by omega⟩

/-! ## The caps -/

theorem exists_map_eq_some {α β : Type} {o : Option α} {f : α → β} :
    (∃ y, o.map f = some y) ↔ ∃ x, o = some x := by
  cases o <;> simp

/-- On a registered asset touching no L1 counter, an inbound call is the bare native credit. -/
theorem finalizeInner_registered_off {cfg : Config} {st : Storage} {sl : ChainId}
    {reads : TokenReads} {fromChain : ChainId} {a : AssetId} {amount : UInt256} {isNative : Bool}
    {token : Address} (hr : st.isAssetRegistered a = true)
    (hoff : ¬ (fromChain = st.l1ChainId ∧ sl = st.l1ChainId)) :
    finalizeInner cfg st sl reads fromChain a amount isNative token =
      if isNative then increaseChainBalance st cfg.thisChain a amount else some st := by
  rw [finalizeInner_eq, registerLegacyTokenIfNeeded_of_registered hr, Option.bind_some]
  cases (if isNative then increaseChainBalance st cfg.thisChain a amount else some st) with
  | none => rfl
  | some st₂ => simp only [Option.bind_some, ite_eq_right hoff]

/-- On a registered asset the vault knows, touching no L1 counter, an outbound call is the bare
native debit. -/
theorem initiateInner_registered_off {cfg : Config} {st : Storage} {sl : ChainId}
    {reads : TokenReads} {toChain : ChainId} {a : AssetId} {amount : UInt256}
    {tokenOrigin : ChainId} (hr : st.isAssetRegistered a = true) (ht : cfg.ntvTokenAddress a ≠ 0)
    (hoff : ¬ (toChain = st.l1ChainId ∧ sl = st.l1ChainId)) :
    initiateInner cfg st sl reads toChain a amount tokenOrigin =
      if tokenOrigin = cfg.thisChain then decreaseChainBalance st cfg.thisChain a amount
      else some st := by
  rw [initiateInner_eq, ite_eq_right ht, registerLegacyTokenIfNeeded_of_registered hr,
    Option.bind_some]
  cases (if tokenOrigin = cfg.thisChain then decreaseChainBalance st cfg.thisChain a amount
    else some st) with
  | none => rfl
  | some st₂ => simp only [Option.bind_some, ite_eq_right hoff]

theorem InflowOverflowIsCap : Properties.InflowOverflowIsCap := by
  intro cfg sys₀ sys reads fromChain a amount hinv hreach hr hn hoff
  obtain ⟨hsent, _⟩ := (AccountingInvariant cfg sys₀ sys hinv hreach).sentinel a hr hn
  unfold ChainBalanceSentinel at hsent
  have hcb := val_le_max (sys.st.chainBalance cfg.thisChain a)
  have hsn := val_le_max (sys.st.totalPreV31TotalSupply a).amount
  have hoff' : ¬ (fromChain = sys.st.l1ChainId ∧ sys.sl = sys.st.l1ChainId) := by
    rintro ⟨h1, h2⟩
    rcases hoff with h | h
    · exact h h1
    · exact h h2
  have hfin : finalizeInner cfg sys.st sys.sl reads fromChain a amount
      (decide (cfg.ntvOriginChainId a = cfg.thisChain)) (cfg.ntvTokenAddress a) =
      increaseChainBalance sys.st cfg.thisChain a amount := by
    rw [finalizeInner_registered_off hr hoff',
      ite_eq_left (decide_eq_true (show cfg.ntvOriginChainId a = cfg.thisChain from hn))]
  simp only [exec, handleFinalizeBridgingOnL2, ne_eq, not_true_eq_false, ite_false, hfin,
    exists_map_eq_some]
  rw [MAX_TOKEN_BALANCE_val] at hcb hsn ⊢
  constructor
  · rintro ⟨st', h⟩
    obtain ⟨_, hlt, _, _⟩ := increaseChainBalance_eq_some.1 h
    omega
  · intro h
    obtain ⟨v, hv, hval⟩ := checkedAdd_some_of_lt (a := sys.st.chainBalance cfg.thisChain a)
      (b := amount) (by omega)
    exact ⟨_, increaseChainBalance_eq_some.2 ⟨v, by omega, hval, rfl⟩⟩

theorem OutflowIffNetOutFits : Properties.OutflowIffNetOutFits := by
  intro cfg sys₀ sys reads toChain a amount hinv hreach hr hn ht hoff
  obtain ⟨hsent, _⟩ := (AccountingInvariant cfg sys₀ sys hinv hreach).sentinel a hr hn
  unfold ChainBalanceSentinel at hsent
  have hcb := val_le_max (sys.st.chainBalance cfg.thisChain a)
  have hsn := val_le_max (sys.st.totalPreV31TotalSupply a).amount
  have hoff' : ¬ (toChain = sys.st.l1ChainId ∧ sys.sl = sys.st.l1ChainId) := by
    rintro ⟨h1, h2⟩
    rcases hoff with h | h
    · exact h h1
    · exact h h2
  have hini : initiateInner cfg sys.st sys.sl reads toChain a amount (cfg.ntvOriginChainId a) =
      decreaseChainBalance sys.st cfg.thisChain a amount := by
    rw [initiateInner_registered_off hr ht hoff',
      ite_eq_left (show cfg.ntvOriginChainId a = cfg.thisChain from hn)]
  simp only [exec, handleInitiateBridgingOnL2, ne_eq, not_true_eq_false, ite_false, hini,
    exists_map_eq_some]
  constructor
  · rintro ⟨st', h⟩
    obtain ⟨_, hle, _, _⟩ := decreaseChainBalance_eq_some.1 h
    omega
  · intro h
    obtain ⟨v, hv, hval⟩ := checkedSub_some_of_le (a := sys.st.chainBalance cfg.thisChain a)
      (b := amount) (by omega)
    exact ⟨_, decreaseChainBalance_eq_some.2 ⟨v, by omega, hval, rfl⟩⟩

theorem TokenReadsIgnoredOnceRegistered : Properties.TokenReadsIgnoredOnceRegistered := by
  intro cfg st sl reads reads' c a amount hr
  refine ⟨?_, ?_⟩
  · simp only [handleInitiateBridgingOnL2, initiateInner_eq,
      registerLegacyTokenIfNeeded_of_registered hr]
  · simp only [handleFinalizeBridgingOnL2, finalizeInner_eq,
      registerLegacyTokenIfNeeded_of_registered hr]

/-! ## The round trip -/

theorem setChainBalance_chainBalance_self (st : Storage) (c : ChainId) (a : AssetId)
    (v : UInt256) : (setChainBalance st c a v).chainBalance c a = v := by
  simp only [setChainBalance_chainBalance, and_self, ite_true]

theorem setChainBalance_setChainBalance (st : Storage) (c : ChainId) (a : AssetId)
    (v w : UInt256) : setChainBalance (setChainBalance st c a v) c a w = setChainBalance st c a w := by
  simp only [setChainBalance, Function.update_self, Function.update_idem]

theorem setChainBalance_self (st : Storage) (c : ChainId) (a : AssetId) :
    setChainBalance st c a (st.chainBalance c a) = st := by
  simp only [setChainBalance, Function.update_eq_self]

/-- A checked credit undoes a checked debit of the same amount. -/
theorem increase_after_decrease {st st₂ : Storage} {c : ChainId} {a : AssetId} {amount : UInt256}
    (h : decreaseChainBalance st c a amount = some st₂) :
    increaseChainBalance st₂ c a amount = some st := by
  obtain ⟨v, hle, hv, rfl⟩ := decreaseChainBalance_eq_some.1 h
  rw [increaseChainBalance_eq_some, setChainBalance_chainBalance_self]
  have := (st.chainBalance c a).isLt
  refine ⟨st.chainBalance c a, by omega, by omega, ?_⟩
  rw [setChainBalance_setChainBalance, setChainBalance_self]

/-- The anatomy of an outbound call that touches no counter. -/
theorem initiateInner_off_cases {cfg : Config} {st st' : Storage} {sl : ChainId}
    {reads : TokenReads} {toChain : ChainId} {a : AssetId} {amount : UInt256}
    {tokenOrigin : ChainId} (h : initiateInner cfg st sl reads toChain a amount tokenOrigin = some st')
    (hoff : ¬ (toChain = st.l1ChainId ∧ sl = st.l1ChainId)) :
    ∃ st₀, registerLegacyTokenIfNeeded cfg st reads a (cfg.ntvTokenAddress a) = some st₀ ∧
      ((tokenOrigin = cfg.thisChain ∧ decreaseChainBalance st₀ cfg.thisChain a amount = some st') ∨
        (tokenOrigin ≠ cfg.thisChain ∧ st' = st₀)) := by
  rw [initiateInner_eq] at h
  by_cases ht : cfg.ntvTokenAddress a = 0
  · rw [ite_eq_left ht] at h; cases h
  rw [ite_eq_right ht, Option.bind_eq_some_iff] at h
  obtain ⟨st₀, h₀, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨st₂, h₂, h₃⟩ := h
  rw [ite_eq_right hoff] at h₃
  cases h₃
  refine ⟨st₀, h₀, ?_⟩
  by_cases ho : tokenOrigin = cfg.thisChain
  · rw [ite_eq_left ho] at h₂
    exact Or.inl ⟨ho, h₂⟩
  · rw [ite_eq_right ho] at h₂
    exact Or.inr ⟨ho, (Option.some.inj h₂).symm⟩

theorem TrackerHooksCancelOffL1 : Properties.TrackerHooksCancelOffL1 := by
  intro cfg st st' sl₁ sl₂ reads₁ reads₂ c a amount h hoff
  unfold handleInitiateBridgingOnL2 at h
  rw [ite_eq_right (not_not.2 rfl)] at h
  have hf := initiateInner_frame h
  have hreg' := (initiateInner_spec h).2.choose_spec.2.2.1
  have hoff₁ : ¬ (c = st.l1ChainId ∧ sl₁ = st.l1ChainId) := by
    rintro ⟨h1, h2⟩
    rcases hoff with h | ⟨h, _⟩
    · exact h h1
    · exact h h2
  have hoff₂ : ¬ (c = st'.l1ChainId ∧ sl₂ = st'.l1ChainId) := by
    rw [hf.l1]
    rintro ⟨h1, h2⟩
    rcases hoff with h | ⟨_, h⟩
    · exact h h1
    · exact h h2
  obtain ⟨st₀, h₀, hcase⟩ := initiateInner_off_cases h hoff₁
  refine ⟨st₀, h₀, ?_, fun hr => ?_⟩
  · unfold handleFinalizeBridgingOnL2
    rw [ite_eq_right (not_not.2 rfl), finalizeInner_registered_off hreg' hoff₂]
    rcases hcase with ⟨ho, hdec⟩ | ⟨ho, rfl⟩
    · rw [decide_eq_true ho, ite_eq_left rfl]
      exact increase_after_decrease hdec
    · rw [decide_eq_false ho]
      rfl
  · rw [registerLegacyTokenIfNeeded_of_registered hr] at h₀
    exact (Option.some.inj h₀).symm

theorem L1CountersMoveTogether : Properties.L1CountersMoveTogether := by
  intro cfg st st' reads₁ reads₂ c a amount h hc
  unfold handleInitiateBridgingOnL2 at h
  rw [ite_eq_right (not_not.2 rfl)] at h
  have hf := initiateInner_frame h
  rw [initiateInner_eq] at h
  by_cases ht : cfg.ntvTokenAddress a = 0
  · rw [ite_eq_left ht] at h; cases h
  rw [ite_eq_right ht, Option.bind_eq_some_iff] at h
  obtain ⟨st₀, h₀, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨st₂, h₂, h₃⟩ := h
  rw [ite_eq_left ⟨hc, rfl⟩] at h₃
  obtain ⟨w, hwlt, hw, rfl⟩ := addWithdrawalToL1_eq_some.1 h₃
  have hreg₀ := registerLegacyTokenIfNeeded_registered h₀
  -- the debit step changes only the chain balance
  have hdeb : st₂.interopInfo = st₀.interopInfo ∧ st₂.isAssetRegistered = st₀.isAssetRegistered ∧
      st₂.totalPreV31TotalSupply = st₀.totalPreV31TotalSupply ∧
      st₂.l1ChainId = st₀.l1ChainId ∧
      ((cfg.ntvOriginChainId a = cfg.thisChain ∧
          decreaseChainBalance st₀ cfg.thisChain a amount = some st₂) ∨
        (cfg.ntvOriginChainId a ≠ cfg.thisChain ∧ st₂ = st₀)) := by
    by_cases ho : cfg.ntvOriginChainId a = cfg.thisChain
    · rw [ite_eq_left ho] at h₂
      have h₂' := h₂
      obtain ⟨v, _, _, rfl⟩ := decreaseChainBalance_eq_some.1 h₂
      exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨ho, h₂'⟩⟩
    · rw [ite_eq_right ho] at h₂
      cases h₂
      exact ⟨rfl, rfl, rfl, rfl, Or.inr ⟨ho, rfl⟩⟩
  obtain ⟨hi₂, hr₂, hs₂, hl₂, hcase⟩ := hdeb
  have hl₀ : st₀.l1ChainId = st.l1ChainId := (registerLegacyTokenIfNeeded_frame h₀).l1
  refine ⟨st₀, h₀, by rw [← hi₂]; exact hwlt, fun hdlt => ?_⟩
  -- the inbound call: registration is the identity, then the credit, then the deposit counter
  have hreg' : (setInterop st₂ a { st₂.interopInfo a with totalWithdrawalsToL1 := w }).isAssetRegistered
      a = true := by simp [hr₂, hreg₀]
  unfold handleFinalizeBridgingOnL2
  rw [ite_eq_right (not_not.2 rfl), finalizeInner_eq,
    registerLegacyTokenIfNeeded_of_registered hreg', Option.bind_some]
  -- the credit restores the chain balance of `st₀`
  obtain ⟨st₃, hst₃, hcb₃, hi₃, hr₃, hs₃⟩ : ∃ st₃,
      (if decide (cfg.ntvOriginChainId a = cfg.thisChain) then
          increaseChainBalance (setInterop st₂ a { st₂.interopInfo a with totalWithdrawalsToL1 := w })
            cfg.thisChain a amount
        else some (setInterop st₂ a { st₂.interopInfo a with totalWithdrawalsToL1 := w })) =
        some st₃ ∧
      st₃.chainBalance = st₀.chainBalance ∧
      st₃.interopInfo = (setInterop st₂ a { st₂.interopInfo a with totalWithdrawalsToL1 := w }).interopInfo ∧
      st₃.isAssetRegistered = st₀.isAssetRegistered ∧
      st₃.totalPreV31TotalSupply = st₀.totalPreV31TotalSupply := by
    rcases hcase with ⟨ho, hdec⟩ | ⟨ho, rfl⟩
    · rw [decide_eq_true ho, ite_eq_left rfl]
      have hinc := increase_after_decrease hdec
      -- crediting after the counter write: the counter write commutes with the credit
      obtain ⟨v, hlt, hv, rfl⟩ := decreaseChainBalance_eq_some.1 hdec
      have hval : (setInterop (setChainBalance st₀ cfg.thisChain a v) a
          { (setChainBalance st₀ cfg.thisChain a v).interopInfo a with totalWithdrawalsToL1 := w }).chainBalance
            cfg.thisChain a = v := by simp
      obtain ⟨u, hu, huval⟩ := checkedAdd_some_of_lt (a := v) (b := amount)
        (by have := (st₀.chainBalance cfg.thisChain a).isLt; omega)
      refine ⟨setChainBalance (setInterop (setChainBalance st₀ cfg.thisChain a v) a
          { (setChainBalance st₀ cfg.thisChain a v).interopInfo a with totalWithdrawalsToL1 := w })
          cfg.thisChain a u, ?_, ?_, rfl, rfl, rfl⟩
      · rw [increaseChainBalance_eq_some]
        exact ⟨u, by rw [hval]; omega, by rw [hval]; exact huval, rfl⟩
      · have hu' : u = st₀.chainBalance cfg.thisChain a := Fin.ext (by omega)
        subst hu'
        funext c' b
        simp only [setChainBalance_chainBalance, setInterop_chainBalance]
        by_cases hcb : c' = cfg.thisChain ∧ b = a
        · rw [ite_eq_left hcb, hcb.1, hcb.2]
        · rw [ite_eq_right hcb, ite_eq_right hcb]
    · rw [decide_eq_false ho]
      exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  rw [hst₃, Option.bind_some]
  have hl₃ : c = (setInterop st₂ a { st₂.interopInfo a with totalWithdrawalsToL1 := w }).l1ChainId ∧
      st.l1ChainId = (setInterop st₂ a { st₂.interopInfo a with totalWithdrawalsToL1 := w }).l1ChainId := by
    simp [hl₂, hl₀, hc]
  rw [ite_eq_left hl₃]
  have hd₃ : (st₃.interopInfo a).totalSuccessfulDepositsFromL1 =
      (st₀.interopInfo a).totalSuccessfulDepositsFromL1 := by
    rw [hi₃]; simp [hi₂]
  have hw₃ : (st₃.interopInfo a).totalWithdrawalsToL1 = w := by rw [hi₃]; simp
  obtain ⟨d, hd, hdval⟩ := checkedAdd_some_of_lt
    (a := (st₃.interopInfo a).totalSuccessfulDepositsFromL1) (b := amount) (by rw [hd₃]; exact hdlt)
  refine ⟨setInterop st₃ a { st₃.interopInfo a with totalSuccessfulDepositsFromL1 := d },
    addDepositFromL1_eq_some.2 ⟨d, by rw [hd₃]; exact hdlt, hdval, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hw₃, hw, hi₂]
  · simp [hdval, hd₃]
  · simp [hcb₃]
  · simp [hr₃]
  · simp [hs₃]
  · intro b hb
    simp only [setInterop_interopInfo, ite_eq_right hb, hi₃]
    simp [hi₂]

/-! ## The base token -/

theorem BaseFinalizeNeverCreditsChainBalance :
    Properties.BaseFinalizeNeverCreditsChainBalance := by
  intro cfg st st' sl reads caller fromChain amount hr h
  unfold handleFinalizeBaseTokenBridgingOnL2 at h
  by_cases hc : caller ≠ cfg.baseTokenHolder ∧ caller ≠ cfg.l2BaseToken
  · rw [ite_eq_left hc] at h; cases h
  rw [ite_eq_right hc] at h
  by_cases h0 : amount = 0
  · rw [ite_eq_left h0] at h; cases h; rfl
  rw [ite_eq_right h0] at h
  by_cases hb : st.baseTokenAssetId = 0
  · rw [ite_eq_left hb] at h; cases h
  rw [ite_eq_right hb, finalizeInner_eq, registerLegacyTokenIfNeeded_of_registered hr,
    Option.bind_some, ite_eq_right (by decide), Option.bind_some] at h
  by_cases hl : fromChain = st.l1ChainId ∧ sl = st.l1ChainId
  · rw [ite_eq_left hl] at h
    obtain ⟨d, _, _, rfl⟩ := addDepositFromL1_eq_some.1 h
    rfl
  · rw [ite_eq_right hl] at h
    cases h
    rfl

/-! ## Registration and the backfill -/

/-- A flow at `x` that registers `x` keeps every registration. -/
theorem registered_of_frame {st st' : Storage} {x : AssetId} (hf : Frame st st' x)
    (hx : st'.isAssetRegistered x = true) (b : AssetId) (hb : st.isAssetRegistered b = true) :
    st'.isAssetRegistered b = true := by
  by_cases h : b = x
  · subst h; exact hx
  · rw [hf.reg b h]; exact hb

/-- One step keeps every registration; the snapshot of a registered asset changes only by the
backfill. -/
theorem exec_registration {cfg : Config} {sys sys' : Sys} {op : Op}
    (h : exec cfg sys op = some sys') (a : AssetId) (hr : sys.st.isAssetRegistered a = true) :
    sys'.st.isAssetRegistered a = true ∧
    (sys'.st.totalPreV31TotalSupply a = sys.st.totalPreV31TotalSupply a ∨
      (a = sys.st.baseTokenAssetId ∧ sys.st.totalPreV31TotalSupply a = ⟨true, 0⟩ ∧
        sys.st.needBaseTokenTotalSupplyBackfill = true ∧
        sys'.st.needBaseTokenTotalSupplyBackfill = false)) := by
  -- the flows, through their frame at `x`, with `x` registered afterwards and its snapshot kept
  have flow : ∀ {st' : Storage} {x : AssetId}, Frame sys.st st' x →
      st'.isAssetRegistered x = true →
      (sys.st.isAssetRegistered x = true →
        st'.totalPreV31TotalSupply x = sys.st.totalPreV31TotalSupply x) →
      st'.isAssetRegistered a = true ∧
        st'.totalPreV31TotalSupply a = sys.st.totalPreV31TotalSupply a := by
    intro st' x hf hx hsx
    refine ⟨registered_of_frame hf hx a hr, ?_⟩
    by_cases hb : a = x
    · subst hb; exact hsx hr
    · exact hf.snap a hb
  cases op with
  | registerNewToken x =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold registerNewTokenIfNeeded at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    by_cases hx : sys.st.isAssetRegistered x = true
    · rw [ite_eq_left hx] at h; cases h; exact ⟨hr, Or.inl rfl⟩
    rw [ite_eq_right hx] at h
    have hax : a ≠ x := fun he => hx (he ▸ hr)
    by_cases hn : cfg.ntvOriginChainId x = cfg.thisChain
    · rw [ite_eq_left hn] at h; cases h
      exact ⟨by simp [hax, hr], Or.inl (by simp [hax])⟩
    · rw [ite_eq_right hn] at h; cases h
      exact ⟨by simp [hax, hr], Or.inl (by simp [hax])⟩
  | registerBaseDuringUpgrade =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold registerBaseTokenDuringUpgrade at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    by_cases hx : sys.st.isAssetRegistered sys.st.baseTokenAssetId = true
    · rw [ite_eq_left hx] at h; cases h
    rw [ite_eq_right hx] at h
    cases h
    have hax : a ≠ sys.st.baseTokenAssetId := fun he => hx (he ▸ hr)
    exact ⟨by simp [hax, hr], Or.inl (by simp [hax])⟩
  | registerLegacy reads x =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    have h' := registerLegacyToken_eq h
    obtain ⟨h1, h2⟩ := flow (registerLegacyTokenIfNeeded_frame h')
      (registerLegacyTokenIfNeeded_registered h') fun hx => by
        rw [registerLegacyTokenIfNeeded_of_registered hx] at h'
        rw [← Option.some.inj h']
    exact ⟨h1, Or.inl h2⟩
  | initiate reads toChain x amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleInitiateBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    obtain ⟨_, st₁, h₁, _, hreg', hsnap', _⟩ := initiateInner_spec h
    obtain ⟨h1, h2⟩ := flow (initiateInner_frame h) hreg' fun hx => by
      rw [hsnap', registerLegacyTokenIfNeeded_of_registered hx] at *
      rw [← Option.some.inj h₁]
    exact ⟨h1, Or.inl h2⟩
  | initiateBase reads toChain amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleInitiateBaseTokenBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    obtain ⟨_, st₁, h₁, _, hreg', hsnap', _⟩ := initiateInner_spec h
    obtain ⟨h1, h2⟩ := flow (initiateInner_frame h) hreg' fun hx => by
      rw [hsnap', registerLegacyTokenIfNeeded_of_registered hx] at *
      rw [← Option.some.inj h₁]
    exact ⟨h1, Or.inl h2⟩
  | finalize reads fromChain x amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleFinalizeBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    obtain ⟨st₁, h₁, _, hreg', hsnap', _⟩ := finalizeInner_spec h
    obtain ⟨h1, h2⟩ := flow (finalizeInner_frame h) hreg' fun hx => by
      rw [hsnap', registerLegacyTokenIfNeeded_of_registered hx] at *
      rw [← Option.some.inj h₁]
    exact ⟨h1, Or.inl h2⟩
  | finalizeBase reads caller fromChain amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleFinalizeBaseTokenBridgingOnL2 at h
    by_cases hc : caller ≠ cfg.baseTokenHolder ∧ caller ≠ cfg.l2BaseToken
    · rw [ite_eq_left hc] at h; cases h
    rw [ite_eq_right hc] at h
    by_cases h0 : amount = 0
    · rw [ite_eq_left h0] at h; cases h; exact ⟨hr, Or.inl rfl⟩
    rw [ite_eq_right h0] at h
    by_cases hb : sys.st.baseTokenAssetId = 0
    · rw [ite_eq_left hb] at h; cases h
    rw [ite_eq_right hb] at h
    obtain ⟨st₁, h₁, _, hreg', hsnap', _⟩ := finalizeInner_spec h
    obtain ⟨h1, h2⟩ := flow (finalizeInner_frame h) hreg' fun hx => by
      rw [hsnap', registerLegacyTokenIfNeeded_of_registered hx] at *
      rw [← Option.some.inj h₁]
    exact ⟨h1, Or.inl h2⟩
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
    refine ⟨hr, ?_⟩
    by_cases hb : a = sys.st.baseTokenAssetId
    · subst hb
      refine Or.inr ⟨rfl, ?_, by simpa using h1, rfl⟩
      have hs : (sys.st.totalPreV31TotalSupply sys.st.baseTokenAssetId).isSaved = true := by
        simpa using h3
      have ha : (sys.st.totalPreV31TotalSupply sys.st.baseTokenAssetId).amount = 0 := by
        simpa using h4
      cases hsnap : sys.st.totalPreV31TotalSupply sys.st.baseTokenAssetId
      rw [hsnap] at hs ha
      simp only at hs ha
      rw [hs, ha]
    · exact Or.inl (by simp [hb])
  | initL2 need =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold initL2 at h
    by_cases hg : sys.st.guardInitialized = true
    · rw [ite_eq_left hg] at h; cases h
    rw [ite_eq_right hg, ite_eq_right (not_not.2 rfl)] at h
    cases h
    exact ⟨hr, Or.inl rfl⟩
  | setSettlementLayer c =>
    simp only [exec, Option.some.injEq] at h
    subst h
    exact ⟨hr, Or.inl rfl⟩

theorem RegistrationMonotone : Properties.RegistrationMonotone := by
  intro cfg
  refine ⟨fun sys sys' a hreach hr => ?_, fun sys sys' a ⟨op, h⟩ hr => (exec_registration h a hr).2⟩
  induction hreach with
  | refl => exact hr
  | tail _ hstep ih =>
    obtain ⟨op, hop⟩ := hstep
    exact (exec_registration hop a ih).1

theorem BackfillOnlyBaseFromZero : Properties.BackfillOnlyBaseFromZero := by
  intro cfg sys sys' amount h
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
  have hs : (sys.st.totalPreV31TotalSupply sys.st.baseTokenAssetId).isSaved = true := by
    simpa using h3
  have ha : (sys.st.totalPreV31TotalSupply sys.st.baseTokenAssetId).amount = 0 := by
    simpa using h4
  refine ⟨by simpa using h2, ?_, by simpa using h1, rfl, rfl, rfl⟩
  cases hsnap : sys.st.totalPreV31TotalSupply sys.st.baseTokenAssetId
  rw [hsnap] at hs ha
  simp only at hs ha
  rw [hs, ha]

/-- Once `initL2` has run and the flag is clear, both stay so. -/
theorem exec_keeps_flag_clear {cfg : Config} {sys sys' : Sys} {op : Op}
    (h : exec cfg sys op = some sys') (hg : sys.st.guardInitialized = true)
    (hn : sys.st.needBaseTokenTotalSupplyBackfill = false) :
    sys'.st.guardInitialized = true ∧ sys'.st.needBaseTokenTotalSupplyBackfill = false := by
  have flow : ∀ {st' : Storage} {x : AssetId}, Frame sys.st st' x →
      st'.guardInitialized = true ∧ st'.needBaseTokenTotalSupplyBackfill = false :=
    fun hf => ⟨hf.guard.trans hg, hf.need.trans hn⟩
  cases op with
  | registerNewToken x =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold registerNewTokenIfNeeded at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    by_cases hx : sys.st.isAssetRegistered x = true
    · rw [ite_eq_left hx] at h; cases h; exact ⟨hg, hn⟩
    rw [ite_eq_right hx] at h
    by_cases hc : cfg.ntvOriginChainId x = cfg.thisChain
    · rw [ite_eq_left hc] at h; cases h; exact ⟨hg, hn⟩
    · rw [ite_eq_right hc] at h; cases h; exact ⟨hg, hn⟩
  | registerBaseDuringUpgrade =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold registerBaseTokenDuringUpgrade at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    by_cases hx : sys.st.isAssetRegistered sys.st.baseTokenAssetId = true
    · rw [ite_eq_left hx] at h; cases h
    rw [ite_eq_right hx] at h
    cases h
    exact ⟨hg, hn⟩
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
    · rw [ite_eq_left h0] at h; cases h; exact ⟨hg, hn⟩
    rw [ite_eq_right h0] at h
    by_cases hb : sys.st.baseTokenAssetId = 0
    · rw [ite_eq_left hb] at h; cases h
    rw [ite_eq_right hb] at h
    exact flow (finalizeInner_frame h)
  | backfill amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold backFillZKSyncOSBaseTokenV31MigrationData at h
    rw [ite_eq_right (not_not.2 rfl), ite_eq_left hn] at h
    cases h
  | initL2 need =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold initL2 at h
    rw [ite_eq_left hg] at h
    cases h
  | setSettlementLayer c =>
    simp only [exec, Option.some.injEq] at h
    subst h
    exact ⟨hg, hn⟩

theorem BackfillAtMostOnce : Properties.BackfillAtMostOnce := by
  intro cfg sys₀ sys₁ sys₂ amount amount' hinv h₁ hreach
  obtain ⟨_, _, hneed, hst, _, _⟩ := BackfillOnlyBaseFromZero cfg sys₀ sys₁ amount h₁
  have hg₀ : sys₀.st.guardInitialized = true := by
    by_contra hg
    have := hinv.backfillNeedsInit (by simpa using hg)
    rw [this] at hneed
    cases hneed
  have hclear : sys₁.st.guardInitialized = true ∧ sys₁.st.needBaseTokenTotalSupplyBackfill = false := by
    rw [hst]; exact ⟨hg₀, rfl⟩
  have hclear₂ : sys₂.st.guardInitialized = true ∧
      sys₂.st.needBaseTokenTotalSupplyBackfill = false := by
    induction hreach with
    | refl => exact hclear
    | tail _ hstep ih =>
      obtain ⟨op, hop⟩ := hstep
      exact exec_keeps_flag_clear hop ih.1 ih.2
  simp only [exec, backFillZKSyncOSBaseTokenV31MigrationData, ne_eq, not_true_eq_false,
    ite_false, hclear₂.2, ite_true, Option.map_none]

/-! ## Witnesses -/

namespace AccountingExample

/-- Vault `1`, holder `2`, base token `3`, upgrader `4`, this chain `7`.  Asset `3` is native
(token `11`), asset `5` comes from chain `9` (token `12`) and is the base asset `initL2`
installs, asset `6` is native (token `13`). -/
def cfgEx : Config :=
  ⟨1, 2, 3, 4, 7,
    fun a => if a = 3 then 7 else if a = 5 then 9 else if a = 6 then 7 else 0,
    fun a => if a = 3 then 11 else if a = 5 then 12 else if a = 6 then 13 else 0, 100, 5⟩

/-- The same, except that the base asset `initL2` installs is the native asset `3`. -/
def cfgSelfNativeBase : Config := { cfgEx with initBaseAssetId := 3 }

theorem cfgEx_fresh_inv (sl : ChainId) : Inv cfgEx (Sys.fresh sl) :=
  FreshTrackerSatisfiesInv cfgEx sl (by decide) (by decide)

/-- Every asset registered, `L1_CHAIN_ID = 100`, everything else zero. -/
def allRegistered : Storage :=
  ⟨fun _ _ => 0, fun _ => true, 100, 0, fun _ => ⟨0, 0⟩, fun _ => ⟨false, 0⟩, false, false⟩

/-- After `initL2` and the genesis registration of the native base token `3`. -/
def selfNativeBaseSys : Sys :=
  ((exec cfgSelfNativeBase (Sys.fresh 100) (.initL2 false)).bind fun s =>
    exec cfgSelfNativeBase s (.registerNewToken 3)).getD (Sys.fresh 100)

end AccountingExample

open AccountingExample in
theorem ChainBalanceGatesInflow : Properties.ChainBalanceGatesInflow :=
  ⟨cfgEx, 100, ⟨0, 0⟩, 8, 3, _, _, _, cfgEx_fresh_inv 100, by decide, by decide, rfl, by decide,
    rfl, rfl⟩

open AccountingExample in
theorem BaseTokenNativeAsymmetry : Properties.BaseTokenNativeAsymmetry :=
  ⟨cfgSelfNativeBase, selfNativeBaseSys, _, _, ⟨0, 0⟩, 8, by decide, by decide, by decide,
    by unfold ChainBalanceSentinel; decide, by decide, rfl, rfl, by decide,
    by unfold ChainBalanceSentinel; decide⟩

open AccountingExample in
theorem AccountingRunSatisfiable : Properties.AccountingRunSatisfiable :=
  ⟨cfgEx, 100, _, ⟨0, 0⟩, 8, 3, 6, 14, 15, cfgEx_fresh_inv 100,
    Relation.ReflTransGen.tail (Relation.ReflTransGen.tail (Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail Relation.ReflTransGen.refl ⟨.registerNewToken 3, rfl⟩)
      ⟨.initiate ⟨0, 0⟩ 8 3 5, rfl⟩) ⟨.finalize ⟨0, 0⟩ 8 3 2, rfl⟩) ⟨.initiate ⟨0, 10⟩ 8 6 4, rfl⟩,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, ⟨_, rfl⟩, by decide⟩

open AccountingExample in
theorem TrackerRoundTripSatisfiable : Properties.TrackerRoundTripSatisfiable :=
  ⟨cfgEx, Storage.fresh, _, allRegistered, _, 100, ⟨4, 0⟩, 8, 100, 5, 1, by decide, by decide,
    by decide, rfl, by decide, rfl, rfl, by decide⟩

open AccountingExample in
theorem BackfillSatisfiable : Properties.BackfillSatisfiable :=
  ⟨cfgEx, 100, _, _, _, 42, cfgEx_fresh_inv 100, by decide, rfl, rfl, rfl⟩

end Contracts.L2AssetTracker
