import EraSpec.Contracts.L2AssetTracker.Properties.RecoveryNeutrality

/-!
# Proofs: atomic recovery and the `L2AssetTracker` at v35

Proofs of `EraSpec.Contracts.L2AssetTracker.Properties.RecoveryNeutrality`.

* Every tracker write is keyed by one asset (`OnlyAt`), so a step that is not on asset `a` leaves the
  asset view at `a` alone (`exec_frame`, `run_frame`).
* The two inner hooks: the outbound one (`initiateInner_facts`) registers the asset, lowers its chain
  balance if native, and raises `totalWithdrawalsToL1` exactly when the destination and the current
  settlement layer are L1; the inbound one (`finalizeInner_facts`) never touches
  `totalWithdrawalsToL1`.
* A v35 vault recovery (`vaultRecover_v35_effect`) has a non-L1 destination, so the inbound hook's
  counter branch is closed; for the base asset it calls no hook at all.
* The round trip composes these: the recoveries' re-credits add back exactly the bridged-out amount
  (`vaultRecoverAll_nonbase`, `vaultRecoverAll_base`), on an asset view the intermediate run left
  alone.
* The ledger (`run_W`) is an induction over runs: each successful bridge-out logs one event and moves
  the counter by its L1 contribution, nothing else moves it.
* The witnesses and countermodels are concrete runs from `rnSys`, evaluated by `decide` and `rfl`.
-/

namespace Contracts.L2AssetTracker.RecoveryNeutrality

/-! ## Field lemmas for the tracker writes -/

@[simp] theorem Tracker.setChainBalance_isAssetRegistered (t : Tracker) (c : ChainId) (a : AssetId)
    (v : UInt256) : (t.setChainBalance c a v).isAssetRegistered = t.isAssetRegistered := rfl
@[simp] theorem Tracker.setChainBalance_interopInfo (t : Tracker) (c : ChainId) (a : AssetId)
    (v : UInt256) : (t.setChainBalance c a v).interopInfo = t.interopInfo := rfl
@[simp] theorem Tracker.setChainBalance_totalPreV31TotalSupply (t : Tracker) (c : ChainId)
    (a : AssetId) (v : UInt256) :
    (t.setChainBalance c a v).totalPreV31TotalSupply = t.totalPreV31TotalSupply := rfl
theorem Tracker.setChainBalance_chainBalance (t : Tracker) (c : ChainId) (a : AssetId)
    (v : UInt256) (c' : ChainId) (a' : AssetId) :
    (t.setChainBalance c a v).chainBalance c' a' =
      if c' = c ∧ a' = a then v else t.chainBalance c' a' := by
  unfold Tracker.setChainBalance
  by_cases hc : c' = c
  · subst hc
    by_cases ha : a' = a
    · subst ha; simp
    · simp [ha]
  · simp [hc]

@[simp] theorem Tracker.markRegistered_chainBalance (t : Tracker) (a : AssetId)
    (s : SavedTotalSupply) : (t.markRegistered a s).chainBalance = t.chainBalance := rfl
@[simp] theorem Tracker.markRegistered_interopInfo (t : Tracker) (a : AssetId)
    (s : SavedTotalSupply) : (t.markRegistered a s).interopInfo = t.interopInfo := rfl
theorem Tracker.markRegistered_isAssetRegistered (t : Tracker) (a : AssetId)
    (s : SavedTotalSupply) (b : AssetId) :
    (t.markRegistered a s).isAssetRegistered b = if b = a then true else t.isAssetRegistered b := by
  unfold Tracker.markRegistered; simp [Function.update_apply]
theorem Tracker.markRegistered_totalPreV31TotalSupply (t : Tracker) (a : AssetId)
    (s : SavedTotalSupply) (b : AssetId) :
    (t.markRegistered a s).totalPreV31TotalSupply b =
      if b = a then s else t.totalPreV31TotalSupply b := by
  unfold Tracker.markRegistered; simp [Function.update_apply]

@[simp] theorem Tracker.setInterop_chainBalance (t : Tracker) (a : AssetId) (i : InteropL2Info) :
    (t.setInterop a i).chainBalance = t.chainBalance := rfl
@[simp] theorem Tracker.setInterop_isAssetRegistered (t : Tracker) (a : AssetId)
    (i : InteropL2Info) : (t.setInterop a i).isAssetRegistered = t.isAssetRegistered := rfl
@[simp] theorem Tracker.setInterop_totalPreV31TotalSupply (t : Tracker) (a : AssetId)
    (i : InteropL2Info) :
    (t.setInterop a i).totalPreV31TotalSupply = t.totalPreV31TotalSupply := rfl
theorem Tracker.setInterop_interopInfo (t : Tracker) (a : AssetId) (i : InteropL2Info)
    (b : AssetId) : (t.setInterop a i).interopInfo b = if b = a then i else t.interopInfo b := by
  unfold Tracker.setInterop; simp [Function.update_apply]

/-! ## A write only at asset `a` -/

/-- `t'` agrees with `t` at every asset other than `a`, and on every chain other than this one. -/
def OnlyAt (cfg : Config) (t t' : Tracker) (a : AssetId) : Prop :=
  (∀ b, b ≠ a → t'.AgreeAt t b) ∧ (∀ c b, c ≠ cfg.thisChain → t'.chainBalance c b = t.chainBalance c b)

theorem OnlyAt.refl (cfg : Config) (t : Tracker) (a : AssetId) : OnlyAt cfg t t a :=
  ⟨fun _ _ => ⟨fun _ => rfl, rfl, rfl, rfl⟩, fun _ _ _ => rfl⟩

theorem OnlyAt.trans {cfg : Config} {t t' t'' : Tracker} {a : AssetId} (h₁ : OnlyAt cfg t t' a)
    (h₂ : OnlyAt cfg t' t'' a) : OnlyAt cfg t t'' a := by
  refine ⟨fun b hb => ?_, fun c b hc => (h₂.2 c b hc).trans (h₁.2 c b hc)⟩
  obtain ⟨c1, r1, i1, s1⟩ := h₁.1 b hb
  obtain ⟨c2, r2, i2, s2⟩ := h₂.1 b hb
  exact ⟨fun c => (c2 c).trans (c1 c), r2.trans r1, i2.trans i1, s2.trans s1⟩

theorem OnlyAt.setChainBalance (cfg : Config) (t : Tracker) (a : AssetId) (v : UInt256) :
    OnlyAt cfg t (t.setChainBalance cfg.thisChain a v) a := by
  refine ⟨fun b hb => ⟨fun c => ?_, rfl, rfl, rfl⟩, fun c b hc => ?_⟩
  · rw [Tracker.setChainBalance_chainBalance]; simp [hb]
  · rw [Tracker.setChainBalance_chainBalance]; simp [hc]

theorem OnlyAt.markRegistered (cfg : Config) (t : Tracker) (a : AssetId) (s : SavedTotalSupply) :
    OnlyAt cfg t (t.markRegistered a s) a := by
  refine ⟨fun b hb => ⟨fun c => rfl, ?_, rfl, ?_⟩, fun c b _ => rfl⟩
  · rw [Tracker.markRegistered_isAssetRegistered]; simp [hb]
  · rw [Tracker.markRegistered_totalPreV31TotalSupply]; simp [hb]

theorem OnlyAt.setInterop (cfg : Config) (t : Tracker) (a : AssetId) (i : InteropL2Info) :
    OnlyAt cfg t (t.setInterop a i) a := by
  refine ⟨fun b hb => ⟨fun c => rfl, rfl, ?_, rfl⟩, fun c b _ => rfl⟩
  rw [Tracker.setInterop_interopInfo]; simp [hb]

/-! ## Registration -/

theorem registerLegacyInner_spec {cfg : Config} {sys : Sys} {reads : TokenReads} {t t' : Tracker}
    {a : AssetId} {tok : Address} (h : registerLegacyInner cfg sys reads t a tok = some t') :
    t'.isAssetRegistered a = true ∧ t'.interopInfo = t.interopInfo ∧ OnlyAt cfg t t' a ∧
      (∀ c b, t.chainBalance c b ≤ t'.chainBalance c b) := by
  unfold registerLegacyInner at h
  split_ifs at h with h0 htok hnat hcb
  · cases h
    refine ⟨?_, rfl, (OnlyAt.setChainBalance cfg t a _).trans (OnlyAt.markRegistered cfg _ a _), ?_⟩
    · rw [Tracker.markRegistered_isAssetRegistered]; simp
    · intro c b
      simp only [Tracker.markRegistered_chainBalance]
      rw [Tracker.setChainBalance_chainBalance]
      split_ifs with hcb'
      · obtain ⟨rfl, rfl⟩ := hcb'
        rw [not_not.mp hcb]; exact Fin.zero_le _
      · exact le_rfl
  · cases h
    refine ⟨?_, rfl, OnlyAt.markRegistered cfg t a _, fun c b => le_rfl⟩
    rw [Tracker.markRegistered_isAssetRegistered]; simp

theorem registerIfNeeded_spec {cfg : Config} {sys : Sys} {reads : TokenReads} {t t' : Tracker}
    {a : AssetId} {tok : Address} (h : registerIfNeeded cfg sys reads t a tok = some t') :
    t'.isAssetRegistered a = true ∧ t'.interopInfo = t.interopInfo ∧ OnlyAt cfg t t' a ∧
      (∀ c b, t.chainBalance c b ≤ t'.chainBalance c b) ∧
      (t.isAssetRegistered a = true → t' = t) := by
  unfold registerIfNeeded at h
  split_ifs at h with hr
  · cases h; exact ⟨hr, rfl, OnlyAt.refl cfg t a, fun c b => le_rfl, fun _ => rfl⟩
  · obtain ⟨h1, h2, h3, h4⟩ := registerLegacyInner_spec h
    exact ⟨h1, h2, h3, h4, fun h' => absurd h' hr⟩

theorem registerIfNeeded_of_registered {cfg : Config} {sys : Sys} {reads : TokenReads}
    {t : Tracker} {a : AssetId} {tok : Address} (h : t.isAssetRegistered a = true) :
    registerIfNeeded cfg sys reads t a tok = some t := by
  unfold registerIfNeeded; simp [h]

theorem registerNewToken_spec (cfg : Config) (t : Tracker) (a : AssetId) (o : ChainId) :
    (registerNewToken cfg t a o).isAssetRegistered a = true ∧
      (registerNewToken cfg t a o).interopInfo = t.interopInfo ∧
      OnlyAt cfg t (registerNewToken cfg t a o) a ∧
      (∀ c b, t.chainBalance c b ≤ (registerNewToken cfg t a o).chainBalance c b) ∧
      (t.isAssetRegistered a = true → registerNewToken cfg t a o = t) := by
  unfold registerNewToken
  split_ifs with hr ho
  · exact ⟨hr, rfl, OnlyAt.refl cfg t a, fun c b => le_rfl, fun _ => rfl⟩
  · subst ho
    refine ⟨?_, rfl, (OnlyAt.setChainBalance cfg t a _).trans (OnlyAt.markRegistered cfg _ a _),
      ?_, fun h' => absurd h' hr⟩
    · rw [Tracker.markRegistered_isAssetRegistered]; simp
    · intro c b
      simp only [Tracker.markRegistered_chainBalance]
      rw [Tracker.setChainBalance_chainBalance]
      split_ifs
      · exact Fin.le_iff_val_le_val.mpr
          (by have := (t.chainBalance c b).isLt; simp only [MAX_TOKEN_BALANCE]; omega)
      · exact le_rfl
  · refine ⟨?_, rfl, OnlyAt.markRegistered cfg t a _, fun c b => le_rfl, fun h' => absurd h' hr⟩
    rw [Tracker.markRegistered_isAssetRegistered]; simp

/-! ## Chain balance and counters -/

theorem decreaseChainBalance_eq {t t' : Tracker} {c : ChainId} {a : AssetId} {x : UInt256}
    (h : decreaseChainBalance t c a x = some t') :
    ∃ hx : x.val ≤ (t.chainBalance c a).val,
      t' = t.setChainBalance c a ⟨(t.chainBalance c a).val - x.val,
        by have := (t.chainBalance c a).isLt; omega⟩ := by
  unfold decreaseChainBalance checkedSub at h
  split_ifs at h with hx
  · simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨hx, h.symm⟩
  · simp at h

theorem increaseChainBalance_eq {t t' : Tracker} {c : ChainId} {a : AssetId} {x : UInt256}
    (h : increaseChainBalance t c a x = some t') :
    ∃ hx : (t.chainBalance c a).val + x.val < UInt256.size,
      t' = t.setChainBalance c a ⟨(t.chainBalance c a).val + x.val, hx⟩ := by
  unfold increaseChainBalance checkedAdd at h
  split_ifs at h with hx
  · simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨hx, h.symm⟩
  · simp at h

theorem increaseChainBalance_of_lt {t : Tracker} {c : ChainId} {a : AssetId} {x : UInt256}
    (hx : (t.chainBalance c a).val + x.val < UInt256.size) :
    increaseChainBalance t c a x = some (t.setChainBalance c a ⟨_, hx⟩) := by
  unfold increaseChainBalance checkedAdd; rw [dite_eq_left hx]; rfl

theorem addWithdrawalToL1_eq {t t' : Tracker} {a : AssetId} {x : UInt256}
    (h : addWithdrawalToL1 t a x = some t') :
    ∃ hx : (t.interopInfo a).totalWithdrawalsToL1.val + x.val < UInt256.size,
      t' = t.setInterop a { t.interopInfo a with
        totalWithdrawalsToL1 := ⟨(t.interopInfo a).totalWithdrawalsToL1.val + x.val, hx⟩ } := by
  unfold addWithdrawalToL1 checkedAdd at h
  split_ifs at h with hx
  · simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨hx, h.symm⟩
  · simp at h

theorem addDepositFromL1_eq {t t' : Tracker} {a : AssetId} {x : UInt256}
    (h : addDepositFromL1 t a x = some t') :
    ∃ hx : (t.interopInfo a).totalSuccessfulDepositsFromL1.val + x.val < UInt256.size,
      t' = t.setInterop a { t.interopInfo a with
        totalSuccessfulDepositsFromL1 :=
          ⟨(t.interopInfo a).totalSuccessfulDepositsFromL1.val + x.val, hx⟩ } := by
  unfold addDepositFromL1 checkedAdd at h
  split_ifs at h with hx
  · simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨hx, h.symm⟩
  · simp at h

theorem decreaseChainBalance_facts {cfg : Config} {t t' : Tracker} {a : AssetId} {x : UInt256}
    (h : decreaseChainBalance t cfg.thisChain a x = some t') :
    OnlyAt cfg t t' a ∧ t'.isAssetRegistered = t.isAssetRegistered ∧
      t'.interopInfo = t.interopInfo ∧
      (t'.chainBalance cfg.thisChain a).val + x.val = (t.chainBalance cfg.thisChain a).val := by
  obtain ⟨hx, rfl⟩ := decreaseChainBalance_eq h
  refine ⟨OnlyAt.setChainBalance cfg t a _, rfl, rfl, ?_⟩
  rw [Tracker.setChainBalance_chainBalance]; simp; omega

theorem increaseChainBalance_facts {cfg : Config} {t t' : Tracker} {a : AssetId} {x : UInt256}
    (h : increaseChainBalance t cfg.thisChain a x = some t') :
    OnlyAt cfg t t' a ∧ t'.isAssetRegistered = t.isAssetRegistered ∧
      t'.interopInfo = t.interopInfo ∧
      (t'.chainBalance cfg.thisChain a).val = (t.chainBalance cfg.thisChain a).val + x.val ∧
      (∀ c b, t.chainBalance c b ≤ t'.chainBalance c b) := by
  obtain ⟨hx, rfl⟩ := increaseChainBalance_eq h
  refine ⟨OnlyAt.setChainBalance cfg t a _, rfl, rfl, ?_, ?_⟩
  · rw [Tracker.setChainBalance_chainBalance]; simp
  · intro c b
    rw [Tracker.setChainBalance_chainBalance]
    split_ifs with hcb
    · obtain ⟨rfl, rfl⟩ := hcb
      exact Fin.le_iff_val_le_val.mpr (by simp)
    · exact le_rfl

/-! ## The two inner hooks -/

theorem initiateInner_unfold {cfg : Config} {sys : Sys} {reads : TokenReads} {d : ChainId}
    {a : AssetId} {x : UInt256} {o : ChainId} {t' : Tracker}
    (h : initiateInner cfg sys reads d a x o = some t') :
    sys.token a ≠ 0 ∧ ∃ t₁, registerIfNeeded cfg sys reads sys.trk a (sys.token a) = some t₁ ∧
      ∃ t₂, (if o = cfg.thisChain then decreaseChainBalance t₁ cfg.thisChain a x
          else some t₁) = some t₂ ∧
        (if d = cfg.l1 ∧ sys.sl = cfg.l1 then addWithdrawalToL1 t₂ a x else some t₂) = some t' := by
  unfold initiateInner at h
  by_cases htok : sys.token a = 0
  · rw [ite_eq_left htok] at h; cases h
  rw [ite_eq_right htok] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨t₁, h₁, t₂, h₂, h₃⟩ := h
  exact ⟨htok, t₁, h₁, t₂, h₂, h₃⟩

/-- What a successful outbound hook does to the tracker. -/
theorem initiateInner_facts {cfg : Config} {sys : Sys} {reads : TokenReads} {d : ChainId}
    {a : AssetId} {x : UInt256} {o : ChainId} {t' : Tracker}
    (h : initiateInner cfg sys reads d a x o = some t') :
    sys.token a ≠ 0 ∧ t'.isAssetRegistered a = true ∧ OnlyAt cfg sys.trk t' a ∧
      (t'.interopInfo a).totalSuccessfulDepositsFromL1 =
        (sys.trk.interopInfo a).totalSuccessfulDepositsFromL1 ∧
      (t'.interopInfo a).totalWithdrawalsToL1.val =
        (sys.trk.interopInfo a).totalWithdrawalsToL1.val +
          (if d = cfg.l1 ∧ sys.sl = cfg.l1 then x.val else 0) := by
  obtain ⟨htok, t₁, h₁, t₂, h₂, h₃⟩ := initiateInner_unfold h
  obtain ⟨r₁, i₁, o₁, -, -⟩ := registerIfNeeded_spec h₁
  have s₂ : t₂.isAssetRegistered a = true ∧ t₂.interopInfo = t₁.interopInfo ∧
      OnlyAt cfg t₁ t₂ a := by
    split_ifs at h₂ with ho
    · obtain ⟨f₁, f₂, f₃, -⟩ := decreaseChainBalance_facts h₂
      exact ⟨f₂ ▸ r₁, f₃, f₁⟩
    · cases h₂; exact ⟨r₁, rfl, OnlyAt.refl cfg _ a⟩
  obtain ⟨r₂, i₂, o₂⟩ := s₂
  refine ⟨htok, ?_⟩
  split_ifs at h₃ with hl
  · obtain ⟨hx, rfl⟩ := addWithdrawalToL1_eq h₃
    refine ⟨r₂, (o₁.trans o₂).trans (OnlyAt.setInterop cfg _ a _), ?_, ?_⟩
    · rw [Tracker.setInterop_interopInfo]; simp [i₂, i₁]
    · rw [Tracker.setInterop_interopInfo]; simp [i₂, i₁, hl]
  · cases h₃
    refine ⟨r₂, o₁.trans o₂, by rw [i₂, i₁], ?_⟩
    rw [i₂, i₁, ite_eq_right hl]; simp

theorem finalizeInner_unfold {cfg : Config} {sys : Sys} {reads : TokenReads} {c : ChainId}
    {a : AssetId} {x : UInt256} {isNative : Bool} {tok : Address} {t' : Tracker}
    (h : finalizeInner cfg sys reads c a x isNative tok = some t') :
    ∃ t₁, registerIfNeeded cfg sys reads sys.trk a tok = some t₁ ∧
      ∃ t₂, (if isNative = true then increaseChainBalance t₁ cfg.thisChain a x
          else some t₁) = some t₂ ∧
        (if c = cfg.l1 ∧ sys.sl = cfg.l1 then addDepositFromL1 t₂ a x else some t₂) = some t' := by
  unfold finalizeInner at h
  simp only [Option.bind_eq_some_iff] at h
  exact h

/-- What a successful inbound hook does to the tracker. -/
theorem finalizeInner_facts {cfg : Config} {sys : Sys} {reads : TokenReads} {c : ChainId}
    {a : AssetId} {x : UInt256} {isNative : Bool} {tok : Address} {t' : Tracker}
    (h : finalizeInner cfg sys reads c a x isNative tok = some t') :
    t'.isAssetRegistered a = true ∧ OnlyAt cfg sys.trk t' a ∧
      (t'.interopInfo a).totalWithdrawalsToL1 = (sys.trk.interopInfo a).totalWithdrawalsToL1 ∧
      (t'.interopInfo a).totalSuccessfulDepositsFromL1.val =
        (sys.trk.interopInfo a).totalSuccessfulDepositsFromL1.val +
          (if c = cfg.l1 ∧ sys.sl = cfg.l1 then x.val else 0) ∧
      (∀ c' b, sys.trk.chainBalance c' b ≤ t'.chainBalance c' b) := by
  obtain ⟨t₁, h₁, t₂, h₂, h₃⟩ := finalizeInner_unfold h
  obtain ⟨r₁, i₁, o₁, m₁, -⟩ := registerIfNeeded_spec h₁
  have s₂ : t₂.isAssetRegistered a = true ∧ t₂.interopInfo = t₁.interopInfo ∧
      OnlyAt cfg t₁ t₂ a ∧ (∀ c' b, t₁.chainBalance c' b ≤ t₂.chainBalance c' b) := by
    split_ifs at h₂ with hn
    · obtain ⟨f₁, f₂, f₃, -, f₅⟩ := increaseChainBalance_facts h₂
      exact ⟨f₂ ▸ r₁, f₃, f₁, f₅⟩
    · cases h₂; exact ⟨r₁, rfl, OnlyAt.refl cfg _ a, fun _ _ => le_rfl⟩
  obtain ⟨r₂, i₂, o₂, m₂⟩ := s₂
  split_ifs at h₃ with hl
  · obtain ⟨hx, rfl⟩ := addDepositFromL1_eq h₃
    refine ⟨r₂, (o₁.trans o₂).trans (OnlyAt.setInterop cfg _ a _), ?_, ?_,
      fun c' b => (m₁ c' b).trans (m₂ c' b)⟩
    · rw [Tracker.setInterop_interopInfo]; simp [i₂, i₁]
    · rw [Tracker.setInterop_interopInfo]; simp [i₂, i₁, hl]
  · cases h₃
    refine ⟨r₂, o₁.trans o₂, by rw [i₂, i₁], ?_, fun c' b => (m₁ c' b).trans (m₂ c' b)⟩
    rw [i₂, i₁, ite_eq_right hl]; simp

/-! ## The holder, the vault, the router and the manager: shapes of a success -/

theorem holderBurn_eq {cfg : Config} {sys s' : Sys} {reads : TokenReads} {d : ChainId}
    {v : UInt256} (h : holderBurn cfg sys reads d v = some s') :
    ∃ t, trackerInitiateBase cfg sys reads d v = some t ∧
      s' = { sys with trk := t, holder := sys.holder + v.val } := by
  unfold holderBurn at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨t, ht, rfl⟩

theorem holderRecover_eq {cfg : Config} {g : Guards} {sys s' : Sys} {x : UInt256} {d : ChainId}
    (h : holderRecover cfg g sys x d = some s') :
    (x = 0 ∧ s' = sys) ∨
      (x ≠ 0 ∧ ¬ (g.holderL1 = true ∧ d = cfg.l1) ∧
        ¬ (g.holderBase = true ∧ sys.origin cfg.base = cfg.thisChain) ∧ x.val ≤ sys.holder ∧
        s' = { sys with holder := sys.holder - x.val }) := by
  unfold holderRecover at h
  split_ifs at h with h0 h1 h2 h3
  · cases h; exact Or.inl ⟨h0, rfl⟩
  · cases h; exact Or.inr ⟨h0, h1, h2, by omega, rfl⟩

theorem vaultRecover_eq {cfg : Config} {g : Guards} {sys s' : Sys}
    {reads : AssetId → TokenReads} {d : ChainId} {a : AssetId} {md : MintData}
    (h : vaultRecover cfg g sys reads d a (some md) = some s') :
    ¬ (g.vaultL1 = true ∧ d = cfg.l1) ∧
      ¬ (g.vaultBase = true ∧ a = cfg.base ∧ sys.origin a = cfg.thisChain) ∧
      ((a = cfg.base ∧ ∃ s, holderRecover cfg g sys md.amount d = some s ∧
          s' = s.record (.recovered a d md.amount)) ∨
        (a ≠ cfg.base ∧ ∃ t, trackerFinalize cfg sys (reads a) d a md.amount = some t ∧
          (((sys.origin a = cfg.thisChain ∨ sys.token a ≠ 0) ∧
              s' = { sys with trk := t }.record (.recovered a d md.amount)) ∨
            (sys.origin a ≠ cfg.thisChain ∧ sys.token a = 0 ∧ ∃ o tok,
              cfg.deploy a md = some (o, tok) ∧ o ≠ cfg.thisChain ∧
              s' = (vaultSetNewTokenStorage cfg { sys with trk := t } a o tok).record
                (.recovered a d md.amount))))) := by
  simp only [vaultRecover] at h
  by_cases h1 : g.vaultL1 = true ∧ d = cfg.l1
  · rw [ite_eq_left h1] at h; cases h
  rw [ite_eq_right h1] at h
  by_cases h2 : g.vaultBase = true ∧ a = cfg.base ∧ sys.origin a = cfg.thisChain
  · rw [ite_eq_left h2] at h; cases h
  rw [ite_eq_right h2] at h
  refine ⟨h1, h2, ?_⟩
  by_cases hb : a = cfg.base
  · rw [ite_eq_left hb] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact Or.inl ⟨hb, s, hs, rfl⟩
  rw [ite_eq_right hb] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, h⟩ := h
  refine Or.inr ⟨hb, t, ht, ?_⟩
  by_cases hk : sys.origin a = cfg.thisChain ∨ sys.token a ≠ 0
  · rw [ite_eq_left hk] at h; cases h; exact Or.inl ⟨hk, rfl⟩
  rw [ite_eq_right hk] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨⟨o, tok⟩, hp, h⟩ := h
  have hk' : sys.origin a ≠ cfg.thisChain ∧ sys.token a = 0 := by
    simp only [not_or, not_not] at hk; exact hk
  by_cases ho : o = cfg.thisChain
  · rw [ite_eq_left ho] at h; cases h
  rw [ite_eq_right ho] at h
  cases h
  exact Or.inr ⟨hk'.1, hk'.2, o, tok, hp, ho, rfl⟩

theorem routerRecoverAtomicCall_eq {cfg : Config} {g : Guards} {sys s' : Sys}
    {reads : AssetId → TokenReads} {d : ChainId} {data : CallData}
    (h : routerRecoverAtomicCall cfg g sys reads d data = some s') :
    ¬ (g.routerL1 = true ∧ d = cfg.l1) ∧
      (s' = sys ∨ ∃ a m, data = .finalizeDeposit a m ∧ sys.handler a = cfg.ntv ∧
        vaultRecover cfg g sys reads d a m = some s') := by
  cases data with
  | other =>
    unfold routerRecoverAtomicCall at h
    split_ifs at h with h1
    cases h; exact ⟨h1, Or.inl rfl⟩
  | badPayload => cases h
  | finalizeDeposit a m =>
    simp only [routerRecoverAtomicCall] at h
    by_cases h1 : g.routerL1 = true ∧ d = cfg.l1
    · rw [ite_eq_left h1] at h; cases h
    rw [ite_eq_right h1] at h
    by_cases h2 : sys.handler a = 0
    · rw [ite_eq_left h2] at h; cases h
    rw [ite_eq_right h2] at h
    by_cases h3 : sys.handler a = cfg.ntv
    · rw [ite_eq_left h3] at h; exact ⟨h1, Or.inr ⟨a, m, rfl, h3, h⟩⟩
    · rw [ite_eq_right h3] at h; cases h; exact ⟨h1, Or.inl rfl⟩

theorem routerRecoverBase_eq {cfg : Config} {g : Guards} {sys s' : Sys}
    {reads : AssetId → TokenReads} {d : ChainId} {a : AssetId} {r : Address} {x : UInt256}
    (h : routerRecoverBase cfg g sys reads d a r x = some s') :
    ¬ (g.routerL1 = true ∧ d = cfg.l1) ∧
      vaultRecover cfg g sys reads d a (some ⟨r, r, 0, x, []⟩) = some s' := by
  unfold routerRecoverBase at h
  split_ifs at h with h1
  exact ⟨h1, h⟩

theorem recoverCall_eq {cfg : Config} {g : Guards} {reads : AssetId → TokenReads} {d : ChainId}
    {destBase : AssetId} {sys s' : Sys} {c : Call}
    (h : recoverCall cfg g reads d destBase sys c = some s') :
    ∃ s, (if c.sender = cfg.router then routerRecoverAtomicCall cfg g sys reads d c.data
        else some sys) = some s ∧
      (if c.sender ≠ cfg.router ∧ c.value ≠ 0 then
        routerRecoverBase cfg g s reads d destBase c.sender c.value else some s) = some s' := by
  unfold recoverCall at h
  simp only [Option.bind_eq_some_iff] at h
  exact h

/-! ## Agreement at an asset -/

theorem Tracker.AgreeAt.refl (t : Tracker) (a : AssetId) : t.AgreeAt t a :=
  ⟨fun _ => rfl, rfl, rfl, rfl⟩

theorem Tracker.AgreeAt.trans {t₁ t₂ t₃ : Tracker} {a : AssetId} (h₁ : t₁.AgreeAt t₂ a)
    (h₂ : t₂.AgreeAt t₃ a) : t₁.AgreeAt t₃ a :=
  ⟨fun c => (h₁.1 c).trans (h₂.1 c), h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
    h₁.2.2.2.trans h₂.2.2.2⟩

theorem Sys.AgreeAt.refl (cfg : Config) (s : Sys) (a : AssetId) : s.AgreeAt cfg s a :=
  ⟨Tracker.AgreeAt.refl _ _, rfl, rfl, rfl, fun _ => rfl⟩

theorem Sys.AgreeAt.trans {cfg : Config} {s₁ s₂ s₃ : Sys} {a : AssetId} (h₁ : s₁.AgreeAt cfg s₂ a)
    (h₂ : s₂.AgreeAt cfg s₃ a) : s₁.AgreeAt cfg s₃ a :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1, h₁.2.2.2.1.trans h₂.2.2.2.1,
    fun hb => (h₁.2.2.2.2 hb).trans (h₂.2.2.2.2 hb)⟩

theorem vaultRecover_frame {cfg : Config} {g : Guards} {sys s' : Sys}
    {reads : AssetId → TokenReads} {d : ChainId} {a : AssetId} {m : Option MintData}
    (h : vaultRecover cfg g sys reads d a m = some s') (b : AssetId) (hb : b ≠ a) :
    s'.AgreeAt cfg sys b := by
  cases m with
  | none => cases h
  | some md =>
    obtain ⟨-, -, hcase⟩ := vaultRecover_eq h
    rcases hcase with ⟨rfl, s, hs, rfl⟩ | ⟨-, t, ht, hbr⟩
    · rcases holderRecover_eq hs with ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩
      · exact Sys.AgreeAt.refl cfg _ b
      · exact ⟨Tracker.AgreeAt.refl _ _, rfl, rfl, rfl, fun hb' => absurd hb' hb⟩
    · have hf := (finalizeInner_facts ht).2.1
      rcases hbr with ⟨-, rfl⟩ | ⟨-, -, o, tok, -, -, rfl⟩
      · exact ⟨hf.1 b hb, rfl, rfl, rfl, fun _ => rfl⟩
      · refine ⟨((registerNewToken_spec cfg t a o).2.2.1.1 b hb).trans (hf.1 b hb), ?_, ?_, rfl,
          fun _ => rfl⟩
        · show Function.update sys.origin a o b = sys.origin b
          exact Function.update_of_ne hb _ _
        · show Function.update sys.token a tok b = sys.token b
          exact Function.update_of_ne hb _ _

theorem recoverCall_frame {cfg : Config} {g : Guards} {reads : AssetId → TokenReads} {d : ChainId}
    {destBase : AssetId} {sys s' : Sys} {c : Call}
    (h : recoverCall cfg g reads d destBase sys c = some s') (b : AssetId)
    (h₁ : ¬ (c.sender = cfg.router ∧ c.data.asset? = some b))
    (h₂ : ¬ (c.sender ≠ cfg.router ∧ c.value ≠ 0 ∧ destBase = b)) :
    s'.AgreeAt cfg sys b := by
  obtain ⟨s, hs, hs'⟩ := recoverCall_eq h
  have f₁ : s.AgreeAt cfg sys b := by
    split_ifs at hs with hr
    · obtain ⟨-, rfl | ⟨a, m, hd, -, hv⟩⟩ := routerRecoverAtomicCall_eq hs
      · exact Sys.AgreeAt.refl cfg _ b
      · refine vaultRecover_frame hv b ?_
        rintro rfl
        exact h₁ ⟨hr, by rw [hd]; rfl⟩
    · cases hs; exact Sys.AgreeAt.refl cfg _ b
  split_ifs at hs' with hv
  · obtain ⟨-, hv'⟩ := routerRecoverBase_eq hs'
    refine (vaultRecover_frame hv' b ?_).trans f₁
    rintro rfl
    exact h₂ ⟨hv.1, hv.2, rfl⟩
  · cases hs'; exact f₁

theorem recoverCalls_frame {cfg : Config} {g : Guards} {reads : AssetId → TokenReads}
    {d : ChainId} {destBase : AssetId} (b : AssetId) :
    ∀ (calls : List Call) (sys s' : Sys),
      recoverCalls cfg g reads d destBase sys calls = some s' →
      (∀ c ∈ calls, ¬ ((c.sender = cfg.router ∧ c.data.asset? = some b) ∨
        (c.sender ≠ cfg.router ∧ c.value ≠ 0 ∧ destBase = b))) →
      s'.AgreeAt cfg sys b
  | [], sys, s', h, _ => by cases h; exact Sys.AgreeAt.refl cfg _ b
  | c :: cs, sys, s', h, hn => by
    unfold recoverCalls at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, hrest⟩ := h
    have hc := hn c (List.mem_cons_self ..)
    have f₁ := recoverCall_frame hs b (fun h' => hc (Or.inl h')) (fun h' => hc (Or.inr h'))
    exact (recoverCalls_frame b cs s s' hrest (fun c' hc' => hn c' (List.mem_cons_of_mem _ hc'))).trans f₁

theorem recoverBundle_frame {cfg : Config} {g : Guards} {sys s' : Sys}
    {reads : AssetId → TokenReads} {bd : Bundle} (h : recoverBundle cfg g sys reads bd = some s')
    (b : AssetId) (hn : ¬ bd.Touches cfg b) : s'.AgreeAt cfg sys b := by
  unfold recoverBundle at h
  split_ifs at h with hm
  refine recoverCalls_frame b bd.calls sys s' h ?_
  intro c hc hc'
  exact hn ⟨c, hc, hc'⟩

/-- **A step that is not on asset `a` leaves everything about `a` alone.** -/
theorem exec_frame {cfg : Config} {g : Guards} {sys s' : Sys} {op : Op}
    (h : exec cfg g sys op = some s') (a : AssetId) (hn : ¬ op.Touches cfg a) :
    s'.AgreeAt cfg sys a := by
  cases op with
  | vaultRegister a' o tok =>
    simp only [Op.Touches] at hn
    cases h
    refine ⟨(registerNewToken_spec cfg sys.trk a' o).2.2.1.1 a (Ne.symm hn), ?_, ?_, rfl,
      fun _ => rfl⟩
    · show Function.update sys.origin a' o a = sys.origin a
      exact Function.update_of_ne (Ne.symm hn) _ _
    · show Function.update sys.token a' tok a = sys.token a
      exact Function.update_of_ne (Ne.symm hn) _ _
  | vaultUpdateBase o =>
    simp only [Op.Touches] at hn
    cases h
    refine ⟨Tracker.AgreeAt.refl _ _, ?_, ?_, rfl, fun hb => absurd hb hn⟩
    · show Function.update sys.origin cfg.base o a = sys.origin a
      exact Function.update_of_ne hn _ _
    · show Function.update sys.token cfg.base cfg.baseTokenAddr a = sys.token a
      exact Function.update_of_ne hn _ _
  | registerBaseIfNeeded =>
    simp only [Op.Touches] at hn
    cases h
    exact ⟨(registerNewToken_spec cfg sys.trk cfg.base _).2.2.1.1 a hn, rfl, rfl, rfl,
      fun _ => rfl⟩
  | registerLegacy reads a' =>
    simp only [Op.Touches] at hn
    simp only [exec] at h
    split_ifs at h with hr ht
    · cases h; exact Sys.AgreeAt.refl cfg _ a
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨t, ht', rfl⟩ := h
      exact ⟨(registerLegacyInner_spec ht').2.2.1.1 a (Ne.symm hn), rfl, rfl, rfl, fun _ => rfl⟩
  | setHandler a' hd =>
    simp only [Op.Touches] at hn
    cases h
    refine ⟨Tracker.AgreeAt.refl _ _, rfl, rfl, ?_, fun _ => rfl⟩
    show Function.update sys.handler a' hd a = sys.handler a
    exact Function.update_of_ne (Ne.symm hn) _ _
  | setSettlementLayer c =>
    cases h; exact ⟨Tracker.AgreeAt.refl _ _, rfl, rfl, rfl, fun _ => rfl⟩
  | holderVm hv =>
    simp only [Op.Touches] at hn
    cases h; exact ⟨Tracker.AgreeAt.refl _ _, rfl, rfl, rfl, fun hb => absurd hb hn⟩
  | vaultBurn reads d a' x =>
    simp only [Op.Touches] at hn
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    unfold vaultBurn at hs
    split_ifs at hs with h0 hb
    · obtain ⟨t, ht, rfl⟩ := holderBurn_eq hs
      have := (initiateInner_facts ht).2.2.1
      refine ⟨this.1 a (hb.1 ▸ Ne.symm hn), rfl, rfl, rfl, fun hab => ?_⟩
      exact absurd (hab.trans hb.1.symm) (Ne.symm hn)
    · simp only [Option.map_eq_some_iff] at hs
      obtain ⟨t, ht, rfl⟩ := hs
      exact ⟨(initiateInner_facts ht).2.2.1.1 a (Ne.symm hn), rfl, rfl, rfl, fun _ => rfl⟩
  | icBurnBase reads d v =>
    simp only [Op.Touches] at hn
    simp only [exec] at h
    split_ifs at h with h0
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    obtain ⟨t, ht, rfl⟩ := holderBurn_eq hs
    exact ⟨(initiateInner_facts ht).2.2.1.1 a hn, rfl, rfl, rfl, fun hb => absurd hb hn⟩
  | vaultMint reads c a' x =>
    simp only [Op.Touches] at hn
    simp only [exec, vaultMint] at h
    split_ifs at h with hb
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rfl⟩ := h
    exact ⟨(finalizeInner_facts ht).2.1.1 a (Ne.symm hn), rfl, rfl, rfl, fun _ => rfl⟩
  | holderGive reads c x =>
    simp only [Op.Touches] at hn
    simp only [exec, holderGive] at h
    by_cases h0 : x = 0
    · rw [ite_eq_left h0] at h; cases h; exact Sys.AgreeAt.refl cfg _ a
    · rw [ite_eq_right h0] at h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split_ifs at h with hh
      cases h
      unfold trackerFinalizeBase at ht
      split_ifs at ht with hx
      exact ⟨(finalizeInner_facts ht).2.1.1 a hn, rfl, rfl, rfl, fun hb => absurd hb hn⟩
  | baseTokenFinalize reads c x =>
    simp only [Op.Touches] at hn
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rfl⟩ := h
    unfold trackerFinalizeBase at ht
    split_ifs at ht with hx hb0
    · cases ht; exact ⟨Tracker.AgreeAt.refl _ _, rfl, rfl, rfl, fun _ => rfl⟩
    · exact ⟨(finalizeInner_facts ht).2.1.1 a hn, rfl, rfl, rfl, fun _ => rfl⟩
  | claimRefund reads bd =>
    simp only [Op.Touches] at hn
    exact recoverBundle_frame h a hn

/-- **A run with no step on asset `a` leaves everything about `a` alone.** -/
theorem run_frame {cfg : Config} {g : Guards} (a : AssetId) :
    ∀ (ops : List Op) (sys s' : Sys), run cfg g sys ops = some s' →
      (∀ op ∈ ops, ¬ op.Touches cfg a) → s'.AgreeAt cfg sys a
  | [], sys, s', h, _ => by cases h; exact Sys.AgreeAt.refl cfg _ a
  | op :: ops, sys, s', h, hn => by
    unfold run at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, hrest⟩ := h
    exact (run_frame a ops s s' hrest (fun o ho => hn o (List.mem_cons_of_mem _ ho))).trans
      (exec_frame hs a (hn op (List.mem_cons_self ..)))

/-! ## What one vault recovery does, at v35 -/

/-- The exact effect of a successful vault recovery under the v35 checks. -/
theorem vaultRecover_v35_effect {cfg : Config} {sys s' : Sys} {reads : AssetId → TokenReads}
    {d : ChainId} {a : AssetId} {md : MintData}
    (h : vaultRecover cfg Guards.v35 sys reads d a (some md) = some s') :
    d ≠ cfg.l1 ∧ s'.trk.interopInfo = sys.trk.interopInfo ∧ s'.handler = sys.handler ∧
      s'.sl = sys.sl ∧ s'.log = sys.log ++ [.recovered a d md.amount] ∧
      (a = cfg.base → sys.origin a ≠ cfg.thisChain ∧ s'.trk = sys.trk ∧
        s'.holder + md.amount.val = sys.holder ∧ s'.origin = sys.origin ∧ s'.token = sys.token) ∧
      (a ≠ cfg.base → s'.holder = sys.holder ∧
        (∀ b, b ≠ a → s'.origin b = sys.origin b ∧ s'.token b = sys.token b) ∧
        ((sys.origin a = cfg.thisChain ∨ sys.token a ≠ 0) →
          s'.origin = sys.origin ∧ s'.token = sys.token) ∧
        ∃ t₀, registerIfNeeded cfg sys (reads a) sys.trk a (sys.token a) = some t₀ ∧
          (if sys.origin a = cfg.thisChain then increaseChainBalance t₀ cfg.thisChain a md.amount
            else some t₀) = some s'.trk) := by
  obtain ⟨h1, h2, hcase⟩ := vaultRecover_eq h
  have hd : d ≠ cfg.l1 := fun hd => h1 ⟨rfl, hd⟩
  rcases hcase with ⟨rfl, s, hs, hs'⟩ | ⟨hb, t, ht, hbr⟩
  · have ho : sys.origin cfg.base ≠ cfg.thisChain := fun ho => h2 ⟨rfl, rfl, ho⟩
    subst hs'
    rcases holderRecover_eq hs with ⟨h0, hse⟩ | ⟨-, -, -, hle, hse⟩
    · subst hse
      refine ⟨hd, rfl, rfl, rfl, rfl, fun _ => ⟨ho, rfl, ?_, rfl, rfl⟩, fun hb => absurd rfl hb⟩
      simp [Sys.record, h0]
    · subst hse
      refine ⟨hd, rfl, rfl, rfl, rfl, fun _ => ⟨ho, rfl, ?_, rfl, rfl⟩, fun hb => absurd rfl hb⟩
      simp only [Sys.record]
      omega
  · -- the tracker hook, with the counter branch closed by `d ≠ L1`
    have hreg := (finalizeInner_facts ht).1
    obtain ⟨t₀, h₀, t₂, h₂, h₃⟩ := finalizeInner_unfold ht
    have hl : ¬ (d = cfg.l1 ∧ sys.sl = cfg.l1) := fun hl => hd hl.1
    rw [ite_eq_right hl] at h₃
    cases h₃
    have hi₀ := (registerIfNeeded_spec h₀).2.1
    have hit : t.interopInfo = sys.trk.interopInfo := by
      split_ifs at h₂ with hn
      · rw [(increaseChainBalance_facts h₂).2.2.1, hi₀]
      · cases h₂; exact hi₀
    have hit' : (if sys.origin a = cfg.thisChain then
        increaseChainBalance t₀ cfg.thisChain a md.amount else some t₀) = some t := by
      by_cases hn : sys.origin a = cfg.thisChain
      · rw [ite_eq_left hn]; simpa [hn] using h₂
      · rw [ite_eq_right hn]; simpa [hn] using h₂
    rcases hbr with ⟨hk, rfl⟩ | ⟨hno, htok, o, tok, -, -, rfl⟩
    · exact ⟨hd, hit, rfl, rfl, rfl, fun hab => absurd hab hb,
        fun _ => ⟨rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, t₀, h₀, hit'⟩⟩
    · have hnew : registerNewToken cfg t a o = t := (registerNewToken_spec cfg t a o).2.2.2.2 hreg
      refine ⟨hd, ?_, rfl, rfl, rfl, fun hab => absurd hab hb, fun _ => ⟨rfl, ?_, ?_, t₀, h₀, ?_⟩⟩
      · show (registerNewToken cfg t a o).interopInfo = _
        rw [hnew, hit]
      · intro b hba
        exact ⟨Function.update_of_ne hba _ _, Function.update_of_ne hba _ _⟩
      · rintro (h' | h')
        · exact absurd h' hno
        · exact absurd htok h'
      · show _ = some (registerNewToken cfg t a o)
        rw [hnew]; exact hit'
/-! ## The two bridge-outs -/

/-- The shape of a successful `vaultBurn` step. -/
theorem exec_vaultBurn_eq {cfg : Config} {g : Guards} {sys₀ sys₁ : Sys} {reads₀ : TokenReads}
    {d : ChainId} {a : AssetId} {x : UInt256}
    (h : exec cfg g sys₀ (.vaultBurn reads₀ d a x) = some sys₁) :
    x ≠ 0 ∧ ∃ t, initiateInner cfg sys₀ reads₀ d a x (sys₀.origin a) = some t ∧
      sys₁.trk = t ∧ sys₁.origin = sys₀.origin ∧ sys₁.token = sys₀.token ∧
      sys₁.handler = sys₀.handler ∧ sys₁.sl = sys₀.sl ∧
      sys₁.log = sys₀.log ++ [.burned a d x sys₀.sl] ∧
      ((a = cfg.base ∧ sys₀.origin a ≠ cfg.thisChain) → sys₁.holder = sys₀.holder + x.val) ∧
      (¬ (a = cfg.base ∧ sys₀.origin a ≠ cfg.thisChain) → sys₁.holder = sys₀.holder) := by
  simp only [exec, Option.map_eq_some_iff] at h
  obtain ⟨s, hs, rfl⟩ := h
  unfold vaultBurn at hs
  by_cases h0 : x = 0
  · rw [ite_eq_left h0] at hs; cases hs
  rw [ite_eq_right h0] at hs
  refine ⟨h0, ?_⟩
  by_cases hb : a = cfg.base ∧ sys₀.origin a ≠ cfg.thisChain
  · rw [ite_eq_left hb] at hs
    obtain ⟨t, ht, rfl⟩ := holderBurn_eq hs
    obtain ⟨hab, hno⟩ := hb
    subst hab
    exact ⟨t, ht, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun h' => absurd ⟨rfl, hno⟩ h'⟩
  · rw [ite_eq_right hb] at hs
    simp only [Option.map_eq_some_iff] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact ⟨t, ht, rfl, rfl, rfl, rfl, rfl, rfl, fun h' => absurd h' hb, fun _ => rfl⟩

/-- The shape of a successful `icBurnBase` step. -/
theorem exec_icBurnBase_eq {cfg : Config} {g : Guards} {sys₀ sys₁ : Sys} {reads₀ : TokenReads}
    {d : ChainId} {v : UInt256} (h : exec cfg g sys₀ (.icBurnBase reads₀ d v) = some sys₁) :
    v ≠ 0 ∧ ∃ t, initiateInner cfg sys₀ reads₀ d cfg.base v (sys₀.origin cfg.base) = some t ∧
      sys₁.trk = t ∧ sys₁.origin = sys₀.origin ∧ sys₁.token = sys₀.token ∧
      sys₁.handler = sys₀.handler ∧ sys₁.sl = sys₀.sl ∧
      sys₁.log = sys₀.log ++ [.burned cfg.base d v sys₀.sl] ∧
      sys₁.holder = sys₀.holder + v.val := by
  simp only [exec] at h
  by_cases h0 : v = 0
  · rw [ite_eq_left h0] at h; cases h
  rw [ite_eq_right h0] at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨s, hs, rfl⟩ := h
  obtain ⟨t, ht, rfl⟩ := holderBurn_eq hs
  exact ⟨h0, t, ht, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-! ## When a vault recovery succeeds, at v35 -/

theorem trackerFinalize_registered_of_not_l1 {cfg : Config} {sys : Sys} {reads : TokenReads}
    {d : ChainId} {a : AssetId} {x : UInt256} (hd : d ≠ cfg.l1)
    (hreg : sys.trk.isAssetRegistered a = true) :
    trackerFinalize cfg sys reads d a x =
      if sys.origin a = cfg.thisChain then increaseChainBalance sys.trk cfg.thisChain a x
      else some sys.trk := by
  unfold trackerFinalize finalizeInner
  rw [registerIfNeeded_of_registered hreg, Option.bind_some]
  have hl : ¬ (d = cfg.l1 ∧ sys.sl = cfg.l1) := fun h => hd h.1
  by_cases hn : sys.origin a = cfg.thisChain
  · rw [ite_eq_left (by simp [hn] : decide (sys.origin a = cfg.thisChain) = true), ite_eq_left hn]
    cases increaseChainBalance sys.trk cfg.thisChain a x with
    | none => rfl
    | some t => rw [Option.bind_some, ite_eq_right hl]
  · rw [ite_eq_right (by simp [hn] : ¬ decide (sys.origin a = cfg.thisChain) = true),
      ite_eq_right hn, Option.bind_some, ite_eq_right hl]

/-- A v35 recovery of an asset other than the base asset, which the tracker has registered and the
vault records as native or with a token, toward a chain other than L1: it succeeds exactly when the
re-credit of a native asset fits in a word. -/
theorem vaultRecover_v35_nonbase_iff {cfg : Config} {sys : Sys} {reads : AssetId → TokenReads}
    {d : ChainId} {a : AssetId} {md : MintData} (hb : a ≠ cfg.base) (hd : d ≠ cfg.l1)
    (hreg : sys.trk.isAssetRegistered a = true)
    (hk : sys.origin a = cfg.thisChain ∨ sys.token a ≠ 0) :
    (∃ s', vaultRecover cfg Guards.v35 sys reads d a (some md) = some s') ↔
      (sys.origin a = cfg.thisChain →
        (sys.trk.chainBalance cfg.thisChain a).val + md.amount.val < UInt256.size) := by
  constructor
  · rintro ⟨s', h⟩ hn
    obtain ⟨-, -, -, -, -, -, hnon⟩ := vaultRecover_v35_effect h
    obtain ⟨-, -, -, t₀, h₀, hfin⟩ := hnon hb
    rw [registerIfNeeded_of_registered hreg] at h₀
    cases h₀
    rw [ite_eq_left hn] at hfin
    exact (increaseChainBalance_eq hfin).1
  · intro hfit
    have hfin := trackerFinalize_registered_of_not_l1 (reads := reads a) (x := md.amount) hd hreg
    simp only [vaultRecover]
    rw [ite_eq_right (by simp [Guards.v35, hd]), ite_eq_right (by simp [Guards.v35, hb]),
      ite_eq_right hb, hfin]
    by_cases hn : sys.origin a = cfg.thisChain
    · rw [ite_eq_left hn, increaseChainBalance_of_lt (hfit hn), Option.bind_some,
        ite_eq_left hk]
      exact ⟨_, rfl⟩
    · rw [ite_eq_right hn, Option.bind_some, ite_eq_left hk]
      exact ⟨_, rfl⟩

/-- A v35 recovery of the base asset toward a chain other than L1, when the vault does not record the
base asset as native here: it succeeds exactly when the amount is zero or the holder can pay it. -/
theorem vaultRecover_v35_base_iff {cfg : Config} {sys : Sys} {reads : AssetId → TokenReads}
    {d : ChainId} {md : MintData} (hd : d ≠ cfg.l1) (ho : sys.origin cfg.base ≠ cfg.thisChain) :
    (∃ s', vaultRecover cfg Guards.v35 sys reads d cfg.base (some md) = some s') ↔
      (md.amount = 0 ∨ md.amount.val ≤ sys.holder) := by
  simp only [vaultRecover]
  rw [ite_eq_right (by simp [Guards.v35, hd]), ite_eq_right (by simp [Guards.v35, ho]),
    ite_eq_left trivial]
  unfold holderRecover
  by_cases h0 : md.amount = 0
  · rw [ite_eq_left h0]; exact ⟨fun _ => Or.inl h0, fun _ => ⟨_, rfl⟩⟩
  rw [ite_eq_right h0, ite_eq_right (by simp [Guards.v35, hd]),
    ite_eq_right (by simp [Guards.v35, ho])]
  by_cases hh : sys.holder < md.amount.val
  · rw [ite_eq_left hh]
    constructor
    · rintro ⟨s', hs'⟩; simp at hs'
    · rintro (h | h)
      · exact absurd h h0
      · omega
  · rw [ite_eq_right hh]
    exact ⟨fun _ => Or.inr (by omega), fun _ => ⟨_, rfl⟩⟩

/-- After an outbound hook on a native asset, the asset's chain balance has room for the amount. -/
theorem initiateInner_native_room {cfg : Config} {sys : Sys} {reads : TokenReads} {d : ChainId}
    {a : AssetId} {x : UInt256} {t : Tracker}
    (h : initiateInner cfg sys reads d a x cfg.thisChain = some t) :
    (t.chainBalance cfg.thisChain a).val + x.val < UInt256.size := by
  obtain ⟨-, t₀, -, t₂, h₂, h₃⟩ := initiateInner_unfold h
  rw [ite_eq_left rfl] at h₂
  obtain ⟨-, -, -, hcb⟩ := decreaseChainBalance_facts h₂
  have hcb' : t.chainBalance cfg.thisChain a = t₂.chainBalance cfg.thisChain a := by
    split_ifs at h₃ with hl
    · obtain ⟨-, rfl⟩ := addWithdrawalToL1_eq h₃; rfl
    · cases h₃; rfl
  rw [hcb', hcb]
  exact (t₀.chainBalance cfg.thisChain a).isLt

/-! ## The withdrawal counter -/

theorem l1BurnTotal_append (cfg : Config) (a : AssetId) :
    ∀ l₁ l₂ : List Event,
      l1BurnTotal cfg a (l₁ ++ l₂) = l1BurnTotal cfg a l₁ + l1BurnTotal cfg a l₂
  | [], l₂ => by simp [l1BurnTotal]
  | e :: l₁, l₂ => by
    cases e with
    | burned a' d x s =>
      simp only [List.cons_append, l1BurnTotal]
      rw [l1BurnTotal_append cfg a l₁ l₂]; omega
    | recovered a' d x =>
      simp only [List.cons_append, l1BurnTotal]
      exact l1BurnTotal_append cfg a l₁ l₂

theorem l1BurnTotal_of_recovered (cfg : Config) (a : AssetId) :
    ∀ l : List Event, (∀ e ∈ l, ∃ A d x, e = .recovered A d x) → l1BurnTotal cfg a l = 0
  | [], _ => rfl
  | e :: l, h => by
    obtain ⟨A, d, x, rfl⟩ := h e (List.mem_cons_self ..)
    simp only [l1BurnTotal]
    exact l1BurnTotal_of_recovered cfg a l (fun e' he' => h e' (List.mem_cons_of_mem _ he'))

theorem initiateInner_W {cfg : Config} {sys : Sys} {reads : TokenReads} {d : ChainId}
    {A : AssetId} {x : UInt256} {o : ChainId} {t : Tracker}
    (h : initiateInner cfg sys reads d A x o = some t) (a : AssetId) :
    (t.interopInfo a).totalWithdrawalsToL1.val =
      (sys.trk.interopInfo a).totalWithdrawalsToL1.val + l1BurnTotal cfg a [.burned A d x sys.sl] := by
  obtain ⟨-, -, ho, -, hW⟩ := initiateInner_facts h
  by_cases ha : a = A
  · subst ha
    simp only [l1BurnTotal, true_and, add_zero]
    exact hW
  · rw [(ho.1 a ha).2.2.1]
    simp [l1BurnTotal, Ne.symm ha]

theorem finalizeInner_W {cfg : Config} {sys : Sys} {reads : TokenReads} {c : ChainId}
    {A : AssetId} {x : UInt256} {isNative : Bool} {tok : Address} {t : Tracker}
    (h : finalizeInner cfg sys reads c A x isNative tok = some t) (a : AssetId) :
    (t.interopInfo a).totalWithdrawalsToL1 = (sys.trk.interopInfo a).totalWithdrawalsToL1 := by
  obtain ⟨-, ho, hW, -, -⟩ := finalizeInner_facts h
  by_cases ha : a = A
  · subst ha; exact hW
  · rw [(ho.1 a ha).2.2.1]

theorem vaultRecover_W {cfg : Config} {g : Guards} {sys s' : Sys}
    {reads : AssetId → TokenReads} {d : ChainId} {a : AssetId} {md : MintData}
    (h : vaultRecover cfg g sys reads d a (some md) = some s') :
    s'.log = sys.log ++ [.recovered a d md.amount] ∧
      ∀ b, (s'.trk.interopInfo b).totalWithdrawalsToL1 =
        (sys.trk.interopInfo b).totalWithdrawalsToL1 := by
  obtain ⟨-, -, hcase⟩ := vaultRecover_eq h
  rcases hcase with ⟨-, s, hs, rfl⟩ | ⟨-, t, ht, hbr⟩
  · rcases holderRecover_eq hs with ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩
    · exact ⟨rfl, fun _ => rfl⟩
    · exact ⟨rfl, fun _ => rfl⟩
  · have hW := finalizeInner_W ht
    rcases hbr with ⟨-, rfl⟩ | ⟨-, -, o, tok, -, -, rfl⟩
    · exact ⟨rfl, hW⟩
    · refine ⟨rfl, fun b => ?_⟩
      show ((registerNewToken cfg t a o).interopInfo b).totalWithdrawalsToL1 = _
      rw [(registerNewToken_spec cfg t a o).2.1, hW]

theorem recoverCalls_W {cfg : Config} {g : Guards} {reads : AssetId → TokenReads} {d : ChainId}
    {destBase : AssetId} :
    ∀ (calls : List Call) (sys s' : Sys), recoverCalls cfg g reads d destBase sys calls = some s' →
      ∃ new, s'.log = sys.log ++ new ∧ (∀ e ∈ new, ∃ A x, e = .recovered A d x) ∧
        ∀ b, (s'.trk.interopInfo b).totalWithdrawalsToL1 =
          (sys.trk.interopInfo b).totalWithdrawalsToL1
  | [], sys, s', h => by
    cases h; exact ⟨[], by simp, by simp, fun _ => rfl⟩
  | c :: cs, sys, s', h => by
    unfold recoverCalls at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, hrest⟩ := h
    -- one call
    have one : ∃ new, s.log = sys.log ++ new ∧ (∀ e ∈ new, ∃ A x, e = .recovered A d x) ∧
        ∀ b, (s.trk.interopInfo b).totalWithdrawalsToL1 =
          (sys.trk.interopInfo b).totalWithdrawalsToL1 := by
      obtain ⟨s₁, hs₁, hs₂⟩ := recoverCall_eq hs
      have first : ∃ new, s₁.log = sys.log ++ new ∧ (∀ e ∈ new, ∃ A x, e = .recovered A d x) ∧
          ∀ b, (s₁.trk.interopInfo b).totalWithdrawalsToL1 =
            (sys.trk.interopInfo b).totalWithdrawalsToL1 := by
        split_ifs at hs₁ with hr
        · obtain ⟨-, rfl | ⟨a, m, -, -, hv⟩⟩ := routerRecoverAtomicCall_eq hs₁
          · exact ⟨[], by simp, by simp, fun _ => rfl⟩
          · cases m with
            | none => cases hv
            | some md =>
              obtain ⟨hl, hW⟩ := vaultRecover_W hv
              exact ⟨_, hl, by simp, hW⟩
        · cases hs₁; exact ⟨[], by simp, by simp, fun _ => rfl⟩
      obtain ⟨n₁, hl₁, he₁, hW₁⟩ := first
      split_ifs at hs₂ with hv
      · obtain ⟨-, hv'⟩ := routerRecoverBase_eq hs₂
        obtain ⟨hl₂, hW₂⟩ := vaultRecover_W hv'
        refine ⟨n₁ ++ [_], by rw [hl₂, hl₁, List.append_assoc], ?_,
          fun b => (hW₂ b).trans (hW₁ b)⟩
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact he₁ e he
        · rw [List.mem_singleton] at he; exact ⟨_, _, he⟩
      · cases hs₂; exact ⟨n₁, hl₁, he₁, hW₁⟩
    obtain ⟨n₁, hl₁, he₁, hW₁⟩ := one
    obtain ⟨n₂, hl₂, he₂, hW₂⟩ := recoverCalls_W cs s s' hrest
    refine ⟨n₁ ++ n₂, by rw [hl₂, hl₁, List.append_assoc], ?_, fun b => (hW₂ b).trans (hW₁ b)⟩
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact he₁ e he
    · exact he₂ e he

/-- One step: the log grows by the step's events, and `totalWithdrawalsToL1` grows by exactly the
logged L1-bound bridge-outs made while settling on L1.  A recovery event's destination is the
bundle's, which the flow manager's check (if present) keeps off L1. -/
theorem exec_W {cfg : Config} {g : Guards} {sys s' : Sys} {op : Op}
    (h : exec cfg g sys op = some s') :
    ∃ new, s'.log = sys.log ++ new ∧
      (∀ a, (s'.trk.interopInfo a).totalWithdrawalsToL1.val =
        (sys.trk.interopInfo a).totalWithdrawalsToL1.val + l1BurnTotal cfg a new) ∧
      (∀ A d x, Event.recovered A d x ∈ new → ¬ (g.managerL1 = true ∧ d = cfg.l1)) := by
  have none_new : ∀ (s : Sys), s.log = sys.log → s.trk.interopInfo = sys.trk.interopInfo →
      ∃ new, s.log = sys.log ++ new ∧
        (∀ a, (s.trk.interopInfo a).totalWithdrawalsToL1.val =
          (sys.trk.interopInfo a).totalWithdrawalsToL1.val + l1BurnTotal cfg a new) ∧
        (∀ A d x, Event.recovered A d x ∈ new → ¬ (g.managerL1 = true ∧ d = cfg.l1)) := by
    intro s hl hi
    exact ⟨[], by simp [hl], fun a => by simp [hi, l1BurnTotal], by simp⟩
  cases op with
  | vaultRegister a o tok =>
    cases h; exact none_new _ rfl (registerNewToken_spec cfg sys.trk a o).2.1
  | vaultUpdateBase o => cases h; exact none_new _ rfl rfl
  | registerBaseIfNeeded =>
    cases h; exact none_new _ rfl (registerNewToken_spec cfg sys.trk cfg.base _).2.1
  | registerLegacy reads a =>
    simp only [exec] at h
    split_ifs at h with hr ht
    · cases h; exact none_new _ rfl rfl
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨t, ht', rfl⟩ := h
      exact none_new _ rfl (registerLegacyInner_spec ht').2.1
  | setHandler a hd => cases h; exact none_new _ rfl rfl
  | setSettlementLayer c => cases h; exact none_new _ rfl rfl
  | holderVm hv => cases h; exact none_new _ rfl rfl
  | vaultBurn reads d a x =>
    obtain ⟨-, t, ht, htrk, -, -, -, -, hlog, -, -⟩ := exec_vaultBurn_eq h
    refine ⟨_, hlog, fun b => ?_, by simp⟩
    rw [htrk]; exact initiateInner_W ht b
  | icBurnBase reads d v =>
    obtain ⟨-, t, ht, htrk, -, -, -, -, hlog, -⟩ := exec_icBurnBase_eq h
    refine ⟨_, hlog, fun b => ?_, by simp⟩
    rw [htrk]; exact initiateInner_W ht b
  | vaultMint reads c a x =>
    simp only [exec, vaultMint] at h
    split_ifs at h with hb
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rfl⟩ := h
    refine ⟨[], by simp, fun b => ?_, by simp⟩
    simp only [l1BurnTotal, add_zero]
    rw [finalizeInner_W ht b]
  | holderGive reads c x =>
    simp only [exec, holderGive] at h
    by_cases h0 : x = 0
    · rw [ite_eq_left h0] at h; cases h; exact none_new _ rfl rfl
    · rw [ite_eq_right h0] at h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split_ifs at h with hh
      cases h
      unfold trackerFinalizeBase at ht
      split_ifs at ht with hx
      refine ⟨[], by simp, fun b => ?_, by simp⟩
      simp only [l1BurnTotal, add_zero]
      rw [finalizeInner_W ht b]
  | baseTokenFinalize reads c x =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rfl⟩ := h
    unfold trackerFinalizeBase at ht
    split_ifs at ht with hx hb0
    · cases ht; exact none_new _ rfl rfl
    · refine ⟨[], by simp, fun b => ?_, by simp⟩
      simp only [l1BurnTotal, add_zero]
      rw [finalizeInner_W ht b]
  | claimRefund reads bd =>
    simp only [exec] at h
    unfold recoverBundle at h
    split_ifs at h with hm
    obtain ⟨new, hl, he, hW⟩ := recoverCalls_W bd.calls sys s' h
    refine ⟨new, hl, fun b => by rw [hW b, l1BurnTotal_of_recovered cfg b new
      (fun e he' => by obtain ⟨A, x, rfl⟩ := he e he'; exact ⟨A, bd.dest, x, rfl⟩)]; rfl, ?_⟩
    intro A d x hx
    obtain ⟨A', x', he'⟩ := he _ hx
    cases he'
    exact hm

/-- **(iv), along any run.** -/
theorem run_W {cfg : Config} {g : Guards} :
    ∀ (ops : List Op) (sys s' : Sys), run cfg g sys ops = some s' →
      ∃ new, s'.log = sys.log ++ new ∧
        (∀ a, (s'.trk.interopInfo a).totalWithdrawalsToL1.val =
          (sys.trk.interopInfo a).totalWithdrawalsToL1.val + l1BurnTotal cfg a new) ∧
        (∀ A d x, Event.recovered A d x ∈ new → ¬ (g.managerL1 = true ∧ d = cfg.l1))
  | [], sys, s', h => by
    cases h; exact ⟨[], by simp, fun a => by simp [l1BurnTotal], by simp⟩
  | op :: ops, sys, s', h => by
    unfold run at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, hrest⟩ := h
    obtain ⟨n₁, hl₁, hW₁, hr₁⟩ := exec_W hs
    obtain ⟨n₂, hl₂, hW₂, hr₂⟩ := run_W ops s s' hrest
    refine ⟨n₁ ++ n₂, by rw [hl₂, hl₁, List.append_assoc], fun a => ?_, ?_⟩
    · rw [hW₂ a, hW₁ a, l1BurnTotal_append]; omega
    · intro A d x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hr₁ A d x hx
      · exact hr₂ A d x hx

/-! ## A bundle's recoveries of one asset -/

/-- One v35 recovery of a registered asset other than the base asset, with a token. -/
theorem vaultRecover_v35_nonbase_step {cfg : Config} {s s₁ : Sys} {reads : AssetId → TokenReads}
    {d : ChainId} {a : AssetId} {md : MintData} (hb : a ≠ cfg.base)
    (hreg : s.trk.isAssetRegistered a = true) (htok : s.token a ≠ 0)
    (h : vaultRecover cfg Guards.v35 s reads d a (some md) = some s₁) :
    d ≠ cfg.l1 ∧ s₁.holder = s.holder ∧ s₁.origin = s.origin ∧ s₁.token = s.token ∧
      s₁.handler = s.handler ∧
      (s.origin a = cfg.thisChain → ∃ hx : (s.trk.chainBalance cfg.thisChain a).val +
          md.amount.val < UInt256.size,
        s₁.trk = s.trk.setChainBalance cfg.thisChain a ⟨_, hx⟩) ∧
      (s.origin a ≠ cfg.thisChain → s₁.trk = s.trk) := by
  obtain ⟨hd, -, hh, -, -, -, hnon⟩ := vaultRecover_v35_effect h
  obtain ⟨hhold, -, hreg', t₀, h₀, hfin⟩ := hnon hb
  obtain ⟨ho, ht⟩ := hreg' (Or.inr htok)
  rw [registerIfNeeded_of_registered hreg] at h₀
  cases h₀
  refine ⟨hd, hhold, ho, ht, hh, fun hn => ?_, fun hn => ?_⟩
  · rw [ite_eq_left hn] at hfin
    exact increaseChainBalance_eq hfin
  · rw [ite_eq_right hn] at hfin
    exact (Option.some.inj hfin).symm

theorem list_sum_cons_amount (md : MintData) (mds : List MintData) :
    ((md :: mds).map fun m => m.amount.val).sum = md.amount.val + (mds.map fun m => m.amount.val).sum := by
  simp

/-- v35 recoveries of a registered asset other than the base asset, with a token: the asset's chain
balance here rises by the total if the vault records it as native here, and nothing else about it
changes. -/
theorem vaultRecoverAll_nonbase {cfg : Config} {reads : AssetId → TokenReads} {d : ChainId}
    {a : AssetId} (hb : a ≠ cfg.base) :
    ∀ (mds : List MintData) (s s' : Sys), vaultRecoverAll cfg Guards.v35 s reads d a mds = some s' →
      s.trk.isAssetRegistered a = true → s.token a ≠ 0 →
      (mds ≠ [] → d ≠ cfg.l1) ∧
      (∀ c, c ≠ cfg.thisChain → s'.trk.chainBalance c a = s.trk.chainBalance c a) ∧
      (s.origin a = cfg.thisChain → (s'.trk.chainBalance cfg.thisChain a).val =
        (s.trk.chainBalance cfg.thisChain a).val + (mds.map fun m => m.amount.val).sum) ∧
      (s.origin a ≠ cfg.thisChain →
        s'.trk.chainBalance cfg.thisChain a = s.trk.chainBalance cfg.thisChain a) ∧
      s'.trk.isAssetRegistered a = true ∧ s'.trk.interopInfo a = s.trk.interopInfo a ∧
      s'.trk.totalPreV31TotalSupply a = s.trk.totalPreV31TotalSupply a ∧
      s'.origin a = s.origin a ∧ s'.token a = s.token a ∧ s'.handler a = s.handler a ∧
      s'.holder = s.holder ∧ (∀ b, b ≠ a → s'.AgreeAt cfg s b)
  | [], s, s', h, hreg, _ => by
    cases h
    exact ⟨fun h' => absurd rfl h', fun _ _ => rfl, fun _ => by simp, fun _ => rfl, hreg, rfl, rfl,
      rfl, rfl, rfl, rfl, fun b _ => Sys.AgreeAt.refl cfg _ b⟩
  | md :: mds, s, s', h, hreg, htok => by
    unfold vaultRecoverAll at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, hrest⟩ := h
    obtain ⟨hd, hhold, ho, ht, hh, hnat, hnn⟩ := vaultRecover_v35_nonbase_step hb hreg htok h₁
    have hfr₁ := vaultRecover_frame h₁
    -- facts about `s₁` at `a`
    have hreg₁ : s₁.trk.isAssetRegistered a = true := by
      by_cases hn : s.origin a = cfg.thisChain
      · obtain ⟨_, he⟩ := hnat hn; rw [he]; exact hreg
      · rw [hnn hn]; exact hreg
    have htok₁ : s₁.token a ≠ 0 := by rw [ht]; exact htok
    obtain ⟨-, hc', hn', hnn', hreg', hi', hp', ho', ht', hh', hhold', hfr'⟩ :=
      vaultRecoverAll_nonbase hb mds s₁ s' hrest hreg₁ htok₁
    -- what the first recovery did to the other entries of `a`
    have hsame : (∀ c, c ≠ cfg.thisChain → s₁.trk.chainBalance c a = s.trk.chainBalance c a) ∧
        s₁.trk.interopInfo a = s.trk.interopInfo a ∧
        s₁.trk.totalPreV31TotalSupply a = s.trk.totalPreV31TotalSupply a := by
      by_cases hn : s.origin a = cfg.thisChain
      · obtain ⟨_, he⟩ := hnat hn
        rw [he]
        refine ⟨fun c hc => ?_, rfl, rfl⟩
        rw [Tracker.setChainBalance_chainBalance]; simp [hc]
      · rw [hnn hn]; exact ⟨fun _ _ => rfl, rfl, rfl⟩
    have ho₁ : s₁.origin a = s.origin a := by rw [ho]
    refine ⟨fun _ => hd, fun c hc => (hc' c hc).trans (hsame.1 c hc), fun hn => ?_, fun hn => ?_,
      hreg', hi'.trans hsame.2.1, hp'.trans hsame.2.2, ho'.trans ho₁, ht'.trans (by rw [ht]),
      hh'.trans (by rw [hh]), hhold'.trans hhold,
      fun b hba => (hfr' b hba).trans (hfr₁ b hba)⟩
    · obtain ⟨_, he⟩ := hnat hn
      rw [hn' (ho₁.trans hn), list_sum_cons_amount, he, Tracker.setChainBalance_chainBalance]
      simp only [and_self, ite_true]
      omega
    · rw [hnn' (fun h' => hn (ho₁.symm.trans h')), hnn hn]

/-- v35 recoveries of the base asset: the tracker and the registry are untouched, and the holder
pays the total. -/
theorem vaultRecoverAll_base {cfg : Config} {reads : AssetId → TokenReads} {d : ChainId} :
    ∀ (mds : List MintData) (s s' : Sys),
      vaultRecoverAll cfg Guards.v35 s reads d cfg.base mds = some s' →
      (mds ≠ [] → d ≠ cfg.l1 ∧ s.origin cfg.base ≠ cfg.thisChain) ∧ s'.trk = s.trk ∧
      s'.origin = s.origin ∧ s'.token = s.token ∧ s'.handler = s.handler ∧
      s'.holder + (mds.map fun m => m.amount.val).sum = s.holder
  | [], s, s', h => by
    cases h; exact ⟨fun h' => absurd rfl h', rfl, rfl, rfl, rfl, by simp⟩
  | md :: mds, s, s', h => by
    unfold vaultRecoverAll at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, hrest⟩ := h
    obtain ⟨hd, -, hh, -, -, hbase, -⟩ := vaultRecover_v35_effect h₁
    obtain ⟨ho, htrk, hhold, horig, htok⟩ := hbase rfl
    obtain ⟨-, htrk', horig', htok', hh', hhold'⟩ := vaultRecoverAll_base mds s₁ s' hrest
    refine ⟨fun _ => ⟨hd, ho⟩, htrk'.trans htrk, horig'.trans horig, htok'.trans htok,
      hh'.trans hh, ?_⟩
    rw [list_sum_cons_amount]; omega

/-- **(ii) for the vault's bridge-out, with the recoveries of one bundle.** -/
theorem vaultBurn_then_recoverAll {cfg : Config} {sys₀ sys₁ sys₂ sys₃ : Sys}
    {reads₀ : TokenReads} {reads : AssetId → TokenReads} {d : ChainId} {a : AssetId} {x : UInt256}
    {mid : List Op} {mds : List MintData}
    (hb : exec cfg Guards.v35 sys₀ (.vaultBurn reads₀ d a x) = some sys₁)
    (hm : run cfg Guards.v35 sys₁ mid = some sys₂) (hn : ∀ op ∈ mid, ¬ op.Touches cfg a)
    (hsum : (mds.map fun m => m.amount.val).sum = x.val)
    (hr : vaultRecoverAll cfg Guards.v35 sys₂ reads d a mds = some sys₃) :
    ∃ t₀, registerIfNeeded cfg sys₀ reads₀ sys₀.trk a (sys₀.token a) = some t₀ ∧
      sys₃.trk.AgreeAt t₀ a ∧ sys₃.origin a = sys₀.origin a ∧ sys₃.token a = sys₀.token a ∧
      sys₃.handler a = sys₀.handler a ∧ (∀ b, b ≠ a → sys₃.AgreeAt cfg sys₂ b) ∧
      (a = cfg.base → sys₃.holder = sys₀.holder) ∧
      (a ≠ cfg.base → sys₁.holder = sys₀.holder ∧ sys₃.holder = sys₂.holder) := by
  obtain ⟨hx0, t, ht, h₁trk, h₁o, h₁t, h₁h, -, -, hhb, hht⟩ := exec_vaultBurn_eq hb
  have hne : mds ≠ [] := by
    rintro rfl
    have hx : x.val = 0 := by simpa using hsum.symm
    exact hx0 (Fin.ext (by rw [hx]; rfl))
  obtain ⟨hA, hO, hT, hH, hHold⟩ := run_frame a mid sys₁ sys₂ hm hn
  have hO' : sys₂.origin a = sys₀.origin a := hO.trans (by rw [h₁o])
  have hT' : sys₂.token a = sys₀.token a := hT.trans (by rw [h₁t])
  have hH' : sys₂.handler a = sys₀.handler a := hH.trans (by rw [h₁h])
  rw [h₁trk] at hA
  obtain ⟨htok, t₀, h₀, t₂, h₂, h₃⟩ := initiateInner_unfold ht
  have hreg₀ := (registerIfNeeded_spec h₀).1
  by_cases hab : a = cfg.base
  · subst hab
    obtain ⟨hpre, htrk, horig, htok', hh, hhold⟩ := vaultRecoverAll_base mds sys₂ sys₃ hr
    obtain ⟨hd, ho⟩ := hpre hne
    have ho₀ : sys₀.origin cfg.base ≠ cfg.thisChain := hO' ▸ ho
    have hl : ¬ (d = cfg.l1 ∧ sys₀.sl = cfg.l1) := fun h' => hd h'.1
    rw [ite_eq_right hl] at h₃
    rw [ite_eq_right ho₀] at h₂
    have e₂ := Option.some.inj h₂
    subst e₂
    have e₃ := Option.some.inj h₃
    subst e₃
    refine ⟨t₀, h₀, by rw [htrk]; exact hA, by rw [horig, hO'], by rw [htok', hT'],
      by rw [hh, hH'], ?_, fun _ => ?_, fun h' => absurd rfl h'⟩
    · intro b hba
      exact ⟨by rw [htrk]; exact Tracker.AgreeAt.refl _ _, by rw [horig], by rw [htok'],
        by rw [hh], fun hb' => absurd hb' hba⟩
    · have h1 := hhb ⟨rfl, ho₀⟩
      have h2 := hHold rfl
      rw [hsum] at hhold
      omega
  · have hreg₂ : sys₂.trk.isAssetRegistered a = true := by
      rw [hA.2.1]; exact (initiateInner_facts ht).2.1
    obtain ⟨hpre, hc', hn', hnn', hreg', hi', hp', ho', ht', hh', hhold', hfr'⟩ :=
      vaultRecoverAll_nonbase hab mds sys₂ sys₃ hr hreg₂ (hT' ▸ htok)
    have hd := hpre hne
    have hl : ¬ (d = cfg.l1 ∧ sys₀.sl = cfg.l1) := fun h' => hd h'.1
    rw [ite_eq_right hl] at h₃
    have e₃ := Option.some.inj h₃
    subst e₃
    refine ⟨t₀, h₀, ⟨fun c => ?_, ?_, ?_, ?_⟩, by rw [ho', hO'], by rw [ht', hT'],
      by rw [hh', hH'], hfr', fun h' => absurd h' hab, fun _ => ⟨hht (fun h' => hab h'.1), hhold'⟩⟩
    · by_cases hc : c = cfg.thisChain
      · subst hc
        by_cases hnat : sys₀.origin a = cfg.thisChain
        · rw [ite_eq_left hnat] at h₂
          obtain ⟨hdec, he⟩ := decreaseChainBalance_eq h₂
          apply Fin.ext
          rw [hn' (hO'.trans hnat), hA.1 cfg.thisChain, hsum, he,
            Tracker.setChainBalance_chainBalance]
          simp only [and_self, ite_true]
          omega
        · rw [ite_eq_right hnat] at h₂
          rw [hnn' (fun h' => hnat (hO'.symm.trans h')), hA.1 cfg.thisChain]
          rw [← Option.some.inj h₂]
      · rw [hc' c hc, hA.1 c]
        by_cases hnat : sys₀.origin a = cfg.thisChain
        · rw [ite_eq_left hnat] at h₂
          rw [(decreaseChainBalance_facts h₂).1.2 c a hc]
        · rw [ite_eq_right hnat] at h₂
          rw [← Option.some.inj h₂]
    · rw [hreg', (registerIfNeeded_spec h₀).1]
    · rw [hi', hA.2.2.1]
      by_cases hnat : sys₀.origin a = cfg.thisChain
      · rw [ite_eq_left hnat] at h₂
        rw [(decreaseChainBalance_facts h₂).2.2.1]
      · rw [ite_eq_right hnat] at h₂
        rw [← Option.some.inj h₂]
    · rw [hp', hA.2.2.2]
      by_cases hnat : sys₀.origin a = cfg.thisChain
      · rw [ite_eq_left hnat] at h₂
        obtain ⟨_, he⟩ := decreaseChainBalance_eq h₂
        rw [he]; rfl
      · rw [ite_eq_right hnat] at h₂
        rw [← Option.some.inj h₂]

/-- **(ii) for the interop center's same-base-token value burn, with the recoveries of one
bundle.** -/
theorem icBurnBase_then_recoverAll {cfg : Config} {sys₀ sys₁ sys₂ sys₃ : Sys}
    {reads₀ : TokenReads} {reads : AssetId → TokenReads} {d : ChainId} {v : UInt256}
    {mid : List Op} {mds : List MintData}
    (hb : exec cfg Guards.v35 sys₀ (.icBurnBase reads₀ d v) = some sys₁)
    (hm : run cfg Guards.v35 sys₁ mid = some sys₂) (hn : ∀ op ∈ mid, ¬ op.Touches cfg cfg.base)
    (hsum : (mds.map fun m => m.amount.val).sum = v.val)
    (hr : vaultRecoverAll cfg Guards.v35 sys₂ reads d cfg.base mds = some sys₃) :
    ∃ t₀, registerIfNeeded cfg sys₀ reads₀ sys₀.trk cfg.base (sys₀.token cfg.base) = some t₀ ∧
      sys₃.trk.AgreeAt t₀ cfg.base ∧ sys₃.origin cfg.base = sys₀.origin cfg.base ∧
      sys₃.token cfg.base = sys₀.token cfg.base ∧ sys₃.handler cfg.base = sys₀.handler cfg.base ∧
      (∀ b, b ≠ cfg.base → sys₃.AgreeAt cfg sys₂ b) ∧ sys₃.holder = sys₀.holder := by
  obtain ⟨hv0, t, ht, h₁trk, h₁o, h₁t, h₁h, -, -, hh⟩ := exec_icBurnBase_eq hb
  have hne : mds ≠ [] := by
    rintro rfl
    have hx : v.val = 0 := by simpa using hsum.symm
    exact hv0 (Fin.ext (by rw [hx]; rfl))
  obtain ⟨hA, hO, hT, hH, hHold⟩ := run_frame cfg.base mid sys₁ sys₂ hm hn
  have hO' : sys₂.origin cfg.base = sys₀.origin cfg.base := hO.trans (by rw [h₁o])
  have hT' : sys₂.token cfg.base = sys₀.token cfg.base := hT.trans (by rw [h₁t])
  have hH' : sys₂.handler cfg.base = sys₀.handler cfg.base := hH.trans (by rw [h₁h])
  rw [h₁trk] at hA
  obtain ⟨-, t₀, h₀, t₂, h₂, h₃⟩ := initiateInner_unfold ht
  obtain ⟨hpre, htrk, horig, htok', hh', hhold⟩ := vaultRecoverAll_base mds sys₂ sys₃ hr
  obtain ⟨hd, ho⟩ := hpre hne
  have ho₀ : sys₀.origin cfg.base ≠ cfg.thisChain := hO' ▸ ho
  have hl : ¬ (d = cfg.l1 ∧ sys₀.sl = cfg.l1) := fun h' => hd h'.1
  rw [ite_eq_right hl] at h₃
  rw [ite_eq_right ho₀] at h₂
  have e₂ := Option.some.inj h₂
  subst e₂
  have e₃ := Option.some.inj h₃
  subst e₃
  refine ⟨t₀, h₀, by rw [htrk]; exact hA, by rw [horig, hO'], by rw [htok', hT'],
    by rw [hh', hH'], fun b hba => ⟨by rw [htrk]; exact Tracker.AgreeAt.refl _ _, by rw [horig],
      by rw [htok'], by rw [hh'], fun hb' => absurd hb' hba⟩, ?_⟩
  have h2 := hHold rfl
  rw [hsum] at hhold
  omega

/-! ## When a bundle's recoveries succeed -/

/-- v35 recoveries of a registered asset other than the base asset, with a token, toward a chain
other than L1: they all succeed when the native re-credit of the total fits. -/
theorem vaultRecoverAll_nonbase_succeeds {cfg : Config} {reads : AssetId → TokenReads}
    {d : ChainId} {a : AssetId} (hb : a ≠ cfg.base) (hd : d ≠ cfg.l1) :
    ∀ (mds : List MintData) (s : Sys), s.trk.isAssetRegistered a = true → s.token a ≠ 0 →
      (s.origin a = cfg.thisChain → (s.trk.chainBalance cfg.thisChain a).val +
        (mds.map fun m => m.amount.val).sum < UInt256.size) →
      ∃ s', vaultRecoverAll cfg Guards.v35 s reads d a mds = some s'
  | [], s, _, _, _ => ⟨s, rfl⟩
  | md :: mds, s, hreg, htok, hfit => by
    rw [list_sum_cons_amount] at hfit
    obtain ⟨s₁, h₁⟩ := (vaultRecover_v35_nonbase_iff (reads := reads) (md := md) hb hd hreg
      (Or.inr htok)).mpr (fun hn => by have := hfit hn; omega)
    obtain ⟨-, -, ho, ht, -, hnat, hnn⟩ := vaultRecover_v35_nonbase_step hb hreg htok h₁
    have hreg₁ : s₁.trk.isAssetRegistered a = true := by
      by_cases hn : s.origin a = cfg.thisChain
      · obtain ⟨_, he⟩ := hnat hn; rw [he]; exact hreg
      · rw [hnn hn]; exact hreg
    have htok₁ : s₁.token a ≠ 0 := by rw [ht]; exact htok
    have hfit₁ : s₁.origin a = cfg.thisChain → (s₁.trk.chainBalance cfg.thisChain a).val +
        (mds.map fun m => m.amount.val).sum < UInt256.size := by
      intro hn₁
      have hn : s.origin a = cfg.thisChain := by rw [← ho]; exact hn₁
      obtain ⟨_, he⟩ := hnat hn
      rw [he, Tracker.setChainBalance_chainBalance]
      simp only [and_self, ite_true]
      have := hfit hn
      omega
    obtain ⟨s', h'⟩ := vaultRecoverAll_nonbase_succeeds hb hd mds s₁ hreg₁ htok₁ hfit₁
    exact ⟨s', by unfold vaultRecoverAll; rw [h₁, Option.bind_some]; exact h'⟩

/-- v35 recoveries of the base asset toward a chain other than L1, when the vault does not record the
base asset as native here: they all succeed when the holder can pay the total. -/
theorem vaultRecoverAll_base_succeeds {cfg : Config} {reads : AssetId → TokenReads}
    {d : ChainId} (hd : d ≠ cfg.l1) :
    ∀ (mds : List MintData) (s : Sys), s.origin cfg.base ≠ cfg.thisChain →
      (mds.map fun m => m.amount.val).sum ≤ s.holder →
      ∃ s', vaultRecoverAll cfg Guards.v35 s reads d cfg.base mds = some s'
  | [], s, _, _ => ⟨s, rfl⟩
  | md :: mds, s, ho, hle => by
    rw [list_sum_cons_amount] at hle
    obtain ⟨s₁, h₁⟩ := (vaultRecover_v35_base_iff (reads := reads) (md := md) hd ho).mpr
      (Or.inr (by omega))
    obtain ⟨-, -, -, -, -, hbase, -⟩ := vaultRecover_v35_effect h₁
    obtain ⟨-, -, hhold, horig, -⟩ := hbase rfl
    obtain ⟨s', h'⟩ := vaultRecoverAll_base_succeeds hd mds s₁ (by rw [horig]; exact ho)
      (by omega)
    exact ⟨s', by unfold vaultRecoverAll; rw [h₁, Option.bind_some]; exact h'⟩

/-- **(ii) enabledness, with the recoveries of one bundle.** -/
theorem recoverAll_after_vaultBurn {cfg : Config} {sys₀ sys₁ sys₂ : Sys} {reads₀ : TokenReads}
    {reads : AssetId → TokenReads} {d : ChainId} {a : AssetId} {x : UInt256} {mid : List Op}
    {mds : List MintData}
    (hb : exec cfg Guards.v35 sys₀ (.vaultBurn reads₀ d a x) = some sys₁)
    (hm : run cfg Guards.v35 sys₁ mid = some sys₂) (hn : ∀ op ∈ mid, ¬ op.Touches cfg a)
    (hd : d ≠ cfg.l1) (ho : a = cfg.base → sys₀.origin a ≠ cfg.thisChain)
    (hsum : (mds.map fun m => m.amount.val).sum = x.val) :
    ∃ sys₃, vaultRecoverAll cfg Guards.v35 sys₂ reads d a mds = some sys₃ := by
  obtain ⟨-, t, ht, h₁trk, h₁o, h₁t, -, -, -, hhb, -⟩ := exec_vaultBurn_eq hb
  obtain ⟨hA, hO, hT, -, hHold⟩ := run_frame a mid sys₁ sys₂ hm hn
  have hO' : sys₂.origin a = sys₀.origin a := hO.trans (by rw [h₁o])
  have hT' : sys₂.token a = sys₀.token a := hT.trans (by rw [h₁t])
  obtain ⟨htok, hreg, -⟩ := initiateInner_facts ht
  by_cases hab : a = cfg.base
  · subst hab
    have ho' := ho rfl
    exact vaultRecoverAll_base_succeeds hd mds sys₂ (hO' ▸ ho')
      (by rw [hHold rfl, hhb ⟨rfl, ho'⟩, hsum]; omega)
  · have hreg₂ : sys₂.trk.isAssetRegistered a = true := by rw [hA.2.1, h₁trk, hreg]
    refine vaultRecoverAll_nonbase_succeeds hab hd mds sys₂ hreg₂ (hT' ▸ htok) ?_
    intro hnat
    rw [hA.1 cfg.thisChain, h₁trk, hsum]
    rw [hO'] at hnat
    rw [hnat] at ht
    exact initiateInner_native_room ht

/-- **(ii) enabledness for the interop center's value burn, with the recoveries of one bundle.** -/
theorem recoverAll_after_icBurnBase {cfg : Config} {sys₀ sys₁ sys₂ : Sys} {reads₀ : TokenReads}
    {reads : AssetId → TokenReads} {d : ChainId} {v : UInt256} {mid : List Op}
    {mds : List MintData}
    (hb : exec cfg Guards.v35 sys₀ (.icBurnBase reads₀ d v) = some sys₁)
    (hm : run cfg Guards.v35 sys₁ mid = some sys₂) (hn : ∀ op ∈ mid, ¬ op.Touches cfg cfg.base)
    (hd : d ≠ cfg.l1) (ho : sys₀.origin cfg.base ≠ cfg.thisChain)
    (hsum : (mds.map fun m => m.amount.val).sum = v.val) :
    ∃ sys₃, vaultRecoverAll cfg Guards.v35 sys₂ reads d cfg.base mds = some sys₃ := by
  obtain ⟨-, t, -, -, h₁o, -, -, -, -, hh⟩ := exec_icBurnBase_eq hb
  obtain ⟨-, hO, -, -, hHold⟩ := run_frame cfg.base mid sys₁ sys₂ hm hn
  have hO' : sys₂.origin cfg.base = sys₀.origin cfg.base := hO.trans (by rw [h₁o])
  exact vaultRecoverAll_base_succeeds hd mds sys₂ (hO' ▸ ho)
    (by rw [hHold rfl, hh, hsum]; omega)

/-! ## A claim is a sequence of vault recoveries -/

theorem routerRecoverBase_of_not_l1 {cfg : Config} {g : Guards} {sys : Sys}
    {reads : AssetId → TokenReads} {d : ChainId} {a : AssetId} {r : Address} {x : UInt256}
    (hd : d ≠ cfg.l1) :
    routerRecoverBase cfg g sys reads d a r x = vaultRecover cfg g sys reads d a (some ⟨r, r, 0, x, []⟩) := by
  unfold routerRecoverBase
  rw [ite_eq_right (fun h => hd h.2)]

theorem recoverCalls_value_calls {cfg : Config} {reads : AssetId → TokenReads} {d : ChainId}
    {destBase : AssetId} (hd : d ≠ cfg.l1) :
    ∀ (calls : List Call) (sys : Sys), (∀ c ∈ calls, c.sender ≠ cfg.router ∧ c.value ≠ 0) →
      recoverCalls cfg Guards.v35 reads d destBase sys calls =
        vaultRecoverAll cfg Guards.v35 sys reads d destBase
          (calls.map fun c => ⟨c.sender, c.sender, 0, c.value, []⟩)
  | [], sys, _ => rfl
  | c :: cs, sys, hc => by
    have hc₀ := hc c (List.mem_cons_self ..)
    have hrec : recoverCall cfg Guards.v35 reads d destBase sys c =
        vaultRecover cfg Guards.v35 sys reads d destBase (some ⟨c.sender, c.sender, 0, c.value, []⟩) := by
      unfold recoverCall
      rw [ite_eq_right hc₀.1, Option.bind_some, ite_eq_left hc₀, routerRecoverBase_of_not_l1 hd]
    simp only [recoverCalls, List.map_cons, vaultRecoverAll]
    rw [hrec]
    congr 1
    funext s
    exact recoverCalls_value_calls hd cs s (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc'))

theorem recoverCalls_router_calls {cfg : Config} {reads : AssetId → TokenReads} {d : ChainId}
    {destBase a : AssetId} (hd : d ≠ cfg.l1) (hntv : cfg.ntv ≠ 0) :
    ∀ (mds : List MintData) (sys : Sys), sys.handler a = cfg.ntv →
      recoverCalls cfg Guards.v35 reads d destBase sys
          (mds.map fun md => ⟨cfg.router, .finalizeDeposit a (some md), 0⟩) =
        vaultRecoverAll cfg Guards.v35 sys reads d a mds
  | [], sys, _ => rfl
  | md :: mds, sys, hh => by
    have hrec : recoverCall cfg Guards.v35 reads d destBase sys
        ⟨cfg.router, .finalizeDeposit a (some md), 0⟩ =
        vaultRecover cfg Guards.v35 sys reads d a (some md) := by
      unfold recoverCall
      rw [ite_eq_left rfl]
      simp only [routerRecoverAtomicCall]
      rw [ite_eq_right (fun h => hd h.2), ite_eq_right (by rw [hh]; exact hntv), ite_eq_left hh]
      cases vaultRecover cfg Guards.v35 sys reads d a (some md) with
      | none => rfl
      | some s => rw [Option.bind_some, ite_eq_right (fun h => h.1 rfl)]
    simp only [List.map_cons, recoverCalls, vaultRecoverAll]
    rw [hrec]
    cases hv : vaultRecover cfg Guards.v35 sys reads d a (some md) with
    | none => rfl
    | some s =>
      rw [Option.bind_some, Option.bind_some]
      exact recoverCalls_router_calls hd hntv mds s
        (by rw [(vaultRecover_v35_effect hv).2.2.1]; exact hh)

/-! ## The L1 checks -/

theorem routerRecoverAtomicCall_l1 {cfg : Config} {g : Guards} {sys : Sys}
    {reads : AssetId → TokenReads} (hg : g.routerL1 = true) (data : CallData) :
    routerRecoverAtomicCall cfg g sys reads cfg.l1 data = none := by
  cases data with
  | other => simp only [routerRecoverAtomicCall]; rw [ite_eq_left ⟨hg, trivial⟩]
  | badPayload => rfl
  | finalizeDeposit a m => simp only [routerRecoverAtomicCall]; rw [ite_eq_left ⟨hg, trivial⟩]

theorem routerRecoverBase_l1 {cfg : Config} {g : Guards} {sys : Sys}
    {reads : AssetId → TokenReads} (hg : g.routerL1 = true) (a : AssetId) (r : Address)
    (x : UInt256) : routerRecoverBase cfg g sys reads cfg.l1 a r x = none := by
  unfold routerRecoverBase; rw [ite_eq_left ⟨hg, rfl⟩]

theorem vaultRecover_l1 {cfg : Config} {g : Guards} {sys : Sys} {reads : AssetId → TokenReads}
    (hg : g.vaultL1 = true) (a : AssetId) (m : Option MintData) :
    vaultRecover cfg g sys reads cfg.l1 a m = none := by
  cases m with
  | none => rfl
  | some md => simp only [vaultRecover]; rw [ite_eq_left ⟨hg, trivial⟩]

theorem holderRecover_l1 {cfg : Config} {g : Guards} {sys : Sys} (hg : g.holderL1 = true)
    (x : UInt256) (hx : x ≠ 0) : holderRecover cfg g sys x cfg.l1 = none := by
  unfold holderRecover; rw [ite_eq_right hx, ite_eq_left ⟨hg, rfl⟩]

theorem recoverBundle_manager_l1 {cfg : Config} {g : Guards} {sys : Sys}
    {reads : AssetId → TokenReads} (hg : g.managerL1 = true) (b : Bundle) (hb : b.dest = cfg.l1) :
    recoverBundle cfg g sys reads b = none := by
  unfold recoverBundle; rw [ite_eq_left ⟨hg, hb⟩]

theorem recoverCalls_router_l1 {cfg : Config} {g : Guards} {reads : AssetId → TokenReads}
    {destBase : AssetId} (hg : g.routerL1 = true) :
    ∀ (calls : List Call) (sys : Sys), (∃ c ∈ calls, c.sender = cfg.router ∨ c.value ≠ 0) →
      recoverCalls cfg g reads cfg.l1 destBase sys calls = none
  | [], _, ⟨c, hc, _⟩ => absurd hc List.not_mem_nil
  | c :: cs, sys, ⟨c', hc', hatt⟩ => by
    simp only [recoverCalls]
    by_cases hr : c.sender = cfg.router
    · unfold recoverCall
      rw [ite_eq_left hr, routerRecoverAtomicCall_l1 hg]; rfl
    · by_cases hv : c.value ≠ 0
      · unfold recoverCall
        rw [ite_eq_right hr, Option.bind_some, ite_eq_left ⟨hr, hv⟩, routerRecoverBase_l1 hg]; rfl
      · have hrec : recoverCall cfg g reads cfg.l1 destBase sys c = some sys := by
          unfold recoverCall
          rw [ite_eq_right hr, Option.bind_some, ite_eq_right (fun h => hv h.2)]
        rw [hrec, Option.bind_some]
        refine recoverCalls_router_l1 hg cs sys ?_
        rcases List.mem_cons.mp hc' with rfl | hc''
        · rcases hatt with h | h
          · exact absurd h hr
          · exact absurd h hv
        · exact ⟨c', hc'', hatt⟩

/-! ## What a claim does, at v35 -/

theorem vaultRecover_v35_mono {cfg : Config} {sys s' : Sys} {reads : AssetId → TokenReads}
    {d : ChainId} {a : AssetId} {m : Option MintData}
    (h : vaultRecover cfg Guards.v35 sys reads d a m = some s') :
    d ≠ cfg.l1 ∧ s'.trk.interopInfo = sys.trk.interopInfo ∧
      (∀ c b, (sys.trk.chainBalance c b).val ≤ (s'.trk.chainBalance c b).val) ∧
      (∀ c b, c ≠ cfg.thisChain → s'.trk.chainBalance c b = sys.trk.chainBalance c b) ∧
      s'.holder ≤ sys.holder ∧ s'.handler = sys.handler ∧ s'.sl = sys.sl := by
  cases m with
  | none => cases h
  | some md =>
    obtain ⟨hd, hi, hh, hsl, -, hbase, hnon⟩ := vaultRecover_v35_effect h
    by_cases hb : a = cfg.base
    · obtain ⟨-, htrk, hhold, -, -⟩ := hbase hb
      exact ⟨hd, hi, fun c b => by rw [htrk], fun c b _ => by rw [htrk], by omega, hh, hsl⟩
    · obtain ⟨hhold, -, -, t₀, h₀, hfin⟩ := hnon hb
      obtain ⟨-, -, ho₀, hm₀, -⟩ := registerIfNeeded_spec h₀
      have key : (∀ c b, (t₀.chainBalance c b).val ≤ (s'.trk.chainBalance c b).val) ∧
          (∀ c b, c ≠ cfg.thisChain → s'.trk.chainBalance c b = t₀.chainBalance c b) := by
        split_ifs at hfin with hn
        · obtain ⟨f₁, -, -, -, f₅⟩ := increaseChainBalance_facts hfin
          exact ⟨fun c b => f₅ c b, fun c b hc => f₁.2 c b hc⟩
        · rw [← Option.some.inj hfin]; exact ⟨fun _ _ => le_rfl, fun _ _ _ => rfl⟩
      exact ⟨hd, hi, fun c b => le_trans (hm₀ c b) (key.1 c b),
        fun c b hc => (key.2 c b hc).trans (ho₀.2 c b hc), le_of_eq hhold, hh, hsl⟩

theorem recoverCalls_v35_mono {cfg : Config} {reads : AssetId → TokenReads} {d : ChainId}
    {destBase : AssetId} :
    ∀ (calls : List Call) (sys s' : Sys),
      recoverCalls cfg Guards.v35 reads d destBase sys calls = some s' →
      s'.trk.interopInfo = sys.trk.interopInfo ∧
        (∀ c b, (sys.trk.chainBalance c b).val ≤ (s'.trk.chainBalance c b).val) ∧
        (∀ c b, c ≠ cfg.thisChain → s'.trk.chainBalance c b = sys.trk.chainBalance c b) ∧
        s'.holder ≤ sys.holder ∧ s'.handler = sys.handler ∧ s'.sl = sys.sl
  | [], sys, s', h => by
    cases h; exact ⟨rfl, fun _ _ => le_rfl, fun _ _ _ => rfl, le_rfl, rfl, rfl⟩
  | c :: cs, sys, s', h => by
    unfold recoverCalls at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, hrest⟩ := h
    have one : s.trk.interopInfo = sys.trk.interopInfo ∧
        (∀ c b, (sys.trk.chainBalance c b).val ≤ (s.trk.chainBalance c b).val) ∧
        (∀ c b, c ≠ cfg.thisChain → s.trk.chainBalance c b = sys.trk.chainBalance c b) ∧
        s.holder ≤ sys.holder ∧ s.handler = sys.handler ∧ s.sl = sys.sl := by
      obtain ⟨s₁, hs₁, hs₂⟩ := recoverCall_eq hs
      have first : s₁.trk.interopInfo = sys.trk.interopInfo ∧
          (∀ c b, (sys.trk.chainBalance c b).val ≤ (s₁.trk.chainBalance c b).val) ∧
          (∀ c b, c ≠ cfg.thisChain → s₁.trk.chainBalance c b = sys.trk.chainBalance c b) ∧
          s₁.holder ≤ sys.holder ∧ s₁.handler = sys.handler ∧ s₁.sl = sys.sl := by
        split_ifs at hs₁ with hr
        · obtain ⟨-, rfl | ⟨a, m, -, -, hv⟩⟩ := routerRecoverAtomicCall_eq hs₁
          · exact ⟨rfl, fun _ _ => le_rfl, fun _ _ _ => rfl, le_rfl, rfl, rfl⟩
          · obtain ⟨-, h1, h2, h3, h4, h5, h6⟩ := vaultRecover_v35_mono hv
            exact ⟨h1, h2, h3, h4, h5, h6⟩
        · cases hs₁; exact ⟨rfl, fun _ _ => le_rfl, fun _ _ _ => rfl, le_rfl, rfl, rfl⟩
      obtain ⟨i₁, m₁, o₁, h₁, hh₁, sl₁⟩ := first
      split_ifs at hs₂ with hv
      · obtain ⟨-, hv'⟩ := routerRecoverBase_eq hs₂
        obtain ⟨-, i₂, m₂, o₂, h₂, hh₂, sl₂⟩ := vaultRecover_v35_mono hv'
        exact ⟨i₂.trans i₁, fun c b => le_trans (m₁ c b) (m₂ c b),
          fun c b hc => (o₂ c b hc).trans (o₁ c b hc), le_trans h₂ h₁, hh₂.trans hh₁,
          sl₂.trans sl₁⟩
      · cases hs₂; exact ⟨i₁, m₁, o₁, h₁, hh₁, sl₁⟩
    obtain ⟨i₁, m₁, o₁, h₁, hh₁, sl₁⟩ := one
    obtain ⟨i₂, m₂, o₂, h₂, hh₂, sl₂⟩ := recoverCalls_v35_mono cs s s' hrest
    exact ⟨i₂.trans i₁, fun c b => le_trans (m₁ c b) (m₂ c b),
      fun c b hc => (o₂ c b hc).trans (o₁ c b hc), le_trans h₂ h₁, hh₂.trans hh₁, sl₂.trans sl₁⟩


/-! ## Recoveries interleaved with other operations -/

theorem scheduleRecoveries_other (op : Op) (items : List SchedItem) :
    scheduleRecoveries (.other op :: items) = scheduleRecoveries items := rfl

theorem scheduleRecoveries_recover (md : MintData) (items : List SchedItem) :
    scheduleRecoveries (.recover md :: items) = md :: scheduleRecoveries items := rfl

/-- A schedule of v35 recoveries of a registered asset other than the base asset, with a token,
interleaved with operations not on it: the asset's chain balance here rises by the recoveries' total if
the vault records it as native here, and nothing else about it changes. -/
theorem runSchedule_nonbase {cfg : Config} {reads : AssetId → TokenReads} {d : ChainId}
    {a : AssetId} (hb : a ≠ cfg.base) :
    ∀ (sched : List SchedItem) (s s' : Sys), runSchedule cfg Guards.v35 reads d a s sched = some s' →
      (∀ op, SchedItem.other op ∈ sched → ¬ op.Touches cfg a) →
      s.trk.isAssetRegistered a = true → s.token a ≠ 0 →
      (scheduleRecoveries sched ≠ [] → d ≠ cfg.l1) ∧
      (∀ c, c ≠ cfg.thisChain → s'.trk.chainBalance c a = s.trk.chainBalance c a) ∧
      (s.origin a = cfg.thisChain → (s'.trk.chainBalance cfg.thisChain a).val =
        (s.trk.chainBalance cfg.thisChain a).val +
          ((scheduleRecoveries sched).map fun m => m.amount.val).sum) ∧
      (s.origin a ≠ cfg.thisChain →
        s'.trk.chainBalance cfg.thisChain a = s.trk.chainBalance cfg.thisChain a) ∧
      s'.trk.isAssetRegistered a = true ∧ s'.trk.interopInfo a = s.trk.interopInfo a ∧
      s'.trk.totalPreV31TotalSupply a = s.trk.totalPreV31TotalSupply a ∧
      s'.origin a = s.origin a ∧ s'.token a = s.token a ∧ s'.handler a = s.handler a
  | [], s, s', h, _, hreg, _ => by
    cases h
    exact ⟨fun h' => absurd rfl h', fun _ _ => rfl, fun _ => by simp [scheduleRecoveries],
      fun _ => rfl, hreg, rfl, rfl, rfl, rfl, rfl⟩
  | .other op :: items, s, s', h, hn, hreg, htok => by
    simp only [runSchedule, Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, hrest⟩ := h
    obtain ⟨hA, hO, hT, hH, -⟩ := exec_frame h₁ a (hn op (List.mem_cons_self ..))
    have hreg₁ : s₁.trk.isAssetRegistered a = true := by rw [hA.2.1]; exact hreg
    have htok₁ : s₁.token a ≠ 0 := by rw [hT]; exact htok
    obtain ⟨hpre, hc', hn', hnn', hreg', hi', hp', ho', ht', hh'⟩ :=
      runSchedule_nonbase hb items s₁ s' hrest
        (fun op' hop' => hn op' (List.mem_cons_of_mem _ hop')) hreg₁ htok₁
    rw [scheduleRecoveries_other]
    refine ⟨hpre, fun c hc => (hc' c hc).trans (hA.1 c), fun hnat => ?_, fun hnat => ?_, hreg',
      hi'.trans hA.2.2.1, hp'.trans hA.2.2.2, ho'.trans hO, ht'.trans hT, hh'.trans hH⟩
    · rw [hn' (hO.trans hnat), hA.1 cfg.thisChain]
    · rw [hnn' (fun h' => hnat (hO.symm.trans h')), hA.1 cfg.thisChain]
  | .recover md :: items, s, s', h, hn, hreg, htok => by
    simp only [runSchedule, Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, hrest⟩ := h
    obtain ⟨hd, -, ho, ht, hh, hnat, hnn⟩ := vaultRecover_v35_nonbase_step hb hreg htok h₁
    have hreg₁ : s₁.trk.isAssetRegistered a = true := by
      by_cases hn₀ : s.origin a = cfg.thisChain
      · obtain ⟨_, he⟩ := hnat hn₀; rw [he]; exact hreg
      · rw [hnn hn₀]; exact hreg
    have htok₁ : s₁.token a ≠ 0 := by rw [ht]; exact htok
    obtain ⟨-, hc', hn', hnn', hreg', hi', hp', ho', ht', hh'⟩ :=
      runSchedule_nonbase hb items s₁ s' hrest
        (fun op' hop' => hn op' (List.mem_cons_of_mem _ hop')) hreg₁ htok₁
    have hsame : (∀ c, c ≠ cfg.thisChain → s₁.trk.chainBalance c a = s.trk.chainBalance c a) ∧
        s₁.trk.interopInfo a = s.trk.interopInfo a ∧
        s₁.trk.totalPreV31TotalSupply a = s.trk.totalPreV31TotalSupply a := by
      by_cases hn₀ : s.origin a = cfg.thisChain
      · obtain ⟨_, he⟩ := hnat hn₀
        rw [he]
        refine ⟨fun c hc => ?_, rfl, rfl⟩
        rw [Tracker.setChainBalance_chainBalance]; simp [hc]
      · rw [hnn hn₀]; exact ⟨fun _ _ => rfl, rfl, rfl⟩
    have ho₁ : s₁.origin a = s.origin a := by rw [ho]
    rw [scheduleRecoveries_recover]
    refine ⟨fun _ => hd, fun c hc => (hc' c hc).trans (hsame.1 c hc), fun hn₀ => ?_,
      fun hn₀ => ?_, hreg', hi'.trans hsame.2.1, hp'.trans hsame.2.2, ho'.trans ho₁,
      ht'.trans (by rw [ht]), hh'.trans (by rw [hh])⟩
    · obtain ⟨_, he⟩ := hnat hn₀
      rw [hn' (ho₁.trans hn₀), list_sum_cons_amount, he, Tracker.setChainBalance_chainBalance]
      simp only [and_self, ite_true]
      omega
    · rw [hnn' (fun h' => hn₀ (ho₁.symm.trans h')), hnn hn₀]

/-- A schedule of v35 recoveries of the base asset interleaved with operations not on it: the base
asset's view is untouched except that the holder pays the recoveries' total. -/
theorem runSchedule_base {cfg : Config} {reads : AssetId → TokenReads} {d : ChainId} :
    ∀ (sched : List SchedItem) (s s' : Sys),
      runSchedule cfg Guards.v35 reads d cfg.base s sched = some s' →
      (∀ op, SchedItem.other op ∈ sched → ¬ op.Touches cfg cfg.base) →
      (scheduleRecoveries sched ≠ [] → d ≠ cfg.l1 ∧ s.origin cfg.base ≠ cfg.thisChain) ∧
      s'.trk.AgreeAt s.trk cfg.base ∧ s'.origin cfg.base = s.origin cfg.base ∧
      s'.token cfg.base = s.token cfg.base ∧ s'.handler cfg.base = s.handler cfg.base ∧
      s'.holder + ((scheduleRecoveries sched).map fun m => m.amount.val).sum = s.holder
  | [], s, s', h, _ => by
    cases h
    exact ⟨fun h' => absurd rfl h', Tracker.AgreeAt.refl _ _, rfl, rfl, rfl,
      by simp [scheduleRecoveries]⟩
  | .other op :: items, s, s', h, hn => by
    simp only [runSchedule, Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, hrest⟩ := h
    obtain ⟨hA, hO, hT, hH, hHold⟩ := exec_frame h₁ cfg.base (hn op (List.mem_cons_self ..))
    obtain ⟨hpre, hA', hO', hT', hH', hhold'⟩ := runSchedule_base items s₁ s' hrest
      (fun op' hop' => hn op' (List.mem_cons_of_mem _ hop'))
    rw [scheduleRecoveries_other]
    refine ⟨fun hne => ?_, hA'.trans hA, hO'.trans hO, hT'.trans hT, hH'.trans hH, ?_⟩
    · obtain ⟨hd, ho⟩ := hpre hne
      exact ⟨hd, hO ▸ ho⟩
    · rw [hhold', hHold rfl]
  | .recover md :: items, s, s', h, hn => by
    simp only [runSchedule, Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, hrest⟩ := h
    obtain ⟨hd, -, hh, -, -, hbase, -⟩ := vaultRecover_v35_effect h₁
    obtain ⟨ho, htrk, hhold, horig, htok⟩ := hbase rfl
    obtain ⟨-, hA', hO', hT', hH', hhold'⟩ := runSchedule_base items s₁ s' hrest
      (fun op' hop' => hn op' (List.mem_cons_of_mem _ hop'))
    rw [scheduleRecoveries_recover]
    refine ⟨fun _ => ⟨hd, ho⟩, by rw [← htrk]; exact hA', by rw [hO', horig],
      by rw [hT', htok], by rw [hH', hh], ?_⟩
    rw [list_sum_cons_amount]; omega

/-- **(ii) under arbitrary interleaving, for the vault's bridge-out.** -/
theorem vaultBurn_then_schedule {cfg : Config} {sys₀ sys₁ sys₃ : Sys} {reads₀ : TokenReads}
    {reads : AssetId → TokenReads} {d : ChainId} {a : AssetId} {x : UInt256}
    {sched : List SchedItem}
    (hb : exec cfg Guards.v35 sys₀ (.vaultBurn reads₀ d a x) = some sys₁)
    (hn : ∀ op, SchedItem.other op ∈ sched → ¬ op.Touches cfg a)
    (hsum : ((scheduleRecoveries sched).map fun m => m.amount.val).sum = x.val)
    (hr : runSchedule cfg Guards.v35 reads d a sys₁ sched = some sys₃) :
    ∃ t₀, registerIfNeeded cfg sys₀ reads₀ sys₀.trk a (sys₀.token a) = some t₀ ∧
      sys₃.trk.AgreeAt t₀ a ∧ sys₃.origin a = sys₀.origin a ∧ sys₃.token a = sys₀.token a ∧
      sys₃.handler a = sys₀.handler a ∧ (a = cfg.base → sys₃.holder = sys₀.holder) := by
  obtain ⟨hx0, t, ht, h₁trk, h₁o, h₁t, h₁h, -, -, hhb, -⟩ := exec_vaultBurn_eq hb
  have hne : scheduleRecoveries sched ≠ [] := by
    intro h0
    rw [h0] at hsum
    have hx : x.val = 0 := by simpa using hsum.symm
    exact hx0 (Fin.ext (by rw [hx]; rfl))
  obtain ⟨htok, t₀, h₀, t₂, h₂, h₃⟩ := initiateInner_unfold ht
  by_cases hab : a = cfg.base
  · subst hab
    obtain ⟨hpre, hA, horig, htok', hh, hhold⟩ := runSchedule_base sched sys₁ sys₃ hr hn
    obtain ⟨hd, ho⟩ := hpre hne
    have ho₀ : sys₀.origin cfg.base ≠ cfg.thisChain := by rw [h₁o] at ho; exact ho
    have hl : ¬ (d = cfg.l1 ∧ sys₀.sl = cfg.l1) := fun h' => hd h'.1
    rw [ite_eq_right hl] at h₃
    rw [ite_eq_right ho₀] at h₂
    have e₂ := Option.some.inj h₂
    subst e₂
    have e₃ := Option.some.inj h₃
    subst e₃
    refine ⟨t₀, h₀, by rw [← h₁trk]; exact hA, by rw [horig, h₁o], by rw [htok', h₁t],
      by rw [hh, h₁h], fun _ => ?_⟩
    have h1 := hhb ⟨rfl, ho₀⟩
    rw [hsum] at hhold
    omega
  · have hreg₁ : sys₁.trk.isAssetRegistered a = true := by
      rw [h₁trk]; exact (initiateInner_facts ht).2.1
    have htok₁ : sys₁.token a ≠ 0 := by rw [h₁t]; exact htok
    obtain ⟨hpre, hc', hn', hnn', hreg', hi', hp', ho', ht', hh'⟩ :=
      runSchedule_nonbase hab sched sys₁ sys₃ hr hn hreg₁ htok₁
    have hd := hpre hne
    have hl : ¬ (d = cfg.l1 ∧ sys₀.sl = cfg.l1) := fun h' => hd h'.1
    rw [ite_eq_right hl] at h₃
    have e₃ := Option.some.inj h₃
    subst e₃
    have hO₁ : sys₁.origin a = sys₀.origin a := by rw [h₁o]
    refine ⟨t₀, h₀, ⟨fun c => ?_, ?_, ?_, ?_⟩, by rw [ho', hO₁], by rw [ht', h₁t],
      by rw [hh', h₁h], fun h' => absurd h' hab⟩
    · by_cases hc : c = cfg.thisChain
      · subst hc
        by_cases hnat : sys₀.origin a = cfg.thisChain
        · rw [ite_eq_left hnat] at h₂
          obtain ⟨hdec, he⟩ := decreaseChainBalance_eq h₂
          apply Fin.ext
          rw [hn' (hO₁.trans hnat), h₁trk, hsum, he, Tracker.setChainBalance_chainBalance]
          simp only [and_self, ite_true]
          omega
        · rw [ite_eq_right hnat] at h₂
          rw [hnn' (fun h' => hnat (hO₁.symm.trans h')), h₁trk]
          rw [← Option.some.inj h₂]
      · rw [hc' c hc, h₁trk]
        by_cases hnat : sys₀.origin a = cfg.thisChain
        · rw [ite_eq_left hnat] at h₂
          rw [(decreaseChainBalance_facts h₂).1.2 c a hc]
        · rw [ite_eq_right hnat] at h₂
          rw [← Option.some.inj h₂]
    · rw [hreg', (registerIfNeeded_spec h₀).1]
    · rw [hi', h₁trk]
      by_cases hnat : sys₀.origin a = cfg.thisChain
      · rw [ite_eq_left hnat] at h₂
        rw [(decreaseChainBalance_facts h₂).2.2.1]
      · rw [ite_eq_right hnat] at h₂
        rw [← Option.some.inj h₂]
    · rw [hp', h₁trk]
      by_cases hnat : sys₀.origin a = cfg.thisChain
      · rw [ite_eq_left hnat] at h₂
        obtain ⟨_, he⟩ := decreaseChainBalance_eq h₂
        rw [he]; rfl
      · rw [ite_eq_right hnat] at h₂
        rw [← Option.some.inj h₂]

/-- **(ii) under arbitrary interleaving, for the interop center's value burn.** -/
theorem icBurnBase_then_schedule {cfg : Config} {sys₀ sys₁ sys₃ : Sys} {reads₀ : TokenReads}
    {reads : AssetId → TokenReads} {d : ChainId} {v : UInt256} {sched : List SchedItem}
    (hb : exec cfg Guards.v35 sys₀ (.icBurnBase reads₀ d v) = some sys₁)
    (hn : ∀ op, SchedItem.other op ∈ sched → ¬ op.Touches cfg cfg.base)
    (hsum : ((scheduleRecoveries sched).map fun m => m.amount.val).sum = v.val)
    (hr : runSchedule cfg Guards.v35 reads d cfg.base sys₁ sched = some sys₃) :
    ∃ t₀, registerIfNeeded cfg sys₀ reads₀ sys₀.trk cfg.base (sys₀.token cfg.base) = some t₀ ∧
      sys₃.trk.AgreeAt t₀ cfg.base ∧ sys₃.origin cfg.base = sys₀.origin cfg.base ∧
      sys₃.token cfg.base = sys₀.token cfg.base ∧ sys₃.handler cfg.base = sys₀.handler cfg.base ∧
      sys₃.holder = sys₀.holder := by
  obtain ⟨hv0, t, ht, h₁trk, h₁o, h₁t, h₁h, -, -, hh⟩ := exec_icBurnBase_eq hb
  have hne : scheduleRecoveries sched ≠ [] := by
    intro h0
    rw [h0] at hsum
    have hx : v.val = 0 := by simpa using hsum.symm
    exact hv0 (Fin.ext (by rw [hx]; rfl))
  obtain ⟨-, t₀, h₀, t₂, h₂, h₃⟩ := initiateInner_unfold ht
  obtain ⟨hpre, hA, horig, htok', hh', hhold⟩ := runSchedule_base sched sys₁ sys₃ hr hn
  obtain ⟨hd, ho⟩ := hpre hne
  have ho₀ : sys₀.origin cfg.base ≠ cfg.thisChain := by rw [h₁o] at ho; exact ho
  have hl : ¬ (d = cfg.l1 ∧ sys₀.sl = cfg.l1) := fun h' => hd h'.1
  rw [ite_eq_right hl] at h₃
  rw [ite_eq_right ho₀] at h₂
  have e₂ := Option.some.inj h₂
  subst e₂
  have e₃ := Option.some.inj h₃
  subst e₃
  refine ⟨t₀, h₀, by rw [← h₁trk]; exact hA, by rw [horig, h₁o], by rw [htok', h₁t],
    by rw [hh', h₁h], ?_⟩
  rw [hsum] at hhold
  omega

/-! ## The property theorems -/

/-- **NO RECOVERY TOWARD L1 AT V35.** -/
theorem RecoveryToL1RevertsAtV35 : Properties.RecoveryToL1RevertsAtV35 := by
  intro cfg sys reads
  exact ⟨fun b hb => recoverBundle_manager_l1 rfl b hb, routerRecoverAtomicCall_l1 rfl,
    fun a r x => routerRecoverBase_l1 rfl a r x, fun a m => vaultRecover_l1 rfl a m,
    fun x hx => holderRecover_l1 rfl x hx⟩

/-- **EACH L1 CHECK ALONE SUFFICES ON ITS PATH.** -/
theorem EachL1CheckSufficesOnItsPath : Properties.EachL1CheckSufficesOnItsPath := by
  intro cfg g sys reads
  refine ⟨fun hg b hb => recoverBundle_manager_l1 hg b hb,
    fun hg => ⟨routerRecoverAtomicCall_l1 hg, fun a r x => routerRecoverBase_l1 hg a r x,
      fun b hb hatt => ?_⟩,
    fun hg a m => vaultRecover_l1 hg a m, fun hg x hx => holderRecover_l1 hg x hx⟩
  unfold recoverBundle
  by_cases hm : g.managerL1 = true ∧ b.dest = cfg.l1
  · rw [ite_eq_left hm]
  · rw [ite_eq_right hm, hb]
    exact recoverCalls_router_l1 hg b.calls sys hatt

/-- **A STEP NOT ON `a` LEAVES `a` ALONE.** -/
theorem StepNotOnAssetLeavesItAlone : Properties.StepNotOnAssetLeavesItAlone :=
  fun _ _ _ _ _ a h hn => exec_frame h a hn

/-- **THE VAULT'S BRIDGE-OUT AND ITS RECOVERIES RESTORE THE ASSET.** -/
theorem BurnThenRecoveriesRestoreAsset : Properties.BurnThenRecoveriesRestoreAsset :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hb hm hn hsum hr => vaultBurn_then_recoverAll hb hm hn hsum hr

/-- **THE INTEROP CENTER'S VALUE BURN AND ITS RECOVERIES RESTORE THE BASE ASSET.** -/
theorem InteropValueBurnThenRecoveriesRestoreBase :
    Properties.InteropValueBurnThenRecoveriesRestoreBase :=
  fun _ _ _ _ _ _ _ _ _ _ _ hb hm hn hsum hr => icBurnBase_then_recoverAll hb hm hn hsum hr

/-- **THE RECOVERIES OF A BRIDGE-OUT SUCCEED.** -/
theorem RecoveriesAfterBurnSucceed : Properties.RecoveriesAfterBurnSucceed :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ hb hm hn hd ho hsum => recoverAll_after_vaultBurn hb hm hn hd ho hsum,
    fun _ _ _ _ _ _ _ _ _ _ hb hm hn hd ho hsum => recoverAll_after_icBurnBase hb hm hn hd ho hsum⟩

/-- **A CLAIM IS THE VAULT'S RECOVERIES.** -/
theorem ClaimRefundIsVaultRecoveries : Properties.ClaimRefundIsVaultRecoveries := by
  intro cfg sys reads b
  refine ⟨fun hc => ?_, fun a mds hntv hh hcalls => ?_⟩
  · show recoverBundle cfg Guards.v35 sys reads b = _
    unfold recoverBundle
    by_cases hd : b.dest = cfg.l1
    · rw [ite_eq_left ⟨rfl, hd⟩, ite_eq_left hd]
    · rw [ite_eq_right (fun h => hd h.2), ite_eq_right hd]
      exact recoverCalls_value_calls hd b.calls sys hc
  · show recoverBundle cfg Guards.v35 sys reads b = _
    unfold recoverBundle
    by_cases hd : b.dest = cfg.l1
    · rw [ite_eq_left ⟨rfl, hd⟩, ite_eq_left hd]
    · rw [ite_eq_right (fun h => hd h.2), ite_eq_right hd, hcalls]
      exact recoverCalls_router_calls hd hntv mds sys hh

/-- **A BRIDGE-OUT AND THE CLAIM OF ITS LEG RESTORE THE ASSET.** -/
theorem BurnThenClaimRestores : Properties.BurnThenClaimRestores := by
  refine ⟨fun cfg sys₀ sys₁ sys₂ sys₃ reads₀ reads d destBase a x mid mds hntv hh hb hm hn hsum hc =>
    ?_, fun cfg sys₀ sys₁ sys₂ sys₃ reads₀ reads d v mid calls hb hm hn hcalls hsum hc => ?_⟩
  · have hH₂ : sys₂.handler a = cfg.ntv := by
      obtain ⟨-, t, -, -, -, -, h₁h, -, -, -, -⟩ := exec_vaultBurn_eq hb
      rw [(run_frame a mid sys₁ sys₂ hm hn).2.2.2.1, h₁h, hh]
    rw [(ClaimRefundIsVaultRecoveries cfg sys₂ reads _).2 a mds hntv hH₂ rfl] at hc
    dsimp only at hc
    by_cases hd : d = cfg.l1
    · rw [ite_eq_left hd] at hc; cases hc
    · rw [ite_eq_right hd] at hc
      exact vaultBurn_then_recoverAll hb hm hn hsum hc
  · rw [(ClaimRefundIsVaultRecoveries cfg sys₂ reads _).1 hcalls] at hc
    dsimp only at hc
    by_cases hd : d = cfg.l1
    · rw [ite_eq_left hd] at hc; cases hc
    · rw [ite_eq_right hd] at hc
      refine icBurnBase_then_recoverAll hb hm hn ?_ hc
      rw [List.map_map]
      exact hsum

/-- **(ii) UNDER ARBITRARY INTERLEAVING.** -/
theorem BurnThenInterleavedRecoveriesRestoreAsset :
    Properties.BurnThenInterleavedRecoveriesRestoreAsset :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ hb hn hsum hr => vaultBurn_then_schedule hb hn hsum hr,
    fun _ _ _ _ _ _ _ _ _ hb hn hsum hr => icBurnBase_then_schedule hb hn hsum hr⟩

/-- **WHAT A VAULT RECOVERY WRITES AT V35.** -/
theorem VaultRecoveryEffectAtV35 : Properties.VaultRecoveryEffectAtV35 :=
  fun _ _ _ _ _ _ _ h => vaultRecover_v35_effect h

/-- **A CLAIM NEVER WRITES `interopInfo`.** -/
theorem ClaimRefundNeverWritesInteropInfo : Properties.ClaimRefundNeverWritesInteropInfo := by
  intro cfg sys sys' reads b h
  have h' : recoverBundle cfg Guards.v35 sys reads b = some sys' := h
  unfold recoverBundle at h'
  by_cases hm : Guards.v35.managerL1 = true ∧ b.dest = cfg.l1
  · rw [ite_eq_left hm] at h'; cases h'
  rw [ite_eq_right hm] at h'
  exact ⟨fun hd => hm ⟨rfl, hd⟩, recoverCalls_v35_mono b.calls sys sys' h'⟩

/-- **WHAT `totalWithdrawalsToL1` COUNTS.** -/
theorem WithdrawalsToL1Ledger : Properties.WithdrawalsToL1Ledger := by
  intro cfg g sys₀ sys ops h
  obtain ⟨new, hl, hW, hr⟩ := run_W ops sys₀ sys h
  exact ⟨new, hl, hW, fun a => by rw [hW a]; omega,
    fun hg A d x hx hd => hr A d x hx ⟨hg, hd⟩⟩

/-- **WHEN A RECOVERY SUCCEEDS AT V35.** -/
theorem RecoveryCreditFitsIff : Properties.RecoveryCreditFitsIff := by
  intro cfg sys reads d a md hd
  refine ⟨fun hb hreg hnat => ?_, fun ho => vaultRecover_v35_base_iff hd ho, fun ho => ?_⟩
  · rw [vaultRecover_v35_nonbase_iff hb hd hreg (Or.inl hnat)]
    exact ⟨fun h => h hnat, fun h _ => h⟩
  · simp only [vaultRecover]
    rw [ite_eq_right (by simp [Guards.v35, hd])]
    rw [ite_eq_left (by simp [Guards.v35, ho])]

/-! ## Concrete witnesses and countermodels -/

/-- The witnesses' configuration: this chain `5`, L1 `1`, base asset `100`, vault `10`, router `11`. -/
def rnCfg : Config where
  thisChain := 5
  l1 := 1
  base := 100
  ntv := 10
  router := 11
  baseTokenAddr := 12
  deploy := fun _ _ => none

/-- An empty tracker. -/
def rnTrk : Tracker where
  chainBalance := fun _ _ => 0
  isAssetRegistered := fun _ => false
  interopInfo := fun _ => ⟨0, 0⟩
  totalPreV31TotalSupply := fun _ => ⟨false, 0⟩

/-- The witnesses' starting state, settling on L1, nothing registered in the tracker: assets `200` and
`400` native here (tokens `20`, `40`), asset `300` from L1 (token `30`), the base asset `100` from L1
(token `12`); the vault is the handler of all four; the holder has `1000`. -/
def rnSys : Sys where
  trk := rnTrk
  origin := fun x =>
    if x = 200 then 5 else if x = 300 then 1 else if x = 100 then 1 else if x = 400 then 5 else 0
  token := fun x =>
    if x = 200 then 20 else if x = 300 then 30 else if x = 100 then 12 else if x = 400 then 40
    else 0
  handler := fun x => if x = 200 ∨ x = 300 ∨ x = 100 ∨ x = 400 then 10 else 0
  holder := 1000
  sl := 1
  log := []

/-- The starting state with the base asset recorded as native here. -/
def rnSysNativeBase : Sys := { rnSys with origin := fun x => if x = 100 then 5 else rnSys.origin x }

/-- Token reads: total supply `50`, the vault's balance `3`. -/
def rnReads : TokenReads := ⟨50, 3⟩

/-- Mint data refunding `x` to `40`. -/
def rnMint (x : UInt256) : MintData := ⟨40, 41, 0, x, []⟩

/-- A router call recovering `x` of `a`. -/
def rnRouterCall (a : AssetId) (x : UInt256) : Call := ⟨11, .finalizeDeposit a (some (rnMint x)), 0⟩

/-- A valued direct call of `x` from `40`. -/
def rnValueCall (x : UInt256) : Call := ⟨40, .other, x⟩

/-- The state a v35 run from `s` reaches (or `s` if it reverts). -/
def rnAfter (s : Sys) (ops : List Op) : Sys := (run rnCfg Guards.v35 s ops).getD s

/-- **THE L1 CHECKS ARE NOT VACUOUS.** -/
theorem L1RecoveryRejectionWitness : Properties.L1RecoveryRejectionWitness := by
  refine ⟨rnCfg, rnSys, fun _ => rnReads, rnValueCall 5, 9, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, ⟨_, rfl, by decide⟩,
    ⟨_, rfl, by decide⟩⟩

/-- **COUNTERMODEL: WITHOUT THE CHECKS, AN L1 WITHDRAWAL IS REFUNDED ON L2.** -/
theorem L1ChecksLoadBearing : Properties.L1ChecksLoadBearing := by
  refine ⟨rnCfg, rnSys, _,
    [.vaultBurn rnReads 1 300 5,
      .claimRefund (fun _ => rnReads) ⟨1, 100, [rnRouterCall 300 5]⟩], 300, 5,
    by decide, by decide, rfl, by decide, by decide, by decide, by decide, by decide⟩

/-- **THE STEP FRAME IS NOT VACUOUS.** -/
theorem StepNotOnAssetWitness : Properties.StepNotOnAssetWitness := by
  refine ⟨rnCfg, rnSys, _, .vaultBurn rnReads 9 200 5, 300, 200, rfl, ?_, ?_, by decide⟩
  · simp only [Op.Touches]; decide
  · simp only [Op.Touches]

/-- **THE ROUND-TRIP PREMISES, NONTRIVIALLY.** -/
theorem RecoveryRoundTripWitness : Properties.RecoveryRoundTripWitness := by
  have hmid : ∀ op ∈ ([.vaultRegister 400 5 40, .vaultBurn rnReads 9 400 7, .setSettlementLayer 9] :
      List Op), ¬ op.Touches rnCfg 200 := by
    intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl <;> simp only [Op.Touches] <;> decide
  have hmds : ∀ m ∈ [rnMint 2, rnMint 3], m.amount ≠ 0 := by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> decide
  exact ⟨rnCfg, rnSys, _, _, _, rnReads, fun _ => rnReads, 9, 200, 400, 5,
    [.vaultRegister 400 5 40, .vaultBurn rnReads 9 400 7, .setSettlementLayer 9],
    [rnMint 2, rnMint 3], _, by decide, by decide, by decide, by decide, by decide, hmds,
    by decide, by decide, List.cons_ne_nil _ _, rfl, rfl, hmid, by decide, by decide, rfl,
    by decide, by decide, by decide, rfl, rfl, by decide, by decide, by decide⟩

/-- **THE BASE-ASSET ROUND-TRIP PREMISES, NONTRIVIALLY.** -/
theorem BaseRecoveryRoundTripWitness : Properties.BaseRecoveryRoundTripWitness := by
  have hmid : ∀ op ∈ ([.vaultBurn rnReads 9 200 5, .setSettlementLayer 9] : List Op),
      ¬ op.Touches rnCfg rnCfg.base := by
    intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl <;> simp only [Op.Touches] <;> decide
  have hcalls : ∀ c ∈ [rnValueCall 2, rnValueCall 4], c.sender ≠ rnCfg.router ∧ c.value ≠ 0 := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> decide
  exact ⟨rnCfg, rnSys, _, _, _, _, _, rnReads, fun _ => rnReads, 9, 4, 6,
    [.vaultBurn rnReads 9 200 5, .setSettlementLayer 9], rnMint 4,
    [rnValueCall 2, rnValueCall 4], by decide, by decide, by decide, by decide, by decide,
    rfl, by decide, rfl, by decide, rfl, List.cons_ne_nil _ _, rfl, hmid, by decide, hcalls,
    by decide, rfl, rfl, by decide, by decide⟩

/-- **THE INTERLEAVED PREMISES, NONTRIVIALLY.** -/
theorem InterleavedRecoveryWitness : Properties.InterleavedRecoveryWitness := by
  have h₁ : ∀ op, SchedItem.other op ∈
      [.recover (rnMint 2), .other (.vaultBurn rnReads 9 400 7), .recover (rnMint 3)] →
      ¬ op.Touches rnCfg 200 := by
    intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or, or_false,
      SchedItem.other.injEq] at hop
    subst hop; simp only [Op.Touches]; decide
  have h₂ : ∀ op, SchedItem.other op ∈
      [.other (.setSettlementLayer 9), .recover (rnMint 2), .other (.vaultBurn rnReads 9 200 5),
        .recover (rnMint 4)] → ¬ op.Touches rnCfg rnCfg.base := by
    intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
      SchedItem.other.injEq] at hop
    rcases hop with rfl | rfl <;> simp only [Op.Touches] <;> decide
  exact ⟨rnCfg, rnSys, _, _, _, _, rnReads, fun _ => rnReads, 9, 200, 5, 6,
    [.recover (rnMint 2), .other (.vaultBurn rnReads 9 400 7), .recover (rnMint 3)],
    [.other (.setSettlementLayer 9), .recover (rnMint 2), .other (.vaultBurn rnReads 9 200 5),
      .recover (rnMint 4)],
    by decide, by decide, by decide, by decide, rfl, h₁,
    ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩, rfl, by decide, rfl, by decide, rfl, h₂,
    ⟨_, List.mem_cons_self ..⟩, rfl, by decide, rfl, by decide⟩

/-- **THE RECOVERY EFFECTS, NONZERO.** -/
theorem RecoveryEffectWitness : Properties.RecoveryEffectWitness :=
  ⟨rnCfg, rnAfter rnSys [.vaultRegister 400 5 40, .vaultBurn rnReads 9 400 7], _, _, _,
    fun _ => rnReads, 9, 400, rnMint 7, rnMint 5, ⟨9, 100, [rnRouterCall 400 3]⟩,
    by decide, by decide, by decide, by decide, by decide, rfl, by decide, rfl, by decide, rfl,
    by decide⟩

/-- **THE LEDGER, NONTRIVIALLY.** -/
theorem WithdrawalsLedgerWitness : Properties.WithdrawalsLedgerWitness :=
  ⟨rnCfg, rnSys, _,
    [.vaultBurn rnReads 1 300 5, .vaultBurn rnReads 9 300 4, .setSettlementLayer 9,
      .vaultBurn rnReads 1 300 6, .claimRefund (fun _ => rnReads) ⟨9, 100, [rnRouterCall 300 4]⟩],
    300, 5, 6, 4, 9, 9, by decide, by decide, by decide, by decide, by decide, by decide, rfl,
    by decide, by decide, by decide, by decide, by decide⟩

/-- **AN INBOUND TRANSFER BETWEEN A BRIDGE-OUT AND ITS CLAIM CAN BLOCK THE CLAIM.** -/
theorem InflowBeforeRecoveryBlocksClaim : Properties.InflowBeforeRecoveryBlocksClaim :=
  ⟨rnCfg, rnAfter rnSys [.vaultRegister 400 5 40], _, _, _, rnReads, fun _ => rnReads, 9, 7, 400, 5,
    rnMint 5, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, rfl, rfl, by decide, rfl, by decide⟩

/-- **COUNTERMODEL: WITHOUT THE ORIGIN CHECKS, A NATIVE BASE TOKEN'S RECOVERY IS NOT NEUTRAL.** -/
theorem BaseOriginCheckLoadBearing : Properties.BaseOriginCheckLoadBearing :=
  ⟨rnCfg, rnAfter rnSysNativeBase [.registerBaseIfNeeded], _, _, rnReads, fun _ => rnReads, 9, 5,
    rnMint 5, by decide, by decide, by decide, by decide, by decide, rfl, by decide, by decide,
    by decide, rfl, by decide, by decide⟩

end Contracts.L2AssetTracker.RecoveryNeutrality
