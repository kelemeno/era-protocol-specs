import EraSpec.Protocol.CtmRecord.Properties.Agreement

/-!
# Proofs: the Bridgehub's CTM record agrees with the CTM the chain's diamond obeys

`CtmInv` is inductive over every call (one lemma per kind of step). The corollaries read it
off; the repaired mint keeps the agreement half alone; the tracker-level discipline is turned
into `NoRebind` by a second invariant tying the asset maps to the registrations seen so far.
The witnesses and countermodels are explicit runs.
-/

namespace Protocol.CtmRecord

@[simp] private lemma upd2_apply {β γ : Type} [DecidableEq β] (f : ChainId → β → γ)
    (h : ChainId) (k : β) (v : γ) (h' : ChainId) (k' : β) :
    upd2 f h k v h' k' = if h' = h ∧ k' = k then v else f h' k' := rfl

/-! ## The invariant, step by step -/

theorem CtmRecordInvInit : Properties.CtmRecordInvInit := by
  intro W
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h a y
    simp only [Sys.init]
    constructor
    · rintro ⟨rfl, hy⟩; exact absurd rfl hy
    · rintro ⟨rfl, ha⟩; exact absurd rfl ha
  · intro h c D hD; simp [Sys.init] at hD
  · intro h c D hD; simp [Sys.init] at hD
  · intro h c D _ hD; simp [Sys.init] at hD
  · intro m hm; simp [Sys.init] at hm

/-- A registration on L1 of a chain with no diamond there, under a nonzero CTM. -/
private lemma inv_addChain {W : World} {s : Sys} {c : ChainId} {x : Address}
    (hI : CtmInv W s) (hnone : s.diamond W.l1 c = none) (hx : x ≠ 0) :
    CtmInv W (s.addChain W c x) := by
  obtain ⟨hbij, hnz, hag, hhome, hsent⟩ := hI
  refine ⟨hbij, ?_, ?_, ?_, ?_⟩
  · intro h c' D hD
    simp only [Sys.addChain, upd2_apply] at hD
    split_ifs at hD with hk
    · cases hD; exact hx
    · exact hnz _ _ _ hD
  · intro h c' D hD
    simp only [Sys.addChain, upd2_apply] at hD ⊢
    split_ifs at hD ⊢ with hk
    · cases hD; rfl
    · exact hag _ _ _ hD
  · intro h c' D hh hD
    simp only [Sys.addChain, upd2_apply] at hD ⊢
    rw [ite_eq_right (fun hk => hh hk.1)] at hD
    obtain ⟨X, hX, hnzX, heq⟩ := hhome h c' D hh hD
    have hc : c' ≠ c := by
      rintro rfl; rw [hnone] at hX; exact absurd hX (by simp)
    refine ⟨X, ?_, hnzX, heq⟩
    rw [ite_eq_right (fun hk => hc hk.2)]; exact hX
  · intro m hm
    obtain ⟨X, hX, hasset⟩ := hsent m hm
    have hc : m.chain ≠ c := by
      intro he; rw [he, hnone] at hX; exact absurd hX (by simp)
    refine ⟨X, ?_, hasset⟩
    simp only [Sys.addChain, upd2_apply]
    rw [ite_eq_right (fun hk => hc hk.2)]; exact hX

/-- A disciplined registration keeps every nonzero reverse entry. -/
private lemma ctmAsset_stable {W : World} {s : Sys} {h : ChainId} {d : Word} {y : Address}
    (hN : NoRebind W s h d y) (g : ChainId) (z : Address) (hz : s.ctmAsset g z ≠ 0) :
    upd2 s.ctmAsset h y (W.enc h d) g z = s.ctmAsset g z := by
  simp only [upd2_apply]
  split_ifs with hk
  · obtain ⟨rfl, rfl⟩ := hk
    rcases hN.2.2 with h0 | h1
    · exact absurd h0 hz
    · exact h1.symm
  · rfl

/-- A disciplined registration keeps the two asset maps mutually inverse. -/
private lemma bij_set {W : World} {s : Sys} {h : ChainId} {d : Word} {y : Address}
    (hbij : AssetBij s) (hy : y ≠ 0) (hN : NoRebind W s h d y) :
    AssetBij { s with
      assetCtm := upd2 s.assetCtm h (W.enc h d) y
      ctmAsset := upd2 s.ctmAsset h y (W.enc h d) } := by
  obtain ⟨ha0, hto, hfrom⟩ := hN
  intro g a z
  show (upd2 s.assetCtm h (W.enc h d) y g a = z ∧ z ≠ 0) ↔
    (upd2 s.ctmAsset h y (W.enc h d) g z = a ∧ a ≠ 0)
  simp only [upd2_apply]
  by_cases hg : g = h
  · subst hg
    by_cases haa : a = W.enc g d <;> by_cases hzz : z = y
    · subst haa; subst hzz; simp [ha0, hy]
    · -- the asset id is re-bound: only `y` is on the left; `z ≠ y` is not on the right
      rw [ite_eq_left ⟨rfl, haa⟩, ite_eq_right (fun hk => hzz hk.2)]
      constructor
      · rintro ⟨rfl, _⟩; exact absurd rfl hzz
      · rintro ⟨hza, hane⟩
        have := (hbij g a z).2 ⟨hza, hane⟩
        rw [haa] at this
        rcases hto with h0 | h1
        · exact absurd (this.1.symm.trans h0) this.2
        · exact absurd (this.1.symm.trans h1) hzz
    · rw [ite_eq_right (fun hk => haa hk.2), ite_eq_left ⟨rfl, hzz⟩]
      constructor
      · rintro ⟨hza, hzne⟩
        have := (hbij g a z).1 ⟨hza, hzne⟩
        rw [hzz] at this
        rcases hfrom with h0 | h1
        · exact absurd (this.1.symm.trans h0) this.2
        · exact absurd (this.1.symm.trans h1) haa
      · rintro ⟨rfl, _⟩; exact absurd rfl haa
    · rw [ite_eq_right (fun hk => haa hk.2), ite_eq_right (fun hk => hzz hk.2)]
      exact hbij g a z
  · rw [ite_eq_right (fun hk => hg hk.1), ite_eq_right (fun hk => hg hk.1)]
    exact hbij g a z

/-- A disciplined `setCTMAssetAddress`. -/
private lemma inv_set {W : World} {s : Sys} {h : ChainId} {d : Word} {y : Address}
    (hI : CtmInv W s) (hy : y ≠ 0) (hN : NoRebind W s h d y) :
    CtmInv W { s with
      assetCtm := upd2 s.assetCtm h (W.enc h d) y
      ctmAsset := upd2 s.ctmAsset h y (W.enc h d) } := by
  obtain ⟨hbij, hnz, hag, hhome, hsent⟩ := hI
  have stable := ctmAsset_stable hN
  refine ⟨bij_set hbij hy hN, hnz, hag, ?_, ?_⟩
  · intro g c D hg hD
    obtain ⟨X, hX, hnzX, heq⟩ := hhome g c D hg hD
    refine ⟨X, hX, ?_, ?_⟩
    · show upd2 s.ctmAsset h y (W.enc h d) W.l1 X ≠ 0
      rw [stable _ _ hnzX]; exact hnzX
    · show upd2 s.ctmAsset h y (W.enc h d) g D = upd2 s.ctmAsset h y (W.enc h d) W.l1 X
      rw [stable _ _ hnzX, stable _ _ (heq ▸ hnzX)]; exact heq
  · intro m hm
    obtain ⟨X, hX, hasset⟩ := hsent m hm
    refine ⟨X, hX, ?_⟩
    show m.asset = 0 ∨ m.asset = upd2 s.ctmAsset h y (W.enc h d) W.l1 X
    by_cases hz : s.ctmAsset W.l1 X = 0
    · left
      rcases hasset with h0 | h1
      · exact h0
      · rw [h1, hz]
    · rw [stable _ _ hz]; exact hasset

/-- A `bridgeBurn` of a chain with a diamond. -/
private lemma inv_burn {W : World} {s : Sys} {h c dst : ChainId} {D : Address}
    (hI : CtmInv W s) (hD : s.diamond h c = some D) :
    CtmInv W { s with
      settlement := upd2 s.settlement h c dst
      sent := s.sent ++ [⟨c, s.ctmAsset h (s.bhCtm h c), h, dst⟩] } := by
  obtain ⟨hbij, hnz, hag, hhome, hsent⟩ := hI
  refine ⟨hbij, hnz, hag, hhome, ?_⟩
  intro m hm
  rcases List.mem_append.1 hm with hm | hm
  · exact hsent m hm
  · rw [List.mem_singleton] at hm
    subst hm
    have hrec := hag h c D hD
    by_cases hh : h = W.l1
    · subst hh
      exact ⟨D, hD, Or.inr (by rw [hrec])⟩
    · obtain ⟨X, hX, _, heq⟩ := hhome h c D hh hD
      exact ⟨X, hX, Or.inr (by show s.ctmAsset h (s.bhCtm h c) = _; rw [hrec]; exact heq)⟩

/-- What a mint of a sent message with a nonzero CTM reads, under the invariant: the message
carries the nonzero asset id of its chain's L1 CTM, the layer maps it back, and an existing
diamond there is under the asset's CTM. -/
private lemma mint_key {W : World} {s : Sys} {m : Msg} (hI : CtmInv W s) (hm : m ∈ s.sent)
    (hG : s.assetCtm m.dst m.asset ≠ 0) :
    ∃ X, s.diamond W.l1 m.chain = some X ∧ m.asset = s.ctmAsset W.l1 X ∧ m.asset ≠ 0 ∧
      s.ctmAsset m.dst (s.assetCtm m.dst m.asset) = m.asset ∧
      ∀ D, s.diamond m.dst m.chain = some D → D = s.assetCtm m.dst m.asset := by
  obtain ⟨hbij, _, _, hhome, hsent⟩ := hI
  obtain ⟨X, hX, hasset⟩ := hsent m hm
  obtain ⟨hfromG, ha⟩ := (hbij m.dst m.asset _).1 ⟨rfl, hG⟩
  have hasset' : m.asset = s.ctmAsset W.l1 X := hasset.resolve_left ha
  refine ⟨X, hX, hasset', ha, hfromG, ?_⟩
  intro D hD
  by_cases hdst : m.dst = W.l1
  · rw [hdst] at hD ⊢
    rw [hX] at hD
    cases hD
    exact ((hbij W.l1 m.asset X).2 ⟨hasset'.symm, ha⟩).1.symm
  · obtain ⟨X', hX', _, heq⟩ := hhome m.dst m.chain D hdst hD
    rw [hX] at hX'
    cases hX'
    exact ((hbij m.dst m.asset D).2 ⟨heq.trans hasset'.symm, ha⟩).1.symm

/-- Under the invariant, the CTM a mint deploys or keeps is the asset's CTM. -/
private lemma mint_getD {W : World} {s : Sys} {m : Msg} (hI : CtmInv W s) (hm : m ∈ s.sent)
    (hG : s.assetCtm m.dst m.asset ≠ 0) :
    (s.diamond m.dst m.chain).getD (s.assetCtm m.dst m.asset) = s.assetCtm m.dst m.asset := by
  obtain ⟨_, _, _, _, _, hexist⟩ := mint_key hI hm hG
  cases hd : s.diamond m.dst m.chain with
  | none => rfl
  | some D => exact hexist D hd

/-- A `bridgeMint` of a sent message with a nonzero CTM. -/
private lemma inv_mint {W : World} {s : Sys} {m : Msg} (hI : CtmInv W s) (hm : m ∈ s.sent)
    (hG : s.assetCtm m.dst m.asset ≠ 0) :
    CtmInv W { s with
      settlement := upd2 s.settlement m.dst m.chain m.dst
      bhCtm := upd2 s.bhCtm m.dst m.chain (s.assetCtm m.dst m.asset)
      diamond := upd2 s.diamond m.dst m.chain
        (some ((s.diamond m.dst m.chain).getD (s.assetCtm m.dst m.asset))) } := by
  have hgetD := mint_getD hI hm hG
  obtain ⟨X, hX, hasset, ha, hfromG, _⟩ := mint_key hI hm hG
  obtain ⟨hbij, hnz, hag, hhome, hsent⟩ := hI
  have hL1 : ∀ c', upd2 s.diamond m.dst m.chain
      (some ((s.diamond m.dst m.chain).getD (s.assetCtm m.dst m.asset))) W.l1 c' =
      s.diamond W.l1 c' := by
    intro c'
    simp only [upd2_apply]
    split_ifs with hk
    · obtain ⟨h1, h2⟩ := hk
      have hd : s.diamond m.dst m.chain = some X := by rw [← h1]; exact hX
      rw [h2, h1, hd]; rfl
    · rfl
  refine ⟨hbij, ?_, ?_, ?_, ?_⟩
  · intro h c D hD
    simp only [upd2_apply] at hD
    split_ifs at hD with hk
    · rw [hgetD] at hD; cases hD; exact hG
    · exact hnz _ _ _ hD
  · intro h c D hD
    simp only [upd2_apply] at hD ⊢
    split_ifs at hD ⊢ with hk
    · rw [hgetD] at hD; cases hD; rfl
    · exact hag _ _ _ hD
  · intro h c D hh hD
    have hD' := hD
    simp only [upd2_apply] at hD'
    split_ifs at hD' with hk
    · obtain ⟨h1, h2⟩ := hk
      rw [hgetD] at hD'
      cases hD'
      refine ⟨X, ?_, ?_, ?_⟩
      · show upd2 s.diamond m.dst m.chain _ W.l1 c = some X
        rw [hL1, h2]; exact hX
      · rw [← hasset]; exact ha
      · show s.ctmAsset h (s.assetCtm m.dst m.asset) = s.ctmAsset W.l1 X
        rw [h1, hfromG, hasset]
    · obtain ⟨X', hX', hnz', heq'⟩ := hhome h c D hh hD'
      refine ⟨X', ?_, hnz', heq'⟩
      show upd2 s.diamond m.dst m.chain _ W.l1 c = some X'
      rw [hL1]; exact hX'
  · intro m' hm'
    obtain ⟨X', hX', h'⟩ := hsent m' hm'
    refine ⟨X', ?_, h'⟩
    show upd2 s.diamond m.dst m.chain _ W.l1 m'.chain = some X'
    rw [hL1]; exact hX'

theorem CtmRecordInvStep : Properties.CtmRecordInvStep := by
  intro W s op s' hI hok hs
  cases hs with
  | createNewChain _ _ hx _ hnone => exact inv_addChain hI hnone hx
  | registerAlreadyDeployed hnone _ _ hx _ => exact inv_addChain hI hnone hx
  | setCTMAssetAddress hy => exact inv_set hI hy hok
  | bridgeBurn _ _ hD _ _ _ _ => exact inv_burn hI hD
  | bridgeMint hm hG _ _ => exact inv_mint hI hm hG
  | confirmFailure _ _ =>
    obtain ⟨hbij, hnz, hag, hhome, hsent⟩ := hI
    exact ⟨hbij, hnz, hag, hhome, hsent⟩

private lemma inv_run {W : World} :
    ∀ {s : Sys} {ops : List Op} {s' : Sys}, Run W (Disciplined W) s ops s' →
      CtmInv W s → CtmInv W s' := by
  intro s ops s' hr
  induction hr with
  | nil _ => exact id
  | cons hok hs _ ih => exact fun hI => ih (CtmRecordInvStep _ _ _ _ hI hok hs)

theorem CtmRecordInvReachable : Properties.CtmRecordInvReachable := by
  rintro W s ⟨ops, hr⟩
  exact inv_run hr (CtmRecordInvInit W)

theorem CtmRecordAgreesWithDiamond : Properties.CtmRecordAgreesWithDiamond :=
  fun W s hs => (CtmRecordInvReachable W s hs).agree

theorem CtmRecordSettlementDiamondFollowsL1Ctm :
    Properties.CtmRecordSettlementDiamondFollowsL1Ctm := by
  intro W s hs h c D hh hD
  have hI := CtmRecordInvReachable W s hs
  obtain ⟨X, hX, hnzX, heq⟩ := hI.home h c D hh hD
  refine ⟨X, hX, hnzX, ?_⟩
  exact ((hI.bij h (s.ctmAsset W.l1 X) D).2 ⟨heq, hnzX⟩).1

/-! ## The corollaries -/

theorem CtmRecordBurnGatesAreDiamondCtm : Properties.CtmRecordBurnGatesAreDiamondCtm := by
  intro W s hs h c D hD
  have hI := CtmRecordInvReachable W s hs
  have hrec := hI.agree h c D hD
  refine ⟨hrec, ?_, ?_⟩
  · intro hne
    unfold burnPauseCtm
    unfold burnAsset at hne ⊢
    rw [hrec] at hne ⊢
    exact ((hI.bij h (s.ctmAsset h D) D).2 ⟨rfl, hne⟩).1
  · intro hh
    obtain ⟨X, _, hnzX, heq⟩ := hI.home h c D hh hD
    unfold burnAsset
    rw [hrec, heq]; exact hnzX

theorem CtmRecordMintGatesAreDiamondCtm : Properties.CtmRecordMintGatesAreDiamondCtm := by
  intro W s m s' hs hstep
  have hI := CtmRecordInvReachable W s hs
  cases hstep with
  | bridgeMint hm hG _ _ =>
    have hgetD := mint_getD hI hm hG
    refine ⟨hgetD, ?_, ?_⟩
    · show upd2 s.diamond m.dst m.chain _ m.dst m.chain = _
      rw [upd2_apply, ite_eq_left ⟨rfl, rfl⟩, hgetD]; rfl
    · show upd2 s.bhCtm m.dst m.chain _ m.dst m.chain = _
      rw [upd2_apply, ite_eq_left ⟨rfl, rfl⟩]; rfl

/-! ## The discipline is exactly what keeps the bijection -/

theorem CtmRecordNoRebindIffKeepsBijection :
    Properties.CtmRecordNoRebindIffKeepsBijection := by
  intro W s s' h d y hbij hs
  cases hs with
  | setCTMAssetAddress hy =>
    refine ⟨bij_set hbij hy, fun hbij' => ?_⟩
    have key : ∀ a z, (upd2 s.assetCtm h (W.enc h d) y h a = z ∧ z ≠ 0) ↔
        (upd2 s.ctmAsset h y (W.enc h d) h z = a ∧ a ≠ 0) := fun a z => hbij' h a z
    have ha0 : W.enc h d ≠ 0 := ((key (W.enc h d) y).1 ⟨by simp, hy⟩).2
    refine ⟨ha0, ?_, ?_⟩
    · -- an asset id already mapped to another CTM would keep that CTM's reverse entry
      by_contra hc
      rw [not_or] at hc
      obtain ⟨hc0, hcy⟩ := hc
      have hb := (hbij h (W.enc h d) _).1 ⟨rfl, hc0⟩
      have := (key (W.enc h d) (s.assetCtm h (W.enc h d))).2 (by
        rw [upd2_apply, ite_eq_right (fun hk => hcy hk.2)]; exact hb)
      rw [upd2_apply, ite_eq_left ⟨rfl, rfl⟩] at this
      exact hcy this.1.symm
    · -- a CTM already mapped to another asset id would keep that asset id's forward entry
      by_contra hc
      rw [not_or] at hc
      obtain ⟨hc0, hca⟩ := hc
      have hb := (hbij h _ y).2 ⟨rfl, hc0⟩
      have := (key (s.ctmAsset h y) y).1 (by
        rw [upd2_apply, ite_eq_right (fun hk => hca hk.2)]; exact hb)
      rw [upd2_apply, ite_eq_left ⟨rfl, rfl⟩] at this
      exact hca this.1.symm

/-! ## The repaired mint -/

/-- The agreement half of `CtmInv`, which the repaired mint keeps without any discipline. -/
private def AgreeInv (s : Sys) : Prop :=
  (∀ h c D, s.diamond h c = some D → D ≠ 0) ∧
    (∀ h c D, s.diamond h c = some D → s.bhCtm h c = D)

private lemma agreeInv_step {W : World} {s s' : Sys} {op : Op}
    (hA : AgreeInv s) (hok : RepairGuard s op) (hs : Step W s op s') : AgreeInv s' := by
  obtain ⟨hnz, hag⟩ := hA
  cases hs with
  | @createNewChain c x _ _ hx _ hnone =>
    refine ⟨?_, ?_⟩
    · intro h c' D hD
      simp only [Sys.addChain, upd2_apply] at hD
      split_ifs at hD with hk
      · cases hD; exact hx
      · exact hnz _ _ _ hD
    · intro h c' D hD
      simp only [Sys.addChain, upd2_apply] at hD ⊢
      split_ifs at hD ⊢ with hk
      · cases hD; rfl
      · exact hag _ _ _ hD
  | @registerAlreadyDeployed c x hnone _ _ hx _ =>
    refine ⟨?_, ?_⟩
    · intro h c' D hD
      simp only [Sys.addChain, upd2_apply] at hD
      split_ifs at hD with hk
      · cases hD; exact hx
      · exact hnz _ _ _ hD
    · intro h c' D hD
      simp only [Sys.addChain, upd2_apply] at hD ⊢
      split_ifs at hD ⊢ with hk
      · cases hD; rfl
      · exact hag _ _ _ hD
  | setCTMAssetAddress _ => exact ⟨hnz, hag⟩
  | bridgeBurn _ _ _ _ _ _ _ => exact ⟨hnz, hag⟩
  | @bridgeMint m _ hG _ _ =>
    have hgetD : (s.diamond m.dst m.chain).getD (s.assetCtm m.dst m.asset) =
        s.assetCtm m.dst m.asset := by
      cases hd : s.diamond m.dst m.chain with
      | none => rfl
      | some D => exact hok D hd
    refine ⟨?_, ?_⟩
    · intro h c D hD
      simp only [upd2_apply] at hD
      split_ifs at hD with hk
      · rw [hgetD] at hD; cases hD; exact hG
      · exact hnz _ _ _ hD
    · intro h c D hD
      simp only [upd2_apply] at hD ⊢
      split_ifs at hD ⊢ with hk
      · rw [hgetD] at hD; cases hD; rfl
      · exact hag _ _ _ hD
  | confirmFailure _ _ => exact ⟨hnz, hag⟩

private lemma agreeInv_run {W : World} :
    ∀ {s : Sys} {ops : List Op} {s' : Sys}, Run W RepairGuard s ops s' →
      AgreeInv s → AgreeInv s' := by
  intro s ops s' hr
  induction hr with
  | nil _ => exact id
  | cons hok hs _ ih => exact fun hA => ih (agreeInv_step hA hok hs)

theorem CtmRecordRepairedMintAgrees : Properties.CtmRecordRepairedMintAgrees := by
  intro W ops s hr
  have hA : AgreeInv Sys.init := ⟨by intro h c D hD; simp [Sys.init] at hD,
    by intro h c D hD; simp [Sys.init] at hD⟩
  exact (agreeInv_run hr hA).2

private lemma admits_run {W : World} :
    ∀ {s : Sys} {ops : List Op} {s' : Sys}, Run W (Disciplined W) s ops s' →
      CtmInv W s → Run W RepairGuard s ops s' := by
  intro s ops s' hr
  induction hr with
  | nil s => exact fun _ => Run.nil s
  | @cons s s1 s2 op ops hok hs _ ih =>
    intro hI
    refine Run.cons ?_ hs (ih (CtmRecordInvStep _ _ _ _ hI hok hs))
    cases hs with
    | bridgeMint hm hG _ _ => exact (mint_key hI hm hG).choose_spec.2.2.2.2
    | createNewChain _ _ _ _ _ => trivial
    | registerAlreadyDeployed _ _ _ _ _ => trivial
    | setCTMAssetAddress _ => trivial
    | bridgeBurn _ _ _ _ _ _ _ => trivial
    | confirmFailure _ _ => trivial

theorem CtmRecordRepairAdmitsDisciplinedRuns :
    Properties.CtmRecordRepairAdmitsDisciplinedRuns := by
  intro W ops s hr
  exact admits_run hr (CtmRecordInvInit W)

/-- With no mint among the calls, the repaired mint's check never applies. -/
private lemma run_repair_of_no_mint {W : World} :
    ∀ {s : Sys} {ops : List Op} {s' : Sys}, Run W AnyCall s ops s' →
      (∀ m, Op.bridgeMint m ∉ ops) → Run W RepairGuard s ops s' := by
  intro s ops s' hr
  induction hr with
  | nil s => intro _; exact Run.nil s
  | @cons s s1 s2 op ops _ hs _ ih =>
    intro hno
    refine Run.cons ?_ hs (ih (fun m hm => hno m (List.mem_cons_of_mem _ hm)))
    cases op with
    | bridgeMint m => exact absurd List.mem_cons_self (hno m)
    | createNewChain => trivial
    | registerAlreadyDeployed => trivial
    | setCTMAssetAddress => trivial
    | bridgeBurn => trivial
    | confirmFailure => trivial

theorem CtmRecordAgreesWithoutMints : Properties.CtmRecordAgreesWithoutMints := by
  intro W ops s hr hno
  exact CtmRecordRepairedMintAgrees W ops s (run_repair_of_no_mint hr hno)

/-! ## The tracker-level discipline -/

/-- The asset maps hold only what the registrations in `L` wrote. -/
private def RegInv (W : World) (L : List (ChainId × Word × Address)) (s : Sys) : Prop :=
  (∀ h a, s.assetCtm h a ≠ 0 → ∃ d y, (h, d, y) ∈ L ∧ W.enc h d = a ∧ s.assetCtm h a = y) ∧
    (∀ h y, s.ctmAsset h y ≠ 0 → ∃ d, (h, d, y) ∈ L ∧ s.ctmAsset h y = W.enc h d)

/-- `PairDiscipline`'s condition, over an explicit list of registrations. -/
private def PairOk (W : World) (L : List (ChainId × Word × Address)) : Prop :=
  ∀ h d y d' y', (h, d, y) ∈ L → (h, d', y') ∈ L →
    (d = d' ↔ y = y') ∧ (W.enc h d = W.enc h d' → d = d') ∧ W.enc h d ≠ 0

/-- A call that is not a registration leaves both asset maps alone. -/
private lemma step_maps {W : World} {s s' : Sys} {op : Op} (hs : Step W s op s')
    (hop : ∀ h d y, op ≠ .setCTMAssetAddress h d y) :
    s'.assetCtm = s.assetCtm ∧ s'.ctmAsset = s.ctmAsset := by
  cases hs <;> first | exact absurd rfl (hop _ _ _) | exact ⟨rfl, rfl⟩

private lemma pair_run {W : World} :
    ∀ {s : Sys} {ops : List Op} {s' : Sys}, Run W AnyCall s ops s' →
      ∀ L, RegInv W L s → PairOk W (L ++ regsOf ops) → Run W (Disciplined W) s ops s' := by
  intro s ops s' hr
  induction hr with
  | nil s => intro _ _ _; exact Run.nil s
  | @cons s s1 s2 op ops _ hs _ ih =>
    intro L hR hP
    by_cases hreg : ∃ h d y, op = .setCTMAssetAddress h d y
    · obtain ⟨h, d, y, rfl⟩ := hreg
      have hmem : (h, d, y) ∈ L ++ regsOf (.setCTMAssetAddress h d y :: ops) := by
        simp [regsOf]
      have hin : ∀ r ∈ L, r ∈ L ++ regsOf (.setCTMAssetAddress h d y :: ops) :=
        fun r hr => List.mem_append_left _ hr
      have hN : NoRebind W s h d y := by
        refine ⟨(hP h d y d y hmem hmem).2.2, ?_, ?_⟩
        · by_cases h0 : s.assetCtm h (W.enc h d) = 0
          · exact Or.inl h0
          · right
            obtain ⟨d', y', hL, henc, hval⟩ := hR.1 h (W.enc h d) h0
            have hp := hP h d' y' d y (hin _ hL) hmem
            rw [hval, hp.1.1 (hp.2.1 henc)]
        · by_cases h0 : s.ctmAsset h y = 0
          · exact Or.inl h0
          · right
            obtain ⟨d', hL, hval⟩ := hR.2 h y h0
            have hp := hP h d' y d y (hin _ hL) hmem
            rw [hval, hp.1.2 rfl]
      cases hs with
      | setCTMAssetAddress hy =>
        refine Run.cons hN (Step.setCTMAssetAddress hy) (ih (L ++ [(h, d, y)]) ⟨?_, ?_⟩ ?_)
        · intro h' a ha
          show ∃ d' y', (h', d', y') ∈ L ++ [(h, d, y)] ∧ W.enc h' d' = a ∧
            upd2 s.assetCtm h (W.enc h d) y h' a = y'
          by_cases hk : h' = h ∧ a = W.enc h d
          · obtain ⟨rfl, rfl⟩ := hk
            exact ⟨d, y, by simp, rfl, by simp⟩
          · have ha' : s.assetCtm h' a ≠ 0 := by
              simpa [upd2_apply, hk] using ha
            obtain ⟨d', y', hL, henc, hval⟩ := hR.1 h' a ha'
            exact ⟨d', y', List.mem_append_left _ hL, henc, by simp [upd2_apply, hk, hval]⟩
        · intro h' z hz
          show ∃ d', (h', d', z) ∈ L ++ [(h, d, y)] ∧
            upd2 s.ctmAsset h y (W.enc h d) h' z = W.enc h' d'
          by_cases hk : h' = h ∧ z = y
          · obtain ⟨rfl, rfl⟩ := hk
            exact ⟨d, by simp, by simp⟩
          · have hz' : s.ctmAsset h' z ≠ 0 := by
              simpa [upd2_apply, hk] using hz
            obtain ⟨d', hL, hval⟩ := hR.2 h' z hz'
            exact ⟨d', List.mem_append_left _ hL, by simp [upd2_apply, hk, hval]⟩
        · have hsub : ∀ r, r ∈ L ++ [(h, d, y)] ++ regsOf ops →
              r ∈ L ++ regsOf (.setCTMAssetAddress h d y :: ops) := by
            intro r hr
            simp only [regsOf, List.mem_append, List.mem_cons,
              List.not_mem_nil, or_false] at hr ⊢
            tauto
          exact fun h1 d1 y1 d2 y2 m1 m2 => hP h1 d1 y1 d2 y2 (hsub _ m1) (hsub _ m2)
    · have hop : ∀ h d y, op ≠ .setCTMAssetAddress h d y :=
        fun h d y he => hreg ⟨h, d, y, he⟩
      have hregs : regsOf (op :: ops) = regsOf ops := by
        cases op <;> first | rfl | exact absurd rfl (hop _ _ _)
      obtain ⟨hto, hfrom⟩ := step_maps hs hop
      have hok : Disciplined W s op := by
        cases op <;> first | trivial | exact absurd rfl (hop _ _ _)
      refine Run.cons hok hs (ih L ⟨?_, ?_⟩ (by rw [← hregs]; exact hP))
      · intro h a ha
        rw [hto] at ha ⊢
        exact hR.1 h a ha
      · intro h y hy
        rw [hfrom] at hy ⊢
        exact hR.2 h y hy

theorem CtmRecordPairDisciplineGivesNoRebind :
    Properties.CtmRecordPairDisciplineGivesNoRebind := by
  intro W ops s hr hP
  refine pair_run hr [] ⟨?_, ?_⟩ ?_
  · intro h a ha; simp [Sys.init] at ha
  · intro h y hy; simp [Sys.init] at hy
  · simpa [PairOk, PairDiscipline] using hP

theorem CtmRecordAgreesUnderPairDiscipline :
    Properties.CtmRecordAgreesUnderPairDiscipline := by
  intro W ops s hr hP
  exact CtmRecordAgreesWithDiamond W s ⟨ops, CtmRecordPairDisciplineGivesNoRebind W ops s hr hP⟩

/-! ## Runs -/

private lemma run_snoc {W : World} {ok : Sys → Op → Prop} :
    ∀ {s : Sys} {ops : List Op} {s' : Sys} {op : Op} {s'' : Sys},
      Run W ok s ops s' → ok s' op → Step W s' op s'' → Run W ok s (ops ++ [op]) s'' := by
  intro s ops s' op s'' hr hok hs
  induction hr with
  | nil s => exact Run.cons hok hs (Run.nil _)
  | cons hok' hs' _ ih => exact Run.cons hok' hs' (ih hok hs)

private lemma run_any {W : World} {ok : Sys → Op → Prop} :
    ∀ {s : Sys} {ops : List Op} {s' : Sys}, Run W ok s ops s' → Run W AnyCall s ops s' := by
  intro s ops s' hr
  induction hr with
  | nil s => exact Run.nil s
  | cons _ hs _ ih => exact Run.cons trivial hs ih

section Runs

attribute [local simp] Sys.addChain Sys.init wWorld wReturnMsg cmReturnMsg mintPauseCtm
  mintVersionCtm burnAsset burnPauseCtm burnVersionCtm NoRebind Disciplined RepairGuard

/-- The calls of the disciplined round trip, as a literal list. -/
private lemma wTrip_eq (e : Word → AssetId) :
    wSetup ++ wRegs ++ wOut e =
      [.createNewChain 2 10, .createNewChain 3 10, .setCTMAssetAddress 1 10 10,
        .setCTMAssetAddress 1 11 11, .setCTMAssetAddress 2 10 20,
        .setCTMAssetAddress 2 11 21, .setCTMAssetAddress 2 10 20,
        .bridgeBurn 1 3 2, .bridgeMint ⟨3, e 10, 1, 2⟩, .bridgeBurn 2 3 1] := rfl

theorem CtmRecordDisciplinedRoundTripWitness :
    Properties.CtmRecordDisciplinedRoundTripWitness := by
  intro e h10 h11 hne
  have hne' : e 11 ≠ e 10 := fun h => hne h.symm
  rw [wTrip_eq]
  exact ⟨_, _,
    Run.cons trivial (Step.createNewChain (by simp) (by simp) (by simp) rfl rfl) <|
    Run.cons trivial (Step.createNewChain (by simp) (by simp) (by simp) (by simp) (by simp)) <|
    Run.cons (by simp [*]) (Step.setCTMAssetAddress (by simp)) <|
    Run.cons (by simp [*]) (Step.setCTMAssetAddress (by simp)) <|
    Run.cons (by simp [*]) (Step.setCTMAssetAddress (by simp)) <|
    Run.cons (by simp [*]) (Step.setCTMAssetAddress (by simp)) <|
    Run.cons (by simp [*]) (Step.setCTMAssetAddress (by simp)) <|
    Run.cons trivial (Step.bridgeBurn (D := 10) (by simp [*]) (by simp [*]) (by simp [*])
      (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])) <|
    Run.cons trivial (Step.bridgeMint (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])) <|
    Run.cons trivial (Step.bridgeBurn (D := 20) (by simp [*]) (by simp [*]) (by simp [*])
      (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])) <|
    Run.nil _,
    Step.bridgeMint (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*]),
    by simp [*]⟩

theorem CtmRecordUndisciplinedRoundTripDrifts :
    Properties.CtmRecordUndisciplinedRoundTripDrifts := by
  intro e h10 h11 hne
  have hne' : e 11 ≠ e 10 := fun h => hne h.symm
  have hs : wSetup = [.createNewChain 2 10, .createNewChain 3 10, .setCTMAssetAddress 1 10 10,
      .setCTMAssetAddress 1 11 11, .setCTMAssetAddress 2 10 20] := rfl
  have ho : wOut e = [.bridgeBurn 1 3 2, .bridgeMint ⟨3, e 10, 1, 2⟩, .bridgeBurn 2 3 1] := rfl
  rw [hs, ho]; clear hs ho
  exact ⟨_, _, _, _,
    Run.cons trivial (Step.createNewChain (by simp) (by simp) (by simp) rfl rfl) <|
    Run.cons trivial (Step.createNewChain (by simp) (by simp) (by simp) (by simp) (by simp)) <|
    Run.cons (by simp [*]) (Step.setCTMAssetAddress (by simp)) <|
    Run.cons (by simp [*]) (Step.setCTMAssetAddress (by simp)) <|
    Run.cons (by simp [*]) (Step.setCTMAssetAddress (by simp)) <|
    Run.nil _,
    by simp [cmRebind, *],
    Step.setCTMAssetAddress (by simp),
    Run.cons trivial (Step.bridgeBurn (D := 10) (by simp [*]) (by simp [*]) (by simp [*])
      (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])) <|
    Run.cons trivial (Step.bridgeMint (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])) <|
    Run.cons trivial (Step.bridgeBurn (D := 20) (by simp [*]) (by simp [*]) (by simp [*])
      (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])) <|
    Run.nil _,
    by simp [*], by simp [*], by simp [*],
    Step.bridgeMint (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*]),
    by simp [*]⟩

theorem CtmRecordStaleReverseEntryMisgatesPause :
    Properties.CtmRecordStaleReverseEntryMisgatesPause := by
  intro e h10
  have hs : staleSetup e = [.createNewChain 2 10, .createNewChain 3 10,
      .setCTMAssetAddress 1 10 10, .setCTMAssetAddress 2 10 20, .bridgeBurn 1 3 2,
      .bridgeMint ⟨3, e 10, 1, 2⟩] := rfl
  rw [hs]; clear hs
  exact ⟨_, _,
    Run.cons trivial (Step.createNewChain (by simp) (by simp) (by simp) rfl rfl) <|
    Run.cons trivial (Step.createNewChain (by simp) (by simp) (by simp) (by simp) (by simp)) <|
    Run.cons (by simp [*]) (Step.setCTMAssetAddress (by simp)) <|
    Run.cons (by simp [*]) (Step.setCTMAssetAddress (by simp)) <|
    Run.cons trivial (Step.bridgeBurn (D := 10) (by simp [*]) (by simp [*]) (by simp [*])
      (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])) <|
    Run.cons trivial (Step.bridgeMint (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])) <|
    Run.nil _,
    by simp [staleRebind, *],
    Step.setCTMAssetAddress (by simp),
    by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], by simp [*],
    by simp [*], _, _,
    Step.bridgeBurn (D := 20) (by simp [*]) (by simp [*]) (by simp [*])
      (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*]),
    Step.bridgeMint (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*]),
    by simp [*], by simp [*]⟩

theorem CtmRecordRepairedRoundTripWitness : Properties.CtmRecordRepairedRoundTripWitness := by
  intro e h10 h11 hne
  obtain ⟨s₁, s₂, hr, hs, -, -, -, -, -, h1, h2, -, h3, -⟩ :=
    CtmRecordDisciplinedRoundTripWitness e h10 h11 hne
  exact ⟨s₂, CtmRecordRepairAdmitsDisciplinedRuns _ _ _ (run_snoc hr trivial hs), h1, h2, h3⟩

theorem CtmRecordRepairedMintKeepsStalePauseGate :
    Properties.CtmRecordRepairedMintKeepsStalePauseGate := by
  intro e h10
  have hs : staleSetup e ++ [staleRebind] = [.createNewChain 2 10, .createNewChain 3 10,
      .setCTMAssetAddress 1 10 10, .setCTMAssetAddress 2 10 20, .bridgeBurn 1 3 2,
      .bridgeMint ⟨3, e 10, 1, 2⟩, .setCTMAssetAddress 2 10 21] := rfl
  rw [hs]; clear hs
  exact ⟨_,
    Run.cons trivial (Step.createNewChain (by simp) (by simp) (by simp) rfl rfl) <|
    Run.cons trivial (Step.createNewChain (by simp) (by simp) (by simp) (by simp) (by simp)) <|
    Run.cons trivial (Step.setCTMAssetAddress (by simp)) <|
    Run.cons trivial (Step.setCTMAssetAddress (by simp)) <|
    Run.cons trivial (Step.bridgeBurn (D := 10) (by simp [*]) (by simp [*]) (by simp [*])
      (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])) <|
    Run.cons (by simp [*]) (Step.bridgeMint (by simp [*]) (by simp [*]) (by simp [*])
      (by simp [*])) <|
    Run.cons trivial (Step.setCTMAssetAddress (by simp)) <|
    Run.nil _,
    by simp [*]⟩

/-- The disciplined `wSetup` run, with the three entries of its final state that the
registrations `11 ↦ 21` and `11 ↦ 20` on layer `2` read. -/
private lemma setup_run (e : Word → AssetId) (h10 : e 10 ≠ 0) (h11 : e 11 ≠ 0)
    (hne : e 10 ≠ e 11) :
    ∃ s₀, Run (wWorld e) (Disciplined (wWorld e)) Sys.init wSetup s₀ ∧
      s₀.assetCtm 2 (e 11) = 0 ∧ s₀.ctmAsset 2 21 = 0 ∧ s₀.ctmAsset 2 20 = e 10 := by
  have hne' : e 11 ≠ e 10 := fun h => hne h.symm
  have hs : wSetup = [.createNewChain 2 10, .createNewChain 3 10, .setCTMAssetAddress 1 10 10,
      .setCTMAssetAddress 1 11 11, .setCTMAssetAddress 2 10 20] := rfl
  rw [hs]
  exact ⟨_,
    Run.cons trivial (Step.createNewChain (by simp) (by simp) (by simp) rfl rfl) <|
    Run.cons trivial (Step.createNewChain (by simp) (by simp) (by simp) (by simp) (by simp)) <|
    Run.cons (by simp [*]) (Step.setCTMAssetAddress (by simp)) <|
    Run.cons (by simp [*]) (Step.setCTMAssetAddress (by simp)) <|
    Run.cons (by simp [*]) (Step.setCTMAssetAddress (by simp)) <|
    Run.nil _,
    by simp [*]⟩

theorem CtmRecordNoRebindIffKeepsBijectionWitness :
    Properties.CtmRecordNoRebindIffKeepsBijectionWitness := by
  intro e h10 h11 hne
  obtain ⟨s₀, hr, ha, hf21, hf20⟩ := setup_run e h10 h11 hne
  have hbij : AssetBij s₀ := (CtmRecordInvReachable _ _ ⟨_, hr⟩).bij
  have hs₁ : Step (wWorld e) s₀ (.setCTMAssetAddress 2 11 21) _ :=
    Step.setCTMAssetAddress (by decide)
  have hs₂ : Step (wWorld e) s₀ (.setCTMAssetAddress 2 11 20) _ :=
    Step.setCTMAssetAddress (by decide)
  have hN₁ : NoRebind (wWorld e) s₀ 2 11 21 := ⟨h11, Or.inl ha, Or.inl hf21⟩
  have hN₂ : ¬ NoRebind (wWorld e) s₀ 2 11 20 := by
    rintro ⟨-, -, h0 | h1⟩
    · rw [hf20] at h0; exact h10 h0
    · rw [hf20] at h1; exact hne h1
  exact ⟨s₀, _, _, hr, hbij, hs₁, hN₁,
    (CtmRecordNoRebindIffKeepsBijection _ _ _ _ _ _ hbij hs₁).1 hN₁, hs₂, hN₂,
    fun hb => hN₂ ((CtmRecordNoRebindIffKeepsBijection _ _ _ _ _ _ hbij hs₂).2 hb)⟩

theorem CtmRecordAgreesWithoutMintsWitness :
    Properties.CtmRecordAgreesWithoutMintsWitness := by
  intro e h10 h11 hne
  have hne' : e 11 ≠ e 10 := fun h => hne h.symm
  have hl : wSetup ++ [cmRebind, .bridgeBurn 1 3 2] =
      [.createNewChain 2 10, .createNewChain 3 10, .setCTMAssetAddress 1 10 10,
        .setCTMAssetAddress 1 11 11, .setCTMAssetAddress 2 10 20,
        .setCTMAssetAddress 2 11 20, .bridgeBurn 1 3 2] := rfl
  rw [hl]
  exact ⟨_,
    Run.cons trivial (Step.createNewChain (by simp) (by simp) (by simp) rfl rfl) <|
    Run.cons trivial (Step.createNewChain (by simp) (by simp) (by simp) (by simp) (by simp)) <|
    Run.cons trivial (Step.setCTMAssetAddress (by simp)) <|
    Run.cons trivial (Step.setCTMAssetAddress (by simp)) <|
    Run.cons trivial (Step.setCTMAssetAddress (by simp)) <|
    Run.cons trivial (Step.setCTMAssetAddress (by simp)) <|
    Run.cons trivial (Step.bridgeBurn (D := 10) (by simp [*]) (by simp [*]) (by simp [*])
      (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])) <|
    Run.nil _,
    by simp, by simp [*]⟩

theorem CtmRecordPairDisciplineWitness : Properties.CtmRecordPairDisciplineWitness := by
  intro e h10 h11 hne
  have hne' : e 11 ≠ e 10 := fun h => hne h.symm
  obtain ⟨s₁, s₂, hr, hs, -⟩ := CtmRecordDisciplinedRoundTripWitness e h10 h11 hne
  refine ⟨⟨s₂, run_any (run_snoc hr trivial hs)⟩, ?_, ?_⟩
  · intro h d y d' y' hm hm'
    simp only [wSetup, wRegs, wOut, wReturnMsg, List.cons_append, List.nil_append, regsOf,
      List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hm hm'
    rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ <;>
      rcases hm' with ⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩ |
        ⟨h1, rfl, rfl⟩ <;>
      simp_all
  · intro hP
    have hm : (2, 10, 20) ∈ regsOf
        (wSetup ++ cmRebind :: wOut e ++ [.bridgeMint (cmReturnMsg e)]) := by
      simp [wSetup, wOut, cmRebind, regsOf]
    have hm' : (2, 11, 20) ∈ regsOf
        (wSetup ++ cmRebind :: wOut e ++ [.bridgeMint (cmReturnMsg e)]) := by
      simp [wSetup, wOut, cmRebind, regsOf]
    have := (hP 2 10 20 11 20 hm hm').1
    simp at this

end Runs

end Protocol.CtmRecord
