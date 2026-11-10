import EraSpec.Contracts.ProxyUpgradeRowLib.Properties.Rows

/-!
# Proofs: the registry upgrade's proxy rows

Two lemmas carry everything.  `applyRows_frame` says a run moves only the proxies
its owned rows name, and `applyRows_target` says it moves those to `implNew` — the
second needing distinct proxies, since otherwise a later row can carry a proxy past
an earlier row's target.  Determinism, idempotence, the post-state gate and order
independence are all corollaries of the pair.

The countermodels are computations: three rows, one proxy, and `decide`.
-/

namespace Contracts.ProxyUpgrade

/-! ## One row -/

@[simp] lemma upd_same (f : Impl) (p v : Address) : upd f p v p = v := by simp [upd]

lemma upd_ne (f : Impl) {q p : Address} (v : Address) (h : q ≠ p) : upd f p v q = f q := by
  simp [upd, h]

/-- A row leaves every other proxy alone. -/
lemma applyRow_frame {C : Config} {I J : Impl} {r : Row} (h : ApplyRow C I r J) :
    ∀ q, q ≠ r.proxy → J q = I q := by
  cases h with
  | leftToAdmin _ => intro _ _; rfl
  | alreadyAtTarget _ _ => intro _ _; rfl
  | upgrade _ _ _ _ => intro q hq; exact upd_ne _ _ hq

/-- A row the applier owns ends with its proxy at `implNew`, whichever of the two
skips or the upgrade it took. -/
lemma applyRow_target {C : Config} {I J : Impl} {r : Row} (h : ApplyRow C I r J)
    (hf : ¬ LeftToAdministrator C r) : J r.proxy = r.implNew := by
  cases h with
  | leftToAdmin hl => exact absurd hl hf
  | alreadyAtTarget _ he => exact he
  | upgrade _ _ _ _ => exact upd_same _ _ _

/-- A row left to a foreign administrator changes nothing. -/
lemma applyRow_fixed {C : Config} {I J : Impl} {r : Row} (h : ApplyRow C I r J)
    (hl : LeftToAdministrator C r) : J = I := by
  cases h with
  | leftToAdmin _ => rfl
  | alreadyAtTarget hn _ => exact absurd hl hn
  | upgrade hn _ _ _ => exact absurd hl hn

/-- The three loop outcomes are mutually exclusive. -/
lemma applyRow_det {C : Config} {I J K : Impl} {r : Row}
    (h₁ : ApplyRow C I r J) (h₂ : ApplyRow C I r K) : J = K := by
  cases h₁ with
  | leftToAdmin hl =>
      cases h₂ with
      | leftToAdmin _ => rfl
      | alreadyAtTarget hn _ => exact absurd hl hn
      | upgrade hn _ _ _ => exact absurd hl hn
  | alreadyAtTarget hn he =>
      cases h₂ with
      | leftToAdmin hl => exact absurd hl hn
      | alreadyAtTarget _ _ => rfl
      | upgrade _ _ hne _ => exact absurd he hne
  | upgrade hn _ hne _ =>
      cases h₂ with
      | leftToAdmin hl => exact absurd hl hn
      | alreadyAtTarget _ he => exact absurd he hne
      | upgrade _ _ _ _ => rfl

/-- A stale row does not apply at all: no state relates to any other. -/
lemma applyRow_stale {C : Config} {I : Impl} {r : Row} (hf : ¬ LeftToAdministrator C r)
    (hsrc : I r.proxy ≠ r.expectedOldImpl) (htgt : I r.proxy ≠ r.implNew) :
    ¬ ∃ J, ApplyRow C I r J := by
  rintro ⟨J, h⟩
  cases h with
  | leftToAdmin hl => exact hf hl
  | alreadyAtTarget _ he => exact htgt he
  | upgrade _ _ _ he => exact hsrc he

/-! ## A run -/

/-- A run moves only the proxies its owned rows name. -/
lemma applyRows_frame {C : Config} {I J : Impl} {rows : List Row} (h : ApplyRows C I rows J) :
    ∀ p, (∀ r ∈ rows, r.proxy = p → LeftToAdministrator C r) → J p = I p := by
  induction h with
  | nil => intro _ _; rfl
  | @cons I J K r rs hstep _ ih =>
      intro p hp
      have htail : K p = J p := ih p (fun t ht => hp t (List.mem_cons_of_mem _ ht))
      have hhead : J p = I p := by
        by_cases hq : p = r.proxy
        · exact congrFun (applyRow_fixed hstep (hp r (List.mem_cons_self _ _) hq.symm)) p
        · exact applyRow_frame hstep p hq
      exact htail.trans hhead

/-- Every owned row ends with its proxy at `implNew`.

`distinctProxies` is what makes this true: it is exactly what stops a later row
from carrying the proxy past this row's target. -/
lemma applyRows_target {C : Config} {I J : Impl} {rows : List Row} (h : ApplyRows C I rows J) :
    rows.Pairwise (fun a b => a.proxy ≠ b.proxy) →
    ∀ r ∈ rows, ¬ LeftToAdministrator C r → J r.proxy = r.implNew := by
  induction h with
  | nil => intro _ r hr; exact absurd hr (List.not_mem_nil r)
  | @cons I J K r rs hstep _ ih =>
      intro hd t ht hf
      rcases List.mem_cons.mp ht with rfl | ht'
      · -- the head row: it lands on `implNew`, and no later row names its proxy
        have hnone : ∀ u ∈ rs, u.proxy = t.proxy → LeftToAdministrator C u := fun u hu hq =>
          absurd hq.symm ((List.pairwise_cons.mp hd).1 u hu)
        exact (applyRows_frame ‹ApplyRows C J rs K› t.proxy hnone).trans (applyRow_target hstep hf)
      · exact ih (List.pairwise_cons.mp hd).2 t ht' hf

lemma applyRows_det {C : Config} {I J K : Impl} {rows : List Row}
    (h₁ : ApplyRows C I rows J) (h₂ : ApplyRows C I rows K) : J = K := by
  induction h₁ generalizing K with
  | nil => cases h₂ with | nil => rfl
  | @cons I J _ r rs hstep _ ih =>
      cases h₂ with
      | cons hstep' hrest' =>
          exact ih (by rw [applyRow_det hstep hstep']; exact hrest')

/-- A second run over the same rows takes a skip at every row. -/
lemma applyRows_idem {C : Config} {I J : Impl} {rows : List Row}
    (hd : rows.Pairwise (fun a b => a.proxy ≠ b.proxy)) (h : ApplyRows C I rows J) :
    ApplyRows C J rows J := by
  have key := applyRows_target h hd
  clear h
  induction rows with
  | nil => exact ApplyRows.nil
  | cons r rs ih =>
      refine ApplyRows.cons ?_ (ih (List.pairwise_cons.mp hd).2
        (fun t ht => key t (List.mem_cons_of_mem _ ht)))
      by_cases hl : LeftToAdministrator C r
      · exact ApplyRow.leftToAdmin hl
      · exact ApplyRow.alreadyAtTarget hl (key r (List.mem_cons_self _ _) hl)

end Contracts.ProxyUpgrade

/-! ## The countermodels -/

namespace Contracts.ProxyUpgrade

lemma cm_owned (r : Row) (h : r.admin = 0) : ¬ LeftToAdministrator cmConfig r := by
  rintro ⟨hz, _⟩; exact hz h

lemma cm_step₁ : ApplyRow cmConfig cmImpl rowAB (upd cmImpl 5 11) :=
  ApplyRow.upgrade (cm_owned _ rfl) rfl (by decide) (by decide)

lemma cm_step₂ : ApplyRow cmConfig (upd cmImpl 5 11) rowBC cmFinal :=
  ApplyRow.upgrade (cm_owned _ rfl) rfl (by decide) (by decide)

lemma cm_run : ApplyRows cmConfig cmImpl [rowAB, rowBC] cmFinal :=
  ApplyRows.cons cm_step₁ (ApplyRows.cons cm_step₂ ApplyRows.nil)

lemma cm_gate_fails : ¬ RowsApplied cmFinal [rowAB, rowBC] := by
  intro hall
  exact absurd (hall rowAB (by simp)) (by decide)

lemma cm_reverse_reverts : ¬ ∃ J, ApplyRows cmConfig cmImpl [rowBC, rowAB] J := by
  rintro ⟨J, h⟩
  cases h with
  | cons hstep _ =>
      exact applyRow_stale (r := rowBC) (cm_owned _ rfl) (by decide) (by decide) ⟨_, hstep⟩

lemma cm_replay_reverts : ¬ ∃ J, ApplyRows cmConfig cmFinal [rowAB, rowBC] J := by
  rintro ⟨J, h⟩
  cases h with
  | cons hstep _ =>
      exact applyRow_stale (r := rowAB) (cm_owned _ rfl) (by decide) (by decide) ⟨_, hstep⟩

lemma fgn_left : LeftToAdministrator fgnConfig fgnRow := ⟨by decide, by decide⟩

lemma fgn_run : ApplyRows fgnConfig cmImpl [fgnRow] cmImpl :=
  ApplyRows.cons (ApplyRow.leftToAdmin fgn_left) ApplyRows.nil

lemma fgn_gate_fails : ¬ RowsApplied cmImpl [fgnRow] := by
  intro hall
  exact absurd (hall fgnRow (by simp)) (by decide)

end Contracts.ProxyUpgrade

/-! ## The inventory -/

namespace Contracts.ProxyUpgrade

lemma mem_toRows {slots : List Row} {r : Row} : r ∈ toRows slots ↔ r ∈ slots ∧ r.implNew ≠ 0 := by
  simp [toRows, dropInertSlots, List.mem_filter]

lemma toRows_sublist (slots : List Row) : (toRows slots).Sublist slots :=
  List.filter_sublist _

end Contracts.ProxyUpgrade

/-! ## Certificates -/

namespace Contracts.ProxyUpgrade

theorem OnlyTheNamedEdge : Properties.OnlyTheNamedEdge := by
  intro C I J r h
  refine ⟨applyRow_frame h, ?_⟩
  cases h with
  | leftToAdmin _ => exact Or.inl rfl
  | alreadyAtTarget _ _ => exact Or.inl rfl
  | upgrade _ _ _ hsrc => exact Or.inr ⟨hsrc, upd_same _ _ _⟩

theorem StaleObjectCannotDowngrade : Properties.StaleObjectCannotDowngrade :=
  fun _ _ _ hf hsrc htgt => applyRow_stale hf hsrc htgt

theorem StaleObjectReverts : Properties.StaleObjectReverts := by
  rintro C I r rs hf hsrc htgt ⟨J, h⟩
  cases h with
  | cons hstep _ => exact applyRow_stale hf hsrc htgt ⟨_, hstep⟩

theorem ApplyRowsDeterministic : Properties.ApplyRowsDeterministic :=
  fun _ _ _ _ _ h₁ h₂ => applyRows_det h₁ h₂

theorem ApplyRowsIdempotent : Properties.ApplyRowsIdempotent :=
  fun _ _ _ _ hd h => applyRows_idem hd h

theorem UnmovedProxiesFrame : Properties.UnmovedProxiesFrame :=
  fun _ _ _ _ h => applyRows_frame h

theorem ApplyRowsPostcondition : Properties.ApplyRowsPostcondition :=
  fun _ _ _ _ hd hf h r hr => applyRows_target h hd r hr (hf r hr)

theorem AppliedGatePasses : Properties.AppliedGatePasses := by
  intro C I J K rows hv hf h hframe r hr
  exact (hframe r hr).trans (applyRows_target h hv.distinctProxies r hr (hf r hr))

theorem OrderIndependent : Properties.OrderIndependent := by
  intro C I J K rows rows' hperm hd h h'
  have hsymm : ∀ {a b : Row}, a.proxy ≠ b.proxy → b.proxy ≠ a.proxy := fun h => Ne.symm h
  have hd' : rows'.Pairwise (fun a b => a.proxy ≠ b.proxy) :=
    (hperm.pairwise_iff hsymm).mp hd
  funext p
  by_cases hex : ∃ r ∈ rows, r.proxy = p ∧ ¬ LeftToAdministrator C r
  · obtain ⟨r, hr, rfl, hf⟩ := hex
    rw [applyRows_target h hd r hr hf,
        applyRows_target h' hd' r (hperm.mem_iff.mp hr) hf]
  · push_neg at hex
    have hall : ∀ r ∈ rows, r.proxy = p → LeftToAdministrator C r := by
      intro r hr hq
      by_contra hc
      exact hc (hex r hr hq)
    rw [applyRows_frame h p hall,
        applyRows_frame h' p (fun r hr => hall r (hperm.mem_iff.mpr hr))]

theorem DuplicateRowsBreakPostcondition :
    Properties.DuplicateRowsBreakPostcondition :=
  ⟨by intro r hr; rcases List.mem_cons.mp hr with rfl | hr'
      · exact cm_owned _ rfl
      · rcases List.mem_cons.mp hr' with rfl | hr''
        · exact cm_owned _ rfl
        · exact absurd hr'' (List.not_mem_nil _),
   cm_run, cm_gate_fails⟩

theorem DuplicateRowsBreakOrder : Properties.DuplicateRowsBreakOrder :=
  ⟨cm_run, cm_reverse_reverts⟩

theorem DuplicateRowsBreakIdempotence : Properties.DuplicateRowsBreakIdempotence :=
  ⟨cm_run, cm_replay_reverts⟩

theorem ForeignRowLeavesGateOpen : Properties.ForeignRowLeavesGateOpen :=
  ⟨⟨by intro r hr
       rcases List.mem_cons.mp hr with rfl | hr'
       · exact ⟨by decide, by decide, by decide⟩
       · exact absurd hr' (List.not_mem_nil _),
     by simp⟩,
   fgn_left, fgn_run, fgn_gate_fails⟩

theorem ToRowsKeepsActiveSlots : Properties.ToRowsKeepsActiveSlots :=
  fun slots _ => ⟨mem_toRows, toRows_sublist slots⟩

theorem InertSlotNeverUpgraded : Properties.InertSlotNeverUpgraded := by
  intro C I J slots s _ _ hother h
  refine applyRows_frame h s.proxy ?_
  intro t ht hq
  exact absurd (hother t (mem_toRows.mp ht).1 hq) (mem_toRows.mp ht).2

end Contracts.ProxyUpgrade
