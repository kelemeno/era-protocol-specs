import EraSpec.Contracts.ProxyUpgradeRowLib.Properties.RowsStrong
import EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.Rows

/-!
# Proofs: when the `612a71ccc` rows apply, and in which orders

`RowEnabled` is read off `ApplyRow`'s constructors (`rowsStrong_step_iff`) and depends on the
mapping only at the row's proxy (`rowsStrong_enabled_congr`). On distinct proxies, a row's
proxy is untouched by every other row (`applyRow_frame`, `Proofs/Rows.lean`), so a run
succeeds iff each row is enabled at the start: one direction by induction over the run, the
other by building it.

Order independence of executability is then a corollary. The right-hand side of
`ApplyRowsEnabledIff` does not depend on the order, so a permutation of a successful run
succeeds, and `OrderIndependent` (`Proofs/Rows.lean`) says the two final states agree.
-/

namespace Contracts.ProxyUpgrade

/-! ## One row -/

/-- A loop iteration succeeds exactly when the row is enabled. -/
lemma rowsStrong_step_iff {C : Config} {I : Impl} {r : Row} :
    (∃ J, ApplyRow C I r J) ↔ RowEnabled C I r := by
  constructor
  · rintro ⟨J, h⟩
    cases h with
    | leftToAdmin hl => exact Or.inl hl
    | alreadyAtTarget _ he => exact Or.inr (Or.inl he)
    | upgrade _ ho _ hs => exact Or.inr (Or.inr ⟨ho, hs⟩)
  · rintro (hl | he | ⟨ho, hs⟩)
    · exact ⟨I, ApplyRow.leftToAdmin hl⟩
    · by_cases hl : LeftToAdministrator C r
      · exact ⟨I, ApplyRow.leftToAdmin hl⟩
      · exact ⟨I, ApplyRow.alreadyAtTarget hl he⟩
    · have hl : ¬ LeftToAdministrator C r := fun h => h.2 ho
      by_cases he : I r.proxy = r.implNew
      · exact ⟨I, ApplyRow.alreadyAtTarget hl he⟩
      · exact ⟨_, ApplyRow.upgrade hl ho he hs⟩

/-- Enabledness reads the mapping only at the row's proxy. -/
lemma rowsStrong_enabled_congr {C : Config} {I I' : Impl} {r : Row}
    (h : I' r.proxy = I r.proxy) (he : RowEnabled C I r) : RowEnabled C I' r := by
  unfold RowEnabled at he ⊢
  rw [h]
  exact he

/-! ## A run on distinct proxies -/

/-- In a successful run on distinct proxies, every row was enabled where the run started. -/
lemma rowsStrong_enabled_of_run {C : Config} {I J : Impl} {rows : List Row}
    (h : ApplyRows C I rows J) : rows.Pairwise (fun a b => a.proxy ≠ b.proxy) →
    ∀ r ∈ rows, RowEnabled C I r := by
  induction h with
  | nil => intro _ r hr; exact absurd hr List.not_mem_nil
  | @cons I J K r rs hstep _ ih =>
      intro hd t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact rowsStrong_step_iff.mp ⟨_, hstep⟩
      · have hne : t.proxy ≠ r.proxy := fun hq => (List.pairwise_cons.mp hd).1 t ht' hq.symm
        exact rowsStrong_enabled_congr (applyRow_frame hstep t.proxy hne).symm
          (ih (List.pairwise_cons.mp hd).2 t ht')

/-- On distinct proxies, rows that are all enabled where the run starts make a successful run. -/
lemma rowsStrong_run_of_enabled {C : Config} :
    ∀ {I : Impl} {rows : List Row}, rows.Pairwise (fun a b => a.proxy ≠ b.proxy) →
      (∀ r ∈ rows, RowEnabled C I r) → ∃ J, ApplyRows C I rows J := by
  intro I rows
  induction rows generalizing I with
  | nil => intro _ _; exact ⟨I, ApplyRows.nil⟩
  | cons r rs ih =>
      intro hd he
      obtain ⟨J₀, h₀⟩ := rowsStrong_step_iff.mpr (he r List.mem_cons_self)
      obtain ⟨K, hK⟩ := ih (List.pairwise_cons.mp hd).2 (fun t ht =>
        rowsStrong_enabled_congr
          (applyRow_frame h₀ t.proxy (fun hq => (List.pairwise_cons.mp hd).1 t ht hq.symm))
          (he t (List.mem_cons_of_mem _ ht)))
      exact ⟨K, ApplyRows.cons h₀ hK⟩

/-- Point updates of distinct proxies commute. -/
lemma rowsStrong_upd_comm (f : Impl) {p q : Address} (h : p ≠ q) (v w : Address) :
    upd (upd f p v) q w = upd (upd f q w) p v := by
  funext x
  by_cases hp : x = p
  · subst hp
    simp [upd, h]
  · by_cases hq : x = q
    · subst hq
      simp [upd, hp]
    · simp [upd, hp, hq]

end Contracts.ProxyUpgrade

/-! ## Certificates -/

namespace Contracts.ProxyUpgrade

theorem RowStepIffEnabled : Properties.RowStepIffEnabled :=
  fun _ _ _ => rowsStrong_step_iff

theorem ApplyRowsEnabledIff : Properties.ApplyRowsEnabledIff := by
  intro C I rows hd
  exact ⟨fun ⟨_, h⟩ => rowsStrong_enabled_of_run h hd, rowsStrong_run_of_enabled hd⟩

theorem ApplyRowsPassesGateWhenEnabled : Properties.ApplyRowsPassesGateWhenEnabled := by
  intro C I rows hd hf he
  obtain ⟨J, h⟩ := rowsStrong_run_of_enabled hd (fun r hr => by
    rcases he r hr with h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1))
  exact ⟨J, h, fun r hr => applyRows_target h hd r hr (hf r hr),
    fun p hp => applyRows_frame h p (fun r hr hq => absurd hq (hp r hr))⟩

theorem OrderIndependentExecutability : Properties.OrderIndependentExecutability := by
  intro C I J rows rows' hperm hd h
  have hsymm : ∀ {a b : Row}, a.proxy ≠ b.proxy → b.proxy ≠ a.proxy := fun h => Ne.symm h
  have hd' : rows'.Pairwise (fun a b => a.proxy ≠ b.proxy) := (hperm.pairwise_iff hsymm).mp hd
  obtain ⟨K, hK⟩ := rowsStrong_run_of_enabled hd' (fun r hr =>
    rowsStrong_enabled_of_run h hd r (hperm.mem_iff.mpr hr))
  rw [OrderIndependent C I J K rows rows' hperm hd h hK]
  exact hK

theorem RowsStrongWitness : Properties.RowsStrongWitness := by
  have hstep₆ : ApplyRow cmConfig (upd cmImpl 5 11) rowP6 pairFinal :=
    ApplyRow.upgrade (cm_owned _ rfl) rfl (by decide) (by decide)
  have hrun : ApplyRows cmConfig cmImpl [rowAB, rowP6] pairFinal :=
    ApplyRows.cons cm_step₁ (ApplyRows.cons hstep₆ ApplyRows.nil)
  have hcomm : upd (upd cmImpl 6 12) 5 11 = pairFinal :=
    rowsStrong_upd_comm cmImpl (by decide) 12 11
  have hrun' : ApplyRows cmConfig cmImpl [rowP6, rowAB] pairFinal := by
    rw [← hcomm]
    exact ApplyRows.cons (ApplyRow.upgrade (cm_owned _ rfl) rfl (by decide) (by decide))
      (ApplyRows.cons (ApplyRow.upgrade (cm_owned _ rfl) rfl (by decide) (by decide))
        ApplyRows.nil)
  have hstale : ¬ RowEnabled cmConfig cmImpl rowBC := by
    rintro (hl | he | ⟨_, hs⟩)
    · exact cm_owned _ rfl hl
    · exact absurd he (by decide)
    · exact absurd hs (by decide)
  have hd : [rowP6, rowBC].Pairwise (fun a b => a.proxy ≠ b.proxy) := by
    simp [rowP6, rowBC]
  refine ⟨⟨by simp [rowAB, rowP6], by simp [rowAB, rowP6]⟩, ?_, hrun, hrun',
    fun h => absurd (congrFun h 5) (by decide), ?_, Or.inl fgn_left, hstale, hd, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨cm_owned _ rfl, rfl, by decide, by decide⟩
    · exact ⟨cm_owned _ rfl, rfl, by decide, by decide⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  · rintro ⟨J, h⟩
    exact hstale (rowsStrong_enabled_of_run h hd rowBC (by simp))

end Contracts.ProxyUpgrade
