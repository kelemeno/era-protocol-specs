import EraSpec.Contracts.ProxyUpgradeRowLib.Properties.RowsCurrentStrong
import EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsCurrent

/-!
# Proofs: when the `e561b9cc2` rows apply, and in which orders

A local swap is a point update of the row's proxy by a fixed implementation. So, on distinct
proxies:

* every other row leaves a row's proxy alone (`rowsCurrentStrong_loop_frame`);
* each row finds its proxy where the call started, and either skips or upgrades it to what its
  swap leaves (`rowsCurrentStrong_loop_rows`).

Together with the verification pass, these give `ApplyRowsEnabledIff`, one direction by
induction over the loop and the other by building it. Its right-hand side does not mention
the order, so `OrderIndependentExecutability` follows. The two final states agree on the
rows' proxies by the verification pass, and elsewhere by the frame.

The countermodel and the witness are computations.
-/

namespace Contracts.ProxyUpgradeCurrent

/-! ## Local swaps -/

lemma rowsCurrentStrong_swap_frame {C : Config} {r : Row} (h : LocalSwap C r) (I : Impl)
    {q : Address} (hq : q ≠ r.proxy) : swap C r I q = I q := by
  obtain ⟨c, hc⟩ := h
  rw [hc I]
  exact upd_ne _ _ hq

/-- What a local swap leaves at its own proxy does not depend on the mapping. -/
lemma rowsCurrentStrong_swap_own {C : Config} {r : Row} (h : LocalSwap C r) (I I' : Impl) :
    swap C r I r.proxy = swap C r I' r.proxy := by
  obtain ⟨c, hc⟩ := h
  rw [hc I, hc I', upd_same, upd_same]

lemma rowsCurrentStrong_localSwap_of_inert {C : Config} {r : Row} (h : RowInert C r) :
    LocalSwap C r :=
  ⟨r.implNew, fun I => swap_inert h I⟩

/-! ## One row, and the loop -/

lemma rowsCurrentStrong_row_frame {C : Config} {I J : Impl} {r : Row} (hl : LocalSwap C r)
    (h : ApplyRow C I r J) : ∀ q, q ≠ r.proxy → J q = I q := by
  intro q hq
  cases h with
  | alreadyAtTarget _ => rfl
  | upgrade _ _ _ => exact rowsCurrentStrong_swap_frame hl I hq

/-- Rows with local swaps move only the proxies they name. -/
lemma rowsCurrentStrong_loop_frame {C : Config} {I J : Impl} {rows : List Row}
    (h : ApplyLoop C I rows J) : (∀ r ∈ rows, LocalSwap C r) →
    ∀ p, (∀ r ∈ rows, r.proxy ≠ p) → J p = I p := by
  induction h with
  | nil => intro _ _ _; rfl
  | @cons I J K r rs hstep _ ih =>
      intro hl p hp
      rw [ih (fun t ht => hl t (List.mem_cons_of_mem _ ht)) p
        (fun t ht => hp t (List.mem_cons_of_mem _ ht))]
      exact rowsCurrentStrong_row_frame (hl r List.mem_cons_self) hstep p
        (fun hq => hp r List.mem_cons_self hq.symm)

/-- On distinct proxies with local swaps, each row either found its proxy at its target and
left it there, or upgraded it from its source to what its swap leaves, measured against the
state the loop started from. -/
lemma rowsCurrentStrong_loop_rows {C : Config} {I J : Impl} {rows : List Row}
    (h : ApplyLoop C I rows J) : rows.Pairwise (fun a b => a.proxy ≠ b.proxy) →
    (∀ r ∈ rows, LocalSwap C r) →
    ∀ r ∈ rows, (I r.proxy = r.implNew ∧ J r.proxy = I r.proxy) ∨
      (C.adminOwner = C.self ∧ I r.proxy = r.expectedOldImpl ∧
        J r.proxy = swap C r I r.proxy) := by
  induction h with
  | nil => intro _ _ r hr; exact absurd hr List.not_mem_nil
  | @cons I J K r rs hstep hrest ih =>
      intro hd hl t ht
      have hrs : ∀ u ∈ rs, u.proxy ≠ r.proxy := fun u hu hq =>
        (List.pairwise_cons.mp hd).1 u hu hq.symm
      have hlrs : ∀ u ∈ rs, LocalSwap C u := fun u hu => hl u (List.mem_cons_of_mem _ hu)
      rcases List.mem_cons.mp ht with rfl | ht'
      · have hK : K t.proxy = J t.proxy := rowsCurrentStrong_loop_frame hrest hlrs t.proxy hrs
        cases hstep with
        | alreadyAtTarget he => exact Or.inl ⟨he, hK⟩
        | upgrade ho _ hs => exact Or.inr ⟨ho, hs, hK⟩
      · have hJt : J t.proxy = I t.proxy :=
          rowsCurrentStrong_row_frame (hl r List.mem_cons_self) hstep t.proxy (hrs t ht')
        rcases ih (List.pairwise_cons.mp hd).2 hlrs t ht' with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
        · exact Or.inl ⟨hJt ▸ h1, h2.trans hJt⟩
        · exact Or.inr ⟨h1, hJt ▸ h2,
            h3.trans (rowsCurrentStrong_swap_own (hlrs t ht') J I)⟩

/-- A successful call on distinct proxies with local swaps: every row applies on its own from
where the call started. -/
lemma rowsCurrentStrong_applies_of_run {C : Config} {I J : Impl} {rows : List Row}
    (h : ApplyRows C I rows J) (hd : rows.Pairwise (fun a b => a.proxy ≠ b.proxy))
    (hl : ∀ r ∈ rows, LocalSwap C r) : ∀ r ∈ rows, RowApplies C I r := by
  intro r hr
  rcases rowsCurrentStrong_loop_rows h.loop hd hl r hr with ⟨h1, _⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h1, h2, h3.symm.trans (h.verified r hr)⟩

/-- Rows on distinct proxies with local swaps, each applying on its own from `I`, make a loop
from `I` whose final state passes the verification. -/
lemma rowsCurrentStrong_loop_of_applies {C : Config} :
    ∀ {I : Impl} {rows : List Row}, rows.Pairwise (fun a b => a.proxy ≠ b.proxy) →
      (∀ r ∈ rows, LocalSwap C r) → (∀ r ∈ rows, RowApplies C I r) →
      ∃ J, ApplyLoop C I rows J ∧ RowsApplied J rows := by
  intro I rows
  induction rows generalizing I with
  | nil => intro _ _ _; exact ⟨I, ApplyLoop.nil, fun r hr => absurd hr List.not_mem_nil⟩
  | cons r rs ih =>
      intro hd hl ha
      have hrs : ∀ u ∈ rs, u.proxy ≠ r.proxy := fun u hu hq =>
        (List.pairwise_cons.mp hd).1 u hu hq.symm
      have hlr : LocalSwap C r := hl r List.mem_cons_self
      have hlrs : ∀ u ∈ rs, LocalSwap C u := fun u hu => hl u (List.mem_cons_of_mem _ hu)
      obtain ⟨J₀, h₀, hJ₀⟩ : ∃ J₀, ApplyRow C I r J₀ ∧ J₀ r.proxy = r.implNew := by
        rcases ha r List.mem_cons_self with he | ⟨ho, hs, hsw⟩
        · exact ⟨I, ApplyRow.alreadyAtTarget he, he⟩
        · by_cases he : I r.proxy = r.implNew
          · exact ⟨I, ApplyRow.alreadyAtTarget he, he⟩
          · exact ⟨_, ApplyRow.upgrade ho he hs, hsw⟩
      have hframe : ∀ u ∈ rs, J₀ u.proxy = I u.proxy := fun u hu =>
        rowsCurrentStrong_row_frame hlr h₀ u.proxy (hrs u hu)
      obtain ⟨K, hK, hKa⟩ := ih (List.pairwise_cons.mp hd).2 hlrs (fun u hu => by
        rcases ha u (List.mem_cons_of_mem _ hu) with he | ⟨ho, hs, hsw⟩
        · exact Or.inl ((hframe u hu).trans he)
        · exact Or.inr ⟨ho, (hframe u hu).trans hs,
            (rowsCurrentStrong_swap_own (hlrs u hu) J₀ I).trans hsw⟩)
      refine ⟨K, ApplyLoop.cons h₀ hK, fun t ht => ?_⟩
      rcases List.mem_cons.mp ht with rfl | ht'
      · rw [rowsCurrentStrong_loop_frame hK hlrs t.proxy hrs]
        exact hJ₀
      · exact hKa t ht'

end Contracts.ProxyUpgradeCurrent

/-! ## Certificates -/

namespace Contracts.ProxyUpgradeCurrent

theorem LocalSwapOfInert : Properties.LocalSwapOfInert :=
  fun _ _ h => rowsCurrentStrong_localSwap_of_inert h

theorem LocalSwapOfOwnProxyReinit : Properties.LocalSwapOfOwnProxyReinit := by
  intro C r hframe hreads
  cases hcall : r.callInitializeUpgrade
  · refine ⟨r.implNew, fun I => ?_⟩
    simp [swap, hcall]
  · refine ⟨C.reinit r (upd (fun _ => 0) r.proxy r.implNew) r.proxy, fun I => ?_⟩
    funext q
    simp only [swap, hcall, ↓reduceIte]
    by_cases hq : q = r.proxy
    · subst hq
      rw [upd_same]
      exact hreads _ _ (by rw [upd_same, upd_same])
    · rw [hframe _ q hq, upd_ne _ _ hq, upd_ne _ _ hq]

theorem ApplyRowsEnabledIff : Properties.ApplyRowsEnabledIff := by
  intro C I rows hd hl
  constructor
  · rintro ⟨J, h⟩
    exact ⟨h.code, rowsCurrentStrong_applies_of_run h hd hl⟩
  · rintro ⟨hc, ha⟩
    obtain ⟨J, hJ, hv⟩ := rowsCurrentStrong_loop_of_applies hd hl ha
    exact ⟨J, hc, hJ, hv⟩

theorem OrderIndependentExecutability : Properties.OrderIndependentExecutability := by
  intro C I J rows rows' hperm hd hl h
  have hsymm : ∀ {a b : Row}, a.proxy ≠ b.proxy → b.proxy ≠ a.proxy := fun h => Ne.symm h
  have hd' : rows'.Pairwise (fun a b => a.proxy ≠ b.proxy) := (hperm.pairwise_iff hsymm).mp hd
  have hl' : ∀ r ∈ rows', LocalSwap C r := fun r hr => hl r (hperm.mem_iff.mpr hr)
  obtain ⟨K, hK⟩ := (ApplyRowsEnabledIff C I rows' hd' hl').mpr
    ⟨fun r hr => h.code r (hperm.mem_iff.mpr hr),
      fun r hr => rowsCurrentStrong_applies_of_run h hd hl r (hperm.mem_iff.mpr hr)⟩
  have hJK : J = K := by
    funext p
    by_cases hp : ∃ r ∈ rows, r.proxy = p
    · obtain ⟨r, hr, rfl⟩ := hp
      rw [h.verified r hr, hK.verified r (hperm.mem_iff.mp hr)]
    · have hall : ∀ r ∈ rows, r.proxy ≠ p := fun r hr hq => hp ⟨r, hr, hq⟩
      rw [rowsCurrentStrong_loop_frame h.loop hl p hall,
        rowsCurrentStrong_loop_frame hK.loop hl' p (fun r hr => hall r (hperm.mem_iff.mpr hr))]
  rw [hJK]
  exact hK

theorem OrderIndependentExecutabilityInert : Properties.OrderIndependentExecutabilityInert :=
  fun C I J rows rows' hperm hd hi h =>
    OrderIndependentExecutability C I J rows rows' hperm hd
      (fun r hr => rowsCurrentStrong_localSwap_of_inert (hi r hr)) h

end Contracts.ProxyUpgradeCurrent

/-! ## The countermodel and the witness -/

namespace Contracts.ProxyUpgradeCurrent

lemma rowsCurrentStrong_readsOther_frames : ReinitFrames wReadsOther := by
  intro r I q hq
  show (if r = rowB then upd I 6 (if I 5 = 11 then 12 else 10) else I) q = I q
  by_cases h : r = rowB
  · rw [ite_eq_left h]
    subst h
    exact upd_ne _ _ hq
  · rw [ite_eq_right h]

theorem ValidRowsOrderDecidesExecutability : Properties.ValidRowsOrderDecidesExecutability := by
  have hloop : ApplyLoop wReadsOther wImpl [rowB, rowA]
      (swap wReadsOther rowA (swap wReadsOther rowB wImpl)) :=
    ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide))
      (ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide)) ApplyLoop.nil)
  refine ⟨rowsCurrentStrong_readsOther_frames, valid_AB, ?_, ⟨_, code_all wReadsOther
    (fun _ => trivial) _, ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide))
      (ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide)) ApplyLoop.nil), ?_⟩,
    ⟨_, hloop⟩, ?_⟩
  · rintro ⟨c, hc⟩
    have h₁ : swap wReadsOther rowB wImpl rowB.proxy = c := by rw [hc wImpl, upd_same]
    have h₂ : swap wReadsOther rowB (upd wImpl 5 11) rowB.proxy = c := by
      rw [hc (upd wImpl 5 11), upd_same]
    have e₁ : swap wReadsOther rowB wImpl rowB.proxy = 10 := by decide
    have e₂ : swap wReadsOther rowB (upd wImpl 5 11) rowB.proxy = 12 := by decide
    rw [e₁] at h₁
    rw [e₂] at h₂
    exact absurd (h₁.trans h₂.symm) (by decide)
  · intro r hr
    rcases mem_AB hr with rfl | rfl <;> decide
  · rintro ⟨J, h⟩
    have h6 := h.verified rowB (by simp)
    rw [applyLoop_det h.loop hloop] at h6
    exact absurd h6 (by decide)

lemma rowsCurrentStrong_localReinit_frames :
    ∀ (I : Impl) (q : Address), q ≠ rowB.proxy → wLocalReinit.reinit rowB I q = I q := by
  intro I q hq
  show (if rowB = rowB then upd I 6 12 else I) q = I q
  rw [ite_eq_left rfl]
  exact upd_ne _ _ hq

lemma rowsCurrentStrong_localReinit_reads :
    ∀ I I' : Impl, I rowB.proxy = I' rowB.proxy →
      wLocalReinit.reinit rowB I rowB.proxy = wLocalReinit.reinit rowB I' rowB.proxy := by
  intro I I' _
  show (if rowB = rowB then upd I 6 12 else I) 6 = (if rowB = rowB then upd I' 6 12 else I') 6
  rw [ite_eq_left rfl, ite_eq_left rfl, upd_same, upd_same]

theorem RowsCurrentStrongWitness : Properties.RowsCurrentStrongWitness := by
  have hlocB : LocalSwap wLocalReinit rowB :=
    LocalSwapOfOwnProxyReinit wLocalReinit rowB rowsCurrentStrong_localReinit_frames
      rowsCurrentStrong_localReinit_reads
  have hlocA : LocalSwap wLocalReinit rowA :=
    rowsCurrentStrong_localSwap_of_inert (Or.inl rfl)
  have hloc : ∀ r ∈ [rowA, rowB], LocalSwap wLocalReinit r := by
    intro r hr
    rcases mem_AB hr with rfl | rfl
    · exact hlocA
    · exact hlocB
  have hJ : ApplyRows wLocalReinit wImpl [rowA, rowB]
      (swap wLocalReinit rowB (swap wLocalReinit rowA wImpl)) := by
    refine ⟨code_all wLocalReinit (fun _ => trivial) _,
      ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide))
        (ApplyLoop.cons (ApplyRow.upgrade rfl (by decide) (by decide)) ApplyLoop.nil), ?_⟩
    intro r hr
    rcases mem_AB hr with rfl | rfl <;> decide
  have hK := OrderIndependentExecutability wLocalReinit wImpl _ [rowA, rowB] [rowB, rowA]
    (List.Perm.swap _ _ _) valid_AB.distinctProxies hloc hJ
  have hSelf : LocalSwap wSelfMoving rowB :=
    LocalSwapOfOwnProxyReinit wSelfMoving rowB
      (fun I q hq => by
        show (if rowB = rowB then upd I 6 10 else I) q = I q
        rw [ite_eq_left rfl]
        exact upd_ne _ _ hq)
      (fun I I' _ => by
        show (if rowB = rowB then upd I 6 10 else I) 6 = (if rowB = rowB then upd I' 6 10 else I') 6
        rw [ite_eq_left rfl, ite_eq_left rfl, upd_same, upd_same])
  refine ⟨valid_AB, ?_, rowsCurrentStrong_localReinit_frames,
    rowsCurrentStrong_localReinit_reads, hloc, code_all wLocalReinit (fun _ => trivial) _, ?_,
    ⟨_, hJ, hK, by decide, by decide⟩, ?_, ⟨_, applyRows_AB⟩, hSelf, ?_⟩
  · rintro (h | h)
    · exact absurd h (by decide)
    · exact absurd (congrFun (h wImpl) 6) (by decide)
  · intro r hr
    rcases mem_AB hr with rfl | rfl
    · exact Or.inr ⟨rfl, rfl, by decide⟩
    · exact Or.inr ⟨rfl, rfl, by decide⟩
  · intro r hr
    rcases mem_AB hr with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (fun _ => rfl)
  · rintro (h | ⟨_, _, h⟩)
    · exact absurd h (by decide)
    · exact absurd h (by decide)

end Contracts.ProxyUpgradeCurrent
