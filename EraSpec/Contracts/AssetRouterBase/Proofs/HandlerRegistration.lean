import EraSpec.Contracts.AssetRouterBase.Properties.HandlerRegistration

/-!
# Proofs: the asset router's routing table

Everything here is one observation and one case split: the written key is
`enc thisChain (senderOf …) d`, so injectivity separates it from any id hashed
from a different sender, and the frame lemma does the rest.
-/

namespace Contracts.AssetRouter

@[simp] lemma upd_same (f : AssetId → Address) (a : AssetId) (v : Address) : upd f a v a = v := by
  simp [upd]

lemma upd_ne (f : AssetId → Address) {x a : AssetId} (v : Address) (h : x ≠ a) :
    upd f a v x = f x := by simp [upd, h]

@[simp] lemma senderOf_ne {ntv ntvAddr caller : Address} (h : caller ≠ ntv) :
    senderOf ntv ntvAddr caller = caller := by simp [senderOf, h]

@[simp] lemma senderOf_self (ntv ntvAddr : Address) : senderOf ntv ntvAddr ntv = ntvAddr := by
  simp [senderOf]

theorem handler_frame (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R : Router)
    (caller : Address) (d : AssetData) (h : Address) (a : AssetId)
    (hne : a ≠ writtenId enc thisChain ntv ntvAddr caller d) :
    (setHandler enc thisChain ntv ntvAddr R caller d h).handler a = R.handler a := by
  simp only [setHandler]
  exact upd_ne _ _ hne

theorem no_hijack {enc : AssetIdOf} (he : IdAssumptions enc) {thisChain : Chain}
    {ntv ntvAddr : Address} (R : Router) {caller : Address} (d : AssetData) (h : Address)
    (hcaller : caller ≠ ntv) (s : Address) (d' : AssetData) (hs : s ≠ caller) :
    (setHandler enc thisChain ntv ntvAddr R caller d h).handler (enc thisChain s d')
      = R.handler (enc thisChain s d') := by
  refine handler_frame enc thisChain ntv ntvAddr R caller d h _ ?_
  intro heq
  simp only [writtenId, senderOf_ne hcaller] at heq
  exact hs (he.inj _ _ _ _ _ _ heq).2.1

theorem ntv_touches_only_its_own_ids {enc : AssetIdOf} (he : IdAssumptions enc)
    {thisChain : Chain} {ntv ntvAddr : Address} (R : Router) (d : AssetData) (h : Address)
    (s : Address) (d' : AssetData) (hs : s ≠ ntvAddr) :
    (setHandler enc thisChain ntv ntvAddr R ntv d h).handler (enc thisChain s d')
      = R.handler (enc thisChain s d') := by
  refine handler_frame enc thisChain ntv ntvAddr R ntv d h _ ?_
  intro heq
  simp only [writtenId, senderOf_self] at heq
  exact hs (he.inj _ _ _ _ _ _ heq).2.1

theorem only_tracker_or_ntv_writes {enc : AssetIdOf} {thisChain : Chain}
    {ntv ntvAddr : Address} {R : Router} {caller : Address} {d : AssetData} {h : Address}
    (hg : SetGuard enc thisChain ntv ntvAddr R caller d) (a : AssetId)
    (hchg : (setHandler enc thisChain ntv ntvAddr R caller d h).handler a ≠ R.handler a) :
    caller = ntv ∨ caller = R.tracker a := by
  by_cases heq : a = writtenId enc thisChain ntv ntvAddr caller d
  · subst heq; exact hg.authorized
  · exact absurd (handler_frame enc thisChain ntv ntvAddr R caller d h a heq) hchg

theorem tracker_records_caller (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address)
    (R : Router) (caller : Address) (d : AssetData) (h : Address) :
    (setHandler enc thisChain ntv ntvAddr R caller d h).tracker
      (writtenId enc thisChain ntv ntvAddr caller d) = caller := by
  simp only [setHandler]
  exact upd_same _ _ _

theorem fresh_id_needs_ntv {enc : AssetIdOf} {thisChain : Chain} {ntv ntvAddr : Address}
    {R : Router} {caller : Address} {d : AssetData} (hcaller : caller ≠ ntv)
    (hfresh : R.tracker (writtenId enc thisChain ntv ntvAddr caller d) = 0) :
    ¬ SetGuard enc thisChain ntv ntvAddr R caller d := by
  intro hg
  rcases hg.authorized with h | h
  · exact hcaller h
  · exact hg.callerNonzero (by rw [h, hfresh])

theorem empty_valid : Valid empty := fun _ h => absurd rfl h

theorem step_preserves_valid {enc : AssetIdOf} {thisChain : Chain} {ntv ntvAddr : Address}
    {R S : Router} (hs : Step enc thisChain ntv ntvAddr R S) (hV : Valid R) : Valid S := by
  cases hs with
  | @setHandler caller d h hg =>
    intro a hnz
    by_cases heq : a = writtenId enc thisChain ntv ntvAddr caller d
    · subst heq
      rw [tracker_records_caller]
      exact hg.callerNonzero
    · rw [show (setHandler enc thisChain ntv ntvAddr R caller d h).tracker a = R.tracker a from
        by simp only [setHandler]; exact upd_ne _ _ heq]
      refine hV a ?_
      rwa [handler_frame enc thisChain ntv ntvAddr R caller d h a heq] at hnz

theorem run_valid {enc : AssetIdOf} {thisChain : Chain} {ntv ntvAddr : Address} {R : Router}
    (hr : Reach enc thisChain ntv ntvAddr empty R) : Valid R := by
  induction hr with
  | refl => exact empty_valid
  | tail _ hs ih => exact step_preserves_valid hs ih

/-! ## Repaired forms: only the two triples compared -/

/-- Injectivity on a two-element set is just the two ids differing. -/
theorem idInjOn_pair {enc : AssetIdOf} {p q : Chain × Address × AssetData}
    (hne : enc p.1 p.2.1 p.2.2 ≠ enc q.1 q.2.1 q.2.2) : IdInjOn enc {p, q} := by
  intro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · exact absurd hxy hne
  · exact absurd hxy.symm hne
  · rfl

theorem idInjOn_of_global {enc : AssetIdOf} (he : IdAssumptions enc)
    (S : Set (Chain × Address × AssetData)) : IdInjOn enc S := by
  rintro ⟨c₁, s₁, d₁⟩ _ ⟨c₂, s₂, d₂⟩ _ h
  obtain ⟨h1, h2, h3⟩ := he.inj _ _ _ _ _ _ h
  subst h1; subst h2; subst h3; rfl

/-- **A FINITE SET ADMITS AN INJECTIVE ENCODING.**  Number its elements. -/
theorem idInjOn_of_card (S : Finset (Chain × Address × AssetData))
    (hS : S.card ≤ UInt256.size) : ∃ enc : AssetIdOf, IdInjOn enc ↑S := by
  classical
  let f := S.equivFin
  refine ⟨fun c s d => if h : (c, s, d) ∈ S then
      ⟨(f ⟨(c, s, d), h⟩).val, by have := (f ⟨(c, s, d), h⟩).isLt; omega⟩ else 0, ?_⟩
  rintro ⟨c₁, s₁, d₁⟩ h₁ ⟨c₂, s₂, d₂⟩ h₂ heq
  rw [Finset.mem_coe] at h₁ h₂
  simp only [dif_pos h₁, dif_pos h₂, Fin.mk.injEq] at heq
  have hf : f ⟨(c₁, s₁, d₁), h₁⟩ = f ⟨(c₂, s₂, d₂), h₂⟩ := Fin.ext heq
  exact congrArg Subtype.val (f.injective hf)

theorem no_hijack_or_collision (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address)
    (R : Router) {caller : Address} (d : AssetData) (h : Address) (hcaller : caller ≠ ntv)
    (s : Address) (d' : AssetData) :
    (setHandler enc thisChain ntv ntvAddr R caller d h).handler (enc thisChain s d')
      = R.handler (enc thisChain s d')
    ∨ enc thisChain s d' = enc thisChain caller d := by
  by_cases heq : enc thisChain s d' = enc thisChain caller d
  · exact Or.inr heq
  · refine Or.inl (handler_frame enc thisChain ntv ntvAddr R caller d h _ ?_)
    simp only [writtenId, senderOf_ne hcaller]
    exact heq

theorem no_hijack_on {enc : AssetIdOf} {thisChain : Chain} {ntv ntvAddr : Address}
    (R : Router) {caller : Address} (d : AssetData) (h : Address) (hcaller : caller ≠ ntv)
    (s : Address) (d' : AssetData) (hs : s ≠ caller)
    (hinj : IdInjOn enc {(thisChain, caller, d), (thisChain, s, d')}) :
    (setHandler enc thisChain ntv ntvAddr R caller d h).handler (enc thisChain s d')
      = R.handler (enc thisChain s d') := by
  refine (no_hijack_or_collision enc thisChain ntv ntvAddr R d h hcaller s d').resolve_right ?_
  intro heq
  have := hinj _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)) _ (Set.mem_insert _ _) heq
  exact hs (congrArg (fun p => p.2.1) this)

theorem ntv_touches_only_its_own_ids_or_collision (enc : AssetIdOf) (thisChain : Chain)
    (ntv ntvAddr : Address) (R : Router) (d : AssetData) (h : Address)
    (s : Address) (d' : AssetData) :
    (setHandler enc thisChain ntv ntvAddr R ntv d h).handler (enc thisChain s d')
      = R.handler (enc thisChain s d')
    ∨ enc thisChain s d' = enc thisChain ntvAddr d := by
  by_cases heq : enc thisChain s d' = enc thisChain ntvAddr d
  · exact Or.inr heq
  · refine Or.inl (handler_frame enc thisChain ntv ntvAddr R ntv d h _ ?_)
    simp only [writtenId, senderOf_self]
    exact heq

theorem ntv_touches_only_its_own_ids_on {enc : AssetIdOf} {thisChain : Chain}
    {ntv ntvAddr : Address} (R : Router) (d : AssetData) (h : Address)
    (s : Address) (d' : AssetData) (hs : s ≠ ntvAddr)
    (hinj : IdInjOn enc {(thisChain, ntvAddr, d), (thisChain, s, d')}) :
    (setHandler enc thisChain ntv ntvAddr R ntv d h).handler (enc thisChain s d')
      = R.handler (enc thisChain s d') := by
  refine (ntv_touches_only_its_own_ids_or_collision enc thisChain ntv ntvAddr R d h s d').resolve_right ?_
  intro heq
  have := hinj _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)) _ (Set.mem_insert _ _) heq
  exact hs (congrArg (fun p => p.2.1) this)

/-! ### Concrete instances -/

/-- The honest instance: the id is the sender.  Injective on any set of triples
with distinct senders. -/
def honestEnc : AssetIdOf := fun _ s _ => s

/-- A colliding instance: every triple gets id `1`. -/
def constEnc : AssetIdOf := fun _ _ _ => 1

/-- A router in which address `1` is the recorded tracker of every id, so its
calls pass the guard. -/
def trackerOne : Router := ⟨fun _ => 0, fun _ => 1⟩

lemma trackerOne_guard (enc : AssetIdOf) :
    SetGuard enc 1 9 8 trackerOne 1 0 := ⟨Or.inr rfl, by decide⟩

lemma ntv_guard (enc : AssetIdOf) (R : Router) :
    SetGuard enc 1 9 8 R 9 0 := ⟨Or.inl rfl, by decide⟩

theorem no_hijack_on_satisfiable :
    ∃ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R : Router)
      (caller : Address) (d : AssetData) (s : Address) (d' : AssetData),
      SetGuard enc thisChain ntv ntvAddr R caller d ∧ caller ≠ ntv ∧ s ≠ caller
      ∧ IdInjOn enc {(thisChain, caller, d), (thisChain, s, d')} :=
  ⟨honestEnc, 1, 9, 8, trackerOne, 1, 0, 2, 0, trackerOne_guard _, by decide, by decide,
    idInjOn_pair (by decide)⟩

theorem ntv_on_satisfiable :
    ∃ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R : Router)
      (d : AssetData) (s : Address) (d' : AssetData),
      SetGuard enc thisChain ntv ntvAddr R ntv d ∧ s ≠ ntvAddr
      ∧ IdInjOn enc {(thisChain, ntvAddr, d), (thisChain, s, d')} :=
  ⟨honestEnc, 1, 9, 8, empty, 0, 2, 0, ntv_guard _ _, by decide, idInjOn_pair (by decide)⟩

theorem no_hijack_collision_not_tautology :
    ∃ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R : Router)
      (caller : Address) (d : AssetData) (s : Address) (d' : AssetData),
      SetGuard enc thisChain ntv ntvAddr R caller d ∧ caller ≠ ntv ∧ s ≠ caller
      ∧ ¬ (enc thisChain s d' = enc thisChain caller d) :=
  ⟨honestEnc, 1, 9, 8, trackerOne, 1, 0, 2, 0, trackerOne_guard _, by decide, by decide,
    by decide⟩

theorem ntv_collision_not_tautology :
    ∃ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R : Router)
      (d : AssetData) (s : Address) (d' : AssetData),
      SetGuard enc thisChain ntv ntvAddr R ntv d ∧ s ≠ ntvAddr
      ∧ ¬ (enc thisChain s d' = enc thisChain ntvAddr d) :=
  ⟨honestEnc, 1, 9, 8, empty, 0, 2, 0, ntv_guard _ _, by decide, by decide⟩

theorem hijack_under_collision :
    ∃ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R : Router)
      (caller : Address) (d : AssetData) (h : Address) (s : Address) (d' : AssetData),
      SetGuard enc thisChain ntv ntvAddr R caller d ∧ caller ≠ ntv ∧ s ≠ caller
      ∧ (setHandler enc thisChain ntv ntvAddr R caller d h).handler (enc thisChain s d')
          ≠ R.handler (enc thisChain s d') := by
  refine ⟨constEnc, 1, 9, 8, trackerOne, 1, 0, 5, 2, 0, trackerOne_guard _, by decide,
    by decide, ?_⟩
  show (if (1 : AssetId) = 1 then (5 : Address) else 0) ≠ (0 : Address)
  rw [if_pos rfl]
  decide

end Contracts.AssetRouter

/-! ## Certificates -/

namespace Contracts.AssetRouter

theorem HandlerFrame : Properties.HandlerFrame := handler_frame
theorem NoHijack : Properties.NoHijack :=
  fun _ he _ _ _ R _ d h hc s d' hs => no_hijack he R d h hc s d' hs
theorem NtvTouchesOnlyItsOwnIds : Properties.NtvTouchesOnlyItsOwnIds :=
  fun _ he _ _ _ R d h s d' hs => ntv_touches_only_its_own_ids he R d h s d' hs
theorem OnlyTrackerOrNtvWrites : Properties.OnlyTrackerOrNtvWrites :=
  fun _ _ _ _ _ _ _ _ hg a hchg => only_tracker_or_ntv_writes hg a hchg
theorem TrackerRecordsCaller : Properties.TrackerRecordsCaller :=
  tracker_records_caller
theorem FreshIdNeedsNtv : Properties.FreshIdNeedsNtv :=
  fun _ _ _ _ _ _ _ hc hf => fresh_id_needs_ntv hc hf
theorem EmptyValid : Properties.EmptyValid := empty_valid
theorem RunValid : Properties.RunValid := fun _ _ _ _ _ hr => run_valid hr


/-- Pigeonhole: no map `UInt256 → UInt256 → UInt256` is injective on pairs. -/
theorem not_pair_inj (f : UInt256 → UInt256 → UInt256)
    (hinj : ∀ a b c d : UInt256, f a b = f c d → a = c ∧ b = d) : False := by
  have hf : Function.Injective (fun p : UInt256 × UInt256 => f p.1 p.2) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ he
    obtain ⟨rfl, rfl⟩ := hinj a b c d he
    rfl
  have hc := Fintype.card_le_of_injective _ hf
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  have hpos : 1 < UInt256.size := by decide
  nlinarith

theorem IdAssumptionsUnsatisfiable : Properties.IdAssumptionsUnsatisfiable := by
  intro enc hA
  obtain ⟨d⟩ : Nonempty AssetData := inferInstance
  exact not_pair_inj (fun c s => enc c s d) fun c₁ s₁ c₂ s₂ he =>
    let h := hA.inj c₁ s₁ d c₂ s₂ d he; ⟨h.1, h.2.1⟩

/-! ### Repaired forms -/

theorem NoHijackOrCollision : Properties.NoHijackOrCollision :=
  fun enc c ntv ntvAddr R _ d h hc s d' _ => no_hijack_or_collision enc c ntv ntvAddr R d h hc s d'
theorem NoHijackOn : Properties.NoHijackOn :=
  fun _ _ _ _ R _ d h hc s d' hs hinj => no_hijack_on R d h hc s d' hs hinj
theorem NtvTouchesOnlyItsOwnIdsOrCollision : Properties.NtvTouchesOnlyItsOwnIdsOrCollision :=
  fun enc c ntv ntvAddr R d h s d' _ =>
    ntv_touches_only_its_own_ids_or_collision enc c ntv ntvAddr R d h s d'
theorem NtvTouchesOnlyItsOwnIdsOn : Properties.NtvTouchesOnlyItsOwnIdsOn :=
  fun _ _ _ _ R d h s d' hs hinj => ntv_touches_only_its_own_ids_on R d h s d' hs hinj
theorem IdInjOnSatisfiable : Properties.IdInjOnSatisfiable := idInjOn_of_card
theorem NoHijackOnSatisfiable : Properties.NoHijackOnSatisfiable := no_hijack_on_satisfiable
theorem NtvTouchesOnlyItsOwnIdsOnSatisfiable :
    Properties.NtvTouchesOnlyItsOwnIdsOnSatisfiable := ntv_on_satisfiable
theorem NoHijackCollisionNotTautology : Properties.NoHijackCollisionNotTautology :=
  no_hijack_collision_not_tautology
theorem NtvCollisionNotTautology : Properties.NtvCollisionNotTautology :=
  ntv_collision_not_tautology
theorem HijackUnderCollision : Properties.HijackUnderCollision := hijack_under_collision

end Contracts.AssetRouter
