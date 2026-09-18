import EraSpec.Properties.AssetRouter

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

end Contracts.AssetRouter

/-! ## Certificates -/

namespace Proofs.AssetRouter

open Contracts.AssetRouter

theorem HandlerFrame : Properties.AssetRouter.HandlerFrame := handler_frame
theorem NoHijack : Properties.AssetRouter.NoHijack :=
  fun _ he _ _ _ R _ d h hc s d' hs => no_hijack he R d h hc s d' hs
theorem NtvTouchesOnlyItsOwnIds : Properties.AssetRouter.NtvTouchesOnlyItsOwnIds :=
  fun _ he _ _ _ R d h s d' hs => ntv_touches_only_its_own_ids he R d h s d' hs
theorem OnlyTrackerOrNtvWrites : Properties.AssetRouter.OnlyTrackerOrNtvWrites :=
  fun _ _ _ _ _ _ _ _ hg a hchg => only_tracker_or_ntv_writes hg a hchg
theorem TrackerRecordsCaller : Properties.AssetRouter.TrackerRecordsCaller :=
  tracker_records_caller
theorem FreshIdNeedsNtv : Properties.AssetRouter.FreshIdNeedsNtv :=
  fun _ _ _ _ _ _ _ hc hf => fresh_id_needs_ntv hc hf
theorem EmptyValid : Properties.AssetRouter.EmptyValid := empty_valid
theorem RunValid : Properties.AssetRouter.RunValid := fun _ _ _ _ _ hr => run_valid hr

end Proofs.AssetRouter
