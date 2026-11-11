import EraSpec.Contracts.AssetRouterBase.Properties.HandlerRegistrationRuns
import EraSpec.Contracts.AssetRouterBase.Proofs.HandlerRegistration

/-!
# Proofs: run-level `NoHijack`

Every bounded result reduces to one observation about a single write.  A call writes the
id `enc` of its own triple; if the hash is injective on a set holding that triple and the
watched triple `q`, the write lands on `enc q` exactly when the call's triple IS `q`.  So
along a run the route at `enc q` is touched only by the calls that hashed `q`, and the
last of them wins (`applyCalls_route`, by induction on the log from its end).  The guard
is not used for that.  It enters in the custom-route result (the writer at a custom id
must be its current tracker, so the tracker never changes), in `logged_run_keeps_vault_routes`
(a non-vault call that hashed the vault's triple would have to be the vault), and in the
hash-free vault results (the vault's tracker record turns every non-vault caller away).
The witnesses are concrete four-call runs checked by `decide`; injectivity of an encoding on
a concrete finite set is decided by comparing the set's size with its image's
(`idInjOn_iff_card_image`).
-/

namespace Contracts.AssetRouter

section Runs
variable {enc : AssetIdOf} {thisChain : Chain} {ntv ntvAddr : Address}

/-! ### Calls, logs and their triples -/

lemma mem_loggedTriples {log : List Call} {p : Chain × Address × AssetData} :
    p ∈ loggedTriples thisChain ntv ntvAddr log ↔ ∃ c ∈ log, c.triple thisChain ntv ntvAddr = p := by
  simp [loggedTriples]

lemma loggedTriples_snoc (log : List Call) (c : Call) :
    loggedTriples thisChain ntv ntvAddr (log ++ [c])
      = insert (c.triple thisChain ntv ntvAddr) (loggedTriples thisChain ntv ntvAddr log) := by
  ext p
  simp only [Finset.mem_insert, mem_loggedTriples, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨c', hc' | rfl, rfl⟩
    · exact Or.inr ⟨c', hc', rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨c', hc', rfl⟩)
    · exact ⟨c, Or.inr rfl, rfl⟩
    · exact ⟨c', Or.inl hc', rfl⟩

theorem loggedTriples_card_le (log : List Call) :
    (loggedTriples thisChain ntv ntvAddr log).card ≤ log.length := by
  unfold loggedTriples
  exact le_trans (List.toFinset_card_le _) (le_of_eq (List.length_map _))

lemma mem_loggedTriples_of_mem {log : List Call} {c : Call} (hc : c ∈ log) :
    c.triple thisChain ntv ntvAddr ∈ loggedTriples thisChain ntv ntvAddr log :=
  mem_loggedTriples.mpr ⟨c, hc, rfl⟩

lemma idInjOn_mono {S T : Set (Chain × Address × AssetData)} (h : IdInjOn enc S) (hT : T ⊆ S) :
    IdInjOn enc T :=
  fun p hp q hq he => h p (hT hp) q (hT hq) he

/-- The premise for a longer log gives it for a shorter one. -/
lemma idInjOn_insert_snoc {q : Chain × Address × AssetData} {log : List Call} {c : Call}
    (h : IdInjOn enc ↑(insert q (loggedTriples thisChain ntv ntvAddr (log ++ [c])))) :
    IdInjOn enc ↑(insert q (loggedTriples thisChain ntv ntvAddr log)) := by
  refine idInjOn_mono h ?_
  intro x hx
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx ⊢
  rcases hx with rfl | hx
  · exact Or.inl rfl
  · rw [loggedTriples_snoc]
    exact Or.inr (Finset.mem_insert_of_mem hx)

lemma mem_insert_self_coe (q : Chain × Address × AssetData) (L : Finset (Chain × Address × AssetData)) :
    q ∈ (↑(insert q L) : Set (Chain × Address × AssetData)) := by
  simp

lemma mem_insert_snoc_coe (q : Chain × Address × AssetData) (log : List Call) (c : Call) :
    c.triple thisChain ntv ntvAddr
      ∈ (↑(insert q (loggedTriples thisChain ntv ntvAddr (log ++ [c]))) : Set (Chain × Address × AssetData)) := by
  rw [loggedTriples_snoc]
  simp

/-- The id a call writes is `enc` of its triple. -/
lemma writtenId_triple (c : Call) :
    writtenId enc thisChain ntv ntvAddr c.caller c.data
      = enc (c.triple thisChain ntv ntvAddr).1 (c.triple thisChain ntv ntvAddr).2.1
          (c.triple thisChain ntv ntvAddr).2.2 := rfl

lemma lastCallOn_snoc (log : List Call) (c : Call) (q : Chain × Address × AssetData) :
    lastCallOn thisChain ntv ntvAddr (log ++ [c]) q
      = if c.triple thisChain ntv ntvAddr = q then some c
        else lastCallOn thisChain ntv ntvAddr log q := by
  unfold lastCallOn
  rw [List.filter_append, List.getLast?_append]
  by_cases h : c.triple thisChain ntv ntvAddr = q
  · simp [h]
  · simp [h]

lemma lastCallOn_nil (q : Chain × Address × AssetData) :
    lastCallOn thisChain ntv ntvAddr [] q = none := rfl

lemma loggedHandler_snoc (R₀ : Router) (log : List Call) (c : Call) (q : Chain × Address × AssetData) :
    loggedHandler enc thisChain ntv ntvAddr R₀ (log ++ [c]) q
      = if c.triple thisChain ntv ntvAddr = q then c.handler
        else loggedHandler enc thisChain ntv ntvAddr R₀ log q := by
  unfold loggedHandler
  rw [lastCallOn_snoc]
  split_ifs <;> rfl

lemma loggedTracker_snoc (R₀ : Router) (log : List Call) (c : Call) (q : Chain × Address × AssetData) :
    loggedTracker enc thisChain ntv ntvAddr R₀ (log ++ [c]) q
      = if c.triple thisChain ntv ntvAddr = q then c.caller
        else loggedTracker enc thisChain ntv ntvAddr R₀ log q := by
  unfold loggedTracker
  rw [lastCallOn_snoc]
  split_ifs <;> rfl

lemma applyCalls_nil (R₀ : Router) : applyCalls enc thisChain ntv ntvAddr R₀ [] = R₀ := rfl

lemma applyCalls_snoc (R₀ : Router) (log : List Call) (c : Call) :
    applyCalls enc thisChain ntv ntvAddr R₀ (log ++ [c])
      = setHandler enc thisChain ntv ntvAddr (applyCalls enc thisChain ntv ntvAddr R₀ log)
          c.caller c.data c.handler := by
  simp [applyCalls, List.foldl_append]

/-! ### The core: the last own write wins -/

/-- **THE LAST CALL HASHING `q` DETERMINES THE ROUTE AT `enc q`** — for any sequence of
calls, guard or no guard. -/
theorem applyCalls_route (R₀ : Router) (log : List Call) (q : Chain × Address × AssetData)
    (hinj : IdInjOn enc ↑(insert q (loggedTriples thisChain ntv ntvAddr log))) :
    (applyCalls enc thisChain ntv ntvAddr R₀ log).handler (enc q.1 q.2.1 q.2.2)
        = loggedHandler enc thisChain ntv ntvAddr R₀ log q
    ∧ (applyCalls enc thisChain ntv ntvAddr R₀ log).tracker (enc q.1 q.2.1 q.2.2)
        = loggedTracker enc thisChain ntv ntvAddr R₀ log q := by
  induction log using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton log c ih =>
    obtain ⟨ih1, ih2⟩ := ih (idInjOn_insert_snoc hinj)
    have hq := mem_insert_self_coe q (loggedTriples thisChain ntv ntvAddr (log ++ [c]))
    have hc := mem_insert_snoc_coe (thisChain := thisChain) (ntv := ntv) (ntvAddr := ntvAddr) q log c
    rw [applyCalls_snoc, loggedHandler_snoc, loggedTracker_snoc]
    simp only [setHandler]
    by_cases h : c.triple thisChain ntv ntvAddr = q
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl]
      exact ⟨upd_same _ _ _, upd_same _ _ _⟩
    · have hne : enc q.1 q.2.1 q.2.2 ≠ writtenId enc thisChain ntv ntvAddr c.caller c.data := by
        intro he
        rw [writtenId_triple] at he
        exact h (hinj _ hc _ hq he.symm)
      rw [ite_eq_right h, ite_eq_right h, upd_ne _ _ hne, upd_ne _ _ hne]
      exact ⟨ih1, ih2⟩

/-! ### Logged runs -/

theorem stepCall_eq {c : Call} {R S : Router} (h : StepCall enc thisChain ntv ntvAddr c R S) :
    S = setHandler enc thisChain ntv ntvAddr R c.caller c.data c.handler := by
  cases h
  rfl

theorem stepCall_guard {c : Call} {R S : Router} (h : StepCall enc thisChain ntv ntvAddr c R S) :
    SetGuard enc thisChain ntv ntvAddr R c.caller c.data := by
  cases h with
  | setHandler hg => exact hg

theorem stepCall_step {c : Call} {R S : Router} (h : StepCall enc thisChain ntv ntvAddr c R S) :
    Step enc thisChain ntv ntvAddr R S := by
  cases h with
  | setHandler hg => exact Step.setHandler hg

theorem step_stepCall {R S : Router} (h : Step enc thisChain ntv ntvAddr R S) :
    ∃ c, StepCall enc thisChain ntv ntvAddr c R S := by
  cases h with
  | @setHandler caller d hh hg => exact ⟨⟨caller, d, hh⟩, StepCall.setHandler hg⟩

theorem reachLog_reach {R S : Router} {log : List Call}
    (h : ReachLog enc thisChain ntv ntvAddr R S log) : Reach enc thisChain ntv ntvAddr R S := by
  induction h with
  | refl => exact Reach.refl
  | tail _ hs ih => exact Reach.tail ih (stepCall_step hs)

theorem reach_reachLog {R S : Router} (h : Reach enc thisChain ntv ntvAddr R S) :
    ∃ log, ReachLog enc thisChain ntv ntvAddr R S log := by
  induction h with
  | refl => exact ⟨[], ReachLog.refl⟩
  | tail _ hs ih =>
    obtain ⟨log, hl⟩ := ih
    obtain ⟨c, hc⟩ := step_stepCall hs
    exact ⟨log ++ [c], ReachLog.tail hl hc⟩

theorem reachLog_applyCalls {R₀ R : Router} {log : List Call}
    (h : ReachLog enc thisChain ntv ntvAddr R₀ R log) :
    R = applyCalls enc thisChain ntv ntvAddr R₀ log := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [applyCalls_snoc, ← ih]; exact stepCall_eq hs

lemma reachLog_nil {R S : Router} (h : ReachLog enc thisChain ntv ntvAddr R S []) : S = R := by
  generalize hl : ([] : List Call) = l at h
  cases h with
  | refl => rfl
  | tail _ _ => simp at hl

lemma reachLog_snoc {R T : Router} {log : List Call} {c : Call}
    (h : ReachLog enc thisChain ntv ntvAddr R T (log ++ [c])) :
    ∃ S, ReachLog enc thisChain ntv ntvAddr R S log ∧ StepCall enc thisChain ntv ntvAddr c S T := by
  generalize hl : log ++ [c] = l at h
  cases h with
  | refl => simp at hl
  | tail h hs =>
    obtain ⟨rfl, h'⟩ := List.append_inj' hl rfl
    obtain rfl := List.singleton_injective h'
    exact ⟨_, h, hs⟩

theorem reachLog_append_iff {R₀ R : Router} {log₁ log₂ : List Call} :
    ReachLog enc thisChain ntv ntvAddr R₀ R (log₁ ++ log₂) ↔
      ∃ S, ReachLog enc thisChain ntv ntvAddr R₀ S log₁ ∧ ReachLog enc thisChain ntv ntvAddr S R log₂ := by
  constructor
  · intro h
    induction log₂ using List.reverseRecOn generalizing R with
    | nil => exact ⟨R, by simpa using h, ReachLog.refl⟩
    | append_singleton l c ih =>
      rw [← List.append_assoc] at h
      obtain ⟨X, hX, hs⟩ := reachLog_snoc h
      obtain ⟨S, h1, h2⟩ := ih hX
      exact ⟨S, h1, ReachLog.tail h2 hs⟩
  · rintro ⟨S, h1, h2⟩
    induction h2 with
    | refl => simpa using h1
    | tail _ hs ih =>
      rw [← List.append_assoc]
      exact ReachLog.tail ih hs

/-! ### The bounded results on logged runs -/

theorem logged_route_is_last_own_write {R₀ R : Router} {log : List Call}
    (h : ReachLog enc thisChain ntv ntvAddr R₀ R log) (q : Chain × Address × AssetData)
    (hinj : IdInjOn enc ↑(insert q (loggedTriples thisChain ntv ntvAddr log))) :
    R.handler (enc q.1 q.2.1 q.2.2) = loggedHandler enc thisChain ntv ntvAddr R₀ log q
    ∧ R.tracker (enc q.1 q.2.1 q.2.2) = loggedTracker enc thisChain ntv ntvAddr R₀ log q := by
  rw [reachLog_applyCalls h]
  exact applyCalls_route R₀ log q hinj

lemma lastCallOn_eq_none {log : List Call} {q : Chain × Address × AssetData}
    (hq : q ∉ loggedTriples thisChain ntv ntvAddr log) :
    lastCallOn thisChain ntv ntvAddr log q = none := by
  unfold lastCallOn
  rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff]
  intro c hc hcq
  exact hq (mem_loggedTriples.mpr ⟨c, hc, of_decide_eq_true hcq⟩)

theorem logged_run_leaves_unhashed_routes {R₀ R : Router} {log : List Call}
    (h : ReachLog enc thisChain ntv ntvAddr R₀ R log) (q : Chain × Address × AssetData)
    (hq : q ∉ loggedTriples thisChain ntv ntvAddr log)
    (hinj : IdInjOn enc ↑(insert q (loggedTriples thisChain ntv ntvAddr log))) :
    R.handler (enc q.1 q.2.1 q.2.2) = R₀.handler (enc q.1 q.2.1 q.2.2)
    ∧ R.tracker (enc q.1 q.2.1 q.2.2) = R₀.tracker (enc q.1 q.2.1 q.2.2) := by
  obtain ⟨h1, h2⟩ := logged_route_is_last_own_write h q hinj
  have hn := lastCallOn_eq_none hq
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · unfold loggedHandler; rw [hn]
  · unfold loggedTracker; rw [hn]

/-- The two triples a single call compares lie in the run's triples plus the watched one. -/
lemma pair_sub_insert_logged {log : List Call} {c : Call} (hmem : c ∈ log)
    (s : Address) (d' : AssetData) :
    ({c.triple thisChain ntv ntvAddr, (thisChain, s, d')} : Set (Chain × Address × AssetData))
      ⊆ ↑(insert (thisChain, s, d') (loggedTriples thisChain ntv ntvAddr log)) := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
  rcases hx with rfl | rfl
  · exact Or.inr (mem_loggedTriples_of_mem hmem)
  · exact Or.inl rfl

theorem logged_run_no_hijack {log pre post : List Call} {c : Call} {S T : Router}
    (hlog : log = pre ++ c :: post) (hs : StepCall enc thisChain ntv ntvAddr c S T)
    (hcn : c.caller ≠ ntv) (s : Address) (d' : AssetData) (hsc : s ≠ c.caller)
    (hinj : IdInjOn enc ↑(insert (thisChain, s, d') (loggedTriples thisChain ntv ntvAddr log))) :
    T.handler (enc thisChain s d') = S.handler (enc thisChain s d') := by
  have hmem : c ∈ log := by rw [hlog]; simp
  rw [stepCall_eq hs]
  refine no_hijack_on S c.data c.handler hcn s d' hsc (idInjOn_mono hinj ?_)
  have htr : c.triple thisChain ntv ntvAddr = (thisChain, c.caller, c.data) := by
    simp [Call.triple, senderOf_ne hcn]
  rw [← htr]
  exact pair_sub_insert_logged hmem s d'

theorem logged_run_ntv_touches_only_its_own_ids {log pre post : List Call} {c : Call}
    {S T : Router} (hlog : log = pre ++ c :: post) (hs : StepCall enc thisChain ntv ntvAddr c S T)
    (hcv : c.caller = ntv) (s : Address) (d' : AssetData) (hsv : s ≠ ntvAddr)
    (hinj : IdInjOn enc ↑(insert (thisChain, s, d') (loggedTriples thisChain ntv ntvAddr log))) :
    T.handler (enc thisChain s d') = S.handler (enc thisChain s d') := by
  have hmem : c ∈ log := by rw [hlog]; simp
  rw [stepCall_eq hs, hcv]
  refine ntv_touches_only_its_own_ids_on S c.data c.handler s d' hsv (idInjOn_mono hinj ?_)
  have htr : c.triple thisChain ntv ntvAddr = (thisChain, ntvAddr, c.data) := by
    simp [Call.triple, hcv]
  rw [← htr]
  exact pair_sub_insert_logged hmem s d'

theorem logged_run_custom_route_answers_to_registrant {R₀ R : Router} {log : List Call}
    (h : ReachLog enc thisChain ntv ntvAddr R₀ R log) (s : Address) (d' : AssetData)
    (hsv : s ≠ ntvAddr)
    (hinj : IdInjOn enc ↑(insert (thisChain, s, d') (loggedTriples thisChain ntv ntvAddr log))) :
    R.tracker (enc thisChain s d') = R₀.tracker (enc thisChain s d')
    ∧ (R.handler (enc thisChain s d') ≠ R₀.handler (enc thisChain s d') →
        R₀.tracker (enc thisChain s d') = s ∧ ∃ c ∈ log, c.caller = s ∧ c.data = d') := by
  induction h with
  | refl => exact ⟨rfl, fun hne => absurd rfl hne⟩
  | @tail X Y log c _ hstep ih =>
    obtain ⟨ihT, ihH⟩ := ih (idInjOn_insert_snoc hinj)
    have hq := mem_insert_self_coe (thisChain, s, d') (loggedTriples thisChain ntv ntvAddr (log ++ [c]))
    have hc := mem_insert_snoc_coe (thisChain := thisChain) (ntv := ntv) (ntvAddr := ntvAddr)
      (thisChain, s, d') log c
    rw [stepCall_eq hstep]
    simp only [setHandler]
    by_cases hw : enc thisChain s d' = writtenId enc thisChain ntv ntvAddr c.caller c.data
    · -- the call hashed `(thisChain, s, d')` itself
      have htr : c.triple thisChain ntv ntvAddr = (thisChain, s, d') := by
        rw [writtenId_triple] at hw
        exact hinj _ hc _ hq hw.symm
      simp only [Call.triple, Prod.mk.injEq] at htr
      obtain ⟨-, hsend, hdata⟩ := htr
      have hcn : c.caller ≠ ntv := by
        intro hcv
        rw [hcv, senderOf_self] at hsend
        exact hsv hsend.symm
      rw [senderOf_ne hcn] at hsend
      have hXtr : X.tracker (enc thisChain s d') = s := by
        rcases (stepCall_guard hstep).authorized with h1 | h1
        · exact absurd h1 hcn
        · rw [hw, ← h1, hsend]
      have hR₀ : R₀.tracker (enc thisChain s d') = s := ihT ▸ hXtr
      rw [show upd X.tracker (writtenId enc thisChain ntv ntvAddr c.caller c.data) c.caller
          (enc thisChain s d') = c.caller by rw [hw]; exact upd_same _ _ _]
      refine ⟨hsend.trans hR₀.symm, fun _ => ⟨hR₀, c, by simp, hsend, hdata⟩⟩
    · rw [upd_ne _ _ hw, upd_ne _ _ hw]
      refine ⟨ihT, fun hne => ?_⟩
      obtain ⟨h1, c', hc', h2⟩ := ihH hne
      exact ⟨h1, c', List.mem_append_left _ hc', h2⟩

/-- Any log shorter than the id space, plus one triple, admits an injective encoding. -/
theorem log_assumption_satisfiable (log : List Call) (q : Chain × Address × AssetData)
    (hlen : log.length < UInt256.size) :
    ∃ enc : AssetIdOf, IdInjOn enc ↑(insert q (loggedTriples thisChain ntv ntvAddr log)) := by
  refine idInjOn_of_card _ (le_trans (Finset.card_insert_le _ _) ?_)
  have := loggedTriples_card_le (thisChain := thisChain) (ntv := ntv) (ntvAddr := ntvAddr) log
  omega

/-! ### Without a hash premise: the guard and the vault's routes -/

theorem vault_tracker_is_permanent {S T : Router} {log : List Call}
    (h : ReachLog enc thisChain ntv ntvAddr S T log) (a : AssetId) (ha : S.tracker a = ntv) :
    T.tracker a = ntv := by
  induction h with
  | refl => exact ha
  | @tail X Y log c _ hs ih =>
    have hX := ih
    rw [stepCall_eq hs]
    simp only [setHandler]
    by_cases hw : a = writtenId enc thisChain ntv ntvAddr c.caller c.data
    · rw [hw, upd_same]
      rcases (stepCall_guard hs).authorized with h1 | h1
      · exact h1
      · rw [h1, ← hw]; exact hX
    · rw [upd_ne _ _ hw]; exact hX

theorem nonvault_run_keeps_vault_routes {S T : Router} {log : List Call}
    (h : ReachLog enc thisChain ntv ntvAddr S T log) (hnv : ∀ c ∈ log, c.caller ≠ ntv)
    (a : AssetId) (ha : S.tracker a = ntv) : T.handler a = S.handler a := by
  induction h with
  | refl => rfl
  | @tail X Y log c hr hs ih =>
    have ih' := ih (fun c' hc' => hnv c' (List.mem_append_left _ hc'))
    have hX : X.tracker a = ntv := vault_tracker_is_permanent hr a ha
    have hcn : c.caller ≠ ntv := hnv c (List.mem_append_right _ (List.mem_singleton_self _))
    rw [stepCall_eq hs]
    have hw : a ≠ writtenId enc thisChain ntv ntvAddr c.caller c.data := by
      intro hw
      rcases (stepCall_guard hs).authorized with h1 | h1
      · exact hcn h1
      · rw [← hw, hX] at h1; exact hcn h1
    rw [handler_frame _ _ _ _ _ _ _ _ _ hw]
    exact ih'

theorem ntv_route_survives_nonvault_calls {S S' T : Router} {c : Call} {post : List Call}
    (hs : StepCall enc thisChain ntv ntvAddr c S S') (hcv : c.caller = ntv)
    (hr : ReachLog enc thisChain ntv ntvAddr S' T post) (hnv : ∀ c' ∈ post, c'.caller ≠ ntv) :
    T.handler (enc thisChain ntvAddr c.data) = c.handler
    ∧ T.tracker (enc thisChain ntvAddr c.data) = ntv := by
  have hw : writtenId enc thisChain ntv ntvAddr c.caller c.data = enc thisChain ntvAddr c.data := by
    simp [writtenId, hcv]
  have h1 : S'.handler (enc thisChain ntvAddr c.data) = c.handler := by
    rw [stepCall_eq hs, ← hw]; exact upd_same _ _ _
  have h2 : S'.tracker (enc thisChain ntvAddr c.data) = ntv := by
    rw [stepCall_eq hs, ← hw]; exact (upd_same _ _ _).trans hcv
  exact ⟨(nonvault_run_keeps_vault_routes hr hnv _ h2).trans h1, vault_tracker_is_permanent hr _ h2⟩

/-- A route the vault holds survives a logged run whose calls hash triples of a set `L` the
hash is injective on, `L` holding the route's own triple, as long as no vault call of the
run has the route's data: a vault call lands elsewhere by injectivity, and a non-vault call
that hashed the route's triple would have to be its tracker, the vault. -/
theorem keeps_vault_route_aux {S T : Router} {post : List Call}
    (h : ReachLog enc thisChain ntv ntvAddr S T post) {L : Set (Chain × Address × AssetData)}
    (hinj : IdInjOn enc L) {d : AssetData} {hv : Address} (hq : (thisChain, ntvAddr, d) ∈ L)
    (hpost : ∀ c' ∈ post, c'.triple thisChain ntv ntvAddr ∈ L)
    (hdata : ∀ c' ∈ post, c'.caller = ntv → c'.data ≠ d)
    (h1 : S.handler (enc thisChain ntvAddr d) = hv) (h2 : S.tracker (enc thisChain ntvAddr d) = ntv) :
    T.handler (enc thisChain ntvAddr d) = hv ∧ T.tracker (enc thisChain ntvAddr d) = ntv := by
  induction h with
  | refl => exact ⟨h1, h2⟩
  | @tail X Y log c' _ hs ih =>
    obtain ⟨ihH, ihT⟩ := ih (fun c'' hc'' => hpost c'' (List.mem_append_left _ hc''))
      (fun c'' hc'' => hdata c'' (List.mem_append_left _ hc''))
    have hmem : c' ∈ log ++ [c'] := List.mem_append_right _ (List.mem_singleton_self _)
    have hw : enc thisChain ntvAddr d ≠ writtenId enc thisChain ntv ntvAddr c'.caller c'.data := by
      intro hw
      have htr : c'.triple thisChain ntv ntvAddr = (thisChain, ntvAddr, d) := by
        rw [writtenId_triple] at hw
        exact hinj _ (hpost c' hmem) _ hq hw.symm
      by_cases hcv : c'.caller = ntv
      · simp only [Call.triple, Prod.mk.injEq] at htr
        exact hdata c' hmem hcv htr.2.2
      · rcases (stepCall_guard hs).authorized with hg | hg
        · exact hcv hg
        · rw [← hw, ihT] at hg
          exact hcv hg
    rw [stepCall_eq hs]
    simp only [setHandler]
    rw [upd_ne _ _ hw, upd_ne _ _ hw]
    exact ⟨ihH, ihT⟩

theorem logged_run_keeps_vault_routes {R₀ R : Router} {log : List Call}
    (h : ReachLog enc thisChain ntv ntvAddr R₀ R log)
    (hinj : IdInjOn enc ↑(loggedTriples thisChain ntv ntvAddr log))
    {pre post : List Call} {c : Call} (hlog : log = pre ++ c :: post) (hcv : c.caller = ntv)
    (hdata : ∀ c' ∈ post, c'.caller = ntv → c'.data ≠ c.data) :
    R.handler (enc thisChain ntvAddr c.data) = c.handler
    ∧ R.tracker (enc thisChain ntvAddr c.data) = ntv := by
  subst hlog
  have hsplit : ReachLog enc thisChain ntv ntvAddr R₀ R (pre ++ [c] ++ post) := by
    rw [← List.append_cons]; exact h
  obtain ⟨S₁, h1, h2⟩ := reachLog_append_iff.mp hsplit
  obtain ⟨S₀, -, hs⟩ := reachLog_snoc h1
  have hw : writtenId enc thisChain ntv ntvAddr c.caller c.data = enc thisChain ntvAddr c.data := by
    simp [writtenId, hcv]
  have hH : S₁.handler (enc thisChain ntvAddr c.data) = c.handler := by
    rw [stepCall_eq hs, ← hw]; exact upd_same _ _ _
  have hT : S₁.tracker (enc thisChain ntvAddr c.data) = ntv := by
    rw [stepCall_eq hs, ← hw]; exact (upd_same _ _ _).trans hcv
  have htr : c.triple thisChain ntv ntvAddr = (thisChain, ntvAddr, c.data) := by
    simp [Call.triple, hcv]
  have hq : (thisChain, ntvAddr, c.data)
      ∈ (↑(loggedTriples thisChain ntv ntvAddr (pre ++ c :: post)) : Set (Chain × Address × AssetData)) := by
    rw [Finset.mem_coe, ← htr]
    exact mem_loggedTriples_of_mem (by simp)
  refine keeps_vault_route_aux h2 hinj hq (fun c' hc' => ?_) hdata hH hT
  rw [Finset.mem_coe]
  exact mem_loggedTriples_of_mem (List.mem_append_right _ (List.mem_cons_of_mem _ hc'))

theorem vault_held_routes_point_at_vault {R₀ R : Router} {log : List Call}
    (h : ReachLog enc thisChain ntv ntvAddr R₀ R log)
    (hvh : ∀ c ∈ log, c.caller = ntv → c.handler = ntv)
    (h0 : ∀ a, R₀.tracker a = ntv → R₀.handler a = ntv) :
    ∀ a, R.tracker a = ntv → R.handler a = ntv := by
  induction h with
  | refl => exact h0
  | @tail X Y log c _ hs ih =>
    have ih' := ih (fun c' hc' => hvh c' (List.mem_append_left _ hc'))
    intro a ha
    rw [stepCall_eq hs] at ha ⊢
    simp only [setHandler] at ha ⊢
    by_cases hw : a = writtenId enc thisChain ntv ntvAddr c.caller c.data
    · rw [hw, upd_same] at ha ⊢
      exact hvh c (List.mem_append_right _ (List.mem_singleton_self _)) ha
    · rw [upd_ne _ _ hw] at ha ⊢
      exact ih' a ha

/-! ### From fresh storage only the vault acts -/

theorem empty_vaultOnly (ntv : Address) : VaultOnlyTrackers ntv empty := fun _ => Or.inl rfl

theorem vaultOnly_admits_only_the_vault {R : Router} {caller : Address} {d : AssetData}
    (hV : VaultOnlyTrackers ntv R) (hg : SetGuard enc thisChain ntv ntvAddr R caller d) :
    caller = ntv := by
  rcases hg.authorized with h | h
  · exact h
  · rcases hV (writtenId enc thisChain ntv ntvAddr caller d) with h0 | h0
    · exact absurd (h.trans h0) hg.callerNonzero
    · exact h.trans h0

theorem setHandler_keeps_vaultOnly {R : Router} {caller : Address} {d : AssetData} {h : Address}
    (hV : VaultOnlyTrackers ntv R) (hc : caller = ntv) :
    VaultOnlyTrackers ntv (setHandler enc thisChain ntv ntvAddr R caller d h) := by
  intro a
  simp only [setHandler]
  by_cases ha : a = writtenId enc thisChain ntv ntvAddr caller d
  · rw [ha, upd_same]; exact Or.inr hc
  · rw [upd_ne _ _ ha]; exact hV a

theorem step_keeps_vaultOnly {R S : Router} (hs : Step enc thisChain ntv ntvAddr R S)
    (hV : VaultOnlyTrackers ntv R) : VaultOnlyTrackers ntv S := by
  cases hs with
  | setHandler hg => exact setHandler_keeps_vaultOnly hV (vaultOnly_admits_only_the_vault hV hg)

theorem reachLog_vaultOnly {R₀ R : Router} {log : List Call}
    (h : ReachLog enc thisChain ntv ntvAddr R₀ R log) (hV : VaultOnlyTrackers ntv R₀) :
    VaultOnlyTrackers ntv R ∧ ∀ c ∈ log, c.caller = ntv := by
  induction h with
  | refl => exact ⟨hV, fun _ h => absurd h (List.not_mem_nil)⟩
  | tail _ hs ih =>
    obtain ⟨ihV, ihC⟩ := ih
    have hc := vaultOnly_admits_only_the_vault ihV (stepCall_guard hs)
    refine ⟨stepCall_eq hs ▸ setHandler_keeps_vaultOnly ihV hc, fun c' hc' => ?_⟩
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact ihC c' hc'
    · rw [List.mem_singleton.mp hc']; exact hc

theorem only_vault_acts_from_empty {R : Router} {log : List Call}
    (h : ReachLog enc thisChain ntv ntvAddr empty R log) : ∀ c ∈ log, c.caller = ntv :=
  (reachLog_vaultOnly h (empty_vaultOnly ntv)).2

theorem reachAmid_vaultOnly {R₀ R : Router} {log : List Call}
    (h : ReachAmidOtherWriters enc thisChain ntv ntvAddr R₀ R log) (hV : VaultOnlyTrackers ntv R₀) :
    VaultOnlyTrackers ntv R ∧ ∀ c ∈ log, c.caller = ntv := by
  induction h with
  | refl => exact ⟨hV, fun _ h => absurd h (List.not_mem_nil)⟩
  | call _ hs ih =>
    obtain ⟨ihV, ihC⟩ := ih
    have hc := vaultOnly_admits_only_the_vault ihV (stepCall_guard hs)
    refine ⟨stepCall_eq hs ▸ setHandler_keeps_vaultOnly ihV hc, fun c' hc' => ?_⟩
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact ihC c' hc'
    · rw [List.mem_singleton.mp hc']; exact hc
  | other _ htr ih =>
    obtain ⟨ihV, ihC⟩ := ih
    exact ⟨fun a => htr ▸ ihV a, ihC⟩

theorem only_vault_acts_amid_other_writers {R : Router} {log : List Call}
    (h : ReachAmidOtherWriters enc thisChain ntv ntvAddr empty R log) :
    ∀ c ∈ log, c.caller = ntv :=
  (reachAmid_vaultOnly h (empty_vaultOnly ntv)).2

end Runs

/-! ### Deciding injectivity on a concrete finite set

`IdInjOn enc ↑F` is `Set.InjOn` of the id map on `F`, so on a concrete `F` it is decided by
comparing the size of `F` with the size of its image. -/

lemma idInjOn_iff_card_image {enc : AssetIdOf} (F : Finset (Chain × Address × AssetData)) :
    IdInjOn enc ↑F ↔ (F.image (fun p => enc p.1 p.2.1 p.2.2)).card = F.card := by
  rw [Finset.card_image_iff]
  exact ⟨fun h p hp q hq he => h p hp q hq he, fun h p hp q hq he => h hp hq he⟩

lemma idInjOn_of_card_image {enc : AssetIdOf} (F : Finset (Chain × Address × AssetData))
    (h : (F.image (fun p => enc p.1 p.2.1 p.2.2)).card = F.card) : IdInjOn enc ↑F :=
  (idInjOn_iff_card_image F).mpr h

lemma not_idInjOn_of_card_image {enc : AssetIdOf} (F : Finset (Chain × Address × AssetData))
    (h : (F.image (fun p => enc p.1 p.2.1 p.2.2)).card ≠ F.card) : ¬ IdInjOn enc ↑F :=
  fun hi => h ((idInjOn_iff_card_image F).mp hi)

/-! ### The witness scenario

L1, chain `1`: the vault at `9`, normalised to the system address `8`; custom registrant
`3`, whitelisted by the owner for data `0` (`wStartH`, whose handler map `hm` is free so
that one witness can start with a route already live).  The log: `3` points its asset at
`5`; the vault registers token `7` (handler: itself); `3` re-points its asset at `4`; the
vault registers token `6`.  The encoding `wEnc` (sender plus data) gives the run's three
triples `(1, 3, 0)`, `(1, 8, 7)`, `(1, 8, 6)` the distinct ids `3`, `15`, `14`, and maps
`(1, 7, 8)`, which the run never hashed, to the vault's id `15`. -/

/-- The witness encoding: sender plus data. -/
def wEnc : AssetIdOf := fun _ s d => s + d

/-- `3` points its asset at `5`. -/
def wCall1 : Call := ⟨3, 0, 5⟩
/-- The vault registers token `7`; its handler is the vault itself. -/
def wCall2 : Call := ⟨9, 7, 9⟩
/-- `3` re-points its asset at `4`. -/
def wCall3 : Call := ⟨3, 0, 4⟩
/-- The vault registers token `6`. -/
def wCall4 : Call := ⟨9, 6, 9⟩
/-- The witness log. -/
def wLog : List Call := [wCall1, wCall2, wCall3, wCall4]

/-- The owner's whitelisting of `3` for data `0`, with handler map `hm`. -/
def wStartH (hm : AssetId → Address) : Router :=
  { afterSetDeploymentTracker wEnc 1 empty 0 3 with handler := hm }
/-- After the first call. -/
def wS1 (hm : AssetId → Address) : Router := setHandler wEnc 1 9 8 (wStartH hm) 3 0 5
/-- After the vault registers token `7`. -/
def wS2 (hm : AssetId → Address) : Router := setHandler wEnc 1 9 8 (wS1 hm) 9 7 9
/-- After the third call. -/
def wS3 (hm : AssetId → Address) : Router := setHandler wEnc 1 9 8 (wS2 hm) 3 0 4
/-- After the vault registers token `6`. -/
def wS4 (hm : AssetId → Address) : Router := setHandler wEnc 1 9 8 (wS3 hm) 9 6 9

/-- Fresh storage's handler map. -/
def wNoRoutes : AssetId → Address := fun _ => 0
/-- A handler map with one route live at id `2`, as another writer might have installed. -/
def wOneRoute : AssetId → Address := upd (fun _ => 0) 2 6

lemma wStart_eq : wStartH wNoRoutes = afterSetDeploymentTracker wEnc 1 empty 0 3 := rfl

/-- The trackers do not depend on the start's handler map. -/
lemma wStartH_tracker (hm : AssetId → Address) :
    (wStartH hm).tracker = (wStartH wNoRoutes).tracker := rfl
lemma wS2_tracker (hm : AssetId → Address) : (wS2 hm).tracker = (wS2 wNoRoutes).tracker := rfl

lemma w_step1 (hm : AssetId → Address) : StepCall wEnc 1 9 8 wCall1 (wStartH hm) (wS1 hm) :=
  StepCall.setHandler ⟨Or.inr (by rw [wStartH_tracker]; decide), by decide⟩
lemma w_step2 (hm : AssetId → Address) : StepCall wEnc 1 9 8 wCall2 (wS1 hm) (wS2 hm) :=
  StepCall.setHandler ⟨Or.inl rfl, by decide⟩
lemma w_step3 (hm : AssetId → Address) : StepCall wEnc 1 9 8 wCall3 (wS2 hm) (wS3 hm) :=
  StepCall.setHandler ⟨Or.inr (by rw [wS2_tracker]; decide), by decide⟩
lemma w_step4 (hm : AssetId → Address) : StepCall wEnc 1 9 8 wCall4 (wS3 hm) (wS4 hm) :=
  StepCall.setHandler ⟨Or.inl rfl, by decide⟩

lemma w_reach1 (hm : AssetId → Address) : ReachLog wEnc 1 9 8 (wStartH hm) (wS1 hm) [wCall1] :=
  ReachLog.tail (log := []) ReachLog.refl (w_step1 hm)
lemma w_reach2 (hm : AssetId → Address) :
    ReachLog wEnc 1 9 8 (wStartH hm) (wS2 hm) [wCall1, wCall2] :=
  ReachLog.tail (log := [wCall1]) (w_reach1 hm) (w_step2 hm)
lemma w_reach3 (hm : AssetId → Address) :
    ReachLog wEnc 1 9 8 (wStartH hm) (wS3 hm) [wCall1, wCall2, wCall3] :=
  ReachLog.tail (log := [wCall1, wCall2]) (w_reach2 hm) (w_step3 hm)
lemma w_reach4 (hm : AssetId → Address) : ReachLog wEnc 1 9 8 (wStartH hm) (wS4 hm) wLog :=
  ReachLog.tail (log := [wCall1, wCall2, wCall3]) (w_reach3 hm) (w_step4 hm)

lemma wCall1_mem : wCall1 ∈ wLog := by simp [wLog]
lemma wCall2_mem : wCall2 ∈ wLog := by simp [wLog]

/-- Every vault call of the witness log names the vault as handler. -/
lemma wLog_vault_handlers : ∀ c ∈ wLog, c.caller = 9 → c.handler = 9 := by
  intro c hc
  simp only [wLog, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> decide

/-- The witness start holds no id for the vault. -/
lemma wStart_no_vault_ids (hm : AssetId → Address) (a : AssetId) :
    (wStartH hm).tracker a ≠ 9 := by
  show upd (fun _ => 0) (wEnc 1 3 0) 3 a ≠ 9
  unfold upd
  split_ifs
  · decide
  · show (0 : Address) ≠ 9
    decide

/-! ### A vault call from fresh storage, and the countermodels' encoding -/

/-- A vault call with data `7` passes the guard anywhere. -/
lemma vault_guard_any (R : Router) : SetGuard honestEnc 1 9 8 R 9 7 := ⟨Or.inl rfl, by decide⟩

/-- An encoding with one collision that matters here: the vault's id for token `7` (sender
`8`, data `7`) is `3`, which is also the id of every triple hashed from sender `3`;
otherwise the id is the sender. -/
def oneCollisionEnc : AssetIdOf := fun _ s d => if s = 8 ∧ d = 7 then 3 else s

/-- The owner's whitelisting of `3` for data `0`, under `oneCollisionEnc`. -/
def cStart : Router := afterSetDeploymentTracker oneCollisionEnc 1 empty 0 3
/-- `3` has pointed its asset at `5`. -/
def cLive : Router := setHandler oneCollisionEnc 1 9 8 cStart 3 0 5
/-- The vault has registered token `7`. -/
def cTaken : Router := setHandler oneCollisionEnc 1 9 8 cLive 9 7 9

end Contracts.AssetRouter

/-! ## Certificates -/

namespace Contracts.AssetRouter

theorem ReachIffReachLog : Properties.ReachIffReachLog :=
  fun _ _ _ _ _ _ => ⟨reach_reachLog, fun ⟨_, h⟩ => reachLog_reach h⟩
theorem ReachLogIsApplyCalls : Properties.ReachLogIsApplyCalls :=
  fun _ _ _ _ _ _ _ h => reachLog_applyCalls h
theorem ReachLogAppend : Properties.ReachLogAppend :=
  fun _ _ _ _ _ _ _ _ => reachLog_append_iff
theorem LoggedTriplesCardLe : Properties.LoggedTriplesCardLe :=
  fun _ _ _ log => loggedTriples_card_le log
theorem MemLoggedTriples : Properties.MemLoggedTriples :=
  fun _ _ _ _ _ => mem_loggedTriples
theorem LogAssumptionSatisfiable : Properties.LogAssumptionSatisfiable :=
  fun _ _ _ log q hlen => log_assumption_satisfiable log q hlen

theorem LoggedRouteIsLastOwnWrite : Properties.LoggedRouteIsLastOwnWrite :=
  fun _ _ _ _ _ _ _ h q hinj => logged_route_is_last_own_write h q hinj
theorem RouteIsLastOwnWriteWithoutGuard : Properties.RouteIsLastOwnWriteWithoutGuard :=
  fun _ _ _ _ R₀ log q hinj => applyCalls_route R₀ log q hinj
theorem LoggedRunLeavesUnhashedRoutes : Properties.LoggedRunLeavesUnhashedRoutes :=
  fun _ _ _ _ _ _ _ h q hq hinj => logged_run_leaves_unhashed_routes h q hq hinj
theorem LoggedRunNoHijack : Properties.LoggedRunNoHijack := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ hlog _ hs hcn s d' hsc hinj
  exact logged_run_no_hijack hlog hs hcn s d' hsc hinj
theorem LoggedRunNtvTouchesOnlyItsOwnIds : Properties.LoggedRunNtvTouchesOnlyItsOwnIds := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ hlog _ hs hcv s d' hsv hinj
  exact logged_run_ntv_touches_only_its_own_ids hlog hs hcv s d' hsv hinj
theorem LoggedRunCustomRouteAnswersToRegistrant :
    Properties.LoggedRunCustomRouteAnswersToRegistrant :=
  fun _ _ _ _ _ _ _ h s d' hsv hinj => logged_run_custom_route_answers_to_registrant h s d' hsv hinj

theorem VaultTrackerIsPermanent : Properties.VaultTrackerIsPermanent :=
  fun _ _ _ _ _ _ _ h a ha => vault_tracker_is_permanent h a ha
theorem NonVaultRunKeepsVaultRoutes : Properties.NonVaultRunKeepsVaultRoutes :=
  fun _ _ _ _ _ _ _ h hnv a ha => nonvault_run_keeps_vault_routes h hnv a ha
theorem NtvRouteSurvivesNonVaultCalls : Properties.NtvRouteSurvivesNonVaultCalls :=
  fun _ _ _ _ _ _ _ _ _ hs hcv hr hnv => ntv_route_survives_nonvault_calls hs hcv hr hnv
theorem LoggedRunKeepsVaultRoutes : Properties.LoggedRunKeepsVaultRoutes :=
  fun _ _ _ _ _ _ _ h hinj _ _ _ hlog hcv hdata => logged_run_keeps_vault_routes h hinj hlog hcv hdata
theorem VaultHeldRoutesPointAtVault : Properties.VaultHeldRoutesPointAtVault :=
  fun _ _ _ _ _ _ _ h hvh h0 => vault_held_routes_point_at_vault h hvh h0

theorem EmptyHasVaultOnlyTrackers : Properties.EmptyHasVaultOnlyTrackers := empty_vaultOnly
theorem VaultOnlyTrackersAdmitOnlyTheVault : Properties.VaultOnlyTrackersAdmitOnlyTheVault :=
  fun _ _ _ _ _ _ _ hV hg => vaultOnly_admits_only_the_vault hV hg
theorem StepKeepsVaultOnlyTrackers : Properties.StepKeepsVaultOnlyTrackers :=
  fun _ _ _ _ _ _ hs hV => step_keeps_vaultOnly hs hV
theorem OnlyVaultActsFromEmpty : Properties.OnlyVaultActsFromEmpty :=
  fun _ _ _ _ _ _ h => only_vault_acts_from_empty h
theorem OnlyVaultActsAmidOtherWriters : Properties.OnlyVaultActsAmidOtherWriters :=
  fun _ _ _ _ _ _ h => only_vault_acts_amid_other_writers h

/-! ### Witnesses, on the four-call run -/

theorem LoggedRouteIsLastOwnWriteSatisfiable : Properties.LoggedRouteIsLastOwnWriteSatisfiable :=
  ⟨wEnc, 1, 9, 8, wStartH wNoRoutes, wS4 wNoRoutes, wLog, (1, 8, 7), w_reach4 _,
    idInjOn_of_card_image _ (by decide), ⟨0, 3, wStart_eq⟩, ⟨wCall2, wCall2_mem, rfl⟩,
    ⟨wCall1, wCall1_mem, by decide⟩, ⟨[wCall1], [wCall3, wCall4], wCall2, rfl, rfl, by simp⟩,
    by decide, (1, 8, 7), by decide, (1, 7, 8), by decide, by decide⟩

theorem LoggedRunLeavesUnhashedRoutesSatisfiable :
    Properties.LoggedRunLeavesUnhashedRoutesSatisfiable :=
  ⟨wEnc, 1, 9, 8, wStartH wOneRoute, wS4 wOneRoute, wLog, (5, 2, 0), w_reach4 _, by decide,
    idInjOn_of_card_image _ (by decide), ⟨wCall2, wCall2_mem, rfl⟩, by decide⟩

theorem LoggedRunNoHijackSatisfiable : Properties.LoggedRunNoHijackSatisfiable :=
  ⟨wEnc, 1, 9, 8, wStartH wNoRoutes, wS4 wNoRoutes, wLog, [wCall1, wCall2], [wCall4], wCall3,
    wS2 wNoRoutes, wS3 wNoRoutes, 8, 7, w_reach4 _, rfl, w_reach2 _, w_step3 _, by decide,
    by decide, idInjOn_of_card_image _ (by decide), ⟨0, 3, wStart_eq⟩, rfl, by decide,
    by decide, (1, 8, 7), by decide, (1, 7, 8), by decide, by decide⟩

theorem LoggedRunNtvTouchesOnlyItsOwnIdsSatisfiable :
    Properties.LoggedRunNtvTouchesOnlyItsOwnIdsSatisfiable :=
  ⟨wEnc, 1, 9, 8, wStartH wNoRoutes, wS4 wNoRoutes, wLog, [wCall1], [wCall3, wCall4], wCall2,
    wS1 wNoRoutes, wS2 wNoRoutes, 3, 0, w_reach4 _, rfl, w_reach1 _, w_step2 _, rfl, by decide,
    idInjOn_of_card_image _ (by decide), ⟨0, 3, wStart_eq⟩, by decide, by decide,
    (1, 8, 7), by decide, (1, 7, 8), by decide, by decide⟩

theorem LoggedRunCustomRouteAnswersToRegistrantSatisfiable :
    Properties.LoggedRunCustomRouteAnswersToRegistrantSatisfiable :=
  ⟨wEnc, 1, 9, 8, wStartH wNoRoutes, wS4 wNoRoutes, wLog, 3, 0, w_reach4 _, by decide,
    idInjOn_of_card_image _ (by decide), ⟨0, 3, wStart_eq⟩, ⟨wCall2, wCall2_mem, rfl⟩, by decide,
    (1, 8, 7), by decide, (1, 7, 8), by decide, by decide⟩

theorem VaultRouteGuardSatisfiable : Properties.VaultRouteGuardSatisfiable :=
  ⟨wEnc, 1, 9, 8, wS1 wNoRoutes, wS2 wNoRoutes, wS3 wNoRoutes, wCall2, [wCall3], w_step2 _, rfl,
    ReachLog.tail (log := []) ReachLog.refl (w_step3 _),
    fun c' hc' => by rw [List.mem_singleton.mp hc']; decide, by decide, by decide, by simp,
    fun h => absurd (congrArg (fun R => R.handler 3) h) (by decide)⟩

theorem LoggedRunKeepsVaultRoutesSatisfiable : Properties.LoggedRunKeepsVaultRoutesSatisfiable := by
  refine ⟨wEnc, 1, 9, 8, wStartH wNoRoutes, wS4 wNoRoutes, wLog, [wCall1], [wCall3, wCall4], wCall2,
    w_reach4 _, idInjOn_of_card_image _ (by decide), rfl, rfl, ?_, ⟨0, 3, wStart_eq⟩,
    ⟨wCall4, by simp, rfl⟩, ⟨wCall3, by simp, by decide⟩, (1, 8, 7), by decide, (1, 7, 8),
    by decide, by decide⟩
  intro c' hc'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl <;> decide

theorem VaultHeldRoutesPointAtVaultSatisfiable :
    Properties.VaultHeldRoutesPointAtVaultSatisfiable :=
  ⟨wEnc, 1, 9, 8, wStartH wNoRoutes, wS4 wNoRoutes, wLog, w_reach4 _, wLog_vault_handlers,
    fun a ha => absurd ha (wStart_no_vault_ids _ a), ⟨0, 3, wStart_eq⟩,
    ⟨wCall1, wCall1_mem, by decide⟩, 15, by decide⟩

theorem FromEmptyWitness : Properties.FromEmptyWitness :=
  ⟨honestEnc, 1, 9, 8, 7, 9, setHandler honestEnc 1 9 8 empty 9 7 9,
    setHandler honestEnc 1 9 8 ⟨wOneRoute, empty.tracker⟩ 9 7 9,
    empty_vaultOnly 9, vault_guard_any empty, Step.setHandler (vault_guard_any empty),
    ReachLog.tail (log := []) ReachLog.refl
      (StepCall.setHandler (c := ⟨9, 7, 9⟩) (vault_guard_any empty)),
    by decide, by decide,
    ReachAmidOtherWriters.call (log := [])
      (ReachAmidOtherWriters.other (T := ⟨wOneRoute, empty.tracker⟩) ReachAmidOtherWriters.refl rfl)
      (StepCall.setHandler (c := ⟨9, 7, 9⟩) (vault_guard_any _)),
    fun h => absurd (congrArg (fun R => R.handler 2) h) (by decide)⟩

/-! ### Countermodels -/

theorem LoggedCollisionTakesOverLiveRoute : Properties.LoggedCollisionTakesOverLiveRoute :=
  ⟨oneCollisionEnc, 1, 9, 8, 3, 7, 0, 5, cStart, cLive, cTaken, by decide, by decide, by decide,
    by decide, rfl,
    ReachLog.tail (log := []) ReachLog.refl
      (StepCall.setHandler (c := ⟨3, 0, 5⟩) ⟨Or.inr (by decide), by decide⟩),
    by decide, StepCall.setHandler (c := ⟨9, 7, 9⟩) ⟨Or.inl rfl, by decide⟩, by decide, by decide,
    fun g => absurd g.authorized (by decide), by decide,
    not_idInjOn_of_card_image _ (by decide)⟩

theorem HashAloneDoesNotProtectVaultRoutes : Properties.HashAloneDoesNotProtectVaultRoutes :=
  ⟨honestEnc, 1, 9, 8, 7, 6, by decide, by decide, idInjOn_of_card_image _ (by decide), by decide,
    by decide, fun g => absurd g.authorized (by decide)⟩

/-- A vault call with data `6` passes the guard anywhere. -/
lemma vault_guard_any6 (R : Router) : SetGuard honestEnc 1 9 8 R 9 6 := ⟨Or.inl rfl, by decide⟩

theorem CollidingVaultCallMovesVaultRoute : Properties.CollidingVaultCallMovesVaultRoute :=
  ⟨honestEnc, 1, 9, 8, 7, 6, 5,
    setHandler honestEnc 1 9 8 (setHandler honestEnc 1 9 8 empty 9 7 9) 9 6 5, by decide, by decide,
    ReachLog.tail (log := [⟨9, 7, 9⟩])
      (ReachLog.tail (log := []) ReachLog.refl
        (StepCall.setHandler (c := ⟨9, 7, 9⟩) (vault_guard_any empty)))
      (StepCall.setHandler (c := ⟨9, 6, 5⟩) (vault_guard_any6 _)),
    rfl, by decide⟩

end Contracts.AssetRouter
