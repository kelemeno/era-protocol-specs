import EraSpec.Contracts.AssetRouterBase.Properties.AllWriters
import EraSpec.Contracts.AssetRouterBase.Proofs.HandlerRegistration

/-!
# Proofs: the router with every writer at the pin

Each call writes at most one handler, at its `target`, and at most one tracker.  The
invariant proofs are case splits on the call, with the frame lemmas below doing the
rest.  The one place a hash premise enters is an owner tracker write naming zero:
under the run-local premise it hits no nonzero tracker, so it writes nothing.
-/

namespace Contracts.AssetRouter.AllWriters

/-! ## Frame lemmas -/

@[simp] lemma pointAt_handler_self (R : Router) (a : AssetId) (h : Address) :
    (pointAt R a h).handler a = h := by
  simp [pointAt]

lemma pointAt_handler_ne (R : Router) {a x : AssetId} (h : Address) (hx : x ≠ a) :
    (pointAt R a h).handler x = R.handler x := by
  simp [pointAt, upd, hx]

@[simp] lemma pointAt_tracker (R : Router) (a : AssetId) (h : Address) :
    (pointAt R a h).tracker = R.tracker := rfl

@[simp] lemma recordTracker_handler (K : Cfg) (R : Router) (d : AssetData) (t : Address) :
    (recordTracker K R d t).handler = R.handler := rfl

@[simp] lemma recordTracker_tracker_self (K : Cfg) (R : Router) (d : AssetData) (t : Address) :
    (recordTracker K R d t).tracker (K.enc K.thisChain t d) = t := by
  simp [recordTracker]

lemma recordTracker_tracker_ne (K : Cfg) (R : Router) {d : AssetData} {t : Address}
    {x : AssetId} (hx : x ≠ K.enc K.thisChain t d) :
    (recordTracker K R d t).tracker x = R.tracker x := by
  simp [recordTracker, upd, hx]

lemma setHandler_tracker_ne (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address)
    (R : Router) (caller : Address) (d : AssetData) (h : Address) {x : AssetId}
    (hx : x ≠ writtenId enc thisChain ntv ntvAddr caller d) :
    (setHandler enc thisChain ntv ntvAddr R caller d h).tracker x = R.tracker x := by
  simp only [setHandler]
  exact upd_ne _ _ hx

/-- `WeakValid` at one id reads only that id's handler and tracker. -/
lemma weakAt_congr {K : Cfg} {R R' : Router} {a : AssetId}
    (hw : R.handler a ≠ 0 → R.tracker a ≠ 0 ∨ VaultRoute K R a)
    (hh : R'.handler a = R.handler a) (ht : R'.tracker a = R.tracker a) :
    R'.handler a ≠ 0 → R'.tracker a ≠ 0 ∨ VaultRoute K R' a := by
  intro hnz
  rw [hh] at hnz
  rcases hw hnz with h | ⟨h1, h2⟩
  · exact Or.inl (by rwa [ht])
  · exact Or.inr ⟨by rw [hh]; exact h1, h2⟩

lemma not_valid_pointAt {R : Router} {a : AssetId} {h : Address} (hh : h ≠ 0)
    (ht : R.tracker a = 0) : ¬ Valid (pointAt R a h) :=
  fun hV => hV a (by rw [pointAt_handler_self]; exact hh) ht

lemma weakValid_pointAt_empty {K : Cfg} {a : AssetId} (ha : IsNtvId K.enc K.ntvAddr a) :
    WeakValid K (pointAt empty a K.ntv) := by
  intro x hx
  by_cases h : x = a
  · subst h
    exact Or.inr ⟨pointAt_handler_self _ _ _, ha⟩
  · exact absurd (pointAt_handler_ne empty K.ntv h) hx

/-! ## Runs -/

/-- Every logged call was enabled at the point it ran. -/
lemma ARun.mem_enabled {K : Cfg} {R0 R : Router} {ops : List Op} (hr : ARun K R0 ops R) :
    ∀ op ∈ ops, ∃ S T, AStep K op S T := by
  induction hr with
  | nil => intro op h; cases h
  | snoc _ hs ih =>
    intro op hop
    rcases List.mem_append.1 hop with h | h
    · exact ih op h
    · rw [List.mem_singleton] at h
      subst h
      exact ⟨_, _, hs⟩

/-- L2 has no tracker writer besides registration. -/
lemma not_zeroTracker_of_l2 {K : Cfg} (hK : K.side = .l2) {op : Op} {S T : Router}
    (hs : AStep K op S T) : ¬ op.ZeroTracker := by
  cases hs with
  | setTracker hside => rw [hK] at hside; cases hside
  | _ => exact fun h => h

/-- L1 has no counterpart write. -/
lemma not_counterpart_of_l1 {K : Cfg} (hK : K.side = .l1) {op : Op} {S T : Router}
    (hs : AStep K op S T) : ¬ op.IsCounterpart := by
  cases hs with
  | counterpartSet hside => rw [hK] at hside; cases hside
  | _ => exact fun h => h

/-! ## (a) `RunValid` fails at the pin -/

theorem finalize_fallback_breaks_valid {K : Cfg} {R : Router} {a : AssetId}
    (h0 : R.handler a = 0) (ht : R.tracker a = 0) (hntv : K.ntv ≠ 0) (hm : K.ntvMints a)
    (hside : K.side = .l2 → a ≠ K.seedId) :
    AStep K (.finalize a) R (pointAt R a K.ntv) ∧ ¬ Valid (pointAt R a K.ntv) :=
  ⟨.finalize h0 hm hside, not_valid_pointAt hntv ht⟩

/-! ## The single-writer model inside this one -/

theorem single_writer_run_embeds (K : Cfg) {R S : Router}
    (hr : Reach K.enc K.thisChain K.ntv K.ntvAddr R S) :
    ∃ ops : List Op, ARun K R ops S ∧ ∀ op ∈ ops, ∃ caller d h, op = .register caller d h := by
  induction hr with
  | refl => exact ⟨[], .nil, fun _ hop => by cases hop⟩
  | tail _ hs ih =>
    obtain ⟨ops, hrun, hops⟩ := ih
    cases hs with
    | @setHandler caller d h hg =>
      refine ⟨ops ++ [.register caller d h], .snoc hrun (.register hg), ?_⟩
      intro op hop
      rcases List.mem_append.1 hop with h1 | h1
      · exact hops op h1
      · rw [List.mem_singleton] at h1
        exact ⟨caller, d, h, h1⟩

theorem register_only_run_reach (K : Cfg) {R S : Router} {ops : List Op}
    (hr : ARun K R ops S) (hops : ∀ op ∈ ops, ∃ caller d h, op = .register caller d h) :
    Reach K.enc K.thisChain K.ntv K.ntvAddr R S := by
  induction hr with
  | nil => exact .refl
  | @snoc S T ops op _ hs ih =>
    have hR := ih fun o ho => hops o (List.mem_append_left _ ho)
    obtain ⟨caller, d, h, rfl⟩ := hops op (List.mem_append_right _ (List.mem_singleton_self _))
    cases hs with
    | register hg => exact .tail hR (.setHandler hg)

theorem weakValid_at_zero_vault {K K' : Cfg} {R : Router} (hK : K.ntv = 0)
    (hW : WeakValid K R) : WeakValid K' R := by
  intro a ha
  rcases hW a ha with h | ⟨h1, _⟩
  · exact Or.inl h
  · exact absurd (h1.trans hK) ha

/-! ## (b) The weakened invariant -/

theorem step_preserves_weakValid {K : Cfg} (hmint : MintsOnlyNtvIds K)
    (hseed : IsNtvId K.enc K.ntvAddr K.seedId) {op : Op} {R R' : Router}
    (hs : AStep K op R R') (hc : ¬ op.IsCounterpart) (hz : ¬ op.ZeroTracker)
    (hV : WeakValid K R) : WeakValid K R' := by
  cases hs with
  | @register _ caller d h hg =>
    intro x hx
    by_cases hxw : x = writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d
    · subst hxw
      left
      rw [tracker_records_caller]
      exact hg.callerNonzero
    · exact weakAt_congr (hV x) (handler_frame _ _ _ _ _ _ _ _ _ hxw)
        (setHandler_tracker_ne _ _ _ _ _ _ _ _ hxw) hx
  | @finalize _ a _ hm _ =>
    intro x hx
    by_cases hxa : x = a
    · subst hxa
      exact Or.inr ⟨pointAt_handler_self _ _ _, hmint _ hm⟩
    · exact weakAt_congr (hV x) (pointAt_handler_ne _ _ hxa) rfl hx
  | seed =>
    intro x hx
    by_cases hxa : x = K.seedId
    · subst hxa
      exact Or.inr ⟨pointAt_handler_self _ _ _, hseed⟩
    · exact weakAt_congr (hV x) (pointAt_handler_ne _ _ hxa) rfl hx
  | counterpartSet _ => exact absurd trivial hc
  | @setTracker _ d t _ =>
    intro x hx
    by_cases hxt : x = K.enc K.thisChain t d
    · subst hxt
      left
      rw [recordTracker_tracker_self]
      exact hz
    · exact weakAt_congr (hV x) rfl (recordTracker_tracker_ne _ _ hxt) hx

theorem run_weakValid {K : Cfg} (hmint : MintsOnlyNtvIds K)
    (hseed : IsNtvId K.enc K.ntvAddr K.seedId) {ops : List Op} {R0 R : Router}
    (hr : ARun K R0 ops R) (h0 : WeakValid K R0)
    (hops : ∀ op ∈ ops, ¬ op.IsCounterpart ∧ ¬ op.ZeroTracker) : WeakValid K R := by
  induction hr with
  | nil => exact h0
  | @snoc S T ops op _ hs ih =>
    have hop := hops op (List.mem_append_right _ (List.mem_singleton_self _))
    exact step_preserves_weakValid hmint hseed hs hop.1 hop.2
      (ih fun o ho => hops o (List.mem_append_left _ ho))

theorem empty_weakValid (K : Cfg) : WeakValid K empty := fun _ h => absurd rfl h

theorem l2_run_weakValid {K : Cfg} (hK : K.side = .l2) (hmint : MintsOnlyNtvIds K)
    (hseed : IsNtvId K.enc K.ntvAddr K.seedId) {ops : List Op} {R : Router}
    (hr : ARun K empty ops R) (hops : ∀ op ∈ ops, ¬ op.IsCounterpart) : WeakValid K R :=
  run_weakValid hmint hseed hr (empty_weakValid K) fun op hop =>
    ⟨hops op hop, by
      obtain ⟨S, T, hs⟩ := hr.mem_enabled op hop
      exact not_zeroTracker_of_l2 hK hs⟩

/-! ### Logged runs -/

lemma mem_loggedTriples {K : Cfg} {ops : List Op} {p : Chain × Address × AssetData} :
    p ∈ loggedTriples K ops ↔ ∃ op ∈ ops, op.triple K = some p := by
  simp [loggedTriples, List.mem_filterMap]

lemma loggedTriples_mono {K : Cfg} {ops : List Op} {op : Op} :
    loggedTriples K ops ⊆ loggedTriples K (ops ++ [op]) := by
  intro p hp
  rw [mem_loggedTriples] at hp ⊢
  obtain ⟨o, ho, h⟩ := hp
  exact ⟨o, List.mem_append_left _ ho, h⟩

lemma mem_loggedTriples_snoc {K : Cfg} {ops : List Op} {op : Op}
    {p : Chain × Address × AssetData} (h : op.triple K = some p) :
    p ∈ loggedTriples K (ops ++ [op]) := by
  rw [mem_loggedTriples]
  exact ⟨op, List.mem_append_right _ (List.mem_singleton_self _), h⟩

lemma idInjOn_mono {enc : AssetIdOf} {S T : Set (Chain × Address × AssetData)} (hST : S ⊆ T)
    (h : IdInjOn enc T) : IdInjOn enc S :=
  fun p hp q hq he => h p (hST hp) q (hST hq) he

/-- Every nonzero tracker sits at the id of a logged triple whose sender is nonzero. -/
def TrackerProvenance (K : Cfg) (ops : List Op) (R : Router) : Prop :=
  ∀ a, R.tracker a ≠ 0 → ∃ p ∈ loggedTriples K ops, p.2.1 ≠ 0 ∧ a = K.enc p.1 p.2.1 p.2.2

lemma provenance_frame {K : Cfg} {ops : List Op} {op : Op} {S T : Router}
    (hP : TrackerProvenance K ops S) (ht : T.tracker = S.tracker) :
    TrackerProvenance K (ops ++ [op]) T := by
  intro a ha
  rw [ht] at ha
  obtain ⟨p, hp, h1, h2⟩ := hP a ha
  exact ⟨p, loggedTriples_mono hp, h1, h2⟩

theorem run_weakValid_on {K : Cfg} (hN : K.ntvAddr ≠ 0) (hmint : MintsOnlyNtvIds K)
    (hseed : IsNtvId K.enc K.ntvAddr K.seedId) {ops : List Op} {R0 R : Router}
    (hr : ARun K R0 ops R) (h0 : R0 = empty) (hops : ∀ op ∈ ops, ¬ op.IsCounterpart)
    (hinj : IdInjOn K.enc ↑(loggedTriples K ops)) :
    WeakValid K R ∧ TrackerProvenance K ops R := by
  induction hr with
  | nil =>
    subst h0
    exact ⟨empty_weakValid K, fun _ h => absurd rfl h⟩
  | @snoc S T ops op _ hs ih =>
    have hc := hops op (List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨hV, hP⟩ := ih (fun o ho => hops o (List.mem_append_left _ ho))
      (idInjOn_mono (Finset.coe_subset.2 loggedTriples_mono) hinj)
    cases hs with
    | @register _ caller d h hg =>
      refine ⟨step_preserves_weakValid hmint hseed (.register hg) hc (fun h => h) hV, ?_⟩
      intro x hx
      by_cases hxw : x = writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d
      · subst hxw
        refine ⟨(K.thisChain, senderOf K.ntv K.ntvAddr caller, d),
          mem_loggedTriples_snoc rfl, ?_, rfl⟩
        by_cases hcn : caller = K.ntv
        · subst hcn
          rw [senderOf_self]
          exact hN
        · rw [senderOf_ne hcn]
          exact hg.callerNonzero
      · rw [setHandler_tracker_ne _ _ _ _ _ _ _ _ hxw] at hx
        obtain ⟨p, hp, h1, h2⟩ := hP x hx
        exact ⟨p, loggedTriples_mono hp, h1, h2⟩
    | @finalize _ a h0' hm hside =>
      exact ⟨step_preserves_weakValid hmint hseed (.finalize h0' hm hside) hc (fun h => h) hV,
        provenance_frame hP rfl⟩
    | seed =>
      exact ⟨step_preserves_weakValid hmint hseed .seed hc (fun h => h) hV, provenance_frame hP rfl⟩
    | counterpartSet _ => exact absurd trivial hc
    | @setTracker _ d t hside =>
      by_cases ht0 : t = 0
      · subst ht0
        -- Under the premise, the zero write hits a zero tracker: it writes nothing.
        have hz : S.tracker (K.enc K.thisChain 0 d) = 0 := by
          by_contra hne
          obtain ⟨p, hp, h1, h2⟩ := hP _ hne
          have hq : ((K.thisChain, (0 : Address), d) : Chain × Address × AssetData) ∈
              loggedTriples K (ops ++ [.setTracker d 0]) := mem_loggedTriples_snoc rfl
          have := hinj p (Finset.mem_coe.2 (loggedTriples_mono hp)) _ (Finset.mem_coe.2 hq)
            h2.symm
          exact h1 (by rw [this])
        have htr : (recordTracker K S d 0).tracker = S.tracker := by
          funext x
          by_cases hx : x = K.enc K.thisChain 0 d
          · subst hx
            rw [recordTracker_tracker_self, hz]
          · exact recordTracker_tracker_ne _ _ hx
        refine ⟨fun x hx => weakAt_congr (hV x) rfl (congrFun htr x) hx, provenance_frame hP htr⟩
      · refine ⟨step_preserves_weakValid hmint hseed (.setTracker hside) hc ht0 hV, ?_⟩
        intro x hx
        by_cases hxt : x = K.enc K.thisChain t d
        · subst hxt
          exact ⟨(K.thisChain, t, d), mem_loggedTriples_snoc rfl, ht0, rfl⟩
        · rw [recordTracker_tracker_ne _ _ hxt] at hx
          obtain ⟨p, hp, h1, h2⟩ := hP x hx
          exact ⟨p, loggedTriples_mono hp, h1, h2⟩

theorem l1_run_weakValid_on {K : Cfg} (hK : K.side = .l1) (hN : K.ntvAddr ≠ 0)
    (hmint : MintsOnlyNtvIds K) (hseed : IsNtvId K.enc K.ntvAddr K.seedId) {ops : List Op}
    {R : Router} (hr : ARun K empty ops R) (hinj : IdInjOn K.enc ↑(loggedTriples K ops)) :
    WeakValid K R :=
  (run_weakValid_on hN hmint hseed hr rfl (fun op hop => by
      obtain ⟨S, T, hs⟩ := hr.mem_enabled op hop
      exact not_counterpart_of_l1 hK hs) hinj).1

theorem loggedTriples_card_le (K : Cfg) (ops : List Op) :
    (loggedTriples K ops).card ≤ ops.length :=
  (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

theorem logged_premise_satisfiable (K : Cfg) (ops : List Op) (h : ops.length ≤ UInt256.size) :
    ∃ enc : AssetIdOf, IdInjOn enc ↑(loggedTriples K ops) :=
  idInjOn_of_card _ ((loggedTriples_card_le K ops).trans h)

/-! ## (c) Who can re-point a route -/

theorem all_writers_frame {K : Cfg} {op : Op} {R R' : Router} (hs : AStep K op R R')
    (x : AssetId) (hx : R'.handler x ≠ R.handler x) : op.target K = some x := by
  cases hs with
  | @register _ caller d h _ =>
    by_cases hxw : x = writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d
    · subst hxw; rfl
    · exact absurd (handler_frame _ _ _ _ _ _ _ _ _ hxw) hx
  | @finalize _ a _ _ _ =>
    by_cases hxa : x = a
    · subst hxa; rfl
    · exact absurd (pointAt_handler_ne _ _ hxa) hx
  | seed =>
    by_cases hxa : x = K.seedId
    · subst hxa; rfl
    · exact absurd (pointAt_handler_ne _ _ hxa) hx
  | @counterpartSet _ a _ _ =>
    by_cases hxa : x = a
    · subst hxa; rfl
    · exact absurd (pointAt_handler_ne _ _ hxa) hx
  | setTracker _ => exact absurd rfl hx

theorem finalize_leaves_live_routes {K : Cfg} {a : AssetId} {R R' : Router}
    (hs : AStep K (.finalize a) R R') (x : AssetId) (hx : R.handler x ≠ 0) :
    R'.handler x = R.handler x := by
  cases hs with
  | finalize h0 _ _ =>
    have hxa : x ≠ a := fun h => hx (h ▸ h0)
    exact pointAt_handler_ne _ _ hxa

/-- A call's target is the id of every triple it is hashed from. -/
lemma target_eq_of_hashedFrom {K : Cfg} {op : Op} {p : Chain × Address × AssetData}
    {x : AssetId} (hp : op.HashedFrom K p) (ht : op.target K = some x) :
    x = K.enc p.1 p.2.1 p.2.2 := by
  cases op with
  | register caller d h =>
    simp only [Op.HashedFrom] at hp
    subst hp
    simp only [Op.target, Option.some.injEq] at ht
    rw [← ht]
    rfl
  | finalize a =>
    simp only [Op.target, Option.some.injEq] at ht
    rw [← ht]
    exact hp.2
  | seed =>
    simp only [Op.target, Option.some.injEq] at ht
    rw [← ht]
    exact hp.2
  | counterpartSet a h => exact hp.elim
  | setTracker d t => simp [Op.target] at ht

theorem no_hijack_on_except_counterpart {K : Cfg} (hmint : MintsOnlyNtvIds K)
    (hseed : IsNtvId K.enc K.ntvAddr K.seedId) {op : Op} {R R' : Router}
    (hs : AStep K op R R') (hc : ¬ op.IsCounterpart) :
    (∃ p, op.HashedFrom K p) ∧
    ∀ (p : Chain × Address × AssetData) (c : Chain) (s : Address) (d' : AssetData),
      op.HashedFrom K p → s ≠ p.2.1 → IdInjOn K.enc {p, (c, s, d')} →
        R'.handler (K.enc c s d') = R.handler (K.enc c s d') := by
  refine ⟨?_, ?_⟩
  · cases hs with
    | @register _ caller d h _ => exact ⟨_, rfl⟩
    | @finalize _ a _ hm _ =>
      obtain ⟨c₀, d₀, he⟩ := hmint a hm
      exact ⟨(c₀, K.ntvAddr, d₀), rfl, he⟩
    | seed =>
      obtain ⟨c₀, d₀, he⟩ := hseed
      exact ⟨(c₀, K.ntvAddr, d₀), rfl, he⟩
    | counterpartSet _ => exact absurd trivial hc
    | @setTracker _ d t _ => exact ⟨_, rfl⟩
  · intro p c s d' hp hsp hinj
    by_contra hne
    have hx := target_eq_of_hashedFrom hp (all_writers_frame hs _ hne)
    have := hinj p (Set.mem_insert _ _) (c, s, d') (Set.mem_insert_of_mem _ rfl) hx.symm
    exact hsp (by rw [this])

theorem l2_only_vault_registers {K : Cfg} (hK : K.side = .l2) {ops : List Op} {R0 R : Router}
    (hr : ARun K R0 ops R) (h0 : ∀ a, R0.tracker a = 0 ∨ R0.tracker a = K.ntv) :
    (∀ a, R.tracker a = 0 ∨ R.tracker a = K.ntv) ∧
    ∀ (caller : Address) (d : AssetData) (h : Address), Op.register caller d h ∈ ops →
      caller = K.ntv := by
  induction hr with
  | nil => exact ⟨h0, fun _ _ _ hm => by cases hm⟩
  | @snoc S T ops op _ hs ih =>
    obtain ⟨hT, hreg⟩ := ih
    have old : ∀ (caller : Address) (d : AssetData) (h : Address),
        Op.register caller d h ∈ ops ++ [op] → op ≠ Op.register caller d h → caller = K.ntv := by
      intro caller d h hm hne
      rcases List.mem_append.1 hm with hm | hm
      · exact hreg caller d h hm
      · rw [List.mem_singleton] at hm
        exact absurd hm.symm hne
    cases hs with
    | @register _ caller d h hg =>
      have hcn : caller = K.ntv := by
        rcases hg.authorized with h1 | h1
        · exact h1
        · rcases hT (writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d) with h2 | h2
          · exact absurd (h1.trans h2) hg.callerNonzero
          · exact h1.trans h2
      refine ⟨fun a => ?_, fun c' d' h' hm => ?_⟩
      · by_cases ha : a = writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d
        · subst ha
          rw [tracker_records_caller]
          exact Or.inr hcn
        · rw [setHandler_tracker_ne _ _ _ _ _ _ _ _ ha]
          exact hT a
      · by_cases he : Op.register caller d h = Op.register c' d' h'
        · cases he
          exact hcn
        · exact old c' d' h' hm he
    | finalize _ _ _ =>
      exact ⟨hT, fun c' d' h' hm => old c' d' h' hm (by intro h; cases h)⟩
    | seed =>
      exact ⟨hT, fun c' d' h' hm => old c' d' h' hm (by intro h; cases h)⟩
    | counterpartSet _ =>
      exact ⟨hT, fun c' d' h' hm => old c' d' h' hm (by intro h; cases h)⟩
    | setTracker hside => rw [hK] at hside; cases hside

theorem run_trackerHashed {K : Cfg} {ops : List Op} {R0 R : Router} (hr : ARun K R0 ops R)
    (h0 : TrackerHashed K R0) : TrackerHashed K R := by
  induction hr with
  | nil => exact h0
  | @snoc S T ops op _ hs ih =>
    have hS := ih
    cases hs with
    | @register _ caller d h _ =>
      intro x hx
      by_cases hxw : x = writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d
      · subst hxw
        rw [tracker_records_caller]
        by_cases hcn : caller = K.ntv
        · subst hcn
          exact ⟨d, Or.inr ⟨rfl, by simp [writtenId]⟩⟩
        · exact ⟨d, Or.inl (by simp [writtenId, senderOf_ne hcn])⟩
      · rw [setHandler_tracker_ne _ _ _ _ _ _ _ _ hxw] at hx ⊢
        exact hS x hx
    | finalize _ _ _ => exact hS
    | seed => exact hS
    | counterpartSet _ => exact hS
    | @setTracker _ d t _ =>
      intro x hx
      by_cases hxt : x = K.enc K.thisChain t d
      · subst hxt
        rw [recordTracker_tracker_self]
        exact ⟨d, Or.inl rfl⟩
      · rw [recordTracker_tracker_ne _ _ hxt] at hx ⊢
        exact hS x hx

theorem empty_trackerHashed (K : Cfg) : TrackerHashed K empty := fun _ h => absurd rfl h

theorem l2_only_counterpart_touches_non_vault_ids {K : Cfg} (hK : K.side = .l2)
    (hmint : MintsOnlyNtvIds K) (hseed : IsNtvId K.enc K.ntvAddr K.seedId)
    {ops : List Op} {R : Router} {op : Op} {R' : Router}
    (hr : ARun K empty ops R) (hs : AStep K op R R') (hc : ¬ op.IsCounterpart)
    (x : AssetId) (hx : R'.handler x ≠ R.handler x) : IsNtvId K.enc K.ntvAddr x := by
  have ht := all_writers_frame hs x hx
  have hT := (l2_only_vault_registers hK hr (fun _ => Or.inl rfl)).1
  cases hs with
  | @register _ caller d h hg =>
    have hcn : caller = K.ntv := by
      rcases hg.authorized with h1 | h1
      · exact h1
      · rcases hT (writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d) with h2 | h2
        · exact absurd (h1.trans h2) hg.callerNonzero
        · exact h1.trans h2
    subst hcn
    simp only [Op.target, Option.some.injEq] at ht
    exact ⟨K.thisChain, d, by rw [← ht]; simp [writtenId]⟩
  | @finalize _ a _ hm _ =>
    simp only [Op.target, Option.some.injEq] at ht
    subst ht
    exact hmint _ hm
  | seed =>
    simp only [Op.target, Option.some.injEq] at ht
    subst ht
    exact hseed
  | counterpartSet _ => exact absurd trivial hc
  | setTracker hside => rw [hK] at hside; cases hside

/-! ## Concrete configurations for the witnesses and countermodels -/

/-- Witness encoding.  A triple whose sender is `8` (the vault sender) gets one of the
three vault ids `100`, `101`, `102` (by data `0`, `1`, anything else).  Any other
triple gets its sender as id. -/
def wEnc : AssetIdOf := fun _ s d =>
  if s = 8 then (if d = 0 then 100 else if d = 1 then 101 else 102) else s

/-- An L1 router: chain `1`, vault `9`, vault sender `8`, seeded id `101` (`ETH`), and a
vault that mints exactly the vault ids. -/
def wK1 : Cfg :=
  { enc := wEnc, thisChain := 1, ntv := 9, ntvAddr := 8, side := .l1, seedId := 101,
    ntvMints := IsNtvId wEnc 8 }

/-- An L2 router: chain `2`, vault = vault sender = `8`, seeded base-token id `101`. -/
def wK2 : Cfg :=
  { enc := wEnc, thisChain := 2, ntv := 8, ntvAddr := 8, side := .l2, seedId := 101,
    ntvMints := IsNtvId wEnc 8 }

lemma isNtv_100 : IsNtvId wEnc 8 100 := ⟨0, 0, by decide⟩
lemma isNtv_101 : IsNtvId wEnc 8 101 := ⟨0, 1, by decide⟩
lemma isNtv_102 : IsNtvId wEnc 8 102 := ⟨0, 2, by decide⟩

lemma not_isNtv_5 : ¬ IsNtvId wEnc 8 5 := by
  rintro ⟨c, d, h⟩
  simp only [wEnc, ite_true] at h
  split_ifs at h <;> exact absurd h (by decide)

lemma wK1_mints : MintsOnlyNtvIds wK1 := fun _ h => h
lemma wK2_mints : MintsOnlyNtvIds wK2 := fun _ h => h

/-! ### The L1 run: seed, owner tracker write, custom registration, fallback -/

/-- `setNativeTokenVault`: `ETH` (id `101`) → vault `9`. -/
def s1 : Router := pointAt empty 101 9
/-- The owner records `5` as tracker of `enc 1 5 3 = 5`. -/
def s2 : Router := recordTracker wK1 s1 3 5
/-- Tracker `5` registers handler `7` for data `3`: id `5`. -/
def s3 : Router := setHandler wEnc 1 9 8 s2 5 3 7
/-- A fallback deposit for the vault id `100`. -/
def s4 : Router := pointAt s3 100 9
/-- The owner writes the zero tracker for data `4`: id `enc 1 0 4 = 0`. -/
def s5 : Router := recordTracker wK1 s4 4 0

def ops1 : List Op := [.seed, .setTracker 3 5, .register 5 3 7, .finalize 100]

lemma run1 : ARun wK1 empty ops1 s4 := by
  have g3 : SetGuard wEnc 1 9 8 s2 5 3 := ⟨Or.inr (by decide), by decide⟩
  exact ((((ARun.nil).snoc AStep.seed).snoc (AStep.setTracker rfl)).snoc
    (AStep.register g3)).snoc (AStep.finalize (by decide) isNtv_100 (fun h => by cases h))

lemma run1' : ARun wK1 empty (ops1 ++ [.setTracker 4 0]) s5 :=
  run1.snoc (AStep.setTracker rfl)

/-! ### The L2 run: seed, vault registration, fallback -/

/-- `initL2`: base token (id `101`) → vault `8`. -/
def t1 : Router := pointAt empty 101 8
/-- The vault registers its token `0`: id `enc 2 8 0 = 100`. -/
def t2 : Router := setHandler wEnc 2 8 8 t1 8 0 8
/-- A fallback deposit for the vault id `102`. -/
def t3 : Router := pointAt t2 102 8

def ops2 : List Op := [.seed, .register 8 0 8, .finalize 102]

lemma run2 : ARun wK2 empty ops2 t3 := by
  have g2 : SetGuard wEnc 2 8 8 t1 8 0 := ⟨Or.inl rfl, by decide⟩
  exact (((ARun.nil).snoc AStep.seed).snoc (AStep.register g2)).snoc
    (AStep.finalize (by decide) isNtv_102 (fun _ => by decide))

/-! ### The colliding L1 run: tracker, registration, zero-tracker write -/

/-- `constEnc` (every triple → `1`) with an L1 router. -/
def cK : Cfg :=
  { enc := constEnc, thisChain := 1, ntv := 9, ntvAddr := 8, side := .l1, seedId := 1,
    ntvMints := IsNtvId constEnc 8 }

def c1 : Router := recordTracker cK empty 3 5
def c2 : Router := setHandler constEnc 1 9 8 c1 5 3 7
def c3 : Router := recordTracker cK c2 4 0

def opsC : List Op := [.setTracker 3 5, .register 5 3 7, .setTracker 4 0]

lemma runC : ARun cK empty opsC c3 := by
  have g : SetGuard constEnc 1 9 8 c1 5 3 := ⟨Or.inr (by decide), by decide⟩
  exact (((ARun.nil).snoc (AStep.setTracker rfl)).snoc (AStep.register g)).snoc
    (AStep.setTracker rfl)

/-! ### Witnesses -/

theorem run_valid_fails_after_one_deposit (side : Side) :
    ∃ (K : Cfg) (a : AssetId) (R : Router),
      K.side = side ∧ K.ntv ≠ 0 ∧ MintsOnlyNtvIds K ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧
      ARun K empty [.finalize a] R ∧ ¬ Valid R ∧ WeakValid K R := by
  cases side with
  | l1 =>
    exact ⟨wK1, 100, pointAt empty 100 9, rfl, by decide, wK1_mints, isNtv_101,
      (ARun.nil).snoc (AStep.finalize rfl isNtv_100 (fun h => by cases h)),
      not_valid_pointAt (by decide) rfl, weakValid_pointAt_empty (K := wK1) isNtv_100⟩
  | l2 =>
    exact ⟨wK2, 100, pointAt empty 100 8, rfl, by decide, wK2_mints, isNtv_101,
      (ARun.nil).snoc (AStep.finalize rfl isNtv_100 (fun _ => by decide)),
      not_valid_pointAt (by decide) rfl, weakValid_pointAt_empty (K := wK2) isNtv_100⟩

theorem seed_and_counterpart_break_valid :
    (∃ (K : Cfg) (R : Router), K.side = .l1 ∧ K.ntv ≠ 0 ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧
        ARun K empty [.seed] R ∧ ¬ Valid R) ∧
    (∃ (K : Cfg) (R : Router), K.side = .l2 ∧ K.ntv ≠ 0 ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧
        ARun K empty [.seed] R ∧ ¬ Valid R) ∧
    (∃ (K : Cfg) (a : AssetId) (h : Address) (R : Router), K.side = .l2 ∧
        ARun K empty [.counterpartSet a h] R ∧ ¬ Valid R) :=
  ⟨⟨wK1, pointAt empty 101 9, rfl, by decide, isNtv_101, (ARun.nil).snoc AStep.seed,
      not_valid_pointAt (by decide) rfl⟩,
    ⟨wK2, pointAt empty 101 8, rfl, by decide, isNtv_101, (ARun.nil).snoc AStep.seed,
      not_valid_pointAt (by decide) rfl⟩,
    ⟨wK2, 5, 7, pointAt empty 5 7, rfl, (ARun.nil).snoc (AStep.counterpartSet rfl),
      not_valid_pointAt (by decide) rfl⟩⟩

lemma ops1_clean : ∀ op ∈ ops1, ¬ op.IsCounterpart ∧ ¬ op.ZeroTracker := by
  intro op hop
  simp only [ops1, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl
  · exact ⟨fun h => h, fun h => h⟩
  · exact ⟨fun h => h, fun h => absurd (show (5 : Address) = 0 from h) (by decide)⟩
  · exact ⟨fun h => h, fun h => h⟩
  · exact ⟨fun h => h, fun h => h⟩

lemma ops2_clean : ∀ op ∈ ops2, ¬ op.IsCounterpart ∧ ¬ op.ZeroTracker := by
  intro op hop
  simp only [ops2, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl <;> exact ⟨fun h => h, fun h => h⟩

theorem run_weakValid_witness (side : Side) :
    ∃ (K : Cfg) (ops : List Op) (R : Router),
      K.side = side ∧ MintsOnlyNtvIds K ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧
      ARun K empty ops R ∧ (∀ op ∈ ops, ¬ op.IsCounterpart ∧ ¬ op.ZeroTracker) ∧
      Op.seed ∈ ops ∧ (∃ caller d h, Op.register caller d h ∈ ops) ∧
      (∃ a, Op.finalize a ∈ ops) ∧
      (side = .l1 → ∃ d t h, Op.setTracker d t ∈ ops ∧ Op.register t d h ∈ ops ∧ t ≠ K.ntv) ∧
      ¬ Valid R := by
  cases side with
  | l1 =>
    refine ⟨wK1, ops1, s4, rfl, wK1_mints, isNtv_101, run1, ops1_clean, by simp [ops1],
      ⟨5, 3, 7, by simp [ops1]⟩, ⟨100, by simp [ops1]⟩,
      fun _ => ⟨3, 5, 7, by simp [ops1], by simp [ops1], by decide⟩, ?_⟩
    exact fun hV => hV 100 (by decide) (by decide)
  | l2 =>
    refine ⟨wK2, ops2, t3, rfl, wK2_mints, isNtv_101, run2, ops2_clean, by simp [ops2],
      ⟨8, 0, 8, by simp [ops2]⟩, ⟨102, by simp [ops2]⟩, (fun h => by cases h), ?_⟩
    exact fun hV => hV 102 (by decide) (by decide)

/-- The triples run `run1'` logs. -/
lemma loggedTriples_run1'_sub :
    (↑(loggedTriples wK1 (ops1 ++ [.setTracker 4 0])) : Set (Chain × Address × AssetData)) ⊆
      {((1 : Chain), (5 : Address), (3 : AssetData)), (1, 0, 4)} := by
  intro p hp
  rw [Finset.mem_coe, mem_loggedTriples] at hp
  obtain ⟨op, hop, hpop⟩ := hp
  simp only [ops1, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl
  · simp [Op.triple] at hpop
  · simp only [Op.triple, Option.some.injEq] at hpop
    subst hpop
    exact Set.mem_insert _ _
  · simp only [Op.triple, Option.some.injEq] at hpop
    subst hpop
    rw [show senderOf wK1.ntv wK1.ntvAddr 5 = 5 from senderOf_ne (by decide)]
    exact Set.mem_insert _ _
  · simp [Op.triple] at hpop
  · simp only [Op.triple, Option.some.injEq] at hpop
    subst hpop
    exact Set.mem_insert_of_mem _ rfl

theorem run_weakValid_on_witness :
    ∃ (K : Cfg) (ops : List Op) (R : Router),
      K.side = .l1 ∧ K.ntvAddr ≠ 0 ∧ MintsOnlyNtvIds K ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧
      ARun K empty ops R ∧ IdInjOn K.enc ↑(loggedTriples K ops) ∧
      (∃ op ∈ ops, op.ZeroTracker) ∧
      (∃ p ∈ loggedTriples K ops, ∃ q, q ∉ loggedTriples K ops ∧
          K.enc p.1 p.2.1 p.2.2 = K.enc q.1 q.2.1 q.2.2) ∧
      ¬ Valid R := by
  refine ⟨wK1, ops1 ++ [.setTracker 4 0], s5, rfl, by decide, wK1_mints, isNtv_101, run1',
    idInjOn_mono loggedTriples_run1'_sub (idInjOn_pair (by decide)),
    ⟨.setTracker 4 0, by simp, rfl⟩,
    ⟨(1, 5, 3), mem_loggedTriples.2 ⟨.setTracker 3 5, by simp [ops1], rfl⟩, (1, 5, 99), ?_,
      by decide⟩, ?_⟩
  · intro hq
    have := loggedTriples_run1'_sub (Finset.mem_coe.2 hq)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h <;> exact absurd h (by decide)
  · exact fun hV => hV 100 (by decide) (by decide)

theorem counterpart_breaks_weakValid {K : Cfg} {R : Router} {a : AssetId} {h : Address}
    (hK : K.side = .l2) (ht : R.tracker a = 0) (h0 : h ≠ 0) (hv : h ≠ K.ntv) :
    AStep K (.counterpartSet a h) R (pointAt R a h) ∧ ¬ WeakValid K (pointAt R a h) := by
  refine ⟨.counterpartSet hK, fun hW => ?_⟩
  rcases hW a (by rw [pointAt_handler_self]; exact h0) with h1 | ⟨h1, _⟩
  · exact h1 ht
  · rw [pointAt_handler_self] at h1
    exact hv h1

theorem zero_tracker_breaks_weakValid_under_collision :
    ∃ (K : Cfg) (ops : List Op) (R : Router),
      K.side = .l1 ∧ K.ntvAddr ≠ 0 ∧ MintsOnlyNtvIds K ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧
      ARun K empty ops R ∧ (∀ op ∈ ops, ¬ op.IsCounterpart) ∧ (∃ op ∈ ops, op.ZeroTracker) ∧
      ¬ IdInjOn K.enc ↑(loggedTriples K ops) ∧ ¬ WeakValid K R := by
  refine ⟨cK, opsC, c3, rfl, by decide, fun _ h => h, ⟨0, 0, rfl⟩, runC, ?_,
    ⟨.setTracker 4 0, by simp [opsC], rfl⟩, ?_, ?_⟩
  · intro op hop
    simp only [opsC, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl <;> exact fun h => h
  · intro hinj
    have h1 : ((1 : Chain), (5 : Address), (3 : AssetData)) ∈ loggedTriples cK opsC :=
      mem_loggedTriples.2 ⟨.setTracker 3 5, by simp [opsC], rfl⟩
    have h2 : ((1 : Chain), (0 : Address), (4 : AssetData)) ∈ loggedTriples cK opsC :=
      mem_loggedTriples.2 ⟨.setTracker 4 0, by simp [opsC], rfl⟩
    exact absurd (hinj _ (Finset.mem_coe.2 h1) _ (Finset.mem_coe.2 h2) rfl) (by decide)
  · intro hW
    rcases hW 1 (by decide) with h | ⟨h, _⟩
    · exact h (by decide)
    · exact absurd h (by decide)

theorem non_vault_mint_breaks_weakValid :
    ∃ (K : Cfg) (a : AssetId) (R : Router),
      K.ntv ≠ 0 ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧ K.ntvMints a ∧
      ¬ IsNtvId K.enc K.ntvAddr a ∧ ARun K empty [.finalize a] R ∧ ¬ WeakValid K R := by
  refine ⟨{ wK1 with ntvMints := fun a => a = 5 }, 5, pointAt empty 5 9, by decide, isNtv_101,
    rfl, not_isNtv_5, (ARun.nil).snoc (AStep.finalize rfl rfl (fun h => by cases h)), ?_⟩
  intro hW
  rcases hW 5 (by decide) with h | ⟨_, h⟩
  · exact h rfl
  · exact not_isNtv_5 h

theorem non_vault_seed_breaks_weakValid :
    ∃ (K : Cfg) (R : Router), K.side = .l2 ∧ K.ntv ≠ 0 ∧ MintsOnlyNtvIds K ∧
      ¬ IsNtvId K.enc K.ntvAddr K.seedId ∧ ARun K empty [.seed] R ∧ ¬ WeakValid K R := by
  refine ⟨{ wK2 with seedId := 5 }, pointAt empty 5 8, rfl, by decide, fun _ h => h, not_isNtv_5,
    (ARun.nil).snoc AStep.seed, ?_⟩
  intro hW
  rcases hW 5 (by decide) with h | ⟨_, h⟩
  · exact h rfl
  · exact not_isNtv_5 h

/-- The custom route of the L1 run, before the fallback. -/
def n2 : Router := setHandler wEnc 1 9 8 (recordTracker wK1 empty 3 5) 5 3 7

theorem no_hijack_on_except_counterpart_witness :
    ∃ (K : Cfg) (ops : List Op) (R R' : Router) (a : AssetId)
      (p : Chain × Address × AssetData) (c : Chain) (s : Address) (d' : AssetData),
      MintsOnlyNtvIds K ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧ ARun K empty ops R ∧
      AStep K (.finalize a) R R' ∧ (Op.finalize a).HashedFrom K p ∧ s ≠ p.2.1 ∧
      IdInjOn K.enc {p, (c, s, d')} ∧ R.handler (K.enc c s d') ≠ 0 := by
  have g : SetGuard wEnc 1 9 8 (recordTracker wK1 empty 3 5) 5 3 := ⟨Or.inr (by decide), by decide⟩
  refine ⟨wK1, [.setTracker 3 5, .register 5 3 7], n2, pointAt n2 100 9, 100, (0, 8, 0), 1, 5, 3,
    wK1_mints, isNtv_101, ((ARun.nil).snoc (AStep.setTracker rfl)).snoc (AStep.register g),
    AStep.finalize (by decide) isNtv_100 (fun h => by cases h), ⟨rfl, by decide⟩, by decide,
    idInjOn_pair (by decide), by decide⟩

/-- The vault's own registration on the L2 router. -/
def v1 : Router := setHandler wEnc 2 8 8 empty 8 0 8

theorem l2_only_counterpart_touches_non_vault_ids_witness :
    ∃ (K : Cfg) (ops : List Op) (R : Router) (op : Op) (R' : Router) (x : AssetId),
      K.side = .l2 ∧ MintsOnlyNtvIds K ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧
      ARun K empty ops R ∧ AStep K op R R' ∧ ¬ op.IsCounterpart ∧
      R'.handler x ≠ R.handler x := by
  have g2 : SetGuard wEnc 2 8 8 t1 8 0 := ⟨Or.inl rfl, by decide⟩
  exact ⟨wK2, [.seed], t1, .register 8 0 8, t2, 100, rfl, wK2_mints, isNtv_101,
    (ARun.nil).snoc AStep.seed, AStep.register g2, fun h => h, by decide⟩

theorem counterpart_repoints_vault_route :
    ∃ (K : Cfg) (ops : List Op) (R R' : Router) (a : AssetId) (h : Address),
      K.side = .l2 ∧ K.ntv = K.ntvAddr ∧ MintsOnlyNtvIds K ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧
      ARun K empty ops R ∧ (∀ op ∈ ops, ¬ op.IsCounterpart) ∧
      VaultRoute K R a ∧ R.tracker a = K.ntv ∧
      AStep K (.counterpartSet a h) R R' ∧ R'.handler a = h ∧ h ≠ 0 ∧ h ≠ K.ntv := by
  have g : SetGuard wEnc 2 8 8 empty 8 0 := ⟨Or.inl rfl, by decide⟩
  refine ⟨wK2, [.register 8 0 8], v1, pointAt v1 100 7, 100, 7, rfl, rfl, wK2_mints, isNtv_101,
    (ARun.nil).snoc (AStep.register g), ?_, ⟨by decide, isNtv_100⟩, by decide,
    AStep.counterpartSet rfl, pointAt_handler_self _ _ _, by decide, by decide⟩
  intro op hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  subst hop
  exact fun h => h

end Contracts.AssetRouter.AllWriters

/-! ## Certificates -/

namespace Contracts.AssetRouter.AllWriters

theorem FinalizeFallbackBreaksValid : Properties.FinalizeFallbackBreaksValid :=
  fun _ _ _ h0 ht hntv hm hside => finalize_fallback_breaks_valid h0 ht hntv hm hside

theorem RunValidFailsAfterOneDeposit : Properties.RunValidFailsAfterOneDeposit :=
  run_valid_fails_after_one_deposit

theorem AllWritersRunValidFalse : Properties.AllWritersRunValidFalse := by
  intro h
  obtain ⟨K, a, R, _, _, _, _, hr, hnv, _⟩ := run_valid_fails_after_one_deposit .l1
  exact hnv (h K _ R hr)

theorem SeedAndCounterpartBreakValid : Properties.SeedAndCounterpartBreakValid :=
  seed_and_counterpart_break_valid

theorem SingleWriterIsRegisterOnlyFragment : Properties.SingleWriterIsRegisterOnlyFragment :=
  fun K _ _ => ⟨single_writer_run_embeds K,
    fun ⟨_, hr, hops⟩ => register_only_run_reach K hr hops⟩

theorem ValidImpliesWeakValid : Properties.ValidImpliesWeakValid :=
  fun _ _ hV a h => Or.inl (hV a h)

theorem WeakValidAtZeroVault : Properties.WeakValidAtZeroVault :=
  fun _ _ _ hK hW => weakValid_at_zero_vault hK hW

theorem StepPreservesWeakValid : Properties.StepPreservesWeakValid :=
  fun _ hmint hseed _ _ _ hs hc hz hV => step_preserves_weakValid hmint hseed hs hc hz hV

theorem RunWeakValid : Properties.RunWeakValid :=
  fun K hmint hseed _ _ hr hops => run_weakValid hmint hseed hr (empty_weakValid K) hops

theorem L2RunWeakValid : Properties.L2RunWeakValid :=
  fun _ hK hmint hseed _ _ hr hops => l2_run_weakValid hK hmint hseed hr hops

theorem RunWeakValidOn : Properties.RunWeakValidOn :=
  fun _ hN hmint hseed _ _ hr hops hinj => (run_weakValid_on hN hmint hseed hr rfl hops hinj).1

theorem L1RunWeakValidOn : Properties.L1RunWeakValidOn :=
  fun _ hK hN hmint hseed _ _ hr hinj => l1_run_weakValid_on hK hN hmint hseed hr hinj

theorem LoggedTriplesCardLe : Properties.LoggedTriplesCardLe := loggedTriples_card_le

theorem LoggedPremiseSatisfiable : Properties.LoggedPremiseSatisfiable :=
  logged_premise_satisfiable

theorem RunWeakValidWitness : Properties.RunWeakValidWitness := run_weakValid_witness

theorem RunWeakValidOnWitness : Properties.RunWeakValidOnWitness := run_weakValid_on_witness

theorem CounterpartBreaksWeakValid : Properties.CounterpartBreaksWeakValid :=
  fun _ _ _ _ hK ht h0 hv => counterpart_breaks_weakValid hK ht h0 hv

theorem ZeroTrackerBreaksWeakValidUnderCollision :
    Properties.ZeroTrackerBreaksWeakValidUnderCollision :=
  zero_tracker_breaks_weakValid_under_collision

theorem NonVaultMintBreaksWeakValid : Properties.NonVaultMintBreaksWeakValid :=
  non_vault_mint_breaks_weakValid

theorem NonVaultSeedBreaksWeakValid : Properties.NonVaultSeedBreaksWeakValid :=
  non_vault_seed_breaks_weakValid

theorem AllWritersFrame : Properties.AllWritersFrame :=
  fun _ _ _ _ hs x hx => all_writers_frame hs x hx

theorem FinalizeLeavesLiveRoutes : Properties.FinalizeLeavesLiveRoutes :=
  fun _ _ _ _ hs x hx => finalize_leaves_live_routes hs x hx

theorem NoHijackOnExceptCounterpart : Properties.NoHijackOnExceptCounterpart :=
  fun _ hmint hseed _ _ _ hs hc => no_hijack_on_except_counterpart hmint hseed hs hc

theorem NoHijackOnExceptCounterpartWitness : Properties.NoHijackOnExceptCounterpartWitness :=
  no_hijack_on_except_counterpart_witness

theorem CounterpartRepointsAnyRoute : Properties.CounterpartRepointsAnyRoute :=
  fun _ R a h hK => ⟨pointAt R a h, .counterpartSet hK, pointAt_handler_self _ _ _,
    fun _ hx => pointAt_handler_ne _ _ hx⟩

theorem CounterpartRepointsVaultRoute : Properties.CounterpartRepointsVaultRoute :=
  counterpart_repoints_vault_route

theorem L2OnlyCounterpartTouchesNonVaultIds :
    Properties.L2OnlyCounterpartTouchesNonVaultIds :=
  fun _ hK hmint hseed _ _ _ _ hr hs hc x hx =>
    l2_only_counterpart_touches_non_vault_ids hK hmint hseed hr hs hc x hx

theorem L2OnlyCounterpartTouchesNonVaultIdsWitness :
    Properties.L2OnlyCounterpartTouchesNonVaultIdsWitness :=
  l2_only_counterpart_touches_non_vault_ids_witness

theorem L2OnlyVaultRegisters : Properties.L2OnlyVaultRegisters :=
  fun _ hK _ _ hr => l2_only_vault_registers hK hr (fun _ => Or.inl rfl)

theorem RunTrackerHashed : Properties.RunTrackerHashed :=
  fun K _ _ hr => run_trackerHashed hr (empty_trackerHashed K)

end Contracts.AssetRouter.AllWriters
