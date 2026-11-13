import EraSpec.Contracts.AssetRouterBase.Properties.AllWritersStrong
import EraSpec.Contracts.AssetRouterBase.Proofs.CounterpartGate

/-!
# Proofs: where each deployment tracker came from, pinned to the run's log

Proofs of `EraSpec.Contracts.AssetRouterBase.Properties.AllWritersStrong`.

One observation does the work.  A successful call changes the tracker mapping exactly as
`trackerAfterOp` of the call alone says (`aws_step_tracker`): the guard decides whether the
call happens, not what it writes.  From that:

* `aws_run_trackerRecorded` is an induction on the run, as `run_trackerSource` in
  `Proofs/CounterpartGate.lean` is, but it keeps the call, not only its triple.
* `aws_run_tracker_is_log_replay` folds `aws_step_tracker` along the run.
* `aws_run_tracker_last_own_write` is the same induction at one id `enc q`.  A logged
  write to another triple hits another id, because there is no logged clash at `q`.
* The clash form, the victim form and the card bound read the logged triple off
  `TrackerRecorded` (`aws_trackerRecorded_triple`).
-/

namespace Contracts.AssetRouter.AllWriters

/-! ## One call -/

/-- **A successful call writes the tracker mapping as `trackerAfterOp` says.** -/
lemma aws_step_tracker {K : Cfg} {op : Op} {S T : Router} (hs : AStep K op S T) :
    T.tracker = trackerAfterOp K S.tracker op := by
  cases hs <;> rfl

/-- A call's tracker write is at its own logged triple. -/
lemma aws_trackerWrite_triple {K : Cfg} {op : Op} {w : (Chain × Address × AssetData) × Address}
    (h : op.trackerWrite K = some w) : op.triple K = some w.1 := by
  cases op with
  | register caller d h' =>
    simp only [Op.trackerWrite, Option.some.injEq] at h
    subst h
    rfl
  | setTracker d t =>
    simp only [Op.trackerWrite, Option.some.injEq] at h
    subst h
    rfl
  | finalize a => simp [Op.trackerWrite] at h
  | seed => simp [Op.trackerWrite] at h
  | counterpartSet a h' => simp [Op.trackerWrite] at h

/-- `trackerAfterOp`, read at one id through `Op.trackerWrite`. -/
lemma aws_trackerAfterOp_apply (K : Cfg) (f : AssetId → Address) (op : Op) (x : AssetId) :
    trackerAfterOp K f op x =
      match op.trackerWrite K with
      | some w => if x = K.enc w.1.1 w.1.2.1 w.1.2.2 then w.2 else f x
      | none => f x := by
  cases op <;> rfl

/-- The last write to `q` after one more call. -/
lemma aws_lastTrackerWriteOn_snoc (K : Cfg) (ops : List Op) (op : Op)
    (q : Chain × Address × AssetData) :
    lastTrackerWriteOn K (ops ++ [op]) q =
      match op.trackerWrite K with
      | some w => if w.1 = q then some w.2 else lastTrackerWriteOn K ops q
      | none => lastTrackerWriteOn K ops q := by
  unfold lastTrackerWriteOn
  rw [List.filterMap_append, List.filter_append, List.getLast?_append]
  cases h : op.trackerWrite K with
  | none => simp [h]
  | some w =>
    by_cases hw : w.1 = q
    · simp [h, hw]
    · simp [h, hw]

/-! ## No hash premise -/

/-- A tracker explanation logged before a call is still logged after it. -/
lemma aws_explained_snoc {K : Cfg} {ops : List Op} {op : Op} {x : AssetId} {t : Address}
    (h : ∃ d : AssetData,
      (Op.setTracker d t ∈ ops ∧ x = K.enc K.thisChain t d) ∨
      ((∃ h, Op.register t d h ∈ ops) ∧ x = writtenId K.enc K.thisChain K.ntv K.ntvAddr t d)) :
    ∃ d : AssetData,
      (Op.setTracker d t ∈ ops ++ [op] ∧ x = K.enc K.thisChain t d) ∨
      ((∃ h, Op.register t d h ∈ ops ++ [op]) ∧
        x = writtenId K.enc K.thisChain K.ntv K.ntvAddr t d) := by
  obtain ⟨d, ⟨hm, he⟩ | ⟨⟨h', hm⟩, he⟩⟩ := h
  · exact ⟨d, Or.inl ⟨List.mem_append_left _ hm, he⟩⟩
  · exact ⟨d, Or.inr ⟨⟨h', List.mem_append_left _ hm⟩, he⟩⟩

theorem aws_run_trackerRecorded {K : Cfg} {ops : List Op} {R : Router}
    (hr : ARun K empty ops R) : TrackerRecorded K ops R := by
  induction hr with
  | nil => intro a ha; exact absurd rfl ha
  | @snoc S T ops op _ hs ih =>
    have hlast : op ∈ ops ++ [op] := List.mem_append_right _ (List.mem_singleton_self _)
    cases hs with
    | @register _ caller d h _ =>
      intro x hx
      by_cases hxw : x = writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d
      · subst hxw
        rw [tracker_records_caller]
        exact ⟨d, Or.inr ⟨⟨h, hlast⟩, rfl⟩⟩
      · rw [setHandler_tracker_ne _ _ _ _ _ _ _ _ hxw] at hx ⊢
        exact aws_explained_snoc (ih x hx)
    | finalize _ _ _ => exact fun x hx => aws_explained_snoc (ih x hx)
    | seed => exact fun x hx => aws_explained_snoc (ih x hx)
    | counterpartSet _ => exact fun x hx => aws_explained_snoc (ih x hx)
    | @setTracker _ d t _ =>
      intro x hx
      by_cases hxt : x = K.enc K.thisChain t d
      · subst hxt
        rw [recordTracker_tracker_self]
        exact ⟨d, Or.inl ⟨hlast, rfl⟩⟩
      · rw [recordTracker_tracker_ne _ _ hxt] at hx ⊢
        exact aws_explained_snoc (ih x hx)

theorem aws_trackerRecorded_trackerHashed {K : Cfg} {ops : List Op} {R : Router}
    (hP : TrackerRecorded K ops R) : TrackerHashed K R := by
  intro a ha
  obtain ⟨d, ⟨_, he⟩ | ⟨_, he⟩⟩ := hP a ha
  · exact ⟨d, Or.inl he⟩
  · by_cases hv : R.tracker a = K.ntv
    · exact ⟨d, Or.inr ⟨hv, he.trans (by simp only [writtenId, hv, senderOf_self])⟩⟩
    · exact ⟨d, Or.inl (he.trans (by simp only [writtenId, senderOf_ne hv]))⟩

/-- The logged triple behind a nonzero tracker: on this chain, with a matching sender. -/
lemma aws_trackerRecorded_triple {K : Cfg} {ops : List Op} {R : Router}
    (hP : TrackerRecorded K ops R) {a : AssetId} (ha : R.tracker a ≠ 0) :
    ∃ p ∈ loggedTriples K ops, K.enc p.1 p.2.1 p.2.2 = a ∧ p.1 = K.thisChain ∧
      (p.2.1 = R.tracker a ∨ (R.tracker a = K.ntv ∧ p.2.1 = K.ntvAddr)) := by
  obtain ⟨d, ⟨hm, he⟩ | ⟨⟨h, hm⟩, he⟩⟩ := hP a ha
  · exact ⟨(K.thisChain, R.tracker a, d), mem_loggedTriples.2 ⟨_, hm, rfl⟩, he.symm, rfl,
      Or.inl rfl⟩
  · refine ⟨(K.thisChain, senderOf K.ntv K.ntvAddr (R.tracker a), d),
      mem_loggedTriples.2 ⟨_, hm, rfl⟩, he.symm, rfl, ?_⟩
    by_cases hv : R.tracker a = K.ntv
    · exact Or.inr ⟨hv, by simp only [hv, senderOf_self]⟩
    · exact Or.inl (senderOf_ne hv)

theorem aws_run_tracker_is_log_replay {K : Cfg} {R₀ R : Router} {ops : List Op}
    (hr : ARun K R₀ ops R) : R.tracker = replayTrackers K R₀.tracker ops := by
  induction hr with
  | nil => rfl
  | @snoc S T ops op _ hs ih =>
    rw [aws_step_tracker hs, ih]
    simp only [replayTrackers, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem aws_run_tracked_ids_card_le {K : Cfg} {ops : List Op} {R : Router}
    (hr : ARun K empty ops R) (A : Finset AssetId) (hA : ∀ a ∈ A, R.tracker a ≠ 0) :
    A.card ≤ (loggedTriples K ops).card := by
  have hsub : A ⊆ (loggedTriples K ops).image (fun p => K.enc p.1 p.2.1 p.2.2) := by
    intro a ha
    obtain ⟨p, hp, he, _, _⟩ := aws_trackerRecorded_triple (aws_run_trackerRecorded hr) (hA a ha)
    exact Finset.mem_image.2 ⟨p, hp, he⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem aws_run_tracker_at_triple_or_logged_clash {K : Cfg} {ops : List Op} {R : Router}
    (hr : ARun K empty ops R) (q : Chain × Address × AssetData)
    (hq : R.tracker (K.enc q.1 q.2.1 q.2.2) ≠ 0) :
    (q ∈ loggedTriples K ops ∧ q.1 = K.thisChain ∧
      (q.2.1 = R.tracker (K.enc q.1 q.2.1 q.2.2) ∨
        (R.tracker (K.enc q.1 q.2.1 q.2.2) = K.ntv ∧ q.2.1 = K.ntvAddr))) ∨
    LoggedClash K ops q := by
  obtain ⟨p, hp, he, hc, hs⟩ := aws_trackerRecorded_triple (aws_run_trackerRecorded hr) hq
  by_cases hpq : p = q
  · subst hpq
    exact Or.inl ⟨hp, hc, hs⟩
  · exact Or.inr ⟨p, hp, hpq, he⟩

/-! ## Under the run-local premise -/

theorem aws_idInjOn_excludes_logged_clash {K : Cfg} {ops : List Op}
    {q : Chain × Address × AssetData} (hinj : IdInjOn K.enc (↑(loggedTriples K ops) ∪ {q})) :
    ¬ LoggedClash K ops q := by
  rintro ⟨p, hp, hpq, he⟩
  exact hpq (hinj p (Set.mem_union_left _ (Finset.mem_coe.2 hp)) q
    (Set.mem_union_right _ (Set.mem_singleton q)) he)

/-- No clash after one more call means no clash before it. -/
lemma aws_not_loggedClash_of_snoc {K : Cfg} {ops : List Op} {op : Op}
    {q : Chain × Address × AssetData} (hnc : ¬ LoggedClash K (ops ++ [op]) q) :
    ¬ LoggedClash K ops q :=
  fun ⟨p, hp, hpq, he⟩ => hnc ⟨p, loggedTriples_mono hp, hpq, he⟩

theorem aws_run_tracker_not_handed_to_other_sender_on {K : Cfg} {ops : List Op} {R : Router}
    (hr : ARun K empty ops R) (q : Chain × Address × AssetData) (t : Address) (ht : t ≠ 0)
    (hqt : q.2.1 ≠ t) (hqv : t = K.ntv → q.2.1 ≠ K.ntvAddr) (hnc : ¬ LoggedClash K ops q) :
    R.tracker (K.enc q.1 q.2.1 q.2.2) ≠ t := by
  intro heq
  have hq : R.tracker (K.enc q.1 q.2.1 q.2.2) ≠ 0 := by rw [heq]; exact ht
  rcases aws_run_tracker_at_triple_or_logged_clash hr q hq with ⟨_, _, hs⟩ | hc
  · rw [heq] at hs
    rcases hs with hs | ⟨hv, hs⟩
    · exact hqt hs
    · exact hqv hv hs
  · exact hnc hc

theorem aws_run_tracker_last_own_write {K : Cfg} {R₀ R : Router} {ops : List Op}
    (hr : ARun K R₀ ops R) (q : Chain × Address × AssetData) (hnc : ¬ LoggedClash K ops q) :
    R.tracker (K.enc q.1 q.2.1 q.2.2) =
      (lastTrackerWriteOn K ops q).getD (R₀.tracker (K.enc q.1 q.2.1 q.2.2)) := by
  induction hr with
  | nil => rfl
  | @snoc S T ops op _ hs ih =>
    have ih' := ih (aws_not_loggedClash_of_snoc hnc)
    rw [aws_lastTrackerWriteOn_snoc, aws_step_tracker hs, aws_trackerAfterOp_apply]
    cases hw : op.trackerWrite K with
    | none => exact ih'
    | some w =>
      dsimp only
      by_cases hwq : w.1 = q
      · have hx : K.enc q.1 q.2.1 q.2.2 = K.enc w.1.1 w.1.2.1 w.1.2.2 := by rw [hwq]
        simp only [hx, hwq, ite_true, Option.getD_some]
      · -- The call wrote another triple's id; with no logged clash at `q`, that id is not
        -- `q`'s.
        have hx : K.enc q.1 q.2.1 q.2.2 ≠ K.enc w.1.1 w.1.2.1 w.1.2.2 := fun he =>
          hnc ⟨w.1, mem_loggedTriples_snoc (aws_trackerWrite_triple hw), hwq, he.symm⟩
        simp only [hx, hwq, ite_false]
        exact ih'

/-! ## Concrete runs for the witnesses and the countermodels

They reuse `AllWriters`' witness configuration `wK1`: an L1 router on chain `1` with vault
`9` and `L2_NATIVE_TOKEN_VAULT_ADDR = 8`, under `wEnc`, which sends a triple with sender `8`
to `100`, `101` or `102` (data `0`, `1`, other) and any other triple to its sender. -/

/-- `wEnc` sends every triple whose sender is not `8` to its sender. -/
lemma aws_wEnc_ne8 (c : Chain) {s : Address} (hs : s ≠ 8) (d : AssetData) : wEnc c s d = s := by
  simp only [wEnc]
  exact ite_eq_right hs

/-- The owner records `5` as tracker for data `3`: id `wEnc 1 5 3 = 5`. -/
def awsR1 : Router := recordTracker wK1 empty 3 5

/-- The vault `9` registers token `0`, naming itself as handler: id `wEnc 1 8 0 = 100`. -/
def awsR2 : Router := setHandler wEnc 1 9 8 awsR1 9 0 9

def awsOps : List Op := [.setTracker 3 5, .register 9 0 9]

lemma awsRun : ARun wK1 empty awsOps awsR2 :=
  ((ARun.nil).snoc (AStep.setTracker rfl)).snoc
    (AStep.register (⟨Or.inl rfl, by decide⟩ : SetGuard wEnc 1 9 8 awsR1 9 0))

/-- `awsOps` logs `(1, 5, 3)` and `(1, 8, 0)`; with the vault triple `(1, 8, 0)` added, the
set is still those two. -/
lemma awsOps_logged_sub :
    (↑(loggedTriples wK1 awsOps) ∪ {((1 : Chain), (8 : Address), (0 : AssetData))} :
        Set (Chain × Address × AssetData)) ⊆
      {((1 : Chain), (5 : Address), (3 : AssetData)), (1, 8, 0)} := by
  intro p hp
  rcases hp with hp | hp
  · rw [Finset.mem_coe, mem_loggedTriples] at hp
    obtain ⟨op, hop, hpop⟩ := hp
    simp only [awsOps, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl
    · simp only [Op.triple, Option.some.injEq] at hpop
      subst hpop
      exact Set.mem_insert _ _
    · simp only [Op.triple, Option.some.injEq] at hpop
      subst hpop
      show ((1 : Chain), senderOf 9 8 9, (0 : AssetData)) ∈
        ({((1 : Chain), (5 : Address), (3 : AssetData)), (1, 8, 0)} :
          Set (Chain × Address × AssetData))
      rw [senderOf_self]
      exact Set.mem_insert_of_mem _ rfl
  · rw [Set.mem_singleton_iff] at hp
    subst hp
    exact Set.mem_insert_of_mem _ rfl

lemma awsOps_inj :
    IdInjOn wEnc (↑(loggedTriples wK1 awsOps) ∪ {((1 : Chain), (8 : Address), (0 : AssetData))}) :=
  idInjOn_mono awsOps_logged_sub (idInjOn_pair (by decide))

lemma awsR2_tracker_5 : awsR2.tracker 5 = 5 := by decide

lemma awsR2_tracker_100 : awsR2.tracker 100 = 9 := by decide

theorem aws_run_tracker_recorded_witness :
    ∃ (K : Cfg) (ops : List Op) (R : Router) (a b : AssetId),
      K.side = .l1 ∧ K.ntv ≠ K.ntvAddr ∧ ARun K empty ops R ∧
      IdInjOn K.enc ↑(loggedTriples K ops) ∧ a ≠ b ∧ (loggedTriples K ops).card = 2 ∧
      R.tracker a ≠ 0 ∧ (∀ d h, Op.register (R.tracker a) d h ∉ ops) ∧
      R.tracker b = K.ntv ∧ (∀ d, Op.setTracker d (R.tracker b) ∉ ops) ∧
      (∀ d, b ≠ K.enc K.thisChain K.ntv d) := by
  refine ⟨wK1, awsOps, awsR2, 5, 100, rfl, by decide, awsRun,
    idInjOn_mono Set.subset_union_left awsOps_inj, by decide, by decide,
    by rw [awsR2_tracker_5]; decide, ?_, awsR2_tracker_100, ?_, ?_⟩
  · intro d h hm
    rw [awsR2_tracker_5] at hm
    simp only [awsOps, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
      Op.register.injEq] at hm
    exact absurd hm.1 (by decide)
  · intro d hm
    rw [awsR2_tracker_100] at hm
    simp only [awsOps, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, or_false,
      Op.setTracker.injEq] at hm
    exact absurd hm.2 (by decide)
  · intro d
    show (100 : AssetId) ≠ wEnc 1 9 d
    rw [aws_wEnc_ne8 1 (by decide) d]
    decide

theorem aws_run_tracker_not_handed_to_other_sender_on_witness :
    ∃ (K : Cfg) (ops : List Op) (R : Router) (q : Chain × Address × AssetData) (t : Address)
      (a : AssetId),
      K.side = .l1 ∧ ARun K empty ops R ∧ t ≠ 0 ∧ t ≠ K.ntv ∧ q.2.1 = K.ntvAddr ∧ q.2.1 ≠ t ∧
      (t = K.ntv → q.2.1 ≠ K.ntvAddr) ∧ IdInjOn K.enc (↑(loggedTriples K ops) ∪ {q}) ∧
      ¬ LoggedClash K ops q ∧ R.tracker a = t ∧ R.tracker (K.enc q.1 q.2.1 q.2.2) ≠ 0 ∧
      R.handler (K.enc q.1 q.2.1 q.2.2) ≠ 0 :=
  ⟨wK1, awsOps, awsR2, (1, 8, 0), 5, 5, rfl, awsRun, by decide, by decide, rfl, by decide,
    fun h => absurd h (by decide), awsOps_inj, aws_idInjOn_excludes_logged_clash awsOps_inj,
    awsR2_tracker_5, by decide, by decide⟩

/-- `constEnc` (every triple → `1`): the owner records `5` as tracker for data `3`, at
id `1`, which is also the id of the vault triple `(1, 8, 0)`. -/
lemma aws_collision_inj :
    IdInjOn constEnc ↑(loggedTriples cK [.setTracker 3 5]) := by
  refine idInjOn_singleton (x := ((1 : Chain), (5 : Address), (3 : AssetData))) ?_
  intro p hp
  rw [Finset.mem_coe, mem_loggedTriples] at hp
  obtain ⟨op, hop, hpop⟩ := hp
  rw [List.mem_singleton] at hop
  subst hop
  simp only [Op.triple, Option.some.injEq] at hpop
  rw [← hpop]
  rfl

theorem aws_tracker_handed_to_other_sender_under_collision :
    ∃ (K : Cfg) (ops : List Op) (R : Router) (q : Chain × Address × AssetData) (t : Address),
      K.side = .l1 ∧ ARun K empty ops R ∧ t ≠ 0 ∧ q.2.1 = K.ntvAddr ∧ q.2.1 ≠ t ∧
      (t = K.ntv → q.2.1 ≠ K.ntvAddr) ∧ IdInjOn K.enc ↑(loggedTriples K ops) ∧
      LoggedClash K ops q ∧ R.tracker (K.enc q.1 q.2.1 q.2.2) = t :=
  ⟨cK, [.setTracker 3 5], recordTracker cK empty 3 5, (1, 8, 0), 5, rfl,
    (ARun.nil).snoc (AStep.setTracker rfl), by decide, rfl, by decide,
    fun h => absurd h (by decide), aws_collision_inj,
    ⟨(1, 5, 3), mem_loggedTriples.2 ⟨.setTracker 3 5, List.mem_singleton_self _, rfl⟩,
      by decide, rfl⟩,
    by decide⟩

/-- The vault `9` registers token `0`: tracker `9` at id `100`. -/
def awsV1 : Router := setHandler wEnc 1 9 8 empty 9 0 9

/-- The owner's `setAssetDeploymentTracker(0, 8)`: tracker `8` at `wEnc 1 8 0 = 100`, the
same id, since `8` is `L2_NATIVE_TOKEN_VAULT_ADDR`. -/
def awsV2 : Router := recordTracker wK1 awsV1 0 8

def awsOpsV : List Op := [.register 9 0 9, .setTracker 0 8]

lemma awsRunV : ARun wK1 empty awsOpsV awsV2 :=
  ((ARun.nil).snoc
    (AStep.register (⟨Or.inl rfl, by decide⟩ : SetGuard wEnc 1 9 8 empty 9 0))).snoc
    (AStep.setTracker rfl)

lemma awsOpsV_inj :
    IdInjOn wEnc
      (↑(loggedTriples wK1 awsOpsV) ∪ {((1 : Chain), (8 : Address), (0 : AssetData))}) := by
  refine idInjOn_singleton (x := ((1 : Chain), (8 : Address), (0 : AssetData))) ?_
  intro p hp
  rcases hp with hp | hp
  · rw [Finset.mem_coe, mem_loggedTriples] at hp
    obtain ⟨op, hop, hpop⟩ := hp
    simp only [awsOpsV, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl
    · simp only [Op.triple, Option.some.injEq] at hpop
      rw [← hpop]
      show ((1 : Chain), senderOf 9 8 9, (0 : AssetData)) = (1, 8, 0)
      rw [senderOf_self]
    · simp only [Op.triple, Option.some.injEq] at hpop
      rw [← hpop]
      rfl
  · exact hp

theorem aws_run_tracker_is_last_own_write_on_witness :
    ∃ (K : Cfg) (ops : List Op) (R : Router) (q : Chain × Address × AssetData)
      (v₁ v₂ : Address),
      K.side = .l1 ∧ ARun K empty ops R ∧ IdInjOn K.enc (↑(loggedTriples K ops) ∪ {q}) ∧
      ¬ LoggedClash K ops q ∧ q.2.1 = K.ntvAddr ∧ Op.register K.ntv q.2.2 K.ntv ∈ ops ∧
      (∃ op ∈ ops, op.trackerWrite K = some (q, v₁)) ∧ v₁ = K.ntv ∧
      lastTrackerWriteOn K ops q = some v₂ ∧ v₂ ≠ v₁ ∧
      R.tracker (K.enc q.1 q.2.1 q.2.2) = v₂ := by
  refine ⟨wK1, awsOpsV, awsV2, (1, 8, 0), 9, 8, rfl, awsRunV, awsOpsV_inj,
    aws_idInjOn_excludes_logged_clash awsOpsV_inj, rfl, List.mem_cons_self ..,
    ⟨.register 9 0 9, List.mem_cons_self .., ?_⟩, rfl, by decide, by decide, by decide⟩
  show some (((1 : Chain), senderOf 9 8 9, (0 : AssetData)), (9 : Address)) =
    some (((1 : Chain), (8 : Address), (0 : AssetData)), (9 : Address))
  rw [senderOf_self]

/-- Sender `8` gets id `100`; every other sender gets id `1`, so all custom triples collide. -/
def awsClashEnc : AssetIdOf := fun _ s _ => if s = 8 then 100 else 1

/-- `wK1` with `awsClashEnc`. -/
def awsClashK : Cfg := { wK1 with enc := awsClashEnc }

/-- The owner records `5` for data `3` and `6` for data `4`, both at id `1`; then the vault
registers token `0` at id `100`. -/
def awsC3 : Router :=
  setHandler awsClashEnc 1 9 8 (recordTracker awsClashK (recordTracker awsClashK empty 3 5) 4 6)
    9 0 9

def awsOpsC : List Op := [.setTracker 3 5, .setTracker 4 6, .register 9 0 9]

lemma awsRunC : ARun awsClashK empty awsOpsC awsC3 :=
  (((ARun.nil).snoc (AStep.setTracker rfl)).snoc (AStep.setTracker rfl)).snoc
    (AStep.register (⟨Or.inl rfl, by decide⟩ :
      SetGuard awsClashEnc 1 9 8 (recordTracker awsClashK (recordTracker awsClashK empty 3 5) 4 6)
        9 0))

theorem aws_last_own_write_holds_despite_clash_elsewhere :
    ∃ (K : Cfg) (ops : List Op) (R : Router) (q : Chain × Address × AssetData),
      K.side = .l1 ∧ ARun K empty ops R ∧ ¬ IdInjOn K.enc ↑(loggedTriples K ops) ∧
      q.2.1 = K.ntvAddr ∧ (∃ h, Op.register K.ntv q.2.2 h ∈ ops) ∧
      ¬ LoggedClash K ops q ∧ lastTrackerWriteOn K ops q = some K.ntv ∧
      R.tracker (K.enc q.1 q.2.1 q.2.2) = K.ntv := by
  refine ⟨awsClashK, awsOpsC, awsC3, (1, 8, 0), rfl, awsRunC, ?_, rfl,
    ⟨9, by simp [awsOpsC, awsClashK, wK1]⟩, ?_, by decide, by decide⟩
  · intro hinj
    have h1 : ((1 : Chain), (5 : Address), (3 : AssetData)) ∈ loggedTriples awsClashK awsOpsC :=
      mem_loggedTriples.2 ⟨.setTracker 3 5, by simp [awsOpsC], rfl⟩
    have h2 : ((1 : Chain), (6 : Address), (4 : AssetData)) ∈ loggedTriples awsClashK awsOpsC :=
      mem_loggedTriples.2 ⟨.setTracker 4 6, by simp [awsOpsC], rfl⟩
    exact absurd (hinj _ (Finset.mem_coe.2 h1) _ (Finset.mem_coe.2 h2) (by decide))
      (by decide)
  · rintro ⟨p, hp, hpq, he⟩
    rw [mem_loggedTriples] at hp
    obtain ⟨op, hop, hpop⟩ := hp
    simp only [awsOpsC, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl
    · simp only [Op.triple, Option.some.injEq] at hpop
      subst hpop
      exact absurd he (by decide)
    · simp only [Op.triple, Option.some.injEq] at hpop
      subst hpop
      exact absurd he (by decide)
    · simp only [Op.triple, Option.some.injEq] at hpop
      subst hpop
      exact hpq (by decide)

/-- An encoding that returns its data word: every id has a preimage with every sender. -/
def awsDataEnc : AssetIdOf := fun _ _ d => d

def awsDataK : Cfg :=
  { enc := awsDataEnc, thisChain := 1, ntv := 9, ntvAddr := 8, side := .l1, seedId := 0,
    ntvMints := fun _ => False }

/-- Every id carries the tracker `5`. -/
def awsAllTracked : Router := ⟨fun _ => 0, fun _ => 5⟩

theorem aws_tracker_hashed_admits_unreachable_router :
    ∃ (K : Cfg) (R : Router), (∀ R' : Router, TrackerHashed K R') ∧ (∀ a, R.tracker a ≠ 0) ∧
      ∀ ops : List Op, ops.length < UInt256.size → ¬ ARun K empty ops R := by
  refine ⟨awsDataK, awsAllTracked, fun _ a _ => ⟨a, Or.inl rfl⟩,
    fun _ => show (5 : Address) ≠ 0 by decide, ?_⟩
  intro ops hlen hr
  have h := aws_run_tracked_ids_card_le hr Finset.univ
    (fun _ _ => show (5 : Address) ≠ 0 by decide)
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact absurd ((h.trans (loggedTriples_card_le _ _)).trans_lt hlen) (lt_irrefl _)

end Contracts.AssetRouter.AllWriters

/-! ## Certificates -/

namespace Contracts.AssetRouter.AllWriters

theorem RunTrackerRecorded : Properties.RunTrackerRecorded :=
  fun _ _ _ hr => aws_run_trackerRecorded hr

theorem TrackerRecordedImpliesTrackerHashed : Properties.TrackerRecordedImpliesTrackerHashed :=
  fun _ _ _ hP => aws_trackerRecorded_trackerHashed hP

theorem RunTrackerIsLogReplay : Properties.RunTrackerIsLogReplay :=
  fun _ _ _ _ hr => aws_run_tracker_is_log_replay hr

theorem RunTrackedIdsCardLe : Properties.RunTrackedIdsCardLe :=
  fun _ _ _ hr A hA => aws_run_tracked_ids_card_le hr A hA

theorem RunTrackerAtTripleOrLoggedClash : Properties.RunTrackerAtTripleOrLoggedClash :=
  fun _ _ _ hr q hq => aws_run_tracker_at_triple_or_logged_clash hr q hq

theorem IdInjOnExcludesLoggedClash : Properties.IdInjOnExcludesLoggedClash :=
  fun _ _ _ hinj => aws_idInjOn_excludes_logged_clash hinj

theorem RunTrackerNotHandedToOtherSenderOn : Properties.RunTrackerNotHandedToOtherSenderOn :=
  fun _ _ _ hr q t ht hqt hqv hnc =>
    aws_run_tracker_not_handed_to_other_sender_on hr q t ht hqt hqv hnc

theorem RunTrackerIsLastOwnWriteOn : Properties.RunTrackerIsLastOwnWriteOn :=
  fun _ _ _ _ hr q hnc => aws_run_tracker_last_own_write hr q hnc

theorem RunTrackerRecordedWitness : Properties.RunTrackerRecordedWitness :=
  aws_run_tracker_recorded_witness

theorem RunTrackerNotHandedToOtherSenderOnWitness :
    Properties.RunTrackerNotHandedToOtherSenderOnWitness :=
  aws_run_tracker_not_handed_to_other_sender_on_witness

theorem TrackerHandedToOtherSenderUnderCollision :
    Properties.TrackerHandedToOtherSenderUnderCollision :=
  aws_tracker_handed_to_other_sender_under_collision

theorem RunTrackerIsLastOwnWriteOnWitness : Properties.RunTrackerIsLastOwnWriteOnWitness :=
  aws_run_tracker_is_last_own_write_on_witness

theorem LastOwnWriteHoldsDespiteClashElsewhere :
    Properties.LastOwnWriteHoldsDespiteClashElsewhere :=
  aws_last_own_write_holds_despite_clash_elsewhere

theorem TrackerHashedAdmitsUnreachableRouter : Properties.TrackerHashedAdmitsUnreachableRouter :=
  aws_tracker_hashed_admits_unreachable_router

end Contracts.AssetRouter.AllWriters
