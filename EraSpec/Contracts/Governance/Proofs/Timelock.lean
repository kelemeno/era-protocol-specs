import EraSpec.Contracts.Governance.Properties.Timelock

/-!
# Proofs: the Governance timelock

Proofs of `EraSpec.Contracts.Governance.Properties.Timelock`.

The run-level results come from one invariant, `Inv`, of a state and its log: the clock is at
least 2, `minDelay` is the log's last minimum delay, each id's execution count is `1` exactly when
its timestamp is `1` and `0` otherwise, each id's timestamp agrees with its outstanding schedule
(`SchedOk`), and every entry of the log satisfies `Good` relative to the log before it.
`calls_inv` shows every sequence of (re-entrant) calls preserves it, by induction on `CallsWith`;
the execution case uses the re-check after the calls (`postCheck`) at the state the calls left.
`reach_inv` lifts it to every reachable state.
-/

namespace Contracts.Governance

/-! ## Operation-state lemmas -/

theorem isOperation_eq_false_iff {s : State} {id : OpId} :
    isOperation s id = false ↔ s.timestamps id = 0 := by
  unfold isOperation getOperationState
  split_ifs <;> simp_all

theorem isOperationPending_iff {s : State} {id : OpId} :
    isOperationPending s id = true ↔ s.timestamps id ≠ 0 ∧ s.timestamps id ≠ 1 := by
  unfold isOperationPending getOperationState
  split_ifs <;> simp_all

theorem isOperationReady_iff {s : State} {id : OpId} :
    isOperationReady s id = true ↔
      s.timestamps id ≠ 0 ∧ s.timestamps id ≠ 1 ∧ ¬ s.now < s.timestamps id := by
  unfold isOperationReady getOperationState
  split_ifs <;> simp_all

theorem isOperationDone_iff {s : State} {id : OpId} :
    isOperationDone s id = true ↔ s.timestamps id = 1 := by
  unfold isOperationDone getOperationState
  split_ifs <;> simp_all

theorem postCheck_pending {instant : Bool} {s : State} {id : OpId}
    (h : postCheck instant s id = true) : s.timestamps id ≠ 0 ∧ s.timestamps id ≠ 1 := by
  cases instant
  · exact (isOperationReady_iff.mp h).imp_right And.left
  · exact isOperationPending_iff.mp h

theorem preCheck_parts {e : Env} {instant : Bool} {caller : Address} {s : State} {op : Operation}
    (h : preCheck e instant caller s op = true) :
    (if instant then caller = s.securityCouncil else caller = s.owner ∨ caller = s.securityCouncil)
    ∧ (op.predecessor = 0 ∨ s.timestamps op.predecessor = 1)
    ∧ (if instant then isOperationPending s (e.hashOp op) = true
       else isOperationReady s (e.hashOp op) = true) := by
  unfold preCheck predecessorDone at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨ha, hp⟩, hr⟩ := h
  refine ⟨?_, hp.imp_right isOperationDone_iff.mp, ?_⟩
  · cases instant <;> simpa using ha
  · cases instant <;> simpa using hr

/-! ## Reading the log -/

theorem hist_snoc (L : List Ev) (x : Ev) : hist (L ++ [x]) = (hist L).apply x := by
  simp [hist, List.foldl_append]

theorem execCount_append (id : OpId) (L M : List Ev) :
    execCount id (L ++ M) = execCount id L + execCount id M := by
  simp [execCount, List.countP_append]

theorem execCount_snoc (id : OpId) (L : List Ev) (x : Ev) :
    execCount id (L ++ [x]) = execCount id L + if x.isExecOf id then 1 else 0 := by
  rw [execCount_append]
  cases h : x.isExecOf id <;> simp [execCount, h]

/-- Every entry of a log satisfies `P` relative to the log before it. -/
def EveryEntry (P : List Ev → Ev → Prop) (log : List Ev) : Prop :=
  ∀ pre x post, log = pre ++ x :: post → P pre x

theorem everyEntry_snoc {P : List Ev → Ev → Prop} {L : List Ev} {x : Ev}
    (hL : EveryEntry P L) (hx : P L x) : EveryEntry P (L ++ [x]) := by
  intro pre y post h
  rcases List.eq_nil_or_concat post with rfl | ⟨post', z, rfl⟩
  · obtain ⟨rfl, h2⟩ := List.append_inj' h rfl
    cases h2
    exact hx
  · have h' : L ++ [x] = (pre ++ y :: post') ++ [z] := by simpa using h
    exact hL pre y post' (List.append_inj' h' rfl).1

theorem everyEntry_of_forall {P : List Ev → Ev → Prop} {L : List Ev}
    (h : ∀ x ∈ L, ∀ pre, P pre x) : EveryEntry P L := by
  intro pre x post hL
  exact h x (by rw [hL]; simp) pre

/-! ## The invariant -/

/-- What every log entry satisfies relative to the log before it. -/
def Good (pre : List Ev) : Ev → Prop
  | .scheduled id _ d => lastDelay pre ≤ d ∧ pendingSched id pre = none ∧ execCount id pre = 0
  | .cancelled id => pendingSched id pre ≠ none ∧ execCount id pre = 0
  | .executed id p instant τ =>
      (∃ t d m, pendingSched id pre = some (t, d, m) ∧ m ≤ d ∧ t.val ≤ τ.val ∧
        (instant = false → t.val + d.val ≤ τ.val)) ∧ (p ≠ 0 → 1 ≤ execCount p pre)
  | _ => True

/-- A stored timestamp agrees with the log's outstanding schedule for its id. -/
def SchedOk (now ts : UInt256) : Option (UInt256 × UInt256 × UInt256) → Prop
  | none => ts = 0 ∨ ts = 1
  | some (t, d, m) => ts.val = t.val + d.val ∧ m ≤ d ∧ 2 ≤ t.val ∧ t.val ≤ now.val

/-- The invariant of a state and its log. -/
structure Inv (s : State) (log : List Ev) : Prop where
  now2 : 2 ≤ s.now.val
  delay : s.minDelay = lastDelay log
  count : ∀ id, execCount id log = if s.timestamps id = 1 then 1 else 0
  sched : ∀ id, SchedOk s.now (s.timestamps id) (pendingSched id log)
  good : EveryEntry Good log

theorem SchedOk.none_of_zero {now : UInt256} {o : Option (UInt256 × UInt256 × UInt256)}
    (h : SchedOk now 0 o) : o = none := by
  cases o with
  | none => rfl
  | some v =>
    obtain ⟨t, d, m⟩ := v
    obtain ⟨h1, -, h2, -⟩ := h
    simp at h1
    omega

theorem SchedOk.ne_none {now ts : UInt256} {o : Option (UInt256 × UInt256 × UInt256)}
    (h : SchedOk now ts o) (h0 : ts ≠ 0) (h1 : ts ≠ 1) : o ≠ none := by
  rintro rfl
  rcases h with h | h <;> contradiction

theorem SchedOk.mono {now now' ts : UInt256} {o : Option (UInt256 × UInt256 × UInt256)}
    (h : SchedOk now ts o) (hle : now.val ≤ now'.val) : SchedOk now' ts o := by
  cases o with
  | none => exact h
  | some v =>
    obtain ⟨t, d, m⟩ := v
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, h3, h4.trans hle⟩

/-- A step whose entry leaves the log's reading alone and whose state keeps the timestamps,
minimum delay and clock. -/
theorem inv_of_neutral {s t : State} {log : List Ev} {ev : Ev} (hI : Inv s log)
    (hts : t.timestamps = s.timestamps) (hd : t.minDelay = s.minDelay) (hn : t.now = s.now)
    (hh : (hist log).apply ev = hist log) (hx : ∀ id, ev.isExecOf id = false)
    (hg : Good log ev) : Inv t (log ++ [ev]) := by
  refine ⟨hn ▸ hI.now2, ?_, ?_, ?_, everyEntry_snoc hI.good hg⟩
  · rw [hd, hI.delay]; simp [lastDelay, hist_snoc, hh]
  · intro id; rw [execCount_snoc, hx id, hts, hI.count id]; simp
  · intro id; rw [hts, hn]; simpa [pendingSched, hist_snoc, hh] using hI.sched id

theorem schedule_eq_some {s t : State} {id : OpId} {d : UInt256}
    (h : schedule s id d = some t) :
    s.timestamps id = 0 ∧ s.minDelay ≤ d ∧ s.now.val + d.val < UInt256.size ∧
    t = { s with timestamps := Function.update s.timestamps id (s.now + d) } := by
  unfold schedule at h
  split_ifs at h with h1 h2 h3
  cases h
  exact ⟨isOperation_eq_false_iff.mp (by simpa using h1), not_lt.mp h2, h3, rfl⟩

theorem scheduled_inv {s t : State} {log : List Ev} {id : OpId} {d : UInt256}
    (hI : Inv s log) (hs : schedule s id d = some t) :
    Inv t (log ++ [.scheduled id s.now d]) ∧ t.now = s.now := by
  obtain ⟨h0, hd, hov, rfl⟩ := schedule_eq_some hs
  have hval : (s.now + d).val = s.now.val + d.val := by
    rw [Fin.val_add, Nat.mod_eq_of_lt hov]
  have hnone : pendingSched id log = none := by
    have := hI.sched id; rw [h0] at this; exact this.none_of_zero
  have hc0 : execCount id log = 0 := by rw [hI.count id, h0]; simp
  have hd' : lastDelay log ≤ d := hI.delay ▸ hd
  have hne1 : s.now + d ≠ 1 := by
    intro h; have := congrArg Fin.val h; rw [hval] at this; have := hI.now2; simp at *; omega
  refine ⟨⟨hI.now2, ?_, ?_, ?_, everyEntry_snoc hI.good ⟨hd', hnone, hc0⟩⟩, rfl⟩
  · simp only [lastDelay, hist_snoc, Hist.apply]; exact hI.delay
  · intro id'
    rw [execCount_snoc]
    by_cases hid : id' = id
    · subst hid; simp [Ev.isExecOf, hc0, hne1]
    · simp [Ev.isExecOf, Function.update_of_ne hid, hI.count id']
  · intro id'
    by_cases hid : id' = id
    · subst hid
      simp only [pendingSched, hist_snoc, Hist.apply, Function.update_self]
      exact ⟨hval, hd', hI.now2, le_refl _⟩
    · simp only [pendingSched, hist_snoc, Hist.apply, Function.update_of_ne hid]
      exact hI.sched id'

theorem cancel_inv {s : State} {log : List Ev} {id : OpId} (hI : Inv s log)
    (hp : isOperationPending s id = true) :
    Inv { s with timestamps := Function.update s.timestamps id 0 } (log ++ [.cancelled id]) := by
  obtain ⟨h0, h1⟩ := isOperationPending_iff.mp hp
  have hc0 : execCount id log = 0 := by rw [hI.count id]; simp [h1]
  refine ⟨hI.now2, ?_, ?_, ?_, everyEntry_snoc hI.good ⟨(hI.sched id).ne_none h0 h1, hc0⟩⟩
  · simp only [lastDelay, hist_snoc, Hist.apply]; exact hI.delay
  · intro id'
    rw [execCount_snoc]
    by_cases hid : id' = id
    · subst hid; simp [Ev.isExecOf, hc0]
    · simp [Ev.isExecOf, Function.update_of_ne hid, hI.count id']
  · intro id'
    by_cases hid : id' = id
    · subst hid
      simp only [pendingSched, hist_snoc, Hist.apply, Function.update_self]
      exact Or.inl rfl
    · simp only [pendingSched, hist_snoc, Hist.apply, Function.update_of_ne hid]
      exact hI.sched id'

theorem entry_inv {e : Env} {caller : Address} {s t : State} {ev : Ev} {log : List Ev}
    (x : Entry) (hI : Inv s log) (h : x.run e caller s = some (ev, t)) :
    Inv t (log ++ [ev]) ∧ t.now = s.now := by
  cases x with
  | scheduleTransparent op d =>
    simp only [Entry.run] at h
    split_ifs at h
    obtain ⟨t', hs, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact scheduled_inv hI hs
  | scheduleShadow id d =>
    simp only [Entry.run] at h
    split_ifs at h
    obtain ⟨t', hs, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact scheduled_inv hI hs
  | cancel id =>
    simp only [Entry.run] at h
    split_ifs at h with h1 h2
    cases h
    exact ⟨cancel_inv hI (by simpa using h2), rfl⟩
  | updateDelay d =>
    simp only [Entry.run] at h
    split_ifs at h
    cases h
    refine ⟨⟨hI.now2, ?_, ?_, ?_, everyEntry_snoc hI.good trivial⟩, rfl⟩
    · simp [lastDelay, hist_snoc, Hist.apply]
    · intro id; rw [execCount_snoc]; simpa [Ev.isExecOf] using hI.count id
    · intro id; simpa [pendingSched, hist_snoc, Hist.apply] using hI.sched id
  | updateSecurityCouncil a =>
    simp only [Entry.run] at h
    split_ifs at h
    cases h
    exact ⟨inv_of_neutral hI rfl rfl rfl rfl (fun _ => rfl) trivial, rfl⟩
  | transferOwnership a =>
    simp only [Entry.run] at h
    split_ifs at h
    cases h
    exact ⟨inv_of_neutral hI rfl rfl rfl rfl (fun _ => rfl) trivial, rfl⟩
  | acceptOwnership =>
    simp only [Entry.run] at h
    split_ifs at h
    cases h
    exact ⟨inv_of_neutral hI rfl rfl rfl rfl (fun _ => rfl) trivial, rfl⟩
  | renounceOwnership =>
    simp only [Entry.run] at h
    split_ifs at h
    cases h
    exact ⟨inv_of_neutral hI rfl rfl rfl rfl (fun _ => rfl) trivial, rfl⟩

theorem exec_inv {t : State} {L : List Ev} {id p : OpId} {instant : Bool} (hI : Inv t L)
    (hpost : postCheck instant t id = true) (hp : p ≠ 0 → 1 ≤ execCount p L) :
    Inv (markDone t id) (L ++ [.executed id p instant t.now]) := by
  obtain ⟨h0, h1⟩ := postCheck_pending hpost
  have hc0 : execCount id L = 0 := by rw [hI.count id]; simp [h1]
  have hsched := hI.sched id
  have hgood : Good L (.executed id p instant t.now) := by
    refine ⟨?_, hp⟩
    cases hps : pendingSched id L with
    | none => exact absurd hps (hsched.ne_none h0 h1)
    | some v =>
      obtain ⟨t0, d, m⟩ := v
      rw [hps] at hsched
      obtain ⟨hv, hm, -, hle⟩ := hsched
      refine ⟨t0, d, m, rfl, hm, hle, fun hi => ?_⟩
      subst hi
      have := (isOperationReady_iff.mp hpost).2.2
      rw [Fin.lt_def, not_lt] at this
      omega
  refine ⟨hI.now2, ?_, ?_, ?_, everyEntry_snoc hI.good hgood⟩
  · simp only [markDone, lastDelay, hist_snoc, Hist.apply]; exact hI.delay
  · intro id'
    rw [execCount_snoc]
    by_cases hid : id' = id
    · subst hid; simp [markDone, Ev.isExecOf, hc0]
    · have : (id == id') = false := by simpa using Ne.symm hid
      simp [markDone, Ev.isExecOf, Function.update_of_ne hid, hI.count id', this]
  · intro id'
    by_cases hid : id' = id
    · subst hid
      simp only [markDone, pendingSched, hist_snoc, Hist.apply, Function.update_self]
      exact Or.inr rfl
    · simp only [markDone, pendingSched, hist_snoc, Hist.apply, Function.update_of_ne hid]
      exact hI.sched id'

/-- Every sequence of calls into Governance inside one transaction, re-entrant executions
included, preserves the invariant and the clock. -/
theorem calls_inv {e : Env} {s u : State} {evs : List Ev} (h : Calls e s evs u) :
    ∀ log, Inv s log → Inv u (log ++ evs) ∧ u.now = s.now := by
  induction h with
  | nil s => intro log hI; simpa using hI
  | entry x hx _ ih =>
    intro log hI
    obtain ⟨hI', hn⟩ := entry_inv x hI hx
    obtain ⟨hU, hn'⟩ := ih _ hI'
    exact ⟨by simpa using hU, hn'.trans hn⟩
  | @exec caller s t u inner rest instant op hpre _ hpost _ ih1 ih2 =>
    intro log hI
    obtain ⟨hIt, hn⟩ := ih1 log hI
    have hp : op.predecessor ≠ 0 → 1 ≤ execCount op.predecessor (log ++ inner) := by
      intro hne
      have hd := ((preCheck_parts hpre).2.1).resolve_left hne
      have := hI.count op.predecessor
      rw [hd] at this; simp only [ite_true] at this
      rw [execCount_append, this]
      omega
    obtain ⟨hU, hn'⟩ := ih2 _ (exec_inv hIt (hpost rfl) hp)
    exact ⟨by simpa using hU, hn'.trans hn⟩

theorem tick_inv {s : State} {log : List Ev} {t : UInt256} (hI : Inv s log) (hle : s.now ≤ t) :
    Inv { s with now := t } log :=
  ⟨le_trans hI.now2 (Fin.le_def.mp hle), hI.delay, hI.count,
    fun id => (hI.sched id).mono (Fin.le_def.mp hle), hI.good⟩

theorem topStep_inv {e : Env} {s t : State} {evs log : List Ev} (hI : Inv s log)
    (h : TopStep e s evs t) : Inv t (log ++ evs) := by
  cases h with
  | entry x _ hx => exact (entry_inv x hI hx).1
  | exec instant op _ hpre hin hpost =>
    have := calls_inv (CallsWith.exec instant op hpre hin hpost (CallsWith.nil _)) log hI
    simpa using this.1
  | tick t hle => simpa using tick_inv hI hle

theorem init_inv (deployer admin council : Address) (delay now : UInt256) (hnow : 2 ≤ now.val) :
    Inv (initState admin council delay now) (ctorEvents deployer admin council delay) := by
  have hh : hist (ctorEvents deployer admin council delay) = ⟨delay, fun _ => none⟩ := by
    simp [hist, ctorEvents, Hist.apply]
  refine ⟨hnow, ?_, ?_, ?_, ?_⟩
  · simp [lastDelay, hh, initState]
  · intro id; simp [execCount, ctorEvents, Ev.isExecOf, initState]
  · intro id; simp [pendingSched, hh, initState, SchedOk]
  · apply everyEntry_of_forall
    intro x hx pre
    simp only [ctorEvents, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> trivial

theorem reach_inv {e : Env} {s : State} {log : List Ev} (h : Reach e s log) : Inv s log := by
  induction h with
  | init deployer admin council delay now _ hnow => exact init_inv deployer admin council delay now hnow
  | step _ hs ih => exact topStep_inv ih hs

theorem reach_topRun {e : Env} {s t : State} {log evs : List Ev} (h : Reach e s log)
    (hr : TopRun e s evs t) : Reach e t (log ++ evs) := by
  induction hr generalizing log with
  | refl s => simpa using h
  | step hs _ ih => simpa using ih (ReachWith.step h hs)

/-! ## The run-level properties -/

theorem state_of_inv {s : State} {log : List Ev} (hI : Inv s log) (id : OpId) :
    getOperationState s id = stateFromLog s.now id log := by
  unfold stateFromLog
  have hs := hI.sched id
  have hc := hI.count id
  cases hp : pendingSched id log with
  | none =>
    rw [hp] at hs
    unfold getOperationState
    rcases hs with h | h <;> simp [h, hc]
  | some v =>
    obtain ⟨t, d, m⟩ := v
    rw [hp] at hs
    obtain ⟨h1, -, h2, -⟩ := hs
    have h0 : s.timestamps id ≠ 0 := by
      intro h; rw [h] at h1; simp at h1; omega
    have h1' : s.timestamps id ≠ 1 := by
      intro h; rw [h] at h1; simp at h1; omega
    unfold getOperationState
    simp only [h0, h1', ite_false, Fin.lt_def, h1]

theorem OperationStateMatchesHistory : Properties.OperationStateMatchesHistory := by
  intro e s log h
  have hI := reach_inv h
  exact ⟨hI.delay, hI.now2, state_of_inv hI⟩

theorem DoneIffExecutedOnce : Properties.DoneIffExecutedOnce := by
  intro e s log h id
  have hc := (reach_inv h).count id
  rw [isOperationDone_iff, hc]
  by_cases h1 : s.timestamps id = 1 <;> simp [h1]

theorem DoneIsPermanent : Properties.DoneIsPermanent := by
  intro e s t log evs h hr id hd
  have h' := reach_topRun h hr
  have hc := (reach_inv h).count id
  have hc' := (reach_inv h').count id
  rw [isOperationDone_iff] at hd ⊢
  rw [hd] at hc; simp only [ite_true] at hc
  rw [execCount_append, hc] at hc'
  by_cases h1 : t.timestamps id = 1
  · simp only [h1, ite_true] at hc'
    exact ⟨h1, by omega⟩
  · simp only [h1, ite_false] at hc'
    omega

theorem ExecutionRespectsTimelock : Properties.ExecutionRespectsTimelock := by
  intro e s log h pre post id p instant τ hlog
  exact ((reach_inv h).good pre _ post hlog).1

theorem ScheduleRespectsMinDelay : Properties.ScheduleRespectsMinDelay := by
  intro e s log h pre post id t d hlog
  exact (reach_inv h).good pre _ post hlog

theorem CancelOnlyPending : Properties.CancelOnlyPending := by
  intro e s log h pre post id hlog
  exact (reach_inv h).good pre _ post hlog

theorem PredecessorExecutedFirst : Properties.PredecessorExecutedFirst := by
  intro e s log h pre post id p instant τ hlog hp
  have h1 := ((reach_inv h).good pre _ post hlog).2 hp
  unfold execCount at h1
  obtain ⟨x, hx, hex⟩ := List.countP_pos_iff.mp h1
  cases x with
  | executed i q b τ' =>
    simp only [Ev.isExecOf, beq_iff_eq] at hex
    subst hex
    exact ⟨q, b, τ', hx⟩
  | _ => simp [Ev.isExecOf] at hex

theorem CallerAuthority : Properties.CallerAuthority := by
  intro e caller s t ev
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (intro a b h; simp only [Entry.run] at h; split_ifs at h with h1; simp_all)
    | (intro a h; simp only [Entry.run] at h; split_ifs at h with h1; simp_all)
    | (intro h; simp only [Entry.run] at h; split_ifs at h with h1; simp_all)

theorem ExecuteAuthority : Properties.ExecuteAuthority := by
  intro e instant caller s op h
  obtain ⟨ha, hp, hr⟩ := preCheck_parts h
  refine ⟨fun hi => ?_, fun hi => ?_, hp.imp_right isOperationDone_iff.mpr⟩
  · subst hi; exact ⟨by simpa using ha, by simpa using hr⟩
  · subst hi; exact ⟨by simpa using ha, by simpa using hr⟩

/-- A non-executing call by anyone other than Governance keeps `minDelay` and the council. -/
theorem entry_keeps_config {e : Env} {caller : Address} {s t : State} {ev : Ev} (x : Entry)
    (hne : caller ≠ e.self) (h : x.run e caller s = some (ev, t)) :
    t.minDelay = s.minDelay ∧ t.securityCouncil = s.securityCouncil := by
  cases x with
  | scheduleTransparent op d =>
    simp only [Entry.run] at h
    split_ifs at h
    obtain ⟨t', hs, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    obtain ⟨-, -, -, rfl⟩ := schedule_eq_some hs
    exact ⟨rfl, rfl⟩
  | scheduleShadow id d =>
    simp only [Entry.run] at h
    split_ifs at h
    obtain ⟨t', hs, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    obtain ⟨-, -, -, rfl⟩ := schedule_eq_some hs
    exact ⟨rfl, rfl⟩
  | cancel id =>
    simp only [Entry.run] at h
    split_ifs at h
    cases h
    exact ⟨rfl, rfl⟩
  | updateDelay d =>
    simp only [Entry.run] at h
    split_ifs at h
  | updateSecurityCouncil a =>
    simp only [Entry.run] at h
    split_ifs at h
  | transferOwnership a =>
    simp only [Entry.run] at h
    split_ifs at h
    cases h
    exact ⟨rfl, rfl⟩
  | acceptOwnership =>
    simp only [Entry.run] at h
    split_ifs at h
    cases h
    exact ⟨rfl, rfl⟩
  | renounceOwnership =>
    simp only [Entry.run] at h
    split_ifs at h
    cases h
    exact ⟨rfl, rfl⟩

theorem ConfigOnlyThroughExecution : Properties.ConfigOnlyThroughExecution := by
  intro e s t log evs _ hs hchg
  cases hs with
  | entry x hne hx =>
    obtain ⟨h1, h2⟩ := entry_keeps_config x hne hx
    exact absurd hchg (by simp [h1, h2])
  | @exec caller _ t' inner instant op _ _ _ _ =>
    exact ⟨e.hashOp op, op.predecessor, instant, t'.now, by simp⟩
  | tick t' _ => simp at hchg

theorem SelfUpdatesTouchOnlyTheirField : Properties.SelfUpdatesTouchOnlyTheirField := by
  intro e caller s t ev
  refine ⟨fun d h => ?_, fun a h => ?_⟩ <;> simp only [Entry.run] at h <;> split_ifs at h <;>
    (cases h; rfl)

theorem ReadyIsExecutable : Properties.ReadyIsExecutable := by
  intro e s op hne hr hp
  have hpre : preCheck e false s.owner s op = true := by
    simp [preCheck, hp, hr]
  refine ⟨TopStepWith.exec (caller := s.owner) false op hne hpre (CallsWith.nil s)
    (fun _ => by simpa [postCheck] using hr), ?_⟩
  simp [isOperationDone_iff, markDone]

/-! ## The countermodel: no re-check, double execution -/

/-- The environment of the concrete runs: Governance at address 7, an operation's id is its salt. -/
def cmEnv : Env := { self := 7, hashOp := fun op => op.salt }

/-- An operation with no calls, no predecessor and id 5. -/
def cmOp : Operation := { calls := [], predecessor := 0, salt := 5 }

/-- Constructed by admin 1 with council 2, minimum delay 0, at time 100. -/
def cm0 : State := initState 1 2 0 100

/-- After `scheduleShadow(5, 0)` by the owner. -/
def cm1 : State := { cm0 with timestamps := Function.update cm0.timestamps 5 (cm0.now + 0) }

theorem cm_step1 : TopStepWith false cmEnv cm0 [.scheduled 5 100 0] cm1 :=
  TopStepWith.entry (caller := 1) (.scheduleShadow 5 0) (by decide) (by rfl)

theorem cm_pre : preCheck cmEnv false 1 cm1 cmOp = true := by decide

/-- The operation's calls re-enter `execute(cmOp)` as the owner; it completes. -/
theorem cm_inner :
    CallsWith false cmEnv cm1 ([] ++ [.executed 5 0 false cm1.now] ++ []) (markDone cm1 5) :=
  CallsWith.exec (caller := 1) false cmOp cm_pre (CallsWith.nil _) (fun h => absurd h (by decide))
    (CallsWith.nil _)

theorem cm_step2 :
    TopStepWith false cmEnv cm1
      (([] ++ [.executed 5 0 false cm1.now] ++ []) ++ [.executed 5 0 false (markDone cm1 5).now])
      (markDone (markDone cm1 5) 5) :=
  TopStepWith.exec (caller := 1) false cmOp (by decide) cm_pre cm_inner
    (fun h => absurd h (by decide))

theorem NoRecheckDoubleExecution : Properties.NoRecheckDoubleExecution :=
  ⟨cmEnv, _, _, 5,
    ReachWith.step (ReachWith.step (ReachWith.init 1 1 2 0 100 (by decide) (by decide)) cm_step1)
      cm_step2,
    by decide⟩

/-! ## The boundary: a clock of 1 -/

/-- Owner 1, council 2, minimum delay 0, clock 1, nothing scheduled. -/
def lc0 : State :=
  { owner := 1, pendingOwner := 0, securityCouncil := 2, timestamps := fun _ => 0, minDelay := 0,
    now := 1 }

/-- An operation with predecessor 5 and id 6. -/
def lcOp : Operation := { calls := [], predecessor := 5, salt := 6 }

def lc1 : State := { lc0 with timestamps := Function.update lc0.timestamps 5 (lc0.now + 0) }
def lc2 : State := { lc1 with timestamps := Function.update lc1.timestamps 6 (lc1.now + 1) }
def lc3 : State := { lc2 with now := 2 }

theorem lc_pre : preCheck cmEnv false 1 lc3 lcOp = true := by decide

theorem lc_run :
    TopRun cmEnv lc0
      ([.scheduled 5 1 0] ++ ([.scheduled 6 1 1] ++ ([] ++
        (([] ++ [.executed 6 5 false lc3.now]) ++ []))))
      (markDone lc3 6) :=
  TopRunWith.step (TopStepWith.entry (caller := 1) (.scheduleShadow 5 0) (by decide) (by rfl)) <|
  TopRunWith.step (TopStepWith.entry (caller := 1) (.scheduleTransparent lcOp 1) (by decide)
    (by rfl)) <|
  TopRunWith.step (TopStepWith.tick (s := lc2) 2 (by decide)) <|
  TopRunWith.step (TopStepWith.exec (caller := 1) false lcOp (by decide) lc_pre (CallsWith.nil _)
    (fun _ => by decide)) <|
  TopRunWith.refl _

theorem LowClockScheduleMarksDone : Properties.LowClockScheduleMarksDone :=
  ⟨cmEnv, lc0, _, _, lcOp, by decide, lc_run, by decide, by decide, by decide, by decide,
    by decide⟩

/-! ## The witness -/

/-- Operation `a` (id 5, no predecessor) and operation `b` (id 6, predecessor 5). -/
def wA : Operation := { calls := [], predecessor := 0, salt := 5 }
def wB : Operation := { calls := [], predecessor := 5, salt := 6 }

/-- Constructed by admin 1 with council 2, minimum delay 10, at time 100. -/
def w0 : State := initState 1 2 10 100
/-- `scheduleTransparent(a, 10)`: ready at 110. -/
def w1 : State := { w0 with timestamps := Function.update w0.timestamps 5 (w0.now + 10) }
/-- `scheduleShadow(6, 50)`: ready at 150. -/
def w2 : State := { w1 with timestamps := Function.update w1.timestamps 6 (w1.now + 50) }
/-- The clock reaches 110. -/
def w3 : State := { w2 with now := 110 }
/-- Inside `execute(a)`: `a`'s call re-enters as Governance and sets `minDelay` to 20. -/
def w3' : State := { w3 with minDelay := 20 }

theorem w_inner : Calls cmEnv w3 ([.minDelayChanged 10 20] ++ []) w3' :=
  CallsWith.entry (caller := 7) (.updateDelay 20) (by rfl) (CallsWith.nil _)

theorem w_reach :
    Reach cmEnv (markDone (markDone w3' 5) 6)
      (ctorEvents 1 1 2 10 ++ [.scheduled 5 100 10] ++ [.scheduled 6 100 50] ++ [] ++
        (([.minDelayChanged 10 20] ++ []) ++ [.executed 5 0 false w3'.now]) ++
        ([] ++ [.executed 6 5 true (markDone w3' 5).now])) :=
  ReachWith.step
    (ReachWith.step
      (ReachWith.step
        (ReachWith.step
          (ReachWith.step (ReachWith.init 1 1 2 10 100 (by decide) (by decide))
            (TopStepWith.entry (caller := 1) (.scheduleTransparent wA 10) (by decide) (by rfl)))
          (TopStepWith.entry (caller := 1) (.scheduleShadow 6 50) (by decide) (by rfl)))
        (TopStepWith.tick (s := w2) 110 (by decide)))
      (TopStepWith.exec (caller := 1) false wA (by decide) (by decide) w_inner (fun _ => by decide)))
    (TopStepWith.exec (caller := 2) true wB (by decide) (by decide) (CallsWith.nil _)
      (fun _ => by decide))

theorem TimelockRunSatisfiable : Properties.TimelockRunSatisfiable :=
  ⟨cmEnv, _, _, 5, 6, 0, 110, 110, 100, 50, 10, w_reach, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end Contracts.Governance
