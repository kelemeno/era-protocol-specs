import EraSpec.Contracts.L1InteropHandler.Properties.WithdrawalGate
import EraSpec.Contracts.InteropHandlerBase.Proofs.Reentrancy
import Mathlib.Tactic

/-!
# Proofs: the L1 withdrawal finalization gate

Two inductions on the budget carry everything.

* `exec_frameOk`: every committed frame satisfies `FrameOk`. A frame's committed verifications and
  deliveries are well formed (what the code checked before committing them); bundle statuses never
  return to `Unreceived`; a status that left `Unreceived`, and the hash of every delivery, was already
  out of `Unreceived` where the frame started or has a committed verification of bytes with that hash;
  the pause flag is the last value written; and the guard slot admits one `initialize`. A call loop
  starts from its entry point's writes (`LoopPre`): its own bundle is already out of `Unreceived`, and
  for a one-call bundle it delivers at most call `0`, first, from an unpaused state. `FrameOk`
  composes along a target's successive calls and along transactions (`FrameOk.append`). From fresh
  storage every status is `Unreceived`, which gives provenance (a) and its single-call form (d).
* `sim`: every committed or reverted frame of this model has a frame of the pin model
  (`InteropHandlerBase` `Reentrancy`, `.deployed`) with the same replay mappings and the same
  deliveries and completions. An administrative call writes neither mapping, so a target's
  administrative call becomes a pin entry that always reverts, caught. Projecting whole runs
  (`L1RunsProjectToPinRuns`) transfers `NoEffectCommittedTwice` and
  `StatusRecordsExactlyTheCommittedEffects`, which gives (e).

The witnesses and countermodels are evaluated by `decide`.
-/

namespace Contracts.L1WithdrawalGate

open AttackVectors.BundleStatusMachine (Status CallStatus)

/-! ## Reading the log -/

@[simp] lemma verifications_nil : verifications [] = [] := rfl
@[simp] lemma verifications_verified (v : Verification) (l : List Effect) :
    verifications (.verified v :: l) = v :: verifications l := rfl
@[simp] lemma verifications_delivered (d : Delivery) (l : List Effect) :
    verifications (.delivered d :: l) = verifications l := rfl
@[simp] lemma verifications_executed (h : Word) (l : List Effect) :
    verifications (.executed h :: l) = verifications l := rfl
@[simp] lemma verifications_pauseSet (c : Address) (b : Bool) (l : List Effect) :
    verifications (.pauseSet c b :: l) = verifications l := rfl
@[simp] lemma verifications_ownerSet (o : Address) (l : List Effect) :
    verifications (.ownerSet o :: l) = verifications l := rfl
@[simp] lemma verifications_pendingSet (o : Address) (l : List Effect) :
    verifications (.pendingSet o :: l) = verifications l := rfl
@[simp] lemma verifications_initialized (c : Address) (l : List Effect) :
    verifications (.initialized c :: l) = verifications l := rfl

@[simp] lemma deliveries_nil : deliveries [] = [] := rfl
@[simp] lemma deliveries_verified (v : Verification) (l : List Effect) :
    deliveries (.verified v :: l) = deliveries l := rfl
@[simp] lemma deliveries_delivered (d : Delivery) (l : List Effect) :
    deliveries (.delivered d :: l) = d :: deliveries l := rfl
@[simp] lemma deliveries_executed (h : Word) (l : List Effect) :
    deliveries (.executed h :: l) = deliveries l := rfl
@[simp] lemma deliveries_pauseSet (c : Address) (b : Bool) (l : List Effect) :
    deliveries (.pauseSet c b :: l) = deliveries l := rfl
@[simp] lemma deliveries_ownerSet (o : Address) (l : List Effect) :
    deliveries (.ownerSet o :: l) = deliveries l := rfl
@[simp] lemma deliveries_pendingSet (o : Address) (l : List Effect) :
    deliveries (.pendingSet o :: l) = deliveries l := rfl
@[simp] lemma deliveries_initialized (c : Address) (l : List Effect) :
    deliveries (.initialized c :: l) = deliveries l := rfl

@[simp] lemma pauseWrites_nil : pauseWrites [] = [] := rfl
@[simp] lemma pauseWrites_verified (v : Verification) (l : List Effect) :
    pauseWrites (.verified v :: l) = pauseWrites l := rfl
@[simp] lemma pauseWrites_delivered (d : Delivery) (l : List Effect) :
    pauseWrites (.delivered d :: l) = pauseWrites l := rfl
@[simp] lemma pauseWrites_executed (h : Word) (l : List Effect) :
    pauseWrites (.executed h :: l) = pauseWrites l := rfl
@[simp] lemma pauseWrites_pauseSet (c : Address) (b : Bool) (l : List Effect) :
    pauseWrites (.pauseSet c b :: l) = b :: pauseWrites l := rfl
@[simp] lemma pauseWrites_ownerSet (o : Address) (l : List Effect) :
    pauseWrites (.ownerSet o :: l) = pauseWrites l := rfl
@[simp] lemma pauseWrites_pendingSet (o : Address) (l : List Effect) :
    pauseWrites (.pendingSet o :: l) = pauseWrites l := rfl
@[simp] lemma pauseWrites_initialized (c : Address) (l : List Effect) :
    pauseWrites (.initialized c :: l) = pauseWrites l := rfl

@[simp] lemma initCount_nil : initCount [] = 0 := rfl
@[simp] lemma initCount_verified (v : Verification) (l : List Effect) :
    initCount (.verified v :: l) = initCount l := rfl
@[simp] lemma initCount_delivered (d : Delivery) (l : List Effect) :
    initCount (.delivered d :: l) = initCount l := rfl
@[simp] lemma initCount_executed (h : Word) (l : List Effect) :
    initCount (.executed h :: l) = initCount l := rfl
@[simp] lemma initCount_pauseSet (c : Address) (b : Bool) (l : List Effect) :
    initCount (.pauseSet c b :: l) = initCount l := rfl
@[simp] lemma initCount_ownerSet (o : Address) (l : List Effect) :
    initCount (.ownerSet o :: l) = initCount l := rfl
@[simp] lemma initCount_pendingSet (o : Address) (l : List Effect) :
    initCount (.pendingSet o :: l) = initCount l := rfl
@[simp] lemma initCount_initialized (c : Address) (l : List Effect) :
    initCount (.initialized c :: l) = initCount l + 1 := rfl

@[simp] lemma verifications_append : ∀ l₁ l₂ : List Effect,
    verifications (l₁ ++ l₂) = verifications l₁ ++ verifications l₂
  | [], _ => rfl
  | e :: l₁, l₂ => by cases e <;> simp [verifications_append l₁ l₂]

@[simp] lemma deliveries_append : ∀ l₁ l₂ : List Effect,
    deliveries (l₁ ++ l₂) = deliveries l₁ ++ deliveries l₂
  | [], _ => rfl
  | e :: l₁, l₂ => by cases e <;> simp [deliveries_append l₁ l₂]

@[simp] lemma pauseWrites_append : ∀ l₁ l₂ : List Effect,
    pauseWrites (l₁ ++ l₂) = pauseWrites l₁ ++ pauseWrites l₂
  | [], _ => rfl
  | e :: l₁, l₂ => by cases e <;> simp [pauseWrites_append l₁ l₂]

@[simp] lemma initCount_append : ∀ l₁ l₂ : List Effect,
    initCount (l₁ ++ l₂) = initCount l₁ + initCount l₂
  | [], _ => by simp
  | e :: l₁, l₂ => by cases e <;> simp [initCount_append l₁ l₂]; omega

lemma getLastD_append' {α : Type*} : ∀ (l₁ l₂ : List α) (a : α),
    (l₁ ++ l₂).getLastD a = l₂.getLastD (l₁.getLastD a)
  | [], _, _ => rfl
  | x :: l₁, l₂, a => by
      rw [List.cons_append, List.getLastD_cons, List.getLastD_cons, getLastD_append' l₁ l₂ x]

/-! ## The frame invariant -/

/-- What every committed frame satisfies, for a frame that went from `s` to `s'` committing `l`. -/
structure FrameOk (P : Params) (s s' : State) (l : List Effect) : Prop where
  verWf : ∀ v ∈ verifications l, VerificationWellFormed P v
  delWf : ∀ d ∈ deliveries l, DeliveryWellFormed P d
  mono : ∀ h, s.replay.bundle h ≠ .Unreceived → s'.replay.bundle h ≠ .Unreceived
  prov : ∀ h, s'.replay.bundle h ≠ .Unreceived →
    s.replay.bundle h ≠ .Unreceived ∨ ∃ v ∈ verifications l, P.codec.keccak v.bytes = h
  provD : ∀ d ∈ deliveries l,
    s.replay.bundle d.hash ≠ .Unreceived ∨ ∃ v ∈ verifications l, P.codec.keccak v.bytes = d.hash
  paused : s'.paused = (pauseWrites l).getLastD s.paused
  guardMono : s.guardSet = true → s'.guardSet = true
  guardCount : initCount l = 0 ∨ (s.guardSet = false ∧ initCount l = 1 ∧ s'.guardSet = true)

lemma FrameOk.refl (P : Params) (s : State) : FrameOk P s s [] where
  verWf _ h := by simp at h
  delWf _ h := by simp at h
  mono _ h := h
  prov _ h := Or.inl h
  provD _ h := by simp at h
  paused := rfl
  guardMono h := h
  guardCount := Or.inl rfl

lemma FrameOk.append {P : Params} {s s₁ s₂ : State} {l₁ l₂ : List Effect}
    (g₁ : FrameOk P s s₁ l₁) (g₂ : FrameOk P s₁ s₂ l₂) : FrameOk P s s₂ (l₁ ++ l₂) where
  verWf v hv := by
    rw [verifications_append, List.mem_append] at hv
    rcases hv with hv | hv
    · exact g₁.verWf v hv
    · exact g₂.verWf v hv
  delWf d hd := by
    rw [deliveries_append, List.mem_append] at hd
    rcases hd with hd | hd
    · exact g₁.delWf d hd
    · exact g₂.delWf d hd
  mono h hne := g₂.mono h (g₁.mono h hne)
  prov h hne := by
    rcases g₂.prov h hne with h₁ | ⟨v, hv, hk⟩
    · rcases g₁.prov h h₁ with h₀ | ⟨v, hv, hk⟩
      · exact Or.inl h₀
      · exact Or.inr ⟨v, by simp [hv], hk⟩
    · exact Or.inr ⟨v, by simp [hv], hk⟩
  provD d hd := by
    rw [deliveries_append, List.mem_append] at hd
    rcases hd with hd | hd
    · rcases g₁.provD d hd with h₀ | ⟨v, hv, hk⟩
      · exact Or.inl h₀
      · exact Or.inr ⟨v, by simp [hv], hk⟩
    · rcases g₂.provD d hd with h₁ | ⟨v, hv, hk⟩
      · rcases g₁.prov d.hash h₁ with h₀ | ⟨v, hv, hk⟩
        · exact Or.inl h₀
        · exact Or.inr ⟨v, by simp [hv], hk⟩
      · exact Or.inr ⟨v, by simp [hv], hk⟩
  paused := by rw [g₂.paused, g₁.paused, pauseWrites_append, getLastD_append']
  guardMono h := g₂.guardMono (g₁.guardMono h)
  guardCount := by
    rw [initCount_append]
    rcases g₁.guardCount with h₁ | ⟨hs, h₁, hs₁⟩ <;> rcases g₂.guardCount with h₂ | ⟨hs', h₂, hs₂⟩
    · exact Or.inl (by omega)
    · right
      refine ⟨?_, by omega, hs₂⟩
      cases hg : s.guardSet
      · rfl
      · have := g₁.guardMono hg; rw [this] at hs'; cases hs'
    · exact Or.inr ⟨hs, by omega, g₂.guardMono hs₁⟩
    · rw [hs₁] at hs'; cases hs'

/-- A frame that commits nothing of its own beyond one well-formed delivery, made from a state in
which the delivered hash is out of `Unreceived`, in front of a frame that is `FrameOk`. -/
lemma FrameOk.cons_delivered {P : Params} {s s₂ : State} {l : List Effect} {d : Delivery}
    (g : FrameOk P s s₂ l) (hwf : DeliveryWellFormed P d)
    (hst : s.replay.bundle d.hash ≠ .Unreceived) : FrameOk P s s₂ (.delivered d :: l) where
  verWf v hv := g.verWf v (by simpa using hv)
  delWf d' hd := by
    simp only [deliveries_delivered, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact hwf
    · exact g.delWf d' hd
  mono := g.mono
  prov h hne := by simpa using g.prov h hne
  provD d' hd := by
    simp only [deliveries_delivered, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact Or.inl hst
    · simpa using g.provD d' hd
  paused := by simpa using g.paused
  guardMono := g.guardMono
  guardCount := by simpa using g.guardCount

/-- A frame that changes nothing and commits only a `BundleExecuted`. -/
lemma FrameOk.executed (P : Params) (s : State) (h : Word) : FrameOk P s s [.executed h] where
  verWf _ hv := by simp at hv
  delWf _ hd := by simp at hd
  mono _ hne := hne
  prov _ hne := Or.inl hne
  provD _ hd := by simp at hd
  paused := rfl
  guardMono hg := hg
  guardCount := Or.inl rfl

/-! ## The entry points -/

lemma executeWrites_bundle (h : Word) (n : ℕ) (r : Contracts.InteropHandler.State) (h' : Word) :
    (executeWrites h n r).bundle h' = if h' = h then .FullyExecuted else r.bundle h' := by
  unfold executeWrites
  simp only [Contracts.InteropHandler.beforeCalls_deployed,
    Contracts.InteropHandler.executeAll_bundle, Contracts.InteropHandler.setBundle_bundle]
  split_ifs with hh
  · rfl
  · unfold Contracts.InteropHandler.State.verifyIfUnreceived
    split_ifs <;> simp [hh]

/-- `executeBundle` after its checks: the optional verification, the writes, then the call loop
(whose frame is `g`), then `BundleExecuted`. -/
lemma frameOk_execute {P : Params} {s s₂ : State} {caller : Address} {B : Bytes} {b : Bundle}
    {pf : InclusionProof} {incl : Bool} {l : List Effect}
    (hdec : P.codec.decode B = some b) (hok : ExecuteOk P s caller B b pf incl)
    (g : FrameOk P { s with replay := executeWrites (P.codec.keccak B) b.calls.length s.replay }
      s₂ l) :
    FrameOk P s s₂ ((if s.replay.bundle (P.codec.keccak B) = .Unreceived then
      [Effect.verified ⟨B, b, pf⟩] else []) ++ l ++ [.executed (P.codec.keccak B)]) := by
  obtain ⟨hver, _, _, _, hopen, hverify⟩ := hok
  set h := P.codec.keccak B with hh
  have pre : FrameOk P s { s with replay := executeWrites h b.calls.length s.replay }
      (if s.replay.bundle h = .Unreceived then [Effect.verified ⟨B, b, pf⟩] else []) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv
      by_cases hu : s.replay.bundle h = .Unreceived
      · simp only [hu, ↓reduceIte, verifications_verified, verifications_nil,
          List.mem_singleton] at hv
        subst hv
        obtain ⟨hctx, _, hsender, _⟩ := hverify hu
        exact ⟨hdec, hver, hctx, hsender, rfl⟩
      · simp [hu] at hv
    · intro d hd
      split_ifs at hd <;> simp at hd
    · intro h' hne
      rw [executeWrites_bundle]
      split_ifs with he
      · simp
      · exact hne
    · intro h' hne
      rw [executeWrites_bundle] at hne
      split_ifs at hne with he
      · subst he
        by_cases hu : s.replay.bundle h = .Unreceived
        · right
          exact ⟨⟨B, b, pf⟩, by simp [hu], rfl⟩
        · exact Or.inl hu
      · exact Or.inl hne
    · intro d hd
      split_ifs at hd <;> simp at hd
    · split_ifs <;> simp
    · exact id
    · left; split_ifs <;> simp
  exact (pre.append g).append (FrameOk.executed P s₂ h)

/-- `verifyBundle`: one verification, and `bundleStatus = Verified`. -/
lemma frameOk_verify {P : Params} {s : State} {B : Bytes} {b : Bundle} {pf : InclusionProof}
    {incl : Bool} (hdec : P.codec.decode B = some b) (hver : b.version = interopBundleVersion)
    (hok : VerifyOk P (s.replay.bundle (P.codec.keccak B)) b pf incl) :
    FrameOk P s { s with replay := s.replay.setBundle (P.codec.keccak B) .Verified }
      [.verified ⟨B, b, pf⟩] := by
  obtain ⟨hctx, _, hsender, _⟩ := hok
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    simp only [verifications_verified, verifications_nil, List.mem_singleton] at hv
    subst hv
    exact ⟨hdec, hver, hctx, hsender, rfl⟩
  · intro d hd; simp at hd
  · intro h' hne
    simp only [Contracts.InteropHandler.setBundle_bundle]
    split_ifs
    · simp
    · exact hne
  · intro h' hne
    simp only [Contracts.InteropHandler.setBundle_bundle] at hne
    split_ifs at hne with he
    · exact Or.inr ⟨⟨B, b, pf⟩, by simp, he.symm⟩
    · exact Or.inl hne
  · intro d hd; simp at hd
  · simp
  · exact id
  · left; simp

/-- `unbundleBundle` after its checks: the writes before the loop, then the loop (frame `g`). -/
lemma frameOk_unbundle {P : Params} {s s₂ : State} {caller : Address} {B : Bytes} {b : Bundle}
    {req : List CallStatus} {r₁ : Contracts.InteropHandler.State} {l : List Effect}
    (hok : UnbundleOk P s caller B b req)
    (hm : Contracts.InteropHandler.markCalls true (P.codec.keccak B) 0 req
      (s.replay.setBundle (P.codec.keccak B) .Unbundled) = some r₁)
    (g : FrameOk P { s with replay := r₁ } s₂ l) : FrameOk P s s₂ l := by
  obtain ⟨_, _, _, hopen⟩ := hok
  have hb := (Contracts.InteropHandler.markCalls_spec req 0 _ r₁ hm).1
  have hb' : ∀ h', r₁.bundle h' =
      if h' = P.codec.keccak B then .Unbundled else s.replay.bundle h' := by
    intro h'; rw [hb]; rfl
  have pre : FrameOk P s { s with replay := r₁ } [] := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv; simp at hv
    · intro d hd; simp at hd
    · intro h' hne
      show r₁.bundle h' ≠ _
      rw [hb']
      split_ifs
      · simp
      · exact hne
    · intro h' hne
      change r₁.bundle h' ≠ _ at hne
      rw [hb'] at hne
      split_ifs at hne with he
      · subst he
        left
        rcases hopen with h1 | h1 <;> rw [h1] <;> simp
      · exact Or.inl hne
    · intro d hd; simp at hd
    · rfl
    · exact id
    · exact Or.inl rfl
  simpa using pre.append g

/-- The administrative functions write neither mapping, commit no verification or delivery, and
write the pause flag and the guard slot as logged. -/
lemma frameOk_admin (P : Params) {caller : Address} {op : AdminOp} {s s' : State}
    {l : List Effect} (hx : adminStep caller op s = some (s', l)) : FrameOk P s s' l := by
  rcases op with o | _ | _ | o | _ | _
  · simp only [adminStep] at hx
    split_ifs at hx with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨by simp, by simp, fun _ h => h, fun _ h => Or.inl h, by simp, by simp,
      fun _ => rfl, Or.inr ⟨hc.1, by simp, rfl⟩⟩
  all_goals
    simp only [adminStep] at hx
    split_ifs at hx with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨by simp, by simp, fun _ h => h, fun _ h => Or.inl h, by simp, by simp,
      fun h => h, Or.inl (by simp)⟩

/-! ## The call loops -/

/-- Where a call loop starts: its bytes decode to its bundle, of version `1`; its bundle's hash is out
of `Unreceived` (the entry point wrote it first); an `executeBundle` loop is of a one-call bundle; and a
loop of a one-call bundle runs at most call `0`, from an unpaused state. -/
def LoopPre (P : Params) (s : State) (B : Bytes) (b : Bundle) (r : Route) (is : List ℕ) : Prop :=
  P.codec.decode B = some b ∧ b.version = interopBundleVersion ∧
    s.replay.bundle (P.codec.keccak B) ≠ .Unreceived ∧ (r = .execute → b.calls.length = 1) ∧
    (b.calls.length = 1 → is.length ≤ 1 ∧ (∀ i ∈ is, i = 0) ∧ (is ≠ [] → s.paused = false))

/-- What a frame needs where it starts: a call loop, `LoopPre`; anything else, nothing. -/
def FramePre (P : Params) : Frame → State → Prop
  | .calls B b r is _, s => LoopPre P s B b r is
  | _, _ => True

lemma toExecute_single (x : CallStatus) :
    (Contracts.InteropHandler.toExecute 0 [x]).length ≤ 1 ∧
      ∀ i ∈ Contracts.InteropHandler.toExecute 0 [x], i = 0 := by
  cases x <;> simp [Contracts.InteropHandler.toExecute]

/-- **The frame invariant.** Every committed frame, from a state satisfying its `FramePre`, is
`FrameOk`. -/
theorem exec_frameOk (P : Params) : ∀ (n : ℕ) (f : Frame) (s s' : State) (l : List Effect),
    exec P n f s = some (s', l) → FramePre P f s → FrameOk P s s' l := by
  intro n
  induction n with
  | zero => intro f s s' l hx _; simp [exec] at hx
  | succ n ih =>
    intro f s s' l hx hpre
    match f with
    | .entry (.executeBundle caller B pf incl) cs =>
      simp only [exec] at hx
      split at hx
      · cases hx
      · rename_i b hdec
        split at hx
        · rename_i hok
          split at hx
          · rename_i s₂ l₂ hrun
            simp only [Option.some.injEq, Prod.mk.injEq] at hx
            obtain ⟨rfl, rfl⟩ := hx
            obtain ⟨hver, hone, hnp, _, _, _⟩ := id hok
            have hpre' : LoopPre P
                { s with replay := executeWrites (P.codec.keccak B) b.calls.length s.replay }
                B b .execute (List.range b.calls.length) := by
              refine ⟨hdec, hver, ?_, fun _ => hone, fun _ => ?_⟩
              · show (executeWrites _ _ _).bundle _ ≠ _
                rw [executeWrites_bundle]; simp
              · rw [hone]; exact ⟨by simp, by simp, fun _ => hnp⟩
            exact frameOk_execute hdec hok (ih _ _ _ _ hrun hpre')
          · cases hx
        · cases hx
    | .entry (.verifyBundle caller B pf incl) cs =>
      simp only [exec] at hx
      split at hx
      · cases hx
      · rename_i b hdec
        split at hx
        · rename_i hok
          simp only [Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact frameOk_verify hdec hok.1 hok.2
        · cases hx
    | .entry (.unbundleBundle caller B req) cs =>
      simp only [exec] at hx
      split at hx
      · cases hx
      · rename_i hp
        split at hx
        · cases hx
        · rename_i b hdec
          split at hx
          · rename_i hok
            split at hx
            · rename_i r₁ hm
              have hb := (Contracts.InteropHandler.markCalls_spec req 0 _ r₁ hm).1
              have hpre' : LoopPre P { s with replay := r₁ } B b .unbundle
                  (Contracts.InteropHandler.toExecute 0 req) := by
                refine ⟨hdec, hok.1, ?_, (fun h => by cases h), fun hone => ?_⟩
                · show r₁.bundle _ ≠ _
                  rw [hb]; simp
                · obtain ⟨_, _, hlen, _⟩ := hok
                  rw [hone] at hlen
                  obtain ⟨x, rfl⟩ : ∃ x, req = [x] := by
                    match req, hlen with
                    | [x], _ => exact ⟨x, rfl⟩
                  obtain ⟨h1, h2⟩ := toExecute_single x
                  exact ⟨h1, h2, fun _ => by simpa using hp⟩
              exact frameOk_unbundle hok hm (ih _ _ _ _ hx hpre')
            · cases hx
          · cases hx
    | .entry (.admin caller op) cs =>
      simp only [exec] at hx
      exact frameOk_admin P hx
    | .calls B b r [] cs =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact FrameOk.refl P s
    | .calls B b r (i :: is) cs =>
      obtain ⟨hdec, hver, hst, hroute, hone⟩ := hpre
      simp only [exec] at hx
      split at hx
      · cases hx
      · rename_i c hc
        split_ifs at hx with hcc
        split at hx
        · rename_i s₁ l₁ ht
          split at hx
          · rename_i s₂ l₂ hr
            simp only [Option.some.injEq, Prod.mk.injEq] at hx
            obtain ⟨rfl, rfl⟩ := hx
            have g₁ := ih _ _ _ _ ht trivial
            have hpre' : LoopPre P s₁ B b r is := by
              refine ⟨hdec, hver, g₁.mono _ hst, hroute, fun h1 => ?_⟩
              obtain ⟨hlen, _, _⟩ := hone h1
              have his : is = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
              subst his
              simp
            have g₂ := ih _ _ _ _ hr hpre'
            refine (g₁.append g₂).cons_delivered ?_ hst
            refine ⟨rfl, rfl, hcc.2.2.1, b, c, hdec, hver, hc, hcc, rfl, rfl, rfl, hroute, ?_⟩
            intro h1
            obtain ⟨_, h0, hnp⟩ := hone h1
            exact ⟨h0 i (by simp), hnp (by simp)⟩
          · cases hx
        · cases hx
    | .target .returns =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact FrameOk.refl P s
    | .target .reverts =>
      simp [exec] at hx
    | .target (.calls e inner caught next) =>
      simp only [exec] at hx
      split at hx
      · rename_i s₁ l₁ he
        split at hx
        · rename_i s₂ l₂ hn
          simp only [Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact (ih _ _ _ _ he trivial).append (ih _ _ _ _ hn trivial)
        · cases hx
      · split_ifs at hx
        exact ih _ _ _ _ hx trivial

/-- One transaction is `FrameOk`. -/
theorem submit_frameOk (P : Params) (s : State) (t : Tx) :
    FrameOk P s (submit P s t).1 (submit P s t).2 := by
  unfold submit
  rcases hx : exec P t.fuel (.entry t.entry t.callees) s with _ | ⟨s', l⟩
  · exact FrameOk.refl P s
  · exact exec_frameOk P _ _ _ _ _ hx trivial

/-- A sequence of transactions is `FrameOk`. -/
theorem submitAll_frameOk (P : Params) : ∀ (s : State) (txs : List Tx),
    FrameOk P s (submitAll P s txs).1 (submitAll P s txs).2
  | s, [] => FrameOk.refl P s
  | s, t :: ts => (submit_frameOk P s t).append (submitAll_frameOk P (submit P s t).1 ts)

/-! ## (a) Provenance -/

/-- A well-formed verification and a well-formed delivery of the same bytes give `ProvenBy`. -/
lemma provenBy_of_wf {P : Params} {v : Verification} {d : Delivery}
    (hv : VerificationWellFormed P v) (hd : DeliveryWellFormed P d) (hb : v.bytes = d.bytes) :
    ProvenBy P v d := by
  obtain ⟨hdecv, _, ⟨hsrc, hdst, hbase⟩, hsender, hdata⟩ := hv
  obtain ⟨_, _, _, b, c, hdec, _, hc, _, hchain, hfrom, hpay, _, _⟩ := hd
  have hbv : b = v.bundle := by
    rw [← hb, hdecv] at hdec
    exact (Option.some.inj hdec).symm
  subst hbv
  refine ⟨hb, hsender, by rw [hdata, hb], by rw [hchain, hsrc], hsrc, hdst, hbase, ?_⟩
  unfold CallHas
  rw [hc]
  exact ⟨hfrom, hpay⟩

theorem VerificationsAreChecked : Properties.VerificationsAreChecked :=
  fun P s txs v hv => (submitAll_frameOk P s txs).verWf v hv

theorem DeliveredCallIsProvenOrKeccakClash : Properties.DeliveredCallIsProvenOrKeccakClash := by
  intro P txs d hd
  have g := submitAll_frameOk P init txs
  rcases g.provD d hd with hu | ⟨v, hv, hk⟩
  · exact absurd rfl hu
  · by_cases hb : v.bytes = d.bytes
    · exact Or.inl ⟨v, hv, provenBy_of_wf (g.verWf v hv) (g.delWf d hd) hb⟩
    · exact Or.inr ⟨v, hv, hb, by rw [hk, (g.delWf d hd).1]⟩

theorem CollisionDisjunctIsNeeded : Properties.CollisionDisjunctIsNeeded := by
  unfold Properties.CollisionDisjunctIsNeeded; decide

theorem ProvenanceWitness : Properties.ProvenanceWitness := by
  unfold Properties.ProvenanceWitness; decide

/-! ## (b) Target pin and value -/

theorem DeliveriesAreCheckedRouterCalls : Properties.DeliveriesAreCheckedRouterCalls :=
  fun P s txs d hd => (submitAll_frameOk P s txs).delWf d hd

/-! ## (c) Pause, owner, initialization -/

theorem PausedHandlerStartsNoDelivery : Properties.PausedHandlerStartsNoDelivery := by
  intro P n s hp
  refine ⟨fun caller B pf incl cs => ?_, fun caller B req cs => ?_⟩
  · cases n with
    | zero => rfl
    | succ n =>
      simp only [exec]
      split
      · rfl
      · rw [ite_eq_right]
        rintro ⟨_, _, h, _⟩
        rw [hp] at h
        cases h
  · cases n with
    | zero => rfl
    | succ n => simp [exec, hp]

theorem OnlyPauseAndUnpauseWritePaused : Properties.OnlyPauseAndUnpauseWritePaused :=
  fun P s txs => (submitAll_frameOk P s txs).paused

theorem PauseWritesAreOwnerCalls : Properties.PauseWritesAreOwnerCalls := by
  intro caller op s s' l hx hw
  rcases op with o | _ | _ | o | _ | _ <;> simp only [adminStep] at hx <;> split_ifs at hx with hc <;>
    simp only [Option.some.injEq, Prod.mk.injEq] at hx <;> obtain ⟨rfl, rfl⟩ := hx <;> simp_all

theorem InitializeRunsAtMostOnce : Properties.InitializeRunsAtMostOnce := by
  intro P s txs
  rcases (submitAll_frameOk P s txs).guardCount with h | ⟨hs, h, _⟩
  · exact ⟨by omega, fun _ => h⟩
  · exact ⟨by omega, fun hg => by rw [hg] at hs; cases hs⟩

theorem PauseGateWitness : Properties.PauseGateWitness := by
  unfold Properties.PauseGateWitness; decide

theorem InitializeOnceWitness : Properties.InitializeOnceWitness := by
  unfold Properties.InitializeOnceWitness; decide

theorem OwnerPauseMidUnbundleWitness : Properties.OwnerPauseMidUnbundleWitness := by
  unfold Properties.OwnerPauseMidUnbundleWitness; decide

/-! ## (d) The single-call rule -/

theorem VerifyThenUnbundleDeliversEveryCall : Properties.VerifyThenUnbundleDeliversEveryCall := by
  unfold Properties.VerifyThenUnbundleDeliversEveryCall; decide

theorem SingleCallEvidenceDeliversOneCall : Properties.SingleCallEvidenceDeliversOneCall := by
  intro P txs hone d hd
  have g := submitAll_frameOk P init txs
  rcases DeliveredCallIsProvenOrKeccakClash P txs d hd with ⟨v, hv, hp⟩ | hc
  · left
    obtain ⟨_, _, _, b, c, hdec, _, _, _, _, _, _, _, hsingle⟩ := g.delWf d hd
    have hbv : b = v.bundle := by
      have hdv := (g.verWf v hv).1
      rw [hp.1, hdec] at hdv
      exact Option.some.inj hdv
    have hlen : b.calls.length = 1 := hbv ▸ hone v hv
    exact ⟨(hsingle hlen).1, (hsingle hlen).2, b, hdec, hlen⟩
  · exact Or.inr hc

theorem SingleCallEvidenceWitness : Properties.SingleCallEvidenceWitness := by
  unfold Properties.SingleCallEvidenceWitness; decide

/-! ## (e) The projection to the pin model -/

/-- A pin-model entry that reverts from every state. -/
def pinRevert : Contracts.InteropHandler.Entry := .verifyBundle ⟨0, 0⟩ false

lemma pin_exec_pinRevert (n : ℕ) (r : Contracts.InteropHandler.State) :
    Contracts.InteropHandler.exec .deployed n (.entry pinRevert []) r = none := by
  cases n <;> simp [Contracts.InteropHandler.exec, pinRevert]

lemma pin_exec_reverts (n : ℕ) (r : Contracts.InteropHandler.State) :
    Contracts.InteropHandler.exec .deployed n (.target .reverts) r = none := by
  cases n <;> simp [Contracts.InteropHandler.exec]

/-- A result of this model, projected to the pin model: the replay mappings, and the deliveries and
completions of the log. -/
def proj : Option (State × List Effect) →
    Option (Contracts.InteropHandler.State × List Contracts.InteropHandler.Effect)
  | some (s, l) => some (s.replay, l.filterMap Effect.toPin)
  | none => none

@[simp] lemma toPin_verified (v : Verification) : Effect.toPin (.verified v) = none := rfl
@[simp] lemma toPin_delivered (d : Delivery) :
    Effect.toPin (.delivered d) = some (.delivered d.hash d.index) := rfl
@[simp] lemma toPin_executed (h : Word) : Effect.toPin (.executed h) = some (.executed h) := rfl
@[simp] lemma toPin_pauseSet (c : Address) (b : Bool) : Effect.toPin (.pauseSet c b) = none := rfl
@[simp] lemma toPin_ownerSet (o : Address) : Effect.toPin (.ownerSet o) = none := rfl
@[simp] lemma toPin_pendingSet (o : Address) : Effect.toPin (.pendingSet o) = none := rfl
@[simp] lemma toPin_initialized (c : Address) : Effect.toPin (.initialized c) = none := rfl

@[simp] lemma proj_none : proj none = none := rfl

@[simp] lemma proj_some (s : State) (l : List Effect) :
    proj (some (s, l)) = some (s.replay, l.filterMap Effect.toPin) := rfl

/-- The administrative entries. -/
def Entry.IsAdmin : Entry → Prop
  | .admin _ _ => True
  | _ => False

/-- An administrative call leaves the replay mappings alone and logs nothing the pin model sees. -/
lemma adminStep_pin {caller : Address} {op : AdminOp} {s s' : State} {l : List Effect}
    (hx : adminStep caller op s = some (s', l)) :
    s'.replay = s.replay ∧ l.filterMap Effect.toPin = [] := by
  rcases op with o | _ | _ | o | _ | _ <;> simp only [adminStep] at hx <;> split_ifs at hx <;>
    simp only [Option.some.injEq, Prod.mk.injEq] at hx <;> obtain ⟨rfl, rfl⟩ := hx <;>
    simp [Effect.toPin]

lemma exec_admin_pin (P : Params) (n : ℕ) (caller : Address) (op : AdminOp) (cs : List Callee)
    (s : State) : exec P n (.entry (.admin caller op) cs) s = none ∨
      ∃ s' l, exec P n (.entry (.admin caller op) cs) s = some (s', l) ∧
        s'.replay = s.replay ∧ l.filterMap Effect.toPin = [] := by
  cases n with
  | zero => exact Or.inl rfl
  | succ n =>
    simp only [exec]
    rcases hx : adminStep caller op s with _ | ⟨s', l⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨s', l, rfl, adminStep_pin hx⟩

/-! ### The entry points, unfolded once on each side -/

lemma exec_execute_ok {P : Params} {n : ℕ} {caller : Address} {B : Bytes} {pf : InclusionProof}
    {incl : Bool} {cs : List Callee} {s : State} {b : Bundle}
    (hdec : P.codec.decode B = some b) (hok : ExecuteOk P s caller B b pf incl) :
    exec P (n + 1) (.entry (.executeBundle caller B pf incl) cs) s =
      (exec P n (.calls B b .execute (List.range b.calls.length) cs)
          { s with replay := executeWrites (P.codec.keccak B) b.calls.length s.replay }).map
        (fun x => (x.1, (if s.replay.bundle (P.codec.keccak B) = .Unreceived then
          [Effect.verified ⟨B, b, pf⟩] else []) ++ x.2 ++ [.executed (P.codec.keccak B)])) := by
  simp only [exec, hdec, hok, ↓reduceIte]
  rcases exec P n (.calls B b .execute (List.range b.calls.length) cs)
      { s with replay := executeWrites (P.codec.keccak B) b.calls.length s.replay }
    with _ | ⟨s₂, l⟩ <;> rfl

lemma exec_execute_rev {P : Params} {n : ℕ} {caller : Address} {B : Bytes} {pf : InclusionProof}
    {incl : Bool} {cs : List Callee} {s : State}
    (hgo : ¬ ∃ b, P.codec.decode B = some b ∧ ExecuteOk P s caller B b pf incl) :
    exec P (n + 1) (.entry (.executeBundle caller B pf incl) cs) s = none := by
  simp only [exec]
  split
  · rfl
  · rename_i b hdec
    rw [ite_eq_right (fun hok => hgo ⟨b, hdec, hok⟩)]

lemma exec_verify_ok {P : Params} {n : ℕ} {caller : Address} {B : Bytes} {pf : InclusionProof}
    {incl : Bool} {cs : List Callee} {s : State} {b : Bundle}
    (hdec : P.codec.decode B = some b)
    (hok : b.version = interopBundleVersion ∧
      VerifyOk P (s.replay.bundle (P.codec.keccak B)) b pf incl) :
    exec P (n + 1) (.entry (.verifyBundle caller B pf incl) cs) s =
      some ({ s with replay := s.replay.setBundle (P.codec.keccak B) .Verified },
        [.verified ⟨B, b, pf⟩]) := by
  simp only [exec, hdec, hok, and_self, ↓reduceIte]

lemma exec_verify_rev {P : Params} {n : ℕ} {caller : Address} {B : Bytes} {pf : InclusionProof}
    {incl : Bool} {cs : List Callee} {s : State}
    (hgo : ¬ ∃ b, P.codec.decode B = some b ∧ b.version = interopBundleVersion ∧
      VerifyOk P (s.replay.bundle (P.codec.keccak B)) b pf incl) :
    exec P (n + 1) (.entry (.verifyBundle caller B pf incl) cs) s = none := by
  simp only [exec]
  split
  · rfl
  · rename_i b hdec
    rw [ite_eq_right (fun hok => hgo ⟨b, hdec, hok⟩)]

lemma exec_unbundle_ok {P : Params} {n : ℕ} {caller : Address} {B : Bytes}
    {req : List CallStatus} {cs : List Callee} {s : State} {b : Bundle}
    (hp : s.paused = false) (hdec : P.codec.decode B = some b)
    (hok : UnbundleOk P s caller B b req) :
    exec P (n + 1) (.entry (.unbundleBundle caller B req) cs) s =
      match Contracts.InteropHandler.markCalls true (P.codec.keccak B) 0 req
          (s.replay.setBundle (P.codec.keccak B) .Unbundled) with
      | some r₁ => exec P n (.calls B b .unbundle (Contracts.InteropHandler.toExecute 0 req) cs)
          { s with replay := r₁ }
      | none => none := by
  simp only [exec, hp, hdec, hok, ↓reduceIte, Bool.false_eq_true]
  rcases Contracts.InteropHandler.markCalls true (P.codec.keccak B) 0 req
    (s.replay.setBundle (P.codec.keccak B) .Unbundled) with _ | r₁ <;> rfl

lemma exec_unbundle_rev {P : Params} {n : ℕ} {caller : Address} {B : Bytes}
    {req : List CallStatus} {cs : List Callee} {s : State}
    (hgo : ¬ (s.paused = false ∧ ∃ b, P.codec.decode B = some b ∧ UnbundleOk P s caller B b req)) :
    exec P (n + 1) (.entry (.unbundleBundle caller B req) cs) s = none := by
  simp only [exec]
  split
  · rfl
  · rename_i hp
    split
    · rfl
    · rename_i b hdec
      rw [ite_eq_right (fun hok => hgo ⟨by simpa using hp, b, hdec, hok⟩)]

lemma pin_exec_execute_open (n : ℕ) (h : Word) (len : ℕ)
    (cs : List Contracts.InteropHandler.Callee) (r : Contracts.InteropHandler.State)
    (hg : r.bundle h = .Unreceived ∨ r.bundle h = .Verified) :
    Contracts.InteropHandler.exec .deployed (n + 1) (.entry (.executeBundle ⟨h, len⟩ true) cs) r =
      (Contracts.InteropHandler.exec .deployed n (.calls h (List.range len) cs)
        (executeWrites h len r)).map (fun x => (x.1, x.2 ++ [.executed h])) := by
  simp only [Contracts.InteropHandler.exec, executeWrites]
  split
  · rcases Contracts.InteropHandler.exec .deployed n (.calls h (List.range len) cs)
      (Contracts.InteropHandler.beforeCalls .deployed ⟨h, len⟩ (r.verifyIfUnreceived h))
      with _ | ⟨s₂, l⟩ <;> rfl
  · rename_i hc
    exfalso
    apply hc
    rcases hg with h1 | h1
    · exact Or.inr ⟨h1, trivial⟩
    · exact Or.inl h1

lemma pin_exec_verify_open (n : ℕ) (h : Word) (len : ℕ)
    (cs : List Contracts.InteropHandler.Callee) (r : Contracts.InteropHandler.State)
    (hu : r.bundle h = .Unreceived) :
    Contracts.InteropHandler.exec .deployed (n + 1) (.entry (.verifyBundle ⟨h, len⟩ true) cs) r =
      some (r.setBundle h .Verified, []) := by
  simp [Contracts.InteropHandler.exec, hu]

lemma pin_exec_unbundle_open (n : ℕ) (h : Word) (len : ℕ) (req : List CallStatus)
    (cs : List Contracts.InteropHandler.Callee) (r : Contracts.InteropHandler.State)
    (hg : req.length = len ∧ (r.bundle h = .Verified ∨ r.bundle h = .Unbundled)) :
    Contracts.InteropHandler.exec .deployed (n + 1) (.entry (.unbundleBundle ⟨h, len⟩ req) cs) r =
      match Contracts.InteropHandler.markCalls true h 0 req (r.setBundle h .Unbundled) with
      | some r₁ => Contracts.InteropHandler.exec .deployed n
          (.calls h (Contracts.InteropHandler.toExecute 0 req) cs) r₁
      | none => none := by
  simp only [Contracts.InteropHandler.exec, Contracts.InteropHandler.writesCallsFirst_deployed,
    Contracts.InteropHandler.afterUnbundle_deployed]
  split
  · rcases Contracts.InteropHandler.markCalls true h 0 req (r.setBundle h .Unbundled) with _ | r₁
    · rfl
    · simp only []
      rcases Contracts.InteropHandler.exec .deployed n
        (.calls h (Contracts.InteropHandler.toExecute 0 req) cs) r₁ with _ | ⟨s₂, l⟩ <;> rfl
  · rename_i hc
    exact absurd hg hc

/-- **The simulation.** Every frame of this model, committed or reverted, has a frame of the pin
model with the projected result: entry points other than the administrative ones, call loops (of the
same hash and indices) and targets. -/
theorem sim (P : Params) : ∀ n : ℕ,
    (∀ (e : Entry) (cs : List Callee) (s : State), ¬ e.IsAdmin →
      ∃ e' cs', Contracts.InteropHandler.exec .deployed n (.entry e' cs') s.replay =
        proj (exec P n (.entry e cs) s)) ∧
    (∀ (B : Bytes) (b : Bundle) (r : Route) (is : List ℕ) (cs : List Callee) (s : State),
      ∃ cs', Contracts.InteropHandler.exec .deployed n (.calls (P.codec.keccak B) is cs') s.replay =
        proj (exec P n (.calls B b r is cs) s)) ∧
    (∀ (t : Callee) (s : State),
      ∃ t', Contracts.InteropHandler.exec .deployed n (.target t') s.replay =
        proj (exec P n (.target t) s))
  | 0 => ⟨fun _ _ _ _ => ⟨pinRevert, [], by simp [exec, Contracts.InteropHandler.exec]⟩,
      fun _ _ _ _ _ _ => ⟨[], by simp [exec, Contracts.InteropHandler.exec]⟩,
      fun _ _ => ⟨.returns, by simp [exec, Contracts.InteropHandler.exec]⟩⟩
  | n + 1 => by
    obtain ⟨ihE, ihC, ihT⟩ := sim P n
    refine ⟨?_, ?_, ?_⟩
    · intro e cs s hne
      match e with
      | .executeBundle caller B pf incl =>
        by_cases hgo : ∃ b, P.codec.decode B = some b ∧ ExecuteOk P s caller B b pf incl
        · obtain ⟨b, hdec, hok⟩ := hgo
          obtain ⟨cs', hcs'⟩ := ihC B b .execute (List.range b.calls.length) cs
            { s with replay := executeWrites (P.codec.keccak B) b.calls.length s.replay }
          refine ⟨.executeBundle ⟨P.codec.keccak B, b.calls.length⟩ true, cs', ?_⟩
          rw [pin_exec_execute_open n _ _ _ _ hok.2.2.2.2.1, exec_execute_ok hdec hok]
          rw [show Contracts.InteropHandler.exec .deployed n
              (.calls (P.codec.keccak B) (List.range b.calls.length) cs')
              (executeWrites (P.codec.keccak B) b.calls.length s.replay) = _ from hcs']
          rcases exec P n (.calls B b .execute (List.range b.calls.length) cs)
            { s with replay := executeWrites (P.codec.keccak B) b.calls.length s.replay }
            with _ | ⟨s₂, l₂⟩
          · rfl
          · split_ifs <;> simp [List.filterMap_cons, List.filterMap_append]
        · refine ⟨pinRevert, [], ?_⟩
          rw [pin_exec_pinRevert, exec_execute_rev hgo]
          rfl
      | .verifyBundle caller B pf incl =>
        by_cases hgo : ∃ b, P.codec.decode B = some b ∧ b.version = interopBundleVersion ∧
            VerifyOk P (s.replay.bundle (P.codec.keccak B)) b pf incl
        · obtain ⟨b, hdec, hok⟩ := hgo
          refine ⟨.verifyBundle ⟨P.codec.keccak B, b.calls.length⟩ true, [], ?_⟩
          rw [pin_exec_verify_open n _ _ _ _ hok.2.2.1, exec_verify_ok hdec hok]
          simp [Effect.toPin]
        · refine ⟨pinRevert, [], ?_⟩
          rw [pin_exec_pinRevert, exec_verify_rev hgo]
          rfl
      | .unbundleBundle caller B req =>
        by_cases hgo : s.paused = false ∧ ∃ b, P.codec.decode B = some b ∧
            UnbundleOk P s caller B b req
        · obtain ⟨hp, b, hdec, hok⟩ := hgo
          rw [exec_unbundle_ok hp hdec hok]
          rcases hm : Contracts.InteropHandler.markCalls true (P.codec.keccak B) 0 req
              (s.replay.setBundle (P.codec.keccak B) .Unbundled) with _ | r₁
          · refine ⟨.unbundleBundle ⟨P.codec.keccak B, b.calls.length⟩ req, [], ?_⟩
            rw [pin_exec_unbundle_open n _ _ _ _ _ ⟨hok.2.2.1, hok.2.2.2⟩, hm]
            rfl
          · obtain ⟨cs', hcs'⟩ := ihC B b .unbundle (Contracts.InteropHandler.toExecute 0 req)
              cs { s with replay := r₁ }
            refine ⟨.unbundleBundle ⟨P.codec.keccak B, b.calls.length⟩ req, cs', ?_⟩
            rw [pin_exec_unbundle_open n _ _ _ _ _ ⟨hok.2.2.1, hok.2.2.2⟩, hm]
            exact hcs'
        · refine ⟨pinRevert, [], ?_⟩
          rw [pin_exec_pinRevert, exec_unbundle_rev hgo]
          rfl
      | .admin caller op => exact absurd trivial hne
    · intro B b r is cs s
      match is with
      | [] => exact ⟨[], by simp [exec, Contracts.InteropHandler.exec]⟩
      | i :: is =>
        rcases hc : b.calls[i]? with _ | c
        · refine ⟨[.reverts], ?_⟩
          simp only [exec, hc, proj_none]
          simp only [Contracts.InteropHandler.exec, List.headD_cons, pin_exec_reverts]
        · by_cases hcc : CallChecks P c
          · obtain ⟨t', ht'⟩ := ihT (cs.headD .returns) s
            rcases hX : exec P n (.target (cs.headD .returns)) s with _ | ⟨s₁, l₁⟩
            · refine ⟨[t'], ?_⟩
              rw [hX] at ht'
              simp only [exec, hc, hcc, ↓reduceIte, hX, proj_none]
              simp only [Contracts.InteropHandler.exec, List.headD_cons, ht', proj_none]
            · obtain ⟨cs'', hcs''⟩ := ihC B b r is cs.tail s₁
              refine ⟨t' :: cs'', ?_⟩
              rw [hX] at ht'
              simp only [exec, hc, hcc, ↓reduceIte, hX]
              simp only [Contracts.InteropHandler.exec, List.headD_cons, List.tail_cons, ht',
                proj_some, hcs'']
              rcases exec P n (.calls B b r is cs.tail) s₁ with _ | ⟨s₂, l₂⟩
              · rfl
              · simp [Effect.toPin, List.filterMap_append]
          · refine ⟨[.reverts], ?_⟩
            simp only [exec, hc, hcc, ↓reduceIte, proj_none]
            simp only [Contracts.InteropHandler.exec, List.headD_cons, pin_exec_reverts]
    · intro t s
      match t with
      | .returns => exact ⟨.returns, by simp [exec, Contracts.InteropHandler.exec]⟩
      | .reverts => exact ⟨.reverts, by simp [exec, Contracts.InteropHandler.exec]⟩
      | .calls e inner caught next =>
        by_cases hadm : e.IsAdmin
        · obtain ⟨caller, op, rfl⟩ : ∃ caller op, e = .admin caller op := by
            match e, hadm with
            | .admin caller op, _ => exact ⟨caller, op, rfl⟩
          rcases exec_admin_pin P n caller op inner s with h0 | ⟨s₁, l₁, h1, hrep, hfm⟩
          · obtain ⟨next', hn⟩ := ihT next s
            refine ⟨.calls pinRevert [] caught next', ?_⟩
            simp only [Contracts.InteropHandler.exec, pin_exec_pinRevert]
            simp only [exec, h0]
            split_ifs
            · exact hn
            · rfl
          · obtain ⟨next', hn⟩ := ihT next s₁
            refine ⟨.calls pinRevert [] true next', ?_⟩
            simp only [Contracts.InteropHandler.exec, pin_exec_pinRevert, ↓reduceIte]
            simp only [exec, h1]
            rw [← hrep, hn]
            rcases exec P n (.target next) s₁ with _ | ⟨s₂, l₂⟩
            · rfl
            · simp [List.filterMap_append, hfm]
        · obtain ⟨e', inner', he'⟩ := ihE e inner s hadm
          rcases hX : exec P n (.entry e inner) s with _ | ⟨s₁, l₁⟩
          · obtain ⟨next', hn⟩ := ihT next s
            refine ⟨.calls e' inner' caught next', ?_⟩
            rw [hX] at he'
            simp only [Contracts.InteropHandler.exec, he', proj_none]
            simp only [exec, hX]
            split_ifs
            · exact hn
            · rfl
          · obtain ⟨next', hn⟩ := ihT next s₁
            refine ⟨.calls e' inner' caught next', ?_⟩
            rw [hX] at he'
            simp only [Contracts.InteropHandler.exec, he', proj_some, hn]
            simp only [exec, hX]
            rcases exec P n (.target next) s₁ with _ | ⟨s₂, l₂⟩
            · rfl
            · simp [List.filterMap_append]

lemma pin_commit_proj (s : State) (x : Option (State × List Effect)) :
    Contracts.InteropHandler.commit s.replay (proj x) =
      ((commit s x).1.replay, (commit s x).2.filterMap Effect.toPin) := by
  rcases x with _ | ⟨s', l⟩ <;> rfl

theorem L1RunsProjectToPinRuns : Properties.L1RunsProjectToPinRuns := by
  intro P s txs
  induction txs generalizing s with
  | nil => exact ⟨[], rfl⟩
  | cons t ts ih =>
    obtain ⟨t', ht'⟩ : ∃ t' : Contracts.InteropHandler.Tx,
        Contracts.InteropHandler.submit .deployed s.replay t' =
          ((submit P s t).1.replay, (submit P s t).2.filterMap Effect.toPin) := by
      obtain ⟨fuel, e, cs⟩ := t
      by_cases hadm : e.IsAdmin
      · obtain ⟨caller, op, rfl⟩ : ∃ caller op, e = .admin caller op := by
          match e, hadm with
          | .admin caller op, _ => exact ⟨caller, op, rfl⟩
        refine ⟨⟨fuel, pinRevert, []⟩, ?_⟩
        simp only [Contracts.InteropHandler.submit, pin_exec_pinRevert, submit]
        rcases exec_admin_pin P fuel caller op cs s with h0 | ⟨s₁, l₁, h1, hrep, hfm⟩
        · rw [h0]; rfl
        · rw [h1]
          simp only [Contracts.InteropHandler.commit, commit, hrep, hfm]
      · obtain ⟨e', cs', he'⟩ := (sim P fuel).1 e cs s hadm
        refine ⟨⟨fuel, e', cs'⟩, ?_⟩
        simp only [Contracts.InteropHandler.submit, submit, he']
        exact pin_commit_proj s _
    obtain ⟨ts', hts'⟩ := ih (submit P s t).1
    refine ⟨t' :: ts', ?_⟩
    simp only [Contracts.InteropHandler.submitAll, submitAll, ht', hts', List.filterMap_append]

/-- The log's deliveries, as `(hash, index)`, read off the pin projection. -/
def pinKey : Contracts.InteropHandler.Effect → Option (Word × ℕ)
  | .delivered h i => some (h, i)
  | .executed _ => none

@[simp] lemma pinKey_delivered (h : Word) (i : ℕ) :
    pinKey (.delivered h i) = some (h, i) := rfl
@[simp] lemma pinKey_executed (h : Word) : pinKey (.executed h) = none := rfl

lemma deliveryKeys_eq : ∀ l : List Effect,
    (deliveries l).map (fun d => (d.hash, d.index)) = (l.filterMap Effect.toPin).filterMap pinKey
  | [] => rfl
  | e :: l => by cases e <;> simp [List.filterMap_cons, deliveryKeys_eq l]

lemma mem_pin_delivered_iff : ∀ (l : List Effect) (h : Word) (i : ℕ),
    Contracts.InteropHandler.Effect.delivered h i ∈ l.filterMap Effect.toPin ↔
      ∃ d ∈ deliveries l, d.hash = h ∧ d.index = i
  | [], _, _ => by simp
  | e :: l, h, i => by
      have ih := mem_pin_delivered_iff l h i
      cases e with
      | delivered d =>
        rw [List.filterMap_cons_some (toPin_delivered d), List.mem_cons, ih, deliveries_delivered]
        constructor
        · rintro (hx | ⟨d', hd', h1, h2⟩)
          · injection hx with h1 h2
            exact ⟨d, List.mem_cons_self, h1.symm, h2.symm⟩
          · exact ⟨d', List.mem_cons_of_mem _ hd', h1, h2⟩
        · rintro ⟨d', hd', h1, h2⟩
          rcases List.mem_cons.1 hd' with rfl | hd'
          · left; rw [h1, h2]
          · exact Or.inr ⟨d', hd', h1, h2⟩
      | _ => simpa using ih

theorem EachCallDeliveredAtMostOnce : Properties.EachCallDeliveredAtMostOnce := by
  intro P s txs
  obtain ⟨txs', h⟩ := L1RunsProjectToPinRuns P s txs
  have hnd := Contracts.InteropHandler.NoEffectCommittedTwice s.replay txs'
  rw [h] at hnd
  rw [deliveryKeys_eq]
  refine hnd.filterMap ?_
  intro a a' x ha ha'
  cases a <;> cases a' <;>
    simp only [pinKey, Option.mem_def, Option.some.injEq, reduceCtorEq] at ha ha'
  subst ha
  simp only [Prod.mk.injEq] at ha'
  rw [ha'.1, ha'.2]

theorem ReentrantRedeliveryRefusedWitness : Properties.ReentrantRedeliveryRefusedWitness := by
  unfold Properties.ReentrantRedeliveryRefusedWitness; decide

theorem CallStatusRecordsDeliveries : Properties.CallStatusRecordsDeliveries := by
  intro P txs h i
  obtain ⟨txs', hp⟩ := L1RunsProjectToPinRuns P init txs
  have hp' : Contracts.InteropHandler.submitAll .deployed Contracts.InteropHandler.init txs' =
      ((submitAll P init txs).1.replay, (submitAll P init txs).2.filterMap Effect.toPin) := hp
  have hrec := (Contracts.InteropHandler.StatusRecordsExactlyTheCommittedEffects txs' h i).1
  rw [hp'] at hrec
  rw [hrec, mem_pin_delivered_iff]

end Contracts.L1WithdrawalGate
