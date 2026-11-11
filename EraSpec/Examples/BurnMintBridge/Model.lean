import EraSpec.Core.PreparedApplication

/-!
# A reference application: burn, hold an obligation in limbo, mint or recover

This is a new reference model, NOT a transcription of the deployed token bridge.
It tracks one obligation, its sender's source balance, its recipient's destination
balance, and tokens spent into the rest of the world. Amounts are mathematical
naturals; bounded arithmetic, access control, and real token behavior need their
own refinement proofs. Chain/account/token identities are fixed by the instance;
the input records the flow/leg identity and amount.

Source recovery and destination execution have independent local flags. Neither
operation reads the other chain's flag. Exclusivity is supplied by protocol
evidence, whose lifetime soundness is an explicit hypothesis. In particular,
there is no assumed synchronously shared cross-chain lock.
-/

namespace Applications.BurnMintBridge

structure Transfer where
  flowId : ℕ
  legId : ℕ
  amount : ℕ
deriving DecidableEq, Repr

structure State where
  sourceBalance : ℕ
  destinationBalance : ℕ
  spent : ℕ
  record : Option Transfer
  delivered : Bool
  refunded : Bool
deriving DecidableEq, Repr

def initial (source destination : ℕ) : State :=
  ⟨source, destination, 0, none, false, false⟩

def burn (s : State) (i : Transfer) : State :=
  { s with sourceBalance := s.sourceBalance - i.amount, record := some i }

def mint (s : State) (i : Transfer) : State :=
  { s with destinationBalance := s.destinationBalance + i.amount, delivered := true }

def restore (s : State) (i : Transfer) : State :=
  { s with sourceBalance := s.sourceBalance + i.amount, refunded := true }

def Prepare (s : State) (i : Transfer) (t : State) : Prop :=
  s.record = none ∧ s.delivered = false ∧ s.refunded = false ∧
    0 < i.amount ∧ i.amount ≤ s.sourceBalance ∧ t = burn s i

/-- Destination readiness depends on the fixed obligation and its own replay
flag, never on the sender retaining an ordinary spendable balance. -/
def Ready (s : State) (i : Transfer) : Prop :=
  s.record = some i ∧ s.delivered = false

def Execute (s : State) (i effect : Transfer) (t : State) : Prop :=
  Ready s i ∧ effect = i ∧ t = mint s i

def Recover (s : State) (i : Transfer) (t : State) : Prop :=
  s.record = some i ∧ s.refunded = false ∧ t = restore s i

/-- Ordinary spending on either chain may continue while a transfer waits. -/
inductive Interfere : State → State → Prop
  | source {s n} : n ≤ s.sourceBalance →
      Interfere s { s with sourceBalance := s.sourceBalance - n, spent := s.spent + n }
  | destination {s n} : n ≤ s.destinationBalance →
      Interfere s { s with destinationBalance := s.destinationBalance - n, spent := s.spent + n }

def application : Prepared.Application State Transfer Transfer where
  prepare := Prepare
  interfere := Interfere
  ready := Ready
  execute := Execute
  intendedEffect := id

/-- The reference bridge DISCHARGES the application interface, rather than
assuming global successful execution. Ordinary spending cannot break readiness. -/
theorem application_laws : Prepared.Laws application where
  preparation_establishes_ready := by
    intro s i p hp
    rcases hp with ⟨_, hd, _, _, _, rfl⟩
    exact ⟨rfl, hd⟩
  interference_preserves_ready := by
    intro s t i hstep hready
    cases hstep <;> exact hready
  ready_permits_execution := by
    intro s i hr
    exact ⟨mint s i, hr, rfl, rfl⟩
  execution_has_intended_effect := by
    intro s i e t he
    exact he.2.1

/-- Preparation removes the full committed amount from spendable source funds. -/
theorem preparation_burns {s t : State} {i : Transfer} (hp : Prepare s i t) :
    t.sourceBalance + i.amount = s.sourceBalance := by
  rcases hp with ⟨_, _, _, _, hbalance, rfl⟩
  simp only [burn]
  omega

/-- The committed input cannot change during any finite unrelated history. -/
theorem waiting_preserves_record {s t : State}
    (h : Prepared.InterferenceRun application s t) : t.record = s.record := by
  induction h with
  | refl => rfl
  | tail _ hs ih => cases hs <;> exact ih

theorem prepared_mint_survives_spending {s p t : State} {i : Transfer}
    (hp : Prepare s i p) (hwait : Prepared.InterferenceRun application p t) :
    ∃ u, Execute t i i u :=
  Prepared.prepared_execution_survives application_laws hp hwait

/-- Evidence that can be accepted over the ENTIRE lifetime of this obligation.
This abstraction includes stale and later evidence: soundness must exclude
conflicting authorizations across time, not just at one snapshot. -/
structure Evidence where
  finalize : Transfer → Prop
  recover : Transfer → Prop

def Evidence.Sound (E : Evidence) : Prop :=
  ∀ i, ¬ (E.finalize i ∧ E.recover i)

/-- A successful reference execution includes the protocol gate and the
application effect. Refining the real entry point to this relation is OPEN. -/
def AuthorizedExecution (E : Evidence) (s : State) (i effect : Transfer) (t : State) : Prop :=
  E.finalize i ∧ Execute s i effect t

inductive Step (E : Evidence) : State → State → Prop
  | prepare {s i t} : Prepare s i t → Step E s t
  | interfere {s t} : Interfere s t → Step E s t
  | execute {s i e t} : E.finalize i → Execute s i e t → Step E s t
  | recover {s i t} : E.recover i → Recover s i t → Step E s t

inductive Run (E : Evidence) : State → State → Prop
  | refl {s} : Run E s s
  | tail {s t u} : Run E s t → Step E t u → Run E s u

/-- Each irreversible effect retains evidence for precisely its stored input. -/
def Authorized (E : Evidence) (s : State) : Prop :=
  (s.delivered = true → ∃ i, s.record = some i ∧ E.finalize i) ∧
  (s.refunded = true → ∃ i, s.record = some i ∧ E.recover i)

theorem initial_authorized (E : Evidence) (source destination : ℕ) :
    Authorized E (initial source destination) := by
  simp [Authorized, initial]

theorem step_preserves_authorized {E : Evidence} {s t : State}
    (hs : Authorized E s) (hstep : Step E s t) : Authorized E t := by
  rcases hs with ⟨hd, hr⟩
  cases hstep with
  | prepare hp =>
    rcases hp with ⟨_, hdf, hrf, _, _, rfl⟩
    simp [Authorized, burn, hdf, hrf]
  | interfere hi => cases hi <;> exact ⟨hd, hr⟩
  | execute hcert he =>
    rcases he with ⟨⟨hrecord, _⟩, _, rfl⟩
    exact ⟨fun _ => ⟨_, hrecord, hcert⟩, hr⟩
  | recover hcert he =>
    rcases he with ⟨hrecord, _, rfl⟩
    exact ⟨hd, fun _ => ⟨_, hrecord, hcert⟩⟩

theorem run_authorized {E : Evidence} {s t : State}
    (hs : Authorized E s) (h : Run E s t) : Authorized E t := by
  induction h with
  | refl => exact hs
  | tail _ hstep ih => exact step_preserves_authorized ih hstep

theorem step_preserves_committed_input {E : Evidence} {s t : State} {i : Transfer}
    (hi : s.record = some i) (hstep : Step E s t) : t.record = some i := by
  cases hstep with
  | prepare hp =>
    have hnone := hp.1
    rw [hi] at hnone
    contradiction
  | interfere hs => cases hs <;> exact hi
  | execute _ he => rcases he with ⟨_, _, rfl⟩; exact hi
  | recover _ hr => rcases hr with ⟨_, _, rfl⟩; exact hi

theorem run_preserves_committed_input {E : Evidence} {s t : State} {i : Transfer}
    (hi : s.record = some i) (h : Run E s t) : t.record = some i := by
  induction h with
  | refl => exact hi
  | tail _ hstep ih => exact step_preserves_committed_input ih hstep

/-- Independent source/destination guards are safe only with sound protocol
evidence: both irreversible outcomes cannot occur for the same obligation. -/
theorem resolution_exclusive {E : Evidence} (hE : E.Sound) {s : State}
    (hs : Authorized E s) : ¬ (s.delivered = true ∧ s.refunded = true) := by
  rintro ⟨hd, hr⟩
  obtain ⟨i, hi, hfi⟩ := hs.1 hd
  obtain ⟨j, hj, hrj⟩ := hs.2 hr
  have hij : i = j := Option.some.inj (hi.symm.trans hj)
  subst j
  exact hE i ⟨hfi, hrj⟩

theorem reachable_resolution_exclusive {E : Evidence} (hE : E.Sound)
    {source destination : ℕ} {s : State} (h : Run E (initial source destination) s) :
    ¬ (s.delivered = true ∧ s.refunded = true) :=
  resolution_exclusive hE (run_authorized (initial_authorized E source destination) h)

/-- Both local replay flags are monotone even without evidence soundness. -/
theorem step_flags_persist {E : Evidence} {s t : State} (h : Step E s t) :
    (s.delivered = true → t.delivered = true) ∧
      (s.refunded = true → t.refunded = true) := by
  cases h with
  | prepare hp =>
    rcases hp with ⟨_, hd, hr, _, _, rfl⟩
    simp [burn, hd, hr]
  | interfere hi => cases hi <;> exact ⟨id, id⟩
  | execute _ he => rcases he with ⟨_, _, rfl⟩; exact ⟨fun _ => rfl, id⟩
  | recover _ he => rcases he with ⟨_, _, rfl⟩; exact ⟨id, fun _ => rfl⟩

theorem run_flags_persist {E : Evidence} {s t : State} (h : Run E s t) :
    (s.delivered = true → t.delivered = true) ∧
      (s.refunded = true → t.refunded = true) := by
  induction h with
  | refl => exact ⟨id, id⟩
  | tail _ hs ih =>
    exact ⟨fun hd => (step_flags_persist hs).1 (ih.1 hd),
      fun hr => (step_flags_persist hs).2 (ih.2 hr)⟩

theorem no_second_execution {E : Evidence} {s t u : State} {i e : Transfer}
    (hd : s.delivered = true) (h : Run E s t) : ¬ Execute t i e u := by
  intro he
  have ht := (run_flags_persist h).1 hd
  have hf := he.1.2
  rw [ht] at hf
  contradiction

theorem no_second_recovery {E : Evidence} {s t u : State} {i : Transfer}
    (hr : s.refunded = true) (h : Run E s t) : ¬ Recover t i u := by
  intro he
  have ht := (run_flags_persist h).2 hr
  have hf := he.2.1
  rw [ht] at hf
  contradiction

/-- The amount still owed, rather than tokens held in an escrow balance. -/
def limbo (s : State) : ℕ :=
  if s.delivered = true ∨ s.refunded = true then 0
  else match s.record with
    | none => 0
    | some i => i.amount

/-- `spent` accounts for ordinary transfers to the rest of the world. -/
def accounted (s : State) : ℕ :=
  s.sourceBalance + s.destinationBalance + s.spent + limbo s

theorem finalize_excludes_refunded {E : Evidence} (hE : E.Sound) {s : State}
    (hs : Authorized E s) {i : Transfer} (hi : s.record = some i) (hc : E.finalize i) :
    s.refunded = false := by
  cases hf : s.refunded with
  | false => rfl
  | true =>
    obtain ⟨j, hj, hcj⟩ := hs.2 hf
    have hij : i = j := Option.some.inj (hi.symm.trans hj)
    subst j
    exact False.elim (hE i ⟨hc, hcj⟩)

theorem recovery_excludes_delivered {E : Evidence} (hE : E.Sound) {s : State}
    (hs : Authorized E s) {i : Transfer} (hi : s.record = some i) (hc : E.recover i) :
    s.delivered = false := by
  cases hd : s.delivered with
  | false => rfl
  | true =>
    obtain ⟨j, hj, hcj⟩ := hs.1 hd
    have hij : i = j := Option.some.inj (hi.symm.trans hj)
    subst j
    exact False.elim (hE i ⟨hcj, hc⟩)

/-- Under a finalization certificate, every permitted full run preserves the
obligation until execution: it is either already executed or remains executable,
and it cannot have been refunded. This includes resolution attempts, not only
the narrower ordinary-spending interference relation. -/
theorem prepared_execution_remains_possible {E : Evidence} (hE : E.Sound)
    {s p t : State} {i : Transfer} (hp : Prepare s i p) (hc : E.finalize i)
    (hrun : Run E p t) :
    t.refunded = false ∧
      (t.delivered = true ∨ ∃ u, AuthorizedExecution E t i i u) := by
  have hrecord : p.record = some i := by
    rcases hp with ⟨_, _, _, _, _, rfl⟩
    rfl
  have hauth : Authorized E p := by
    rcases hp with ⟨_, hd, hr, _, _, rfl⟩
    simp [Authorized, burn, hd, hr]
  have ht := run_preserves_committed_input hrecord hrun
  refine ⟨finalize_excludes_refunded hE (run_authorized hauth hrun) ht hc, ?_⟩
  cases hd : t.delivered with
  | false => exact Or.inr ⟨mint t i, hc, ⟨ht, hd⟩, rfl, rfl⟩
  | true => exact Or.inl rfl

/-- No step creates or destroys accounted value: burn moves value into limbo;
mint/recovery moves it out exactly once. Evidence soundness is essential. -/
theorem step_conserves_value {E : Evidence} (hE : E.Sound) {s t : State}
    (hs : Authorized E s) (hstep : Step E s t) : accounted t = accounted s := by
  cases hstep with
  | prepare hp =>
    rcases hp with ⟨hrecord, hd, hr, _, hbalance, rfl⟩
    simp only [accounted, limbo, burn, hd, hr, hrecord]
    simp
    omega
  | interfere hi =>
    cases hi with
    | source hb =>
      change (s.sourceBalance - _ + s.destinationBalance + (s.spent + _) + limbo s) = _
      unfold accounted
      omega
    | destination hb =>
      change (s.sourceBalance + (s.destinationBalance - _) + (s.spent + _) + limbo s) = _
      unfold accounted
      omega
  | execute hc he =>
    rcases he with ⟨⟨hrecord, hd⟩, _, rfl⟩
    have hr := finalize_excludes_refunded hE hs hrecord hc
    simp [accounted, limbo, mint, hd, hr, hrecord]
    omega
  | recover hc he =>
    rcases he with ⟨hrecord, hr, rfl⟩
    have hd := recovery_excludes_delivered hE hs hrecord hc
    simp [accounted, limbo, restore, hd, hr, hrecord]
    omega

theorem run_conserves_value {E : Evidence} (hE : E.Sound) {s t : State}
    (hs : Authorized E s) (h : Run E s t) : accounted t = accounted s := by
  induction h with
  | refl => rfl
  | tail hrun hstep ih =>
    exact (step_conserves_value hE (run_authorized hs hrun) hstep).trans ih

theorem reachable_value_conserved {E : Evidence} (hE : E.Sound)
    {source destination : ℕ} {s : State} (h : Run E (initial source destination) s) :
    accounted s = source + destination := by
  have hc := run_conserves_value hE (initial_authorized E source destination) h
  simpa [accounted, limbo, initial] using hc

/-- Application-level input binding: the exact committed amount is minted, and
the effect identifies the same flow and leg as the stored obligation. -/
theorem execution_credits_committed_amount {s t : State} {i e : Transfer}
    (h : Execute s i e t) :
    s.record = some e ∧ t.destinationBalance = s.destinationBalance + e.amount := by
  rcases h with ⟨⟨hrecord, _⟩, rfl, rfl⟩
  exact ⟨hrecord, rfl⟩

/-! ## Non-vacuity and countermodels -/

def sampleTransfer : Transfer := ⟨1, 1, 1⟩

/-- Burning is a real successful preparation: with no remaining source funds,
the destination can still mint exactly the committed amount. -/
theorem empty_source_still_executable :
    Prepare (initial 1 0) sampleTransfer (burn (initial 1 0) sampleTransfer) ∧
    (burn (initial 1 0) sampleTransfer).sourceBalance = 0 ∧
    ∃ t, Execute (burn (initial 1 0) sampleTransfer) sampleTransfer sampleTransfer t := by
  have hp : Prepare (initial 1 0) sampleTransfer (burn (initial 1 0) sampleTransfer) := by
    simp [Prepare, initial, sampleTransfer, burn]
  exact ⟨hp, by decide, prepared_mint_survives_spending hp .refl⟩

def conflictingEvidence : Evidence := ⟨fun _ => True, fun _ => True⟩

def finalizeOnly : Evidence := ⟨fun _ => True, fun _ => False⟩

def recoverOnly : Evidence := ⟨fun _ => False, fun _ => True⟩

/-- Sound certificates admit successful resolution on either branch. The two
branches use different lifetime evidence environments, as exclusivity requires. -/
theorem both_sound_outcomes_reachable :
    finalizeOnly.Sound ∧ recoverOnly.Sound ∧
    (∃ s, Run finalizeOnly (initial 1 0) s ∧ s.delivered = true ∧ s.destinationBalance = 1) ∧
    (∃ s, Run recoverOnly (initial 1 0) s ∧ s.refunded = true ∧ s.sourceBalance = 1) := by
  have hp : Prepare (initial 1 0) sampleTransfer (burn (initial 1 0) sampleTransfer) := by
    simp [Prepare, initial, sampleTransfer, burn]
  have he : Execute (burn (initial 1 0) sampleTransfer) sampleTransfer sampleTransfer
      (mint (burn (initial 1 0) sampleTransfer) sampleTransfer) := by
    simp [Execute, Ready, burn, initial]
  have hr : Recover (burn (initial 1 0) sampleTransfer) sampleTransfer
      (restore (burn (initial 1 0) sampleTransfer) sampleTransfer) := by
    simp [Recover, burn, initial]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _i; simp [Evidence.Sound, finalizeOnly]
  · intro _i; simp [Evidence.Sound, recoverOnly]
  · exact ⟨_, .tail (.tail .refl (.prepare hp)) (.execute trivial he), rfl, by decide⟩
  · exact ⟨_, .tail (.tail .refl (.prepare hp)) (.recover trivial hr), rfl, by decide⟩

/-- Removing evidence exclusivity permits BOTH effects through their independent
local guards. Thus the distributed safety theorem is not true by construction. -/
theorem conflicting_evidence_double_pays :
    ∃ s, Run conflictingEvidence (initial 1 0) s ∧
      s.delivered = true ∧ s.refunded = true ∧ accounted s = 2 := by
  let p := burn (initial 1 0) sampleTransfer
  let d := mint p sampleTransfer
  refine ⟨restore d sampleTransfer, ?_, by decide, by decide, by decide⟩
  have hp : Prepare (initial 1 0) sampleTransfer p := by
    simp [Prepare, p, initial, sampleTransfer, burn]
  have he : Execute p sampleTransfer sampleTransfer d := by
    simp [Execute, Ready, p, d, burn, initial]
  have hr : Recover d sampleTransfer (restore d sampleTransfer) := by
    simp [Recover, d, p, mint, burn, initial]
  exact .tail (.tail (.tail .refl (.prepare hp)) (.execute trivial he)) (.recover trivial hr)

/-- A balance check without reservation is deterministic at each state but fails
the preservation law: the user can spend the checked balance before execution. -/
theorem unlocked_balance_check_not_stable :
    ∃ balance amount spent : ℕ,
      0 < amount ∧ amount ≤ balance ∧ spent ≤ balance ∧ ¬ amount ≤ balance - spent := by
  exact ⟨1, 1, 1, by decide, by decide, by decide, by decide⟩

end Applications.BurnMintBridge
