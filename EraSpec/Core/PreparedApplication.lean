import Mathlib.Tactic

/-!
# Applications that preserve prepared obligations

These are requirements on an APPLICATION, not facts about arbitrary contracts.
`Laws` gives local proof obligations: preparation establishes readiness, unrelated
steps preserve it, and readiness permits execution with the committed effect.
The theorems lift those local obligations to arbitrary finite interference runs.

An effect describes the intended externally visible operation, not the entire
post-state: unrelated balances and records may change while an obligation waits.
Protocol evidence, recovery authorization, scheduling, and data availability are
separate obligations. No fairness or eventual-execution claim is made here.
-/

namespace Applications.Prepared

structure Application (State Input Effect : Type*) where
  prepare : State → Input → State → Prop
  interfere : State → State → Prop
  ready : State → Input → Prop
  execute : State → Input → Effect → State → Prop
  intendedEffect : Input → Effect

variable {State Input Effect : Type*}

/-- The application author's local obligations. These are explicit hypotheses,
not axioms and not a definition of global execution success. -/
structure Laws (A : Application State Input Effect) : Prop where
  preparation_establishes_ready : ∀ {s i p}, A.prepare s i p → A.ready p i
  interference_preserves_ready : ∀ {s t i}, A.interfere s t → A.ready s i → A.ready t i
  ready_permits_execution : ∀ {s i}, A.ready s i →
    ∃ t, A.execute s i (A.intendedEffect i) t
  execution_has_intended_effect : ∀ {s i e t}, A.execute s i e t → e = A.intendedEffect i

/-- All finite sequences of the application's permitted unrelated transactions. -/
inductive InterferenceRun (A : Application State Input Effect) : State → State → Prop
  | refl {s} : InterferenceRun A s s
  | tail {s t u} : InterferenceRun A s t → A.interfere t u → InterferenceRun A s u

theorem ready_survives_interference {A : Application State Input Effect} (hA : Laws A)
    {s t : State} {i : Input} (hrun : InterferenceRun A s t) (hready : A.ready s i) :
    A.ready t i := by
  induction hrun with
  | refl => exact hready
  | tail _ hstep ih => exact hA.interference_preserves_ready hstep ih

/-- Preparation followed by any number of permitted unrelated transactions still
allows a successful execution with precisely the committed effect. -/
theorem prepared_execution_survives {A : Application State Input Effect} (hA : Laws A)
    {s p t : State} {i : Input} (hprepare : A.prepare s i p)
    (hrun : InterferenceRun A p t) :
    ∃ u, A.execute t i (A.intendedEffect i) u :=
  hA.ready_permits_execution
    (ready_survives_interference hA hrun (hA.preparation_establishes_ready hprepare))

/-- Different permitted waiting histories may produce different post-states,
but cannot change the intended effect of the same committed input. -/
theorem committed_effect_unique {A : Application State Input Effect} (hA : Laws A)
    {s t u v : State} {i : Input} {e f : Effect}
    (he : A.execute s i e u) (hf : A.execute t i f v) : e = f := by
  rw [hA.execution_has_intended_effect he, hA.execution_has_intended_effect hf]

/-- Conditional flow composition: every still-pending prepared leg can execute
once the protocol evidence needed for that leg is available.

`Evidence` must include authenticated input/chain binding and the protocol's
execution gate. `hallEvidence` is an explicit protocol obligation; this theorem
does not derive it from an actual Solidity execution on another chain. -/
theorem all_prepared_legs_executable
    {Leg : Type*} {A : Application State Input Effect} (hA : Laws A)
    (inputs : Leg → Input) (before prepared current : Leg → State)
    (Evidence : Leg → Prop)
    (hprepare : ∀ l, A.prepare (before l) (inputs l) (prepared l))
    (hwait : ∀ l, InterferenceRun A (prepared l) (current l))
    (hallEvidence : ∀ l, Evidence l) :
    ∀ l, Evidence l ∧ ∃ u, A.execute (current l) (inputs l) (A.intendedEffect (inputs l)) u :=
  fun l => ⟨hallEvidence l, prepared_execution_survives hA (hprepare l) (hwait l)⟩

end Applications.Prepared
