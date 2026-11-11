import Mathlib.Tactic

/-!
# Generic safety refinement by simulation

This file is a Mathlib-only, abstract foundation for composing verification
assumptions across layers (for example, a VM model, a Solidity-level model, and
a contract model). It states no correspondence theorem for an EVM, Solidity, or
any compiler. A concrete bridge must be supplied and proved separately.

The results concern finite-step safety only. Enabledness, progress, fairness,
and preservation of call or other external observations require additional
witnesses and are not implied by a state relation alone.
-/

namespace LayeredVerification

/-- Zero or more transitions of a relation. -/
inductive Run {State : Type*} (step : State → State → Prop) : State → State → Prop
  | refl (s : State) : Run step s s
  | tail {s t u : State} : Run step s t → step t u → Run step s u

theorem Run.transitive {State : Type*} {step : State → State → Prop}
    {s t u : State} (hst : Run step s t) (htu : Run step t u) :
    Run step s u := by
  induction htu with
  | refl => exact hst
  | tail _ hstep ih => exact Run.tail ih hstep

variable {A B C : Type*}
variable {stepA : A → A → Prop} {stepB : B → B → Prop} {stepC : C → C → Prop}

/-- Forward simulation: each concrete step can be matched by finitely many
abstract steps, ending in a state related to the concrete successor. -/
structure Simulation (concrete : A → A → Prop) (abstract : B → B → Prop) where
  Rel : A → B → Prop
  match_step : ∀ {a a' b}, Rel a b → concrete a a' →
    ∃ b', Run abstract b b' ∧ Rel a' b'

/-- A simulation lifts every finite concrete run to a related abstract run. -/
theorem Simulation.lift_run {concrete : A → A → Prop} {abstract : B → B → Prop}
    (sim : Simulation concrete abstract) {a a' b}
    (hrel : sim.Rel a b) (hrun : Run concrete a a') :
    ∃ b', Run abstract b b' ∧ sim.Rel a' b' := by
  induction hrun with
  | refl => exact ⟨b, Run.refl b, hrel⟩
  | tail _ hstep ih =>
    obtain ⟨bmid, hab, hmid⟩ := ih
    obtain ⟨b', hbb', hend⟩ := sim.match_step hmid hstep
    exact ⟨b', Run.transitive hab hbb', hend⟩

/-- Identity is a simulation. -/
def Simulation.refl (step : A → A → Prop) : Simulation step step where
  Rel := Eq
  match_step := by
    rintro a a' b rfl hstep
    exact ⟨a', Run.tail (Run.refl a) hstep, rfl⟩

/-- Forward simulations compose, including their zero-or-more matching paths. -/
def Simulation.comp (relAB : Simulation stepA stepB)
    (relBC : Simulation stepB stepC) : Simulation stepA stepC where
  Rel a c := ∃ b, relAB.Rel a b ∧ relBC.Rel b c
  match_step := by
    intro a a' c ⟨b, hab, hbc⟩ hstep
    obtain ⟨b', hbb', hab'⟩ := relAB.match_step hab hstep
    obtain ⟨c', hcc', hbc'⟩ := relBC.lift_run hbc hbb'
    exact ⟨c', hcc', b', hab', hbc'⟩

/-- A non-vacuous initial relation can be carried across any concrete run.
The explicit initial witnesses matter: a universally quantified safety result
without them could hold vacuously when the relation has no related states. -/
theorem reachable_related {sim : Simulation stepA stepB}
    {a₀ a : A} {b₀ : B}
    (hinit : sim.Rel a₀ b₀) (hrun : Run stepA a₀ a) :
    ∃ b, Run stepB b₀ b ∧ sim.Rel a b :=
  sim.lift_run hinit hrun

/-- Transfer a reachable-state safety predicate from the abstract system to the
concrete one. The concrete and abstract initial states must be explicitly
related, and `reflects` states how abstract safety implies concrete safety. -/
theorem safety_transfer {sim : Simulation stepA stepB}
    {a₀ : A} {b₀ : B} {SafeA : A → Prop} {SafeB : B → Prop}
    (hinit : sim.Rel a₀ b₀)
    (abstract_safe : ∀ b, Run stepB b₀ b → SafeB b)
    (reflects : ∀ a b, sim.Rel a b → SafeB b → SafeA a) :
    ∀ a, Run stepA a₀ a → SafeA a := by
  intro a hrun
  obtain ⟨b, hbrun, hab⟩ := reachable_related hinit hrun
  exact reflects a b hab (abstract_safe b hbrun)

end LayeredVerification
