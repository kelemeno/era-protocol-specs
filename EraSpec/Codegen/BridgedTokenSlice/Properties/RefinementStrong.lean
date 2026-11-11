import EraSpec.Codegen.BridgedTokenSlice.Specs.Correspondence
import EraSpec.Core.Simulation

/-!
# Every successful call is matched by at most one model step

Statements that strengthen `Properties.simulation` of `Properties/Refinement.lean`.  Proofs:
`../Proofs/RefinementStrong.lean`.

## Why

`Properties.simulation` says that some `LayeredVerification.Simulation` has the relation
`Rel ∧ WellFormed`.  A `Simulation` matches each concrete step by a `Run` of the abstract
system, which is zero or more model steps.  So the statement only says that every successful
call is matched by finitely many model steps.  Its docstring and `EraSpec/Codegen/README.md`
say "at most one".  The per-entry-point results (`mint_refines`, `burn_refines`,
`transfer_refines`, `views_exact`) imply the single-step form only after a case analysis over
the program's functions and the ABI-validity cases of `Step`, and no statement records it.

## What is claimed

* `step_matched_by_at_most_one`: take a storage related to a well-formed model state.  Every
  successful call from it, to any function, by any caller, with ABI-valid arguments, reaches
  storage related to a well-formed model state that is the same state or the result of exactly
  one model step.
* `simulation_at_most_one`: the same as a `Simulation` instance whose relation is that of
  `Properties.simulation`, with every match a stutter or a single model step.
* `step_matched_by_at_most_one_witness`: the premises hold together, for a call whose match is
  a model step that changes the model state.  The single-step disjunct is therefore not idle.
-/

namespace Codegen.BridgedTokenSlice

open Codegen
open Contracts.BridgedStandardERC20 (State WellFormed)

/-- **EVERY SUCCESSFUL CALL IS MATCHED BY AT MOST ONE MODEL STEP.**  From a storage related to a
well-formed model state, every successful call, to any function, by any caller, with ABI-valid
arguments, reaches a storage related to a well-formed model state.  That state is either the
same one (a stutter) or the result of exactly one model step. -/
abbrev Properties.step_matched_by_at_most_one :=
  ∀ (st st' : Storage) (s : State), Rel st s → WellFormed s → Step st st' →
    ∃ t, (t = s ∨ Contracts.BridgedStandardERC20.Step s t) ∧ Rel st' t ∧ WellFormed t

/-- **A FORWARD SIMULATION WHOSE MATCHES ARE AT MOST ONE STEP.**  Some `Simulation` of the model
by the program has the relation `Rel ∧ WellFormed`, as in `Properties.simulation`.  Every
successful call from a related pair is matched by a stutter or by a single model step. -/
abbrev Properties.simulation_at_most_one :=
  ∃ sim : LayeredVerification.Simulation Step Contracts.BridgedStandardERC20.Step,
    (∀ st s, sim.Rel st s ↔ Rel st s ∧ WellFormed s) ∧
    ∀ st st' s, sim.Rel st s → Step st st' →
      ∃ t, (t = s ∨ Contracts.BridgedStandardERC20.Step s t) ∧ sim.Rel st' t

/-- **ITS PREMISES ARE SATISFIABLE, WITH A MATCH THAT MOVES THE MODEL.**  A storage related to a
well-formed model state, a successful call from it, and a model step to a different
well-formed state related to the storage the call reaches. -/
abbrev Properties.step_matched_by_at_most_one_witness :=
  ∃ (st st' : Storage) (s t : State), Rel st s ∧ WellFormed s ∧ Step st st' ∧
    Contracts.BridgedStandardERC20.Step s t ∧ t ≠ s ∧ Rel st' t ∧ WellFormed t

end Codegen.BridgedTokenSlice
