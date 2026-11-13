import EraSpec.Codegen.BridgedTokenSlice.Specs.Correspondence
import EraSpec.Core.Simulation

/-!
# Every call is at most one model step

`simulation` (`Properties/Refinement.lean`) is a `LayeredVerification.Simulation`, whose
`match_step` may answer a concrete step with any finite `Run` of model steps.  Its type
fixes no bound on their number.  This file states the bound and builds the simulation from
it.  Proofs: `../Proofs/AtMostOneStep.lean`.

* `call_matches_at_most_one_step`: from storage representing a well-formed model state,
  every successful call is matched by no model step (`t = s`) or by exactly one
  (`Contracts.BridgedStandardERC20.Step s t`).  The proof matches the getters with no step
  and `bridgeMint`, `bridgeBurn` and `transfer` with one.
* `simulation_at_most_one_step`: a simulation with the relation of `simulation`
  (`Rel ∧ WellFormed`), built from the first statement, together with its bound.
* `at_most_one_step_witness`: the premises hold together, for a call that must be matched
  by a real model step, not by a stutter.
-/

namespace Codegen.BridgedTokenSlice

open Codegen
open Contracts.BridgedStandardERC20 (State WellFormed)

/-- **EVERY SUCCESSFUL CALL IS AT MOST ONE MODEL STEP.**  From storage representing a
well-formed model state, every successful call (mutating or not, to any function, by any
caller, with any ABI-valid arguments) is matched by no model step (`t = s`) or by exactly one
(`Contracts.BridgedStandardERC20.Step s t`), ending in a well-formed model state that the new
storage represents. -/
abbrev Properties.call_matches_at_most_one_step :=
  ∀ (st st' : Storage) (s : State), Rel st s → WellFormed s → Step st st' →
    ∃ t, (t = s ∨ Contracts.BridgedStandardERC20.Step s t) ∧ Rel st' t ∧ WellFormed t

/-- **THE SIMULATION, WITH ITS BOUND.**  A forward simulation of the token model by the
program whose relation is `Rel ∧ WellFormed`, as in `simulation`, built from
`call_matches_at_most_one_step`, and under which every successful call from a related pair is
matched by at most one model step.  Its first two components are `simulation`'s statement;
the third is the bound, which the `Simulation` type cannot express. -/
abbrev Properties.simulation_at_most_one_step :=
  ∃ sim : LayeredVerification.Simulation Step Contracts.BridgedStandardERC20.Step,
    (∀ st s, sim.Rel st s ↔ Rel st s ∧ WellFormed s) ∧
    ∀ st st' s, sim.Rel st s → Step st st' →
      ∃ t, (t = s ∨ Contracts.BridgedStandardERC20.Step s t) ∧ sim.Rel st' t

/-- **THE PREMISES HOLD, AND THE MATCH IS A REAL MODEL STEP.**  There are storage
representing a well-formed model state and a successful call from it such that no model state
the new storage represents is the starting one, so the stutter disjunct of
`call_matches_at_most_one_step` cannot match the call.  The proof's instance is the
deployment with vault `1`, which represents the empty ledger, and the vault minting one unit
to address `2`. -/
abbrev Properties.at_most_one_step_witness :=
  ∃ (st st' : Storage) (s : State), Rel st s ∧ WellFormed s ∧ Step st st' ∧
    ∀ t, Rel st' t → t ≠ s

end Codegen.BridgedTokenSlice
