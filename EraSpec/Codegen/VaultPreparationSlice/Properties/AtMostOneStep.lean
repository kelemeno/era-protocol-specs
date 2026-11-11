import EraSpec.Codegen.VaultPreparationSlice.Specs.Correspondence
import EraSpec.Core.Simulation

/-!
# Every call is at most one step of the preparation trace

`Simulation` (`Properties/Refinement.lean`) is a `LayeredVerification.Simulation`, whose
`match_step` may answer a concrete step with any finite `Run` of trace steps.  Its type fixes
no bound on their number.  This file states the bound and builds the simulation from it.
Proofs: `../Proofs/AtMostOneStep.lean`.

* `CallMatchesAtMostOneTraceStep`: under agreeing hooks, from a system representing a trace
  ledger, every successful call to either contract is matched by no trace step (`L' = L`) or
  by exactly one (`AssetBridgePreparation.Step h L L'`).  The proof matches a `bridgeBurn`
  with the trace's `prepare`, the token's `transfer` with its `spend`, and the vault's views
  and the token's getters with no step.  The token's `bridgeMint` and `bridgeBurn` revert for
  every caller but the vault, and `Step` excludes calls from the vault.
* `SimulationAtMostOneTraceStep`: a simulation with the relation of `Simulation` (`SysRel`),
  built from the first statement, together with its bound.
* `AtMostOneTraceStepWitness`: the premises hold together, for a call that must be matched by
  a real trace step, not by a stutter.
-/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.NativeTokenVaultBase (Hooks)

/-- **EVERY SUCCESSFUL CALL IS AT MOST ONE TRACE STEP.**  Under agreeing hooks, from a
system representing a trace ledger (`SysRel`), every successful call to either contract
(`Step`) is matched by no trace step (`L' = L`) or by exactly one
(`AssetBridgePreparation.Step h L L'`), ending in a ledger that the new system represents. -/
def Properties.CallMatchesAtMostOneTraceStep : Prop :=
  ∀ {Acct : Type} (d : Deployment) (ch : CHooks Acct) (h : Hooks Acct), HooksAgree ch h →
    ∀ (sys sys' : Sys Acct) (L : AssetBridgePreparation.Ledger Acct),
      SysRel d sys L → Step d ch sys sys' →
      ∃ L', (L' = L ∨ AssetBridgePreparation.Step h L L') ∧ SysRel d sys' L'

/-- **THE SIMULATION, WITH ITS BOUND.**  For agreeing hooks, a forward simulation of the
protocol preparation trace by the two programs whose relation is `SysRel`, as in
`Simulation`, built from `CallMatchesAtMostOneTraceStep`, and under which every successful
call from a related pair is matched by at most one trace step.  Its first two components are
`Simulation`'s statement; the third is the bound, which the `Simulation` type cannot
express. -/
def Properties.SimulationAtMostOneTraceStep : Prop :=
  ∀ {Acct : Type} (d : Deployment) (ch : CHooks Acct) (h : Hooks Acct), HooksAgree ch h →
    ∃ sim : LayeredVerification.Simulation (Step d ch) (AssetBridgePreparation.Step h),
      (∀ sys L, sim.Rel sys L ↔ SysRel d sys L) ∧
      ∀ sys sys' L, sim.Rel sys L → Step d ch sys sys' →
        ∃ L', (L' = L ∨ AssetBridgePreparation.Step h L L') ∧ sim.Rel sys' L'

/-- **THE PREMISES HOLD, AND THE MATCH IS A REAL TRACE STEP.**  There are agreeing hooks, a
system representing a trace ledger and a successful call from it such that no ledger the new
system represents is the starting one, so the stutter disjunct of
`CallMatchesAtMostOneTraceStep` cannot match the call.  The proof's instance is the concrete
vault of `Properties/Witnesses.lean`, with an empty journal, preparing its accepted request:
the call journals an entry, and the starting ledger has no pending obligation. -/
def Properties.AtMostOneTraceStepWitness : Prop :=
  ∃ (d : Deployment) (ch : CHooks Unit) (h : Hooks Unit) (sys sys' : Sys Unit)
    (L : AssetBridgePreparation.Ledger Unit),
    HooksAgree ch h ∧ SysRel d sys L ∧ Step d ch sys sys' ∧ ∀ L', SysRel d sys' L' → L' ≠ L

end Codegen.VaultPreparationSlice
