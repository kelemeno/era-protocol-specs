import EraSpec.Codegen.VaultPreparationSlice.Specs.Correspondence
import EraSpec.Core.Simulation

/-!
# Every successful call is matched by at most one trace step

Statements that strengthen `Properties.Simulation` of `Properties/Refinement.lean`.  Proofs:
`../Proofs/RefinementStrong.lean`.

## Why

`Properties.Simulation` says that, for agreeing hooks, some `LayeredVerification.Simulation`
of the protocol preparation trace has the relation `SysRel`.  A `Simulation` matches each
concrete step by a `Run` of the trace, which is zero or more `AssetBridgePreparation.Step`s.
So the statement only says that every successful call is matched by finitely many trace
steps.  Its docstring and this slice's module header say "at most one".  `SysRel` fixes the
journal and the related vault state, so a longer match must still end in a related ledger.
The statement still does not rule such a match out.

## What is claimed

* `StepMatchedByAtMostOneTraceStep`: take a system related to a trace ledger by `SysRel`,
  under agreeing hooks.  Every successful call from it, to either contract, reaches a system
  related to the same ledger or to the result of exactly one trace step.
* `SimulationAtMostOneTraceStep`: the same as a `Simulation` instance whose relation is that
  of `Properties.Simulation`, with every match a stutter or a single trace step.
* `StepMatchedByAtMostOneTraceStepWitness`: the premises hold together, for a `bridgeBurn`
  matched by a trace step.  The call adds a journal entry, so no stutter can match it, and the
  single-step disjunct is not idle.
-/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.NativeTokenVaultBase (Hooks)

/-- **EVERY SUCCESSFUL CALL IS MATCHED BY AT MOST ONE TRACE STEP.**  Under agreeing hooks, from
a system related to a trace ledger by `SysRel`, every successful call, to either contract,
reaches a system related by `SysRel` to the same ledger (a stutter) or to the result of exactly
one step of `AssetBridgePreparation.Step`. -/
def Properties.StepMatchedByAtMostOneTraceStep : Prop :=
  ∀ {Acct : Type} (d : Deployment) (ch : CHooks Acct) (h : Hooks Acct), HooksAgree ch h →
    ∀ (sys sys' : Sys Acct) (L : AssetBridgePreparation.Ledger Acct),
      SysRel d sys L → Step d ch sys sys' →
        ∃ L', (L' = L ∨ AssetBridgePreparation.Step h L L') ∧ SysRel d sys' L'

/-- **A FORWARD SIMULATION WHOSE MATCHES ARE AT MOST ONE TRACE STEP.**  For agreeing hooks,
some `Simulation` of the preparation trace by the two programs has the relation `SysRel`, as in
`Properties.Simulation`.  Every successful call from a related pair is matched by a stutter or
by a single trace step. -/
def Properties.SimulationAtMostOneTraceStep : Prop :=
  ∀ {Acct : Type} (d : Deployment) (ch : CHooks Acct) (h : Hooks Acct), HooksAgree ch h →
    ∃ sim : LayeredVerification.Simulation (Step d ch) (AssetBridgePreparation.Step h),
      (∀ sys L, sim.Rel sys L ↔ SysRel d sys L) ∧
      ∀ sys sys' L, sim.Rel sys L → Step d ch sys sys' →
        ∃ L', (L' = L ∨ AssetBridgePreparation.Step h L L') ∧ sim.Rel sys' L'

/-- **ITS PREMISES ARE SATISFIABLE, WITH A MATCH THAT IS A TRACE STEP.**  Agreeing hooks, a
system related to a ledger, a successful call from it that adds a journal entry, and a trace
step from that ledger to one related to the system the call reaches. -/
def Properties.StepMatchedByAtMostOneTraceStepWitness : Prop :=
  ∃ (d : Deployment) (ch : CHooks Unit) (h : Hooks Unit) (sys sys' : Sys Unit)
    (L L' : AssetBridgePreparation.Ledger Unit),
    HooksAgree ch h ∧ SysRel d sys L ∧ Step d ch sys sys' ∧
      AssetBridgePreparation.Step h L L' ∧ SysRel d sys' L' ∧ sys'.journal ≠ sys.journal

end Codegen.VaultPreparationSlice
