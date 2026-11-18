import EraSpec.Codegen.VaultPreparationSlice.Specs.L1TrackerHooks
import EraSpec.Core.Simulation

/-!
# Properties: the vault slice with the deployed L1 accounting hook

Statements about `Specs/L1TrackerHooks.lean`.  Proofs: `../Proofs/L1TrackerHooks.lean`.

* `L1HooksAgree`: the concrete L1 hook agrees with the model's L1 hook
  (`Contracts.NativeTokenVaultBase.l1Hooks`), given an agreeing metadata hook.  So the slice's
  `HooksAgree` premise is met by the L1 accounting hook of the pin, whose model is the identity on
  the bridged branch the slice transcribes
  (`Contracts.NativeTokenVaultBase.Properties.L1BridgedBranchHooksAreIdentity`).
* `L1VaultSimulation`: the slice's simulation with that hook, with its bound: every successful call
  to the vault or the token, from a related pair, is matched by at most one step of the protocol
  preparation trace run with the L1 hooks (`SimulationAtMostOneTraceStep`, instantiated).
* `L1HooksAgreeSatisfiable`: for every model metadata hook there is a concrete one agreeing with
  it, so the metadata premise of both results is satisfiable whatever the model's metadata hook.
-/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.NativeTokenVaultBase (L1Ledger l1Hooks)

/-- **THE L1 HOOK OF THE PIN MEETS THE SLICE'S HOOK PREMISE.** -/
def Properties.L1HooksAgree : Prop :=
  ∀ (thisChain : Word) (cm : Storage → Word → Except XFailure Bytes)
    (md : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes),
    MetadataAgrees cm md → HooksAgree (l1CHooks thisChain cm) (l1Hooks thisChain md)

/-- **THE SLICE'S SIMULATION, WITH THE L1 HOOK OF THE PIN.**  For an agreeing metadata hook: a
forward simulation of the protocol preparation trace run with the L1 hooks, whose relation is
`SysRel`, under which every successful call from a related pair is matched by no trace step or by
exactly one. -/
def Properties.L1VaultSimulation : Prop :=
  ∀ (d : Deployment) (thisChain : Word) (cm : Storage → Word → Except XFailure Bytes)
    (md : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes),
    MetadataAgrees cm md →
      ∃ sim : LayeredVerification.Simulation (Step d (l1CHooks thisChain cm))
          (AssetBridgePreparation.Step (l1Hooks thisChain md)),
        (∀ sys L, sim.Rel sys L ↔ SysRel d sys L) ∧
        ∀ sys sys' L, sim.Rel sys L → Step d (l1CHooks thisChain cm) sys sys' →
          ∃ L', (L' = L ∨ AssetBridgePreparation.Step (l1Hooks thisChain md) L L') ∧
            sim.Rel sys' L'

/-- **THE METADATA PREMISE IS SATISFIABLE FOR EVERY MODEL METADATA HOOK.** -/
def Properties.L1HooksAgreeSatisfiable : Prop :=
  ∀ (md : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes),
    ∃ cm : Storage → Word → Except XFailure Bytes, MetadataAgrees cm md

end Codegen.VaultPreparationSlice
