import EraSpec.Codegen.VaultPreparationSlice.Specs.L1TrackerHooks
import EraSpec.Core.Simulation

/-!
# Properties: the vault slice with the deployed L1 accounting hook

Statements about `Specs/L1TrackerHooks.lean`.  Proofs: `../Proofs/L1TrackerHooks.lean`.

* `L1HooksAgree`: the concrete L1 hook agrees with the model's L1 hook
  (`Contracts.NativeTokenVaultBase.l1Hooks`), given an agreeing metadata hook.  So the slice's
  `HooksAgree` premise is met by the deployed L1 accounting hook, whose model is the identity on the
  bridged branch the slice transcribes (`Contracts.NativeTokenVaultBase.Properties.L1BridgedBranchHooksAreIdentity`).
* `L1VaultSimulation`: the slice's `Simulation` with that hook: every successful call to the vault
  or the token is matched by at most one step of the protocol preparation trace run with the L1
  hooks.
* `L1HooksAgreeSatisfiable`: the metadata premise is satisfiable.
-/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.NativeTokenVaultBase (L1Ledger l1Hooks)

/-- **THE DEPLOYED L1 HOOK MEETS THE SLICE'S HOOK PREMISE.** -/
def Properties.L1HooksAgree : Prop :=
  ∀ (thisChain : Word) (cm : Storage → Word → Except XFailure Bytes)
    (md : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes),
    MetadataAgrees cm md → HooksAgree (l1CHooks thisChain cm) (l1Hooks thisChain md)

/-- **THE SLICE'S SIMULATION, WITH THE DEPLOYED L1 HOOK.** -/
def Properties.L1VaultSimulation : Prop :=
  ∀ (d : Deployment) (thisChain : Word) (cm : Storage → Word → Except XFailure Bytes)
    (md : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes),
    MetadataAgrees cm md →
      ∃ sim : LayeredVerification.Simulation (Step d (l1CHooks thisChain cm))
          (AssetBridgePreparation.Step (l1Hooks thisChain md)),
        ∀ sys L, sim.Rel sys L ↔ SysRel d sys L

/-- **THE METADATA PREMISE IS SATISFIABLE.** -/
def Properties.L1HooksAgreeSatisfiable : Prop :=
  ∃ (thisChain : Word) (cm : Storage → Word → Except XFailure Bytes)
    (md : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes),
    MetadataAgrees cm md ∧ HooksAgree (l1CHooks thisChain cm) (l1Hooks thisChain md)

end Codegen.VaultPreparationSlice
