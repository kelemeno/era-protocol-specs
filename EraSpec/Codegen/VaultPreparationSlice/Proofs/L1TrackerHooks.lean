import EraSpec.Codegen.VaultPreparationSlice.Properties.L1TrackerHooks
import EraSpec.Codegen.VaultPreparationSlice.Proofs.Refinement

/-! # Proofs: the vault slice with the deployed L1 accounting hook -/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.NativeTokenVaultBase (L1Ledger l1Hooks l1ToChain)

theorem L1HooksAgree : Properties.L1HooksAgree := by
  intro thisChain cm md hm
  refine ⟨fun acc st t c a m _ => ?_, hm⟩
  change (match l1ToChain thisChain acc a m with
    | some x => (Except.ok x : Except XFailure L1Ledger)
    | none => .error .empty).toOption = l1ToChain thisChain acc a m
  cases l1ToChain thisChain acc a m <;> rfl

theorem L1VaultSimulation : Properties.L1VaultSimulation := by
  intro d thisChain cm md hm
  exact Simulation d (l1CHooks thisChain cm) (l1Hooks thisChain md) (L1HooksAgree thisChain cm md hm)

theorem L1HooksAgreeSatisfiable : Properties.L1HooksAgreeSatisfiable := by
  have hm : MetadataAgrees (fun _ _ => .ok []) (fun _ _ => some []) := fun _ _ _ _ => rfl
  exact ⟨1, _, _, hm, L1HooksAgree 1 _ _ hm⟩

end Codegen.VaultPreparationSlice
