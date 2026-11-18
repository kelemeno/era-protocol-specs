import EraSpec.Codegen.VaultPreparationSlice.Properties.L1TrackerHooks
import EraSpec.Codegen.VaultPreparationSlice.Proofs.AtMostOneStep

/-! # Proofs: the vault slice with the L1 accounting hook of the pin -/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.NativeTokenVaultBase (L1Ledger l1Hooks l1ToChain Hooks)

theorem L1HooksAgree : Properties.L1HooksAgree := by
  intro thisChain cm md hm
  refine ⟨fun acc st t c a m _ => ?_, hm⟩
  change (match l1ToChain thisChain acc a m with
    | some x => (Except.ok x : Except XFailure L1Ledger)
    | none => .error .empty).toOption = l1ToChain thisChain acc a m
  cases l1ToChain thisChain acc a m <;> rfl

theorem L1VaultSimulation : Properties.L1VaultSimulation := by
  intro d thisChain cm md hm
  exact SimulationAtMostOneTraceStep d (l1CHooks thisChain cm) (l1Hooks thisChain md)
    (L1HooksAgree thisChain cm md hm)

theorem L1HooksAgreeSatisfiable : Properties.L1HooksAgreeSatisfiable := by
  intro md
  let h : Hooks L1Ledger := ⟨fun acc _ _ _ _ => some acc, md⟩
  exact ⟨(liftHooks h).metadata, fun st t o ht => (liftHooks_agree h).2 st t o ht⟩

end Codegen.VaultPreparationSlice
