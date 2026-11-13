import EraSpec.Codegen.BridgedTokenSlice.Properties.AtMostOneStep
import EraSpec.Codegen.BridgedTokenSlice.Proofs.Refinement

/-!
# Proofs: every call is at most one model step

The case split of `match_step` (`Proofs/Refinement.lean`), kept with its bound: dispatch
resolves the function, the getters leave storage unchanged and the model stutters, and
`bridgeMint`, `bridgeBurn` and `transfer` succeed exactly when the model's operation does
(`mint_refines`, `burn_refines`, `transfer_refines`), which is one model step.  The simulation
turns `t = s` into the empty run and a step into a run of one.
-/

namespace Codegen.BridgedTokenSlice

open Codegen
open Contracts.BridgedStandardERC20 (Address State WellFormed Config empty)
open LayeredVerification (Run)

theorem call_matches_at_most_one_step : Properties.call_matches_at_most_one_step := by
  intro st st' s hr hw hstep
  obtain ⟨⟨fn, hfind, hargs⟩, hcall⟩ := hstep
  rename_i fname caller args r
  have hmem := List.mem_of_find?_eq_some hfind
  have hname : fn.name = fname := by simpa using List.find?_some hfind
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at hmem
  -- getters: storage is unchanged, so the model stutters
  have stutter : r.st = st → ∃ t, (t = s ∨ Contracts.BridgedStandardERC20.Step s t) ∧
      Rel r.st t ∧ WellFormed t := fun h => ⟨s, Or.inl rfl, h ▸ hr, hw⟩
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · -- bridgeMint: the model's `mint`
    obtain rfl : fname = "bridgeMint" := by rw [← hname]; rfl
    obtain ⟨x, y, rfl, hx⟩ := forall₂_two hargs
    have hx' := hx rfl
    rw [← addrWord_toAddr x hx'] at hcall
    rcases hm : Contracts.BridgedStandardERC20.mint s caller (toAddr x hx') y with _ | t
    · obtain ⟨e, he⟩ := (mint_refines hw hr caller _ y).1 hm
      rw [he] at hcall; exact nomatch hcall
    · obtain ⟨r', he, hrel, -⟩ := (mint_refines hw hr caller _ y).2 t hm
      rw [he] at hcall; cases hcall
      exact ⟨t, Or.inr (.mint hm), hrel,
        Contracts.BridgedStandardERC20.mint_preserves_ledger hw hm⟩
  · -- bridgeBurn: the model's `burn`
    obtain rfl : fname = "bridgeBurn" := by rw [← hname]; rfl
    obtain ⟨x, y, rfl, hx⟩ := forall₂_two hargs
    have hx' := hx rfl
    rw [← addrWord_toAddr x hx'] at hcall
    rcases hm : Contracts.BridgedStandardERC20.burn s caller (toAddr x hx') y with _ | t
    · obtain ⟨e, he⟩ := (burn_refines hw hr caller _ y).1 hm
      rw [he] at hcall; exact nomatch hcall
    · obtain ⟨r', he, hrel, -⟩ := (burn_refines hw hr caller _ y).2 t hm
      rw [he] at hcall; cases hcall
      exact ⟨t, Or.inr (.burn hm), hrel,
        Contracts.BridgedStandardERC20.burn_preserves_ledger hw hm⟩
  · -- transfer: the model's `transfer`
    obtain rfl : fname = "transfer" := by rw [← hname]; rfl
    obtain ⟨x, y, rfl, hx⟩ := forall₂_two hargs
    have hx' := hx rfl
    rw [← addrWord_toAddr x hx'] at hcall
    rcases hm : Contracts.BridgedStandardERC20.transfer s caller (toAddr x hx') y with _ | t
    · obtain ⟨e, he⟩ := (transfer_refines hw hr caller _ y).1 hm
      rw [he] at hcall; exact nomatch hcall
    · obtain ⟨r', he, hrel, -⟩ := (transfer_refines hw hr caller _ y).2 t hm
      rw [he] at hcall; cases hcall
      exact ⟨t, Or.inr (.transfer hm), hrel,
        (Contracts.BridgedStandardERC20.transfer_preserves_ledger hw hm).1⟩
  · -- balanceOf
    obtain rfl : fname = "balanceOf" := by rw [← hname]; rfl
    obtain ⟨x, rfl⟩ := forall₂_one hargs
    rw [call_balanceOf] at hcall; cases hcall; exact stutter rfl
  · -- totalSupply
    obtain rfl : fname = "totalSupply" := by rw [← hname]; rfl
    rw [forall₂_nil hargs] at hcall
    rw [call_totalSupply] at hcall; cases hcall; exact stutter rfl
  · -- nativeTokenVault
    obtain rfl : fname = "nativeTokenVault" := by rw [← hname]; rfl
    rw [forall₂_nil hargs] at hcall
    rw [call_nativeTokenVault] at hcall; cases hcall; exact stutter rfl

/-- The simulation built from `call_matches_at_most_one_step`: no step is the empty run,
one step a run of one. -/
def atMostOneStepSim :
    LayeredVerification.Simulation Step Contracts.BridgedStandardERC20.Step where
  Rel st s := Rel st s ∧ WellFormed s
  match_step := by
    rintro st st' s ⟨hr, hw⟩ hstep
    obtain ⟨t, ht, hrel, hwt⟩ := call_matches_at_most_one_step st st' s hr hw hstep
    refine ⟨t, ?_, hrel, hwt⟩
    rcases ht with rfl | ht
    · exact Run.refl t
    · exact Run.tail (Run.refl s) ht

theorem simulation_at_most_one_step : Properties.simulation_at_most_one_step :=
  ⟨atMostOneStepSim, fun _ _ => Iff.rfl, fun st st' s ⟨hr, hw⟩ hstep =>
    call_matches_at_most_one_step st st' s hr hw hstep⟩

/-! ## The witness -/

theorem at_most_one_step_witness : Properties.at_most_one_step_witness := by
  let config : Config := ⟨1, 0, 0⟩
  have hv : config.vault ≠ 0 := by decide
  obtain ⟨r, -, hrel, -⟩ := deploy_establishes 0 config hv
  obtain ⟨hwe, funded, hm, -, -⟩ :=
    Contracts.BridgedStandardERC20.one_unit_roundtrip config 2 hv (by decide)
  obtain ⟨r', hcall, hrel', -, -⟩ := (mint_refines hwe hrel config.vault 2 1).2 funded hm
  have habi : AbiValid "bridgeMint" [addrWord 2, 1] :=
    ⟨bridgeMint, find_bridgeMint,
      List.Forall₂.cons (fun _ => (2 : Address).isLt)
        (List.Forall₂.cons (fun h => nomatch h) List.Forall₂.nil)⟩
  have hsupply : funded.totalSupply = 1 := by
    rw [(Contracts.BridgedStandardERC20.mint_exact hm).2.2.2.1]
    rfl
  refine ⟨r.st, r'.st, empty config, hrel, hwe, Step.call habi hcall, ?_⟩
  rintro t ht rfl
  have h := ht.supply.symm.trans hrel'.supply
  rw [hsupply] at h
  exact absurd h (by decide)

end Codegen.BridgedTokenSlice
