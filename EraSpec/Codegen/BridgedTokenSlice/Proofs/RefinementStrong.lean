import EraSpec.Codegen.BridgedTokenSlice.Properties.RefinementStrong
import EraSpec.Codegen.BridgedTokenSlice.Proofs.Refinement

/-!
# Proofs: every successful call is matched by at most one model step

The case analysis of `Proofs/Refinement.lean`'s `match_step`, with its conclusion kept.  Each
mutator is matched by the model step that `mint_refines`, `burn_refines` or
`transfer_refines` names, and each getter by the stutter that `call_balanceOf`,
`call_totalSupply` and `call_nativeTokenVault` give.  `simulation_at_most_one` is witnessed by
the existing `simulationWitness`, whose relation is already `Rel ∧ WellFormed`.  The witness
deploys with vault `1` and has the vault mint one unit to address `2`.
-/

namespace Codegen.BridgedTokenSlice

open Codegen
open Contracts.BridgedStandardERC20 (Address State WellFormed Config empty)

/-- `match_step` with the matching run kept to a stutter or one model step. -/
theorem match_step_at_most_one {st st' : Storage} {s : State} (hr : Rel st s)
    (hw : WellFormed s) (hstep : Step st st') :
    ∃ t, (t = s ∨ Contracts.BridgedStandardERC20.Step s t) ∧ Rel st' t ∧ WellFormed t := by
  obtain ⟨⟨fn, hfind, hargs⟩, hcall⟩ := hstep
  rename_i fname caller args r
  have hmem := List.mem_of_find?_eq_some hfind
  have hname : fn.name = fname := by simpa using List.find?_some hfind
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at hmem
  -- getters: storage is unchanged, so the model stutters
  have stutter : r.st = st → ∃ t, (t = s ∨ Contracts.BridgedStandardERC20.Step s t) ∧
      Rel r.st t ∧ WellFormed t := fun h => ⟨s, Or.inl rfl, h ▸ hr, hw⟩
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · -- bridgeMint: one model `mint`
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
  · -- bridgeBurn: one model `burn`
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
  · -- transfer: one model `transfer`
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
  · -- balanceOf: stutter
    obtain rfl : fname = "balanceOf" := by rw [← hname]; rfl
    obtain ⟨x, rfl⟩ := forall₂_one hargs
    rw [call_balanceOf] at hcall; cases hcall; exact stutter rfl
  · -- totalSupply: stutter
    obtain rfl : fname = "totalSupply" := by rw [← hname]; rfl
    rw [forall₂_nil hargs] at hcall
    rw [call_totalSupply] at hcall; cases hcall; exact stutter rfl
  · -- nativeTokenVault: stutter
    obtain rfl : fname = "nativeTokenVault" := by rw [← hname]; rfl
    rw [forall₂_nil hargs] at hcall
    rw [call_nativeTokenVault] at hcall; cases hcall; exact stutter rfl

/-! ## The witness: the vault mints one unit -/

/-- The witness's configuration: vault `1`, origin token `0`, asset id `0`. -/
def atMostOneConfig : Config := ⟨1, 0, 0⟩

theorem atMostOne_mint :
    Contracts.BridgedStandardERC20.mint (empty atMostOneConfig) 1 2 1 =
      some (Contracts.BridgedStandardERC20.mintEffect (empty atMostOneConfig) 2 1) := by
  have hallowed : Contracts.BridgedStandardERC20.MintAllowed (empty atMostOneConfig) 1 2 1 :=
    ⟨by decide, rfl, by decide, by decide⟩
  unfold Contracts.BridgedStandardERC20.mint
  rw [ite_eq_left hallowed]

/-- `bridgeMint(2, 1)` is ABI-valid: its address argument is below `2^160`. -/
theorem atMostOne_abiValid : AbiValid "bridgeMint" [addrWord 2, 1] :=
  ⟨bridgeMint, find_bridgeMint,
    .cons (fun _ => (2 : Address).isLt) (.cons (fun h => absurd h (by decide)) .nil)⟩

end Codegen.BridgedTokenSlice

/-! ## Certificates -/

namespace Codegen.BridgedTokenSlice

open Contracts.BridgedStandardERC20 (State WellFormed Config empty)

theorem step_matched_by_at_most_one : Properties.step_matched_by_at_most_one :=
  fun _ _ _ hr hw hstep => match_step_at_most_one hr hw hstep

theorem simulation_at_most_one : Properties.simulation_at_most_one :=
  ⟨simulationWitness, fun _ _ => Iff.rfl, fun _ _ _ ⟨hr, hw⟩ hstep =>
    let ⟨t, hts, hrel, hwt⟩ := match_step_at_most_one hr hw hstep
    ⟨t, hts, hrel, hwt⟩⟩

theorem step_matched_by_at_most_one_witness : Properties.step_matched_by_at_most_one_witness := by
  obtain ⟨r, -, hrel, -⟩ := deploy_establishes 0 atMostOneConfig (by decide)
  have hw := empty_wellFormed atMostOneConfig
  obtain ⟨r', hcall, hrel', -, -⟩ := (mint_refines hw hrel 1 2 1).2 _ atMostOne_mint
  refine ⟨r.st, r'.st, empty atMostOneConfig, _, hrel, hw, .call atMostOne_abiValid hcall,
    .mint atMostOne_mint, ?_, hrel',
    Contracts.BridgedStandardERC20.mint_preserves_ledger hw atMostOne_mint⟩
  intro h
  have := congrArg State.totalSupply h
  simp [Contracts.BridgedStandardERC20.mintEffect, empty] at this

end Codegen.BridgedTokenSlice
