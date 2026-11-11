import EraSpec.Codegen.VaultPreparationSlice.Properties.AtMostOneStep
import EraSpec.Codegen.VaultPreparationSlice.Proofs.Witnesses

/-!
# Proofs: every call is at most one step of the preparation trace

The case split of `simulationWitness` (`Proofs/Refinement.lean`), kept with its bound.  A
`bridgeBurn` is one `prepare` (`BridgeBurnSuccessIsPreparation`); a vault view changes nothing
(`xcall_view`); a token call by anyone but the vault is one `spend` for a `transfer`, nothing
for a getter, and impossible for `bridgeMint` and `bridgeBurn` (`token_step_at_most_one`, the
case split of `token_step` with the same bound).  The simulation turns `L' = L` into the
empty run and a step into a run of one.  The witness is the accepted request of
`Proofs/Witnesses.lean`.
-/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.BridgedStandardERC20 (Address)
open Codegen.BridgedTokenSlice (addrWord addrWord_inj)
open Contracts.NativeTokenVaultBase (Hooks)
open LayeredVerification (Run)

variable {Acct : Type}

/-- A token getter: no trace step. -/
theorem stutter_at_most_one {d : Deployment} {h : Hooks Acct} {sys : Sys Acct}
    {L : AssetBridgePreparation.Ledger Acct} {st : Storage} (hsr : SysRel d sys L)
    (hst : st = sys.world.token) :
    ∃ L', (L' = L ∨ AssetBridgePreparation.Step h L L') ∧
      SysRel d ⟨sys.vault, { sys.world with token := st }, sys.journal⟩ L' := by
  subst hst
  exact ⟨L, Or.inl rfl, hsr⟩

/-- A successful call to the token by anyone but the vault is one trace `spend` (a
`transfer`) or no trace step (a getter); `bridgeMint` and `bridgeBurn` revert. -/
theorem token_step_at_most_one {d : Deployment} {h : Hooks Acct} {sys : Sys Acct}
    {L : AssetBridgePreparation.Ledger Acct} {fname : String} {caller : Address}
    {args : List Word} {r : Success}
    (hsr : SysRel d sys L) (hc : caller ≠ d.vault) (hv : TokenAbiValid fname args)
    (hcall : Codegen.call tokenProgram fname (addrWord caller) args sys.world.token =
      some (.ok r)) :
    ∃ L', (L' = L ∨ AssetBridgePreparation.Step h L L') ∧
      SysRel d ⟨sys.vault, { sys.world with token := r.st }, sys.journal⟩ L' := by
  obtain ⟨fn, hfind, hargs⟩ := hv
  have hmem := List.mem_of_find?_eq_some hfind
  have hname : fn.name = fname := by simpa using List.find?_some hfind
  simp only [tokenProgram, BridgedTokenSlice.program, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hmem
  have hvault : sys.world.token.scalars "_nativeTokenVault" = addrWord d.vault := by
    rw [hsr.rel.tokenState.base.vault, hsr.wf.2.1, hsr.rel.vault]
  have hne : addrWord caller ≠ sys.world.token.scalars "_nativeTokenVault" := by
    rw [hvault]; exact fun h0 => hc (addrWord_inj.mp h0)
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- bridgeMint: only the vault may call it
    obtain rfl : fname = "bridgeMint" := by rw [← hname]; rfl
    obtain ⟨x, y, rfl, -⟩ := BridgedTokenSlice.forall₂_two hargs
    rw [tokenCall_bridgeMint, BridgedTokenSlice.call_mint, ite_eq_left hne] at hcall
    cases hcall
  · -- bridgeBurn: only the vault may call it
    obtain rfl : fname = "bridgeBurn" := by rw [← hname]; rfl
    obtain ⟨x, y, rfl, -⟩ := BridgedTokenSlice.forall₂_two hargs
    rw [tokenCall_bridgeBurn, BridgedTokenSlice.call_burn, ite_eq_left hne] at hcall
    cases hcall
  · -- transfer: one trace `spend`
    obtain rfl : fname = "transfer" := by rw [← hname]; rfl
    obtain ⟨x, y, rfl, hx⟩ := BridgedTokenSlice.forall₂_two hargs
    have hx' := hx rfl
    have hscal := tokenTransfer_scalars hcall
    rw [tokenCall_transfer, ← BridgedTokenSlice.addrWord_toAddr x hx'] at hcall
    rcases hm : Contracts.BridgedStandardERC20.transfer L.vault.token caller
        (BridgedTokenSlice.toAddr x hx') y with _ | t
    · obtain ⟨e, he⟩ := (BridgedTokenSlice.transfer_refines hsr.wf.1 hsr.rel.tokenState.base
        caller _ y).1 hm
      rw [he] at hcall; cases hcall
    · obtain ⟨r', he, hrel', -⟩ := (BridgedTokenSlice.transfer_refines hsr.wf.1
        hsr.rel.tokenState.base caller _ y).2 t hm
      rw [he] at hcall
      cases hcall
      obtain ⟨hl', -, hcfg⟩ :=
        Contracts.BridgedStandardERC20.transfer_preserves_ledger hsr.wf.1 hm
      refine ⟨⟨{ L.vault with token := t }, L.pending⟩, Or.inr (.spend hm), ?_⟩
      refine ⟨⟨hsr.rel.vault, hsr.rel.token, hsr.rel.chainId, hsr.rel.router, hsr.rel.paused,
        hsr.rel.baseAsset, hsr.rel.tokenFor, hsr.rel.assetFor, hsr.rel.origin,
        ⟨hrel', ?_, ?_⟩, hsr.rel.acct⟩, ⟨hl', ?_, ?_, hsr.wf.2.2.2⟩, hsr.journal⟩
      · rw [hscal, hsr.rel.tokenState.originToken, hcfg]
      · rw [hscal, hsr.rel.tokenState.assetId, hcfg]
      · exact (congrArg Contracts.BridgedStandardERC20.Config.vault hcfg).trans hsr.wf.2.1
      · exact (congrArg Contracts.BridgedStandardERC20.Config.assetId hcfg).trans hsr.wf.2.2.1
  · -- balanceOf
    obtain rfl : fname = "balanceOf" := by rw [← hname]; rfl
    obtain ⟨x, rfl⟩ := BridgedTokenSlice.forall₂_one hargs
    rw [tokenCall_balanceOf, BridgedTokenSlice.call_balanceOf] at hcall
    cases hcall
    exact stutter_at_most_one hsr rfl
  · -- totalSupply
    obtain rfl : fname = "totalSupply" := by rw [← hname]; rfl
    rw [BridgedTokenSlice.forall₂_nil hargs, tokenCall_totalSupply,
      BridgedTokenSlice.call_totalSupply] at hcall
    cases hcall
    exact stutter_at_most_one hsr rfl
  · -- nativeTokenVault
    obtain rfl : fname = "nativeTokenVault" := by rw [← hname]; rfl
    rw [BridgedTokenSlice.forall₂_nil hargs, tokenCall_nativeTokenVault,
      BridgedTokenSlice.call_nativeTokenVault] at hcall
    cases hcall
    exact stutter_at_most_one hsr rfl
  · -- originToken
    obtain rfl : fname = "originToken" := by rw [← hname]; rfl
    rw [BridgedTokenSlice.forall₂_nil hargs, tokenCall_originToken] at hcall
    cases hcall
    exact stutter_at_most_one hsr rfl
  · -- assetId
    obtain rfl : fname = "assetId" := by rw [← hname]; rfl
    rw [BridgedTokenSlice.forall₂_nil hargs, tokenCall_assetId] at hcall
    cases hcall
    exact stutter_at_most_one hsr rfl

theorem CallMatchesAtMostOneTraceStep : Properties.CallMatchesAtMostOneTraceStep := by
  intro Acct d ch h hag sys sys' L hsr hstep
  cases hstep with
  | bridgeBurn hoc hx =>
    rename_i caller value c l2v a oc data res
    obtain ⟨r, out, -, -, hdc, -, ha, -, -, hp, -, hrel', hret, -⟩ :=
      BridgeBurnSuccessIsPreparation d ch h sys.vault sys.world L.vault caller value c l2v a oc
        data res hag hsr.wf hsr.rel hoc hx
    refine ⟨⟨out.state, L.pending ++ [AssetBridgePreparation.obligation r out.data]⟩,
      Or.inr (.prepare hp), hrel',
      (Contracts.NativeTokenVaultBase.preparation_preserves_ledger hsr.wf hp).1, ?_⟩
    rw [hsr.journal, hret, List.map_append]
    simp only [List.map_cons, List.map_nil, entryOf, AssetBridgePreparation.obligation, hdc, ha]
  | vaultCall hname _ hx =>
    obtain ⟨hst, hw', -⟩ := xcall_view hname hx
    exact ⟨L, Or.inl rfl, by rw [hst, hw']; exact hsr⟩
  | tokenCall hc hv hcall =>
    exact token_step_at_most_one hsr hc hv hcall

/-- The simulation built from `CallMatchesAtMostOneTraceStep`: no step is the empty run, one
step a run of one. -/
def atMostOneTraceStepSim (d : Deployment) (ch : CHooks Acct) (h : Hooks Acct)
    (hag : HooksAgree ch h) :
    LayeredVerification.Simulation (Step d ch) (AssetBridgePreparation.Step h) where
  Rel sys L := SysRel d sys L
  match_step := by
    intro sys sys' L hsr hstep
    obtain ⟨L', hL', hrel⟩ := CallMatchesAtMostOneTraceStep d ch h hag sys sys' L hsr hstep
    refine ⟨L', ?_, hrel⟩
    rcases hL' with rfl | hL'
    · exact Run.refl L'
    · exact Run.tail (Run.refl L) hL'

theorem SimulationAtMostOneTraceStep : Properties.SimulationAtMostOneTraceStep := by
  intro Acct d ch h hag
  exact ⟨atMostOneTraceStepSim d ch h hag, fun _ _ => Iff.rfl,
    fun sys sys' L hsr hstep => CallMatchesAtMostOneTraceStep d ch h hag sys sys' L hsr hstep⟩

/-! ## The witness -/

theorem AtMostOneTraceStepWitness : Properties.AtMostOneTraceStepWitness := by
  obtain ⟨out, res, hp, hx, hret⟩ := r0_call
  refine ⟨deploymentOf s0, liftHooks h0, h0,
    ⟨vaultStorageOf s0, ⟨tokenStorageOf s0.token, s0.accounting⟩, []⟩, _, ⟨s0, []⟩,
    liftHooks_agree h0, ⟨rel_of s0 s0_wellFormed s0_vault, s0_wellFormed, rfl⟩,
    Step.bridgeBurn r0.depositor.isLt hx, ?_⟩
  rintro L' hL' rfl
  have hj := hL'.journal
  simp at hj

end Codegen.VaultPreparationSlice
