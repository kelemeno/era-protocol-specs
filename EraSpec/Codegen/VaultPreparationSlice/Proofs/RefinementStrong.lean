import EraSpec.Codegen.VaultPreparationSlice.Properties.RefinementStrong
import EraSpec.Codegen.VaultPreparationSlice.Proofs.Refinement
import EraSpec.Codegen.VaultPreparationSlice.Proofs.Witnesses

/-!
# Proofs: every successful call is matched by at most one trace step

The case analysis of `Proofs/Refinement.lean`'s `simulationWitness` and `token_step`, with the
matching run kept to a stutter or one step:

* a `bridgeBurn` is matched by the trace's `prepare` of the request it decodes to
  (`BridgeBurnSuccessIsPreparation`);
* any other vault call by the stutter (`xcall_view`);
* a token `transfer` by the trace's `spend` (`BridgedTokenSlice.transfer_refines`);
* a token getter by the stutter;
* a token `bridgeMint` or `bridgeBurn` from anyone but the vault reverts.

`SimulationAtMostOneTraceStep` is witnessed by the existing `simulationWitness`, whose
relation is already `SysRel`.  The witness is the successful call of `Witnesses.lean`'s
request `r0` from the represented state `s0`.
-/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.BridgedStandardERC20 (Address)
open Codegen.BridgedTokenSlice (addrWord addrWord_inj)
open Contracts.NativeTokenVaultBase (State Hooks Request Result prepare WellFormed)

variable {Acct : Type}

/-- `token_step` with the matching run kept to a stutter or one trace step.  A successful call
to the token by anyone but the vault is a trace `spend` (a `transfer`) or changes nothing (a
getter).  `bridgeMint` and `bridgeBurn` revert. -/
theorem token_step_at_most_one_trace {d : Deployment} {h : Hooks Acct} {sys : Sys Acct}
    {L : AssetBridgePreparation.Ledger Acct} {fname : String} {caller : Address}
    {args : List Word} {r : Success}
    (hsr : SysRel d sys L) (hc : caller ≠ d.vault) (hv : TokenAbiValid fname args)
    (hcall : Codegen.call tokenProgram fname (addrWord caller) args sys.world.token =
      some (.ok r)) :
    ∃ L', (L' = L ∨ AssetBridgePreparation.Step h L L') ∧
      SysRel d ⟨sys.vault, { sys.world with token := r.st }, sys.journal⟩ L' := by
  -- a getter: the token's storage is unchanged, so the trace stutters
  have stutter : r.st = sys.world.token → ∃ L', (L' = L ∨ AssetBridgePreparation.Step h L L') ∧
      SysRel d ⟨sys.vault, { sys.world with token := r.st }, sys.journal⟩ L' := by
    intro hst
    rw [hst]
    exact ⟨L, Or.inl rfl, hsr⟩
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
  · -- transfer: exactly the trace's `spend`
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
    exact stutter rfl
  · -- totalSupply
    obtain rfl : fname = "totalSupply" := by rw [← hname]; rfl
    rw [BridgedTokenSlice.forall₂_nil hargs, tokenCall_totalSupply,
      BridgedTokenSlice.call_totalSupply] at hcall
    cases hcall
    exact stutter rfl
  · -- nativeTokenVault
    obtain rfl : fname = "nativeTokenVault" := by rw [← hname]; rfl
    rw [BridgedTokenSlice.forall₂_nil hargs, tokenCall_nativeTokenVault,
      BridgedTokenSlice.call_nativeTokenVault] at hcall
    cases hcall
    exact stutter rfl
  · -- originToken
    obtain rfl : fname = "originToken" := by rw [← hname]; rfl
    rw [BridgedTokenSlice.forall₂_nil hargs, tokenCall_originToken] at hcall
    cases hcall
    exact stutter rfl
  · -- assetId
    obtain rfl : fname = "assetId" := by rw [← hname]; rfl
    rw [BridgedTokenSlice.forall₂_nil hargs, tokenCall_assetId] at hcall
    cases hcall
    exact stutter rfl

/-- `simulationWitness`'s matching, kept to a stutter or one trace step. -/
theorem match_step_at_most_one_trace {d : Deployment} {ch : CHooks Acct} {h : Hooks Acct}
    (hag : HooksAgree ch h) {sys sys' : Sys Acct} {L : AssetBridgePreparation.Ledger Acct}
    (hsr : SysRel d sys L) (hstep : Step d ch sys sys') :
    ∃ L', (L' = L ∨ AssetBridgePreparation.Step h L L') ∧ SysRel d sys' L' := by
  cases hstep with
  | bridgeBurn hoc hx =>
    -- exactly the trace's `prepare` of the request the call decodes to
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
    -- a view: nothing changes, so the trace stutters
    obtain ⟨hst, hw', -⟩ := xcall_view hname hx
    exact ⟨L, Or.inl rfl, by rw [hst, hw']; exact hsr⟩
  | tokenCall hc hv hcall =>
    exact token_step_at_most_one_trace hsr hc hv hcall

/-! ## The witness: `r0`'s successful call from `s0` -/

theorem step_matched_by_at_most_one_trace_step_witness :
    Properties.StepMatchedByAtMostOneTraceStepWitness := by
  obtain ⟨out, res, hp, hx, hret⟩ := r0_call
  have hag := liftHooks_agree h0
  have hsr : SysRel (deploymentOf s0)
      ⟨vaultStorageOf s0, ⟨tokenStorageOf s0.token, s0.accounting⟩, []⟩ ⟨s0, []⟩ :=
    ⟨rel_of s0 s0_wellFormed s0_vault, s0_wellFormed, rfl⟩
  have hstep := Step.bridgeBurn (d := deploymentOf s0) (ch := liftHooks h0)
    (sys := ⟨vaultStorageOf s0, ⟨tokenStorageOf s0.token, s0.accounting⟩, []⟩)
    r0.depositor.isLt hx
  obtain ⟨L', hL', hsr'⟩ := match_step_at_most_one_trace hag hsr hstep
  have hj : ([] : List Entry) ++ [⟨r0.destinationChain, r0.assetId, res.ret⟩] ≠ [] := by simp
  refine ⟨deploymentOf s0, liftHooks h0, h0, _, _, ⟨s0, []⟩, L', hag, hsr, hstep, ?_, hsr', hj⟩
  rcases hL' with rfl | hL'
  · -- a stutter would leave the journal empty
    exfalso
    exact hj hsr'.journal
  · exact hL'

end Codegen.VaultPreparationSlice

/-! ## Certificates -/

namespace Codegen.VaultPreparationSlice

theorem StepMatchedByAtMostOneTraceStep : Properties.StepMatchedByAtMostOneTraceStep := by
  intro Acct d ch h hag sys sys' L hsr hstep
  exact match_step_at_most_one_trace hag hsr hstep

theorem SimulationAtMostOneTraceStep : Properties.SimulationAtMostOneTraceStep := by
  intro Acct d ch h hag
  exact ⟨simulationWitness d ch h hag, fun _ _ => Iff.rfl,
    fun _ _ _ hsr hstep => match_step_at_most_one_trace hag hsr hstep⟩

theorem StepMatchedByAtMostOneTraceStepWitness :
    Properties.StepMatchedByAtMostOneTraceStepWitness :=
  step_matched_by_at_most_one_trace_step_witness

end Codegen.VaultPreparationSlice
