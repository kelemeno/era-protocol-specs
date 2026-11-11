import EraSpec.Codegen.VaultPreparationSlice.Properties.Refinement
import EraSpec.Codegen.VaultPreparationSlice.Proofs.Denotation
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.RepresentationPreparation
import EraSpec.Protocol.AssetBridgePreparation.Proofs.Model

/-!
# Proofs: the vault program refines the preparation model

Two layers.  `Denotation.lean` evaluates the program to `burnDenote`, conditions on its
inputs and on what its calls and hooks return.  Here those conditions are related to
the model's under `Rel`: the success direction (`bridgeBurn_success`) runs the model's
successful `prepare` through `burnDenote`; the converse (`bridgeBurn_ok_prepares`)
reads the model's conditions off a successful run and hands them to the model's
`preparation_enabled`.  The token's burn and transfer are the bridged-token slice's, so
`BridgedTokenSlice.burn_refines` and `transfer_refines` supply them.  The simulation
matches a `bridgeBurn` with the trace's `prepare`, a token `transfer` with its `spend`,
and every getter with no step; `ReachableJournalBacked` is `safety_transfer` of the
trace's `reachable_conservation` through it.
-/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.BridgedStandardERC20 (Address)
open Codegen.BridgedTokenSlice (addrWord addrWord_inj addrWord_zero addrWord_eq_zero)
open Contracts.NativeTokenVaultBase (State Hooks Request Result prepare WellFormed InScope
  EntryAllowed selectedToken mintData)

variable {Acct : Type}

/-! ## The model's preparation, unfolded -/

/-- What a successful `prepare` consists of.  The same statement as the private
`prepare_view` of `Contracts/NativeTokenVaultBase/Proofs/RepresentationPreparation.lean`,
re-proved here so that file is left unchanged. -/
theorem prepare_view {h : Hooks Acct} {s : State Acct} {r : Request} {out : Result Acct}
    (hp : prepare h s r = some out) :
    InScope s r ∧ EntryAllowed s r ∧ r.msgValue = 0 ∧
    ∃ acc burned md,
      h.account s.accounting s.token r.destinationChain r.assetId r.data.amount = some acc ∧
      Contracts.BridgedStandardERC20.burn s.token s.config.vault r.depositor r.data.amount =
        some burned ∧
      burned.config.originToken ≠ 0 ∧ s.config.originChainId ≠ 0 ∧
      h.metadata burned s.config.originChainId = some md ∧
      out = ⟨{ s with token := burned, accounting := acc }, mintData r burned md⟩ := by
  unfold prepare at hp
  split_ifs at hp with hg hv <;>
    rcases ha : h.account s.accounting s.token r.destinationChain r.assetId r.data.amount
      with _ | acc <;> simp only [ha, reduceCtorEq] at hp
  rcases hb : Contracts.BridgedStandardERC20.burn s.token s.config.vault r.depositor
    r.data.amount with _ | burned <;> simp only [hb, reduceCtorEq] at hp
  split_ifs at hp with ho
  rcases hm : h.metadata burned s.config.originChainId with _ | md <;>
    simp only [hm, reduceCtorEq] at hp
  exact ⟨hg.1, hg.2, hv, acc, burned, md, rfl, rfl, ho.1, ho.2, hm, (Option.some.inj hp).symm⟩

/-! ## Facts the representation gives -/

theorem resolve_eq {d : Deployment} {st : Storage} {w : World Acct} {s : State Acct}
    (hrel : Rel d st w s) (r : Request) :
    resolve st r.assetId (addrWord r.data.tokenHint) = addrWord (selectedToken s r) := by
  unfold resolve selectedToken
  by_cases h : r.data.tokenHint = 0 <;> simp [h, addrWord_zero, addrWord_eq_zero, hrel.tokenFor]

theorem toOption_eq_some {ε α : Type} {x : Except ε α} {a : α} (h : x.toOption = some a) :
    x = .ok a := by
  cases x <;> simp_all [Except.toOption]

theorem toOption_ok {ε α : Type} {x : Except ε α} {a : α} (h : x = .ok a) :
    x.toOption = some a :=
  h ▸ rfl

/-- The token's burn writes only the balances and the supply. -/
theorem tokenBurn_frame {st : Storage} {snd acct amt : Word} {r : Success}
    (h : Codegen.call tokenProgram "bridgeBurn" snd [acct, amt] st = some (.ok r)) :
    r.st.scalars "_originToken" = st.scalars "_originToken" ∧
    r.st.scalars "_assetId" = st.scalars "_assetId" ∧ r.ret = none := by
  rw [tokenCall_bridgeBurn, BridgedTokenSlice.call_burn] at h
  split_ifs at h <;> cases h
  simp [upd]

/-- After the token's burn, its storage represents the model's burned token. -/
theorem tokenRel_burn {st : Storage} {t t' : Contracts.BridgedStandardERC20.State}
    {vault acct : Address} {amt : Word} {r : Success}
    (hl : Contracts.BridgedStandardERC20.WellFormed t) (htr : TokenRel st t)
    (hb : Contracts.BridgedStandardERC20.burn t vault acct amt = some t')
    (hc : Codegen.call tokenProgram "bridgeBurn" (addrWord vault) [addrWord acct, amt] st =
      some (.ok r)) :
    TokenRel r.st t' ∧ r.logs = BridgedTokenSlice.burnLogs acct amt ∧ r.ret = none := by
  obtain ⟨r', hr', hrel', hlogs', hret'⟩ :=
    (BridgedTokenSlice.burn_refines hl htr.base vault acct amt).2 t' hb
  rw [tokenCall_bridgeBurn, hr'] at hc
  cases hc
  have hcfg := (Contracts.BridgedStandardERC20.burn_exact hl hb).2.2.2.2.2
  obtain ⟨ho, ha, -⟩ := tokenBurn_frame (by rw [tokenCall_bridgeBurn]; exact hr')
  refine ⟨⟨hrel', ?_, ?_⟩, hlogs', hret'⟩
  · rw [ho, htr.originToken, hcfg]
  · rw [ha, htr.assetId, hcfg]

/-! ## Success -/

theorem bridgeBurn_success {d : Deployment} {ch : CHooks Acct} {h : Hooks Acct} {st : Storage}
    {w : World Acct} {s : State Acct} {r : Request} {out : Result Acct}
    (hag : HooksAgree ch h) (hw : WellFormed s) (hrel : Rel d st w s)
    (hp : prepare h s r = some out) :
    ∃ res, xcall (d.machine ch) vaultProgram "bridgeBurn" (d.env r.caller r.msgValue)
        (requestArgs r) st w = some (.ok res) ∧
      res.st = st ∧ Rel d res.st res.w out.state ∧
      res.ret = some (.bytes (encodeMintData out.data)) ∧ res.logs = prepareLogs d r := by
  obtain ⟨hs, he, hv, acc, burned, md, hacc, hburn, hot, hoc, hmd, rfl⟩ := prepare_view hp
  have hsel : selectedToken s r = s.config.tokenAddress := hs.2.2.2.2
  have hasset : r.assetId = s.config.assetId := by
    have := he.2.2.2.2.1
    rw [hsel, hw.2.2.2.2] at this
    exact this.symm
  have htokW : resolve st r.assetId (addrWord r.data.tokenHint) = addrWord d.token := by
    rw [resolve_eq hrel, hsel, hrel.token]
  have hT0 : addrWord d.token ≠ 0 := by
    rw [← hrel.token]; exact fun h0 => hs.2.1 (addrWord_eq_zero.mp h0)
  -- the accounting hook
  have hacc' : ch.account w.acct w.token r.destinationChain r.assetId r.data.amount = .ok acc := by
    apply toOption_eq_some
    rw [hag.1 w.acct w.token s.token _ _ _ hrel.tokenState, hrel.acct, hacc]
  -- the token's burn
  obtain ⟨r1, hr1, -, -, -⟩ := (BridgedTokenSlice.burn_refines hw.1 hrel.tokenState.base
    s.config.vault r.depositor r.data.amount).2 burned hburn
  have hcall1 : Codegen.call tokenProgram "bridgeBurn" (addrWord d.vault)
      [addrWord r.depositor, r.data.amount] w.token = some (.ok r1) := by
    rw [tokenCall_bridgeBurn, ← hrel.vault]; exact hr1
  obtain ⟨htr1, hlogs1, hret1⟩ := tokenRel_burn hw.1 hrel.tokenState hburn
    (by rw [hrel.vault]; exact hcall1)
  obtain ⟨hfo, -, -⟩ := tokenBurn_frame hcall1
  have hcfg := (Contracts.BridgedStandardERC20.burn_exact hw.1 hburn).2.2.2.2.2
  have hot' : r1.st.scalars "_originToken" = addrWord burned.config.originToken := by
    rw [hfo, hrel.tokenState.originToken, hcfg]
  -- the metadata hook
  have hmd' : ch.metadata r1.st s.config.originChainId = .ok md := by
    apply toOption_eq_some
    rw [hag.2 r1.st burned _ htr1, hmd]
  -- the remaining guards, in the program's terms
  have hA : s.registry.assetForToken d.token = s.config.assetId := by
    rw [← hrel.token]; exact hw.2.2.2.2
  have hOC : ¬ s.config.originChainId = d.chainId := by
    rw [← hrel.chainId]; exact hs.2.2.2.1
  have hB : ¬ s.config.assetId = s.config.baseAssetId := hs.2.2.1
  have hacc'' : ch.account w.acct w.token r.destinationChain s.config.assetId r.data.amount =
      .ok acc := hasset ▸ hacc'
  have hot'' : ¬ r1.st.scalars "_originToken" = 0 := by
    rw [hot']; exact fun h0 => hot (addrWord_eq_zero.mp h0)
  have htokW' : resolve st s.config.assetId (addrWord r.data.tokenHint) = addrWord d.token :=
    hasset ▸ htokW
  have hm1 := machine_hook_account_of (T := addrWord d.token) hacc''
  have hm2 := machine_call_token_ok (T := addrWord d.token) (ch := ch)
    (w := ⟨w.token, acc⟩) hcall1
  have hm3 := machine_call_token_ok (T := addrWord d.token) (ch := ch)
    (w := ⟨r1.st, acc⟩) (tokenCall_originToken r1.st (addrWord d.vault))
  have hm4 := machine_hook_metadata_of (T := addrWord d.token) (w := ⟨r1.st, acc⟩) hmd'
  have hx : xcall (d.machine ch) vaultProgram "bridgeBurn" (d.env r.caller r.msgValue)
      (requestArgs r) st w =
      some (.ok ⟨st, ⟨r1.st, acc⟩,
        r1.logs.map (XLog.mk (addrWord d.token)) ++ [] ++
          [⟨addrWord d.vault, ⟨"BridgeBurn", [r.destinationChain, s.config.assetId,
            addrWord r.depositor, addrWord r.data.receiver, r.data.amount]⟩⟩],
        some (.bytes (abiEncode [.word (addrWord r.depositor), .word (addrWord r.data.receiver),
          .word (r1.st.scalars "_originToken"), .word r.data.amount, .bytes md]))⟩) := by
    rw [requestArgs, xcall_bridgeBurn]
    simp [burnDenote, burnTail, Deployment.env, length_encodeBurnData,
      bAmount_encodeBurnData, bReceiver_encodeBurnData, bHint_encodeBurnData, natCast_addr,
      htokW', he.2.2.1, hrel.router, he.1, hrel.paused, he.2.1, hasset, hrel.assetFor, hA,
      hrel.origin, hT0, he.2.2.2.2.2, hOC, hB, hrel.baseAsset, hv, hot'', hoc, retOf,
      hm1, hm2, hm3, hm4, -Nat.reducePow]
  refine ⟨_, hx, rfl, ?_, ?_, ?_⟩
  · exact ⟨hrel.vault, hrel.token, hrel.chainId, hrel.router, hrel.paused, hrel.baseAsset,
      hrel.tokenFor, hrel.assetFor, hrel.origin, htr1, rfl⟩
  · simp only [hot', encodeMintData, mintData]
  · simp only [prepareLogs, hlogs1, hasset, List.append_nil]

/-! ## A successful run is an accepted request -/

/-- The request a call stands for: its sender, value and words, and its burn data
decoded. -/
def callRequest (caller : Address) (value c l2v a oc : Word) (hoc : oc.val < 2 ^ 160)
    (data : Bytes) (hr : bReceiver data < 2 ^ 160) (hh : bHint data < 2 ^ 160) : Request :=
  ⟨caller, c, a, ⟨oc.val, hoc⟩, l2v, value, ⟨bAmount data, ⟨bReceiver data, hr⟩, ⟨bHint data, hh⟩⟩⟩

theorem bridgeBurn_ok_prepares {d : Deployment} {ch : CHooks Acct} {h : Hooks Acct}
    {st : Storage} {w : World Acct} {s : State Acct} {caller : Address} {value c l2v a oc : Word}
    {data : Bytes} {res : XSuccess (World Acct)}
    (hag : HooksAgree ch h) (hw : WellFormed s) (hrel : Rel d st w s) (hoc : oc.val < 2 ^ 160)
    (hx : xcall (d.machine ch) vaultProgram "bridgeBurn" (d.env caller value)
      [.word c, .word l2v, .word a, .word oc, .bytes data] st w = some (.ok res)) :
    ∃ (hr : bReceiver data < 2 ^ 160) (hh : bHint data < 2 ^ 160),
      data.length = 96 ∧
      ∃ out, prepare h s (callRequest caller value c l2v a oc hoc data hr hh) = some out := by
  rw [xcall_bridgeBurn, Option.some.injEq] at hx
  unfold burnDenote at hx
  split_ifs at hx with h1 h2 h3 h4 h5
  obtain ⟨hr, hh⟩ := h5
  refine ⟨hr, hh, not_not.mp h4, ?_⟩
  set r := callRequest caller value c l2v a oc hoc data hr hh with hrdef
  have hres : resolve st a ↑(bHint data) = addrWord (selectedToken s r) := by
    have := resolve_eq hrel r
    rwa [show addrWord r.data.tokenHint = ↑(bHint data) from (natCast_addr _).symm] at this
  rw [hres] at hx
  unfold burnTail at hx
  by_cases h6 : addrWord (selectedToken s r) = 0
  · rw [ite_eq_left h6] at hx; cases hx
  rw [ite_eq_right h6] at hx
  by_cases h7 : a ≠ st.maps "_assetIdOf" (addrWord (selectedToken s r))
  · rw [ite_eq_left h7] at hx; cases hx
  rw [ite_eq_right h7] at hx
  by_cases h8 : bAmount data = 0
  · rw [ite_eq_left h8] at hx; cases hx
  rw [ite_eq_right h8] at hx
  by_cases h9 : st.maps "_originChainId" a = (d.env caller value).chainId
  · rw [ite_eq_left h9] at hx; cases hx
  rw [ite_eq_right h9] at hx
  by_cases h10 : a = st.scalars "_baseTokenAssetId"
  · rw [ite_eq_left h10] at hx; cases hx
  rw [ite_eq_right h10] at hx
  split at hx
  · cases hx
  rename_i w1 r1 hk
  by_cases h11 : (d.env caller value).value ≠ 0
  · rw [ite_eq_left h11] at hx; cases hx
  rw [ite_eq_right h11] at hx
  split at hx
  · cases hx
  rename_i w2 r2 logs1 hc1
  split at hx
  · cases hx
  rotate_left
  · cases hx
  · cases hx
  rename_i w3 ot logs2 hc2
  by_cases h12 : ot = 0
  · rw [ite_eq_left h12] at hx; cases hx
  rw [ite_eq_right h12] at hx
  by_cases h13 : st.maps "_originChainId" a = 0
  · rw [ite_eq_left h13] at hx; cases hx
  rw [ite_eq_right h13] at hx
  split at hx
  · cases hx
  rotate_left
  · cases hx
  · cases hx
  rename_i w4 md hk2
  -- what the machine did
  obtain ⟨acc, hacc, rfl⟩ := machine_hook_account_ok hk
  obtain ⟨hT, rb, hrb, rfl, -, -⟩ := machine_call_ok hc1
  obtain ⟨-, ro, hro, rfl, hret2, -⟩ := machine_call_ok hc2
  rw [tokenCall_originToken] at hro
  cases hro
  obtain ⟨-, b, hb, rfl, -⟩ := machine_hook_metadata_ok hk2
  have hot : ot = rb.st.scalars "_originToken" := by simpa [retOf] using hret2
  -- the request's fields
  have hdep : addrWord r.depositor = oc := Fin.ext rfl
  have hself : (d.env caller value).self = addrWord s.config.vault := by
    rw [hrel.vault]; rfl
  have hsel : selectedToken s r = s.config.tokenAddress := by
    rw [hrel.token]; exact addrWord_inj.mp hT
  have hassetFor : s.registry.assetForToken (selectedToken s r) = a := by
    rw [← hrel.assetFor]; exact (not_not.mp h7).symm
  have hasset : a = s.config.assetId := by
    rw [← hassetFor, hsel, hw.2.2.2.2]
  -- the token's burn is the model's
  have hrb' : Codegen.call tokenProgram "bridgeBurn" (addrWord s.config.vault)
      [addrWord r.depositor, r.data.amount] w.token = some (.ok rb) := by
    rw [hdep, ← hself]; exact hrb
  obtain ⟨burned, hburned⟩ : ∃ burned, Contracts.BridgedStandardERC20.burn s.token
      s.config.vault r.depositor r.data.amount = some burned := by
    rcases hb0 : Contracts.BridgedStandardERC20.burn s.token s.config.vault r.depositor
        r.data.amount with _ | burned
    · obtain ⟨e, he⟩ := (BridgedTokenSlice.burn_refines hw.1 hrel.tokenState.base
        s.config.vault r.depositor r.data.amount).1 hb0
      rw [← tokenCall_bridgeBurn, hrb'] at he
      cases he
    · exact ⟨burned, rfl⟩
  have hBA : Contracts.BridgedStandardERC20.BurnAllowed s.token s.config.vault r.depositor
      r.data.amount := by
    by_contra hna
    simp [Contracts.BridgedStandardERC20.burn, hna] at hburned
  have hbe : burned = Contracts.BridgedStandardERC20.burnEffect s.token r.depositor
      r.data.amount := by
    simp only [Contracts.BridgedStandardERC20.burn, hBA, ite_true, Option.some.injEq] at hburned
    exact hburned.symm
  obtain ⟨htr, -, -⟩ := tokenRel_burn hw.1 hrel.tokenState hburned hrb'
  obtain ⟨hfo, -, -⟩ := tokenBurn_frame hrb'
  -- the model's conditions
  have hT0 : s.config.tokenAddress ≠ 0 := fun h0 => h6 (by rw [hsel, h0, addrWord_zero])
  have hs : InScope s r := by
    refine ⟨?_, hT0, ?_, ?_, hsel⟩
    · rw [← hw.2.1]; exact hrel.tokenState.base.vault_ne
    · intro heq
      apply h10
      rw [hrel.baseAsset, hasset, heq]
    · intro heq
      apply h9
      show st.maps "_originChainId" a = d.chainId
      rw [hasset, hrel.origin, heq, hrel.chainId]
  have he : EntryAllowed s r := by
    refine ⟨?_, ?_, not_not.mp h1, by rw [hsel]; exact hT0, hassetFor, h8⟩
    · apply addrWord_inj.mp
      rw [← hrel.router]
      exact not_not.mp h2
    · cases hp : s.paused
      · rfl
      · simp [hrel.paused, hp] at h3
  have hv : r.msgValue = 0 := not_not.mp h11
  have ho : s.token.config.originToken ≠ 0 := by
    intro h0
    apply h12
    rw [hot, hfo, hrel.tokenState.originToken, h0, addrWord_zero]
  have hc : s.config.originChainId ≠ 0 := by
    rw [hasset, hrel.origin] at h13; exact h13
  have ha : h.account s.accounting s.token r.destinationChain r.assetId r.data.amount =
      some acc := by
    rw [← hrel.acct, ← hag.1 w.acct w.token s.token _ _ _ hrel.tokenState]
    exact toOption_ok hacc
  have hm : h.metadata (Contracts.BridgedStandardERC20.burnEffect s.token r.depositor
      r.data.amount) s.config.originChainId = some b := by
    rw [← hbe, ← hag.2 rb.st burned _ htr, ← hrel.origin, ← hasset]
    exact toOption_ok hb
  exact Contracts.NativeTokenVaultBase.preparation_enabled hw hs he hv hBA.2.2.1 hBA.2.2.2 ho hc
    ha hm

/-- The call a request stands for decodes back to that request. -/
theorem callRequest_requestArgs (r : Request) (hoc : (addrWord r.depositor).val < 2 ^ 160)
    (hr : bReceiver (encodeBurnData r.data) < 2 ^ 160)
    (hh : bHint (encodeBurnData r.data) < 2 ^ 160) :
    callRequest r.caller r.msgValue r.destinationChain r.l2MsgValue r.assetId
      (addrWord r.depositor) hoc (encodeBurnData r.data) hr hh = r := by
  have h1 : (⟨(addrWord r.depositor).val, hoc⟩ : Address) = r.depositor := Fin.ext rfl
  have h2 : (⟨bReceiver (encodeBurnData r.data), hr⟩ : Address) = r.data.receiver := by
    apply Fin.ext
    rw [Fin.val_mk]
    exact bReceiver_encodeBurnData r.data
  have h3 : (⟨bHint (encodeBurnData r.data), hh⟩ : Address) = r.data.tokenHint := by
    apply Fin.ext
    rw [Fin.val_mk]
    exact bHint_encodeBurnData r.data
  have h4 : bAmount (encodeBurnData r.data) = r.data.amount := bAmount_encodeBurnData r.data
  unfold callRequest
  rw [h1, h2, h3, h4]

/-- The request decoded from a call stands for that call. -/
theorem requestArgs_callRequest {caller : Address} {value c l2v a oc : Word}
    {hoc : oc.val < 2 ^ 160} {data : Bytes} {hr : bReceiver data < 2 ^ 160}
    {hh : bHint data < 2 ^ 160} (hl : data.length = 96) :
    requestArgs (callRequest caller value c l2v a oc hoc data hr hh) =
      [.word c, .word l2v, .word a, .word oc, .bytes data] := by
  simp only [requestArgs, callRequest]
  rw [encodeBurnData_decoded hl hr hh]
  rfl

/-! ## The statements -/

theorem BridgeBurnRefines : Properties.BridgeBurnRefines := by
  intro Acct d ch h st w s r hag hw hrel
  refine ⟨fun hnone => ?_, fun out hp => bridgeBurn_success hag hw hrel hp⟩
  rw [requestArgs, xcall_bridgeBurn]
  rcases hden : burnDenote (d.machine ch) (d.env r.caller r.msgValue) r.destinationChain
      r.l2MsgValue r.assetId (addrWord r.depositor) (encodeBurnData r.data) st w with e | res
  · exact ⟨e, rfl⟩
  · exfalso
    have hoc : (addrWord r.depositor).val < 2 ^ 160 := r.depositor.isLt
    obtain ⟨hr, hh, -, out, hp⟩ := bridgeBurn_ok_prepares hag hw hrel hoc
      (by rw [xcall_bridgeBurn, hden])
    rw [callRequest_requestArgs r hoc hr hh, hnone] at hp
    cases hp

theorem BridgeBurnSuccessIsPreparation : Properties.BridgeBurnSuccessIsPreparation := by
  intro Acct d ch h st w s caller value c l2v a oc data res hag hw hrel hoc hx
  obtain ⟨hr, hh, hl, out, hp⟩ := bridgeBurn_ok_prepares hag hw hrel hoc hx
  obtain ⟨res', hx', hst, hrel', hret, hlogs⟩ := bridgeBurn_success hag hw hrel hp
  rw [requestArgs_callRequest hl] at hx'
  have henv : d.env (callRequest caller value c l2v a oc hoc data hr hh).caller
      (callRequest caller value c l2v a oc hoc data hr hh).msgValue = d.env caller value := rfl
  rw [henv, hx, Option.some.injEq, Except.ok.injEq] at hx'
  subst hx'
  exact ⟨callRequest caller value c l2v a oc hoc data hr hh, out, rfl, rfl, rfl, rfl, rfl,
    Fin.ext rfl, encodeBurnData_decoded hl hr hh, hp, hst, hrel', hret, hlogs⟩

theorem BridgeBurnBacked : Properties.BridgeBurnBacked := by
  intro Acct d ch h st w s caller value c l2v a oc data res hag hw hrel hoc hx
  obtain ⟨r, out, -, -, -, -, -, hdep, -, hp, -, hrel', hret, -⟩ :=
    BridgeBurnSuccessIsPreparation d ch h st w s caller value c l2v a oc data res hag hw hrel hoc hx
  obtain ⟨-, hbal, hsup, hne⟩ := Contracts.NativeTokenVaultBase.preparation_backed hw hp
  obtain ⟨-, -, -, -, hframe⟩ := Contracts.NativeTokenVaultBase.preparation_preserves_ledger hw hp
  refine ⟨out.data.amount, hne, ?_, ?_, ?_, ?_⟩
  · rw [hret, mintAmount_encodeMintData]
  · rw [← hdep, hrel'.tokenState.base.balances, hrel.tokenState.base.balances]
    exact hbal
  · rw [hrel'.tokenState.base.supply, hrel.tokenState.base.supply]
    exact hsup
  · intro k hk
    apply Fin.ext
    rw [hrel'.tokenState.base.balances, hrel.tokenState.base.balances]
    exact hframe k (fun hkd => hk (by rw [hkd, hdep]))

theorem VaultViewsChangeNothing : Properties.VaultViewsChangeNothing := by
  intro Acct d ch fname caller value args st w res hname hx
  exact xcall_view hname hx

/-! ## Every call is matched by the preparation trace -/

open LayeredVerification (Run)

/-- The token's `transfer` writes only the balances. -/
theorem tokenTransfer_scalars {st : Storage} {snd x y : Word} {r : Success}
    (h : Codegen.call tokenProgram "transfer" snd [x, y] st = some (.ok r)) :
    r.st.scalars = st.scalars := by
  rw [tokenCall_transfer, BridgedTokenSlice.call_transfer] at h
  split_ifs at h <;> cases h
  rfl

/-- A token getter changes nothing. -/
theorem stutter {d : Deployment} {h : Hooks Acct} {sys : Sys Acct}
    {L : AssetBridgePreparation.Ledger Acct} {st : Storage} (hsr : SysRel d sys L)
    (hst : st = sys.world.token) :
    ∃ L', Run (AssetBridgePreparation.Step h) L L' ∧
      SysRel d ⟨sys.vault, { sys.world with token := st }, sys.journal⟩ L' := by
  subst hst
  exact ⟨L, Run.refl L, hsr⟩

/-- A successful call to the token by anyone but the vault is a trace `spend` (a
`transfer`) or changes nothing (a getter); `bridgeMint` and `bridgeBurn` revert. -/
theorem token_step {d : Deployment} {h : Hooks Acct} {sys : Sys Acct}
    {L : AssetBridgePreparation.Ledger Acct} {fname : String} {caller : Address}
    {args : List Word} {r : Success}
    (hsr : SysRel d sys L) (hc : caller ≠ d.vault) (hv : TokenAbiValid fname args)
    (hcall : Codegen.call tokenProgram fname (addrWord caller) args sys.world.token =
      some (.ok r)) :
    ∃ L', Run (AssetBridgePreparation.Step h) L L' ∧
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
  · -- transfer: the trace's `spend`
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
      refine ⟨⟨{ L.vault with token := t }, L.pending⟩, Run.tail (Run.refl _) (.spend hm), ?_⟩
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
    exact stutter hsr rfl
  · -- totalSupply
    obtain rfl : fname = "totalSupply" := by rw [← hname]; rfl
    rw [BridgedTokenSlice.forall₂_nil hargs, tokenCall_totalSupply,
      BridgedTokenSlice.call_totalSupply] at hcall
    cases hcall
    exact stutter hsr rfl
  · -- nativeTokenVault
    obtain rfl : fname = "nativeTokenVault" := by rw [← hname]; rfl
    rw [BridgedTokenSlice.forall₂_nil hargs, tokenCall_nativeTokenVault,
      BridgedTokenSlice.call_nativeTokenVault] at hcall
    cases hcall
    exact stutter hsr rfl
  · -- originToken
    obtain rfl : fname = "originToken" := by rw [← hname]; rfl
    rw [BridgedTokenSlice.forall₂_nil hargs, tokenCall_originToken] at hcall
    cases hcall
    exact stutter hsr rfl
  · -- assetId
    obtain rfl : fname = "assetId" := by rw [← hname]; rfl
    rw [BridgedTokenSlice.forall₂_nil hargs, tokenCall_assetId] at hcall
    cases hcall
    exact stutter hsr rfl

/-- The simulation, for agreeing hooks. -/
def simulationWitness (d : Deployment) (ch : CHooks Acct) (h : Hooks Acct)
    (hag : HooksAgree ch h) :
    LayeredVerification.Simulation (Step d ch) (AssetBridgePreparation.Step h) where
  Rel sys L := SysRel d sys L
  match_step := by
    intro sys sys' L hsr hstep
    cases hstep with
    | bridgeBurn hoc hx =>
      rename_i caller value c l2v a oc data res
      obtain ⟨r, out, -, -, hdc, -, ha, -, -, hp, hst, hrel', hret, -⟩ :=
        BridgeBurnSuccessIsPreparation d ch h sys.vault sys.world L.vault caller value c l2v a oc
          data res hag hsr.wf hsr.rel hoc hx
      refine ⟨⟨out.state, L.pending ++ [AssetBridgePreparation.obligation r out.data]⟩,
        Run.tail (Run.refl _) (.prepare hp), hrel',
        (Contracts.NativeTokenVaultBase.preparation_preserves_ledger hsr.wf hp).1, ?_⟩
      rw [hsr.journal, hret, List.map_append]
      simp only [List.map_cons, List.map_nil, entryOf, AssetBridgePreparation.obligation, hdc, ha]
    | vaultCall hname _ hx =>
      obtain ⟨hst, hw', -⟩ := xcall_view hname hx
      exact ⟨L, Run.refl L, by rw [hst, hw']; exact hsr⟩
    | tokenCall hc hv hcall =>
      exact token_step hsr hc hv hcall

theorem Simulation : Properties.Simulation := by
  intro Acct d ch h hag
  exact ⟨simulationWitness d ch h hag, fun _ _ => Iff.rfl⟩

/-! ## What the trace's conservation says about the concrete system -/

theorem run_reach {h : Hooks Acct} {L L' : AssetBridgePreparation.Ledger Acct}
    (hr : Run (AssetBridgePreparation.Step h) L L') : AssetBridgePreparation.Reach h L L' := by
  induction hr with
  | refl => exact .refl
  | tail _ hstep ih => exact .tail ih hstep

theorem journalTotal_map (pending : List AssetBridgePreparation.Obligation) :
    journalTotal (pending.map entryOf) = AssetBridgePreparation.pendingAmount pending := by
  induction pending with
  | nil => rfl
  | cons o rest ih =>
    simp only [journalTotal, AssetBridgePreparation.pendingAmount, List.map_cons, List.sum_cons]
    simp only [journalTotal, AssetBridgePreparation.pendingAmount] at ih
    rw [List.map_map] at ih
    rw [List.map_map, ih, entryOf, mintAmount_encodeMintData]

theorem ReachableJournalBacked : Properties.ReachableJournalBacked := by
  intro Acct d ch h s₀ sys₀ hag hw hrel hj sys hrun
  have hinit : (simulationWitness d ch h hag).Rel sys₀ ⟨s₀, []⟩ :=
    ⟨hrel, hw, by rw [hj]; rfl⟩
  refine LayeredVerification.safety_transfer (sim := simulationWitness d ch h hag)
    (SafeA := fun sys : Sys Acct =>
      (sys.world.token.scalars "_totalSupply").val + journalTotal sys.journal =
        (sys₀.world.token.scalars "_totalSupply").val ∧
      (∑ a : Address, (sys.world.token.maps "_balances" (addrWord a)).val) =
        (sys.world.token.scalars "_totalSupply").val ∧
      sys.world.token.scalars "_nativeTokenVault" = addrWord d.vault ∧
      sys.vault.maps "_assetIdOf" (addrWord d.token) = sys.world.token.scalars "_assetId")
    (SafeB := fun L => WellFormed L.vault ∧
      L.vault.token.totalSupply + AssetBridgePreparation.pendingAmount L.pending =
        s₀.token.totalSupply)
    hinit ?_ ?_ sys hrun
  · intro L hL
    obtain ⟨hwf, hsum, -⟩ := AssetBridgePreparation.reachable_conservation
      (s := ⟨s₀, []⟩) (t := L) hw (run_reach hL)
    exact ⟨hwf, by simpa [AssetBridgePreparation.pendingAmount] using hsum⟩
  · rintro sys' L ⟨hrel', -, hj'⟩ ⟨hwf, hsum⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hj', journalTotal_map, hrel'.tokenState.base.supply, hrel.tokenState.base.supply]
      exact hsum
    · simp only [hrel'.tokenState.base.balances, hrel'.tokenState.base.supply]
      exact hwf.1.1
    · rw [hrel'.tokenState.base.vault, hwf.2.1, hrel'.vault]
    · rw [hrel'.assetFor, ← hrel'.token, hwf.2.2.2.2, hrel'.tokenState.assetId, hwf.2.2.1]

end Codegen.VaultPreparationSlice
