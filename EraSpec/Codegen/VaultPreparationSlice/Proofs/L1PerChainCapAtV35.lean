import EraSpec.Codegen.VaultPreparationSlice.Properties.L1PerChainCapAtV35
import EraSpec.Codegen.VaultPreparationSlice.Proofs.Refinement
import EraSpec.Codegen.VaultPreparationSlice.Proofs.Witnesses

/-!
# Proofs: the vault slice on L1 at draft/v0.35.0, and the per-chain balance cap

Three layers.

* The slice. `L1BridgeBurnRefinesAtV35` is `BridgeBurnRefines` at the v35 hooks.
  `burnDenote_ok_factsV35` reads off any successful `bridgeBurn` (for any hooks) that the vault
  storage is unchanged, the asset is not native, and the accounting hook ran on the call's
  destination, asset and amount, with that amount as the returned amount word;
  `burnDenote_other_accountV35` re-runs a successful call under hooks that differ only in the
  accounting hook, which gives the comparison with the pin's hook;
  `handleBridgeToChainV35_bridged` says exactly what the v35 hook does on such an asset. The run
  statements are inductions over the slice's `Step`, and `L1SliceDepositsBackedByBurnsAtV35`
  adds `ReachableJournalBacked` and the fact that a journal entry credits at most one key.
* The cap's functions: one lemma per function, each stating what it writes.
* The cap's runs: `poolInvV35_step` and `capInvV35_step` are the one-step preservation
  lemmas; the countermodel and the witnesses are concrete runs checked by `rfl` and `decide`.
-/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.BridgedStandardERC20 (Address)
open Codegen.BridgedTokenSlice (addrWord)
open Contracts.NativeTokenVaultBase (State Request prepare WellFormed)

theorem InteropPoolKeyOutsideChainIdsV35 : Properties.InteropPoolKeyOutsideChainIdsV35 := by
  unfold Properties.InteropPoolKeyOutsideChainIdsV35 PoolKeyOutsideChainIdsV35 chainIdBoundV35
    interopPoolChainIdV35
  decide

theorem L1HooksAgreeAtV35 : Properties.L1HooksAgreeAtV35 :=
  fun _ _ _ hmd => ⟨fun _ _ _ _ _ _ _ => rfl, hmd⟩

theorem L1BridgeBurnRefinesAtV35 : Properties.L1BridgeBurnRefinesAtV35 :=
  fun d env md mdm st w s r hmd hw hrel =>
    BridgeBurnRefines d (l1HooksV35 env md) (l1ModelHooksV35 env mdm) st w s r
      (L1HooksAgreeAtV35 env md mdm hmd) hw hrel

theorem L1PrepareAtV35IsPinPlusCredit : Properties.L1PrepareAtV35IsPinPlusCredit := by
  intro env mdm s r hb
  have hpin : (l1ModelHooksPin env mdm).account s.accounting s.token r.destinationChain
      r.assetId r.data.amount = some s.accounting := by
    simp [l1ModelHooksPin, handleBridgeToChainPin, hb, Except.toOption]
  unfold prepare
  rw [hpin]
  split_ifs with hg hv
  · simp only [l1ModelHooksV35]
    rcases hacc : handleBridgeToChainV35 env s.accounting r.destinationChain r.assetId
      r.data.amount with e | acc
    · simp [Except.toOption]
    · simp only [Except.toOption]
      rcases Contracts.BridgedStandardERC20.burn s.token s.config.vault r.depositor
        r.data.amount with _ | burned
      · rfl
      · simp only
        split_ifs
        · simp only [l1ModelHooksPin]
          rcases mdm burned s.config.originChainId with _ | md <;> simp
        · rfl
  · cases (l1ModelHooksV35 env mdm).account s.accounting s.token r.destinationChain r.assetId
      r.data.amount <;> rfl
  · rfl

variable {Acct : Type}

/-- The amount word of `abi.encode(oc, rcv, ot, amt, md)`: its fourth head. -/
theorem mintAmount_abiEncode_fiveV35 (oc rcv ot amt : Word) (md : Bytes) :
    mintAmount (some (.bytes (abiEncode [.word oc, .word rcv, .word ot, .word amt, .bytes md]))) =
      amt.val := by
  have h96 : (96 : ℕ) = 32 + 32 + 32 := rfl
  have heq : abiEncode [.word oc, .word rcv, .word ot, .word amt, .bytes md] =
      word32 oc.val ++ word32 rcv.val ++ word32 ot.val ++ word32 amt.val ++ word32 160 ++
        word32 md.length ++ pad32 md := by
    simp [abiEncode, heads, AbiVal.tail]
  simp only [mintAmount, heq, List.append_assoc]
  rw [h96, ← List.drop_drop, ← List.drop_drop, drop_word32, drop_word32, drop_word32,
    take_word32, fromBytes_word32_val]

/-- **WHAT A SUCCESSFUL `bridgeBurn` DID**, for any hooks: the vault's storage is unchanged, the
asset is not native to the call's chain, the amount is nonzero, the accounting hook ran on the
call's destination, asset and amount and its result is the final accounting state, and the
returned amount word is that amount. -/
theorem burnDenote_ok_factsV35 {T : Word} {ch : CHooks Acct} {e : Env} {c l2v a oc : Word}
    {data : Bytes} {st : Storage} {w : World Acct} {res : XSuccess (World Acct)}
    (h : burnDenote (machine T ch) e c l2v a oc data st w = .ok res) :
    res.st = st ∧ st.maps "_originChainId" a ≠ e.chainId ∧ bAmount data ≠ 0 ∧
    ∃ acc, ch.account w.acct w.token c a (bAmount data) = .ok acc ∧ res.w.acct = acc ∧
      mintAmount res.ret = (bAmount data).val := by
  unfold burnDenote at h
  by_cases h1 : l2v ≠ 0
  · rw [ite_eq_left h1] at h; cases h
  rw [ite_eq_right h1] at h
  by_cases h2 : e.sender ≠ st.scalars "_assetRouter"
  · rw [ite_eq_left h2] at h; cases h
  rw [ite_eq_right h2] at h
  by_cases h3 : st.scalars "_paused" ≠ 0
  · rw [ite_eq_left h3] at h; cases h
  rw [ite_eq_right h3] at h
  by_cases h4 : data.length ≠ 96
  · rw [ite_eq_left h4] at h; cases h
  rw [ite_eq_right h4] at h
  by_cases h5 : ¬ (bReceiver data < 2 ^ 160 ∧ bHint data < 2 ^ 160)
  · rw [ite_eq_left h5] at h; cases h
  rw [ite_eq_right h5] at h
  unfold burnTail at h
  by_cases h6 : resolve st a (bHint data : Word) = 0
  · rw [ite_eq_left h6] at h; cases h
  rw [ite_eq_right h6] at h
  by_cases h7 : a ≠ st.maps "_assetIdOf" (resolve st a (bHint data : Word))
  · rw [ite_eq_left h7] at h; cases h
  rw [ite_eq_right h7] at h
  by_cases h8 : bAmount data = 0
  · rw [ite_eq_left h8] at h; cases h
  rw [ite_eq_right h8] at h
  by_cases h9 : st.maps "_originChainId" a = e.chainId
  · rw [ite_eq_left h9] at h; cases h
  rw [ite_eq_right h9] at h
  by_cases h10 : a = st.scalars "_baseTokenAssetId"
  · rw [ite_eq_left h10] at h; cases h
  rw [ite_eq_right h10] at h
  split at h
  · cases h
  rename_i w1 r1 hk
  by_cases h11 : e.value ≠ 0
  · rw [ite_eq_left h11] at h; cases h
  rw [ite_eq_right h11] at h
  split at h
  · cases h
  rename_i w2 r2 logs1 hc1
  split at h
  · cases h
  rotate_left
  · cases h
  · cases h
  rename_i w3 ot logs2 hc2
  by_cases h12 : ot = 0
  · rw [ite_eq_left h12] at h; cases h
  rw [ite_eq_right h12] at h
  by_cases h13 : st.maps "_originChainId" a = 0
  · rw [ite_eq_left h13] at h; cases h
  rw [ite_eq_right h13] at h
  split at h
  · cases h
  rotate_left
  · cases h
  · cases h
  rename_i w4 md hk2
  obtain ⟨acc, hacc, rfl⟩ := machine_hook_account_ok hk
  obtain ⟨-, rb, -, rfl, -, -⟩ := machine_call_ok hc1
  obtain ⟨-, ro, -, rfl, -, -⟩ := machine_call_ok hc2
  obtain ⟨-, b, -, rfl, -⟩ := machine_hook_metadata_ok hk2
  cases h
  exact ⟨rfl, h9, h8, acc, hacc, rfl, mintAmount_abiEncode_fiveV35 _ _ _ _ _⟩

theorem machine_hook_account_errV35 {T : Word} {ch : CHooks Acct} {w : World Acct} {c a m : Word}
    {err : XFailure} (h : ch.account w.acct w.token c a m = .error err) :
    (machine T ch).hook w "_handleBridgeToChain" [c, a, m] = .error err := by
  simp [machine, h]

/-- **ONLY THE ACCOUNTING HOOK'S RESULT DIFFERS.** If `bridgeBurn` succeeds under hooks `ch`, then
under hooks `ch'` with the same metadata hook, on the same inputs: if `ch'`'s accounting hook
fails on the call's destination, asset and amount, the call reverts with exactly that failure;
if it succeeds, the call succeeds with the same result except the accounting state, which is
`ch'`'s. -/
theorem burnDenote_other_accountV35 {T : Word} {ch ch' : CHooks Acct}
    (hmd : ch'.metadata = ch.metadata) {e : Env} {c l2v a oc : Word} {data : Bytes}
    {st : Storage} {w : World Acct} {res : XSuccess (World Acct)}
    (h : burnDenote (machine T ch) e c l2v a oc data st w = .ok res) :
    (∀ err, ch'.account w.acct w.token c a (bAmount data) = .error err →
      burnDenote (machine T ch') e c l2v a oc data st w = .error err) ∧
    (∀ acc', ch'.account w.acct w.token c a (bAmount data) = .ok acc' →
      burnDenote (machine T ch') e c l2v a oc data st w =
        .ok { res with w := { res.w with acct := acc' } }) := by
  unfold burnDenote at h ⊢
  by_cases h1 : l2v ≠ 0
  · rw [ite_eq_left h1] at h; cases h
  rw [ite_eq_right h1] at h ⊢
  by_cases h2 : e.sender ≠ st.scalars "_assetRouter"
  · rw [ite_eq_left h2] at h; cases h
  rw [ite_eq_right h2] at h ⊢
  by_cases h3 : st.scalars "_paused" ≠ 0
  · rw [ite_eq_left h3] at h; cases h
  rw [ite_eq_right h3] at h ⊢
  by_cases h4 : data.length ≠ 96
  · rw [ite_eq_left h4] at h; cases h
  rw [ite_eq_right h4] at h ⊢
  by_cases h5 : ¬ (bReceiver data < 2 ^ 160 ∧ bHint data < 2 ^ 160)
  · rw [ite_eq_left h5] at h; cases h
  rw [ite_eq_right h5] at h ⊢
  unfold burnTail at h ⊢
  by_cases h6 : resolve st a (bHint data : Word) = 0
  · rw [ite_eq_left h6] at h; cases h
  rw [ite_eq_right h6] at h ⊢
  by_cases h7 : a ≠ st.maps "_assetIdOf" (resolve st a (bHint data : Word))
  · rw [ite_eq_left h7] at h; cases h
  rw [ite_eq_right h7] at h ⊢
  by_cases h8 : bAmount data = 0
  · rw [ite_eq_left h8] at h; cases h
  rw [ite_eq_right h8] at h ⊢
  by_cases h9 : st.maps "_originChainId" a = e.chainId
  · rw [ite_eq_left h9] at h; cases h
  rw [ite_eq_right h9] at h ⊢
  by_cases h10 : a = st.scalars "_baseTokenAssetId"
  · rw [ite_eq_left h10] at h; cases h
  rw [ite_eq_right h10] at h ⊢
  split at h
  · cases h
  rename_i w1 r1 hk
  obtain ⟨acc, -, rfl⟩ := machine_hook_account_ok hk
  by_cases h11 : e.value ≠ 0
  · rw [ite_eq_left h11] at h; cases h
  rw [ite_eq_right h11] at h
  split at h
  · cases h
  rename_i w2 r2 logs1 hc1
  obtain ⟨hT, rb, hrb, rfl, -, rfl⟩ := machine_call_ok hc1
  split at h
  · cases h
  rotate_left
  · cases h
  · cases h
  rename_i w3 ot logs2 hc2
  obtain ⟨-, ro, hro, rfl, hret2, rfl⟩ := machine_call_ok hc2
  rw [tokenCall_originToken] at hro
  cases hro
  have hot : ot = rb.st.scalars "_originToken" := by simpa [retOf] using hret2
  subst hot
  by_cases h12 : rb.st.scalars "_originToken" = 0
  · rw [ite_eq_left h12] at h; cases h
  rw [ite_eq_right h12] at h
  by_cases h13 : st.maps "_originChainId" a = 0
  · rw [ite_eq_left h13] at h; cases h
  rw [ite_eq_right h13] at h
  split at h
  · cases h
  rotate_left
  · cases h
  · cases h
  rename_i w4 md hk2
  obtain ⟨-, b, hb, rfl, hmdb⟩ := machine_hook_metadata_ok hk2
  cases hmdb
  cases h
  rw [hT]
  refine ⟨fun err herr => ?_, fun acc' hacc' => ?_⟩
  · rw [machine_hook_account_errV35 herr]
  · have hcall1 := machine_call_token_ok (T := T) (ch := ch') (w := ⟨w.token, acc'⟩) hrb
    have hcall2 := machine_call_token_ok (T := T) (ch := ch') (w := ⟨rb.st, acc'⟩)
      (tokenCall_originToken rb.st e.self)
    have hmeta : ch'.metadata rb.st (st.maps "_originChainId" a) = .ok md := by
      rw [hmd]; exact hb
    have hk2' := machine_hook_metadata_of (T := T) (w := ⟨rb.st, acc'⟩) hmeta
    rw [machine_hook_account_of (T := T) hacc']
    simp only [h11, h12, h13, ite_false, hcall1, hcall2, hk2', retOf]

/-! ## The cap's functions -/

theorem checkedAddV35_ok {x y v : Word} (h : checkedAddV35 x y = .ok v) :
    x.val + y.val < UInt256.size ∧ v.val = x.val + y.val := by
  unfold checkedAddV35 at h
  by_cases hc : UInt256.size ≤ x.val + y.val
  · rw [ite_eq_left hc] at h; cases h
  rw [ite_eq_right hc] at h
  cases h
  have hlt : x.val + y.val < UInt256.size := not_le.mp hc
  exact ⟨hlt, by rw [Fin.val_add]; exact Nat.mod_eq_of_lt hlt⟩

theorem capUpdate2V35_apply {β : Type} (f : Word → Word → β) (k a : Word) (v : β) (k' a' : Word) :
    capUpdate2V35 f k a v k' a' = if k' = k ∧ a' = a then v else f k' a' := by
  unfold capUpdate2V35
  by_cases hk : k' = k
  · subst hk
    by_cases ha : a' = a
    · subst ha; simp
    · simp [ha]
  · simp [hk]

theorem creditBridgedOutV35_ok {s t : CapStateV35} {asset amount : Word}
    (h : creditBridgedOutV35 s asset amount = .ok t) :
    t.deposited = s.deposited ∧ t.withdrawn = s.withdrawn ∧ t.backfill = s.backfill ∧
      t.inPool = s.inPool ∧ t.pending = s.pending := by
  unfold creditBridgedOutV35 at h
  split at h
  · cases h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · cases h

theorem creditDepositedV35_ok {s t : CapStateV35} {key asset amount : Word}
    (h : creditDepositedV35 s key asset amount = .ok t) :
    ∃ v : Word, v.val = (s.deposited key asset).val + amount.val ∧
      t = { s with deposited := capUpdate2V35 s.deposited key asset v } := by
  unfold creditDepositedV35 at h
  split at h
  · rename_i v hv
    cases h
    exact ⟨v, (checkedAddV35_ok hv).2, rfl⟩
  · cases h

/-- Crediting a deposit only raises deposit counters. -/
theorem creditDepositedV35_mono {s t : CapStateV35} {key asset amount : Word}
    (h : creditDepositedV35 s key asset amount = .ok t) :
    t.bridgedOut = s.bridgedOut ∧ t.withdrawn = s.withdrawn ∧ t.backfill = s.backfill ∧
      t.inPool = s.inPool ∧ t.pending = s.pending ∧
      ∀ k x, (s.deposited k x).val ≤ (t.deposited k x).val := by
  obtain ⟨v, hv, rfl⟩ := creditDepositedV35_ok h
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun k x => ?_⟩
  simp only [capUpdate2V35_apply]
  split_ifs with hkx
  · obtain ⟨rfl, rfl⟩ := hkx; omega
  · exact le_rfl

/-- The v35 hook only raises deposit counters (and may raise `bridgedOut`). -/
theorem handleBridgeToChainV35_mono {env : CapEnvV35} {s t : CapStateV35} {chain asset m : Word}
    (h : handleBridgeToChainV35 env s chain asset m = .ok t) :
    t.withdrawn = s.withdrawn ∧ t.backfill = s.backfill ∧ t.inPool = s.inPool ∧
      t.pending = s.pending ∧ ∀ k x, (s.deposited k x).val ≤ (t.deposited k x).val := by
  unfold handleBridgeToChainV35 at h
  split at h
  · cases h
  rename_i s₁ hs₁
  have h₁ : s₁.deposited = s.deposited ∧ s₁.withdrawn = s.withdrawn ∧ s₁.backfill = s.backfill ∧
      s₁.inPool = s.inPool ∧ s₁.pending = s.pending := by
    split at hs₁
    · exact creditBridgedOutV35_ok hs₁
    · cases hs₁; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hd, hw, hb, hi, hp⟩ := h₁
  split at h
  · obtain ⟨-, hw', hb', hi', hp', hd'⟩ := creditDepositedV35_mono h
    exact ⟨hw'.trans hw, hb'.trans hb, hi'.trans hi, hp'.trans hp,
      fun k x => hd ▸ hd' k x⟩
  · cases h
    exact ⟨hw, hb, hi, hp, fun k x => by rw [hd]⟩

/-- **THE V35 HOOK ON AN ASSET NOT NATIVE TO L1**, exactly: `bridgedOut` and every other counter
unchanged, and the deposit at the tracked key grows by the amount, in `ℕ`. -/
theorem handleBridgeToChainV35_bridged {env : CapEnvV35} {s t : CapStateV35} {chain asset m : Word}
    (hb : env.originChainId asset ≠ env.chainId)
    (h : handleBridgeToChainV35 env s chain asset m = .ok t) :
    t.bridgedOut = s.bridgedOut ∧ t.withdrawn = s.withdrawn ∧ t.backfill = s.backfill ∧
      t.inPool = s.inPool ∧ t.pending = s.pending ∧
      ∀ k x, (t.deposited k x).val = (s.deposited k x).val +
        (if x = asset ∧ trackedBalanceV35 env chain (env.originChainId asset) = (true, k)
          then m.val else 0) := by
  unfold handleBridgeToChainV35 at h
  rw [ite_eq_right hb] at h
  simp only at h
  by_cases htr : (trackedBalanceV35 env chain (env.originChainId asset)).1 = true
  · rw [ite_eq_left htr] at h
    obtain ⟨v, hv, rfl⟩ := creditDepositedV35_ok h
    refine ⟨rfl, rfl, rfl, rfl, rfl, fun k x => ?_⟩
    simp only [capUpdate2V35_apply]
    by_cases hkx : k = (trackedBalanceV35 env chain (env.originChainId asset)).2 ∧ x = asset
    · obtain ⟨rfl, rfl⟩ := hkx
      have htb : trackedBalanceV35 env chain (env.originChainId x) =
          (true, (trackedBalanceV35 env chain (env.originChainId x)).2) := Prod.ext htr rfl
      rw [ite_eq_left ⟨rfl, rfl⟩, hv, ite_eq_left ⟨rfl, htb⟩]
    · rw [ite_eq_right hkx, ite_eq_right]
      · simp
      · rintro ⟨rfl, htb⟩
        exact hkx ⟨by rw [htb], rfl⟩
  · rw [ite_eq_right htr] at h
    cases h
    refine ⟨rfl, rfl, rfl, rfl, rfl, fun k x => ?_⟩
    rw [ite_eq_right]
    · simp
    · rintro ⟨-, htb⟩
      exact htr (by rw [htb])

theorem L1HookFailsOnlyOnDepositOverflowAtV35 :
    Properties.L1HookFailsOnlyOnDepositOverflowAtV35 := by
  intro env s chain asset amount hb
  unfold handleBridgeToChainV35
  rw [ite_eq_right hb]
  simp only
  by_cases htr : (trackedBalanceV35 env chain (env.originChainId asset)).1 = true
  · rw [ite_eq_left htr]
    unfold creditDepositedV35 checkedAddV35
    by_cases hov : UInt256.size ≤
        (s.deposited (trackedBalanceV35 env chain (env.originChainId asset)).2 asset).val +
          amount.val
    · rw [ite_eq_left hov]
      refine ⟨fun e he => ?_, ⟨fun _ => ⟨htr, hov⟩, fun _ => ⟨_, rfl⟩⟩⟩
      cases he
      rfl
    · rw [ite_eq_right hov]
      refine ⟨fun e he => ?_, ?_⟩
      · cases he
      constructor
      · rintro ⟨e, he⟩; cases he
      · intro h; exact absurd h.2 hov
  · rw [ite_eq_right htr]
    refine ⟨fun e he => ?_, ?_⟩
    · cases he
    constructor
    · rintro ⟨e, he⟩; cases he
    · intro h; exact absurd h.1 htr

/-! ## The slice at v35 -/

theorem L1BridgeBurnAtV35IsPinCallPlusCredit : Properties.L1BridgeBurnAtV35IsPinCallPlusCredit := by
  intro d env md st w caller value c l2v a oc data
  refine ⟨fun res hx => ?_, fun henv res hx => ?_⟩
  · rw [xcall_bridgeBurn, Option.some.injEq] at hx
    obtain ⟨-, -, -, -, -, -, hmint⟩ := burnDenote_ok_factsV35 hx
    obtain ⟨herr, hok⟩ := burnDenote_other_accountV35 (ch := l1HooksPin env md)
      (ch' := l1HooksV35 env md) rfl hx
    refine ⟨bAmount data, hmint, fun err h => ?_, fun acc h => ?_⟩
    · rw [xcall_bridgeBurn, herr err h]
    · rw [xcall_bridgeBurn, hok acc h]
  · rw [xcall_bridgeBurn, Option.some.injEq] at hx
    obtain ⟨-, hoc, -, -⟩ := burnDenote_ok_factsV35 hx
    have hb : env.originChainId a ≠ env.chainId := by
      rw [henv.2, henv.1]; exact hoc
    have hpin : (l1HooksPin env md).account w.acct w.token c a (bAmount data) = .ok w.acct := by
      show handleBridgeToChainPin env w.acct a (bAmount data) = .ok w.acct
      unfold handleBridgeToChainPin
      rw [ite_eq_right hb]
    obtain ⟨-, hok⟩ := burnDenote_other_accountV35 (ch := l1HooksV35 env md)
      (ch' := l1HooksPin env md) rfl hx
    rw [xcall_bridgeBurn, hok w.acct hpin]

theorem L1BridgeBurnCreditsJournalEntryAtV35 : Properties.L1BridgeBurnCreditsJournalEntryAtV35 := by
  intro d env md st w caller value c l2v a oc data res henv hx
  rw [xcall_bridgeBurn, Option.some.injEq] at hx
  obtain ⟨hst, hoc, hamt, acc, hacc, hacct, hmint⟩ := burnDenote_ok_factsV35 hx
  have hb : env.originChainId a ≠ env.chainId := by
    rw [henv.2, henv.1]; exact hoc
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := handleBridgeToChainV35_bridged hb hacc
  rw [hacct]
  refine ⟨hst, ?_, h1, h2, h3, h4, h5, fun k x => ?_⟩
  · rw [hmint]
    exact Nat.pos_of_ne_zero (fun h0 => hamt (Fin.ext h0))
  · rw [h6, entryDepositV35, hmint]
    by_cases hxa : x = a
    · subst hxa; simp
    · simp [hxa, Ne.symm hxa]

/-- A slice step with the v35 hooks, from a vault storage the environment matches: the vault's
storage is unchanged, and either nothing in the cap or the journal changed, or the step is a
`bridgeBurn` that appended one entry and ran the v35 hook. -/
theorem sliceStep_capV35 {d : Deployment} {env : CapEnvV35}
    {md : Storage → Word → Except XFailure Bytes} {sys sys' : Sys CapStateV35}
    (henv : EnvMatchesV35 env d sys.vault) (hs : Step d (l1HooksV35 env md) sys sys') :
    sys'.vault = sys.vault ∧
      ((sys'.world.acct = sys.world.acct ∧ sys'.journal = sys.journal) ∨
        ∃ (c a : Word) (ret : Option Ret) (m : Word),
          sys'.journal = sys.journal ++ [⟨c, a, ret⟩] ∧
          handleBridgeToChainV35 env sys.world.acct c a m = .ok sys'.world.acct ∧
          (∀ key asset, (sys'.world.acct.deposited key asset).val =
            (sys.world.acct.deposited key asset).val + entryDepositV35 env key asset ⟨c, a, ret⟩) ∧
          sys'.world.acct.bridgedOut = sys.world.acct.bridgedOut ∧
          sys'.world.acct.withdrawn = sys.world.acct.withdrawn ∧
          sys'.world.acct.backfill = sys.world.acct.backfill ∧
          sys'.world.acct.inPool = sys.world.acct.inPool ∧
          sys'.world.acct.pending = sys.world.acct.pending) := by
  cases hs with
  | bridgeBurn hoc hx =>
    rename_i caller value c l2v a oc data res
    obtain ⟨hst, -, h1, h2, h3, h4, h5, h6⟩ :=
      L1BridgeBurnCreditsJournalEntryAtV35 d env md _ _ _ _ _ _ _ _ _ _ henv hx
    have hx' := hx
    rw [xcall_bridgeBurn, Option.some.injEq] at hx'
    obtain ⟨-, -, -, acc, hacc, hacct, -⟩ := burnDenote_ok_factsV35 hx'
    refine ⟨hst, Or.inr ⟨c, a, res.ret, bAmount data, rfl, ?_, h6, h1, h2, h3, h4, h5⟩⟩
    rw [hacct]; exact hacc
  | vaultCall hname _ hx =>
    obtain ⟨hst, hw, -⟩ := xcall_view hname hx
    exact ⟨hst, Or.inl ⟨by rw [hw], rfl⟩⟩
  | tokenCall _ _ _ =>
    exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem L1SliceStepIsCapStepAtV35 : Properties.L1SliceStepIsCapStepAtV35 := by
  intro d env md sys sys' henv hs
  obtain ⟨-, hcase⟩ := sliceStep_capV35 henv hs
  rcases hcase with ⟨hacct, -⟩ | ⟨c, a, ret, m, -, hhook, -⟩
  · exact Or.inl hacct
  · exact Or.inr (CapStepV35.toChain rfl hhook)

theorem journalDepositsV35_append (env : CapEnvV35) (key asset : Word) (j j' : List Entry) :
    journalDepositsV35 env key asset (j ++ j') =
      journalDepositsV35 env key asset j + journalDepositsV35 env key asset j' := by
  simp [journalDepositsV35, List.map_append, List.sum_append]

theorem L1SliceRunCreditsJournalAtV35 : Properties.L1SliceRunCreditsJournalAtV35 := by
  intro d env md sys₀ sys henv hrun
  induction hrun with
  | refl =>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, [], by simp, fun k x => by simp [journalDepositsV35]⟩
  | tail _ hstep ih =>
    obtain ⟨hv, hbo, hwd, hbf, hip, hpd, new, hj, hdep⟩ := ih
    obtain ⟨hv', hcase⟩ := sliceStep_capV35 (hv ▸ henv) hstep
    rcases hcase with ⟨hacct, hj'⟩ | ⟨c, a, ret, m, hj', -, hdep', h1, h2, h3, h4, h5⟩
    · refine ⟨hv'.trans hv, ?_, ?_, ?_, ?_, ?_, new, by rw [hj', hj], fun k x => ?_⟩
      · rw [hacct, hbo]
      · rw [hacct, hwd]
      · rw [hacct, hbf]
      · rw [hacct, hip]
      · rw [hacct, hpd]
      · rw [hacct, hdep]
    · refine ⟨hv'.trans hv, h1.trans hbo, h2.trans hwd, h3.trans hbf, h4.trans hip, h5.trans hpd,
        new ++ [⟨c, a, ret⟩], by rw [hj', hj, List.append_assoc], fun k x => ?_⟩
      rw [hdep', hdep, journalDepositsV35_append]
      simp [journalDepositsV35, Nat.add_assoc]

/-- An entry credits at most one key, so over any set of keys it credits at most its amount. -/
theorem sum_entryDepositV35_le (env : CapEnvV35) (keys : Finset Word) (asset : Word) (e : Entry) :
    ∑ k ∈ keys, entryDepositV35 env k asset e ≤ mintAmount e.ret := by
  unfold entryDepositV35
  by_cases hP : e.assetId = asset ∧
      (trackedBalanceV35 env e.destinationChain (env.originChainId asset)).1 = true
  · have hiff : ∀ k, (e.assetId = asset ∧
        trackedBalanceV35 env e.destinationChain (env.originChainId asset) = (true, k)) ↔
        (trackedBalanceV35 env e.destinationChain (env.originChainId asset)).2 = k := by
      intro k
      constructor
      · rintro ⟨-, htb⟩; rw [htb]
      · intro hk
        exact ⟨hP.1, Prod.ext hP.2 hk⟩
    simp_rw [hiff]
    rw [Finset.sum_ite_eq]
    split_ifs <;> simp
  · have hno : ∀ k, ¬ (e.assetId = asset ∧
        trackedBalanceV35 env e.destinationChain (env.originChainId asset) = (true, k)) := by
      rintro k ⟨ha, htb⟩
      exact hP ⟨ha, by rw [htb]⟩
    simp [hno]

theorem sum_journalDepositsV35_le (env : CapEnvV35) (keys : Finset Word) (asset : Word)
    (j : List Entry) : ∑ k ∈ keys, journalDepositsV35 env k asset j ≤ journalTotal j := by
  induction j with
  | nil => simp [journalDepositsV35, journalTotal]
  | cons e j ih =>
    simp only [journalDepositsV35, journalTotal, List.map_cons, List.sum_cons] at ih ⊢
    rw [Finset.sum_add_distrib]
    exact Nat.add_le_add (sum_entryDepositV35_le env keys asset e) ih

theorem L1SliceDepositsBackedByBurnsAtV35 : Properties.L1SliceDepositsBackedByBurnsAtV35 := by
  intro d env md mdm s₀ sys₀ sys hmd hw hrel henv hj hrun keys asset
  obtain ⟨-, -, -, -, -, -, new, hjn, hdep⟩ :=
    L1SliceRunCreditsJournalAtV35 d env md sys₀ sys henv hrun
  obtain ⟨hsupply, -⟩ := ReachableJournalBacked d (l1HooksV35 env md) (l1ModelHooksV35 env mdm)
    s₀ sys₀ (L1HooksAgreeAtV35 env md mdm hmd) hw hrel hj sys hrun
  rw [hj, List.nil_append] at hjn
  rw [hjn] at hsupply
  have hsum : ∑ k ∈ keys, (sys.world.acct.deposited k asset).val =
      ∑ k ∈ keys, (sys₀.world.acct.deposited k asset).val +
        ∑ k ∈ keys, journalDepositsV35 env k asset new := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => hdep k asset)
  have hle := sum_journalDepositsV35_le env keys asset new
  omega

/-! ## The cap's own runs -/

theorem recordWithdrawalV35_ok {s t : CapStateV35} {chain key asset amount : Word}
    (h : recordWithdrawalV35 s chain key asset amount = .ok t) :
    t.bridgedOut = s.bridgedOut ∧ t.deposited = s.deposited ∧ t.backfill = s.backfill ∧
      t.inPool = s.inPool ∧ t.pending = s.pending ∧
      ∃ newW : Word, newW.val = (s.withdrawn key asset).val + amount.val ∧
        t.withdrawn = capUpdate2V35 s.withdrawn key asset newW ∧
        (s.pending key = false →
          newW.val ≤ (s.deposited key asset).val + (s.backfill key asset).val) := by
  unfold recordWithdrawalV35 at h
  split at h
  · cases h
  rename_i newW hnew
  split at h
  · cases h
  rename_i hcap
  cases h
  refine ⟨rfl, rfl, rfl, rfl, rfl, newW, (checkedAddV35_ok hnew).2, rfl, fun hp => ?_⟩
  unfold capCheckV35 at hcap
  rw [hp] at hcap
  simp only [Bool.false_eq_true, ↓reduceIte] at hcap
  split at hcap
  · cases hcap
  rename_i limit hlim
  by_cases hlt : limit.val < newW.val
  · rw [ite_eq_left hlt] at hcap; cases hcap
  rw [← (checkedAddV35_ok hlim).2]
  exact not_lt.mp hlt

theorem debitBridgedOutV35_ok {s t : CapStateV35} {chain asset amount : Word}
    (h : debitBridgedOutV35 s chain asset amount = .ok t) :
    t.deposited = s.deposited ∧ t.withdrawn = s.withdrawn ∧ t.backfill = s.backfill ∧
      t.inPool = s.inPool ∧ t.pending = s.pending := by
  unfold debitBridgedOutV35 at h
  by_cases hlt : (s.bridgedOut asset).val < amount.val
  · rw [ite_eq_left hlt] at h; cases h
  rw [ite_eq_right hlt] at h
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `_handleBridgeFromChain` writes only `bridgedOut` and the withdrawals, and a withdrawal total
it changes under a key that is not pending ends at most at that key's deposits plus backfill. -/
theorem handleBridgeFromChainV35_frame {env : CapEnvV35} {s t : CapStateV35}
    {chain asset m : Word} (h : handleBridgeFromChainV35 env s chain asset m = .ok t) :
    t.deposited = s.deposited ∧ t.backfill = s.backfill ∧ t.inPool = s.inPool ∧
      t.pending = s.pending ∧
      ∀ k x, t.withdrawn k x ≠ s.withdrawn k x → s.pending k = false →
        (t.withdrawn k x).val ≤ (s.deposited k x).val + (s.backfill k x).val := by
  unfold handleBridgeFromChainV35 at h
  split at h
  · cases h
  rename_i s₁ hs₁
  have h₁ : s₁.deposited = s.deposited ∧ s₁.withdrawn = s.withdrawn ∧ s₁.backfill = s.backfill ∧
      s₁.inPool = s.inPool ∧ s₁.pending = s.pending := by
    split at hs₁
    · exact debitBridgedOutV35_ok hs₁
    · cases hs₁; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hd, hw, hb, hi, hp⟩ := h₁
  split at h
  · obtain ⟨-, hd', hb', hi', hp', newW, -, hwt, hcap⟩ := recordWithdrawalV35_ok h
    refine ⟨hd'.trans hd, hb'.trans hb, hi'.trans hi, hp'.trans hp, fun k x hne hpk => ?_⟩
    rw [hwt, capUpdate2V35_apply] at hne ⊢
    split_ifs at hne ⊢ with hkx
    · obtain ⟨rfl, rfl⟩ := hkx
      rw [← hd, ← hb]
      exact hcap (by rw [hp]; exact hpk)
    · exact absurd (by rw [hw]) hne
  · cases h
    exact ⟨hd, hb, hi, hp, fun k x hne _ => absurd (by rw [hw]) hne⟩

theorem CappedWithdrawalWithinLimitV35 : Properties.CappedWithdrawalWithinLimitV35 := by
  intro env s t chain asset amount h htr hpend
  unfold handleBridgeFromChainV35 at h
  split at h
  · cases h
  rename_i s₁ hs₁
  have h₁ : s₁.deposited = s.deposited ∧ s₁.withdrawn = s.withdrawn ∧ s₁.backfill = s.backfill ∧
      s₁.inPool = s.inPool ∧ s₁.pending = s.pending := by
    split at hs₁
    · exact debitBridgedOutV35_ok hs₁
    · cases hs₁; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hd, hw, hb, -, hp⟩ := h₁
  rw [ite_eq_left htr] at h
  obtain ⟨-, hd', hb', -, -, newW, hnew, hwt, hcap⟩ := recordWithdrawalV35_ok h
  have hwk :
      t.withdrawn (trackedBalanceV35 env chain (env.originChainId asset)).2 asset = newW := by
    rw [hwt, capUpdate2V35_apply, ite_eq_left ⟨rfl, rfl⟩]
  rw [hwk, hd', hb']
  refine ⟨by rw [hnew, hw], hcap (by rw [hp]; exact hpend)⟩

theorem checkedAddV35_eq_ok {x y : Word} (h : x.val + y.val < UInt256.size) :
    checkedAddV35 x y = .ok (x + y) := by
  unfold checkedAddV35
  rw [ite_eq_right (not_le.mpr h)]

theorem val_add_of_lt_sizeV35 {x y : Word} (h : x.val + y.val < UInt256.size) :
    (x + y).val = x.val + y.val := by
  rw [Fin.val_add]; exact Nat.mod_eq_of_lt h

/-- The tracked branch under a key that is not pending succeeds exactly within the limit. -/
theorem recordWithdrawalV35_ok_iff {s : CapStateV35} {chain key asset amount : Word}
    (hp : s.pending key = false) :
    (∃ t, recordWithdrawalV35 s chain key asset amount = .ok t) ↔
      (s.withdrawn key asset).val + amount.val ≤
          (s.deposited key asset).val + (s.backfill key asset).val ∧
        (s.deposited key asset).val + (s.backfill key asset).val < UInt256.size := by
  constructor
  · rintro ⟨t, h⟩
    unfold recordWithdrawalV35 at h
    split at h
    · cases h
    rename_i newW hnew
    split at h
    · cases h
    rename_i hcap
    obtain ⟨-, hnewv⟩ := checkedAddV35_ok hnew
    unfold capCheckV35 at hcap
    rw [hp] at hcap
    simp only [Bool.false_eq_true, ↓reduceIte] at hcap
    split at hcap
    · cases hcap
    rename_i limit hlim
    obtain ⟨hlt, hlimv⟩ := checkedAddV35_ok hlim
    by_cases hc : limit.val < newW.val
    · rw [ite_eq_left hc] at hcap; cases hcap
    exact ⟨by rw [← hnewv, ← hlimv]; exact not_lt.mp hc, hlt⟩
  · rintro ⟨hle, hlt⟩
    have h1 : (s.withdrawn key asset).val + amount.val < UInt256.size := lt_of_le_of_lt hle hlt
    have hcap : capCheckV35 s chain key asset (s.withdrawn key asset + amount) = .ok () := by
      unfold capCheckV35
      rw [hp]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [checkedAddV35_eq_ok hlt]
      simp only
      rw [ite_eq_right]
      rw [val_add_of_lt_sizeV35 hlt, val_add_of_lt_sizeV35 h1]
      exact not_lt.mpr hle
    refine ⟨{ s with
      withdrawn := capUpdate2V35 s.withdrawn key asset (s.withdrawn key asset + amount) }, ?_⟩
    unfold recordWithdrawalV35
    rw [checkedAddV35_eq_ok h1]
    simp only [hcap]

/-- The tracked branch under a pending key succeeds exactly when the new total does not overflow,
and then adds the amount. -/
theorem recordWithdrawalV35_pending {s : CapStateV35} {chain key asset amount : Word}
    (hp : s.pending key = true) :
    ((∃ t, recordWithdrawalV35 s chain key asset amount = .ok t) ↔
      (s.withdrawn key asset).val + amount.val < UInt256.size) := by
  constructor
  · rintro ⟨t, h⟩
    unfold recordWithdrawalV35 at h
    split at h
    · cases h
    rename_i newW hnew
    exact (checkedAddV35_ok hnew).1
  · intro h1
    refine ⟨{ s with
      withdrawn := capUpdate2V35 s.withdrawn key asset (s.withdrawn key asset + amount) }, ?_⟩
    unfold recordWithdrawalV35
    rw [checkedAddV35_eq_ok h1]
    have hcap : capCheckV35 s chain key asset (s.withdrawn key asset + amount) = .ok () := by
      unfold capCheckV35; rw [ite_eq_left hp]
    simp only [hcap]

/-- Before the tracked branch: the `bridgedOut` debit for an asset native to the environment's
chain succeeds iff the amount is covered, and changes no counter. -/
theorem handleBridgeFromChainV35_prefix (env : CapEnvV35) (s : CapStateV35)
    (chain asset amount : Word) :
    ((∃ s₁, (if env.originChainId asset = env.chainId then debitBridgedOutV35 s chain asset amount
        else .ok s) = .ok s₁) ↔
      (env.originChainId asset = env.chainId → amount.val ≤ (s.bridgedOut asset).val)) ∧
    ∀ s₁, (if env.originChainId asset = env.chainId then debitBridgedOutV35 s chain asset amount
        else .ok s) = .ok s₁ →
      s₁.deposited = s.deposited ∧ s₁.withdrawn = s.withdrawn ∧ s₁.backfill = s.backfill ∧
        s₁.inPool = s.inPool ∧ s₁.pending = s.pending := by
  by_cases hnat : env.originChainId asset = env.chainId
  · rw [ite_eq_left hnat]
    refine ⟨⟨fun ⟨s₁, h⟩ _ => ?_, fun h => ?_⟩, fun s₁ h => debitBridgedOutV35_ok h⟩
    · unfold debitBridgedOutV35 at h
      by_cases hlt : (s.bridgedOut asset).val < amount.val
      · rw [ite_eq_left hlt] at h; cases h
      · exact not_lt.mp hlt
    · unfold debitBridgedOutV35
      rw [ite_eq_right (not_lt.mpr (h hnat))]
      exact ⟨_, rfl⟩
  · rw [ite_eq_right hnat]
    exact ⟨⟨fun _ h => absurd h hnat, fun _ => ⟨s, rfl⟩⟩,
      fun s₁ h => by cases h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

theorem CappedWithdrawalSucceedsIffWithinLimitV35 :
    Properties.CappedWithdrawalSucceedsIffWithinLimitV35 := by
  intro env s chain asset amount htr hpend
  obtain ⟨hpre, hframe⟩ := handleBridgeFromChainV35_prefix env s chain asset amount
  constructor
  · rintro ⟨t, h⟩
    unfold handleBridgeFromChainV35 at h
    split at h
    · cases h
    rename_i s₁ hs₁
    obtain ⟨hd, hw, hb, -, hp⟩ := hframe s₁ hs₁
    rw [ite_eq_left htr] at h
    have hp₁ : s₁.pending (trackedBalanceV35 env chain (env.originChainId asset)).2 = false := by
      rw [hp]; exact hpend
    obtain ⟨hle, hlt⟩ := (recordWithdrawalV35_ok_iff hp₁).1 ⟨t, h⟩
    rw [hd, hw, hb] at hle
    rw [hd, hb] at hlt
    exact ⟨hpre.1 ⟨s₁, hs₁⟩, hle, hlt⟩
  · rintro ⟨hnat, hle, hlt⟩
    obtain ⟨s₁, hs₁⟩ := hpre.2 hnat
    obtain ⟨hd, hw, hb, -, hp⟩ := hframe s₁ hs₁
    have hp₁ : s₁.pending (trackedBalanceV35 env chain (env.originChainId asset)).2 = false := by
      rw [hp]; exact hpend
    obtain ⟨t, ht⟩ := (recordWithdrawalV35_ok_iff hp₁).2
      ⟨by rw [hd, hw, hb]; exact hle, by rw [hd, hb]; exact hlt⟩
    refine ⟨t, ?_⟩
    unfold handleBridgeFromChainV35
    rw [hs₁]
    simp only
    rw [ite_eq_left htr]
    exact ht

theorem PendingWithdrawalUncappedV35 : Properties.PendingWithdrawalUncappedV35 := by
  intro env s chain asset amount htr hpend
  obtain ⟨hpre, hframe⟩ := handleBridgeFromChainV35_prefix env s chain asset amount
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨t, h⟩
    unfold handleBridgeFromChainV35 at h
    split at h
    · cases h
    rename_i s₁ hs₁
    obtain ⟨-, hw, -, -, hp⟩ := hframe s₁ hs₁
    rw [ite_eq_left htr] at h
    have hp₁ : s₁.pending (trackedBalanceV35 env chain (env.originChainId asset)).2 = true := by
      rw [hp]; exact hpend
    have hlt := (recordWithdrawalV35_pending hp₁).1 ⟨t, h⟩
    rw [hw] at hlt
    exact ⟨hpre.1 ⟨s₁, hs₁⟩, hlt⟩
  · rintro ⟨hnat, hlt⟩
    obtain ⟨s₁, hs₁⟩ := hpre.2 hnat
    obtain ⟨-, hw, -, -, hp⟩ := hframe s₁ hs₁
    have hp₁ : s₁.pending (trackedBalanceV35 env chain (env.originChainId asset)).2 = true := by
      rw [hp]; exact hpend
    obtain ⟨t, ht⟩ := (recordWithdrawalV35_pending hp₁).2 (by rw [hw]; exact hlt)
    refine ⟨t, ?_⟩
    unfold handleBridgeFromChainV35
    rw [hs₁]
    simp only
    rw [ite_eq_left htr]
    exact ht
  · intro t h
    unfold handleBridgeFromChainV35 at h
    split at h
    · cases h
    rename_i s₁ hs₁
    obtain ⟨-, hw, -, -, -⟩ := hframe s₁ hs₁
    rw [ite_eq_left htr] at h
    obtain ⟨-, -, -, -, -, newW, hnew, hwt, -⟩ := recordWithdrawalV35_ok h
    rw [hwt, capUpdate2V35_apply, ite_eq_left ⟨rfl, rfl⟩, hnew, hw]

theorem setChainBalanceBackfillV35_ok {pool : Word} {s t : CapStateV35} {chain asset amount : Word}
    (h : setChainBalanceBackfillV35 pool s chain asset amount = .ok t) :
    chain ≠ pool ∧ s.backfill chain asset = 0 ∧ t.withdrawn = s.withdrawn ∧
      t.pending = s.pending ∧ t.backfill = capUpdate2V35 s.backfill chain asset amount ∧
      ∀ k x, (s.deposited k x).val ≤ (t.deposited k x).val := by
  unfold setChainBalanceBackfillV35 at h
  by_cases h1 : chain = pool
  · rw [ite_eq_left h1] at h; cases h
  rw [ite_eq_right h1] at h
  by_cases h2 : s.backfill chain asset ≠ 0
  · rw [ite_eq_left h2] at h; cases h
  rw [ite_eq_right h2] at h
  split at h
  · cases h
  rename_i s₁ hs₁
  cases h
  have h₁ : s₁.withdrawn = s.withdrawn ∧ s₁.pending = s.pending ∧ s₁.backfill = s.backfill ∧
      ∀ k x, (s.deposited k x).val ≤ (s₁.deposited k x).val := by
    split at hs₁
    · unfold poolBackfillCreditV35 at hs₁
      split at hs₁
      · rename_i n₁ n₀ _ _
        by_cases hlt : n₁.val < n₀.val
        · rw [ite_eq_left hlt] at hs₁; cases hs₁
        rw [ite_eq_right hlt] at hs₁
        obtain ⟨-, hw, hb, -, hp, hd⟩ := creditDepositedV35_mono hs₁
        exact ⟨hw, hp, hb, hd⟩
      · cases hs₁
      · cases hs₁
    · cases hs₁; exact ⟨rfl, rfl, rfl, fun _ _ => le_rfl⟩
  obtain ⟨hw, hp, hb, hd⟩ := h₁
  exact ⟨h1, not_not.mp h2, hw, hp, by simp only [hb], hd⟩

theorem markBackfilledV35_ok {s t : CapStateV35} {chain : Word}
    (h : markBackfilledV35 s chain = .ok t) :
    s.pending chain = true ∧ t = { s with pending := Function.update s.pending chain false } := by
  unfold markBackfilledV35 at h
  by_cases hp : s.pending chain = true
  · rw [ite_eq_left hp] at h; cases h; exact ⟨hp, rfl⟩
  · rw [ite_eq_right hp] at h; cases h

theorem moveChainBalanceToInteropPoolV35_ok {pool : Word} {interop : Bool} {s t : CapStateV35}
    {chain asset : Word} (h : moveChainBalanceToInteropPoolV35 pool interop s chain asset = .ok t) :
    t.withdrawn = s.withdrawn ∧ t.backfill = s.backfill ∧ t.pending = s.pending ∧
      ∀ k x, (s.deposited k x).val ≤ (t.deposited k x).val := by
  unfold moveChainBalanceToInteropPoolV35 at h
  by_cases h1 : interop = false
  · rw [ite_eq_left h1] at h; cases h
  rw [ite_eq_right h1] at h
  by_cases h2 : s.pending chain = true
  · rw [ite_eq_left h2] at h; cases h
  rw [ite_eq_right h2] at h
  by_cases h3 : s.inPool chain asset = true
  · rw [ite_eq_left h3] at h; cases h
  rw [ite_eq_right h3] at h
  split at h
  · cases h
  obtain ⟨-, hw, hb, -, hp, hd⟩ := creditDepositedV35_mono h
  exact ⟨hw, hb, hp, hd⟩

/-- One `CapStepV35` keeps `PoolInvV35`, for a pool key outside the chain ids. -/
theorem poolInvV35_step {pool : Word} (hpool : PoolKeyOutsideChainIdsV35 pool)
    {s t : CapStateV35} (hinv : PoolInvV35 pool s) (h : CapStepV35 pool s t) :
    PoolInvV35 pool t := by
  obtain ⟨hpp, hbf, hwd⟩ := hinv
  cases h with
  | toChain _ hh =>
    obtain ⟨hw, hb, -, hp, hd⟩ := handleBridgeToChainV35_mono hh
    refine ⟨by rw [hp]; exact hpp, fun x => by rw [hb]; exact hbf x, fun x => ?_⟩
    rw [hw]
    exact (hwd x).trans (hd pool x)
  | fromChain _ hh =>
    obtain ⟨hd, hb, -, hp, hcap⟩ := handleBridgeFromChainV35_frame hh
    refine ⟨by rw [hp]; exact hpp, fun x => by rw [hb]; exact hbf x, fun x => ?_⟩
    rw [hd]
    by_cases hne : t.withdrawn pool x = s.withdrawn pool x
    · rw [hne]; exact hwd x
    · have h' := hcap pool x hne hpp
      rw [hbf x] at h'
      simpa using h'
  | populateBridgedOut hh =>
    obtain ⟨hd, hw, hb, -, hp⟩ := creditBridgedOutV35_ok hh
    exact ⟨by rw [hp]; exact hpp, fun x => by rw [hb]; exact hbf x,
      fun x => by rw [hw, hd]; exact hwd x⟩
  | setBackfill hh =>
    rename_i chain asset amount
    obtain ⟨hne, -, hw, hp, hb, hd⟩ := setChainBalanceBackfillV35_ok hh
    refine ⟨by rw [hp]; exact hpp, fun x => ?_, fun x => ?_⟩
    · rw [hb, capUpdate2V35_apply, ite_eq_right (fun hk => hne hk.1.symm)]
      exact hbf x
    · rw [hw]
      exact (hwd x).trans (hd pool x)
  | markBackfilled hh =>
    rename_i chain
    obtain ⟨hpc, rfl⟩ := markBackfilledV35_ok hh
    have hne : pool ≠ chain := by
      rintro rfl
      rw [hpp] at hpc
      exact Bool.false_ne_true hpc
    exact ⟨by simp [Function.update_of_ne hne, hpp], hbf, hwd⟩
  | moveToPool hh =>
    obtain ⟨hw, hb, hp, hd⟩ := moveChainBalanceToInteropPoolV35_ok hh
    refine ⟨by rw [hp]; exact hpp, fun x => by rw [hb]; exact hbf x, fun x => ?_⟩
    rw [hw]
    exact (hwd x).trans (hd pool x)
  | initializeUpgrade hc =>
    rename_i chains
    have hnot : pool ∉ chains := by
      intro hm
      have h1 := hc pool hm
      unfold PoolKeyOutsideChainIdsV35 at hpool
      omega
    exact ⟨by simp [markPendingV35, hnot, hpp], hbf, hwd⟩

/-- One `CoveredCapStepV35` keeps `CapInvV35`. -/
theorem capInvV35_step {pool : Word} {s t : CapStateV35} (hinv : CapInvV35 s)
    (h : CoveredCapStepV35 pool s t) : CapInvV35 t := by
  obtain ⟨h, hcov⟩ := h
  intro k hk x
  cases h with
  | toChain _ hh =>
    obtain ⟨hw, hb, -, hp, hd⟩ := handleBridgeToChainV35_mono hh
    have hks : s.pending k = false := by rw [← hp]; exact hk
    have h1 := hinv k hks x
    have h2 := hd k x
    rw [hw, hb]
    omega
  | fromChain _ hh =>
    obtain ⟨hd, hb, -, hp, hcap⟩ := handleBridgeFromChainV35_frame hh
    have hks : s.pending k = false := by rw [← hp]; exact hk
    rw [hd, hb]
    by_cases hne : t.withdrawn k x = s.withdrawn k x
    · rw [hne]; exact hinv k hks x
    · exact hcap k x hne hks
  | populateBridgedOut hh =>
    obtain ⟨hd, hw, hb, -, hp⟩ := creditBridgedOutV35_ok hh
    have hks : s.pending k = false := by rw [← hp]; exact hk
    rw [hd, hw, hb]
    exact hinv k hks x
  | setBackfill hh =>
    rename_i chain asset amount
    obtain ⟨-, h0, hw, hp, hb, hd⟩ := setChainBalanceBackfillV35_ok hh
    have hks : s.pending k = false := by rw [← hp]; exact hk
    have h1 := hinv k hks x
    have h2 := hd k x
    rw [hw, hb, capUpdate2V35_apply]
    split_ifs with hkx
    · obtain ⟨rfl, rfl⟩ := hkx
      rw [h0] at h1
      simp only [Fin.val_zero, Nat.add_zero] at h1
      omega
    · omega
  | markBackfilled hh =>
    rename_i chain
    obtain ⟨hpc, rfl⟩ := markBackfilledV35_ok hh
    by_cases hkc : k = chain
    · subst hkc
      exact hcov k hpc hk x
    · have hks : s.pending k = false := by simpa [Function.update_of_ne hkc] using hk
      exact hinv k hks x
  | moveToPool hh =>
    obtain ⟨hw, hb, hp, hd⟩ := moveChainBalanceToInteropPoolV35_ok hh
    have hks : s.pending k = false := by rw [← hp]; exact hk
    have h1 := hinv k hks x
    have h2 := hd k x
    rw [hw, hb]
    omega
  | initializeUpgrade hc =>
    rename_i chains
    simp only [markPendingV35] at hk ⊢
    by_cases hm : k ∈ chains
    · simp [hm] at hk
    · simp only [hm, ↓reduceIte] at hk
      exact hinv k hk x

/-- `_handleBridgeFromChain` only raises withdrawal counters and leaves the pool flags alone. -/
theorem handleBridgeFromChainV35_withdrawn_mono {env : CapEnvV35} {s t : CapStateV35}
    {chain asset m : Word} (h : handleBridgeFromChainV35 env s chain asset m = .ok t) :
    t.inPool = s.inPool ∧ ∀ k x, (s.withdrawn k x).val ≤ (t.withdrawn k x).val := by
  obtain ⟨-, hframe⟩ := handleBridgeFromChainV35_prefix env s chain asset m
  unfold handleBridgeFromChainV35 at h
  split at h
  · cases h
  rename_i s₁ hs₁
  obtain ⟨-, hw, -, hi, -⟩ := hframe s₁ hs₁
  split at h
  · obtain ⟨-, -, -, hi', -, newW, hnew, hwt, -⟩ := recordWithdrawalV35_ok h
    refine ⟨hi'.trans hi, fun k x => ?_⟩
    rw [hwt, capUpdate2V35_apply, ← hw]
    split_ifs with hkx
    · obtain ⟨rfl, rfl⟩ := hkx; omega
    · exact le_rfl
  · cases h
    exact ⟨hi, fun k x => by rw [hw]⟩

theorem setChainBalanceBackfillV35_inPool {pool : Word} {s t : CapStateV35}
    {chain asset amount : Word} (h : setChainBalanceBackfillV35 pool s chain asset amount = .ok t) :
    t.inPool = s.inPool := by
  unfold setChainBalanceBackfillV35 at h
  by_cases h1 : chain = pool
  · rw [ite_eq_left h1] at h; cases h
  rw [ite_eq_right h1] at h
  by_cases h2 : s.backfill chain asset ≠ 0
  · rw [ite_eq_left h2] at h; cases h
  rw [ite_eq_right h2] at h
  split at h
  · cases h
  rename_i s₁ hs₁
  cases h
  show s₁.inPool = s.inPool
  split at hs₁
  · unfold poolBackfillCreditV35 at hs₁
    split at hs₁
    · rename_i n₁ n₀ _ _
      by_cases hlt : n₁.val < n₀.val
      · rw [ite_eq_left hlt] at hs₁; cases hs₁
      rw [ite_eq_right hlt] at hs₁
      exact (creditDepositedV35_mono hs₁).2.2.2.1
    · cases hs₁
    · cases hs₁
  · cases hs₁; rfl

theorem moveChainBalanceToInteropPoolV35_inPool {pool : Word} {interop : Bool} {s t : CapStateV35}
    {chain asset : Word} (h : moveChainBalanceToInteropPoolV35 pool interop s chain asset = .ok t) :
    ∀ k x, s.inPool k x = true → t.inPool k x = true := by
  unfold moveChainBalanceToInteropPoolV35 at h
  by_cases h1 : interop = false
  · rw [ite_eq_left h1] at h; cases h
  rw [ite_eq_right h1] at h
  by_cases h2 : s.pending chain = true
  · rw [ite_eq_left h2] at h; cases h
  rw [ite_eq_right h2] at h
  by_cases h3 : s.inPool chain asset = true
  · rw [ite_eq_left h3] at h; cases h
  rw [ite_eq_right h3] at h
  split at h
  · cases h
  intro k x hk
  rw [(creditDepositedV35_mono h).2.2.2.1]
  show capUpdate2V35 s.inPool chain asset true k x = true
  rw [capUpdate2V35_apply]
  split_ifs <;> simp [hk]

theorem capStepV35_mono {pool : Word} {s t : CapStateV35} (h : CapStepV35 pool s t) (k x : Word) :
    (s.deposited k x).val ≤ (t.deposited k x).val ∧
      (s.withdrawn k x).val ≤ (t.withdrawn k x).val ∧
      (s.backfill k x).val ≤ (t.backfill k x).val ∧
      (s.inPool k x = true → t.inPool k x = true) := by
  cases h with
  | toChain _ hh =>
    obtain ⟨hw, hb, hi, -, hd⟩ := handleBridgeToChainV35_mono hh
    exact ⟨hd k x, by rw [hw], by rw [hb], fun h => by rw [hi]; exact h⟩
  | fromChain _ hh =>
    obtain ⟨hd, hb, -, -, -⟩ := handleBridgeFromChainV35_frame hh
    obtain ⟨hi, hw⟩ := handleBridgeFromChainV35_withdrawn_mono hh
    exact ⟨by rw [hd], hw k x, by rw [hb], fun h => by rw [hi]; exact h⟩
  | populateBridgedOut hh =>
    obtain ⟨hd, hw, hb, hi, -⟩ := creditBridgedOutV35_ok hh
    exact ⟨by rw [hd], by rw [hw], by rw [hb], fun h => by rw [hi]; exact h⟩
  | setBackfill hh =>
    obtain ⟨-, h0, hw, -, hb, hd⟩ := setChainBalanceBackfillV35_ok hh
    have hi := setChainBalanceBackfillV35_inPool hh
    refine ⟨hd k x, by rw [hw], ?_, fun h => by rw [hi]; exact h⟩
    rw [hb, capUpdate2V35_apply]
    split_ifs with hkx
    · obtain ⟨rfl, rfl⟩ := hkx
      rw [h0]
      exact Nat.zero_le _
    · exact le_rfl
  | markBackfilled hh =>
    obtain ⟨-, rfl⟩ := markBackfilledV35_ok hh
    exact ⟨le_rfl, le_rfl, le_rfl, id⟩
  | moveToPool hh =>
    obtain ⟨hw, hb, -, hd⟩ := moveChainBalanceToInteropPoolV35_ok hh
    exact ⟨hd k x, by rw [hw], by rw [hb], moveChainBalanceToInteropPoolV35_inPool hh k x⟩
  | initializeUpgrade _ =>
    exact ⟨le_rfl, le_rfl, le_rfl, id⟩

theorem CapCountersMonotoneV35 : Properties.CapCountersMonotoneV35 := by
  intro pool s t hrun
  induction hrun with
  | refl => exact fun _ _ => ⟨le_rfl, le_rfl, le_rfl, id⟩
  | tail _ hstep ih =>
    intro k x
    obtain ⟨h1, h2, h3, h4⟩ := ih k x
    obtain ⟨g1, g2, g3, g4⟩ := capStepV35_mono hstep k x
    exact ⟨h1.trans g1, h2.trans g2, h3.trans g3, fun h => g4 (h4 h)⟩

theorem PoolNeverOverdrawnV35 : Properties.PoolNeverOverdrawnV35 := by
  intro pool hpool s t hinv hrun
  induction hrun with
  | refl => exact hinv
  | tail _ hstep ih => exact poolInvV35_step hpool ih hstep

theorem CoveredRunsKeepCapV35 : Properties.CoveredRunsKeepCapV35 := by
  intro pool hpool s t hcap hpinv hrun
  induction hrun with
  | refl => exact ⟨hcap, hpinv⟩
  | tail _ hstep ih => exact ⟨capInvV35_step ih.1 hstep, poolInvV35_step hpool ih.2 hstep.1⟩

/-! ## Concrete cap runs: the countermodel and the cap witnesses -/

/-- The environment of the concrete cap runs: L1 is chain 1, every asset comes from chain 7, no
chain has interop, and the pool key is the real one. -/
def capEnvNoInteropV35 : CapEnvV35 := ⟨1, fun _ => 7, fun _ => false, interopPoolChainIdV35⟩

/-- As `capEnvNoInteropV35`, but chain 5 has interop. -/
def capEnvPoolV35 : CapEnvV35 := ⟨1, fun _ => 7, fun c => decide (c = 5), interopPoolChainIdV35⟩

theorem chains5_belowBoundV35 : ∀ c ∈ ([5] : List Word), c.val < chainIdBoundV35 := by
  intro c hc
  rw [List.mem_singleton] at hc
  subst hc
  decide

/-- Fresh storage after `initializeUpgrade` listed chain 5. -/
def capPendingS1V35 : CapStateV35 := markPendingV35 CapStateV35.zero [5]

/-- Then chain 5 withdrew 3 units of asset 9 while pending. -/
def capPendingS2V35 : CapStateV35 :=
  { capPendingS1V35 with withdrawn := capUpdate2V35 capPendingS1V35.withdrawn 5 9 3 }

/-- Then `markBackfilled(5)` with no backfill set. -/
def capUncoveredS3V35 : CapStateV35 :=
  { capPendingS2V35 with pending := Function.update capPendingS2V35.pending 5 false }

theorem capPendingS2V35_step :
    handleBridgeFromChainV35 capEnvNoInteropV35 capPendingS1V35 5 9 3 = .ok capPendingS2V35 := rfl

theorem capUncoveredS3V35_run :
    LayeredVerification.Run (CapStepV35 interopPoolChainIdV35) CapStateV35.zero capUncoveredS3V35 :=
  .tail (.tail (.tail (.refl _) (CapStepV35.initializeUpgrade chains5_belowBoundV35))
    (CapStepV35.fromChain (env := capEnvNoInteropV35) rfl capPendingS2V35_step))
    (CapStepV35.markBackfilled (chain := 5) rfl)

theorem capUncoveredS3V35_not_capInv : ¬ CapInvV35 capUncoveredS3V35 := by
  intro h
  have h59 := h 5 rfl 9
  revert h59
  decide

theorem zero_poolInvV35 (pool : Word) : PoolInvV35 pool CapStateV35.zero :=
  ⟨rfl, fun _ => rfl, fun _ => le_rfl⟩

theorem zero_capInvV35 : CapInvV35 CapStateV35.zero := fun _ _ _ => by
  simp [CapStateV35.zero]

theorem UncoveredCloseBreaksCapV35 : Properties.UncoveredCloseBreaksCapV35 :=
  ⟨⟨capUncoveredS3V35, capUncoveredS3V35_run, capUncoveredS3V35_not_capInv⟩,
    fun h => capUncoveredS3V35_not_capInv
      (h _ _ zero_capInvV35 (zero_poolInvV35 _) capUncoveredS3V35_run)⟩

/-- A state where chain 5 holds 10 units of asset 9 in deposits, nothing pending. -/
def capDepositedV35 : CapStateV35 :=
  { CapStateV35.zero with deposited := capUpdate2V35 CapStateV35.zero.deposited 5 9 10 }

theorem PendingWithdrawalWitnessV35 : Properties.PendingWithdrawalWitnessV35 :=
  ⟨capEnvNoInteropV35, capPendingS1V35, capPendingS2V35, 5, 9, 3, rfl, rfl, capPendingS2V35_step,
    by decide⟩

theorem CappedWithdrawalWitnessV35 : Properties.CappedWithdrawalWitnessV35 :=
  ⟨capEnvNoInteropV35, capDepositedV35,
    { capDepositedV35 with withdrawn := capUpdate2V35 capDepositedV35.withdrawn 5 9 10 },
    5, 9, 10, 10, rfl, rfl, rfl, by decide, rfl⟩

/-- The pool after a deposit of 10 units of asset 9 to chain 5 (which has interop). -/
def capPoolP1V35 : CapStateV35 :=
  { CapStateV35.zero with
    deposited := capUpdate2V35 CapStateV35.zero.deposited interopPoolChainIdV35 9 10 }

/-- Then a withdrawal of 4 from chain 5, drawn on the pool. -/
def capPoolP2V35 : CapStateV35 :=
  { capPoolP1V35 with
    withdrawn := capUpdate2V35 capPoolP1V35.withdrawn interopPoolChainIdV35 9 4 }

theorem capPoolP1V35_step :
    handleBridgeToChainV35 capEnvPoolV35 CapStateV35.zero 5 9 10 = .ok capPoolP1V35 := rfl

theorem capPoolP2V35_step :
    handleBridgeFromChainV35 capEnvPoolV35 capPoolP1V35 5 9 4 = .ok capPoolP2V35 := rfl

theorem PoolRunWitnessV35 : Properties.PoolRunWitnessV35 := by
  refine ⟨zero_poolInvV35 _, capPoolP2V35, 9, ?_, by decide⟩
  exact .tail (.tail (.refl _) (CapStepV35.toChain (env := capEnvPoolV35) rfl capPoolP1V35_step))
    (CapStepV35.fromChain (env := capEnvPoolV35) rfl capPoolP2V35_step)

/-- A step that leaves every pending flag alone is covered. -/
theorem coveredOfPendingEqV35 {pool : Word} {s t : CapStateV35} (h : CapStepV35 pool s t)
    (hp : t.pending = s.pending) : CoveredCapStepV35 pool s t :=
  ⟨h, fun c hs ht => by rw [hp, hs] at ht; cases ht⟩

/-- Chain 5's backfill for asset 9 is set to 3 after its pending-time withdrawal. -/
def capCoveredC3V35 : CapStateV35 :=
  { capPendingS2V35 with backfill := capUpdate2V35 capPendingS2V35.backfill 5 9 3 }

/-- Then `markBackfilled(5)`. -/
def capCoveredC4V35 : CapStateV35 :=
  { capCoveredC3V35 with pending := Function.update capCoveredC3V35.pending 5 false }

/-- Then a deposit of 2 to chain 5. -/
def capCoveredC5V35 : CapStateV35 :=
  { capCoveredC4V35 with deposited := capUpdate2V35 capCoveredC4V35.deposited 5 9 2 }

/-- Then a capped withdrawal of 2 from chain 5: 5 withdrawn, against 2 deposited plus 3 backfill. -/
def capCoveredC6V35 : CapStateV35 :=
  { capCoveredC5V35 with withdrawn := capUpdate2V35 capCoveredC5V35.withdrawn 5 9 5 }

theorem capCoveredC3V35_step :
    setChainBalanceBackfillV35 interopPoolChainIdV35 capPendingS2V35 5 9 3 = .ok capCoveredC3V35 :=
  rfl

theorem capCoveredC5V35_step :
    handleBridgeToChainV35 capEnvNoInteropV35 capCoveredC4V35 5 9 2 = .ok capCoveredC5V35 := rfl

theorem capCoveredC6V35_step :
    handleBridgeFromChainV35 capEnvNoInteropV35 capCoveredC5V35 5 9 2 = .ok capCoveredC6V35 := rfl

theorem capCoveredC3V35_covers : BackfillCoversV35 capCoveredC3V35 5 := by
  intro asset
  by_cases ha : asset = 9
  · subst ha; decide
  · simp [capCoveredC3V35, capPendingS2V35, capPendingS1V35, markPendingV35, CapStateV35.zero,
      capUpdate2V35_apply, ha]

theorem CoveredRunWitnessV35 : Properties.CoveredRunWitnessV35 := by
  refine ⟨zero_capInvV35, zero_poolInvV35 _, capCoveredC6V35, 5, 9, ?_, by decide, by decide,
    by decide⟩
  have s1 : CoveredCapStepV35 interopPoolChainIdV35 CapStateV35.zero capPendingS1V35 :=
    ⟨CapStepV35.initializeUpgrade chains5_belowBoundV35, fun c hs _ => by
      simp [CapStateV35.zero] at hs⟩
  have s2 : CoveredCapStepV35 interopPoolChainIdV35 capPendingS1V35 capPendingS2V35 :=
    coveredOfPendingEqV35 (CapStepV35.fromChain (env := capEnvNoInteropV35) rfl
      capPendingS2V35_step) rfl
  have s3 : CoveredCapStepV35 interopPoolChainIdV35 capPendingS2V35 capCoveredC3V35 :=
    coveredOfPendingEqV35 (CapStepV35.setBackfill capCoveredC3V35_step) rfl
  have s4 : CoveredCapStepV35 interopPoolChainIdV35 capCoveredC3V35 capCoveredC4V35 := by
    refine ⟨CapStepV35.markBackfilled (chain := 5) rfl, fun c hs ht => ?_⟩
    by_cases hc : c = 5
    · subst hc; exact capCoveredC3V35_covers
    · simp [capCoveredC4V35, Function.update_of_ne hc] at ht
      rw [ht] at hs
      cases hs
  have s5 : CoveredCapStepV35 interopPoolChainIdV35 capCoveredC4V35 capCoveredC5V35 :=
    coveredOfPendingEqV35 (CapStepV35.toChain (env := capEnvNoInteropV35) rfl
      capCoveredC5V35_step) rfl
  have s6 : CoveredCapStepV35 interopPoolChainIdV35 capCoveredC5V35 capCoveredC6V35 :=
    coveredOfPendingEqV35 (CapStepV35.fromChain (env := capEnvNoInteropV35) rfl
      capCoveredC6V35_step) rfl
  exact .tail (.tail (.tail (.tail (.tail (.tail (.refl _) s1) s2) s3) s4) s5) s6

/-! ## Slice witnesses: `Witnesses.lean`'s vault with cap storage -/

/-- `Witnesses.lean`'s model state `s0` (asset 7 from chain 1, on chain 10; address 4 holds
100 units) with the cap storage `acc`. -/
def s0AtV35 (acc : CapStateV35) : State CapStateV35 :=
  ⟨s0.config, s0.registry, s0.paused, s0.token, acc⟩

theorem s0AtV35_wellFormed (acc : CapStateV35) : WellFormed (s0AtV35 acc) := s0_wellFormed

theorem s0AtV35_vault (acc : CapStateV35) : (s0AtV35 acc).token.config.vault ≠ 0 := s0_vault

/-- The hook environment of the slice witnesses: chain 10, the origin map of the vault storage
`vaultStorageOf` writes, no chain with interop, the real pool key. -/
def sliceEnvV35 (acc : CapStateV35) : CapEnvV35 :=
  ⟨10, (vaultStorageOf (s0AtV35 acc)).maps "_originChainId", fun _ => false, interopPoolChainIdV35⟩

theorem sliceEnvV35_matches (acc : CapStateV35) :
    EnvMatchesV35 (sliceEnvV35 acc) (deploymentOf (s0AtV35 acc)) (vaultStorageOf (s0AtV35 acc)) :=
  ⟨rfl, rfl⟩

/-- The metadata hook of `Witnesses.lean`'s `h0`, and its storage-level implementation. -/
def sliceMdmV35 : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes := h0.metadata

def sliceMdV35 : Storage → Word → Except XFailure Bytes := (liftHooks h0).metadata

theorem sliceMdV35_agrees : MetadataAgreesV35 sliceMdV35 sliceMdmV35 := (liftHooks_agree h0).2

theorem L1MetadataAgreementSatisfiableAtV35 : Properties.L1MetadataAgreementSatisfiableAtV35 :=
  fun mdm => ⟨(liftHooks (⟨fun _ _ _ _ _ => some (), mdm⟩ :
    Contracts.NativeTokenVaultBase.Hooks Unit)).metadata, (liftHooks_agree _).2⟩

theorem r0_inScopeV35 (acc : CapStateV35) :
    Contracts.NativeTokenVaultBase.InScope (s0AtV35 acc) r0 :=
  (by decide : Contracts.NativeTokenVaultBase.InScope s0 r0)

theorem r0_entryAllowedV35 (acc : CapStateV35) :
    Contracts.NativeTokenVaultBase.EntryAllowed (s0AtV35 acc) r0 :=
  (by decide : Contracts.NativeTokenVaultBase.EntryAllowed s0 r0)

/-- The model accepts `r0` with the v35 hook from fresh cap storage. -/
theorem r0_acceptedV35 :
    ∃ out, prepare (l1ModelHooksV35 (sliceEnvV35 CapStateV35.zero) sliceMdmV35)
      (s0AtV35 CapStateV35.zero) r0 = some out :=
  Contracts.NativeTokenVaultBase.preparation_enabled (s0AtV35_wellFormed _) (r0_inScopeV35 _)
    (r0_entryAllowedV35 _) rfl (by decide) (by decide) (by decide) (by decide) rfl rfl

theorem L1SliceCreditWitnessAtV35 : Properties.L1SliceCreditWitnessAtV35 := by
  obtain ⟨out, hp⟩ := r0_acceptedV35
  set acc := CapStateV35.zero
  have hrel := rel_of (s0AtV35 acc) (s0AtV35_wellFormed acc) (s0AtV35_vault acc)
  obtain ⟨res, hx, -, -, -, -⟩ := (L1BridgeBurnRefinesAtV35 (deploymentOf (s0AtV35 acc))
    (sliceEnvV35 acc) sliceMdV35 sliceMdmV35 (vaultStorageOf (s0AtV35 acc))
    ⟨tokenStorageOf (s0AtV35 acc).token, (s0AtV35 acc).accounting⟩ (s0AtV35 acc) r0
    sliceMdV35_agrees (s0AtV35_wellFormed acc) hrel).2 out hp
  obtain ⟨-, hpos, -, -, -, -, -, hdep⟩ := L1BridgeBurnCreditsJournalEntryAtV35
    (deploymentOf (s0AtV35 acc)) (sliceEnvV35 acc) sliceMdV35 (vaultStorageOf (s0AtV35 acc))
    ⟨tokenStorageOf (s0AtV35 acc).token, (s0AtV35 acc).accounting⟩ r0.caller r0.msgValue
    r0.destinationChain r0.l2MsgValue r0.assetId (addrWord r0.depositor)
    (encodeBurnData r0.data) res (sliceEnvV35_matches acc) hx
  have hpin := (L1BridgeBurnAtV35IsPinCallPlusCredit (deploymentOf (s0AtV35 acc)) (sliceEnvV35 acc)
    sliceMdV35 (vaultStorageOf (s0AtV35 acc))
    ⟨tokenStorageOf (s0AtV35 acc).token, (s0AtV35 acc).accounting⟩ r0.caller r0.msgValue
    r0.destinationChain r0.l2MsgValue r0.assetId (addrWord r0.depositor)
    (encodeBurnData r0.data)).2 (sliceEnvV35_matches acc) res hx
  refine ⟨deploymentOf (s0AtV35 acc), sliceEnvV35 acc, sliceMdV35, sliceMdmV35, s0AtV35 acc, r0,
    out, vaultStorageOf (s0AtV35 acc),
    ⟨tokenStorageOf (s0AtV35 acc).token, (s0AtV35 acc).accounting⟩, res, 20, sliceMdV35_agrees,
    s0AtV35_wellFormed acc, hrel, sliceEnvV35_matches acc, rfl, hp, hx, ?_, ⟨_, hpin⟩,
    .tail (.refl _) (Step.bridgeBurn r0.depositor.isLt hx)⟩
  rw [hdep 20 r0.assetId]
  have htb : trackedBalanceV35 (sliceEnvV35 acc) r0.destinationChain
      ((sliceEnvV35 acc).originChainId r0.assetId) = (true, 20) := by decide
  simp only [entryDepositV35, htb, true_and]
  simpa using hpos

/-- `s0`'s cap storage with the deposit counter of chain 20 for asset 7 at its maximum. -/
def capFullDepositV35 : CapStateV35 :=
  { CapStateV35.zero with
    deposited := capUpdate2V35 CapStateV35.zero.deposited 20 7 (-1 : Word) }

theorem L1DepositOverflowWitnessAtV35 : Properties.L1DepositOverflowWitnessAtV35 := by
  set acc := capFullDepositV35
  have hrel := rel_of (s0AtV35 acc) (s0AtV35_wellFormed acc) (s0AtV35_vault acc)
  have hb : (sliceEnvV35 acc).originChainId r0.assetId ≠ (sliceEnvV35 acc).chainId := by decide
  obtain ⟨out, hp⟩ : ∃ out, prepare (l1ModelHooksPin (sliceEnvV35 acc) sliceMdmV35)
      (s0AtV35 acc) r0 = some out :=
    Contracts.NativeTokenVaultBase.preparation_enabled (s0AtV35_wellFormed _) (r0_inScopeV35 _)
      (r0_entryAllowedV35 _) rfl (by decide) (by decide) (by decide) (by decide) rfl rfl
  have hhook : handleBridgeToChainV35 (sliceEnvV35 acc) (s0AtV35 acc).accounting
      r0.destinationChain r0.assetId r0.data.amount = .error (.data (.panic panicOverflow)) := rfl
  have hnone : prepare (l1ModelHooksV35 (sliceEnvV35 acc) sliceMdmV35) (s0AtV35 acc) r0 = none := by
    rw [L1PrepareAtV35IsPinPlusCredit _ _ _ _ hb, hp, hhook]
    rfl
  -- the program call with the pin's hook succeeds: `BridgeBurnRefines` at the pin's hooks
  have hagPin : HooksAgree (l1HooksPin (sliceEnvV35 acc) sliceMdV35)
      (l1ModelHooksPin (sliceEnvV35 acc) sliceMdmV35) :=
    ⟨fun _ _ _ _ _ _ _ => rfl, sliceMdV35_agrees⟩
  obtain ⟨res, hx, -, -, hret, -⟩ := (BridgeBurnRefines (deploymentOf (s0AtV35 acc))
    (l1HooksPin (sliceEnvV35 acc) sliceMdV35) (l1ModelHooksPin (sliceEnvV35 acc) sliceMdmV35)
    (vaultStorageOf (s0AtV35 acc)) ⟨tokenStorageOf (s0AtV35 acc).token, (s0AtV35 acc).accounting⟩
    (s0AtV35 acc) r0 hagPin (s0AtV35_wellFormed acc) hrel).2 out hp
  -- so the v35 call reverts with the v35 hook's failure
  obtain ⟨amount, hmint, herr, -⟩ := (L1BridgeBurnAtV35IsPinCallPlusCredit
    (deploymentOf (s0AtV35 acc)) (sliceEnvV35 acc) sliceMdV35 (vaultStorageOf (s0AtV35 acc))
    ⟨tokenStorageOf (s0AtV35 acc).token, (s0AtV35 acc).accounting⟩ r0.caller r0.msgValue
    r0.destinationChain r0.l2MsgValue r0.assetId (addrWord r0.depositor)
    (encodeBurnData r0.data)).1 res hx
  have hamount : amount = r0.data.amount := by
    apply Fin.ext
    rw [← hmint, hret, mintAmount_encodeMintData,
      (Contracts.NativeTokenVaultBase.preparation_payload (s0AtV35_wellFormed acc) hp).2.2.2.1]
  subst hamount
  exact ⟨deploymentOf (s0AtV35 acc), sliceEnvV35 acc, sliceMdV35, sliceMdmV35, s0AtV35 acc, r0,
    vaultStorageOf (s0AtV35 acc), ⟨tokenStorageOf (s0AtV35 acc).token, (s0AtV35 acc).accounting⟩,
    sliceMdV35_agrees, s0AtV35_wellFormed acc, hrel, sliceEnvV35_matches acc, hb,
    by rw [hp]; rfl, hnone, ⟨res, hx⟩, herr _ hhook⟩

end Codegen.VaultPreparationSlice
