import EraSpec.Protocol.AssetBridgePreparation.Properties.Resolution
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.Resolution

/-!
# Proofs: delivery and refund across two chains

The accounting is split along the chains. Each chain's books balance on its own record
(`step_sourceBooks`, `step_destinationBooks`), and a static identity
(`twoChain_static_identity`) relates the two records to value in flight and value paid twice.
The global identity is their sum, so the only cross-chain fact conservation needs is that no
entry is in both records, which is what the evidence supplies (`twoChain_run_records_logged`).
-/

namespace AssetBridgePreparation

open Contracts

variable {A B Wd Wr : Type}

/-! ## Reading entries -/

theorem twoChain_pendingAmountAt_of_getElem? {pending : List Obligation} {i : ℕ}
    {o : Obligation} (h : pending[i]? = some o) :
    pendingAmountAt pending i = o.data.amount.val := by
  simp only [pendingAmountAt, h]

theorem twoChain_pendingAmountAt_append_of_lt {pending : List Obligation} {o : Obligation}
    {i : ℕ} (hi : i < pending.length) :
    pendingAmountAt (pending ++ [o]) i = pendingAmountAt pending i := by
  simp only [pendingAmountAt, List.getElem?_append_left hi]

theorem twoChain_pendingAmountAt_append_length (pending : List Obligation) (o : Obligation) :
    pendingAmountAt (pending ++ [o]) pending.length = o.data.amount.val := by
  simp only [pendingAmountAt, List.getElem?_concat_length]

theorem twoChain_lt_of_getElem? {pending : List Obligation} {i : ℕ} {o : Obligation}
    (h : pending[i]? = some o) : i < pending.length :=
  (List.getElem?_eq_some_iff.mp h).1

/-! ## Sums -/

/-- Changing one summand of a range sum. -/
private theorem sum_range_change (f g : ℕ → ℕ) {n i : ℕ} (hi : i < n)
    (h : ∀ j, j ≠ i → f j = g j) :
    (∑ j ∈ Finset.range n, f j) + g i = (∑ j ∈ Finset.range n, g j) + f i := by
  have hmem : i ∈ Finset.range n := Finset.mem_range.mpr hi
  rw [← Finset.add_sum_erase _ f hmem, ← Finset.add_sum_erase _ g hmem,
    Finset.sum_congr rfl fun j hj => h j (Finset.ne_of_mem_erase hj)]
  ring

/-- Appending an entry adds its amount to a filtered range sum exactly when the new position
passes the filter. -/
private theorem sum_filter_append (p : ℕ → Prop) [DecidablePred p] (pending : List Obligation)
    (o : Obligation) :
    (∑ j ∈ Finset.range (pending ++ [o]).length with p j, pendingAmountAt (pending ++ [o]) j) =
      (∑ j ∈ Finset.range pending.length with p j, pendingAmountAt pending j) +
        (if p pending.length then o.data.amount.val else 0) := by
  rw [List.length_append, List.length_singleton, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_range_succ, twoChain_pendingAmountAt_append_length]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [twoChain_pendingAmountAt_append_of_lt (Finset.mem_range.mp hj)]

/-! ## The four sums under each kind of step -/

private theorem unrefunded_prepare (s : TwoChainLedger A B) (hr : s.RecordsInRange)
    (src : NativeTokenVaultBase.State A) (o : Obligation) :
    TwoChainLedger.unrefunded { s with source := src, pending := s.pending ++ [o] } =
      s.unrefunded + o.data.amount.val := by
  have hn : s.pending.length ∉ s.refunded := fun h => (Nat.lt_irrefl _) (hr.2 _ h)
  show (∑ j ∈ Finset.range (s.pending ++ [o]).length with j ∉ s.refunded,
      pendingAmountAt (s.pending ++ [o]) j) = _
  rw [sum_filter_append, ite_eq_left hn]
  rfl

private theorem deliveredAmount_prepare (s : TwoChainLedger A B) (hr : s.RecordsInRange)
    (src : NativeTokenVaultBase.State A) (o : Obligation) :
    TwoChainLedger.deliveredAmount { s with source := src, pending := s.pending ++ [o] } =
      s.deliveredAmount := by
  show (∑ j ∈ s.delivered, pendingAmountAt (s.pending ++ [o]) j) =
    ∑ j ∈ s.delivered, pendingAmountAt s.pending j
  exact Finset.sum_congr rfl fun j hj => twoChain_pendingAmountAt_append_of_lt (hr.1 j hj)

private theorem unrefunded_refund (s : TwoChainLedger A B) {i : ℕ} {o : Obligation}
    (hget : s.pending[i]? = some o) (hi : i ∉ s.refunded) (u : NativeTokenVaultBase.State A) :
    TwoChainLedger.unrefunded { s with source := u, refunded := insert i s.refunded } +
      o.data.amount.val = s.unrefunded := by
  have hlt := twoChain_lt_of_getElem? hget
  show (∑ j ∈ Finset.range s.pending.length with j ∉ insert i s.refunded,
      pendingAmountAt s.pending j) + o.data.amount.val =
    ∑ j ∈ Finset.range s.pending.length with j ∉ s.refunded, pendingAmountAt s.pending j
  rw [Finset.sum_filter, Finset.sum_filter]
  have hc := sum_range_change (fun j => if j ∉ s.refunded then pendingAmountAt s.pending j else 0)
    (fun j => if j ∉ insert i s.refunded then pendingAmountAt s.pending j else 0) hlt
    (fun j hj => by simp [Finset.mem_insert, hj])
  simp only [Finset.mem_insert, true_or, not_true_eq_false, ite_false, hi, not_false_eq_true,
    ite_true, twoChain_pendingAmountAt_of_getElem? hget, add_zero] at hc
  simp only [Finset.mem_insert]
  omega

private theorem deliveredAmount_deliver (s : TwoChainLedger A B) {i : ℕ} {o : Obligation}
    (hget : s.pending[i]? = some o) (hi : i ∉ s.delivered) (d : NativeTokenVaultBase.State B) :
    TwoChainLedger.deliveredAmount
        { s with destination := d, delivered := insert i s.delivered } =
      s.deliveredAmount + o.data.amount.val := by
  show (∑ j ∈ insert i s.delivered, pendingAmountAt s.pending j) = _
  rw [Finset.sum_insert hi, twoChain_pendingAmountAt_of_getElem? hget]
  unfold TwoChainLedger.deliveredAmount
  omega

/-- **THE STATIC IDENTITY.** In flight plus delivered equals unrefunded plus paid twice: each entry
is counted once on each side unless it is in neither record (counted in flight and unrefunded),
in the destination's only (delivered and unrefunded), in the source's only (nowhere), or in both
(delivered and paid twice). -/
theorem twoChain_static_identity (s : TwoChainLedger A B) (hr : s.RecordsInRange) :
    s.outstanding + s.deliveredAmount = s.unrefunded + s.doublePaid := by
  have hD : (∑ j ∈ s.delivered, pendingAmountAt s.pending j) =
      ∑ j ∈ Finset.range s.pending.length,
        if j ∈ s.delivered then pendingAmountAt s.pending j else 0 := by
    rw [Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr fun j hj => Finset.mem_range.mpr (hr.1 j hj)]
  have hDR : (∑ j ∈ s.delivered ∩ s.refunded, pendingAmountAt s.pending j) =
      ∑ j ∈ Finset.range s.pending.length,
        if j ∈ s.delivered ∩ s.refunded then pendingAmountAt s.pending j else 0 := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr fun j hj =>
      Finset.mem_range.mpr (hr.1 j (Finset.mem_inter.mp hj).1)]
  unfold TwoChainLedger.outstanding TwoChainLedger.deliveredAmount TwoChainLedger.unrefunded
    TwoChainLedger.doublePaid
  rw [hD, hDR, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : j ∈ s.delivered <;> by_cases h2 : j ∈ s.refunded <;>
    simp [h1, h2, Finset.mem_inter]

/-! ## One step -/

/-- A token transfer changes neither the supply nor the token's identity. -/
private theorem transfer_frame {tok tok' : BridgedStandardERC20.State}
    {owner recipient : NativeTokenVaultBase.Address} {amount : UInt256}
    (h : BridgedStandardERC20.transfer tok owner recipient amount = some tok') :
    tok'.totalSupply = tok.totalSupply ∧ tok'.config = tok.config := by
  unfold BridgedStandardERC20.transfer at h
  split at h
  · rw [← Option.some.inj h]
    exact ⟨rfl, rfl⟩
  · cases h

theorem twoChain_step_recordsInRange {E : TwoChainEnv A B Wd Wr} {s t : TwoChainLedger A B}
    {l : TwoChainLabel Wd Wr} (hr : s.RecordsInRange) (h : TwoChainStep E s l t) :
    t.RecordsInRange := by
  cases h with
  | prepare _ =>
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := hr.1 i hi
      simp only [List.length_append, List.length_singleton]
      omega
    · have := hr.2 i hi
      simp only [List.length_append, List.length_singleton]
      omega
  | spendSource _ => exact hr
  | spendDestination _ => exact hr
  | deliver hget _ _ _ =>
    refine ⟨fun i hi => ?_, hr.2⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact twoChain_lt_of_getElem? hget
    · exact hr.1 i hi
  | refund hget _ _ _ =>
    refine ⟨hr.1, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact twoChain_lt_of_getElem? hget
    · exact hr.2 i hi

theorem twoChain_step_wellFormed {E : TwoChainEnv A B Wd Wr} {s t : TwoChainLedger A B}
    {l : TwoChainLabel Wd Wr} (hw : NativeTokenVaultBase.WellFormed s.source)
    (h : TwoChainStep E s l t) : NativeTokenVaultBase.WellFormed t.source := by
  cases h with
  | prepare hp => exact (NativeTokenVaultBase.preparation_preserves_ledger hw hp).1
  | spendSource ht =>
    obtain ⟨hl, _, hc⟩ := BridgedStandardERC20.transfer_preserves_ledger hw.1 ht
    refine ⟨hl, ?_, ?_, hw.2.2.2⟩
    · exact (congrArg BridgedStandardERC20.Config.vault hc).trans hw.2.1
    · exact (congrArg BridgedStandardERC20.Config.assetId hc).trans hw.2.2.1
  | spendDestination _ => exact hw
  | deliver _ _ _ _ => exact hw
  | refund _ _ _ hu => exact NativeTokenVaultBase.RecoverPreservesWellFormed _ _ _ _ _ hw hu

private theorem step_sourceBooks {E : TwoChainEnv A B Wd Wr} {s t : TwoChainLedger A B}
    {l : TwoChainLabel Wd Wr} (hw : NativeTokenVaultBase.WellFormed s.source)
    (hr : s.RecordsInRange) (h : TwoChainStep E s l t) :
    t.source.token.totalSupply + t.unrefunded = s.source.token.totalSupply + s.unrefunded := by
  cases h with
  | prepare hp =>
    have hb := (NativeTokenVaultBase.preparation_backed hw hp).2.2.1
    rw [unrefunded_prepare s hr]
    dsimp only [obligation]
    omega
  | spendSource ht =>
    change _ + s.unrefunded = _
    exact congrArg (· + s.unrefunded) (transfer_frame ht).1
  | spendDestination _ => rfl
  | deliver _ _ _ _ => rfl
  | @refund j o wr u hget hnot _ hu =>
    have hx := (NativeTokenVaultBase.RecoverExact _ _ _ _ _ hu).2.2.2.2.2.1
    have hu' := unrefunded_refund s hget hnot u
    dsimp only [twoChainRefundCall] at hx ⊢
    omega

private theorem step_destinationBooks {E : TwoChainEnv A B Wd Wr} {s t : TwoChainLedger A B}
    {l : TwoChainLabel Wd Wr} (hr : s.RecordsInRange) (h : TwoChainStep E s l t) :
    t.destination.token.totalSupply + s.deliveredAmount =
      s.destination.token.totalSupply + t.deliveredAmount := by
  cases h with
  | prepare _ => rw [deliveredAmount_prepare s hr]
  | spendSource _ => rfl
  | spendDestination ht =>
    change _ + s.deliveredAmount = _ + s.deliveredAmount
    exact congrArg (· + s.deliveredAmount) (transfer_frame ht).1
  | deliver hget hnot _ hm =>
    rw [deliveredAmount_deliver s hget hnot]
    have hx := (NativeTokenVaultBase.BridgeMintExact _ _ _ _ _ hm).2.2.2.2.2.1
    dsimp only [twoChainDeliveryCall] at hx ⊢
    omega
  | refund _ _ _ _ => rfl

/-! ## Runs: invariants and books -/

theorem twoChain_run_recordsInRange {E : TwoChainEnv A B Wd Wr} {s t : TwoChainLedger A B}
    {ls : List (TwoChainLabel Wd Wr)} (hr : s.RecordsInRange) (h : TwoChainRun E s ls t) :
    t.RecordsInRange := by
  induction h with
  | refl => exact hr
  | tail _ hs ih => exact twoChain_step_recordsInRange ih hs

theorem twoChain_run_invariants {E : TwoChainEnv A B Wd Wr} {s t : TwoChainLedger A B}
    {ls : List (TwoChainLabel Wd Wr)} (hw : NativeTokenVaultBase.WellFormed s.source)
    (hr : s.RecordsInRange) (h : TwoChainRun E s ls t) :
    NativeTokenVaultBase.WellFormed t.source ∧ t.RecordsInRange := by
  induction h with
  | refl => exact ⟨hw, hr⟩
  | tail _ hs ih => exact ⟨twoChain_step_wellFormed ih.1 hs, twoChain_step_recordsInRange ih.2 hs⟩

theorem twoChain_fresh_recordsInRange {s : TwoChainLedger A B} (hf : s.FreshRecords) :
    s.RecordsInRange :=
  ⟨fun i hi => by rw [hf.1] at hi; exact absurd hi (Finset.notMem_empty i),
    fun i hi => by rw [hf.2] at hi; exact absurd hi (Finset.notMem_empty i)⟩

theorem TwoChainSourceBooks : Properties.TwoChainSourceBooks := by
  intro A B Wd Wr E s t ls hw hr h
  induction h with
  | refl => rfl
  | tail hrun hs ih =>
    have hinv := twoChain_run_invariants hw hr hrun
    have := step_sourceBooks hinv.1 hinv.2 hs
    omega

theorem TwoChainDestinationBooks : Properties.TwoChainDestinationBooks := by
  intro A B Wd Wr E s t ls hr h
  induction h with
  | refl => rfl
  | tail hrun hs ih =>
    have := step_destinationBooks (twoChain_run_recordsInRange hr hrun) hs
    omega

theorem TwoChainLedgerExact : Properties.TwoChainLedgerExact := by
  intro A B Wd Wr E s t ls hw hr h
  obtain ⟨hwt, hrt⟩ := twoChain_run_invariants hw hr h
  have hS := TwoChainSourceBooks A B Wd Wr E s t ls hw hr h
  have hD := TwoChainDestinationBooks A B Wd Wr E s t ls hr h
  have h1 := twoChain_static_identity s hr
  have h2 := twoChain_static_identity t hrt
  refine ⟨hwt, hrt, ?_⟩
  unfold TwoChainLedger.circulating
  omega

theorem TwoChainEntriesPersist : Properties.TwoChainEntriesPersist := by
  intro A B Wd Wr E s t ls h
  induction h with
  | refl => exact ⟨⟨[], (List.append_nil _).symm⟩, subset_rfl, subset_rfl⟩
  | tail _ hs ih =>
    obtain ⟨⟨later, he⟩, hd, hr⟩ := ih
    cases hs with
    | prepare _ => exact ⟨⟨_, by rw [he, List.append_assoc]⟩, hd, hr⟩
    | spendSource _ => exact ⟨⟨later, he⟩, hd, hr⟩
    | spendDestination _ => exact ⟨⟨later, he⟩, hd, hr⟩
    | deliver _ _ _ _ =>
      exact ⟨⟨later, he⟩, hd.trans (Finset.subset_insert _ _), hr⟩
    | refund _ _ _ _ =>
      exact ⟨⟨later, he⟩, hd, hr.trans (Finset.subset_insert _ _)⟩

theorem TwoChainResolutionPaysEntry : Properties.TwoChainResolutionPaysEntry := by
  intro A B Wd Wr E s t i o hget
  refine ⟨fun wd h => ?_, fun wr h => ?_⟩
  · cases h with
    | deliver hget' _ _ hm =>
      obtain rfl : _ = o := Option.some.inj (hget'.symm.trans hget)
      obtain ⟨_, _, _, _, hbal, hsup, hframe, _⟩ :=
        NativeTokenVaultBase.BridgeMintExact _ _ _ _ _ hm
      exact ⟨hbal, hsup, hframe, rfl, rfl, rfl⟩
  · cases h with
    | refund hget' _ _ hu =>
      obtain rfl : _ = o := Option.some.inj (hget'.symm.trans hget)
      obtain ⟨_, _, _, _, hbal, hsup, hframe, _⟩ :=
        NativeTokenVaultBase.RecoverExact _ _ _ _ _ hu
      exact ⟨hbal, hsup, hframe, rfl, rfl, rfl⟩

theorem twoChain_run_wellFormed {E : TwoChainEnv A B Wd Wr} {s t : TwoChainLedger A B}
    {ls : List (TwoChainLabel Wd Wr)} (hw : NativeTokenVaultBase.WellFormed s.source)
    (h : TwoChainRun E s ls t) : NativeTokenVaultBase.WellFormed t.source := by
  induction h with
  | refl => exact hw
  | tail _ hs ih => exact twoChain_step_wellFormed ih hs

theorem TwoChainEntriesFromRequests : Properties.TwoChainEntriesFromRequests := by
  intro A B Wd Wr E s t ls hw hp h
  induction h with
  | refl =>
    intro o ho
    rw [hp] at ho
    cases ho
  | @tail t u ls l hrun hs ih =>
    have lift : ∀ o ∈ t.pending, ∃ r, TwoChainLabel.prepare r ∈ ls ++ [l] ∧
        o.destinationChain = r.destinationChain ∧ o.assetId = r.assetId ∧
        o.data.originalCaller = r.depositor ∧ o.data.remoteReceiver = r.data.receiver ∧
        o.data.amount = r.data.amount ∧ o.data.amount ≠ 0 :=
      fun o ho => (ih o ho).imp fun _ ⟨hm, rest⟩ => ⟨List.mem_append_left _ hm, rest⟩
    cases hs with
    | @prepare r out hprep =>
      intro o ho
      rcases List.mem_append.mp ho with ho | ho
      · exact lift o ho
      · rw [List.mem_singleton] at ho
        subst ho
        have hwt := twoChain_run_wellFormed hw hrun
        obtain ⟨hcaller, hrecv, _, hamt, _⟩ := NativeTokenVaultBase.preparation_payload hwt hprep
        have hne := (NativeTokenVaultBase.preparation_backed hwt hprep).2.2.2
        exact ⟨r, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl, hcaller, hrecv,
          hamt, hne⟩
    | spendSource _ => exact lift
    | spendDestination _ => exact lift
    | deliver _ _ _ _ => exact lift
    | refund _ _ _ _ => exact lift

theorem TwoChainExtendsPreparationTrace : Properties.TwoChainExtendsPreparationTrace := by
  intro A B Wd Wr E
  refine ⟨fun s t d D R h => ?_, fun s t l h hl => ?_⟩
  · induction h with
    | refl => exact ⟨[], TwoChainRun.refl⟩
    | tail _ hs ih =>
      obtain ⟨ls, hrun⟩ := ih
      cases hs with
      | prepare hp => exact ⟨_, TwoChainRun.tail hrun (TwoChainStep.prepare hp)⟩
      | spend ht => exact ⟨_, TwoChainRun.tail hrun (TwoChainStep.spendSource ht)⟩
  · cases h with
    | prepare hp => exact ⟨Step.prepare hp, rfl, rfl, rfl⟩
    | spendSource ht => exact ⟨Step.spend ht, rfl, rfl, rfl⟩
    | spendDestination _ => rcases hl with hl | ⟨_, hl⟩ <;> cases hl
    | deliver _ _ _ _ => rcases hl with hl | ⟨_, hl⟩ <;> cases hl
    | refund _ _ _ _ => rcases hl with hl | ⟨_, hl⟩ <;> cases hl

theorem TwoChainResolutionsCommute : Properties.TwoChainResolutionsCommute := by
  intro A B Wd Wr E s t u i j wd wr hd hr
  cases hd with
  | @deliver _ o _ d hgeti hnoti hfin hmint =>
    cases hr with
    | @refund _ o' _ src hgetj hnotj hrec hrecover =>
      have hc := (NativeTokenVaultBase.RecoverExact _ _ _ _ _ hrecover).2.2.2.2.2.2.2.2.1
      have hmint' : NativeTokenVaultBase.bridgeMint E.destinationResolve s.destination
          (twoChainDeliveryCall s.destination.config.router src.config.chainId o) = some d := by
        rw [hc]
        exact hmint
      exact ⟨⟨src, d, s.pending, insert i s.delivered, insert j s.refunded⟩,
        TwoChainStep.refund hgetj hnotj hrec hrecover, TwoChainStep.deliver hgeti hnoti hfin hmint'⟩

theorem TwoChainRefundCallIsRecoveryCall : Properties.TwoChainRefundCallIsRecoveryCall :=
  fun _ _ _ => rfl

/-! ## Counting resolutions -/

private theorem deliveries_append (ls : List (TwoChainLabel Wd Wr)) (l : TwoChainLabel Wd Wr)
    (i : ℕ) :
    deliveryCount (ls ++ [l]) i =
      deliveryCount ls i + (if l.deliveryOf = some i then 1 else 0) := by
  unfold deliveryCount
  rw [List.countP_append, List.countP_singleton]
  simp only [decide_eq_true_eq]

private theorem refunds_append (ls : List (TwoChainLabel Wd Wr)) (l : TwoChainLabel Wd Wr)
    (i : ℕ) :
    refundCount (ls ++ [l]) i = refundCount ls i + (if l.refundOf = some i then 1 else 0) := by
  unfold refundCount
  rw [List.countP_append, List.countP_singleton]
  simp only [decide_eq_true_eq]

private theorem step_counts {E : TwoChainEnv A B Wd Wr} {s t : TwoChainLedger A B}
    {l : TwoChainLabel Wd Wr} (h : TwoChainStep E s l t) (i : ℕ) :
    (if l.deliveryOf = some i then 1 else 0) + (if i ∈ s.delivered then 1 else 0) =
        (if i ∈ t.delivered then 1 else 0) ∧
      (if l.refundOf = some i then 1 else 0) + (if i ∈ s.refunded then 1 else 0) =
        (if i ∈ t.refunded then 1 else 0) := by
  cases h with
  | prepare _ => simp [TwoChainLabel.deliveryOf, TwoChainLabel.refundOf]
  | spendSource _ => simp [TwoChainLabel.deliveryOf, TwoChainLabel.refundOf]
  | spendDestination _ => simp [TwoChainLabel.deliveryOf, TwoChainLabel.refundOf]
  | @deliver j o wd d _ hnot _ _ =>
    refine ⟨?_, by simp [TwoChainLabel.refundOf]⟩
    by_cases hij : j = i
    · subst hij
      simp [TwoChainLabel.deliveryOf, hnot]
    · simp [TwoChainLabel.deliveryOf, hij, Ne.symm hij]
  | @refund j o wr u _ hnot _ _ =>
    refine ⟨by simp [TwoChainLabel.deliveryOf], ?_⟩
    by_cases hij : j = i
    · subst hij
      simp [TwoChainLabel.refundOf, hnot]
    · simp [TwoChainLabel.refundOf, hij, Ne.symm hij]

theorem TwoChainReplayCounts : Properties.TwoChainReplayCounts := by
  intro A B Wd Wr E s t ls h i
  induction h with
  | refl => simp [deliveryCount, refundCount]
  | tail _ hs ih =>
    rw [deliveries_append, refunds_append]
    have := step_counts hs i
    omega

/-! ## Each record entry was put there by a logged step with passing evidence -/

theorem twoChain_run_records_logged {E : TwoChainEnv A B Wd Wr} {s t : TwoChainLedger A B}
    {ls : List (TwoChainLabel Wd Wr)} (h : TwoChainRun E s ls t) :
    (∀ i ∈ t.delivered, i ∈ s.delivered ∨
        ∃ wd, TwoChainLabel.deliver i wd ∈ ls ∧ E.gate.finalize i wd) ∧
      (∀ i ∈ t.refunded, i ∈ s.refunded ∨
        ∃ wr, TwoChainLabel.refund i wr ∈ ls ∧ E.gate.recover i wr) := by
  induction h with
  | refl => exact ⟨fun i hi => Or.inl hi, fun i hi => Or.inl hi⟩
  | @tail t u ls l _ hs ih =>
    have lift : ∀ x : TwoChainLabel Wd Wr, x ∈ ls → x ∈ ls ++ [l] :=
      fun x hx => List.mem_append_left _ hx
    have keepD : ∀ i ∈ t.delivered, i ∈ s.delivered ∨
        ∃ wd, TwoChainLabel.deliver i wd ∈ ls ++ [l] ∧ E.gate.finalize i wd :=
      fun i hi => (ih.1 i hi).imp_right fun ⟨wd, hm, hf⟩ => ⟨wd, lift _ hm, hf⟩
    have keepR : ∀ i ∈ t.refunded, i ∈ s.refunded ∨
        ∃ wr, TwoChainLabel.refund i wr ∈ ls ++ [l] ∧ E.gate.recover i wr :=
      fun i hi => (ih.2 i hi).imp_right fun ⟨wr, hm, hf⟩ => ⟨wr, lift _ hm, hf⟩
    cases hs with
    | prepare _ => exact ⟨keepD, keepR⟩
    | spendSource _ => exact ⟨keepD, keepR⟩
    | spendDestination _ => exact ⟨keepD, keepR⟩
    | @deliver j o wd d _ _ hf _ =>
      refine ⟨fun i hi => ?_, keepR⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact Or.inr ⟨wd, List.mem_append_right _ (List.mem_singleton_self _), hf⟩
      · exact keepD i hi
    | @refund j o wr u _ _ hf _ =>
      refine ⟨keepD, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact Or.inr ⟨wr, List.mem_append_right _ (List.mem_singleton_self _), hf⟩
      · exact keepR i hi

theorem TwoChainDoubleResolutionLocated : Properties.TwoChainDoubleResolutionLocated := by
  intro A B Wd Wr E Brk s t ls hsb hf h i hd hr
  obtain ⟨hD, hR⟩ := twoChain_run_records_logged h
  rcases hD i hd with hd0 | ⟨wd, hmd, hfin⟩
  · rw [hf.1] at hd0
    exact absurd hd0 (Finset.notMem_empty i)
  rcases hR i hr with hr0 | ⟨wr, hmr, hrec⟩
  · rw [hf.2] at hr0
    exact absurd hr0 (Finset.notMem_empty i)
  exact ⟨wd, wr, hmd, hmr, hfin, hrec, hsb i wd wr hfin hrec⟩

theorem ResolutionGateSoundIffNoBreak : Properties.ResolutionGateSoundIffNoBreak := by
  intro Wd Wr G
  exact ⟨fun h i wd wr hf hr => h i wd wr ⟨hf, hr⟩, fun h i wd wr ⟨hf, hr⟩ => h i wd wr hf hr⟩

theorem TwoChainExclusive : Properties.TwoChainExclusive := by
  intro A B Wd Wr E s t ls hs hf h i ⟨hd, hr⟩
  obtain ⟨_, _, _, _, _, _, hbrk⟩ := TwoChainDoubleResolutionLocated A B Wd Wr E
    (fun _ _ _ => False) s t ls ((ResolutionGateSoundIffNoBreak Wd Wr E.gate).mp hs) hf h i hd hr
  exact hbrk

/-- With fresh records, the run's resolution counts are the end state's record memberships. -/
private theorem counts_of_fresh {E : TwoChainEnv A B Wd Wr} {s t : TwoChainLedger A B}
    {ls : List (TwoChainLabel Wd Wr)} (hf : s.FreshRecords) (h : TwoChainRun E s ls t) (i : ℕ) :
    deliveryCount ls i = (if i ∈ t.delivered then 1 else 0) ∧
      refundCount ls i = (if i ∈ t.refunded then 1 else 0) := by
  obtain ⟨hd, hr⟩ := TwoChainReplayCounts A B Wd Wr E s t ls h i
  rw [hf.1] at hd
  rw [hf.2] at hr
  simp only [Finset.notMem_empty, ite_false, add_zero] at hd hr
  exact ⟨hd, hr⟩

theorem TwoChainResolvesOnce : Properties.TwoChainResolvesOnce := by
  intro A B Wd Wr E s t ls hs hf h i
  obtain ⟨hd, hr⟩ := counts_of_fresh hf h i
  have hx := TwoChainExclusive A B Wd Wr E s t ls hs hf h i
  rw [hd, hr]
  by_cases h1 : i ∈ t.delivered <;> by_cases h2 : i ∈ t.refunded <;> simp_all

theorem TwoChainResolvesOnceOrBreak : Properties.TwoChainResolvesOnceOrBreak := by
  intro A B Wd Wr E Brk s t ls hsb hf h i
  obtain ⟨hd, hr⟩ := counts_of_fresh hf h i
  by_cases hboth : i ∈ t.delivered ∧ i ∈ t.refunded
  · obtain ⟨wd, wr, hmd, hmr, _, _, hbrk⟩ :=
      TwoChainDoubleResolutionLocated A B Wd Wr E Brk s t ls hsb hf h i hboth.1 hboth.2
    exact Or.inr ⟨wd, wr, hmd, hmr, hbrk⟩
  · left
    rw [hd, hr]
    by_cases h1 : i ∈ t.delivered <;> by_cases h2 : i ∈ t.refunded <;> simp_all

/-! ## Conservation -/

private theorem doublePaid_fresh {s : TwoChainLedger A B} (hf : s.FreshRecords) :
    s.doublePaid = 0 := by
  simp [TwoChainLedger.doublePaid, hf.1]

theorem TwoChainConservation : Properties.TwoChainConservation := by
  intro A B Wd Wr E s t ls hs hw hf h
  obtain ⟨_, _, hex⟩ := TwoChainLedgerExact A B Wd Wr E s t ls hw
    (twoChain_fresh_recordsInRange hf) h
  have hexcl := TwoChainExclusive A B Wd Wr E s t ls hs hf h
  have ht : t.doublePaid = 0 := by
    unfold TwoChainLedger.doublePaid
    rw [Finset.eq_empty_of_forall_notMem fun i hi => hexcl i (Finset.mem_inter.mp hi),
      Finset.sum_empty]
  rw [doublePaid_fresh hf, ht] at hex
  exact ⟨by omega, ht⟩

theorem TwoChainConservedOrBreak : Properties.TwoChainConservedOrBreak := by
  intro A B Wd Wr E Brk s t ls hsb hw hf h
  obtain ⟨_, _, hex⟩ := TwoChainLedgerExact A B Wd Wr E s t ls hw
    (twoChain_fresh_recordsInRange hf) h
  rw [doublePaid_fresh hf] at hex
  by_cases h0 : t.doublePaid = 0
  · left
    omega
  · right
    obtain ⟨i, hi⟩ := Finset.nonempty_of_sum_ne_zero h0
    obtain ⟨hd, hr⟩ := Finset.mem_inter.mp hi
    obtain ⟨wd, wr, hmd, hmr, _, _, hbrk⟩ :=
      TwoChainDoubleResolutionLocated A B Wd Wr E Brk s t ls hsb hf h i hd hr
    exact ⟨i, wd, wr, hmd, hmr, hbrk⟩

/-! ## Refund enabledness -/

/-- A successful preparation passed the vault's scope and entry checks. -/
private theorem prepare_guards {hooks : NativeTokenVaultBase.Hooks A}
    {s : NativeTokenVaultBase.State A} {r : NativeTokenVaultBase.Request}
    {out : NativeTokenVaultBase.Result A} (h : NativeTokenVaultBase.prepare hooks s r = some out) :
    NativeTokenVaultBase.InScope s r ∧ NativeTokenVaultBase.EntryAllowed s r := by
  unfold NativeTokenVaultBase.prepare at h
  split at h
  · rename_i hg
    exact hg
  · cases h

private theorem burn_owner_ne_zero {tok burned : BridgedStandardERC20.State}
    {caller owner : NativeTokenVaultBase.Address} {amount : UInt256}
    (h : BridgedStandardERC20.burn tok caller owner amount = some burned) : owner ≠ 0 := by
  unfold BridgedStandardERC20.burn at h
  split at h
  · rename_i hg
    exact hg.2.2.1
  · cases h

/-- What every entry's preparation established about the source vault, and the trace never
changes: the vault is unpaused, the entry names the tracked asset and a nonzero depositor, and the
tracked representation is in scope. -/
private def SourceReady (s : TwoChainLedger A B) : Prop :=
  ∀ o ∈ s.pending, s.source.paused = false ∧ o.assetId = s.source.config.assetId ∧
    o.data.originalCaller ≠ 0 ∧ s.source.config.vault ≠ 0 ∧ s.source.config.tokenAddress ≠ 0 ∧
    s.source.config.originChainId ≠ s.source.config.chainId

private theorem sourceReady_frame {s t : TwoChainLedger A B} (hready : SourceReady s)
    (hp : t.pending = s.pending) (hc : t.source.config = s.source.config)
    (hpa : t.source.paused = s.source.paused) : SourceReady t := by
  intro o ho
  rw [hp] at ho
  rw [hc, hpa]
  exact hready o ho

private theorem step_sourceReady {E : TwoChainEnv A B Wd Wr} {s t : TwoChainLedger A B}
    {l : TwoChainLabel Wd Wr} (hw : NativeTokenVaultBase.WellFormed s.source)
    (hready : SourceReady s) (h : TwoChainStep E s l t) : SourceReady t := by
  cases h with
  | @prepare r out hp =>
    obtain ⟨_, hc, _, hpa, _⟩ := NativeTokenVaultBase.preparation_preserves_ledger hw hp
    obtain ⟨hs, he⟩ := prepare_guards hp
    have hasset := (NativeTokenVaultBase.preparation_asset_binding hw hp).1
    have hcaller := (NativeTokenVaultBase.preparation_payload hw hp).1
    have hdep := burn_owner_ne_zero (NativeTokenVaultBase.preparation_backed hw hp).1
    intro o ho
    show out.state.paused = false ∧ o.assetId = out.state.config.assetId ∧
      o.data.originalCaller ≠ 0 ∧ out.state.config.vault ≠ 0 ∧
      out.state.config.tokenAddress ≠ 0 ∧ out.state.config.originChainId ≠ out.state.config.chainId
    rw [hc, hpa]
    rcases List.mem_append.mp ho with ho | ho
    · exact hready o ho
    · rw [List.mem_singleton] at ho
      subst ho
      exact ⟨he.2.1, hasset, fun h0 => hdep (hcaller.symm.trans h0), hs.1, hs.2.1, hs.2.2.2.1⟩
  | spendSource _ => exact sourceReady_frame hready rfl rfl rfl
  | spendDestination _ => exact sourceReady_frame hready rfl rfl rfl
  | deliver _ _ _ _ => exact sourceReady_frame hready rfl rfl rfl
  | refund _ _ _ hu =>
    obtain ⟨_, _, _, _, _, _, _, _, hc, _, hpa⟩ :=
      NativeTokenVaultBase.RecoverExact _ _ _ _ _ hu
    exact sourceReady_frame hready rfl hc hpa

private theorem run_sourceReady {E : TwoChainEnv A B Wd Wr} {s t : TwoChainLedger A B}
    {ls : List (TwoChainLabel Wd Wr)} (hw : NativeTokenVaultBase.WellFormed s.source)
    (hr : s.RecordsInRange) (hready : SourceReady s) (h : TwoChainRun E s ls t) :
    SourceReady t := by
  induction h with
  | refl => exact hready
  | tail hrun hs ih => exact step_sourceReady (twoChain_run_invariants hw hr hrun).1 ih hs

theorem TwoChainRefundAvailable : Properties.TwoChainRefundAvailable := by
  intro A B Wd Wr E s t ls hw hfresh h i o wr acc hget hnot hrec hhook
  have hr := twoChain_fresh_recordsInRange hfresh.2
  obtain ⟨hwt, _⟩ := twoChain_run_invariants hw hr h
  have hready : SourceReady t := run_sourceReady hw hr (by
    intro o ho
    rw [hfresh.1] at ho
    cases ho) h
  have hbooks := TwoChainSourceBooks A B Wd Wr E s t ls hw hr h
  have h0 : TwoChainLedger.unrefunded s = 0 := by simp [TwoChainLedger.unrefunded, hfresh.1]
  have hle : o.data.amount.val ≤ t.unrefunded := by
    unfold TwoChainLedger.unrefunded
    rw [← twoChain_pendingAmountAt_of_getElem? hget]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (twoChain_lt_of_getElem? hget), hnot⟩)
  have hsup : s.source.token.totalSupply < UInt256.size := hw.1.2.1
  obtain ⟨hpa, hasset, hcaller, hvault, htok, horigin⟩ := hready o (List.mem_of_getElem? hget)
  have hentry : NativeTokenVaultBase.ResolveEntryAllowed t.source
      (twoChainRefundCall t.source.config.router o) := ⟨rfl, rfl, hpa⟩
  have hscope : NativeTokenVaultBase.RegisteredBridged t.source
      (twoChainRefundCall t.source.config.router o) := by
    refine ⟨hvault, hasset, horigin, ?_, htok⟩
    show t.source.registry.tokenForAsset o.assetId = t.source.config.tokenAddress
    rw [hasset]
    exact hwt.2.2.2.1
  obtain ⟨u, hu⟩ := NativeTokenVaultBase.RecoverEnabled A E.sourceResolve t.source _ acc hwt.2
    hentry hscope hcaller (by show t.source.token.totalSupply + o.data.amount.val < _; omega)
    hhook
  exact ⟨_, TwoChainStep.refund hget hnot hrec hu,
    (NativeTokenVaultBase.RecoverExact _ _ _ _ _ hu).2.2.2.2.1⟩

/-! ## Concrete runs for the countermodel and the witnesses

The source is B2's example vault (`NativeTokenVaultBase.ResolutionExample.stateWith`: vault `1`,
router `2`, token `5`, asset `3`, this chain `1`, origin chain `4`), with holder `11` owning `4`
units. The destination is the same representation of asset `3` on chain `6`, with no supply yet.
Hooks always succeed (accounting is `Unit`): the hooks are B2's subject, and every result here is
universally quantified over them. Every vault call below is evaluated by `rfl`. Two generic runs
are built for an arbitrary gate, so the countermodel and every witness (also those of
`Proofs/ResolutionEvidence.lean`) differ only in the evidence. -/

namespace TwoChainExample

open Contracts.NativeTokenVaultBase.ResolutionExample

/-- Preparation hooks that always succeed. -/
def unitHooks : NativeTokenVaultBase.Hooks Unit := ⟨fun _ _ _ _ _ => some (), fun _ _ => some []⟩

/-- A resolution hook that always succeeds. -/
def unitResolve : NativeTokenVaultBase.ResolutionHooks Unit := ⟨fun _ _ _ _ _ => some ()⟩

/-- The example environment, for any evidence. -/
def env (G : ResolutionGate Wd Wr) : TwoChainEnv Unit Unit Wd Wr :=
  ⟨unitHooks, unitResolve, unitResolve, G⟩

/-- The destination vault: B2's example configuration on chain `6`. -/
def dstConfig : NativeTokenVaultBase.Config := ⟨1, 2, 5, 3, 0, 6, 4⟩

def dstStart : NativeTokenVaultBase.State Unit :=
  ⟨dstConfig, exRegistry, false, BridgedStandardERC20.empty ⟨1, 7, 3⟩, ()⟩

def srcStart : NativeTokenVaultBase.State Unit := stateWith (tokenWith 11 4) ()

/-- The fresh trace both runs start from. -/
def start : TwoChainLedger Unit Unit := ⟨srcStart, dstStart, [], ∅, ∅⟩

/-- Burn one unit of holder `11` towards chain `6` for receiver `12` (B2's `prepRequest`). -/
abbrev req : NativeTokenVaultBase.Request := prepRequest 12

def src1 : NativeTokenVaultBase.State Unit :=
  { srcStart with token := BridgedStandardERC20.burnEffect srcStart.token 11 1, accounting := () }

def data1 : NativeTokenVaultBase.MintData :=
  NativeTokenVaultBase.mintData req (BridgedStandardERC20.burnEffect srcStart.token 11 1) []

def entry1 : Obligation := obligation req data1

def src2 : NativeTokenVaultBase.State Unit :=
  { src1 with token := BridgedStandardERC20.burnEffect src1.token 11 1, accounting := () }

def data2 : NativeTokenVaultBase.MintData :=
  NativeTokenVaultBase.mintData req (BridgedStandardERC20.burnEffect src1.token 11 1) []

def entry2 : Obligation := obligation req data2

/-- After holder `11` transfers one unit to `14`. -/
def src2Spent : BridgedStandardERC20.State := BridgedStandardERC20.transferEffect src2.token 11 14 1

/-- After the delivery of the first entry: one unit minted to `12`. -/
def dst1 : NativeTokenVaultBase.State Unit :=
  { dstStart with token := BridgedStandardERC20.mintEffect dstStart.token 12 1, accounting := () }

/-- After receiver `12` transfers the delivered unit to `13`. -/
def dst1Spent : BridgedStandardERC20.State := BridgedStandardERC20.transferEffect dst1.token 12 13 1

/-- The source after refunding the first entry: the unit re-minted to depositor `11`. -/
def src1Refunded : NativeTokenVaultBase.State Unit :=
  { src1 with token := BridgedStandardERC20.mintEffect src1.token 11 1, accounting := () }

/-- The end of the double-payment run: the entry is in both records. -/
def doublePayEnd : TwoChainLedger Unit Unit :=
  ⟨src1Refunded, dst1, [entry1], insert 0 ∅, insert 0 ∅⟩

/-- The state before the split run's refund. -/
def splitPre : TwoChainLedger Unit Unit :=
  ⟨{ src2 with token := src2Spent }, { dst1 with token := dst1Spent }, [entry1, entry2],
    insert 0 ∅, ∅⟩

/-- The source after refunding the second entry. -/
def src2Refunded : NativeTokenVaultBase.State Unit :=
  { src2 with token := BridgedStandardERC20.mintEffect src2Spent 11 1, accounting := () }

/-- The end of the split run: entry `0` delivered, entry `1` refunded. -/
def splitPost : TwoChainLedger Unit Unit :=
  ⟨src2Refunded, { dst1 with token := dst1Spent }, [entry1, entry2], insert 0 ∅, insert 1 ∅⟩

/-- The destination after delivering the first entry a second time. -/
def dst1Twice : NativeTokenVaultBase.State Unit :=
  { dst1 with token := BridgedStandardERC20.mintEffect dst1.token 12 1, accounting := () }

/-- The source after refunding the second entry once, then a second time. -/
def src2Once : NativeTokenVaultBase.State Unit :=
  { src2 with token := BridgedStandardERC20.mintEffect src2.token 11 1, accounting := () }

def src2Twice : NativeTokenVaultBase.State Unit :=
  { src2Once with token := BridgedStandardERC20.mintEffect src2Once.token 11 1, accounting := () }

/-- The end of the run without the local records: both entries paid twice. -/
def unguardedEnd : TwoChainLedger Unit Unit :=
  ⟨src2Twice, dst1Twice, [entry1, entry2], insert 0 (insert 0 ∅), insert 1 (insert 1 ∅)⟩

theorem start_wellFormed : NativeTokenVaultBase.WellFormed start.source :=
  stateWith_wf (show (11 : NativeTokenVaultBase.Address) ≠ 0 by decide) 4 ()

theorem start_fresh : start.FreshTrace := ⟨rfl, rfl, rfl⟩

/-- **THE DOUBLE-PAYMENT RUN, FOR ANY GATE THAT ACCEPTS BOTH SIDES OF ENTRY `0`.** One preparation,
delivered with `wd` and refunded with `wr`: the entry ends in both records and the books end one
unit above their start. -/
theorem doublePay_run (G : ResolutionGate Wd Wr) (wd : Wd) (wr : Wr) (hf : G.finalize 0 wd)
    (hr : G.recover 0 wr) :
    ∃ t, TwoChainRun (env G) start [.prepare req, .deliver 0 wd, .refund 0 wr] t ∧
      0 ∈ t.delivered ∧ 0 ∈ t.refunded ∧ pendingAmountAt t.pending 0 = 1 ∧
      t.circulating + t.outstanding =
        start.circulating + start.outstanding + pendingAmountAt t.pending 0 := by
  have hrun : TwoChainRun (env G) start [.prepare req, .deliver 0 wd, .refund 0 wr]
      doublePayEnd :=
    TwoChainRun.tail (TwoChainRun.tail (TwoChainRun.tail TwoChainRun.refl
      (TwoChainStep.prepare (out := ⟨src1, data1⟩) rfl))
      (TwoChainStep.deliver (i := 0) (o := entry1) (d := dst1) rfl (Finset.notMem_empty 0) hf rfl))
      (TwoChainStep.refund (i := 0) (o := entry1) (u := src1Refunded) rfl (Finset.notMem_empty 0)
        hr rfl)
  refine ⟨_, hrun, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _, rfl, ?_⟩
  obtain ⟨_, _, hex⟩ := TwoChainLedgerExact Unit Unit Wd Wr (env G) start _ _ start_wellFormed
    (twoChain_fresh_recordsInRange start_fresh.2) hrun
  rw [doublePaid_fresh start_fresh.2] at hex
  have hdp : doublePayEnd.doublePaid = pendingAmountAt doublePayEnd.pending 0 := by
    simp [TwoChainLedger.doublePaid, doublePayEnd]
  rw [hdp] at hex
  exact hex

/-- **THE SPLIT RUN, FOR ANY GATE THAT LETS THE DESTINATION EXECUTE ENTRY `0` AND THE SOURCE REFUND
ENTRY `1`.** Two preparations, a source transfer, the delivery of entry `0` and a destination
transfer reach `pre`; from `pre`, the refund of entry `1` reaches `post`. -/
theorem split_run (G : ResolutionGate Wd Wr) (wd : Wd) (wr : Wr) (hf : G.finalize 0 wd)
    (hr : G.recover 1 wr) :
    ∃ pre post, TwoChainRun (env G) start
        [.prepare req, .prepare req, .spendSource, .deliver 0 wd, .spendDestination] pre ∧
      pre.pending[1]? = some entry2 ∧ 1 ∉ pre.refunded ∧
      TwoChainStep (env G) pre (.refund 1 wr) post ∧
      TwoChainRun (env G) start
        ([.prepare req, .prepare req, .spendSource, .deliver 0 wd, .spendDestination] ++
          [.refund 1 wr]) post ∧
      0 ∈ post.delivered ∧ 1 ∈ post.refunded ∧ pendingAmountAt post.pending 0 = 1 ∧
      pendingAmountAt post.pending 1 = 1 ∧ post.outstanding = 0 ∧
      post.circulating + post.outstanding = start.circulating + start.outstanding := by
  have hrun : TwoChainRun (env G) start
      [.prepare req, .prepare req, .spendSource, .deliver 0 wd, .spendDestination] splitPre :=
    TwoChainRun.tail (TwoChainRun.tail (TwoChainRun.tail (TwoChainRun.tail (TwoChainRun.tail
      TwoChainRun.refl
      (TwoChainStep.prepare (out := ⟨src1, data1⟩) rfl))
      (TwoChainStep.prepare (out := ⟨src2, data2⟩) rfl))
      (TwoChainStep.spendSource (owner := 11) (recipient := 14) (amount := 1) rfl))
      (TwoChainStep.deliver (i := 0) (o := entry1) (d := dst1) rfl (Finset.notMem_empty 0) hf rfl))
      (TwoChainStep.spendDestination (owner := 12) (recipient := 13) (amount := 1) rfl)
  have hstep : TwoChainStep (env G) splitPre (.refund 1 wr) splitPost :=
    TwoChainStep.refund (i := 1) (o := entry2) (u := src2Refunded) rfl (Finset.notMem_empty 1) hr
      rfl
  have hrun' := TwoChainRun.tail hrun hstep
  refine ⟨_, _, hrun, rfl, Finset.notMem_empty 1, hstep, hrun',
    Finset.mem_insert_self _ _, Finset.mem_insert_self _ _, rfl, rfl, ?_, ?_⟩
  · simp [TwoChainLedger.outstanding, splitPost, Finset.sum_filter, Finset.sum_range_succ]
  · obtain ⟨_, _, hex⟩ := TwoChainLedgerExact Unit Unit Wd Wr (env G) start _ _ start_wellFormed
      (twoChain_fresh_recordsInRange start_fresh.2) hrun'
    have hdp : TwoChainLedger.doublePaid splitPost = 0 := by
      simp [TwoChainLedger.doublePaid, splitPost]
    rw [doublePaid_fresh start_fresh.2, hdp] at hex
    omega

end TwoChainExample

open TwoChainExample

theorem TwoChainConflictingGateDoublePays : Properties.TwoChainConflictingGateDoublePays := by
  obtain ⟨t, hrun, hd, hr, hamt, hval⟩ :=
    doublePay_run acceptAllResolutionGate () () trivial trivial
  refine ⟨env acceptAllResolutionGate, start, t, _, rfl, fun h => h 0 () () ⟨trivial, trivial⟩,
    start_wellFormed, start_fresh, hrun, hd, hr, by rw [hamt]; decide, hval⟩

theorem TwoChainSatisfiable : Properties.TwoChainSatisfiable := by
  obtain ⟨pre, post, hrun, hget, hnot, hstep, hrun', hd, hr, h0, h1, hout, _⟩ :=
    split_run (splitResolutionGate 0 1) () () rfl rfl
  refine ⟨env (splitResolutionGate 0 1), start, pre, post, _, entry2, rfl,
    fun i _ _ ⟨h0, h1⟩ => absurd (h0.symm.trans h1) (by decide), start_wellFormed, start_fresh,
    hrun, by simp, by simp, by simp, hget, hnot, rfl, rfl, hstep, hrun', hd, hr,
    by rw [h0]; decide, by rw [h1]; decide, hout⟩

theorem TwoChainWithoutRecordsPaysTwice : Properties.TwoChainWithoutRecordsPaysTwice := by
  let G := splitResolutionGate 0 1
  have hrun : TwoChainRunUnguarded (env G) start
      [.prepare req, .prepare req, .deliver 0 (), .deliver 0 (), .refund 1 (), .refund 1 ()]
      unguardedEnd :=
    TwoChainRunUnguarded.tail (TwoChainRunUnguarded.tail (TwoChainRunUnguarded.tail
      (TwoChainRunUnguarded.tail (TwoChainRunUnguarded.tail (TwoChainRunUnguarded.tail
      TwoChainRunUnguarded.refl
      (.guarded (TwoChainStep.prepare (out := ⟨src1, data1⟩) rfl)))
      (.guarded (TwoChainStep.prepare (out := ⟨src2, data2⟩) rfl)))
      (.guarded (TwoChainStep.deliver (i := 0) (o := entry1) (d := dst1) rfl
        (Finset.notMem_empty 0) rfl rfl)))
      (.redeliver (i := 0) (o := entry1) (d := dst1Twice) rfl rfl rfl))
      (.guarded (TwoChainStep.refund (i := 1) (o := entry2) (u := src2Once) rfl
        (Finset.notMem_empty 1) rfl rfl)))
      (.rerefund (i := 1) (o := entry2) (u := src2Twice) rfl rfl rfl)
  have hout : unguardedEnd.outstanding = 0 := by
    simp [TwoChainLedger.outstanding, unguardedEnd, Finset.sum_filter, Finset.sum_range_succ]
  have hout0 : start.outstanding = 0 := by
    simp [TwoChainLedger.outstanding, start]
  refine ⟨env G, start, unguardedEnd, _, rfl,
    fun i _ _ ⟨h0, h1⟩ => absurd (h0.symm.trans h1) (by decide), start_wellFormed, start_fresh,
    hrun, rfl, rfl, by decide, by decide, ?_⟩
  rw [hout, hout0]
  rfl

theorem TwoChainResolutionsCommuteSatisfiable :
    Properties.TwoChainResolutionsCommuteSatisfiable := by
  let G := splitResolutionGate 0 1
  have hrun : TwoChainRun (env G) start [.prepare req, .prepare req]
      ⟨src2, dstStart, [entry1, entry2], ∅, ∅⟩ :=
    TwoChainRun.tail (TwoChainRun.tail TwoChainRun.refl
      (TwoChainStep.prepare (out := ⟨src1, data1⟩) rfl))
      (TwoChainStep.prepare (out := ⟨src2, data2⟩) rfl)
  refine ⟨env G, start, _, _, _, _, rfl,
    fun i _ _ ⟨h0, h1⟩ => absurd (h0.symm.trans h1) (by decide), start_wellFormed, start_fresh,
    hrun,
    TwoChainStep.deliver (i := 0) (o := entry1) (d := dst1) rfl (Finset.notMem_empty 0) rfl rfl,
    TwoChainStep.refund (i := 1) (o := entry2)
      (u := { src2 with token := BridgedStandardERC20.mintEffect src2.token 11 1,
                        accounting := () })
      rfl (Finset.notMem_empty 1) rfl rfl⟩

end AssetBridgePreparation
