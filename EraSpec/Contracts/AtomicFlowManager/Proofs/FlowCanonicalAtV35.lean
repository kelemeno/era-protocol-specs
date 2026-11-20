import EraSpec.Contracts.AtomicFlowManager.Properties.FlowCanonicalAtV35
import EraSpec.Contracts.AtomicFlowManager.Proofs.FlowCanonical
import EraSpec.Contracts.AtomicFlowManager.Proofs.Model

/-!
# Proofs: `_validateAndComputeFlowId` and the leg writes at `draft/v0.35.0`

* The acceptance results unfold `validateV35` check by check; the canonicity results are the
  `AttackVectors.FlowCanonical` theorems applied to `AcceptedV35 → Valid`.
* `AppendV35SomeIff`: an accepted preimage has distinct bundle hashes, so `append`'s leg search
  stops at the position that declares the leg (`legIndex_source_of_mem_zip_V35`).
* The run results rest on one lemma per call (`stepV35_legState_V35`): a successful call leaves a
  leg as it was, or is the `append` of that leg under a preimage that validates to the leg's flow
  id (`Unset → Committed`), or an `authorizeRefund` under that flow id listing the leg
  (`Committed → Revertable`), or the `claimRefund` of that leg (`Revertable → Reverted`). The
  marking loop is characterized leg by leg (`markRevertableV35_legState`). Induction over the
  run gives the backing `append` (`writtenLegAppended_V35`) and `authorizeRefund`
  (`refundedLegAuthorized_V35`) calls; two accepted preimages with one hash are equal or clash.
  The same lemma gives the at-most-once counts (`claimCount_V35`, `appendCount_V35`).
* `RunV35IsPinLegRun`: `append` is one `Step.append`, the marking loop one `Step.authorize`
  per leg it marks, `claimRefund` one `Step.claim`, `requireFlowFinalized` none.
* The witnesses are evaluated by `decide`.
-/

namespace Contracts.FlowCanonicalAtV35

open AttackVectors.FlowCanonical
open Contracts.AtomicFlowManager (Manager LegState)

/-! ## Acceptance -/

theorem AcceptedV35Iff : Properties.AcceptedV35Iff := fun _ =>
  ⟨fun hp => ⟨hp.version, hp.legCap, And.intro hp.sorted hp.lengths⟩,
   fun ⟨hv, hc, hvalid⟩ => ⟨hv, hc, hvalid.1, hvalid.2⟩⟩

theorem AcceptedV35ImpliesValid : Properties.AcceptedV35ImpliesValid :=
  fun _ hp => And.intro hp.sorted hp.lengths

theorem ValidateV35SomeIff : Properties.ValidateV35SomeIff := by
  intro enc p id
  unfold validateV35
  constructor
  · intro h
    split_ifs at h with h1 h2 h3 h4
    exact ⟨⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4⟩,
      Option.some.inj h⟩
  · rintro ⟨⟨hv, hc, hs, hl⟩, rfl⟩
    simp [hv, not_lt.mpr hc, hs, hl]

theorem CheckFlowIdV35Iff : Properties.CheckFlowIdV35Iff :=
  fun enc F => ValidateV35SomeIff enc F.preimage F.flowId

theorem ValidNotSufficientVersionV35 : Properties.ValidNotSufficientVersionV35 :=
  ⟨wWrongVersionV35, And.intro (by decide) (by decide), by decide,
    fun h => absurd h.version (by decide), fun _ => rfl⟩

theorem ValidNotSufficientLegCapV35 : Properties.ValidNotSufficientLegCapV35 :=
  ⟨wOversizedV35, And.intro (by decide) (by decide), by decide, by decide,
    fun h => absurd h.legCap (by decide), fun _ => rfl⟩

/-! ## The cap -/

theorem TooManyLegsRejectedV35 : Properties.TooManyLegsRejectedV35 := by
  intro enc p hp
  unfold validateV35
  split_ifs <;> rfl

theorem TooManyLegsRevertsEveryEntryPointV35 : Properties.TooManyLegsRevertsEveryEntryPointV35 := by
  intro enc chainId M p hp h id e k
  have hv := TooManyLegsRejectedV35 enc p hp
  refine ⟨?_, ?_, ?_⟩
  · simp [stepV35, appendV35, hv]
  · simp [stepV35, requireFinalizedV35, hv]
  · simp [stepV35, authorizeRefundV35, hv]

/-! ## The `FlowCanonical` canonicity results, over v35's acceptance -/

theorem AcceptedV35NoDuplicateLeg : Properties.AcceptedV35NoDuplicateLeg :=
  fun _ hp _ _ hij => AttackVectors.FlowCanonical.no_duplicate_leg hp.sorted hij

theorem AcceptedV35UniquePerLegSet : Properties.AcceptedV35UniquePerLegSet :=
  fun _ _ hp hq hperm => AttackVectors.FlowCanonical.ascending_unique hperm hp.sorted hq.sorted

theorem AcceptedV35PairingFunctional : Properties.AcceptedV35PairingFunctional :=
  fun p hp => AttackVectors.FlowCanonical.valid_pairing_functional (f := p.arrays)
    (And.intro hp.sorted hp.lengths)

/-! ## One call, one leg -/

/-- `Manager.set`, read back. -/
lemma set_legState_V35 (M : Manager) (f b f' b' : UInt256) (s : LegState) :
    (M.set f b s).legState f' b' = if f' = f ∧ b' = b then s else M.legState f' b' := rfl

/-- The marking loop of `authorizeRefund`, leg by leg: leg `(id, h)` ends `Revertable` if it is
under the presented flow id, listed, and was `Committed`; otherwise it is unchanged. -/
lemma markRevertableV35_legState (id₀ : UInt256) (legs : List UInt256) :
    ∀ (M : Manager) (id h : UInt256), (markRevertableV35 id₀ M legs).legState id h =
      if id = id₀ ∧ h ∈ legs ∧ M.legState id₀ h = .Committed then .Revertable
      else M.legState id h := by
  induction legs with
  | nil => intro M id h; simp [markRevertableV35]
  | cons a rest ih =>
    intro M id h
    show (markRevertableV35 id₀
      (if M.legState id₀ a = .Committed then M.set id₀ a .Revertable else M) rest).legState id h = _
    rw [ih]
    by_cases ha : M.legState id₀ a = .Committed
    · simp only [ha, ↓reduceIte, set_legState_V35, List.mem_cons]
      by_cases hid : id = id₀ <;> by_cases hh : h = a <;> simp_all
    · simp only [ha, ↓reduceIte, List.mem_cons]
      by_cases hid : id = id₀ <;> by_cases hh : h = a <;> simp_all

/-- The leg `append` writes is declared, with this chain as its source, in its preimage. -/
lemma mem_zip_of_legIndex_V35 {p : PreimageV35} {h chainId : UInt256}
    (hidx : legIndexV35 p h ≠ p.legBundleHashes.length)
    (hsrc : p.legSourceChainIds[legIndexV35 p h]? = some chainId) :
    (h, chainId) ∈ p.legBundleHashes.zip p.legSourceChainIds := by
  have hmem : h ∈ p.legBundleHashes := by
    by_contra hn
    exact hidx (List.idxOf_eq_length_iff.mpr hn)
  have hlt : legIndexV35 p h < p.legBundleHashes.length := List.idxOf_lt_length_iff.mpr hmem
  have hget : p.legBundleHashes[legIndexV35 p h] = h := List.getElem_idxOf hlt
  have hz : (p.legBundleHashes.zip p.legSourceChainIds)[legIndexV35 p h]? = some (h, chainId) := by
    rw [List.getElem?_zip_eq_some]
    exact ⟨by rw [List.getElem?_eq_getElem hlt, hget], hsrc⟩
  exact List.mem_of_getElem? hz

/-- **ONE CALL, ONE LEG.** A successful call leaves leg `(id, h)` as it was, or it is the
`append` of `h` under a preimage that validates to `id` and declares `h` on this chain
(`Unset → Committed`), or an `authorizeRefund` presenting a flow with id `id` that passes
`_checkFlowId` and lists `h` (`Committed → Revertable`), or the `claimRefund` of `(id, h)`
(`Revertable → Reverted`). -/
lemma stepV35_legState_V35 {enc : PreimageHashV35} {chainId : UInt256} {M M' : Manager}
    {c : CallV35} (hs : stepV35 enc chainId M c = some M') (id h : UInt256) :
    M'.legState id h = M.legState id h ∨
    (∃ p, c = .append h p ∧ validateV35 enc p = some id ∧
        (h, chainId) ∈ p.legBundleHashes.zip p.legSourceChainIds ∧
        M.legState id h = .Unset ∧ M'.legState id h = .Committed) ∨
    (∃ F k, c = .authorizeRefund F k ∧ validateV35 enc F.preimage = some F.flowId ∧
        F.flowId = id ∧ h ∈ F.preimage.legBundleHashes ∧
        M.legState id h = .Committed ∧ M'.legState id h = .Revertable) ∨
    (c = .claimRefund id h ∧ M.legState id h = .Revertable ∧ M'.legState id h = .Reverted) := by
  cases c with
  | append h₀ p =>
    simp only [stepV35, appendV35] at hs
    split at hs
    · cases hs
    · rename_i id₀ hv
      split_ifs at hs with h1 h2 h3
      cases hs
      rw [set_legState_V35]
      by_cases hk : id = id₀ ∧ h = h₀
      · obtain ⟨rfl, rfl⟩ := hk
        refine Or.inr (Or.inl ⟨p, rfl, hv, mem_zip_of_legIndex_V35 h1 (not_not.mp h2),
          not_not.mp h3, by simp⟩)
      · exact Or.inl (by simp [hk])
  | requireFinalized e F =>
    simp only [stepV35, requireFinalizedV35] at hs
    split_ifs at hs
    cases hs
    exact Or.inl rfl
  | authorizeRefund F k =>
    simp only [stepV35, authorizeRefundV35] at hs
    split_ifs at hs with h1
    cases hs
    rw [markRevertableV35_legState]
    by_cases hk : id = F.flowId ∧ h ∈ F.preimage.legBundleHashes ∧
        M.legState F.flowId h = .Committed
    · obtain ⟨rfl, hh, hc⟩ := hk
      refine Or.inr (Or.inr (Or.inl ⟨F, k, rfl, h1.1, rfl, hh, hc, ?_⟩))
      simp [hh, hc]
    · exact Or.inl (by simp only [hk, ↓reduceIte])
  | claimRefund id₀ h₀ =>
    simp only [stepV35, claimRefundV35] at hs
    split_ifs at hs with h1
    cases hs
    rw [set_legState_V35]
    by_cases hk : id = id₀ ∧ h = h₀
    · obtain ⟨rfl, rfl⟩ := hk
      exact Or.inr (Or.inr (Or.inr ⟨rfl, h1, by simp⟩))
    · exact Or.inl (by simp [hk])

lemma runV35_cons_eq_some_V35 {enc : PreimageHashV35} {chainId : UInt256} {M M' : Manager}
    {c : CallV35} {cs : List CallV35} :
    runV35 enc chainId M (c :: cs) = some M' ↔
      ∃ M₁, stepV35 enc chainId M c = some M₁ ∧ runV35 enc chainId M₁ cs = some M' := by
  simp [runV35, Option.bind_eq_some_iff]

/-! ## `append`, exactly -/

/-- For an accepted preimage, a declared leg passes `append`'s leg search and its source-chain
check: the bundle hashes are distinct, so the search finds the declaring position. -/
lemma legIndex_source_of_mem_zip_V35 {p : PreimageV35} {h c : UInt256} (hacc : AcceptedV35 p)
    (hz : (h, c) ∈ p.legBundleHashes.zip p.legSourceChainIds) :
    legIndexV35 p h ≠ p.legBundleHashes.length ∧
      p.legSourceChainIds[legIndexV35 p h]? = some c := by
  obtain ⟨i, hi, hzi⟩ := List.mem_iff_getElem.mp hz
  rw [List.getElem_zip] at hzi
  simp only [Prod.mk.injEq] at hzi
  obtain ⟨hl, hs⟩ := hzi
  have hlen := hi
  rw [List.length_zip] at hlen
  have hi1 : i < p.legBundleHashes.length := lt_of_lt_of_le hlen (min_le_left _ _)
  have hi2 : i < p.legSourceChainIds.length := lt_of_lt_of_le hlen (min_le_right _ _)
  have hnd : p.legBundleHashes.Nodup := AttackVectors.FlowCanonical.ascending_nodup hacc.sorted
  have hidx : legIndexV35 p h = i := by
    unfold legIndexV35
    rw [← hl]
    exact List.Nodup.idxOf_getElem hnd i hi1
  refine ⟨by rw [hidx]; exact Nat.ne_of_lt hi1, ?_⟩
  rw [hidx, List.getElem?_eq_getElem hi2, hs]

theorem AppendV35SomeIff : Properties.AppendV35SomeIff := by
  intro enc chainId M M' h p
  constructor
  · intro hs
    unfold appendV35 at hs
    split at hs
    · cases hs
    · rename_i id hv
      obtain ⟨hacc, henc⟩ := (ValidateV35SomeIff enc p id).mp hv
      subst henc
      split_ifs at hs with h1 h2 h3
      cases hs
      exact ⟨hacc, mem_zip_of_legIndex_V35 h1 (not_not.mp h2), not_not.mp h3, rfl⟩
  · rintro ⟨hacc, hz, hU, rfl⟩
    obtain ⟨h1, h2⟩ := legIndex_source_of_mem_zip_V35 hacc hz
    have hv : validateV35 enc p = some (enc p) :=
      (ValidateV35SomeIff enc p (enc p)).mpr ⟨hacc, rfl⟩
    unfold appendV35
    rw [hv]
    simp [h1, h2, hU]

/-! ## Runs are runs of the `Model` leg machine -/

lemma reachTrans_V35 {M N P : Manager} (h₁ : Contracts.AtomicFlowManager.Reach M N)
    (h₂ : Contracts.AtomicFlowManager.Reach N P) : Contracts.AtomicFlowManager.Reach M P := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact .tail ih hs

/-- The marking loop is a sequence of `authorize` steps. -/
lemma markRevertableV35_reach (id : UInt256) (legs : List UInt256) :
    ∀ M : Manager, Contracts.AtomicFlowManager.Reach M (markRevertableV35 id M legs) := by
  induction legs with
  | nil => intro M; exact .refl
  | cons a rest ih =>
    intro M
    show Contracts.AtomicFlowManager.Reach M (markRevertableV35 id
      (if M.legState id a = .Committed then M.set id a .Revertable else M) rest)
    by_cases ha : M.legState id a = .Committed
    · simp only [ha, ↓reduceIte]
      exact reachTrans_V35 (.tail .refl (.authorize ha)) (ih _)
    · simp only [ha, ↓reduceIte]
      exact ih M

/-- One successful call is a run of the `Model` leg machine: `append` one `Step.append`,
`authorizeRefund` one `Step.authorize` per leg it marks, `claimRefund` one `Step.claim`,
`requireFlowFinalized` none. -/
lemma stepV35_reach_V35 {enc : PreimageHashV35} {chainId : UInt256} {M M' : Manager}
    {c : CallV35} (hs : stepV35 enc chainId M c = some M') :
    Contracts.AtomicFlowManager.Reach M M' := by
  cases c with
  | append h p =>
    simp only [stepV35, appendV35] at hs
    split at hs
    · cases hs
    · split_ifs at hs with h1 h2 h3
      cases hs
      exact .tail .refl (.append (not_not.mp h3))
  | requireFinalized e F =>
    simp only [stepV35, requireFinalizedV35] at hs
    split_ifs at hs
    cases hs
    exact .refl
  | authorizeRefund F k =>
    simp only [stepV35, authorizeRefundV35] at hs
    split_ifs at hs
    cases hs
    exact markRevertableV35_reach _ _ _
  | claimRefund id h =>
    simp only [stepV35, claimRefundV35] at hs
    split_ifs at hs with h1
    cases hs
    exact .tail .refl (.claim h1)

theorem RunV35IsPinLegRun : Properties.RunV35IsPinLegRun := by
  intro enc chainId M₀ M calls
  induction calls generalizing M₀ with
  | nil =>
    intro hrun
    simp only [runV35, Option.some.injEq] at hrun
    subst hrun
    exact .refl
  | cons c cs ih =>
    intro hrun
    obtain ⟨M₁, hs, hr⟩ := runV35_cons_eq_some_V35.mp hrun
    exact reachTrans_V35 (stepV35_reach_V35 hs) (ih M₁ hr)

theorem RunV35LegRankMonotone : Properties.RunV35LegRankMonotone :=
  fun enc chainId M₀ M calls hrun id h =>
    Contracts.AtomicFlowManager.reach_rank_mono (RunV35IsPinLegRun enc chainId M₀ M calls hrun) id h

/-! ## At most once per leg -/

/-- A successful call leaves a `Reverted` leg `Reverted`. -/
lemma stepV35_reverted_V35 {enc : PreimageHashV35} {chainId : UInt256} {M M' : Manager}
    {c : CallV35} (hs : stepV35 enc chainId M c = some M') {id h : UInt256}
    (hr : M.legState id h = .Reverted) : M'.legState id h = .Reverted := by
  rcases stepV35_legState_V35 hs id h with heq | ⟨_, _, _, _, hU, _⟩ |
      ⟨_, _, _, _, _, _, hC, _⟩ | ⟨_, hR, _⟩
  · rw [heq, hr]
  · rw [hr] at hU; cases hU
  · rw [hr] at hC; cases hC
  · rw [hr] at hR; cases hR

/-- A successful call never takes a leg back to `Unset`. -/
lemma stepV35_written_V35 {enc : PreimageHashV35} {chainId : UInt256} {M M' : Manager}
    {c : CallV35} (hs : stepV35 enc chainId M c = some M') {id h : UInt256}
    (hw : M.legState id h ≠ .Unset) : M'.legState id h ≠ .Unset := by
  rcases stepV35_legState_V35 hs id h with heq | ⟨_, _, _, _, hU, _⟩ |
      ⟨_, _, _, _, _, _, _, hRv⟩ | ⟨_, _, hRd⟩
  · rw [heq]; exact hw
  · exact absurd hU hw
  · rw [hRv]; decide
  · rw [hRd]; decide

lemma claimCount_V35 {enc : PreimageHashV35} {chainId : UInt256} (id h : UInt256) :
    ∀ (calls : List CallV35) (M₀ M : Manager), runV35 enc chainId M₀ calls = some M →
      calls.count (.claimRefund id h) ≤ (if M₀.legState id h = .Reverted then 0 else 1) := by
  intro calls
  induction calls with
  | nil => intro M₀ M _; simp
  | cons c cs ih =>
    intro M₀ M hrun
    obtain ⟨M₁, hs, hr⟩ := runV35_cons_eq_some_V35.mp hrun
    have ih' := ih M₁ M hr
    rw [List.count_cons]
    by_cases hc : c = .claimRefund id h
    · subst hc
      simp only [stepV35, claimRefundV35] at hs
      split_ifs at hs with h1
      cases hs
      have hM₁ : (M₀.set id h .Reverted).legState id h = .Reverted := by
        rw [set_legState_V35]; simp
      simp only [hM₁, ↓reduceIte, nonpos_iff_eq_zero] at ih'
      simp [h1, ih']
    · have hbeq : (c == .claimRefund id h) = false := by simpa using hc
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, add_zero]
      by_cases hR : M₀.legState id h = .Reverted
      · have hR₁ := stepV35_reverted_V35 hs hR
        simpa [hR, hR₁] using ih'
      · simp only [hR, ↓reduceIte]
        split_ifs at ih' <;> omega

lemma appendCount_V35 {enc : PreimageHashV35} {chainId : UInt256} (id h : UInt256) :
    ∀ (calls : List CallV35) (M₀ M : Manager), runV35 enc chainId M₀ calls = some M →
      calls.countP (CallV35.appendsLegV35 enc id h) ≤
        (if M₀.legState id h = .Unset then 1 else 0) := by
  intro calls
  induction calls with
  | nil => intro M₀ M _; simp
  | cons c cs ih =>
    intro M₀ M hrun
    obtain ⟨M₁, hs, hr⟩ := runV35_cons_eq_some_V35.mp hrun
    have ih' := ih M₁ M hr
    rw [List.countP_cons]
    cases hcall : CallV35.appendsLegV35 enc id h c with
    | true =>
      obtain ⟨p, rfl, hpid⟩ : ∃ p, c = .append h p ∧ enc p = id := by
        cases c with
        | append h' p =>
          simp only [CallV35.appendsLegV35, decide_eq_true_eq] at hcall
          exact ⟨p, by rw [hcall.1], hcall.2⟩
        | _ => simp [CallV35.appendsLegV35] at hcall
      obtain ⟨-, -, hU, rfl⟩ := (AppendV35SomeIff enc chainId M₀ M₁ h p).mp hs
      subst hpid
      have hC : (M₀.set (enc p) h .Committed).legState (enc p) h ≠ .Unset := by
        rw [set_legState_V35]; simp
      simp only [hC, ↓reduceIte, nonpos_iff_eq_zero] at ih'
      simp [hU, ih']
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      by_cases hU : M₀.legState id h = .Unset
      · simp only [hU, ↓reduceIte]
        split_ifs at ih' <;> omega
      · have hU₁ := stepV35_written_V35 hs hU
        simpa [hU, hU₁] using ih'

theorem RunV35ClaimsEachLegAtMostOnce : Properties.RunV35ClaimsEachLegAtMostOnce := by
  intro enc chainId M₀ M calls hrun id h
  have hb := claimCount_V35 id h calls M₀ M hrun
  refine ⟨?_, fun hR => ?_⟩
  · split_ifs at hb <;> omega
  · simpa [hR] using hb

theorem RunV35AppendsEachLegAtMostOnce : Properties.RunV35AppendsEachLegAtMostOnce := by
  intro enc chainId M₀ M calls hrun id h
  have hb := appendCount_V35 id h calls M₀ M hrun
  refine ⟨?_, fun hU => ?_⟩
  · split_ifs at hb <;> omega
  · simpa [hU] using hb

/-! ## Over runs -/

/-- Every leg that a run takes out of `Unset` was appended in the run, under a preimage that
validates to its flow id and declares it on this chain. -/
lemma writtenLegAppended_V35 {enc : PreimageHashV35} {chainId : UInt256} :
    ∀ (calls : List CallV35) (M₀ M : Manager), runV35 enc chainId M₀ calls = some M →
      ∀ id h : UInt256, M₀.legState id h = .Unset → M.legState id h ≠ .Unset →
        ∃ p, CallV35.append h p ∈ calls ∧ validateV35 enc p = some id ∧
          (h, chainId) ∈ p.legBundleHashes.zip p.legSourceChainIds := by
  intro calls
  induction calls with
  | nil =>
    intro M₀ M hrun id h h0 h1
    simp only [runV35, Option.some.injEq] at hrun
    subst hrun
    exact absurd h0 h1
  | cons c cs ih =>
    intro M₀ M hrun id h h0 h1
    obtain ⟨M₁, hs, hr⟩ := runV35_cons_eq_some_V35.mp hrun
    by_cases hM₁ : M₁.legState id h = .Unset
    · obtain ⟨p, hp, hv, hz⟩ := ih M₁ M hr id h hM₁ h1
      exact ⟨p, List.mem_cons_of_mem _ hp, hv, hz⟩
    · rcases stepV35_legState_V35 hs id h with heq | ⟨p, rfl, hv, hz, -, -⟩ |
          ⟨F, k, -, -, -, -, hc, -⟩ | ⟨-, hc, -⟩
      · exact absurd (heq.trans h0) hM₁
      · exact ⟨p, List.mem_cons_self .., hv, hz⟩
      · rw [h0] at hc; cases hc
      · rw [h0] at hc; cases hc

/-- Every leg that a run takes to `Revertable` or `Reverted` from below was marked in the run by
an `authorizeRefund` under its flow id that passes `_checkFlowId` and lists it. -/
lemma refundedLegAuthorized_V35 {enc : PreimageHashV35} {chainId : UInt256} :
    ∀ (calls : List CallV35) (M₀ M : Manager), runV35 enc chainId M₀ calls = some M →
      ∀ id h : UInt256, (M.legState id h = .Revertable ∨ M.legState id h = .Reverted) →
        (M₀.legState id h = .Revertable ∨ M₀.legState id h = .Reverted) ∨
        ∃ F k, CallV35.authorizeRefund F k ∈ calls ∧
          validateV35 enc F.preimage = some F.flowId ∧ F.flowId = id ∧
          h ∈ F.preimage.legBundleHashes := by
  intro calls
  induction calls with
  | nil =>
    intro M₀ M hrun id h hend
    simp only [runV35, Option.some.injEq] at hrun
    subst hrun
    exact Or.inl hend
  | cons c cs ih =>
    intro M₀ M hrun id h hend
    obtain ⟨M₁, hs, hr⟩ := runV35_cons_eq_some_V35.mp hrun
    rcases ih M₁ M hr id h hend with hM₁ | ⟨F, k, hF, hv, hid, hh⟩
    · rcases stepV35_legState_V35 hs id h with heq | ⟨p, -, -, -, -, hc⟩ |
          ⟨F, k, rfl, hv, hid, hh, -, -⟩ | ⟨-, hc, -⟩
      · exact Or.inl (heq ▸ hM₁)
      · rw [hc] at hM₁; rcases hM₁ with h' | h' <;> cases h'
      · exact Or.inr ⟨F, k, List.mem_cons_self .., hv, hid, hh⟩
      · exact Or.inl (Or.inl hc)
    · exact Or.inr ⟨F, k, List.mem_cons_of_mem _ hF, hv, hid, hh⟩

theorem WrittenLegAppendedUnderAcceptedPreimageV35 :
    Properties.WrittenLegAppendedUnderAcceptedPreimageV35 := by
  intro enc chainId M₀ M calls hrun id h h0 h1
  obtain ⟨p, hp, hv, hz⟩ := writtenLegAppended_V35 calls M₀ M hrun id h h0 h1
  obtain ⟨hacc, henc⟩ := (ValidateV35SomeIff enc p id).mp hv
  exact ⟨p, hp, hacc, henc, hz⟩

theorem RejectedPreimageLegsUntouchedOrLoggedClashV35 :
    Properties.RejectedPreimageLegsUntouchedOrLoggedClashV35 := by
  intro enc chainId M₀ M calls p hrej hrun h h0
  by_cases hU : M.legState (enc p) h = .Unset
  · exact Or.inl hU
  · right
    obtain ⟨q, hq, hv, -⟩ := writtenLegAppended_V35 calls M₀ M hrun (enc p) h h0 hU
    obtain ⟨hqacc, hqenc⟩ := (ValidateV35SomeIff enc q (enc p)).mp hv
    refine ⟨q, hq, hqacc, fun hpq => ?_, hqenc.symm⟩
    subst hpq
    exact hrej hqacc

theorem OversizedFlowCommitsNoLegOrLoggedClashV35 :
    Properties.OversizedFlowCommitsNoLegOrLoggedClashV35 := by
  intro enc chainId M₀ M calls p hp hrun h h0
  exact RejectedPreimageLegsUntouchedOrLoggedClashV35 enc chainId M₀ M calls p
    (fun ha => absurd ha.legCap (not_le.mpr hp)) hrun h h0

theorem RefundedLegSameFlowOrLoggedClashV35 : Properties.RefundedLegSameFlowOrLoggedClashV35 := by
  intro enc chainId M₀ M calls hrun id h h0 hend
  have hne : M.legState id h ≠ .Unset := by
    rcases hend with h' | h' <;> rw [h'] <;> decide
  obtain ⟨p, hp, hpv, -⟩ := writtenLegAppended_V35 calls M₀ M hrun id h h0 hne
  rcases refundedLegAuthorized_V35 calls M₀ M hrun id h hend with h0' | ⟨F, k, hF, hFv, hFid, hFh⟩
  · rcases h0' with h0' | h0' <;> rw [h0] at h0' <;> cases h0'
  · obtain ⟨hpacc, hpenc⟩ := (ValidateV35SomeIff enc p id).mp hpv
    obtain ⟨-, hFenc⟩ := (ValidateV35SomeIff enc F.preimage F.flowId).mp hFv
    refine ⟨p, F, k, hp, hF, hpacc, hpenc, hFv, hFid, hFh, ?_⟩
    by_cases hpF : F.preimage = p
    · exact Or.inl hpF
    · exact Or.inr ⟨fun hpF' => hpF hpF'.symm, by rw [hpenc, hFenc, hFid]⟩

/-! ## One check, unfolded -/

theorem SameFlowIdSamePreimageOrClashV35 : Properties.SameFlowIdSamePreimageOrClashV35 := by
  intro enc F G hF hG hid
  by_cases hp : F.preimage = G.preimage
  · left
    cases F
    cases G
    simp_all
  · right
    obtain ⟨-, hFe⟩ := (CheckFlowIdV35Iff enc F).mp hF
    obtain ⟨-, hGe⟩ := (CheckFlowIdV35Iff enc G).mp hG
    exact ⟨hp, by rw [hFe, hGe, hid]⟩

theorem PreimageClashNotForcedV35 : Properties.PreimageClashNotForcedV35 := by
  intro p q hpq
  refine ⟨honestPreimageHashV35 p 0, fun hclash => ?_⟩
  have h := hclash.2
  simp only [honestPreimageHashV35, Ne.symm hpq, ↓reduceIte] at h
  exact absurd h (by decide)

/-! ## Witnesses -/

theorem AcceptanceWitnessV35 : Properties.AcceptanceWitnessV35 :=
  ⟨⟨by decide, by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩,
    by decide, by decide, List.Perm.refl _, by decide, by decide⟩

theorem SameFlowIdClashFiresV35 : Properties.SameFlowIdClashFiresV35 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem TooManyLegsWitnessV35 : Properties.TooManyLegsWitnessV35 :=
  ⟨And.intro (by decide) (by decide), by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem LegWritesWitnessV35 : Properties.LegWritesWitnessV35 :=
  ⟨by decide, fun h => absurd h.version (by decide), by decide, by decide⟩

theorem OversizedFlowWitnessV35 : Properties.OversizedFlowWitnessV35 :=
  ⟨fun h => absurd h.legCap (by decide), ⟨by decide, by decide, by decide, by decide⟩, by decide,
    by decide, by decide, ⟨by decide, by decide⟩, by decide⟩

theorem SecondClaimOrAppendRevertsWitnessV35 : Properties.SecondClaimOrAppendRevertsWitnessV35 :=
  ⟨by decide, by decide⟩

theorem RefundUnderOtherPreimageWitnessV35 : Properties.RefundUnderOtherPreimageWitnessV35 :=
  ⟨by decide, by decide, ⟨by decide, by decide⟩⟩

end Contracts.FlowCanonicalAtV35
