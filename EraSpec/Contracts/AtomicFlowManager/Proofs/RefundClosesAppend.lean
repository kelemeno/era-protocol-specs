import EraSpec.Contracts.AtomicFlowManager.Properties.RefundClosesAppend

/-!
# Proofs: an authorized refund closes `append` for its flow, on that chain

Proofs of `EraSpec.Contracts.AtomicFlowManager.Properties.RefundClosesAppend`.

The argument is four one-step facts and two run-level invariants.  A successful
`authorizeRefund` of preimage `p` under the deployed checks reads a stored root of `p`'s
settlement layer with timestamp above `p.deadline` (`timeoutAbsence_deployed`).
`LatestBoundsStored` turns that into `p.deadline < latestInteropRootTimestamp(sl)`
(`after_authorization`).  No call lowers a tracked timestamp (`execCall_latest_ge`), and
`L1_CHAIN_ID` never changes once set (`execCall_l1`).  A successful `append` of `q` passes
`q.deadline ≥ latestInteropRootTimestamp(q.sl)` and `q.sl = L1_CHAIN_ID` (`appendCall_ok`).
The leg-level results use one frame lemma (`execCall_legState`): a call changes a leg only as
`append`, `authorizeRefund` or `claimRefund` of that leg.  The witness and the countermodels are
concrete runs, evaluated by `decide` through `runCalls`.
-/

namespace Contracts.AtomicFlowManager.RefundClosesAppend

/-! ## Runs as a function -/

theorem ChainRunIffRunCalls : Properties.ChainRunIffRunCalls := by
  intro τ P K S S' cs
  induction cs generalizing S with
  | nil =>
    constructor
    · intro h; cases h; rfl
    · intro h
      simp only [runCalls, Option.some.injEq] at h
      subst h; exact .nil
  | cons c cs ih =>
    constructor
    · intro h
      cases h with
      | cons hc hr => simp only [runCalls, hc]; exact (ih _).1 hr
    · intro h
      simp only [runCalls] at h
      cases hc : execCall P K S c with
      | none => rw [hc] at h; cases h
      | some S₁ => rw [hc] at h; exact .cons hc ((ih _).2 h)

lemma chainRun_append {τ : Type} {P : ChainParams τ} {K : Checks} {S S₁ S₂ : ChainState τ}
    {cs₁ cs₂ : List ChainCall} (h₁ : ChainRun P K S cs₁ S₁) (h₂ : ChainRun P K S₁ cs₂ S₂) :
    ChainRun P K S (cs₁ ++ cs₂) S₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons hc _ ih => exact .cons hc (ih h₂)

/-! ## The manager's leg map -/

lemma legState_set (M : Manager) (f b f' b' : Word) (s : LegState) :
    (M.set f b s).legState f' b' = if f' = f ∧ b' = b then s else M.legState f' b' :=
  rfl

/-- The marking loop, in closed form: exactly the flow's `Committed` legs become
`Revertable`. -/
lemma markCommittedRevertable_legState (M : Manager) (flowId : Word) (hs : List Word)
    (f b : Word) :
    (markCommittedRevertable M flowId hs).legState f b =
      if f = flowId ∧ b ∈ hs ∧ M.legState f b = .Committed then .Revertable
      else M.legState f b := by
  induction hs generalizing M with
  | nil => simp [markCommittedRevertable]
  | cons h hs ih =>
    simp only [markCommittedRevertable]
    rw [ih]
    by_cases hfb : f = flowId ∧ b = h
    · obtain ⟨rfl, rfl⟩ := hfb
      by_cases hc : M.legState f b = .Committed
      · simp [hc, legState_set]
      · simp [hc]
    · have hM : (if M.legState flowId h = .Committed then M.set flowId h .Revertable else M).legState
          f b = M.legState f b := by
        split_ifs
        · simp [legState_set, hfb]
        · rfl
      rw [hM]
      by_cases hf : f = flowId
      · have hb : b ≠ h := fun hb => hfb ⟨hf, hb⟩
        simp [hf, hb]
      · simp [hf]

/-! ## The root storage -/

lemma write_latest_ge {K : Checks} (hK : K.latestKeepsMax = true) (R : RootStore)
    (chainId blk ts root c : ℕ) :
    R.latestInteropRootTimestamp c ≤ (R.write K chainId blk ts root).latestInteropRootTimestamp c := by
  simp only [RootStore.write, hK, ↓reduceIte]
  split_ifs with h1 h2 <;> subst_vars <;> omega

lemma write_bound {K : Checks} (hK : K.latestKeepsMax = true) {R : RootStore}
    (hR : LatestBoundsStored R) (chainId blk ts root : ℕ) :
    LatestBoundsStored (R.write K chainId blk ts root) := by
  intro c b
  simp only [RootStore.write, hK, ↓reduceIte]
  by_cases hc : c = chainId
  · subst hc
    by_cases hb : b = blk
    · subst hb; simp only [and_self, ↓reduceIte]; split_ifs <;> omega
    · simp only [hb, and_false, ↓reduceIte]
      have := hR c b
      split_ifs <;> omega
  · simp only [hc, false_and, ↓reduceIte]
    exact hR c b

lemma addInteropRoot_some {K : Checks} {R R' : RootStore} {chainId blk ts : ℕ} {sides : List ℕ}
    (h : addInteropRoot K R chainId blk ts sides = some R') :
    R' = R.write K chainId blk ts (sides.headD 0) := by
  unfold addInteropRoot at h
  split_ifs at h
  exact (Option.some.inj h).symm

lemma addInteropRoots_latest_ge {K : Checks} (hK : K.latestKeepsMax = true) :
    ∀ (rs : List ImportedRoot) (R R' : RootStore), addInteropRoots K R rs = some R' →
      ∀ c, R.latestInteropRootTimestamp c ≤ R'.latestInteropRootTimestamp c
  | [], R, R', h, c => by
    simp only [addInteropRoots, Option.some.injEq] at h; subst h; exact le_rfl
  | r :: rs, R, R', h, c => by
    simp only [addInteropRoots] at h
    split at h
    · cases h
    · rename_i R₁ h₁
      rw [addInteropRoot_some h₁] at h
      exact le_trans (write_latest_ge hK R _ _ _ _ c) (addInteropRoots_latest_ge hK rs _ _ h c)

lemma addInteropRoots_bound {K : Checks} (hK : K.latestKeepsMax = true) :
    ∀ (rs : List ImportedRoot) (R R' : RootStore), addInteropRoots K R rs = some R' →
      LatestBoundsStored R → LatestBoundsStored R'
  | [], R, R', h, hR => by
    simp only [addInteropRoots, Option.some.injEq] at h; subst h; exact hR
  | r :: rs, R, R', h, hR => by
    simp only [addInteropRoots] at h
    split at h
    · cases h
    · rename_i R₁ h₁
      rw [addInteropRoot_some h₁] at h
      exact addInteropRoots_bound hK rs _ _ h (write_bound hK hR _ _ _ _)

/-! ## One call -/

/-- **A SUCCESSFUL `append`.**  Every check passed, and the only writes are the leg and the
tree. -/
lemma appendCall_ok {τ : Type} {P : ChainParams τ} {K : Checks} {S S' : ChainState τ}
    {caller : ℕ} {registered : ℕ → Bool} {b : Word} {idx : ℕ} {q : FlowPreimage}
    (h : appendCall P K S caller registered b idx q = .ok S') :
    caller = P.interopCenter ∧ preimageError? q = none ∧
    q.settlementLayerChainId = S.l1ChainId ∧
    ¬ (K.deadlineGate = true ∧
      q.deadline < S.roots.latestInteropRootTimestamp q.settlementLayerChainId) ∧
    b ∈ q.legBundleHashes ∧
    S.legs.legState (P.flowHash q) b = .Unset ∧
    S'.legs = S.legs.set (P.flowHash q) b .Committed ∧
    S'.l1ChainId = S.l1ChainId ∧ S'.roots = S.roots := by
  unfold appendCall at h
  split at h
  · cases h
  · rename_i hcaller
    split at h
    · cases h
    · rename_i hpe
      split at h
      · cases h
      · rename_i hsl
        split at h
        · cases h
        · rename_i hgate
          split at h
          · cases h
          · rename_i i hi
            split at h
            · cases h
            · split at h
              · cases h
              · split at h
                · cases h
                · rename_i hunset
                  split at h
                  · cases h
                  · rename_i T hT
                    cases h
                    have hmem : b ∈ q.legBundleHashes := by
                      unfold legIndexOf at hi
                      obtain ⟨hlt, hb, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
                      have : q.legBundleHashes[i] = b := by simpa using hb
                      exact this ▸ List.getElem_mem hlt
                    exact ⟨not_not.1 hcaller, hpe, not_not.1 hsl, hgate, hmem, not_not.1 hunset,
                      rfl, rfl, rfl⟩

/-- **A SUCCESSFUL `authorizeRefund`.** -/
lemma authorizeRefundCall_some {τ : Type} {P : ChainParams τ} {K : Checks} {S S' : ChainState τ}
    {peerAllowed : ℕ → Bool} {flowId : Word} {p : FlowPreimage} {i : ℕ} {a : AbsenceProof}
    (h : authorizeRefundCall P K S peerAllowed flowId p i a = some S') :
    preimageError? p = none ∧ P.flowHash p = flowId ∧
    p.settlementLayerChainId = S.l1ChainId ∧
    TimeoutAbsenceVerified P K S.roots a (P.commitValue flowId (p.legBundleHashes.getD i 0))
      p.deadline p.settlementLayerChainId ∧
    S' = { S with legs := markCommittedRevertable S.legs flowId p.legBundleHashes } := by
  unfold authorizeRefundCall at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7
  exact ⟨not_not.1 h1, not_not.1 h2, not_not.1 h3, h7, (Option.some.inj h).symm⟩

/-- Under the deployed checks, a verified absence proof reads a root of the expected settlement
layer whose timestamp is past the deadline. -/
lemma timeoutAbsence_deployed {τ : Type} {P : ChainParams τ} {R : RootStore} {a : AbsenceProof}
    {v : Word} {d sl : ℕ} (h : TimeoutAbsenceVerified P deployed R a v d sl) :
    a.settlementLayerChainId = sl ∧
      d < (R.storedInteropRoots a.settlementLayerChainId a.settlementLayerBatchNumber).timestamp := by
  obtain ⟨-, hsl, -, hlt, -, -⟩ := h
  exact ⟨hsl rfl, by simpa [deployed] using hlt⟩

lemma claimRefundCall_some {τ : Type} {S S' : ChainState τ} {flowId b : Word} {ok : Bool}
    (h : claimRefundCall S flowId b ok = some S') :
    S.legs.legState flowId b = .Revertable ∧ S' = { S with legs := S.legs.set flowId b .Reverted } := by
  unfold claimRefundCall at h
  split_ifs at h with h1 h2
  exact ⟨not_not.1 h1, (Option.some.inj h).symm⟩

lemma initL2Call_some {τ : Type} {P : ChainParams τ} {S S' : ChainState τ} {caller l1 : ℕ}
    (h : initL2Call P S caller l1 = some S') :
    S.l1ChainId = 0 ∧ S' = { S with l1ChainId := l1 } := by
  unfold initL2Call at h
  split_ifs at h with h1 h2 h3
  exact ⟨not_not.1 h2, (Option.some.inj h).symm⟩

/-- **THE ROOT STORAGE CHANGES ONLY BY AN IMPORT.** -/
lemma execCall_roots {τ : Type} {P : ChainParams τ} {K : Checks} {S S' : ChainState τ}
    {c : ChainCall} (h : execCall P K S c = some S') :
    S'.roots = S.roots ∨
    (∃ r : ImportedRoot, addInteropRoot K S.roots r.chainId r.blockOrBatchNumber r.timestamp
      r.sides = some S'.roots) ∨
    (∃ rs : List ImportedRoot, addInteropRoots K S.roots rs = some S'.roots) := by
  cases c with
  | initL2 caller l1 =>
    obtain ⟨-, rfl⟩ := initL2Call_some h; exact .inl rfl
  | append caller registered b idx q =>
    simp only [execCall] at h
    cases hA : appendCall P K S caller registered b idx q with
    | error e => rw [hA] at h; cases h
    | ok S₁ =>
      rw [hA] at h
      cases h
      exact .inl (appendCall_ok hA).2.2.2.2.2.2.2.2
  | authorizeRefund peer flowId p i a =>
    obtain ⟨-, -, -, -, rfl⟩ := authorizeRefundCall_some h; exact .inl rfl
  | claimRefund flowId b ok =>
    obtain ⟨-, rfl⟩ := claimRefundCall_some h; exact .inl rfl
  | requireFlowFinalized passes =>
    simp only [execCall] at h
    split_ifs at h
    cases h; exact .inl rfl
  | addSingleInteropRoot caller r =>
    simp only [execCall, addSingleInteropRootCall] at h
    split_ifs at h
    obtain ⟨R, hR, rfl⟩ := Option.map_eq_some_iff.1 h
    exact .inr (.inl ⟨r, hR⟩)
  | addInteropRootsInBatch caller rs =>
    simp only [execCall, addInteropRootsInBatchCall] at h
    split_ifs at h
    obtain ⟨R, hR, rfl⟩ := Option.map_eq_some_iff.1 h
    exact .inr (.inr ⟨rs, hR⟩)

lemma execCall_latest_ge {τ : Type} {P : ChainParams τ} {K : Checks} (hK : K.latestKeepsMax = true)
    {S S' : ChainState τ} {c : ChainCall} (h : execCall P K S c = some S') (x : ℕ) :
    S.roots.latestInteropRootTimestamp x ≤ S'.roots.latestInteropRootTimestamp x := by
  rcases execCall_roots h with h₁ | ⟨r, h₁⟩ | ⟨rs, h₁⟩
  · rw [h₁]
  · rw [addInteropRoot_some h₁]; exact write_latest_ge hK _ _ _ _ _ x
  · exact addInteropRoots_latest_ge hK rs _ _ h₁ x

lemma execCall_bound {τ : Type} {P : ChainParams τ} {K : Checks} (hK : K.latestKeepsMax = true)
    {S S' : ChainState τ} {c : ChainCall} (h : execCall P K S c = some S')
    (hS : LatestBoundsStored S.roots) : LatestBoundsStored S'.roots := by
  rcases execCall_roots h with h₁ | ⟨r, h₁⟩ | ⟨rs, h₁⟩
  · rw [h₁]; exact hS
  · rw [addInteropRoot_some h₁]; exact write_bound hK hS _ _ _ _
  · exact addInteropRoots_bound hK rs _ _ h₁ hS

/-- **`L1_CHAIN_ID` NEVER CHANGES ONCE SET.** -/
lemma execCall_l1 {τ : Type} {P : ChainParams τ} {K : Checks} {S S' : ChainState τ}
    {c : ChainCall} (h : execCall P K S c = some S') (h0 : S.l1ChainId ≠ 0) :
    S'.l1ChainId = S.l1ChainId := by
  cases c with
  | initL2 caller l1 =>
    obtain ⟨h1, -⟩ := initL2Call_some h; exact absurd h1 h0
  | append caller registered b idx q =>
    simp only [execCall] at h
    cases hA : appendCall P K S caller registered b idx q with
    | error e => rw [hA] at h; cases h
    | ok S₁ =>
      rw [hA] at h
      cases h
      exact (appendCall_ok hA).2.2.2.2.2.2.2.1
  | authorizeRefund peer flowId p i a =>
    obtain ⟨-, -, -, -, rfl⟩ := authorizeRefundCall_some h; rfl
  | claimRefund flowId b ok =>
    obtain ⟨-, rfl⟩ := claimRefundCall_some h; rfl
  | requireFlowFinalized passes =>
    simp only [execCall] at h
    split_ifs at h
    cases h; rfl
  | addSingleInteropRoot caller r =>
    simp only [execCall, addSingleInteropRootCall] at h
    split_ifs at h
    obtain ⟨R, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  | addInteropRootsInBatch caller rs =>
    simp only [execCall, addInteropRootsInBatchCall] at h
    split_ifs at h
    obtain ⟨R, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl

/-- **A CALL CHANGES A LEG ONLY BY ITS OWN `append`, `authorizeRefund` OR `claimRefund`.**  Either
leg `(f, b)` is unchanged, or the call is a successful `append` of it (from `Unset` to
`Committed`), an `authorizeRefund` of flow id `f` (from `Committed` to `Revertable`), or a
`claimRefund` of it (from `Revertable` to `Reverted`). -/
lemma execCall_legState {τ : Type} {P : ChainParams τ} {K : Checks} {S S' : ChainState τ}
    {c : ChainCall} (h : execCall P K S c = some S') (f b : Word) :
    S'.legs.legState f b = S.legs.legState f b ∨
    (S.legs.legState f b = .Unset ∧ S'.legs.legState f b = .Committed ∧
      ∃ (q : FlowPreimage) (caller : ℕ) (registered : ℕ → Bool) (idx : ℕ),
        c = .append caller registered b idx q ∧ P.flowHash q = f ∧ b ∈ q.legBundleHashes ∧
        appendCall P K S caller registered b idx q = .ok S') ∨
    (S.legs.legState f b = .Committed ∧ S'.legs.legState f b = .Revertable ∧
      ∃ (peer : ℕ → Bool) (q : FlowPreimage) (i : ℕ) (a : AbsenceProof),
        c = .authorizeRefund peer f q i a) ∨
    (S.legs.legState f b = .Revertable ∧ S'.legs.legState f b = .Reverted ∧
      c.isClaimOf f b = true) := by
  cases c with
  | initL2 caller l1 =>
    obtain ⟨-, rfl⟩ := initL2Call_some h; exact .inl rfl
  | append caller registered b' idx q =>
    simp only [execCall] at h
    cases hA : appendCall P K S caller registered b' idx q with
    | error e => rw [hA] at h; cases h
    | ok S₁ =>
      rw [hA] at h
      cases h
      obtain ⟨-, -, -, -, hmem, hunset, hlegs, -, -⟩ := appendCall_ok hA
      by_cases hfb : f = P.flowHash q ∧ b = b'
      · obtain ⟨rfl, rfl⟩ := hfb
        refine .inr (.inl ⟨hunset, ?_, q, caller, registered, idx, rfl, rfl, hmem, hA⟩)
        rw [hlegs, legState_set]; simp
      · left; rw [hlegs, legState_set, ite_eq_right hfb]
  | authorizeRefund peer flowId q i a =>
    obtain ⟨-, -, -, -, rfl⟩ := authorizeRefundCall_some h
    simp only
    rw [markCommittedRevertable_legState]
    by_cases hc : f = flowId ∧ b ∈ q.legBundleHashes ∧ S.legs.legState f b = .Committed
    · obtain ⟨rfl, hmem, hcom⟩ := hc
      refine .inr (.inr (.inl ⟨hcom, ?_, peer, q, i, a, rfl⟩))
      rw [ite_eq_left ⟨rfl, hmem, hcom⟩]
    · left; rw [ite_eq_right hc]
  | claimRefund flowId b' ok =>
    obtain ⟨hrev, rfl⟩ := claimRefundCall_some h
    simp only
    by_cases hfb : f = flowId ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := hfb
      refine .inr (.inr (.inr ⟨hrev, ?_, ?_⟩))
      · rw [legState_set]; simp
      · simp [ChainCall.isClaimOf]
    · left; rw [legState_set, ite_eq_right hfb]
  | requireFlowFinalized passes =>
    simp only [execCall] at h
    split_ifs at h
    cases h; exact .inl rfl
  | addSingleInteropRoot caller r =>
    simp only [execCall, addSingleInteropRootCall] at h
    split_ifs at h
    obtain ⟨R, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact .inl rfl
  | addInteropRootsInBatch caller rs =>
    simp only [execCall, addInteropRootsInBatchCall] at h
    split_ifs at h
    obtain ⟨R, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact .inl rfl

/-- A successful claim of leg `(f, b)` found it `Revertable` and left it `Reverted`. -/
lemma isClaimOf_exec {τ : Type} {P : ChainParams τ} {K : Checks} {S S' : ChainState τ}
    {c : ChainCall} {f b : Word} (hc : c.isClaimOf f b = true)
    (h : execCall P K S c = some S') :
    S.legs.legState f b = .Revertable ∧ S'.legs.legState f b = .Reverted := by
  cases c with
  | claimRefund flowId b' ok =>
    simp only [ChainCall.isClaimOf, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨hrev, rfl⟩ := claimRefundCall_some h
    exact ⟨hrev, by simp [legState_set]⟩
  | _ => simp [ChainCall.isClaimOf] at hc

/-- Ranks never decrease. -/
lemma execCall_rank {τ : Type} {P : ChainParams τ} {K : Checks} {S S' : ChainState τ}
    {c : ChainCall} (h : execCall P K S c = some S') (f b : Word) :
    rank (S.legs.legState f b) ≤ rank (S'.legs.legState f b) := by
  rcases execCall_legState h f b with h₁ | ⟨h₀, h₁, -⟩ | ⟨h₀, h₁, -⟩ | ⟨h₀, h₁, -⟩
  · rw [h₁]
  all_goals rw [h₀, h₁]; decide

/-! ## Runs -/

lemma chainRun_latest_ge {τ : Type} {P : ChainParams τ} {K : Checks}
    (hK : K.latestKeepsMax = true) {S S' : ChainState τ} {cs : List ChainCall}
    (h : ChainRun P K S cs S') (x : ℕ) :
    S.roots.latestInteropRootTimestamp x ≤ S'.roots.latestInteropRootTimestamp x := by
  induction h with
  | nil => exact le_rfl
  | cons hc _ ih => exact le_trans (execCall_latest_ge hK hc x) ih

lemma chainRun_bound {τ : Type} {P : ChainParams τ} {K : Checks}
    (hK : K.latestKeepsMax = true) {S S' : ChainState τ} {cs : List ChainCall}
    (h : ChainRun P K S cs S') (hS : LatestBoundsStored S.roots) : LatestBoundsStored S'.roots := by
  induction h with
  | nil => exact hS
  | cons hc _ ih => exact ih (execCall_bound hK hc hS)

lemma chainRun_l1 {τ : Type} {P : ChainParams τ} {K : Checks} {S S' : ChainState τ}
    {cs : List ChainCall} (h : ChainRun P K S cs S') (h0 : S.l1ChainId ≠ 0) :
    S'.l1ChainId = S.l1ChainId := by
  induction h with
  | nil => rfl
  | cons hc _ ih =>
    have h1 := execCall_l1 hc h0
    rw [ih (h1 ▸ h0), h1]

theorem LatestBoundsStoredInvariant : Properties.LatestBoundsStoredInvariant := by
  refine ⟨fun c b => le_refl _, fun R hR c b => by rw [hR c b]; exact Nat.zero_le _, ?_⟩
  intro τ P K S S' cs hK h hS
  exact chainRun_bound hK h hS

theorem LatestNeverDecreases : Properties.LatestNeverDecreases := by
  intro τ P K S S' cs hK h c
  exact chainRun_latest_ge hK h c

/-! ## The leg map as the abstract manager -/

private lemma reach_head {M N R : Manager} (h₁ : Contracts.AtomicFlowManager.Step M N)
    (h₂ : Contracts.AtomicFlowManager.Reach N R) : Contracts.AtomicFlowManager.Reach M R := by
  induction h₂ with
  | refl => exact .tail .refl h₁
  | tail _ hs ih => exact .tail ih hs

private lemma reach_trans {M N R : Manager} (h₁ : Contracts.AtomicFlowManager.Reach M N)
    (h₂ : Contracts.AtomicFlowManager.Reach N R) : Contracts.AtomicFlowManager.Reach M R := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact .tail ih hs

/-- The marking loop is a sequence of abstract `authorize` steps, one per marked leg. -/
private lemma markCommittedRevertable_reach (M : Manager) (flowId : Word) (hs : List Word) :
    Contracts.AtomicFlowManager.Reach M (markCommittedRevertable M flowId hs) := by
  induction hs generalizing M with
  | nil => exact .refl
  | cons h hs ih =>
    simp only [markCommittedRevertable]
    split_ifs with hc
    · exact reach_head (.authorize hc) (ih _)
    · exact ih M

private lemma execCall_legs_reach {τ : Type} {P : ChainParams τ} {K : Checks}
    {S S' : ChainState τ} {c : ChainCall} (h : execCall P K S c = some S') :
    Contracts.AtomicFlowManager.Reach S.legs S'.legs := by
  cases c with
  | initL2 caller l1 =>
    obtain ⟨-, rfl⟩ := initL2Call_some h; exact .refl
  | append caller registered b idx q =>
    simp only [execCall] at h
    cases hA : appendCall P K S caller registered b idx q with
    | error e => rw [hA] at h; cases h
    | ok S₁ =>
      rw [hA] at h
      cases h
      obtain ⟨-, -, -, -, -, hunset, hlegs, -, -⟩ := appendCall_ok hA
      rw [hlegs]
      exact .tail .refl (.append hunset)
  | authorizeRefund peer flowId p i a =>
    obtain ⟨-, -, -, -, rfl⟩ := authorizeRefundCall_some h
    exact markCommittedRevertable_reach _ _ _
  | claimRefund flowId b ok =>
    obtain ⟨hrev, rfl⟩ := claimRefundCall_some h
    exact .tail .refl (.claim hrev)
  | requireFlowFinalized passes =>
    simp only [execCall] at h
    split_ifs at h
    cases h; exact .refl
  | addSingleInteropRoot caller r =>
    simp only [execCall, addSingleInteropRootCall] at h
    split_ifs at h
    obtain ⟨R, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact .refl
  | addInteropRootsInBatch caller rs =>
    simp only [execCall, addInteropRootsInBatchCall] at h
    split_ifs at h
    obtain ⟨R, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact .refl

theorem ChainRunLegsReach : Properties.ChainRunLegsReach := by
  intro τ P K S S' cs h
  induction h with
  | nil => exact .refl
  | cons hc _ ih => exact reach_trans (execCall_legs_reach hc) ih

/-! ## The ordering claim -/

/-- **WHAT A DEPLOYED AUTHORIZATION LEAVES BEHIND.**  From a state with `LatestBoundsStored`, a
successful `authorizeRefund` of `p` validated `p`, checked its flow id and settlement layer, wrote
only the leg map, and the tracked timestamp of `p`'s settlement layer is past `p.deadline`. -/
lemma after_authorization {τ : Type} {P : ChainParams τ} {S₁ S₂ : ChainState τ}
    {peer : ℕ → Bool} {flowId : Word} {p : FlowPreimage} {i : ℕ} {a : AbsenceProof}
    (hb : LatestBoundsStored S₁.roots)
    (h : execCall P deployed S₁ (.authorizeRefund peer flowId p i a) = some S₂) :
    preimageError? p = none ∧ P.flowHash p = flowId ∧
    p.settlementLayerChainId = S₁.l1ChainId ∧ S₂.l1ChainId = S₁.l1ChainId ∧
    p.deadline < S₂.roots.latestInteropRootTimestamp p.settlementLayerChainId ∧
    S₂.legs = markCommittedRevertable S₁.legs flowId p.legBundleHashes := by
  obtain ⟨hpe, hfh, hsl, htav, rfl⟩ := authorizeRefundCall_some h
  obtain ⟨hasl, hlt⟩ := timeoutAbsence_deployed htav
  refine ⟨hpe, hfh, hsl, rfl, ?_, rfl⟩
  have := hb a.settlementLayerChainId a.settlementLayerBatchNumber
  rw [hasl] at this hlt
  exact lt_of_lt_of_le hlt this

/-- In a state where `p`'s settlement layer is tracked past `p.deadline`, no deployed `append`
of `p` succeeds. -/
lemma append_blocked {τ : Type} {P : ChainParams τ} {S : ChainState τ} {p : FlowPreimage}
    (hlt : p.deadline < S.roots.latestInteropRootTimestamp p.settlementLayerChainId)
    (caller : ℕ) (registered : ℕ → Bool) (b : Word) (idx : ℕ) :
    ∃ e, appendCall P deployed S caller registered b idx p = .error e := by
  cases hA : appendCall P deployed S caller registered b idx p with
  | error e => exact ⟨e, rfl⟩
  | ok S' => exact absurd ⟨rfl, hlt⟩ (appendCall_ok hA).2.2.2.1

/-- The whole run: the authorization's facts, carried to the end of the continuation. -/
lemma closed_after {τ : Type} {P : ChainParams τ} {S₀ S₁ S₂ S₃ : ChainState τ}
    {pre post : List ChainCall} {peer : ℕ → Bool} {flowId : Word} {p : FlowPreimage} {i : ℕ}
    {a : AbsenceProof} (hb : LatestBoundsStored S₀.roots) (hpre : ChainRun P deployed S₀ pre S₁)
    (hauth : execCall P deployed S₁ (.authorizeRefund peer flowId p i a) = some S₂)
    (hpost : ChainRun P deployed S₂ post S₃) :
    preimageError? p = none ∧ P.flowHash p = flowId ∧
    p.settlementLayerChainId = S₁.l1ChainId ∧
    p.deadline < S₂.roots.latestInteropRootTimestamp p.settlementLayerChainId ∧
    p.deadline < S₃.roots.latestInteropRootTimestamp p.settlementLayerChainId ∧
    (S₁.l1ChainId ≠ 0 → S₃.l1ChainId = S₁.l1ChainId) ∧
    S₂.legs = markCommittedRevertable S₁.legs flowId p.legBundleHashes := by
  have hb₁ := chainRun_bound rfl hpre hb
  obtain ⟨hpe, hfh, hsl, hl1, hlt, hlegs⟩ := after_authorization hb₁ hauth
  refine ⟨hpe, hfh, hsl, hlt, lt_of_lt_of_le hlt (chainRun_latest_ge rfl hpost _), ?_, hlegs⟩
  intro h0
  rw [chainRun_l1 hpost (hl1 ▸ h0), hl1]

theorem AuthorizedPreimageNeverAppendedAgain : Properties.AuthorizedPreimageNeverAppendedAgain := by
  intro τ P S₀ S₁ S₂ S₃ pre post peer flowId p i a hb hpre hauth hpost caller registered b idx
  obtain ⟨-, -, -, -, hlt, -, -⟩ := closed_after hb hpre hauth hpost
  exact append_blocked hlt caller registered b idx

theorem AuthorizedPreimageAppendHitsDeadlineGate :
    Properties.AuthorizedPreimageAppendHitsDeadlineGate := by
  intro τ P S₀ S₁ S₂ S₃ pre post peer flowId p i a hb hpre hauth hpost h0
  obtain ⟨hpe, -, hsl, -, hlt, hl1, -⟩ := closed_after hb hpre hauth hpost
  have hsl₃ : p.settlementLayerChainId = S₃.l1ChainId := by rw [hl1 h0, hsl]
  refine ⟨hlt, fun registered b idx => ?_⟩
  have hne : ¬ (p.settlementLayerChainId ≠ S₃.l1ChainId) := not_not.2 hsl₃
  have hgate : deployed.deadlineGate = true ∧
      p.deadline < S₃.roots.latestInteropRootTimestamp p.settlementLayerChainId := ⟨rfl, hlt⟩
  simp only [appendCall, ne_eq, not_true_eq_false, ↓reduceIte, hpe]
  rw [ite_eq_right hne, ite_eq_left hgate]

theorem AuthorizedFlowIdAppendRevertsOrLoggedClash :
    Properties.AuthorizedFlowIdAppendRevertsOrLoggedClash := by
  intro τ P S₀ S₁ S₂ S₃ pre post peer flowId p i a hb hpre hauth hpost
  obtain ⟨-, hfh, -, -, hlt, -, -⟩ := closed_after hb hpre hauth hpost
  refine ⟨hfh, fun caller registered b idx q hq => ?_⟩
  by_cases hqp : q = p
  · subst hqp; exact .inl (append_blocked hlt caller registered b idx)
  · exact .inr ⟨hqp, hq.trans hfh.symm⟩

theorem LaterAppendsHaveLaterDeadlines : Properties.LaterAppendsHaveLaterDeadlines := by
  intro τ P S₀ S₁ S₂ S₃ pre post peer flowId p i a hb hpre hauth hpost h0 caller registered b idx
    q S₄ hA
  obtain ⟨-, -, hsl, -, hlt, hl1, -⟩ := closed_after hb hpre hauth hpost
  obtain ⟨-, -, hqsl, hgate, -⟩ := appendCall_ok hA
  have hsame : q.settlementLayerChainId = p.settlementLayerChainId := by
    rw [hqsl, hl1 h0, hsl]
  refine ⟨hsame, ?_⟩
  rw [hsame] at hgate
  have : ¬ q.deadline < S₃.roots.latestInteropRootTimestamp p.settlementLayerChainId :=
    fun h => hgate ⟨rfl, h⟩
  omega

/-! ## Legs of the refunded flow -/

/-- From a start where leg `(f, b)` is not `Committed`, a run that ends with it `Committed`
contains a successful `append` of it, whose preimage lists `b`. -/
lemma committed_logged {τ : Type} {P : ChainParams τ} {K : Checks} {S S' : ChainState τ}
    {cs : List ChainCall} (h : ChainRun P K S cs S') (f b : Word)
    (hc : S'.legs.legState f b = .Committed) :
    S.legs.legState f b = .Committed ∨
      ∃ c ∈ cs, ∃ q : FlowPreimage, c.AppendsLeg P f b q ∧ b ∈ q.legBundleHashes := by
  induction h with
  | nil => exact .inl hc
  | @cons S S₁ S₂ c cs hstep _ ih =>
    rcases ih hc with h₁ | ⟨c', hc', q, hq⟩
    · rcases execCall_legState hstep f b with h₂ | ⟨-, -, q, caller, reg, idx, rfl, hfq, hmem, -⟩ |
          ⟨-, h₂, -⟩ | ⟨-, h₂, -⟩
      · exact .inl (h₂ ▸ h₁)
      · exact .inr ⟨_, List.mem_cons_self .., q, ⟨caller, reg, idx, rfl, hfq⟩, hmem⟩
      · rw [h₁] at h₂; cases h₂
      · rw [h₁] at h₂; cases h₂
    · exact .inr ⟨c', List.mem_cons_of_mem _ hc', q, hq⟩

/-- Along a deployed run that starts with `p`'s settlement layer tracked past `p.deadline`, a leg
that ends `Committed` was `Committed` at the start or was appended with a preimage other than
`p`. -/
lemma committed_after_closed {τ : Type} {P : ChainParams τ} {S S' : ChainState τ}
    {cs : List ChainCall} (h : ChainRun P deployed S cs S') {p : FlowPreimage}
    (hlt : p.deadline < S.roots.latestInteropRootTimestamp p.settlementLayerChainId) (f b : Word)
    (hc : S'.legs.legState f b = .Committed) :
    S.legs.legState f b = .Committed ∨
      ∃ c ∈ cs, ∃ q : FlowPreimage, c.AppendsLeg P f b q ∧ q ≠ p := by
  induction h with
  | nil => exact .inl hc
  | @cons S S₁ S₂ c cs hstep _ ih =>
    have hlt₁ := lt_of_lt_of_le hlt (execCall_latest_ge rfl hstep p.settlementLayerChainId)
    rcases ih hlt₁ hc with h₁ | ⟨c', hc', q, hq⟩
    · rcases execCall_legState hstep f b with h₂ | ⟨-, -, q, caller, reg, idx, rfl, hfq, -, hA⟩ |
          ⟨-, h₂, -⟩ | ⟨-, h₂, -⟩
      · exact .inl (h₂ ▸ h₁)
      · refine .inr ⟨_, List.mem_cons_self .., q, ⟨caller, reg, idx, rfl, hfq⟩, ?_⟩
        rintro rfl
        obtain ⟨e, he⟩ := append_blocked (P := P) hlt caller reg b idx
        rw [hA] at he; cases he
      · rw [h₁] at h₂; cases h₂
      · rw [h₁] at h₂; cases h₂
    · exact .inr ⟨c', List.mem_cons_of_mem _ hc', q, hq⟩

theorem RefundedFlowHasNoCommittedLegOrLoggedClash :
    Properties.RefundedFlowHasNoCommittedLegOrLoggedClash := by
  intro τ P S₀ S₁ S₂ S₃ pre post peer flowId p i a hfresh hb hpre hauth hpost h hc
  obtain ⟨-, hfh, -, hlt₂, -, -, hlegs⟩ := closed_after hb hpre hauth hpost
  rcases committed_after_closed hpost hlt₂ flowId h hc with h₂ | ⟨c, hcmem, q, hq, hne⟩
  · -- `(flowId, h)` was already `Committed` after the authorization: the loop skipped it
    rw [hlegs, markCommittedRevertable_legState] at h₂
    by_cases hcond : flowId = flowId ∧ h ∈ p.legBundleHashes ∧ S₁.legs.legState flowId h = .Committed
    · rw [ite_eq_left hcond] at h₂; cases h₂
    · rw [ite_eq_right hcond] at h₂
      have hnot : h ∉ p.legBundleHashes := fun hm => hcond ⟨rfl, hm, h₂⟩
      rcases committed_logged hpre flowId h h₂ with h₀ | ⟨c, hcmem, q, hq, hmem⟩
      · rw [hfresh] at h₀; cases h₀
      · refine ⟨c, List.mem_append_left _ hcmem, q, hq, ?_, ?_⟩
        · rintro rfl; exact hnot hmem
        · obtain ⟨-, -, -, -, hfq⟩ := hq; rw [hfq, hfh]
  · refine ⟨c, List.mem_append_right _ hcmem, q, hq, hne, ?_⟩
    obtain ⟨-, -, -, -, hfq⟩ := hq; rw [hfq, hfh]

/-! ## Claims -/

lemma reverted_run {τ : Type} {P : ChainParams τ} {K : Checks} {S S' : ChainState τ}
    {cs : List ChainCall} (h : ChainRun P K S cs S') (f b : Word)
    (hr : S.legs.legState f b = .Reverted) :
    cs.countP (ChainCall.isClaimOf f b) = 0 ∧ S'.legs.legState f b = .Reverted := by
  induction h with
  | nil => exact ⟨rfl, hr⟩
  | @cons S S₁ S₂ c cs hstep _ ih =>
    have h₁ : S₁.legs.legState f b = .Reverted := by
      rcases execCall_legState hstep f b with h₂ | ⟨h₀, -⟩ | ⟨h₀, -⟩ | ⟨h₀, -⟩
      · rw [h₂, hr]
      all_goals rw [hr] at h₀; cases h₀
    have hnc : c.isClaimOf f b = false := by
      cases hcl : c.isClaimOf f b
      · rfl
      · rw [(isClaimOf_exec hcl hstep).1] at hr; cases hr
    obtain ⟨hcnt, hend⟩ := ih h₁
    exact ⟨by simp [hnc, hcnt], hend⟩

lemma revertable_run {τ : Type} {P : ChainParams τ} {K : Checks} {S S' : ChainState τ}
    {cs : List ChainCall} (h : ChainRun P K S cs S') (f b : Word)
    (hr : S.legs.legState f b = .Revertable) :
    cs.countP (ChainCall.isClaimOf f b) ≤ 1 ∧
      S'.legs.legState f b =
        (if cs.countP (ChainCall.isClaimOf f b) = 0 then .Revertable else .Reverted) := by
  induction h with
  | nil => exact ⟨by simp, by simp [hr]⟩
  | @cons S S₁ S₂ c cs hstep hrest ih =>
    cases hcl : c.isClaimOf f b
    · -- not a claim of the leg: it stays `Revertable`
      have h₁ : S₁.legs.legState f b = .Revertable := by
        rcases execCall_legState hstep f b with h₂ | ⟨h₀, -⟩ | ⟨h₀, -⟩ | ⟨-, -, h₂⟩
        · rw [h₂, hr]
        · rw [hr] at h₀; cases h₀
        · rw [hr] at h₀; cases h₀
        · rw [hcl] at h₂; cases h₂
      simpa [List.countP_cons, hcl] using ih h₁
    · -- the claim: `Reverted` from here on, and no further claim
      obtain ⟨-, h₁⟩ := isClaimOf_exec hcl hstep
      obtain ⟨hcnt, hend⟩ := reverted_run hrest f b h₁
      simp [hcl, hcnt, hend]

theorem CommittedLegsBecomeClaimableOnce : Properties.CommittedLegsBecomeClaimableOnce := by
  intro τ P S₁ S₂ peer flowId p i a hauth h hmem hcom
  obtain ⟨-, -, -, -, rfl⟩ := authorizeRefundCall_some hauth
  have hrev : (markCommittedRevertable S₁.legs flowId p.legBundleHashes).legState flowId h =
      .Revertable := by
    rw [markCommittedRevertable_legState, ite_eq_left ⟨rfl, hmem, hcom⟩]
  refine ⟨hrev, fun post S₃ hpost => ?_⟩
  obtain ⟨hcnt, hend⟩ := revertable_run hpost flowId h hrev
  refine ⟨hcnt, hend, fun h0 => ?_⟩
  rw [ite_eq_left h0] at hend
  exact ⟨{ S₃ with legs := S₃.legs.set flowId h .Reverted },
    by simp [execCall, claimRefundCall, hend]⟩

/-! ## The source comment's form -/

/-- A run that lifts leg `(f, b)` from below `Revertable` to `Revertable` or above contains an
`authorizeRefund` of flow id `f`, and splits there. -/
lemma split_at_authorization {τ : Type} {P : ChainParams τ} {K : Checks} {S S' : ChainState τ}
    {cs : List ChainCall} (h : ChainRun P K S cs S') (f b : Word)
    (hlo : rank (S.legs.legState f b) < 2) (hhi : 2 ≤ rank (S'.legs.legState f b)) :
    ∃ (pre₁ pre₂ : List ChainCall) (peer : ℕ → Bool) (p : FlowPreimage) (i : ℕ)
      (a : AbsenceProof) (Sa Sb : ChainState τ),
      cs = pre₁ ++ ChainCall.authorizeRefund peer f p i a :: pre₂ ∧ ChainRun P K S pre₁ Sa ∧
      execCall P K Sa (.authorizeRefund peer f p i a) = some Sb ∧ ChainRun P K Sb pre₂ S' := by
  induction h with
  | nil => omega
  | @cons S S₁ S₂ c cs hstep hrest ih =>
    by_cases h₁ : 2 ≤ rank (S₁.legs.legState f b)
    · rcases execCall_legState hstep f b with h₂ | ⟨-, h₂, -⟩ |
          ⟨-, -, peer, p, i, a, rfl⟩ | ⟨h₀, -⟩
      · rw [h₂] at h₁; omega
      · rw [h₂] at h₁; simp [rank] at h₁
      · exact ⟨[], cs, peer, p, i, a, S, S₁, rfl, .nil, hstep, hrest⟩
      · rw [h₀] at hlo; simp [rank] at hlo
    · obtain ⟨pre₁, pre₂, peer, p, i, a, Sa, Sb, rfl, h₁', hauth, h₂'⟩ := ih (by omega) hhi
      exact ⟨c :: pre₁, pre₂, peer, p, i, a, Sa, Sb, rfl, .cons hstep h₁', hauth, h₂'⟩

theorem RevertedLegClosesFlowOrLoggedClash : Properties.RevertedLegClosesFlowOrLoggedClash := by
  intro τ P S₀ S₁ pre hfresh hb hrun flowId h hstate
  have hlo : rank (S₀.legs.legState flowId h) < 2 := by
    rw [hfresh]; simp [Contracts.AtomicFlowManager.empty, rank]
  have hhi : 2 ≤ rank (S₁.legs.legState flowId h) := by
    rcases hstate with h₁ | h₁ <;> rw [h₁] <;> simp [rank]
  obtain ⟨pre₁, pre₂, peer, p, i, a, Sa, Sb, rfl, h₁, hauth, h₂⟩ :=
    split_at_authorization hrun flowId h hlo hhi
  have hba := chainRun_bound rfl h₁ hb
  obtain ⟨-, hfh, -, -, hlt, -⟩ := after_authorization hba hauth
  refine ⟨peer, p, i, a, List.mem_append_right _ (List.mem_cons_self ..), hfh, ?_⟩
  intro post S₃ hpost caller registered b idx q S₄ hA hq
  rintro rfl
  have hlt₃ := lt_of_lt_of_le hlt
    (chainRun_latest_ge rfl (chainRun_append h₂ hpost) q.settlementLayerChainId)
  obtain ⟨e, he⟩ := append_blocked (P := P) hlt₃ caller registered b idx
  rw [hA] at he; cases he

/-! ## A concrete configuration, for the witness and the countermodels

Every state below is computed from genesis by `runCalls`, and every fact about it is checked by
`decide`. -/

/-- An `Except` read as its error, if any. -/
private def errorOf {ε α : Type} : Except ε α → Option ε
  | .error e => some e
  | .ok _ => none

private lemma eq_error_of_errorOf {ε α : Type} {x : Except ε α} {e : ε}
    (h : errorOf x = some e) : x = .error e := by
  cases x with
  | error e' => simp only [errorOf, Option.some.injEq] at h; rw [h]
  | ok _ => simp [errorOf] at h

private lemma eq_ok_of_toOption {ε α : Type} {x : Except ε α} {a : α}
    (h : x.toOption = some a) : x = .ok a := by
  cases x with
  | error e => simp [Except.toOption] at h
  | ok a' => simp only [Except.toOption, Option.some.injEq] at h; rw [h]

/-- The witnesses' chain: chain id 10 and the deployed addresses (`L2_INTEROP_CENTER_ADDR =
0x1000d`, `L2_COMPLEX_UPGRADER_ADDR = 0x800f`, `L2_BOOTLOADER_ADDRESS = 0x8001`).  `flowHash` is
the deadline and `commitValue` the bundle hash; the tree rejects a value it already holds (the
`IMTValueAlreadyExists` check); a proof authenticates exactly when the root it names is
imported; the last-batch and IMT checks pass. -/
private def demoParams : ChainParams (List Word) where
  chainId := 10
  interopCenter := 0x1000d
  complexUpgrader := 0x800f
  bootloader := 0x8001
  flowHash := fun p => (p.deadline : Word)
  commitValue := fun _ b => b
  treeInsert := fun T v _ => if v ∈ T then none else some (v :: T)
  rootAuthenticated := fun R a =>
    decide ((R.storedInteropRoots a.settlementLayerChainId a.settlementLayerBatchNumber).root ≠ 0)
  lastBatchInRoot := fun _ => true
  absent := fun _ _ => true

/-- A three-leg flow settling on chain 1 with deadline 50: legs `0x11` and `0x33` on this chain,
`0x22` on chain 20. -/
private def demoFlow : FlowPreimage := ⟨1, 50, 1, [0x11, 0x22, 0x33], [10, 20, 10]⟩

/-- A one-leg flow on this chain, deadline 200. -/
private def demoLaterFlow : FlowPreimage := ⟨1, 200, 1, [0x44], [10]⟩

/-- The Bridgehub's answers: chain 20 is a registered, allowed peer. -/
private def demoPeer : ℕ → Bool := fun c => c == 20

/-- An absence proof for leg `0x22` (index 1, source chain 20) against the BEGIN root of a batch
settled at time 60, through settlement-layer block 7 of chain `sl`. -/
private def demoProof (sl : ℕ) : AbsenceProof := ⟨20, true, sl, 7, 60, 0⟩

/-- The bootloader imports a root of chain `chainId`, block `blk`, created at `ts`. -/
private def demoImport (chainId blk ts : ℕ) : ChainCall :=
  .addSingleInteropRoot 0x8001 ⟨chainId, blk, ts, [0xabc]⟩

/-- `authorizeRefund` of `demoFlow`, missing leg 1, with `demoProof sl`. -/
private def demoAuth (sl : ℕ) : ChainCall := .authorizeRefund demoPeer 50 demoFlow 1 (demoProof sl)

/-! ### The witness run -/

private def wPre₁ : List ChainCall :=
  [.initL2 0x800f 1, .append 0x1000d demoPeer 0x11 0 demoFlow]

private def wPost : List ChainCall :=
  [.claimRefund 50 0x11 true, .append 0x1000d demoPeer 0x44 0 demoLaterFlow]

private def wM : ChainState (List Word) :=
  (runCalls demoParams deployed (genesis []) wPre₁).get (by decide)

private def wM' : ChainState (List Word) :=
  (appendCall demoParams deployed wM demoParams.interopCenter demoPeer 0x33 0 demoFlow).toOption.get
    (by decide)

private def wS₁ : ChainState (List Word) :=
  (execCall demoParams deployed wM (demoImport 1 7 100)).get (by decide)

private def wS₂ : ChainState (List Word) :=
  (execCall demoParams deployed wS₁ (demoAuth 1)).get (by decide)

private def wS₃ : ChainState (List Word) :=
  (runCalls demoParams deployed wS₂ wPost).get (by decide)

theorem RefundClosesAppendWitness : Properties.RefundClosesAppendWitness := by
  have hpre : ChainRun demoParams deployed (genesis []) wPre₁ wM :=
    (ChainRunIffRunCalls _ _ _ _ _).2 (Option.some_get _).symm
  have himp : execCall demoParams deployed wM (demoImport 1 7 100) = some wS₁ :=
    (Option.some_get _).symm
  refine ⟨demoParams, wPre₁, wPost, demoImport 1 7 100, genesis [], wM, wS₁, wS₂, wS₃, wM',
    demoPeer, 50, demoFlow, demoLaterFlow, 1, demoProof 1, demoPeer, 0x11, 0x33,
    rfl, fun _ _ => le_rfl, hpre, by decide, eq_ok_of_toOption (Option.some_get _).symm, himp,
    chainRun_append hpre (.cons himp .nil), by decide, by decide, by decide, by decide, by decide,
    by decide, (Option.some_get _).symm, rfl, by decide,
    (ChainRunIffRunCalls _ _ _ _ _).2 (Option.some_get _).symm, by decide, by decide,
    ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), 0x1000d, demoPeer, 0x44, 0, rfl⟩,
    by decide, by decide, ?_, by decide, eq_error_of_errorOf (by decide)⟩
  intro c hc caller reg b idx r hcr
  subst hcr
  simp only [wPre₁, wPost, demoImport, List.cons_append, List.nil_append, List.mem_cons,
    ChainCall.append.injEq, reduceCtorEq, List.not_mem_nil, or_false, false_or] at hc
  rcases hc with ⟨-, -, -, -, rfl⟩ | ⟨-, -, -, -, rfl⟩
  · exact .inl rfl
  · exact .inr rfl

/-! ### Countermodels -/

private def cxPre (chainId ts : ℕ) : List ChainCall := [.initL2 0x800f 1, demoImport chainId 7 ts]

private def x1S₁ : ChainState (List Word) :=
  (runCalls demoParams withoutDeadlineGate (genesis []) (cxPre 1 100)).get (by decide)

private def x1S₂ : ChainState (List Word) :=
  (execCall demoParams withoutDeadlineGate x1S₁ (demoAuth 1)).get (by decide)

private def x1S₃ : ChainState (List Word) :=
  (appendCall demoParams withoutDeadlineGate x1S₂ demoParams.interopCenter demoPeer 0x11 0
    demoFlow).toOption.get (by decide)

private def x1S₄ : ChainState (List Word) :=
  (execCall demoParams withoutDeadlineGate x1S₃ (demoAuth 1)).get (by decide)

theorem WithoutDeadlineGateLegCommittedAfterRefund :
    Properties.WithoutDeadlineGateLegCommittedAfterRefund := by
  have hrun : runCalls demoParams deployed (genesis []) (cxPre 1 100) =
      runCalls demoParams withoutDeadlineGate (genesis []) (cxPre 1 100) := rfl
  have hauth : execCall demoParams deployed x1S₁ (demoAuth 1) =
      execCall demoParams withoutDeadlineGate x1S₁ (demoAuth 1) := rfl
  refine ⟨demoParams, cxPre 1 100, x1S₁, x1S₂, x1S₃, x1S₄, demoPeer, 50, demoFlow, 1, demoProof 1,
    demoPeer, 0x11, 0, (ChainRunIffRunCalls _ _ _ _ _).2 (Option.some_get _).symm,
    (Option.some_get _).symm, eq_ok_of_toOption (Option.some_get _).symm, by decide,
    (ChainRunIffRunCalls _ _ _ _ _).2 (hrun.trans (Option.some_get _).symm),
    hauth.trans (Option.some_get _).symm, eq_error_of_errorOf (by decide),
    (Option.some_get _).symm, by decide⟩

private def x2S₁ : ChainState (List Word) :=
  (runCalls demoParams lastValueLatest (genesis []) (cxPre 1 100)).get (by decide)

private def x2S₂ : ChainState (List Word) :=
  (execCall demoParams lastValueLatest x2S₁ (demoAuth 1)).get (by decide)

private def x2S₃ : ChainState (List Word) :=
  (runCalls demoParams lastValueLatest x2S₂ [demoImport 1 5 40]).get (by decide)

private def x2S₄ : ChainState (List Word) :=
  (appendCall demoParams lastValueLatest x2S₃ demoParams.interopCenter demoPeer 0x11 0
    demoFlow).toOption.get (by decide)

private def x2D₁ : ChainState (List Word) :=
  (runCalls demoParams deployed (genesis []) (cxPre 1 100)).get (by decide)

private def x2D₂ : ChainState (List Word) :=
  (execCall demoParams deployed x2D₁ (demoAuth 1)).get (by decide)

private def x2D₃ : ChainState (List Word) :=
  (runCalls demoParams deployed x2D₂ [demoImport 1 5 40]).get (by decide)

theorem LastValueLatestReadmitsAppend : Properties.LastValueLatestReadmitsAppend := by
  refine ⟨demoParams, cxPre 1 100, [demoImport 1 5 40], x2S₁, x2S₂, x2S₃, x2S₄, x2D₁, x2D₂, x2D₃,
    demoPeer, 50, demoFlow, 1, demoProof 1, demoPeer, 0x11, 0,
    (ChainRunIffRunCalls _ _ _ _ _).2 (Option.some_get _).symm, (Option.some_get _).symm,
    (ChainRunIffRunCalls _ _ _ _ _).2 (Option.some_get _).symm,
    eq_ok_of_toOption (Option.some_get _).symm, by decide,
    fun h => absurd (h 1 7) (by decide),
    (ChainRunIffRunCalls _ _ _ _ _).2 (Option.some_get _).symm, (Option.some_get _).symm,
    (ChainRunIffRunCalls _ _ _ _ _).2 (Option.some_get _).symm,
    .flowDeadlinePassed 50 100, eq_error_of_errorOf (by decide)⟩

private def x3S₁ : ChainState (List Word) :=
  (runCalls demoParams unboundProofSettlementLayer (genesis []) (cxPre 2 100)).get (by decide)

private def x3S₂ : ChainState (List Word) :=
  (execCall demoParams unboundProofSettlementLayer x3S₁ (demoAuth 2)).get (by decide)

private def x3S₃ : ChainState (List Word) :=
  (appendCall demoParams unboundProofSettlementLayer x3S₂ demoParams.interopCenter demoPeer 0x11 0
    demoFlow).toOption.get (by decide)

theorem UnboundProofSettlementLayerReadmitsAppend :
    Properties.UnboundProofSettlementLayerReadmitsAppend := by
  have hrun : runCalls demoParams deployed (genesis []) (cxPre 2 100) =
      runCalls demoParams unboundProofSettlementLayer (genesis []) (cxPre 2 100) := rfl
  refine ⟨demoParams, cxPre 2 100, x3S₁, x3S₂, x3S₃, demoPeer, 50, demoFlow, 1, demoProof 2,
    demoPeer, 0x11, 0, (ChainRunIffRunCalls _ _ _ _ _).2 (Option.some_get _).symm,
    (Option.some_get _).symm, by decide, eq_ok_of_toOption (Option.some_get _).symm, by decide,
    (ChainRunIffRunCalls _ _ _ _ _).2 (hrun.trans (Option.some_get _).symm),
    Option.isNone_iff_eq_none.1 (by decide)⟩

private def x4S₁ : ChainState (List Word) :=
  (runCalls demoParams nonStrictRootTimestamp (genesis []) (cxPre 1 50)).get (by decide)

private def x4S₂ : ChainState (List Word) :=
  (execCall demoParams nonStrictRootTimestamp x4S₁ (demoAuth 1)).get (by decide)

private def x4S₃ : ChainState (List Word) :=
  (appendCall demoParams nonStrictRootTimestamp x4S₂ demoParams.interopCenter demoPeer 0x11 0
    demoFlow).toOption.get (by decide)

theorem NonStrictRootTimestampReadmitsAppend : Properties.NonStrictRootTimestampReadmitsAppend := by
  have hrun : runCalls demoParams deployed (genesis []) (cxPre 1 50) =
      runCalls demoParams nonStrictRootTimestamp (genesis []) (cxPre 1 50) := rfl
  refine ⟨demoParams, cxPre 1 50, x4S₁, x4S₂, x4S₃, demoPeer, 50, demoFlow, 1, demoProof 1,
    demoPeer, 0x11, 0, (ChainRunIffRunCalls _ _ _ _ _).2 (Option.some_get _).symm,
    (Option.some_get _).symm, by decide, eq_ok_of_toOption (Option.some_get _).symm, by decide,
    (ChainRunIffRunCalls _ _ _ _ _).2 (hrun.trans (Option.some_get _).symm),
    Option.isNone_iff_eq_none.1 (by decide)⟩

/-- A state no run from fresh storage reaches: `L1_CHAIN_ID` is 1 and chain 1's root at block 7
has timestamp 100 while the tracked timestamp is 0. -/
private def x5S₁ : ChainState (List Word) where
  legs := Contracts.AtomicFlowManager.empty
  l1ChainId := 1
  tree := []
  roots :=
    { storedInteropRoots := fun c b => if c = 1 ∧ b = 7 then ⟨0xabc, 100⟩ else ⟨0, 0⟩
      latestInteropRootTimestamp := fun _ => 0 }

private def x5S₂ : ChainState (List Word) :=
  (execCall demoParams deployed x5S₁ (demoAuth 1)).get (by decide)

private def x5S₃ : ChainState (List Word) :=
  (appendCall demoParams deployed x5S₂ demoParams.interopCenter demoPeer 0x11 0
    demoFlow).toOption.get (by decide)

theorem WithoutLatestBoundAppendAfterRefund : Properties.WithoutLatestBoundAppendAfterRefund := by
  refine ⟨demoParams, x5S₁, x5S₂, x5S₃, demoPeer, 50, demoFlow, 1, demoProof 1, demoPeer, 0x11, 0,
    fun h => absurd (h 1 7) (by decide), (Option.some_get _).symm,
    eq_ok_of_toOption (Option.some_get _).symm, by decide⟩

end Contracts.AtomicFlowManager.RefundClosesAppend
