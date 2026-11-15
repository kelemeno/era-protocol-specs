import EraSpec.Contracts.L2InteropHandler.Properties.AtomicSourceBindingStrong
import EraSpec.Contracts.InteropCenter.Proofs.Dispatch
import Mathlib.Tactic

/-!
# Proofs: the atomic path's source binding, derived from one tree and named collisions

The headline follows the values back. A key of the honest tree is the sentinel or the commit
value of a logged atomic dispatch. Equal commit values come from equal commit preimages or a
named collision; equal commit preimages (three words) have equal bundle-hash words. Equal bundle
hashes come from equal bundle-hash preimages or a named collision; equal preimages
`abi.encode(src, x) = abi.encode(P.chainId, abi.encode(bundle))` have the same first word, so
`src = P.chainId`, and the same bytes argument (`Contracts.InteropCenter.abiEncode_right_inj`,
which needs no length bound).
-/

namespace AttackVectors.AtomicSourceBinding

open AttackVectors.BundleHashEncoding (abiEncode HashCollision word pad32 toBytesBE
  length_toBytesBE)
open Contracts.InteropCenter (Params Dispatch Word bundleHash bundlePreimage KeccakInjOn)

/-! ## Words -/

/-- A `uint256` word determines its value. -/
lemma word_val_inj {a b : Word} (h : word a.val = word b.val) : a = b := by
  have hm := Contracts.InteropCenter.toBytesBE_eq_mod h
  rw [Contracts.InteropCenter.size_eq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hm
  exact Fin.ext hm

/-- The commit preimage determines its three words. -/
lemma commitPreimage_inj {t f h t' f' h' : Word}
    (heq : commitPreimage t f h = commitPreimage t' f' h') : t = t' ∧ f = f' ∧ h = h' := by
  unfold commitPreimage at heq
  obtain ⟨h1, h23⟩ := List.append_inj heq (by simp only [length_toBytesBE])
  obtain ⟨h2, h3⟩ := List.append_inj h23 (by simp only [length_toBytesBE])
  exact ⟨word_val_inj h1, word_val_inj h2, word_val_inj h3⟩

/-- `abi.encode(uint256, bytes)` determines its chain-id word. -/
lemma abiEncode_chainWord_eq {c c' : Word} {x y : List UInt8}
    (h : abiEncode c.val x = abiEncode c'.val y) : c = c' := by
  have h32 := congrArg (List.take 32) h
  simp only [abiEncode] at h32
  rw [List.take_left' (length_toBytesBE 32 _), List.take_left' (length_toBytesBE 32 _)] at h32
  exact word_val_inj h32

/-! ## The validator -/

theorem DestContextCheckBySite : Properties.DestContextCheckBySite := by
  refine ⟨fun chainId base b => ?_, fun chainId base c b h => h.1, 325, 1, 999, ⟨324, 325, 1⟩,
    ⟨rfl, rfl, rfl⟩, ?_⟩
  · simp [DestContextValid, CtxSite.proofChainId]
  · rintro ⟨h, -, -⟩
    exact absurd h (by decide)

/-! ## The binding -/

theorem AtomicSourceBoundToVouchingTreeOrLoggedClash :
    Properties.AtomicSourceBoundToVouchingTreeOrLoggedClash := by
  intro P tag log T f src x hT hmem
  rcases hT _ hmem with h0 | ⟨d, hd, hat, hv⟩
  · exact Or.inr (Or.inl h0)
  · by_cases hcp : commitPreimage tag f (destBundleHash P.keccak src x) =
        commitPreimage tag d.atomicSend.flowId (bundleHash P d.bundle)
    · obtain ⟨-, hf, hh⟩ := commitPreimage_inj hcp
      by_cases hbp : abiEncode src.val x = bundlePreimage P d.bundle
      · left
        have hbp' : abiEncode src.val x = abiEncode P.chainId.val (P.enc d.bundle) := hbp
        exact ⟨abiEncode_chainWord_eq hbp', d, hd, hat, hf.symm,
          Contracts.InteropCenter.abiEncode_right_inj hbp'⟩
      · exact Or.inr (Or.inr ⟨d, hd, hat, Or.inr ⟨hbp, hh⟩⟩)
    · exact Or.inr (Or.inr ⟨d, hd, hat, Or.inl ⟨hcp, hv⟩⟩)

theorem AtomicSourceBoundOn : Properties.AtomicSourceBoundOn := by
  intro P tag log T f src x hT hmem hne hinj1 hinj2
  rcases AtomicSourceBoundToVouchingTreeOrLoggedClash P tag log T f src x hT hmem with
    h | h | ⟨d, hd, hat, hc | hc⟩
  · exact h
  · exact absurd h hne
  · exfalso
    obtain ⟨hne', heq⟩ := hc
    exact hne' (hinj1 _ List.mem_cons_self _
      (List.mem_cons_of_mem _ (List.mem_map.2 ⟨d, List.mem_filter.2 ⟨hd, hat⟩, rfl⟩)) heq)
  · exfalso
    obtain ⟨hne', heq⟩ := hc
    exact hne' (hinj2 _ List.mem_cons_self _
      (List.mem_cons_of_mem _ (List.mem_map.2 ⟨d, List.mem_filter.2 ⟨hd, hat⟩, rfl⟩)) heq)

theorem CenterRunTreeHoldsOwnLegs : Properties.CenterRunTreeHoldsOwnLegs := by
  intro P S tag T hr hT v hv
  rcases hT v hv with h0 | ⟨f, h, hne, rfl⟩
  · exact Or.inl h0
  · obtain ⟨d, hd, hat, hf, hh, -, -⟩ :=
      Contracts.InteropCenter.CommittedLegsAreValidatedDispatches P S hr f h hne
    exact Or.inr ⟨d, hd, hat, by rw [hf, hh]⟩

theorem AtomicSourceBoundOnCenterRunOrLoggedClash :
    Properties.AtomicSourceBoundOnCenterRunOrLoggedClash := by
  intro P S tag T f src x hr hT hmem
  rcases AtomicSourceBoundToVouchingTreeOrLoggedClash P tag S.log T f src x
      (CenterRunTreeHoldsOwnLegs P S tag T hr hT) hmem with
    ⟨hsrc, d, hd, hat, hf, hx⟩ | h | h
  · left
    have hinv := Contracts.InteropCenter.inv_reach hr
    exact ⟨hsrc, d, hd, hat, hf, hx,
      Contracts.InteropCenter.AtomicDispatchesCarryNoValue P S hr d hd hat,
      (hinv.formed d hd).source⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem ExecutingBundleSenderChainIsItsLegChainOrLoggedClash :
    Properties.ExecutingBundleSenderChainIsItsLegChainOrLoggedClash := by
  intro P tag trees log flowId src x legs hgate hleg hT
  exact AtomicSourceBoundToVouchingTreeOrLoggedClash P tag log (trees P.chainId) flowId src x hT
    (hgate.included _ hleg)

/-! ## The witnesses -/

/-- The witness keccak reads the last word, so a commit value is its bundle-hash word. -/
lemma commitValue_lastWord (tag f h : Word) :
    commitValue Contracts.InteropCenter.lastWord tag f h = h := by
  unfold commitValue commitPreimage
  rw [← List.append_assoc, Contracts.InteropCenter.lastWord_append_word,
    Contracts.InteropCenter.ofNat_val]

/-- The foreign bytes hash, with source chain `325`, to their last word `5`. -/
lemma foreign_hash :
    destBundleHash Contracts.InteropCenter.lastWord 325 wForeignBytes = 5 := by
  unfold destBundleHash wForeignBytes
  have hpad : pad32 (word 5) = word 5 := by simp [pad32, length_toBytesBE]
  rw [abiEncode, hpad]
  rw [show word (325 : Word).val ++ (word 0x40 ++ (word (word 5).length ++ word 5)) =
      (word (325 : Word).val ++ (word 0x40 ++ word (word 5).length)) ++ toBytesBE 32 5 by
    simp [List.append_assoc]]
  rw [Contracts.InteropCenter.lastWord_append_word]
  rfl

/-- `wD1`'s commit value on the witness chain is its bundle hash, `1`. -/
lemma wD1_commit :
    commitValue Contracts.InteropCenter.wParams.keccak wTag 7
      (bundleHash Contracts.InteropCenter.wParams Contracts.InteropCenter.wD1.bundle) = 1 := by
  show commitValue Contracts.InteropCenter.lastWord wTag 7 _ = 1
  rw [commitValue_lastWord, Contracts.InteropCenter.wHash1]

/-- The foreign commit value is `5`. -/
lemma foreign_commit :
    commitValue Contracts.InteropCenter.wParams.keccak wTag 7
      (destBundleHash Contracts.InteropCenter.wParams.keccak 325 wForeignBytes) = 5 := by
  show commitValue Contracts.InteropCenter.lastWord wTag 7
    (destBundleHash Contracts.InteropCenter.lastWord 325 wForeignBytes) = 5
  rw [foreign_hash, commitValue_lastWord]

lemma wS1_log : Contracts.InteropCenter.wS1.log = [Contracts.InteropCenter.wD1] := rfl

lemma wS1_filter :
    Contracts.InteropCenter.wS1.log.filter Dispatch.isAtomic = [Contracts.InteropCenter.wD1] :=
  rfl

theorem ForeignCommitInTreeUnbindsSource : Properties.ForeignCommitInTreeUnbindsSource := by
  have h15 : (5 : Word) ≠ 1 := by decide
  refine ⟨Or.inr (Or.inr rfl), by rw [foreign_commit]; decide, by decide, ?_, ?_⟩
  · intro d hd _
    rw [wS1_log, List.mem_singleton] at hd
    subst hd
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · obtain ⟨-, hk⟩ := hc
      have hk' : commitValue Contracts.InteropCenter.wParams.keccak wTag 7
            (destBundleHash Contracts.InteropCenter.wParams.keccak 325 wForeignBytes) =
          commitValue Contracts.InteropCenter.wParams.keccak wTag
            Contracts.InteropCenter.wD1.atomicSend.flowId
            (bundleHash Contracts.InteropCenter.wParams Contracts.InteropCenter.wD1.bundle) := hk
      rw [foreign_commit, show Contracts.InteropCenter.wD1.atomicSend.flowId = 7 from rfl,
        wD1_commit] at hk'
      exact h15 hk'
    · obtain ⟨-, hk⟩ := hc
      have hk' : destBundleHash Contracts.InteropCenter.lastWord 325 wForeignBytes =
          bundleHash Contracts.InteropCenter.wParams Contracts.InteropCenter.wD1.bundle := hk
      rw [foreign_hash, Contracts.InteropCenter.wHash1] at hk'
      exact h15 hk'
  · intro hT
    rcases hT _ (Or.inr (Or.inr rfl)) with h0 | ⟨d, hd, _, hv⟩
    · rw [foreign_commit] at h0
      exact absurd h0 (by decide)
    · rw [wS1_log, List.mem_singleton] at hd
      subst hd
      rw [foreign_commit, show Contracts.InteropCenter.wD1.atomicSend.flowId = 7 from rfl,
        wD1_commit] at hv
      exact h15 hv

theorem AtomicSourceBindingStrongWitness : Properties.AtomicSourceBindingStrongWitness := by
  have hreach : Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed
      Contracts.InteropCenter.wParams Contracts.InteropCenter.init Contracts.InteropCenter.wS1 :=
    .tail .refl Contracts.InteropCenter.wStep1
  have hbacked : TreeBackedByManager Contracts.InteropCenter.wParams wTag
      Contracts.InteropCenter.wS1 wTree := by
    intro v hv
    rcases hv with h0 | rfl
    · exact Or.inl h0
    · refine Or.inr ⟨7, _, ?_, rfl⟩
      rw [Contracts.InteropCenter.wS1_leg]
      exact Contracts.AtomicFlowManager.LegState.noConfusion
  refine ⟨hreach, hbacked, CenterRunTreeHoldsOwnLegs _ _ _ _ hreach hbacked,
    ⟨⟨_, List.mem_singleton.2 rfl⟩, ?_⟩, Or.inr rfl, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    show _ ∈ (if Contracts.InteropCenter.wParams.chainId = Contracts.InteropCenter.wParams.chainId
      then wTree else ∅)
    simp only [↓reduceIte]
    exact Or.inr rfl
  · show commitValue Contracts.InteropCenter.wParams.keccak wTag 7
      (bundleHash Contracts.InteropCenter.wParams Contracts.InteropCenter.wD1.bundle) ≠ 0
    rw [wD1_commit]
    decide
  · intro d hd _
    rw [wS1_log, List.mem_singleton] at hd
    subst hd
    exact ⟨fun hc => hc.1 rfl, fun hc => hc.1 rfl⟩
  · rw [wS1_filter]
    intro u hu w hw _
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hu hw
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl <;> rfl
  · rw [wS1_filter]
    intro u hu w hw _
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hu hw
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl <;> rfl

end AttackVectors.AtomicSourceBinding
