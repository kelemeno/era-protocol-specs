import EraSpec.Protocol.ZKsyncOSDA.Properties.CommitterDA
import EraSpec.Protocol.ZKsyncOSDA.Proofs.Bytes

/-!
# Proofs: the DA guarantee each validator leaves once the committer discards its output

Proofs of `../Properties/CommitterDA.lean`. Each validator's acceptance is inverted through
`processL2_eq_some` (`./Bytes.lean`): an accepted input is `l2Output sd fp lin ++ l1DaInput`. The
committer's check forces every parsed linear hash and every returned commitment to zero
(`CommitterDACheckIff`), which fixes the remaining bytes. The headlines then compare the
validator's prefix with the program's preimage: equal prefixes agree on the full pubdata hash
(`l2Output_fp_eq`), unequal ones are a named collision.
-/

namespace Contracts.ZKsyncOSCommitterDA

open AttackVectors.BundleHashEncoding
open Contracts.ZKsyncOSBlobsDA (Bytes toB32 b32At DAOutput TxEnv encWords World LoggedInWindow
  resolvedHashes toB32_length getD_of_lt getD_of_ge encWords_length b32At_append_right
  b32At_zero_toB32)

/-! ## The committer's check -/

theorem committerDACheck_eq_true (o : DAOutput) :
    committerDACheck o = true ↔
      o.blobsLinearHashes.length = o.blobsOpeningCommitments.length
        ∧ (o.blobsLinearHashes.length = 0 ∨ o.blobsLinearHashes.length = TOTAL_BLOBS_IN_COMMITMENT)
        ∧ ∀ i < o.blobsLinearHashes.length,
            o.blobsLinearHashes.getD i 0 = 0 ∧ o.blobsOpeningCommitments.getD i 0 = 0 := by
  unfold committerDACheck
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, bne_eq_false_iff_eq,
    Bool.and_eq_false_iff, List.all_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, ?_, h3⟩
    rcases h2 with h2 | h2
    · left; simpa using h2
    · right; simpa using h2
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, ?_⟩, h3⟩
    rcases h2 with h2 | h2
    · left; simpa using h2
    · right; simpa using h2

theorem eq_replicate_zero_of_getD {l : List UInt256} {n : ℕ} (hl : l.length = n)
    (h : ∀ i < n, l.getD i 0 = 0) : l = List.replicate n 0 := by
  subst hl
  apply List.ext_getElem (by simp)
  intro i h1 _
  rw [List.getElem_replicate]
  have := h i h1
  rwa [getD_of_lt h1] at this

theorem getD_replicate_zero (n i : ℕ) : (List.replicate n (0 : UInt256)).getD i 0 = 0 := by
  by_cases hi : i < n
  · rw [getD_of_lt (by simpa using hi), List.getElem_replicate]
  · rw [getD_of_ge (by simp; omega)]

theorem CommitterDACheckIff : Properties.CommitterDACheckIff := by
  intro o
  rw [committerDACheck_eq_true]
  constructor
  · rintro ⟨h1, h2 | h2, h3⟩
    · left
      exact ⟨List.length_eq_zero_iff.mp h2, List.length_eq_zero_iff.mp (h1 ▸ h2)⟩
    · right
      refine ⟨eq_replicate_zero_of_getD h2 (fun i hi => (h3 i (h2 ▸ hi)).1),
        eq_replicate_zero_of_getD (h1 ▸ h2) (fun i hi => (h3 i (h2 ▸ hi)).2)⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [h1, h2]
      exact ⟨rfl, Or.inl rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · rw [h1, h2]
      refine ⟨rfl, Or.inr (by simp), fun i _ => ⟨getD_replicate_zero _ _, getD_replicate_zero _ _⟩⟩

/-- The committer accepts an output whose linear-hash array has `16` entries only if both arrays are
sixteen zeros. -/
theorem committer_zero_of_length {o : DAOutput} (hc : committerDACheck o = true)
    (hl : o.blobsLinearHashes.length = TOTAL_BLOBS_IN_COMMITMENT) :
    o.blobsLinearHashes = List.replicate TOTAL_BLOBS_IN_COMMITMENT 0
      ∧ o.blobsOpeningCommitments = List.replicate TOTAL_BLOBS_IN_COMMITMENT 0 := by
  rcases (CommitterDACheckIff o).mp hc with ⟨h1, _⟩ | h
  · rw [h1] at hl; cases hl
  · exact h

/-- A padded linear-hash array that is all zero comes from all-zero words. -/
theorem lin_zero_of_padded {lin : List UInt256} {max : ℕ} (hle : lin.length ≤ max)
    (h : lin ++ List.replicate (max - lin.length) 0 = List.replicate max 0) :
    lin = List.replicate lin.length 0 := by
  have := congrArg (List.take lin.length) h
  rw [List.take_left' rfl, List.take_replicate, Nat.min_eq_left hle] at this
  exact this

theorem padded_length {lin : List UInt256} {max : ℕ} (hle : lin.length ≤ max) :
    (lin ++ List.replicate (max - lin.length) 0).length = max := by
  rw [List.length_append, List.length_replicate]; omega

theorem padded_replicate {n max : ℕ} (hn : n ≤ max) :
    List.replicate n (0 : UInt256) ++ List.replicate (max - (List.replicate n (0 : UInt256)).length) 0
      = List.replicate max 0 := by
  rw [List.length_replicate, ← List.replicate_add, Nat.add_sub_cancel' hn]

theorem toNat_eq_one {src : UInt8} (h : src.toNat = 1) : src = 1 :=
  UInt8.toNat_inj.mp (by rw [h]; rfl)

theorem toNat_eq_zero {src : UInt8} (h : src.toNat = 0) : src = 0 :=
  UInt8.toNat_inj.mp (by rw [h]; rfl)

theorem rollupPair_any_zero (max n m : ℕ) :
    (List.range max).any (fun i => rollupPairMismatch ((List.replicate n (0 : UInt256)).getD i 0)
      ((List.replicate m (0 : UInt256)).getD i 0)) = false := by
  rw [List.any_eq_false]
  intro i _
  rw [getD_replicate_zero, getD_replicate_zero]
  decide

theorem relayedPair_any_zero (max n m : ℕ) :
    (List.range max).any (fun i => relayedPairMismatch ((List.replicate n (0 : UInt256)).getD i 0)
      ((List.replicate m (0 : UInt256)).getD i 0)) = false := by
  rw [List.any_eq_false]
  intro i _
  rw [getD_replicate_zero, getD_replicate_zero]
  decide

/-! ## Inverting the rollup validator -/

set_option linter.unusedSimpArgs false in
/-- Inverting the L1 calldata branch. -/
theorem processCalldataDA_eq_some {keccak : Bytes → UInt256} {n : ℕ} {fp : UInt256} {max : ℕ}
    {rest : Bytes} {cs : List UInt256} {pub : Bytes}
    (h : processCalldataDA keccak n fp max rest = some (cs, pub)) :
    n = 1 ∧ BLOB_COMMITMENT_SIZE ≤ rest.length
      ∧ pub = rest.take (rest.length - BLOB_COMMITMENT_SIZE) ∧ pub.length ≤ BLOB_SIZE_BYTES
      ∧ fp = keccak pub ∧ max ≠ 0
      ∧ cs = (List.replicate max 0).set 0 (b32At rest (rest.length - BLOB_COMMITMENT_SIZE)) := by
  unfold processCalldataDA at h
  by_cases hn1 : n ≠ 1
  · simp only [hn1, ↓reduceIte, reduceCtorEq, ne_eq, not_false_eq_true, not_true_eq_false] at h
  by_cases hl : rest.length < BLOB_COMMITMENT_SIZE
  · simp only [hn1, hl, ↓reduceIte, reduceCtorEq, ne_eq, not_false_eq_true, not_true_eq_false] at h
  by_cases hs : BLOB_SIZE_BYTES < (rest.take (rest.length - BLOB_COMMITMENT_SIZE)).length
  · simp only [hn1, hl, hs, ↓reduceIte, reduceCtorEq, ne_eq, not_false_eq_true, not_true_eq_false] at h
  by_cases hf : fp ≠ keccak (rest.take (rest.length - BLOB_COMMITMENT_SIZE))
  · simp only [hn1, hl, hs, hf, ↓reduceIte, reduceCtorEq, ne_eq, not_false_eq_true, not_true_eq_false] at h
  by_cases hm : max = 0
  · simp only [hn1, hl, hs, hf, hm, ↓reduceIte, reduceCtorEq, ne_eq, not_false_eq_true,
      not_true_eq_false] at h
  simp only [hn1, hl, hs, hf, hm, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨not_not.mp hn1, Nat.le_of_not_lt hl, rfl, Nat.le_of_not_lt hs, not_not.mp hf, hm, rfl⟩

set_option linter.unusedSimpArgs false in
/-- Inverting the gateway calldata branch. -/
theorem processCalldataDAGateway_eq_some {keccak : Bytes → UInt256} {n : ℕ} {fp : UInt256}
    {max : ℕ} {rest : Bytes} {cs : List UInt256} {pub : Bytes}
    (h : processCalldataDAGateway keccak n fp max rest = some (cs, pub)) :
    n * BLOB_COMMITMENT_SIZE ≤ rest.length
      ∧ pub = rest.take (rest.length - n * BLOB_COMMITMENT_SIZE)
      ∧ pub.length ≤ n * BLOB_SIZE_BYTES ∧ fp = keccak pub
      ∧ cs = wordsAt (rest.drop (rest.length - n * BLOB_COMMITMENT_SIZE)) n max := by
  unfold processCalldataDAGateway at h
  by_cases hl : rest.length < n * BLOB_COMMITMENT_SIZE
  · simp only [hl, ↓reduceIte, reduceCtorEq, ne_eq, not_false_eq_true, not_true_eq_false] at h
  by_cases hs : n * BLOB_SIZE_BYTES < (rest.take (rest.length - n * BLOB_COMMITMENT_SIZE)).length
  · simp only [hl, hs, ↓reduceIte, reduceCtorEq, ne_eq, not_false_eq_true, not_true_eq_false] at h
  by_cases hf : fp ≠ keccak (rest.take (rest.length - n * BLOB_COMMITMENT_SIZE))
  · simp only [hl, hs, hf, ↓reduceIte, reduceCtorEq, ne_eq, not_false_eq_true, not_true_eq_false] at h
  simp only [hl, hs, hf, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨Nat.le_of_not_lt hl, rfl, Nat.le_of_not_lt hs, not_not.mp hf, rfl⟩


theorem rollupCheckDA_eq_some {K : Crypto} {env : TxEnv} {S : RollupState} {h : UInt256}
    {input : Bytes} {max : ℕ} {o : DAOutput} (hr : rollupCheckDA K env S h input max = some o) :
    ∃ (p : L2Parsed) (src : UInt8) (rest : Bytes) (cs : List UInt256),
      processL2 K.keccak h max input = some p ∧ p.l1DaInput = src :: rest
      ∧ ((src.toNat = 1 ∧ processBlobDA K env S p.blobsProvided max rest = some cs)
        ∨ (src.toNat = 0 ∧ ∃ pub, processCalldataDA K.keccak p.blobsProvided p.fullPubdataHash
            max rest = some (cs, pub)))
      ∧ o = ⟨p.stateDiffHash, p.blobsLinearHashes, cs⟩ := by
  unfold rollupCheckDA at hr
  cases hp : processL2 K.keccak h max input with
  | none => rw [hp] at hr; cases hr
  | some p =>
    rw [hp] at hr
    cases hl : p.l1DaInput with
    | nil => simp [hl] at hr
    | cons src rest =>
      simp only [hl] at hr
      by_cases h1 : src.toNat = 1
      · rw [ite_eq_left h1] at hr
        cases hb : processBlobDA K env S p.blobsProvided max rest with
        | none => simp [hb] at hr
        | some cs =>
          simp only [hb] at hr
          split_ifs at hr with hpair
          cases hr
          exact ⟨p, src, rest, cs, rfl, hl, Or.inl ⟨h1, hb⟩, rfl⟩
      · rw [ite_eq_right h1] at hr
        by_cases h0 : src.toNat = 0
        · rw [ite_eq_left h0] at hr
          cases hc : processCalldataDA K.keccak p.blobsProvided p.fullPubdataHash max rest with
          | none => simp [hc] at hr
          | some r =>
            obtain ⟨cs, pub⟩ := r
            simp only [hc, Option.map_some] at hr
            split_ifs at hr with hpair
            cases hr
            exact ⟨p, src, rest, cs, rfl, hl, Or.inr ⟨h0, pub, hc⟩, rfl⟩
        · rw [ite_eq_right h0] at hr
          cases hr

/-- The bytes after the prefix and the source byte of an accepted input. -/
theorem l1Rest_of_parsed {input : Bytes} {sd fp : UInt256} {lin : List UInt256} {src : UInt8}
    {rest : Bytes} (hinput : input = l2Output sd fp lin ++ src :: rest)
    (hplen : l2PrefixLen input = (l2Output sd fp lin).length) : l1Rest input = rest := by
  unfold l1Rest
  rw [hplen]
  conv_lhs => rw [hinput]
  rw [← List.drop_drop, List.drop_left]
  rfl

/-- The blob branch with at least one record: the first commitment is the first record's
prepublished word, or the commitment computed from `blobhash(0)`. -/
theorem blobLoop_succ_head {K : Crypto} {env : TxEnv} {S : RollupState} {k : ℕ} {rest : Bytes}
    {cs : List UInt256} {idx : ℕ} (h : blobLoop K env S (k + 1) rest 0 = some (cs, idx)) :
    (b32At rest PUBDATA_COMMITMENT_SIZE ≠ 0 ∧ cs.head? = some (b32At rest PUBDATA_COMMITMENT_SIZE))
      ∨ (cs.head? = some (blobCommitmentOf K (env.blobhash 0) (rest.take PUBDATA_COMMITMENT_SIZE))) := by
  unfold blobLoop at h
  by_cases hpre : b32At rest PUBDATA_COMMITMENT_SIZE ≠ 0
  · rw [ite_eq_left hpre] at h
    split_ifs at h with hav
    obtain ⟨r, _, hr⟩ := Option.map_eq_some_iff.mp h
    cases hr
    exact Or.inl ⟨hpre, rfl⟩
  · rw [ite_eq_right hpre] at h
    cases hg : getPublishedBlobCommitment K env 0 (rest.take PUBDATA_COMMITMENT_SIZE) with
    | none => rw [hg] at h; cases h
    | some c =>
      rw [hg] at h
      obtain ⟨r, _, hr⟩ := Option.map_eq_some_iff.mp h
      cases hr
      right
      unfold getPublishedBlobCommitment at hg
      split_ifs at hg
      cases hg
      rfl

theorem RollupAcceptedCases : Properties.RollupAcceptedCases := by
  rintro K env S h input ⟨o, hr, hc⟩
  obtain ⟨p, src, rest, cs, hp, hl, hbr, rfl⟩ := rollupCheckDA_eq_some hr
  obtain ⟨lin, hlinlen, hnmax, hinput, hpre, hplen, hk, hlin⟩ := processL2_eq_some hp
  rw [hl] at hinput
  have hmax : TOTAL_BLOBS_IN_COMMITMENT = 16 := rfl
  obtain ⟨hz1, hz2⟩ := committer_zero_of_length hc
    (by show p.blobsLinearHashes.length = _; rw [hlin]; exact padded_length (by omega))
  change p.blobsLinearHashes = _ at hz1
  change cs = _ at hz2
  have hlin0 : lin = List.replicate lin.length 0 := lin_zero_of_padded (by omega) (hlin ▸ hz1)
  have hrest : l1Rest input = rest := l1Rest_of_parsed hinput hplen
  rcases hbr with ⟨hs1, hb⟩ | ⟨hs0, pub, hcd⟩
  · -- the blob branch
    unfold processBlobDA at hb
    split_ifs at hb with hlen
    cases hloop : blobLoop K env S p.blobsProvided rest 0 with
    | none => rw [hloop] at hb; cases hb
    | some r =>
      obtain ⟨cs', idx⟩ := r
      rw [hloop] at hb
      simp only at hb
      split_ifs at hb with hidx
      cases hb
      rcases hn : p.blobsProvided with _ | k
      · -- no record: the zero-blob shape
        left
        rw [hn] at hloop hlen
        have hrest0 : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
        have hidx0 : idx = 0 := by
          simp only [blobLoop, Option.some.injEq, Prod.mk.injEq] at hloop
          exact hloop.2.symm
        have hlin_nil : lin = [] := List.eq_nil_of_length_eq_zero (by rw [hlinlen, hn])
        refine ⟨p.stateDiffHash, p.fullPubdataHash, ?_, ?_, ?_⟩
        · rw [hinput, hrest0, toNat_eq_one hs1, hlin_nil]
        · rw [← hidx0]; exact not_not.mp hidx
        · rw [← hk, hlin_nil]
      · -- at least one record: the first commitment must be zero
        right; right
        rw [hn] at hloop
        have hcs0 : (cs' ++ List.replicate (TOTAL_BLOBS_IN_COMMITMENT - p.blobsProvided) 0).head?
            = some 0 := by
          rw [hz2]; rfl
        rcases blobLoop_succ_head hloop with ⟨hpre0, hhd⟩ | hhd
        · exfalso
          rw [List.head?_append, hhd] at hcs0
          simp at hcs0
          exact hpre0 hcs0
        · rw [List.head?_append, hhd] at hcs0
          simp only [Option.some_or, Option.some.injEq] at hcs0
          unfold blobCommitmentOf at hcs0
          unfold firstBlobCommitmentPreimage
          rw [hrest, ← hcs0, List.take_take]
          rfl
  · -- the calldata branch
    right; left
    obtain ⟨hn, hlen32, rfl, hsize, hfp, _, rfl⟩ := processCalldataDA_eq_some hcd
    have hset : b32At rest (rest.length - BLOB_COMMITMENT_SIZE) = 0 := by
      have h0 : ((List.replicate TOTAL_BLOBS_IN_COMMITMENT (0 : UInt256)).set 0
          (b32At rest (rest.length - BLOB_COMMITMENT_SIZE))).getD 0 0
          = (List.replicate TOTAL_BLOBS_IN_COMMITMENT (0 : UInt256)).getD 0 0 := by rw [hz2]
      rw [getD_replicate_zero, List.getD_eq_getElem?_getD,
        List.getElem?_set_self (by simp [TOTAL_BLOBS_IN_COMMITMENT])] at h0
      simpa using h0
    have hlast : rest.drop (rest.length - BLOB_COMMITMENT_SIZE) = toB32 0 := by
      have hs := Contracts.ZKsyncOSCommitterDA.b32At_eq_zero_slice
        (x := rest) (off := rest.length - BLOB_COMMITMENT_SIZE)
        (by show rest.length - 32 + 32 ≤ rest.length; exact Nat.sub_add_cancel hlen32 ▸ le_refl _) hset
      rw [List.take_of_length_le (by
        rw [List.length_drop]; show rest.length - (rest.length - 32) ≤ 32; omega)] at hs
      exact hs
    have hrest_eq : rest = rest.take (rest.length - BLOB_COMMITMENT_SIZE) ++ toB32 0 := by
      rw [← hlast, List.take_append_drop]
    have hlin1 : lin = [0] := by
      rw [hlin0, hlinlen, hn]; rfl
    refine ⟨p.stateDiffHash, p.fullPubdataHash, rest.take (rest.length - BLOB_COMMITMENT_SIZE), ?_,
      hsize, hfp.symm, ?_⟩
    · rw [hinput, toNat_eq_zero hs0, hlin1]
      conv_lhs => rw [hrest_eq]
      simp
    · rw [← hk, hlin1]

/-! ## The two shapes are accepted -/

theorem rollupCheckDA_of_coms {K : Crypto} {env : TxEnv} {S : RollupState} {h : UInt256}
    {input : Bytes} {max : ℕ} {p : L2Parsed} {src : UInt8} {rest : Bytes} {cs : List UInt256}
    (hp : processL2 K.keccak h max input = some p) (hl : p.l1DaInput = src :: rest)
    (hc : (if src.toNat = 1 then processBlobDA K env S p.blobsProvided max rest
        else if src.toNat = 0 then
          (processCalldataDA K.keccak p.blobsProvided p.fullPubdataHash max rest).map Prod.fst
        else none) = some cs) :
    rollupCheckDA K env S h input max =
      if (List.range max).any (fun i =>
          rollupPairMismatch (p.blobsLinearHashes.getD i 0) (cs.getD i 0)) then none
      else some ⟨p.stateDiffHash, p.blobsLinearHashes, cs⟩ := by
  unfold rollupCheckDA
  rw [hp]
  simp only [hl]
  rw [hc]

theorem processBlobDA_none_attached {K : Crypto} {env : TxEnv} {S : RollupState} {max : ℕ}
    (h0 : env.blobhash 0 = 0) : processBlobDA K env S 0 max [] = some (List.replicate max 0) := by
  simp [processBlobDA, blobLoop, h0]

theorem processCalldataDA_form (keccak : Bytes → UInt256) {pub : Bytes} {max : ℕ}
    (hpub : pub.length ≤ BLOB_SIZE_BYTES) (hmax : max ≠ 0) :
    processCalldataDA keccak 1 (keccak pub) max (pub ++ toB32 0)
      = some (List.replicate max 0, pub) := by
  have hlen : (pub ++ toB32 0).length = pub.length + 32 := by
    rw [List.length_append, toB32_length]
  have htake : (pub ++ toB32 0).take ((pub ++ toB32 0).length - BLOB_COMMITMENT_SIZE) = pub := by
    rw [hlen, show pub.length + 32 - BLOB_COMMITMENT_SIZE = pub.length from by
      show pub.length + 32 - 32 = pub.length; omega]
    exact List.take_left' rfl
  have hlast : b32At (pub ++ toB32 0) ((pub ++ toB32 0).length - BLOB_COMMITMENT_SIZE) = 0 := by
    rw [hlen, show pub.length + 32 - BLOB_COMMITMENT_SIZE = pub.length + 0 from by
      show pub.length + 32 - 32 = pub.length + 0; omega, b32At_append_right]
    exact Contracts.ZKsyncOSBlobsDA.b32At_zero_toB32 0
  unfold processCalldataDA
  have h1 : ¬ (pub ++ toB32 0).length < BLOB_COMMITMENT_SIZE := by
    rw [hlen]; show ¬ _ < 32; omega
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, h1, htake, hlast, hmax, List.set_replicate_self]
  rw [ite_eq_right (by omega)]

/-- The zero-blob shape is accepted. -/
theorem rollupZeroBlob_accepted (K : Crypto) (env : TxEnv) (S : RollupState) (sd fp : UInt256)
    (h0 : env.blobhash 0 = 0) :
    RollupAccepted K env S (K.keccak (l2Output sd fp [])) (l2Output sd fp [] ++ [1]) := by
  refine ⟨⟨sd, List.replicate 16 0, List.replicate 16 0⟩, ?_, ?_⟩
  · have hp := processL2_l2Output K.keccak sd fp (lin := []) [1]
      (max := TOTAL_BLOBS_IN_COMMITMENT) (by simp) (by simp)
    have hpad : ([] : List UInt256)
        ++ List.replicate (TOTAL_BLOBS_IN_COMMITMENT - ([] : List UInt256).length) 0
        = List.replicate 16 0 := rfl
    rw [hpad] at hp
    have hc : (if (1 : UInt8).toNat = 1 then processBlobDA K env S ([] : List UInt256).length
          TOTAL_BLOBS_IN_COMMITMENT []
        else if (1 : UInt8).toNat = 0 then
          (processCalldataDA K.keccak ([] : List UInt256).length fp TOTAL_BLOBS_IN_COMMITMENT []).map
            Prod.fst
        else none) = some (List.replicate 16 0) := by
      rw [ite_eq_left (show (1 : UInt8).toNat = 1 from rfl)]
      exact processBlobDA_none_attached h0
    rw [rollupCheckDA_of_coms hp rfl hc, rollupPair_any_zero]
    rfl
  · exact (CommitterDACheckIff _).mpr (Or.inr ⟨rfl, rfl⟩)

/-- The calldata shape is accepted. -/
theorem rollupCalldata_accepted (K : Crypto) (env : TxEnv) (S : RollupState) (sd : UInt256) (pub : Bytes)
    (hpub : pub.length ≤ BLOB_SIZE_BYTES) :
    RollupAccepted K env S (K.keccak (l2Output sd (K.keccak pub) [0]))
      (l2Output sd (K.keccak pub) [0] ++ [0] ++ pub ++ toB32 0) := by
  refine ⟨⟨sd, List.replicate 16 0, List.replicate 16 0⟩, ?_, ?_⟩
  · have hp := processL2_l2Output K.keccak sd (K.keccak pub) (lin := [0]) (0 :: (pub ++ toB32 0))
      (max := TOTAL_BLOBS_IN_COMMITMENT) (by simp [TOTAL_BLOBS_IN_COMMITMENT]) (by simp)
    have hpad : [(0 : UInt256)] ++ List.replicate (TOTAL_BLOBS_IN_COMMITMENT - [(0 : UInt256)].length) 0
        = List.replicate 16 0 := rfl
    rw [hpad] at hp
    have heq : l2Output sd (K.keccak pub) [0] ++ [0] ++ pub ++ toB32 0
        = l2Output sd (K.keccak pub) [0] ++ 0 :: (pub ++ toB32 0) := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    have hc : (if (0 : UInt8).toNat = 1 then processBlobDA K env S [(0 : UInt256)].length
          TOTAL_BLOBS_IN_COMMITMENT (pub ++ toB32 0)
        else if (0 : UInt8).toNat = 0 then
          (processCalldataDA K.keccak [(0 : UInt256)].length (K.keccak pub) TOTAL_BLOBS_IN_COMMITMENT
            (pub ++ toB32 0)).map Prod.fst
        else none) = some (List.replicate 16 0) := by
      rw [ite_eq_right (show ¬ (0 : UInt8).toNat = 1 by decide),
        ite_eq_left (show (0 : UInt8).toNat = 0 from rfl), List.length_singleton,
        processCalldataDA_form K.keccak hpub (by decide)]
      rfl
    rw [heq, rollupCheckDA_of_coms hp rfl hc, rollupPair_any_zero]
    rfl
  · exact (CommitterDACheckIff _).mpr (Or.inr ⟨rfl, rfl⟩)

theorem RollupFormsAccepted : Properties.RollupFormsAccepted := by
  intro K env S h input hf
  rcases hf with ⟨sd, fp, hi, h0, hh⟩ | ⟨sd, fp, pub, hi, hpub, hfp, hh⟩
  · rw [hi, hh]
    exact rollupZeroBlob_accepted K env S sd fp h0
  · rw [hi, hh, ← hfp]
    exact rollupCalldata_accepted K env S sd pub hpub

theorem RollupAcceptedIff : Properties.RollupAcceptedIff := by
  intro K env S h input hz
  constructor
  · intro ha
    rcases RollupAcceptedCases K env S h input ha with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd h1 hz
  · exact RollupFormsAccepted K env S h input

/-! ## The rollup headline and its two countermodels -/

theorem zeroBlob_shape_parts (sd fp : UInt256) :
    l2Prefix (l2Output sd fp [] ++ [1]) = l2Output sd fp []
      ∧ l1Rest (l2Output sd fp [] ++ [1]) = [] := by
  refine ⟨l2Prefix_l2Output sd fp [1] (by simp), ?_⟩
  unfold l1Rest
  rw [l2PrefixLen_l2Output sd fp [1] (by simp), ← List.drop_drop, List.drop_left]
  rfl

theorem calldata_shape_parts (sd fp : UInt256) (pub : Bytes) :
    l2Prefix (l2Output sd fp [0] ++ [0] ++ pub ++ toB32 0) = l2Output sd fp [0]
      ∧ l1Rest (l2Output sd fp [0] ++ [0] ++ pub ++ toB32 0) = pub ++ toB32 0
      ∧ calldataPubdata (l2Output sd fp [0] ++ [0] ++ pub ++ toB32 0) = pub := by
  have heq : l2Output sd fp [0] ++ [0] ++ pub ++ toB32 0
      = l2Output sd fp [0] ++ (0 :: (pub ++ toB32 0)) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hrest : l1Rest (l2Output sd fp [0] ++ [0] ++ pub ++ toB32 0) = pub ++ toB32 0 := by
    unfold l1Rest
    rw [heq, l2PrefixLen_l2Output sd fp _ (by simp), ← List.drop_drop, List.drop_left]
    rfl
  refine ⟨by rw [heq]; exact l2Prefix_l2Output sd fp _ (by simp), hrest, ?_⟩
  unfold calldataPubdata
  rw [hrest, List.length_append, toB32_length,
    show pub.length + 32 - BLOB_COMMITMENT_SIZE = pub.length from by
      show pub.length + 32 - 32 = pub.length; omega]
  exact List.take_left' rfl

theorem l2Output_ne_of_length {sd fp sd' fp' : UInt256} {lin lin' : List UInt256}
    (h : lin.length ≠ lin'.length) : l2Output sd fp lin ≠ l2Output sd' fp' lin' := by
  intro he
  have := congrArg List.length he
  rw [l2Output_length, l2Output_length] at this
  omega

theorem RollupPubdataPublishedOrCollision : Properties.RollupPubdataPublishedOrCollision := by
  intro K env S sd lin pub input hprog ha
  by_cases hpub : pub = []
  · exact Or.inl hpub
  have hlin : lin ≠ [] := hprog hpub
  right
  rcases RollupAcceptedCases K env S _ input ha with
    ⟨sd', fp', hi, _, hh⟩ | ⟨sd', fp', pub', hi, _, hfp, hh⟩ | hz
  · -- the zero-blob shape: the prefix is shorter than the program's preimage
    right; left
    have hpre : l2Prefix input = l2Output sd' fp' [] := by
      rw [hi]; exact (zeroBlob_shape_parts sd' fp').1
    rw [hpre]
    refine ⟨l2Output_ne_of_length ?_, hh.symm⟩
    intro hl
    exact hlin (List.eq_nil_of_length_eq_zero hl.symm)
  · -- the calldata shape
    obtain ⟨hpre, _, hcd⟩ := calldata_shape_parts sd' fp' pub'
    rw [← hi] at hpre hcd
    by_cases heq : l2Output sd' fp' [0] = l2Output sd (K.keccak pub) lin
    · have hfp' : fp' = K.keccak pub := l2Output_fp_eq heq
      by_cases hp' : pub' = pub
      · left
        rw [← hp']
        exact ⟨sd', fp', hi⟩
      · right; right; left
        rw [hcd]
        exact ⟨hp', hfp.trans hfp'⟩
    · right; left
      rw [hpre]
      exact ⟨heq, hh.symm⟩
  · right; right; right
    exact hz

theorem RollupZeroBlobAcceptsUnpublishedPubdata :
    Properties.RollupZeroBlobAcceptsUnpublishedPubdata := by
  intro K S sd pub
  refine ⟨rollupZeroBlob_accepted K ⟨[]⟩ S sd (K.keccak pub) rfl, ?_, ?_⟩
  · rw [List.length_append, l2Output_length]; rfl
  · rintro ⟨sd', fp', he⟩
    have := congrArg List.length he
    simp only [List.length_append, l2Output_length, List.length_singleton, List.length_nil,
      toB32_length] at this
    omega

/-- A keccak stand-in that is nonzero on every input shorter than `2^256 - 1` bytes: one plus the
length. Its precompile oracle accepts every input. -/
def lengthHash : Crypto := ⟨fun b => Nat.toUInt256 (b.length + 1), fun _ => true⟩

/-- The instance: `lengthHash`, pubdata `[7]`, the zero-blob commitment to it, and the 66-byte
zero-blob input from a transaction with no blob. -/
theorem RollupProgramPremiseLoadBearing : Properties.RollupProgramPremiseLoadBearing := by
  refine ⟨lengthHash, ⟨[]⟩, ⟨fun _ => 0, 0⟩, 0, [7],
    l2Output 0 (lengthHash.keccak [7]) [] ++ [1], by simp,
    rollupZeroBlob_accepted _ _ _ 0 _ rfl, ?_⟩
  obtain ⟨hpre, hrest⟩ := zeroBlob_shape_parts 0 (lengthHash.keccak [7])
  rintro (h | ⟨sd', fp', he⟩ | ⟨hne, _⟩ | ⟨_, hk⟩ | hz)
  · simp at h
  · have := congrArg List.length he
    simp only [List.length_append, l2Output_length, List.length_singleton, List.length_nil,
      toB32_length] at this
    omega
  · exact hne hpre
  · have hcd : calldataPubdata (l2Output 0 (lengthHash.keccak [7]) [] ++ [1]) = [] := by
      unfold calldataPubdata; rw [hrest]; rfl
    rw [hcd] at hk
    exact absurd hk (by decide +kernel)
  · unfold firstBlobCommitmentPreimage at hz
    rw [hrest] at hz
    exact absurd hz (by decide +kernel)

/-- The one-record blob input of `CommitterZeroCheckLoadBearing`: the prefix with one nonzero linear
hash `3`, the blob source byte, and one 176-byte record of zeros (prepublished word zero). -/
def oneRecordInput : Bytes :=
  l2Output 0 (lengthHash.keccak [7]) [3] ++ [1] ++ List.replicate 176 0

/-- The instance: `lengthHash`, pubdata `[7]`, the commitment with the one linear hash `3`, a
transaction carrying blob `5`, and `oneRecordInput`. The record's commitment is
`keccak (blobhash(0) ‖ record[0:48])`, of length 80, so `81`. -/
theorem CommitterZeroCheckLoadBearing : Properties.CommitterZeroCheckLoadBearing := by
  refine ⟨lengthHash, ⟨[5]⟩, ⟨fun _ => 0, 0⟩, 0, 3, [7], oneRecordInput,
    ⟨0, 3 :: List.replicate 15 0, 81 :: List.replicate 15 0⟩, by decide, by simp,
    by decide +kernel, rfl, rfl, by decide +kernel, ?_⟩
  have hpre : l2Prefix oneRecordInput = l2Output 0 (lengthHash.keccak [7]) [3] := by
    decide +kernel
  rintro (h | ⟨sd', fp', he⟩ | ⟨hne, _⟩ | ⟨_, hk⟩ | hz)
  · simp at h
  · have := congrArg List.length he
    simp only [oneRecordInput, List.length_append, l2Output_length, List.length_cons,
      List.length_nil, toB32_length, List.length_replicate] at this
    omega
  · exact hne hpre
  · exact absurd hk (by decide +kernel)
  · exact absurd hz (by decide +kernel)

/-! ## The gateway validator -/

theorem relayedCheckDA_eq_some {K : Crypto} {G : GatewayEnv} {caller chainId batchNumber h : UInt256}
    {input : Bytes} {max : ℕ} {o : DAOutput} {msg : RelayMessage}
    (hr : relayedCheckDA K G caller chainId batchNumber h input max = some (o, msg)) :
    G.getZKChain chainId = caller ∧
    ∃ (p : L2Parsed) (src : UInt8) (rest : Bytes) (cs : List UInt256) (pub : Bytes),
      processL2 K.keccak h max input = some p ∧ p.l1DaInput = src :: rest ∧ src.toNat = 0
      ∧ processCalldataDAGateway K.keccak p.blobsProvided p.fullPubdataHash max rest
          = some (cs, pub)
      ∧ o = ⟨p.stateDiffHash, p.blobsLinearHashes, cs⟩
      ∧ msg = ⟨RELAYED_SL_DA_VALIDATOR_VERSION, chainId, batchNumber, pub⟩ := by
  unfold relayedCheckDA at hr
  by_cases hcall : G.getZKChain chainId ≠ caller
  · rw [ite_eq_left hcall] at hr; cases hr
  rw [ite_eq_right hcall] at hr
  refine ⟨not_not.mp hcall, ?_⟩
  cases hp : processL2 K.keccak h max input with
  | none => rw [hp] at hr; cases hr
  | some p =>
    rw [hp] at hr
    cases hl : p.l1DaInput with
    | nil => simp [hl] at hr
    | cons src rest =>
      simp only [hl] at hr
      by_cases h0 : src.toNat ≠ 0
      · rw [ite_eq_left h0] at hr; cases hr
      rw [ite_eq_right h0] at hr
      cases hg : processCalldataDAGateway K.keccak p.blobsProvided p.fullPubdataHash max rest with
      | none => rw [hg] at hr; cases hr
      | some r =>
        obtain ⟨cs, pub⟩ := r
        rw [hg] at hr
        simp only at hr
        split_ifs at hr with hpair
        cases hr
        exact ⟨p, src, rest, cs, pub, rfl, hl, not_not.mp h0, hg, rfl, rfl⟩

theorem relayedCheckDA_of_parts {K : Crypto} {G : GatewayEnv}
    {caller chainId batchNumber h : UInt256} {input : Bytes} {max : ℕ} {p : L2Parsed}
    {src : UInt8} {rest : Bytes} {cs : List UInt256} {pub : Bytes}
    (hcall : G.getZKChain chainId = caller) (hp : processL2 K.keccak h max input = some p)
    (hl : p.l1DaInput = src :: rest) (hs : src.toNat = 0)
    (hg : processCalldataDAGateway K.keccak p.blobsProvided p.fullPubdataHash max rest
      = some (cs, pub)) :
    relayedCheckDA K G caller chainId batchNumber h input max =
      if (List.range max).any (fun i =>
          relayedPairMismatch (p.blobsLinearHashes.getD i 0) (cs.getD i 0)) then none
      else some (⟨p.stateDiffHash, p.blobsLinearHashes, cs⟩,
        ⟨RELAYED_SL_DA_VALIDATOR_VERSION, chainId, batchNumber, pub⟩) := by
  unfold relayedCheckDA
  rw [ite_eq_right (not_not.mpr hcall), hp]
  simp only [hl]
  rw [ite_eq_right (not_not.mpr hs), hg]

theorem processCalldataDAGateway_form (keccak : Bytes → UInt256) {pub : Bytes} {n max : ℕ}
    (hn : n ≤ max) (hpub : pub.length ≤ n * BLOB_SIZE_BYTES) :
    processCalldataDAGateway keccak n (keccak pub) max (pub ++ encWords (List.replicate n 0))
      = some (List.replicate max 0, pub) := by
  have hlen : (pub ++ encWords (List.replicate n 0)).length = pub.length + n * BLOB_COMMITMENT_SIZE := by
    rw [List.length_append, encWords_length, List.length_replicate]
    show _ = pub.length + n * 32
    ring
  have hcut : (pub ++ encWords (List.replicate n 0)).length - n * BLOB_COMMITMENT_SIZE = pub.length := by
    rw [hlen]; omega
  have hwords : wordsAt (encWords (List.replicate n 0)) n max = List.replicate max 0 := by
    rw [wordsAt_eq _ hn]
    have hmap : (List.range n).map (fun i => b32At (encWords (List.replicate n (0 : UInt256))) (32 * i))
        = List.replicate n 0 := by
      apply List.ext_getElem (by simp)
      intro i h1 _
      simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
      have := b32At_encWords_append (List.replicate n (0 : UInt256)) [] i (by simpa using h1)
      rw [List.append_nil, getD_replicate_zero] at this
      exact this
    rw [hmap, ← List.replicate_add, Nat.add_sub_cancel' hn]
  unfold processCalldataDAGateway
  have h1 : ¬ (pub ++ encWords (List.replicate n 0)).length < n * BLOB_COMMITMENT_SIZE := by
    rw [hlen]; omega
  simp only [h1, ↓reduceIte, hcut, List.take_left', List.drop_left, hwords]
  rw [ite_eq_right (by omega), ite_eq_right (not_not.mpr rfl)]

theorem RelayedAcceptedIff : Properties.RelayedAcceptedIff := by
  intro K G caller chainId batchNumber h input msg
  constructor
  · rintro ⟨o, hr, hc⟩
    obtain ⟨hcall, p, src, rest, cs, pub, hp, hl, hs, hg, rfl, rfl⟩ := relayedCheckDA_eq_some hr
    obtain ⟨lin, hlinlen, hnmax, hinput, _, _, hk, hlin⟩ := processL2_eq_some hp
    rw [hl] at hinput
    obtain ⟨hz1, hz2⟩ := committer_zero_of_length hc
      (by show p.blobsLinearHashes.length = _; rw [hlin]; exact padded_length (by omega))
    change p.blobsLinearHashes = _ at hz1
    change cs = _ at hz2
    have hlin0 : lin = List.replicate lin.length 0 := lin_zero_of_padded (by omega) (hlin ▸ hz1)
    obtain ⟨hlen, hpub, hsize, hfp, hcs⟩ := processCalldataDAGateway_eq_some hg
    set n := p.blobsProvided with hn
    set prov := rest.drop (rest.length - n * BLOB_COMMITMENT_SIZE) with hprov
    have hlen' : n * 32 ≤ rest.length := hlen
    have hprovlen : prov.length = 32 * n := by
      rw [hprov, List.length_drop]; show rest.length - (rest.length - n * 32) = 32 * n; omega
    have hprov0 : prov = encWords (List.replicate n 0) := by
      have hmap : (List.range n).map (fun i => b32At prov (32 * i)) = List.replicate n 0 := by
        apply List.ext_getElem (by simp)
        intro i h1 _
        simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
        have hi : i < n := by simpa using h1
        have := congrArg (fun l : List UInt256 => l.getD i 0) (hcs.symm.trans hz2)
        simp only [wordsAt, getD_replicate_zero] at this
        rw [getD_of_lt (by simp; omega), List.getElem_map, List.getElem_range,
          ite_eq_left hi] at this
        exact this
      rw [← hmap, encWords_map_range (by omega), List.take_of_length_le (by omega)]
    have hrest : rest = pub ++ encWords (List.replicate n 0) := by
      rw [hpub, ← hprov0, hprov, List.take_append_drop]
    refine ⟨hcall, p.stateDiffHash, p.fullPubdataHash, n, pub, by omega, ?_, hsize, hfp.symm, ?_, rfl⟩
    · rw [hinput, toNat_eq_zero hs, hrest, hlin0, hlinlen]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    · rw [← hk, hlin0, hlinlen]
  · rintro ⟨hcall, sd, fp, n, pub, hn, hi, hpub, hfp, hh, hmsg⟩
    refine ⟨⟨sd, List.replicate 16 0, List.replicate 16 0⟩, ?_, ?_⟩
    · have hp := processL2_l2Output K.keccak sd fp (lin := List.replicate n 0)
        (0 :: (pub ++ encWords (List.replicate n 0))) (max := TOTAL_BLOBS_IN_COMMITMENT)
        (by simpa using hn) (by simp [TOTAL_BLOBS_IN_COMMITMENT] at hn ⊢; omega)
      rw [padded_replicate hn, List.length_replicate] at hp
      have heq : input
          = l2Output sd fp (List.replicate n 0) ++ (0 :: (pub ++ encWords (List.replicate n 0))) := by
        rw [hi]; simp only [List.append_assoc, List.cons_append, List.nil_append]
      have hg := processCalldataDAGateway_form K.keccak hn hpub
      rw [hfp] at hg
      rw [heq, hh, relayedCheckDA_of_parts hcall hp rfl rfl hg, relayedPair_any_zero, hmsg]
      rfl
    · exact (CommitterDACheckIff _).mpr (Or.inr ⟨rfl, rfl⟩)

theorem RelayedPubdataRelayedOrCollision : Properties.RelayedPubdataRelayedOrCollision := by
  intro K G caller chainId batchNumber sd lin pub input msg ha
  obtain ⟨_, sd', fp', n, pub', hn, hi, _, hfp, hh, hmsg⟩ :=
    (RelayedAcceptedIff K G caller chainId batchNumber _ input msg).mp ha
  rw [hmsg]
  refine ⟨rfl, rfl, ?_⟩
  have hpre : l2Prefix input = l2Output sd' fp' (List.replicate n 0) := by
    have heq : input = l2Output sd' fp' (List.replicate n 0)
        ++ (0 :: (pub' ++ encWords (List.replicate n 0))) := by
      rw [hi]; simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [heq]
    exact l2Prefix_l2Output sd' fp' _ (by simp [TOTAL_BLOBS_IN_COMMITMENT] at hn ⊢; omega)
  by_cases heq : l2Output sd' fp' (List.replicate n 0) = l2Output sd (K.keccak pub) lin
  · have hfp' : fp' = K.keccak pub := l2Output_fp_eq heq
    by_cases hp' : pub' = pub
    · exact Or.inl hp'
    · exact Or.inr (Or.inr ⟨hp', hfp.trans hfp'⟩)
  · right; left
    rw [hpre]
    exact ⟨heq, hh.symm⟩

/-! ## The validium validator -/

theorem ValidiumAcceptedIff : Properties.ValidiumAcceptedIff := by
  intro input
  unfold ValidiumAccepted validiumCheckDA
  constructor
  · rintro ⟨o, ho, _⟩
    by_contra hne
    rw [ite_eq_left hne] at ho
    cases ho
  · intro hl
    rw [ite_eq_right (not_not.mpr hl)]
    exact ⟨_, rfl, (CommitterDACheckIff _).mpr (Or.inr ⟨rfl, rfl⟩)⟩

/-! ## The ZKsync OS blobs validator -/

theorem BlobsAcceptedIffCheckDA : Properties.BlobsAcceptedIffCheckDA := by
  intro K env S h input
  unfold BlobsAccepted
  constructor
  · rintro ⟨o, ho, _⟩
    exact ⟨o, ho⟩
  · rintro ⟨o, ho⟩
    have := (Contracts.ZKsyncOSBlobsDA.BlobsCheckDAAcceptsIff K.keccak env S h input o).mp ho
    refine ⟨o, ho, ?_⟩
    rw [this.2.2.2.2.2]
    rfl

theorem BlobsCommittedHashesFreshOrCollision :
    Properties.BlobsCommittedHashesFreshOrCollision := by
  intro K env W vs input hr ha
  obtain ⟨o, ho, _⟩ := ha
  rcases Contracts.ZKsyncOSBlobsDA.BlobsAcceptedBindsOrCollision K.keccak env W.st input vs o ho
    with he | hcol
  · left
    intro v hv
    rw [← he] at hv
    obtain ⟨i, hi, rfl⟩ := Contracts.ZKsyncOSBlobsDA.mem_iff_getD.mp hv
    have hi' : i < (Contracts.ZKsyncOSBlobsDA.inputWords input).length := by
      unfold resolvedHashes at hi
      rwa [Contracts.ZKsyncOSBlobsDA.resolveWords_length] at hi
    obtain ⟨hnz, hz⟩ := Contracts.ZKsyncOSBlobsDA.BlobsAcceptedHashesFresh K.keccak env W _ input o
      hr ho i hi'
    by_cases hw : (Contracts.ZKsyncOSBlobsDA.inputWords input).getD i 0 = 0
    · exact Or.inl (hz hw)
    · obtain ⟨heq, hlog⟩ := hnz hw
      rw [heq]
      exact Or.inr hlog
  · exact Or.inr hcol

/-! ## Witnesses -/

/-- The calldata input of the witnesses: blob count 1, zero linear hash, the pubdata `[7]`, a zero
commitment. -/
def calldataWitnessInput : Bytes :=
  l2Output 0 (lengthHash.keccak [7]) [0] ++ [0] ++ [7] ++ toB32 0

/-- The instance: `lengthHash`, pubdata `[7]`, `lin = [0]`, and `calldataWitnessInput`. -/
theorem RollupHeadlineWitness : Properties.RollupHeadlineWitness := by
  obtain ⟨hpre, _, hcd⟩ := calldata_shape_parts 0 (lengthHash.keccak [7]) [7]
  refine ⟨lengthHash, ⟨[]⟩, ⟨fun _ => 0, 0⟩, 0, [0], [7], calldataWitnessInput, by simp, by simp,
    rollupCalldata_accepted _ _ _ 0 [7] (by decide), ⟨0, lengthHash.keccak [7], rfl⟩, ?_, ?_, ?_⟩
  · rintro ⟨hne, _⟩
    exact hne hpre
  · rintro ⟨hne, _⟩
    exact hne hcd
  · decide +kernel

/-- The instance: the constant hash `0`, pubdata `[7]`, `lin = [0]`, and the zero-blob input
`l2Output 0 0 [] ++ [1]`, whose 65-byte prefix differs from the 97-byte program preimage. -/
theorem RollupHeadlineCollisionFires : Properties.RollupHeadlineCollisionFires := by
  let K0 : Crypto := ⟨fun _ => 0, fun _ => true⟩
  refine ⟨K0, ⟨[]⟩, ⟨fun _ => 0, 0⟩, 0, [0], [7], l2Output 0 0 [] ++ [1], by simp, by simp,
    rollupZeroBlob_accepted K0 ⟨[]⟩ _ 0 0 rfl, ?_, ?_⟩
  · rintro ⟨sd', fp', he⟩
    have := congrArg List.length he
    simp only [List.length_append, l2Output_length, List.length_singleton, List.length_nil,
      toB32_length] at this
    omega
  · rw [(zeroBlob_shape_parts 0 0).1]
    exact ⟨l2Output_ne_of_length (by simp), rfl⟩

/-- The instance: `lengthHash`, the zero-blob input `l2Output 0 0 [] ++ [1]` and
`calldataWitnessInput`. -/
theorem RollupFormsWitness : Properties.RollupFormsWitness := by
  obtain ⟨_, _, hcd⟩ := calldata_shape_parts 0 (lengthHash.keccak [7]) [7]
  refine ⟨lengthHash, ⟨fun _ => 0, 0⟩, lengthHash.keccak (l2Output 0 0 []),
    lengthHash.keccak (l2Output 0 (lengthHash.keccak [7]) [0]), l2Output 0 0 [] ++ [1],
    calldataWitnessInput, by decide +kernel, by decide +kernel,
    ⟨0, 0, rfl, rfl, rfl⟩, rollupZeroBlob_accepted _ _ _ 0 0 rfl,
    ⟨0, lengthHash.keccak [7], [7], rfl, by decide, rfl, rfl⟩,
    rollupCalldata_accepted _ _ _ 0 [7] (by decide), ?_⟩
  unfold calldataWitnessInput
  rw [hcd]
  simp

/-- The gateway input of the witness: blob count 1, zero linear hash, the calldata source byte, the
pubdata `[7]`, one zero commitment. -/
def relayedWitnessInput : Bytes :=
  l2Output 0 (lengthHash.keccak [7]) (List.replicate 1 0) ++ [0] ++ [7]
    ++ encWords (List.replicate 1 0)

/-- The instance: `lengthHash`, a bridgehub that reports the caller `1` for every chain, chain `2`,
batch `3`, pubdata `[7]`, `lin = [0]`, and `relayedWitnessInput`. -/
theorem RelayedHeadlineWitness : Properties.RelayedHeadlineWitness := by
  have hform : RelayedForm lengthHash ⟨fun _ => 1⟩ 1 2 3
      (lengthHash.keccak (l2Output 0 (lengthHash.keccak [7]) (List.replicate 1 0)))
      relayedWitnessInput ⟨RELAYED_SL_DA_VALIDATOR_VERSION, 2, 3, [7]⟩ :=
    ⟨rfl, 0, lengthHash.keccak [7], 1, [7], by decide, rfl, by decide, rfl, rfl, rfl⟩
  have hpre : l2Prefix relayedWitnessInput = l2Output 0 (lengthHash.keccak [7]) (List.replicate 1 0) := by
    decide +kernel
  refine ⟨lengthHash, ⟨fun _ => 1⟩, 1, 2, 3, 0, List.replicate 1 0, [7], relayedWitnessInput,
    ⟨RELAYED_SL_DA_VALIDATOR_VERSION, 2, 3, [7]⟩, by simp, by simp,
    (RelayedAcceptedIff _ _ _ _ _ _ _ _).mpr hform, rfl, ?_, ?_⟩
  · rintro ⟨hne, _⟩
    exact hne hpre
  · rintro ⟨hne, _⟩
    exact hne rfl

/-- The instance: the constant hash `0`, a bridgehub that reports the caller `1`, pubdata `[7]`,
`lin = [0]`, and a gateway input relaying `[8]`. -/
theorem RelayedCollisionFires : Properties.RelayedCollisionFires := by
  let K0 : Crypto := ⟨fun _ => 0, fun _ => true⟩
  have hform : RelayedForm K0 ⟨fun _ => 1⟩ 1 2 3
      (K0.keccak (l2Output 0 (K0.keccak [7]) (List.replicate 1 0)))
      (l2Output 0 0 (List.replicate 1 0) ++ [0] ++ [8] ++ encWords (List.replicate 1 0))
      ⟨RELAYED_SL_DA_VALIDATOR_VERSION, 2, 3, [8]⟩ :=
    ⟨rfl, 0, 0, 1, [8], by decide, rfl, by decide, rfl, rfl, rfl⟩
  exact ⟨K0, ⟨fun _ => 1⟩, 1, 2, 3, 0, List.replicate 1 0, [7],
    l2Output 0 0 (List.replicate 1 0) ++ [0] ++ [8] ++ encWords (List.replicate 1 0),
    ⟨RELAYED_SL_DA_VALIDATOR_VERSION, 2, 3, [8]⟩, by simp, by simp,
    (RelayedAcceptedIff _ _ _ _ _ _ _ _).mpr hform, by decide, by decide, rfl⟩

/-- The instance: the world `demoWorld [7] 10` (hash `7` published at block 1, now block 10), a
transaction carrying blob `9`, `vs = [7, 9]` and the input `[7, 0]`. -/
theorem BlobsHeadlineWitness : Properties.BlobsHeadlineWitness := by
  intro K
  have hatt : Contracts.ZKsyncOSBlobsDA.attached ⟨[7]⟩ = [7] := by decide
  have h7 : (7 : UInt256) ∈ Contracts.ZKsyncOSBlobsDA.attached ⟨[7]⟩ := by rw [hatt]; simp
  have hres : resolvedHashes ⟨[9]⟩ (toB32 7 ++ toB32 0) = [7, 9] := by
    unfold resolvedHashes
    rw [Contracts.ZKsyncOSBlobsDA.inputWords_two]
    decide
  refine ⟨⟨[9]⟩, Contracts.ZKsyncOSBlobsDA.demoWorld [7] 10, [7, 9], toB32 7 ++ toB32 0,
    Contracts.ZKsyncOSBlobsDA.demoWorld_reachable _ (by omega), rfl, by simp,
    (BlobsAcceptedIffCheckDA _ _ _ _ _).mpr
      ⟨_, Contracts.ZKsyncOSBlobsDA.blobs_demo_accept K.keccak [7] h7⟩, ?_, ?_⟩
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · right
      refine ⟨(1, [7]), ?_, by simp, Nat.one_pos, by
        show 1 ≤ 10; omega, by
        show 10 - 1 ≤ Contracts.ZKsyncOSBlobsDA.BLOB_EXPIRATION_BLOCKS
        simp [Contracts.ZKsyncOSBlobsDA.BLOB_EXPIRATION_BLOCKS]⟩
      show (1, [(7 : UInt256)]) ∈ [(1, Contracts.ZKsyncOSBlobsDA.attached ⟨[7]⟩)]
      rw [hatt]; simp
    · left
      exact ⟨by simp, by decide⟩
  · rw [hres]
    rintro ⟨hne, _⟩
    exact hne rfl

end Contracts.ZKsyncOSCommitterDA
