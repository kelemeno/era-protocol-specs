import EraSpec.Contracts.L2MessageVerification.Properties.Verification
import EraSpec.Contracts.L2InteropRootStorage.Proofs.Storage

/-!
# Proofs: `L2MessageVerification`

The structural fact is `prove_eq_anchor_map`: `proveRecursive` and `anchorRec` have the same
recursion, and the verdict reads the storage only in the final comparison.  Every non-final step
moves the proof pointer by at least five words and stays inside the proof
(`getProofData_nonfinal_ptr`), which gives fuel independence (`anchorRec_fuel`) and, at depth 0,
the two-step closed form `anchor_zero_eq`.  The storage-run results combine the first with
`L2InteropRootStorage`'s `no_overwrite` and `storage_is_the_log`.
-/

namespace Contracts.MessageVerification

open Contracts.InteropRootStorage

/-! ### Small facts about the parse -/

lemma parseProofMetadata_nonfinal {proof : List UInt256} {md : ProofMetadata}
    (h : parseProofMetadata proof = some md) (hf : md.finalProofNode = false) :
    md.proofStartIndex = 1 := by
  unfold parseProofMetadata at h
  split at h
  · exact absurd h (by simp)
  · split_ifs at h
    · obtain rfl := (Option.some.inj h).symm
      rfl
    · obtain rfl := (Option.some.inj h).symm
      simp at hf

lemma getProofData_empty (H : Hashes) (c b m leaf : UInt256) {proof : List UInt256}
    (h0 : proof.length = 0) : getProofData H c b m leaf proof = none := by
  unfold getProofData
  exact ite_eq_left h0

lemma getProofData_length {H : Hashes} {c b m leaf : UInt256} {proof : List UInt256}
    {pd : ProofData} (h : getProofData H c b m leaf proof = some pd) : proof.length ≠ 0 := by
  intro h0
  rw [getProofData_empty H c b m leaf h0] at h
  exact absurd h (by simp)

/-- `getProofData` past its two leading reverts. -/
lemma getProofData_eq_bind {H : Hashes} {c b m leaf : UInt256} {proof : List UInt256}
    (hlen : proof.length ≠ 0) (hleaf : leaf ≠ L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH) :
    getProofData H c b m leaf proof =
      (parseProofMetadata proof).bind fun md =>
      (extractSlice proof md.proofStartIndex (md.proofStartIndex + md.logLeafProofLen)).bind
        fun logPath =>
      (calculateRootMemory H.node logPath m leaf).bind fun batchSettlementRoot =>
      if md.finalProofNode then
        some
          { settlementLayerChainId := 0
            settlementLayerBatchNumber := 0
            settlementLayerBatchRootMask := 0
            batchLeafProofLen := 0
            batchSettlementRoot := batchSettlementRoot
            chainIdLeaf := 0
            l1BatchTimestamp := 0
            ptr := md.proofStartIndex + md.logLeafProofLen
            finalProofNode := true }
      else
        proof[md.proofStartIndex + md.logLeafProofLen]?.bind fun l1BatchTimestamp =>
        proof[md.proofStartIndex + md.logLeafProofLen + 1]?.bind fun batchLeafProofMask =>
        (extractSlice proof (md.proofStartIndex + md.logLeafProofLen + 2)
          (md.proofStartIndex + md.logLeafProofLen + 2 + md.batchLeafProofLen)).bind fun batchPath =>
        (calculateRootMemory H.node batchPath batchLeafProofMask
          (H.batchLeaf batchSettlementRoot b l1BatchTimestamp)).bind fun chainIdRoot =>
        proof[md.proofStartIndex + md.logLeafProofLen + 2 + md.batchLeafProofLen]?.bind
          fun packedBatchInfo =>
        proof[md.proofStartIndex + md.logLeafProofLen + 3 + md.batchLeafProofLen]?.bind
          fun settlementLayerChainId =>
        some
          { settlementLayerChainId := settlementLayerChainId
            settlementLayerBatchNumber := Nat.toUInt256 (packedBatchInfo.val / 2 ^ 128)
            settlementLayerBatchRootMask := Nat.toUInt256 (packedBatchInfo.val % 2 ^ 128)
            batchLeafProofLen := md.batchLeafProofLen
            batchSettlementRoot := batchSettlementRoot
            chainIdLeaf := H.chainIdLeaf chainIdRoot c
            l1BatchTimestamp := l1BatchTimestamp
            ptr := md.proofStartIndex + md.logLeafProofLen + 4 + md.batchLeafProofLen
            finalProofNode := false } := by
  unfold getProofData
  rw [ite_eq_right hlen, ite_eq_right hleaf]

lemma getProofData_leaf {H : Hashes} {c b m leaf : UInt256} {proof : List UInt256}
    {pd : ProofData} (h : getProofData H c b m leaf proof = some pd) :
    leaf ≠ L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH := by
  intro hl
  unfold getProofData at h
  rw [ite_eq_right (getProofData_length h), ite_eq_left hl] at h
  exact absurd h (by simp)

/-- A non-final step moves the pointer by at least five words and stays inside the proof. -/
lemma getProofData_nonfinal_ptr {H : Hashes} {c b m leaf : UInt256} {proof : List UInt256}
    {pd : ProofData} (h : getProofData H c b m leaf proof = some pd)
    (hf : pd.finalProofNode = false) : 5 ≤ pd.ptr ∧ pd.ptr ≤ proof.length := by
  rw [getProofData_eq_bind (getProofData_length h) (getProofData_leaf h)] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨md, hmd, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨logPath, -, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨root, -, h⟩ := h
  by_cases hfin : md.finalProofNode = true
  · rw [ite_eq_left hfin] at h
    obtain rfl := (Option.some.inj h).symm
    simp at hf
  · rw [ite_eq_right hfin] at h
    have hstart := parseProofMetadata_nonfinal hmd (by simpa using hfin)
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨_, -, _, -, _, -, _, -, _, -, w, hw, h⟩ := h
    obtain rfl := (Option.some.inj h).symm
    have hlt := (List.getElem?_eq_some_iff.mp hw).1
    simp only
    omega

/-! ### One storage read -/

theorem prove_eq_anchor_map (H : Hashes) (S : State) :
    ∀ (fuel : ℕ) (c b m leaf : UInt256) (proof : List UInt256) (depth : UInt256),
      proveRecursive H S fuel c b m leaf proof depth =
        (anchorRec H fuel c b m leaf proof depth).map (anchorHolds S) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _; rfl
  | succ f ih =>
    intro c b m leaf proof depth
    simp only [proveRecursive, anchorRec]
    cases getProofData H c b m leaf proof with
    | none => rfl
    | some pd =>
      simp only
      split_ifs
      · rfl
      · rfl
      · rfl
      · rw [ih, Option.map_map]
        rfl

/-! ### Fuel -/

theorem anchorRec_fuel (H : Hashes) :
    ∀ (f g : ℕ) (c b m leaf : UInt256) (proof : List UInt256) (depth : UInt256),
      proof.length ≤ f → proof.length ≤ g →
        anchorRec H f c b m leaf proof depth = anchorRec H g c b m leaf proof depth := by
  intro f
  induction f with
  | zero =>
    intro g c b m leaf proof depth hf _
    have h0 : proof.length = 0 := by omega
    cases g with
    | zero => rfl
    | succ g =>
      simp only [anchorRec]
      rw [getProofData_empty H c b m leaf h0]
  | succ f ih =>
    intro g c b m leaf proof depth hf hg
    cases g with
    | zero =>
      have h0 : proof.length = 0 := by omega
      simp only [anchorRec]
      rw [getProofData_empty H c b m leaf h0]
    | succ g =>
      simp only [anchorRec]
      cases hpd : getProofData H c b m leaf proof with
      | none => rfl
      | some pd =>
        simp only
        split_ifs with hfin
        · rfl
        · rfl
        · rfl
        · have hptr := getProofData_nonfinal_ptr hpd (by simpa using hfin)
          rw [ih g _ _ _ _ _ _ (by simp; omega) (by simp; omega)]

theorem fuel_irrelevant (H : Hashes) (S : State) (k : ℕ) (c b m leaf : UInt256)
    (proof : List UInt256) (depth : UInt256) :
    anchorRec H (proof.length + k) c b m leaf proof depth =
        anchorRec H proof.length c b m leaf proof depth ∧
      proveRecursive H S (proof.length + k) c b m leaf proof depth =
        proveRecursive H S proof.length c b m leaf proof depth := by
  have h := anchorRec_fuel H (proof.length + k) proof.length c b m leaf proof depth (by omega) le_rfl
  refine ⟨h, ?_⟩
  rw [prove_eq_anchor_map, prove_eq_anchor_map, h]

/-! ### The entry points -/

lemma shared_eq_anchor_map (H : Hashes) (S : State) (c b m leaf : UInt256) (proof : List UInt256)
    (depth : UInt256) :
    proveL2LeafInclusionSharedRecursive H S c b m leaf proof depth =
      (anchor H c b m leaf proof depth).map (anchorHolds S) :=
  prove_eq_anchor_map H S _ _ _ _ _ _ _

lemma anchorHolds_iff (S : State) (a : Anchor) :
    anchorHolds S a = true ↔
      (interopRoots S a.chainId a.blockOrBatchNumber).root = a.computedRoot ∧ a.computedRoot ≠ 0 := by
  unfold anchorHolds
  constructor
  · intro h
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    exact ⟨h.1, h.1 ▸ h.2⟩
  · rintro ⟨h1, h2⟩
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    exact ⟨h1, h1 ▸ h2⟩

theorem revert_is_storage_independent (H : Hashes) (S S' : State) (c b m leaf : UInt256)
    (proof : List UInt256) (depth : UInt256) :
    proveL2LeafInclusionSharedRecursive H S c b m leaf proof depth = none ↔
      proveL2LeafInclusionSharedRecursive H S' c b m leaf proof depth = none := by
  rw [shared_eq_anchor_map, shared_eq_anchor_map, Option.map_eq_none_iff, Option.map_eq_none_iff]

theorem accepted_iff_stored_root_at_anchor (H : Hashes) (S : State) (c b m leaf : UInt256)
    (proof : List UInt256) (depth : UInt256) :
    proveL2LeafInclusionSharedRecursive H S c b m leaf proof depth = some true ↔
      ∃ a, anchor H c b m leaf proof depth = some a ∧
        (interopRoots S a.chainId a.blockOrBatchNumber).root = a.computedRoot ∧
        a.computedRoot ≠ 0 := by
  rw [shared_eq_anchor_map, Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, ha, hholds⟩
    exact ⟨a, ha, (anchorHolds_iff S a).mp hholds⟩
  · rintro ⟨a, ha, hholds⟩
    exact ⟨a, ha, (anchorHolds_iff S a).mpr hholds⟩

/-- At depth 1 one step suffices: a non-final step reverts. -/
lemma anchorRec_depth_one (H : Hashes) (f : ℕ) (c b m leaf : UInt256) (proof : List UInt256) :
    anchorRec H (f + 1) c b m leaf proof 1 =
      (getProofData H c b m leaf proof).bind fun pd =>
        if pd.finalProofNode then some ⟨c, b, pd.batchSettlementRoot, 0⟩ else none := by
  simp only [anchorRec]
  cases getProofData H c b m leaf proof with
  | none => rfl
  | some pd =>
    simp only [Option.bind_some]
    split_ifs <;> rfl

theorem anchor_depth_one_eq (H : Hashes) (c b m leaf : UInt256) (proof : List UInt256) :
    anchor H c b m leaf proof 1 =
      (getProofData H c b m leaf proof).bind fun pd =>
        if pd.finalProofNode then some ⟨c, b, pd.batchSettlementRoot, 0⟩ else none := by
  unfold anchor
  cases hlen : proof.length with
  | zero =>
    rw [getProofData_empty H c b m leaf hlen]
    rfl
  | succ f => exact anchorRec_depth_one H f c b m leaf proof

/-- The depth-0 entry in closed form: at most two parsing steps. -/
theorem anchor_zero_eq (H : Hashes) (c b m leaf : UInt256) (proof : List UInt256) :
    anchor H c b m leaf proof 0 =
      (getProofData H c b m leaf proof).bind fun pd =>
        if pd.finalProofNode then some ⟨c, b, pd.batchSettlementRoot, 0⟩
        else (getProofData H pd.settlementLayerChainId pd.settlementLayerBatchNumber
            pd.settlementLayerBatchRootMask pd.chainIdLeaf (proof.drop pd.ptr)).bind fun pd' =>
          if pd'.finalProofNode then
            some ⟨pd.settlementLayerChainId, pd.settlementLayerBatchNumber, pd'.batchSettlementRoot, 1⟩
          else none := by
  unfold anchor
  cases hlen : proof.length with
  | zero =>
    rw [getProofData_empty H c b m leaf hlen]
    rfl
  | succ f =>
    simp only [anchorRec]
    cases hpd : getProofData H c b m leaf proof with
    | none => rfl
    | some pd =>
      simp only [Option.bind_some]
      split_ifs with hfin h1 h2
      · rfl
      · exact absurd h1 (by decide)
      · exact absurd h2 (by decide)
      · have hptr := getProofData_nonfinal_ptr hpd (by simpa using hfin)
        obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        rw [show (0 : UInt256) + 1 = 1 from rfl, anchorRec_depth_one]
        cases getProofData H pd.settlementLayerChainId pd.settlementLayerBatchNumber
            pd.settlementLayerBatchRootMask pd.chainIdLeaf (proof.drop pd.ptr) with
        | none => rfl
        | some pd' =>
          simp only [Option.bind_some]
          split_ifs <;> rfl

theorem shared_entry_anchor_iff (H : Hashes) (c b m leaf : UInt256) (proof : List UInt256)
    (a : Anchor) :
    anchor H c b m leaf proof 0 = some a ↔
      ∃ pd, getProofData H c b m leaf proof = some pd ∧
        ((pd.finalProofNode = true ∧ a = ⟨c, b, pd.batchSettlementRoot, 0⟩) ∨
         (pd.finalProofNode = false ∧
          ∃ pd', getProofData H pd.settlementLayerChainId pd.settlementLayerBatchNumber
              pd.settlementLayerBatchRootMask pd.chainIdLeaf (proof.drop pd.ptr) = some pd' ∧
            pd'.finalProofNode = true ∧
            a = ⟨pd.settlementLayerChainId, pd.settlementLayerBatchNumber,
              pd'.batchSettlementRoot, 1⟩)) := by
  rw [anchor_zero_eq, Option.bind_eq_some_iff]
  refine exists_congr fun pd => and_congr_right fun _ => ?_
  cases pd.finalProofNode
  · simp only [Bool.false_eq_true, ite_false, Option.bind_eq_some_iff, false_and, true_and,
      false_or]
    refine exists_congr fun pd' => and_congr_right fun _ => ?_
    cases pd'.finalProofNode
    · simp
    · simp only [ite_true, Option.some.injEq, true_and]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
  · simp only [ite_true, Option.some.injEq, true_and, Bool.true_eq_false, false_and, or_false]
    exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem depth_one_anchor_iff (H : Hashes) (c b m leaf : UInt256) (proof : List UInt256)
    (a : Anchor) :
    anchor H c b m leaf proof 1 = some a ↔
      ∃ pd, getProofData H c b m leaf proof = some pd ∧
        pd.finalProofNode = true ∧ a = ⟨c, b, pd.batchSettlementRoot, 0⟩ := by
  rw [anchor_depth_one_eq, Option.bind_eq_some_iff]
  refine exists_congr fun pd => and_congr_right fun _ => ?_
  cases pd.finalProofNode
  · simp
  · simp only [ite_true, Option.some.injEq, true_and]
    exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem shared_entry_accepts_iff (H : Hashes) (S : State) (c b m leaf : UInt256)
    (proof : List UInt256) :
    proveL2LeafInclusionShared H S c b m leaf proof = some true ↔
      ∃ pd, getProofData H c b m leaf proof = some pd ∧
        ((pd.finalProofNode = true ∧
            (interopRoots S c b).root = pd.batchSettlementRoot ∧ pd.batchSettlementRoot ≠ 0) ∨
         (pd.finalProofNode = false ∧
          ∃ pd', getProofData H pd.settlementLayerChainId pd.settlementLayerBatchNumber
              pd.settlementLayerBatchRootMask pd.chainIdLeaf (proof.drop pd.ptr) = some pd' ∧
            pd'.finalProofNode = true ∧
            (interopRoots S pd.settlementLayerChainId pd.settlementLayerBatchNumber).root =
              pd'.batchSettlementRoot ∧
            pd'.batchSettlementRoot ≠ 0)) := by
  unfold proveL2LeafInclusionShared
  rw [accepted_iff_stored_root_at_anchor]
  constructor
  · rintro ⟨a, ha, hroot, hnz⟩
    obtain ⟨pd, hpd, hcase⟩ := (shared_entry_anchor_iff H c b m leaf proof a).mp ha
    refine ⟨pd, hpd, ?_⟩
    rcases hcase with ⟨hf, rfl⟩ | ⟨hf, pd', hpd', hf', rfl⟩
    · exact Or.inl ⟨hf, hroot, hnz⟩
    · exact Or.inr ⟨hf, pd', hpd', hf', hroot, hnz⟩
  · rintro ⟨pd, hpd, hcase⟩
    rcases hcase with ⟨hf, hroot, hnz⟩ | ⟨hf, pd', hpd', hf', hroot, hnz⟩
    · exact ⟨_, (shared_entry_anchor_iff H c b m leaf proof _).mpr
        ⟨pd, hpd, Or.inl ⟨hf, rfl⟩⟩, hroot, hnz⟩
    · exact ⟨_, (shared_entry_anchor_iff H c b m leaf proof _).mpr
        ⟨pd, hpd, Or.inr ⟨hf, pd', hpd', hf', rfl⟩⟩, hroot, hnz⟩

/-! ### The consumer's positional read -/

lemma readSettlementLayerReference_of_getProofData {H : Hashes} {c b m leaf : UInt256}
    {proof : List UInt256} {pd : ProofData} (h : getProofData H c b m leaf proof = some pd)
    (hf : pd.finalProofNode = false) :
    readSettlementLayerReference proof =
      some ⟨pd.settlementLayerBatchNumber, pd.settlementLayerChainId, pd.l1BatchTimestamp⟩ := by
  rw [getProofData_eq_bind (getProofData_length h) (getProofData_leaf h)] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨md, hmd, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨logPath, -, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨root, -, h⟩ := h
  by_cases hfin : md.finalProofNode = true
  · rw [ite_eq_left hfin] at h
    obtain rfl := (Option.some.inj h).symm
    simp at hf
  · rw [ite_eq_right hfin] at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨ts, hts, _, -, _, -, _, -, packed, hpacked, slc, hslc, h⟩ := h
    obtain rfl := (Option.some.inj h).symm
    unfold readSettlementLayerReference
    rw [hmd, Option.bind_some, ite_eq_right hfin]
    simp only [hts, hpacked, hslc, Option.bind_some]

theorem settlement_layer_reference_is_the_anchor_key (H : Hashes) (c b m leaf : UInt256)
    (proof : List UInt256) (a : Anchor) (ha : anchor H c b m leaf proof 0 = some a)
    (hhops : a.hops = 1) :
    ∃ pd, getProofData H c b m leaf proof = some pd ∧ pd.finalProofNode = false ∧
      readSettlementLayerReference proof = some ⟨a.blockOrBatchNumber, a.chainId, pd.l1BatchTimestamp⟩ := by
  obtain ⟨pd, hpd, hcase⟩ := (shared_entry_anchor_iff H c b m leaf proof a).mp ha
  rcases hcase with ⟨-, rfl⟩ | ⟨hf, pd', -, -, rfl⟩
  · simp at hhops
  · exact ⟨pd, hpd, hf, readSettlementLayerReference_of_getProofData hpd hf⟩

/-! ### What the compared root is built from -/

lemma calculateRootMemory_eq_walk {h : UInt256 → UInt256 → UInt256} {path : List UInt256}
    {index item r : UInt256} (hr : calculateRootMemory h path index item = some r) :
    r = walk h path index.val item := by
  unfold calculateRootMemory at hr
  split_ifs at hr
  exact (Option.some.inj hr).symm

lemma getProofData_shape {H : Hashes} {c b m leaf : UInt256} {proof : List UInt256}
    {pd : ProofData} (h : getProofData H c b m leaf proof = some pd) :
    ∃ logPath, pd.batchSettlementRoot = walk H.node logPath m.val leaf ∧
      (pd.finalProofNode = false →
        ∃ (batchPath : List UInt256) (batchMask : UInt256),
          pd.chainIdLeaf = H.chainIdLeaf (walk H.node batchPath batchMask.val
            (H.batchLeaf pd.batchSettlementRoot b pd.l1BatchTimestamp)) c) := by
  rw [getProofData_eq_bind (getProofData_length h) (getProofData_leaf h)] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨md, -, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨logPath, -, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨root, hroot, h⟩ := h
  have hroot := calculateRootMemory_eq_walk hroot
  by_cases hfin : md.finalProofNode = true
  · rw [ite_eq_left hfin] at h
    obtain rfl := (Option.some.inj h).symm
    exact ⟨logPath, hroot, fun hf => absurd hf (by simp)⟩
  · rw [ite_eq_right hfin] at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨ts, -, mask, -, batchPath, -, cir, hcir, _, -, _, -, h⟩ := h
    obtain rfl := (Option.some.inj h).symm
    exact ⟨logPath, hroot, fun _ => ⟨batchPath, mask, by rw [calculateRootMemory_eq_walk hcir]⟩⟩

theorem shared_entry_root_shape (H : Hashes) (c b m leaf : UInt256) (proof : List UInt256)
    (a : Anchor) (ha : anchor H c b m leaf proof 0 = some a) :
    (a.hops = 0 ∧ a.chainId = c ∧ a.blockOrBatchNumber = b ∧
      ∃ logPath : List UInt256, a.computedRoot = walk H.node logPath m.val leaf) ∨
    (a.hops = 1 ∧
      ∃ (logPath batchPath slPath : List UInt256) (batchMask slMask ts : UInt256),
        a.computedRoot = walk H.node slPath slMask.val
          (H.chainIdLeaf (walk H.node batchPath batchMask.val
            (H.batchLeaf (walk H.node logPath m.val leaf) b ts)) c) ∧
        readSettlementLayerReference proof = some ⟨a.blockOrBatchNumber, a.chainId, ts⟩) := by
  obtain ⟨pd, hpd, hcase⟩ := (shared_entry_anchor_iff H c b m leaf proof a).mp ha
  obtain ⟨logPath, hroot, hcil⟩ := getProofData_shape hpd
  rcases hcase with ⟨-, rfl⟩ | ⟨hf, pd', hpd', -, rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl, logPath, hroot⟩
  · right
    obtain ⟨batchPath, batchMask, hcil⟩ := hcil hf
    obtain ⟨slPath, hroot', -⟩ := getProofData_shape hpd'
    refine ⟨rfl, logPath, batchPath, slPath, batchMask, pd.settlementLayerBatchRootMask,
      pd.l1BatchTimestamp, ?_, readSettlementLayerReference_of_getProofData hpd hf⟩
    rw [hroot', hcil, hroot]

/-! ### The walk is `MerkleSpec.walkPure` -/

lemma walk_eq_walkPure (h : UInt256 → UInt256 → UInt256) :
    ∀ (path : List UInt256) (sibs : ℕ → UInt256) (lvl idx : ℕ) (x : UInt256),
      (∀ i, i < path.length → sibs (lvl + i) = path.getD i 0) →
        walk h path idx x = MerkleSpec.walkPure h sibs lvl path.length idx x := by
  intro path
  induction path with
  | nil => intro _ _ _ _ _; rfl
  | cons s path ih =>
    intro sibs lvl idx x hs
    have h0 : sibs lvl = s := by simpa using hs 0 (by simp)
    simp only [walk, List.length_cons, MerkleSpec.walkPure]
    rw [ih sibs (lvl + 1) (idx / 2) _ (fun i hi => by
      have := hs (i + 1) (by simp; omega)
      rw [show lvl + 1 + i = lvl + (i + 1) by omega, this]
      simp)]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one idx with hp | hp
    · simp [hp, h0]
    · simp [hp, h0]

theorem calculate_root_memory_is_merkle_spec_walk (h : UInt256 → UInt256 → UInt256)
    (path : List UInt256) (index item r : UInt256) :
    calculateRootMemory h path index item = some r ↔
      path.length < 256 ∧ index.val < 2 ^ path.length ∧
        r = MerkleSpec.walkPure h (fun l => path.getD l 0) 0 path.length index.val item := by
  have hw := walk_eq_walkPure h path (fun l => path.getD l 0) 0 index.val item
    (fun i _ => by simp)
  unfold calculateRootMemory
  split_ifs with h1 h2
  · simp only [false_iff, not_and]
    intro h3
    omega
  · simp only [false_iff, not_and]
    intro _
    omega
  · rw [Option.some_inj, hw]
    constructor
    · intro hr
      exact ⟨by omega, by omega, hr.symm⟩
    · rintro ⟨-, -, hr⟩
      exact hr.symm

/-! ### Against the storage's runs -/

theorem acceptance_survives_runs (H : Hashes) {S S' : State} (hreach : Reach S S')
    (c b m leaf : UInt256) (proof : List UInt256) (depth : UInt256)
    (hacc : proveL2LeafInclusionSharedRecursive H S c b m leaf proof depth = some true) :
    proveL2LeafInclusionSharedRecursive H S' c b m leaf proof depth = some true := by
  obtain ⟨a, ha, hroot, hnz⟩ := (accepted_iff_stored_root_at_anchor H S c b m leaf proof depth).mp hacc
  have hkeep := no_overwrite hreach (c := a.chainId) (b := a.blockOrBatchNumber)
    (by unfold interopRoots at hroot; rw [hroot]; exact hnz)
  refine (accepted_iff_stored_root_at_anchor H S' c b m leaf proof depth).mpr ⟨a, ha, ?_, hnz⟩
  unfold interopRoots at hroot ⊢
  rw [hkeep, hroot]

lemma reach_of_reachLog {S₀ S : State} {log : List (Address × Call)} (h : ReachLog S₀ S log) :
    Reach S₀ S :=
  (reach_iff_reachLog).mpr ⟨log, h⟩

theorem accepted_after_run_was_accepted_or_imported (H : Hashes) {S₀ S : State}
    {log : List (Address × Call)} (hlog : ReachLog S₀ S log) (c b m leaf : UInt256)
    (proof : List UInt256) (depth : UInt256)
    (hacc : proveL2LeafInclusionSharedRecursive H S c b m leaf proof depth = some true) :
    proveL2LeafInclusionSharedRecursive H S₀ c b m leaf proof depth = some true ∨
      ∃ a, anchor H c b m leaf proof depth = some a ∧
        (interopRoots S₀ a.chainId a.blockOrBatchNumber).root = 0 ∧
        ∃ r ∈ imports log, r.key = (a.chainId, a.blockOrBatchNumber) ∧
          r.sides.headD 0 = a.computedRoot := by
  obtain ⟨a, ha, hroot, hnz⟩ := (accepted_iff_stored_root_at_anchor H S c b m leaf proof depth).mp hacc
  by_cases h0 : (interopRoots S₀ a.chainId a.blockOrBatchNumber).root = 0
  · right
    refine ⟨a, ha, h0, ?_⟩
    obtain ⟨hhit, hmiss⟩ := storage_is_the_log hlog a.chainId a.blockOrBatchNumber
    by_contra hnone
    push Not at hnone
    have hall : ∀ r ∈ imports log, r.key ≠ (a.chainId, a.blockOrBatchNumber) := by
      intro r hr hkey
      have hst := hhit r hr hkey
      have := hnone r hr hkey
      apply this
      unfold interopRoots at hroot
      rw [← hroot, hst]
      rfl
    have hsame := hmiss hall
    unfold interopRoots at hroot h0
    rw [hsame] at hroot
    exact hnz (hroot ▸ h0)
  · left
    have hkeep := no_overwrite (reach_of_reachLog hlog) (c := a.chainId) (b := a.blockOrBatchNumber) h0
    refine (accepted_iff_stored_root_at_anchor H S₀ c b m leaf proof depth).mpr ⟨a, ha, ?_, hnz⟩
    unfold interopRoots at hroot ⊢
    rw [← hkeep, hroot]

theorem accepted_from_fresh_storage_was_imported (H : Hashes) {S : State}
    {log : List (Address × Call)} (hlog : ReachLog empty S log) (c b m leaf : UInt256)
    (proof : List UInt256) (depth : UInt256)
    (hacc : proveL2LeafInclusionSharedRecursive H S c b m leaf proof depth = some true) :
    ∃ a, anchor H c b m leaf proof depth = some a ∧
      ∃ p ∈ log, p.1 = L2_BOOTLOADER_ADDRESS ∧
        ∃ r ∈ p.2.roots, r.key = (a.chainId, a.blockOrBatchNumber) ∧ r.sides = [a.computedRoot] := by
  rcases accepted_after_run_was_accepted_or_imported H hlog c b m leaf proof depth hacc with
    hempty | ⟨a, ha, -, r, hr, hkey, hside⟩
  · exfalso
    obtain ⟨a, -, hroot, hnz⟩ :=
      (accepted_iff_stored_root_at_anchor H empty c b m leaf proof depth).mp hempty
    exact hnz hroot.symm
  · refine ⟨a, ha, ?_⟩
    obtain ⟨p, hp, hrp⟩ := List.mem_flatMap.mp hr
    refine ⟨p, hp, logged_callers_are_bootloader hlog p hp, r, hrp, hkey, ?_⟩
    obtain ⟨hlen, -, -⟩ := logged_imports_well_formed hlog r hr
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
    rw [hx] at hside ⊢
    simp only [List.headD_cons] at hside
    rw [hside]

theorem accepted_anchor_has_nonzero_timestamp (H : Hashes) {S : State} (hreach : Reach empty S)
    (c b m leaf : UInt256) (proof : List UInt256) (depth : UInt256)
    (hacc : proveL2LeafInclusionSharedRecursive H S c b m leaf proof depth = some true) :
    ∃ a, anchor H c b m leaf proof depth = some a ∧
      (interopRoots S a.chainId a.blockOrBatchNumber).timestamp ≠ 0 := by
  obtain ⟨a, ha, hroot, hnz⟩ := (accepted_iff_stored_root_at_anchor H S c b m leaf proof depth).mp hacc
  refine ⟨a, ha, fun h0 => hnz ?_⟩
  have hz := zero_timestamp_iff_unset_invariant.2 _ _ hreach zero_timestamp_iff_unset_invariant.1
    a.chainId a.blockOrBatchNumber
  unfold interopRoots at hroot h0
  rw [← hroot]
  exact hz.mpr h0

/-! ### The countermodel -/

lemma parse_final_word (rest : List UInt256) :
    parseProofMetadata (metadataWord 0 0 1 :: rest) = some ⟨1, 0, 0, true⟩ := by
  simp only [parseProofMetadata, List.getElem?_cons_zero]
  rw [ite_eq_left (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
  decide

lemma parse_nonfinal_word (rest : List UInt256) :
    parseProofMetadata (metadataWord 0 0 0 :: rest) = some ⟨1, 0, 0, false⟩ := by
  simp only [parseProofMetadata, List.getElem?_cons_zero]
  rw [ite_eq_left (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
  decide

/-- An empty path at index 0 recomputes the item itself. -/
lemma calculateRootMemory_nil (h : UInt256 → UInt256 → UInt256) (x : UInt256) :
    calculateRootMemory h [] 0 x = some x := by
  simp [calculateRootMemory, walk]

/-- A one-word final-node proof with an empty log path: the recomputed root is the leaf. -/
lemma getProofData_final_word (H : Hashes) (c b leaf : UInt256)
    (hleaf : leaf ≠ L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH) :
    getProofData H c b 0 leaf [metadataWord 0 0 1] =
      some ⟨0, 0, 0, 0, leaf, 0, 0, 1, true⟩ := by
  unfold getProofData
  rw [ite_eq_right (by simp), ite_eq_right hleaf, parse_final_word]
  simp [extractSlice, calculateRootMemory, walk]

theorem without_nonzero_check_unimported_key_accepts (H : Hashes) (S : State) (c b : UInt256)
    (h0 : (interopRoots S c b).root = 0) :
    proveL2LeafInclusionShared H S c b 0 0 zeroLeafDirectProof = some false ∧
      proveL2LeafInclusionSharedNoZeroCheck H S c b 0 0 zeroLeafDirectProof = some true := by
  have hpd := getProofData_final_word H c b 0 (by decide)
  constructor
  · simp only [proveL2LeafInclusionShared, proveL2LeafInclusionSharedRecursive, zeroLeafDirectProof,
      List.length_singleton, proveRecursive, hpd]
    simp [h0]
  · simp only [proveL2LeafInclusionSharedNoZeroCheck, zeroLeafDirectProof, List.length_singleton,
      proveRecursiveNoZeroCheck, hpd]
    simp [h0]

/-! ### The witnesses -/

/-- The first step of `oneHopExampleProof`. -/
lemma getProofData_oneHop (H : Hashes) (leaf : UInt256)
    (hleaf : leaf ≠ L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH) :
    getProofData H 7 3 0 leaf oneHopExampleProof =
      some ⟨1, 42, 0, 0, leaf, H.chainIdLeaf (H.batchLeaf leaf 3 100) 7, 100, 5, false⟩ := by
  unfold getProofData oneHopExampleProof
  rw [ite_eq_right (by simp), ite_eq_right hleaf, parse_nonfinal_word]
  simp only [Option.bind_some, extractSlice]
  simp [calculateRootMemory_nil]
  congr 1

theorem honest_one_hop_proof_accepted (H : Hashes) (leaf : UInt256)
    (hleaf : leaf ≠ L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH)
    (hR : H.chainIdLeaf (H.batchLeaf leaf 3 100) 7 ≠ L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH)
    (hR0 : H.chainIdLeaf (H.batchLeaf leaf 3 100) 7 ≠ 0) :
    anchor H 7 3 0 leaf oneHopExampleProof 0 =
        some ⟨1, 42, H.chainIdLeaf (H.batchLeaf leaf 3 100) 7, 1⟩ ∧
      proveL2LeafInclusionShared H empty 7 3 0 leaf oneHopExampleProof = some false ∧
      ∀ S : State, (interopRoots S 1 42).root = H.chainIdLeaf (H.batchLeaf leaf 3 100) 7 →
        proveL2LeafInclusionShared H S 7 3 0 leaf oneHopExampleProof = some true := by
  have hanchor : anchor H 7 3 0 leaf oneHopExampleProof 0 =
      some ⟨1, 42, H.chainIdLeaf (H.batchLeaf leaf 3 100) 7, 1⟩ := by
    rw [anchor_zero_eq, getProofData_oneHop H leaf hleaf]
    simp only [Option.bind_some, Bool.false_eq_true, ite_false]
    rw [show oneHopExampleProof.drop 5 = [metadataWord 0 0 1] from rfl,
      getProofData_final_word H 1 42 _ hR]
    rfl
  refine ⟨hanchor, ?_, ?_⟩
  · unfold proveL2LeafInclusionShared
    rw [shared_eq_anchor_map, hanchor]
    simp [anchorHolds, interopRoots, empty]
  · intro S hS
    unfold proveL2LeafInclusionShared
    rw [shared_eq_anchor_map, hanchor]
    simp [anchorHolds, hS, hR0]

/-- The concrete hash of `OneHopProofWitness`: sums, so its values are easy to evaluate. -/
def oneHopWitnessHashes : Hashes where
  node := fun x y => x + y + 1
  batchLeaf := fun r n t => r + n + t + 1
  chainIdLeaf := fun r c => r + c + 1

theorem one_hop_proof_witness : Properties.OneHopProofWitness := by
  let H := oneHopWitnessHashes
  have hR : H.chainIdLeaf (H.batchLeaf 1 3 100) 7 = 113 := by decide
  let S₁ := writeRoot empty 1 42 9 113
  let S₂ := writeRoot S₁ 5 5 10 0xee
  have h1 : exec empty L2_BOOTLOADER_ADDRESS (.single ⟨1, 42, 9, [113]⟩) = some S₁ := by
    refine exec_eq_some.mpr ⟨rfl, ?_⟩
    rw [Call.roots, addRoots_singleton]
    exact addRoot_mk (by decide) (by decide) rfl
  have h2 : exec S₁ L2_BOOTLOADER_ADDRESS (.single ⟨5, 5, 10, [0xee]⟩) = some S₂ := by
    refine exec_eq_some.mpr ⟨rfl, ?_⟩
    rw [Call.roots, addRoots_singleton]
    exact addRoot_mk (by decide) (by decide) (by decide)
  obtain ⟨hanchor, hfalse, htrue⟩ := honest_one_hop_proof_accepted H 1 (by decide)
    (by rw [hR]; decide) (by rw [hR]; decide)
  have hread : readSettlementLayerReference oneHopExampleProof = some ⟨42, 1, 100⟩ :=
    readSettlementLayerReference_of_getProofData (getProofData_oneHop H 1 (by decide)) rfl
  refine ⟨H, S₁, S₂, _, _, by decide, by rw [hR]; decide, by rw [hR]; decide,
    ⟨_, hanchor, rfl⟩, hread,
    ReachLog.tail _ _ ReachLog.refl h1, rfl, ReachLog.tail _ _ ReachLog.refl h2, rfl, rfl,
    hfalse, htrue S₁ (by rw [hR]; decide), htrue S₂ (by rw [hR]; decide)⟩

/-! ### The named properties -/

theorem ProveIsOneStorageRead : Properties.ProveIsOneStorageRead :=
  fun H S fuel c b m leaf proof depth => prove_eq_anchor_map H S fuel c b m leaf proof depth
theorem FuelIrrelevant : Properties.FuelIrrelevant := fuel_irrelevant
theorem RevertIsStorageIndependent : Properties.RevertIsStorageIndependent :=
  revert_is_storage_independent
theorem AcceptedIffStoredRootAtAnchor : Properties.AcceptedIffStoredRootAtAnchor :=
  accepted_iff_stored_root_at_anchor
theorem SharedEntryAnchorIff : Properties.SharedEntryAnchorIff := shared_entry_anchor_iff
theorem DepthOneAnchorIff : Properties.DepthOneAnchorIff := depth_one_anchor_iff
theorem SharedEntryAcceptsIff : Properties.SharedEntryAcceptsIff := shared_entry_accepts_iff
theorem CalculateRootMemoryIsMerkleSpecWalk : Properties.CalculateRootMemoryIsMerkleSpecWalk :=
  calculate_root_memory_is_merkle_spec_walk
theorem SettlementLayerReferenceIsTheAnchorKey :
    Properties.SettlementLayerReferenceIsTheAnchorKey :=
  settlement_layer_reference_is_the_anchor_key
theorem AcceptedAnchorHasNonzeroTimestamp : Properties.AcceptedAnchorHasNonzeroTimestamp :=
  fun H _ c b m leaf proof depth hreach hacc =>
    accepted_anchor_has_nonzero_timestamp H hreach c b m leaf proof depth hacc
theorem SharedEntryRootShape : Properties.SharedEntryRootShape := shared_entry_root_shape
theorem AcceptanceSurvivesRuns : Properties.AcceptanceSurvivesRuns :=
  fun H _ _ c b m leaf proof depth hreach hacc =>
    acceptance_survives_runs H hreach c b m leaf proof depth hacc
theorem AcceptedAfterRunWasAcceptedOrImported :
    Properties.AcceptedAfterRunWasAcceptedOrImported :=
  fun H _ _ _ c b m leaf proof depth hlog hacc =>
    accepted_after_run_was_accepted_or_imported H hlog c b m leaf proof depth hacc
theorem AcceptedFromFreshStorageWasImported : Properties.AcceptedFromFreshStorageWasImported :=
  fun H _ _ c b m leaf proof depth hlog hacc =>
    accepted_from_fresh_storage_was_imported H hlog c b m leaf proof depth hacc
theorem WithoutNonzeroCheckUnimportedKeyAccepts :
    Properties.WithoutNonzeroCheckUnimportedKeyAccepts :=
  without_nonzero_check_unimported_key_accepts
theorem HonestOneHopProofAccepted : Properties.HonestOneHopProofAccepted :=
  honest_one_hop_proof_accepted
theorem OneHopProofWitness : Properties.OneHopProofWitness := one_hop_proof_witness

end Contracts.MessageVerification
