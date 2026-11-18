import EraSpec.Contracts.MessageVerification.Properties.StatusProof
import EraSpec.Contracts.MessageHashing.Proofs.LogLeafSeparation
import EraSpec.Contracts.Merkle.Proofs.PathCollision

/-!
# Proofs: an accepted status proof for a status the batch never recorded locates a break

The composed walk splits at three steps below its top (`walkPure_add`): the last three climb the
height-3 tree, where `accept_pins_entry_or_collision` opens one of its leaves or locates a
collision; the first `m` either reach the logs root, where `accept_pins_entry_any_length_or_break`
applies to the logs tree, or reach another leaf (`otherLeaf`). Over keccak, an opened logs-tree
entry is the leaf of the batch's log at that position (the default-leaf check excludes padding),
and the log preimages differ by `LogLeafSeparation`.
-/

namespace Contracts.MessageVerification

open Contracts.MessageHashing
open MerkleSpec MerkleSpec.Verifier
open AttackVectors.BundleHashEncoding (HashCollision)

/-! ## The height-3 tree -/

theorem chainBatchRoot_eq_rootOf (h : Hash) (a b c d : UInt256) :
    chainBatchRoot h a b c d = rootOf h 0 (batchLeaves a b c d) 3 :=
  rfl

/-! ## Sibling-stream congruence for `walkPair` and `PathCollision` -/

lemma statusProof_walkPair_congr (h : Hash) (s₁ s₂ : ℕ → UInt256) :
    ∀ (i lvl j : ℕ) (x : UInt256), (∀ l, lvl ≤ l → l ≤ lvl + i → s₁ l = s₂ l) →
      walkPair h s₁ lvl j x i = walkPair h s₂ lvl j x i
  | 0, lvl, j, x, hs => by
      simp only [walkPair, walkStep, hs lvl le_rfl (by omega)]
  | i + 1, lvl, j, x, hs => by
      rw [walkPair_succ, walkPair_succ]
      have hstep : walkStep s₁ lvl j x = walkStep s₂ lvl j x := by
        simp only [walkStep, hs lvl le_rfl (by omega)]
      rw [hstep]
      exact statusProof_walkPair_congr h s₁ s₂ i (lvl + 1) (j / 2) _
        (fun l h1 h2 => hs l (by omega) (by omega))

lemma statusProof_pathCollision_congr (h : Hash) (z0 : UInt256) (L : List UInt256)
    (s₁ s₂ : ℕ → UInt256) (lvl k j : ℕ) (x : UInt256)
    (hs : ∀ l, lvl ≤ l → l < lvl + k → s₁ l = s₂ l) :
    PathCollision h z0 L s₁ lvl k j x → PathCollision h z0 L s₂ lvl k j x := by
  rintro ⟨i, hi, hne, heq⟩
  have e := statusProof_walkPair_congr h s₁ s₂ i lvl j x (fun l h1 h2 => hs l h1 (by omega))
  rw [e] at hne heq
  exact ⟨i, hi, hne, heq⟩

/-! ## The composed walk -/

theorem batch_walk_opens_or_break (h : Hash) (z0 : UInt256) (L : List UInt256) (H : ℕ)
    (mc b e : UInt256) (sibs : ℕ → UInt256) (k j : ℕ) (x : UInt256) (hj : j < 2 ^ k)
    (hacc : walkPure h sibs 0 k j x = chainBatchRoot h (rootOf h z0 L H) mc b e) :
    (k = H + 3 ∧ j < 2 ^ H ∧ L.getD j z0 = x) ∨ BatchWalkBreak h z0 L H mc b e sibs k j x := by
  rw [chainBatchRoot_eq_rootOf] at hacc
  rcases Nat.lt_or_ge k 3 with hk | hk
  · right
    rcases accept_forces_height_or_break h 0 _ sibs k 3 j x hj hacc with h3 | hb
    · omega
    · exact BatchWalkBreak.short hk hb
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    have hsplit := walkPure_add h sibs m 3 0 j x
    rw [walkPure_shift h sibs m 3 0, hacc] at hsplit
    have hq : j / 2 ^ m < 2 ^ 3 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_comm]
      exact hj
    rcases accept_pins_entry_or_collision h 0 (batchLeaves (rootOf h z0 L H) mc b e)
        (fun l => sibs (l + m)) 3 (j / 2 ^ m) (walkPure h sibs 0 m j x) hq hsplit.symm
      with he | hc
    · by_cases hq0 : j / 2 ^ m = 0
      · have hjm : j < 2 ^ m := by
          rcases Nat.lt_or_ge j (2 ^ m) with h1 | h1
          · exact h1
          · exact absurd hq0 (Nat.div_pos h1 (by positivity)).ne'
        rw [hq0] at he
        have hy : walkPure h sibs 0 m j x = rootOf h z0 L H := he.symm
        rcases accept_pins_entry_any_length_or_break h z0 L sibs m H j x hjm hy
          with ⟨hmH, hx⟩ | ⟨hmH, hc⟩ | hb
        · subst hmH
          exact Or.inl ⟨rfl, hjm, hx⟩
        · subst hmH
          exact Or.inr (BatchWalkBreak.logsCollision rfl hjm hc)
        · exact Or.inr (BatchWalkBreak.logsHeight m rfl hjm hb)
      · exact Or.inr (BatchWalkBreak.otherLeaf m rfl hq0 he.symm)
    · exact Or.inr (BatchWalkBreak.top m rfl hc)

theorem honest_batch_walk_no_break (h : Hash) (z0 : UInt256) (L : List UInt256) (H : ℕ)
    (mc b e : UInt256) (j : ℕ) (hj : j < 2 ^ H) :
    j < 2 ^ (H + 3)
      ∧ walkPure h (honestBatchSibs h z0 L H mc b e j) 0 (H + 3) j (L.getD j z0)
          = chainBatchRoot h (rootOf h z0 L H) mc b e
      ∧ ¬ BatchWalkBreak h z0 L H mc b e (honestBatchSibs h z0 L H mc b e j) (H + 3) j
          (L.getD j z0) := by
  have hjH3 : j < 2 ^ (H + 3) :=
    lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hlow : ∀ l, 0 ≤ l → l < 0 + H →
      honestBatchSibs h z0 L H mc b e j l = honestSibs h z0 L j l := by
    intro l _ hl
    simp only [honestBatchSibs, ite_eq_left (show l < H by omega)]
  have hinner : walkPure h (honestBatchSibs h z0 L H mc b e j) 0 H j (L.getD j z0)
      = rootOf h z0 L H := by
    rw [walkPure_congr_sibs h _ (honestSibs h z0 L j) H 0 j _ hlow]
    exact honest_walk_root h z0 L H j hj
  have hshift : (fun l => honestBatchSibs h z0 L H mc b e j (l + H))
      = honestSibs h 0 (batchLeaves (rootOf h z0 L H) mc b e) 0 := by
    funext l
    simp only [honestBatchSibs, ite_eq_right (show ¬ l + H < H by omega), Nat.add_sub_cancel]
  have hq : j / 2 ^ H = 0 := Nat.div_eq_of_lt hj
  have hroot : walkPure h (honestBatchSibs h z0 L H mc b e j) 0 (H + 3) j (L.getD j z0)
      = chainBatchRoot h (rootOf h z0 L H) mc b e := by
    rw [walkPure_add h _ H 3 0 j, hinner, walkPure_shift h _ H 3 0, hshift, hq,
      chainBatchRoot_eq_rootOf]
    exact honest_walk_root h 0 (batchLeaves (rootOf h z0 L H) mc b e) 3 0 (by norm_num)
  refine ⟨hjH3, hroot, ?_⟩
  intro hb
  cases hb with
  | short hk _ => omega
  | top m hm hc =>
    have hmH : m = H := by omega
    rw [hmH, hshift, hq, hinner] at hc
    exact honest_walk_no_collision h 0 (batchLeaves (rootOf h z0 L H) mc b e) 3 0 hc
  | otherLeaf m hm hq0 _ =>
    have hmH : m = H := by omega
    rw [hmH] at hq0
    exact hq0 hq
  | logsCollision _ _ hc =>
    exact honest_walk_no_collision h z0 L H j
      (statusProof_pathCollision_congr h z0 L _ (honestSibs h z0 L j) 0 H j _ hlow hc)
  | logsHeight m hm _ hb =>
    have hmH : m = H := by omega
    rw [hmH] at hb
    exact heightBreak_not_tautology.1 h z0 L _ H j _ hb

/-! ## The L1 check -/

lemma logsLeaves_getD_some (keccak : Keccak) {logs : List L2Log} {j : ℕ} {log : L2Log}
    (hlog : logs[j]? = some log) (d : UInt256) :
    (logsLeaves keccak logs).getD j d = logLeaf keccak log := by
  simp [logsLeaves, List.getD_eq_getElem?_getD, hlog]

lemma logsLeaves_getD_none (keccak : Keccak) {logs : List L2Log} {j : ℕ}
    (hlog : logs[j]? = none) (d : UInt256) :
    (logsLeaves keccak logs).getD j d = d := by
  simp [logsLeaves, List.getD_eq_getElem?_getD, hlog]

theorem log_proof_of_absent_log (keccak : Keccak) (logs : List L2Log) (H : ℕ)
    (mc b e R : UInt256) (ℓ : L2Log) (j : ℕ) (sibs : ℕ → UInt256) (k : ℕ)
    (hwf : ∀ log ∈ logs, LogWellFormed log) (hℓ : LogWellFormed ℓ) (hnot : ℓ ∉ logs)
    (hR : BatchRootCommitsLogs keccak R logs H mc b e)
    (hacc : LogProofAccepted keccak R ℓ j sibs k) :
    (k = H + 3 ∧ j < 2 ^ H
        ∧ ∃ log : L2Log, logs[j]? = some log ∧ HashCollision keccak (logPre log) (logPre ℓ))
      ∨ BatchWalkBreak (efficientHash keccak) (keccak logDefaultPre) (logsLeaves keccak logs) H
          mc b e sibs k j (logLeaf keccak ℓ) := by
  obtain ⟨hdef, -, hj, hwalk, -⟩ := hacc
  rw [hR] at hwalk
  rcases batch_walk_opens_or_break (efficientHash keccak) (keccak logDefaultPre)
      (logsLeaves keccak logs) H mc b e sibs k j (logLeaf keccak ℓ) hj hwalk
    with ⟨hk, hjH, hx⟩ | hb
  · left
    refine ⟨hk, hjH, ?_⟩
    rcases hlog : logs[j]? with _ | log
    · rw [logsLeaves_getD_none keccak hlog] at hx
      exact absurd hx.symm hdef
    · refine ⟨log, rfl, ?_, ?_⟩
      · intro hp
        have hmem : log ∈ logs := List.mem_of_getElem? hlog
        have hle : log = ℓ := logPre_inj (hwf log hmem) hℓ hp
        exact hnot (hle ▸ hmem)
      · rw [logsLeaves_getD_some keccak hlog] at hx
        exact hx
  · exact Or.inr hb

theorem status_proof_of_unreal_status (keccak : Keccak) (logs : List L2Log) (H : ℕ)
    (mc b e R : UInt256) (truth : UInt256 → Option TxStatus) (t : ℕ) (tx : UInt256)
    (s : TxStatus) (j : ℕ) (sibs : ℕ → UInt256) (k : ℕ)
    (hwf : ∀ log ∈ logs, LogWellFormed log) (ht : t < 256 ^ 2)
    (hR : BatchRootCommitsLogs keccak R logs H mc b e)
    (hB : BootloaderLogsAreStatusLogs truth logs) (hts : truth tx ≠ some s)
    (hacc : StatusProofAccepted keccak R t tx s j sibs k) :
    (k = H + 3 ∧ j < 2 ^ H
        ∧ ∃ log : L2Log, logs[j]? = some log
          ∧ HashCollision keccak (logPre log) (logPre (statusLog t tx s)))
      ∨ BatchWalkBreak (efficientHash keccak) (keccak logDefaultPre) (logsLeaves keccak logs) H
          mc b e sibs k j (logLeaf keccak (statusLog t tx s)) := by
  have hnot : statusLog t tx s ∉ logs := by
    intro hmem
    obtain ⟨t', tx', s', heq, htruth⟩ := hB _ hmem rfl
    have hkey : tx = tx' := congrArg L2Log.key heq
    have hs : s = s' := logLeaf_toWord_inj (congrArg L2Log.value heq)
    rw [← hkey, ← hs] at htruth
    exact hts htruth
  exact log_proof_of_absent_log keccak logs H mc b e R (statusLog t tx s) j sibs k hwf
    (statusLog_wellFormed tx s ht) hnot hR hacc

theorem failure_proof_for_succeeded_tx (keccak : Keccak) (logs : List L2Log) (H : ℕ)
    (mc b e R : UInt256) (truth : UInt256 → Option TxStatus) (t : ℕ) (tx : UInt256) (j : ℕ)
    (sibs : ℕ → UInt256) (k : ℕ)
    (hwf : ∀ log ∈ logs, LogWellFormed log) (ht : t < 256 ^ 2)
    (hR : BatchRootCommitsLogs keccak R logs H mc b e)
    (hB : BootloaderLogsAreStatusLogs truth logs) (hts : truth tx = some .success)
    (hacc : StatusProofAccepted keccak R t tx .failure j sibs k) :
    (k = H + 3 ∧ j < 2 ^ H
        ∧ ∃ log : L2Log, logs[j]? = some log
          ∧ HashCollision keccak (logPre log) (logPre (statusLog t tx .failure)))
      ∨ BatchWalkBreak (efficientHash keccak) (keccak logDefaultPre) (logsLeaves keccak logs) H
          mc b e sibs k j (logLeaf keccak (statusLog t tx .failure)) :=
  status_proof_of_unreal_status keccak logs H mc b e R truth t tx .failure j sibs k hwf ht hR hB
    (by rw [hts]; simp) hacc

/-! ## Certificates -/

theorem ChainBatchRootIsFold : Properties.ChainBatchRootIsFold := chainBatchRoot_eq_rootOf

theorem BatchWalkOpensLogsEntryOrBreak : Properties.BatchWalkOpensLogsEntryOrBreak :=
  batch_walk_opens_or_break

theorem HonestBatchWalkNoBreak : Properties.HonestBatchWalkNoBreak :=
  honest_batch_walk_no_break

theorem LogProofOfAbsentLogLocatesBreak : Properties.LogProofOfAbsentLogLocatesBreak :=
  log_proof_of_absent_log

theorem StatusProofOfUnrealStatusLocatesBreak : Properties.StatusProofOfUnrealStatusLocatesBreak :=
  status_proof_of_unreal_status

theorem FailureProofForSucceededTxLocatesBreak :
    Properties.FailureProofForSucceededTxLocatesBreak :=
  failure_proof_for_succeeded_tx

/-! ## The stand-in keccak -/

lemma pak_default : paddingAwareLengthKeccak logDefaultPre = 1 := by
  simp [paddingAwareLengthKeccak]

lemma pak_logLeaf (log : L2Log) (hne : logPre log ≠ logDefaultPre) :
    logLeaf paddingAwareLengthKeccak log = Nat.toUInt256 88 := by
  simp only [logLeaf, paddingAwareLengthKeccak, ite_eq_right hne, logPre_length]

lemma pak_node (a b : UInt256) : efficientHash paddingAwareLengthKeccak a b = Nat.toUInt256 64 := by
  have hne : nodePre a b ≠ logDefaultPre := by
    intro he
    have := congrArg List.length he
    rw [nodePre_length] at this
    simp [logDefaultPre] at this
  simp only [efficientHash, paddingAwareLengthKeccak, ite_eq_right hne, nodePre_length]

lemma pak_chainBatchRoot (lr mc b e : UInt256) :
    chainBatchRoot (efficientHash paddingAwareLengthKeccak) lr mc b e = Nat.toUInt256 64 := by
  simp only [chainBatchRoot, pak_node]

lemma statusPre_ne_default (t : ℕ) (tx : UInt256) (s : TxStatus) :
    logPre (statusLog t tx s) ≠ logDefaultPre :=
  StatusPreimageNeDefault.1 t tx s

theorem held_log_is_provable (keccak : Keccak) (logs : List L2Log) (H : ℕ) (mc b e R : UInt256)
    (j : ℕ) (log : L2Log) (hR : BatchRootCommitsLogs keccak R logs H mc b e)
    (hlog : logs[j]? = some log) (hj : j < 2 ^ H) (hH : H + 3 < 256) (hR0 : R ≠ 0)
    (hdef : logLeaf keccak log ≠ keccak logDefaultPre) :
    LogProofAccepted keccak R log j
      (honestBatchSibs (efficientHash keccak) (keccak logDefaultPre) (logsLeaves keccak logs) H
        mc b e j) (H + 3) := by
  have hhon := honest_batch_walk_no_break (efficientHash keccak) (keccak logDefaultPre)
    (logsLeaves keccak logs) H mc b e j hj
  have hleaf := logsLeaves_getD_some keccak hlog (keccak logDefaultPre)
  refine ⟨hdef, hH, hhon.1, ?_, hR0⟩
  rw [← hleaf, hR]
  exact hhon.2.1

theorem HeldLogIsProvable : Properties.HeldLogIsProvable := held_log_is_provable

theorem HeldLogIsProvableWitness : Properties.HeldLogIsProvableWitness := by
  unfold Properties.HeldLogIsProvableWitness
  have hR0 : chainBatchRoot (efficientHash paddingAwareLengthKeccak)
      (logsRootOf paddingAwareLengthKeccak
        [messageLog paddingAwareLengthKeccak ⟨2, 0x1234, [1, 2, 3]⟩, statusLog 3 5 .failure] 1)
      0 7 7 ≠ 0 := by
    rw [pak_chainBatchRoot]
    decide
  have hdef : logLeaf paddingAwareLengthKeccak (statusLog 3 5 .failure)
      ≠ paddingAwareLengthKeccak logDefaultPre := by
    rw [pak_logLeaf _ (statusPre_ne_default 3 5 .failure), pak_default]
    decide
  exact ⟨rfl, rfl, by norm_num, by norm_num, hR0, hdef,
    held_log_is_provable _ _ 1 0 7 7 _ 1 _ rfl rfl (by norm_num) (by norm_num) hR0 hdef⟩

/-! ## Witness and countermodels -/

theorem StatusProofWitness : Properties.StatusProofWitness := by
  let K := paddingAwareLengthKeccak
  let m : L2Message := ⟨2, 0x1234, [1, 2, 3]⟩
  let logs : List L2Log := [messageLog K m, statusLog 3 5 .success]
  let truth : UInt256 → Option TxStatus := fun x => if x = 5 then some .success else none
  let sibs := honestBatchSibs (efficientHash K) (K logDefaultPre) (logsLeaves K logs) 1 0 7 7 1
  have hhon := honest_batch_walk_no_break (efficientHash K) (K logDefaultPre) (logsLeaves K logs)
    1 0 7 7 1 (by norm_num)
  have hleaf : (logsLeaves K logs).getD 1 (K logDefaultPre)
      = logLeaf K (statusLog 3 5 .failure) := by
    rw [logsLeaves_getD_some K (log := statusLog 3 5 .success) rfl,
      pak_logLeaf _ (statusPre_ne_default 3 5 .success),
      pak_logLeaf _ (statusPre_ne_default 3 5 .failure)]
  have hmsgwf : LogWellFormed (messageLog K m) := ⟨by simp [messageLog, m], logLeaf_messenger_lt⟩
  refine ⟨K, logs, 1, 0, 7, 7,
    chainBatchRoot (efficientHash K) (logsRootOf K logs 1) 0 7 7, truth, 3, 5, 1, sibs, 4,
    ?_, by norm_num, statusLog_wellFormed 5 .failure (by norm_num), ?_, rfl, ?_,
    by simp [truth], by simp [truth], ?_, by norm_num, by norm_num, by decide, ?_, rfl,
    by norm_num, rfl, ?_⟩
  · intro log hlog
    simp only [logs, List.mem_cons, List.not_mem_nil, or_false] at hlog
    rcases hlog with rfl | rfl
    · exact hmsgwf
    · exact statusLog_wellFormed 5 .success (by norm_num)
  · intro hmem
    simp only [logs, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with he | he
    · exact absurd (congrArg L2Log.sender he) (by decide)
    · exact absurd (congrArg L2Log.value he) (by decide)
  · intro log hlog hs
    simp only [logs, List.mem_cons, List.not_mem_nil, or_false] at hlog
    rcases hlog with rfl | rfl
    · exact absurd hs (by decide)
    · exact ⟨3, 5, .success, rfl, by simp [truth]⟩
  · refine ⟨?_, by norm_num, by norm_num, ?_, ?_⟩
    · rw [pak_logLeaf _ (statusPre_ne_default 3 5 .failure)]
      show Nat.toUInt256 88 ≠ paddingAwareLengthKeccak logDefaultPre
      rw [pak_default]
      decide
    · rw [← hleaf]
      exact hhon.2.1
    · show chainBatchRoot (efficientHash paddingAwareLengthKeccak) _ 0 7 7 ≠ 0
      rw [pak_chainBatchRoot]
      decide
  · exact ⟨messageLog K m, by simp [logs], rfl⟩
  · refine ⟨fun hp => StatusPreimageFailureNeSuccess 3 3 5 5 hp.symm, ?_⟩
    show logLeaf K (statusLog 3 5 .success) = logLeaf K (statusLog 3 5 .failure)
    rw [pak_logLeaf _ (statusPre_ne_default 3 5 .success),
      pak_logLeaf _ (statusPre_ne_default 3 5 .failure)]

theorem BootloaderPremiseLoadBearing : Properties.BootloaderPremiseLoadBearing := by
  let other : L2Log := ⟨0, true, 1, 0x10012, 77, 0⟩
  let logs : List L2Log := [other, statusLog 3 5 .failure]
  let truth : UInt256 → Option TxStatus := fun x => if x = 5 then some .success else none
  refine ⟨logs, 1, 0, 7, 7, truth, 3, 5, 1, 4, ?_, by norm_num, by simp [truth], ?_, ?_, ?_, ?_⟩
  · intro log hlog
    simp only [logs, List.mem_cons, List.not_mem_nil, or_false] at hlog
    rcases hlog with rfl | rfl
    · exact ⟨by simp [other], by simp [other]⟩
    · exact statusLog_wellFormed 5 .failure (by norm_num)
  · intro hB
    obtain ⟨t', tx', s', heq, htruth⟩ := hB (statusLog 3 5 .failure) (by simp [logs]) rfl
    have hkey : (5 : UInt256) = tx' := congrArg L2Log.key heq
    have hs : TxStatus.failure = s' := logLeaf_toWord_inj (congrArg L2Log.value heq)
    rw [← hkey, ← hs] at htruth
    simp [truth] at htruth
  · intro keccak hR0 hdef
    let h := efficientHash keccak
    let z0 := keccak logDefaultPre
    let L := logsLeaves keccak logs
    have hhon := honest_batch_walk_no_break h z0 L 1 0 7 7 1 (by norm_num)
    have hleaf : L.getD 1 z0 = logLeaf keccak (statusLog 3 5 .failure) :=
      logsLeaves_getD_some keccak (log := statusLog 3 5 .failure) rfl z0
    refine ⟨honestBatchSibs h z0 L 1 0 7 7 1, ⟨hdef, by norm_num, by norm_num, ?_, hR0⟩, ?_⟩
    · rw [← hleaf]
      exact hhon.2.1
    · rintro (⟨-, -, log, hlog, hne, -⟩ | hb)
      · have hl : log = statusLog 3 5 .failure := by
          simp only [logs] at hlog
          exact (Option.some.inj hlog).symm
        exact hne (by rw [hl])
      · rw [← hleaf] at hb
        exact hhon.2.2 hb
  · rw [pak_chainBatchRoot]
    decide
  · rw [pak_logLeaf _ (statusPre_ne_default 3 5 .failure), pak_default]
    decide

theorem DefaultLeafCheckLoadBearing : Properties.DefaultLeafCheckLoadBearing := by
  let logs : List L2Log := [statusLog 3 5 .success]
  have hzero : logPre zeroLog = logDefaultPre := StatusPreimageNeDefault.2
  refine ⟨logs, 1, 0, 7, 7, 1, 4, ?_, ⟨by decide, by decide⟩, ?_, ?_, ?_, ?_⟩
  · intro log hlog
    simp only [logs, List.mem_cons, List.not_mem_nil, or_false] at hlog
    rw [hlog]
    exact statusLog_wellFormed 5 .success (by norm_num)
  · intro hmem
    simp only [logs, List.mem_cons, List.not_mem_nil, or_false] at hmem
    exact absurd (congrArg L2Log.isService hmem) (by decide)
  · simp only [logLeaf, hzero]
  · intro keccak hR0
    let h := efficientHash keccak
    let z0 := keccak logDefaultPre
    let L := logsLeaves keccak logs
    have hhon := honest_batch_walk_no_break h z0 L 1 0 7 7 1 (by norm_num)
    have hleaf : L.getD 1 z0 = logLeaf keccak zeroLog := by
      rw [logsLeaves_getD_none keccak (logs := logs) (j := 1) rfl z0]
      simp only [logLeaf, hzero, z0]
    refine ⟨honestBatchSibs h z0 L 1 0 7 7 1, by norm_num, by norm_num, ?_, ?_⟩
    · rw [← hleaf]
      exact hhon.2.1
    · rintro (⟨-, -, log, hlog, -⟩ | hb)
      · simp [logs] at hlog
      · rw [← hleaf] at hb
        exact hhon.2.2 hb
  · rw [pak_chainBatchRoot]
    decide

end Contracts.MessageVerification
