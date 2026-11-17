import EraSpec.Contracts.MessageVerification.Properties.StatusProofKeccak
import EraSpec.Contracts.MessageVerification.Proofs.StatusProof

/-!
# Proofs: the located breaks of a status proof are keccak collisions on named byte strings

Each `HeightBreak` and `PathCollision` case maps to one `StatusWalkKeccakBreak` case and back. The
only facts used are that `nodePre` is injective and 64 bytes long, and that every log preimage and
the padding preimage are 88 bytes long. Helper names carry the prefix `spk_` (this topic).
-/

namespace Contracts.MessageVerification

open Contracts.MessageHashing
open MerkleSpec MerkleSpec.Verifier
open AttackVectors.BundleHashEncoding (HashCollision)

/-! ## Byte facts -/

lemma spk_nodePre_inj {a b c d : UInt256} (h : nodePre a b = nodePre c d) : a = c ∧ b = d := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by rw [logLeaf_w32_length, logLeaf_w32_length])
  exact ⟨logLeaf_w32_inj h1, logLeaf_w32_inj h2⟩

lemma spk_pairPre_inj {p q : UInt256 × UInt256} (h : pairPre p = pairPre q) : p = q := by
  obtain ⟨h1, h2⟩ := spk_nodePre_inj h
  exact Prod.ext h1 h2

lemma spk_pairPre_length (p : UInt256 × UInt256) : (pairPre p).length = 64 :=
  nodePre_length p.1 p.2

/-- Different lengths make the strings different, so equal hashes are a collision. -/
lemma spk_crossLength_collision (keccak : Keccak) {u v : List UInt8} (hu : u.length = 88)
    (hv : v.length = 64) (h : keccak u = keccak v) : HashCollision keccak u v :=
  ⟨fun he => by rw [he] at hu; omega, h⟩

lemma logEntryPre_length (logs : List L2Log) (q : ℕ) : (logEntryPre logs q).length = 88 := by
  unfold logEntryPre
  split
  · exact logPre_length _
  · simp [logDefaultPre]

lemma logsLeaves_getD_eq (keccak : Keccak) (logs : List L2Log) (q : ℕ) :
    (logsLeaves keccak logs).getD q (keccak logDefaultPre) = keccak (logEntryPre logs q) := by
  rcases hq : logs[q]? with _ | log
  · rw [logsLeaves_getD_none keccak hq]
    simp [logEntryPre, hq]
  · rw [logsLeaves_getD_some keccak hq]
    simp [logEntryPre, hq, logLeaf]

/-! ## Path collisions -/

theorem spk_pathCollision_iff (keccak : Keccak) (z0 : UInt256) (L : List UInt256)
    (sibs : ℕ → UInt256) (lvl k j : ℕ) (x : UInt256) :
    PathCollision (efficientHash keccak) z0 L sibs lvl k j x
      ↔ PathKeccakCollision keccak z0 L sibs lvl k j x := by
  constructor
  · rintro ⟨i, hi, hne, heq⟩
    exact ⟨i, hi, fun hp => hne (spk_pairPre_inj hp), heq⟩
  · rintro ⟨i, hi, hne, heq⟩
    exact ⟨i, hi, fun hp => hne (by rw [hp]), heq⟩

/-! ## The two directions -/

theorem batchWalkBreak_to_keccak (keccak : Keccak) (logs : List L2Log) (H : ℕ) (mc b e : UInt256)
    (sibs : ℕ → UInt256) (k j : ℕ) (xPre : List UInt8) (hx : xPre.length = 88)
    (hb : BatchWalkBreak (efficientHash keccak) (keccak logDefaultPre) (logsLeaves keccak logs) H
      mc b e sibs k j (keccak xPre)) :
    StatusWalkKeccakBreak keccak logs H mc b e sibs k j xPre := by
  cases hb with
  | short hk hh =>
    cases hh with
    | shortInteriorLeaf _ he =>
      exact .shortLeafIsNode hk (spk_crossLength_collision keccak hx (spk_pairPre_length _) he)
    | shortCollision _ hc =>
      exact .shortCollision hk ((spk_pathCollision_iff keccak _ _ _ _ _ _ _).1 hc)
    | longEntryIsNode hlt _ => omega
    | longCollision hlt _ => omega
  | top m hm hc => exact .top m hm ((spk_pathCollision_iff keccak _ _ _ _ _ _ _).1 hc)
  | otherLeaf m hm hq he => exact .otherLeaf m hm hq he
  | logsCollision hk hj hc =>
    exact .logsCollision hk hj ((spk_pathCollision_iff keccak _ _ _ _ _ _ _).1 hc)
  | logsHeight m hm hj hh =>
    cases hh with
    | shortInteriorLeaf hlt he =>
      exact .logsLeafIsNode m hm hj hlt
        (spk_crossLength_collision keccak hx (spk_pairPre_length _) he)
    | shortCollision hlt hc =>
      exact .logsShortCollision m hm hj hlt ((spk_pathCollision_iff keccak _ _ _ _ _ _ _).1 hc)
    | longEntryIsNode hlt he =>
      refine .logsEntryIsNode m hm hj hlt
        (spk_crossLength_collision keccak (logEntryPre_length _ _) (spk_pairPre_length _) ?_)
      rw [← logsLeaves_getD_eq keccak logs]
      exact he
    | longCollision hlt hc =>
      exact .logsLongCollision m hm hj hlt ((spk_pathCollision_iff keccak _ _ _ _ _ _ _).1 hc)

theorem keccak_to_batchWalkBreak (keccak : Keccak) (logs : List L2Log) (H : ℕ) (mc b e : UInt256)
    (sibs : ℕ → UInt256) (k j : ℕ) (xPre : List UInt8)
    (hb : StatusWalkKeccakBreak keccak logs H mc b e sibs k j xPre) :
    BatchWalkBreak (efficientHash keccak) (keccak logDefaultPre) (logsLeaves keccak logs) H
      mc b e sibs k j (keccak xPre) := by
  cases hb with
  | shortLeafIsNode hk hc => exact .short hk (.shortInteriorLeaf (by omega) hc.2)
  | shortCollision hk hc =>
    exact .short hk
      (.shortCollision (by omega) ((spk_pathCollision_iff keccak _ _ _ _ _ _ _).2 hc))
  | top m hm hc => exact .top m hm ((spk_pathCollision_iff keccak _ _ _ _ _ _ _).2 hc)
  | otherLeaf m hm hq he => exact .otherLeaf m hm hq he
  | logsCollision hk hj hc =>
    exact .logsCollision hk hj ((spk_pathCollision_iff keccak _ _ _ _ _ _ _).2 hc)
  | logsLeafIsNode m hm hj hlt hc => exact .logsHeight m hm hj (.shortInteriorLeaf hlt hc.2)
  | logsShortCollision m hm hj hlt hc =>
    exact .logsHeight m hm hj
      (.shortCollision hlt ((spk_pathCollision_iff keccak _ _ _ _ _ _ _).2 hc))
  | logsEntryIsNode m hm hj hlt hc =>
    refine .logsHeight m hm hj (.longEntryIsNode hlt ?_)
    rw [logsLeaves_getD_eq]
    exact hc.2
  | logsLongCollision m hm hj hlt hc =>
    exact .logsHeight m hm hj
      (.longCollision hlt ((spk_pathCollision_iff keccak _ _ _ _ _ _ _).2 hc))

/-! ## Certificates -/

theorem PathCollisionIffKeccakCollision : Properties.PathCollisionIffKeccakCollision :=
  spk_pathCollision_iff

theorem BatchWalkBreakIffKeccakBreak : Properties.BatchWalkBreakIffKeccakBreak :=
  fun keccak logs H mc b e sibs k j xPre hx =>
    ⟨batchWalkBreak_to_keccak keccak logs H mc b e sibs k j xPre hx,
      keccak_to_batchWalkBreak keccak logs H mc b e sibs k j xPre⟩

theorem FailureProofForSucceededTxIsKeccakBreak :
    Properties.FailureProofForSucceededTxIsKeccakBreak := by
  intro keccak logs H mc b e R truth t tx j sibs k hwf ht hR hB hts hacc
  rcases failure_proof_for_succeeded_tx keccak logs H mc b e R truth t tx j sibs k hwf ht hR hB hts
      hacc with hc | hb
  · exact Or.inl hc
  · exact Or.inr (batchWalkBreak_to_keccak keccak logs H mc b e sibs k j _ (logPre_length _) hb)

theorem HonestStatusWalkNoKeccakBreak : Properties.HonestStatusWalkNoKeccakBreak := by
  intro keccak logs H mc b e j hj
  have he := (logsLeaves_getD_eq keccak logs j).symm
  refine ⟨he, fun hb => ?_⟩
  have hb' := keccak_to_batchWalkBreak keccak logs H mc b e _ (H + 3) j _ hb
  rw [he] at hb'
  exact (honest_batch_walk_no_break (efficientHash keccak) (keccak logDefaultPre)
    (logsLeaves keccak logs) H mc b e j hj).2.2 hb'

/-! ## Witness -/

lemma tvk_of_ne {x : List UInt8} (hx : x ≠ logDefaultPre) : twoValuedKeccak x = 2 := by
  simp [twoValuedKeccak, hx]

lemma tvk_node (a b : UInt256) : efficientHash twoValuedKeccak a b = 2 := by
  apply tvk_of_ne
  intro he
  have := congrArg List.length he
  rw [nodePre_length] at this
  simp [logDefaultPre] at this

theorem ShortStatusProofIsCrossLengthCollision :
    Properties.ShortStatusProofIsCrossLengthCollision := by
  have hfail : twoValuedKeccak (logPre (statusLog 3 5 .failure)) = 2 :=
    tvk_of_ne (statusPre_ne_default 3 5 .failure)
  have hroot : chainBatchRoot (efficientHash twoValuedKeccak)
      (logsRootOf twoValuedKeccak [statusLog 3 5 .success] 1) 0 7 7 = 2 := by
    simp only [chainBatchRoot, tvk_node]
  have hpair : twoValuedKeccak (pairPre (treePair (efficientHash twoValuedKeccak) 0
      (batchLeaves (logsRootOf twoValuedKeccak [statusLog 3 5 .success] 1) 0 7 7) 2 0)) = 2 :=
    tvk_node _ _
  have hcoll : HashCollision twoValuedKeccak (logPre (statusLog 3 5 .failure))
      (pairPre (treePair (efficientHash twoValuedKeccak) 0
        (batchLeaves (logsRootOf twoValuedKeccak [statusLog 3 5 .success] 1) 0 7 7) 2 0)) :=
    spk_crossLength_collision twoValuedKeccak (logPre_length _) (spk_pairPre_length _)
      (by rw [hfail, hpair])
  have hkb : StatusWalkKeccakBreak twoValuedKeccak [statusLog 3 5 .success] 1 0 7 7 (fun _ => 0)
      0 0 (logPre (statusLog 3 5 .failure)) :=
    .shortLeafIsNode (by norm_num) hcoll
  refine ⟨⟨?_, by norm_num, by norm_num, ?_, ?_⟩,
    keccak_to_batchWalkBreak _ _ _ _ _ _ _ _ _ _ hkb, hkb, hcoll⟩
  · show twoValuedKeccak (logPre (statusLog 3 5 .failure)) ≠ twoValuedKeccak logDefaultPre
    rw [hfail]
    simp [twoValuedKeccak]
  · show logLeaf twoValuedKeccak (statusLog 3 5 .failure) = _
    rw [hroot]
    exact hfail
  · rw [hroot]
    decide

end Contracts.MessageVerification
