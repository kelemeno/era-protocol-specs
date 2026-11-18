import EraSpec.Contracts.AtomicInteropProof.Properties.AuthenticateRootAtV35
import EraSpec.Contracts.AtomicInteropProof.Proofs.LastLeafFaithful

/-! # Proofs: the v35 `_authenticateRoot` refactor, and the walks the end branch relies on
(see `../Specs/AuthenticateRootAtV35.lean`) -/

namespace AttackVectors.AuthenticateRootAtV35

open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf MerkleSpec.LastLeafFaithful

/-! ## The building blocks, unfolded -/

/-- A successful `extractSlice` has the requested length. -/
theorem authV35_slice_length {w : Proof} {l r : ℕ} {s : List UInt256}
    (hs : slice w l r = some s) : s.length = r - l := by
  unfold slice at hs
  by_cases hb : l ≤ r ∧ (l = r ∨ r ≤ w.length)
  · rw [ite_eq_left hb] at hs
    cases hs
    rcases hb with ⟨hlr, rfl | hr⟩
    · simp
    · simp only [List.length_take, List.length_drop]
      omega
  · rw [ite_eq_right hb] at hs
    cases hs

/-- `calculateRootMemory` returned: the length and index checks passed, and the result is the
walk. -/
theorem authV35_calcRoot_some {h : Hash} {path : List UInt256} {index : ℕ} {item r : UInt256}
    (hc : calcRoot h path index item = some r) :
    path.length < 256 ∧ index < 2 ^ path.length
      ∧ r = walkPure h (fun l => path.getD l 0) 0 path.length index item := by
  unfold calcRoot at hc
  by_cases hb : path.length < 256 ∧ index < 2 ^ path.length
  · rw [ite_eq_left hb] at hc
    exact ⟨hb.1, hb.2, (Option.some.inj hc).symm⟩
  · rw [ite_eq_right hb] at hc
    cases hc

/-- `_getProofData` returned: its steps, unfolded. -/
theorem authV35_getProofData_some {E : Env} {c b m leaf : UInt256} {w : Proof} {pd : ProofData}
    (h : getProofData E c b m leaf w = some pd) :
    ∃ md, E.parse w = some md ∧ ∃ logPath bsr,
      slice w md.proofStartIndex (md.proofStartIndex + md.logLeafProofLen) = some logPath ∧
      calcRoot E.node logPath m.val leaf = some bsr ∧
      ((md.finalProofNode = true ∧
          pd = ⟨0, 0, 0, 0, bsr, 0, 0, md.proofStartIndex + md.logLeafProofLen, true⟩) ∨
        (md.finalProofNode = false ∧ ∃ t bmask bPath chainIdRoot packed slChain,
          word w (md.proofStartIndex + md.logLeafProofLen) = some t ∧
          word w (md.proofStartIndex + md.logLeafProofLen + 1) = some bmask ∧
          slice w (md.proofStartIndex + md.logLeafProofLen + 2)
            (md.proofStartIndex + md.logLeafProofLen + 2 + md.batchLeafProofLen) = some bPath ∧
          calcRoot E.node bPath bmask.val (E.batchLeaf bsr b t) = some chainIdRoot ∧
          word w (md.proofStartIndex + md.logLeafProofLen + 2 + md.batchLeafProofLen) = some packed ∧
          word w (md.proofStartIndex + md.logLeafProofLen + 3 + md.batchLeafProofLen) = some slChain ∧
          pd = ⟨slChain, hi128 packed, lo128 packed, md.batchLeafProofLen, bsr,
            E.chainIdLeaf chainIdRoot c, t,
            md.proofStartIndex + md.logLeafProofLen + 4 + md.batchLeafProofLen, false⟩)) := by
  unfold getProofData at h
  by_cases h1 : w = []
  · rw [ite_eq_left h1] at h; cases h
  rw [ite_eq_right h1] at h
  by_cases h2 : leaf = E.defaultLeaf
  · rw [ite_eq_left h2] at h; cases h
  rw [ite_eq_right h2, Option.bind_eq_some_iff] at h
  obtain ⟨md, hmd, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨logPath, hlog, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨bsr, hbsr, h⟩ := h
  refine ⟨md, hmd, logPath, bsr, hlog, hbsr, ?_⟩
  by_cases hfin : md.finalProofNode = true
  · rw [ite_eq_left hfin] at h
    cases h
    exact Or.inl ⟨hfin, rfl⟩
  · rw [ite_eq_right hfin] at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨t, ht, bmask, hbm, bPath, hbp, cr, hcr, packed, hp, slc, hs, h⟩ := h
    cases h
    exact Or.inr ⟨by simpa using hfin, t, bmask, bPath, cr, packed, slc, ht, hbm, hbp, hcr, hp, hs,
      rfl⟩

/-- The returned `finalProofNode` is the parsed flag. -/
theorem authV35_getProofData_final_eq {E : Env} {c b m leaf : UInt256} {w : Proof}
    {pd : ProofData} (h : getProofData E c b m leaf w = some pd) :
    ∃ md, E.parse w = some md ∧ pd.finalProofNode = md.finalProofNode := by
  obtain ⟨md, hmd, logPath, bsr, _, _, ⟨hf, hpd⟩ | ⟨hf, t, bmask, bPath, cr, packed, slc,
    _, _, _, _, _, _, hpd⟩⟩ := authV35_getProofData_some h
  · subst hpd
    exact ⟨md, hmd, hf.symm⟩
  · subst hpd
    exact ⟨md, hmd, hf.symm⟩

/-- A non-final first hop, unfolded. -/
theorem authV35_getProofData_nonfinal {E : Env} {c b m leaf : UInt256} {w : Proof}
    {pd : ProofData} (h : getProofData E c b m leaf w = some pd)
    (hf : pd.finalProofNode = false) :
    ∃ md, E.parse w = some md ∧ md.finalProofNode = false ∧
      ∃ logPath bsr t bmask bPath chainIdRoot packed slChain,
        slice w md.proofStartIndex (md.proofStartIndex + md.logLeafProofLen) = some logPath ∧
        calcRoot E.node logPath m.val leaf = some bsr ∧
        word w (md.proofStartIndex + md.logLeafProofLen) = some t ∧
        word w (md.proofStartIndex + md.logLeafProofLen + 1) = some bmask ∧
        slice w (md.proofStartIndex + md.logLeafProofLen + 2)
          (md.proofStartIndex + md.logLeafProofLen + 2 + md.batchLeafProofLen) = some bPath ∧
        calcRoot E.node bPath bmask.val (E.batchLeaf bsr b t) = some chainIdRoot ∧
        word w (md.proofStartIndex + md.logLeafProofLen + 2 + md.batchLeafProofLen) = some packed ∧
        word w (md.proofStartIndex + md.logLeafProofLen + 3 + md.batchLeafProofLen) = some slChain ∧
        pd = ⟨slChain, hi128 packed, lo128 packed, md.batchLeafProofLen, bsr,
          E.chainIdLeaf chainIdRoot c, t,
          md.proofStartIndex + md.logLeafProofLen + 4 + md.batchLeafProofLen, false⟩ := by
  obtain ⟨md, hmd, logPath, bsr, hlog, hbsr, ⟨-, hpd⟩ | ⟨hmf, t, bmask, bPath, cr, packed, slc,
    ht, hbm, hbp, hcr, hp, hs, hpd⟩⟩ := authV35_getProofData_some h
  · rw [hpd] at hf; cases hf
  · exact ⟨md, hmd, hmf, logPath, bsr, t, bmask, bPath, cr, packed, slc, hlog, hbsr, ht, hbm, hbp,
      hcr, hp, hs, hpd⟩

/-- A final hop, unfolded: its root is the log-leaf walk. -/
theorem authV35_getProofData_final {E : Env} {c b m leaf : UInt256} {w : Proof}
    {pd : ProofData} (h : getProofData E c b m leaf w = some pd)
    (hf : pd.finalProofNode = true) :
    ∃ md, E.parse w = some md ∧ md.finalProofNode = true ∧ ∃ logPath,
      slice w md.proofStartIndex (md.proofStartIndex + md.logLeafProofLen) = some logPath ∧
      calcRoot E.node logPath m.val leaf = some pd.batchSettlementRoot := by
  obtain ⟨md, hmd, logPath, bsr, hlog, hbsr, ⟨hmf, hpd⟩ | ⟨-, t, bmask, bPath, cr, packed, slc,
    -, -, -, -, -, -, hpd⟩⟩ := authV35_getProofData_some h
  · subst hpd
    exact ⟨md, hmd, hmf, logPath, hlog, hbsr⟩
  · rw [hpd] at hf; cases hf

/-- The first hop's log-leaf walk, final or not: `logHopPath` folds the claimed leaf into
`batchSettlementRoot`, and its length is the parsed `logLeafProofLen`. -/
theorem authV35_first_hop {E : Env} {c b m leaf : UInt256} {w : Proof} {pd : ProofData}
    (h : getProofData E c b m leaf w = some pd) :
    ∃ md lp, E.parse w = some md ∧ logHopPath E w = some lp ∧ lp.length = md.logLeafProofLen ∧
      calcRoot E.node lp m.val leaf = some pd.batchSettlementRoot := by
  obtain ⟨md, hmd, logPath, bsr, hlog, hbsr, ⟨-, hpd⟩ | ⟨-, t, bmask, bPath, cr, packed, slc,
    _, _, _, _, _, _, hpd⟩⟩ := authV35_getProofData_some h
  all_goals
    subst hpd
    refine ⟨md, logPath, hmd, ?_, ?_, hbsr⟩
    · simp only [logHopPath, hmd, Option.bind_some, hlog]
    · rw [authV35_slice_length hlog]
      omega

/-- The verifier returned `true`: the first hop, and (if it is not final) the recursive hop. -/
theorem authV35_proveShared_true {E : Env} {roots : UInt256 → UInt256 → UInt256}
    {c b m leaf : UInt256} {w : Proof} (h : proveShared E roots c b m leaf w = some true) :
    ∃ pd, getProofData E c b m leaf w = some pd ∧
      ((pd.finalProofNode = true ∧ roots c b = pd.batchSettlementRoot ∧ roots c b ≠ 0) ∨
        (pd.finalProofNode = false ∧ ∃ rest pd', slice w pd.ptr w.length = some rest ∧
          getProofData E pd.slChainId pd.slBatchNumber pd.slBatchRootMask pd.chainIdLeaf rest
            = some pd' ∧ pd'.finalProofNode = true
          ∧ roots pd.slChainId pd.slBatchNumber = pd'.batchSettlementRoot
          ∧ roots pd.slChainId pd.slBatchNumber ≠ 0)) := by
  unfold proveShared at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨pd, hpd, h⟩ := h
  refine ⟨pd, hpd, ?_⟩
  by_cases hf : pd.finalProofNode = true
  · rw [ite_eq_left hf] at h
    exact Or.inl ⟨hf, of_decide_eq_true (Option.some.inj h)⟩
  · rw [ite_eq_right hf, Option.bind_eq_some_iff] at h
    obtain ⟨rest, hrest, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨pd', hpd', h⟩ := h
    by_cases hf' : pd'.finalProofNode = true
    · rw [ite_eq_left hf'] at h
      exact Or.inr ⟨by simpa using hf, rest, pd', hrest, hpd', hf',
        of_decide_eq_true (Option.some.inj h)⟩
    · rw [ite_eq_right hf'] at h
      cases h

/-! ## The readers -/

theorem read_sl_eq_parsed_v35 : Properties.ReadSLEqParsedV35 := by
  intro E c b m leaf w pd h hf
  obtain ⟨md, hmd, hmf, logPath, bsr, t, bmask, bPath, cr, packed, slc, -, -, ht, -, -, -, hp, hs,
    rfl⟩ := authV35_getProofData_nonfinal h hf
  simp only [readSL, hmd, Option.bind_some, hmf, ht, hp, hs]
  rfl

theorem read_hop_is_folded_path_v35 : Properties.ReadHopIsFoldedPathV35 := by
  intro E c b m leaf w pd h hf
  obtain ⟨md, hmd, hmf, logPath, bsr, t, bmask, bPath, cr, packed, slc, -, -, -, hbm, hbp, hcr, -, -,
    rfl⟩ := authV35_getProofData_nonfinal h hf
  refine ⟨⟨bmask, bPath⟩, ?_, cr, hcr, rfl⟩
  simp only [readHop, hmd, Option.bind_some, hmf, hbm, hbp]
  rfl

/-- On a proof whose parsed metadata is not a final node, the v35 hop read is the pin's. -/
theorem authV35_readHop_eq_pin {E : Env} {w : Proof} {md : Metadata}
    (hmd : E.parse w = some md) (hmf : md.finalProofNode = false) :
    readHop E w = readHopPin E w := by
  simp only [readHop, readHopPin, hmd, Option.bind_some, hmf]
  rfl

/-! ## `_authenticateRoot` -/

/-- The v35 `_authenticateRoot` accepted: the metadata, the depth, the verifier and the read. -/
theorem authV35_auth_some {E : Env} {roots : UInt256 → UInt256 → UInt256}
    {src batch leafIndex imtRoot : UInt256} {w : Proof} {sl : SLRef}
    (h : authenticateRootV35 E roots src batch leafIndex imtRoot w = some sl) :
    ∃ md, E.parse w = some md ∧ md.logLeafProofLen = treeDepth ∧ md.finalProofNode = false
      ∧ proveShared E roots src batch leafIndex imtRoot w = some true ∧ readSL E w = some sl := by
  unfold authenticateRootV35 at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨md, hmd, h⟩ := h
  by_cases hd : md.logLeafProofLen ≠ treeDepth
  · rw [ite_eq_left hd] at h; cases h
  rw [ite_eq_right hd, Option.bind_eq_some_iff] at h
  obtain ⟨ok, hok, h⟩ := h
  by_cases hk : ok = false
  · rw [ite_eq_left hk] at h; cases h
  rw [ite_eq_right hk] at h
  by_cases hf : md.finalProofNode = true
  · rw [ite_eq_left hf] at h; cases h
  rw [ite_eq_right hf] at h
  have hok' : ok = true := by simpa using hk
  subst hok'
  exact ⟨md, hmd, not_not.mp hd, by simpa using hf, hok, h⟩

/-- **The v35 `_authenticateRoot` accepted: the first hop is not final, gave the returned triple,
and the recursive hop anchored at the returned coordinates.** -/
theorem authV35_accepted {E : Env} {roots : UInt256 → UInt256 → UInt256}
    {src batch leafIndex imtRoot : UInt256} {w : Proof} {sl : SLRef}
    (h : authenticateRootV35 E roots src batch leafIndex imtRoot w = some sl) :
    ∃ pd, getProofData E src batch leafIndex imtRoot w = some pd ∧ pd.finalProofNode = false ∧
      sl = ⟨pd.slBatchNumber, pd.slChainId, pd.l1BatchTimestamp⟩ ∧
      ∃ rest pd', slice w pd.ptr w.length = some rest ∧
        getProofData E pd.slChainId pd.slBatchNumber pd.slBatchRootMask pd.chainIdLeaf rest
          = some pd' ∧ pd'.finalProofNode = true
        ∧ roots pd.slChainId pd.slBatchNumber = pd'.batchSettlementRoot
        ∧ roots pd.slChainId pd.slBatchNumber ≠ 0 := by
  obtain ⟨md, hmd, -, hmf, hok, hread⟩ := authV35_auth_some h
  obtain ⟨pd, hpd, hcase⟩ := authV35_proveShared_true hok
  obtain ⟨md', hmd', hfeq⟩ := authV35_getProofData_final_eq hpd
  rw [hmd] at hmd'
  cases hmd'
  have hpf : pd.finalProofNode = false := hfeq.trans hmf
  rcases hcase with ⟨hpt, -⟩ | ⟨-, rest⟩
  · rw [hpf] at hpt; cases hpt
  have hsl := read_sl_eq_parsed_v35 E src batch leafIndex imtRoot w pd hpd hpf
  rw [hread] at hsl
  exact ⟨pd, hpd, hpf, Option.some.inj hsl, rest⟩

theorem authenticate_root_refactor_exact_v35 : Properties.AuthenticateRootRefactorExactV35 := by
  intro E roots src batch leafIndex imtRoot w
  unfold authenticateRootV35 authenticateRootPin
  cases hmd : E.parse w with
  | none => rfl
  | some md =>
    simp only [Option.bind_some]
    by_cases hd : md.logLeafProofLen ≠ treeDepth
    · rw [ite_eq_left hd, ite_eq_left hd]
    rw [ite_eq_right hd, ite_eq_right hd]
    cases hok : proveShared E roots src batch leafIndex imtRoot w with
    | none => rfl
    | some ok =>
      simp only [Option.bind_some]
      by_cases hk : ok = false
      · rw [ite_eq_left hk, ite_eq_left hk]
      rw [ite_eq_right hk, ite_eq_right hk]
      have hok' : ok = true := by simpa using hk
      subst hok'
      obtain ⟨pd, hpd, -⟩ := authV35_proveShared_true hok
      obtain ⟨md', hmd', hfeq⟩ := authV35_getProofData_final_eq hpd
      rw [hmd] at hmd'
      cases hmd'
      rw [hpd, Option.bind_some]
      by_cases hf : md.finalProofNode = true
      · rw [ite_eq_left hf, ite_eq_left (hfeq.trans hf)]
      · have hpf : pd.finalProofNode = false := by simpa [hfeq] using hf
        rw [ite_eq_right hf, ite_eq_right (by simpa using hpf)]
        exact read_sl_eq_parsed_v35 E src batch leafIndex imtRoot w pd hpd hpf

theorem hop_read_total_after_auth_v35 : Properties.HopReadTotalAfterAuthV35 := by
  intro E roots src batch leafIndex imtRoot w sl h
  obtain ⟨pd, hpd, hpf, -⟩ := authV35_accepted h
  obtain ⟨hop, hhop, -⟩ := read_hop_is_folded_path_v35 E src batch leafIndex imtRoot w pd hpd hpf
  exact ⟨hop, hhop⟩

theorem end_branch_refactor_exact_v35 : Properties.EndBranchRefactorExactV35 := by
  intro E roots z0 src batch imtRoot w sl hop
  constructor
  · rintro ⟨hauth, hhop, hlast⟩
    obtain ⟨md, hmd, -, hmf, -⟩ := authV35_auth_some hauth
    refine ⟨?_, ?_, hlast⟩
    · rw [← authenticate_root_refactor_exact_v35]; exact hauth
    · rw [← authV35_readHop_eq_pin hmd hmf]; exact hhop
  · rintro ⟨hauth, hhop, hlast⟩
    have hauth' : authenticateRootV35 E roots src batch imtEndLeafIndex imtRoot w = some sl := by
      rw [authenticate_root_refactor_exact_v35]; exact hauth
    obtain ⟨md, hmd, -, hmf, -⟩ := authV35_auth_some hauth'
    exact ⟨hauth', by rw [authV35_readHop_eq_pin hmd hmf]; exact hhop, hlast⟩

/-! ## The walks -/

theorem last_batch_check_on_verified_walk_v35 : Properties.LastBatchCheckOnVerifiedWalkV35 := by
  intro E roots z0 src batch imtRoot w sl hop hpass
  obtain ⟨pd, hpd, hpf, hsl, -⟩ := authV35_accepted hpass.auth
  obtain ⟨hop', hhop', cr, hcr, hcl⟩ :=
    read_hop_is_folded_path_v35 E src batch imtEndLeafIndex imtRoot w pd hpd hpf
  rw [hpass.hop_eq] at hhop'
  cases hhop'
  obtain ⟨-, hlt, rfl⟩ := authV35_calcRoot_some hcr
  subst hsl
  exact ⟨pd, hpd, hpf, rfl, hlt, hcl, fun l hl hb => hpass.last l hl hb⟩

theorem sl_hop_is_verified_walk_v35 : Properties.SLHopIsVerifiedWalkV35 := by
  intro E roots src batch leafIndex imtRoot w sl h
  obtain ⟨pd, hpd, hpf, hsl, rest, pd', hrest, hpd', hf', hroot, hne⟩ := authV35_accepted h
  obtain ⟨md', hmd', -, sp, hsp, hcalc⟩ := authV35_getProofData_final hpd' hf'
  obtain ⟨-, hlt, hwalk⟩ := authV35_calcRoot_some hcalc
  subst hsl
  refine ⟨pd, sp, hpd, hpf, rfl, ?_, hlt, (hwalk.symm.trans hroot.symm), hne⟩
  simp only [slHopPath, hrest, Option.bind_some, hmd', hsp]

/-! ## The last leaf -/

/-- The batch-leaf path of an accepted end branch, as `LastLeafFaithful` takes it, once its walk
is known to reach the chain tree's root. -/
theorem authV35_lastBatchPathAccepted {E : Env} {z0 : UInt256} {L : List UInt256} {height : ℕ}
    {hop : HopPath} {x : UInt256} (hlt : hop.mask.val < 2 ^ hop.sibs.length)
    (hroot : walkPure E.node (fun l => hop.sibs.getD l 0) 0 hop.sibs.length hop.mask.val x
      = rootOf E.node z0 L height)
    (hzero : ∀ l < hop.sibs.length, (hop.mask.val / 2 ^ l) % 2 = 0 →
      (fun l => hop.sibs.getD l 0) l = zeros E.node z0 l) :
    LastBatchPathAccepted E.node z0 L height (fun l => hop.sibs.getD l 0) hop.sibs.length
      hop.mask.val x :=
  ⟨hlt, hroot, hzero⟩

theorem end_branch_last_leaf_or_break_v35 : Properties.EndBranchLastLeafOrBreakV35 := by
  intro E roots z0 src batch imtRoot w sl hop L height hpass hcap hbind
  obtain ⟨pd, hpd, -, -, hlt, hcl, hzero⟩ :=
    last_batch_check_on_verified_walk_v35 E roots z0 src batch imtRoot w sl hop hpass
  refine ⟨pd, hpd, ?_⟩
  dsimp only
  have hleaf := hcl.symm.trans (hbind pd hpd)
  by_cases hw : walkPure E.node (fun l => hop.sibs.getD l 0) 0 hop.sibs.length hop.mask.val
      (E.batchLeaf pd.batchSettlementRoot batch sl.l1BatchTimestamp) = rootOf E.node z0 L height
  · right
    rcases accepted_last_leaf_any_length_or_break E.node z0 L _ _ _ _ _ hcap
        (authV35_lastBatchPathAccepted hlt hw hzero) with
      ⟨hk, hj, -⟩ | hb | ⟨hk, hle, hx⟩ | ⟨hk, hp⟩ | ⟨hk, hc⟩
    · exact Or.inl ⟨hk, by omega, Or.inl hj⟩
    · exact Or.inr (Or.inr hb)
    · exact Or.inr (Or.inl ⟨hk, hle, Or.inl hx⟩)
    · have hjl : hop.mask.val + 1 < L.length := by cases hp <;> assumption
      exact Or.inl ⟨hk, by omega, Or.inr (Or.inl hp)⟩
    · rw [hk] at hc
      by_cases hj : hop.mask.val < L.length
      · exact Or.inl ⟨hk, hj, Or.inr (Or.inr hc)⟩
      · exact Or.inr (Or.inl ⟨hk, not_lt.mp hj, Or.inr hc⟩)
  · exact Or.inl ⟨hw, hleaf⟩

theorem end_branch_two_hop_last_leaf_or_break_v35 :
    Properties.EndBranchTwoHopLastLeafOrBreakV35 := by
  intro E roots z0 zS src batch imtRoot w sl hop B L height hpass hcap hslot
  obtain ⟨pd, hpd, hpf, hsl, hlt, hcl, hzero⟩ :=
    last_batch_check_on_verified_walk_v35 E roots z0 src batch imtRoot w sl hop hpass
  obtain ⟨pd₂, sp, hpd₂, -, -, hsp, hm, hwalkS, -⟩ :=
    sl_hop_is_verified_walk_v35 E roots src batch imtEndLeafIndex imtRoot w sl hpass.auth
  rw [hpd] at hpd₂
  cases hpd₂
  refine ⟨pd, sp, hpd, hsp, ?_⟩
  dsimp only
  set walk := walkPure E.node (fun l => hop.sibs.getD l 0) 0 hop.sibs.length hop.mask.val
    (E.batchLeaf pd.batchSettlementRoot batch sl.l1BatchTimestamp) with hwalk_def
  rcases AcceptPinsEntryAnyLengthOrBreak E.node zS B.slots (fun l => sp.getD l 0) sp.length
      B.height pd.slBatchRootMask.val pd.chainIdLeaf hm (hwalkS.trans B.root) with
    ⟨-, hopen⟩ | ⟨hk, hc⟩ | hb
  · by_cases hmS : pd.slBatchRootMask.val < B.slots.length
    · have hslotEq := hopen.symm.trans (B.slot _ hmS)
      rw [hcl] at hslotEq
      by_cases hpair : (walk, src) = (B.chainRoot pd.slBatchRootMask.val,
          B.chainAt pd.slBatchRootMask.val)
      · simp only [Prod.mk.injEq] at hpair
        obtain ⟨hw, hsrc⟩ := hpair
        have hroot : walk = rootOf E.node z0 L height := hw.trans (hslot _ hmS hsrc.symm)
        rcases accepted_last_leaf_any_length_or_break E.node z0 L _ _ _ _ _ hcap
            (authV35_lastBatchPathAccepted hlt hroot hzero) with hl | hb
        · exact Or.inl hl
        · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr (SLHopBreak.chainIdLeafCollision hmS hpair hslotEq))
    · have hpad : B.slots.getD pd.slBatchRootMask.val zS = zS :=
        getD_default _ _ _ (not_lt.mp hmS)
      rw [hpad, hcl] at hopen
      exact Or.inr (Or.inr (SLHopBreak.paddedSlot (not_lt.mp hmS) hopen.symm))
  · rw [hk, hcl] at hc
    exact Or.inr (Or.inr (SLHopBreak.pathCollision hk hc))
  · rw [hcl] at hb
    exact Or.inr (Or.inr (SLHopBreak.wrongLength hb))

/-! ## What `_authenticateRoot` authenticates -/

theorem authenticate_root_sound_v35 : Properties.AuthenticateRootSoundV35 := by
  intro E roots z0 zS src batch leafIndex imtRoot w sl B L height C hauth hslot
  obtain ⟨md, hmd, hdepth, -, -, -⟩ := authV35_auth_some hauth
  obtain ⟨pd, hpd, hpf, hsl, -⟩ := authV35_accepted hauth
  obtain ⟨md', lp, hmd', hlp, hlplen, hfirst⟩ := authV35_first_hop hpd
  rw [hmd] at hmd'
  cases hmd'
  obtain ⟨hop, hhop, cr, hcr, hcl⟩ :=
    read_hop_is_folded_path_v35 E src batch leafIndex imtRoot w pd hpd hpf
  obtain ⟨-, hlt, hcrEq⟩ := authV35_calcRoot_some hcr
  obtain ⟨pd₂, sp, hpd₂, -, -, hsp, hm, hwalkS, -⟩ :=
    sl_hop_is_verified_walk_v35 E roots src batch leafIndex imtRoot w sl hauth
  rw [hpd] at hpd₂
  cases hpd₂
  refine ⟨pd, lp, sp, hop, hpd, hlp, hhop, hsp, ?_⟩
  have ht : pd.l1BatchTimestamp = sl.l1BatchTimestamp := by rw [hsl]
  rw [ht] at hcrEq
  subst hcrEq
  set walk := walkPure E.node (fun l => hop.sibs.getD l 0) 0 hop.sibs.length hop.mask.val
    (E.batchLeaf pd.batchSettlementRoot batch sl.l1BatchTimestamp) with hwalk_def
  -- the outer hop
  rcases AcceptPinsEntryAnyLengthOrBreak E.node zS B.slots (fun l => sp.getD l 0) sp.length
      B.height pd.slBatchRootMask.val pd.chainIdLeaf hm (hwalkS.trans B.root) with
    ⟨-, hopen⟩ | ⟨hk, hc⟩ | hb
  rotate_left
  · rw [hk, hcl] at hc
    exact Or.inr (Or.inr (SLHopBreak.pathCollision hk hc))
  · rw [hcl] at hb
    exact Or.inr (Or.inr (SLHopBreak.wrongLength hb))
  by_cases hmS : pd.slBatchRootMask.val < B.slots.length
  rotate_left
  · have hpad : B.slots.getD pd.slBatchRootMask.val zS = zS := getD_default _ _ _ (not_lt.mp hmS)
    rw [hpad, hcl] at hopen
    exact Or.inr (Or.inr (SLHopBreak.paddedSlot (not_lt.mp hmS) hopen.symm))
  have hslotEq := hopen.symm.trans (B.slot _ hmS)
  rw [hcl] at hslotEq
  by_cases hpair : (walk, src) = (B.chainRoot pd.slBatchRootMask.val, B.chainAt pd.slBatchRootMask.val)
  rotate_left
  · exact Or.inr (Or.inr (SLHopBreak.chainIdLeafCollision hmS hpair hslotEq))
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨hw, hsrc⟩ := hpair
  have hroot : walk = rootOf E.node z0 L height := hw.trans (hslot _ hmS hsrc.symm)
  -- the batch-leaf hop
  rcases AcceptPinsEntryAnyLengthOrBreak E.node z0 L (fun l => hop.sibs.getD l 0) hop.sibs.length
      height hop.mask.val (E.batchLeaf pd.batchSettlementRoot batch sl.l1BatchTimestamp) hlt hroot with
    ⟨hk, hentry⟩ | ⟨hk, hc⟩ | hb
  rotate_left
  · rw [hk] at hc
    exact Or.inr (Or.inl (AuthBreak.batchPathCollision hk hc))
  · exact Or.inr (Or.inl (AuthBreak.batchPathLength hb))
  by_cases hj : hop.mask.val < L.length
  rotate_left
  · rw [getD_default _ _ _ (not_lt.mp hj)] at hentry
    exact Or.inr (Or.inl (AuthBreak.paddedEntry hk (not_lt.mp hj) hentry.symm))
  have hleaf := hentry.symm.trans (C.entry _ hj)
  by_cases htrip : (pd.batchSettlementRoot, batch, sl.l1BatchTimestamp)
      = (C.batchRoot hop.mask.val, C.number hop.mask.val, C.timestamp hop.mask.val)
  rotate_left
  · exact Or.inr (Or.inl (AuthBreak.batchLeafCollision hj htrip hleaf))
  simp only [Prod.mk.injEq] at htrip
  obtain ⟨hbsr, hbatch, hts⟩ := htrip
  -- the first hop, at the pinned depth
  obtain ⟨-, hidx, hfw⟩ := authV35_calcRoot_some hfirst
  rw [hlplen, hdepth] at hidx hfw
  have hbr : walkPure E.node (fun l => lp.getD l 0) 0 treeDepth leafIndex.val imtRoot
      = rootOf E.node 0 (C.rootLeaves hop.mask.val) treeDepth :=
    hfw.symm.trans (hbsr.trans (C.batchRootTree _ hj))
  rcases AcceptPinsEntryOrCollision E.node 0 (C.rootLeaves hop.mask.val) (fun l => lp.getD l 0)
      treeDepth leafIndex.val imtRoot hidx hbr with hgood | hc
  · exact Or.inl ⟨hk, hj, hbatch.symm, hts.symm, hgood⟩
  · exact Or.inr (Or.inl (AuthBreak.logPathCollision hj hc))

theorem end_branch_sound_v35 : Properties.EndBranchSoundV35 := by
  intro E roots z0 zS src batch imtRoot w sl hop B L height C hpass hcap hslot
  obtain ⟨pd, sp, hpd, hsp, hlast⟩ :=
    end_branch_two_hop_last_leaf_or_break_v35 E roots z0 zS src batch imtRoot w sl hop B L height
      hpass hcap hslot
  obtain ⟨pd', lp, sp', hop', hpd', hlp, hhop', hsp', hauth⟩ :=
    authenticate_root_sound_v35 E roots z0 zS src batch imtEndLeafIndex imtRoot w sl B L height C
      hpass.auth hslot
  rw [hpd] at hpd'
  cases hpd'
  rw [hpass.hop_eq] at hhop'
  cases hhop'
  rw [hsp] at hsp'
  cases hsp'
  refine ⟨pd, lp, sp, hpd, hlp, hsp, ?_⟩
  dsimp only at hlast ⊢
  have h3 : (imtEndLeafIndex).val = 3 := rfl
  rw [h3] at hauth
  rcases hlast with ⟨hk, hlastj, -⟩ | hb | hb
  · rcases hauth with ⟨-, -, hnum, hts, hroot⟩ | hb | hb
    · exact Or.inl ⟨hk, hlastj, hnum, hts, hroot⟩
    · exact Or.inr (Or.inr (Or.inl hb))
    · exact Or.inr (Or.inr (Or.inr hb))
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr (Or.inr hb))

/-! ## The witness -/

/-- The demo first hop. -/
theorem authV35_demo_getProofData :
    getProofData authDemoEnv 300 2 imtEndLeafIndex 43 authDemoProof
      = some ⟨7, 9, 1, 2, authDemoBatchRoot, authDemoEnv.chainIdLeaf authDemoChainRoot 300, 100,
          10, false⟩ := by
  decide

theorem authV35_demo_auth :
    authenticateRootV35 authDemoEnv authDemoRoots 300 2 imtEndLeafIndex 43 authDemoProof
      = some ⟨9, 7, 100⟩ := by
  decide

theorem authV35_demo_readHop :
    readHop authDemoEnv authDemoProof
      = some ⟨2, [authDemoZ0, authDemoEnv.node (authDemoEntryLeaf 0) (authDemoEntryLeaf 1)]⟩ := by
  decide

theorem authV35_demo_logHopPath :
    logHopPath authDemoEnv authDemoProof
      = some [42, authDemoEnv.node 0 0, zeros authDemoEnv.node 0 2] := by
  decide

theorem authV35_demo_slHopPath :
    slHopPath authDemoEnv authDemoProof
      ⟨7, 9, 1, 2, authDemoBatchRoot, authDemoEnv.chainIdLeaf authDemoChainRoot 300, 100, 10, false⟩
      = some [authDemoEnv.chainIdLeaf 0 7] := by
  decide

theorem end_branch_v35_satisfiable : Properties.EndBranchV35Satisfiable := by
  refine ⟨authDemoEnv, authDemoRoots, authDemoZ0, authDemoZ0, 300, 2, 43, authDemoProof,
    ⟨9, 7, 100⟩, ⟨2, [authDemoZ0, authDemoEnv.node (authDemoEntryLeaf 0) (authDemoEntryLeaf 1)]⟩,
    authDemoShared, authDemoChainLeaves, 2, authDemoEntries,
    ⟨7, 9, 1, 2, authDemoBatchRoot, authDemoEnv.chainIdLeaf authDemoChainRoot 300, 100, 10, false⟩,
    [42, authDemoEnv.node 0 0, zeros authDemoEnv.node 0 2], [authDemoEnv.chainIdLeaf 0 7], rfl,
    ⟨authV35_demo_auth, authV35_demo_readHop, ?_⟩, authV35_demo_getProofData, rfl,
    authV35_demo_logHopPath, authV35_demo_slHopPath, ⟨0, by decide, by decide⟩, rfl, rfl, rfl,
    by decide, ?_, ?_, ?_, ?_⟩
  · -- the zero check: level 0 turns left, and its sibling is `zeros 0`
    intro i hi hb
    have hi' : i < 2 := hi
    interval_cases i
    · rfl
    · exact absurd hb (by decide)
  · intro pd' hpd'
    rw [authV35_demo_getProofData] at hpd'
    cases hpd'
    show authDemoEnv.chainIdLeaf authDemoChainRoot 300 = _
    rfl
  · intro i hi hsrc
    have hi' : i < 2 := hi
    interval_cases i
    · exact absurd hsrc (by decide)
    · rfl
  · -- no break on the outer hop
    rintro (⟨hm, hpair, -⟩ | ⟨hm, -⟩ | ⟨-, ⟨i, hi, hne, -⟩⟩ | hb)
    · exact hpair (by decide)
    · exact absurd hm (by decide)
    · have hi' : i < 1 := hi
      obtain rfl : i = 0 := by omega
      exact hne (by decide)
    · exact HeightBreakNotTautology.1 _ _ _ _ _ _ _ hb
  · -- no break on the first hop or the batch-leaf hop
    rintro (⟨-, ⟨i, hi, hne, -⟩⟩ | hb | ⟨-, hle, -⟩ | ⟨-, htrip, -⟩ | ⟨-, ⟨i, hi, hne, -⟩⟩)
    · have hi' : i < 2 := hi
      interval_cases i
      · exact hne (by decide)
      · exact hne (by decide)
    · exact HeightBreakNotTautology.1 _ _ _ _ _ _ _ hb
    · exact absurd hle (by decide)
    · exact htrip (by decide)
    · have hi' : i < 3 := hi
      interval_cases i
      · exact hne (by decide)
      · exact hne (by decide)
      · exact hne (by decide)

/-! ## The named properties -/

theorem ReadSLEqParsedV35 : Properties.ReadSLEqParsedV35 := read_sl_eq_parsed_v35

theorem ReadHopIsFoldedPathV35 : Properties.ReadHopIsFoldedPathV35 := read_hop_is_folded_path_v35

theorem AuthenticateRootRefactorExactV35 : Properties.AuthenticateRootRefactorExactV35 :=
  authenticate_root_refactor_exact_v35

theorem EndBranchRefactorExactV35 : Properties.EndBranchRefactorExactV35 :=
  end_branch_refactor_exact_v35

theorem HopReadTotalAfterAuthV35 : Properties.HopReadTotalAfterAuthV35 :=
  hop_read_total_after_auth_v35

theorem LastBatchCheckOnVerifiedWalkV35 : Properties.LastBatchCheckOnVerifiedWalkV35 :=
  last_batch_check_on_verified_walk_v35

theorem SLHopIsVerifiedWalkV35 : Properties.SLHopIsVerifiedWalkV35 := sl_hop_is_verified_walk_v35

theorem EndBranchLastLeafOrBreakV35 : Properties.EndBranchLastLeafOrBreakV35 :=
  end_branch_last_leaf_or_break_v35

theorem EndBranchTwoHopLastLeafOrBreakV35 : Properties.EndBranchTwoHopLastLeafOrBreakV35 :=
  end_branch_two_hop_last_leaf_or_break_v35

theorem AuthenticateRootSoundV35 : Properties.AuthenticateRootSoundV35 :=
  authenticate_root_sound_v35

theorem EndBranchSoundV35 : Properties.EndBranchSoundV35 := end_branch_sound_v35

theorem EndBranchV35Satisfiable : Properties.EndBranchV35Satisfiable := end_branch_v35_satisfiable

end AttackVectors.AuthenticateRootAtV35
