import EraSpec.Contracts.ChainTypeManager.Properties.UpgradeTxNonces
import EraSpec.Contracts.ChainTypeManager.Proofs.CommittedEdgeExecutable

/-!
# Proofs: the L2 upgrade transaction's nonce along one chain's history

Checked derivations of the statements in
`EraSpec.Contracts.ChainTypeManager.Properties.UpgradeTxNonces`.
-/

namespace Contracts.ChainTypeManager.EdgeChecks

/-! ## The chain-side functions, read backwards -/

/-- How `_setL2SystemContractUpgrade` can succeed. -/
theorem setL2_some {H : L2Tx → ℕ} {c : ChainUpgradeState} {mp : ℕ} {tx : L2Tx} {m : ℕ} {p : Bool}
    {hsh : ℕ} {c' : ChainUpgradeState}
    (h : setL2SystemContractUpgrade H c mp tx m p = some (hsh, c')) :
    (tx.txType = 0 ∧ hsh = 0 ∧ c' = c) ∨
      (tx.txType ≠ 0 ∧ p = false ∧ tx.nonce = m ∧ hsh = H tx ∧ c' = { c with h := H tx }) := by
  unfold setL2SystemContractUpgrade at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨h1, h.1.symm, h.2.symm⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    refine Or.inr ⟨h1, ?_, not_not.mp h6, h.1.symm, h.2.symm⟩
    simpa using h3

/-- How a crossing on the settlement layer can succeed. -/
theorem cross_facts {H : L2Tx → ℕ} {c : ChainUpgradeState} {mp newV : ℕ} {tx : L2Tx} {hsh : ℕ}
    {c' : ChainUpgradeState} (h : upgradeStoragePart H c mp newV tx true = some (hsh, c')) :
    EdgeVersionShape c.pv newV ∧ (minorOf newV ≠ minorOf c.pv → c.h = 0 ∧ c.b = 0) ∧
      ((tx.txType = 0 ∧ c' = { c with pv := newV }) ∨
        (tx.txType ≠ 0 ∧ minorOf newV ≠ minorOf c.pv ∧ tx.nonce = minorOf newV ∧
          c' = { c with pv := newV, h := H tx })) := by
  rw [upgradeStoragePart_onSL] at h
  cases hV : setNewProtocolVersion c newV true with
  | none => rw [hV] at h; exact absurd h (by simp)
  | some r =>
    rw [hV, Option.bind_some] at h
    obtain ⟨hS, hclean, rfl⟩ := (setNewProtocolVersion_some_iff c newV true r).mp hV
    refine ⟨hS, fun hne => hclean hne rfl, ?_⟩
    rcases setL2_some h with ⟨h0, _, rfl⟩ | ⟨h0, hp, hn, _, rfl⟩
    · exact Or.inl ⟨h0, rfl⟩
    · refine Or.inr ⟨h0, ?_, hn, rfl⟩
      intro heq
      simp [heq] at hp

/-- The genesis version step on a fresh diamond at its own version. -/
theorem genesisVersion_self (v0 : ℕ) :
    setNewProtocolVersionGenesis ⟨v0, 0, 0⟩ v0 true =
      if VersionWf v0 then some (minorOf v0, false, ⟨v0, 0, 0⟩) else none := by
  unfold setNewProtocolVersionGenesis
  rw [ite_eq_right (lt_irrefl v0)]
  by_cases h2 : v0 < 2 ^ 96
  · rw [unpackChecked_of_lt h2]
    simp only
    by_cases hA : majorOf v0 = 0
    · rw [ite_eq_right (not_not.mpr hA), ite_eq_right (not_not.mpr hA), ite_eq_right (lt_irrefl _),
        Nat.sub_self, ite_eq_right (by decide), ite_eq_right (by decide),
        ite_eq_right (by simp), ite_eq_left ⟨h2, hA⟩]
    · rw [ite_eq_left hA, ite_eq_right (by rintro ⟨_, h⟩; exact hA h)]
  · rw [unpackChecked_of_not_lt h2, ite_eq_right (by rintro ⟨h, _⟩; exact h2 h)]

/-- How a genesis can succeed. -/
theorem genesis_facts {H : L2Tx → ℕ} {v0 mp : ℕ} {tx : L2Tx} {hsh : ℕ} {c' : ChainUpgradeState}
    (h : genesisStoragePart H ⟨v0, 0, 0⟩ mp tx = some (hsh, c')) :
    VersionWf v0 ∧ c'.pv = v0 ∧
      (tx.txType = 0 ∨ (tx.txType ≠ 0 ∧ tx.nonce = minorOf v0)) := by
  unfold genesisStoragePart at h
  rw [genesisVersion_self] at h
  by_cases hw : VersionWf v0
  · rw [ite_eq_left hw] at h
    simp only at h
    refine ⟨hw, ?_, ?_⟩
    · rcases setL2_some h with ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> rfl
    · rcases setL2_some h with ⟨h0, _, _⟩ | ⟨h0, _, hn, _, _⟩
      · exact Or.inl h0
      · exact Or.inr ⟨h0, hn⟩
  · rw [ite_eq_right hw] at h
    exact absurd h (by simp)

/-! ## Point updates of the diamond map -/

theorem upd_dia_eq (f : ℕ → Option NonceDiamond) (d d' : ℕ) (x : NonceDiamond) :
    upd f d (some x) d' = if d' = d then some x else f d' := rfl

theorem commitBatchState_pv (c : ChainUpgradeState) (n : ℕ) : (commitBatchState c n).pv = c.pv := by
  unfold commitBatchState; split_ifs <;> rfl

theorem executeBatchesState_pv (c : ChainUpgradeState) (e : ℕ) :
    (executeBatchesState c e).pv = c.pv := by
  unfold executeBatchesState; split_ifs <;> rfl

theorem revertBatchesState_pv (c : ChainUpgradeState) (k : ℕ) :
    (revertBatchesState c k).pv = c.pv := by
  unfold revertBatchesState; split_ifs <;> rfl

/-! ## Preservation of the invariant -/

/-- A step that replaces the settlement-layer diamond `d` by another settlement-layer diamond with
a version no lower minor, and appends to the log only transactions above everything logged and at
most the new minor, preserves the invariant. -/
theorem inv_replace_sl {s : NonceSys} {d : ℕ} {c c' : ChainUpgradeState} (newLog : List L2Tx)
    (hI : NonceInv s) (hd : s.dia d = some ⟨c, true⟩) (hwf : VersionWf c'.pv)
    (hmono : minorOf c.pv ≤ minorOf c'.pv)
    (hnew : ∀ tx ∈ newLog, tx.nonce ≤ minorOf c'.pv ∧ ∀ a ∈ s.log, a.nonce < tx.nonce)
    (hnewSorted : newLog.Pairwise (fun a b => a.nonce < b.nonce)) :
    NonceInv { s with dia := upd s.dia d (some ⟨c', true⟩), log := s.log ++ newLog } := by
  have hpend : s.pending = none := by
    cases hp : s.pending with
    | none => rfl
    | some p => exact absurd hd (hI.pendingNoSL p hp d c)
  have hother : ∀ d' c'', d' ≠ d → s.dia d' ≠ some ⟨c'', true⟩ := by
    intro d' c'' hne h'
    exact hne (hI.slUnique d' d c'' c h' hd)
  constructor
  · intro d' x hx
    simp only [upd_dia_eq] at hx
    split_ifs at hx with he
    · cases hx; exact hwf
    · exact hI.wf d' x hx
  · intro p hp; simp [hpend] at hp
  · intro d' c'' hx tx htx
    simp only [upd_dia_eq] at hx
    split_ifs at hx with he
    · cases hx
      rcases List.mem_append.mp htx with h1 | h1
      · exact le_trans (hI.slBound d c hd tx h1) hmono
      · exact (hnew tx h1).1
    · exact absurd hx (hother d' c'' he)
  · intro p hp; simp [hpend] at hp
  · intro d1 d2 c1 c2 h1 h2
    simp only [upd_dia_eq] at h1 h2
    split_ifs at h1 h2 with he1 he2 he2
    · rw [he1, he2]
    · exact absurd h2 (hother d2 c2 he2)
    · exact absurd h1 (hother d1 c1 he1)
    · exact absurd h1 (hother d1 c1 he1)
  · intro p hp; simp [hpend] at hp
  · intro hall
    have := hall d
    simp at this
  · rw [List.pairwise_append]
    refine ⟨hI.sorted, hnewSorted, fun a ha b hb => (hnew b hb).2 a ha⟩

/-- A step that rewrites a diamond to one off its settlement layer, with a well-formed version,
preserves the invariant. -/
theorem inv_replace_off {s : NonceSys} {d : ℕ} {c' : ChainUpgradeState}
    (hI : NonceInv s) (hwf : VersionWf c'.pv) :
    NonceInv { s with dia := upd s.dia d (some ⟨c', false⟩) } := by
  constructor
  · intro d' y hy
    simp only [upd_dia_eq] at hy
    split_ifs at hy with he
    · cases hy; exact hwf
    · exact hI.wf d' y hy
  · exact hI.pendingWf
  · intro d' c'' hy tx htx
    simp only [upd_dia_eq] at hy
    split_ifs at hy with he
    · cases hy
    · exact hI.slBound d' c'' hy tx htx
  · exact hI.pendingBound
  · intro d1 d2 c1 c2 h1 h2
    simp only [upd_dia_eq] at h1 h2
    split_ifs at h1 h2 with he1 he2 he2
    · rw [he1, he2]
    · cases h1
    · cases h2
    · exact hI.slUnique d1 d2 c1 c2 h1 h2
  · intro p hp d' c'' hy
    simp only [upd_dia_eq] at hy
    split_ifs at hy with he
    · cases hy
    · exact hI.pendingNoSL p hp d' c'' hy
  · intro hall
    have := hall d
    simp at this
  · exact hI.sorted

/-- A migration's landing (a fresh or an existing destination, or the source on restore) puts one
diamond on its settlement layer with a version whose minor is at least the version the migration
left with, and clears the migration in flight. It preserves the invariant. -/
theorem inv_land {s : NonceSys} {d : ℕ} {p : NonceMigration} {c' : ChainUpgradeState}
    (hI : NonceInv s) (hp : s.pending = some p) (hwf : VersionWf c'.pv)
    (hmono : minorOf p.pv ≤ minorOf c'.pv) :
    NonceInv { s with dia := upd s.dia d (some ⟨c', true⟩), pending := none } := by
  have hnoSL := hI.pendingNoSL p hp
  constructor
  · intro d' y hy
    simp only [upd_dia_eq] at hy
    split_ifs at hy with he
    · cases hy; exact hwf
    · exact hI.wf d' y hy
  · intro q hq; cases hq
  · intro d' c'' hy tx htx
    simp only [upd_dia_eq] at hy
    split_ifs at hy with he
    · cases hy
      exact le_trans (hI.pendingBound p hp tx htx) hmono
    · exact absurd hy (hnoSL d' c'')
  · intro q hq; cases hq
  · intro d1 d2 c1 c2 h1 h2
    simp only [upd_dia_eq] at h1 h2
    split_ifs at h1 h2 with he1 he2 he2
    · rw [he1, he2]
    · exact absurd h2 (hnoSL d2 c2)
    · exact absurd h1 (hnoSL d1 c1)
    · exact absurd h1 (hnoSL d1 c1)
  · intro q hq; cases hq
  · intro hall
    have := hall d
    simp at this
  · exact hI.sorted

theorem NonceInitSatisfiesInvariant : Properties.NonceInitSatisfiesInvariant := by
  constructor
  · intro d x hx; cases hx
  · intro p hp; cases hp
  · intro d c hx; cases hx
  · intro p hp; cases hp
  · intro d d' c c' h; cases h
  · intro p hp; cases hp
  · intro _; rfl
  · exact List.Pairwise.nil

theorem NonceStepPreservesInvariant : Properties.NonceStepPreservesInvariant := by
  intro H s s' l hI hM hstep
  cases hstep with
  | @genesis d v0 mp tx hsh c' hnone hpend hg =>
    obtain ⟨hwf, hpv, htx⟩ := genesis_facts hg
    have hlog : s.log = [] := hI.emptyNoLog hnone
    constructor
    · intro d' y hy
      simp only [upd_dia_eq] at hy
      split_ifs at hy with he
      · cases hy; rw [hpv]; exact hwf
      · rw [hnone d'] at hy; cases hy
    · intro p hp; rw [hpend] at hp; cases hp
    · intro d' c'' hy t ht
      simp only [upd_dia_eq] at hy
      split_ifs at hy with he
      · cases hy
        rw [hpv]
        unfold logWrite at ht
        rw [hlog] at ht
        split_ifs at ht with h0
        · cases ht
        · rcases htx with h0' | ⟨_, hn⟩
          · exact absurd h0' h0
          · simp only [List.nil_append, List.mem_singleton] at ht
            rw [ht, hn]
      · rw [hnone d'] at hy; cases hy
    · intro p hp; rw [hpend] at hp; cases hp
    · intro d1 d2 c1 c2 h1 h2
      simp only [upd_dia_eq] at h1 h2
      split_ifs at h1 h2 with he1 he2 he2
      · rw [he1, he2]
      · rw [hnone d2] at h2; cases h2
      · rw [hnone d1] at h1; cases h1
      · rw [hnone d1] at h1; cases h1
    · intro p hp; rw [hpend] at hp; cases hp
    · intro hall
      have := hall d
      simp at this
    · unfold logWrite
      rw [hlog]
      split_ifs <;> simp
  | @cross d newV mp tx c c' hsh hd hU =>
    obtain ⟨hS, _, hcases⟩ := cross_facts hU
    have hmono := minor_mono hS.2.1 hS.2.2.1 (Nat.le_of_lt hS.1)
    rcases hcases with ⟨h0, rfl⟩ | ⟨h0, hne, hn, rfl⟩
    · have : logWrite s.log tx = s.log ++ [] := by simp [logWrite, h0]
      simp only [this]
      exact inv_replace_sl [] hI hd hS.2.2.1 hmono (by simp) List.Pairwise.nil
    · have : logWrite s.log tx = s.log ++ [tx] := by simp [logWrite, h0]
      simp only [this]
      have hlt : minorOf c.pv < minorOf newV := lt_of_le_of_ne hmono (Ne.symm hne)
      refine inv_replace_sl [tx] hI hd hS.2.2.1 hmono ?_ (List.pairwise_singleton _ _)
      intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      refine ⟨le_of_eq hn, fun a ha => ?_⟩
      rw [hn]
      exact lt_of_le_of_lt (hI.slBound d c hd a ha) hlt
  | @crossOff d newV c c' m p hd hV =>
    obtain ⟨hS, _, hr⟩ := (setNewProtocolVersion_some_iff c newV false (m, p, c')).mp hV
    have hc' : c' = { c with pv := newV } := by
      simp only [Prod.mk.injEq] at hr; exact hr.2.2
    subst hc'
    exact inv_replace_off hI hS.2.2.1
  | @commitBatch d n c hd hn =>
    have := inv_replace_sl (c' := commitBatchState c n) [] hI hd
      (by rw [commitBatchState_pv]; exact hI.wf d _ hd) (by rw [commitBatchState_pv]) (by simp)
      List.Pairwise.nil
    simpa using this
  | @executeBatches d e c hd =>
    have := inv_replace_sl (c' := executeBatchesState c e) [] hI hd
      (by rw [executeBatchesState_pv]; exact hI.wf d _ hd) (by rw [executeBatchesState_pv]) (by simp)
      List.Pairwise.nil
    simpa using this
  | @revertBatches d k c hd =>
    have := inv_replace_sl (c' := revertBatchesState c k) [] hI hd
      (by rw [revertBatchesState_pv]; exact hI.wf d _ hd) (by rw [revertBatchesState_pv]) (by simp)
      List.Pairwise.nil
    simpa using this
  | @burn d c hd hpend =>
    have hother : ∀ d' c'', d' ≠ d → s.dia d' ≠ some ⟨c'', true⟩ := by
      intro d' c'' hne h'
      exact hne (hI.slUnique d' d c'' c h' hd)
    constructor
    · intro d' y hy
      simp only [upd_dia_eq] at hy
      split_ifs at hy with he
      · cases hy; exact hI.wf d ⟨c, true⟩ hd
      · exact hI.wf d' y hy
    · intro p hp
      simp only [Option.some.injEq] at hp
      subst hp
      exact hI.wf d ⟨c, true⟩ hd
    · intro d' c'' hy
      simp only [upd_dia_eq] at hy
      split_ifs at hy with he
      · cases hy
      · exact absurd hy (hother d' c'' he)
    · intro p hp
      simp only [Option.some.injEq] at hp
      subst hp
      exact hI.slBound d c hd
    · intro d1 d2 c1 c2 h1 h2
      simp only [upd_dia_eq] at h1 h2
      split_ifs at h1 h2 with he1 he2 he2
      · rw [he1, he2]
      · cases h1
      · exact absurd h1 (hother d1 c1 he1)
      · exact absurd h1 (hother d1 c1 he1)
    · intro p _ d' c'' hy
      simp only [upd_dia_eq] at hy
      split_ifs at hy with he
      · cases hy
      · exact hother d' c'' he hy
    · intro hall
      have := hall d
      simp at this
    · exact hI.sorted
  | @mintFresh d p hp hnone =>
    exact inv_land hI hp (hI.pendingWf p hp) le_rfl
  | @mintExisting d p c hp hne hd =>
    have hle : p.pv ≤ c.pv := hM p c hp hd
    exact inv_land hI hp (hI.wf d _ hd) (minor_mono (hI.pendingWf p hp) (hI.wf d _ hd) hle)
  | @restore p c hp hd hpv =>
    exact inv_land hI hp (hI.wf p.src _ hd) (by rw [hpv])

theorem logWrite_eq (log : List L2Tx) (tx : L2Tx) :
    logWrite log tx = log ++ (if tx.txType = 0 then [] else [tx]) := by
  unfold logWrite; split_ifs <;> simp

/-- Every step only appends to the log. -/
theorem step_log_grows {H : L2Tx → ℕ} {s s' : NonceSys} {l : NonceLabel}
    (hs : NonceStep H s l s') : ∃ new, s'.log = s.log ++ new := by
  cases hs with
  | genesis _ _ _ => exact ⟨_, logWrite_eq _ _⟩
  | cross _ _ => exact ⟨_, logWrite_eq _ _⟩
  | crossOff _ _ => exact ⟨[], by simp⟩
  | commitBatch _ _ => exact ⟨[], by simp⟩
  | executeBatches _ => exact ⟨[], by simp⟩
  | revertBatches _ => exact ⟨[], by simp⟩
  | burn _ _ => exact ⟨[], by simp⟩
  | mintFresh _ _ => exact ⟨[], by simp⟩
  | mintExisting _ _ _ => exact ⟨[], by simp⟩
  | restore _ _ _ => exact ⟨[], by simp⟩

/-- Along a run satisfying `MintLandsNotBehind`, the invariant holds throughout and the log only
grows by appending. -/
theorem run_inv {H : L2Tx → ℕ} {s s' : NonceSys} {ls : List NonceLabel} (hI : NonceInv s)
    (h : NonceRunWith H MintLandsNotBehind s ls s') :
    NonceInv s' ∧ ∃ new, s'.log = s.log ++ new := by
  induction h with
  | nil => exact ⟨hI, [], by simp⟩
  | @cons s s1 s2 l ls hP hs _ ih =>
    obtain ⟨hI2, new, hnew⟩ := ih (NonceStepPreservesInvariant H s s1 l hI hP hs)
    refine ⟨hI2, ?_⟩
    obtain ⟨new1, hnew1⟩ := step_log_grows hs
    exact ⟨new1 ++ new, by rw [hnew, hnew1, List.append_assoc]⟩

/-! ## Per step -/

theorem CrossingKeepsANonzeroPendingHash : Properties.CrossingKeepsANonzeroPendingHash := by
  intro H s s' d newV mp tx c hstep hd hh
  cases hstep with
  | @cross _ _ _ _ c0 c' hsh hd' hU =>
    rw [hd] at hd'
    simp only [Option.some.injEq, NonceDiamond.mk.injEq, and_true] at hd'
    subst hd'
    obtain ⟨_, hclean, hcases⟩ := cross_facts hU
    rcases hcases with ⟨h0, rfl⟩ | ⟨_, hne, _, _⟩
    · exact ⟨h0, by simp [logWrite, h0], { c with pv := newV }, by simp, rfl, rfl, rfl⟩
    · exact absurd (hclean hne).1 hh

theorem PatchCrossingKeepsThePendingUpgrade : Properties.PatchCrossingKeepsThePendingUpgrade := by
  intro H s s' d newV mp tx c hstep hd hpatch
  cases hstep with
  | @cross _ _ _ _ c0 c' hsh hd' hU =>
    rw [hd] at hd'
    simp only [Option.some.injEq, NonceDiamond.mk.injEq, and_true] at hd'
    subst hd'
    obtain ⟨_, _, hcases⟩ := cross_facts hU
    rcases hcases with ⟨h0, rfl⟩ | ⟨_, hne, _, _⟩
    · exact ⟨h0, by simp [logWrite, h0], { c with pv := newV }, by simp, rfl, rfl, rfl⟩
    · exact absurd hpatch hne

theorem WritingCrossingRaisesTheMinor : Properties.WritingCrossingRaisesTheMinor := by
  intro H s s' d newV mp tx c hstep hd h0
  cases hstep with
  | @cross _ _ _ _ c0 c' hsh hd' hU =>
    rw [hd] at hd'
    simp only [Option.some.injEq, NonceDiamond.mk.injEq, and_true] at hd'
    subst hd'
    obtain ⟨hS, hclean, hcases⟩ := cross_facts hU
    rcases hcases with ⟨h0', _⟩ | ⟨_, hne, hn, rfl⟩
    · exact absurd h0' h0
    · have hmono := minor_mono hS.2.1 hS.2.2.1 (Nat.le_of_lt hS.1)
      obtain ⟨hh, hb⟩ := hclean hne
      refine ⟨hh, hb, lt_of_le_of_ne hmono (Ne.symm hne), hn, by simp [logWrite, h0], ?_⟩
      simp [hb]

/-! ## Along runs -/

theorem UpgradeTxNoncesStrictlyIncrease : Properties.UpgradeTxNoncesStrictlyIncrease := by
  intro H s s' ls hI hrun
  obtain ⟨hI', hgrow⟩ := run_inv hI hrun
  exact ⟨hgrow, hI'.sorted⟩

theorem LoggedUpgradeTxHashesDistinctOrCollide :
    Properties.LoggedUpgradeTxHashesDistinctOrCollide := by
  intro H s s' ls hI hrun i j hi hj
  have hsorted := (run_inv hI hrun).1.sorted
  have hlt : (s'.log[i]'(Nat.lt_trans hi hj)).nonce < (s'.log[j]'hj).nonce :=
    List.pairwise_iff_getElem.mp hsorted i j (Nat.lt_trans hi hj) hj hi
  refine ⟨hlt, fun hH => ⟨fun heq => ?_, hH⟩⟩
  rw [heq] at hlt
  exact lt_irrefl _ hlt

/-! ## Increasing nonces do not rule out a skipped transaction -/

/-- One step keeps a live version, unless it is a genesis or a crossing on the settlement layer,
when migrations onto existing diamonds land exactly. -/
theorem step_keeps_active {H : L2Tx → ℕ} {s s' : NonceSys} {l : NonceLabel}
    (hM : MintLandsExactly s l) (hK : l.KeepsVersionLabel) (hs : NonceStep H s l s') (v : ℕ)
    (ha : ActiveVersion s v) : ActiveVersion s' v := by
  cases hs with
  | genesis _ _ _ => exact hK.elim
  | cross _ _ => exact hK.elim
  | @crossOff d newV c c' m p hd hV =>
    rcases ha with ⟨d1, c1, h1, hv⟩ | ⟨p1, hp1, hv⟩
    · have hne : d1 ≠ d := by rintro rfl; rw [hd] at h1; cases h1
      exact Or.inl ⟨d1, c1, by simp only [upd_dia_eq, hne, ↓reduceIte]; exact h1, hv⟩
    · exact Or.inr ⟨p1, hp1, hv⟩
  | @commitBatch d n c hd hn =>
    rcases ha with ⟨d1, c1, h1, hv⟩ | ⟨p1, hp1, hv⟩
    · by_cases hde : d1 = d
      · subst hde
        rw [hd] at h1
        simp only [Option.some.injEq, NonceDiamond.mk.injEq, and_true] at h1
        subst h1
        exact Or.inl ⟨d1, commitBatchState c n, by simp, by rw [commitBatchState_pv]; exact hv⟩
      · exact Or.inl ⟨d1, c1, by simp only [upd_dia_eq, hde, ↓reduceIte]; exact h1, hv⟩
    · exact Or.inr ⟨p1, hp1, hv⟩
  | @executeBatches d e c hd =>
    rcases ha with ⟨d1, c1, h1, hv⟩ | ⟨p1, hp1, hv⟩
    · by_cases hde : d1 = d
      · subst hde
        rw [hd] at h1
        simp only [Option.some.injEq, NonceDiamond.mk.injEq, and_true] at h1
        subst h1
        exact Or.inl ⟨d1, executeBatchesState c e, by simp,
          by rw [executeBatchesState_pv]; exact hv⟩
      · exact Or.inl ⟨d1, c1, by simp only [upd_dia_eq, hde, ↓reduceIte]; exact h1, hv⟩
    · exact Or.inr ⟨p1, hp1, hv⟩
  | @revertBatches d k c hd =>
    rcases ha with ⟨d1, c1, h1, hv⟩ | ⟨p1, hp1, hv⟩
    · by_cases hde : d1 = d
      · subst hde
        rw [hd] at h1
        simp only [Option.some.injEq, NonceDiamond.mk.injEq, and_true] at h1
        subst h1
        exact Or.inl ⟨d1, revertBatchesState c k, by simp,
          by rw [revertBatchesState_pv]; exact hv⟩
      · exact Or.inl ⟨d1, c1, by simp only [upd_dia_eq, hde, ↓reduceIte]; exact h1, hv⟩
    · exact Or.inr ⟨p1, hp1, hv⟩
  | @burn d c hd hpend =>
    rcases ha with ⟨d1, c1, h1, hv⟩ | ⟨p1, hp1, hv⟩
    · by_cases hde : d1 = d
      · subst hde
        rw [hd] at h1
        simp only [Option.some.injEq, NonceDiamond.mk.injEq, and_true] at h1
        subst h1
        exact Or.inr ⟨⟨d1, c.h, c.b, c.pv⟩, rfl, hv⟩
      · exact Or.inl ⟨d1, c1, by simp only [upd_dia_eq, hde, ↓reduceIte]; exact h1, hv⟩
    · rw [hpend] at hp1; cases hp1
  | @mintFresh d p hp hnone =>
    rcases ha with ⟨d1, c1, h1, hv⟩ | ⟨p1, hp1, hv⟩
    · have hne : d1 ≠ d := by rintro rfl; rw [hnone] at h1; cases h1
      exact Or.inl ⟨d1, c1, by simp only [upd_dia_eq, hne, ↓reduceIte]; exact h1, hv⟩
    · rw [hp] at hp1
      simp only [Option.some.injEq] at hp1
      subst hp1
      exact Or.inl ⟨d, ⟨p.pv, p.h, p.b⟩, by simp, hv⟩
  | @mintExisting d p c hp hne hd =>
    have hex : p.pv = c.pv := hM p c hp hd
    rcases ha with ⟨d1, c1, h1, hv⟩ | ⟨p1, hp1, hv⟩
    · have hne' : d1 ≠ d := by rintro rfl; rw [hd] at h1; cases h1
      exact Or.inl ⟨d1, c1, by simp only [upd_dia_eq, hne', ↓reduceIte]; exact h1, hv⟩
    · rw [hp] at hp1
      simp only [Option.some.injEq] at hp1
      subst hp1
      exact Or.inl ⟨d, { c with h := p.h, b := p.b }, by simp, by rw [← hex]; exact hv⟩
  | @restore p c hp hd hpv =>
    rcases ha with ⟨d1, c1, h1, hv⟩ | ⟨p1, hp1, hv⟩
    · have hne' : d1 ≠ p.src := by rintro rfl; rw [hd] at h1; cases h1
      exact Or.inl ⟨d1, c1, by simp only [upd_dia_eq, hne', ↓reduceIte]; exact h1, hv⟩
    · rw [hp] at hp1
      simp only [Option.some.injEq] at hp1
      subst hp1
      exact Or.inl ⟨p.src, c, by simp, by rw [hpv]; exact hv⟩

theorem ExactLandingRunsKeepTheActiveVersion :
    Properties.ExactLandingRunsKeepTheActiveVersion := by
  intro H s s' ls hrun hK v ha
  induction hrun with
  | nil => exact ha
  | @cons s s1 s2 l ls hP hs _ ih =>
    exact ih (fun l' hl' => hK l' (List.mem_cons_of_mem _ hl'))
      (step_keeps_active hP (hK l List.mem_cons_self) hs v ha)

/-! ## What it needs, and the witness -/

/-- The first nine steps of `wLaggingRun`, up to the migration back. -/
private def wLaggingPrefix : List NonceLabel :=
  [.genesis 0 v29 99000 (wUpgradeTx 29 [9]),
   .commitBatch 0 1, .executeBatches 0 1,
   .burn 0, .mint 1,
   .cross 1 v30 99000 (wUpgradeTx 30 [1]),
   .commitBatch 1 2, .executeBatches 1 2,
   .burn 1]

theorem LaggingReturnRepeatsNonce : Properties.LaggingReturnRepeatsNonce := by
  refine ⟨_,
    NonceRunWith.cons trivial (NonceStep.genesis (hsh := 30) (c' := ⟨v29, 30, 0⟩)
        (fun _ => rfl) rfl (by decide))
    (NonceRunWith.cons trivial (NonceStep.commitBatch (c := ⟨v29, 30, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.executeBatches (c := ⟨v29, 30, 1⟩) (by decide))
    (NonceRunWith.cons trivial (NonceStep.burn (c := ⟨v29, 0, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.mintFresh (p := ⟨0, 0, 0, v29⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.cross (c := ⟨v29, 0, 0⟩) (c' := ⟨v30, 31, 0⟩) (hsh := 31)
        (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.commitBatch (c := ⟨v30, 31, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.executeBatches (c := ⟨v30, 31, 2⟩) (by decide))
    (NonceRunWith.cons trivial (NonceStep.burn (c := ⟨v30, 0, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.mintExisting (p := ⟨1, 0, 0, v30⟩) (c := ⟨v29, 0, 0⟩)
        (by decide) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.cross (c := ⟨v29, 0, 0⟩) (c' := ⟨v30, 31, 0⟩) (hsh := 31)
        (by decide) (by decide))
      NonceRunWith.nil)))))))))),
    by decide, by decide, _, _, wLaggingPrefix, [.cross 0 v30 99000 (wUpgradeTx 30 [1])], rfl,
    NonceRunWith.cons trivial (NonceStep.genesis (hsh := 30) (c' := ⟨v29, 30, 0⟩)
        (fun _ => rfl) rfl (by decide))
    (NonceRunWith.cons trivial (NonceStep.commitBatch (c := ⟨v29, 30, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.executeBatches (c := ⟨v29, 30, 1⟩) (by decide))
    (NonceRunWith.cons trivial (NonceStep.burn (c := ⟨v29, 0, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.mintFresh (p := ⟨0, 0, 0, v29⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.cross (c := ⟨v29, 0, 0⟩) (c' := ⟨v30, 31, 0⟩) (hsh := 31)
        (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.commitBatch (c := ⟨v30, 31, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.executeBatches (c := ⟨v30, 31, 2⟩) (by decide))
    (NonceRunWith.cons trivial (NonceStep.burn (c := ⟨v30, 0, 0⟩) (by decide) (by decide))
      NonceRunWith.nil)))))))),
    ?_, NonceStep.mintExisting (p := ⟨1, 0, 0, v30⟩) (c := ⟨v29, 0, 0⟩)
        (by decide) (by decide) (by decide)⟩
  intro h
  have := h ⟨1, 0, 0, v30⟩ ⟨v29, 0, 0⟩ (by decide) (by decide)
  exact absurd this (by decide)

theorem UpgradeTxNoncesWitness : Properties.UpgradeTxNoncesWitness := by
  refine ⟨_,
    NonceRunWith.cons trivial (NonceStep.genesis (hsh := 30) (c' := ⟨v29, 30, 0⟩)
        (fun _ => rfl) rfl (by decide))
    (NonceRunWith.cons trivial (NonceStep.commitBatch (c := ⟨v29, 30, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.executeBatches (c := ⟨v29, 30, 1⟩) (by decide))
    (NonceRunWith.cons trivial (NonceStep.burn (c := ⟨v29, 0, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons (fun _ _ _ h => by cases h)
        (NonceStep.mintFresh (p := ⟨0, 0, 0, v29⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.cross (c := ⟨v29, 0, 0⟩) (c' := ⟨v30, 31, 0⟩) (hsh := 31)
        (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.crossOff (c := ⟨v29, 0, 0⟩) (c' := ⟨v30, 0, 0⟩) (m := 30)
        (p := false) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.crossOff (c := ⟨v30, 0, 0⟩) (c' := ⟨v30p1, 0, 0⟩) (m := 30)
        (p := true) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.cross (c := ⟨v30, 31, 0⟩) (c' := ⟨v30p1, 31, 0⟩) (hsh := 0)
        (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.commitBatch (c := ⟨v30p1, 31, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.revertBatches (c := ⟨v30p1, 31, 5⟩) (by decide))
    (NonceRunWith.cons trivial (NonceStep.commitBatch (c := ⟨v30p1, 31, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.executeBatches (c := ⟨v30p1, 31, 6⟩) (by decide))
    (NonceRunWith.cons trivial (NonceStep.burn (c := ⟨v30p1, 0, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons (fun p c hp hd => by cases hp; cases hd; decide)
        (NonceStep.mintExisting (p := ⟨1, 0, 0, v30p1⟩) (c := ⟨v30p1, 0, 0⟩)
        (by decide) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.cross (c := ⟨v30p1, 0, 0⟩) (c' := ⟨v31, 32, 0⟩) (hsh := 32)
        (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.commitBatch (c := ⟨v31, 32, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.executeBatches (c := ⟨v31, 32, 7⟩) (by decide))
    (NonceRunWith.cons trivial (NonceStep.burn (c := ⟨v31, 0, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.restore (p := ⟨0, 0, 0, v31⟩) (c := ⟨v31, 0, 0⟩)
        (by decide) (by decide) (by decide))
      NonceRunWith.nil))))))))))))))))))),
    by decide, by decide⟩

theorem ReturnAheadSkipsAnL2Upgrade : Properties.ReturnAheadSkipsAnL2Upgrade := by
  refine ⟨by unfold Constructed; decide, by decide, rfl, rfl, _,
    NonceRunWith.cons trivial (NonceStep.genesis (hsh := 30) (c' := ⟨v29, 30, 0⟩)
        (fun _ => rfl) rfl (by decide))
    (NonceRunWith.cons trivial (NonceStep.commitBatch (c := ⟨v29, 30, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.executeBatches (c := ⟨v29, 30, 1⟩) (by decide))
    (NonceRunWith.cons trivial (NonceStep.burn (c := ⟨v29, 0, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons (fun _ _ _ h => by cases h)
        (NonceStep.mintFresh (p := ⟨0, 0, 0, v29⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.crossOff (c := ⟨v29, 0, 0⟩) (c' := ⟨v30, 0, 0⟩) (m := 30)
        (p := false) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.burn (c := ⟨v29, 0, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons (fun p c hp hd => by cases hp; cases hd; decide)
        (NonceStep.mintExisting (p := ⟨1, 0, 0, v29⟩) (c := ⟨v30, 0, 0⟩)
        (by decide) (by decide) (by decide))
      NonceRunWith.nil))))))),
    ?_, by decide, Or.inl ⟨0, ⟨v30, 0, 0⟩, by decide, rfl⟩, by decide, by decide⟩
  intro l hl
  simp only [wSkipRun, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  all_goals exact Or.inr trivial

theorem ExactLandingWitness : Properties.ExactLandingWitness := by
  refine ⟨_, _,
    NonceRunWith.cons trivial (NonceStep.genesis (hsh := 30) (c' := ⟨v29, 30, 0⟩)
        (fun _ => rfl) rfl (by decide)) NonceRunWith.nil,
    NonceRunWith.cons trivial (NonceStep.commitBatch (c := ⟨v29, 30, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.revertBatches (c := ⟨v29, 30, 1⟩) (by decide))
    (NonceRunWith.cons trivial (NonceStep.commitBatch (c := ⟨v29, 30, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.executeBatches (c := ⟨v29, 30, 2⟩) (by decide))
    (NonceRunWith.cons trivial (NonceStep.burn (c := ⟨v29, 0, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons (fun _ _ _ h => by cases h)
        (NonceStep.mintFresh (p := ⟨0, 0, 0, v29⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.burn (c := ⟨v29, 0, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons (fun p c hp hd => by cases hp; cases hd; rfl)
        (NonceStep.mintExisting (p := ⟨1, 0, 0, v29⟩) (c := ⟨v29, 0, 0⟩)
        (by decide) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.burn (c := ⟨v29, 0, 0⟩) (by decide) (by decide))
    (NonceRunWith.cons trivial (NonceStep.restore (p := ⟨0, 0, 0, v29⟩) (c := ⟨v29, 0, 0⟩)
        (by decide) (by decide) (by decide))
      NonceRunWith.nil))))))))),
    ?_, Or.inl ⟨0, ⟨v29, 30, 0⟩, by decide, rfl⟩, Or.inl ⟨0, ⟨v29, 0, 0⟩, by decide, rfl⟩,
    by decide⟩
  intro l hl
  simp only [wExactRun, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

end Contracts.ChainTypeManager.EdgeChecks
