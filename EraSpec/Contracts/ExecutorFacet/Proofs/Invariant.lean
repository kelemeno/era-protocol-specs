import EraSpec.Contracts.ExecutorFacet.Specs.Pipeline

/-!
# Auxiliary: the pipeline's reachable-state invariant

`Inv env s` is the conjunction proved for every reachable state. It has an unconditional
part and a part `CleanInv` that holds while no hash break is logged. The named guarantees
in `Proofs/Pipeline.lean` are read off it. No property is stated here.
-/

namespace Contracts.ExecutorFacet

/-- The invariant that holds while the run has logged no hash break. -/
structure CleanInv (env : Env) (s : State) : Prop where
  hashes : ∀ n ≤ s.totalBatchesCommitted, s.storedBatchHashes n = env.hashStored (s.preimage n)
  numbers : ∀ n ≤ s.totalBatchesCommitted, (s.preimage n).batchNumber = n
  chain : ∀ n, 1 ≤ n → n ≤ s.totalBatchesCommitted → ∃ a, s.commitArgs n = some a ∧
    a.prevBatchHash = (s.preimage (n - 1)).batchHash ∧ s.preimage n = storedInfoOf env a
  fees : ∀ n, 1 ≤ n → n ≤ s.totalBatchesCommitted → ∀ a, s.commitArgs n = some a →
    s.interopFeeUnits n = a.input.interopFeeUnits
  execInfo : ∀ r ∈ s.executed, r.info = s.preimage r.info.batchNumber
  proved : ∀ n, s.totalBatchesExecuted < n → n ≤ s.totalBatchesVerified →
    ProvedAt s n (s.preimage n)
  execProved : ∀ r ∈ s.executed, ProvedAt s r.info.batchNumber r.info
  upPending : s.l2SystemContractsUpgradeBatchNumber ≠ 0 →
    s.l2SystemContractsUpgradeTxHash ≠ 0 ∧
    s.l2SystemContractsUpgradeBatchNumber = s.totalBatchesExecuted + 1 ∧
    s.l2SystemContractsUpgradeBatchNumber ≤ s.totalBatchesCommitted ∧
    ∃ a, s.commitArgs s.l2SystemContractsUpgradeBatchNumber = some a ∧
      a.upgradeTxHash = s.l2SystemContractsUpgradeTxHash
  upWaiting : s.l2SystemContractsUpgradeTxHash ≠ 0 → s.l2SystemContractsUpgradeBatchNumber = 0 →
    s.totalBatchesCommitted = s.totalBatchesExecuted
  upOthers : ∀ n, s.totalBatchesExecuted < n → n ≤ s.totalBatchesCommitted →
    n ≠ s.l2SystemContractsUpgradeBatchNumber → ∀ a, s.commitArgs n = some a →
    a.upgradeTxHash = 0

/-- The invariant of every reachable state. -/
structure Inv (env : Env) (s : State) : Prop where
  ev : s.totalBatchesExecuted ≤ s.totalBatchesVerified
  vc : s.totalBatchesVerified ≤ s.totalBatchesCommitted
  execNums : s.executed.map (·.info.batchNumber) = List.range' 1 s.totalBatchesExecuted
  execPrio : ∀ r ∈ s.executed, r.items.length = r.info.numberOfLayer1Txs ∧
    env.rollingHash r.items = r.info.priorityOperationsHash
  logRoots : ∀ r ∈ s.executed, s.l2LogsRootHashes r.info.batchNumber = r.info.l2LogsTreeRoot
  unproc : s.ptUnprocessedIndex = (consumed s).length
  roots : ∀ r, s.ptHistoricalRoots r = true →
    ∃ k ≤ s.ptLeaves.length, r = env.treeRoot (s.ptLeaves.take k)
  merkleGenuine : ∀ br ∈ s.merkleBreaks, br.Genuine env
  prefixOk : s.merkleBreaks = [] →
    consumed s = s.ptLeaves.take s.ptUnprocessedIndex ∧ s.ptUnprocessedIndex ≤ s.ptLeaves.length
  verifiedOk : ∀ call ∈ s.verified,
    env.verify (call.batches.map (·.commitment)) call.proof = true
  firstBreak : ∀ br, s.hashBreaks.head? = some br → br.Genuine env
  clean : s.hashBreaks = [] → CleanInv env s

/-! ## Small lemmas -/

theorem mem_logHash {s : State} {n : Nat} {b : StoredBatchInfo} {br : HashBreak}
    (h : br ∈ logHash s n b) : br = ⟨n, b, s.preimage n⟩ ∧ b ≠ s.preimage n := by
  unfold logHash at h
  split at h
  · simp at h
  · simp at h; exact ⟨h, by assumption⟩

theorem logHash_eq_nil {s : State} {n : Nat} {b : StoredBatchInfo} :
    logHash s n b = [] ↔ b = s.preimage n := by
  unfold logHash; split <;> simp_all

theorem firstBreak_append {env : Env} {l X : List HashBreak}
    (h1 : ∀ br, l.head? = some br → br.Genuine env)
    (h2 : l = [] → ∀ br ∈ X, br.Genuine env) :
    ∀ br, (l ++ X).head? = some br → br.Genuine env := by
  intro br hbr
  cases l with
  | nil =>
    simp only [List.nil_append] at hbr
    exact h2 rfl br (List.mem_of_head? hbr)
  | cons a l => exact h1 br (by simpa using hbr)

theorem logHash_genuine {env : Env} {s : State} {n : Nat} {b : StoredBatchInfo}
    (hs : s.storedBatchHashes n = env.hashStored b)
    (hp : s.storedBatchHashes n = env.hashStored (s.preimage n)) :
    ∀ br ∈ logHash s n b, br.Genuine env := by
  intro br hbr
  obtain ⟨rfl, hne⟩ := mem_logHash hbr
  exact ⟨hne, hs.symm.trans hp⟩

theorem mem_executed_bounds {s : State}
    (h : s.executed.map (·.info.batchNumber) = List.range' 1 s.totalBatchesExecuted)
    {r : ExecRecord} (hr : r ∈ s.executed) :
    1 ≤ r.info.batchNumber ∧ r.info.batchNumber ≤ s.totalBatchesExecuted := by
  have : r.info.batchNumber ∈ List.range' 1 s.totalBatchesExecuted := by
    rw [← h]; exact List.mem_map_of_mem hr
  rw [List.mem_range'_1] at this
  omega

theorem take_append_segment {L X : List Word} {u : Nat} (h : SegmentOk L u X) :
    L.take u ++ X = L.take (u + X.length) := by
  rw [List.take_add, h.2]

theorem segment_append {L X Y : List Word} {u : Nat} (hX : SegmentOk L u X)
    (hY : SegmentOk L (u + X.length) Y) : SegmentOk L u (X ++ Y) := by
  refine ⟨by simp; have := hY.1; omega, ?_⟩
  rw [List.length_append, List.take_add, hX.2, List.drop_drop]
  rw [hY.2]

theorem segment_nil (L : List Word) (u : Nat) (h : u ≤ L.length) : SegmentOk L u [] := by
  simp [SegmentOk, h]

/-! ## Initial states -/

theorem inv_init {env : Env} {s : State} (h : Init env s) : Inv env s := by
  refine
    { ev := by rw [h.executed0, h.verified0]
      vc := by rw [h.verified0, h.committed0]
      execNums := by rw [h.executedLog0, h.executed0]; rfl
      execPrio := by simp [h.executedLog0]
      logRoots := by simp [h.executedLog0]
      unproc := by simp [consumed, h.executedLog0, h.unprocessed0]
      roots := ?_
      merkleGenuine := by simp [h.merkleBreaks0]
      prefixOk := by intro; simp [consumed, h.executedLog0, h.unprocessed0, h.leaves0]
      verifiedOk := by simp [h.verifiedLog0]
      firstBreak := by simp [h.hashBreaks0]
      clean := fun _ => ?_ }
  · intro r hr
    exact ⟨0, Nat.zero_le _, by rw [h.roots0 r hr, h.leaves0]; rfl⟩
  · refine
      { hashes := ?_, numbers := ?_, chain := ?_
        fees := fun n h1 hn => by rw [h.committed0] at hn; omega
        execInfo := by simp [h.executedLog0]
        proved := ?_, execProved := by simp [h.executedLog0]
        upPending := by simp [h.noUpgradeBatch]
        upWaiting := by simp [h.noUpgradeTx]
        upOthers := ?_ }
    · intro n hn; rw [h.committed0] at hn; obtain rfl : n = 0 := by omega
      exact h.genesisHash
    · intro n hn; rw [h.committed0] at hn; obtain rfl : n = 0 := by omega
      exact h.genesisNumber
    · intro n h1 hn; rw [h.committed0] at hn; omega
    · intro n h1 h2; rw [h.executed0] at h1; rw [h.verified0] at h2; omega
    · intro n h1 h2; rw [h.committed0] at h2; omega

/-! ## Revert -/

theorem revertBatches_some {s s' : State} {n : Nat} (h : revertBatches s n = some s') :
    s.totalBatchesExecuted ≤ n ∧ n ≤ s.totalBatchesCommitted ∧
    s' = { s with
      totalBatchesVerified := if n < s.totalBatchesVerified then n else s.totalBatchesVerified
      totalBatchesCommitted := n
      l2SystemContractsUpgradeBatchNumber :=
        if s.l2SystemContractsUpgradeBatchNumber > n then 0
        else s.l2SystemContractsUpgradeBatchNumber } := by
  unfold revertBatches revertBatchesWith at h
  by_cases h1 : s.totalBatchesCommitted < n
  · simp [h1] at h
  by_cases h2 : n < s.totalBatchesExecuted
  · simp [h1, h2] at h
  simp only [h1, h2, and_false, ↓reduceIte, Option.some.injEq] at h
  exact ⟨by omega, by omega, h.symm⟩

theorem inv_revertBatches {env : Env} {s s' : State} {n : Nat} (hi : Inv env s)
    (h : revertBatches s n = some s') : Inv env s' := by
  obtain ⟨h1, h2, rfl⟩ := revertBatches_some h
  have hev := hi.ev
  have hvc := hi.vc
  refine
    { ev := by dsimp only; split <;> omega
      vc := by dsimp only; split <;> omega
      execNums := hi.execNums, execPrio := hi.execPrio, logRoots := hi.logRoots
      unproc := hi.unproc
      roots := hi.roots, merkleGenuine := hi.merkleGenuine, prefixOk := hi.prefixOk
      verifiedOk := hi.verifiedOk, firstBreak := hi.firstBreak
      clean := fun hc => ?_ }
  have c := hi.clean hc
  have hev := hi.ev
  have hvc := hi.vc
  refine
    { hashes := fun m hm => c.hashes m (by dsimp only at hm; omega)
      numbers := fun m hm => c.numbers m (by dsimp only at hm; omega)
      chain := fun m h1 hm => c.chain m h1 (by dsimp only at hm; omega)
      fees := fun m h1 hm => c.fees m h1 (by dsimp only at hm; omega)
      execInfo := c.execInfo
      proved := fun m hm1 hm2 => c.proved m hm1 (by dsimp only at hm2; split at hm2 <;> omega)
      execProved := c.execProved
      upPending := ?_, upWaiting := ?_, upOthers := ?_ }
  · dsimp only
    split
    · intro h; exact absurd rfl h
    · intro hne
      obtain ⟨a1, a2, a3, a4⟩ := c.upPending hne
      exact ⟨a1, a2, by omega, a4⟩
  · dsimp only
    intro htx hub
    split at hub
    · rename_i hgt
      have := (c.upPending (by omega)).2.1
      omega
    · have := c.upWaiting htx hub; omega
  · dsimp only
    intro m hm1 hm2 hne a ha
    split at hne
    · rename_i hgt
      exact c.upOthers m hm1 (by omega) (by omega) a ha
    · exact c.upOthers m hm1 (by omega) hne a ha

/-! ## Push, priority mode, upgrade transaction -/

theorem cleanInv_setPriorityMode {env : Env} {s : State} (b : Bool) (c : CleanInv env s) :
    CleanInv env { s with priorityModeActivated := b } :=
  ⟨c.1, c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10⟩

theorem inv_setPriorityMode {env : Env} {s : State} (b : Bool) (hi : Inv env s) :
    Inv env { s with priorityModeActivated := b } :=
  ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6, hi.7, hi.8, hi.9, hi.10, hi.11,
    fun hc => cleanInv_setPriorityMode b (hi.12 hc)⟩

theorem inv_push {env : Env} {s : State} (hv : Word) (hi : Inv env s) :
    Inv env { s with
      ptLeaves := s.ptLeaves ++ [hv]
      ptHistoricalRoots :=
        Function.update s.ptHistoricalRoots (env.treeRoot (s.ptLeaves ++ [hv])) true } := by
  refine
    { ev := hi.ev, vc := hi.vc, execNums := hi.execNums, execPrio := hi.execPrio
      logRoots := hi.logRoots
      unproc := hi.unproc, roots := ?_, merkleGenuine := hi.merkleGenuine, prefixOk := ?_
      verifiedOk := hi.verifiedOk, firstBreak := hi.firstBreak
      clean := fun hc =>
        let c := hi.clean hc; ⟨c.1, c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10⟩ }
  · intro r hr
    dsimp only at hr ⊢
    by_cases heq : r = env.treeRoot (s.ptLeaves ++ [hv])
    · exact ⟨s.ptLeaves.length + 1, by simp, by rw [heq, List.take_of_length_le (by simp)]⟩
    · rw [Function.update_of_ne heq] at hr
      obtain ⟨k, hk, rfl⟩ := hi.roots r hr
      exact ⟨k, by simp; omega, by rw [List.take_append_of_le_length hk]⟩
  · intro hm
    obtain ⟨h1, h2⟩ := hi.prefixOk hm
    dsimp only
    refine ⟨?_, by simp; omega⟩
    rw [List.take_append_of_le_length h2]
    exact h1

theorem inv_setUpgradeTx {env : Env} {s s' : State} {hv : Word} (hi : Inv env s)
    (h : setUpgradeTx s hv = some s') : Inv env s' := by
  unfold setUpgradeTx at h
  split_ifs at h with h1 h2 h3 h4 h5
  injection h with h; subst h
  refine
    { ev := hi.ev, vc := hi.vc, execNums := hi.execNums, execPrio := hi.execPrio
      logRoots := hi.logRoots
      unproc := hi.unproc, roots := hi.roots, merkleGenuine := hi.merkleGenuine
      prefixOk := hi.prefixOk, verifiedOk := hi.verifiedOk, firstBreak := hi.firstBreak
      clean := fun hc => ?_ }
  have c := hi.clean hc
  simp only [not_not] at h3 h5
  refine
    { hashes := c.hashes, numbers := c.numbers, chain := c.chain, fees := c.fees
      execInfo := c.execInfo
      proved := c.proved, execProved := c.execProved
      upPending := fun hne => absurd h5 hne
      upWaiting := fun _ _ => h3
      upOthers := fun m hm1 hm2 _ _ _ => by dsimp only at hm1 hm2; omega }

/-! ## ProvedAt -/

theorem provedAt_mono {s s' : State} (h : ∀ call ∈ s.verified, call ∈ s'.verified)
    {n : Nat} {b : StoredBatchInfo} (hp : ProvedAt s n b) : ProvedAt s' n b := by
  obtain ⟨call, hc, j, hj, hb⟩ := hp
  exact ⟨call, h call hc, j, hj, hb⟩

/-! ## Commit -/

/-- The state `commit` writes on success. -/
def commitState (env : Env) (s : State) (last : StoredBatchInfo) (b : CommitBatchInfo) :
    State :=
  let processUpgrade : Bool :=
    decide (s.l2SystemContractsUpgradeTxHash ≠ 0 ∧ s.l2SystemContractsUpgradeBatchNumber = 0)
  let upgradeTx : Word := if processUpgrade then s.l2SystemContractsUpgradeTxHash else 0
  let args : CommitArgs := ⟨last.batchHash, b, upgradeTx⟩
  let info := storedInfoOf env args
  { s with
    l2SystemContractsUpgradeBatchNumber :=
      if processUpgrade then b.batchNumber else s.l2SystemContractsUpgradeBatchNumber
    storedBatchHashes := Function.update s.storedBatchHashes b.batchNumber (env.hashStored info)
    interopFeeUnits := Function.update s.interopFeeUnits b.batchNumber b.interopFeeUnits
    totalBatchesCommitted := s.totalBatchesCommitted + 1
    preimage := Function.update s.preimage b.batchNumber info
    commitArgs := Function.update s.commitArgs b.batchNumber (some args)
    hashBreaks := s.hashBreaks ++ logHash s s.totalBatchesCommitted last }

theorem commit_some {env : Env} {s s' : State} {c : CommitCall}
    (h : commit env s c = some s') :
    ∃ b, c.newBatches = [b] ∧ settlerAllowed s c.caller = true ∧ s.settlementLayer = 0 ∧
      s.storedBatchHashes s.totalBatchesCommitted = env.hashStored c.lastCommitted ∧
      b.batchNumber = c.lastCommitted.batchNumber + 1 ∧
      ¬ (s.priorityModeActivated = true ∧ (b.numberOfLayer2Txs ≠ 0 ∨ b.numberOfLayer1Txs = 0)) ∧
      s' = commitState env s c.lastCommitted b := by
  unfold commit at h
  split at h
  · simp at h
  rename_i h1
  split at h
  · simp at h
  rename_i h2
  split at h
  · simp at h
  rename_i h3
  split at h
  · rename_i b hb
    split at h
    · simp at h
    rename_i h4
    simp only [] at h
    split at h
    · simp at h
    rename_i h5
    split at h
    · simp at h
    rename_i h6
    injection h with h
    exact ⟨b, hb, by simpa using h1, by simpa using h2, by simpa using h4, by simpa using h5,
      h6, h.symm⟩
  · simp at h

theorem inv_commit {env : Env} {s s' : State} {c : CommitCall} (hi : Inv env s)
    (h : commit env s c = some s') : Inv env s' := by
  obtain ⟨b, -, -, -, hhash, hnum, -, rfl⟩ := commit_some h
  have hev := hi.ev
  have hvc := hi.vc
  refine
    { ev := by simp only [commitState]; omega
      vc := by simp only [commitState]; omega
      execNums := hi.execNums, execPrio := hi.execPrio, logRoots := hi.logRoots
      unproc := hi.unproc, roots := hi.roots
      merkleGenuine := hi.merkleGenuine, prefixOk := hi.prefixOk, verifiedOk := hi.verifiedOk
      firstBreak := ?_, clean := ?_ }
  · simp only [commitState]
    exact firstBreak_append hi.firstBreak
      (fun hc => logHash_genuine hhash ((hi.clean hc).hashes _ le_rfl))
  · intro hc'
    simp only [commitState, List.append_eq_nil_iff] at hc'
    obtain ⟨hc, hl⟩ := hc'
    have c0 := hi.clean hc
    have hlast : c.lastCommitted = s.preimage s.totalBatchesCommitted := logHash_eq_nil.1 hl
    have hN : b.batchNumber = s.totalBatchesCommitted + 1 := by
      rw [hnum, hlast, c0.numbers _ le_rfl]
    have hexec : ∀ r ∈ s.executed, r.info.batchNumber ≤ s.totalBatchesExecuted :=
      fun r hr => (mem_executed_bounds hi.execNums hr).2
    simp only [commitState]
    refine
      { hashes := ?_, numbers := ?_, chain := ?_, fees := ?_, execInfo := ?_, proved := ?_
        execProved := c0.execProved, upPending := ?_, upWaiting := ?_, upOthers := ?_ }
    · intro m hm
      dsimp only at hm ⊢
      rw [hN]
      by_cases hm' : m = s.totalBatchesCommitted + 1
      · subst hm'; simp
      · rw [Function.update_of_ne hm', Function.update_of_ne hm']
        exact c0.hashes m (by omega)
    · intro m hm
      dsimp only at hm ⊢
      rw [hN]
      by_cases hm' : m = s.totalBatchesCommitted + 1
      · subst hm'; simp [storedInfoOf, hN]
      · rw [Function.update_of_ne hm']
        exact c0.numbers m (by omega)
    · intro m h1 hm
      dsimp only at hm ⊢
      rw [hN]
      by_cases hm' : m = s.totalBatchesCommitted + 1
      · subst hm'
        refine ⟨_, Function.update_self _ _ _, ?_, Function.update_self _ _ _⟩
        rw [Function.update_of_ne (by omega), Nat.add_sub_cancel, ← hlast]
      · rw [Function.update_of_ne hm', Function.update_of_ne hm',
          Function.update_of_ne (by omega)]
        exact c0.chain m h1 (by omega)
    · intro m h1 hm a ha
      dsimp only at hm ha ⊢
      rw [hN] at ha ⊢
      by_cases hm' : m = s.totalBatchesCommitted + 1
      · subst hm'
        simp only [Function.update_self, Option.some.injEq] at ha ⊢
        subst ha; rfl
      · rw [Function.update_of_ne hm'] at ha ⊢
        exact c0.fees m h1 (by omega) a ha
    · intro r hr
      dsimp only
      rw [hN, Function.update_of_ne (by have := hexec r hr; omega)]
      exact c0.execInfo r hr
    · intro m h1 h2
      dsimp only at h1 h2 ⊢
      rw [hN, Function.update_of_ne (by omega)]
      exact c0.proved m h1 h2
    · dsimp only
      by_cases hp : s.l2SystemContractsUpgradeTxHash ≠ 0 ∧
          s.l2SystemContractsUpgradeBatchNumber = 0
      · have hce := c0.upWaiting hp.1 hp.2
        have hd := decide_eq_true hp
        simp only [hd, ↓reduceIte]
        intro _
        refine ⟨hp.1, by omega, by omega, _, Function.update_self _ _ _, rfl⟩
      · have hd := decide_eq_false hp
        simp only [hd, Bool.false_eq_true, ↓reduceIte]
        intro hne
        obtain ⟨a1, a2, a3, a, ha, ha'⟩ := c0.upPending hne
        refine ⟨a1, a2, by omega, a, ?_, ha'⟩
        rw [hN, Function.update_of_ne (by omega)]
        exact ha
    · dsimp only
      intro htx hub
      by_cases hp : s.l2SystemContractsUpgradeTxHash ≠ 0 ∧
          s.l2SystemContractsUpgradeBatchNumber = 0
      · have hd := decide_eq_true hp
        simp only [hd, ↓reduceIte] at hub; omega
      · have hd := decide_eq_false hp
        simp only [hd, Bool.false_eq_true, ↓reduceIte] at hub
        exact absurd ⟨htx, hub⟩ hp
    · dsimp only
      intro m h1 h2 hne a ha
      rw [hN] at ha
      by_cases hp : s.l2SystemContractsUpgradeTxHash ≠ 0 ∧
          s.l2SystemContractsUpgradeBatchNumber = 0
      · have hce := c0.upWaiting hp.1 hp.2
        have hd := decide_eq_true hp
        simp only [hd, ↓reduceIte] at hne
        rw [Function.update_of_ne (by omega)] at ha
        omega
      · have hd := decide_eq_false hp
        simp only [hd, Bool.false_eq_true, ↓reduceIte] at hne
        by_cases hm' : m = s.totalBatchesCommitted + 1
        · subst hm'
          simp only [Function.update_self, Option.some.injEq] at ha
          subst ha
          simp [hp]
        · rw [Function.update_of_ne hm'] at ha
          exact c0.upOthers m h1 (by omega) hne a ha

/-! ## Prove -/

theorem proveChecks_spec {env : Env} {s : State} :
    ∀ {n : Nat} {bs : List StoredBatchInfo}, proveChecks env s n bs = true →
    ∀ j b, bs[j]? = some b → s.storedBatchHashes (n + 1 + j) = env.hashStored b
  | _, [], _, j, b, hb => by simp at hb
  | n, x :: bs, h, j, b, hb => by
    simp only [proveChecks, Bool.and_eq_true, decide_eq_true_eq] at h
    cases j with
    | zero => simp at hb; subst hb; simpa using h.1
    | succ j =>
      simp at hb
      have := proveChecks_spec h.2 j b hb
      rw [show n + 1 + (j + 1) = n + 1 + 1 + j by omega]; exact this

theorem mem_proveBreaks {s : State} :
    ∀ {n : Nat} {bs : List StoredBatchInfo} {br : HashBreak}, br ∈ proveBreaks s n bs →
    ∃ j b, bs[j]? = some b ∧ br = ⟨n + 1 + j, b, s.preimage (n + 1 + j)⟩ ∧
      b ≠ s.preimage (n + 1 + j)
  | _, [], _, h => by simp [proveBreaks] at h
  | n, x :: bs, br, h => by
    simp only [proveBreaks, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨rfl, hne⟩ := mem_logHash h
      exact ⟨0, x, by simp, by simp, by simpa using hne⟩
    · obtain ⟨j, b, hb, rfl, hne⟩ := mem_proveBreaks h
      refine ⟨j + 1, b, by simpa using hb, ?_, ?_⟩
      · rw [show n + 1 + (j + 1) = n + 1 + 1 + j by omega]
      · rw [show n + 1 + (j + 1) = n + 1 + 1 + j by omega]; exact hne

theorem proveBreaks_nil {s : State} :
    ∀ {n : Nat} {bs : List StoredBatchInfo}, proveBreaks s n bs = [] →
    ∀ j b, bs[j]? = some b → b = s.preimage (n + 1 + j)
  | _, [], _, j, b, hb => by simp at hb
  | n, x :: bs, h, j, b, hb => by
    simp only [proveBreaks, List.append_eq_nil_iff] at h
    cases j with
    | zero => simp at hb; subst hb; simpa using logHash_eq_nil.1 h.1
    | succ j =>
      simp at hb
      rw [show n + 1 + (j + 1) = n + 1 + 1 + j by omega]
      exact proveBreaks_nil h.2 j b hb

theorem proveWith_some {ab : Bool} {env : Env} {s s' : State} {c : ProveCall}
    (h : proveWith ab env s c = some s') :
    settlerAllowed s c.caller = true ∧ s.settlementLayer = 0 ∧
      c.batches ≠ [] ∧
      proveChecks env s s.totalBatchesVerified c.batches = true ∧
      (ab = false → s.totalBatchesVerified + c.batches.length ≤ s.totalBatchesCommitted) ∧
      env.verify (c.batches.map (·.commitment)) c.proof = true ∧
      s' = { s with
        totalBatchesVerified := s.totalBatchesVerified + c.batches.length
        verified := s.verified ++ [⟨s.totalBatchesVerified + 1, c.batches, c.proof⟩]
        hashBreaks := s.hashBreaks ++ proveBreaks s s.totalBatchesVerified c.batches } := by
  unfold proveWith at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7
  injection h with h
  refine ⟨by simpa using h1, by simpa using h2, ?_, by simpa using h5, ?_, by simpa using h7,
    h.symm⟩
  · intro hn
    simp [hn, boundsOk] at h3
  · intro hab; subst hab; simp at h6; omega

theorem inv_prove {env : Env} {s s' : State} {c : ProveCall} (hi : Inv env s)
    (h : prove env s c = some s') : Inv env s' := by
  obtain ⟨-, -, hne, hchk, hle, hver, rfl⟩ := proveWith_some h
  have hle := hle rfl
  have hev := hi.ev
  refine
    { ev := by dsimp only; omega
      vc := by dsimp only; omega
      execNums := hi.execNums, execPrio := hi.execPrio, logRoots := hi.logRoots
      unproc := hi.unproc, roots := hi.roots
      merkleGenuine := hi.merkleGenuine, prefixOk := hi.prefixOk
      verifiedOk := ?_, firstBreak := ?_, clean := ?_ }
  · intro call hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hi.verifiedOk call hc
    · exact hver
  · dsimp only
    refine firstBreak_append hi.firstBreak (fun hc br hbr => ?_)
    obtain ⟨j, b, hb, rfl, hne'⟩ := mem_proveBreaks hbr
    have hj : j < c.batches.length := (List.getElem?_eq_some_iff.1 hb).1
    refine ⟨hne', ?_⟩
    rw [← proveChecks_spec hchk j b hb, (hi.clean hc).hashes _ (by omega)]
  · intro hc'
    simp only [List.append_eq_nil_iff] at hc'
    obtain ⟨hc, hl⟩ := hc'
    have c0 := hi.clean hc
    have hsub : ∀ call ∈ s.verified, call ∈ s.verified ++
        [⟨s.totalBatchesVerified + 1, c.batches, c.proof⟩] :=
      fun call h => List.mem_append_left _ h
    refine
      { hashes := c0.hashes, numbers := c0.numbers, chain := c0.chain, fees := c0.fees
        execInfo := c0.execInfo
        proved := ?_
        execProved := fun r hr => provedAt_mono (s' := { s with
          totalBatchesVerified := s.totalBatchesVerified + c.batches.length
          verified := s.verified ++ [⟨s.totalBatchesVerified + 1, c.batches, c.proof⟩]
          hashBreaks := s.hashBreaks ++ proveBreaks s s.totalBatchesVerified c.batches })
          hsub (c0.execProved r hr)
        upPending := c0.upPending, upWaiting := c0.upWaiting, upOthers := c0.upOthers }
    intro m h1 h2
    dsimp only at h1 h2 ⊢
    by_cases hm : m ≤ s.totalBatchesVerified
    · exact provedAt_mono (s := s) hsub (c0.proved m h1 hm)
    · obtain ⟨j, rfl⟩ : ∃ j, m = s.totalBatchesVerified + 1 + j :=
        ⟨m - (s.totalBatchesVerified + 1), by omega⟩
      have hj : j < c.batches.length := by omega
      obtain ⟨b, hb⟩ : ∃ b, c.batches[j]? = some b := ⟨_, List.getElem?_eq_getElem hj⟩
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), j, rfl, ?_⟩
      rw [hb, proveBreaks_nil hl j b hb]

/-! ## Execute -/

/-- The state `processBatch` writes on success, for some merkle-break log `X`. -/
def pbState (s : State) (ops : PriorityOpsBatchInfo) (X : List MerkleBreak) : State :=
  { s with
    ptUnprocessedIndex := s.ptUnprocessedIndex + ops.itemHashes.length
    merkleBreaks := s.merkleBreaks ++ X }

theorem processBatch_spec {env : Env} {s s1 : State} {ops : PriorityOpsBatchInfo}
    (h : processBatch env s ops = some s1)
    (hroots : ∀ r, s.ptHistoricalRoots r = true →
      ∃ k ≤ s.ptLeaves.length, r = env.treeRoot (s.ptLeaves.take k)) :
    ∃ X, s1 = pbState s ops X ∧ (∀ br ∈ X, br.Genuine env) ∧
      (X = [] → s.ptUnprocessedIndex ≤ s.ptLeaves.length →
        SegmentOk s.ptLeaves s.ptUnprocessedIndex ops.itemHashes) := by
  unfold processBatch at h
  split at h
  · rename_i hpos
    split at h
    · simp at h
    · rename_i hroot
      injection h with h
      subst h
      refine ⟨_, rfl, ?_, ?_⟩
      · intro br hbr
        split at hbr
        · simp at hbr
        · rename_i hseg
          simp only [List.mem_singleton] at hbr
          subst hbr
          obtain ⟨k, hk, hr⟩ := hroots _ (by simpa using hroot)
          exact ⟨hseg, k, hk, hr⟩
      · intro hX _
        split at hX
        · assumption
        · simp at hX
  · rename_i hlen
    injection h with h
    subst h
    have h0 : ops.itemHashes = [] := List.eq_nil_of_length_eq_zero (by omega)
    refine ⟨[], ?_, by simp, fun _ hu => by rw [h0]; exact segment_nil _ _ hu⟩
    simp [pbState, h0]

theorem executeOne_spec {env : Env} {s s' : State} {i : Nat} {b : ExecBatch}
    (h : executeOne env s i b = some s')
    (hroots : ∀ r, s.ptHistoricalRoots r = true →
      ∃ k ≤ s.ptLeaves.length, r = env.treeRoot (s.ptLeaves.take k)) :
    b.ops.itemHashes.length = b.info.numberOfLayer1Txs ∧
    b.info.batchNumber = s.totalBatchesExecuted + i + 1 ∧
    s.storedBatchHashes b.info.batchNumber = env.hashStored b.info ∧
    env.rollingHash b.ops.itemHashes = b.info.priorityOperationsHash ∧
    ∃ X, (∀ br ∈ X, br.Genuine env) ∧
      (X = [] → s.ptUnprocessedIndex ≤ s.ptLeaves.length →
        SegmentOk s.ptLeaves s.ptUnprocessedIndex b.ops.itemHashes) ∧
      s' = { pbState s b.ops X with
        l2LogsRootHashes := Function.update s.l2LogsRootHashes b.info.batchNumber
          b.info.l2LogsTreeRoot
        executed := s.executed ++ [⟨b.info, b.ops.itemHashes⟩]
        hashBreaks := s.hashBreaks ++ logHash s b.info.batchNumber b.info } := by
  unfold executeOne at h
  split at h
  · simp at h
  rename_i h1
  split at h
  · simp at h
  rename_i depHash _
  split at h
  · simp at h
  rename_i h2
  split at h
  · simp at h
  rename_i h3
  split at h
  · simp at h
  rename_i h4
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i s1 hpb
  injection h with h
  subst h
  obtain ⟨X, rfl, hX, hseg⟩ := processBatch_spec hpb hroots
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4, X, hX, hseg,
    rfl⟩

/-- Fields the execute loop does not write. -/
structure ExecFrame (s0 s : State) : Prop where
  e : s.totalBatchesExecuted = s0.totalBatchesExecuted
  v : s.totalBatchesVerified = s0.totalBatchesVerified
  c : s.totalBatchesCommitted = s0.totalBatchesCommitted
  stored : s.storedBatchHashes = s0.storedBatchHashes
  pre : s.preimage = s0.preimage
  args : s.commitArgs = s0.commitArgs
  tx : s.l2SystemContractsUpgradeTxHash = s0.l2SystemContractsUpgradeTxHash
  ubn : s.l2SystemContractsUpgradeBatchNumber = s0.l2SystemContractsUpgradeBatchNumber
  verified : s.verified = s0.verified
  leaves : s.ptLeaves = s0.ptLeaves
  roots : s.ptHistoricalRoots = s0.ptHistoricalRoots
  fee : s.interopFeeUnits = s0.interopFeeUnits
  logs : ∀ n ≤ s0.totalBatchesExecuted, s.l2LogsRootHashes n = s0.l2LogsRootHashes n

/-- The execute loop's invariant after `i` batches, relative to its start state `s0`. -/
def LoopInv (env : Env) (s0 : State) (i : Nat) (s : State) : Prop :=
  ExecFrame s0 s ∧
  ∃ (new : List ExecRecord) (hb : List HashBreak) (mb : List MerkleBreak),
    s.executed = s0.executed ++ new ∧ s.hashBreaks = s0.hashBreaks ++ hb ∧
    s.merkleBreaks = s0.merkleBreaks ++ mb ∧
    new.map (·.info.batchNumber) = List.range' (s0.totalBatchesExecuted + 1) i ∧
    (∀ r ∈ new, r.items.length = r.info.numberOfLayer1Txs ∧
      env.rollingHash r.items = r.info.priorityOperationsHash ∧
      s0.storedBatchHashes r.info.batchNumber = env.hashStored r.info) ∧
    s.ptUnprocessedIndex = s0.ptUnprocessedIndex + (new.flatMap (·.items)).length ∧
    (∀ br ∈ hb, br.submitted ≠ br.stored ∧
      s0.storedBatchHashes br.index = env.hashStored br.submitted ∧
      br.stored = s0.preimage br.index ∧ br.index ≤ s0.totalBatchesExecuted + i) ∧
    (hb = [] → ∀ r ∈ new, r.info = s0.preimage r.info.batchNumber) ∧
    (∀ br ∈ mb, br.Genuine env) ∧
    (mb = [] → s0.ptUnprocessedIndex ≤ s0.ptLeaves.length →
      SegmentOk s0.ptLeaves s0.ptUnprocessedIndex (new.flatMap (·.items))) ∧
    (∀ r ∈ new, s.l2LogsRootHashes r.info.batchNumber = r.info.l2LogsTreeRoot)

theorem loopInv_zero {env : Env} (s0 : State) : LoopInv env s0 0 s0 := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩,
    [], [], [], by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
    by simp, fun _ hu => by simpa using segment_nil _ _ hu, by simp⟩

theorem loopInv_step {env : Env} {s0 s s' : State} {i : Nat} {b : ExecBatch}
    (hl : LoopInv env s0 i s)
    (hroots : ∀ r, s0.ptHistoricalRoots r = true →
      ∃ k ≤ s0.ptLeaves.length, r = env.treeRoot (s0.ptLeaves.take k))
    (h : executeOne env s i b = some s') : LoopInv env s0 (i + 1) s' := by
  obtain ⟨hF, new, hb, mb, hex, hhb, hmb, hnums, hrec, hu, hhbOk, hhbNil, hmbOk, hseg,
    hlog⟩ := hl
  have hroots' : ∀ r, s.ptHistoricalRoots r = true →
      ∃ k ≤ s.ptLeaves.length, r = env.treeRoot (s.ptLeaves.take k) := by
    rw [hF.roots, hF.leaves]; exact hroots
  obtain ⟨hlen, hnum, hst, hroll, X, hX, hXseg, rfl⟩ := executeOne_spec h hroots'
  rw [hF.e] at hnum
  rw [hF.stored] at hst
  refine ⟨⟨hF.e, hF.v, hF.c, hF.stored, hF.pre, hF.args, hF.tx, hF.ubn, hF.verified, hF.leaves,
    hF.roots, hF.fee, fun n hn => ?_⟩, new ++ [⟨b.info, b.ops.itemHashes⟩],
    hb ++ logHash s b.info.batchNumber b.info, mb ++ X, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · dsimp only [pbState]
    rw [Function.update_of_ne (by omega)]
    exact hF.logs n hn
  · dsimp only [pbState]; rw [hex, List.append_assoc]
  · dsimp only [pbState]; rw [hhb, List.append_assoc]
  · dsimp only [pbState]; rw [hmb, List.append_assoc]
  · rw [List.map_append, hnums, List.range'_concat]
    simp only [List.map_cons, List.map_nil, List.append_cancel_left_eq, List.cons.injEq, and_true]
    omega
  · intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact hrec r hr
    · exact ⟨hlen, hroll, hst⟩
  · dsimp only [pbState]
    rw [hu, List.flatMap_append]; simp; omega
  · intro br hbr
    simp only [List.mem_append] at hbr
    rcases hbr with hbr | hbr
    · obtain ⟨a1, a2, a3, a4⟩ := hhbOk br hbr; exact ⟨a1, a2, a3, by omega⟩
    · obtain ⟨rfl, hne⟩ := mem_logHash hbr
      exact ⟨hne, hst, by rw [hF.pre], by dsimp only; omega⟩
  · intro hnil r hr
    simp only [List.append_eq_nil_iff] at hnil
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact hhbNil hnil.1 r hr
    · rw [← hF.pre]; exact logHash_eq_nil.1 hnil.2
  · intro br hbr
    simp only [List.mem_append] at hbr
    rcases hbr with hbr | hbr
    · exact hmbOk br hbr
    · exact hX br hbr
  · intro hnil hu0
    simp only [List.append_eq_nil_iff] at hnil
    have h1 := hseg hnil.1 hu0
    have h2 : SegmentOk s.ptLeaves s.ptUnprocessedIndex b.ops.itemHashes :=
      hXseg hnil.2 (by rw [hu, hF.leaves]; exact h1.1)
    rw [hF.leaves, hu] at h2
    rw [List.flatMap_append]
    simpa using segment_append h1 h2
  · intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    dsimp only [pbState]
    rcases hr with hr | rfl
    · have hmem : r.info.batchNumber ∈ List.range' (s0.totalBatchesExecuted + 1) i := by
        rw [← hnums]; exact List.mem_map_of_mem hr
      rw [List.mem_range'_1] at hmem
      rw [Function.update_of_ne (by omega)]
      exact hlog r hr
    · exact Function.update_self _ _ _

theorem loopInv_run {env : Env} {s0 : State}
    (hroots : ∀ r, s0.ptHistoricalRoots r = true →
      ∃ k ≤ s0.ptLeaves.length, r = env.treeRoot (s0.ptLeaves.take k)) :
    ∀ {bs : List ExecBatch} {s s1 : State} {i : Nat}, LoopInv env s0 i s →
    executeLoop env s i bs = some s1 → LoopInv env s0 (i + bs.length) s1
  | [], s, s1, i, hl, h => by
    simp only [executeLoop, Option.some.injEq] at h; subst h; simpa using hl
  | b :: bs, s, s1, i, hl, h => by
    simp only [executeLoop] at h
    split at h
    · simp at h
    · rename_i s2 h2
      have := loopInv_run hroots (loopInv_step hl hroots h2) h
      rw [List.length_cons]
      rwa [show i + (bs.length + 1) = i + 1 + bs.length by omega]

theorem executeWith_some {ab : Bool} {env : Env} {s s' : State} {c : ExecuteCall}
    (h : executeWith ab env s c = some s') :
    settlerAllowed s c.caller = true ∧ s.settlementLayer = 0 ∧ c.batches ≠ [] ∧
    ∃ s1, executeLoop env s 0 c.batches = some s1 ∧
      (ab = false → s.totalBatchesExecuted + c.batches.length ≤ s1.totalBatchesVerified) ∧
      let cond := s1.l2SystemContractsUpgradeBatchNumber ≠ 0 ∧
        s1.l2SystemContractsUpgradeBatchNumber ≤ s.totalBatchesExecuted + c.batches.length
      s' = { s1 with
        totalBatchesExecuted := s.totalBatchesExecuted + c.batches.length
        l2SystemContractsUpgradeTxHash :=
          if cond then 0 else s1.l2SystemContractsUpgradeTxHash
        l2SystemContractsUpgradeBatchNumber :=
          if cond then 0 else s1.l2SystemContractsUpgradeBatchNumber } := by
  unfold executeWith at h
  split at h
  · simp at h
  rename_i h1
  split at h
  · simp at h
  rename_i h2
  split at h
  · simp at h
  rename_i h3
  split at h
  · simp at h
  rename_i s1 hloop
  split at h
  · simp at h
  rename_i h4
  refine ⟨by simpa using h1, by simpa using h2, ?_, s1, hloop, ?_, ?_⟩
  · intro hn; simp [hn, boundsOk] at h3
  · intro hab; subst hab; simp at h4; omega
  · split at h
    · rename_i hc
      injection h with h; subst h; simp [hc]
    · rename_i hc
      injection h with h; subst h; simp [hc]

theorem inv_execute {env : Env} {s s' : State} {c : ExecuteCall} (hi : Inv env s)
    (h : execute env s c = some s') :
    Inv env s' ∧ (∀ n ≤ s.totalBatchesExecuted,
      s'.l2LogsRootHashes n = s.l2LogsRootHashes n) ∧
    s'.storedBatchHashes = s.storedBatchHashes ∧ s'.preimage = s.preimage := by
  obtain ⟨-, -, hne, s1, hloop, hle, rfl⟩ := executeWith_some h
  have hle := hle rfl
  have hl := loopInv_run hi.roots (loopInv_zero s) hloop
  rw [Nat.zero_add] at hl
  obtain ⟨hF, new, hb, mb, hex, hhb, hmb, hnums, hrec, hu, hhbOk, hhbNil, hmbOk, hseg,
    hlog⟩ := hl
  have hev := hi.ev
  have hvc := hi.vc
  have hpos : 0 < c.batches.length := List.length_pos_iff.2 hne
  have hnewNum : ∀ r ∈ new, s.totalBatchesExecuted < r.info.batchNumber ∧
      r.info.batchNumber ≤ s.totalBatchesExecuted + c.batches.length := by
    intro r hr
    have : r.info.batchNumber ∈ List.range' (s.totalBatchesExecuted + 1) c.batches.length := by
      rw [← hnums]; exact List.mem_map_of_mem hr
    rw [List.mem_range'_1] at this; omega
  rw [hF.v] at hle
  refine ⟨?_, fun n hn => hF.logs n hn, hF.stored, hF.pre⟩
  refine
    { ev := by dsimp only; rw [hF.v]; exact hle
      vc := by dsimp only; rw [hF.v, hF.c]; exact hvc
      execNums := ?_, execPrio := ?_, logRoots := ?_, unproc := ?_
      roots := by dsimp only; rw [hF.roots, hF.leaves]; exact hi.roots
      merkleGenuine := ?_, prefixOk := ?_
      verifiedOk := by dsimp only; rw [hF.verified]; exact hi.verifiedOk
      firstBreak := ?_, clean := ?_ }
  · dsimp only
    rw [hex, List.map_append, hi.execNums, hnums,
      show s.totalBatchesExecuted + 1 = 1 + s.totalBatchesExecuted from Nat.add_comm _ _,
      List.range'_append_1]
  · dsimp only
    rw [hex]
    intro r hr
    simp only [List.mem_append] at hr
    rcases hr with hr | hr
    · exact hi.execPrio r hr
    · exact ⟨(hrec r hr).1, (hrec r hr).2.1⟩
  · dsimp only
    rw [hex]
    intro r hr
    simp only [List.mem_append] at hr
    rcases hr with hr | hr
    · rw [hF.logs _ (mem_executed_bounds hi.execNums hr).2]
      exact hi.logRoots r hr
    · exact hlog r hr
  · dsimp only [consumed]
    rw [hu, hex, List.flatMap_append, List.length_append, hi.unproc]
    rfl
  · dsimp only
    rw [hmb]
    intro br hbr
    simp only [List.mem_append] at hbr
    rcases hbr with hbr | hbr
    · exact hi.merkleGenuine br hbr
    · exact hmbOk br hbr
  · dsimp only
    intro hnil
    rw [hmb, List.append_eq_nil_iff] at hnil
    obtain ⟨hc0, hu0⟩ := hi.prefixOk hnil.1
    have hs := hseg hnil.2 hu0
    rw [hF.leaves, hu]
    refine ⟨?_, hs.1⟩
    simp only [consumed]
    rw [hex, List.flatMap_append]
    rw [show s.executed.flatMap (·.items) = consumed s from rfl, hc0]
    exact take_append_segment hs
  · dsimp only
    rw [hhb]
    refine firstBreak_append hi.firstBreak (fun hc br hbr => ?_)
    obtain ⟨a1, a2, a3, a4⟩ := hhbOk br hbr
    refine ⟨a1, ?_⟩
    rw [← a2, a3, (hi.clean hc).hashes _ (by omega)]
  · dsimp only
    intro hc'
    rw [hhb, List.append_eq_nil_iff] at hc'
    have c0 := hi.clean hc'.1
    have hnewInfo := hhbNil hc'.2
    have hpv : ∀ {n b}, ProvedAt s1 n b ↔ ProvedAt s n b := by
      intro n b; simp only [ProvedAt, hF.verified]
    refine
      { hashes := by rw [hF.c, hF.stored, hF.pre]; exact c0.hashes
        numbers := by rw [hF.c, hF.pre]; exact c0.numbers
        chain := by rw [hF.c, hF.pre, hF.args]; exact c0.chain
        fees := by rw [hF.c, hF.args, hF.fee]; exact c0.fees
        execInfo := ?_, proved := ?_, execProved := ?_
        upPending := ?_, upWaiting := ?_, upOthers := ?_ }
    · rw [hex, hF.pre]
      intro r hr
      simp only [List.mem_append] at hr
      rcases hr with hr | hr
      · exact c0.execInfo r hr
      · exact hnewInfo r hr
    · intro n h1 h2
      dsimp only at h1 h2
      rw [hF.pre]
      exact hpv.2 (c0.proved n (by omega) (by rw [hF.v] at h2; exact h2))
    · rw [hex]
      intro r hr
      simp only [List.mem_append] at hr
      rcases hr with hr | hr
      · exact hpv.2 (c0.execProved r hr)
      · have hb := hnewNum r hr
        have h' := c0.proved _ hb.1 (by omega)
        rw [← hnewInfo r hr] at h'
        exact hpv.2 h'
    · simp only [hF.ubn, hF.tx, hF.c, hF.args]
      by_cases hcond : s.l2SystemContractsUpgradeBatchNumber ≠ 0 ∧
          s.l2SystemContractsUpgradeBatchNumber ≤ s.totalBatchesExecuted + c.batches.length
      · simp only [eq_true hcond, ↓reduceIte]; intro h; exact absurd rfl h
      · simp only [eq_false hcond, ↓reduceIte]
        intro hub
        have := (c0.upPending hub).2.1
        exact absurd ⟨hub, by omega⟩ hcond
    · simp only [hF.ubn, hF.tx, hF.c]
      by_cases hcond : s.l2SystemContractsUpgradeBatchNumber ≠ 0 ∧
          s.l2SystemContractsUpgradeBatchNumber ≤ s.totalBatchesExecuted + c.batches.length
      · simp only [eq_true hcond, ↓reduceIte]; intro h; exact absurd rfl h
      · simp only [eq_false hcond, ↓reduceIte]
        intro htx hub
        have := c0.upWaiting htx hub
        omega
    · simp only [hF.ubn, hF.c, hF.args]
      intro m h1 h2 hne a ha
      split at hne
      · rename_i hcond
        have := (c0.upPending hcond.1).2.1
        exact c0.upOthers m (by omega) h2 (by omega) a ha
      · exact c0.upOthers m (by omega) h2 hne a ha

/-! ## Every entry point -/

theorem revertShared_some {ab : Bool} {s s' : State} {caller n : Nat}
    (h : revertBatchesSharedBridgeWith ab s caller n = some s') :
    (s.validators caller = true ∨ caller = s.chainTypeManager) ∧
    s.priorityModeActivated = false ∧ s.settlementLayer = 0 ∧
    revertBatchesWith ab s n = some s' := by
  unfold revertBatchesSharedBridgeWith at h
  split at h
  · simp at h
  rename_i h1
  split at h
  · simp at h
  rename_i h2
  split at h
  · simp at h
  rename_i h3
  exact ⟨not_not.1 h1, by simpa using h2, by simpa using h3, h⟩

theorem activate_some {s s' : State} (h : activatePriorityMode s = some s') :
    s.settlementLayer = 0 ∧ s.priorityModeActivated = false ∧
    revertBatches { s with priorityModeActivated := true } s.totalBatchesExecuted = some s' := by
  unfold activatePriorityMode at h
  split at h
  · simp at h
  rename_i h1
  split at h
  · simp at h
  rename_i h2
  exact ⟨by simpa using h1, by simpa using h2, h⟩

theorem deactivate_some {s s' : State} {caller : Addr}
    (h : deactivatePriorityMode s caller = some s') :
    s' = { s with priorityModeActivated := false } := by
  unfold deactivatePriorityMode at h
  split_ifs at h
  injection h with h; exact h.symm

theorem inv_step {env : Env} {s s' : State} {c : Call} (hi : Inv env s)
    (h : step env s c = some s') : Inv env s' := by
  cases c with
  | commit cc => exact inv_commit hi h
  | prove pc => exact inv_prove hi h
  | execute ec => exact (inv_execute hi h).1
  | revert caller n =>
    exact inv_revertBatches hi (revertShared_some h).2.2.2
  | activatePriorityMode =>
    exact inv_revertBatches (inv_setPriorityMode true hi) (activate_some h).2.2
  | deactivatePriorityMode caller =>
    rw [deactivate_some h]; exact inv_setPriorityMode false hi
  | pushPriorityOp hv =>
    simp only [step, stepWith, pushPriorityOp, Option.some.injEq] at h
    subst h; exact inv_push hv hi
  | setUpgradeTx hv => exact inv_setUpgradeTx hi h

theorem inv_reach {env : Env} {s : State} (h : Reach env s) : Inv env s := by
  induction h with
  | init hi => exact inv_init hi
  | step _ hs ih => obtain ⟨c, hc⟩ := hs; exact inv_step ih hc

theorem reach_runCalls {env : Env} :
    ∀ {cs : List Call} {s s' : State}, Reach env s → runCalls env s cs = some s' → Reach env s'
  | [], s, s', hr, h => by simp only [runCalls, Option.some.injEq] at h; subst h; exact hr
  | c :: cs, s, s', hr, h => by
    simp only [runCalls] at h
    split at h
    · simp at h
    · rename_i s2 h2
      exact reach_runCalls (Reach.step hr ⟨c, h2⟩) h

theorem reach_steps {env : Env} {s s' : State} (hr : Reach env s) (h : Steps env s s') :
    Reach env s' := by
  induction h with
  | refl => exact hr
  | tail _ hs ih => exact Reach.step ih hs

/-! ## One-step frame facts -/

theorem executeLoop_hashBreaks {env : Env} :
    ∀ {bs : List ExecBatch} {s s1 : State} {i : Nat},
    executeLoop env s i bs = some s1 → ∃ X, s1.hashBreaks = s.hashBreaks ++ X
  | [], s, s1, i, h => by
    simp only [executeLoop, Option.some.injEq] at h; subst h; exact ⟨[], by simp⟩
  | b :: bs, s, s1, i, h => by
    simp only [executeLoop] at h
    split at h
    · simp at h
    · rename_i s2 h2
      obtain ⟨X2, hX2⟩ := executeLoop_hashBreaks h
      have h3 : ∃ Y, s2.hashBreaks = s.hashBreaks ++ Y := by
        unfold executeOne at h2
        split at h2
        · simp at h2
        split at h2
        · simp at h2
        split at h2
        · simp at h2
        split at h2
        · simp at h2
        split at h2
        · simp at h2
        split at h2
        · simp at h2
        split at h2
        · simp at h2
        rename_i s3 hpb
        injection h2 with h2
        subst h2
        have : s3.hashBreaks = s.hashBreaks := by
          unfold processBatch at hpb
          split at hpb
          · split at hpb
            · simp at hpb
            · injection hpb with hpb; subst hpb; rfl
          · injection hpb with hpb; subst hpb; rfl
        exact ⟨_, by dsimp only; rw [this]⟩
      obtain ⟨Y, hY⟩ := h3
      exact ⟨Y ++ X2, by rw [hX2, hY, List.append_assoc]⟩

theorem setUpgradeTx_some {s s' : State} {hv : Word} (h : setUpgradeTx s hv = some s') :
    s' = { s with l2SystemContractsUpgradeTxHash := hv } := by
  unfold setUpgradeTx at h
  split_ifs at h
  injection h with h; exact h.symm

/-- Every step only appends to the hash-break log. -/
theorem step_hashBreaks {env : Env} {s s' : State} {c : Call} (h : step env s c = some s') :
    ∃ X, s'.hashBreaks = s.hashBreaks ++ X := by
  cases c with
  | commit cc => obtain ⟨b, -, -, -, -, -, -, rfl⟩ := commit_some h; exact ⟨_, rfl⟩
  | prove pc => obtain ⟨-, -, -, -, -, -, rfl⟩ := proveWith_some h; exact ⟨_, rfl⟩
  | execute ec =>
    obtain ⟨-, -, -, s1, hloop, -, rfl⟩ := executeWith_some h
    obtain ⟨X, hX⟩ := executeLoop_hashBreaks hloop
    exact ⟨X, hX⟩
  | revert caller n =>
    obtain ⟨-, -, -, h⟩ := revertShared_some h
    obtain ⟨-, -, rfl⟩ := revertBatches_some h; exact ⟨[], by simp⟩
  | activatePriorityMode =>
    obtain ⟨-, -, h⟩ := activate_some h
    obtain ⟨-, -, rfl⟩ := revertBatches_some h; exact ⟨[], by simp⟩
  | deactivatePriorityMode caller => rw [deactivate_some h]; exact ⟨[], by simp⟩
  | pushPriorityOp hv =>
    simp only [step, stepWith, pushPriorityOp, Option.some.injEq] at h
    subst h; exact ⟨[], by simp⟩
  | setUpgradeTx hv =>
    rw [setUpgradeTx_some (s := s) h]; exact ⟨[], by simp⟩

/-- One step from a state satisfying `Inv`: the executed count does not decrease and, if the
step logs no hash break onto a clean state, the stored hashes, preimages and log roots of
executed batches are unchanged. -/
theorem step_frozen {env : Env} {s s' : State} {c : Call} (hi : Inv env s)
    (h : step env s c = some s') :
    s.totalBatchesExecuted ≤ s'.totalBatchesExecuted ∧
    (s'.hashBreaks = [] → ∀ n ≤ s.totalBatchesExecuted,
      s'.storedBatchHashes n = s.storedBatchHashes n ∧ s'.preimage n = s.preimage n ∧
      s'.l2LogsRootHashes n = s.l2LogsRootHashes n) := by
  cases c with
  | commit cc =>
    obtain ⟨b, -, -, -, hhash, hnum, -, rfl⟩ := commit_some h
    refine ⟨by simp only [commitState]; exact le_rfl, fun hc' n hn => ?_⟩
    simp only [commitState, List.append_eq_nil_iff] at hc'
    have c0 := hi.clean hc'.1
    have hlast := logHash_eq_nil.1 hc'.2
    have hN : b.batchNumber = s.totalBatchesCommitted + 1 := by
      rw [hnum, hlast, c0.numbers _ le_rfl]
    have := hi.ev; have := hi.vc
    have hne : n ≠ b.batchNumber := by omega
    exact ⟨Function.update_of_ne hne _ _, Function.update_of_ne hne _ _, rfl⟩
  | prove pc =>
    obtain ⟨-, -, -, -, -, -, rfl⟩ := proveWith_some h
    exact ⟨le_rfl, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩
  | execute ec =>
    obtain ⟨hi', hlogs, hst, hpre⟩ := inv_execute hi h
    obtain ⟨-, -, -, s1, -, -, rfl⟩ := executeWith_some h
    refine ⟨by dsimp only; omega, fun _ n hn => ⟨?_, ?_, hlogs n hn⟩⟩
    · rw [hst]
    · rw [hpre]
  | revert caller n =>
    obtain ⟨-, -, -, h⟩ := revertShared_some h
    obtain ⟨-, -, rfl⟩ := revertBatches_some h
    exact ⟨le_rfl, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩
  | activatePriorityMode =>
    obtain ⟨-, -, h⟩ := activate_some h
    obtain ⟨-, -, rfl⟩ := revertBatches_some h
    exact ⟨le_rfl, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩
  | deactivatePriorityMode caller =>
    rw [deactivate_some h]; exact ⟨le_rfl, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩
  | pushPriorityOp hv =>
    simp only [step, stepWith, pushPriorityOp, Option.some.injEq] at h
    subst h; exact ⟨le_rfl, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩
  | setUpgradeTx hv =>
    rw [setUpgradeTx_some (s := s) h]; exact ⟨le_rfl, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩

end Contracts.ExecutorFacet
