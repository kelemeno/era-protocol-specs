import EraSpec.Contracts.ChainBatchRootTree.Properties.GenesisSeed
import EraSpec.Contracts.ChainBatchRootTree.Proofs.Layout

/-!
# Proofs: genesis seeding (see `../Specs/GenesisSeed.lean`)

Three facts about one message-root call carry everything:

* every `seedGenesisRoot` needs `chainBatchRoots[c][0] = 0` and leaves it nonzero, and no other
  call writes slot 0 (a recorded batch is `current + 1 ≥ 1`);
* a recorded batch leaves `c` registered with `current ≥ 1`, and from there no call lowers
  `current` (`setMigratingChainBatchNumber` needs `current ≤ n`) or re-registers `c`;
* `seedGenesisRoot` needs `current = 0`.

`GenesisRootStable` is the invariant "a chain contract exists ⇒ both slots hold the genesis root,
which is nonzero, and `c` is registered", checked step by step.
-/

namespace Contracts.ChainBatchRootTree

open MerkleSpec MerkleSpec.Verifier
open AttackVectors.BundleHashEncoding (HashCollision word toBytesBE)

/-! ## One call -/

theorem seedExec_addNewChain {m : SeedChainState} {read0 : Option UInt256} {start : ℕ}
    {m' : SeedChainState} (h : seedExec m read0 (.addNewChain start) = some m') :
    m.registered = false ∧ m' = { m with registered := true, current := start } := by
  simp only [seedExec] at h
  cases hr : m.registered <;> simp_all

theorem seedExec_setMigrating {m : SeedChainState} {read0 : Option UInt256} {n : ℕ}
    {m' : SeedChainState} (h : seedExec m read0 (.setMigratingChainBatchNumber n) = some m') :
    m.current ≤ n ∧ m' = { m with current := n } := by
  simp only [seedExec] at h
  split_ifs at h with h1
  · exact ⟨h1, (Option.some.inj h).symm⟩

theorem seedExec_record {m : SeedChainState} {read0 : Option UInt256} {n : ℕ} {r : UInt256}
    {m' : SeedChainState} (h : seedExec m read0 (.addChainBatchRoot n r) = some m') :
    m.registered = true ∧ r ≠ 0 ∧ m.roots n = 0 ∧ n = m.current + 1
      ∧ m' = { m with roots := Function.update m.roots n r, current := m.current + 1 } := by
  simp only [seedExec] at h
  split_ifs at h with h1 h2 h3 h4 h5
  refine ⟨?_, h2, ?_, ?_, (Option.some.inj h).symm⟩
  · simpa using h1
  · simpa using h3
  · simpa using h5

theorem seedExec_seed {m : SeedChainState} {read0 : Option UInt256} {m' : SeedChainState}
    (h : seedExec m read0 .seedGenesisRoot = some m') :
    ∃ g, read0 = some g ∧ g ≠ 0 ∧ m.registered = true ∧ m.current = 0 ∧ m.roots 0 = 0
      ∧ m' = { m with roots := Function.update m.roots 0 g } := by
  simp only [seedExec] at h
  cases read0 with
  | none => simp at h
  | some g =>
    simp only at h
    split_ifs at h with h1 h2 h3 h4
    refine ⟨g, rfl, h1, ?_, ?_, ?_, (Option.some.inj h).symm⟩
    · simpa using h2
    · simpa using h3
    · simpa using h4

/-! ## One step -/

theorem seedStep_createNewChain {keccak : Keccak} {s s' : SeedSystem}
    (h : seedStep keccak s .createNewChain = some s') :
    s.diamond = none ∧ s'.diamond = some (diamondInit keccak)
      ∧ ∃ mr₁, seedExec s.mr none (.addNewChain 0) = some mr₁
        ∧ seedExec mr₁ (some ((diamondInit keccak).logsRoots 0)) .seedGenesisRoot = some s'.mr := by
  unfold seedStep at h
  cases hd : s.diamond with
  | some d => simp [hd] at h
  | none =>
    simp only [hd] at h
    cases h1 : seedExec s.mr none (.addNewChain 0) with
    | none => simp [h1] at h
    | some mr₁ =>
      cases h2 : seedExec mr₁ (some ((diamondInit keccak).logsRoots 0)) .seedGenesisRoot with
      | none => simp [h1, h2] at h
      | some mr₂ =>
        simp only [h1, h2, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, Option.some.injEq] at h
        subst h
        exact ⟨rfl, rfl, mr₁, rfl, h2⟩

theorem seedStep_execute {keccak : Keccak} {s s' : SeedSystem} {r : UInt256}
    (h : seedStep keccak s (.execute r) = some s') :
    ∃ d, s.diamond = some d
      ∧ seedExec s.mr (some (d.logsRoots 0)) (.addChainBatchRoot (d.executed + 1) r) = some s'.mr
      ∧ s'.diamond = some ⟨Function.update d.logsRoots (d.executed + 1) r, d.executed + 1⟩ := by
  unfold seedStep at h
  cases hd : s.diamond with
  | none => simp [hd] at h
  | some d =>
    simp only [hd] at h
    cases h1 : seedExec s.mr (some (d.logsRoots 0)) (.addChainBatchRoot (d.executed + 1) r) with
    | none => simp [h1] at h
    | some mr' =>
      simp only [h1, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      subst h
      exact ⟨d, rfl, h1, rfl⟩

theorem seedStep_mrCall {keccak : Keccak} {s s' : SeedSystem} {call : SeedCall}
    (h : seedStep keccak s (.mrCall call) = some s') :
    seedExec s.mr (s.diamond.map (·.logsRoots 0)) call = some s'.mr ∧ s'.diamond = s.diamond := by
  unfold seedStep at h
  cases h1 : seedExec s.mr (s.diamond.map (·.logsRoots 0)) call with
  | none => simp [h1] at h
  | some mr' =>
    simp only [h1, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩

theorem seedStep_diamondOther {keccak : Keccak} {s s' : SeedSystem} {d' : SeedDiamond}
    (h : seedStep keccak s (.diamondOther d') = some s') :
    ∃ d, s.diamond = some d ∧ d'.logsRoots 0 = d.logsRoots 0 ∧ s' = ⟨some d', s.mr⟩ := by
  unfold seedStep at h
  cases hd : s.diamond with
  | none => simp [hd] at h
  | some d =>
    simp only [hd] at h
    split_ifs at h with h1
    exact ⟨d, rfl, h1, (Option.some.inj h).symm⟩

/-! ## Runs -/

theorem seedRun_append (keccak : Keccak) :
    ∀ (ls₁ ls₂ : List SeedLabel) (s : SeedSystem),
      seedRun keccak s (ls₁ ++ ls₂) = (seedRun keccak s ls₁).bind (fun t => seedRun keccak t ls₂)
  | [], _, _ => rfl
  | ℓ :: ls₁, ls₂, s => by
      simp only [List.cons_append, seedRun]
      cases seedStep keccak s ℓ with
      | none => rfl
      | some t => exact seedRun_append keccak ls₁ ls₂ t

theorem seedRun_cons {keccak : Keccak} {s t : SeedSystem} {ℓ : SeedLabel} {ls : List SeedLabel}
    (h : seedRun keccak s (ℓ :: ls) = some t) :
    ∃ s₁, seedStep keccak s ℓ = some s₁ ∧ seedRun keccak s₁ ls = some t := by
  simp only [seedRun] at h
  cases h1 : seedStep keccak s ℓ with
  | none => simp [h1] at h
  | some s₁ => exact ⟨s₁, rfl, by simpa [h1] using h⟩

/-! ## Slot 0 is written once -/

/-- A seeding step needs slot 0 empty and fills it; every other step keeps slot 0. -/
theorem seedStep_slot0 {keccak : Keccak} {s s' : SeedSystem} {ℓ : SeedLabel}
    (h : seedStep keccak s ℓ = some s') :
    (ℓ.IsSeed → s.mr.roots 0 = 0 ∧ s'.mr.roots 0 ≠ 0) ∧ (¬ ℓ.IsSeed → s'.mr.roots 0 = s.mr.roots 0) := by
  cases ℓ with
  | createNewChain =>
    obtain ⟨_, _, mr₁, h1, h2⟩ := seedStep_createNewChain h
    obtain ⟨_, rfl⟩ := seedExec_addNewChain h1
    obtain ⟨g, _, hg, _, _, h0, hm⟩ := seedExec_seed h2
    refine ⟨fun _ => ⟨h0, ?_⟩, fun hn => absurd trivial hn⟩
    rw [hm]
    simpa using hg
  | execute r =>
    obtain ⟨d, _, h1, _⟩ := seedStep_execute h
    obtain ⟨_, _, _, _, hm⟩ := seedExec_record h1
    refine ⟨fun hs => absurd hs id, fun _ => ?_⟩
    rw [hm]
    simp
  | mrCall call =>
    obtain ⟨h1, _⟩ := seedStep_mrCall h
    cases call with
    | addNewChain start =>
      obtain ⟨_, hm⟩ := seedExec_addNewChain h1
      exact ⟨fun hs => absurd hs id, fun _ => by rw [hm]⟩
    | setMigratingChainBatchNumber n =>
      obtain ⟨_, hm⟩ := seedExec_setMigrating h1
      exact ⟨fun hs => absurd hs id, fun _ => by rw [hm]⟩
    | addChainBatchRoot n r =>
      obtain ⟨_, _, _, hn, hm⟩ := seedExec_record h1
      refine ⟨fun hs => absurd hs id, fun _ => ?_⟩
      rw [hm]
      simp [Function.update_of_ne (show (0 : ℕ) ≠ n from by omega)]
    | seedGenesisRoot =>
      obtain ⟨g, _, hg, _, _, h0, hm⟩ := seedExec_seed h1
      refine ⟨fun _ => ⟨h0, ?_⟩, fun hn => absurd trivial hn⟩
      rw [hm]
      simpa using hg
  | diamondOther d' =>
    obtain ⟨_, _, _, rfl⟩ := seedStep_diamondOther h
    exact ⟨fun hs => absurd hs id, fun _ => rfl⟩

/-- From a state with slot 0 filled, no step of a successful run seeds, and slot 0 stays filled. -/
theorem seedRun_no_seed_of_filled (keccak : Keccak) :
    ∀ (ls : List SeedLabel) (s t : SeedSystem),
      seedRun keccak s ls = some t → s.mr.roots 0 ≠ 0 → seedCount ls = 0 ∧ t.mr.roots 0 ≠ 0
  | [], s, t, h, h0 => by
      simp only [seedRun, Option.some.injEq] at h
      subst h
      exact ⟨rfl, h0⟩
  | ℓ :: ls, s, t, h, h0 => by
      obtain ⟨s₁, h1, h2⟩ := seedRun_cons h
      obtain ⟨hseed, hother⟩ := seedStep_slot0 h1
      by_cases hs : ℓ.IsSeed
      · exact absurd (hseed hs).1 h0
      · have h0' : s₁.mr.roots 0 ≠ 0 := by rw [hother hs]; exact h0
        obtain ⟨hc, ht⟩ := seedRun_no_seed_of_filled keccak ls s₁ t h2 h0'
        refine ⟨?_, ht⟩
        cases ℓ with
        | createNewChain => exact absurd trivial hs
        | execute r => simpa [seedCount] using hc
        | mrCall call =>
          cases call with
          | seedGenesisRoot => exact absurd trivial hs
          | addNewChain _ => simpa [seedCount] using hc
          | setMigratingChainBatchNumber _ => simpa [seedCount] using hc
          | addChainBatchRoot _ _ => simpa [seedCount] using hc
        | diamondOther _ => simpa [seedCount] using hc

theorem seed_at_most_once (keccak : Keccak) :
    ∀ (s₀ : SeedSystem) (ls : List SeedLabel) (s : SeedSystem),
      seedRun keccak s₀ ls = some s → seedCount ls ≤ 1
  | _, [], _, _ => by simp [seedCount]
  | s₀, ℓ :: ls, s, h => by
      obtain ⟨s₁, h1, h2⟩ := seedRun_cons h
      obtain ⟨hseed, _⟩ := seedStep_slot0 h1
      by_cases hs : ℓ.IsSeed
      · have hc := (seedRun_no_seed_of_filled keccak ls s₁ s h2 (hseed hs).2).1
        cases ℓ with
        | createNewChain => simp [seedCount, hc]
        | mrCall call =>
          cases call with
          | seedGenesisRoot => simp [seedCount, hc]
          | _ => exact absurd hs id
        | _ => exact absurd hs id
      · have ih := seed_at_most_once keccak s₁ ls s h2
        cases ℓ with
        | createNewChain => exact absurd trivial hs
        | execute r => simpa [seedCount] using ih
        | mrCall call =>
          cases call with
          | seedGenesisRoot => exact absurd trivial hs
          | addNewChain _ => simpa [seedCount] using ih
          | setMigratingChainBatchNumber _ => simpa [seedCount] using ih
          | addChainBatchRoot _ _ => simpa [seedCount] using ih
        | diamondOther _ => simpa [seedCount] using ih

/-! ## No seeding after a real batch -/

/-- A registered chain past batch 0 stays so, and no seeding step succeeds from it. -/
theorem seedStep_past_genesis {keccak : Keccak} {s s' : SeedSystem} {ℓ : SeedLabel}
    (h : seedStep keccak s ℓ = some s') (hreg : s.mr.registered = true) (hcur : 1 ≤ s.mr.current) :
    s'.mr.registered = true ∧ 1 ≤ s'.mr.current ∧ ¬ ℓ.IsSeed := by
  cases ℓ with
  | createNewChain =>
    obtain ⟨_, _, mr₁, h1, _⟩ := seedStep_createNewChain h
    obtain ⟨hr, _⟩ := seedExec_addNewChain h1
    rw [hreg] at hr
    exact absurd hr (by decide)
  | execute r =>
    obtain ⟨d, _, h1, _⟩ := seedStep_execute h
    obtain ⟨_, _, _, _, hm⟩ := seedExec_record h1
    refine ⟨by rw [hm]; exact hreg, by rw [hm]; simp, fun hs => hs⟩
  | mrCall call =>
    obtain ⟨h1, _⟩ := seedStep_mrCall h
    cases call with
    | addNewChain start =>
      obtain ⟨hr, _⟩ := seedExec_addNewChain h1
      rw [hreg] at hr
      exact absurd hr (by decide)
    | setMigratingChainBatchNumber n =>
      obtain ⟨hle, hm⟩ := seedExec_setMigrating h1
      refine ⟨by rw [hm]; exact hreg, by rw [hm]; simp; omega, fun hs => hs⟩
    | addChainBatchRoot n r =>
      obtain ⟨_, _, _, _, hm⟩ := seedExec_record h1
      refine ⟨by rw [hm]; exact hreg, by rw [hm]; simp, fun hs => hs⟩
    | seedGenesisRoot =>
      obtain ⟨_, _, _, _, h0, _⟩ := seedExec_seed h1
      omega
  | diamondOther d' =>
    obtain ⟨_, _, _, rfl⟩ := seedStep_diamondOther h
    exact ⟨hreg, hcur, fun hs => hs⟩

/-- A step that records a batch leaves `c` registered past batch 0. -/
theorem seedStep_real_batch {keccak : Keccak} {s s' : SeedSystem} {ℓ : SeedLabel}
    (h : seedStep keccak s ℓ = some s') (hℓ : ℓ.IsRealBatch) :
    s'.mr.registered = true ∧ 1 ≤ s'.mr.current := by
  cases ℓ with
  | execute r =>
    obtain ⟨d, _, h1, _⟩ := seedStep_execute h
    obtain ⟨hr, _, _, _, hm⟩ := seedExec_record h1
    exact ⟨by rw [hm]; exact hr, by rw [hm]; simp⟩
  | mrCall call =>
    cases call with
    | addChainBatchRoot n r =>
      obtain ⟨h1, _⟩ := seedStep_mrCall h
      obtain ⟨hr, _, _, _, hm⟩ := seedExec_record h1
      exact ⟨by rw [hm]; exact hr, by rw [hm]; simp⟩
    | _ => exact absurd hℓ id
  | _ => exact absurd hℓ id

theorem seedRun_past_genesis (keccak : Keccak) :
    ∀ (ls : List SeedLabel) (s t : SeedSystem),
      seedRun keccak s ls = some t → s.mr.registered = true → 1 ≤ s.mr.current →
        ∀ ℓ' ∈ ls, ¬ ℓ'.IsSeed
  | [], _, _, _, _, _ => by simp
  | ℓ :: ls, s, t, h, hreg, hcur => by
      obtain ⟨s₁, h1, h2⟩ := seedRun_cons h
      obtain ⟨hreg', hcur', hns⟩ := seedStep_past_genesis h1 hreg hcur
      intro ℓ' hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hns
      · exact seedRun_past_genesis keccak ls s₁ t h2 hreg' hcur' ℓ' hmem

theorem no_seed_after_real_batch (keccak : Keccak) (s₀ : SeedSystem) (ls₁ : List SeedLabel)
    (ℓ : SeedLabel) (ls₂ : List SeedLabel) (s : SeedSystem)
    (h : seedRun keccak s₀ (ls₁ ++ ℓ :: ls₂) = some s) (hℓ : ℓ.IsRealBatch) :
    ∀ ℓ' ∈ ls₂, ¬ ℓ'.IsSeed := by
  rw [seedRun_append] at h
  cases h1 : seedRun keccak s₀ ls₁ with
  | none => simp [h1] at h
  | some t =>
    rw [h1, Option.bind_some] at h
    obtain ⟨t₁, h2, h3⟩ := seedRun_cons h
    obtain ⟨hreg, hcur⟩ := seedStep_real_batch h2 hℓ
    exact seedRun_past_genesis keccak ls₂ t₁ s h3 hreg hcur

/-! ## `createNewChain` -/

theorem diamondInit_slot0 (keccak : Keccak) :
    (diamondInit keccak).logsRoots 0 = genesisChainBatchRoot keccak := by
  simp [diamondInit]

theorem create_new_chain_seeds (keccak : Keccak) (s s' : SeedSystem)
    (h : seedStep keccak s .createNewChain = some s') :
    (∃ d, s'.diamond = some d ∧ d.logsRoots 0 = genesisChainBatchRoot keccak)
      ∧ s'.mr.roots 0 = genesisChainBatchRoot keccak
      ∧ s'.mr.current = 0 ∧ s'.mr.registered = true := by
  obtain ⟨_, hd, mr₁, h1, h2⟩ := seedStep_createNewChain h
  obtain ⟨_, rfl⟩ := seedExec_addNewChain h1
  obtain ⟨g, hg, _, _, _, _, hm⟩ := seedExec_seed h2
  rw [diamondInit_slot0] at hg
  cases hg
  refine ⟨⟨_, hd, diamondInit_slot0 keccak⟩, ?_, ?_, ?_⟩ <;> simp [hm]

theorem create_new_chain_succeeds_iff (keccak : Keccak) (s : SeedSystem)
    (hd : s.diamond = none) (hr : s.mr.registered = false) (h0 : s.mr.roots 0 = 0) :
    (seedStep keccak s .createNewChain).isSome ↔ genesisChainBatchRoot keccak ≠ 0 := by
  constructor
  · intro hs
    obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨_, _, mr₁, h1, h2⟩ := seedStep_createNewChain hs'
    obtain ⟨g, hg, hg0, _⟩ := seedExec_seed h2
    rw [diamondInit_slot0] at hg
    cases hg
    exact hg0
  · intro hG
    simp [seedStep, hd, seedExec, hr, h0, diamondInit_slot0, hG]

/-! ## Genesis consistency -/

/-- The invariant. -/
def GenesisInv (keccak : Keccak) (s : SeedSystem) : Prop :=
  ∀ d, s.diamond = some d →
    d.logsRoots 0 = genesisChainBatchRoot keccak ∧ s.mr.roots 0 = genesisChainBatchRoot keccak
      ∧ genesisChainBatchRoot keccak ≠ 0 ∧ s.mr.registered = true

theorem genesisInv_step {keccak : Keccak} {s s' : SeedSystem} {ℓ : SeedLabel}
    (h : seedStep keccak s ℓ = some s') (hinv : GenesisInv keccak s) : GenesisInv keccak s' := by
  intro d' hd'
  cases ℓ with
  | createNewChain =>
    obtain ⟨hl, hd, _, _, h2⟩ := seedStep_createNewChain h
    obtain ⟨_, hroot, _, hreg⟩ := create_new_chain_seeds keccak s s' h
    rw [hd] at hd'
    cases hd'
    obtain ⟨g, hg, hg0, _⟩ := seedExec_seed h2
    rw [diamondInit_slot0] at hg
    cases hg
    exact ⟨diamondInit_slot0 keccak, hroot, hg0, hreg⟩
  | execute r =>
    obtain ⟨d, hd, h1, hd2⟩ := seedStep_execute h
    obtain ⟨hl, hroot, hG, hreg⟩ := hinv d hd
    obtain ⟨_, _, _, hn, hm⟩ := seedExec_record h1
    rw [hd2] at hd'
    cases hd'
    refine ⟨?_, ?_, hG, ?_⟩
    · simp [hl]
    · rw [hm]
      simp [hroot]
    · rw [hm]; exact hreg
  | mrCall call =>
    obtain ⟨h1, hdeq⟩ := seedStep_mrCall h
    rw [hdeq] at hd'
    obtain ⟨hl, hroot, hG, hreg⟩ := hinv d' hd'
    refine ⟨hl, ?_, hG, ?_⟩
    · cases call with
      | addNewChain start =>
        obtain ⟨hr, _⟩ := seedExec_addNewChain h1
        rw [hreg] at hr
        exact absurd hr (by decide)
      | setMigratingChainBatchNumber n =>
        obtain ⟨_, hm⟩ := seedExec_setMigrating h1
        rw [hm]; exact hroot
      | addChainBatchRoot n r =>
        obtain ⟨_, _, _, hn, hm⟩ := seedExec_record h1
        rw [hm]
        simp [Function.update_of_ne (show (0 : ℕ) ≠ n from by omega), hroot]
      | seedGenesisRoot =>
        obtain ⟨_, _, _, _, _, h0, _⟩ := seedExec_seed h1
        rw [hroot] at h0
        exact absurd h0 hG
    · cases call with
      | addNewChain start =>
        obtain ⟨hr, _⟩ := seedExec_addNewChain h1
        rw [hreg] at hr
        exact absurd hr (by decide)
      | setMigratingChainBatchNumber n =>
        obtain ⟨_, hm⟩ := seedExec_setMigrating h1
        rw [hm]; exact hreg
      | addChainBatchRoot n r =>
        obtain ⟨_, _, _, _, hm⟩ := seedExec_record h1
        rw [hm]; exact hreg
      | seedGenesisRoot =>
        obtain ⟨_, _, _, _, _, _, hm⟩ := seedExec_seed h1
        rw [hm]; exact hreg
  | diamondOther d'' =>
    obtain ⟨d, hd, hl', rfl⟩ := seedStep_diamondOther h
    simp only [Option.some.injEq] at hd'
    subst hd'
    obtain ⟨hl, hroot, hG, hreg⟩ := hinv d hd
    exact ⟨by rw [hl', hl], hroot, hG, hreg⟩

theorem genesisInv_run (keccak : Keccak) :
    ∀ (ls : List SeedLabel) (s t : SeedSystem),
      seedRun keccak s ls = some t → GenesisInv keccak s → GenesisInv keccak t
  | [], s, t, h, hinv => by
      simp only [seedRun, Option.some.injEq] at h
      subst h
      exact hinv
  | ℓ :: ls, s, t, h, hinv => by
      obtain ⟨s₁, h1, h2⟩ := seedRun_cons h
      exact genesisInv_run keccak ls s₁ t h2 (genesisInv_step h1 hinv)

theorem genesis_root_stable (keccak : Keccak) (ls : List SeedLabel) (s : SeedSystem)
    (h : seedRun keccak seedFresh ls = some s) : GenesisInv keccak s :=
  genesisInv_run keccak ls seedFresh s h (fun d hd => by simp [seedFresh] at hd)

/-! ## The genesis IMT leaves -/

theorem toBytesBE_zero' : ∀ k, toBytesBE k 0 = List.replicate k 0
  | 0 => rfl
  | k + 1 => by
      rw [AttackVectors.BundleHashEncoding.toBytesBE, Nat.zero_div, toBytesBE_zero' k,
        List.replicate_succ']
      rfl

theorem imtLeafPre_sentinel : imtLeafPre ⟨0, 0, 0⟩ = sentinelLeafPre := by
  simp only [imtLeafPre, w32, Fin.val_zero, toBytesBE_zero', sentinelLeafPre,
    List.replicate_append_replicate]

theorem setup_root (keccak : Keccak) (z0 : UInt256) :
    Contracts.InteropCommitmentTree.root (node keccak) z0 (imtHashLeaf keccak)
      Contracts.InteropCommitmentTree.setup 0 = keccak sentinelLeafPre := by
  rw [← imtLeafPre_sentinel]
  rfl

theorem genesis_imt_leaves (keccak : Keccak) (z0 : UInt256) (sibs : ℕ → UInt256) (len m : ℕ)
    (x : UInt256) (hdoc : EmptyImtRootDocumented keccak)
    (hm : m = IMT_BEGIN_ROOT_LEAF_INDEX ∨ m = IMT_END_ROOT_LEAF_INDEX)
    (hacc : ImtRootHopAccepted keccak 0 0 EMPTY_IMT_ROOT EMPTY_IMT_ROOT sibs len m x) :
    x = Contracts.InteropCommitmentTree.root (node keccak) z0 (imtHashLeaf keccak)
          Contracts.InteropCommitmentTree.setup 0
      ∨ OpeningCollision keccak 0 0 EMPTY_IMT_ROOT EMPTY_IMT_ROOT sibs m x := by
  rw [setup_root, ← hdoc]
  rcases hm with rfl | rfl
  · exact (imt_root_hop_pins keccak 0 0 _ _ sibs len x).1 hacc
  · exact (imt_root_hop_pins keccak 0 0 _ _ sibs len x).2 hacc

/-! ## The witness run -/

/-- Hashes a byte string to its length: a stand-in for keccak under which the genesis root is `64`. -/
def lengthKeccak : Keccak := fun s => Nat.toUInt256 s.length

theorem lengthKeccak_genesis : genesisChainBatchRoot lengthKeccak = 64 := by
  show lengthKeccak (nodePre _ RESERVED_SUBTREE_NODE) = 64
  simp only [lengthKeccak, nodePre_length]
  rfl

theorem genesis_seed_run_witness : Properties.GenesisSeedRunWitness := by
  have hG : genesisChainBatchRoot lengthKeccak ≠ 0 := by rw [lengthKeccak_genesis]; decide
  refine ⟨lengthKeccak, 1, ⟨some ⟨Function.update (diamondInit lengthKeccak).logsRoots 1 1, 1⟩,
    ⟨true, 1, Function.update (Function.update (fun _ => 0) 0 (genesisChainBatchRoot lengthKeccak))
      1 1⟩⟩, hG, by decide, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · simp [seedRun, seedStep, seedExec, seedFresh, diamondInit, hG]
  · simp
  · simp
  · rfl
  · simp [seedStep, seedExec, diamondInit, hG]
  · rfl

/-! ## Certificates -/

theorem CreateNewChainSeedsGenesisRoot : Properties.CreateNewChainSeedsGenesisRoot :=
  create_new_chain_seeds

theorem CreateNewChainSucceedsIffGenesisNonzero :
    Properties.CreateNewChainSucceedsIffGenesisNonzero :=
  create_new_chain_succeeds_iff

theorem GenesisRootStable : Properties.GenesisRootStable := genesis_root_stable

theorem SeedAtMostOnce : Properties.SeedAtMostOnce := seed_at_most_once

theorem NoSeedAfterRealBatch : Properties.NoSeedAfterRealBatch := no_seed_after_real_batch

theorem FirstRealBatchIsOne : Properties.FirstRealBatchIsOne := by
  intro keccak s s' read0 n r h hne
  obtain ⟨_, hcur, _⟩ := (create_new_chain_seeds keccak s s' h).2
  cases hx : seedExec s'.mr read0 (.addChainBatchRoot n r) with
  | none => exact absurd hx hne
  | some m' =>
    obtain ⟨_, _, _, hn, _⟩ := seedExec_record hx
    omega

theorem GenesisImtLeavesOpenSetupRoot : Properties.GenesisImtLeavesOpenSetupRoot :=
  genesis_imt_leaves

theorem GenesisSeedRunWitness : Properties.GenesisSeedRunWitness := genesis_seed_run_witness

/-- A keccak meeting the documented `EMPTY_IMT_ROOT`: 96 zero bytes go to that literal. -/
def emptyRootKeccak : Keccak := fun s => if s = sentinelLeafPre then EMPTY_IMT_ROOT else 0

theorem emptyRootKeccak_documented : EmptyImtRootDocumented emptyRootKeccak := by
  unfold EmptyImtRootDocumented emptyRootKeccak
  simp

theorem GenesisImtLeavesWitness : Properties.GenesisImtLeavesWitness := by
  refine ⟨emptyRootKeccak, emptyRootKeccak_documented, fun z0 m hm => ⟨?_, ?_, ?_⟩⟩
  · rcases hm with rfl | rfl
    · exact ⟨rfl, by decide, honest_opening_accepted emptyRootKeccak 0 0 _ _ 2 (Or.inl (by decide))⟩
    · exact ⟨rfl, by decide, honest_opening_accepted emptyRootKeccak 0 0 _ _ 3 (Or.inl (by decide))⟩
  · rcases hm with rfl | rfl
    · exact honest_opening_no_collision emptyRootKeccak 0 0 _ _ 2 (Or.inl (by decide))
    · exact honest_opening_no_collision emptyRootKeccak 0 0 _ _ 3 (Or.inl (by decide))
  · rw [setup_root]
    exact emptyRootKeccak_documented

end Contracts.ChainBatchRootTree
