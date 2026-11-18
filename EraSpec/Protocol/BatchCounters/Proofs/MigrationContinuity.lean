import EraSpec.Protocol.BatchCounters.Properties.MigrationContinuity
import EraSpec.Protocol.BatchCounters.Proofs.MessageRootSync

/-!
# Proofs: batch counters across migration

Two one-layer lemmas carry most of the work. `hubStep_frame`: a step of another chain leaves chain
`c`'s diamond and counter alone. `hubStep_slot`: a step that is not a migration step of `c` keeps
`c`'s diamond present or absent, keeps its `away` flag, advances its executed count by exactly the
batch numbers it executes for `c` (consecutive, after the old count), and leaves an away diamond
and its counter unchanged. The two-layer results are then a case analysis over `TwoStep` and the
three phases.
-/

namespace Contracts.BatchCounters

/-! ## One layer: what a step does to one chain's slot -/

lemma execNumbers_single_ne {c c' : ChainId} {infos : List BatchInfo} (h : c' ≠ c) :
    execNumbers c [.execute c' infos] = [] := by
  simp [execNumbers, h]

lemma execNumbers_single_self (c : ChainId) (infos : List BatchInfo) :
    execNumbers c [.execute c infos] = infos.map BatchInfo.batchNumber := by
  simp [execNumbers]

/-- A step of another chain leaves chain `c`'s diamond and message-root counter alone. -/
lemma hubStep_frame {cfg : HubConfig} {h h' : Hub} {l : HubLabel} {c : ChainId}
    (hs : HubStep cfg h l h') (hc : l.chain ≠ c) :
    h'.chains c = h.chains c ∧ h'.mr.cur c = h.mr.cur c := by
  cases hs with
  | @createChain c₀ gh gr g _ _ _ _ _ _ =>
    have hx : c ≠ c₀ := fun e => hc (by simp [HubLabel.chain, e])
    exact ⟨upd_ne _ _ hx, upd_ne _ _ hx⟩
  | @registerDeployed c₀ d _ _ _ =>
    have hx : c ≠ c₀ := fun e => hc (by simp [HubLabel.chain, e])
    exact ⟨upd_ne _ _ hx, upd_ne _ _ hx⟩
  | @commit c₀ d prev new _ _ _ _ =>
    have hx : c ≠ c₀ := fun e => hc (by simp [HubLabel.chain, e])
    exact ⟨upd_ne _ _ hx, rfl⟩
  | @prove c₀ d v _ _ _ _ =>
    have hx : c ≠ c₀ := fun e => hc (by simp [HubLabel.chain, e])
    exact ⟨upd_ne _ _ hx, rfl⟩
  | @execute c₀ d infos m' _ _ hA =>
    have hx : c ≠ c₀ := fun e => hc (by simp [HubLabel.chain, e])
    obtain ⟨_, scur, _, _, _, _, _, _⟩ := appendAll_spec hA
    refine ⟨upd_ne _ _ hx, ?_⟩
    show m'.cur c = h.mr.cur c
    rw [scur, upd_ne _ _ hx]
  | @revert c₀ d n _ _ _ _ =>
    have hx : c ≠ c₀ := fun e => hc (by simp [HubLabel.chain, e])
    exact ⟨upd_ne _ _ hx, rfl⟩
  | @upgrade c₀ d t _ =>
    have hx : c ≠ c₀ := fun e => hc (by simp [HubLabel.chain, e])
    exact ⟨upd_ne _ _ hx, rfl⟩
  | @burn c₀ d _ _ _ _ _ _ =>
    have hx : c ≠ c₀ := fun e => hc (by simp [HubLabel.chain, e])
    exact ⟨upd_ne _ _ hx, rfl⟩
  | @mintExisting c₀ d bn com _ _ _ _ _ =>
    have hx : c ≠ c₀ := fun e => hc (by simp [HubLabel.chain, e])
    exact ⟨upd_ne _ _ hx, upd_ne _ _ hx⟩
  | @mintNew c₀ bn com gh gr _ _ _ _ _ _ =>
    have hx : c ≠ c₀ := fun e => hc (by simp [HubLabel.chain, e])
    exact ⟨upd_ne _ _ hx, upd_ne _ _ hx⟩
  | @confirmFailure c₀ d _ _ _ =>
    have hx : c ≠ c₀ := fun e => hc (by simp [HubLabel.chain, e])
    exact ⟨upd_ne _ _ hx, rfl⟩

/-- A label that is not a migration label is not a mint, so its mint data is consistent. -/
lemma mintConsistent_of_not_migration {l : HubLabel} (h : l.isMigration = false) :
    l.MintConsistent := by
  cases l <;> simp_all [HubLabel.isMigration, HubLabel.MintConsistent]

/-- A label of another chain executes no batch of `c`. -/
lemma execNumbers_nil_of_ne {l : HubLabel} {c : ChainId} (hc : l.chain ≠ c) :
    execNumbers c [l] = [] := by
  cases l with
  | execute c' infos =>
    have : c' ≠ c := fun e => hc (by simp [HubLabel.chain, e])
    exact execNumbers_single_ne this
  | _ => rfl

/-- **What a step that is not a migration step of `c` does to `c`'s slot.** On a layer that is
not L1, an absent diamond stays absent and its counter unchanged; a present diamond stays present
with the same `away` flag, and its executed count grows by exactly the batch numbers executed for
`c`, which follow the old count; an away diamond and its counter do not change. -/
lemma hubStep_slot {cfg : HubConfig} {h h' : Hub} {l : HubLabel} {c : ChainId}
    (hs : HubStep cfg h l h') (hnm : l.chain = c → l.isMigration = false) :
    (h.chains c = none → cfg.isL1 = false →
      h'.chains c = none ∧ h'.mr.cur c = h.mr.cur c ∧ execNumbers c [l] = []) ∧
    ∀ d, h.chains c = some d → ∃ d', h'.chains c = some d' ∧ d'.away = d.away ∧
      d'.executed = d.executed + (execNumbers c [l]).length ∧
      execNumbers c [l] = List.range' (d.executed + 1) (execNumbers c [l]).length ∧
      (d.away = true → d' = d ∧ h'.mr.cur c = h.mr.cur c ∧ execNumbers c [l] = []) := by
  by_cases hc : l.chain = c
  · have hm := hnm hc
    cases hs with
    | @createChain c₀ gh gr g hL1 hnone _ _ _ _ =>
      simp only [HubLabel.chain] at hc; subst hc
      refine ⟨fun _ h1 => absurd (hL1.symm.trans h1) (by decide), fun d hd => ?_⟩
      rw [hnone] at hd; cases hd
    | @registerDeployed c₀ d₀ hL1 hnone _ =>
      simp only [HubLabel.chain] at hc; subst hc
      refine ⟨fun _ h1 => absurd (hL1.symm.trans h1) (by decide), fun d hd => ?_⟩
      rw [hnone] at hd; cases hd
    | @commit c₀ d₀ prev new hc₀ haway _ _ =>
      simp only [HubLabel.chain] at hc; subst hc
      refine ⟨fun hn => absurd (hc₀.symm.trans hn) (by simp), fun d hd => ?_⟩
      rw [hc₀] at hd; cases hd
      exact ⟨_, upd_same _ _ _, rfl, by simp [execNumbers, commitEffect], by simp [execNumbers],
        fun ha => by rw [haway] at ha; cases ha⟩
    | @prove c₀ d₀ v hc₀ haway _ _ =>
      simp only [HubLabel.chain] at hc; subst hc
      refine ⟨fun hn => absurd (hc₀.symm.trans hn) (by simp), fun d hd => ?_⟩
      rw [hc₀] at hd; cases hd
      exact ⟨_, upd_same _ _ _, rfl, by simp [execNumbers], by simp [execNumbers],
        fun ha => by rw [haway] at ha; cases ha⟩
    | @execute c₀ d₀ infos m' hc₀ hg hA =>
      simp only [HubLabel.chain] at hc; subst hc
      refine ⟨fun hn => absurd (hc₀.symm.trans hn) (by simp), fun d hd => ?_⟩
      rw [hc₀] at hd; cases hd
      obtain ⟨_, haway, hnums, _, _⟩ := hg
      rw [execNumbers_single_self]
      refine ⟨_, upd_same _ _ _, rfl, by simp [executeEffect], by rw [hnums]; simp, ?_⟩
      intro ha; rw [haway] at ha; cases ha
    | @revert c₀ d₀ n hc₀ haway _ _ =>
      simp only [HubLabel.chain] at hc; subst hc
      refine ⟨fun hn => absurd (hc₀.symm.trans hn) (by simp), fun d hd => ?_⟩
      rw [hc₀] at hd; cases hd
      exact ⟨_, upd_same _ _ _, rfl, by simp [execNumbers, revertEffect], by simp [execNumbers],
        fun ha => by rw [haway] at ha; cases ha⟩
    | @upgrade c₀ d₀ t hc₀ =>
      simp only [HubLabel.chain] at hc; subst hc
      refine ⟨fun hn => absurd (hc₀.symm.trans hn) (by simp), fun d hd => ?_⟩
      rw [hc₀] at hd; cases hd
      refine ⟨_, upd_same _ _ _, ?_, ?_, by simp [execNumbers], fun ha => ?_⟩
      · unfold upgradeEffect; split <;> rfl
      · simp only [execNumbers, List.length_nil, add_zero]; unfold upgradeEffect; split <;> rfl
      · refine ⟨?_, rfl, by simp [execNumbers]⟩
        unfold upgradeEffect; simp [ha]
    | burn => simp [HubLabel.isMigration] at hm
    | mintExisting => simp [HubLabel.isMigration] at hm
    | mintNew => simp [HubLabel.isMigration] at hm
    | confirmFailure => simp [HubLabel.isMigration] at hm
  · obtain ⟨hch, hcur⟩ := hubStep_frame hs hc
    have hnum := execNumbers_nil_of_ne hc
    refine ⟨fun hn _ => ⟨by rw [hch, hn], hcur, hnum⟩, fun d hd => ?_⟩
    rw [hnum]
    exact ⟨d, by rw [hch, hd], rfl, by simp, by simp, fun _ => ⟨rfl, hcur, rfl⟩⟩

/-! ## Stored batch hashes written by a mint -/

lemma writeHashes_below (f : ℕ → Word) (base : ℕ) (l : List Word) (n : ℕ) (hn : n < base) :
    writeHashes f base l n = f n := by
  induction l generalizing base with
  | nil => rfl
  | cons x xs ih =>
    simp only [writeHashes]
    rw [upd_ne _ _ (by omega)]
    exact ih (base + 1) (by omega)

/-- With every committed batch executed, the commitment carries one stored hash: the last
executed batch's. -/
lemma prepare_batchHashes_of_eq {d : Diamond} (h : d.committed = d.executed) :
    (prepare d).batchHashes = [d.batchHash d.executed] := by
  simp [prepare, h]

/-- `prepareChainCommitment`'s checks give the shape `forwardedBridgeMint` checks. -/
lemma prepare_mintShape {d : Diamond} (h1 : d.executed ≤ d.verified) (h2 : d.verified ≤ d.committed) :
    MintShape (prepare d) :=
  ⟨h1, h2, by simp [prepare]⟩

lemma diamond_away_true_eq {d : Diamond} (h : d.away = true) : { d with away := true } = d := by
  cases d; simp_all

/-! ## Mint data on one layer -/

theorem BurnDataConsistent : Properties.BurnDataConsistent := by
  intro cfg h h' c bn com hs hsync
  cases hs with
  | @burn _ d _ hc _ hce hev hvc =>
    have hcur := hsync d hc
    refine ⟨hcur, by simp [prepare, hce], by simp [prepare]; omega, prepare_mintShape hev hvc,
      d, hc, prepare_batchHashes_of_eq hce⟩

theorem ConsistentMintNeverLowersExecuted : Properties.ConsistentMintNeverLowersExecuted := by
  intro cfg h h' c bn com d hs hbn hsync hc
  cases hs with
  | @mintExisting _ d₀ _ _ _ hc₀ hle _ _ =>
    rw [hc] at hc₀; cases hc₀
    have hcur := hsync d hc
    refine ⟨mintApply d com, upd_same _ _ _, by simp [mintApply]; omega, fun n hn => ?_⟩
    exact writeHashes_below _ _ _ _ (by omega)

theorem StaleMintRewritesHistory : Properties.StaleMintRewritesHistory := by
  have hc : wAwayHub.chains 1 = some wAwayDiamond := rfl
  have hshape : MintShape wStaleCom := ⟨by decide, by decide, rfl⟩
  have hs : HubStep latentL1 wAwayHub (.mintExisting 1 10 wStaleCom) _ :=
    HubStep.mintExisting rfl hc (by decide) hshape rfl
  refine ⟨⟨fun x => ?_, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ h => absurd rfl h⟩,
    fun d hd => by rw [hc] at hd; cases hd; rfl, hshape, _, hs, mintApply wAwayDiamond wStaleCom,
    rfl, rfl, by decide, by decide, rfl, fun infos h'' hex => ?_⟩
  · by_cases hx : x = 1
    · subst hx; simp [wAwayHub]
    · simp [wAwayHub, upd, hx]
  · exact DriftBlocksExecute _ _ _ (mintApply wAwayDiamond wStaleCom) rfl (by decide) infos h'' hex

/-! ## Two layers: phases and the chain's executed count -/

lemma idle_of_away {h : Hub} {c : ChainId} {d : Diamond} (hd : h.chains c = some d)
    (ha : d.away = true) : Idle h c := by
  intro e he; rw [hd] at he; cases he; exact ha

lemma idle_of_none {h : Hub} {c : ChainId} (hd : h.chains c = none) : Idle h c := by
  intro e he; rw [hd] at he; cases he

lemma copyExecuted_of_some {h : Hub} {c : ChainId} {d : Diamond} (hd : h.chains c = some d) :
    copyExecuted h c = d.executed := by
  simp [copyExecuted, hd]

lemma copyExecuted_of_none {h : Hub} {c : ChainId} (hd : h.chains c = none) :
    copyExecuted h c = 0 := by
  simp [copyExecuted, hd]

lemma chainExecuted_of_flight {P : TwoConfig} {s : TwoHubs} {f : Flight}
    (hf : s.flight = some f) : chainExecuted P s = f.com.executed := by
  simp [chainExecuted, hf]

lemma chainExecuted_of_l1 {P : TwoConfig} {s : TwoHubs} {d : Diamond} (hf : s.flight = none)
    (hd : s.l1.chains P.C = some d) (ha : d.away = false) : chainExecuted P s = d.executed := by
  simp [chainExecuted, hf, hd, ha]

lemma chainExecuted_of_sl {P : TwoConfig} {s : TwoHubs} {d : Diamond} (hf : s.flight = none)
    (hd : s.l1.chains P.C = some d) (ha : d.away = true) :
    chainExecuted P s = copyExecuted s.sl P.C := by
  simp [chainExecuted, hf, hd, ha]

lemma chainExecuted_congr {P : TwoConfig} {s s' : TwoHubs} (hf : s'.flight = s.flight)
    (h1 : s'.l1.chains P.C = s.l1.chains P.C) (h2 : s'.sl.chains P.C = s.sl.chains P.C) :
    chainExecuted P s' = chainExecuted P s := by
  simp only [chainExecuted, copyExecuted, hf, h1, h2]

/-- The three phases of a state satisfying `TwoInv`, with the chain's executed count in each. -/
lemma twoInv_phase {P : TwoConfig} {s : TwoHubs} (hI : TwoInv P s) :
    (s.flight = none ∧ ∃ d, s.l1.chains P.C = some d ∧ d.away = false ∧ Idle s.sl P.C ∧
      chainExecuted P s = d.executed) ∨
    (s.flight = none ∧ ∃ d e, s.l1.chains P.C = some d ∧ d.away = true ∧
      s.sl.chains P.C = some e ∧ e.away = false ∧ chainExecuted P s = e.executed) ∨
    (∃ f, s.flight = some f ∧ Idle s.l1 P.C ∧ Idle s.sl P.C ∧
      chainExecuted P s = f.com.executed) := by
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.1 hI.l1Present
  rcases hI.phase with ⟨hf, ⟨d₁, hd₁, ha⟩, hi⟩ | ⟨hf, hi, ⟨e, he, ha⟩⟩ | ⟨hf, hi1, hi2⟩
  · exact Or.inl ⟨hf, d₁, hd₁, ha, hi, chainExecuted_of_l1 hf hd₁ ha⟩
  · refine Or.inr (Or.inl ⟨hf, d, e, hd, hi d hd, he, ha, ?_⟩)
    rw [chainExecuted_of_sl hf hd (hi d hd), copyExecuted_of_some he]
  · obtain ⟨f, hf'⟩ := Option.ne_none_iff_exists'.1 hf
    exact Or.inr (Or.inr ⟨f, hf', hi1, hi2, chainExecuted_of_flight hf'⟩)

/-- The data in flight is consistent and has the shape the mint checks. -/
lemma twoInv_flight_consistent {P : TwoConfig} {s : TwoHubs} {f : Flight} (hI : TwoInv P s)
    (hf : s.flight = some f) : f.bn = f.com.executed ∧ MintShape f.com := by
  obtain ⟨d, _, hcom, hbn, hce, hve⟩ := hI.snapshot f hf
  rw [hcom]
  exact ⟨hbn, prepare_mintShape (by omega) (by omega)⟩

/-- A state whose layers satisfy the layer invariant and agree with a `TwoInv` state on the data
in flight and on `C`'s diamonds and counters satisfies `TwoInv`. -/
lemma twoInv_of_same_slots {P : TwoConfig} {s s' : TwoHubs} (hI : TwoInv P s)
    (h1 : HubInv s'.l1) (h2 : HubInv s'.sl) (hf : s'.flight = s.flight)
    (hc1 : s'.l1.chains P.C = s.l1.chains P.C) (hc2 : s'.sl.chains P.C = s.sl.chains P.C)
    (hu1 : s'.l1.mr.cur P.C = s.l1.mr.cur P.C) (hu2 : s'.sl.mr.cur P.C = s.sl.mr.cur P.C) :
    TwoInv P s' := by
  refine ⟨h1, h2, fun d hd => ?_, fun d hd => ?_, by rw [hc1]; exact hI.l1Present, ?_, ?_, ?_⟩
  · rw [hc1] at hd; rw [hu1]; exact hI.l1Sync d hd
  · rw [hc2] at hd; rw [hu2]; exact hI.slSync d hd
  · unfold Phase Settles Idle; rw [hf, hc1, hc2]; exact hI.phase
  · intro f hfs
    rw [hf] at hfs
    obtain ⟨d, hd, hrest⟩ := hI.snapshot f hfs
    refine ⟨d, ?_, hrest⟩
    rcases f with ⟨dir, bn, com⟩
    cases dir
    · simp only [Flight.source] at hd ⊢; rw [hc1]; exact hd
    · simp only [Flight.source] at hd ⊢; rw [hc2]; exact hd
  · rw [chainExecuted_congr hf hc1 hc2]
    simp only [copyExecuted, hc1, hc2]
    exact hI.behind

/-! ## Two layers: one step -/

/-- What one step does, for the two-layer results: the invariant, the batch numbers it executes
for `C` (the next ones after the chain's executed count), and neither copy going back. -/
def TwoStepFacts (P : TwoConfig) (s s' : TwoHubs) (l : TwoLabel) : Prop :=
  TwoInv P s' ∧
    twoExecNumbers P.C [l] = List.range' (chainExecuted P s + 1) (twoExecNumbers P.C [l]).length ∧
    chainExecuted P s' = chainExecuted P s + (twoExecNumbers P.C [l]).length ∧
    copyExecuted s.l1 P.C ≤ copyExecuted s'.l1 P.C ∧ copyExecuted s.sl P.C ≤ copyExecuted s'.sl P.C

lemma twoExecNumbers_l1 (C : ChainId) (l : HubLabel) :
    twoExecNumbers C [.l1 l] = execNumbers C [l] := by simp [twoExecNumbers]

lemma twoExecNumbers_sl (C : ChainId) (l : HubLabel) :
    twoExecNumbers C [.sl l] = execNumbers C [l] := by simp [twoExecNumbers]

/-- A step on L1 that is not a migration step of `C`. -/
lemma twoStepFacts_l1 {P : TwoConfig} {s : TwoHubs} {l : HubLabel} {h' : Hub} (hI : TwoInv P s)
    (hnm : l.chain = P.C → l.isMigration = false) (hs : HubStep P.l1 s.l1 l h') :
    TwoStepFacts P s { s with l1 := h' } (.l1 l) := by
  have hInv := HubStepPreservesInv _ _ _ _ hI.l1Inv hs
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.1 hI.l1Present
  obtain ⟨d', hd', haway, hexec, hnums, hidle⟩ := (hubStep_slot hs hnm).2 d hd
  have hsync : Synced h' P.C := by
    by_cases hc : l.chain = P.C
    · exact SyncedStaysSynced _ _ _ _ _ hs (mintConsistent_of_not_migration (hnm hc)) hI.l1Sync
    · intro e he
      obtain ⟨hch, hcur⟩ := hubStep_frame hs hc
      rw [hch] at he; rw [hcur]; exact hI.l1Sync e he
  unfold TwoStepFacts
  rw [twoExecNumbers_l1]
  cases hda : d.away with
  | true =>
    obtain ⟨rfl, hcur, hnil⟩ := hidle hda
    have hsame : TwoInv P { s with l1 := h' } :=
      twoInv_of_same_slots hI hInv hI.slInv rfl (by rw [hd', hd]) rfl hcur rfl
    refine ⟨hsame, by rw [hnil]; rfl, ?_, by simp [copyExecuted, hd, hd'], le_rfl⟩
    rw [hnil, List.length_nil, add_zero]
    exact chainExecuted_congr rfl (by rw [hd', hd]) rfl
  | false =>
    -- `C` settles on L1: phase 1.
    rcases twoInv_phase hI with ⟨hf, d₁, hd₁, ha₁, hi, hce⟩ | ⟨_, d₁, _, hd₁, ha₁, _⟩ |
      ⟨f, hf, hi1, _, _⟩
    · rw [hd] at hd₁; cases hd₁
      have hce' : chainExecuted P { s with l1 := h' } = d'.executed :=
        chainExecuted_of_l1 (P := P) (s := { s with l1 := h' }) hf hd' (by rw [haway, hda])
      have hbeh := hI.behind.2
      rw [hce] at hbeh
      rw [hce]
      refine ⟨⟨hInv, hI.slInv, hsync, hI.slSync, by rw [hd']; simp,
        Or.inl ⟨hf, ⟨d', hd', by rw [haway, hda]⟩, hi⟩, fun f hf' => ?_, ?_⟩,
        hnums, by rw [hce', hexec], ?_, le_rfl⟩
      · exact absurd (hf.symm.trans hf') (by simp)
      · rw [hce', copyExecuted_of_some hd']
        exact ⟨le_rfl, le_trans hbeh (by rw [hexec]; omega)⟩
      · rw [copyExecuted_of_some hd, copyExecuted_of_some hd', hexec]; omega
    · rw [hd] at hd₁; cases hd₁; rw [hda] at ha₁; cases ha₁
    · have := hi1 d hd; rw [hda] at this; cases this

/-- A step on the settlement layer that is not a migration step of `C`. -/
lemma twoStepFacts_sl {P : TwoConfig} {s : TwoHubs} {l : HubLabel} {h' : Hub} (hI : TwoInv P s)
    (hnm : l.chain = P.C → l.isMigration = false) (hs : HubStep P.sl s.sl l h') :
    TwoStepFacts P s { s with sl := h' } (.sl l) := by
  have hInv := HubStepPreservesInv _ _ _ _ hI.slInv hs
  have hsync : Synced h' P.C := by
    by_cases hc : l.chain = P.C
    · exact SyncedStaysSynced _ _ _ _ _ hs (mintConsistent_of_not_migration (hnm hc)) hI.slSync
    · intro e he
      obtain ⟨hch, hcur⟩ := hubStep_frame hs hc
      rw [hch] at he; rw [hcur]; exact hI.slSync e he
  unfold TwoStepFacts
  rw [twoExecNumbers_sl]
  -- An idle settlement-layer copy (absent or away) does not change.
  have hidleCase : Idle s.sl P.C →
      h'.chains P.C = s.sl.chains P.C ∧ h'.mr.cur P.C = s.sl.mr.cur P.C ∧ execNumbers P.C [l] = [] := by
    intro hi
    cases he : s.sl.chains P.C with
    | none =>
      obtain ⟨h1, h2, h3⟩ := (hubStep_slot hs hnm).1 he P.slNotL1
      exact ⟨h1, h2, h3⟩
    | some e =>
      obtain ⟨e', he', _, _, _, hidle⟩ := (hubStep_slot hs hnm).2 e he
      obtain ⟨rfl, hcur, hnil⟩ := hidle (hi e he)
      exact ⟨he', hcur, hnil⟩
  have idleFacts : Idle s.sl P.C → TwoStepFacts P s { s with sl := h' } (.sl l) := by
    intro hi
    obtain ⟨hch, hcur, hnil⟩ := hidleCase hi
    unfold TwoStepFacts
    rw [twoExecNumbers_sl, hnil]
    refine ⟨twoInv_of_same_slots hI hI.l1Inv hInv rfl rfl hch rfl hcur, rfl, ?_, le_rfl, ?_⟩
    · rw [List.length_nil, add_zero]; exact chainExecuted_congr rfl rfl hch
    · show copyExecuted s.sl P.C ≤ copyExecuted h' P.C
      simp only [copyExecuted, hch]; exact le_rfl
  rcases twoInv_phase hI with ⟨_, _, _, _, hi, _⟩ | ⟨hf, d, e, hd, hda, he, hea, hce⟩ |
    ⟨_, _, _, hi, _⟩
  · have := idleFacts hi; unfold TwoStepFacts at this; rw [twoExecNumbers_sl] at this; exact this
  · -- `C` settles on the settlement layer: phase 2.
    obtain ⟨e', he', haway, hexec, hnums, _⟩ := (hubStep_slot hs hnm).2 e he
    have hce' : chainExecuted P { s with sl := h' } = e'.executed := by
      rw [chainExecuted_of_sl (P := P) (s := { s with sl := h' }) hf hd hda]
      exact copyExecuted_of_some he'
    have hbeh := hI.behind.1
    rw [hce] at hbeh
    rw [hce]
    refine ⟨⟨hI.l1Inv, hInv, hI.l1Sync, hsync, hI.l1Present,
      Or.inr (Or.inl ⟨hf, idle_of_away hd hda, ⟨e', he', by rw [haway, hea]⟩⟩), fun f hf' => ?_, ?_⟩,
      hnums, by rw [hce', hexec], le_rfl, ?_⟩
    · exact absurd (hf.symm.trans hf') (by simp)
    · rw [hce', copyExecuted_of_some he']
      exact ⟨le_trans hbeh (by rw [hexec]; omega), le_rfl⟩
    · show copyExecuted s.sl P.C ≤ copyExecuted h' P.C
      rw [copyExecuted_of_some he, copyExecuted_of_some he', hexec]; omega
  · have := idleFacts hi; unfold TwoStepFacts at this; rw [twoExecNumbers_sl] at this; exact this

/-! ## Two layers: the migration steps on one layer -/

lemma hubStep_burn_slot {cfg : HubConfig} {h h' : Hub} {c : ChainId} {bn : ℕ} {com : Commitment}
    (hs : HubStep cfg h (.burn c bn com) h') :
    ∃ d, h.chains c = some d ∧ d.away = false ∧ d.committed = d.executed ∧
      d.executed ≤ d.verified ∧ d.verified ≤ d.committed ∧ bn = h.mr.cur c ∧ com = prepare d ∧
      h'.chains c = some { d with away := true } ∧ h'.mr.cur c = h.mr.cur c ∧
      cfg.migrationsEnabled = true := by
  cases hs with
  | @burn _ d hme hc haway hce hev hvc =>
    exact ⟨d, hc, haway, hce, hev, hvc, rfl, rfl, upd_same _ _ _, rfl, hme⟩

lemma hubStep_mintExisting_slot {cfg : HubConfig} {h h' : Hub} {c : ChainId} {bn : ℕ}
    {com : Commitment} (hs : HubStep cfg h (.mintExisting c bn com) h') :
    ∃ d, h.chains c = some d ∧ h.mr.cur c ≤ bn ∧ MintShape com ∧ d.away = true ∧
      h'.chains c = some (mintApply d com) ∧ h'.mr.cur c = bn ∧ cfg.migrationsEnabled = true := by
  cases hs with
  | @mintExisting _ d _ _ hme hc hle hshape haway =>
    exact ⟨d, hc, hle, hshape, haway, upd_same _ _ _, upd_same _ _ _, hme⟩

lemma hubStep_mintNew_slot {cfg : HubConfig} {h h' : Hub} {c : ChainId} {bn : ℕ}
    {com : Commitment} {gh gr : Word} (hs : HubStep cfg h (.mintNew c bn com gh gr) h') :
    h.chains c = none ∧ h.mr.reg c = false ∧ cfg.isL1 = false ∧ gh ≠ 0 ∧ MintShape com ∧
      h'.chains c = some (mintApply (initDiamond gh gr 0) com) ∧ h'.mr.cur c = bn ∧
      cfg.migrationsEnabled = true := by
  cases hs with
  | @mintNew _ _ _ _ _ hme hL1 hnone hreg hgh hshape =>
    exact ⟨hnone, hreg, hL1, hgh, hshape, upd_same _ _ _, upd_same _ _ _, hme⟩

lemma hubStep_confirmFailure_slot {cfg : HubConfig} {h h' : Hub} {c : ChainId}
    (hs : HubStep cfg h (.confirmFailure c) h') :
    ∃ d, h.chains c = some d ∧ d.away = true ∧ h'.chains c = some { d with away := false } ∧
      h'.mr.cur c = h.mr.cur c ∧ cfg.isL1 = true := by
  cases hs with
  | @confirmFailure _ d hL1 hc haway => exact ⟨d, hc, haway, upd_same _ _ _, rfl, hL1⟩

/-- **Every step, from a state satisfying `TwoInv`.** -/
lemma twoStepFacts {P : TwoConfig} {s s' : TwoHubs} {l : TwoLabel} (hI : TwoInv P s)
    (hs : TwoStep P s l s') : TwoStepFacts P s s' l := by
  cases hs with
  | l1 hnm hstep => exact twoStepFacts_l1 hI hnm hstep
  | sl hnm hstep => exact twoStepFacts_sl hI hnm hstep
  | @departL1 bn com h' hf hstep =>
    have hInv := HubStepPreservesInv _ _ _ _ hI.l1Inv hstep
    have hsync := SyncedStaysSynced _ _ _ _ P.C hstep trivial hI.l1Sync
    obtain ⟨d, hc, haway, hce, hev, hvc, rfl, rfl, hc', _, _⟩ := hubStep_burn_slot hstep
    have hcur := hI.l1Sync d hc
    rcases twoInv_phase hI with ⟨_, d₁, hd₁, _, hi, hcex⟩ | ⟨_, d₁, _, hd₁, ha₁, _⟩ |
      ⟨f, hf', _, _, _⟩
    · rw [hc] at hd₁; cases hd₁
      have hbeh := hI.behind.2
      rw [hcex] at hbeh
      have hce' : chainExecuted P { s with l1 := h', flight := some ⟨.toSL, s.l1.mr.cur P.C,
          prepare d⟩ } = d.executed := by simp [chainExecuted, prepare]
      refine ⟨⟨hInv, hI.slInv, hsync, hI.slSync, by rw [hc']; simp, Or.inr (Or.inr ⟨by simp,
        idle_of_away hc' rfl, hi⟩), fun f hf => ?_, ?_⟩, by simp [twoExecNumbers], ?_, ?_, le_rfl⟩
      · simp only [Option.some.injEq] at hf; subst hf
        exact ⟨{ d with away := true }, hc', rfl, hcur, hce, by show d.verified = d.executed; omega⟩
      · rw [hce', copyExecuted_of_some hc']; exact ⟨le_rfl, hbeh⟩
      · rw [hce', hcex]; simp [twoExecNumbers]
      · show copyExecuted s.l1 P.C ≤ copyExecuted h' P.C
        rw [copyExecuted_of_some hc, copyExecuted_of_some hc']
    · rw [hc] at hd₁; cases hd₁; rw [haway] at ha₁; cases ha₁
    · rw [hf] at hf'; cases hf'
  | @arriveSLNew f gh gr h' hf hdir hstep =>
    have hInv := HubStepPreservesInv _ _ _ _ hI.slInv hstep
    obtain ⟨hcons, _⟩ := twoInv_flight_consistent hI hf
    have hsync := SyncedStaysSynced _ _ _ _ P.C hstep hcons hI.slSync
    obtain ⟨hnone, _, _, _, _, hc', _, _⟩ := hubStep_mintNew_slot hstep
    rcases twoInv_phase hI with ⟨hf', _⟩ | ⟨hf', _⟩ | ⟨f', hf', hi1, _, hcex⟩
    · rw [hf] at hf'; cases hf'
    · rw [hf] at hf'; cases hf'
    · rw [hf] at hf'; cases hf'
      obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.1 hI.l1Present
      have hce' : chainExecuted P { s with sl := h', flight := none } = f.com.executed := by
        rw [chainExecuted_of_sl (P := P) (s := { s with sl := h', flight := none }) rfl hd
          (hi1 d hd)]
        rw [copyExecuted_of_some hc']; rfl
      have hbeh := hI.behind.1
      rw [hcex] at hbeh
      refine ⟨⟨hI.l1Inv, hInv, hI.l1Sync, hsync, hI.l1Present,
        Or.inr (Or.inl ⟨rfl, hi1, ⟨_, hc', rfl⟩⟩), (fun _ h => by cases h), ?_⟩,
        by simp [twoExecNumbers], ?_, le_rfl, ?_⟩
      · rw [hce', copyExecuted_of_some hc']; exact ⟨hbeh, le_rfl⟩
      · rw [hce', hcex]; simp [twoExecNumbers]
      · rw [copyExecuted_of_none hnone]; exact Nat.zero_le _
  | @arriveSLExisting f h' hf hdir hstep =>
    have hInv := HubStepPreservesInv _ _ _ _ hI.slInv hstep
    obtain ⟨hcons, _⟩ := twoInv_flight_consistent hI hf
    have hsync := SyncedStaysSynced _ _ _ _ P.C hstep hcons hI.slSync
    obtain ⟨e, he, _, _, _, hc', _, _⟩ := hubStep_mintExisting_slot hstep
    rcases twoInv_phase hI with ⟨hf', _⟩ | ⟨hf', _⟩ | ⟨f', hf', hi1, _, hcex⟩
    · rw [hf] at hf'; cases hf'
    · rw [hf] at hf'; cases hf'
    · rw [hf] at hf'; cases hf'
      obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.1 hI.l1Present
      have hce' : chainExecuted P { s with sl := h', flight := none } = f.com.executed := by
        rw [chainExecuted_of_sl (P := P) (s := { s with sl := h', flight := none }) rfl hd
          (hi1 d hd)]
        rw [copyExecuted_of_some hc']; rfl
      have hbeh := hI.behind
      rw [hcex] at hbeh
      refine ⟨⟨hI.l1Inv, hInv, hI.l1Sync, hsync, hI.l1Present,
        Or.inr (Or.inl ⟨rfl, hi1, ⟨_, hc', rfl⟩⟩), (fun _ h => by cases h), ?_⟩,
        by simp [twoExecNumbers], ?_, le_rfl, ?_⟩
      · rw [hce', copyExecuted_of_some hc']; exact ⟨hbeh.1, le_rfl⟩
      · rw [hce', hcex]; simp [twoExecNumbers]
      · show copyExecuted s.sl P.C ≤ copyExecuted h' P.C
        rw [copyExecuted_of_some hc']
        exact hbeh.2
  | @failL1 f h' hf hdir hstep =>
    have hInv := HubStepPreservesInv _ _ _ _ hI.l1Inv hstep
    have hsync := SyncedStaysSynced _ _ _ _ P.C hstep trivial hI.l1Sync
    obtain ⟨d₀, hd₀, hcom, _⟩ := hI.snapshot f hf
    simp only [Flight.source, hdir] at hd₀
    obtain ⟨d, hc, _, hc', _, _⟩ := hubStep_confirmFailure_slot hstep
    have hdd : d = d₀ := Option.some.inj (hc.symm.trans hd₀)
    subst hdd
    rcases twoInv_phase hI with ⟨hf', _⟩ | ⟨hf', _⟩ | ⟨f', hf', _, hi2, hcex⟩
    · rw [hf] at hf'; cases hf'
    · rw [hf] at hf'; cases hf'
    · rw [hf] at hf'; cases hf'
      have hce' : chainExecuted P { s with l1 := h', flight := none } = d.executed := by
        rw [chainExecuted_of_l1 (P := P) (s := { s with l1 := h', flight := none }) rfl hc' rfl]
      have hfe : f.com.executed = d.executed := by rw [hcom]; rfl
      have hbeh := hI.behind.2
      rw [hcex, hfe] at hbeh
      refine ⟨⟨hInv, hI.slInv, hsync, hI.slSync, by rw [hc']; simp,
        Or.inl ⟨rfl, ⟨_, hc', rfl⟩, hi2⟩, (fun _ h => by cases h), ?_⟩,
        by simp [twoExecNumbers], ?_, ?_, le_rfl⟩
      · rw [hce', copyExecuted_of_some hc']; exact ⟨le_rfl, hbeh⟩
      · rw [hce', hcex, hfe]; simp [twoExecNumbers]
      · show copyExecuted s.l1 P.C ≤ copyExecuted h' P.C
        rw [copyExecuted_of_some hc', copyExecuted_of_some hc]
  | @departSL bn com h' hf hstep =>
    have hInv := HubStepPreservesInv _ _ _ _ hI.slInv hstep
    have hsync := SyncedStaysSynced _ _ _ _ P.C hstep trivial hI.slSync
    obtain ⟨e, he, heaway, hce, hev, hvc, rfl, rfl, hc', _, _⟩ := hubStep_burn_slot hstep
    have hcur := hI.slSync e he
    rcases twoInv_phase hI with ⟨_, d₁, hd₁, _, hi, _⟩ | ⟨_, d, e₁, hd, hda, he₁, _, hcex⟩ |
      ⟨f, hf', _, _, _⟩
    · have := hi e he; rw [heaway] at this; cases this
    · rw [he] at he₁; cases he₁
      have hbeh := hI.behind.1
      rw [hcex] at hbeh
      have hce' : chainExecuted P { s with sl := h', flight := some ⟨.toL1, s.sl.mr.cur P.C,
          prepare e⟩ } = e.executed := by simp [chainExecuted, prepare]
      refine ⟨⟨hI.l1Inv, hInv, hI.l1Sync, hsync, hI.l1Present, Or.inr (Or.inr ⟨by simp,
        idle_of_away hd hda, idle_of_away hc' rfl⟩), fun f hf => ?_, ?_⟩,
        by simp [twoExecNumbers], ?_, le_rfl, ?_⟩
      · simp only [Option.some.injEq] at hf; subst hf
        exact ⟨{ e with away := true }, hc', rfl, hcur, hce, by show e.verified = e.executed; omega⟩
      · rw [hce', copyExecuted_of_some hc']; exact ⟨hbeh, le_rfl⟩
      · rw [hce', hcex]; simp [twoExecNumbers]
      · show copyExecuted s.sl P.C ≤ copyExecuted h' P.C
        rw [copyExecuted_of_some hc', copyExecuted_of_some he]
    · rw [hf] at hf'; cases hf'
  | @arriveL1 f h' hf hdir hstep =>
    have hInv := HubStepPreservesInv _ _ _ _ hI.l1Inv hstep
    obtain ⟨hcons, _⟩ := twoInv_flight_consistent hI hf
    have hsync := SyncedStaysSynced _ _ _ _ P.C hstep hcons hI.l1Sync
    obtain ⟨d, hc, _, _, _, hc', _, _⟩ := hubStep_mintExisting_slot hstep
    rcases twoInv_phase hI with ⟨hf', _⟩ | ⟨hf', _⟩ | ⟨f', hf', _, hi2, hcex⟩
    · rw [hf] at hf'; cases hf'
    · rw [hf] at hf'; cases hf'
    · rw [hf] at hf'; cases hf'
      have hce' : chainExecuted P { s with l1 := h', flight := none } = f.com.executed :=
        chainExecuted_of_l1 (P := P) (s := { s with l1 := h', flight := none }) rfl hc' rfl
      have hbeh := hI.behind
      rw [hcex] at hbeh
      refine ⟨⟨hInv, hI.slInv, hsync, hI.slSync, by rw [hc']; simp,
        Or.inl ⟨rfl, ⟨_, hc', rfl⟩, hi2⟩, (fun _ h => by cases h), ?_⟩,
        by simp [twoExecNumbers], ?_, ?_, le_rfl⟩
      · rw [hce', copyExecuted_of_some hc']; exact ⟨le_rfl, hbeh.2⟩
      · rw [hce', hcex]; simp [twoExecNumbers]
      · show copyExecuted s.l1 P.C ≤ copyExecuted h' P.C
        rw [copyExecuted_of_some hc']
        exact hbeh.1

/-! ## The two-layer invariant -/

theorem TwoInvInit : Properties.TwoInvInit := by
  intro P s h1 h2 hsync hset hnone hf
  obtain ⟨d, hd, ha⟩ := hset
  refine ⟨h1, h2, hsync, (fun e he => by rw [hnone] at he; cases he), (by rw [hd]; simp),
    Or.inl ⟨hf, ⟨d, hd, ha⟩, idle_of_none hnone⟩, (fun f hf' => by rw [hf] at hf'; cases hf'), ?_⟩
  rw [chainExecuted_of_l1 hf hd ha, copyExecuted_of_some hd, copyExecuted_of_none hnone]
  exact ⟨le_rfl, Nat.zero_le _⟩

theorem TwoStepPreservesInv : Properties.TwoStepPreservesInv :=
  fun _ _ _ _ hI hs => (twoStepFacts hI hs).1

theorem TwoRunKeepsInv : Properties.TwoRunKeepsInv := by
  intro P s s' ls hI hr
  induction hr with
  | nil => exact hI
  | cons hs _ ih => exact ih (TwoStepPreservesInv _ _ _ _ hI hs)

lemma not_settles_and_idle {h : Hub} {c : ChainId} (hs : Settles h c) (hi : Idle h c) : False := by
  obtain ⟨d, hd, ha⟩ := hs
  have := hi d hd
  rw [ha] at this; cases this

theorem ExactlyOneCopySettles : Properties.ExactlyOneCopySettles := by
  intro P s s' ls hI hr
  have hI' := TwoRunKeepsInv _ _ _ _ hI hr
  refine ⟨fun h1 h2 => ?_, ⟨fun hf => ?_, fun h => ?_⟩⟩
  · rcases hI'.phase with ⟨_, _, hi⟩ | ⟨_, hi, _⟩ | ⟨_, hi, _⟩
    · exact not_settles_and_idle h2 hi
    · exact not_settles_and_idle h1 hi
    · exact not_settles_and_idle h1 hi
  · rcases hI'.phase with ⟨_, h, _⟩ | ⟨_, _, h⟩ | ⟨hne, _, _⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd hf hne
  · rcases hI'.phase with ⟨hf, _, _⟩ | ⟨hf, _, _⟩ | ⟨_, hi1, hi2⟩
    · exact hf
    · exact hf
    · rcases h with h | h
      · exact (not_settles_and_idle h hi1).elim
      · exact (not_settles_and_idle h hi2).elim

/-- A pipeline step needs the chain's diamond to settle on its layer. -/
lemma hubStep_pipeline_settles {cfg : HubConfig} {h h' : Hub} {l : HubLabel}
    (hs : HubStep cfg h l h') (hp : l.isPipeline = true) : Settles h l.chain := by
  cases hs with
  | commit hc haway _ _ => exact ⟨_, hc, haway⟩
  | prove hc haway _ _ => exact ⟨_, hc, haway⟩
  | execute hc hg _ => exact ⟨_, hc, hg.2.1⟩
  | revert hc haway _ _ => exact ⟨_, hc, haway⟩
  | _ => simp [HubLabel.isPipeline] at hp

theorem PipelineOnlyOnSettlingCopy : Properties.PipelineOnlyOnSettlingCopy := by
  intro P s s' l hI hc hp
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · cases hs with
    | l1 _ hstep =>
      have hset := hubStep_pipeline_settles hstep hp
      rw [hc] at hset
      rcases hI.phase with ⟨hf, _, hi⟩ | ⟨_, hi, _⟩ | ⟨_, hi, _⟩
      · exact ⟨hset, hf, hi⟩
      · exact (not_settles_and_idle hset hi).elim
      · exact (not_settles_and_idle hset hi).elim
  · cases hs with
    | sl _ hstep =>
      have hset := hubStep_pipeline_settles hstep hp
      rw [hc] at hset
      rcases hI.phase with ⟨_, _, hi⟩ | ⟨hf, hi, _⟩ | ⟨_, _, hi⟩
      · exact (not_settles_and_idle hset hi).elim
      · exact ⟨hset, hf, hi⟩
      · exact (not_settles_and_idle hset hi).elim

/-- On a layer, a step that is not a migration step of `c` leaves an away diamond of `c` and its
counter unchanged. -/
lemma hubStep_keeps_away {cfg : HubConfig} {h h' : Hub} {l : HubLabel} {c : ChainId}
    {d : Diamond} (hs : HubStep cfg h l h') (hnm : l.chain = c → l.isMigration = false)
    (hd : h.chains c = some d) (ha : d.away = true) :
    ∃ d', h'.chains c = some d' ∧ { d' with away := true } = d ∧ h'.mr.cur c = h.mr.cur c := by
  obtain ⟨d', hd', _, _, _, hidle⟩ := (hubStep_slot hs hnm).2 d hd
  obtain ⟨rfl, hcur, _⟩ := hidle ha
  exact ⟨d', hd', diamond_away_true_eq ha, hcur⟩

theorem IdleCopyChangesOnlyByMint : Properties.IdleCopyChangesOnlyByMint := by
  intro P s s' l _ hs
  refine ⟨fun hne d hd ha => ?_, fun hne1 hne2 d hd ha => ?_⟩
  · cases hs with
    | l1 hnm hstep => exact hubStep_keeps_away hstep hnm hd ha
    | sl => exact ⟨d, hd, diamond_away_true_eq ha, rfl⟩
    | departL1 _ hstep =>
      obtain ⟨d₀, hd₀, ha₀, _⟩ := hubStep_burn_slot hstep
      rw [hd] at hd₀; cases hd₀; rw [ha] at ha₀; cases ha₀
    | arriveSLNew => exact ⟨d, hd, diamond_away_true_eq ha, rfl⟩
    | arriveSLExisting => exact ⟨d, hd, diamond_away_true_eq ha, rfl⟩
    | failL1 _ _ hstep =>
      obtain ⟨d₀, hd₀, _, hc', hcur, _⟩ := hubStep_confirmFailure_slot hstep
      rw [hd] at hd₀; cases hd₀
      refine ⟨_, hc', ?_, hcur⟩
      cases d; simp_all
    | departSL => exact ⟨d, hd, diamond_away_true_eq ha, rfl⟩
    | arriveL1 => exact absurd rfl hne
  · cases hs with
    | l1 => exact ⟨d, hd, diamond_away_true_eq ha, rfl⟩
    | sl hnm hstep => exact hubStep_keeps_away hstep hnm hd ha
    | departL1 => exact ⟨d, hd, diamond_away_true_eq ha, rfl⟩
    | arriveSLNew => exact absurd rfl (hne2 _ _)
    | arriveSLExisting => exact absurd rfl hne1
    | failL1 => exact ⟨d, hd, diamond_away_true_eq ha, rfl⟩
    | departSL _ hstep =>
      obtain ⟨d₀, hd₀, ha₀, _⟩ := hubStep_burn_slot hstep
      rw [hd] at hd₀; cases hd₀; rw [ha] at ha₀; cases ha₀
    | arriveL1 => exact ⟨d, hd, diamond_away_true_eq ha, rfl⟩

/-! ## Continuity -/

/-- The mint's diamond: counters, stored hashes and upgrade fields of a commitment taken with
every committed batch executed. -/
lemma mintApply_prepare {d src : Diamond} (hce : src.committed = src.executed)
    (hve : src.verified = src.executed) :
    (mintApply d (prepare src)).executed = src.executed ∧
      (mintApply d (prepare src)).committed = src.executed ∧
      (mintApply d (prepare src)).verified = src.executed ∧
      (mintApply d (prepare src)).batchHash src.executed = src.batchHash src.executed ∧
      (∀ n, n ≠ src.executed → (mintApply d (prepare src)).batchHash n = d.batchHash n) ∧
      (mintApply d (prepare src)).logsRoot = d.logsRoot ∧
      (mintApply d (prepare src)).upgradeTxHash = src.upgradeTxHash ∧
      (mintApply d (prepare src)).upgradeBatch = src.upgradeBatch ∧
      (mintApply d (prepare src)).away = false := by
  have hb : (mintApply d (prepare src)).batchHash = upd d.batchHash src.executed
      (src.batchHash src.executed) := by
    simp only [mintApply]
    rw [prepare_batchHashes_of_eq hce]
    rfl
  refine ⟨rfl, by simp [mintApply, prepare, hce], by simp [mintApply, prepare, hve],
    by rw [hb]; exact upd_same _ _ _, fun n hn => by rw [hb]; exact upd_ne _ _ hn, rfl, rfl, rfl,
    rfl⟩

theorem ArrivalOnL1CopiesSource : Properties.ArrivalOnL1CopiesSource := by
  intro P s s' hI hs
  cases hs with
  | @arriveL1 f h' hf hdir hstep =>
    obtain ⟨src, hsrc, hcom, hbn, hce, hve⟩ := hI.snapshot f hf
    simp only [Flight.source, hdir] at hsrc
    obtain ⟨d, hc, hle, _, _, hc', hcur', _⟩ := hubStep_mintExisting_slot hstep
    rw [hcom] at hc'
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := mintApply_prepare (d := d) hce hve
    refine ⟨src, d, _, hsrc, hc, hc', e1, e2, e3, e4, e5, e6, e7, e8, e9, ?_, ?_⟩
    · show h'.mr.cur P.C = src.executed
      rw [hcur', hbn]
    · have := hI.l1Sync d hc
      omega

theorem ArrivalOnSLCopiesSource : Properties.ArrivalOnSLCopiesSource := by
  intro P s s' l hI hs hl
  rcases hl with rfl | ⟨gh, gr, rfl⟩
  · cases hs with
    | @arriveSLExisting f h' hf hdir hstep =>
      obtain ⟨src, hsrc, hcom, hbn, hce, hve⟩ := hI.snapshot f hf
      simp only [Flight.source, hdir] at hsrc
      obtain ⟨e, he, hle, _, _, hc', hcur', _⟩ := hubStep_mintExisting_slot hstep
      rw [hcom] at hc'
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := mintApply_prepare (d := e) hce hve
      refine ⟨src, _, hsrc, hc', e1, e2, e3, e4, e7, e8, e9, ?_, fun d hd => ?_⟩
      · show h'.mr.cur P.C = src.executed
        rw [hcur', hbn]
      · rw [he] at hd; cases hd
        have := hI.slSync e he
        exact ⟨by omega, e5, e6⟩
  · cases hs with
    | @arriveSLNew f _ _ h' hf hdir hstep =>
      obtain ⟨src, hsrc, hcom, hbn, hce, hve⟩ := hI.snapshot f hf
      simp only [Flight.source, hdir] at hsrc
      obtain ⟨hnone, _, _, _, _, hc', hcur', _⟩ := hubStep_mintNew_slot hstep
      rw [hcom] at hc'
      obtain ⟨e1, e2, e3, e4, _, _, e7, e8, e9⟩ :=
        mintApply_prepare (d := initDiamond gh gr 0) hce hve
      refine ⟨src, _, hsrc, hc', e1, e2, e3, e4, e7, e8, e9, ?_, fun d hd => ?_⟩
      · show h'.mr.cur P.C = src.executed
        rw [hcur', hbn]
      · rw [hnone] at hd; cases hd

lemma twoExecNumbers_cons (C : ChainId) (l : TwoLabel) (ls : List TwoLabel) :
    twoExecNumbers C (l :: ls) = twoExecNumbers C [l] ++ twoExecNumbers C ls := by
  cases l <;> simp [twoExecNumbers]

theorem ExecutedLogContiguous : Properties.ExecutedLogContiguous := by
  intro P s s' ls hI hr
  induction hr with
  | nil => simp [twoExecNumbers]
  | @cons s₀ s₁ s₂ l ls' hs _ ih =>
    obtain ⟨hI₁, hnums, hce, _, _⟩ := twoStepFacts hI hs
    obtain ⟨ihnums, ihce⟩ := ih hI₁
    rw [twoExecNumbers_cons]
    constructor
    · rw [ihnums, hnums, hce, List.length_append, List.length_range', List.length_range']
      have := List.range'_append (s := chainExecuted P s₀ + 1)
        (m := (twoExecNumbers P.C [l]).length) (n := (twoExecNumbers P.C ls').length) (step := 1)
      simp only [one_mul] at this
      rw [← this]
      congr 2
      omega
    · rw [ihce, hce, List.length_append]; omega

theorem CopiesNeverGoBack : Properties.CopiesNeverGoBack := by
  intro P s s' ls hI hr
  induction hr with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | cons hs _ ih =>
    obtain ⟨hI₁, _, _, h1, h2⟩ := twoStepFacts hI hs
    obtain ⟨ih1, ih2⟩ := ih hI₁
    exact ⟨le_trans h1 ih1, le_trans h2 ih2⟩

theorem HonestArrivalsAccepted : Properties.HonestArrivalsAccepted := by
  intro P s f hI hf
  obtain ⟨hcons, hshape⟩ := twoInv_flight_consistent hI hf
  have hcex := chainExecuted_of_flight (P := P) hf
  have hne : s.flight ≠ none := by rw [hf]; simp
  have hidle : Idle s.l1 P.C ∧ Idle s.sl P.C := by
    rcases hI.phase with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h1, h2⟩
    · exact absurd h hne
    · exact absurd h hne
    · exact ⟨h1, h2⟩
  refine ⟨fun hdir hme => ?_, fun hdir hme hsome => ?_, fun hdir hme hnone gh gr hgh => ?_⟩
  · obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.1 hI.l1Present
    have hle : s.l1.mr.cur P.C ≤ f.bn := by
      have := hI.behind.1
      rw [copyExecuted_of_some hd, hcex] at this
      rw [hI.l1Sync d hd, hcons]; exact this
    exact ⟨_, TwoStep.arriveL1 hf hdir (HubStep.mintExisting hme hd hle hshape (hidle.1 d hd))⟩
  · obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.1 hsome
    have hle : s.sl.mr.cur P.C ≤ f.bn := by
      have := hI.behind.2
      rw [copyExecuted_of_some he, hcex] at this
      rw [hI.slSync e he, hcons]; exact this
    exact ⟨_, TwoStep.arriveSLExisting hf hdir
      (HubStep.mintExisting hme he hle hshape (hidle.2 e he))⟩
  · have hreg : s.sl.mr.reg P.C = false := by
      cases h : s.sl.mr.reg P.C with
      | false => rfl
      | true => exact absurd hnone ((hI.slInv.regIff P.C).1 h)
    exact ⟨_, TwoStep.arriveSLNew hf hdir
      (HubStep.mintNew hme P.slNotL1 hnone hreg hgh hshape)⟩

/-! ## Witness -/

/-! The witness diamonds of chain `1`: `wRtA*` on L1, `wRtB*` on the settlement layer. -/

/-- L1, after the start: batch 1 committed, proved and executed. -/
def wRtA0 : Diamond :=
  executeEffect { commitEffect wHash (initDiamond 13 12 0) (wInfo 1) with verified := 1 } [wInfo 1]
/-- L1, departed. -/
def wRtA1 : Diamond := { wRtA0 with away := true }
/-- The settlement layer, arrived on a fresh diamond. -/
def wRtB0 : Diamond := mintApply (initDiamond 13 12 0) (prepare wRtA0)
/-- The settlement layer, batches 2 and 3 committed. -/
def wRtB2 : Diamond := commitEffect wHash (commitEffect wHash wRtB0 (wInfo 2)) (wInfo 3)
/-- The settlement layer, batches 2 and 3 proved and executed. -/
def wRtB4 : Diamond := executeEffect { wRtB2 with verified := 3 } [wInfo 2, wInfo 3]
/-- The settlement layer, departed. -/
def wRtB5 : Diamond := { wRtB4 with away := true }
/-- L1, arrived back. -/
def wRtA2 : Diamond := mintApply wRtA1 (prepare wRtB4)
/-- L1, batch 4 committed and proved. -/
def wRtA4 : Diamond := { commitEffect wHash wRtA2 (wInfo 4) with verified := 4 }
/-- L1, batch 4 executed. -/
def wRtA5 : Diamond := executeEffect wRtA4 [wInfo 4]

/-- The L1 start of the round trip, from the empty layer. -/
lemma wRt_l1Start : ∃ h₀, HubRun latentL1 emptyHub
    [.createChain 1 13 12 0, .commit 1 wInfo0 (wInfo 1), .prove 1 1, .execute 1 [wInfo 1]] h₀ ∧
    h₀.chains 1 = some wRtA0 ∧ h₀.mr.cur 1 = 1 :=
  ⟨_, HubRun.cons (cfg := latentL1) (h := emptyHub)
    (HubStep.createChain (c := 1) (gh := 13) (gr := 12) (g := 0) rfl rfl rfl (by decide)
      (by decide) rfl)
    (HubRun.cons (HubStep.commit (c := 1) (prev := wInfo0) (new := wInfo 1) rfl rfl rfl rfl)
    (HubRun.cons (HubStep.prove (c := 1) (v := 1) rfl rfl (by decide) (by decide))
    (HubRun.cons (HubStep.execute (c := 1) (infos := [wInfo 1]) rfl
        ⟨by simp, rfl, rfl, fun b hb => by
          simp only [List.mem_singleton] at hb
          subst hb; rfl, by decide⟩ rfl)
    HubRun.nil))), rfl, rfl⟩

/-- An execute on a layer satisfying the invariant, with the counters in sync. -/
lemma hubStep_execute_exists {cfg : HubConfig} {h : Hub} {c : ChainId} {d : Diamond}
    {infos : List BatchInfo} (hI : HubInv h) (hs : Synced h c) (hc : h.chains c = some d)
    (hg : ExecGuard cfg.hash d infos) (hnz : ∀ b ∈ infos, b.logsRoot ≠ 0) :
    ∃ h', HubStep cfg h (.execute c infos) h' ∧ h'.chains c = some (executeEffect d infos) ∧
      h'.mr.cur c = d.executed + infos.length := by
  obtain ⟨⟨m', hA, hcur⟩, _⟩ := ExecuteNeverRevertsInMessageRoot cfg h c d infos hI hs hc hg hnz
  exact ⟨_, HubStep.execute hc hg hA, upd_same _ _ _, hcur⟩

/-- The round trip, with the facts both witnesses read off its end. -/
lemma wRt_roundTrip : ∃ (ls₀ : List HubLabel) (L0 : Hub) (ls : List TwoLabel) (L5 S6 : Hub),
    HubRun latentL1 emptyHub ls₀ L0 ∧ execNumbers 1 ls₀ = [1] ∧
    TwoInv wTwo ⟨L0, emptyHub, none⟩ ∧ TwoRun wTwo ⟨L0, emptyHub, none⟩ ls ⟨L5, S6, none⟩ ∧
    TwoLabel.departL1 ∈ ls ∧ (∃ gh gr, TwoLabel.arriveSLNew gh gr ∈ ls) ∧
    TwoLabel.departSL ∈ ls ∧ TwoLabel.arriveL1 ∈ ls ∧ twoExecNumbers 1 ls = [2, 3, 4] ∧
    TwoInv wTwo ⟨L5, S6, none⟩ ∧ L5.chains 1 = some wRtA5 ∧ L5.mr.cur 1 = 4 ∧
    S6.chains 1 = some wRtB5 ∧ S6.mr.cur 1 = 3 := by
  obtain ⟨L0, hr₀, hcL0, hcurL0⟩ := wRt_l1Start
  have hS0 : Synced L0 1 := fun d hd => by rw [hcL0] at hd; cases hd; rw [hcurL0]; rfl
  have hI0 : TwoInv wTwo ⟨L0, emptyHub, none⟩ :=
    TwoInvInit wTwo _ (ReachableHubsSatisfyInv _ _ _ hr₀).1 EmptyHubInv hS0 ⟨_, hcL0, rfl⟩ rfl rfl
  -- 1. `C` leaves L1.
  obtain ⟨L1, hb1, hcL1, hcurL1⟩ : ∃ L1, HubStep latentL1 L0
      (.burn 1 (L0.mr.cur 1) (prepare wRtA0)) L1 ∧ L1.chains 1 = some wRtA1 ∧ L1.mr.cur 1 = 1 :=
    ⟨_, HubStep.burn rfl hcL0 rfl rfl (by decide) (by decide), rfl, hcurL0⟩
  have st1 : TwoStep wTwo ⟨L0, emptyHub, none⟩ .departL1
      ⟨L1, emptyHub, some ⟨.toSL, L0.mr.cur 1, prepare wRtA0⟩⟩ := TwoStep.departL1 rfl hb1
  have hI1 := TwoStepPreservesInv _ _ _ _ hI0 st1
  -- 2. It arrives on the settlement layer, which has no diamond for it.
  obtain ⟨S1, hm2, hcS1, hcurS1⟩ : ∃ S1, HubStep latentSL emptyHub
      (.mintNew 1 (L0.mr.cur 1) (prepare wRtA0) 13 12) S1 ∧ S1.chains 1 = some wRtB0 ∧
      S1.mr.cur 1 = 1 :=
    ⟨_, HubStep.mintNew rfl rfl rfl rfl (by decide) (prepare_mintShape (by decide) (by decide)),
      rfl, (upd_same emptyHub.mr.cur 1 (L0.mr.cur 1)).trans hcurL0⟩
  have st2 : TwoStep wTwo ⟨L1, emptyHub, some ⟨.toSL, L0.mr.cur 1, prepare wRtA0⟩⟩
      (.arriveSLNew 13 12) ⟨L1, S1, none⟩ := TwoStep.arriveSLNew rfl rfl hm2
  have hI2 := TwoStepPreservesInv _ _ _ _ hI1 st2
  -- 3–5. Batches 2 and 3 are committed and proved there.
  obtain ⟨S2, hc3, hcS2, hmS2⟩ : ∃ S2, HubStep latentSL S1 (.commit 1 (wInfo 1) (wInfo 2)) S2 ∧
      S2.chains 1 = some (commitEffect wHash wRtB0 (wInfo 2)) ∧ S2.mr = S1.mr :=
    ⟨_, HubStep.commit hcS1 rfl rfl rfl, rfl, rfl⟩
  have st3 : TwoStep wTwo ⟨L1, S1, none⟩ (.sl (.commit 1 (wInfo 1) (wInfo 2))) ⟨L1, S2, none⟩ :=
    TwoStep.sl (fun _ => rfl) hc3
  have hI3 := TwoStepPreservesInv _ _ _ _ hI2 st3
  obtain ⟨S3, hc4, hcS3, hmS3⟩ : ∃ S3, HubStep latentSL S2 (.commit 1 (wInfo 2) (wInfo 3)) S3 ∧
      S3.chains 1 = some wRtB2 ∧ S3.mr = S1.mr :=
    ⟨_, HubStep.commit hcS2 rfl rfl rfl, rfl, hmS2⟩
  have st4 : TwoStep wTwo ⟨L1, S2, none⟩ (.sl (.commit 1 (wInfo 2) (wInfo 3))) ⟨L1, S3, none⟩ :=
    TwoStep.sl (fun _ => rfl) hc4
  have hI4 := TwoStepPreservesInv _ _ _ _ hI3 st4
  obtain ⟨S4, hp5, hcS4, hmS4⟩ : ∃ S4, HubStep latentSL S3 (.prove 1 3) S4 ∧
      S4.chains 1 = some { wRtB2 with verified := 3 } ∧ S4.mr = S1.mr :=
    ⟨_, HubStep.prove hcS3 rfl (by decide) (by decide), rfl, hmS3⟩
  have st5 : TwoStep wTwo ⟨L1, S3, none⟩ (.sl (.prove 1 3)) ⟨L1, S4, none⟩ :=
    TwoStep.sl (fun _ => rfl) hp5
  have hI5 := TwoStepPreservesInv _ _ _ _ hI4 st5
  -- 6. Both are executed there in one call.
  have hg6 : ExecGuard latentSL.hash { wRtB2 with verified := 3 } [wInfo 2, wInfo 3] :=
    ⟨by simp, rfl, rfl, fun b hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> rfl, by decide⟩
  obtain ⟨S5, he6, hcS5, hcurS5⟩ := hubStep_execute_exists (c := 1) hI5.slInv hI5.slSync hcS4 hg6
    (by decide)
  have hcurS5' : S5.mr.cur 1 = 3 := by rw [hcurS5]; decide
  have st6 : TwoStep wTwo ⟨L1, S4, none⟩ (.sl (.execute 1 [wInfo 2, wInfo 3])) ⟨L1, S5, none⟩ :=
    TwoStep.sl (fun _ => rfl) he6
  have hI6 := TwoStepPreservesInv _ _ _ _ hI5 st6
  -- 7. `C` leaves the settlement layer.
  obtain ⟨S6, hb7, hcS6, hcurS6⟩ : ∃ S6, HubStep latentSL S5
      (.burn 1 (S5.mr.cur 1) (prepare wRtB4)) S6 ∧ S6.chains 1 = some wRtB5 ∧ S6.mr.cur 1 = 3 :=
    ⟨_, HubStep.burn rfl hcS5 rfl rfl (by decide) (by decide), rfl, hcurS5'⟩
  have st7 : TwoStep wTwo ⟨L1, S5, none⟩ .departSL
      ⟨L1, S6, some ⟨.toL1, S5.mr.cur 1, prepare wRtB4⟩⟩ := TwoStep.departSL rfl hb7
  have hI7 := TwoStepPreservesInv _ _ _ _ hI6 st7
  -- 8. It arrives back on L1.
  obtain ⟨L2, hm8, hcL2, hcurL2⟩ : ∃ L2, HubStep latentL1 L1
      (.mintExisting 1 (S5.mr.cur 1) (prepare wRtB4)) L2 ∧ L2.chains 1 = some wRtA2 ∧
      L2.mr.cur 1 = 3 :=
    ⟨_, HubStep.mintExisting rfl hcL1 (by rw [hcurL1, hcurS5']; decide)
      (prepare_mintShape (by decide) (by decide)) rfl, rfl,
      (upd_same L1.mr.cur 1 (S5.mr.cur 1)).trans hcurS5'⟩
  have st8 : TwoStep wTwo ⟨L1, S6, some ⟨.toL1, S5.mr.cur 1, prepare wRtB4⟩⟩ .arriveL1
      ⟨L2, S6, none⟩ := TwoStep.arriveL1 rfl rfl hm8
  have hI8 := TwoStepPreservesInv _ _ _ _ hI7 st8
  -- 9–11. Batch 4 is committed, proved and executed on L1.
  obtain ⟨L3, hc9, hcL3, hmL3⟩ : ∃ L3, HubStep latentL1 L2 (.commit 1 (wInfo 3) (wInfo 4)) L3 ∧
      L3.chains 1 = some (commitEffect wHash wRtA2 (wInfo 4)) ∧ L3.mr = L2.mr :=
    ⟨_, HubStep.commit hcL2 rfl (by decide) rfl, rfl, rfl⟩
  have st9 : TwoStep wTwo ⟨L2, S6, none⟩ (.l1 (.commit 1 (wInfo 3) (wInfo 4))) ⟨L3, S6, none⟩ :=
    TwoStep.l1 (fun _ => rfl) hc9
  have hI9 := TwoStepPreservesInv _ _ _ _ hI8 st9
  obtain ⟨L4, hp10, hcL4, hmL4⟩ : ∃ L4, HubStep latentL1 L3 (.prove 1 4) L4 ∧
      L4.chains 1 = some wRtA4 ∧ L4.mr = L2.mr :=
    ⟨_, HubStep.prove hcL3 rfl (by decide) (by decide), rfl, hmL3⟩
  have st10 : TwoStep wTwo ⟨L3, S6, none⟩ (.l1 (.prove 1 4)) ⟨L4, S6, none⟩ :=
    TwoStep.l1 (fun _ => rfl) hp10
  have hI10 := TwoStepPreservesInv _ _ _ _ hI9 st10
  obtain ⟨L5, he11, hcL5, hcurL5⟩ := hubStep_execute_exists (cfg := latentL1) (c := 1) hI10.l1Inv
    hI10.l1Sync hcL4 (execGuard_single (b := wInfo 4) rfl rfl (by decide) (by decide)) (by decide)
  have st11 : TwoStep wTwo ⟨L4, S6, none⟩ (.l1 (.execute 1 [wInfo 4])) ⟨L5, S6, none⟩ :=
    TwoStep.l1 (fun _ => rfl) he11
  have hI11 := TwoStepPreservesInv _ _ _ _ hI10 st11
  have hr := TwoRun.cons st1 (TwoRun.cons st2 (TwoRun.cons st3 (TwoRun.cons st4
    (TwoRun.cons st5 (TwoRun.cons st6 (TwoRun.cons st7 (TwoRun.cons st8 (TwoRun.cons st9
    (TwoRun.cons st10 (TwoRun.cons st11 TwoRun.nil))))))))))
  exact ⟨_, _, _, _, _, hr₀, rfl, hI0, hr, by simp, ⟨13, 12, by simp⟩, by simp, by simp, rfl, hI11,
    hcL5, by rw [hcurL5]; decide, hcS6, hcurS6⟩

theorem RoundTripWitness : Properties.RoundTripWitness := by
  obtain ⟨ls₀, L0, ls, L5, S6, hr₀, hn₀, hI0, hr, hm1, hm2, hm3, hm4, hn, hI, hcL5, hcurL5, hcS6,
    hcurS6⟩ := wRt_roundTrip
  exact ⟨ls₀, L0, ls, ⟨L5, S6, none⟩, hr₀, hn₀, hI0, hr, hm1, hm2, hm3, hm4, hn, hI, rfl,
    ⟨_, hcL5, by decide, by decide⟩, ⟨_, hcS6, by decide, rfl⟩, hcurL5, hcurS6⟩

/-- L1, departed again. -/
def wRtA6 : Diamond := { wRtA5 with away := true }
/-- L1, the departure having failed. -/
def wRtA7 : Diamond := { wRtA6 with away := false }
/-- L1, departed a third time. -/
def wRtA8 : Diamond := { wRtA7 with away := true }
/-- The settlement layer, arrived on its existing diamond. -/
def wRtB6 : Diamond := mintApply wRtB5 (prepare wRtA7)
/-- The settlement layer, batch 5 committed and proved. -/
def wRtB7 : Diamond := { commitEffect wHash wRtB6 (wInfo 5) with verified := 5 }

theorem ReentryWitness : Properties.ReentryWitness := by
  obtain ⟨ls₀, L0, ls, L5, S6, hr₀, _, _, hr, _, _, _, _, hn, hI1, hcL5, hcurL5, hcS6,
    hcurS6⟩ := wRt_roundTrip
  -- 12. `C` departs from L1 again.
  obtain ⟨L6, hb12, hcL6, hcurL6⟩ : ∃ L6, HubStep latentL1 L5
      (.burn 1 (L5.mr.cur 1) (prepare wRtA5)) L6 ∧ L6.chains 1 = some wRtA6 ∧ L6.mr.cur 1 = 4 :=
    ⟨_, HubStep.burn rfl hcL5 rfl rfl (by decide) (by decide), rfl, hcurL5⟩
  have st12 : TwoStep wTwo ⟨L5, S6, none⟩ .departL1
      ⟨L6, S6, some ⟨.toSL, L5.mr.cur 1, prepare wRtA5⟩⟩ := TwoStep.departL1 rfl hb12
  have hI2 := TwoStepPreservesInv _ _ _ _ hI1 st12
  -- 13. The departure fails.
  obtain ⟨L7, hf13, hcL7, hcurL7⟩ : ∃ L7, HubStep latentL1 L6 (.confirmFailure 1) L7 ∧
      L7.chains 1 = some wRtA7 ∧ L7.mr.cur 1 = 4 :=
    ⟨_, HubStep.confirmFailure rfl hcL6 rfl, rfl, hcurL6⟩
  have st13 : TwoStep wTwo ⟨L6, S6, some ⟨.toSL, L5.mr.cur 1, prepare wRtA5⟩⟩ .failL1
      ⟨L7, S6, none⟩ := TwoStep.failL1 rfl rfl hf13
  have hI3 := TwoStepPreservesInv _ _ _ _ hI2 st13
  -- 14. `C` departs from L1 once more.
  obtain ⟨L8, hb14, hcL8, _⟩ : ∃ L8, HubStep latentL1 L7
      (.burn 1 (L7.mr.cur 1) (prepare wRtA7)) L8 ∧ L8.chains 1 = some wRtA8 ∧ L8.mr.cur 1 = 4 :=
    ⟨_, HubStep.burn rfl hcL7 rfl rfl (by decide) (by decide), rfl, hcurL7⟩
  have st14 : TwoStep wTwo ⟨L7, S6, none⟩ .departL1
      ⟨L8, S6, some ⟨.toSL, L7.mr.cur 1, prepare wRtA7⟩⟩ := TwoStep.departL1 rfl hb14
  have hI4 := TwoStepPreservesInv _ _ _ _ hI3 st14
  -- 15. It arrives on the settlement layer's existing diamond.
  obtain ⟨S7, hm15, hcS7, hcurS7⟩ : ∃ S7, HubStep latentSL S6
      (.mintExisting 1 (L7.mr.cur 1) (prepare wRtA7)) S7 ∧ S7.chains 1 = some wRtB6 ∧
      S7.mr.cur 1 = 4 :=
    ⟨_, HubStep.mintExisting rfl hcS6 (by rw [hcurS6, hcurL7]; decide)
      (prepare_mintShape (by decide) (by decide)) rfl, rfl,
      (upd_same S6.mr.cur 1 (L7.mr.cur 1)).trans hcurL7⟩
  have st15 : TwoStep wTwo ⟨L8, S6, some ⟨.toSL, L7.mr.cur 1, prepare wRtA7⟩⟩ .arriveSLExisting
      ⟨L8, S7, none⟩ := TwoStep.arriveSLExisting rfl rfl hm15
  have hI5 := TwoStepPreservesInv _ _ _ _ hI4 st15
  -- 16–18. Batch 5 is committed, proved and executed there.
  obtain ⟨S8, hc16, hcS8, _⟩ : ∃ S8, HubStep latentSL S7 (.commit 1 (wInfo 4) (wInfo 5)) S8 ∧
      S8.chains 1 = some (commitEffect wHash wRtB6 (wInfo 5)) ∧ S8.mr = S7.mr :=
    ⟨_, HubStep.commit hcS7 rfl (by decide) rfl, rfl, rfl⟩
  have st16 : TwoStep wTwo ⟨L8, S7, none⟩ (.sl (.commit 1 (wInfo 4) (wInfo 5))) ⟨L8, S8, none⟩ :=
    TwoStep.sl (fun _ => rfl) hc16
  have hI6 := TwoStepPreservesInv _ _ _ _ hI5 st16
  obtain ⟨S9, hp17, hcS9, _⟩ : ∃ S9, HubStep latentSL S8 (.prove 1 5) S9 ∧
      S9.chains 1 = some wRtB7 ∧ S9.mr = S7.mr :=
    ⟨_, HubStep.prove hcS8 rfl (by decide) (by decide), rfl, by assumption⟩
  have st17 : TwoStep wTwo ⟨L8, S8, none⟩ (.sl (.prove 1 5)) ⟨L8, S9, none⟩ :=
    TwoStep.sl (fun _ => rfl) hp17
  have hI7 := TwoStepPreservesInv _ _ _ _ hI6 st17
  obtain ⟨S10, he18, hcS10, hcurS10⟩ := hubStep_execute_exists (cfg := latentSL) (c := 1)
    hI7.slInv hI7.slSync hcS9 (execGuard_single (b := wInfo 5) rfl rfl (by decide) (by decide))
    (by decide)
  have st18 : TwoStep wTwo ⟨L8, S9, none⟩ (.sl (.execute 1 [wInfo 5])) ⟨L8, S10, none⟩ :=
    TwoStep.sl (fun _ => rfl) he18
  have hI8 := TwoStepPreservesInv _ _ _ _ hI7 st18
  refine ⟨ls₀, L0, ls, _, _, _, _, _, _, hr₀, hr, hn, st12, hI2, ⟨_, hcL6, rfl, by decide⟩,
    ⟨_, hcS6, rfl, by decide⟩, st13, ⟨_, hcL7, rfl, by decide⟩, st14, hI4,
    ⟨_, rfl, rfl, show (prepare wRtA7).executed = 4 by decide⟩, ⟨_, hcS6, rfl, by decide⟩, st15, ⟨_, hcS7, rfl, by decide⟩, hcurS7,
    TwoRun.cons st16 (TwoRun.cons st17 (TwoRun.cons st18 TwoRun.nil)), hI8,
    ⟨_, hcS10, by decide, rfl⟩, ?_⟩
  rw [hcurS10]; decide

end Contracts.BatchCounters
