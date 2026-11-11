import EraSpec.Protocol.InteropAtomicity.Properties.OncePerLegAtHead
import EraSpec.Protocol.InteropAtomicity.Proofs.OncePerLeg
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.HintSearchAtHead

/-!
# Proofs: once per leg, at head

The bridge is one step lemma.  On a valid tree, a head append is the pin's append with the
landing index as the hint (`pin_append_of_atHead`), and a pin append is a head append
(`atHead_append_of_pin`).  The written state is the same either way.  Along a run the trees
stay valid (`steps_tree_reaches`), so the head's runs are the pin's runs
(`stepsAtHead_steps`, `steps_stepsAtHead`).  Every restated headline is then the pin's
theorem applied through that equivalence.  Where a statement names the insert itself, the
head's insert is translated by the same step lemma.  The witnesses build the honest
six-append run whose tree is `chainTree 6`, and lift `HonestInsertSucceedsAtHead` to an
`append`.
-/

namespace Contracts.AppendPath

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund

/-! ## One append -/

/-- On a valid tree, a head insert passes the pin's checks from its landing index. -/
lemma pin_insert_of_atHead {T : Tree} (hV : Valid T) {v : UInt256} {hint low : ℕ}
    (h : InsertChecksAtHead T v hint low) : InsertSucceeds T v low low := by
  have hg := insertChecksAtHead_guard hV h
  refine ⟨hg.initialized, hg.nonzero, hg.fresh, hg.inBounds, hg.lowBelow, ?_⟩
  apply lowSearch_stop
  rintro ⟨hne, hlt⟩
  rcases hg.window with h0 | hle
  · exact hne h0
  · exact absurd hle (not_le.mpr hlt)

/-- Every pin insert is a head insert. -/
lemma atHead_insert_of_pin {T : Tree} {v : UInt256} {hint low : ℕ}
    (h : InsertSucceeds T v hint low) : InsertChecksAtHead T v hint low :=
  ⟨h.initialized, h.nonzero, h.fresh, h.hintInBounds, h.hintBelow, _, h.search⟩

lemma pin_append_of_atHead {cv : CommitValue} {s : ChainState} (hV : Valid s.tree)
    {f b : UInt256} {hint low : ℕ} (h : AppendSucceedsAtHead cv s f b hint low) :
    AppendSucceeds cv s f b low low :=
  ⟨h.legUnset, pin_insert_of_atHead hV h.treeInsert⟩

lemma atHead_append_of_pin {cv : CommitValue} {s : ChainState} {f b : UInt256}
    {hint low : ℕ} (h : AppendSucceeds cv s f b hint low) :
    AppendSucceedsAtHead cv s f b hint low :=
  ⟨h.legUnset, atHead_insert_of_pin h.treeInsert⟩

/-! ## Runs -/

/-- A head run from a valid tree is a pin run with the same states and log. -/
theorem stepsAtHead_steps {cv : CommitValue} {c : Chain} {s t : ChainState}
    {log : List Obligation} (h : StepsAtHead cv c s t log) (hV : Valid s.tree) :
    Steps cv c s t log := by
  induction h with
  | refl => exact Steps.refl
  | append _ ha ih =>
    exact Steps.append ih
      (pin_append_of_atHead (reaches_valid (steps_tree_reaches ih hV) hV) ha)
  | authorize _ hg ih => exact Steps.authorize ih hg
  | claim _ hg ih => exact Steps.claim ih hg
  | initL2 _ h0 ih => exact Steps.initL2 ih h0

/-- A pin run is a head run. -/
theorem steps_stepsAtHead {cv : CommitValue} {c : Chain} {s t : ChainState}
    {log : List Obligation} (h : Steps cv c s t log) : StepsAtHead cv c s t log := by
  induction h with
  | refl => exact StepsAtHead.refl
  | append _ ha ih => exact StepsAtHead.append ih (atHead_append_of_pin ha)
  | authorize _ hg ih => exact StepsAtHead.authorize ih hg
  | claim _ hg ih => exact StepsAtHead.claim ih hg
  | initL2 _ h0 ih => exact StepsAtHead.initL2 ih h0

theorem stepsAtHead_iff_steps (cv : CommitValue) (c : Chain) (s : ChainState)
    (log : List Obligation) : StepsAtHead cv c genesis s log ↔ Steps cv c genesis s log :=
  ⟨fun h => stepsAtHead_steps h setup_valid, steps_stepsAtHead⟩

/-- A head system run from genesis is a pin system run. -/
theorem sysStepsAtHead_sysSteps {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {Y : Chains} {log : List Obligation} {alog : List AuthCall}
    (hr : SysStepsAtHead h z0 hl cv fh S genesisAll Y log alog) :
    SysSteps h z0 hl cv fh S genesisAll Y log alog := by
  induction hr with
  | refl => exact SysSteps.refl
  | @append Y log alog c f b hint low _ ha ih =>
    exact SysSteps.append ih (pin_append_of_atHead (inv_of_steps (sysSteps_chain ih c)).valid ha)
  | @authorize Y log alog a _ hv hg ih => exact SysSteps.authorize a ih hv hg
  | claim _ hg ih => exact SysSteps.claim ih hg
  | initL2 _ h0 ih => exact SysSteps.initL2 ih h0

/-- A pin system run is a head system run. -/
theorem sysSteps_sysStepsAtHead {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {X Y : Chains} {log : List Obligation} {alog : List AuthCall}
    (hr : SysSteps h z0 hl cv fh S X Y log alog) :
    SysStepsAtHead h z0 hl cv fh S X Y log alog := by
  induction hr with
  | refl => exact SysStepsAtHead.refl
  | append _ ha ih => exact SysStepsAtHead.append ih (atHead_append_of_pin ha)
  | @authorize Y log alog a _ hv hg ih => exact SysStepsAtHead.authorize a ih hv hg
  | claim _ hg ih => exact SysStepsAtHead.claim ih hg
  | initL2 _ h0 ih => exact SysStepsAtHead.initL2 ih h0

theorem sysStepsAtHead_iff_sysSteps (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) (Y : Chains) (log : List Obligation) (alog : List AuthCall) :
    SysStepsAtHead h z0 hl cv fh S genesisAll Y log alog
      ↔ SysSteps h z0 hl cv fh S genesisAll Y log alog :=
  ⟨sysStepsAtHead_sysSteps, sysSteps_sysStepsAtHead⟩

/-- The tree of every reachable state is valid. -/
lemma stepsAtHead_valid {cv : CommitValue} {c : Chain} {s : ChainState} {log : List Obligation}
    (h : StepsAtHead cv c genesis s log) : Valid s.tree :=
  (inv_of_steps (stepsAtHead_steps h setup_valid)).valid

/-! ## The restated headlines -/

theorem OncePerLegAtHead : Properties.OncePerLegAtHead :=
  fun cv c s log h => OncePerLeg cv c s log ((stepsAtHead_iff_steps cv c s log).mp h)

theorem NoSecondAppendAtHead : Properties.NoSecondAppendAtHead := by
  intro cv c s log f b hint low t log' hrun happ hseg
  have hrun' := (stepsAtHead_iff_steps cv c s log).mp hrun
  have hV : Valid s.tree := (inv_of_steps hrun').valid
  have happ' : AppendSucceeds cv s f b low low := pin_append_of_atHead hV happ
  have hV₁ : Valid (s.appended cv f b low).tree :=
    insert_preserves_valid hV (insertChecksAtHead_guard hV happ.treeInsert)
  have hseg' : Steps cv c (s.appended cv f b low) t log' := stepsAtHead_steps hseg hV₁
  obtain ⟨h1, h2⟩ := NoSecondAppend cv c s log f b low low t log' hrun' happ' hseg'
  refine ⟨h1, fun hint' low' hins => ?_⟩
  have hVt : Valid t.tree := reaches_valid (steps_tree_reaches hseg' hV₁) hV₁
  exact h2 low' low' (pin_insert_of_atHead hVt hins)

theorem RefundedLegWasAppendedOnceAtHead : Properties.RefundedLegWasAppendedOnceAtHead :=
  fun cv c s log h =>
    RefundedLegWasAppendedOnce cv c s log ((stepsAtHead_iff_steps cv c s log).mp h)

theorem KeyPinsAppendedLegOrClashAtHead : Properties.KeyPinsAppendedLegOrClashAtHead :=
  fun cv c s log h =>
    KeyPinsAppendedLegOrClash cv c s log ((stepsAtHead_iff_steps cv c s log).mp h)

theorem TreeGateImpliesManagerGateAtHead : Properties.TreeGateImpliesManagerGateAtHead := by
  intro cv c s log h f b hint low hins
  exact TreeGateImpliesManagerGate cv c s log ((stepsAtHead_iff_steps cv c s log).mp h) f b
    low low (pin_insert_of_atHead (stepsAtHead_valid h) hins)

theorem GatesDisagreeOnlyOnLoggedClashAtHead :
    Properties.GatesDisagreeOnlyOnLoggedClashAtHead :=
  fun cv c s log h =>
    GatesDisagreeOnlyOnLoggedClash cv c s log ((stepsAtHead_iff_steps cv c s log).mp h)

theorem AppendAtHeadEnabledIff : Properties.AppendAtHeadEnabledIff := by
  intro cv c s log h f b hint
  have hI := inv_of_steps ((stepsAtHead_iff_steps cv c s log).mp h)
  have hV := hI.valid
  constructor
  · rintro ⟨low, happ⟩
    exact ⟨happ.treeInsert.nonzero, dedup_gate_sound hV happ.treeInsert.nonzero
      happ.treeInsert.unregistered, happ.treeInsert.hintInBounds, happ.treeInsert.hintBelow⟩
  · rintro ⟨hv0, hfresh, hi, hlow⟩
    obtain ⟨low, hw⟩ := walkAtHead_terminates hV (cv f b) hint hi
    refine ⟨low, ?_, hV.occupied.ne', hv0, ?_, hi, hlow, hw⟩
    · show s.mgr.legState f b = .Unset
      rw [hI.mgrUnset]
      intro hmem
      exact hfresh (hI.key_of_mem hmem)
    · by_contra hreg
      exact hfresh (registered_is_key hV hreg)

theorem AppendBlockedOnlyByClashAtHead : Properties.AppendBlockedOnlyByClashAtHead := by
  intro cv c s log h f b hunset hv0
  have h' := (stepsAtHead_iff_steps cv c s log).mp h
  have hV := stepsAtHead_valid h
  have hsame : (∃ hint low, AppendSucceedsAtHead cv s f b hint low)
      ↔ ∃ hint low, AppendSucceeds cv s f b hint low := by
    constructor
    · rintro ⟨hint, low, happ⟩
      exact ⟨low, low, pin_append_of_atHead hV happ⟩
    · rintro ⟨hint, low, happ⟩
      exact ⟨hint, low, atHead_append_of_pin happ⟩
  rw [hsame]
  exact AppendBlockedOnlyByClash cv c s log h' f b hunset hv0

theorem StepsAtHeadIffSteps : Properties.StepsAtHeadIffSteps := stepsAtHead_iff_steps

theorem SysStepsAtHeadIffSysSteps : Properties.SysStepsAtHeadIffSysSteps :=
  sysStepsAtHead_iff_sysSteps

theorem AppendAtHeadIsPinAppendAtLanding : Properties.AppendAtHeadIsPinAppendAtLanding :=
  fun _ _ _ _ h _ _ _ _ happ => pin_append_of_atHead (stepsAtHead_valid h) happ

theorem SystemOncePerLegAtHead : Properties.SystemOncePerLegAtHead :=
  fun h z0 hl cv fh S Y log alog hr =>
    SystemOncePerLeg h z0 hl cv fh S Y log alog (sysStepsAtHead_sysSteps hr)

theorem SystemRefundedWasAppendedOnceAtHead : Properties.SystemRefundedWasAppendedOnceAtHead :=
  fun h z0 hl cv fh S Y log alog hr =>
    SystemRefundedWasAppendedOnce h z0 hl cv fh S Y log alog (sysStepsAtHead_sysSteps hr)

theorem SystemExecutedObligationNeverRefundedOrBreakAtHead :
    Properties.SystemExecutedObligationNeverRefundedOrBreakAtHead :=
  fun h z0 hl cv fh S hS F ev leg hex Y log alog hr =>
    SystemExecutedObligationNeverRefundedOrBreak h z0 hl cv fh S hS F ev leg hex Y log alog
      (sysStepsAtHead_sysSteps hr)

/-! ## The witnesses: six honest appends, then a stale hint -/

/-- A leg's commit value is its bundle hash. -/
private def headCv : CommitValue := fun _ b => b

/-- After the honest appends `(0, 1), …, (0, n)` on chain `0`, each from its own low leaf. -/
private def honestState : ℕ → ChainState
  | 0 => genesis
  | n + 1 => (honestState n).appended headCv 0 ((n + 1 : ℕ) : UInt256) n

/-- Their log, most recent first. -/
private def honestLog : ℕ → List Obligation
  | 0 => []
  | n + 1 => ⟨0, ((n + 1 : ℕ) : UInt256), 0⟩ :: honestLog n

private lemma honestState_tree : ∀ n, (honestState n).tree = chainTree n
  | 0 => rfl
  | n + 1 => by
    show Contracts.InteropCommitmentTree.insert (honestState n).tree ((n + 1 : ℕ) : UInt256) n
      = chainTree (n + 1)
    rw [honestState_tree n]
    rfl

private lemma honest_append (n : ℕ) (hn : n < 6) :
    AppendSucceeds headCv (honestState n) 0 ((n + 1 : ℕ) : UInt256) n n := by
  refine ⟨?_, ?_⟩
  · interval_cases n <;> (unfold AppendGuard; decide)
  · show InsertSucceeds (honestState n).tree ((n + 1 : ℕ) : UInt256) n n
    rw [honestState_tree n]
    interval_cases n <;>
      exact ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide,
        by decide⟩

private lemma honest_steps : ∀ n, n ≤ 6 → Steps headCv 0 genesis (honestState n) (honestLog n)
  | 0, _ => Steps.refl
  | n + 1, hn => Steps.append (honest_steps n (by omega)) (honest_append n (by omega))

private lemma honest_six_guard : AppendGuard (honestState 6).mgr 0 7 := by
  unfold AppendGuard
  decide

private lemma stale_atHead : AppendSucceedsAtHead headCv (honestState 6) 0 7 0 6 := by
  refine ⟨honest_six_guard, ?_⟩
  show InsertChecksAtHead (honestState 6).tree 7 0 6
  rw [honestState_tree 6]
  exact HonestInsertSucceedsAtHead.2.2

theorem StaleHintAppendRevertsAtPinSucceedsAtHead :
    Properties.StaleHintAppendRevertsAtPinSucceedsAtHead := by
  have hrun := honest_steps 6 le_rfl
  have hV : Valid (honestState 6).tree := (inv_of_steps hrun).valid
  refine ⟨headCv, honestState 6, honestLog 6, 0, 7, hrun, steps_stepsAtHead hrun,
    honestState_tree 6, honest_six_guard, ?_, stale_atHead,
    pin_append_of_atHead hV stale_atHead⟩
  intro low happ
  have hs : lowSearch (honestState 6).tree 7 maxLowIndexSearchAttempts 0 = some low :=
    happ.treeInsert.search
  rw [honestState_tree 6, HonestInsertRevertsAtDeployedFuel.2.2.2.1] at hs
  exact absurd hs (by simp)

theorem OncePerLegAtHeadWitness : Properties.OncePerLegAtHeadWitness := by
  have hrun := steps_stepsAtHead (honest_steps 6 le_rfl)
  refine ⟨headCv, (honestState 6).appended headCv 0 7 6, ⟨0, 7, 0⟩ :: honestLog 6,
    StepsAtHead.append hrun stale_atHead, rfl, ?_, ?_⟩
  · show (Contracts.InteropCommitmentTree.insert (honestState 6).tree (headCv 0 7) 6).leafCount = 8
    rw [honestState_tree 6]
    decide
  · show ((honestState 6).mgr.set 0 7 .Committed).legState 0 7 = .Committed
    exact set_same

end Contracts.AppendPath
