import EraSpec.Protocol.InteropAtomicity.Properties.Operational
import EraSpec.Protocol.InteropAtomicity.Proofs.OncePerLeg
import EraSpec.Protocol.InteropAtomicity.Proofs.FlowBinding
import EraSpec.Protocol.InteropAtomicity.Proofs.SourceHeight
import EraSpec.Protocol.InteropAtomicity.Proofs.Timeout

/-!
# Proofs: every operational run projects to a fixed history

Proofs of `EraSpec.Protocol.InteropAtomicity.Properties.Operational`.

One invariant (`OpInv`), proved by induction over a run from `opGenesis`, carries the
projection: every live tree is valid, consecutive END snapshots and the live tree are related
by guarded inserts, settlement times are monotone and not after the clock, and every recorded
root holds every batch settled strictly before it.  `opHistory_wf` reads `Wf` off it, through
`Contracts.Atomicity.wf_of_heights_from_source`.

A second relation (`OpExtends`) says a later state keeps every snapshot, settlement time and
root of an earlier one.  A call checked at a state against settled batches is then checked
against the history of every later state (`opExecChecks_transfer`, `opAuthVerified_transfer`):
that is what lets `opSteps_embed` replay the run's per-chain steps as a
`Contracts.AppendPath.SysSteps` run and its checked calls as a `Contracts.FlowBinding.RunLog`
run over the final state's history, and every transferred headline is that embedding followed
by the fixed-history theorem.  The timeout gate's END branch needs only the strict
aggregation fact (`isLastOnTime_of_aggregatesBefore`).

The two new results about escrow (`op_executed_leg_appended_or_break`,
`op_executed_leg_escrowed_or_break`) read the executed leg's commit value off the cited
batch's tree (`finality_means_membership_or_break`), carry it to the live tree
(`op_history_keys_live`, by `keys_mono_batch` on the projected history), and then use the
once-per-leg facts of the live tree's own chain (`SystemKeyPinsAppendedLegOrClash`).
-/

namespace Contracts.InteropOperational

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.Timeout Contracts.AtomicFlowManager Contracts.Refund Contracts.AppendPath
open Contracts.FlowBinding MerkleSpec.Verifier

/-! ## Reading the updated states -/

@[simp] lemma OpState.setChain_chains (X : OpState) (c : Chain) (s : ChainState) :
    (X.setChain c s).chains = X.chains.update c s := rfl
@[simp] lemma OpState.setChain_batches (X : OpState) (c : Chain) (s : ChainState) :
    (X.setChain c s).batches = X.batches := rfl
@[simp] lemma OpState.setChain_now (X : OpState) (c : Chain) (s : ChainState) :
    (X.setChain c s).now = X.now := rfl
@[simp] lemma OpState.setChain_roots (X : OpState) (c : Chain) (s : ChainState) :
    (X.setChain c s).roots = X.roots := rfl

@[simp] lemma OpState.endBatch_chains (X : OpState) (c : Chain) :
    (X.endBatch c).chains = X.chains := rfl
@[simp] lemma OpState.endBatch_now (X : OpState) (c : Chain) : (X.endBatch c).now = X.now := rfl
@[simp] lemma OpState.endBatch_roots (X : OpState) (c : Chain) :
    (X.endBatch c).roots = X.roots := rfl
lemma OpState.endBatch_batches (X : OpState) (c x : Chain) :
    (X.endBatch c).batches x
      = if x = c then (X.batches c).endBatch (X.chains c).tree else X.batches x := rfl

@[simp] lemma OpState.settle_chains (X : OpState) (c : Chain) : (X.settle c).chains = X.chains := rfl
@[simp] lemma OpState.settle_now (X : OpState) (c : Chain) : (X.settle c).now = X.now := rfl
@[simp] lemma OpState.settle_roots (X : OpState) (c : Chain) : (X.settle c).roots = X.roots := rfl
lemma OpState.settle_batches (X : OpState) (c x : Chain) :
    (X.settle c).batches x = if x = c then (X.batches c).settle X.now else X.batches x := rfl

@[simp] lemma OpState.tick_chains (X : OpState) (t : ℕ) : (X.tick t).chains = X.chains := rfl
@[simp] lemma OpState.tick_batches (X : OpState) (t : ℕ) : (X.tick t).batches = X.batches := rfl
@[simp] lemma OpState.tick_now (X : OpState) (t : ℕ) : (X.tick t).now = t := rfl
@[simp] lemma OpState.tick_roots (X : OpState) (t : ℕ) : (X.tick t).roots = X.roots := rfl

@[simp] lemma OpState.recordRoot_chains (X : OpState) : X.recordRoot.chains = X.chains := rfl
@[simp] lemma OpState.recordRoot_batches (X : OpState) : X.recordRoot.batches = X.batches := rfl
@[simp] lemma OpState.recordRoot_now (X : OpState) : X.recordRoot.now = X.now := rfl
@[simp] lemma OpState.recordRoot_roots (X : OpState) :
    X.recordRoot.roots = X.currentRoot :: X.roots := rfl

@[simp] lemma BatchLog.endBatch_ended (B : BatchLog) (T : Tree) :
    (B.endBatch T).ended = B.ended + 1 := rfl
@[simp] lemma BatchLog.endBatch_settled (B : BatchLog) (T : Tree) :
    (B.endBatch T).settled = B.settled := rfl
@[simp] lemma BatchLog.endBatch_stamp (B : BatchLog) (T : Tree) :
    (B.endBatch T).stamp = B.stamp := rfl
lemma BatchLog.endBatch_snap (B : BatchLog) (T : Tree) (n : ℕ) :
    (B.endBatch T).snap n = if n = B.ended then T else B.snap n := rfl

@[simp] lemma BatchLog.settle_ended (B : BatchLog) (t : ℕ) : (B.settle t).ended = B.ended := rfl
@[simp] lemma BatchLog.settle_settled (B : BatchLog) (t : ℕ) :
    (B.settle t).settled = B.settled + 1 := rfl
@[simp] lemma BatchLog.settle_snap (B : BatchLog) (t : ℕ) : (B.settle t).snap = B.snap := rfl
lemma BatchLog.settle_stamp (B : BatchLog) (t : ℕ) (n : ℕ) :
    (B.settle t).stamp n = if n = B.settled then t else B.stamp n := rfl

/-- A chain-state update that keeps the tree keeps every chain's tree. -/
lemma opUpdate_tree_same (X : Chains) {c : Chain} {s : ChainState} (hs : s.tree = (X c).tree)
    (x : Chain) : ((X.update c s) x).tree = (X x).tree := by
  by_cases hx : x = c
  · subst hx; rw [update_self, hs]
  · rw [update_other _ _ hx]

/-! ## The run invariant -/

/-- What every run from `opGenesis` keeps. -/
structure OpInv (X : OpState) : Prop where
  settledPos : ∀ c, 0 < (X.batches c).settled
  settledLe : ∀ c, (X.batches c).settled ≤ (X.batches c).ended
  liveValid : ∀ c, Valid (X.chains c).tree
  snapStart : ∀ c, Reaches setup ((X.batches c).snap 0)
  snapStep : ∀ c n, n + 1 < (X.batches c).ended →
    Reaches ((X.batches c).snap n) ((X.batches c).snap (n + 1))
  snapLive : ∀ c, Reaches ((X.batches c).snap ((X.batches c).ended - 1)) (X.chains c).tree
  stampMono : ∀ c m n, m ≤ n → n < (X.batches c).settled →
    (X.batches c).stamp m ≤ (X.batches c).stamp n
  stampLe : ∀ c n, n < (X.batches c).settled → (X.batches c).stamp n ≤ X.now
  rootsPast : ∀ R ∈ X.roots, R.created ≤ X.now
  rootsSettled : ∀ R ∈ X.roots, ∀ c, R.upTo c < (X.batches c).settled
  rootsAggregate : ∀ R ∈ X.roots, ∀ c n, n < (X.batches c).settled →
    (X.batches c).stamp n < R.created → n ≤ R.upTo c

lemma OpInv.endedPos {X : OpState} (hI : OpInv X) (c : Chain) : 0 < (X.batches c).ended :=
  lt_of_lt_of_le (hI.settledPos c) (hI.settledLe c)

lemma opInv_genesis : OpInv opGenesis where
  settledPos := fun _ => Nat.one_pos
  settledLe := fun _ => le_refl _
  liveValid := fun _ => setup_valid
  snapStart := fun _ => Reaches.refl
  snapStep := fun _ n hn => by
    exfalso
    have : n + 1 < 1 := hn
    omega
  snapLive := fun _ => Reaches.refl
  stampMono := fun _ _ _ _ _ => le_refl _
  stampLe := fun _ _ _ => le_refl _
  rootsPast := fun _ hR => absurd hR List.not_mem_nil
  rootsSettled := fun _ hR => absurd hR List.not_mem_nil
  rootsAggregate := fun _ hR => absurd hR List.not_mem_nil

/-- A per-chain step that keeps every tree keeps the invariant. -/
lemma opInv_setChain_sameTree {X : OpState} (hI : OpInv X) {c : Chain} {s : ChainState}
    (hs : s.tree = (X.chains c).tree) : OpInv (X.setChain c s) := by
  have ht := opUpdate_tree_same X.chains hs
  refine ⟨hI.settledPos, hI.settledLe, fun x => ?_, hI.snapStart, hI.snapStep, fun x => ?_,
    hI.stampMono, hI.stampLe, hI.rootsPast, hI.rootsSettled, hI.rootsAggregate⟩
  · simp only [OpState.setChain_chains]; rw [ht]; exact hI.liveValid x
  · simp only [OpState.setChain_chains, OpState.setChain_batches]; rw [ht]; exact hI.snapLive x

/-- A successful `append` keeps the invariant: the live tree takes one guarded insert. -/
lemma opInv_append {X : OpState} (hI : OpInv X) {c : Chain} {f b : UInt256} {hint low : ℕ}
    {cv : CommitValue} (ha : AppendSucceeds cv (X.chains c) f b hint low) :
    OpInv (X.setChain c ((X.chains c).appended cv f b low)) := by
  have hg : InsertGuard (X.chains c).tree (cv f b) low := ha.treeInsert.guard (hI.liveValid c)
  refine ⟨hI.settledPos, hI.settledLe, fun x => ?_, hI.snapStart, hI.snapStep, fun x => ?_,
    hI.stampMono, hI.stampLe, hI.rootsPast, hI.rootsSettled, hI.rootsAggregate⟩
  · simp only [OpState.setChain_chains]
    by_cases hx : x = c
    · subst hx
      rw [update_self, appended_tree]
      exact insert_preserves_valid (hI.liveValid x) hg
    · rw [update_other _ _ hx]; exact hI.liveValid x
  · simp only [OpState.setChain_chains, OpState.setChain_batches]
    by_cases hx : x = c
    · subst hx
      rw [update_self, appended_tree]
      exact Reaches.tail (hI.snapLive x) hg
    · rw [update_other _ _ hx]; exact hI.snapLive x

/-- `initL2` cannot fire on a reachable state: every live tree is occupied. -/
lemma opInitL2_dead {X : OpState} (hI : OpInv X) (c : Chain) :
    (X.chains c).tree.leafCount ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (hI.liveValid c).occupied

lemma OpState.endBatch_batches_self (X : OpState) (c : Chain) :
    (X.endBatch c).batches c = (X.batches c).endBatch (X.chains c).tree := by
  rw [OpState.endBatch_batches, ite_eq_left rfl]

lemma OpState.endBatch_batches_other (X : OpState) {c x : Chain} (hx : x ≠ c) :
    (X.endBatch c).batches x = X.batches x := by
  rw [OpState.endBatch_batches, ite_eq_right hx]

lemma OpState.settle_batches_self (X : OpState) (c : Chain) :
    (X.settle c).batches c = (X.batches c).settle X.now := by
  rw [OpState.settle_batches, ite_eq_left rfl]

lemma OpState.settle_batches_other (X : OpState) {c x : Chain} (hx : x ≠ c) :
    (X.settle c).batches x = X.batches x := by
  rw [OpState.settle_batches, ite_eq_right hx]

lemma opInv_endBatch {X : OpState} (hI : OpInv X) (c : Chain) : OpInv (X.endBatch c) := by
  refine ⟨fun x => ?_, fun x => ?_, hI.liveValid, fun x => ?_, fun x n hn => ?_, fun x => ?_,
    fun x m n hmn hn => ?_, fun x n hn => ?_, hI.rootsPast, fun R hR x => ?_,
    fun R hR x n hn hlt => ?_⟩
  all_goals by_cases hx : x = c
  all_goals first
    | (subst hx; rw [OpState.endBatch_batches_self] at *)
    | rw [OpState.endBatch_batches_other _ hx] at *
  · exact hI.settledPos x
  · exact hI.settledPos x
  · exact le_trans (hI.settledLe x) (Nat.le_succ _)
  · exact hI.settledLe x
  · rw [BatchLog.endBatch_snap, ite_eq_right (Nat.pos_iff_ne_zero.mp (hI.endedPos x)).symm]
    exact hI.snapStart x
  · exact hI.snapStart x
  · simp only [BatchLog.endBatch_ended] at hn
    rw [BatchLog.endBatch_snap, BatchLog.endBatch_snap]
    by_cases hlast : n + 1 = (X.batches x).ended
    · rw [ite_eq_left hlast, ite_eq_right (by omega)]
      have := hI.snapLive x
      rwa [show (X.batches x).ended - 1 = n by omega] at this
    · rw [ite_eq_right hlast, ite_eq_right (by omega)]
      exact hI.snapStep x n (by omega)
  · exact hI.snapStep x n hn
  · simp only [OpState.endBatch_chains, BatchLog.endBatch_ended]
    rw [BatchLog.endBatch_snap, ite_eq_left (by omega)]
    exact Reaches.refl
  · simp only [OpState.endBatch_chains]
    exact hI.snapLive x
  · exact hI.stampMono x m n hmn hn
  · exact hI.stampMono x m n hmn hn
  · exact hI.stampLe x n hn
  · exact hI.stampLe x n hn
  · exact hI.rootsSettled R hR x
  · exact hI.rootsSettled R hR x
  · exact hI.rootsAggregate R hR x n hn hlt
  · exact hI.rootsAggregate R hR x n hn hlt

lemma opInv_settle {X : OpState} (hI : OpInv X) {c : Chain}
    (hlt : (X.batches c).settled < (X.batches c).ended) : OpInv (X.settle c) := by
  refine ⟨fun x => ?_, fun x => ?_, hI.liveValid, fun x => ?_, fun x n hn => ?_, fun x => ?_,
    fun x m n hmn hn => ?_, fun x n hn => ?_, hI.rootsPast, fun R hR x => ?_,
    fun R hR x n hn hlt' => ?_⟩
  all_goals by_cases hx : x = c
  all_goals first
    | (subst hx; rw [OpState.settle_batches_self] at *)
    | rw [OpState.settle_batches_other _ hx] at *
  all_goals try simp only [BatchLog.settle_settled, BatchLog.settle_ended, BatchLog.settle_snap,
    OpState.settle_chains, OpState.settle_now, OpState.settle_roots] at *
  · omega
  · exact hI.settledPos x
  · omega
  · exact hI.settledLe x
  · exact hI.snapStart x
  · exact hI.snapStart x
  · exact hI.snapStep x n hn
  · exact hI.snapStep x n hn
  · exact hI.snapLive x
  · exact hI.snapLive x
  · rw [BatchLog.settle_stamp, BatchLog.settle_stamp]
    by_cases hn' : n = (X.batches x).settled
    · rw [ite_eq_left hn']
      by_cases hm' : m = (X.batches x).settled
      · rw [ite_eq_left hm']
      · rw [ite_eq_right hm']
        exact hI.stampLe x m (by omega)
    · rw [ite_eq_right hn', ite_eq_right (by omega)]
      exact hI.stampMono x m n hmn (by omega)
  · exact hI.stampMono x m n hmn hn
  · rw [BatchLog.settle_stamp]
    by_cases hn' : n = (X.batches x).settled
    · rw [ite_eq_left hn']
    · rw [ite_eq_right hn']
      exact hI.stampLe x n (by omega)
  · exact hI.stampLe x n hn
  · exact Nat.lt_succ_of_lt (hI.rootsSettled R hR x)
  · exact hI.rootsSettled R hR x
  · rw [BatchLog.settle_stamp] at hlt'
    by_cases hn' : n = (X.batches x).settled
    · rw [ite_eq_left hn'] at hlt'
      exact absurd (hI.rootsPast R hR) (not_le.mpr hlt')
    · rw [ite_eq_right hn'] at hlt'
      exact hI.rootsAggregate R hR x n (by omega) hlt'
  · exact hI.rootsAggregate R hR x n hn hlt'

lemma opInv_tick {X : OpState} (hI : OpInv X) {t : ℕ} (ht : X.now ≤ t) : OpInv (X.tick t) :=
  ⟨hI.settledPos, hI.settledLe, hI.liveValid, hI.snapStart, hI.snapStep, hI.snapLive,
    hI.stampMono, fun c n hn => le_trans (hI.stampLe c n hn) ht,
    fun R hR => le_trans (hI.rootsPast R hR) ht, hI.rootsSettled, hI.rootsAggregate⟩

lemma opInv_recordRoot {X : OpState} (hI : OpInv X) : OpInv X.recordRoot := by
  refine ⟨hI.settledPos, hI.settledLe, hI.liveValid, hI.snapStart, hI.snapStep, hI.snapLive,
    hI.stampMono, hI.stampLe, fun R hR => ?_, fun R hR c => ?_, fun R hR c n hn hlt => ?_⟩
  all_goals simp only [OpState.recordRoot_roots, List.mem_cons] at hR
  all_goals rcases hR with rfl | hR
  · exact le_refl _
  · exact hI.rootsPast R hR
  · show (X.batches c).settled - 1 < (X.batches c).settled
    have := hI.settledPos c
    omega
  · exact hI.rootsSettled R hR c
  · show n ≤ (X.batches c).settled - 1
    simp only [OpState.recordRoot_batches] at hn
    omega
  · exact hI.rootsAggregate R hR c n hn hlt

/-- **THE INVARIANT HOLDS ALONG EVERY RUN FROM `opGenesis`.** -/
theorem opInv_of_opSteps {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {Y : OpState} {log : List Obligation} {clog : List CheckedCall}
    (hr : OpSteps h z0 hl cv fh opGenesis Y log clog) : OpInv Y := by
  induction hr with
  | refl => exact opInv_genesis
  | append _ ha ih => exact opInv_append ih ha
  | execute _ _ _ ih => exact ih
  | authorize _ _ _ _ _ ih => exact opInv_setChain_sameTree ih rfl
  | claim _ _ ih => exact opInv_setChain_sameTree ih rfl
  | @initL2 Y _ _ c _ h0 ih => exact absurd h0 (opInitL2_dead ih c)
  | endBatch _ ih => exact opInv_endBatch ih _
  | settle _ hlt ih => exact opInv_settle ih hlt
  | tick _ ht ih => exact opInv_tick ih ht
  | recordRoot _ ih => exact opInv_recordRoot ih

/-! ## The history only grows -/

/-- `Y` extends `X`'s history: every ended batch keeps its snapshot, every settled batch its
settlement time, every recorded root stays recorded, and the clock does not go back. -/
structure OpExtends (X Y : OpState) : Prop where
  ended : ∀ c, (X.batches c).ended ≤ (Y.batches c).ended
  settled : ∀ c, (X.batches c).settled ≤ (Y.batches c).settled
  snap : ∀ c n, n < (X.batches c).ended → (Y.batches c).snap n = (X.batches c).snap n
  stamp : ∀ c n, n < (X.batches c).settled → (Y.batches c).stamp n = (X.batches c).stamp n
  roots : ∀ R ∈ X.roots, R ∈ Y.roots
  now : X.now ≤ Y.now

lemma opExtends_refl (X : OpState) : OpExtends X X :=
  ⟨fun _ => le_refl _, fun _ => le_refl _, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ hR => hR, le_refl _⟩

lemma opExtends_trans {X Y Z : OpState} (h₁ : OpExtends X Y) (h₂ : OpExtends Y Z) :
    OpExtends X Z :=
  ⟨fun c => le_trans (h₁.ended c) (h₂.ended c), fun c => le_trans (h₁.settled c) (h₂.settled c),
    fun c n hn => (h₂.snap c n (lt_of_lt_of_le hn (h₁.ended c))).trans (h₁.snap c n hn),
    fun c n hn => (h₂.stamp c n (lt_of_lt_of_le hn (h₁.settled c))).trans (h₁.stamp c n hn),
    fun R hR => h₂.roots R (h₁.roots R hR), le_trans h₁.now h₂.now⟩

lemma opExtends_setChain (X : OpState) (c : Chain) (s : ChainState) :
    OpExtends X (X.setChain c s) :=
  ⟨fun _ => le_refl _, fun _ => le_refl _, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ hR => hR, le_refl _⟩

lemma opExtends_endBatch (X : OpState) (c : Chain) : OpExtends X (X.endBatch c) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x n hn => ?_, fun x n hn => ?_, fun _ hR => hR,
    le_refl _⟩
  all_goals by_cases hx : x = c
  all_goals first
    | (subst hx; rw [OpState.endBatch_batches_self])
    | rw [OpState.endBatch_batches_other _ hx]
  all_goals first
    | exact Nat.le_succ _
    | exact le_refl _
    | rfl
    | rw [BatchLog.endBatch_snap, ite_eq_right (by omega)]

lemma opExtends_settle (X : OpState) (c : Chain) : OpExtends X (X.settle c) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x n hn => ?_, fun x n hn => ?_, fun _ hR => hR,
    le_refl _⟩
  all_goals by_cases hx : x = c
  all_goals first
    | (subst hx; rw [OpState.settle_batches_self])
    | rw [OpState.settle_batches_other _ hx]
  all_goals first
    | exact Nat.le_succ _
    | exact le_refl _
    | rfl
    | rw [BatchLog.settle_stamp, ite_eq_right (by omega)]

lemma opExtends_tick (X : OpState) {t : ℕ} (ht : X.now ≤ t) : OpExtends X (X.tick t) :=
  ⟨fun _ => le_refl _, fun _ => le_refl _, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ hR => hR, ht⟩

lemma opExtends_recordRoot (X : OpState) : OpExtends X X.recordRoot :=
  ⟨fun _ => le_refl _, fun _ => le_refl _, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ hR => List.mem_cons_of_mem _ hR, le_refl _⟩

/-- **EVERY RUN ONLY EXTENDS THE HISTORY.** -/
theorem opExtends_of_opSteps {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {X Y : OpState} {log : List Obligation} {clog : List CheckedCall}
    (hr : OpSteps h z0 hl cv fh X Y log clog) : OpExtends X Y := by
  induction hr with
  | refl => exact opExtends_refl _
  | append _ _ ih => exact opExtends_trans ih (opExtends_setChain _ _ _)
  | execute _ _ _ ih => exact ih
  | authorize _ _ _ _ _ ih => exact opExtends_trans ih (opExtends_setChain _ _ _)
  | claim _ _ ih => exact opExtends_trans ih (opExtends_setChain _ _ _)
  | initL2 _ _ ih => exact opExtends_trans ih (opExtends_setChain _ _ _)
  | endBatch _ ih => exact opExtends_trans ih (opExtends_endBatch _ _)
  | settle _ _ ih => exact opExtends_trans ih (opExtends_settle _ _)
  | tick _ ht ih => exact opExtends_trans ih (opExtends_tick _ ht)
  | recordRoot _ ih => exact opExtends_trans ih (opExtends_recordRoot _)

/-- Runs compose; the logs concatenate, later entries first. -/
theorem opSteps_trans {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {X Y Z : OpState} {l₁ l₂ : List Obligation} {c₁ c₂ : List CheckedCall}
    (h₁ : OpSteps h z0 hl cv fh X Y l₁ c₁) (h₂ : OpSteps h z0 hl cv fh Y Z l₂ c₂) :
    OpSteps h z0 hl cv fh X Z (l₂ ++ l₁) (c₂ ++ c₁) := by
  induction h₂ with
  | refl => exact h₁
  | append _ ha ih => exact OpSteps.append ih ha
  | execute e _ hc ih => exact OpSteps.execute e ih hc
  | authorize a R _ hc hg ih => exact OpSteps.authorize a R ih hc hg
  | claim _ hg ih => exact OpSteps.claim ih hg
  | initL2 _ h0 ih => exact OpSteps.initL2 ih h0
  | endBatch _ ih => exact OpSteps.endBatch ih
  | settle _ hlt ih => exact OpSteps.settle ih hlt
  | tick _ ht ih => exact OpSteps.tick ih ht
  | recordRoot _ ih => exact OpSteps.recordRoot ih

/-! ## Settled batches are final -/

lemma OpState.history_tree (X : OpState) (c : Chain) (n : ℕ) :
    X.history.tree c n
      = if n < (X.batches c).ended then (X.batches c).snap n else (X.chains c).tree := rfl

lemma OpState.history_time (X : OpState) (c : Chain) (n : ℕ) :
    X.history.time c n = if n < (X.batches c).settled then (X.batches c).stamp n else X.now := rfl

lemma OpState.history_height (X : OpState) (c : Chain) (n : ℕ) :
    X.history.height c n = fmHeight (X.history.tree c n).leafCount := rfl

lemma opHistory_tree_ended {X : OpState} {c : Chain} {n : ℕ} (hn : n < (X.batches c).ended) :
    X.history.tree c n = (X.batches c).snap n := by
  rw [OpState.history_tree, ite_eq_left hn]

lemma opHistory_time_settled {X : OpState} {c : Chain} {n : ℕ} (hn : n < (X.batches c).settled) :
    X.history.time c n = (X.batches c).stamp n := by
  rw [OpState.history_time, ite_eq_left hn]

/-- A settled batch of `X` has the same tree, time and height in every extension. -/
lemma opHistory_agree {X Y : OpState} (hX : OpInv X) (hE : OpExtends X Y) {c : Chain} {n : ℕ}
    (hn : n < (X.batches c).settled) :
    Y.history.tree c n = X.history.tree c n ∧ Y.history.time c n = X.history.time c n
      ∧ Y.history.height c n = X.history.height c n := by
  have hnE : n < (X.batches c).ended := lt_of_lt_of_le hn (hX.settledLe c)
  have htree : Y.history.tree c n = X.history.tree c n := by
    rw [opHistory_tree_ended hnE, opHistory_tree_ended (lt_of_lt_of_le hnE (hE.ended c)),
      hE.snap c n hnE]
  refine ⟨htree, ?_, ?_⟩
  · rw [opHistory_time_settled hn, opHistory_time_settled (lt_of_lt_of_le hn (hE.settled c)),
      hE.stamp c n hn]
  · rw [OpState.history_height, OpState.history_height, htree]

/-- The BEGIN tree of a settled batch is final too. -/
lemma opBeginTree_agree {X Y : OpState} (hX : OpInv X) (hE : OpExtends X Y) {c : Chain} {N : ℕ}
    (hN : N < (X.batches c).settled) :
    beginTree Y.history c N = beginTree X.history c N
      ∧ beginHeight Y.history c N = beginHeight X.history c N := by
  cases N with
  | zero => exact ⟨rfl, rfl⟩
  | succ k =>
    obtain ⟨ht, -, hh⟩ := opHistory_agree hX hE (c := c) (n := k) (by omega)
    exact ⟨ht, hh⟩

/-- An execution's gate, checked on settled batches, holds in every extension. -/
lemma opExecChecks_transfer {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {X Y : OpState} (hX : OpInv X) (hE : OpExtends X Y) {e : ExecCall}
    (hc : OpExecChecks h z0 hl cv fh X e) :
    ExecutedViaBy h z0 hl cv fh Y.history e.flow e.evidence e.leg := by
  obtain ⟨⟨hmem, hchk, hfin⟩, hset⟩ := hc
  refine ⟨hmem, hchk, fun ℓ hℓ => ?_⟩
  obtain ⟨ht, htime, hh⟩ := opHistory_agree hX hE (hset ℓ hℓ)
  obtain ⟨hon, hacc⟩ := hfin ℓ hℓ
  refine ⟨by rw [htime]; exact hon, ?_⟩
  unfold Accepts at hacc ⊢
  rw [ht, hh]
  exact hacc

/-- A timeout gate, checked on a settled batch, holds in every extension. -/
lemma opRefundableVerified_transfer {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {X Y : OpState} (hX : OpInv X) (hE : OpExtends X Y) {R : SlRoot} {F : Flow} {leg : FlowLeg}
    {N : ℕ} {p : ImtProof} (hN : N < (X.batches leg.chain).settled)
    (hv : LegRefundableVerifiedBy h z0 hl cv X.history R F leg N p) :
    LegRefundableVerifiedBy h z0 hl cv Y.history R F leg N p := by
  obtain ⟨ht, htime, hh⟩ := opHistory_agree hX hE hN
  obtain ⟨hbt, hbh⟩ := opBeginTree_agree hX hE hN
  rcases hv with ⟨hb, habs⟩ | ⟨he, habs⟩
  · refine Or.inl ⟨⟨hb.rootAfterDeadline, by rw [htime]; exact hb.late⟩, ?_⟩
    rw [hbt, hbh]
    exact habs
  · refine Or.inr ⟨⟨he.rootAfterDeadline, by rw [htime]; exact he.onTime, he.lastInRoot⟩, ?_⟩
    rw [ht, hh]
    exact habs

/-! ## The aggregation fact, and the END branch from it -/

/-- `Contracts.Timeout.isLastOnTime_of_verified` with the strict aggregation fact. -/
theorem isLastOnTime_of_aggregatesBefore {S : System} {R : SlRoot} (hagg : AggregatesBefore S R)
    {c : Chain} {D N : ℕ} (he : EndBranchVerified S R c D N) : IsLastOnTime S c D N := by
  refine ⟨he.onTime, fun m hm => ?_⟩
  by_contra hcon
  push Not at hcon
  have hin : m ≤ R.upTo c := hagg c m (lt_of_le_of_lt hcon he.rootAfterDeadline)
  rw [← he.lastInRoot] at hin
  omega

/-- A verified timeout, witnesses named, is a refundable leg, under the strict aggregation
fact. -/
theorem refundableBy_of_verifiedBy_before {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {R : SlRoot} (hagg : AggregatesBefore S R)
    {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof}
    (hv : LegRefundableVerifiedBy h z0 hl cv S R F leg N p) :
    LegRefundableBy h z0 hl cv S F leg N p := by
  rcases hv with ⟨hb, habs⟩ | ⟨he, habs⟩
  · exact Or.inl ⟨hb.late, habs⟩
  · exact Or.inr ⟨isLastOnTime_of_aggregatesBefore hagg he, habs⟩

/-- **EVERY RECORDED ROOT AGGREGATES EVERY BATCH THAT SETTLED STRICTLY BEFORE IT.** -/
theorem opRoots_aggregateBefore {Y : OpState} (hY : OpInv Y) :
    ∀ R ∈ Y.roots, AggregatesBefore Y.history R := by
  intro R hR c n hlt
  by_cases hn : n < (Y.batches c).settled
  · rw [opHistory_time_settled hn] at hlt
    exact hY.rootsAggregate R hR c n hn hlt
  · rw [OpState.history_time, ite_eq_right hn] at hlt
    exact absurd (hY.rootsPast R hR) (not_le.mpr hlt)

/-- A refund authorization, checked against a recorded root and a settled batch, is an
`AuthCall.Verified` of every reachable extension's history. -/
lemma opAuthVerified_transfer {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {X Y : OpState} (hX : OpInv X) (hY : OpInv Y) (hE : OpExtends X Y)
    {a : AuthCall} {R : SlRoot} (hc : OpAuthChecks h z0 hl cv fh X a R) :
    a.Verified h z0 hl cv fh Y.history :=
  ⟨hc.flowChecked, hc.legMem, hc.missingMem,
    refundableBy_of_verifiedBy_before (opRoots_aggregateBefore hY R (hE.roots R hc.rootImported))
      (opRefundableVerified_transfer hX hE hc.settled hc.timeout)⟩

/-! ## The history is well formed -/

theorem opHistory_wf {Y : OpState} (hY : OpInv Y) : Wf Y.history := by
  refine wf_of_heights_from_source _ (fun c => ?_) (fun c n => ?_) (fun c => ?_) (fun _ _ => rfl)
  · rw [opHistory_tree_ended (hY.endedPos c)]
    exact hY.snapStart c
  · rw [OpState.history_tree, OpState.history_tree]
    by_cases h1 : n + 1 < (Y.batches c).ended
    · rw [ite_eq_left (by omega : n < (Y.batches c).ended), ite_eq_left h1]
      exact hY.snapStep c n h1
    · rw [ite_eq_right h1]
      by_cases h2 : n < (Y.batches c).ended
      · rw [ite_eq_left h2]
        have := hY.snapLive c
        rwa [show (Y.batches c).ended - 1 = n by omega] at this
      · rw [ite_eq_right h2]
        exact Reaches.refl
  · intro i j hij
    show Y.history.time c i ≤ Y.history.time c j
    rw [OpState.history_time, OpState.history_time]
    by_cases hj : j < (Y.batches c).settled
    · rw [ite_eq_left (by omega : i < (Y.batches c).settled), ite_eq_left hj]
      exact hY.stampMono c i j hij hj
    · rw [ite_eq_right hj]
      by_cases hi : i < (Y.batches c).settled
      · rw [ite_eq_left hi]
        exact hY.stampLe c i hi
      · rw [ite_eq_right hi]

/-! ## The embedding -/

/-- **THE LOGGED CALLS OF A RUN, CHECKED AGAINST THE HISTORY OF ANY REACHABLE EXTENSION.**
The per-chain steps of the run are a `SysSteps` run, and its manager steps and checked calls
a `RunLog` run, over that history. -/
theorem opSteps_embed {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {Y : OpState} {log : List Obligation} {clog : List CheckedCall}
    (hr : OpSteps h z0 hl cv fh opGenesis Y log clog) :
    ∀ Z : OpState, OpInv Z → OpExtends Y Z →
      SysSteps h z0 hl cv fh Z.history genesisAll Y.chains log (authCalls clog)
        ∧ RunLog h z0 hl cv fh Z.history emptyManagers Y.chains.mgrs clog := by
  induction hr with
  | refl => exact fun _ _ _ => ⟨SysSteps.refl, RunLog.refl⟩
  | @append Y log clog c f b hint low _ ha ih =>
    intro Z hZ hE
    obtain ⟨hs, hrl⟩ := ih Z hZ (opExtends_trans (opExtends_setChain _ _ _) hE)
    refine ⟨SysSteps.append hs ha, ?_⟩
    simp only [OpState.setChain_chains]
    rw [mgrs_update]
    exact RunLog.append hrl ha.legUnset
  | @execute Y log clog e hprev hc ih =>
    intro Z hZ hE
    obtain ⟨hs, hrl⟩ := ih Z hZ hE
    exact ⟨hs, RunLog.execute e hrl (opExecChecks_transfer (opInv_of_opSteps hprev) hE hc)⟩
  | @authorize Y log clog a R hprev hc hg ih =>
    intro Z hZ hE
    have hE' := opExtends_trans (opExtends_setChain _ _ _) hE
    obtain ⟨hs, hrl⟩ := ih Z hZ hE'
    have hv := opAuthVerified_transfer (opInv_of_opSteps hprev) hZ hE' hc
    refine ⟨SysSteps.authorize a hs hv hg, ?_⟩
    simp only [OpState.setChain_chains]
    rw [mgrs_update]
    exact RunLog.authorize a hrl hv hg
  | @claim Y log clog c f b _ hg ih =>
    intro Z hZ hE
    obtain ⟨hs, hrl⟩ := ih Z hZ (opExtends_trans (opExtends_setChain _ _ _) hE)
    refine ⟨SysSteps.claim hs hg, ?_⟩
    simp only [OpState.setChain_chains]
    rw [mgrs_update]
    exact RunLog.claim hrl hg
  | @initL2 Y log clog c hprev h0 _ =>
    exact absurd h0 (opInitL2_dead (opInv_of_opSteps hprev) c)
  | endBatch _ ih =>
    exact fun Z hZ hE => ih Z hZ (opExtends_trans (opExtends_endBatch _ _) hE)
  | settle _ _ ih =>
    exact fun Z hZ hE => ih Z hZ (opExtends_trans (opExtends_settle _ _) hE)
  | tick _ ht ih =>
    exact fun Z hZ hE => ih Z hZ (opExtends_trans (opExtends_tick _ ht) hE)
  | recordRoot _ ih =>
    exact fun Z hZ hE => ih Z hZ (opExtends_trans (opExtends_recordRoot _) hE)

/-- The embedding at the run's own end state. -/
theorem opRun_embeds {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {Y : OpState} {log : List Obligation} {clog : List CheckedCall}
    (hr : OpSteps h z0 hl cv fh opGenesis Y log clog) :
    SysSteps h z0 hl cv fh Y.history genesisAll Y.chains log (authCalls clog)
      ∧ RunLog h z0 hl cv fh Y.history emptyManagers Y.chains.mgrs clog :=
  opSteps_embed hr Y (opInv_of_opSteps hr) (opExtends_refl Y)

/-! ## Reading the checked-call log -/

lemma op_mem_authCalls {a : AuthCall} {log : List CheckedCall} :
    a ∈ authCalls log ↔ CheckedCall.authorize a ∈ log := by
  induction log with
  | nil => simp
  | cons c t ih =>
    cases c with
    | execute e => simp [ih]
    | authorize a' =>
      rw [authCalls_authorize, List.mem_cons, List.mem_cons, ih]
      constructor
      · rintro (rfl | h)
        · exact Or.inl rfl
        · exact Or.inr h
      · rintro (h | h)
        · injection h with h; exact Or.inl h
        · exact Or.inr h

lemma op_authCalls_append (l₁ l₂ : List CheckedCall) :
    authCalls (l₁ ++ l₂) = authCalls l₁ ++ authCalls l₂ :=
  List.filterMap_append

/-- **EVERY LOGGED CALL CITED A BATCH THAT IS SETTLED IN EVERY EXTENSION.** -/
theorem opLogged_settled {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {Y : OpState} {log : List Obligation} {clog : List CheckedCall}
    (hr : OpSteps h z0 hl cv fh opGenesis Y log clog) :
    ∀ Z, OpExtends Y Z →
      (∀ e, CheckedCall.execute e ∈ clog → ∀ ℓ ∈ e.flow.legs,
          (e.evidence ℓ).1 < (Z.batches ℓ.chain).settled)
        ∧ (∀ a, CheckedCall.authorize a ∈ clog → a.batch < (Z.batches a.missing.chain).settled) := by
  induction hr with
  | refl => exact fun _ _ => ⟨fun _ he => absurd he List.not_mem_nil,
      fun _ ha => absurd ha List.not_mem_nil⟩
  | append _ _ ih => exact fun Z hE => ih Z (opExtends_trans (opExtends_setChain _ _ _) hE)
  | @execute Y log clog e _ hc ih =>
    intro Z hE
    obtain ⟨h1, h2⟩ := ih Z hE
    refine ⟨fun e' he' ℓ hℓ => ?_, fun a ha => ?_⟩
    · rcases List.mem_cons.mp he' with heq | he'
      · injection heq with heq
        subst heq
        exact lt_of_lt_of_le (hc.settled ℓ hℓ) (hE.settled _)
      · exact h1 e' he' ℓ hℓ
    · rcases List.mem_cons.mp ha with heq | ha
      · cases heq
      · exact h2 a ha
  | @authorize Y log clog a R _ hc _ ih =>
    intro Z hE
    have hE' := opExtends_trans (opExtends_setChain _ _ _) hE
    obtain ⟨h1, h2⟩ := ih Z hE'
    refine ⟨fun e' he' ℓ hℓ => ?_, fun a' ha' => ?_⟩
    · rcases List.mem_cons.mp he' with heq | he'
      · cases heq
      · exact h1 e' he' ℓ hℓ
    · rcases List.mem_cons.mp ha' with heq | ha'
      · injection heq with heq
        subst heq
        exact lt_of_lt_of_le hc.settled (hE'.settled _)
      · exact h2 a' ha'
  | claim _ _ ih => exact fun Z hE => ih Z (opExtends_trans (opExtends_setChain _ _ _) hE)
  | initL2 _ _ ih => exact fun Z hE => ih Z (opExtends_trans (opExtends_setChain _ _ _) hE)
  | endBatch _ ih => exact fun Z hE => ih Z (opExtends_trans (opExtends_endBatch _ _) hE)
  | settle _ _ ih => exact fun Z hE => ih Z (opExtends_trans (opExtends_settle _ _) hE)
  | tick _ ht ih => exact fun Z hE => ih Z (opExtends_trans (opExtends_tick _ ht) hE)
  | recordRoot _ ih => exact fun Z hE => ih Z (opExtends_trans (opExtends_recordRoot _) hE)

/-- An `AbsenceBreak` on a settled batch is the same in every extension. -/
lemma opAbsenceBreak_agree {h : Hash} {z0 : UInt256} {hl : LeafHash} {X Y : OpState}
    (hX : OpInv X) (hE : OpExtends X Y) {D : ℕ} {c : Chain} {N : ℕ} {p : ImtProof}
    (hN : N < (X.batches c).settled) :
    AbsenceBreak h z0 hl Y.history D c N p ↔ AbsenceBreak h z0 hl X.history D c N p := by
  obtain ⟨ht, htime, hh⟩ := opHistory_agree hX hE hN
  obtain ⟨hbt, hbh⟩ := opBeginTree_agree hX hE hN
  unfold AbsenceBreak
  rw [ht, htime, hh, hbt, hbh]

/-- An `InclusionBreak` on a settled batch is the same in every extension. -/
lemma opInclusionBreak_agree {h : Hash} {z0 : UInt256} {hl : LeafHash} {X Y : OpState}
    (hX : OpInv X) (hE : OpExtends X Y) {c : Chain} {n : ℕ} {p : ImtProof}
    (hn : n < (X.batches c).settled) :
    InclusionBreak h z0 hl Y.history c n p ↔ InclusionBreak h z0 hl X.history c n p := by
  obtain ⟨ht, -, hh⟩ := opHistory_agree hX hE hn
  unfold InclusionBreak
  rw [ht, hh]

/-! ## The headlines, transferred -/

section Transfers

variable {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue} {fh : FlowHash}
  {Y : OpState} {log : List Obligation} {clog : List CheckedCall}

/-- A logged execution passed the fixed-history gate on the run's history. -/
lemma op_logged_execution_executes (hr : OpSteps h z0 hl cv fh opGenesis Y log clog)
    {e : ExecCall} (he : CheckedCall.execute e ∈ clog) :
    ExecutedViaBy h z0 hl cv fh Y.history e.flow e.evidence e.leg :=
  logged_execution_executes (opRun_embeds hr).2 he

/-- A logged authorization passed the fixed-history checks on the run's history. -/
lemma op_logged_authorize_verified (hr : OpSteps h z0 hl cv fh opGenesis Y log clog)
    {a : AuthCall} (ha : a ∈ authCalls clog) : a.Verified h z0 hl cv fh Y.history :=
  logged_authorize_verified (opRun_embeds hr).2 (op_mem_authCalls.mp ha)

theorem op_executed_freezes_flow_or_break (hr : OpSteps h z0 hl cv fh opGenesis Y log clog)
    {e : ExecCall} (he : CheckedCall.execute e ∈ clog) (o : Obligation)
    (ho : o.flowId = e.flow.flowId) :
    ¬ Refunded Y.chains.mgrs o
      ∨ RefundBreak h z0 hl fh Y.history e.flow e.evidence o (authCalls clog) :=
  executed_freezes_flow_or_break (opHistory_wf (opInv_of_opSteps hr))
    (op_logged_execution_executes hr he) (runLog_reachLog (opRun_embeds hr).2) o ho

theorem op_refunded_leg_missed_deadline_or_break
    (hr : OpSteps h z0 hl cv fh opGenesis Y log clog) {a : AuthCall} (ha : a ∈ authCalls clog) :
    (∀ n, Y.history.time a.missing.chain n ≤ a.flow.deadline →
        legValue cv a.flow a.missing ∉ keys (toAbs (Y.history.tree a.missing.chain n)))
      ∨ AbsenceBreak h z0 hl Y.history a.flow.deadline a.missing.chain a.batch a.proof := by
  have hS := opHistory_wf (opInv_of_opSteps hr)
  have hv := op_logged_authorize_verified hr ha
  by_cases hb : AbsenceBreak h z0 hl Y.history a.flow.deadline a.missing.chain a.batch a.proof
  · exact Or.inr hb
  · refine Or.inl fun n hon hmem => ?_
    rcases member_not_refundable_or_break hS hon hmem a.batch a.proof with hn | hb'
    · exact hn hv.2.2.2
    · exact hb hb'

/-- Every key of a batch's tree is a key of the live tree. -/
lemma op_history_keys_live {Y : OpState} (hY : OpInv Y) (c : Chain) (n : ℕ) :
    keys (toAbs (Y.history.tree c n)) ⊆ keys (toAbs (Y.chains c).tree) := by
  have hS := opHistory_wf hY
  have hlive : Y.history.tree c (max n (Y.batches c).ended) = (Y.chains c).tree := by
    rw [OpState.history_tree, ite_eq_right (by omega)]
  intro v hv
  have := keys_mono_batch hS c (le_max_left n (Y.batches c).ended) hv
  rwa [hlive] at this

/-- **AN EXECUTED LEG WAS APPENDED ON ITS DECLARED CHAIN, OR A LOCATED BREAK.** -/
theorem op_executed_leg_appended_or_break (hr : OpSteps h z0 hl cv fh opGenesis Y log clog)
    {e : ExecCall} (he : CheckedCall.execute e ∈ clog) {ℓ : FlowLeg} (hℓ : ℓ ∈ e.flow.legs) :
    (obligationOf e.flow ℓ ∈ log ∧ stateOf Y.chains.mgrs (obligationOf e.flow ℓ) ≠ .Unset)
      ∨ (∃ o ∈ log, o.chain = ℓ.chain ∧ CommitClash cv (obligationOf e.flow ℓ) o)
      ∨ legValue cv e.flow ℓ = 0
      ∨ InclusionBreak h z0 hl Y.history ℓ.chain (e.evidence ℓ).1 (e.evidence ℓ).2 := by
  have hY := opInv_of_opSteps hr
  obtain ⟨hs, _⟩ := opRun_embeds hr
  obtain ⟨_, hacc⟩ := (op_logged_execution_executes hr he).2.2 ℓ hℓ
  rcases finality_means_membership_or_break hacc with hmem | hb
  · by_cases hv0 : legValue cv e.flow ℓ = 0
    · exact Or.inr (Or.inr (Or.inl hv0))
    · have hkey : cv e.flow.flowId ℓ.bundleHash ∈ keys (toAbs (Y.chains ℓ.chain).tree) :=
        op_history_keys_live hY ℓ.chain _ hmem
      rcases (SystemKeyPinsAppendedLegOrClash h z0 hl cv fh Y.history Y.chains log
          (authCalls clog) hs ℓ.chain e.flow.flowId ℓ.bundleHash hv0 hkey).1 with hm | hcl
      · refine Or.inl ⟨hm, ?_⟩
        have hI := inv_of_steps (sysSteps_chain hs ℓ.chain)
        intro hunset
        exact (hI.mgrUnset e.flow.flowId ℓ.bundleHash).mp hunset
          (mem_filter_chain.mpr ⟨hm, rfl⟩)
      · exact Or.inr (Or.inl hcl)
  · exact Or.inr (Or.inr (Or.inr hb))

/-- **CAPSTONE: AN EXECUTED FLOW'S EVERY LEG IS ESCROWED AND NEVER REFUNDED, OR A LOCATED
BREAK.** -/
theorem op_executed_leg_escrowed_or_break (hr : OpSteps h z0 hl cv fh opGenesis Y log clog)
    {e : ExecCall} (he : CheckedCall.execute e ∈ clog) {ℓ : FlowLeg} (hℓ : ℓ ∈ e.flow.legs) :
    (obligationOf e.flow ℓ ∈ log ∧ stateOf Y.chains.mgrs (obligationOf e.flow ℓ) = .Committed)
      ∨ (∃ o ∈ log, o.chain = ℓ.chain ∧ CommitClash cv (obligationOf e.flow ℓ) o)
      ∨ legValue cv e.flow ℓ = 0
      ∨ InclusionBreak h z0 hl Y.history ℓ.chain (e.evidence ℓ).1 (e.evidence ℓ).2
      ∨ RefundBreak h z0 hl fh Y.history e.flow e.evidence (obligationOf e.flow ℓ)
          (authCalls clog) := by
  rcases op_executed_leg_appended_or_break hr he hℓ with ⟨hm, hne⟩ | hcl | h0 | hb
  · rcases op_executed_freezes_flow_or_break hr he (obligationOf e.flow ℓ) rfl with hnr | hrb
    · refine Or.inl ⟨hm, ?_⟩
      unfold Refunded at hnr
      cases hst : stateOf Y.chains.mgrs (obligationOf e.flow ℓ) with
      | Unset => exact absurd hst hne
      | Committed => rfl
      | Revertable => rw [hst] at hnr; exact absurd (by decide) hnr
      | Reverted => rw [hst] at hnr; exact absurd (by decide) hnr
    · exact Or.inr (Or.inr (Or.inr (Or.inr hrb)))
  · exact Or.inr (Or.inl hcl)
  · exact Or.inr (Or.inr (Or.inl h0))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hb)))

end Transfers

end Contracts.InteropOperational

namespace Contracts.InteropOperational

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.Timeout Contracts.AtomicFlowManager Contracts.Refund Contracts.AppendPath
open Contracts.FlowBinding MerkleSpec.Verifier

/-! ## Certificates -/

theorem OpRunHistoryWf : Properties.OpRunHistoryWf :=
  fun _ _ _ _ _ _ _ _ hr => ⟨opHistory_wf (opInv_of_opSteps hr), fun _ _ => rfl⟩

theorem OpRunRootsAggregateBefore : Properties.OpRunRootsAggregateBefore :=
  fun _ _ _ _ _ _ _ _ hr => opRoots_aggregateBefore (opInv_of_opSteps hr)

theorem OpRunSettledHistoryIsFinal : Properties.OpRunSettledHistoryIsFinal := by
  intro h z0 hl cv fh X Y logX log' clogX clog' hX hXY
  have hE := opExtends_of_opSteps hXY
  exact ⟨fun _ _ hn => opHistory_agree (opInv_of_opSteps hX) hE hn, hE.roots, hE.settled⟩

theorem OpLoggedEvidenceIsSettled : Properties.OpLoggedEvidenceIsSettled :=
  fun _ _ _ _ _ Y _ _ hr => opLogged_settled hr Y (opExtends_refl Y)

theorem IsLastOnTimeDerivedBefore : Properties.IsLastOnTimeDerivedBefore :=
  fun _ _ hagg _ _ _ he => isLastOnTime_of_aggregatesBefore hagg he

theorem AggregatesImpliesAggregatesBefore : Properties.AggregatesImpliesAggregatesBefore :=
  fun _ _ hagg c n hlt => hagg c n (le_of_lt hlt)

theorem OpRunEmbedsInSysSteps : Properties.OpRunEmbedsInSysSteps :=
  fun _ _ _ _ _ _ _ _ hr => (opRun_embeds hr).1

theorem OpRunEmbedsInRunLog : Properties.OpRunEmbedsInRunLog :=
  fun _ _ _ _ _ _ _ _ hr => (opRun_embeds hr).2

theorem OpRunEmbedsInReachLog : Properties.OpRunEmbedsInReachLog :=
  fun _ _ _ _ _ _ _ _ hr => runLog_reachLog (opRun_embeds hr).2

theorem OpPrefixEmbedsInLaterHistory : Properties.OpPrefixEmbedsInLaterHistory :=
  fun _ _ _ _ _ _ Y _ _ _ _ hX hXY =>
    opSteps_embed hX Y (opInv_of_opSteps (opSteps_trans hX hXY)) (opExtends_of_opSteps hXY)

theorem OpExecutedObligationNeverRefundedOrBreak :
    Properties.OpExecutedObligationNeverRefundedOrBreak :=
  fun _ _ _ _ _ _ _ _ hr _ he => op_executed_freezes_flow_or_break hr he _ rfl

theorem OpOneExecutionFreezesTheFlowOrBreak : Properties.OpOneExecutionFreezesTheFlowOrBreak :=
  fun _ _ _ _ _ _ _ _ hr _ he _ _ => op_executed_freezes_flow_or_break hr he _ rfl

theorem OpRefundImpliesOwnFlowTimeoutOrLoggedClash :
    Properties.OpRefundImpliesOwnFlowTimeoutOrLoggedClash :=
  fun _ _ _ _ _ _ _ _ hr _ _ hchk _ hrf =>
    refund_implies_own_flow_timeout_or_logged_clash hchk (runLog_reachLog (opRun_embeds hr).2) hrf

theorem OpExecutedImpliesAllFinalizableOrBreak :
    Properties.OpExecutedImpliesAllFinalizableOrBreak :=
  fun _ _ _ _ _ _ _ _ hr _ hDA _ he other hother =>
    executed_implies_all_finalizable_or_break (opHistory_wf (opInv_of_opSteps hr)) hDA
      (op_logged_execution_executes hr he) other hother

theorem OpSiblingFinalizableNowOrBreak : Properties.OpSiblingFinalizableNowOrBreak := by
  intro h z0 hl cv fh Y log clog hr A hDA e he other hother
  have hS := opHistory_wf (opInv_of_opSteps hr)
  refine ⟨(opLogged_settled hr Y (opExtends_refl Y)).1 e he other hother, ?_⟩
  obtain ⟨hon, hacc⟩ := (op_logged_execution_executes hr he).2.2 other hother
  rcases finality_means_membership_or_break hacc with hmem | hb
  · obtain ⟨i, hi, hacc'⟩ := honest_accepts (h := h) (z0 := z0) (hl := hl) hS hmem
    exact Or.inl ⟨_, hDA _ _ _ hi, hon, hacc'⟩
  · exact Or.inr hb

theorem OpNoneOrAllOrBreakPinned : Properties.OpNoneOrAllOrBreakPinned := by
  intro h z0 hl cv fh Y log clog hr A hDA e he
  have hex := op_logged_execution_executes hr he
  rcases none_or_all_or_break_pinned (fh := fh) (opHistory_wf (opInv_of_opSteps hr)) hDA
      e.flow e.evidence with hfin | hnex | hpin
  · exact Or.inl hfin
  · exact absurd hex (hnex e.leg)
  · exact Or.inr hpin

theorem OpLoggedExecutionExcludesLoggedRefundOrBreak :
    Properties.OpLoggedExecutionExcludesLoggedRefundOrBreak :=
  fun _ _ _ _ _ _ _ _ hr _ he _ ha hid =>
    logged_execution_excludes_logged_refund_or_break (opHistory_wf (opInv_of_opSteps hr))
      (opRun_embeds hr).2 he ha hid

theorem OpExecutedImpliesRealFlowFinalizableOrLoggedClash :
    Properties.OpExecutedImpliesRealFlowFinalizableOrLoggedClash :=
  fun _ _ _ _ _ _ _ _ hr _ hDA _ he _ hc hid =>
    executed_implies_real_flow_finalizable_or_logged_clash (opHistory_wf (opInv_of_opSteps hr))
      hDA (opRun_embeds hr).2 he hc hid

theorem OpRefundedLegMissedDeadlineOrBreak : Properties.OpRefundedLegMissedDeadlineOrBreak :=
  fun _ _ _ _ _ _ _ _ hr _ ha => op_refunded_leg_missed_deadline_or_break hr ha

theorem OpRefundStaysDeserved : Properties.OpRefundStaysDeserved := by
  intro h z0 hl cv fh X Y logX log' clogX clog' hX hXY a ha
  have hr := opSteps_trans hX hXY
  have ha' : a ∈ authCalls (clog' ++ clogX) := by
    rw [op_authCalls_append]
    exact List.mem_append_right _ ha
  have hset : a.batch < (X.batches a.missing.chain).settled :=
    (opLogged_settled hX X (opExtends_refl X)).2 a (op_mem_authCalls.mp ha)
  rcases op_refunded_leg_missed_deadline_or_break hr ha' with hm | hb
  · exact Or.inl hm
  · exact Or.inr ((opAbsenceBreak_agree (opInv_of_opSteps hX) (opExtends_of_opSteps hXY) hset).mp hb)

theorem OpSystemOncePerLeg : Properties.OpSystemOncePerLeg :=
  fun h z0 hl cv fh Y log clog hr =>
    SystemOncePerLeg h z0 hl cv fh Y.history Y.chains log (authCalls clog) (opRun_embeds hr).1

theorem OpRefundedWasAppendedOnce : Properties.OpRefundedWasAppendedOnce :=
  fun h z0 hl cv fh Y log clog hr =>
    SystemRefundedWasAppendedOnce h z0 hl cv fh Y.history Y.chains log (authCalls clog)
      (opRun_embeds hr).1

theorem OpExecutedLegWasAppendedOrBreak : Properties.OpExecutedLegWasAppendedOrBreak :=
  fun _ _ _ _ _ _ _ _ hr _ he _ hℓ => op_executed_leg_appended_or_break hr he hℓ

theorem OpExecutedLegEscrowedAndNotRefundedOrBreak :
    Properties.OpExecutedLegEscrowedAndNotRefundedOrBreak :=
  fun _ _ _ _ _ _ _ _ hr _ he _ hℓ => op_executed_leg_escrowed_or_break hr he hℓ

/-! ## Liveness: once a post-deadline root is recorded, the flow's fate is decided -/

section Liveness

variable {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue} {fh : FlowHash}

/-- The genesis batch settled at time `0`, in every reachable state. -/
lemma op_stamp_zero {Y : OpState} {log : List Obligation} {clog : List CheckedCall}
    (hr : OpSteps h z0 hl cv fh opGenesis Y log clog) (c : Chain) : (Y.batches c).stamp 0 = 0 :=
  (opExtends_of_opSteps hr).stamp c 0 Nat.one_pos

/-- A batch that settles during a continuation carries a time no earlier than the clock at
the continuation's start. -/
theorem opSteps_new_stamps {X Y : OpState} {log : List Obligation} {clog : List CheckedCall}
    (hr : OpSteps h z0 hl cv fh X Y log clog) :
    ∀ c n, (X.batches c).settled ≤ n → n < (Y.batches c).settled →
      X.now ≤ (Y.batches c).stamp n := by
  induction hr with
  | refl => intro c n h1 h2; omega
  | append _ _ ih => exact ih
  | execute _ _ _ ih => exact ih
  | authorize _ _ _ _ _ ih => exact ih
  | claim _ _ ih => exact ih
  | initL2 _ _ ih => exact ih
  | @endBatch Y log clog c' _ ih =>
    intro c n h1 h2
    by_cases hc : c = c'
    · subst hc
      rw [OpState.endBatch_batches_self] at h2 ⊢
      exact ih c n h1 h2
    · rw [OpState.endBatch_batches_other _ hc] at h2 ⊢
      exact ih c n h1 h2
  | @settle Y log clog c' hprev _ ih =>
    intro c n h1 h2
    by_cases hc : c = c'
    · subst hc
      rw [OpState.settle_batches_self] at h2 ⊢
      rw [BatchLog.settle_settled] at h2
      rw [BatchLog.settle_stamp]
      by_cases hn : n = (Y.batches c).settled
      · rw [ite_eq_left hn]
        exact (opExtends_of_opSteps hprev).now
      · rw [ite_eq_right hn]
        exact ih c n h1 (by omega)
    · rw [OpState.settle_batches_other _ hc] at h2 ⊢
      exact ih c n h1 h2
  | tick _ _ ih => exact ih
  | recordRoot _ ih => exact ih

theorem op_on_time_batches_final {X Y : OpState} {logX log' : List Obligation}
    {clogX clog' : List CheckedCall} (hX : OpSteps h z0 hl cv fh opGenesis X logX clogX)
    (hXY : OpSteps h z0 hl cv fh X Y log' clog') {R : SlRoot} (hR : R ∈ X.roots) {D : ℕ}
    (hD : D < R.created) {c : Chain} {n : ℕ} (hn : n < (Y.batches c).settled)
    (hle : Y.history.time c n ≤ D) : n < (X.batches c).settled := by
  by_contra hnot
  push Not at hnot
  have hstamp := opSteps_new_stamps hXY c n hnot hn
  rw [opHistory_time_settled hn] at hle
  have hpast := (opInv_of_opSteps hX).rootsPast R hR
  omega

theorem op_finalized_flow_executable {Y : OpState} {log : List Obligation}
    {clog : List CheckedCall} (hr : OpSteps h z0 hl cv fh opGenesis Y log clog) {F : Flow}
    (hchk : FlowIdChecked fh F)
    (hin : ∀ ℓ ∈ F.legs, ∃ n, n < (Y.batches ℓ.chain).settled
      ∧ Y.history.time ℓ.chain n ≤ F.deadline
      ∧ legValue cv F ℓ ∈ keys (toAbs (Y.history.tree ℓ.chain n)))
    {leg : FlowLeg} (hleg : leg ∈ F.legs) :
    ∃ e : ExecCall, e.flow = F ∧ e.leg = leg ∧ OpSteps h z0 hl cv fh Y Y [] [.execute e] := by
  have hS := opHistory_wf (opInv_of_opSteps hr)
  choose! n hn using hin
  have hidx : ∀ ℓ ∈ F.legs, ∃ i, i < (Y.history.tree ℓ.chain (n ℓ)).leafCount
      ∧ Accepts h z0 hl Y.history ℓ.chain (n ℓ) (legValue cv F ℓ)
          (honestProof h z0 hl Y.history ℓ.chain (n ℓ) i) :=
    fun ℓ hℓ => honest_accepts hS (hn ℓ hℓ).2.2
  choose! i hi using hidx
  refine ⟨⟨F, fun ℓ => (n ℓ, honestProof h z0 hl Y.history ℓ.chain (n ℓ) (i ℓ)), leg⟩,
    rfl, rfl, ?_⟩
  exact OpSteps.execute _ OpSteps.refl
    ⟨⟨hleg, hchk, fun ℓ hℓ => ⟨(hn ℓ hℓ).2.1, (hi ℓ hℓ).2⟩⟩, fun ℓ hℓ => (hn ℓ hℓ).1⟩

/-- The least batch satisfying a property, below a given one that does. -/
lemma exists_least_below {P : ℕ → Prop} [DecidablePred P] {U : ℕ} (hU : P U) :
    ∃ N, P N ∧ N ≤ U ∧ ∀ m < N, ¬ P m :=
  ⟨Nat.find ⟨U, hU⟩, Nat.find_spec ⟨U, hU⟩, Nat.find_min' ⟨U, hU⟩ hU,
    fun _ hm => Nat.find_min ⟨U, hU⟩ hm⟩

theorem op_timed_out_leg_refundable {Y : OpState} {log : List Obligation}
    {clog : List CheckedCall} (hr : OpSteps h z0 hl cv fh opGenesis Y log clog) {F : Flow}
    {missing : FlowLeg} {R : SlRoot} (hchk : FlowIdChecked fh F) (hmiss : missing ∈ F.legs)
    (hv0 : legValue cv F missing ≠ 0) (hR : R ∈ Y.roots) (hD : F.deadline < R.created)
    (habs : ∀ n, n < (Y.batches missing.chain).settled →
      Y.history.time missing.chain n ≤ F.deadline →
        legValue cv F missing ∉ keys (toAbs (Y.history.tree missing.chain n)))
    {leg : FlowLeg} (hleg : leg ∈ F.legs)
    (hg : AuthorizeGuard (Y.chains leg.chain).mgr F.flowId leg.bundleHash) :
    ∃ a : AuthCall, a.flow = F ∧ a.leg = leg ∧ a.missing = missing
      ∧ OpSteps h z0 hl cv fh Y
          (Y.setChain leg.chain
            ⟨(Y.chains leg.chain).mgr.set F.flowId leg.bundleHash .Revertable,
              (Y.chains leg.chain).tree⟩)
          [] [.authorize a] := by
  have hY := opInv_of_opSteps hr
  have hS := opHistory_wf hY
  have hU : R.upTo missing.chain < (Y.batches missing.chain).settled :=
    hY.rootsSettled R hR missing.chain
  -- the honest absence proof against any on-time settled batch
  have hproof : ∀ n, n < (Y.batches missing.chain).settled →
      Y.history.time missing.chain n ≤ F.deadline →
      ∃ p : ImtProof, AbsenceAccepted h z0 hl (Y.history.tree missing.chain n)
        (Y.history.height missing.chain n) (legValue cv F missing) p := by
    intro n hn hon
    obtain ⟨ℓ, idx, hN⟩ := non_inclusion_complete (h := h) (z0 := z0) (hl := hl)
      (valid_batch hS missing.chain n) (hS.capacity missing.chain n) hv0 (habs n hn hon)
    exact ⟨⟨ℓ, idx, honestSibs h z0 (leafHashes hl (Y.history.tree missing.chain n)) idx,
      Y.history.height missing.chain n⟩, hN⟩
  -- the batch and the branch
  have hverified : ∃ (N : ℕ) (p : ImtProof), N < (Y.batches missing.chain).settled
      ∧ LegRefundableVerifiedBy h z0 hl cv Y.history R F missing N p := by
    by_cases hlast : Y.history.time missing.chain (R.upTo missing.chain) ≤ F.deadline
    · -- END branch at the root's last batch
      obtain ⟨p, hp⟩ := hproof _ hU hlast
      exact ⟨R.upTo missing.chain, p, hU, Or.inr ⟨⟨hD, hlast, rfl⟩, hp⟩⟩
    · -- BEGIN branch at the first late batch inside the root
      push Not at hlast
      obtain ⟨N, hlate, hNle, hmin⟩ := exists_least_below
        (P := fun m => F.deadline < Y.history.time missing.chain m) hlast
      have hzero : Y.history.time missing.chain 0 = 0 := by
        rw [opHistory_time_settled (hY.settledPos _)]
        exact op_stamp_zero hr _
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := by
        rcases N with _ | N'
        · exact absurd (hzero ▸ hlate) (Nat.not_lt_zero _)
        · exact ⟨N', rfl⟩
      have hon : Y.history.time missing.chain N' ≤ F.deadline :=
        not_lt.mp (hmin N' (Nat.lt_succ_self N'))
      obtain ⟨p, hp⟩ := hproof N' (by omega) hon
      exact ⟨N' + 1, p, by omega, Or.inl ⟨⟨hD, hlate⟩, hp⟩⟩
  obtain ⟨N, p, hN, hv⟩ := hverified
  exact ⟨⟨F, leg, missing, N, p⟩, rfl, rfl, rfl,
    OpSteps.authorize ⟨F, leg, missing, N, p⟩ R OpSteps.refl ⟨hR, hchk, hleg, hmiss, hN, hv⟩ hg⟩

end Liveness

theorem OpFinalizedFlowIsExecutable : Properties.OpFinalizedFlowIsExecutable :=
  fun _ _ _ _ _ _ _ _ hr _ hchk hin _ hleg => op_finalized_flow_executable hr hchk hin hleg

theorem OpTimedOutLegIsRefundable : Properties.OpTimedOutLegIsRefundable :=
  fun _ _ _ _ _ _ _ _ hr _ _ _ hchk hmiss hv0 hR hD habs _ hleg hg =>
    op_timed_out_leg_refundable hr hchk hmiss hv0 hR hD habs hleg hg

theorem OpOnTimeBatchesFinalAfterRoot : Properties.OpOnTimeBatchesFinalAfterRoot :=
  fun _ _ _ _ _ _ _ _ _ _ _ hX hXY _ hR _ hD _ _ hn hle =>
    op_on_time_batches_final hX hXY hR hD hn hle

theorem OpFlowFateDecidedAfterRoot : Properties.OpFlowFateDecidedAfterRoot := by
  intro h z0 hl cv fh Y log clog hr F R hchk hwf hR hD
  by_cases hall : ∀ ℓ ∈ F.legs, ∃ n, n < (Y.batches ℓ.chain).settled
      ∧ Y.history.time ℓ.chain n ≤ F.deadline
      ∧ legValue cv F ℓ ∈ keys (toAbs (Y.history.tree ℓ.chain n))
  · exact Or.inl fun leg hleg => op_finalized_flow_executable hr hchk hall hleg
  · push Not at hall
    obtain ⟨missing, hmiss, habs⟩ := hall
    exact Or.inr ⟨missing, hmiss, fun leg hleg hg =>
      op_timed_out_leg_refundable hr hchk hmiss (hwf missing hmiss) hR hD habs hleg hg⟩

/-! ## Countermodels -/

theorem FixedHistoryAdmitsUnescrowedExecution :
    Properties.FixedHistoryAdmitsUnescrowedExecution := by
  intro h z0 hl
  have h1 : (0 : UInt256) < 1 := by decide
  obtain ⟨hex, hnb⟩ := subsetFlow_executes h z0 hl lengthFlowHash lengthFlowHash_checks_subset
  let e : ExecCall :=
    ⟨subsetFlow 0 1, fun _ => (0, honestProof h z0 hl (mixedSystem 1) 0 0 1), ⟨0, 1⟩⟩
  refine ⟨fun _ _ => 1, lengthFlowHash, mixedSystem 1, emptyManagers, [.execute e], e,
    mixedSystem_wf h1, RunLog.execute e RunLog.refl hex, List.mem_singleton_self _, ?_⟩
  intro ℓ hℓ
  obtain rfl : ℓ = ⟨0, 1⟩ := List.mem_singleton.mp hℓ
  exact ⟨rfl, by simp [legValue], hnb⟩

/-- Record the root at time `0`, then end and settle chain `0`'s batch 1, also at time `0`. -/
def opSameTimeState : OpState := (opGenesis.recordRoot.endBatch 0).settle 0

lemma opSameTime_run (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) :
    OpSteps h z0 hl cv fh opGenesis opSameTimeState [] [] :=
  OpSteps.settle (OpSteps.endBatch (OpSteps.recordRoot OpSteps.refl)) (by decide)

theorem OpRootMayMissSameTimeBatch : Properties.OpRootMayMissSameTimeBatch := by
  intro h z0 hl cv fh
  have r := opSameTime_run h z0 hl cv fh
  have hR : opGenesis.currentRoot ∈ opSameTimeState.roots := List.mem_singleton_self _
  refine ⟨_, _, _, opGenesis.currentRoot, r, hR,
    opRoots_aggregateBefore (opInv_of_opSteps r) _ hR, fun hagg => ?_⟩
  have := hagg 0 1 (by decide)
  exact absurd this (by decide)

/-! ## The honest run

Commit value `bundleCv` (a leg's bundle hash) and `lengthFlowHash` (one-leg flows have id
`0`, the others id `1`).  Two flows: `subsetFlow 0 1` (one leg `⟨0, 1⟩`, id `0`, deadline
`0`) and `mixedFlow 1 1 2` (legs `⟨0, 1⟩`, `⟨1, 2⟩`, id `1`, deadline `0`).

1. Chain `0` appends `⟨0, 1, 0⟩`, ends its batch 1 and settles it at time `0`.
2. `subsetFlow 0 1` executes on the honest proof against that settled batch.
3. The clock moves to `1`.  Chain `1` appends `⟨1, 2, 1⟩` (too late for deadline `0`),
   ends its batch 1 and settles it at time `1`.
4. The root is recorded at time `1`, the clock moves to `2`, and leg `⟨1, 2⟩` of
   `mixedFlow 1 1 2` is authorized for refund on the BEGIN branch at chain `1`'s late batch
   1, with the honest absence proof against batch 0 (`setup`); then it is claimed. -/

/-- After `append(0, 1, _, 0)` on chain `0`. -/
def opHonest1 : OpState := opGenesis.setChain 0 (genesis.appended bundleCv 0 1 0)
/-- Chain `0`'s batch 1 ends. -/
def opHonest2 : OpState := opHonest1.endBatch 0
/-- …and settles at time `0`. -/
def opHonest3 : OpState := opHonest2.settle 0
/-- The clock moves to `1`. -/
def opHonest4 : OpState := opHonest3.tick 1
/-- After `append(1, 2, _, 0)` on chain `1`. -/
def opHonest5 : OpState := opHonest4.setChain 1 (genesis.appended bundleCv 1 2 0)
/-- Chain `1`'s batch 1 ends. -/
def opHonest6 : OpState := opHonest5.endBatch 1
/-- …and settles at time `1`. -/
def opHonest7 : OpState := opHonest6.settle 1
/-- The root is recorded at time `1`, and the clock moves to `2`. -/
def opHonest8 : OpState := opHonest7.recordRoot.tick 2
/-- Leg `⟨1, 2⟩` is authorized for refund. -/
def opHonest9 : OpState :=
  opHonest8.setChain 1 ⟨(opHonest8.chains 1).mgr.set 1 2 .Revertable, (opHonest8.chains 1).tree⟩
/-- …and claimed. -/
def opHonest10 : OpState :=
  opHonest9.setChain 1 ⟨(opHonest9.chains 1).mgr.set 1 2 .Reverted, (opHonest9.chains 1).tree⟩

/-- The root the refund resolves against. -/
def opHonestRoot : SlRoot := opHonest7.currentRoot

/-- The execution: `subsetFlow 0 1` on the honest proof of leaf 1 of chain `0`'s batch 1. -/
def opHonestExec (h : Hash) (z0 : UInt256) (hl : LeafHash) : ExecCall :=
  ⟨subsetFlow 0 1, fun _ => (1, honestProof h z0 hl opHonest3.history 0 1 1), ⟨0, 1⟩⟩

/-- The refund authorization: leg `⟨1, 2⟩` of `mixedFlow 1 1 2`, its own absence at batch 1. -/
def opHonestAuth (h : Hash) (z0 : UInt256) (hl : LeafHash) : AuthCall :=
  ⟨mixedFlow 1 1 2, ⟨1, 2⟩, ⟨1, 2⟩, 1, setupAbsence h z0 hl⟩

lemma opHonest3_tree : opHonest3.history.tree 0 1 = insert setup 1 0 := rfl

lemma opHonest_pre (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    OpSteps h z0 hl bundleCv lengthFlowHash opGenesis opHonest3 [⟨0, 1, 0⟩] [] := by
  have r1 : OpSteps h z0 hl bundleCv lengthFlowHash opGenesis opHonest1 [⟨0, 1, 0⟩] [] :=
    OpSteps.append (c := 0) (f := 0) (b := 1) (hint := 0) (low := 0) OpSteps.refl
      (append_01_genesis rfl)
  exact OpSteps.settle (OpSteps.endBatch r1) (by decide)

lemma opHonest_exec_checks (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    OpExecChecks h z0 hl bundleCv lengthFlowHash opHonest3 (opHonestExec h z0 hl) := by
  have hS : Wf opHonest3.history := opHistory_wf (opInv_of_opSteps (opHonest_pre h z0 hl))
  refine ⟨⟨List.mem_singleton_self _, lengthFlowHash_checks_subset, fun ℓ hℓ => ?_⟩,
    fun ℓ hℓ => ?_⟩
  · obtain rfl : ℓ = ⟨0, 1⟩ := List.mem_singleton.mp hℓ
    refine ⟨show opHonest3.history.time 0 1 ≤ 0 by decide, honestProof_accepts hS ?_ ?_⟩
    · show 1 < (opHonest3.history.tree 0 1).leafCount
      rw [opHonest3_tree, insertSetup_leafCount]; norm_num
    · show ((opHonest3.history.tree 0 1).leaf 1).value = bundleCv 0 1
      rw [opHonest3_tree, insertSetup_leaf_one_value]; rfl
  · obtain rfl : ℓ = ⟨0, 1⟩ := List.mem_singleton.mp hℓ
    show 1 < (opHonest3.batches 0).settled
    decide

lemma opHonest_seg1 (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    OpSteps h z0 hl bundleCv lengthFlowHash opGenesis opHonest3 [⟨0, 1, 0⟩]
      [.execute (opHonestExec h z0 hl)] :=
  OpSteps.execute _ (opHonest_pre h z0 hl) (opHonest_exec_checks h z0 hl)

lemma opHonest4_chain_one : opHonest4.chains 1 = genesis := by
  show genesisAll.update 0 (genesis.appended bundleCv 0 1 0) 1 = genesis
  exact update_other _ _ (by decide : (1 : Chain) ≠ 0)

lemma opHonest_mid (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    OpSteps h z0 hl bundleCv lengthFlowHash opHonest3 opHonest8 [⟨1, 2, 1⟩] [] := by
  have r4 : OpSteps h z0 hl bundleCv lengthFlowHash opHonest3 opHonest4 [] [] :=
    OpSteps.tick OpSteps.refl (by decide)
  have happ : AppendSucceeds bundleCv (opHonest4.chains 1) 1 2 0 0 := by
    rw [opHonest4_chain_one]
    exact ⟨rfl, by unfold Initialized; decide, by decide, rfl, by decide, by decide, by decide⟩
  have r5 := OpSteps.append (c := 1) (f := 1) (b := 2) (hint := 0) (low := 0) r4 happ
  rw [opHonest4_chain_one] at r5
  have r7 := OpSteps.settle (c := 1) (OpSteps.endBatch (c := 1) r5) (by decide)
  exact OpSteps.tick (OpSteps.recordRoot r7) (by decide)

lemma opHonest8_tree_one : opHonest8.history.tree 1 0 = setup := rfl

lemma opHonest_auth_checks (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    OpAuthChecks h z0 hl bundleCv lengthFlowHash opHonest8 (opHonestAuth h z0 hl) opHonestRoot := by
  have hmem : (⟨1, 2⟩ : FlowLeg) ∈ (mixedFlow 1 1 2).legs := by simp [mixedFlow]
  refine ⟨List.mem_singleton_self _, lengthFlowHash_checks_mixed, hmem, hmem,
    show 1 < (opHonest8.batches 1).settled by decide, ?_⟩
  refine Or.inl ⟨⟨show (0 : ℕ) < 1 by decide, show 0 < opHonest8.history.time 1 1 by decide⟩, ?_⟩
  show AbsenceAccepted h z0 hl (opHonest8.history.tree 1 0) (opHonest8.history.height 1 0)
    (bundleCv 1 2) (setupAbsence h z0 hl)
  rw [show opHonest8.history.height 1 0 = 0 from by decide, opHonest8_tree_one]
  exact setup_absence_accepted h z0 hl (by decide)

/-- The refund and the claim, from the state where the root is recorded. -/
lemma opHonest_tail (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    OpSteps h z0 hl bundleCv lengthFlowHash opHonest8 opHonest10 []
      [.authorize (opHonestAuth h z0 hl)] := by
  have r9 := OpSteps.authorize (opHonestAuth h z0 hl) opHonestRoot OpSteps.refl
    (opHonest_auth_checks h z0 hl)
    (show (opHonest8.chains 1).mgr.legState 1 2 = .Committed by decide)
  exact OpSteps.claim (c := 1) (f := 1) (b := 2) r9
    (show (opHonest9.chains 1).mgr.legState 1 2 = .Revertable by decide)

lemma opHonest_seg2 (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    OpSteps h z0 hl bundleCv lengthFlowHash opHonest3 opHonest10 [⟨1, 2, 1⟩]
      [.authorize (opHonestAuth h z0 hl)] :=
  opSteps_trans (opHonest_mid h z0 hl) (opHonest_tail h z0 hl)

theorem OpHonestRunWitness : Properties.OpHonestRunWitness := by
  intro h z0 hl
  have r1 := opHonest_seg1 h z0 hl
  have r2 := opHonest_seg2 h z0 hl
  have r := opSteps_trans r1 r2
  have hI3 := opInv_of_opSteps r1
  have hE := opExtends_of_opSteps r2
  have hmemE : CheckedCall.execute (opHonestExec h z0 hl) ∈
      [CheckedCall.authorize (opHonestAuth h z0 hl)] ++ [.execute (opHonestExec h z0 hl)] := by
    simp
  have hmemA : opHonestAuth h z0 hl ∈
      authCalls ([CheckedCall.authorize (opHonestAuth h z0 hl)] ++ [.execute (opHonestExec h z0 hl)]) := by
    simp
  -- the inclusion proof the execution submitted carries no break, at the end state too
  have hnbI : ¬ InclusionBreak h z0 hl opHonest10.history 0 1
      (honestProof h z0 hl opHonest3.history 0 1 1) := by
    rw [opInclusionBreak_agree hI3 hE (by decide)]
    exact honestProof_no_break h z0 hl _ 0 1 1 (by rw [opHonest3_tree, insertSetup_leafCount]; norm_num)
  have hnbA : ¬ AbsenceBreak h z0 hl opHonest10.history (mixedFlow 1 1 2).deadline 1 1
      (setupAbsence h z0 hl) :=
    setupAbsence_no_break (N := 0) (by decide) rfl (by decide)
  -- the executed obligation is not the refunded one
  have hneq : obligationOf (opHonestAuth h z0 hl).flow (opHonestAuth h z0 hl).leg
      ≠ obligationOf (subsetFlow 0 1) ⟨0, 1⟩ :=
    show (⟨1, 2, 1⟩ : Obligation) ≠ ⟨0, 1, 0⟩ by decide
  have hnoRB : ¬ RefundBreak h z0 hl lengthFlowHash opHonest10.history (subsetFlow 0 1)
      (opHonestExec h z0 hl).evidence (obligationOf (subsetFlow 0 1) ⟨0, 1⟩)
      (authCalls ([CheckedCall.authorize (opHonestAuth h z0 hl)]
        ++ [.execute (opHonestExec h z0 hl)])) := by
    intro hb
    cases hb with
    | flowIdClash a ha hobl _ =>
      simp only [op_authCalls_append, authCalls_authorize, authCalls_execute, authCalls_nil,
        List.append_nil, List.mem_singleton] at ha
      subst ha; exact hneq hobl
    | inclusion a ha hobl _ _ =>
      simp only [op_authCalls_append, authCalls_authorize, authCalls_execute, authCalls_nil,
        List.append_nil, List.mem_singleton] at ha
      subst ha; exact hneq hobl
    | absence a ha hobl _ _ =>
      simp only [op_authCalls_append, authCalls_authorize, authCalls_execute, authCalls_nil,
        List.append_nil, List.mem_singleton] at ha
      subst ha; exact hneq hobl
  have hDA := honestAccess_dataAvailable h z0 hl opHonest10.history
  refine ⟨bundleCv, lengthFlowHash, opHonest3, opHonest10, [⟨0, 1, 0⟩], [⟨1, 2, 1⟩],
    [.execute (opHonestExec h z0 hl)], [.authorize (opHonestAuth h z0 hl)],
    opHonestExec h z0 hl, opHonestAuth h z0 hl, r1, r2, r, List.mem_singleton_self _,
    List.mem_singleton_self _, show (1 : UInt256) ≠ 0 by decide, hDA, ?_, ?_,
    lengthFlowHash_checks_mixed, by simp [opHonestAuth, mixedFlow],
    show (opHonest10.chains 1).mgr.legState 1 2 = .Reverted by decide, hnbA, ?_, ?_,
    by simp [opHonest10, opHonest9, opHonest8], ?_⟩
  · intro ℓ hℓ
    obtain rfl : ℓ = ⟨0, 1⟩ := List.mem_singleton.mp hℓ
    refine ⟨show (⟨0, 1, 0⟩ : Obligation) ∈ [⟨1, 2, 1⟩] ++ [⟨0, 1, 0⟩] by decide,
      show (opHonest10.chains 0).mgr.legState 0 1 = .Committed by decide, ?_,
      show bundleCv 0 1 ≠ 0 by decide, hnbI, hnoRB⟩
    rintro ⟨o, ho, hch, hne, _⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ho
    rcases ho with rfl | rfl
    · exact absurd hch (by decide)
    · exact hne rfl
  · intro other hother
    rcases OpExecutedImpliesAllFinalizableOrBreak h z0 hl bundleCv lengthFlowHash _ _ _ r
        _ hDA _ hmemE other hother with hf | hb
    · exact hf
    · obtain rfl : other = ⟨0, 1⟩ := List.mem_singleton.mp hother
      exact absurd hb hnbI
  · rcases op_refunded_leg_missed_deadline_or_break r hmemA with hm | hb
    · exact hm
    · exact absurd hb hnbA
  · rintro ⟨a', ha', _, hcl⟩
    simp only [op_authCalls_append, authCalls_authorize, authCalls_execute, authCalls_nil,
      List.append_nil, List.mem_singleton] at ha'
    subst ha'
    exact hcl.1 rfl
  · intro R hR c n hle
    have hroots : opHonest10.roots = [opHonestRoot] := rfl
    rw [hroots, List.mem_singleton] at hR
    subst hR
    show n ≤ (opHonest7.batches c).settled - 1
    have hbat : opHonest10.batches = opHonest7.batches := rfl
    have hnow : opHonest10.now = 2 := rfl
    rw [OpState.history_time, hbat, hnow] at hle
    by_cases hn : n < (opHonest7.batches c).settled
    · omega
    · rw [ite_eq_right hn] at hle
      exact absurd hle (by decide)

theorem OpLivenessWitness : Properties.OpLivenessWitness := by
  intro h z0 hl
  have r8 := opSteps_trans (opHonest_seg1 h z0 hl) (opHonest_mid h z0 hl)
  refine ⟨bundleCv, lengthFlowHash, opHonest8, opHonest10, _, _, _, _, opHonestRoot, r8,
    opHonest_tail h z0 hl, List.cons_ne_nil _ _, List.mem_singleton_self _,
    show (0 : ℕ) < 1 from Nat.one_pos, lengthFlowHash_checks_subset, ?_, ?_,
    lengthFlowHash_checks_mixed, ?_, ?_,
    show (opHonest8.chains 1).mgr.legState 1 2 = .Committed by decide⟩
  · intro ℓ hℓ
    obtain rfl : ℓ = ⟨0, 1⟩ := List.mem_singleton.mp hℓ
    show bundleCv 0 1 ≠ 0
    decide
  · intro ℓ hℓ
    obtain rfl : ℓ = ⟨0, 1⟩ := List.mem_singleton.mp hℓ
    refine ⟨1, show 1 < (opHonest8.batches 0).settled by decide,
      show opHonest8.history.time 0 1 ≤ 0 by decide, ?_⟩
    show (1 : UInt256) ∈ keys (toAbs (insert setup 1 0))
    exact mem_insertSetup (by decide)
  · intro ℓ hℓ
    have hℓ' : ℓ = ⟨0, 1⟩ ∨ ℓ = ⟨1, 2⟩ := by simpa [mixedFlow] using hℓ
    rcases hℓ' with rfl | rfl
    · show bundleCv 1 1 ≠ 0
      decide
    · show bundleCv 1 2 ≠ 0
      decide
  · intro n hn hon
    have hn' : n < 2 := hn
    interval_cases n
    · show (2 : UInt256) ∉ keys (toAbs (opHonest8.history.tree 1 0))
      rw [opHonest8_tree_one]
      exact not_mem_setup (by decide)
    · exact absurd hon (show ¬ opHonest8.history.time 1 1 ≤ 0 by decide)

/-! ## The padding bug as an operational run

At the extraction pin the IMT pads with `hashLeaf({0,0,0})`, so an empty slot "holds" the
sentinel leaf (`Contracts.InteropCommitmentTree.Properties.PaddingCollisionRefundsDeliveredLeg`).
Here it is replayed operationally, on settled batches and a recorded root. -/

/-- Commit value `a` for bundle `0` and `b` for every other bundle. -/
def opPadCv (a b : UInt256) : CommitValue := fun _ bh => if bh = 0 then a else b

/-- After `append(0, 0, _, 0)` on chain `0`: commit value `a`. -/
def opPad1 (a b : UInt256) : OpState := opGenesis.setChain 0 (genesis.appended (opPadCv a b) 0 0 0)
/-- After `append(0, 1, _, 1)` on chain `0`: commit value `b`. -/
def opPad2 (a b : UInt256) : OpState :=
  (opPad1 a b).setChain 0 (((opPad1 a b).chains 0).appended (opPadCv a b) 0 1 1)
/-- Chain `0`'s batch 1 ends and settles at time `0`. -/
def opPad3 (a b : UInt256) : OpState := ((opPad2 a b).endBatch 0).settle 0
/-- The clock moves to `1` and the root is recorded. -/
def opPad4 (a b : UInt256) : OpState := ((opPad3 a b).tick 1).recordRoot
/-- The executed leg `⟨0, 0⟩` is authorized for refund. -/
def opPad5 (a b : UInt256) : OpState :=
  (opPad4 a b).setChain 0 ⟨((opPad4 a b).chains 0).mgr.set 0 0 .Revertable, ((opPad4 a b).chains 0).tree⟩

/-- The root the forged refund resolves against: created at `1`, chain `0`'s last batch 1. -/
def opPadRoot (a b : UInt256) : SlRoot := ((opPad3 a b).tick 1).currentRoot

/-- The honest inclusion proof of leaf 1 (value `a`) of `threeLeafTree a b`, at height 2. -/
def opPadProof (h : Hash) (hl : LeafHash) (a b : UInt256) : ImtProof :=
  ⟨(threeLeafTree a b).leaf 1, 1, honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 1, 2⟩

/-- The forged absence proof: the sentinel at the empty slot 3. -/
def opPadForged (h : Hash) (hl : LeafHash) (a b : UInt256) : ImtProof :=
  ⟨⟨0, 0, 0⟩, 3, honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3, 2⟩

/-- The execution of the one-leg flow `subsetFlow 0 0` (commit value `a`) against batch 1. -/
def opPadExec (h : Hash) (hl : LeafHash) (a b : UInt256) : ExecCall :=
  ⟨subsetFlow 0 0, fun _ => (1, opPadProof h hl a b), ⟨0, 0⟩⟩

/-- The forged refund of the same leg, on the END branch at batch 1. -/
def opPadAuth (h : Hash) (hl : LeafHash) (a b : UInt256) : AuthCall :=
  ⟨subsetFlow 0 0, ⟨0, 0⟩, ⟨0, 0⟩, 1, opPadForged h hl a b⟩

lemma opPadCv_zero (a b : UInt256) : opPadCv a b 0 0 = a := rfl

lemma opPadCv_one (a b : UInt256) : opPadCv a b 0 1 = b := by
  show (if (1 : UInt256) = 0 then a else b) = b
  exact ite_eq_right (by decide)

lemma opPad3_tree (a b : UInt256) : (opPad3 a b).history.tree 0 1 = threeLeafTree a b := by
  show insert (insert setup (opPadCv a b 0 0) 0) (opPadCv a b 0 1) 1 = insert (insert setup a 0) b 1
  rw [opPadCv_zero, opPadCv_one]

lemma opPad3_height (a b : UInt256) : (opPad3 a b).history.height 0 1 = 2 := by
  rw [OpState.history_height, opPad3_tree]
  rfl

/-- A guarded insert passes the contract's checks with its own low leaf as the hint. -/
lemma opInsertSucceeds_of_guard {T : Tree} {v : UInt256} {low : ℕ} (hg : InsertGuard T v low) :
    InsertSucceeds T v low low := by
  refine ⟨hg.initialized, hg.nonzero, hg.fresh, hg.inBounds, hg.lowBelow, ?_⟩
  apply lowSearch_stop
  rintro ⟨hne, hlt⟩
  rcases hg.window with h0 | hle
  · exact hne h0
  · exact absurd hle (not_le.mpr hlt)

lemma opPad_pre (h : Hash) (hl : LeafHash) (a b : UInt256) (ha : 0 < a) (hab : a < b) :
    OpSteps h (hl ⟨0, 0, 0⟩) hl (opPadCv a b) (honestFlowHash (subsetFlow 0 0)) opGenesis
      (opPad3 a b) [⟨0, 1, 0⟩, ⟨0, 0, 0⟩] [] := by
  obtain ⟨hg1, hg2⟩ := threeLeafTree_guards ha hab
  have happ1 : AppendSucceeds (opPadCv a b) (opGenesis.chains 0) 0 0 0 0 :=
    ⟨rfl, opInsertSucceeds_of_guard (by rw [opPadCv_zero]; exact hg1)⟩
  have r1 := OpSteps.append (c := 0) (f := 0) (b := 0) (hint := 0) (low := 0)
    (OpSteps.refl (h := h) (z0 := hl ⟨0, 0, 0⟩) (hl := hl)
      (fh := honestFlowHash (subsetFlow 0 0))) happ1
  have happ2 : AppendSucceeds (opPadCv a b) ((opPad1 a b).chains 0) 0 1 1 1 := by
    refine ⟨show (Contracts.AtomicFlowManager.empty.set 0 0 .Committed).legState 0 1 = .Unset
      by decide, opInsertSucceeds_of_guard ?_⟩
    show InsertGuard (insert setup (opPadCv a b 0 0) 0) (opPadCv a b 0 1) 1
    rw [opPadCv_zero, opPadCv_one]
    exact hg2
  have r2 := OpSteps.append (c := 0) (f := 0) (b := 1) (hint := 1) (low := 1) r1 happ2
  exact OpSteps.settle (OpSteps.endBatch r2) (show (1 : ℕ) < 2 from Nat.one_lt_two)

lemma opPad_exec_checks (h : Hash) (hl : LeafHash) (a b : UInt256) (ha : 0 < a) (hab : a < b) :
    OpExecChecks h (hl ⟨0, 0, 0⟩) hl (opPadCv a b) (honestFlowHash (subsetFlow 0 0)) (opPad3 a b)
      (opPadExec h hl a b) := by
  obtain ⟨_, hI, _⟩ := proofs_exclusive_or_break_satisfiable h hl a b ha hab
  refine ⟨⟨List.mem_singleton_self _, (honest_flowHash_no_clash _).1, fun ℓ hℓ => ?_⟩,
    fun ℓ hℓ => ?_⟩
  · obtain rfl : ℓ = ⟨0, 0⟩ := List.mem_singleton.mp hℓ
    refine ⟨show (opPad3 a b).history.time 0 1 ≤ 0 from le_of_eq rfl, ?_⟩
    show InclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl ((opPad3 a b).history.tree 0 1)
      ((opPad3 a b).history.height 0 1)) (opPadCv a b 0 0) _ _ _ _
    rw [opPad3_tree, opPad3_height, opPadCv_zero]
    exact hI
  · obtain rfl : ℓ = ⟨0, 0⟩ := List.mem_singleton.mp hℓ
    show 1 < ((opPad3 a b).batches 0).settled
    exact Nat.lt_succ_self 1

lemma opPad_auth_checks (h : Hash) (hl : LeafHash) (a b : UInt256) (ha : 0 < a) (hab : a < b) :
    OpAuthChecks h (hl ⟨0, 0, 0⟩) hl (opPadCv a b) (honestFlowHash (subsetFlow 0 0)) (opPad4 a b)
      (opPadAuth h hl a b) (opPadRoot a b) := by
  obtain ⟨_, _, hN⟩ := proofs_exclusive_or_break_satisfiable h hl a b ha hab
  refine ⟨List.mem_singleton_self _, (honest_flowHash_no_clash _).1, List.mem_singleton_self _,
    List.mem_singleton_self _, show 1 < ((opPad4 a b).batches 0).settled from Nat.lt_succ_self 1,
    Or.inr ⟨⟨show (0 : ℕ) < 1 from Nat.one_pos, show (opPad4 a b).history.time 0 1 ≤ 0
      from le_of_eq rfl, rfl⟩, ?_⟩⟩
  show NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl ((opPad3 a b).history.tree 0 1)
    ((opPad3 a b).history.height 0 1)) (opPadCv a b 0 0) _ _ _ _
  rw [opPad3_tree, opPad3_height, opPadCv_zero]
  exact hN

lemma opPad_run (h : Hash) (hl : LeafHash) (a b : UInt256) (ha : 0 < a) (hab : a < b) :
    OpSteps h (hl ⟨0, 0, 0⟩) hl (opPadCv a b) (honestFlowHash (subsetFlow 0 0)) opGenesis
      (opPad5 a b) [⟨0, 1, 0⟩, ⟨0, 0, 0⟩]
      [.authorize (opPadAuth h hl a b), .execute (opPadExec h hl a b)] := by
  have r3 := OpSteps.execute _ (opPad_pre h hl a b ha hab) (opPad_exec_checks h hl a b ha hab)
  have r4 := OpSteps.recordRoot (OpSteps.tick (t := 1) r3 (Nat.zero_le 1))
  exact OpSteps.authorize (opPadAuth h hl a b) (opPadRoot a b) r4
    (opPad_auth_checks h hl a b ha hab)
    (show (((Contracts.AtomicFlowManager.empty.set 0 0 .Committed).set 0 1 .Committed)).legState
      0 0 = .Committed by decide)

theorem OpPaddingRefundLocatesAbsenceBreak : Properties.OpPaddingRefundLocatesAbsenceBreak := by
  intro h hl a b ha hab
  obtain ⟨hnb, hpad⟩ := padding_countermodel_locates_padding_hit h hl a b
  have htree : (opPad5 a b).history.tree 0 1 = threeLeafTree a b := opPad3_tree a b
  have hheight : (opPad5 a b).history.height 0 1 = 2 := opPad3_height a b
  have hab' : AbsenceBreak h (hl ⟨0, 0, 0⟩) hl (opPad5 a b).history (subsetFlow 0 0).deadline 0 1
      (opPadForged h hl a b) := by
    refine Or.inr ⟨show (opPad5 a b).history.time 0 1 ≤ 0 from le_of_eq rfl, ?_⟩
    unfold ImtProofBreak
    rw [htree, hheight]
    exact hpad
  refine ⟨opPadCv a b, honestFlowHash (subsetFlow 0 0), opPad5 a b, _, _, opPadExec h hl a b,
    opPadAuth h hl a b, opPad_run h hl a b ha hab, by simp, by simp, rfl, rfl, rfl,
    ⟨opPadRoot a b, List.mem_singleton_self _,
      ⟨show (0 : ℕ) < 1 from Nat.one_pos, show (opPad5 a b).history.time 0 1 ≤ 0
        from le_of_eq rfl, rfl⟩⟩,
    show (⟨0, 0, 0⟩ : Obligation) ∈ [⟨0, 1, 0⟩, ⟨0, 0, 0⟩] by decide, ?_,
    RefundBreak.absence (opPadAuth h hl a b) (by simp) rfl rfl hab', ?_,
    fun hcl => hcl.1 rfl, hab', htree, hpad, le_refl 3, rfl⟩
  · show 2 ≤ rank (((((Contracts.AtomicFlowManager.empty.set 0 0 .Committed).set 0 1
      .Committed)).set 0 0 .Revertable).legState 0 0)
    decide
  · show ¬ ImtProofBreak h (hl ⟨0, 0, 0⟩) hl ((opPad5 a b).history.tree 0 1)
      ((opPad5 a b).history.height 0 1) (opPadProof h hl a b)
    unfold ImtProofBreak
    rw [htree, hheight]
    exact hnb

end Contracts.InteropOperational
