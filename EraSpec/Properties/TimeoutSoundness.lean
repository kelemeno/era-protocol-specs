import Mathlib.Tactic
import EraSpec.Word

/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/TimeoutSoundness.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  THE TIMEOUT PROTOCOL'S SOUNDNESS ARGUMENT, AS A THEOREM.

  `AtomicInteropProof`'s library header states why a timeout proof cannot be produced for a leg that
  actually finalized.  For the BEGIN branch the argument is (verbatim from the source):

      the commit value is absent from the batch-BEGIN IMT root (leaf 2). The tree is append-only and
      `begin(N) == end(N-1)`, so absence at the begin of a late batch means absence from every batch
      with `t <= deadline` — the leg can never finalize.

  That is a real argument with real hypotheses, and it lives only in a comment.  This file states it
  over an abstract batch history and proves it.

  The point is not that the argument is doubtful — it is short and correct — but that its HYPOTHESES
  become visible once written down: append-only growth, `begin(N) = end(N-1)`, and the batch order
  following time.  The third is the concrete counterpart of `Timestamps`' `Monotone t`, and this file
  shows exactly where it is used: it is what forces a late batch to come AFTER every in-time one.

  Axiom-free.  Nothing here models the aggregation tree, the proof encoding, or the END branch (which
  needs "last batch in root", a structural property of the aggregation path with no counterpart here).
-/

namespace AttackVectors.TimeoutSoundness

/-- A source chain's batch history: the IMT contents at the END of each batch, and each batch's
settlement time. -/
structure BatchHistory where
  /-- The committed values present at the end of batch `n`. -/
  endSet : ℕ → Finset UInt256
  /-- The settlement time attributed to batch `n`. -/
  time : ℕ → ℕ

/-- The IMT is append-only: a batch never removes a committed value. -/
def AppendOnly (H : BatchHistory) : Prop :=
  ∀ n : ℕ, H.endSet n ⊆ H.endSet (n + 1)

/-- Batch order follows aggregation-time order — the parenthesis in `AtomicInteropProof`'s SOUNDNESS
paragraph, and the concrete counterpart of `Timestamps.Monotone t`. -/
def TimeOrdered (H : BatchHistory) : Prop :=
  Monotone H.time

/-- `begin(N) = end(N-1)`, with `begin 0` empty. -/
def beginSet (H : BatchHistory) : ℕ → Finset UInt256
  | 0 => ∅
  | n + 1 => H.endSet n

/-- Append-only growth, iterated: earlier ends sit inside later ones. -/
theorem endSet_mono {H : BatchHistory} (hao : AppendOnly H) :
    ∀ {a b : ℕ}, a ≤ b → H.endSet a ⊆ H.endSet b := by
  intro a b hab
  induction b with
  | zero => simp_all
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h | h
    · exact fun x hx => hao b (ih (by omega) hx)
    · have : a = b + 1 := by omega
      subst this
      exact fun x hx => hx

/-- **BEGIN-BRANCH SOUNDNESS.**  If a commit value is absent from the BEGIN set of a batch settled
strictly after the deadline, it is absent from the END set of every batch settled by the deadline — so
no inclusion proof against an in-time batch can exist, and the leg can never finalize.

This is the argument `AtomicInteropProof`'s header gives for the begin branch.  `TimeOrdered` is used
exactly once, and only to place the late batch after the in-time one. -/
theorem begin_absence_implies_never_finalized {H : BatchHistory}
    (hao : AppendOnly H) (hto : TimeOrdered H)
    {L : ℕ} {D : ℕ} {v : UInt256}
    (hlate : D < H.time L)
    (habsent : v ∉ beginSet H L) :
    ∀ B : ℕ, H.time B ≤ D → v ∉ H.endSet B := by
  intro B hB hmem
  -- an in-time batch precedes the late one, since time is ordered
  have hBL : B < L := by
    by_contra hge
    exact absurd (hto (not_lt.mp hge)) (by omega)
  -- so `L` has a predecessor, and `B`'s end sits inside it
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  exact habsent (endSet_mono hao (by omega) hmem)

/-- **CONTRAPOSITIVE — the form the security argument uses.**  A leg whose commit value IS present in
some in-time batch cannot have a begin-branch timeout proof: its value is in the begin set of every
later batch.

So finalization and the begin-branch timeout are mutually exclusive, which is what the protocol needs
and what the abstract `delivered_and_reclaimed_impossible` assumes of its two witnesses. -/
theorem finalized_blocks_begin_timeout {H : BatchHistory}
    (hao : AppendOnly H) (hto : TimeOrdered H)
    {L : ℕ} {D : ℕ} {v : UInt256}
    (hlate : D < H.time L)
    {B : ℕ} (hB : H.time B ≤ D) (hmem : v ∈ H.endSet B) :
    v ∈ beginSet H L := by
  by_contra habsent
  exact begin_absence_implies_never_finalized hao hto hlate habsent B hB hmem

/-! ## THE END BRANCH

The other half of the protocol, for a source chain that HALTS and never settles a post-deadline batch.
Its argument, again from `AtomicInteropProof`'s header:

    Since the root was created at `T > deadline`, any batch aggregated after it has `t' >= T > deadline`,
    so the proven batch's end root is the final IMT state reachable in time — absence there means the
    leg can never finalize.

The structural check `_verifyLastBatchInRoot` enters as the hypothesis `hlast` below: everything after
`B` settles no earlier than the root's creation time.  That is what "B is the chain's LAST batch inside
this root" buys, expressed without modelling the aggregation tree. -/

/-- **END-BRANCH SOUNDNESS.**  If `B` settled by the deadline, every batch after it settles no earlier
than a root time `T` strictly past the deadline, and the value is absent from `B`'s END set, then the
value is absent from the END set of every in-time batch.

`hlast` is the abstract content of `_verifyLastBatchInRoot`: without it a non-final in-time batch could
be presented, and a later in-time batch could still commit the value. -/
theorem end_absence_implies_never_finalized {H : BatchHistory}
    (hao : AppendOnly H)
    {B : ℕ} {D T : ℕ} {v : UInt256}
    (hintime : H.time B ≤ D) (hroot : D < T)
    (hlast : ∀ n : ℕ, B < n → T ≤ H.time n)
    (habsent : v ∉ H.endSet B) :
    ∀ B' : ℕ, H.time B' ≤ D → v ∉ H.endSet B' := by
  intro B' hB' hmem
  -- an in-time batch cannot lie beyond `B`: everything past `B` settles at or after `T > D`
  have hle : B' ≤ B := by
    by_contra hgt
    have := hlast B' (by omega)
    omega
  exact habsent (endSet_mono hao hle hmem)

/-- **CONTRAPOSITIVE.**  A value committed in some in-time batch is present in the END set of the
chain's last in-time batch, so no end-branch timeout proof exists for it. -/
theorem finalized_blocks_end_timeout {H : BatchHistory}
    (hao : AppendOnly H)
    {B : ℕ} {D T : ℕ} {v : UInt256}
    (hintime : H.time B ≤ D) (hroot : D < T)
    (hlast : ∀ n : ℕ, B < n → T ≤ H.time n)
    {B' : ℕ} (hB' : H.time B' ≤ D) (hmem : v ∈ H.endSet B') :
    v ∈ H.endSet B := by
  by_contra habsent
  exact end_absence_implies_never_finalized hao hintime hroot hlast habsent B' hB' hmem

/-! ## The begin branch's hidden assumption, promoted

`beginSet` above is DEFINED as `begin(n+1) = end(n)`.  That is convenient and it matches the library
header ("its begin root equals the end root of the last in-time batch"), but defining it hides it: the
begin branch's soundness RESTS on that equation, and nothing on chain checks it.

`_authenticateRoot` authenticates the begin and end roots of the SAME batch, at leaf indices 2 and 3 of
that batch's root tree.  The equation relates DIFFERENT batches — batch `n+1`'s begin leaf to batch
`n`'s end leaf — so no single proof can establish it.  It is a property of how the source chain builds
its batch roots, in the same trust bucket as `TimeOrdered` and `LastBatchInRoot.OutsideRootLate`.

Below it is a hypothesis rather than a definition, and the sharpness result shows it is load-bearing. -/

/-- A history that records begin sets INDEPENDENTLY, instead of deriving them. -/
structure BatchHistory' where
  beginSet : ℕ → Finset UInt256
  endSet : ℕ → Finset UInt256
  time : ℕ → ℕ

/-- The append-only tree property, as an assumption. -/
def BeginIsPrevEnd (H : BatchHistory') : Prop := ∀ n : ℕ, H.beginSet (n + 1) = H.endSet n

/-- Append-only, restated for the independent history. -/
def AppendOnly' (H : BatchHistory') : Prop := ∀ n : ℕ, H.endSet n ⊆ H.endSet (n + 1)

/-- **THE BEGIN BRANCH, WITH THE ASSUMPTION VISIBLE.**  Same conclusion as
`begin_absence_implies_never_finalized`, but `BeginIsPrevEnd` now appears as a hypothesis instead of
being built into the model. -/
theorem begin_absence_of_beginIsPrevEnd {H : BatchHistory'}
    (hbp : BeginIsPrevEnd H) (hao : AppendOnly' H) (hto : Monotone H.time)
    {L D : ℕ} {v : UInt256} (hlate : D < H.time L) (habsent : v ∉ H.beginSet L) :
    ∀ B : ℕ, H.time B ≤ D → v ∉ H.endSet B := by
  intro B hB hmem
  -- as in the derived model: time ordering places the in-time batch before the late one
  have hBL : B < L := by
    by_contra hge
    exact absurd (hto (not_lt.mp hge)) (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  have hmono : ∀ {a b : ℕ}, a ≤ b → H.endSet a ⊆ H.endSet b := by
    intro a b hab
    induction b with
    | zero => simp_all
    | succ c ih =>
      rcases Nat.lt_or_ge a (c + 1) with h | h
      · exact fun x hx => hao c (ih (by omega) hx)
      · have : a = c + 1 := by omega
        subst this; exact fun _ hx => hx
  exact habsent (hbp k ▸ hmono (by omega : B ≤ k) hmem)

/-- **AND IT IS LOAD-BEARING.**  Drop `BeginIsPrevEnd` and the begin branch is unsound: a history whose
begin sets are unrelated to its end sets admits an absence witness at a late batch while the value is
finalized on time.  So the equation is not bookkeeping — it is what the branch runs on. -/
theorem begin_branch_needs_beginIsPrevEnd :
    ∃ (H : BatchHistory') (L D B : ℕ) (v : UInt256),
      AppendOnly' H ∧ Monotone H.time ∧ D < H.time L ∧ v ∉ H.beginSet L ∧
        H.time B ≤ D ∧ v ∈ H.endSet B := by
  refine ⟨⟨fun _ => ∅, fun _ => {0}, fun n => n⟩, 1, 0, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n; exact fun _ hx => hx
  · exact fun a b hab => hab
  · simp
  · simp
  · simp
  · simp

/-! ## THE TWO ROOTS ARE NOT INTERCHANGEABLE — and only one swap is dangerous

The branch is a prover input (`_absence.provesAgainstBeginRoot`), but it selects the LEAF INDEX that
`_authenticateRoot` verifies against — `IMT_BEGIN_ROOT_LEAF_INDEX = 2` versus
`IMT_END_ROOT_LEAF_INDEX = 3`, passed as `_leafProofMask` into `proveL2LeafInclusionShared`.  So a
root's ROLE is authenticated by its Merkle position, not merely its value, and a begin root cannot be
presented where an end root is required.

That guard is worth more in one direction than the other, which the constants alone do not show. -/

/-- `begin(n) ⊆ end(n)`: the batch's own insertions are what separate them. -/
theorem beginSet_subset_endSet {H : BatchHistory} (hao : AppendOnly H) (n : ℕ) :
    beginSet H n ⊆ H.endSet n := by
  cases n with
  | zero => simp [beginSet]
  | succ k => exact endSet_mono hao (Nat.le_succ k)

/-- **THE HARMLESS SWAP.**  Offering an END root on the BEGIN branch proves something STRONGER, since
`begin(L) ⊆ end(L)`.  Had the contract accepted it, soundness would survive — so the leaf-index binding
is not load-bearing in this direction. -/
theorem begin_branch_with_end_root_sound {H : BatchHistory}
    (hao : AppendOnly H) (hto : TimeOrdered H) {L D : ℕ} {v : UInt256}
    (hlate : D < H.time L) (habsent : v ∉ H.endSet L) :
    ∀ B : ℕ, H.time B ≤ D → v ∉ H.endSet B :=
  begin_absence_implies_never_finalized hao hto hlate
    (fun hmem => habsent (beginSet_subset_endSet hao L hmem))

/-- **THE DANGEROUS SWAP.**  Offering a BEGIN root on the END branch is UNSOUND: a value inserted
DURING an in-time batch is absent from that batch's begin root while being finalized on time.  Accepting
it would let `authorizeRefund` mark a live leg `Revertable` — a refund of a leg that did commit before
the deadline.

This is what the `_leafProofMask` binding actually buys: without it the end branch would admit exactly
this witness.  The end branch's own `l1BatchTimestamp <= _deadline` check does NOT catch it — the batch
here IS in time; it is the ROOT that is wrong. -/
theorem end_branch_with_begin_root_unsound :
    ∃ (H : BatchHistory) (D : ℕ) (v : UInt256) (B : ℕ),
      AppendOnly H ∧ H.time B ≤ D ∧ v ∉ beginSet H B ∧ v ∈ H.endSet B := by
  refine ⟨⟨fun n => if n = 0 then ∅ else {0}, fun _ => 0⟩, 0, 0, 1, ?_, ?_, ?_, ?_⟩
  · intro n
    cases n <;> simp
  · simp
  · simp [beginSet]
  · simp

/-! ### Two structural observations the proofs make visible

**1. `TimeOrdered` is not used in the END branch.**  The begin branch needs it exactly once, to place
the late batch after the in-time one.  Here `hlast` does that work directly, so the end branch stays
sound even for a history whose settlement times are not monotone in the batch index.

**2. `hintime` is redundant.**  The contract checks that the proven batch settled by the deadline, but
the soundness conclusion does not need it: absence at a LATER batch is a strictly stronger claim than
absence at an in-time one, because END sets only grow.  So that check is a well-formedness guard, not a
soundness requirement — dropping it would not admit a forged timeout proof.  Witnessed below. -/

/-- The END branch with `hintime` dropped, witnessing observation 2. -/
theorem end_absence_implies_never_finalized' {H : BatchHistory}
    (hao : AppendOnly H)
    {B : ℕ} {D T : ℕ} {v : UInt256}
    (hroot : D < T)
    (hlast : ∀ n : ℕ, B < n → T ≤ H.time n)
    (habsent : v ∉ H.endSet B) :
    ∀ B' : ℕ, H.time B' ≤ D → v ∉ H.endSet B' := by
  intro B' hB' hmem
  have hle : B' ≤ B := by
    by_contra hgt
    have := hlast B' (by omega)
    omega
  exact habsent (endSet_mono hao hle hmem)

/-- **BOTH BRANCHES, ONE STATEMENT.**  Whichever branch a prover declares, a successful timeout proof
implies the value is absent from every in-time batch — which is exactly "the leg can never finalize",
the property `authorizeRefund` relies on before marking legs `Revertable`. -/
theorem timeout_implies_never_finalized {H : BatchHistory}
    (hao : AppendOnly H) (hto : TimeOrdered H) {D : ℕ} {v : UInt256}
    (h : (∃ L, D < H.time L ∧ v ∉ beginSet H L)
       ∨ (∃ B T, H.time B ≤ D ∧ D < T ∧ (∀ n, B < n → T ≤ H.time n) ∧ v ∉ H.endSet B)) :
    ∀ B : ℕ, H.time B ≤ D → v ∉ H.endSet B := by
  rcases h with ⟨L, hlate, habsent⟩ | ⟨B, T, hintime, hroot, hlast, habsent⟩
  · exact begin_absence_implies_never_finalized hao hto hlate habsent
  · exact end_absence_implies_never_finalized hao hintime hroot hlast habsent


end AttackVectors.TimeoutSoundness
