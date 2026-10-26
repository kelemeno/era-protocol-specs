import Mathlib.Tactic

import EraSpec.Core.Word


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



end AttackVectors.TimeoutSoundness
