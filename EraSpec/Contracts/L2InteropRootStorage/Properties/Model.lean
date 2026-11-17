import EraSpec.Contracts.L2InteropRootStorage.Specs.Model

/-!
# Properties: imported roots are write-once, and a zero timestamp means absent

Statements about `EraSpec.Contracts.L2InteropRootStorage.Specs.Model`. Proofs are in
`EraSpec.Contracts.L2InteropRootStorage.Proofs.Model`. `ok` is the admission predicate on imported
tuples (anything, for the contract alone). No statement takes a hash premise.

## Write-once

In any run from any storage, an entry with a nonzero root is never rewritten, root and timestamp
alike (`WriteOnce`); from fresh storage, an entry with a nonzero timestamp never changes
(`TimestampNotRewritable`). A batch import that succeeds stores every tuple as given
(`BatchImportWritesEach`), and its keys are pairwise distinct and unused before the call: a batch
that repeats a key, or reuses a stored one, has no successful run (`BatchKeysDistinct`).

## A zero timestamp means "nothing imported"

From fresh storage, an entry's timestamp is zero iff its root is (`ZeroTimestampIffAbsent`), the
`IL2InteropRootStorage.sol:18-19` invariant the timeout path relies on, and every nonzero entry
is `(root, timestamp)` of an admitted tuple for its key (`EntriesAreAdmittedImports`).

## An entry with a zero timestamp, from earlier storage

A storage holding `(root ≠ 0, timestamp 0)` at a key, which is how a bare `bytes32` root carried
over from v31 would read, keeps that entry forever: in every later state inclusion against that
root is accepted at the key, and the timeout path's root read fails at the key for every deadline
(`LegacyEntryBlocksTimeoutForever`; `LegacyEntryCountermodel` is a concrete run). By
`ZeroTimestampIffAbsent` no such entry is reachable from fresh storage; the source's NatSpec says
none was carried over (`L2InteropRootStorage.sol:35-39`).

## Witnesses

`RootStorageRunWitness` meets the premises of the six results above it: from fresh storage, a
batch import of two tuples stores both with nonzero roots and timestamps, and a later single import
writes a third, previously empty key. `LegacyEntryCountermodel` meets the premises of
`LegacyEntryBlocksTimeoutForever`.
-/

namespace Contracts.L2InteropRootStorage

/-- **WRITE-ONCE.** In any run from any storage, an entry with a nonzero root never changes —
root and timestamp alike. -/
def Properties.WriteOnce : Prop :=
  ∀ (ok : RootIn → Prop) (st st' : State), Reach ok st st' →
    ∀ c n, (st.entries c n).root ≠ 0 → st'.entries c n = st.entries c n

/-- **THE TIMESTAMP IS NOT REWRITABLE.** From fresh storage, once an entry's timestamp is nonzero
the entry never changes. -/
def Properties.TimestampNotRewritable : Prop :=
  ∀ (ok : RootIn → Prop) (st st' : State), Reach ok empty st → Reach ok st st' →
    ∀ c n, (st.entries c n).ts ≠ 0 → st'.entries c n = st.entries c n

/-- **A ZERO TIMESTAMP MEANS NOTHING IMPORTED** (`IL2InteropRootStorage.sol:18-19`). From fresh
storage, an entry's timestamp is `0` iff its root is. -/
def Properties.ZeroTimestampIffAbsent : Prop :=
  ∀ (ok : RootIn → Prop) (st : State), Reach ok empty st →
    ∀ c n, (st.entries c n).ts = 0 ↔ (st.entries c n).root = 0

/-- **EVERY ENTRY IS AN ADMITTED IMPORT, AS IMPORTED.** From fresh storage, a nonzero entry at
`(c, n)` is `(root, timestamp)` of an admitted tuple for `(c, n)` whose `sides` is `[root]`. -/
def Properties.EntriesAreAdmittedImports : Prop :=
  ∀ (ok : RootIn → Prop) (st : State), Reach ok empty st → ∀ c n, (st.entries c n).root ≠ 0 →
    ∃ (x : RootIn) (r : Word), ok x ∧ x.chainId = c ∧ x.blockOrBatchNumber = n ∧ x.sides = [r]
      ∧ st.entries c n = ⟨r, x.ts⟩

/-- **A SUCCESSFUL BATCH IMPORT STORES EVERY TUPLE.** Each tuple is admitted and stored as given. -/
def Properties.BatchImportWritesEach : Prop :=
  ∀ (ok : RootIn → Prop) (st st' : State) (xs : List RootIn), AddsAll ok st xs st' →
    ∀ x ∈ xs, ok x ∧ ∃ r, x.sides = [r] ∧ st'.entries x.chainId x.blockOrBatchNumber = ⟨r, x.ts⟩

/-- **ALL OR NOTHING.** A successful batch import has pairwise distinct keys, each unused before
the call. So a batch that repeats a key, or reuses a stored one, has no successful run: the call
reverts as a whole. -/
def Properties.BatchKeysDistinct : Prop :=
  ∀ (ok : RootIn → Prop) (st st' : State) (xs : List RootIn), AddsAll ok st xs st' →
    (xs.map fun x => (x.chainId, x.blockOrBatchNumber)).Nodup
      ∧ ∀ x ∈ xs, (st.entries x.chainId x.blockOrBatchNumber).root = 0

/-- **A ZERO-TIMESTAMP ENTRY BLOCKS EVERY TIMEOUT READ AT ITS KEY, FOREVER.** From any storage
holding `(r, 0)` with `r ≠ 0` at `(c, n)`, in every later state inclusion against `r` is accepted
at `(c, n)` and the timeout path's root read fails at `(c, n)` for every deadline. -/
def Properties.LegacyEntryBlocksTimeoutForever : Prop :=
  ∀ (ok : RootIn → Prop) (st₀ st : State) (c : ChainId) (n : ℕ) (r : Word), r ≠ 0 →
    st₀.entries c n = ⟨r, 0⟩ → Reach ok st₀ st →
      st.InclusionRootAccepts c n r ∧ ∀ D, ¬ st.TimeoutRootPasses c n D

/-- **THE COUNTERMODEL, CONCRETELY.** A storage with a legacy entry, and a run from it that imports
another root: afterwards the legacy root still passes inclusion and fails every timeout read,
while the new root passes the timeout read. -/
def Properties.LegacyEntryCountermodel : Prop :=
  ∃ (st₀ st : State) (c : ChainId) (n n' : ℕ) (r : Word), r ≠ 0 ∧ st₀.entries c n = ⟨r, 0⟩
    ∧ Reach (fun _ => True) st₀ st ∧ st.InclusionRootAccepts c n r
    ∧ (∀ D, ¬ st.TimeoutRootPasses c n D) ∧ st.TimeoutRootPasses c n' 0

/-- **NON-VACUITY.** From fresh storage, a batch import of two tuples stores both with nonzero
roots and timestamps (`st₁`); a later single import (`st₂`) writes a key `y` that was empty in
`st₁`. -/
def Properties.RootStorageRunWitness : Prop :=
  ∃ (st₁ st₂ : State) (xs : List RootIn) (y : RootIn),
    AddsAll (fun _ => True) empty xs st₁ ∧ xs.length = 2
      ∧ (∀ x ∈ xs, (st₁.entries x.chainId x.blockOrBatchNumber).root ≠ 0
          ∧ (st₁.entries x.chainId x.blockOrBatchNumber).ts ≠ 0)
      ∧ Step (fun _ => True) st₁ st₂
      ∧ (st₁.entries y.chainId y.blockOrBatchNumber).root = 0
      ∧ (st₂.entries y.chainId y.blockOrBatchNumber).root ≠ 0

end Contracts.L2InteropRootStorage
