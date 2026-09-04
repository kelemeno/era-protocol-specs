import EraSpec.Contracts.InteropCommitmentTree

/-!
# Properties: the commitment tree

Every declaration in this file is a `Prop` — a statement about the model in
`EraSpec.Contracts.InteropCommitmentTree` with no proof attached.  Reading it
tells you WHAT is claimed.  `EraSpec.Proofs.InteropCommitmentTree` supplies a
theorem of each of these exact types (a *certificate*), and
`scripts/check-properties.sh` lists which properties have one and which are
still open.

Nothing here needs to be trusted: a mis-stated property is caught by reading it
against the model, and a stated-but-unproved one is caught by the checker.
-/

namespace Properties.InteropCommitmentTree

open IMTAbstract Contracts.InteropCommitmentTree

/-! ## Genesis and the invariant -/

/-- `setup` establishes a valid state: the sentinel is seeded, the maps are
empty, and the projection is the genesis singleton. -/
def SetupValid : Prop := Valid setup

/-- `insert` preserves every invariant when its guard holds — index bookkeeping
and order theory alike. -/
def InsertPreservesValid : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (low : ℕ), InsertGuard T v low → Valid (insert T v low)

/-- Every state of a contract run from a valid start is valid. -/
def RunValid : Prop :=
  ∀ (R : ℕ → Tree), Run R → Valid (R 0) → ∀ n, Valid (R n)

/-- Validity survives any number of guarded inserts — the batch-sized step. -/
def ReachesValid : Prop :=
  ∀ (T U : Tree), Reaches T U → Valid T → Valid U

/-- **THE KEY SET ONLY GROWS.**  Over any number of guarded inserts, no key is ever
removed: a value committed in one batch is still committed in every later one.  This
is the append-only content of the IMT's *finality signal* — a leg's commitment cannot
be revoked by later batches. -/
def ReachesKeysMono : Prop :=
  ∀ (T U : Tree), Reaches T U → Valid T → keys (toAbs T) ⊆ keys (toAbs U)

/-! ## The dedup gate

The contract's freshness check reads `valueToIndex`; the order theory wants
`v ∉ keys`.  These are different statements about different data. -/

/-- The storage dedup gate implies set-level freshness: in a valid tree, a
nonzero value with `valueToIndex[v] == 0` is not a key.  (`v ≠ 0` rules out the
sentinel, the one occupied leaf deliberately left unregistered — which is why the
contract rejects `_value == 0` separately from the dedup check.) -/
def DedupGateSound : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256), v ≠ 0 → T.valueToIndex v = 0 → v ∉ keys (toAbs T)

/-- The converse: a registered value is a key. -/
def RegisteredIsKey : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256), T.valueToIndex v ≠ 0 → v ∈ keys (toAbs T)

/-- The gate is an exact membership test on nonzero values. -/
def GateIffAbsent : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256), v ≠ 0 → (T.valueToIndex v = 0 ↔ v ∉ keys (toAbs T))

/-! ## The bounded search loop -/

/-- Whenever the search returns an index, that leaf satisfies the loop-exit
condition — the WEAK window `nextValue = 0 ∨ v ≤ nextValue`. -/
def LowSearchWindow : Prop :=
  ∀ (T : Tree) (v : UInt256) (fuel i j : ℕ), lowSearch T v fuel i = some j →
    (T.leaf j).nextValue = 0 ∨ v ≤ (T.leaf j).nextValue

/-- Starting from an occupied leaf below `v`, the returned leaf is occupied and
still below `v`.  Rests on `linkAgree`: hopping to `nextIndex` is only sound
because that index really carries `nextValue`. -/
def LowSearchSound : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (fuel i j : ℕ),
    i < T.leafCount → (T.leaf i).value < v → lowSearch T v fuel i = some j →
    j < T.leafCount ∧ (T.leaf j).value < v

/-- The contract's actual `insert` flow — the three up-front reverts, then the
search from the caller's hint — establishes `InsertGuard` at the index the search
returns.  So the guarded `insert` the rest of the theory is about is exactly what
a successful call performs. -/
def SearchYieldsGuard : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (fuel i j : ℕ),
    Initialized T → v ≠ 0 → T.valueToIndex v = 0 →
    i < T.leafCount → (T.leaf i).value < v → lowSearch T v fuel i = some j →
    InsertGuard T v j

/-! ## `insert` and the order theory -/

/-- The indexed insert projects to `imtInsert`: the contract's three-write index
manipulation and the order theory's set operation are the same thing. -/
def InsertProjects : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (low : ℕ), InsertGuard T v low →
    toAbs (insert T v low) = imtInsert (toAbs T) (lowAbs T low) v

/-- The contract's guard performs a sound insert: the order invariants survive
and the key set grows by exactly `v`.  The WEAK window suffices, because the
dedup gate closes the boundary. -/
def InsertSoundStep : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (low : ℕ), InsertGuard T v low →
    SoundState (toAbs (insert T v low))
      ∧ keys (toAbs (insert T v low)) = Insert.insert v (keys (toAbs T))

/-- A contract run, projected index-wise, is a `GuardedEvolution` — the history
shape `EraSpec.Core.IMT`'s whole security corpus is stated over. -/
def RunIsGuardedEvolution : Prop :=
  ∀ (R : ℕ → Tree), Run R → Valid (R 0) → GuardedEvolution (fun n => toAbs (R n))

/-- **The headline for one tree.**  At every step of every run from `setup`, a
nonzero commit value has a reclaim witness exactly when it is absent: a
delivered leg can never be refunded, and an undelivered one always can. -/
def GenesisRunReclaimableIffAbsent : Prop :=
  ∀ (R : ℕ → Tree), Run R → R 0 = setup → ∀ (n : ℕ) (v : UInt256), v ≠ 0 →
    ((∃ W ∈ toAbs (R n), W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)) ↔ v ∉ keys (toAbs (R n)))

/-! ## Open

Stated, not yet proved.  `scripts/check-properties.sh` reports these as `OPEN`. -/

/-- The search terminates with enough fuel: from any occupied hint, `leafCount`
hops suffice to reach a leaf whose successor is not below `v`.  (Values strictly
increase along `nextIndex` links and there are finitely many leaves.)  This is
the liveness half of the hint mechanism; `LowSearchSound`/`LowSearchWindow` are
the safety half. -/
def LowSearchTerminates : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (i : ℕ), i < T.leafCount →
    ∃ j, lowSearch T v T.leafCount i = some j

end Properties.InteropCommitmentTree
