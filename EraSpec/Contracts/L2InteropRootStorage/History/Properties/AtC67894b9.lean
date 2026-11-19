import EraSpec.Contracts.L2InteropRootStorage.History.Specs.AtC67894b9

/-!
# History properties: `L2InteropRootStorage` at `c67894b9`

**This is a record of an older commit, not a claim about `b17415d20`.** Statements about
`../Specs/AtC67894b9.lean`; proofs are in `../Proofs/AtC67894b9.lean`. The `c67894b9` contract is
the canonical `b17415d20` model with the tracked timestamps dropped, per call and per run, so the
canonical results transfer: a stored root is never overwritten and, from fresh storage, a zero
timestamp means "not imported". Read off one such storage per destination,
`Contracts.RootImport.ImportsGrow` follows from the storages' runs. The canonical-model version of
that link is `../../Properties/RootImportLink.lean`.
-/

namespace Contracts.InteropRootStorage.History

/-- **THE `c67894b9` CONTRACT IS THIS ONE WITHOUT THE TRACKED TIMESTAMPS, PER CALL.**  For every
state, caller and call, the `c67894b9` writer on the state's `storedInteropRoots` succeeds exactly
when this model's call does, and leaves the `storedInteropRoots` this model's call leaves. -/
def Properties.C67894b9CallIsTheProjection : Prop :=
  ∀ (S : State) (caller : Address) (c : Call),
    execAtC67 S.storedInteropRoots caller c = (exec S caller c).map State.storedInteropRoots

/-- **… AND PER RUN.**  The `c67894b9` contract reaches `R'` from `R` exactly when, for every
choice `L` of tracked timestamps, this model reaches from `⟨R, L⟩` some state whose
`storedInteropRoots` is `R'`. -/
def Properties.C67894b9RunsAreProjectedRuns : Prop :=
  ∀ (R R' : RootsAtC67),
    ReachAtC67 R R' ↔ ∀ L : UInt256 → UInt256, ∃ L', Reach ⟨R, L⟩ ⟨R', L'⟩

/-- **AT `c67894b9` A STORED ROOT IS NEVER OVERWRITTEN EITHER**: the pin's `InteropRootAlreadyExists`
check (`L2InteropRootStorage.sol:97-100` there), along every run of that contract. -/
def Properties.NoOverwriteAtC67894b9 : Prop :=
  ∀ (R R' : RootsAtC67) (c b : UInt256),
    ReachAtC67 R R' → (R c b).root ≠ 0 → R' c b = R c b

/-- **AT `c67894b9` A ZERO TIMESTAMP MEANS "NOT IMPORTED" TOO**, at every key, along every run of
that contract from fresh storage.  The pin's timeout check reads a zero
`interopRoots(…).timestamp` as "not imported" (`AtomicInteropProof.sol:171-174` there). -/
def Properties.ZeroTimestampIffUnsetAtC67894b9 : Prop :=
  ∀ R : RootsAtC67, ReachAtC67 empty.storedInteropRoots R →
    ∀ c b, (R c b).root = 0 ↔ (R c b).timestamp = 0

/-- **A RUN OF THE `c67894b9` CONTRACT.**  From fresh storage the bootloader imports `(9, 7)`;
from there it imports `(9, 8)`, and `(9, 7)` keeps its pair: the premises of
`NoOverwriteAtC67894b9` and `ZeroTimestampIffUnsetAtC67894b9`, on a run that changes the
storage. -/
def Properties.C67894b9RunWitness : Prop :=
  ∃ (R₁ R₂ : RootsAtC67),
    ReachAtC67 empty.storedInteropRoots R₁ ∧ ReachAtC67 R₁ R₂ ∧
    R₁ 9 7 = ⟨0xdd, 5⟩ ∧ R₂ 9 7 = ⟨0xdd, 5⟩ ∧ (R₁ 9 8).root = 0 ∧ R₂ 9 8 = ⟨0xee, 6⟩

/-- **AT `c67894b9`, THE STORAGE'S RUNS ONLY ADD IMPORTS.**  For any settlement-layer roots and
`L1_CHAIN_ID`s, if each destination's storage `R d` reaches `R' d` by a run of the `c67894b9`
contract, then the world read off `R'` is a later snapshot of the world read off `R` in the sense
of `Contracts.RootImport.ImportsGrow`: the same roots and configuration, and every import of the
first still an import of the second. -/
def Properties.StorageRunsGrowImportsAtC67894b9 : Prop :=
  ∀ (slRoot : Contracts.Atomicity.Chain → ℕ → Contracts.Timeout.SlRoot)
    (l1 : Contracts.RootImport.Dest → Contracts.Atomicity.Chain)
    (R R' : Contracts.RootImport.Dest → RootsAtC67),
    (∀ d, ReachAtC67 (R d) (R' d)) →
      Contracts.RootImport.ImportsGrow (importWorldAtC67 slRoot l1 R) (importWorldAtC67 slRoot l1 R')

/-- **A RUN THAT ADDS AN IMPORT.**  Destination 5 runs from fresh storage to a state holding a root
at `(9, 7)`, every other destination stays at fresh storage: the premise of
`StorageRunsGrowImportsAtC67894b9` holds, and the later world has destination 5's import of
`(9, 7)`, which the earlier one does not have. -/
def Properties.StorageRunsGrowImportsWitnessAtC67894b9 : Prop :=
  ∃ (R R' : Contracts.RootImport.Dest → RootsAtC67),
    (∀ d, ReachAtC67 (R d) (R' d)) ∧
    ∀ (slRoot : Contracts.Atomicity.Chain → ℕ → Contracts.Timeout.SlRoot)
      (l1 : Contracts.RootImport.Dest → Contracts.Atomicity.Chain),
      ¬ (importWorldAtC67 slRoot l1 R).imported 5 9 7 ∧ (importWorldAtC67 slRoot l1 R').imported 5 9 7

end Contracts.InteropRootStorage.History
