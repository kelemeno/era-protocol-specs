import EraSpec.Contracts.InteropRootStorage.Specs.Storage

/-!
# Properties: `L2InteropRootStorage`

Statements about `EraSpec.Contracts.InteropRootStorage.Specs.Storage`; proofs are in
`EraSpec.Contracts.InteropRootStorage.Proofs.Storage`.  Source: era-contracts
`d9f678900e1bc8286412b78f56d4a9f443983c29`, `l1-contracts/contracts/interop/L2InteropRootStorage.sol`.

## What holds

* **Only the bootloader writes** (`OnlyBootloaderWrites`, per call; `LoggedCallersAreBootloader`,
  for every call of every run).
* **A stored root is never overwritten** (`NoOverwrite`): once a key holds a nonzero root, the
  whole stored pair — root and timestamp — is the same in every later state of every run.
* **Each key is imported at most once per run, and the storage is exactly the log**
  (`EachKeyImportedOnce`, `StorageIsTheLog`, `StoredIffImported`).
* **A zero timestamp means "not imported"** along every run from fresh storage
  (`ZeroTimestampIffUnsetInvariant`), and `latestInteropRootTimestamp` is the maximum stored
  timestamp of the chain, never decreases, and bounds every import of the run
  (`LatestIsMaxInvariant`, `LatestNeverDecreases`, `LatestBoundsEveryImport`,
  `LatestZeroIffNothingImported`).
* **A batch is its singles in order, all or nothing** (`BatchUnfoldsToSingles`,
  `BatchRejectsDuplicateKey`).

## Why each check is there (countermodels; the mutants are in the Specs file)

* `WithoutAuthAnyoneSquatsAKey` — without `onlyCallFromBootloader` anyone stores a bogus root
  at a key, and the genuine import of that key then reverts in every later state.
* `WithoutExistsCheckRootIsOverwritten` — without `InteropRootAlreadyExists` a stored root is
  replaced.
* `WithoutZeroRootCheckTimestampIsRewritten` — without `MessageRootIsZero` a key can hold a
  nonzero timestamp and still be imported again, with another timestamp.
* `WithoutZeroTimestampCheckRootLooksUnimported` — without `InteropRootTimestampIsZero` a key
  can hold a root with timestamp zero, permanently.
* `LegacyRootBreaksZeroTimestampClaim` — the same permanent state arises, with NO check deleted,
  from a start state holding a root without a timestamp (the pre-widening value type).  So the
  source comment's premise "the mapping was empty at upgrade time" (`:29-31`) is needed for the
  interface's zero-timestamp claim; this model does not check that premise.

## Non-vacuity

`ConcreteRun` is a two-call run from fresh storage (one single import, one batch of three)
ending with four stored roots.  The batch imports chain 1's roots out of timestamp order and
the tracked timestamp ends at the maximum, not at the last one.
-/

namespace Contracts.InteropRootStorage

/-! ## One call, exactly -/

/-- **EXACT SUCCESS CONDITION AND EFFECT OF ONE IMPORT.**  `_addInteropRoot` succeeds exactly
when `sides` is a single nonzero word, the timestamp is nonzero and the key holds no root; it
then stores that pair at the key and raises the chain's tracked timestamp to the maximum. -/
def Properties.AddInteropRootIff : Prop :=
  ∀ (S S' : State) (chainId blockOrBatchNumber timestamp : UInt256) (sides : List UInt256),
    addInteropRoot S chainId blockOrBatchNumber timestamp sides = some S' ↔
      ∃ root, sides = [root] ∧ root ≠ 0 ∧ timestamp ≠ 0 ∧
        (S.storedInteropRoots chainId blockOrBatchNumber).root = 0 ∧
        S' = writeRoot S chainId blockOrBatchNumber timestamp root

/-- **THE EFFECT OF ONE IMPORT, FIELD BY FIELD.**  After a successful import the key holds
`(root, timestamp)`, every other key is untouched, the chain's tracked timestamp is the larger
of its old value and `timestamp`, and every other chain's tracked timestamp is untouched. -/
def Properties.AddInteropRootEffect : Prop :=
  ∀ (S S' : State) (chainId blockOrBatchNumber timestamp root : UInt256),
    addInteropRoot S chainId blockOrBatchNumber timestamp [root] = some S' →
      S'.storedInteropRoots chainId blockOrBatchNumber = ⟨root, timestamp⟩ ∧
      (∀ c b, (c, b) ≠ (chainId, blockOrBatchNumber) →
        S'.storedInteropRoots c b = S.storedInteropRoots c b) ∧
      S'.latestInteropRootTimestamp chainId = max (S.latestInteropRootTimestamp chainId) timestamp ∧
      (∀ c, c ≠ chainId → S'.latestInteropRootTimestamp c = S.latestInteropRootTimestamp c)

/-! ## Authority -/

/-- **ONLY THE BOOTLOADER WRITES.**  Every successful state-changing call — single or batch,
any arguments, any state — has `msg.sender = L2_BOOTLOADER_ADDRESS`. -/
def Properties.OnlyBootloaderWrites : Prop :=
  ∀ (S S' : State) (caller : Address) (c : Call),
    exec S caller c = some S' → caller = L2_BOOTLOADER_ADDRESS

/-- **LOGGING LOSES NO RUN.**  `Reach` and `ReachLog` relate the same states. -/
def Properties.ReachIffReachLog : Prop :=
  ∀ (S T : State), Reach S T ↔ ∃ log, ReachLog S T log

/-- **EVERY CALL OF EVERY RUN IS THE BOOTLOADER'S.**  Run-level form of
`OnlyBootloaderWrites`: in any logged run, from any state, each logged caller is the
bootloader. -/
def Properties.LoggedCallersAreBootloader : Prop :=
  ∀ (S₀ S : State) (log : List (Address × Call)),
    ReachLog S₀ S log → ∀ p ∈ log, p.1 = L2_BOOTLOADER_ADDRESS

/-! ## No overwrite, one import per key -/

/-- **A STORED ROOT IS NEVER OVERWRITTEN.**  If a key holds a nonzero root in some state, then
in every state reachable from it — any calls, any callers, any order — the key holds the same
pair, root and timestamp. -/
def Properties.NoOverwrite : Prop :=
  ∀ (S S' : State) (c b : UInt256),
    Reach S S' → (S.storedInteropRoots c b).root ≠ 0 →
      S'.storedInteropRoots c b = S.storedInteropRoots c b

/-- **EVERY LOGGED IMPORT PASSED THE VALUE CHECKS.**  Each `InteropRoot` imported in a run has
exactly one side, nonzero, and a nonzero timestamp. -/
def Properties.LoggedImportsWellFormed : Prop :=
  ∀ (S₀ S : State) (log : List (Address × Call)),
    ReachLog S₀ S log →
      ∀ r ∈ imports log, r.sides.length = 1 ∧ r.sides.headD 0 ≠ 0 ∧ r.timestamp ≠ 0

/-- **EACH KEY IS IMPORTED AT MOST ONCE.**  In any logged run from any state `S₀`, the keys
`(chainId, blockOrBatchNumber)` of the imported roots are pairwise distinct — across calls and
inside one batch — and none of them held a root in `S₀`. -/
def Properties.EachKeyImportedOnce : Prop :=
  ∀ (S₀ S : State) (log : List (Address × Call)),
    ReachLog S₀ S log →
      ((imports log).map InteropRoot.key).Nodup ∧
      ∀ r ∈ imports log, (S₀.storedInteropRoots r.chainId r.blockOrBatchNumber).root = 0

/-- **THE STORAGE IS EXACTLY THE LOG.**  After any logged run from `S₀`, a key some logged
import named holds that import's `(sides[0], timestamp)` (the import is unique by
`EachKeyImportedOnce`), and a key no logged import named holds what `S₀` held. -/
def Properties.StorageIsTheLog : Prop :=
  ∀ (S₀ S : State) (log : List (Address × Call)),
    ReachLog S₀ S log → ∀ c b,
      (∀ r ∈ imports log, r.key = (c, b) → S.storedInteropRoots c b = r.stored) ∧
      ((∀ r ∈ imports log, r.key ≠ (c, b)) → S.storedInteropRoots c b = S₀.storedInteropRoots c b)

/-- **FROM FRESH STORAGE, A KEY HOLDS A ROOT EXACTLY WHEN THE RUN IMPORTED IT.** -/
def Properties.StoredIffImported : Prop :=
  ∀ (S : State) (log : List (Address × Call)),
    ReachLog empty S log → ∀ c b,
      (S.storedInteropRoots c b).root ≠ 0 ↔ ∃ r ∈ imports log, r.key = (c, b)

/-! ## Timestamps -/

/-- **A ZERO TIMESTAMP MEANS "NOT IMPORTED".**  `ZeroTimestampIffUnset` holds of fresh storage
and is preserved by every run; so it holds in every state reachable from fresh storage.  (From
other start states it can fail forever: `LegacyRootBreaksZeroTimestampClaim`.) -/
def Properties.ZeroTimestampIffUnsetInvariant : Prop :=
  ZeroTimestampIffUnset empty ∧
  ∀ (S S' : State), Reach S S' → ZeroTimestampIffUnset S → ZeroTimestampIffUnset S'

/-- **`latestInteropRootTimestamp` IS THE MAXIMUM STORED TIMESTAMP.**  `LatestIsMax` (an upper
bound on the chain's stored timestamps, attained when nonzero) holds of fresh storage and is
preserved by every run. -/
def Properties.LatestIsMaxInvariant : Prop :=
  LatestIsMax empty ∧
  ∀ (S S' : State), Reach S S' → LatestIsMax S → LatestIsMax S'

/-- **THE TRACKED TIMESTAMP NEVER DECREASES**, for any chain, along any run from any state. -/
def Properties.LatestNeverDecreases : Prop :=
  ∀ (S S' : State) (c : UInt256),
    Reach S S' → S.latestInteropRootTimestamp c ≤ S'.latestInteropRootTimestamp c

/-- **THE TRACKED TIMESTAMP BOUNDS EVERY IMPORT OF THE RUN.**  The interface's "once a root
created at time `T` is imported, the returned value is `>= T` forever"
(`IL2InteropRootStorage.sol:24-26`): after any logged run from any state, each imported root's
timestamp is at most its chain's tracked timestamp. -/
def Properties.LatestBoundsEveryImport : Prop :=
  ∀ (S₀ S : State) (log : List (Address × Call)),
    ReachLog S₀ S log →
      ∀ r ∈ imports log, r.timestamp ≤ S.latestInteropRootTimestamp r.chainId

/-- **FROM FRESH STORAGE, THE TRACKED TIMESTAMP IS ZERO EXACTLY WHEN THE CHAIN HAS NO ROOT.**
The interface's "(zero if none was imported yet)", and its converse. -/
def Properties.LatestZeroIffNothingImported : Prop :=
  ∀ (S : State), Reach empty S → ∀ c,
    S.latestInteropRootTimestamp c = 0 ↔ ∀ b, (S.storedInteropRoots c b).root = 0

/-! ## Batches -/

/-- **A BATCH IS ITS SINGLES IN ORDER.**  For the bootloader, the empty batch succeeds and
changes nothing, and a nonempty batch is `addSingleInteropRoot` of its head followed by the
batch of its tail, reverting as a whole if either does. -/
def Properties.BatchUnfoldsToSingles : Prop :=
  ∀ (S : State),
    addInteropRootsInBatch S L2_BOOTLOADER_ADDRESS [] = some S ∧
    ∀ (r : InteropRoot) (rs : List InteropRoot),
      addInteropRootsInBatch S L2_BOOTLOADER_ADDRESS (r :: rs) =
        (addSingleInteropRoot S L2_BOOTLOADER_ADDRESS r).bind
          (fun S' => addInteropRootsInBatch S' L2_BOOTLOADER_ADDRESS rs)

/-- **A BATCH NAMING A KEY TWICE REVERTS AS A WHOLE.**  No caller, state or other content makes
`addInteropRootsInBatch` succeed on an array with two entries for one key: nothing of such a
batch is imported. -/
def Properties.BatchRejectsDuplicateKey : Prop :=
  ∀ (S : State) (caller : Address) (rs : List InteropRoot),
    ¬ (rs.map InteropRoot.key).Nodup → addInteropRootsInBatch S caller rs = none

/-! ## Countermodels: each check is load-bearing -/

/-- **WITHOUT `onlyCallFromBootloader`, ANYONE SQUATS A KEY.**  There are a non-bootloader
caller and two imports for one key with different contents, such that: on fresh storage the
bootloader's import of the genuine one succeeds; the source rejects the attacker's call; the
contract with the modifier deleted accepts it; and from the state it leaves, in every reachable
state of the real contract, the key holds the attacker's pair and the bootloader's genuine
import reverts. -/
def Properties.WithoutAuthAnyoneSquatsAKey : Prop :=
  ∃ (attacker : Address) (bogus genuine : InteropRoot) (S : State),
    attacker ≠ L2_BOOTLOADER_ADDRESS ∧ bogus.key = genuine.key ∧ bogus.stored ≠ genuine.stored ∧
    addSingleInteropRoot empty L2_BOOTLOADER_ADDRESS genuine ≠ none ∧
    addSingleInteropRoot empty attacker bogus = none ∧
    addSingleNoAuth empty attacker bogus = some S ∧
    ∀ S', Reach S S' →
      S'.storedInteropRoots genuine.chainId genuine.blockOrBatchNumber = bogus.stored ∧
      exec S' L2_BOOTLOADER_ADDRESS (.single genuine) = none

/-- **WITHOUT `InteropRootAlreadyExists`, A STORED ROOT IS REPLACED.**  In a state reachable from
fresh storage a key holds `(root, ts)`; the source rejects a second import at that key; the
contract with the check deleted accepts it and the key then holds a different root. -/
def Properties.WithoutExistsCheckRootIsOverwritten : Prop :=
  ∃ (S S' : State) (c b ts ts' root root' : UInt256),
    Reach empty S ∧ S.storedInteropRoots c b = ⟨root, ts⟩ ∧ root ≠ root' ∧
    addInteropRoot S c b ts' [root'] = none ∧
    addInteropRootNoExistsCheck S c b ts' [root'] = some S' ∧
    S'.storedInteropRoots c b = ⟨root', ts'⟩

/-- **WITHOUT `MessageRootIsZero`, A NONZERO TIMESTAMP IS NOT FINAL.**  The source rejects a
zero root; the contract with that check deleted stores `(0, 5)`, which breaks
`ZeroTimestampIffUnset`; and the REAL `_addInteropRoot` then accepts another import at the
same key (its root slot is still zero) and the timestamp read there changes from 5 to 7. -/
def Properties.WithoutZeroRootCheckTimestampIsRewritten : Prop :=
  ∃ (S₁ S₂ : State) (c b : UInt256),
    addInteropRoot empty c b 5 [0] = none ∧
    addInteropRootNoZeroRootCheck empty c b 5 [0] = some S₁ ∧
    ¬ ZeroTimestampIffUnset S₁ ∧ (S₁.storedInteropRoots c b).timestamp = 5 ∧
    addInteropRoot S₁ c b 7 [1] = some S₂ ∧ (S₂.storedInteropRoots c b).timestamp = 7

/-- **WITHOUT `InteropRootTimestampIsZero`, AN IMPORTED ROOT LOOKS UNIMPORTED FOREVER.**  The
source rejects a zero timestamp; the contract with that check deleted stores a root with
timestamp zero, and in every state the real contract reaches from there the key still holds a
nonzero root with timestamp zero. -/
def Properties.WithoutZeroTimestampCheckRootLooksUnimported : Prop :=
  ∃ (S₁ : State) (c b : UInt256),
    addInteropRoot empty c b 0 [1] = none ∧
    addInteropRootNoZeroTimestampCheck empty c b 0 [1] = some S₁ ∧
    ∀ S', Reach S₁ S' →
      (S'.storedInteropRoots c b).root ≠ 0 ∧ (S'.storedInteropRoots c b).timestamp = 0

/-- **THE ZERO-TIMESTAMP CLAIM NEEDS FRESH STORAGE.**  With no check deleted: from a start
state in which a key holds a root with timestamp zero (what the pre-widening `bytes32` value
type would have left), `ZeroTimestampIffUnset` fails in every reachable state.  The source
relies on "the mapping was empty at upgrade time" (`L2InteropRootStorage.sol:29-31`). -/
def Properties.LegacyRootBreaksZeroTimestampClaim : Prop :=
  ∃ (S : State), ∀ S', Reach S S' → ¬ ZeroTimestampIffUnset S'

/-! ## Non-vacuity -/

/-- **A CONCRETE RUN.**  From fresh storage the bootloader imports `(9, 7)` with a single call
and then three roots of chain 1 with one batch, out of timestamp order (50, 70, 60).  All four
are stored, chain 1's tracked timestamp is the maximum 70 (not the last, 60), chain 9's is 5,
and an untouched chain's is 0. -/
def Properties.ConcreteRun : Prop :=
  ∃ (S : State) (log : List (Address × Call)),
    ReachLog empty S log ∧ log.length = 2 ∧ (imports log).length = 4 ∧
    S.storedInteropRoots 9 7 = ⟨0xdd, 5⟩ ∧
    S.storedInteropRoots 1 100 = ⟨0xaa, 50⟩ ∧
    S.storedInteropRoots 1 101 = ⟨0xbb, 70⟩ ∧
    S.storedInteropRoots 1 99 = ⟨0xcc, 60⟩ ∧
    S.latestInteropRootTimestamp 1 = 70 ∧
    S.latestInteropRootTimestamp 9 = 5 ∧
    S.latestInteropRootTimestamp 2 = 0

end Contracts.InteropRootStorage
