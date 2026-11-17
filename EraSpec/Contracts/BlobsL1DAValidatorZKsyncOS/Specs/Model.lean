import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashPinned

/-!
# Spec: `BlobsL1DAValidatorZKsyncOS`

Source: era-contracts `draft/v0.35.0` at `b17415d20`, under `l1-contracts/contracts/`. Line numbers
without a file name are in `state-transition/data-availability/BlobsL1DAValidatorZKsyncOS.sol`
(107 lines). Main at `70096e2ea` has the same logic in
`da-contracts/contracts/BlobsL1DAValidatorZKsyncOS.sol`; there the two constants are declared in
the file instead of `DAConstants.sol`.

Storage: `publishedBlobs : bytes32 → uint256` (`:18`), the block in which a blob versioned hash was
last recorded. Entry points:

* `publishBlobs()` (`:21-32`) is the only function that writes storage. It takes no argument and has
  no caller restriction. It reads the transaction's blob versioned hashes `blobhash(0)`,
  `blobhash(1)`, … up to the first zero, and sets `publishedBlobs[v] = block.number` for each.
* `isBlobAvailable(bytes32)` (`:34-40`, view): recorded at a nonzero block, and at most
  `BLOB_EXPIRATION_BLOCKS` blocks ago.
* `checkDA(…)` (`:43-100`, view). `_chainId`, `_batchNumber` and `_maxBlobsSupported` are unnamed and
  unused. The operator input must be a whole number of 32-byte entries (`:52-54`). A nonzero entry
  must be available (`:65-68`). A zero entry is replaced by the transaction's next blob versioned
  hash, which must be nonzero (`:69-73`). After the loop the transaction must carry no further blob
  (`:83-88`), and the keccak of the resolved hashes, concatenated, must equal
  `_l2DAValidatorOutputHash` (`:91-94`). The output is `(bytes32(0), [], [])` (`:97-99`).

`BLOB_EXPIRATION_BLOCKS = (4096 * 32) / 2` and `BLOB_VERSIONED_HASH_SIZE = 32` are
`DAConstants.sol:28` and `:31`.

## Model boundaries

* Bytes are `List UInt8`. Entry `i` of the input, `bytes32(_operatorDAInput[32 i : 32 (i + 1)])`
  (`:62-64`), is `b32At input (32 * i)`, the big-endian value of those 32 bytes. Under the length
  check at `:52-54` every such slice is in bounds.
* `keccak256` is an arbitrary function `Bytes → UInt256`. Nothing about it is assumed. Binding
  results are stated with `HashCollision` (from `InteropDataEncoding`), a collision on two inputs the
  statement names.
* `BLOBHASH` (`:102-106`) reads the transaction's list of blob versioned hashes: `blobhash(i)` is entry
  `i` of the list, and `0` from the end of the list on (`TxEnv.blobhash`). On Ethereum every versioned
  hash starts with the version byte `0x01`, so it is nonzero (`TxEnv.WellFormed`). The results that
  use this take it as a premise.
* The memory array `publishedVersionedHashes` (`:58`) has `input.length` bytes. The `mstore` at
  `:75-80` writes the resolved hash of entry `index` to bytes `32 index … 32 index + 32` of the array
  (the `+ 1` skips the length word). All entries are written, so after the loop the array is the
  concatenation of the resolved hashes (`encWords`).
* Loops are recursions over the remaining entries. Every guard reverts the whole call, so this order
  gives the same accepted inputs and the same result as the source's loop.
* A revert is `none`. `block.number - blockOfPublishing` (`:39`) is checked arithmetic and panics if
  the recorded block is in the future; the model returns `none` there. On reachable states this does
  not happen (`Properties.BlobsAvailabilityNeverPanics`).
* `checkDA` is `view` and is not a step: `checkDA` evaluates it at a given state and transaction.
  The block number is part of the state, and the step `advance` moves it forward; any number of
  transactions may run in one block.
* `World.log` is a ghost: the block and the written hashes of every `publishBlobs` call so far.
  It is not contract storage.
* `Ablation` deletes single guards for the countermodels. The source has every flag `true`.
-/

namespace Contracts.ZKsyncOSBlobsDA

open AttackVectors.BundleHashEncoding

/-- Raw bytes (calldata or memory). -/
abbrev Bytes := List UInt8

/-! ## Constants and byte helpers -/

/-- `BLOB_EXPIRATION_BLOCKS = (4096 * 32) / 2` (`DAConstants.sol:28`). -/
def BLOB_EXPIRATION_BLOCKS : ℕ := (4096 * 32) / 2

/-- `BLOB_VERSIONED_HASH_SIZE = 32` (`DAConstants.sol:31`). -/
def BLOB_VERSIONED_HASH_SIZE : ℕ := 32

/-- A `bytes32` value as its 32 big-endian bytes (what `mstore` writes). -/
def toB32 (x : UInt256) : Bytes := toBytesBE 32 x.val

/-- `bytes32(b[off : off + 32])`: the big-endian value of the 32 bytes at `off`. -/
def b32At (b : Bytes) (off : ℕ) : UInt256 := Nat.toUInt256 (fromBytesBE ((b.drop off).take 32))

/-- The validator output `L1DAValidatorOutput` (`chain-interfaces/IL1DAValidator.sol:11-21`). -/
structure DAOutput where
  stateDiffHash : UInt256
  blobsLinearHashes : List UInt256
  blobsOpeningCommitments : List UInt256
deriving DecidableEq

/-- `(bytes32(0), new bytes32[](0), new bytes32[](0))` (`:97-99`). -/
def DAOutput.empty : DAOutput := ⟨0, [], []⟩

/-! ## State and transaction environment -/

/-- The validator's storage plus the current block number. -/
structure VState where
  /-- `publishedBlobs` (`:18`). -/
  published : UInt256 → ℕ
  /-- `block.number`. -/
  block : ℕ

/-- One transaction's EIP-4844 blob versioned hashes, in order. -/
structure TxEnv where
  blobs : List UInt256

/-- `blobhash(i)` (`:102-106`): entry `i`, or `0` past the end of the list. -/
def TxEnv.blobhash (env : TxEnv) (i : ℕ) : UInt256 := env.blobs.getD i 0

/-- **EIP-4844 VERSIONED HASHES ARE NONZERO.** Each starts with the version byte `0x01`. Then the
indices with a nonzero `blobhash` are exactly `0 … blobs.length - 1`. -/
def TxEnv.WellFormed (env : TxEnv) : Prop := ∀ v ∈ env.blobs, v ≠ 0

/-! ## `publishBlobs` (`:21-32`) -/

/-- **The `while (true)` loop of `publishBlobs`** (`:24-31`) over the remaining blob hashes: stop at
the first zero hash (`:26-28`, and `blobhash` is zero past the end of the list), otherwise set
`publishedBlobs[versionedHash] = block.number` (`:29`) and continue. -/
def publishLoop (b : ℕ) : List UInt256 → (UInt256 → ℕ) → (UInt256 → ℕ)
  | [], m => m
  | v :: vs, m => if v = 0 then m else publishLoop b vs (Function.update m v b)

/-- **`publishBlobs()`** (`:21-32`). No caller check and no revert. -/
def publishBlobs (env : TxEnv) (S : VState) : VState :=
  { S with published := publishLoop S.block env.blobs S.published }

/-- The hashes `publishBlobs` writes: the blob hashes before the first zero one. -/
def attached (env : TxEnv) : List UInt256 := env.blobs.takeWhile (fun v => decide (v ≠ 0))

/-! ## `checkDA` (`:43-100`) -/

/-- Guards that the countermodels delete one at a time. The source has every flag `true`. -/
structure Ablation where
  /-- The second conjunct of `isBlobAvailable`, `block.number - blockOfPublishing <=
  BLOB_EXPIRATION_BLOCKS` (`:39`). -/
  window : Bool := true
  /-- The extra-blob check after the loop (`:83-88`). -/
  extraBlob : Bool := true

/-- **`isBlobAvailable`** (`:34-40`). `&&` short-circuits, so an unrecorded hash is `false` without
the subtraction. The subtraction is checked: a recorded block in the future panics (`none`). With
`window = false` the second conjunct is deleted (countermodel only). -/
def isBlobAvailableWith (A : Ablation) (S : VState) (v : UInt256) : Option Bool :=
  if S.published v = 0 then some false
  else if A.window = false then some true
  else if S.block < S.published v then none
  else some (decide (S.block - S.published v ≤ BLOB_EXPIRATION_BLOCKS))

/-- The source's `isBlobAvailable`. -/
abbrev isBlobAvailable (S : VState) (v : UInt256) : Option Bool := isBlobAvailableWith {} S v

/-- **The `for` loop of `checkDA`** (`:61-81`) over the remaining entries, with
`versionedHashIndex = j`. Returns the hashes written to `publishedVersionedHashes`, in order, and
the final `versionedHashIndex`.

* A nonzero entry must be available (`:65-68`); it is written as is.
* A zero entry takes `blobhash(versionedHashIndex)` (`:70`), which must be nonzero (`:71`); the index
  then advances (`:72`). -/
def checkLoopWith (A : Ablation) (env : TxEnv) (S : VState) :
    List UInt256 → ℕ → Option (List UInt256 × ℕ)
  | [], j => some ([], j)
  | w :: ws, j =>
    if w ≠ 0 then
      if isBlobAvailableWith A S w = some true then
        (checkLoopWith A env S ws j).map (fun r => (w :: r.1, r.2))
      else none
    else if env.blobhash j = 0 then none
    else (checkLoopWith A env S ws (j + 1)).map (fun r => (env.blobhash j :: r.1, r.2))

/-- The input's entries: `blobsProvided = length / 32` (`:56`) words, entry `i` read at offset
`32 i` (`:62-64`). -/
def inputWords (input : Bytes) : List UInt256 :=
  (List.range (input.length / BLOB_VERSIONED_HASH_SIZE)).map (fun i => b32At input (32 * i))

/-- The bytes of `publishedVersionedHashes` once every entry is written: the resolved hashes,
concatenated (`:58`, `:75-80`). -/
def encWords (vs : List UInt256) : Bytes := (vs.map toB32).flatten

/-- **`checkDA`** (`:43-100`), with ablation flags. The chain id, batch number and
`_maxBlobsSupported` are not read. -/
def checkDAWith (A : Ablation) (K : Bytes → UInt256) (env : TxEnv) (S : VState) (h : UInt256)
    (input : Bytes) : Option DAOutput :=
  -- `:52-54`
  if input.length % BLOB_VERSIONED_HASH_SIZE ≠ 0 then none
  else match checkLoopWith A env S (inputWords input) 0 with
    | none => none
    | some (vs, j) =>
      -- `:83-88`
      if A.extraBlob = true ∧ env.blobhash j ≠ 0 then none
      -- `:91-94`
      else if K (encWords vs) ≠ h then none
      -- `:97-99`
      else some DAOutput.empty

/-- The source's `checkDA`. -/
abbrev checkDA (K : Bytes → UInt256) (env : TxEnv) (S : VState) (h : UInt256) (input : Bytes) :
    Option DAOutput :=
  checkDAWith {} K env S h input

/-! ## The declarative reading -/

/-- **AVAILABLE**: recorded at a nonzero block, not in the future, at most `BLOB_EXPIRATION_BLOCKS`
blocks ago. -/
def Available (S : VState) (v : UInt256) : Prop :=
  0 < S.published v ∧ S.published v ≤ S.block ∧ S.block - S.published v ≤ BLOB_EXPIRATION_BLOCKS

/-- The number of zero entries. -/
def zeroCount (ws : List UInt256) : ℕ := ws.count 0

/-- **THE RESOLVED HASHES**, declaratively: a nonzero entry is kept; the zero entries, in order,
take `bh j`, `bh (j + 1)`, …. -/
def resolveWords (bh : ℕ → UInt256) : ℕ → List UInt256 → List UInt256
  | _, [] => []
  | j, w :: ws => if w = 0 then bh j :: resolveWords bh (j + 1) ws else w :: resolveWords bh j ws

/-- The hashes `checkDA` resolves the input to, for transaction `env`. -/
def resolvedHashes (env : TxEnv) (input : Bytes) : List UInt256 :=
  resolveWords env.blobhash 0 (inputWords input)

/-- The entries of `vs` at the positions where `ws` is zero, in order. -/
def atZeroEntries : List UInt256 → List UInt256 → List UInt256
  | [], _ => []
  | _ :: _, [] => []
  | w :: ws, v :: vs => if w = 0 then v :: atZeroEntries ws vs else atZeroEntries ws vs

/-! ## Runs -/

/-- The validator's storage and block number, with a ghost log of every `publishBlobs` call so
far: its block and the hashes it wrote. -/
structure World where
  st : VState
  log : List (ℕ × List UInt256)

/-- One step: a `publishBlobs` transaction (any caller, any attached blobs), or the block number
moving forward. These are all of the contract's state changes: the other two entry points are
`view`. -/
inductive WStep : World → World → Prop
  | publish (W : World) (env : TxEnv) :
      WStep W ⟨publishBlobs env W.st, W.log ++ [(W.st.block, attached env)]⟩
  | advance (W : World) (b : ℕ) : W.st.block ≤ b → WStep W ⟨{ W.st with block := b }, W.log⟩

/-- A freshly deployed validator at block `b`: nothing recorded, empty log. -/
def World.fresh (b : ℕ) : World := ⟨⟨fun _ => 0, b⟩, []⟩

/-- Reachable from a fresh deployment at some block, by any sequence of steps. -/
def World.Reachable (W : World) : Prop := ∃ b, Relation.ReflTransGen WStep (World.fresh b) W

/-- **IN THE WINDOW**: `v` was written by a logged `publishBlobs` call at a nonzero block that is at
most `BLOB_EXPIRATION_BLOCKS` before the current block. -/
def LoggedInWindow (W : World) (v : UInt256) : Prop :=
  ∃ e ∈ W.log, v ∈ e.2 ∧ 0 < e.1 ∧ e.1 ≤ W.st.block ∧ W.st.block - e.1 ≤ BLOB_EXPIRATION_BLOCKS

end Contracts.ZKsyncOSBlobsDA
