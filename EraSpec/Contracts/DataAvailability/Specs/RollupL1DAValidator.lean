import EraSpec.Contracts.DataAvailability.Specs.Common

/-!
# Spec: `RollupL1DAValidator`

Source: era-contracts `d9f678900e1bc8286412b78f56d4a9f443983c29`,
`l1-contracts/contracts/state-transition/data-availability/RollupL1DAValidator.sol` (218 lines),
with the helpers of `CalldataDA.sol` (see `Specs/Common.lean`). Line numbers without a file name
are in `RollupL1DAValidator.sol`.

Storage: `publishedBlobCommitments : bytes32 → uint256` (`:34`), the block in which a commitment
was last published. Entry points:

* `publishBlobs(bytes)` (`:40-58`): the only state-changing function. Anyone may call it. For each
  144-byte chunk it reads the transaction's next blob versioned hash (`BLOBHASH`), runs the
  point-evaluation precompile, and marks `keccak(versionedHash ‖ chunk[0:48])` as published at the
  current block.
* `isBlobAvailable(bytes32)` (`:60-66`, view).
* `checkDA(...)` (`:69-110`, view): parses the operator input against the L2 output hash, then the
  blob branch (`_processBlobDA`, `:143-187`) or the calldata branch (`CalldataDA._processCalldataDA`),
  then the pair sanity loop (`:98-105`).

## Model boundaries

* The block number is part of the state (`VState.block`), a natural number; the environment step
  `advance` moves it forward. Within one block any number of transactions may run.
* `BLOBHASH` is a per-transaction function `TxEnv.blobhash : ℕ → UInt256`, arbitrary. On Ethereum it
  is non-zero exactly below the transaction's blob count; the results do not assume this, and say
  how they use the zero and non-zero answers.
* Loops are written as "the state after `k` iterations" (`blobLoop`, `publishLoop`). The source's
  `_processBlobDA` advances a calldata pointer by 176 bytes per iteration (`:178`); the model reads
  record `i` at offset `176 i` of the original slice, which is the same bytes. A revert in any
  iteration is `none` for the whole loop.
* `publishBlobs` computes all commitments, then writes them. The source interleaves the writes with
  the computation, but `_getPublishedBlobCommitment` does not read `publishedBlobCommitments`, and
  any revert discards all writes, so the final state is the same.
* `checkDA` is `view` and is not a step: `rollupCheckDA` returns the output at a given state.
* `Ablation` deletes single guards for the countermodels; the source is `rollupCheckDA`, every flag
  `true`.
-/

namespace Contracts.DataAvailability

open AttackVectors.BundleHashEncoding

/-- The storage of the validator plus the current block number. -/
structure VState where
  /-- `publishedBlobCommitments` (`:34`). -/
  published : UInt256 → ℕ
  /-- `block.number`. -/
  block : ℕ

/-- The per-transaction environment: `blobhash(i)` (`:213-217`). -/
structure TxEnv where
  blobhash : ℕ → UInt256

/-- A fresh validator at block `b`: nothing published. -/
def freshValidator (b : ℕ) : VState := { published := fun _ => 0, block := b }

/-- Guards that the countermodels delete one at a time. The source has every flag `true`. -/
structure Ablation where
  /-- The keccak check of the L2 output prefix (`CalldataDA.sol:76-78`). -/
  outputHash : Bool := true
  /-- The expiry window in `isBlobAvailable` (`:65`, second conjunct). -/
  expiry : Bool := true

/-- **`isBlobAvailable`** (`:60-66`). `&&` short-circuits, so an unpublished commitment is `false`
without the subtraction. `block.number - blockOfPublishing` is checked arithmetic: if the recorded
block were in the future it would panic, which is `none` (a revert of the calling `checkDA`).
With `checkWindow = false` the second conjunct is deleted (countermodel only). -/
def isBlobAvailableWith (checkWindow : Bool) (S : VState) (c : UInt256) : Option Bool :=
  if S.published c = 0 then some false
  else if checkWindow = true then
    if S.block < S.published c then none
    else some (decide (S.block - S.published c ≤ BLOB_EXPIRATION_BLOCKS))
  else some true

/-- The source's `isBlobAvailable`. -/
abbrev isBlobAvailable := isBlobAvailableWith true

/-- `bytes32(uint256(uint128(bytes16(_commitment[:16]))))` (`:125-127`). -/
def openingPoint (chunk : Bytes) : UInt256 := Nat.toUInt256 (fromBytesBE (chunk.take 16))

/-- `abi.encodePacked(_versionedHash, _openingPoint, _commitment[16:144])` (`:129-133`, `:198`):
the bytes given to the point-evaluation precompile. -/
def precompileInput (vh : UInt256) (chunk : Bytes) : Bytes :=
  toB32 vh ++ toB32 (openingPoint chunk) ++ (chunk.drop PUBDATA_COMMITMENT_CLAIMED_VALUE_OFFSET).take
    (PUBDATA_COMMITMENT_SIZE - PUBDATA_COMMITMENT_CLAIMED_VALUE_OFFSET)

/-- `keccak256(abi.encodePacked(blobVersionedHash, _commitment[:48]))` (`:136`): the opening
commitment, binding the versioned hash, the opening point and the claimed value. -/
def blobCommitmentOf (K : Crypto) (vh : UInt256) (chunk : Bytes) : UInt256 :=
  K.keccak (toB32 vh ++ chunk.take PUBDATA_COMMITMENT_COMMITMENT_OFFSET)

/-- **`_getPublishedBlobCommitment`** (`:116-137`). -/
def getPublishedBlobCommitment (K : Crypto) (env : TxEnv) (idx : ℕ) (chunk : Bytes) :
    Option UInt256 :=
  -- `:117-121`
  if env.blobhash idx = 0 then none
  -- `:129-133`, `:204-210`
  else if K.pointEvalOk (precompileInput (env.blobhash idx) chunk) = false then none
  else some (blobCommitmentOf K (env.blobhash idx) chunk)

/-! ## The blob branch -/

/-- Record `i` of the blob branch's input: the bytes from offset `176 i` on. -/
def blobRecord (rest : Bytes) (i : ℕ) : Bytes := rest.drop (BLOB_DA_INPUT_SIZE * i)

/-- `prepublishedCommitment` of record `i` (`:163`): its bytes 144..176. -/
def blobPre (rest : Bytes) (i : ℕ) : UInt256 := b32At (blobRecord rest i) PUBDATA_COMMITMENT_SIZE

/-- `commitmentData` of record `i` (`:162`): its first 144 bytes. -/
def blobChunk (rest : Bytes) (i : ℕ) : Bytes := (blobRecord rest i).take PUBDATA_COMMITMENT_SIZE

/-- **The loop of `_processBlobDA`** (`:161-179`) after `k` iterations over `rest`: the commitments
of records `0..k-1`, in order, and `versionedHashIndex`. -/
def blobLoop (A : Ablation) (K : Crypto) (env : TxEnv) (S : VState) (rest : Bytes) :
    ℕ → Option (List UInt256 × ℕ)
  | 0 => some ([], 0)
  | k + 1 =>
      match blobLoop A K env S rest k with
      | none => none
      | some (cs, idx) =>
        if blobPre rest k ≠ 0 then
          -- `:165-171`
          match isBlobAvailableWith A.expiry S (blobPre rest k) with
          | some true => some (cs ++ [blobPre rest k], idx)
          | _ => none
        else
          -- `:172-175`
          match getPublishedBlobCommitment K env idx (blobChunk rest k) with
          | some c => some (cs ++ [c], idx + 1)
          | none => none

/-- **`_processBlobDA`** (`:143-187`): the input must be exactly `n` records of 176 bytes; after the
loop, there must be no further blob in the transaction (`:183-186`). The result has length `max`
(`:148`); entries from `n` on stay zero. -/
def processBlobDAWith (A : Ablation) (K : Crypto) (env : TxEnv) (S : VState) (n max : ℕ)
    (rest : Bytes) : Option (List UInt256) :=
  -- `:154-156`
  if rest.length ≠ n * BLOB_DA_INPUT_SIZE then none
  else match blobLoop A K env S rest n with
    | none => none
    | some (cs, idx) =>
        -- `:183-186`
        if env.blobhash idx ≠ 0 then none
        else some (cs ++ List.replicate (max - n) 0)

/-- The sanity predicate of `:99-102`: exactly one of the two entries is zero. -/
def rollupPairMismatch (lin com : UInt256) : Bool :=
  (lin == 0 && com != 0) || (lin != 0 && com == 0)

/-- **`checkDA`** (`:69-110`), with ablation flags. -/
def rollupCheckDAWith (A : Ablation) (K : Crypto) (env : TxEnv) (S : VState) (h : UInt256)
    (input : Bytes) (max : ℕ) : Option Output :=
  -- `:76-82`
  match processL2With A.outputHash K.keccak h max input with
  | none => none
  | some p =>
    -- `:84`: `l1DaInput[0]` is out of bounds on an empty slice (a panic)
    match p.l1DaInput with
    | [] => none
    | src :: rest =>
      let coms : Option (List UInt256) :=
        -- `:87-88`, `PubdataSource.Blob = 1`
        if src.toNat = 1 then processBlobDAWith A K env S p.blobsProvided max rest
        -- `:89-90`, `PubdataSource.Calldata = 0`
        else if src.toNat = 0 then
          (processCalldataDA K.keccak p.blobsProvided p.fullPubdataHash max rest).map Prod.fst
        -- `:91-93`
        else none
      match coms with
      | none => none
      | some cs =>
        -- `:98-105`
        if (List.range max).any (fun i =>
            rollupPairMismatch (p.blobsLinearHashes.getD i 0) (cs.getD i 0)) then none
        -- `:107-109`
        else some { stateDiffHash := p.stateDiffHash, blobsLinearHashes := p.blobsLinearHashes,
                    blobsOpeningCommitments := cs }

/-- The source's `checkDA`. -/
def rollupCheckDA (K : Crypto) (env : TxEnv) (S : VState) (h : UInt256) (input : Bytes)
    (max : ℕ) : Option Output :=
  rollupCheckDAWith {} K env S h input max

/-! ## `publishBlobs` and runs -/

/-- The loop of `publishBlobs` (`:50-57`) after `k` iterations: the commitments of chunks `0..k-1`.
Chunk `i` is `_pubdataCommitments[144 i : 144 i + 144]` and uses `blobhash(i)`. -/
def publishLoop (K : Crypto) (env : TxEnv) (input : Bytes) : ℕ → Option (List UInt256)
  | 0 => some []
  | k + 1 =>
      match publishLoop K env input k with
      | none => none
      | some cs =>
        match getPublishedBlobCommitment K env k
            ((input.drop (PUBDATA_COMMITMENT_SIZE * k)).take PUBDATA_COMMITMENT_SIZE) with
        | none => none
        | some c => some (cs ++ [c])

/-- Mark each commitment as published at block `b` (`:55`). -/
def markPublished (m : UInt256 → ℕ) (cs : List UInt256) (b : ℕ) : UInt256 → ℕ :=
  cs.foldl (fun m c => fun x => if x = c then b else m x) m

/-- **`publishBlobs`** (`:40-58`). -/
def publishBlobs (K : Crypto) (env : TxEnv) (S : VState) (input : Bytes) : Option VState :=
  -- `:41-43`
  if input.length = 0 then none
  -- `:44-46`
  else if input.length % PUBDATA_COMMITMENT_SIZE ≠ 0 then none
  else match publishLoop K env input (input.length / PUBDATA_COMMITMENT_SIZE) with
    | none => none
    | some cs => some { S with published := markPublished S.published cs S.block }

/-- One step of the validator's world: a successful `publishBlobs` transaction (any caller, any
blobs attached), or the block number moving forward. -/
inductive VStep (K : Crypto) : VState → VState → Prop
  | publish {S S' : VState} (env : TxEnv) (input : Bytes) :
      publishBlobs K env S input = some S' → VStep K S S'
  | advance {S : VState} (b : ℕ) : S.block ≤ b → VStep K S { S with block := b }

/-- Reachability: any interleaving of `publishBlobs` calls and block advances. -/
def VReach (K : Crypto) : VState → VState → Prop := Relation.ReflTransGen (VStep K)

/-! ## What an accepted commitment is -/

/-- **`c` WAS AUTHENTICATED BY THE PRECOMPILE**: it is `keccak(vh ‖ chunk[0:48])` for a non-zero
versioned hash `vh` and a 144-byte chunk on which the point-evaluation precompile accepted the
opening of `vh` (`_getPublishedBlobCommitment`'s success condition). -/
def Authenticated (K : Crypto) (c : UInt256) : Prop :=
  ∃ vh chunk, vh ≠ 0 ∧ chunk.length = PUBDATA_COMMITMENT_SIZE ∧
    K.pointEvalOk (precompileInput vh chunk) = true ∧ c = blobCommitmentOf K vh chunk

/-- The number of records among `0..i-1` with a zero prepublished word: the value of
`versionedHashIndex` when the loop reaches record `i`. -/
def freshBefore (rest : Bytes) : ℕ → ℕ
  | 0 => 0
  | i + 1 => freshBefore rest i + (if blobPre rest i = 0 then 1 else 0)

/-- **WHAT THE BLOB BRANCH CHECKED ABOUT ENTRY `i`**, whose returned commitment is `c`.

* If record `i` names a prepublished commitment (non-zero word): `c` is that word, it is recorded
  as published, not in the future, and at most `BLOB_EXPIRATION_BLOCKS` blocks ago.
* Otherwise `c` is computed in this transaction: with `j` the number of earlier such records, the
  transaction's blob `j` exists (`blobhash(j) ≠ 0`), the precompile accepted its opening in the
  record's 144-byte chunk, and `c = keccak(blobhash(j) ‖ chunk[0:48])`. -/
def BlobEntryOk (K : Crypto) (env : TxEnv) (S : VState) (rest : Bytes) (i : ℕ) (c : UInt256) :
    Prop :=
  (blobPre rest i ≠ 0 →
      c = blobPre rest i ∧ 0 < S.published c ∧ S.published c ≤ S.block
        ∧ S.block - S.published c ≤ BLOB_EXPIRATION_BLOCKS)
  ∧ (blobPre rest i = 0 →
      env.blobhash (freshBefore rest i) ≠ 0
        ∧ K.pointEvalOk (precompileInput (env.blobhash (freshBefore rest i)) (blobChunk rest i))
            = true
        ∧ c = blobCommitmentOf K (env.blobhash (freshBefore rest i)) (blobChunk rest i))

end Contracts.DataAvailability
