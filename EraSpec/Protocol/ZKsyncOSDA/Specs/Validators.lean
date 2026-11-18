import EraSpec.Contracts.BlobsL1DAValidatorZKsyncOS.Specs.Model

/-!
# Spec: the EraVM-format DA validators, as a ZKsync OS chain's committer calls them

Source: era-contracts `draft/v0.35.0` at `b17415d20`, under
`l1-contracts/contracts/state-transition/data-availability/` unless another directory is named:

* `CalldataDA.sol:29-82` (`_processL2RollupDAValidatorOutputHash`) and `:90-117`
  (`_processCalldataDA`);
* `CalldataDAGateway.sol:12-40` (its override, used by `RelayedSLDAValidator`);
* `RollupL1DAValidator.sol:60-66` (`isBlobAvailable`), `:69-110` (`checkDA`), `:116-137`
  (`_getPublishedBlobCommitment`), `:143-187` (`_processBlobDA`);
* `RelayedSLDAValidator.sol:27-33`, `:39-45`, `:48-110`;
* `ValidiumL1DAValidator.sol:9-28`;
* constants: `DAConstants.sol:11-20`, `CalldataDA.sol:17-20`, `common/Config.sol:43`.

These transcriptions are adapted from an earlier draft DA model and re-checked line by line
against `b17415d20`. Changes from that draft: the namespace (`Contracts.ZKsyncOSCommitterDA`),
the ablation flags are dropped, `publishBlobs` of the rollup validator is not
transcribed (its record only matters through `RollupState`), and the blob loop advances its slice
by one record per iteration as the source does at `:178`.

## Model boundaries

* Bytes, `toB32`, `b32At`, the output record `DAOutput`, the transaction's blob list `TxEnv` and
  `BLOB_EXPIRATION_BLOCKS` are those of `Contracts.ZKsyncOSBlobsDA`
  (`Contracts/BlobsL1DAValidatorZKsyncOS/Specs/Model.lean`). `uint8(x[i])` is `byteAt x i`.
* Solidity bounds-checks every calldata slice and index. The model does not: under the guards before
  each read the read is in bounds. The two reads no guard covers are modelled as reverts: the index
  `l1DaInput[0]` on an empty slice, and the write `blobCommitments[0]` into an array of length `max = 0`
  (unreachable from `checkDA`, where `1 = blobsProvided ≤ max`).
* `_cloneCalldata(dst, src, n)` (`CalldataDA.sol:123-130`) copies `32 n` bytes over a zeroed array of
  `max` words (`wordsAt src n max`). Both call sites have `n ≤ max` and `32 n` readable bytes, so
  the unchecked assembly stays in bounds.
* `keccak256` is an arbitrary function and nothing about it is assumed (`Crypto.keccak`). The
  EIP-4844 point-evaluation precompile, with the decode of its output and the comparison with
  `BLS_MODULUS` (`RollupL1DAValidator.sol:193-211`), is one oracle `Crypto.pointEvalOk` on the exact
  input bytes.
* `IL2Bridgehub(L2_BRIDGEHUB_ADDR).getZKChain` is an arbitrary function (`GatewayEnv`) and is assumed
  not to revert. `L2_TO_L1_MESSENGER_SYSTEM_CONTRACT.sendToL1` is assumed to succeed; its effect is
  the returned `RelayMessage`, the four fields of the `abi.encode` at `RelayedSLDAValidator.sol:42-44`
  (the encoding itself is not modelled). The sanity loop runs after the relay, so a revert there
  also undoes the message (`VM-REVERT`).
* A revert is `none`. Every guard reverts the whole call, so only the accepted set and the result
  matter, not the order of the guards.
-/

namespace Contracts.ZKsyncOSCommitterDA

open AttackVectors.BundleHashEncoding
open Contracts.ZKsyncOSBlobsDA (Bytes toB32 b32At DAOutput TxEnv BLOB_EXPIRATION_BLOCKS encWords)

/-! ## Constants -/

/-- `BLOB_SIZE_BYTES = 126_976` (`common/Config.sol:43`). -/
def BLOB_SIZE_BYTES : ℕ := 126976

/-- `PUBDATA_COMMITMENT_SIZE = 144` (`DAConstants.sol:11`). -/
def PUBDATA_COMMITMENT_SIZE : ℕ := 144

/-- `PUBDATA_COMMITMENT_CLAIMED_VALUE_OFFSET = 16` (`DAConstants.sol:14`). -/
def PUBDATA_COMMITMENT_CLAIMED_VALUE_OFFSET : ℕ := 16

/-- `PUBDATA_COMMITMENT_COMMITMENT_OFFSET = 48` (`DAConstants.sol:17`). -/
def PUBDATA_COMMITMENT_COMMITMENT_OFFSET : ℕ := 48

/-- `BLOB_DA_INPUT_SIZE = PUBDATA_COMMITMENT_SIZE + 32` (`DAConstants.sol:20`). -/
def BLOB_DA_INPUT_SIZE : ℕ := PUBDATA_COMMITMENT_SIZE + 32

/-- `BLOB_DATA_OFFSET = 65` (`CalldataDA.sol:17`): state diff hash, full pubdata hash, blob count. -/
def BLOB_DATA_OFFSET : ℕ := 65

/-- `BLOB_COMMITMENT_SIZE = 32` (`CalldataDA.sol:20`). -/
def BLOB_COMMITMENT_SIZE : ℕ := 32

/-- `uint256(uint8(b[i]))`. -/
def byteAt (b : Bytes) (i : ℕ) : ℕ := (b.getD i 0).toNat

/-! ## The cryptographic environment -/

/-- The two primitives the validators call. Both are arbitrary. -/
structure Crypto where
  /-- `keccak256`. -/
  keccak : Bytes → UInt256
  /-- The point-evaluation precompile at `0x0A` on the given input: the `staticcall` succeeded and
  the second returned word equals `BLS_MODULUS` (`RollupL1DAValidator.sol:198-210`). -/
  pointEvalOk : Bytes → Bool

/-! ## `_processL2RollupDAValidatorOutputHash` (`CalldataDA.sol:29-82`) -/

/-- The five return values of `_processL2RollupDAValidatorOutputHash`. -/
structure L2Parsed where
  stateDiffHash : UInt256
  fullPubdataHash : UInt256
  blobsLinearHashes : List UInt256
  blobsProvided : ℕ
  l1DaInput : Bytes

/-- `ptr = BLOB_DATA_OFFSET + 32 * blobsProvided` (`CalldataDA.sol:73`), with
`blobsProvided = uint8(_operatorDAInput[64])` (`:57`). -/
def l2PrefixLen (input : Bytes) : ℕ := BLOB_DATA_OFFSET + 32 * byteAt input 64

/-- `_operatorDAInput[:ptr]`, the bytes hashed against `_l2DAValidatorOutputHash`
(`CalldataDA.sol:76`). -/
def l2Prefix (input : Bytes) : Bytes := input.take (l2PrefixLen input)

/-- `new bytes32[](max)` followed by `_cloneCalldata(dst, src, n)` (`CalldataDA.sol:123-130`): `max`
words, the first `n` read from `src`, the rest zero. -/
def wordsAt (src : Bytes) (n max : ℕ) : List UInt256 :=
  (List.range max).map fun i => if i < n then b32At src (32 * i) else 0

/-- `blobsLinearHashes` (`CalldataDA.sol:65`, `:71`): `max` words, the first `n` from
`_operatorDAInput[BLOB_DATA_OFFSET:]`. -/
def linearOf (input : Bytes) (n max : ℕ) : List UInt256 :=
  wordsAt (input.drop BLOB_DATA_OFFSET) n max

/-- **`_processL2RollupDAValidatorOutputHash`** (`CalldataDA.sol:29-82`), guards in source order. -/
def processL2 (keccak : Bytes → UInt256) (h : UInt256) (max : ℕ) (input : Bytes) :
    Option L2Parsed :=
  -- `:51-53`
  if input.length < BLOB_DATA_OFFSET then none
  -- `:59-61`
  else if max < byteAt input 64 then none
  -- `:67-69`
  else if input.length < l2PrefixLen input then none
  -- `:76-78`
  else if keccak (l2Prefix input) ≠ h then none
  else some
    { stateDiffHash := b32At input 0                         -- `:55`
      fullPubdataHash := b32At input 32                      -- `:56`
      blobsLinearHashes := linearOf input (byteAt input 64) max
      blobsProvided := byteAt input 64                        -- `:57`
      l1DaInput := input.drop (l2PrefixLen input) }           -- `:81`

/-! ## The calldata branches -/

/-- **`CalldataDA._processCalldataDA`** (`CalldataDA.sol:90-117`): exactly one blob; the last 32
bytes are the blob commitment, the rest is the pubdata, at most `BLOB_SIZE_BYTES` long, whose
keccak must be the full pubdata hash. Returns the commitments array (length `max`, entry 0 set) and
the pubdata. -/
def processCalldataDA (keccak : Bytes → UInt256) (n : ℕ) (fp : UInt256) (max : ℕ)
    (pubdataInput : Bytes) : Option (List UInt256 × Bytes) :=
  -- `:96-98`
  if n ≠ 1 then none
  -- `:99-101`
  else if pubdataInput.length < BLOB_COMMITMENT_SIZE then none
  else
    -- `:108`
    let pub := pubdataInput.take (pubdataInput.length - BLOB_COMMITMENT_SIZE)
    -- `:110-112`
    if BLOB_SIZE_BYTES < pub.length then none
    -- `:113-115`
    else if fp ≠ keccak pub then none
    -- `:116` on the array of `:106`: index 0 is out of bounds when `max = 0`
    else if max = 0 then none
    else some ((List.replicate max 0).set 0
      (b32At pubdataInput (pubdataInput.length - BLOB_COMMITMENT_SIZE)), pub)

/-- **`CalldataDAGateway._processCalldataDA`** (`CalldataDAGateway.sol:12-40`): `n` commitments of
32 bytes at the end, the pubdata before them, at most `n * BLOB_SIZE_BYTES` long, whose keccak must
be the full pubdata hash. The commitments array has `max` words, the first `n` copied (`:39`); the
one caller has `n ≤ max`. -/
def processCalldataDAGateway (keccak : Bytes → UInt256) (n : ℕ) (fp : UInt256) (max : ℕ)
    (pubdataInput : Bytes) : Option (List UInt256 × Bytes) :=
  -- `:18-20`
  if pubdataInput.length < n * BLOB_COMMITMENT_SIZE then none
  else
    -- `:26`
    let pub := pubdataInput.take (pubdataInput.length - n * BLOB_COMMITMENT_SIZE)
    -- `:28-30`
    if n * BLOB_SIZE_BYTES < pub.length then none
    -- `:31-33`
    else if fp ≠ keccak pub then none
    else
      -- `:35-37`
      let provided := pubdataInput.drop (pubdataInput.length - n * BLOB_COMMITMENT_SIZE)
      -- `:24`, `:39`
      some (wordsAt provided n max, pub)

/-! ## `RollupL1DAValidator` -/

/-- `publishedBlobCommitments` (`RollupL1DAValidator.sol:34`) and the block number. -/
structure RollupState where
  published : UInt256 → ℕ
  block : ℕ

/-- **`isBlobAvailable`** (`RollupL1DAValidator.sol:60-66`): the same shape as the ZKsync OS
validator's. -/
def rollupIsBlobAvailable (S : RollupState) (c : UInt256) : Option Bool :=
  if S.published c = 0 then some false
  else if S.block < S.published c then none
  else some (decide (S.block - S.published c ≤ BLOB_EXPIRATION_BLOCKS))

/-- `bytes32(uint256(uint128(bytes16(_commitment[:16]))))` (`:125-127`). -/
def openingPoint (chunk : Bytes) : UInt256 := Nat.toUInt256 (fromBytesBE (chunk.take 16))

/-- `abi.encodePacked(_versionedHash, _openingPoint, _commitment[16:144])` (`:129-133`, `:198`). -/
def precompileInput (vh : UInt256) (chunk : Bytes) : Bytes :=
  toB32 vh ++ toB32 (openingPoint chunk) ++ (chunk.drop PUBDATA_COMMITMENT_CLAIMED_VALUE_OFFSET).take
    (PUBDATA_COMMITMENT_SIZE - PUBDATA_COMMITMENT_CLAIMED_VALUE_OFFSET)

/-- `keccak256(abi.encodePacked(blobVersionedHash, _commitment[:48]))` (`:136`). -/
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

/-- **The loop of `_processBlobDA`** (`:161-179`) over `k` remaining 176-byte records starting at
`rest`, with `versionedHashIndex = idx`. Returns the commitments of these records, in order, and the
final index. Each iteration reads the record's first 144 bytes (`:162`) and its prepublished word at
bytes 144..176 (`:163`), then advances the slice by one record (`:178`). -/
def blobLoop (K : Crypto) (env : TxEnv) (S : RollupState) :
    ℕ → Bytes → ℕ → Option (List UInt256 × ℕ)
  | 0, _, idx => some ([], idx)
  | k + 1, rest, idx =>
    if b32At rest PUBDATA_COMMITMENT_SIZE ≠ 0 then
      -- `:165-171`
      if rollupIsBlobAvailable S (b32At rest PUBDATA_COMMITMENT_SIZE) = some true then
        (blobLoop K env S k (rest.drop BLOB_DA_INPUT_SIZE) idx).map
          (fun r => (b32At rest PUBDATA_COMMITMENT_SIZE :: r.1, r.2))
      else none
    else
      -- `:172-175`
      match getPublishedBlobCommitment K env idx (rest.take PUBDATA_COMMITMENT_SIZE) with
      | none => none
      | some c => (blobLoop K env S k (rest.drop BLOB_DA_INPUT_SIZE) (idx + 1)).map
          (fun r => (c :: r.1, r.2))

/-- **`_processBlobDA`** (`:143-187`): the input must be exactly `n` records of 176 bytes; after the
loop, the transaction must carry no further blob (`:183-186`). The result has `max` words (`:148`),
the entries from `n` on zero. -/
def processBlobDA (K : Crypto) (env : TxEnv) (S : RollupState) (n max : ℕ) (rest : Bytes) :
    Option (List UInt256) :=
  -- `:154-156`
  if rest.length ≠ n * BLOB_DA_INPUT_SIZE then none
  else match blobLoop K env S n rest 0 with
    | none => none
    | some (cs, idx) =>
      -- `:183-186`
      if env.blobhash idx ≠ 0 then none
      else some (cs ++ List.replicate (max - n) 0)

/-- The sanity predicate of `RollupL1DAValidator.sol:99-102`: exactly one of the two entries is zero. -/
def rollupPairMismatch (lin com : UInt256) : Bool :=
  (lin == 0 && com != 0) || (lin != 0 && com == 0)

/-- **`RollupL1DAValidator.checkDA`** (`:69-110`). The chain id and batch number are not read. -/
def rollupCheckDA (K : Crypto) (env : TxEnv) (S : RollupState) (h : UInt256) (input : Bytes)
    (max : ℕ) : Option DAOutput :=
  -- `:76-82`
  match processL2 K.keccak h max input with
  | none => none
  | some p =>
    -- `:84`: `l1DaInput[0]` is out of bounds on an empty slice (a panic)
    match p.l1DaInput with
    | [] => none
    | src :: rest =>
      let coms : Option (List UInt256) :=
        -- `:87-88`, `PubdataSource.Blob = 1`
        if src.toNat = 1 then processBlobDA K env S p.blobsProvided max rest
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
        else some ⟨p.stateDiffHash, p.blobsLinearHashes, cs⟩

/-! ## `RelayedSLDAValidator` and `ValidiumL1DAValidator` -/

/-- What the gateway validator reads from its environment. -/
structure GatewayEnv where
  /-- `IL2Bridgehub(L2_BRIDGEHUB_ADDR).getZKChain(chainId)` (`RelayedSLDAValidator.sol:30`). -/
  getZKChain : UInt256 → UInt256

/-- The message relayed to L1: the fields of
`abi.encode(RELAYED_SL_DA_VALIDATOR_VERSION, _chainId, _batchNumber, _pubdata)` (`:42-44`). -/
structure RelayMessage where
  version : ℕ
  chainId : UInt256
  batchNumber : UInt256
  pubdata : Bytes
deriving DecidableEq

/-- `RELAYED_SL_DA_VALIDATOR_VERSION = 0` (`RelayedSLDAValidator.sol:18`). -/
def RELAYED_SL_DA_VALIDATOR_VERSION : ℕ := 0

/-- The sanity predicate of `RelayedSLDAValidator.sol:103-106`, as written there. -/
def relayedPairMismatch (lin com : UInt256) : Bool :=
  (lin != 0 || com != 0) && (lin == 0 || com == 0)

/-- **`RelayedSLDAValidator.checkDA`** (`:48-110`): the output and the relayed message. `caller` is
`msg.sender`. -/
def relayedCheckDA (K : Crypto) (G : GatewayEnv) (caller chainId batchNumber h : UInt256)
    (input : Bytes) (max : ℕ) : Option (DAOutput × RelayMessage) :=
  -- `:57`, `:27-33`
  if G.getZKChain chainId ≠ caller then none
  -- `:66-72`
  else match processL2 K.keccak h max input with
  | none => none
  | some p =>
    -- `:78`: `l1DaInput[0]` panics on an empty slice
    match p.l1DaInput with
    | [] => none
    | src :: rest =>
      -- `:81`, `PubdataSource.Calldata = 0`; otherwise `:95-97`
      if src.toNat ≠ 0 then none
      else match processCalldataDAGateway K.keccak p.blobsProvided p.fullPubdataHash max rest with
      | none => none
      | some (cs, pub) =>
        -- `:102-109`
        if (List.range max).any (fun i =>
            relayedPairMismatch (p.blobsLinearHashes.getD i 0) (cs.getD i 0)) then none
        else some
          (⟨p.stateDiffHash, p.blobsLinearHashes, cs⟩,
           -- `:92`, `:39-45`
           { version := RELAYED_SL_DA_VALIDATOR_VERSION, chainId := chainId,
             batchNumber := batchNumber, pubdata := pub })

/-- **`ValidiumL1DAValidator.checkDA`** (`ValidiumL1DAValidator.sol:9-28`). The chain id, batch
number and `_l2DAValidatorOutputHash` are not read: the model takes no `h`. -/
def validiumCheckDA (input : Bytes) (max : ℕ) : Option DAOutput :=
  -- `:18-20`
  if input.length ≠ 32 then none
  -- `:21-27`
  else some ⟨b32At input 0, List.replicate max 0, List.replicate max 0⟩

end Contracts.ZKsyncOSCommitterDA
