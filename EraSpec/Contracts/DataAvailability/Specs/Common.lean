import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashPinned

/-!
# Spec: shared byte layer of the DA validators (`CalldataDA`, `CalldataDAGateway`, `DAConstants`)

Source: era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`, under
`l1-contracts/contracts/`. All `file:line` citations below are relative to
`state-transition/data-availability/` unless another directory is named.

This file transcribes the pure helpers that the L1 DA validators share:

* the constants of `DAConstants.sol`, `CalldataDA.sol:17-20` and `common/Config.sol:43`;
* `CalldataDA._processL2RollupDAValidatorOutputHash` (`CalldataDA.sol:29-82`), which parses the
  operator's DA input and checks its prefix against the hash the L2 DA validator returned;
* `CalldataDA._processCalldataDA` (`CalldataDA.sol:90-117`), the L1 calldata branch;
* `CalldataDAGateway._processCalldataDA` (`CalldataDAGateway.sol:12-40`), its override used by
  `RelayedSLDAValidator`;
* the layout of the L2 DA validator's output, as the comment at `CalldataDA.sol:44-48` states it
  (`l2Output`).

## Model boundaries

* Bytes are `List UInt8`. `bytes32(x[a:a+32])` is `b32At x a`, the big-endian value of the 32
  bytes at offset `a`. `uint8(x[i])` is `byteAt x i`. Solidity bounds-checks every calldata slice
  and index; the model does not, because under the guards before each read the read is in bounds
  (the README lists each read with its guard). The two reads no guard of the helper itself covers
  are modelled as reverts: the index `l1DaInput[0]` on an empty slice (in the `checkDA` models) and
  the write `blobCommitments[0]` into an empty array (`processCalldataDA`, `max = 0`).
* `_cloneCalldata(dst, src, n)` (`CalldataDA.sol:123-130`) is `calldatacopy` of `32 n` bytes over a
  fresh zeroed array of `max` words: `wordsAt src n max`. The assembly has no bounds check. Both
  call sites have `n ≤ max` (from `CalldataDA.sol:59-61`) and `32 n` readable bytes (from
  `CalldataDA.sol:67-69` and `CalldataDAGateway.sol:18-20`), so no word is written past the array
  and none is read past the calldata; `wordsAt` is only meaningful under these two bounds.
* `keccak256` is an arbitrary function `Bytes → UInt256` (field `Crypto.keccak`). Nothing about it
  is assumed. Results that need binding are stated in pinned-collision form
  (`AttackVectors.BundleHashEncoding.HashCollision`, reused here).
* The EIP-4844 point-evaluation precompile, including the `abi.decode` of its output and the
  comparison with `BLS_MODULUS` (`RollupL1DAValidator.sol:193-211`), is one oracle
  `Crypto.pointEvalOk : Bytes → Bool` on the exact input bytes the source builds.
* `_maxBlobsSupported` is a natural number. Memory allocation of `new bytes32[](max)` is assumed to
  succeed (out-of-gas is not modelled). No arithmetic in these helpers can overflow: the blob count
  is one byte, so every product is below `2^40`.
* A revert is `none`. The order of the guards is the source order, but since every guard reverts the
  whole call, only the set of accepted inputs matters to the results.
-/

namespace Contracts.DataAvailability

open AttackVectors.BundleHashEncoding

/-- Raw bytes (calldata or memory). -/
abbrev Bytes := List UInt8

/-- An EVM address, kept as a word (a superset of the 160-bit range). -/
abbrev Address := UInt256

/-! ## Constants -/

/-- `BLOB_SIZE_BYTES = 126_976` (`common/Config.sol:43`). -/
def BLOB_SIZE_BYTES : ℕ := 126976

/-- `PUBDATA_COMMITMENT_SIZE = 144` (`DAConstants.sol:11`): opening point (16) ‖ claimed value (32)
‖ commitment (48) ‖ proof (48). -/
def PUBDATA_COMMITMENT_SIZE : ℕ := 144

/-- `PUBDATA_COMMITMENT_CLAIMED_VALUE_OFFSET = 16` (`DAConstants.sol:14`). -/
def PUBDATA_COMMITMENT_CLAIMED_VALUE_OFFSET : ℕ := 16

/-- `PUBDATA_COMMITMENT_COMMITMENT_OFFSET = 48` (`DAConstants.sol:17`). -/
def PUBDATA_COMMITMENT_COMMITMENT_OFFSET : ℕ := 48

/-- `BLOB_DA_INPUT_SIZE = PUBDATA_COMMITMENT_SIZE + 32` (`DAConstants.sol:20`). -/
def BLOB_DA_INPUT_SIZE : ℕ := PUBDATA_COMMITMENT_SIZE + 32

/-- `BLOB_EXPIRATION_BLOCKS = (4096 * 32) / 2` (`DAConstants.sol:28`). -/
def BLOB_EXPIRATION_BLOCKS : ℕ := (4096 * 32) / 2

/-- `BLOB_DATA_OFFSET = 65` (`CalldataDA.sol:17`): state diff hash, full pubdata hash, blob count. -/
def BLOB_DATA_OFFSET : ℕ := 65

/-- `BLOB_COMMITMENT_SIZE = 32` (`CalldataDA.sol:20`). -/
def BLOB_COMMITMENT_SIZE : ℕ := 32

/-! ## Byte helpers -/

/-- A `bytes32` value as its 32 big-endian bytes (`abi.encodePacked(bytes32)`). -/
def toB32 (x : UInt256) : Bytes := toBytesBE 32 x.val

/-- `bytes32(b[off:off+32])`: the big-endian value of the 32 bytes at `off`. -/
def b32At (b : Bytes) (off : ℕ) : UInt256 := Nat.toUInt256 (fromBytesBE ((b.drop off).take 32))

/-- `uint256(uint8(b[i]))`. -/
def byteAt (b : Bytes) (i : ℕ) : ℕ := (b.getD i 0).toNat

/-! ## The cryptographic environment -/

/-- The two primitives the validators call. Both are arbitrary. -/
structure Crypto where
  /-- `keccak256`. -/
  keccak : Bytes → UInt256
  /-- The point-evaluation precompile at `0x0A` on the given input bytes: the `staticcall`
  succeeded and the second returned word equals `BLS_MODULUS`
  (`RollupL1DAValidator.sol:198-210`). -/
  pointEvalOk : Bytes → Bool

/-! ## The validator output (`IL1DAValidator.sol:11-21`) -/

/-- `L1DAValidatorOutput`. -/
structure Output where
  stateDiffHash : UInt256
  blobsLinearHashes : List UInt256
  blobsOpeningCommitments : List UInt256
deriving DecidableEq

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

/-- `new bytes32[](max)` followed by `_cloneCalldata(dst, src, n)` (`CalldataDA.sol:123-130`): an
array of `max` words whose first `n` are the consecutive 32-byte words of `src`, the rest zero. -/
def wordsAt (src : Bytes) (n max : ℕ) : List UInt256 :=
  (List.range max).map fun i => if i < n then b32At src (32 * i) else 0

/-- `blobsLinearHashes`: an array of length `max` (`CalldataDA.sol:65`) whose first `n` entries are
copied from `_operatorDAInput[BLOB_DATA_OFFSET:]` by `_cloneCalldata` (`:71`), the rest zero. -/
def linearOf (input : Bytes) (n max : ℕ) : List UInt256 :=
  wordsAt (input.drop BLOB_DATA_OFFSET) n max

/-- **`_processL2RollupDAValidatorOutputHash`** (`CalldataDA.sol:29-82`), guards in source order.
`checkHash = false` deletes the keccak check at `:76-78`; it exists only for the countermodel
`Properties.OutputHashCheckLoadBearing`. The source is `processL2 = processL2With true`. -/
def processL2With (checkHash : Bool) (keccak : Bytes → UInt256) (h : UInt256) (max : ℕ)
    (input : Bytes) : Option L2Parsed :=
  -- `:51-53`
  if input.length < BLOB_DATA_OFFSET then none
  -- `:59-61`
  else if max < byteAt input 64 then none
  -- `:67-69`
  else if input.length < l2PrefixLen input then none
  -- `:76-78`
  else if checkHash = true ∧ keccak (l2Prefix input) ≠ h then none
  else some
    { stateDiffHash := b32At input 0                         -- `:55`
      fullPubdataHash := b32At input 32                      -- `:56`
      blobsLinearHashes := linearOf input (byteAt input 64) max
      blobsProvided := byteAt input 64                        -- `:57`
      l1DaInput := input.drop (l2PrefixLen input) }           -- `:81`

/-- The source's `_processL2RollupDAValidatorOutputHash`. -/
abbrev processL2 := processL2With true

/-! ## The L1 calldata branch (`CalldataDA.sol:90-117`) -/

/-- **`CalldataDA._processCalldataDA`**: exactly one blob, the last 32 bytes are the blob
commitment, the rest is the pubdata, at most `BLOB_SIZE_BYTES` long, whose keccak must be the full
pubdata hash. Returns the commitments array (length `max`, only entry 0 set) and the pubdata.
The write `blobCommitments[0] = …` (`:116`) panics on an array of length `max = 0`; from `checkDA`
this cannot happen (`1 = blobsProvided ≤ max`). -/
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

/-! ## The gateway calldata branch (`CalldataDAGateway.sol:12-40`) -/

/-- **`CalldataDAGateway._processCalldataDA`**: `n` commitments of 32 bytes at the end, the pubdata
before them, at most `n * BLOB_SIZE_BYTES` long, whose keccak must be the full pubdata hash.
The commitments array has length `max`; its first `n` entries are copied (`:39`). The copy is the
unchecked `_cloneCalldata`: with `n > max` the source writes past the array. The model truncates
there and is only meaningful for `n ≤ max`, which the one caller guarantees. -/
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

/-! ## What the L2 DA validator returns -/

/-- **THE L2 DA VALIDATOR'S OUTPUT**, in the layout `CalldataDA.sol:44-48` documents:
the state diff hash, the full pubdata hash, the one-byte number of blobs, then one 32-byte linear
hash per blob. `_l2DAValidatorOutputHash` is meant to be `keccak256` of these bytes. The L2 side is
not modelled; the results take an honest `(sd, fp, lin)` as a parameter. -/
def l2Output (sd fp : UInt256) (lin : List UInt256) : Bytes :=
  toB32 sd ++ toB32 fp ++ [UInt8.ofNat lin.length] ++ (lin.map toB32).flatten

/-- The array `lin` padded with zeros to length `max`: what an honest `blobsLinearHashes` is. -/
def padTo (lin : List UInt256) (max : ℕ) : List UInt256 := lin ++ List.replicate (max - lin.length) 0

/-- `uint8(l1DaInput[0])`, the pubdata source byte (`PubdataSource`: `Calldata = 0`, `Blob = 1`,
`IL1DAValidator.sol:6-9`), at offset `ptr` of the operator input. -/
def sourceByte (input : Bytes) : ℕ := byteAt input (l2PrefixLen input)

/-- `l1DaInput[1:]`: the part of the operator input after the source byte. -/
def l1Rest (input : Bytes) : Bytes := input.drop (l2PrefixLen input + 1)

/-- The pubdata the L1 calldata branch hashes: `l1Rest` without its last 32 bytes
(`CalldataDA.sol:108`). -/
def calldataPubdata (input : Bytes) : Bytes :=
  (l1Rest input).take ((l1Rest input).length - BLOB_COMMITMENT_SIZE)

/-- The pubdata the gateway branch hashes and relays: `l1Rest` without its last `32 n` bytes
(`CalldataDAGateway.sol:26`). -/
def gatewayPubdata (input : Bytes) : Bytes :=
  (l1Rest input).take ((l1Rest input).length - byteAt input 64 * BLOB_COMMITMENT_SIZE)

end Contracts.DataAvailability
