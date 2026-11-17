import EraSpec.Protocol.ZKsyncOSDA.Specs.Validators

/-!
# Spec: what `CommitterFacet` checks of a DA validator's output on ZKsync OS

Source: era-contracts `draft/v0.35.0` at `b17415d20`,
`l1-contracts/contracts/state-transition/chain-deps/facets/Committer.sol`. In `_commitOneBatch` the
committer calls the chain's configured validator (`:179-185`):

    checkDA(s.chainId, _newBatch.batchNumber, _newBatch.daCommitment, _newBatch.operatorDAInput,
            TOTAL_BLOBS_IN_COMMITMENT)

with `TOTAL_BLOBS_IN_COMMITMENT = 16` (`chain-interfaces/IExecutor.sol:12`). It then discards the
output after two checks (`:190-210`): the two arrays have equal length, which is 0 or 16, and every
entry of both is zero. Nothing else of the output is read; the comment at `:176-178` says so.

The batch's `daCommitmentScheme` must equal the chain's stored scheme (`:230-232`), and
`daCommitmentScheme` and `daCommitment` are hashed into the batch output hash (`:291-311`), which
enters the proof's public input (`:253-258`, `:320-328`). So the proof authenticates the pair
`(scheme, daCommitment)`; what the ZKsync OS program computes for it is off-chain and not modelled.
The validator/scheme pair is set by the chain admin with no compatibility check between the two
(`Admin.sol:387-401`); for a permanent rollup the pair must be allowed by `RollupDAManager`
(`Admin.sol:396-398`, `RollupDAManager.sol:58-78`).

This file defines, for each validator, `…Accepted`: the validator's `checkDA` returns, with
`_maxBlobsSupported = 16`, and the committer's two checks pass on its output. Every other check of
`_commitOneBatch` only adds conditions, so a committed batch satisfies `…Accepted` of its chain's
validator for its `daCommitment` and `operatorDAInput`.

## The program's side

`l2Output sd fp lin` is the layout `CalldataDA.sol:44-48` documents for the preimage of
`_l2DAValidatorOutputHash`: the state diff hash, the full pubdata hash, the one-byte number of blobs,
then one 32-byte linear hash per blob. Under the `BLOBS_AND_PUBDATA_KECCAK256` scheme the results
take the batch's `daCommitment` to be `keccak (l2Output sd (keccak pub) lin)` for the batch's pubdata
`pub` and some `sd`, `lin` the program chooses. That form, and the premise on `lin` that some
results add, are statements about the off-chain program, named where they are used.

## Named events

* `HashCollision` (from `InteropDataEncoding`) on two inputs the statement names.
* `firstBlobCommitmentPreimage env input`: the keccak input of the blob commitment the rollup
  validator computes for the first blob record of `input` (`RollupL1DAValidator.sol:136`). The
  committer rejects a nonzero commitment, so the blob branch with at least one record passes only
  if keccak maps this named input to zero.
-/

namespace Contracts.ZKsyncOSCommitterDA

open AttackVectors.BundleHashEncoding
open Contracts.ZKsyncOSBlobsDA (Bytes toB32 b32At DAOutput TxEnv encWords)

/-- `TOTAL_BLOBS_IN_COMMITMENT = 16` (`chain-interfaces/IExecutor.sol:12`). -/
def TOTAL_BLOBS_IN_COMMITMENT : ℕ := 16

/-- **THE COMMITTER'S CHECK OF THE VALIDATOR OUTPUT** (`Committer.sol:190-210`). Revert unless the
two arrays have equal length and that length is 0 or `TOTAL_BLOBS_IN_COMMITMENT` (`:190-200`); then
revert if any entry of either array is nonzero (`:201-210`). -/
def committerDACheck (o : DAOutput) : Bool :=
  !(o.blobsLinearHashes.length != o.blobsOpeningCommitments.length
      || (o.blobsLinearHashes.length != 0
          && o.blobsLinearHashes.length != TOTAL_BLOBS_IN_COMMITMENT))
    && (List.range o.blobsLinearHashes.length).all (fun i =>
        o.blobsLinearHashes.getD i 0 == 0 && o.blobsOpeningCommitments.getD i 0 == 0)

/-! ## Acceptance through each validator -/

/-- **ACCEPTED BY `RollupL1DAValidator` AND THE COMMITTER.** -/
def RollupAccepted (K : Crypto) (env : TxEnv) (S : RollupState) (h : UInt256) (input : Bytes) :
    Prop :=
  ∃ o, rollupCheckDA K env S h input TOTAL_BLOBS_IN_COMMITMENT = some o ∧ committerDACheck o = true

/-- **ACCEPTED BY `RelayedSLDAValidator` AND THE COMMITTER**, with relayed message `msg`. -/
def RelayedAccepted (K : Crypto) (G : GatewayEnv) (caller chainId batchNumber h : UInt256)
    (input : Bytes) (msg : RelayMessage) : Prop :=
  ∃ o, relayedCheckDA K G caller chainId batchNumber h input TOTAL_BLOBS_IN_COMMITMENT
      = some (o, msg) ∧ committerDACheck o = true

/-- **ACCEPTED BY `ValidiumL1DAValidator` AND THE COMMITTER.** -/
def ValidiumAccepted (input : Bytes) : Prop :=
  ∃ o, validiumCheckDA input TOTAL_BLOBS_IN_COMMITMENT = some o ∧ committerDACheck o = true

/-- **ACCEPTED BY `BlobsL1DAValidatorZKsyncOS` AND THE COMMITTER.** -/
def BlobsAccepted (K : Crypto) (env : TxEnv) (S : Contracts.ZKsyncOSBlobsDA.VState) (h : UInt256)
    (input : Bytes) : Prop :=
  ∃ o, Contracts.ZKsyncOSBlobsDA.checkDA K.keccak env S h input = some o ∧ committerDACheck o = true

/-! ## Input shapes -/

/-- **THE L2 DA OUTPUT LAYOUT** (`CalldataDA.sol:44-48`): state diff hash, full pubdata hash, the
one-byte blob count, one 32-byte linear hash per blob. -/
def l2Output (sd fp : UInt256) (lin : List UInt256) : Bytes :=
  toB32 sd ++ toB32 fp ++ [UInt8.ofNat lin.length] ++ encWords lin

/-- `l1DaInput[1:]` (`RollupL1DAValidator.sol:88`, `:90`): the input after the prefix and the source
byte. -/
def l1Rest (input : Bytes) : Bytes := input.drop (l2PrefixLen input + 1)

/-- The pubdata the L1 calldata branch hashes: `l1Rest` without its last 32 bytes
(`CalldataDA.sol:108`). -/
def calldataPubdata (input : Bytes) : Bytes :=
  (l1Rest input).take ((l1Rest input).length - BLOB_COMMITMENT_SIZE)

/-- **THE KECCAK INPUT OF THE FIRST BLOB COMMITMENT**: `blobhash(0) ‖ record[0:48]` for the first
176-byte record after the source byte (`RollupL1DAValidator.sol:136`, `:162`). -/
def firstBlobCommitmentPreimage (env : TxEnv) (input : Bytes) : Bytes :=
  toB32 (env.blobhash 0) ++ (l1Rest input).take PUBDATA_COMMITMENT_COMMITMENT_OFFSET

/-- **THE ZERO-BLOB SHAPE.** A 65-byte prefix with blob count 0, then the blob source byte `1`, and
nothing else; no blob attached; `h` is keccak of the prefix. `fp` is compared with nothing. -/
def RollupZeroBlobForm (K : Crypto) (env : TxEnv) (h : UInt256) (input : Bytes) : Prop :=
  ∃ sd fp : UInt256, input = l2Output sd fp [] ++ [1] ∧ env.blobhash 0 = 0
    ∧ h = K.keccak (l2Output sd fp [])

/-- **THE CALLDATA SHAPE.** A prefix with blob count 1 and a zero linear hash, the calldata source
byte `0`, the pubdata `pub` (at most `BLOB_SIZE_BYTES`) and a zero 32-byte blob commitment;
`keccak pub` is the prefix's full pubdata hash and `h` is keccak of the prefix. -/
def RollupCalldataForm (K : Crypto) (h : UInt256) (input : Bytes) : Prop :=
  ∃ (sd fp : UInt256) (pub : Bytes), input = l2Output sd fp [0] ++ [0] ++ pub ++ toB32 0
    ∧ pub.length ≤ BLOB_SIZE_BYTES ∧ K.keccak pub = fp ∧ h = K.keccak (l2Output sd fp [0])

/-- **`pub` IS IN THE COMMIT CALLDATA**: the input has the calldata shape with pubdata `pub`. -/
def CalldataCarries (input pub : Bytes) : Prop :=
  ∃ sd fp : UInt256, input = l2Output sd fp [0] ++ [0] ++ pub ++ toB32 0

/-- **THE GATEWAY SHAPE.** A prefix with blob count `n ≤ 16` and zero linear hashes, the calldata
source byte `0`, the pubdata `pub` (at most `n * BLOB_SIZE_BYTES`) and `n` zero 32-byte commitments;
`keccak pub` is the prefix's full pubdata hash, `h` is keccak of the prefix, and the relayed message
carries `pub`. The caller is the chain's diamond as the gateway's bridgehub reports it. -/
def RelayedForm (K : Crypto) (G : GatewayEnv) (caller chainId batchNumber h : UInt256)
    (input : Bytes) (msg : RelayMessage) : Prop :=
  G.getZKChain chainId = caller ∧
  ∃ (sd fp : UInt256) (n : ℕ) (pub : Bytes), n ≤ TOTAL_BLOBS_IN_COMMITMENT
    ∧ input = l2Output sd fp (List.replicate n 0) ++ [0] ++ pub ++ encWords (List.replicate n 0)
    ∧ pub.length ≤ n * BLOB_SIZE_BYTES ∧ K.keccak pub = fp
    ∧ h = K.keccak (l2Output sd fp (List.replicate n 0))
    ∧ msg = ⟨RELAYED_SL_DA_VALIDATOR_VERSION, chainId, batchNumber, pub⟩

end Contracts.ZKsyncOSCommitterDA
