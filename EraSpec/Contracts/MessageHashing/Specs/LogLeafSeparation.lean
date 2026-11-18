import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashPinned
import EraSpec.Core.Word

/-!
# Spec: the L2 log leaf preimage, and what separates a status log from every other log

Source: era-contracts `draft/v0.35.0` head `b17415d20`. Paths are relative to
`l1-contracts/contracts/`; `MH` is `common/libraries/MessageHashing.sol`. The functions below are
unchanged at `main` `70096e2ea`.

## The source

An L2 → L1 log is the struct `L2Log` (`common/Messaging.sol:27-34`):

    struct L2Log { uint8 l2ShardId; bool isService; uint16 txNumberInBatch;
                   address sender; bytes32 key; bytes32 value; }

and the leaf of the batch's logs tree is (`MH:64-68`)

    keccak256(abi.encodePacked(_log.l2ShardId, _log.isService, _log.txNumberInBatch,
                               _log.sender, _log.key, _log.value))

an 88-byte preimage: 1 + 1 + 2 + 20 + 32 + 32 (`L2_TO_L1_LOG_SERIALIZE_SIZE = 88`,
`common/Config.sol:23-24`). Two kinds of log are built on L1 to be checked against that tree:

* the **status log** of an L1 → L2 transaction (`getL2LogFromL1ToL2Transaction`, `MH:39-62`):
  shard 0, `isService = true`, the transaction's number in its batch, sender
  `L2_BOOTLOADER_ADDRESS = 0x8001` (`common/l2-helpers/L2ContractAddresses.sol:6, 41`),
  key the L2 transaction hash, value `bytes32(uint256(_status))`, which is 0 for
  `TxStatus.Failure` and 1 for `TxStatus.Success` (`common/Messaging.sol:12-15`);
* the log of an **L2 → L1 message** (`_l2MessageToLog`, `MH:26-37`): shard 0,
  `isService = true`, the message's number in its batch, sender
  `L2_TO_L1_MESSENGER_SYSTEM_CONTRACT_ADDR = 0x8008` (`L2ContractAddresses.sol:56`), key the
  message's L2 sender as a word, value `keccak256(message.data)`.

`L1Nullifier.bridgeRecoverFailedTransfer` (`bridge/L1Nullifier.sol:180-213`) passes
`TxStatus.Failure` (`:202`) to `_verifyAndClearTransfer` (`:218-248`), which requires
`proveL1ToL2TransactionStatusShared` to return `true` (`:222-231`), and then forwards the Failure
result to the asset router (`:206-212`), whose asset handler refunds the deposit. That a Failure
leaf cannot be met by any other log's leaf rests on the byte facts stated in
`../Properties/LogLeafSeparation.lean`.

## Model boundaries

* `keccak : List UInt8 → UInt256` is an arbitrary function; nothing about it is assumed.
  `HashCollision keccak x y` (`InteropDataEncoding/Specs/BundleHashPinned.lean`) says that the two
  named byte strings differ and keccak maps them to the same word.
* `abi.encodePacked` of a `uint8` is that byte, of a `bool` the byte `0x01` or `0x00`, of a
  `uint16` its 2 big-endian bytes, of an `address` its 20 bytes, of a `bytes32` its 32 bytes.
  `toBytesBE` and `word` are the byte models of `BundleHashEncoding` (`SOL-ABI`): this is the
  packed-encoding specification, not the code solc emits.
* `txNumberInBatch` and `sender` are natural numbers in the model; `toBytesBE` keeps their low 2
  and 20 bytes. `LogWellFormed` says they fit their Solidity types, as every value of those types
  does. Results that need the preimage to determine the log take it as a premise.
* `L2Message.sender` is an `address`; `bytes32(uint256(uint160(sender)))` is then the address as a
  word, `Nat.toUInt256 sender` for a well-formed message.
-/

namespace Contracts.MessageHashing

open AttackVectors.BundleHashEncoding (HashCollision toBytesBE word)

/-- `keccak256` over byte strings. An arbitrary function: nothing is assumed about it. -/
abbrev Keccak := List UInt8 → UInt256

/-- The 32-byte big-endian word of a `bytes32` value: `abi.encodePacked` of a `bytes32`, and one
half of `Merkle.efficientHash`'s preimage. -/
abbrev w32 (x : UInt256) : List UInt8 := word x.val

/-- `enum TxStatus { Failure, Success }` (`common/Messaging.sol:12-15`). -/
inductive TxStatus
  | failure
  | success
  deriving DecidableEq, Repr

/-- `bytes32(uint256(_status))` (`MH:60`): the enum's ordinal, `Failure = 0`, `Success = 1`. -/
def TxStatus.toWord : TxStatus → UInt256
  | .failure => 0
  | .success => 1

/-- `L2_BOOTLOADER_ADDRESS = address(SYSTEM_CONTRACTS_OFFSET + 0x01)` with
`SYSTEM_CONTRACTS_OFFSET = 0x8000` (`common/l2-helpers/L2ContractAddresses.sol:6, 41`). -/
def BOOTLOADER_ADDRESS : ℕ := 0x8001

/-- `L2_TO_L1_MESSENGER_SYSTEM_CONTRACT_ADDR = address(SYSTEM_CONTRACTS_OFFSET + 0x08)`
(`L2ContractAddresses.sol:6, 56`). -/
def MESSENGER_ADDRESS : ℕ := 0x8008

/-- `struct L2Log` (`common/Messaging.sol:27-34`). `txNumberInBatch` (a `uint16`) and `sender`
(an `address`) are natural numbers here; `LogWellFormed` bounds them. -/
structure L2Log where
  l2ShardId : UInt8
  isService : Bool
  txNumberInBatch : ℕ
  sender : ℕ
  key : UInt256
  value : UInt256
  deriving DecidableEq

/-- The log's fields fit their Solidity types: `txNumberInBatch < 2^16`, `sender < 2^160`. -/
def LogWellFormed (log : L2Log) : Prop :=
  log.txNumberInBatch < 256 ^ 2 ∧ log.sender < 256 ^ 20

/-- A packed `bool`: one byte, `0x01` or `0x00`. -/
def boolByte (b : Bool) : UInt8 := if b then 1 else 0

/-- **THE LEAF PREIMAGE, 88 BYTES.** `getLeafHashFromLog` (`MH:64-68`):

    keccak256(abi.encodePacked(l2ShardId, isService, txNumberInBatch, sender, key, value))

The fields in order, at byte offsets 0, 1, 2..4, 4..24, 24..56 and 56..88. -/
def logPre (log : L2Log) : List UInt8 :=
  [log.l2ShardId] ++ ([boolByte log.isService] ++ (toBytesBE 2 log.txNumberInBatch
    ++ (toBytesBE 20 log.sender ++ (w32 log.key ++ w32 log.value))))

/-- `MessageHashing.getLeafHashFromLog` (`MH:64-68`): keccak of the leaf preimage. -/
def logLeaf (keccak : Keccak) (log : L2Log) : UInt256 := keccak (logPre log)

/-- **THE STATUS LOG.** `getL2LogFromL1ToL2Transaction(_l2TxNumberInBatch, _l2TxHash, _status)`
(`MH:39-62`): shard 0, `isService = true`, sender the bootloader, key the transaction hash, value
the status word. -/
def statusLog (txNumberInBatch : ℕ) (txHash : UInt256) (status : TxStatus) : L2Log :=
  ⟨0, true, txNumberInBatch, BOOTLOADER_ADDRESS, txHash, status.toWord⟩

/-- `struct L2Message` (`common/Messaging.sol:41-45`). -/
structure L2Message where
  txNumberInBatch : ℕ
  sender : ℕ
  data : List UInt8
  deriving DecidableEq

/-- The message's fields fit their Solidity types: a `uint16` and an `address`. -/
def MessageWellFormed (m : L2Message) : Prop :=
  m.txNumberInBatch < 256 ^ 2 ∧ m.sender < 256 ^ 20

/-- **THE MESSAGE LOG.** `_l2MessageToLog(_message)` (`MH:26-37`): shard 0, `isService = true`,
sender the L2 → L1 messenger, key `bytes32(uint256(uint160(_message.sender)))`, value
`keccak256(_message.data)`. -/
def messageLog (keccak : Keccak) (m : L2Message) : L2Log :=
  ⟨0, true, m.txNumberInBatch, MESSENGER_ADDRESS, Nat.toUInt256 m.sender, keccak m.data⟩

/-- `MessageHashing.getLeafHashFromMessage` (`MH:21-24`). -/
def messageLeaf (keccak : Keccak) (m : L2Message) : UInt256 := logLeaf keccak (messageLog keccak m)

/-- **THE NODE PREIMAGE, 64 BYTES.** `Merkle.efficientHash(_lhs, _rhs)`
(`common/libraries/Merkle.sol:125-131`): `mstore(0x00, _lhs) mstore(0x20, _rhs)
keccak256(0x00, 0x40)`. -/
def nodePre (a b : UInt256) : List UInt8 := w32 a ++ w32 b

/-- `new bytes(L2_TO_L1_LOG_SERIALIZE_SIZE)`: 88 zero bytes. `L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH` is
documented as its keccak (`common/Config.sol:26-27`), and `_getProofData` rejects that leaf hash
(`MH:163-167`). -/
def logDefaultPre : List UInt8 := List.replicate 88 0

/-- The all-zero log: shard 0, `isService = false`, transaction 0, sender 0, key 0, value 0. -/
def zeroLog : L2Log := ⟨0, false, 0, 0, 0, 0⟩

/-! ## Stand-ins for keccak, used by the witnesses only

Neither is a model of keccak. Each has collisions that can be read off, so that a witness can
exhibit a premise holding or a collision predicate being false on a named instance. -/

/-- Hashes a byte string to its length: every two strings of one length collide. -/
def lengthKeccak : Keccak := fun x => Nat.toUInt256 x.length

/-- Hashes the one string `p` to `1` and every other string to `0`. -/
def pointKeccak (p : List UInt8) : Keccak := fun x => if x = p then 1 else 0

end Contracts.MessageHashing
