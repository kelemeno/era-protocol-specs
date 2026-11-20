# MessageHashing

## Headline guarantees

About `common/libraries/MessageHashing.sol` at era-contracts `draft/v0.35.0` head `b17415d20`: the
88-byte leaf preimage `abi.encodePacked(l2ShardId, isService, txNumberInBatch, sender, key, value)` of
an L2 → L1 log (`MH:64-68`), the status log of an L1 → L2 transaction (`MH:39-62`) and the log of an
L2 → L1 message (`MH:27-37`). Keccak is any function; no headline takes a premise on it.
"Well-formed" means the transaction number fits a `uint16` and the sender an `address`.

| Guarantee | Premises | Lean name |
|---|---|---|
| A Failure status leaf is met by the leaf of any other well-formed log (the Success log of the same transaction, another transaction's status, a message) only through a keccak collision on the two named 88-byte preimages | the Failure log's transaction number fits a `uint16`; the other log is well-formed and differs from it; the two leaves are equal | `Contracts.MessageHashing.Properties.FailureLeafOfOtherLogIsCollision` |
| A Success leaf meets a Failure leaf only through a named collision | the two leaves are equal (no well-formedness premise) | `Properties.FailureLeafOfSuccessLogIsCollision` |
| A message leaf meets a status leaf only through a named collision | the two leaves are equal (no well-formedness premise) | `Properties.StatusLeafOfMessageIsCollision` |
| Equal leaves of two well-formed logs pin the log, or keccak collides on the two named preimages | both logs well-formed; the leaves are equal | `Properties.LeafHashPinsLogOrCollision` |
| Equal leaves of two well-formed messages pin the message, or keccak collides on their log preimages or on their bodies | both messages well-formed; the leaves are equal | `Properties.MessageLeafPinsMessageOrCollision` |

Witnesses (`@[witness]`): `StatusLeafCollisionWitness`, `LeafPinningWitness`,
`LogPreimageInjectiveWitness`, `StatusPreimageInjectiveWitness`, `OtherSenderPreimageWitness`.
The L1 interop handler's message log is this model's `messageLog` (`L1InteropHandler` topic
`MessageLog`, `MsgToLogIsMessageLog`).

## Source and scope

Source: `l1-contracts/contracts/common/libraries/MessageHashing.sol` (`MH`) at `b17415d20`, with the
structs it builds (`common/Messaging.sol`: `L2Log`, `L2Message`, `TxStatus`) and the two sender
constants (`common/l2-helpers/L2ContractAddresses.sol:41`, `:56`).

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| LogLeafSeparation | [Specs/LogLeafSeparation.lean](Specs/LogLeafSeparation.lean) | [Properties/LogLeafSeparation.lean](Properties/LogLeafSeparation.lean) | [Proofs/LogLeafSeparation.lean](Proofs/LogLeafSeparation.lean) |

`LogLeafSeparation` models the 88-byte leaf preimage of an L2 → L1 log,
`abi.encodePacked(l2ShardId, isService, txNumberInBatch, sender, key, value)` (`logPre`), the
status log of an L1 → L2 transaction (`statusLog`, sender the bootloader `0x8001`, value the
status word) and the log of an L2 → L1 message (`messageLog`, sender the messenger `0x8008`, value
`keccak(data)`). Keccak is an arbitrary function. No property takes a hash premise.

- (a) Every log preimage is 88 bytes and every node preimage 64 (`LeafAndNodePreimageLengths`,
  the lengths `common/MessageVerification.sol:94-96` relies on); the preimage determines a
  well-formed log (`LogPreimageInjective`; `uint16`/`address` bounds, load-bearing by
  `LogPreimageInjectiveWitness`).
- (b) A Failure preimage is never a Success preimage, for any transaction numbers and hashes
  (`StatusPreimageFailureNeSuccess`); a status preimage determines its transaction number, hash
  and status (`StatusPreimageInjective`); no status preimage is a message preimage
  (`StatusPreimageNeMessagePreimage`, the sender bytes), the padding preimage `new bytes(88)`
  (`StatusPreimageNeDefault`, which also shows that the all-zero log's preimage is the padding
  preimage), or the preimage of any well-formed log with another sender
  (`OtherSenderPreimageNeStatusPreimage`).
- (c) Pinned forms: equal leaf hashes of two well-formed logs pin the log or are a keccak
  collision on their two named 88-byte preimages (`LeafHashPinsLogOrCollision`). Headline:
  a Failure leaf equals another well-formed log's leaf only through such a collision
  (`FailureLeafOfOtherLogIsCollision`; without well-formedness for a Success log,
  `FailureLeafOfSuccessLogIsCollision`, and for any message, `StatusLeafOfMessageIsCollision`).
  Two well-formed messages with equal leaves are equal, or keccak collides on their log
  preimages, or on their bodies (`MessageLeafPinsMessageOrCollision`).
- Witnesses: `StatusLeafCollisionWitness` and `LeafPinningWitness` meet every premise with a
  stand-in keccak (`lengthKeccak`), show each collision disjunct is the one that holds on its
  instance (both message disjuncts are needed), and show the collisions false under another
  stand-in (`pointKeccak`).

The composition with the Merkle proof, the chain batch root and the L2-side premises is
`../MessageVerification/` topic `StatusProof`. Not covered: that solc emits this packed layout
(`SOL-ABI`).
