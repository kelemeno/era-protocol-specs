import EraSpec.Contracts.DataEncoding.Specs.TxDataHash

/-!
# Properties: the deposit record hash, the legacy format, and the burn data

Statements about `EraSpec.Contracts.DataEncoding.Specs.TxDataHash`. Proofs are in
`EraSpec.Contracts.DataEncoding.Proofs.TxDataHash`.

None of these takes a premise on keccak. The only premise anywhere is the EVM bound
`transferData.length < 2^256` in the injectivity results: the length word is 256 bits.

Groups, in order:

* **(f) Lengths and first bytes.** The record preimage is `129 + 32·⌈len/32⌉` bytes: always
  `≡ 1 (mod 32)` and at least 129, and at least 161 exactly when the transfer data is nonempty.
  The legacy preimage is 96 bytes. The record starts with `0x01` and the legacy one with `0x00`.
* **(f) Injectivity and separation.** The record preimage determines `(sender, assetId,
  transferData)`; the legacy preimage determines its triple; and no record preimage is a legacy
  preimage. This is the separation the comment at `DataEncoding.sol:165-167` claims, by its own
  argument (byte 0) and also by length.
* **(f) At the hash level.** Equal record hashes mean the same record or a keccak collision on the
  two named preimages; a record hash equal to a legacy hash is a keccak collision on the two
  named preimages; a zero record hash is a zero preimage. Witnesses show none of these
  disjuncts is a tautology.
* **(g) The burn data.** `decodeBridgeBurnData` accepts exactly the 96-byte strings whose two
  address words fit 160 bits, and on those it inverts `encodeBridgeBurnData`. The two-field
  tuple the NatSpec of `bridgeBurn` describes is rejected.
-/

namespace Contracts.DataEncoding

open AttackVectors.BundleHashEncoding (fromBytesBE HashCollision)

/-! ## (f) Lengths and first bytes -/

/-- **(f) THE RECORD PREIMAGE'S LENGTH.** One version byte, four 32-byte words, and the transfer
data padded to a multiple of 32: `129 + 32 · ⌈len / 32⌉` bytes. -/
def Properties.TxDataPreimageLength : Prop :=
  ∀ (s : Addr) (a : UInt256) (d : List UInt8),
    (txDataPreimage s a d).length = 129 + 32 * ((d.length + 31) / 32)

/-- **(f) ITS SHAPE: `≡ 1 (mod 32)` AND AT LEAST 129.** 129 is attained (see
`TxDataPreimageMinimumIs129`), so 129 is the exact lower bound. -/
def Properties.TxDataPreimageLengthShape : Prop :=
  ∀ (s : Addr) (a : UInt256) (d : List UInt8),
    (txDataPreimage s a d).length % 32 = 1 ∧ 129 ≤ (txDataPreimage s a d).length

/-- **(f) AT LEAST 161 BYTES EXACTLY WHEN THE TRANSFER DATA IS NONEMPTY.** This is the correct
form of the bound "≥ 161". -/
def Properties.TxDataPreimageAtLeast161IffNonempty : Prop :=
  ∀ (s : Addr) (a : UInt256) (d : List UInt8), 161 ≤ (txDataPreimage s a d).length ↔ d ≠ []

/-- **(f) "AT LEAST 161 BYTES" FAILS FOR EMPTY TRANSFER DATA.** With `_transferData` empty the
record preimage is 129 bytes: the version byte, three heads and a zero length word. Nothing in
`encodeTxDataHash` or at its call sites forbids empty transfer data (a custom asset handler may
accept it). -/
def Properties.TxDataPreimageMinimumIs129 : Prop :=
  ∀ (s : Addr) (a : UInt256), (txDataPreimage s a []).length = 129

/-- **(f) THE LEGACY PREIMAGE IS 96 BYTES**: three static words. -/
def Properties.LegacyPreimageLength : Prop :=
  ∀ (account token : Addr) (amount : UInt256),
    (legacyTxDataPreimage account token amount).length = 96

/-- **(f) THE FIRST BYTES.** A record preimage starts with `NEW_ENCODING_VERSION = 0x01`. A legacy
preimage starts with the most significant byte of an address word, which is zero. -/
def Properties.TxDataFirstBytes : Prop :=
  (∀ (s : Addr) (a : UInt256) (d : List UInt8), (txDataPreimage s a d).head? = some 0x01)
  ∧ (∀ (account token : Addr) (amount : UInt256),
      (legacyTxDataPreimage account token amount).head? = some 0x00)

/-! ## (f) Injectivity and separation -/

/-- **(f) THE RECORD PREIMAGE DETERMINES THE RECORD.** Equal record preimages have equal sender,
asset id and transfer data. The premise is the EVM bound on the length word. -/
def Properties.NewPreimageInjective : Prop :=
  ∀ (s s' : Addr) (a a' : UInt256) (d d' : List UInt8),
    d.length < 2 ^ 256 → d'.length < 2 ^ 256 →
    txDataPreimage s a d = txDataPreimage s' a' d' → s = s' ∧ a = a' ∧ d = d'

/-- **(f) THE LEGACY PREIMAGE DETERMINES ITS TRIPLE.** -/
def Properties.LegacyPreimageInjective : Prop :=
  ∀ (account account' token token' : Addr) (amount amount' : UInt256),
    legacyTxDataPreimage account token amount = legacyTxDataPreimage account' token' amount' →
      account = account' ∧ token = token' ∧ amount = amount'

/-- **(f) A RECORD PREIMAGE IS NEVER A LEGACY PREIMAGE.** The two differ in length (at least 129
bytes against 96) and in their first byte (`0x01` against `0x00`), so they differ. The first-byte
argument is the one `DataEncoding.sol:165-167` gives; the length argument is a second,
independent one. No premise. -/
def Properties.NewNeverLegacy : Prop :=
  ∀ (s : Addr) (a : UInt256) (d : List UInt8) (account token : Addr) (amount : UInt256),
    (txDataPreimage s a d).length ≠ (legacyTxDataPreimage account token amount).length
    ∧ (txDataPreimage s a d).head? ≠ (legacyTxDataPreimage account token amount).head?
    ∧ txDataPreimage s a d ≠ legacyTxDataPreimage account token amount

/-! ## (f) At the hash level -/

/-- **(f) A RECORD HASH BINDS ITS RECORD, OR KECCAK COLLIDES ON THE TWO NAMED PREIMAGES.** If a
claim's recomputed `encodeTxDataHash` equals a recorded one, the claim names the recorded
`(sender, assetId, transferData)`, or keccak collides on the two record preimages. This is the
binding the nullifier's claim check (`L1Nullifier.sol:237-248`) relies on. -/
def Properties.TxDataHashBindsOrCollision : Prop :=
  ∀ (keccak : Keccak) (s s' : Addr) (a a' : UInt256) (d d' : List UInt8),
    d.length < 2 ^ 256 → d'.length < 2 ^ 256 →
    encodeTxDataHash keccak s a d = encodeTxDataHash keccak s' a' d' →
      (s = s' ∧ a = a' ∧ d = d')
      ∨ HashCollision keccak (txDataPreimage s a d) (txDataPreimage s' a' d')

/-- **(f) A RECORD HASH EQUALS A LEGACY HASH ONLY THROUGH A KECCAK COLLISION ON THE TWO NAMED
PREIMAGES.** So a legacy record can be matched by a new-format claim only by a keccak collision
between that record's preimage and the claim's. No premise. -/
def Properties.NewHashMatchesLegacyOnlyByCollision : Prop :=
  ∀ (keccak : Keccak) (s : Addr) (a : UInt256) (d : List UInt8) (account token : Addr)
    (amount : UInt256),
    encodeTxDataHash keccak s a d = legacyTxDataHash keccak account token amount →
      HashCollision keccak (txDataPreimage s a d) (legacyTxDataPreimage account token amount)

/-- **(f) A ZERO RECORD HASH IS A ZERO PREIMAGE.** The nullifier reads `depositHappened == 0` as
"no record" (`L1Nullifier.sol:164`) and deletes a claimed slot back to zero (`:250`). A record
hash is zero only when keccak sends the named record preimage to zero. -/
def Properties.TxDataHashZeroIsPreimageEvent : Prop :=
  ∀ (keccak : Keccak) (s : Addr) (a : UInt256) (d : List UInt8),
    encodeTxDataHash keccak s a d = 0 ↔ ZeroPreimage keccak (txDataPreimage s a d)

/-- **(f) THE HASH-LEVEL DISJUNCTS ARE NOT TAUTOLOGIES.** One keccak, two different records and
one legacy record, such that:

* the two records' hashes differ, and keccak does not collide on their two preimages;
* the first record's hash differs from the legacy hash, with no collision on those two
  preimages either;
* no hash is zero.

(The keccak reads only the input length; it is a stand-in, not a hash.) -/
def Properties.TxDataHashWitness : Prop :=
  ∃ (keccak : Keccak) (s s' : Addr) (a a' : UInt256) (d d' : List UInt8) (account token : Addr)
    (amount : UInt256),
    d.length < 2 ^ 256 ∧ d'.length < 2 ^ 256
    ∧ ¬ (s = s' ∧ a = a' ∧ d = d')
    ∧ encodeTxDataHash keccak s a d ≠ encodeTxDataHash keccak s' a' d'
    ∧ ¬ HashCollision keccak (txDataPreimage s a d) (txDataPreimage s' a' d')
    ∧ encodeTxDataHash keccak s a d ≠ legacyTxDataHash keccak account token amount
    ∧ ¬ HashCollision keccak (txDataPreimage s a d) (legacyTxDataPreimage account token amount)
    ∧ ¬ ZeroPreimage keccak (txDataPreimage s a d)
    ∧ ¬ ZeroPreimage keccak (txDataPreimage s' a' d')

/-- **(f) THE COLLISION DISJUNCT CANNOT BE DROPPED.** Under a colliding keccak two different
records have one hash, so a claim for one passes the check against the other's record; and a
record hash can equal a legacy hash. This instance satisfies every premise of
`TxDataHashBindsOrCollision` and of `NewHashMatchesLegacyOnlyByCollision` with the first
disjunct false. -/
def Properties.TxDataHashCollisionDisjunctNeeded : Prop :=
  ∃ (keccak : Keccak) (s s' : Addr) (a a' : UInt256) (d d' : List UInt8) (account token : Addr)
    (amount : UInt256),
    d.length < 2 ^ 256 ∧ d'.length < 2 ^ 256
    ∧ ¬ (s = s' ∧ a = a' ∧ d = d')
    ∧ encodeTxDataHash keccak s a d = encodeTxDataHash keccak s' a' d'
    ∧ encodeTxDataHash keccak s a d = legacyTxDataHash keccak account token amount

/-! ## (g) The burn data -/

/-- **(g) THE DECODER ACCEPTS EXACTLY THE ENCODINGS, AND INVERTS THE ENCODER.**
`decodeBridgeBurnData data` returns `b` iff `data` is `encodeBridgeBurnData b`. So it accepts
exactly the byte strings `encodeBridgeBurnData` produces, and on those it returns the encoded
value. -/
def Properties.BurnDataDecodeIffEncode : Prop :=
  ∀ (data : List UInt8) (b : NativeTokenVaultBase.BurnData),
    decodeBridgeBurnData data = some b ↔ data = encodeBridgeBurnData b

/-- **(g) THE BURN DATA IS EXACTLY 96 BYTES.** Every encoding is 96 bytes; the decoder rejects
every other length; and it decodes every encoding back to its value. -/
def Properties.BurnDataLength : Prop :=
  (∀ b : NativeTokenVaultBase.BurnData, (encodeBridgeBurnData b).length = 96)
  ∧ (∀ data : List UInt8, data.length ≠ 96 → decodeBridgeBurnData data = none)
  ∧ (∀ b : NativeTokenVaultBase.BurnData, decodeBridgeBurnData (encodeBridgeBurnData b) = some b)

/-- **(g) WHAT THE DECODER ACCEPTS, EXACTLY.** It returns iff the data is 96 bytes and its second
and third words (the receiver and the token) fit 160 bits. -/
def Properties.BurnDataAcceptsIff : Prop :=
  ∀ data : List UInt8,
    decodeBridgeBurnData data ≠ none ↔
      data.length = 96 ∧ fromBytesBE ((data.drop 32).take 32) < 2 ^ 160
        ∧ fromBytesBE ((data.drop 64).take 32) < 2 ^ 160

/-- **(g) THE DOCUMENTED TWO-FIELD TUPLE IS REJECTED.** The NatSpec of `bridgeBurn` says `_data` is
"the tuple of _depositAmount and _receiver" (`NativeTokenVaultBase.sol:313-314`,
`bridge/interfaces/IAssetHandler.sol:32-33`). `abi.encode(amount, receiver)` is 64 bytes, and
`decodeBridgeBurnData` rejects it. -/
def Properties.TwoFieldBurnDataRejected : Prop :=
  ∀ (amount : UInt256) (receiver : Addr),
    decodeBridgeBurnData (encWord amount ++ encAddr receiver) = none

/-- **(g) NINETY-SIX BYTES ARE NOT ENOUGH.** A 96-byte string whose receiver word does not fit 160
bits is rejected, so the length check alone does not decide acceptance. -/
def Properties.BurnDataLengthNotSufficient : Prop :=
  ∃ data : List UInt8, data.length = 96 ∧ decodeBridgeBurnData data = none

end Contracts.DataEncoding
