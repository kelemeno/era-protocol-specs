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
  preimage, by the first byte (the argument of the comment at `DataEncoding.sol:164-166`) and
  also by length.
* **(f) At the hash level.** Equal record hashes mean the same record or a keccak collision on the
  two named preimages; a record hash equal to a legacy hash is a keccak collision on the two
  named preimages; a zero record hash is a zero preimage. A witness shows the collision and
  zero-preimage disjuncts are not tautologies, and a countermodel that the collision disjuncts
  cannot be dropped.
* **(g) The burn data.** `decodeNtvBurnData` accepts exactly the 96-byte strings whose two
  address words fit 160 bits, and on those it inverts `encodeNtvBurnData`. A 64-byte
  `abi.encode(amount, receiver)` is rejected.
* **(f) and (g) together.** A claim whose transfer data the vault's parser accepts and whose
  hash matches an NTV deposit record names that record's sender, asset id and burn data, or
  keccak collides on the two named record preimages.
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

/-- **(f) AT LEAST 161 BYTES EXACTLY WHEN THE TRANSFER DATA IS NONEMPTY.** Nonempty transfer data
adds at least one padded 32-byte word to the 129 bytes of `TxDataPreimageMinimumIs129`. -/
def Properties.TxDataPreimageAtLeast161IffNonempty : Prop :=
  ∀ (s : Addr) (a : UInt256) (d : List UInt8), 161 ≤ (txDataPreimage s a d).length ↔ d ≠ []

/-- **(f) WITH EMPTY TRANSFER DATA THE RECORD PREIMAGE IS 129 BYTES**: the version byte, three
heads and a zero length word, with no data word. `encodeTxDataHash` itself places no condition
on the length of `_transferData`. -/
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
argument is the one `DataEncoding.sol:164-166` gives; the length argument is a second,
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
binding the nullifier's claim check (`L1Nullifier.sol:234-247`) relies on. -/
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
"no record" (`L1Nullifier.sol:160`) and deletes a claimed slot back to zero (`:247`). A record
hash is zero only when keccak sends the named record preimage to zero. -/
def Properties.TxDataHashZeroIsPreimageEvent : Prop :=
  ∀ (keccak : Keccak) (s : Addr) (a : UInt256) (d : List UInt8),
    encodeTxDataHash keccak s a d = 0 ↔ ZeroPreimage keccak (txDataPreimage s a d)

/-- **(f) THE HASH-LEVEL DISJUNCTS ARE NOT TAUTOLOGIES.** There is a keccak and an NTV deposit
record `(s, a, encodeNtvBurnData b)`: sender `s ≠ 0`, asset id `a ≠ 0`, and burn data `b` of a
nonzero amount to a nonzero receiver, such that:

* a claim whose burn data `b'` differs from `b` only in the amount recomputes a different hash,
  and keccak does not collide on the two record preimages;
* the legacy record of the same sender, a nonzero token and the same amount has a different
  hash, and keccak does not collide on that preimage and the record's either;
* neither record hash is zero.

(In the proof the keccak sends the deposit record's preimage to `1` and every other byte
string to `2`; it is a stand-in, not a hash.) -/
def Properties.TxDataHashWitness : Prop :=
  ∃ (keccak : Keccak) (s : Addr) (a : UInt256) (b b' : NativeTokenVaultBase.BurnData)
    (token : Addr),
    s ≠ 0 ∧ a ≠ 0 ∧ b.amount ≠ 0 ∧ b.receiver ≠ 0 ∧ token ≠ 0
    ∧ b'.amount ≠ b.amount ∧ b'.receiver = b.receiver ∧ b'.tokenHint = b.tokenHint
    ∧ encodeTxDataHash keccak s a (encodeNtvBurnData b')
        ≠ encodeTxDataHash keccak s a (encodeNtvBurnData b)
    ∧ ¬ HashCollision keccak (txDataPreimage s a (encodeNtvBurnData b'))
        (txDataPreimage s a (encodeNtvBurnData b))
    ∧ encodeTxDataHash keccak s a (encodeNtvBurnData b) ≠ legacyTxDataHash keccak s token b.amount
    ∧ ¬ HashCollision keccak (txDataPreimage s a (encodeNtvBurnData b))
        (legacyTxDataPreimage s token b.amount)
    ∧ ¬ ZeroPreimage keccak (txDataPreimage s a (encodeNtvBurnData b))
    ∧ ¬ ZeroPreimage keccak (txDataPreimage s a (encodeNtvBurnData b'))

/-- **(f) THE COLLISION DISJUNCTS CANNOT BE DROPPED.** There is a keccak (in the proof, one that
sends every byte string to `1`), an NTV deposit record `(s, a, encodeNtvBurnData b)` (sender
`s ≠ 0`, asset id `a ≠ 0`, burn data `b` of a nonzero amount to a nonzero receiver) and a claim
whose burn data `b'` differs from `b` only in the amount, with one nonzero hash: the claim
recomputes the recorded word, which is what the nullifier's claim check compares. This
satisfies every premise of `TxDataHashBindsOrCollision` (both transfer data are 96 bytes) with
its first disjunct false, since the transfer data differ. The record hash also equals the
legacy hash of the same sender, a nonzero token and the same amount, the premise of
`NewHashMatchesLegacyOnlyByCollision`. -/
def Properties.TxDataHashCollisionDisjunctNeeded : Prop :=
  ∃ (keccak : Keccak) (s : Addr) (a : UInt256) (b b' : NativeTokenVaultBase.BurnData)
    (token : Addr),
    s ≠ 0 ∧ a ≠ 0 ∧ b.amount ≠ 0 ∧ b.receiver ≠ 0 ∧ token ≠ 0
    ∧ b'.amount ≠ b.amount ∧ b'.receiver = b.receiver ∧ b'.tokenHint = b.tokenHint
    ∧ (encodeNtvBurnData b).length < 2 ^ 256 ∧ (encodeNtvBurnData b').length < 2 ^ 256
    ∧ encodeNtvBurnData b' ≠ encodeNtvBurnData b
    ∧ encodeTxDataHash keccak s a (encodeNtvBurnData b')
        = encodeTxDataHash keccak s a (encodeNtvBurnData b)
    ∧ encodeTxDataHash keccak s a (encodeNtvBurnData b) = legacyTxDataHash keccak s token b.amount
    ∧ encodeTxDataHash keccak s a (encodeNtvBurnData b) ≠ 0

/-! ## (g) The burn data -/

/-- **(g) THE DECODER ACCEPTS EXACTLY THE ENCODINGS, AND INVERTS THE ENCODER.**
`decodeNtvBurnData data` returns `b` iff `data` is `encodeNtvBurnData b`. So it accepts
exactly the byte strings `encodeNtvBurnData` produces, and on those it returns the encoded
value. -/
def Properties.BurnDataDecodeIffEncode : Prop :=
  ∀ (data : List UInt8) (b : NativeTokenVaultBase.BurnData),
    decodeNtvBurnData data = some b ↔ data = encodeNtvBurnData b

/-- **(g) THE BURN DATA IS EXACTLY 96 BYTES.** Every encoding is 96 bytes; the decoder rejects
every other length; and it decodes every encoding back to its value. -/
def Properties.BurnDataLength : Prop :=
  (∀ b : NativeTokenVaultBase.BurnData, (encodeNtvBurnData b).length = 96)
  ∧ (∀ data : List UInt8, data.length ≠ 96 → decodeNtvBurnData data = none)
  ∧ (∀ b : NativeTokenVaultBase.BurnData, decodeNtvBurnData (encodeNtvBurnData b) = some b)

/-- **(g) WHAT THE DECODER ACCEPTS, EXACTLY.** It returns iff the data is 96 bytes and its second
and third words (the receiver and the token) fit 160 bits. -/
def Properties.BurnDataAcceptsIff : Prop :=
  ∀ data : List UInt8,
    decodeNtvBurnData data ≠ none ↔
      data.length = 96 ∧ fromBytesBE ((data.drop 32).take 32) < 2 ^ 160
        ∧ fromBytesBE ((data.drop 64).take 32) < 2 ^ 160

/-- **(g) A TWO-WORD TUPLE IS REJECTED.** `abi.encode(amount, receiver)`, types
`(uint256, address)`, is 64 bytes, and `decodeNtvBurnData` rejects it: the vault's burn data is
the three-word tuple `(amount, receiver, maybeTokenAddress)`. -/
def Properties.TwoFieldBurnDataRejected : Prop :=
  ∀ (amount : UInt256) (receiver : Addr),
    decodeNtvBurnData (encWord amount ++ encAddr receiver) = none

/-- **(g) NINETY-SIX BYTES ARE NOT ENOUGH.** A 96-byte string whose receiver word does not fit 160
bits is rejected, so the length check alone does not decide acceptance. -/
def Properties.BurnDataLengthNotSufficient : Prop :=
  ∃ data : List UInt8, data.length = 96 ∧ 2 ^ 160 ≤ fromBytesBE ((data.drop 32).take 32)
    ∧ decodeNtvBurnData data = none

/-! ## (f) and (g) together: a claim against an NTV deposit record -/

/-- **A CLAIM THAT MATCHES AN NTV DEPOSIT RECORD NAMES THAT DEPOSIT, OR KECCAK COLLIDES ON THE TWO
NAMED RECORD PREIMAGES.** Take a record hashed from `(s, a, encodeNtvBurnData b)` and a claim
`(s', a', d')` whose transfer data the vault's parser accepts (`decodeNtvBurnData d' = some b'`)
and whose recomputed hash equals the record's. Then `s' = s`, `a' = a` and `b' = b`, or keccak
collides on the claim's record preimage and the deposit's. No premise on keccak.
(`Specs/TxDataHash.lean` describes how the L1 vault uses these fields after the check: it pays
the decoded amount to the claimed sender. That payment is not modelled here.) -/
def Properties.NtvClaimNamesRecordedDepositOrCollision : Prop :=
  ∀ (keccak : Keccak) (s s' : Addr) (a a' : UInt256) (b b' : NativeTokenVaultBase.BurnData)
    (d' : List UInt8),
    decodeNtvBurnData d' = some b' →
    encodeTxDataHash keccak s' a' d' = encodeTxDataHash keccak s a (encodeNtvBurnData b) →
      (s' = s ∧ a' = a ∧ b' = b)
      ∨ HashCollision keccak (txDataPreimage s' a' d') (txDataPreimage s a (encodeNtvBurnData b))

/-- **ITS PREMISES HOLD, WITH EITHER DISJUNCT.** An NTV deposit record (sender `s ≠ 0`, asset id
`a ≠ 0`, burn data `b` of a nonzero amount to a nonzero receiver) and:

* a keccak under which the record's hash is nonzero and the claim naming that deposit meets
  both premises (its data decodes to `b`, and it recomputes the record's hash; that claim has
  the record's own fields, so the hash equality holds by reflexivity and this half only shows
  the first disjunct is reachable);
* a keccak under which a claim whose burn data `b'` differs from `b` only in the amount meets
  both premises, so the first disjunct is false and keccak collides on the two preimages. -/
def Properties.NtvClaimNamesRecordedDepositOrCollisionWitness : Prop :=
  ∃ (s : Addr) (a : UInt256) (b b' : NativeTokenVaultBase.BurnData),
    s ≠ 0 ∧ a ≠ 0 ∧ b.amount ≠ 0 ∧ b.receiver ≠ 0
    ∧ b'.amount ≠ b.amount ∧ b'.receiver = b.receiver ∧ b'.tokenHint = b.tokenHint
    ∧ (∃ keccak : Keccak,
        encodeTxDataHash keccak s a (encodeNtvBurnData b) ≠ 0
        ∧ decodeNtvBurnData (encodeNtvBurnData b) = some b
        ∧ encodeTxDataHash keccak s a (encodeNtvBurnData b)
            = encodeTxDataHash keccak s a (encodeNtvBurnData b))
    ∧ (∃ keccak : Keccak,
        encodeTxDataHash keccak s a (encodeNtvBurnData b) ≠ 0
        ∧ decodeNtvBurnData (encodeNtvBurnData b') = some b'
        ∧ encodeTxDataHash keccak s a (encodeNtvBurnData b')
            = encodeTxDataHash keccak s a (encodeNtvBurnData b)
        ∧ HashCollision keccak (txDataPreimage s a (encodeNtvBurnData b'))
            (txDataPreimage s a (encodeNtvBurnData b)))

end Contracts.DataEncoding
