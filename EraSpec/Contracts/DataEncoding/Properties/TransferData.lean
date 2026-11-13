import EraSpec.Contracts.DataEncoding.Specs.TransferData

/-!
# Properties: `DataEncoding` transfer data round-trips, injectivity and canonicity

Statements about `EraSpec.Contracts.DataEncoding.Specs.TransferData`; proofs in
`EraSpec.Contracts.DataEncoding.Proofs.TransferData`.

The valid domain of each encoder is the range of its Solidity argument types: `uint256` and
`bytes32` values below `2^256`, addresses below `2^160`, `bytes4` below `2^32`, and `bytes`
values shorter than `2^64` bytes (the bound solc's decoder enforces on lengths).

Groups, in order:

* round trips: each decoder inverts its encoder on the valid domain;
* injectivity: each encoder is injective on the valid domain, as a statement about byte lists;
* canonicity: `decodeBridgeBurnData` and `decodeFinalizeDepositData` accept exactly the encoder's
  image, so their input bytes are determined by the decoded values;
* load-bearing check: without the `length != 96` check of `decodeBridgeBurnData`, two different
  byte strings decode to the same burn data; `decodeBridgeMintData`, which has no such check,
  accepts non-canonical bytes.
-/

namespace Contracts.DataEncoding

/-! ## Round trips -/

/-- **BURN DATA ROUND TRIP.** `decodeBridgeBurnData(encodeBridgeBurnData(a, r, t)) = (a, r, t)`
for every `uint256` amount and addresses `r`, `t`. -/
def Properties.BurnDataRoundTrip : Prop :=
  ∀ a r t : ℕ, a < 2 ^ 256 → r < 2 ^ 160 → t < 2 ^ 160 →
    decodeBridgeBurnData (encodeBridgeBurnData a r t) = some (a, r, t)

/-- **MINT DATA ROUND TRIP.** `decodeBridgeMintData(encodeBridgeMintData(c, r, t, a, m)) =
(c, r, t, a, m)` for addresses `c, r, t`, a `uint256` amount and metadata shorter than `2^64`. -/
def Properties.MintDataRoundTrip : Prop :=
  ∀ (c r t a : ℕ) (m : List UInt8), c < 2 ^ 160 → r < 2 ^ 160 → t < 2 ^ 160 → a < 2 ^ 256 →
    m.length < 2 ^ 64 →
    decodeBridgeMintData (encodeBridgeMintData c r t a m) = some (c, r, t, a, m)

/-- **DEPOSIT DATA ROUND TRIP.** `decodeAssetRouterBridgehubDepositData` inverts
`encodeAssetRouterBridgehubDepositData` on every `bytes32` asset id and transfer data shorter
than `2^64`. -/
def Properties.DepositDataRoundTrip : Prop :=
  ∀ (id : ℕ) (td : List UInt8), id < 2 ^ 256 → td.length < 2 ^ 64 →
    decodeDepositData (encodeDepositData id td) = some (id, td)

/-- **TOKEN DATA ROUND TRIP.** `decodeTokenData(encodeTokenData(c, n, s, k)) = (c, n, s, k)` for a
`uint256` chain id and three metadata strings, each shorter than `2^60` bytes (so every tail
offset stays below the decoder's `2^64` offset bound). -/
def Properties.TokenDataRoundTrip : Prop :=
  ∀ (c : ℕ) (n s k : List UInt8), c < 2 ^ 256 →
    n.length < 2 ^ 60 → s.length < 2 ^ 60 → k.length < 2 ^ 60 →
    decodeTokenData (encodeTokenData c n s k) = some (c, n, s, k)

/-- **FINALIZE-DEPOSIT ROUND TRIP.** `decodeAssetRouterFinalizeDepositData` inverts
`encodeAssetRouterFinalizeDepositData` for every selector, chain id, asset id and transfer data
(of any length: the transfer data is the unprefixed remainder). -/
def Properties.FinalizeRoundTrip : Prop :=
  ∀ (sel c id : ℕ) (td : List UInt8), sel < 2 ^ 32 → c < 2 ^ 256 → id < 2 ^ 256 →
    decodeFinalizeDepositData (encodeFinalizeDepositData sel c id td) = some (sel, c, id, td)

/-! ## Injectivity on the valid domain -/

/-- **BURN DATA ENCODING IS INJECTIVE** on the valid domain: equal bytes force equal
`(amount, receiver, token)`. -/
def Properties.BurnDataEncodeInjective : Prop :=
  ∀ a r t a' r' t' : ℕ, a < 2 ^ 256 → r < 2 ^ 160 → t < 2 ^ 160 →
    a' < 2 ^ 256 → r' < 2 ^ 160 → t' < 2 ^ 160 →
    encodeBridgeBurnData a r t = encodeBridgeBurnData a' r' t' → (a, r, t) = (a', r', t')

/-- **MINT DATA ENCODING IS INJECTIVE** on the valid domain. -/
def Properties.MintDataEncodeInjective : Prop :=
  ∀ (c r t a c' r' t' a' : ℕ) (m m' : List UInt8),
    c < 2 ^ 160 → r < 2 ^ 160 → t < 2 ^ 160 → a < 2 ^ 256 → m.length < 2 ^ 64 →
    c' < 2 ^ 160 → r' < 2 ^ 160 → t' < 2 ^ 160 → a' < 2 ^ 256 → m'.length < 2 ^ 64 →
    encodeBridgeMintData c r t a m = encodeBridgeMintData c' r' t' a' m' →
      (c, r, t, a, m) = (c', r', t', a', m')

/-- **DEPOSIT DATA ENCODING IS INJECTIVE** on the valid domain. -/
def Properties.DepositDataEncodeInjective : Prop :=
  ∀ (id id' : ℕ) (td td' : List UInt8), id < 2 ^ 256 → td.length < 2 ^ 64 →
    id' < 2 ^ 256 → td'.length < 2 ^ 64 →
    encodeDepositData id td = encodeDepositData id' td' → (id, td) = (id', td')

/-- **TOKEN DATA ENCODING IS INJECTIVE** on the valid domain. -/
def Properties.TokenDataEncodeInjective : Prop :=
  ∀ (c c' : ℕ) (n s k n' s' k' : List UInt8), c < 2 ^ 256 → c' < 2 ^ 256 →
    n.length < 2 ^ 60 → s.length < 2 ^ 60 → k.length < 2 ^ 60 →
    n'.length < 2 ^ 60 → s'.length < 2 ^ 60 → k'.length < 2 ^ 60 →
    encodeTokenData c n s k = encodeTokenData c' n' s' k' → (c, n, s, k) = (c', n', s', k')

/-- **FINALIZE-DEPOSIT ENCODING IS INJECTIVE** on the valid domain, with no bound on the transfer
data. -/
def Properties.FinalizeEncodeInjective : Prop :=
  ∀ (sel c id sel' c' id' : ℕ) (td td' : List UInt8),
    sel < 2 ^ 32 → c < 2 ^ 256 → id < 2 ^ 256 → sel' < 2 ^ 32 → c' < 2 ^ 256 → id' < 2 ^ 256 →
    encodeFinalizeDepositData sel c id td = encodeFinalizeDepositData sel' c' id' td' →
      (sel, c, id, td) = (sel', c', id', td')

/-! ## Canonicity -/

/-- **BURN DATA IS CANONICAL.** Whatever bytes `decodeBridgeBurnData` accepts are exactly the
encoding of what it returns. So two accepted byte strings with the same decoded values are equal,
and the decoded values lie in the valid domain. -/
def Properties.BurnDataCanonical : Prop :=
  ∀ (d : List UInt8) (a r t : ℕ), decodeBridgeBurnData d = some (a, r, t) →
    d = encodeBridgeBurnData a r t ∧ a < 2 ^ 256 ∧ r < 2 ^ 160 ∧ t < 2 ^ 160

/-- **FINALIZE-DEPOSIT MESSAGES ARE CANONICAL AND TOTAL ABOVE 68 BYTES.** Every message of at least
68 bytes decodes, and re-encoding the decoded values gives the message back. Shorter messages
revert. -/
def Properties.FinalizeCanonical : Prop :=
  ∀ d : List UInt8,
    (d.length < 68 → decodeFinalizeDepositData d = none) ∧
    (68 ≤ d.length → ∃ sel c id td, decodeFinalizeDepositData d = some (sel, c, id, td) ∧
      sel < 2 ^ 32 ∧ c < 2 ^ 256 ∧ id < 2 ^ 256 ∧ encodeFinalizeDepositData sel c id td = d)

/-! ## The length check is load-bearing -/

/-- **COUNTERMODEL: THE `length != 96` CHECK IS LOAD-BEARING FOR CANONICITY** (`:54-57`). Without
it, two different byte strings decode to the same burn data; the source decoder rejects one of
them. -/
def Properties.BurnLengthCheckLoadBearing : Prop :=
  ∃ d d' : List UInt8, d ≠ d' ∧
    (decodeBridgeBurnDataNoLengthCheck d).isSome ∧
    decodeBridgeBurnDataNoLengthCheck d = decodeBridgeBurnDataNoLengthCheck d' ∧
    decodeBridgeBurnData d' = none

/-- **MINT DATA DECODING IS NOT CANONICAL.** `decodeBridgeMintData` has no length check, so it
accepts bytes other than the encoding of the values it returns (here, a canonical encoding with
one trailing byte). Nothing that hashes or compares raw mint-data bytes can rely on their being
canonical. -/
def Properties.MintDecodeNotCanonical : Prop :=
  ∃ (d : List UInt8) (c r t a : ℕ) (m : List UInt8),
    decodeBridgeMintData d = some (c, r, t, a, m) ∧ d ≠ encodeBridgeMintData c r t a m

end Contracts.DataEncoding
