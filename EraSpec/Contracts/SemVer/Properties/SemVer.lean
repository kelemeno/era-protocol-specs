import EraSpec.Contracts.SemVer.Specs.SemVer

/-!
# Properties: `SemVer` round trips and order

Statements about `EraSpec.Contracts.SemVer.Specs.SemVer`; proofs in
`EraSpec.Contracts.SemVer.Proofs.SemVer`.

The valid domain of `packSemVer` is three `uint32` values; of `unpackSemVer`, a `uint96`.

* `PackIsPositional`, `UnpackPackRoundTrip`, `PackUnpackRoundTrip`, `PackInjective`: the two
  functions are mutually inverse bijections between `uint32³` and `uint96`.
* `PackOrderIsLexicographic`, `UnpackOrderIsLexicographic`: comparing packed versions as integers
  is SemVer precedence on the triples.
* `MinorDoesNotDecreaseWhenMajorsZero`, `UpgradeNonceIsMinorWhenMajorZero`: the two source comments
  that rely on the order, as theorems, each with the countermodel showing its `major == 0`
  premise is needed.
* `ToUint96CheckLoadBearing`: the checked cast at the call sites is needed.
-/

namespace Contracts.SemVer

/-- **`packSemVer` IS THE POSITIONAL VALUE.** For `uint32` components the bitwise expression of
`packSemVer` equals `major · 2^64 + minor · 2^32 + patch`, and fits a `uint96`. -/
def Properties.PackIsPositional : Prop :=
  ∀ M m p : ℕ, M < 2 ^ 32 → m < 2 ^ 32 → p < 2 ^ 32 →
    packSemVer M m p = M * 2 ^ 64 + m * 2 ^ 32 + p ∧ packSemVer M m p < 2 ^ 96

/-- **UNPACK ∘ PACK.** `unpackSemVer(packSemVer(M, m, p)) = (M, m, p)` for `uint32` components. -/
def Properties.UnpackPackRoundTrip : Prop :=
  ∀ M m p : ℕ, M < 2 ^ 32 → m < 2 ^ 32 → p < 2 ^ 32 →
    unpackSemVer (packSemVer M m p) = (M, m, p)

/-- **PACK ∘ UNPACK.** Every `uint96` is the packing of its unpacked components, and those
components are `uint32` values (the latter for every input, with no bound on `v`). -/
def Properties.PackUnpackRoundTrip : Prop :=
  ∀ v : ℕ,
    (major v < 2 ^ 32 ∧ minor v < 2 ^ 32 ∧ patch v < 2 ^ 32) ∧
    (v < 2 ^ 96 → packSemVer (major v) (minor v) (patch v) = v)

/-- **`packSemVer` IS INJECTIVE** on `uint32` triples. -/
def Properties.PackInjective : Prop :=
  ∀ M m p M' m' p' : ℕ, M < 2 ^ 32 → m < 2 ^ 32 → p < 2 ^ 32 →
    M' < 2 ^ 32 → m' < 2 ^ 32 → p' < 2 ^ 32 →
    packSemVer M m p = packSemVer M' m' p' → (M, m, p) = (M', m', p')

/-- **PACKED ORDER IS SEMVER PRECEDENCE.** For `uint32` triples, `packSemVer a < packSemVer b`
exactly when `a` precedes `b` lexicographically (major, then minor, then patch). -/
def Properties.PackOrderIsLexicographic : Prop :=
  ∀ M m p M' m' p' : ℕ, M < 2 ^ 32 → m < 2 ^ 32 → p < 2 ^ 32 →
    M' < 2 ^ 32 → m' < 2 ^ 32 → p' < 2 ^ 32 →
    (packSemVer M m p < packSemVer M' m' p' ↔ SemVerLt (M, m, p) (M', m', p'))

/-- **THE SAME, READ FROM THE PACKED SIDE.** For two `uint96` versions, `v < w` as integers exactly
when the unpacked triple of `v` precedes that of `w`. This is the comparison the upgrade paths
make on raw `uint256` versions (`_newProtocolVersion <= previousProtocolVersion`,
`BaseZkSyncUpgrade.sol:223`). -/
def Properties.UnpackOrderIsLexicographic : Prop :=
  ∀ v w : ℕ, v < 2 ^ 96 → w < 2 ^ 96 →
    (v < w ↔ SemVerLt (unpackSemVer v) (unpackSemVer w))

/-- **THE MINOR CANNOT DECREASE WHEN BOTH MAJORS ARE ZERO.** The comments at
`BaseZkSyncUpgrade.sol:241-242` and `VersionEdgeLib.sol:78-79` justify the checked subtraction
`newMinor - oldMinor` by: the packed new version is strictly greater and both majors are zero.
Proved here for `uint96` versions (the `SafeCast.toUint96` checks at those sites). -/
def Properties.MinorDoesNotDecreaseWhenMajorsZero : Prop :=
  ∀ old new : ℕ, old < 2 ^ 96 → new < 2 ^ 96 → old < new → major old = 0 → major new = 0 →
    minor old ≤ minor new

/-- **COUNTERMODEL: THE `newMajor == 0` CHECK IS LOAD-BEARING FOR THAT COMMENT.** With the old
major zero but the new major unconstrained, a strictly greater packed version can have a smaller
minor (`0.5.0 → 1.0.0`), so `newMinor - oldMinor` would underflow. -/
def Properties.MajorZeroCheckLoadBearingForMinorDelta : Prop :=
  ∃ old new : ℕ, old < 2 ^ 96 ∧ new < 2 ^ 96 ∧ old < new ∧ major old = 0 ∧ minor new < minor old

/-- **THE UPGRADE NONCE IS THE MINOR VERSION WHEN THE MAJOR IS ZERO.** The comment at
`L2CanonicalTransactionLib.sol:67-69` says `_protocolVersion >> 32` equals the new minor version
because every upgrade path rejects a non-zero major. In general the nonce is
`major · 2^32 + minor`. -/
def Properties.UpgradeNonceIsMinorWhenMajorZero : Prop :=
  ∀ v : ℕ, v < 2 ^ 96 →
    protocolUpgradeNonce v = major v * 2 ^ 32 + minor v ∧
    (major v = 0 → protocolUpgradeNonce v = minor v)

/-- **COUNTERMODEL: WITHOUT `major == 0` THE NONCE IS NOT THE MINOR.** A `uint96` version with a
non-zero major whose upgrade nonce differs from its minor version. -/
def Properties.UpgradeNonceNeedsMajorZero : Prop :=
  ∃ v : ℕ, v < 2 ^ 96 ∧ protocolUpgradeNonce v ≠ minor v

/-- **COUNTERMODEL: `SafeCast.toUint96` IS LOAD-BEARING.** `unpackSemVer` reads only the low 96
bits. With a truncating cast two different `uint256` versions unpack to the same triple; the
checked cast used at every call site rejects the one that does not fit, and on the versions it
accepts unpacking is injective. -/
def Properties.ToUint96CheckLoadBearing : Prop :=
  (∃ v w : ℕ, v < 2 ^ 256 ∧ w < 2 ^ 256 ∧ v ≠ w ∧
    unpackTruncating v = unpackTruncating w ∧ unpackChecked w = none) ∧
  (∀ (t : ℕ × ℕ × ℕ) (x y : ℕ), unpackChecked x = some t → unpackChecked y = some t → x = y)

/-- **WITNESS.** Protocol version `0.29.1` packs to `0x1d00000001`, unpacks back, and precedes
`0.30.0`. -/
def Properties.SemVerWitness : Prop :=
  packSemVer 0 29 1 = 0x1d00000001 ∧ unpackChecked 0x1d00000001 = some (0, 29, 1) ∧
  packSemVer 0 29 1 < packSemVer 0 30 0 ∧ protocolUpgradeNonce (packSemVer 0 30 0) = 30

end Contracts.SemVer
