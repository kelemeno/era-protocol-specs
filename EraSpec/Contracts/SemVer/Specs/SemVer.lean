import Mathlib.Tactic

/-!
# Spec: `SemVer` — packing a protocol version into a `uint96`

Source: `l1-contracts/contracts/common/libraries/SemVer.sol` at era-contracts
`d9f678900e1bc8286412b78f56d4a9f443983c29` (draft/v0.35.0). Line numbers are in that file unless
another file is named.

Values are natural numbers; the bound of the Solidity type is stated where it is used (`uint32`:
below `2^32`; `uint96`: below `2^96`; `uint256`: below `2^256`). The Solidity operators are
transcribed as written: `uint32(x)` is truncation `x % 2^32`, `>>` is `Nat.shiftRight`, `|` is
`Nat.lor`, and `<<` on a `uint96` is `Nat.shiftLeft` followed by truncation to 96 bits. That the
packed word equals `major · 2^64 + minor · 2^32 + patch` is a theorem (`PackIsPositional`), not the
definition.

| Solidity | Lean |
|---|---|
| `SEMVER_MINOR_OFFSET` (:7), `SEMVER_MAJOR_OFFSET` (:12) | same names |
| `unpackSemVer` (:25-31) | `unpackSemVer` |
| `packSemVer` (:38-47) | `packSemVer` |
| `SemVer.unpackSemVer(SafeCast.toUint96(v))` (every call site) | `unpackChecked` |
| `L2CanonicalTransactionLib.protocolUpgradeNonce` (:70-72 of that file) | `protocolUpgradeNonce` |

The call sites of `unpackSemVer` (`BaseZkSyncUpgrade.sol:227-236`, `BaseZkSyncUpgradeGenesis.sol:37-47`,
`VersionEdgeLib.sol:66-68`, `ChainTypeManager.sol:249`, `Getters.sol:187`) all pass
`SafeCast.toUint96(version)` for a `uint256` version; `unpackChecked` is that composition. The
checks those call sites then make on the components are not modelled here.
-/

namespace Contracts.SemVer

/-- `SEMVER_MINOR_OFFSET = 32` (:7). -/
def SEMVER_MINOR_OFFSET : ℕ := 32

/-- `SEMVER_MAJOR_OFFSET = 64` (:12). -/
def SEMVER_MAJOR_OFFSET : ℕ := 64

/-- `uint32(x)`: truncation to the low 32 bits. -/
def toUint32 (x : ℕ) : ℕ := x % 2 ^ 32

/-- `x << n` on a `uint96`: shift, keep the low 96 bits. -/
def shl96 (x n : ℕ) : ℕ := (x <<< n) % 2 ^ 96

/-- `unpackSemVer(_packedProtocolVersion)` (:25-31), returning `(major, minor, patch)`:
`patch = uint32(v)` (:28), `minor = uint32(v >> 32)` (:29), `major = uint32(v >> 64)` (:30). -/
def unpackSemVer (v : ℕ) : ℕ × ℕ × ℕ :=
  (toUint32 (v >>> SEMVER_MAJOR_OFFSET), toUint32 (v >>> SEMVER_MINOR_OFFSET), toUint32 v)

/-- `packSemVer(_major, _minor, _patch)` (:38-47):
`uint96(_patch) | (uint96(_minor) << 32) | (uint96(_major) << 64)`. -/
def packSemVer (major minor patch : ℕ) : ℕ :=
  patch ||| shl96 minor SEMVER_MINOR_OFFSET ||| shl96 major SEMVER_MAJOR_OFFSET

/-- `SemVer.unpackSemVer(SafeCast.toUint96(v))` for a `uint256` `v`, as every call site writes it.
`SafeCast.toUint96` reverts when `v > type(uint96).max`; `none` is that revert. -/
def unpackChecked (v : ℕ) : Option (ℕ × ℕ × ℕ) :=
  if v < 2 ^ 96 then some (unpackSemVer v) else none

/-- **Ablation, not source.** The call-site composition with the `SafeCast.toUint96` check replaced
by a plain truncating cast `uint96(v)`. Used to show the checked cast is load-bearing. -/
def unpackTruncating (v : ℕ) : ℕ × ℕ × ℕ := unpackSemVer (v % 2 ^ 96)

/-- `L2CanonicalTransactionLib.protocolUpgradeNonce(_protocolVersion)`
(`state-transition/libraries/L2CanonicalTransactionLib.sol:70-72`):
`_protocolVersion >> SEMVER_MINOR_OFFSET`. -/
def protocolUpgradeNonce (v : ℕ) : ℕ := v >>> SEMVER_MINOR_OFFSET

/-- The components of a version, by name. -/
def major (v : ℕ) : ℕ := (unpackSemVer v).1
def minor (v : ℕ) : ℕ := (unpackSemVer v).2.1
def patch (v : ℕ) : ℕ := (unpackSemVer v).2.2

/-- **Lexicographic SemVer precedence** on `(major, minor, patch)` triples: the major decides;
on equal majors the minor decides; on equal majors and minors the patch decides. -/
def SemVerLt (a b : ℕ × ℕ × ℕ) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 < b.2.2)))

end Contracts.SemVer
