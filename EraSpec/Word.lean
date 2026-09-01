import Init.Data.Nat.Div
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic

/-!
# The 256-bit machine word

`UInt256 := Fin 2^256`, with the wrapping arithmetic that carries.

## Why this file is VENDORED rather than imported

This is a trimmed copy of `Clear/UInt256.lean` from Nethermind's Clear framework
(pinned there at `8ab513e`).  It is vendored so that this package depends on
Mathlib and nothing else — see `lakefile.lean`.  Importing Clear for it would drag
in the EVM interpreter and defeat the whole point of the package.

**The copy is deliberately narrower than the original.**  Kept: the type, its
numeric instances, and the wrapping-arithmetic lemmas.  Dropped: everything that
is EVM *semantics* rather than a word type — the signed-arithmetic opcodes
(`sdiv`, `smod`, `slt`, `sgt`, `sar`, `signextend`, `sgn`, `abs`, `byteAt`) and
the byte-serialization layer (`fromBytes!`, `toBytes!`, `zeroPadBytes`).  None of
those are referenced by any protocol-level proof; if a future one needs them, that
is a signal the statement has drifted below the protocol boundary, and it should be
proved in `contracts-formal-verification` instead.

## Fidelity

Definitions kept here are character-identical to Clear's, so a theorem stated over
this `UInt256` and a theorem stated over Clear's are about the same type up to the
`abbrev` unfolding.  `scripts/check-word-fidelity.sh` diffs the kept declarations
against the Clear submodule in the sibling repo and fails on any divergence — run
it whenever the Clear pin moves.  Do not "improve" a definition here: the value of
the copy is that it is a copy.
-/

-- 2^256
@[simp]
def UInt256.size : ℕ := 115792089237316195423570985008687907853269984665640564039457584007913129639936

instance : NeZero UInt256.size := ⟨by decide⟩

abbrev UInt256 := Fin UInt256.size

instance : SizeOf UInt256 where
  sizeOf := 1

instance (n : ℕ) : OfNat UInt256 n := ⟨Fin.ofNat n⟩
instance : Inhabited UInt256 := ⟨0⟩
instance : NatCast UInt256 := ⟨Fin.ofNat⟩

abbrev Nat.toUInt256 : ℕ → UInt256 := Fin.ofNat
abbrev UInt8.toUInt256 (a : UInt8) : UInt256 := a.toNat.toUInt256

def Bool.toUInt256 (b : Bool) : UInt256 := if b then 1 else 0

@[simp]
lemma Bool.toUInt256_true : true.toUInt256 = 1
:= rfl

@[simp]
lemma Bool.toUInt256_false : false.toUInt256 = 0
:= rfl

def Clear.UInt256.complement (a : UInt256) : UInt256 := -a - 1

instance : Complement UInt256 := ⟨Clear.UInt256.complement⟩
instance : HMod UInt256 ℕ UInt256 := ⟨Fin.modn⟩
instance : HPow UInt256 UInt256 UInt256 where
  hPow a n := a ^ n.val
instance : DecidableEq UInt256 := instDecidableEqFin UInt256.size

namespace Clear.UInt256

def eq0 (a : UInt256) : Bool := a = 0

def lnot (a : UInt256) : UInt256 := (UInt256.size - 1) - a

lemma UInt256_pow_def {a b : UInt256} : a ^ b = a ^ b.val := by
  rfl

lemma UInt256_pow_succ {a b : UInt256} (h : b.val + 1 < UInt256.size) : a * a ^ b = a ^ (b + 1) := by
  rw [UInt256_pow_def, UInt256_pow_def]
  have : (↑(b + 1) : ℕ) = (b + 1 : ℕ) := by rw [Fin.val_add, Nat.mod_eq_of_lt (by norm_cast)]; rfl
  rw [this]
  ring

lemma UInt256_zero_pow {a : UInt256} (h : a.val ≠ 0) : (0 : UInt256) ^ a = 0 := zero_pow h

lemma UInt256_pow_zero {a : UInt256} : a ^ (0 : UInt256) = 1 := by
  unfold HPow.hPow instHPowUInt256
  simp

end Clear.UInt256
