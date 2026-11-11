import Init.Data.Nat.Div
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic

/-!
# The 256-bit machine word

`UInt256 := Fin 2^256`, with the wrapping arithmetic that carries.

## Historical origin

This module originated as a trimmed copy of `Clear/UInt256.lean` from Nethermind's
Clear framework (then pinned at `8ab513e`). It is maintained here as a local
definition. This package depends on Mathlib and nothing else; it does not import
Clear or rely on Clear's compiled proofs.

**The copy is deliberately narrower than the original.**  Kept: the type, its
numeric instances, and the wrapping-arithmetic lemmas.  Dropped: everything that
is EVM *semantics* rather than a word type — the signed-arithmetic opcodes
(`sdiv`, `smod`, `slt`, `sgt`, `sar`, `signextend`, `sgn`, `abs`, `byteAt`) and
the byte-serialization layer (`fromBytes!`, `toBytes!`, `zeroPadBytes`).  None of
those are referenced by any protocol-level proof. Their absence describes this
module's scope; it does not assign future work to another repository.

## Local definition

The historical source relationship does not make this declaration interchangeable
with another module's `UInt256`, and does not connect the abstract theorems here to
compiled code. The local type and its behavior are defined by this file.
-/

-- 2^256
@[simp]
def UInt256.size : ℕ := 115792089237316195423570985008687907853269984665640564039457584007913129639936

instance : NeZero UInt256.size := ⟨by decide⟩

abbrev UInt256 := Fin UInt256.size

/-- Mathlib scopes `Fin.instCommRing`; the word type keeps it as a global instance. -/
instance : CommRing UInt256 := Fin.instCommRing UInt256.size

instance : SizeOf UInt256 where
  sizeOf := 1

instance (n : ℕ) : OfNat UInt256 n := ⟨Fin.ofNat UInt256.size n⟩
instance : Inhabited UInt256 := ⟨0⟩
instance : NatCast UInt256 := ⟨Fin.ofNat UInt256.size⟩

abbrev Nat.toUInt256 : ℕ → UInt256 := Fin.ofNat UInt256.size
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
  have : (b + 1).val = b.val + 1 := by rw [Fin.val_add]; exact Nat.mod_eq_of_lt h
  rw [UInt256_pow_def, UInt256_pow_def, this, pow_succ, mul_comm]

lemma UInt256_zero_pow {a : UInt256} (h : a.val ≠ 0) : (0 : UInt256) ^ a = 0 := by
  rw [UInt256_pow_def]; exact zero_pow h

lemma UInt256_pow_zero {a : UInt256} : a ^ (0 : UInt256) = 1 := by
  rw [UInt256_pow_def]; exact pow_zero a

end Clear.UInt256
