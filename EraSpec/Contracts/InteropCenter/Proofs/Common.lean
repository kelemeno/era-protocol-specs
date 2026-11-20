import EraSpec.Contracts.InteropCenter.Properties.Common
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashEncoding
import EraSpec.Contracts.AtomicFlowManager.Specs.Model

/-!
# Proofs: byte and vocabulary lemmas shared by the InteropCenter models

Proofs of `EraSpec.Contracts.InteropCenter.Properties.Common`, and the lemmas about
`Specs/Common.lean` that the send model, the fee model and the `History` record use:
big-endian byte reading, the injectivity of `abi.encode(uint256, bytes)` in its second argument
(`abiEncode_right_inj`: it needs no length bound, because the length word fixes the length modulo
`2^256` and the padded payload fixes it to within 32), the packed salt preimage, the toy keccak
`lastWord`, the witness call starters, and the flow manager's leg map.
-/

namespace Contracts.InteropCenter

open AttackVectors.BundleHashEncoding
open Contracts.AtomicFlowManager (Manager LegState)

/-! ## The manager -/

@[simp] theorem legState_set (M : Manager) (f h f' h' : Word) (s : LegState) :
    (M.set f h s).legState f' h' = if f' = f ∧ h' = h then s else M.legState f' h' := rfl

@[simp] theorem legState_empty (f h : Word) :
    Contracts.AtomicFlowManager.empty.legState f h = .Unset := rfl


/-! ## Bytes -/

/-- Big-endian reading of a concatenation. -/
theorem fromBytesBE_append (l m : List UInt8) :
    fromBytesBE (l ++ m) = fromBytesBE l * 256 ^ m.length + fromBytesBE m := by
  have key : ∀ (acc : ℕ) (m : List UInt8),
      m.foldl (fun acc b => acc * 256 + b.toNat) acc
        = acc * 256 ^ m.length + m.foldl (fun acc b => acc * 256 + b.toNat) 0 := by
    intro acc m
    induction m generalizing acc with
    | nil => simp
    | cons x m ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih (acc * 256 + x.toNat), ih (0 * 256 + x.toNat)]
      ring
  simp only [fromBytesBE, List.foldl_append]
  exact key _ m

/-- `toBytesBE k` keeps the value modulo `256 ^ k`. -/
theorem fromBytesBE_toBytesBE_mod (k n : ℕ) : fromBytesBE (toBytesBE k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [toBytesBE, fromBytesBE, Nat.mod_one]
  | succ k ih =>
    have hmod : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
      unfold UInt8.toNat UInt8.ofNat
      simp
    rw [toBytesBE, fromBytesBE_append_singleton, ih, hmod]
    rw [pow_succ, mul_comm (256 ^ k) 256, Nat.mod_mul]
    ring

theorem toBytesBE_eq_mod {k n m : ℕ} (h : toBytesBE k n = toBytesBE k m) :
    n % 256 ^ k = m % 256 ^ k := by
  have := congrArg fromBytesBE h
  rwa [fromBytesBE_toBytesBE_mod, fromBytesBE_toBytesBE_mod] at this

theorem size_eq : (256 : ℕ) ^ 32 = UInt256.size := by rfl

/-- **`abi.encode(uint256, bytes)` DETERMINES ITS BYTES ARGUMENT**, with no length bound: the
length word fixes the length modulo `2^256`, and the padded payload fixes it to within 32. -/
theorem abiEncode_right_inj {c c' : ℕ} {x y : List UInt8}
    (h : abiEncode c x = abiEncode c' y) : x = y := by
  have h96 : ∀ (c : ℕ) (x : List UInt8), abiEncode c x
      = (word c ++ word 0x40) ++ (word x.length ++ pad32 x) := by
    intro c x; simp [abiEncode, List.append_assoc]
  have hl : ∀ c, (word c ++ word 0x40).length = 64 := by
    intro c; simp [List.length_append, length_toBytesBE]
  rw [h96, h96] at h
  have h1 : word x.length ++ pad32 x = word y.length ++ pad32 y := by
    have := congrArg (List.drop 64) h
    rwa [List.drop_left' (hl c), List.drop_left' (hl c')] at this
  have hw : word x.length = word y.length := by
    have := congrArg (List.take 32) h1
    rwa [List.take_left' (length_toBytesBE 32 _), List.take_left' (length_toBytesBE 32 _)] at this
  have hp : pad32 x = pad32 y := by
    have := congrArg (List.drop 32) h1
    rwa [List.drop_left' (length_toBytesBE 32 _), List.drop_left' (length_toBytesBE 32 _)] at this
  have hmod := toBytesBE_eq_mod hw
  have hlen : (pad32 x).length = (pad32 y).length := by rw [hp]
  simp only [pad32, List.length_append, List.length_replicate] at hlen
  have hN : (256 : ℕ) ^ 32 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num
  rw [hN] at hmod
  have hxy : x.length = y.length := by omega
  have := congrArg (List.take x.length) hp
  rwa [pad32, pad32, List.take_left' rfl, hxy, List.take_left' rfl] at this

/-- **THE PACKED SALT PREIMAGE DETERMINES `(sender, salt)`** (`packed_addr_salt_inj`). -/
theorem saltPreimage_inj {a a' : Address} {s s' : Word}
    (h : saltPreimage a s = saltPreimage a' s') : a = a' ∧ s = s' := by
  have hs : (toBytesBE 32 s.val).length = 32 := length_toBytesBE 32 _
  have hs' : (toBytesBE 32 s'.val).length = 32 := length_toBytesBE 32 _
  obtain ⟨ha, hss⟩ := packed_addr_salt_inj a.isLt a'.isLt hs hs' h
  refine ⟨Fin.ext ha, Fin.ext ?_⟩
  have h1 := toBytesBE_eq_mod hss
  rwa [size_eq, Nat.mod_eq_of_lt s.isLt, Nat.mod_eq_of_lt s'.isLt] at h1

theorem map_value_of_forall₂ {sender : Address} {cs : List CallStarter} {calls : List InteropCall}
    (h : List.Forall₂ (FormsCall sender) cs calls) :
    calls.map InteropCall.value = cs.map fun c => c.callAttributes.interopCallValue := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp [hab.value, ih]

/-- `_processCallStarter` for a direct starter: the call it forms. -/
theorem formsCall_direct (sender : Address) (v : ℕ) :
    FormsCall sender (wDirect v) ⟨5, sender, v, []⟩ :=
  ⟨rfl, fun h => (Bool.false_ne_true h).elim, fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- `_processCallStarter` for the indirect starter: `from` is the indirect sender. -/
theorem formsCall_indirect (sender : Address) :
    FormsCall sender wIndirect ⟨5, 9, 0, []⟩ :=
  ⟨rfl, fun _ => rfl, fun h => absurd h (by decide)⟩

/-! ## Non-vacuity -/

theorem EncInjOnSatisfiable : Properties.EncInjOnSatisfiable := by
  intro L
  refine ⟨fun b => List.replicate (L.idxOf b) 0, ?_⟩
  intro b hb b' _ h
  have := congrArg List.length h
  simp only [List.length_replicate] at this
  exact (List.idxOf_inj hb).mp this

theorem KeccakInjOnSatisfiable : Properties.KeccakInjOnSatisfiable := by
  intro L hL
  refine ⟨fun x => Fin.ofNat _ (L.idxOf x), ?_⟩
  intro x hx y hy h
  have hxl : L.idxOf x < UInt256.size := lt_of_lt_of_le (List.idxOf_lt_length_iff.mpr hx) hL
  have hyl : L.idxOf y < UInt256.size := lt_of_lt_of_le (List.idxOf_lt_length_iff.mpr hy) hL
  have hv := congrArg Fin.val h
  simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hxl, Nat.mod_eq_of_lt hyl] at hv
  exact (List.idxOf_inj hx).mp hv

/-- The toy keccak reads the last word. -/
theorem lastWord_append_word (l : List UInt8) (n : ℕ) :
    lastWord (l ++ toBytesBE 32 n) = Fin.ofNat _ n := by
  apply Fin.ext
  simp only [lastWord, Fin.val_ofNat, fromBytesBE_append, length_toBytesBE,
    fromBytesBE_toBytesBE_mod, size_eq]
  rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]

theorem ofNat_val (s : Word) : (Fin.ofNat UInt256.size s.val : Word) = s :=
  Fin.ext (by rw [Fin.val_ofNat]; exact Nat.mod_eq_of_lt s.isLt)

theorem lastWord_saltPreimage (a : Address) (s : Word) : lastWord (saltPreimage a s) = s := by
  rw [saltPreimage, lastWord_append_word, ofNat_val]

/-- A two-element list whose images differ. -/
theorem keccakInjOn_pair {k : List UInt8 → Word} {x y : List UInt8} (h : k x ≠ k y) :
    KeccakInjOn k [x, y] := by
  intro u hu v hv huv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · rfl
  · exact absurd huv h
  · exact absurd huv.symm h
  · rfl

theorem encInjOn_pair {enc : Bundle → List UInt8} {b b' : Bundle} (h : enc b ≠ enc b') :
    EncInjOn enc [b, b'] := by
  intro u hu v hv huv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · rfl
  · exact absurd huv h
  · exact absurd huv.symm h
  · rfl

end Contracts.InteropCenter
