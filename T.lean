import Mathlib
example : ∀ m : UInt8, (m ||| ((1:UInt8) <<< (2:UInt8))) &&& 4 ≠ 0 := by decide
example : ∀ m : UInt8, (m &&& ~~~((1:UInt8) <<< (2:UInt8))) &&& 4 = 0 := by decide
example (m : UInt8) : (m ||| 4) &&& 4 = 4 := by
  rw [UInt8.and_comm]; simp
theorem x : ∀ m : UInt8, (m &&& ~~~(4:UInt8)) &&& 4 = 0 := by
  intro m; apply UInt8.eq_of_toBitVec_eq; simp; bv_omega
#print axioms x
