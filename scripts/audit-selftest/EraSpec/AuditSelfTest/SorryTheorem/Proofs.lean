/-!
# Audit self-test, planted defect: a theorem admitted with `sorry`
-/

namespace AuditSelfTest.SorryTheorem

/-- An admitted false theorem. -/
theorem bad : 1 = 2 := by sorry

end AuditSelfTest.SorryTheorem
