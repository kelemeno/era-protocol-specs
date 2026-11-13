/-!
# Audit self-test, planted defect: an unfinished computational `def`

`f` is a `sorry` placeholder that no theorem uses. The audit must flag it.
-/

namespace AuditSelfTest.UnusedSorryData

/-- An unfinished definition. -/
def f : Nat := sorry

end AuditSelfTest.UnusedSorryData
