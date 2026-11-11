/-!
# Audit self-test, planted defect: an unused `def` proving `False` with `sorry`

No theorem depends on `hiddenFalse`, and Lean only warns about it. The audit must flag
the declaration itself.
-/

namespace AuditSelfTest.UnusedSorryProof

/-- An admitted proof of `False`, stated as a `def`. -/
def hiddenFalse : False := by sorry

end AuditSelfTest.UnusedSorryProof
