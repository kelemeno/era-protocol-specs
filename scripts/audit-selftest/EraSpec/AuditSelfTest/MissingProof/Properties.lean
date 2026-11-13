/-!
# Audit self-test, planted defect: a property with no named theorem
-/

namespace AuditSelfTest.MissingProof

/-- A property that no theorem `AuditSelfTest.MissingProof.Q` proves. -/
def Properties.Q : Prop := True

end AuditSelfTest.MissingProof
