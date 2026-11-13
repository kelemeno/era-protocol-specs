/-!
# Audit self-test, planted defect: a `def` in a Properties module that is not a proposition
-/

namespace AuditSelfTest.NotProp

/-- Data, not a statement. -/
def Properties.Q : Nat := 0

end AuditSelfTest.NotProp
