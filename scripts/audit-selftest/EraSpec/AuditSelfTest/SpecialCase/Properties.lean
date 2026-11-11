/-!
# Audit self-test, planted defect: a property proved for one parameter value only
-/

namespace AuditSelfTest.SpecialCase

/-- A property with a parameter. -/
def Properties.Q (n : Nat) : Prop := n + 0 = n

end AuditSelfTest.SpecialCase
