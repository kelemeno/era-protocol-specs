/-!
# Audit self-test, planted defect: a theorem that restates the property's conclusion

The theorem proves the same proposition but never names the property, so a later edit
to either could make them diverge unnoticed.
-/

namespace AuditSelfTest.Restated

/-- The property. -/
def Properties.Q : Prop := ∀ n : Nat, n + 0 = n

end AuditSelfTest.Restated
