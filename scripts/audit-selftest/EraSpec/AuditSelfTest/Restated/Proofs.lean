import EraSpec.AuditSelfTest.Restated.Properties

namespace AuditSelfTest.Restated

/-- Restates `Properties.Q` instead of referencing it. -/
theorem Q : ∀ n : Nat, n + 0 = n := fun _ => rfl

end AuditSelfTest.Restated
