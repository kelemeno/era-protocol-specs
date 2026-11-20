import EraSpec.Core.Headline

/-!
# Audit self-test, planted defect: a property statement with two classification tags

A statement is a headline, a witness or a countermodel, never two of them, so that the
per-kind counts add up to the tagged properties.
-/

namespace AuditSelfTest.DoubleTag

/-- A valid property, tagged twice. -/
@[headline, witness] def Properties.Q : Prop := ∀ n : Nat, n + 0 = n

end AuditSelfTest.DoubleTag
