/-!
# Audit self-test, planted defect: a classification tag on the proof instead of the statement

The property and its theorem are valid; the tag sits on the theorem `Q` in the Proofs
module, where the audit's tag counts would never see it as a property.
-/

namespace AuditSelfTest.TagOnTheorem

/-- A valid property. -/
def Properties.Q : Prop := ∀ n : Nat, n + 0 = n

end AuditSelfTest.TagOnTheorem
