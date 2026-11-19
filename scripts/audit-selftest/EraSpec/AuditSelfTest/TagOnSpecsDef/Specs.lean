import EraSpec.Core.Headline

/-!
# Audit self-test, planted defect: a classification tag on a model definition

`@[headline]` belongs on a property statement in a Properties module. A tagged model
definition would count as a guarantee that no named theorem proves.
-/

namespace AuditSelfTest.TagOnSpecsDef

/-- A model function, not a property statement. -/
@[headline] def helper (n : Nat) : Nat := n + 1

end AuditSelfTest.TagOnSpecsDef
