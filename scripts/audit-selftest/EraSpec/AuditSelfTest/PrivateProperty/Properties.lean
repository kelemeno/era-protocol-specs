/-!
# Audit self-test, planted defect: a private property statement

A private name carries the `_private.<module>.0` prefix, which `Name.isInternal` takes for a
Lean auxiliary. An audit that skips internal names therefore skipped this unprovable statement:
it was neither counted nor required to have a proof.
-/

namespace AuditSelfTest.PrivateProperty

/-- A false statement, hidden as private. -/
private def Properties.Unproved : Prop := False

end AuditSelfTest.PrivateProperty
