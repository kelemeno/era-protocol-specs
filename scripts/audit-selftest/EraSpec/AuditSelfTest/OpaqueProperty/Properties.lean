/-!
# Audit self-test, planted defect: an opaque property with no proof

`Properties.Unproved` is false, has no theorem, and depends on no axiom. As an `opaque`
constant it is not a `def`, so the coverage check must reject its kind rather than skip
it.
-/

namespace AuditSelfTest.OpaqueProperty

/-- An unproved, false property behind `opaque`. -/
opaque Properties.Unproved : Prop := False

end AuditSelfTest.OpaqueProperty
