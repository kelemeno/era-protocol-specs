/-!
# Audit self-test, planted defect: a theorem in a Properties module

A Properties module holds `def` property statements only. A theorem named
`Properties.*` there is neither a statement the coverage check can require a proof
of nor a declaration it may skip.
-/

namespace AuditSelfTest.TheoremInProperties

/-- A theorem where only statements belong. -/
theorem Properties.Smuggled : True := trivial

end AuditSelfTest.TheoremInProperties
