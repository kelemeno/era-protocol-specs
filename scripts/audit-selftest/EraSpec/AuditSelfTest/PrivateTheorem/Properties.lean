/-!
# Audit self-test, planted defect: a private theorem in a Properties module

As `TheoremInProperties`, but private, so that its name looks like a Lean auxiliary.
-/

namespace AuditSelfTest.PrivateTheorem

/-- A theorem where only statements belong. -/
private theorem Properties.Smuggled : True := trivial

end AuditSelfTest.PrivateTheorem
