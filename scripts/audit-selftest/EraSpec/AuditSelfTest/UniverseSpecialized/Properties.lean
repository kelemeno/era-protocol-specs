/-!
# Audit self-test, planted defect: a property proved at one universe only

`Properties.P` quantifies over `Sort u`. It holds at `Sort 0`, where any two proofs are
equal, and fails at `Sort 1`, where `Bool` has two elements (`not_P_one`). The theorem
`P` proves only `Properties.P.{0}` but does reference the property, so only the
universe part of the full-proof check can reject it.
-/

namespace AuditSelfTest.UniverseSpecialized

universe u

/-- Every type of `Sort u` is a subsingleton. -/
def Properties.P : Prop := ∀ α : Sort u, Subsingleton α

end AuditSelfTest.UniverseSpecialized
