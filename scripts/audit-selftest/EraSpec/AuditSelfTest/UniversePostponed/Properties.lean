/-!
# Audit self-test, planted defect: a universe gap hidden in a postponed constraint

The theorem `HasDistinct` proves `Properties.HasDistinct.{max v 1}`, which misses
`Sort 0`, where the property is false (`not_HasDistinct_zero`). Comparing it with the
property at a rigid level `u` leaves `u =?= max ?v 1`, which Lean's `isDefEq` POSTPONES
and then reports as success. Rigid property levels alone accept this case; the audit
must also require every postponed universe constraint to be solved.
-/

namespace AuditSelfTest.UniversePostponed

universe u

/-- Some type of `Sort u` has two distinct elements. -/
def Properties.HasDistinct : Prop := ∃ α : Sort u, ∃ a b : α, a ≠ b

end AuditSelfTest.UniversePostponed
