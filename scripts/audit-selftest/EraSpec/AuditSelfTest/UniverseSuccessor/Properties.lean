/-!
# Audit self-test, planted defect: a property proved at successor universes only

`Properties.HasDistinct` is false at `Sort 0` (`not_HasDistinct_zero`) and true at every
`Sort (v + 1)`. The theorem `HasDistinct` is universe-polymorphic, but it proves only
`Properties.HasDistinct.{v + 1}`. Unification must not solve the property's level `u`
to `?v + 1`.
-/

namespace AuditSelfTest.UniverseSuccessor

universe u

/-- Some type of `Sort u` has two distinct elements. -/
def Properties.HasDistinct : Prop := ∃ α : Sort u, ∃ a b : α, a ≠ b

end AuditSelfTest.UniverseSuccessor
