import EraSpec.AuditSelfTest.UniversePostponed.Properties

namespace AuditSelfTest.UniversePostponed

/-- Proves the property at every universe `max v 1`, and so misses `Sort 0`. -/
theorem HasDistinct.{v} : Properties.HasDistinct.{max v 1} :=
  ⟨PSum PUnit.{v} PUnit.{v}, .inl ⟨⟩, .inr ⟨⟩, by intro h; cases h⟩

/-- The property is false at `Sort 0`, so `HasDistinct` does not prove it. -/
theorem not_HasDistinct_zero : ¬ Properties.HasDistinct.{0} :=
  fun ⟨_, _, _, h⟩ => h rfl

end AuditSelfTest.UniversePostponed
