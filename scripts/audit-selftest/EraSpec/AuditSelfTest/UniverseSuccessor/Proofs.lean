import EraSpec.AuditSelfTest.UniverseSuccessor.Properties

namespace AuditSelfTest.UniverseSuccessor

/-- Proves the property at every successor universe, and so misses `Sort 0`. -/
theorem HasDistinct.{v} : Properties.HasDistinct.{v + 1} :=
  ⟨ULift.{v} Bool, ⟨true⟩, ⟨false⟩, fun h => Bool.noConfusion (congrArg ULift.down h)⟩

/-- The property is false at `Sort 0`, so `HasDistinct` does not prove it. -/
theorem not_HasDistinct_zero : ¬ Properties.HasDistinct.{0} :=
  fun ⟨_, _, _, h⟩ => h rfl

end AuditSelfTest.UniverseSuccessor
