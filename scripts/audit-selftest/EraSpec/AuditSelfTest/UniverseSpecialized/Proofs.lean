import EraSpec.AuditSelfTest.UniverseSpecialized.Properties

namespace AuditSelfTest.UniverseSpecialized

/-- Proves the property at `Sort 0` only. -/
theorem P : Properties.P.{0} := fun _ => inferInstance

/-- The property is false at `Sort 1`, so `P` does not prove it. -/
theorem not_P_one : ¬ Properties.P.{1} :=
  fun h => Bool.noConfusion ((h Bool).allEq true false)

end AuditSelfTest.UniverseSpecialized
