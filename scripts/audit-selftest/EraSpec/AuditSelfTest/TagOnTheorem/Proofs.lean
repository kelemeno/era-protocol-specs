import EraSpec.Core.Headline
import EraSpec.AuditSelfTest.TagOnTheorem.Properties

namespace AuditSelfTest.TagOnTheorem

/-- The full proof, tagged in the wrong place. -/
@[witness] theorem Q : Properties.Q := fun _ => rfl

end AuditSelfTest.TagOnTheorem
