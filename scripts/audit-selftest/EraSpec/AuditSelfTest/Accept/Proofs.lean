import EraSpec.AuditSelfTest.Accept.Properties

namespace AuditSelfTest.Accept

theorem MapCongr.{b, a} : Properties.MapCongr.{a, b} := fun _ _ _ h => h ▸ rfl

theorem PairEta.{w} : Properties.PairEta.{w} := fun _ => rfl

theorem AddZero : ∀ n, Properties.AddZero n := fun _ => rfl

theorem FinZero : Properties.FinZero := rfl

theorem ColorEM : Properties.ColorEM := fun _ => Classical.em _

end AuditSelfTest.Accept
