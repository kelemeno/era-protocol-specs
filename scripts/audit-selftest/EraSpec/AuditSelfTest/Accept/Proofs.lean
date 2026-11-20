import EraSpec.AuditSelfTest.Accept.Properties

namespace AuditSelfTest.Accept

theorem MapCongr.{b, a} : Properties.MapCongr.{a, b} := fun _ _ _ h => h ▸ rfl

theorem PairEta.{w} : Properties.PairEta.{w} := fun _ => rfl

/-- A private lemma outside the Properties module, which the audit accepts (only a Properties
module is limited to public statements). -/
private theorem addZeroAux (n : Nat) : n + 0 = n := rfl

theorem AddZero : ∀ n, Properties.AddZero n := addZeroAux

theorem FinZero : Properties.FinZero := rfl

theorem ColorEM : Properties.ColorEM := fun _ => Classical.em _

end AuditSelfTest.Accept
