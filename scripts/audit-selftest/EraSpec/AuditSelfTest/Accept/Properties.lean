import EraSpec.AuditSelfTest.Accept.Specs

namespace AuditSelfTest.Accept

universe u v

/-- Polymorphic in two universes, like the bundle-hash properties. Its proof lists the
universe parameters in the other order. -/
def Properties.MapCongr : Prop :=
  ∀ {α : Type u} {β : Type v} (f : α → β) (x y : α), x = y → f x = f y

/-- A property at a successor universe (`Type u` is `Sort (u + 1)`). -/
def Properties.PairEta : Prop := ∀ {α : Type u} (p : Pair α), Pair.mk p.fst p.snd = p

/-- A property with a parameter, proved for every value of it. -/
def Properties.AddZero (n : Nat) : Prop := n + 0 = n

/-- A statement with a nested proof term, which Lean abstracts into an internal
auxiliary theorem of this module. -/
def Properties.FinZero : Prop := (⟨0, by decide⟩ : Fin 1) = 0

/-- A property whose proof uses classical logic. -/
def Properties.ColorEM : Prop := ∀ c : Color, c = .red ∨ c ≠ .red

end AuditSelfTest.Accept
