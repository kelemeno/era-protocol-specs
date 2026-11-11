/-!
# Audit self-test, control: declarations the audit must accept

Every declaration here is valid. Together with `Properties` and `Proofs`, this case
covers the shapes the stricter checks look at, so that they cannot pass the planted
defects by rejecting valid code. It includes a structure, an inductive type with derived
instances, a `partial def` (an `opaque` constant outside any Properties module), a
`noncomputable` choice, and an instance.
-/

namespace AuditSelfTest.Accept

universe u

/-- A structure: its constructor, recursor and projections are audited for axioms. -/
structure Pair (α : Type u) where
  fst : α
  snd : α

/-- An inductive type with derived instances. -/
inductive Color where
  | red
  | green
  deriving DecidableEq, Repr

instance : Inhabited Color := ⟨.red⟩

/-- A `partial def` compiles to an `opaque` constant with an implementation. -/
partial def countdown (n : Nat) : Nat := if n = 0 then 0 else countdown (n - 1)

/-- Classical choice is one of the standard axioms. -/
noncomputable def pick (α : Type u) [h : Nonempty α] : α := Classical.choice h

end AuditSelfTest.Accept
