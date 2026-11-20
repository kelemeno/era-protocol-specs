import EraSpec.Core.Headline

/-!
# Audit self-test, control: a tagged property in a History module

A History module may hold witnesses and countermodels (the record of a fixed finding,
for example); only `@[headline]` is reserved for the target commit.
-/

namespace AuditSelfTest.Accept.History

/-- A countermodel kept as a historical record. -/
@[countermodel] def Properties.NotAlwaysZero : Prop := ∃ n : Nat, n ≠ 0

end AuditSelfTest.Accept.History
