import EraSpec.Core.Headline

/-!
# Audit self-test, planted defect: a headline without a docstring

A `@[headline]` states every premise of the guarantee in its docstring, so a reader of the
folder's headline index need not read the Lean statement.
-/

namespace AuditSelfTest.HeadlineNoDocstring

@[headline] def Properties.Q : Prop := ∀ n : Nat, n + 0 = n

end AuditSelfTest.HeadlineNoDocstring
