import EraSpec.Core.Headline

/-!
# Audit self-test, planted defect: a headline in a History module

History folders keep the record of an older era-contracts commit. A statement there is
not a guarantee about the target commit, so it may not carry `@[headline]`.
-/

namespace AuditSelfTest.HistoryHeadline.History

/-- A valid property in a History module, wrongly tagged as a headline. -/
@[headline] def Properties.Q : Prop := ∀ n : Nat, n + 0 = n

end AuditSelfTest.HistoryHeadline.History
