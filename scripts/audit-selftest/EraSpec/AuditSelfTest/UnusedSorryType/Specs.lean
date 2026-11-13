/-!
# Audit self-test, planted defect: an unused inductive proposition built on `sorry`

The constructor's type mentions `sorry`, and no theorem uses the type. A `Prop`-valued
inductive gets no generated theorems (no `injEq`, no `sizeOf_spec`) that would carry
`sorryAx` into the theorem count. So the audit must check the type and its constructor
themselves, not only declarations with values.
-/

namespace AuditSelfTest.UnusedSorryType

/-- A proposition whose constructor takes a proof about an unfinished value. -/
inductive Bad : Prop where
  | mk : (sorry : Nat) = 0 → Bad

end AuditSelfTest.UnusedSorryType
