import Lean

/-!
# Headline, witness and countermodel tags for property statements

The audit (`scripts/Audit.lean`) counts every `def` in a Properties module as a property and
requires a full named theorem for each. That count alone does not say how many of them are real
guarantees: it also contains non-vacuity witnesses, countermodels and supporting lemmas. These three
tag attributes classify a property statement, so the audit can report each kind separately.

* `@[headline]`: a **real guarantee about the behaviour of the target commit**, era-contracts
  `b17415d20` (draft/v0.35.0 head). A reader of the contract's README should know it, and its
  docstring states every premise in plain words. A property about an older pin, kept under a
  `History` folder and namespace, is not a headline.
* `@[witness]`: a **non-vacuity or satisfiability witness** for some headline. It shows that the
  headline's premises can all hold at once, or that the guarded operation can succeed, so the
  headline is not true only because nothing satisfies its premises.
* `@[countermodel]`: a **countermodel**. It shows that a stronger reading of some headline is false,
  or that one of a headline's premises is necessary (without it the conclusion fails).

A property statement with none of the three tags is a **supporting lemma**: proved and audited like
every other property, but not part of the headline list.

Two rules are enforced by the audit, not here, so that its self-test can plant the defects:

* a tag goes only on a property statement, that is a `def` in a Properties module;
* a statement carries at most one of the three tags.

Usage, in a Properties module:

```
import EraSpec.Core.Headline

@[headline] abbrev Properties.balance_bounded … := …
@[witness] abbrev Properties.one_unit_roundtrip … := …
```

`attribute [headline] Properties.foo` after the declaration also works, in the same module (a tag
attribute cannot be added to a declaration of an imported module).
-/

namespace EraSpec.Headline

open Lean

/-- `@[headline]`: a real guarantee about the behaviour of era-contracts `b17415d20`. -/
initialize headlineAttr : TagAttribute ←
  registerTagAttribute `headline
    "property statement: a real guarantee about the behaviour of era-contracts b17415d20"

/-- `@[witness]`: a non-vacuity or satisfiability witness for some headline. -/
initialize witnessAttr : TagAttribute ←
  registerTagAttribute `witness
    "property statement: a non-vacuity or satisfiability witness for some headline"

/-- `@[countermodel]`: shows that a stronger reading of some headline fails, or that one of its
premises is necessary. -/
initialize countermodelAttr : TagAttribute ←
  registerTagAttribute `countermodel
    "property statement: shows that a stronger reading of some headline fails, or that a premise is necessary"

end EraSpec.Headline
