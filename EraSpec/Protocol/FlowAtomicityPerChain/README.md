# FlowAtomicityPerChain

The `FlowAtomicity` results restated with one commitment history per source chain, and a
countermodel showing what the single-history reading gets wrong on a two-chain flow
([Properties/Model.lean](Properties/Model.lean)). Pure order theory over `IMTAbstract` leaf sets.

## Pin

The Specs header cites era-contracts `c67894b9` (`AtomicFlowManager.append`,
`requireFlowFinalized`, `AtomicInteropProof.verifyInclusion`). It builds on `c67894b9` records and
has not been re-checked against `b17415d20`, where `AtomicFlowManager` differs. It is not a claim
about `b17415d20`.

## Headline guarantees

None. Nothing in this area is a `@[headline]`, because it models `c67894b9`, not `b17415d20`.
