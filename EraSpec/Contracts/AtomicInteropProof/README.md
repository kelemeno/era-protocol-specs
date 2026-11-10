# AtomicInteropProof

Source: `contracts/atomic-interop/libraries/AtomicInteropProof.sol` in the pinned
era-contracts tree. This Solidity library owns the finalization/timeout proof gates.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| LastBatchInRoot | [Specs/LastBatchInRoot.lean](Specs/LastBatchInRoot.lean) | [Properties/LastBatchInRoot.lean](Properties/LastBatchInRoot.lean) | [Proofs/LastBatchInRoot.lean](Proofs/LastBatchInRoot.lean) |
| ProofPolarity | [Specs/ProofPolarity.lean](Specs/ProofPolarity.lean) | [Properties/ProofPolarity.lean](Properties/ProofPolarity.lean) | [Proofs/ProofPolarity.lean](Proofs/ProofPolarity.lean) |
| StaleSnapshot | [Specs/StaleSnapshot.lean](Specs/StaleSnapshot.lean) | [Properties/StaleSnapshot.lean](Properties/StaleSnapshot.lean) | [Proofs/StaleSnapshot.lean](Proofs/StaleSnapshot.lean) |
| TimeoutSoundness | [Specs/TimeoutSoundness.lean](Specs/TimeoutSoundness.lean) | [Properties/TimeoutSoundness.lean](Properties/TimeoutSoundness.lean) | [Proofs/TimeoutSoundness.lean](Proofs/TimeoutSoundness.lean) |
| Timestamps | [Specs/Timestamps.lean](Specs/Timestamps.lean) | [Properties/Timestamps.lean](Properties/Timestamps.lean) | [Proofs/Timestamps.lean](Proofs/Timestamps.lean) |
| LastLeaf | [Specs/LastLeaf.lean](Specs/LastLeaf.lean) | [Properties/LastLeaf.lean](Properties/LastLeaf.lean) | [Proofs/LastLeaf.lean](Proofs/LastLeaf.lean) |

`LastLeaf` is the hash side of `_verifyLastBatchInRoot`: if every left-child
sibling on the path is the empty-subtree hash, the proven leaf is the last leaf,
**or** a concrete `HashBreak` (node collision, or an entry equal to the empty-entry
constant) is exhibited. No hash injectivity is assumed for that disjunction over the
tree's own siblings (`LastLeafOrBreak`), but `HashBreak`'s node-collision case takes any
four words, so it is always inhabited (`HashBreakAlways`) and the disjunction is
trivially true; a break pinned to a tree node is open. The submitted-path version
(`AcceptedLastLeafOrBreak`) and `NotHashBreak` take global pair-injectivity, which no
`UInt256` hash meets, so they are vacuous as stated (ASSUMPTIONS.md).

These modules expose the hypotheses used by the library's argument. They do not
prove the compiled verifier, authenticate imported roots, or establish settlement
clocks. The cross-chain binding model is `../../Protocol/Spec.lean`; the reference
application composition is `../../Examples/BurnMintBridge/ProtocolComposition.lean`.
