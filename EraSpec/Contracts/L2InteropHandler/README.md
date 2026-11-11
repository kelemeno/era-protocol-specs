# L2InteropHandler

Source: `contracts/interop/interop-handler/L2InteropHandler.sol` in the pinned
era-contracts tree.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| AtomicSourceBinding | [Specs/AtomicSourceBinding.lean](Specs/AtomicSourceBinding.lean) | [Properties/AtomicSourceBinding.lean](Properties/AtomicSourceBinding.lean) | [Proofs/AtomicSourceBinding.lean](Proofs/AtomicSourceBinding.lean) |

Bundle replay and self-call permission properties are under `../InteropHandlerBase/`.
The insertion authorization chain crosses contracts and is modeled in
`../../Protocol/LocalHonesty.lean`. A compiled proof that successful
`executeAtomicBundle` passed every flow gate and executed the committed bytes
remains a separate obligation.
