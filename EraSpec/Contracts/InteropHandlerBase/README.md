# InteropHandlerBase

Source: `contracts/interop/interop-handler/InteropHandlerBase.sol` and its L1/L2
variants in the pinned era-contracts tree.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| BundleStatusMachine | [Specs/BundleStatusMachine.lean](Specs/BundleStatusMachine.lean) | [Properties/BundleStatusMachine.lean](Properties/BundleStatusMachine.lean) | [Proofs/BundleStatusMachine.lean](Proofs/BundleStatusMachine.lean) |
| SelfCallAuthority | [Specs/SelfCallAuthority.lean](Specs/SelfCallAuthority.lean) | [Properties/SelfCallAuthority.lean](Properties/SelfCallAuthority.lean) | [Proofs/SelfCallAuthority.lean](Proofs/SelfCallAuthority.lean) |

The atomic path's source identity is reviewed separately under
`../L2InteropHandler/`. Destination-wide composition is
`../../Protocol/DestinationCapstone.lean`. Whole-program call-site enumeration,
external-call semantics, and binding the actual executed bytes to authenticated
bundle bytes are separate implementation obligations, not discharged by these
abstract state machines.
