# Historical reference inventory

This file records potentially useful material found in the older
`contracts-formal-verification` checkout during an inspection on 2026-10-23.
That repository is not a dependency of `era-protocol-specs`. The entries below are
historical references for independent future work; none is imported here or
claimed to verify the local abstract models against deployed Solidity.

## Historical proof and helper candidates

| Existing artifact | What the inspected artifact appeared to establish; remaining gap |
|---|---|
| `specs/L1AssetRouter/L1AssetRouter/bridged_amount_preserved_user.lean` | Relates two generated amount-store blocks given matching input slots and an assumed custody delta. Does not establish the custody delta or a complete current deposit transaction. |
| `specs/L1AssetRouter/L1AssetRouter/ntv_caller_guard_user.lean` | Caller/authorized-address operand reasoning for a historical generated guard; not a complete successful-entry authorization theorem. |
| `specs/L1AssetRouter/L1AssetRouter/fun_transferFundsToNTV_inner_user.lean` | Control-flow evidence at a balance-check block; the artifact itself notes that the balance-delta equality is not exposed by its sub-specification. |
| `specs/L1Nullifier/L1Nullifier/no_replay_user.lean` and `modifier_nonReentrant_892_user.lean` | Historical withdrawal replay/check-set reasoning with generated primitive and model assumptions to audit. Current route behavior needs independent source review. |
| `specs/L2AssetRouter/L2AssetRouter/fun_burn_user.lean` | Abstract predicate aliases a generated concrete predicate; this is not an independent behavioral specification proving assets were burned. |
| `specs/ModelFidelity.lean`, `specs/RevertModel.lean`, storage/keccak/frame modules, and generation/build/audit scripts | Historical infrastructure that may inform separate implementation-refinement work. Its assumptions and applicability require review. |

The inspected Lean trees had no matching token, vault, tracker, holder, or wrapper
modules for `BridgedStandardERC20`, `NativeTokenVaultBase`, `L2AssetTracker`,
`BaseTokenHolder`, or `L2WrappedBaseToken`. Solidity source being present is not
Lean verification coverage.

The source context for this project's models is era-contracts commit
`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`. Some historical generated artifacts
refer to entry points absent at that pin, including
`L1AssetRouter.transferFundsToNTV` and `L1Nullifier.finalizeWithdrawal`. They do
not establish coverage of the current source.

## Local word type

`EraSpec.Core.Word` is a local definition with historical derivation from a trimmed
Clear word module. It is not shared with or imported from Clear. A historical mixed
import probe found a Lean declaration collision between independently declared
`UInt256` constants. This is background about cross-importing those two codebases;
it is not a blocker or dependency for this independent repository.
