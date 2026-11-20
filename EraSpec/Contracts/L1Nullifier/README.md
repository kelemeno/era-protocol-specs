# L1Nullifier

`L1Nullifier` and the L1 asset router's deposit-record paths at era-contracts `draft/v0.35.0`
`b17415d20`.

## Headline guarantees

The folder's real guarantees about `b17415d20`, each with every premise. Each carries `@[headline]` (the lists after the table: `@[witness]`,
`@[countermodel]`). "A run
of the source" is any sequence of successful top-level calls of the fifteen modelled labels, with
every source check, from any start storage and an empty ghost log. The hash and the status prover
are arbitrary (`Env`); no statement assumes the hash injective.

| Guarantee | Premises | Statement |
|---|---|---|
| A deposit key is cleared (confirmed or recovered) at most once, so never both | The key is recorded with a nonzero value at most once in the run, counting a record already in the start storage (`PROTO-TXHASH-FRESH`); no clear of it carries a triple hashing to zero | `AtMostOneClearPerDeposit` |
| Every clear follows a bridgehub deposit at its key whose triple has the same hash, and, absent a collision among the run's deposit triples at that key, exactly the claimed `(depositSender, assetId, assetData)` | The run ends with the nullifier's `l1AssetRouter` unset or the router; the key was empty at the start; the claimed hash is nonzero | `ClearCarriesDepositTriple` |
| Every clear carries the real status of its L2 transaction | The status prover accepts only real statuses (`PROTO-TX-STATUS`) | `ClearStatusIsTrue` |
| A deposit whose L2 transaction succeeded is never cleared as failed, and no key is cleared with both statuses | The same sound prover | `NoFailureClearOfSucceededDeposit` |
| An unclaimed deposit can be recovered by any caller | At the end both contracts are unpaused, the nullifier's `l1AssetRouter` is the router, the deposit's hash is nonzero and the prover accepts the failure query; enabledness of the two modelled contracts only (the asset handler's checks are not modelled) | `UnclaimedDepositRecoverable` |
| The router calls an asset handler only inside a clear | None | `NoHandlerCallWithoutClear` |
| A claim whose callback calls back into the two contracts, at any depth, is a flat run (the delete precedes the external call) | Any checks | `NestedRunIsFlatRun` |
| `AtMostOneClearPerDeposit` holds with callbacks | As `AtMostOneClearPerDeposit` | `NestedAtMostOneClearPerDeposit` |
| `l1AssetRouter`, `l1NativeTokenVault` and `l1InteropHandler` are set once | Any run, any checks | `ConfigSetOnce` |
| The deprecated slots (the old withdrawal map, the legacy-bridge and Era-upgrade slots, the old admin pair) never change | Any run, any checks | `DeprecatedSlotsFrozen` |

Witnesses: `LedgerRunWitness`, `SameKeyClearedTwiceWitness`,
`RecordLeavesOnlyByPreimageWitness`, `UnclaimedDepositRecoverableWitness`, `LedgerStepWitness`,
`InitializeOnlyOnceWitness`, `RouterPausedStepWitness`, `ConfigSetOnceWitness`,
`PausedOwnerlessReachable`, `NestedRunWitness`. Countermodels:
`HashCheckLoadBearing`, `ProofCheckLoadBearing`, `DepositExistsLoadBearing`,
`OnlyNullifierLoadBearing`, `TxHashFreshnessLoadBearing`, `SoundProverLoadBearing`,
`RouterConfiguredLoadBearing`, `ZeroHashClaimClearsEmptySlot`, `RepeatedKeyAccepted`,
`CallFirstClearsOneDepositTwice`. The other statements are supporting lemmas.

## Source

era-contracts branch `draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`, under
`l1-contracts/contracts/`. Every `file:line` is at that commit (the file list is in the header of
`Specs/Model.lean`). The files:

- `bridge/L1Nullifier.sol` (all of it);
- `bridge/asset-router/L1AssetRouter.sol`: `bridgehubDeposit`, `bridgehubConfirmL2Transaction`,
  `bridgeConfirmTransferResult`, `onlyNullifier`, the pause flag;
- for the record path, `bridge/asset-router/AssetRouterBase.sol` (`_bridgehubDeposit`,
  `_bridgehubDepositNonBaseTokenAsset`), `core/bridgehub/L1Bridgehub.sol`
  (`requestL2TransactionTwoBridges`, `:200-264`) and `common/libraries/DataEncoding.sol`
  (`encodeTxDataHash`, `:159-170`);
- the OpenZeppelin v4.9 ownership, pause and initializer code both contracts inherit, at the
  submodule commit `b17415d20` pins (`2d081f2`).

Namespace `Contracts.L1Nullifier`. Statements are `Contracts.L1Nullifier.Properties.*`; each
proof has the same name without the `Properties` segment.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |
| Reentrancy | [Specs/Reentrancy.lean](Specs/Reentrancy.lean) | [Properties/Reentrancy.lean](Properties/Reentrancy.lean) | [Proofs/Reentrancy.lean](Proofs/Reentrancy.lean) |

## What the nullifier is at this pin

At this pin the nullifier keeps one live mapping, `depositHappened[chainId][l2TxHash]`, the data
hash of an initiated L1 → L2 deposit, recorded by the bridgehub's two-bridges request through the
asset router and cleared by a claim of the deposit's result. Withdrawal finalization is not here:
`__DEPRECATED_isWithdrawalFinalized` is kept only for the storage layout
(`L1Nullifier.sol:71-76`; per its comment, withdrawal replay protection is now the interop
handler's `bundleStatus`), and the router's `finalizeDeposit` is `onlySelf`, reached through
`receiveMessage` from `l1InteropHandler`. The legacy-bridge slots are kept only for the layout
too, and a deposit whose data is not `NEW_ENCODING_VERSION` reverts
(`AssetRouterBase.sol:125-137`).

So, of the `L1AssetRouter` / `L1Nullifier` row of [REVIEW.md](../../../REVIEW.md):

- *a transfer cannot be claimed twice or both finalized and refunded* is, for deposits,
  `AtMostOneClearPerDeposit` (under `PROTO-TXHASH-FRESH`) and `NoFailureClearOfSucceededDeposit`
  (under `PROTO-TX-STATUS`). For withdrawals it is no longer a property of these two contracts.
  `DeprecatedSlotsFrozen` proves the old mapping never changes. The interop handler's bundle status
  is modelled in `../InteropHandlerBase/` at `c67894b9`, not at this commit.
- *authenticated transfer results bind all identifying data*: `ClearCarriesDepositTriple` (the
  claimed `(depositSender, assetId, assetData)` is a deposit's own triple, under a no-collision
  premise on the run's deposits at that key) and `ClearStatusIsTrue` (the status, under a sound
  prover).
- *local context is cleared before callbacks*: `NestedRunIsFlatRun`.
- *native and representation paths preserve accounting*: not modelled here (the asset handler).

## What is modelled

`Specs/Model.lean`: one step is one successful top-level call (revert = no step), over fifteen
labels. They are the nullifier's twelve state-changing entry points: `initialize`;
`transferOwnership`, `acceptOwnership`, `renounceOwnership`; the three set-once setters; `pause`,
`unpause`; `bridgehubConfirmL2TransactionForwarded` called directly; the two claim entry points
`bridgeConfirmTransferResult` and `bridgeRecoverFailedTransfer`. Then the bridgehub's two-bridges
request with the router as second bridge (deposit or counterpart registration), the only way the
router forwards a record; the router's `bridgeConfirmTransferResult` called directly; and the
router's pause flag. `Reach` is any sequence of these, in any interleaving, from any start
storage. A ghost log records writes (with origin), clears and handler calls.

`Specs/Reentrancy.lean`: `NestedRun` lets each claim run a nested execution (its callback) inside
its call to the router, to any depth, with the claim's delete placed before the call (the source)
or after it (a countermodel).

Not modelled: `nonReentrant` (its checks only remove executions); the router's
`_checkAssetHandlerAllowed`; the asset handler's `bridgeBurn` and `bridgeConfirmTransferResult`
(the native token vault rejects `Success`); the bridgehub's own checks and `_sendRequest`; events;
the router's owner (its pause may flip at any time); proxy upgrades. The hash and the status prover
are arbitrary (`Env`). Register rows: `MODEL-NULLIFIER`, `PROTO-TX-STATUS`, `PROTO-TXHASH-FRESH`
in [ASSUMPTIONS.md](../../../ASSUMPTIONS.md).

## Results

Run-level results are over `Reach` with every source check (`Checks.source`); some hold for any
checks.

- **At most one clear per recorded key** (`AtMostOneClearPerDeposit`, from the identity
  `ClearCountIdentity`): a key recorded with a nonzero value at most once, and never claimed with a
  triple hashing to zero, is cleared at most once. `DepositExists` alone does not give the count
  premise (`TxHashFreshnessLoadBearing`, `RepeatedKeyAccepted`); the zero-hash premise is needed
  too (`ZeroHashClaimClearsEmptySlot`).
- **A clear carries a deposit's triple** (`ClearCarriesDepositTriple`, from `ClearsAreBacked` and
  `RecordsComeFromBridgehub`): with the nullifier's `l1AssetRouter` unset or the router, a fresh
  start slot and a nonzero claimed hash, every clear follows a bridgehub deposit at its key whose
  triple has the same hash, and, with no collision among the run's deposit triples at that key,
  of exactly the claimed triple. `RouterConfiguredLoadBearing`: with another `l1AssetRouter`, a
  clear needs no deposit.
- **A clear carries the real status** (`ClearStatusIsTrue`, `NoFailureClearOfSucceededDeposit`):
  with a sound status prover, a deposit whose L2 transaction succeeded is never cleared as failed,
  and no key is cleared with both statuses. `SoundProverLoadBearing` drops the soundness premise.
- **No handler call without a clear** (`NoHandlerCallWithoutClear`).
- **Records persist and stay claimable**: a nonzero record changes only by a clear presenting a
  preimage of it (`RecordLeavesOnlyByPreimage`) and stays until its key is cleared
  (`RecordStaysUntilCleared`). An unclaimed bridgehub deposit can be recovered by any caller while
  both contracts are unpaused, the nullifier's `l1AssetRouter` is the router and the prover
  accepts the failure query (`UnclaimedDepositRecoverable`; enabledness of the two modelled
  contracts only).
- **Callbacks.** With the source's delete-before-call order, every nested execution is a flat run
  (`NestedRunIsFlatRun`), so the results above hold with callbacks, for example
  `NestedAtMostOneClearPerDeposit`. This does not use `nonReentrant`. With the call first and no
  `nonReentrant`, a callback clears one recorded key a second time
  (`CallFirstClearsOneDepositTwice`).
- **Configuration**: `DeprecatedSlotsFrozen`, `ConfigSetOnce` and `OnlyOwnerPausesOrConfigures`
  (for any checks), `InitializeOnlyOnce`, `PausedStepKeepsRecords`, `RouterPausedStepKeepsRecords`,
  `PausedOwnerlessFreezesForever` (in the model, which has no proxy upgrade) and
  `PausedOwnerlessReachable`.

Countermodels removing one source check each: `HashCheckLoadBearing` (`DepositDoesNotExist`,
`L1Nullifier.sol:243-245`: double clear), `ProofCheckLoadBearing` (`InvalidProof`, `:231`: a
succeeded deposit cleared as failed), `DepositExistsLoadBearing` (`DepositExists`, `:160`: a
record overwritten), `OnlyNullifierLoadBearing` (`onlyNullifier`, `L1AssetRouter.sol:70-73`: a
handler call with no clear).

Non-vacuity: `LedgerRunWitness` (fresh storage → initialize → set router → two deposits → a
recovery and a confirmation, with a prover that accepts exactly the real statuses and a hash that
separates the deposits), `SameKeyClearedTwiceWitness`, `RecordLeavesOnlyByPreimageWitness`,
`UnclaimedDepositRecoverableWitness`, `LedgerStepWitness`, `ConfigSetOnceWitness`,
`InitializeOnlyOnceWitness`, `RouterPausedStepWitness`, `PausedOwnerlessReachable`, and
`NestedRunWitness` for the nested form.

## Open

- Withdrawal at-most-once at this pin (the interop handler's `bundleStatus`), not re-pinned here.
- The asset handler's refund (amount, receiver) for the triple: `ClearCarriesDepositTriple` fixes
  the triple handed to the router; what the vault pays from it is `NativeTokenVaultBase`'s.
- Soundness of the status prover and tx-hash freshness are premises, not proved.
- The deployed proxy's actual records: the model starts from arbitrary storage.
- `main` (`70096e2`) is not covered. `L1Nullifier.sol`, `IL1Nullifier.sol`, `ReentrancyGuard.sol`
  and `MessageVerification.sol` are identical there; `L1AssetRouter.sol`, `AssetRouterBase.sol`,
  `L1Bridgehub.sol`, `DataEncoding.sol` and `Messaging.sol` differ.

## Review order

1. `Specs/Model.lean`: the header (source quotes, modelling choices), then `Step`.
2. `Properties/Model.lean`: the statements and their premises.
3. `Specs/Reentrancy.lean` and `Properties/Reentrancy.lean`.
4. `Proofs/` only if a proof is in doubt; the audit checks each property has its proof.
