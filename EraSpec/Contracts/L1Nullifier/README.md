# L1Nullifier

Source: era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`, under
`l1-contracts/contracts/`:

- `bridge/L1Nullifier.sol` (all of it);
- `bridge/asset-router/L1AssetRouter.sol`: `bridgehubDeposit`, `bridgehubConfirmL2Transaction`,
  `bridgeConfirmTransferResult`, the pause flag;
- for the record path, `bridge/asset-router/AssetRouterBase.sol` (`_bridgehubDeposit`,
  `_bridgehubDepositNonBaseTokenAsset`), `core/bridgehub/L1Bridgehub.sol`
  (`requestL2TransactionTwoBridges`, `:200-264`) and `common/libraries/DataEncoding.sol`
  (`encodeTxDataHash`, `:159-170`).

Namespace `Contracts.L1Nullifier`. Statements are `Contracts.L1Nullifier.Properties.*`; each
proof has the same name without the `Properties` segment.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |

## What changed at this pin

At v0.35.0 the nullifier is only a **deposit ledger**: `depositHappened[chainId][l2TxHash]`.
Withdrawal finalization is no longer here. `__DEPRECATED_isWithdrawalFinalized` is "no longer
read or written" (`L1Nullifier.sol:71-76`); replay protection moved to the L1 interop handler's
`bundleStatus`, and the router's `finalizeDeposit` is `onlySelf`, reached only through
`receiveMessage` from `l1InteropHandler`. The legacy bridge is gone: every legacy slot is
deprecated, and a deposit whose data is not `NEW_ENCODING_VERSION` reverts
(`AssetRouterBase.sol:125-137`). So two items of the brief are answered by absence:

- **Withdrawal finalization at most once per `(chainId, batch, index)`** is not a property of these
  two contracts any more. `DeprecatedSlotsFrozen` proves the old mapping never changes. The
  at-most-once guarantee belongs to the interop handler (see `InteropHandlerBase`,
  `BundleStatusMachine`, pinned at `c67894b9`; not re-pinned here). **Open** at this pin.
- **Legacy bridge paths** have no writer: no entry point touches a deprecated slot
  (`DeprecatedSlotsFrozen`), every bridgehub record is a new-format hash or zero
  (`RecordsComeFromBridgehub`). A record the deployed proxy already holds in the **legacy** hash
  format can be cleared only by a new-format triple hashing to that value
  (`RecordLeavesOnlyByPreimage`): a cross-format keccak collision. So, if mainnet still holds
  legacy-format records of failed deposits, they are unclaimable through the nullifier at this pin.
  Whether such records exist is **open** (needs chain state).

## What is modelled

One step is one successful top-level call (revert = no step), over fifteen entry points:
`initialize`; `transferOwnership`, `acceptOwnership`, `renounceOwnership`; the three set-once
setters; `pause`, `unpause`; `bridgehubConfirmL2TransactionForwarded` called directly; the two
claim entry points `bridgeConfirmTransferResult` and `bridgeRecoverFailedTransfer`; the bridgehub's
two-bridges request with the router as second bridge (deposit or counterpart registration), which
is the only way the router forwards a record; the router's `bridgeConfirmTransferResult` called
directly; and the router's pause flag. `Reach` is any sequence of these, in any interleaving, from
any start storage. A ghost log records writes (with origin), clears and handler calls.

Not modelled (all reject-only for the nullifier's state, so omitting them only adds runs):
`nonReentrant` and callbacks; the router's `_checkAssetHandlerAllowed`; the asset handler's
`bridgeConfirmTransferResult` and its refund (the native token vault rejects `Success`); the vault's
`_burn`; the bridgehub's own checks and `_sendRequest`; events; the router's owner. The hash and the
status prover are arbitrary (`Env`). Register rows: `MODEL-NULLIFIER`, `PROTO-TX-STATUS`,
`PROTO-TXHASH-FRESH` in `ASSUMPTIONS.md`.

## Results

The ledger (all run-level over `Reach`, source checks):

- `DepositRecordsClaimClears`: a bridgehub deposit records `txDataHash` of its own
  `(originalCaller, assetId, transferData)`; a claim empties its slot.
- `ClearCountIdentity`: for every key, `clears + occupied(end) = nonzero writes + zero-hash clears
  + occupied(start)`.
- `AtMostOneClearPerDeposit`: a key recorded at most once (`PROTO-TXHASH-FRESH`) and never
  claimed with a zero hash is cleared at most once. A deposit is refunded or confirmed at most once,
  and a refunded deposit is never also confirmed.
- `ClearsAreBacked`, `RecordsComeFromBridgehub`, `RefundGoesToDepositor`: with the nullifier's
  `l1AssetRouter` unset or the router, every clear follows a bridgehub deposit at its key whose
  triple has the same hash; with no collision among the run's deposit triples at that key
  (restricted, not global, injectivity), the refund's `(depositSender, assetId, assetData)` is
  exactly the deposit's.
- `ClearStatusIsTrue`, `NoFailureClearOfSucceededDeposit`: with a sound status prover
  (`PROTO-TX-STATUS`), every clear carries the transaction's real status; a deposit that succeeded
  on L2 is never refunded as failed.
- `NoHandlerCallWithoutClear`: the router reaches an asset handler only through a nullifier clear.
- `RecordLeavesOnlyByPreimage`: a nonzero record changes only by a clear of its key presenting a
  preimage of the record.

Configuration: `DeprecatedSlotsFrozen`, `ConfigSetOnce` (for any checks),
`PausedStepKeepsRecords`, `PausedOwnerlessFreezesForever`, `PausedOwnerlessReachable`.

Countermodels (each removes one source check and breaks the matching result):
`HashCheckLoadBearing` (`DepositDoesNotExist`, `L1Nullifier.sol:243-245`: double clear),
`ProofCheckLoadBearing` (`InvalidProof`, `:231`: a succeeded deposit refunded),
`DepositExistsLoadBearing` (`DepositExists`, `:160`: a record overwritten),
`OnlyNullifierLoadBearing` (`onlyNullifier`, `L1AssetRouter.sol:70-73`: unbacked handler call).

Non-vacuity: `LifecycleWitness` (fresh storage → initialize → set router → deposit → recover, with a
sound prover; the premises of `RefundGoesToDepositor` and `ClearStatusIsTrue` hold with a clear
present), `PausedOwnerlessReachable`.

## Source observations (internal; do not publish)

- **NatSpec, `IL1Nullifier.sol:30-31`**: `bridgehubConfirmL2TransactionForwarded` "Rejects
  duplicates". It rejects only an occupied slot: a repeated `(chainId, txHash)` is accepted after a
  zero record (a counterpart registration records `bytes32(0)`) or after a clear
  (`RepeatedKeyAccepted`). Harmless while canonical tx hashes are fresh. Low.
- **NatSpec, `IL1Nullifier.sol:33`**: `_txDataHash` is described as
  `keccak256(0x01 || abi.encode(bytes32, bytes))`; the source encodes `(address, bytes32, bytes)`
  (`DataEncoding.sol:167-169`). Documentation only; not expressible in this abstract-hash model.
- **Contract NatSpec, `L1Nullifier.sol:31`** says deposits are cleared "when a failed deposit is
  claimed back"; `bridgeConfirmTransferResult` also clears on a proven `Success` (the vault then
  rejects it, so for vault assets the success path always reverts).
- **Operations**: `renounceOwnership` is not disabled. Renouncing while paused freezes every
  record forever (`PausedOwnerlessFreezesForever`, reachable: `PausedOwnerlessReachable`), so no
  failed deposit can be refunded. Owner-only, so low.
- **Legacy-format records** (above) are unclaimable at this pin, if any exist.

## Open

- Withdrawal at-most-once at v0.35.0 (interop handler `bundleStatus`), not re-pinned here.
- The asset handler's refund (amount, receiver) for the triple: `RefundGoesToDepositor` fixes the
  triple handed to the router; what the vault pays from it is `NativeTokenVaultBase`'s.
- Soundness of the status prover and tx-hash freshness are premises, not proved.
- Whether the deployed proxy holds legacy-format records.

## Review order

1. `Specs/Model.lean`: the header (source quotes, modelling choices), then `Step`.
2. `Properties/Model.lean`: the statements and their premises.
3. `Proofs/Model.lean` only if a proof is in doubt; the audit checks each property has its proof.
