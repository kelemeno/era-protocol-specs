# Consolidation inventory: smalls-enc unit

Unit `smalls-enc`, branch `consol9/smalls-enc`, from `claude/proof-round-9` at `35d2eb9`. Contracts:
DataEncoding, InteropDataEncoding, MessageHashing, L1Messenger, BridgedStandardERC20,
L1InteropHandler, L2InteropHandler. Target commit: era-contracts `draft/v0.35.0` head `b17415d20`.
Citations were checked against an extracted `b17415d20` tree. `c67894b9` and `e561b9cc2` were not
available locally, so claims about them are kept only where they already were.

Property counts at the branch point (4447 in all): DataEncoding 78, InteropDataEncoding 54,
MessageHashing 17, L1Messenger 3, BridgedStandardERC20 90, L1InteropHandler 21,
L2InteropHandler 52.

"Pinned" in `BundleHashPinned` and in "pinned collision" means a collision on two named inputs, not
the `c67894b9` source pin.

## Topics

| Contract / topic | Commit it models (checked) | Model | Imported by (outside the folder) | Decision |
|---|---|---|---|---|
| DataEncoding / AssetId | header: `c67894b9`, with a "later trees" section; the five functions are the same at `b17415d20` (`DataEncoding.sol:125-152`, `:207-213`, checked) | byte layouts `assetIdPreimage`, `encodeAssetId` … `assetIdCheck`; instances `routerEnc`, `vaultEnc` of the router and vault models' abstract id hashes | `EraSpec.lean` only | **re-pin** to `b17415d20` (lines and the renamed getters); the canonical byte model of the id encoders |
| DataEncoding / AssetIdRuns | no code of its own: instantiates AssetRouterBase `HandlerRegistration(Runs)` and NativeTokenVaultBase `RegistryAndEscrow` | none | none | **keep**; the instantiated models' pins are their folders' concern (the assets unit re-pins `RegistryAndEscrow`; AssetRouterBase has no unit this round) |
| DataEncoding / AssetIdRecovery | `c67894b9` only: instantiates AssetRouterBase `AtomicRecovery`. At `b17415d20` `L2AssetRouter.recoverAtomicCall` (`:269-303`) sends a refund to the asset's registered handler, not to the vault | none | none | **History** (whole topic) |
| DataEncoding / TxDataHash | header: `c67894b9` with later trees; the modelled code is the same at `b17415d20` (`DataEncoding.sol:35-60`, `:159-170`; `AssetRouterBase.sol:162-166`; `L1Nullifier.sol:155-163`, `:234-247`, checked) | `txDataPreimage`, `legacyTxDataPreimage`, `encodeNtvBurnData`, `decodeNtvBurnData` | `EraSpec.lean` | **re-pin**. The legacy layout stays: it is the format the `b17415d20` comment (`DataEncoding.sol:164-166`) calls removed, and its layout is the one the pin's storage comment gave |
| DataEncoding / BurnDataSlice | no model; compares with `Codegen/VaultPreparationSlice` | none | none | **re-pin** the one cited range (unchanged) |
| InteropDataEncoding / BundleHashEncoding | ABI byte layer (`abi.encode(uint256, bytes)`, packed forms, big-endian words), not contract code. The header described the pin's bundle hash | `toBytesBE`, `word`, `pad32`, `abiEncode`, `packed` | Codegen/Calls, Codegen/VaultPreparationSlice, InteropCenter/Dispatch, ProxyUpgradeExecutorBase/EngineLegV35, BlobsL1DAValidatorZKsyncOS | **keep** as shared ABI vocabulary; rewrite the header with no pin claim. `distinct_sends_distinct_hashes` stays (abstract hash functions; vacuous at `UInt256`, as documented) |
| InteropDataEncoding / BundleHashPinned | the abstract layer and the layout facts hold at `b17415d20` (`Messaging.sol:268-276`, salt at `InteropCenter.sol:638`); the keccak layer uses the pin's preimage `abi.encode(chainId, B)` | `HashCollision`, `packedSalt`, `bundleEncoding`, `bundleSaltSlot`; pin-only `preimageSaltSlot`, `bundleHashOfBytes` | Specs: BlobsL1DAValidatorZKsyncOS, ChainBatchRootTree/Layout, InteropHandlerBase/BundleStatusMachineStrong, L2InteropCommitmentTree/PaddingAtHead, Merkle/DomainSeparation, and in this unit DataEncoding, MessageHashing, L2InteropHandler. Proofs: ChainBatchRootTree, L2InteropCommitmentTree, Merkle, ProxyUpgradeExecutorBase (all use only `HashCollision` and word lemmas) | **split**. The module paths and the shared names stay, so no import outside the unit changes. The two pin-only definitions and the seven keccak-layer statements over them go to **History** (`History/*/BundleHashPinned.lean`, namespace `AttackVectors.BundleHashEncoding.History`). The 13 abstract and layout statements stay, re-cited at `b17415d20` |
| InteropDataEncoding / BundleHashAtV35 | `b17415d20` (checked `InteropDataEncoding.sol:14-16`, `InteropCenter.sol:690-692`, `:634`, `:638`, `:562-566`, `InteropHandlerBase.sol:231`, `AtomicFlowManager.sol:252`, `Messaging.sol:224-276`) | `bundleHashV35`, the slots, `sendMessageBytesV35` | none | **canonical** topic of the contract, the `b17415d20` replacement of the History keccak layer |
| MessageHashing / LogLeafSeparation | `b17415d20` (checked `MH:21-68`, `Messaging.sol:12-45`, `Config.sol:23-27`, the addresses) | `L2Log`, `logPre`, `statusLog`, `L2Message`, `messageLog` | MessageVerification/StatusProof | **canonical** for `_l2MessageToLog` and the leaf preimage. Duplicates: `L1WithdrawalGate.L2Log`/`msgToLog` (this unit, see L1InteropHandler) and ChainBatchRootTree `LogConfinement`'s `L2Log` (roots unit) |
| L1Messenger / SenderKeying | `b17415d20` (checked `L1Messenger.sol:38-60`, `L2ContractAddresses.sol:18-31`, `InteropCenter.sol:207-735`, `system-hooks.md:17-57`) | `HookSem`, `HooksAsDocumented`, `L2State`, `Step`, `Reach` | Protocol/L1WithdrawalProvenance | **canonical**; reuses L1InteropHandler's types |
| BridgedStandardERC20 / Model, ModelStrong, Initialization, LegacyFallback, Reinitialization, ReinitializationStrong, ReinitializationFaithful | header: `c67894b9`; the token has the same code at `b17415d20` with rewritten comments (`Specs/ReinitializationFaithful.lean` maps the lines) | `State`/`Reach` (ledger), `InitState`, `LegacyStep`, `TokenStorage`/`StorageStep`, `DeployedStorageStep`, `DeployedStorageCall` | NativeTokenVaultBase (Initialization, LegacyFallback, ModelCorrespondence, RepresentationPreparation, Reinitialization), L2AssetTracker/Accounting, Codegen/BridgedTokenSlice, Protocol/AssetBridgePreparation | **re-pin** every Specs citation to `b17415d20`. This is one layered model whose layers are already joined by proved refinement lemmas (`nonlegacy_runs_agree`, `nonlegacy_bridge_calls_unchanged`, `StorageRunsAreReach`, `ModelledRunsAreDeployedRunsWithoutLegacyCall`). No layer is redundant, and other folders import the layers by path, so none is merged. The README and headline tags are the infra unit's (it tags Model and ModelStrong) |
| L1InteropHandler / WithdrawalGate | `b17415d20` (checked `L1InteropHandler.sol:59-236`, `InteropHandlerBase.sol:55-413`) | `State`, `Entry`, `Callee`, `Effect`, runs; reuses InteropHandlerBase `Reentrancy` (`c67894b9`) replay types and unbundle loop | L1Messenger, Protocol/L1WithdrawalProvenance | **canonical**. Add a refinement lemma: its `msgToLog` is MessageHashing's `messageLog`, so `_l2MessageToLog` has one model |
| L2InteropHandler / AtomicSourceBinding | abstract (three free symbols). The self-binding call `_validateBundleDestinationContext(…, interopBundle.sourceChainId)` is also at `b17415d20` (`L2InteropHandler.sol:69`) | `HonestCommits` | Protocol/DestinationCapstone | **re-pin** the header to `b17415d20`; keep |
| L2InteropHandler / AtomicSourceBindingStrong, SourceBindingReduced, AtomicSourceBindingFaithful | `c67894b9`: the destination's bundle hash is `keccak(abi.encode(sourceChainId, bytes))`, and `executeAtomicBundle` is the pin's (status must be `Unreceived`, gate always run). At `b17415d20` the hash is `keccak(bytes)` (`InteropHandlerBase.sol:231`), `executeAtomicBundle` (`L2InteropHandler.sol:61-78`) skips the gate for a `Verified` bundle, and `verifyAtomicBundle` is new. The source side is InteropCenter `Dispatch` (`c67894b9`) | `DestCtx`, `FlowGatePassed`; `SourceState`/`SourceStep`; `Dest`, `HandlerState`, `ExecutesAtomic` | none outside the folder | **History** (all three). A `b17415d20` model of `executeAtomicBundle`/`verifyAtomicBundle` is not done here |

## Step 2 (one model per contract)

- **DataEncoding**: one byte model (`Specs/AssetId.lean` with `Specs/TxDataHash.lean`); the other
  topics add no definitions.
- **InteropDataEncoding**: `BundleHashAtV35` is the topic for the bundle hash; `BundleHashEncoding`
  and the shared part of `BundleHashPinned` are the ABI byte vocabulary it builds on.
- **MessageHashing**: one model. `L1WithdrawalGate.msgToLog` gets a refinement lemma onto it.
- **L1Messenger**, **L1InteropHandler**: one model each.
- **BridgedStandardERC20**: one layered model (see the table); nothing deleted.
- **L2InteropHandler**: the current folder keeps only the abstract `AtomicSourceBinding`; the three
  entry-point models are History.

## Edits planned outside the unit's folders

- `EraSpec.lean` (module list).
- `ASSUMPTIONS.md`: rows that name statements moving to History get the new names; ids unchanged.
