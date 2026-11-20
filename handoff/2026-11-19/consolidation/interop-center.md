# Consolidation inventory: interop-center unit

Unit `interop-center`, branch `consol9/interop-center`, from `claude/proof-round-9` at `7cee115`.
Contract: InteropCenter. Target commit: era-contracts `draft/v0.35.0` head `b17415d20`, checked
against an extracted `b17415d20` tree. Main `70096e2ea` was read with `git show`; `c67894b9` is not
available locally (it is the abandoned interop pin, the `ad-atomic-interop` feature line), so claims
about it are kept only where they already were.

Property counts at the branch point (162 in all): Dispatch 30, ClaimBinding 26, AtomicRouting 18,
SendAtHead 52, FeeState 28, FeeReentry 8. No tags (the audit shows `0 / 0 / 0 / 162`).

Concurrent wave-2 units: handler-base (InteropHandlerBase), atomic-flow (AtomicFlowManager).

## Topics

| Topic | Commit it models (checked) | Model types | Imported by (outside the folder) | Decision |
|---|---|---|---|---|
| Dispatch | `c67894b9` (header; `_validateAtomicBundle`, the outer-chain-id bundle hash `keccak(abi.encode(chainid, abi.encode(bundle)))`, the pin `append(flowId, …)`, `sendMessage` with constant `isAtomic: false`). None of these is the `b17415d20` code: there `_validateAtomicBundle` is gone, the hash is `keccak256(abi.encode(bundle))` (`InteropCenter.sol:690-692`), `append` takes the flow preimage (`AtomicFlowManager.sol:104-173`), and every L2→L2 send is atomic (`:552-556`) | vocabulary `Word`, `Address`, `InteropCall`, `BundleAttributes`, `Bundle`, `CallAttributes`, `CallStarter`, `saltPreimage`, `totalBurnedCallsValue`, `FormsCall`, `markSalt`, `Validated`, `KeccakInjOn`, `EncInjOn`; pin model `AtomicSend`, `Params`, `bundlePreimage`, `bundleHash`, `Dispatch`, `FormedBy`, `State`, `Checks`, `Step`, `Reach`, witnesses `w*` | Specs: InteropHandlerBase/BundleStatusMachineStrong, AtomicFlowManager/RecoveryLimitsFaithful, Protocol/InteropAtomicity/DispatchLiveness, L2InteropHandler History (3). Proofs: the same plus InteropDataEncoding/BundleHashAtV35 (`abiEncode_right_inj`), Protocol/InteropAtomicity/ExecutionLiveness, AssetRouterBase/AtomicRecovery and DataEncoding History (`wReach`). In-folder: SendAtHead, FeeState, FeeReentry use the vocabulary | **split.** The vocabulary, whose structures match `b17415d20` (`Messaging.sol:199-276`), moves to a new current module `Specs/Common.lean` (with the generic lemmas in `Proofs/Common.lean`), keeping its names in `Contracts.InteropCenter`. The pin model and all 30 statements go to **History** (`History/*/Dispatch.lean`, namespace `Contracts.InteropCenter.History`). Importers outside the folder get the forced renames only |
| ClaimBinding | `c67894b9`: `claimRefund` hashing `abi.encode(sourceChainId, x)`, over the pin model | none of its own beyond claim helpers | none | **History** (whole topic) |
| AtomicRouting | `c67894b9` with the `e561b9cc2` checks as a switch (`upgradeTree`); composes the pin model with AtomicFlowManager `RecoveryTargets` and InteropHandlerBase `BundleStatusMachine` | `Send`, `World`, `Step`, … in `Contracts.InteropCenter.AtomicRouting` | none | **History** (whole topic). The `b17415d20` attribute routing is SendAtHead's (`AtomicBundleAttributeMeansAppended`, `EveryL2SendIsAtomic`) |
| SendAtHead | main `3605e82` = `70096e2ea` (header), with a line map to `b17415d20`. Checked by diffing: on the modelled path `b17415d20` differs from main only by reject-only checks (no `whenNotPaused`; `isPeerAllowed` in `_getDestinationBaseTokenAssetId`, `:699-702`; `_checkLegSourceAllowed` in `requireFlowFinalized`/`authorizeRefund`, whose proof checks are omitted) and the unmodelled fee-unit counter (`:749`). `InteropAttributeParser.sol`, `IERC7786Attributes.sol`, `InteropDataEncoding.sol`, `IAtomicInterop.sol` are byte-identical | own `State`, `Dispatch`, `Params`, `Checks`, `Step`, `Reach`, attribute parser, pin-parser transcription | ASSUMPTIONS (`MODEL-CENTER-HEAD`, results table) | **canonical send model, re-pinned to `b17415d20`**: every citation rewritten to `b17415d20` lines (mechanically from per-file line maps, then reviewed). The pin comparisons that need the pin model go to **History** |
| FeeState | `b17415d20` (header; spot-checked) | `State`, `Tx`, `Step`, `Reach` in `Contracts.InteropCenter.FeeState` | none | **keep**, current. Imports the vocabulary from `Specs/Common.lean` instead of `Specs/Dispatch.lean`; the one main sentence stays as a stated difference |
| FeeReentry | `b17415d20` | nested-call refinement of FeeState (`FlatIsNestedWithoutCalls`) | none | **keep** |

## Step 2 (one model per contract)

After step 1 the current InteropCenter models are the send model (salts, legs, attributes, L1
messages) and `FeeState` with its refinement `FeeReentry` (balances, fee ledgers, fee parameters,
fee units). They model disjoint parts of the center's storage and share the vocabulary of
`Specs/Common.lean` (`CallStarter`, `totalBurnedCallsValue`).

## Edits planned outside the unit's folder

- `EraSpec.lean` (module list).
- Forced renames of the pin model (`Contracts.InteropCenter.X` → `Contracts.InteropCenter.History.X`
  for the pin-model names; vocabulary names unchanged) and of the import paths, in:
  InteropHandlerBase/BundleStatusMachineStrong (concurrent unit), AtomicFlowManager/RecoveryLimitsFaithful
  (concurrent unit), Protocol/InteropAtomicity DispatchLiveness and ExecutionLiveness, L2InteropHandler
  History, InteropDataEncoding/BundleHashAtV35, AssetRouterBase/AtomicRecovery, DataEncoding History.
- `ASSUMPTIONS.md`: rows naming moved statements get the new names; ids unchanged.
