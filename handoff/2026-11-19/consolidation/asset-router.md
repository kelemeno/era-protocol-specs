# Consolidation inventory: asset-router unit

Unit `asset-router`, branch `consol9/asset-router`, from `claude/proof-round-9` at `1ad0078`.
Contract: AssetRouterBase (`EraSpec/Contracts/AssetRouterBase`, 11 topics, 256 properties at the
branch point). Target commit: era-contracts `draft/v0.35.0` head `b17415d20`; citations checked
against the extracted `b17415d20` tree. `c67894b9` and `e561b9cc2` are not in the local clone, so
claims about them are kept only where they already were (as History or as marked pin records).

Concurrent wave-2 units: atomic-proof (AtomicInteropProof), merkle-libs (Merkle, FullMerkle,
DynamicIncrementalMerkle). This unit does not edit their folders.

Abbreviations: `ARB` = `bridge/asset-router/AssetRouterBase.sol`, `L1AR` = `L1AssetRouter.sol`,
`L2AR` = `L2AssetRouter.sol` (same folder), `NTV` = `bridge/ntv/NativeTokenVaultBase.sol`,
`L2NTV` = `bridge/ntv/L2NativeTokenVault.sol`, all under `l1-contracts/contracts/`.

## What changed in the routers between the pin `c67894b9` and `b17415d20`

- **The writers of the two router maps are the same five.** A grep of `_setAssetHandler(` and
  `assetDeploymentTracker[` over the `b17415d20` tree (tests and vendored libraries excluded) finds
  exactly: `_setAssetHandlerAddressThisChain` (`ARB:65-77`, guard `:73`), `_finalizeDeposit`'s
  fallback (`ARB:267-283`, write `:278`), L1 `setNativeTokenVault` (`L1AR:116-121`, write `:120`,
  now one-shot `:117`), L2 `initL2` (`L2AR:154-163`, write `:162`), L2 `setAssetHandlerAddress`
  (`L2AR:198-204`, `onlyAssetRouterCounterpart` `:96-107`) and L1 `setAssetDeploymentTracker`
  (`L1AR:135-142`). No other non-test contract inherits either router. `updateL2`
  (`L2AR:173-188`) writes `BASE_TOKEN_ASSET_ID` but no router map.
- **Callers of `finalizeDeposit`.** L1: `onlySelf` (`L1AR:291-299`), reached through
  `receiveMessage` (`ARB:213-251`), plus the v35 gate `_checkAssetHandlerAllowed` (`L1AR:276-288`),
  which lets an unset handler through, so it never stops the fallback. L2:
  `onlyAssetRouterCounterpartOrSelf` (`L2AR:111-126`) and the base-token rejection (`L2AR:258`).
  `AllWriters` admits every caller for `finalize`, which only adds runs.
- **The refund.** At the pin `recoverAtomicCall` always called the vault and the manager's loop
  dispatched on the call's target with a `recovered == 0` revert. At `b17415d20` the manager
  dispatches on `InteropCall.from` and ignores the answer; `recoverAtomicCall` (`L2AR:269-303`)
  rejects an L1 destination (`:275`), returns `false` on a non-`finalizeDeposit` call
  (`:284-286`) and calls the handler `assetHandlerAddress` names at claim time (`:299-301`).
  `bridgehubRecoverBaseToken` (`L2AR:314-328`) is new. This is `AtomicRecoveryAtHead`'s model.
- **The vault refund.** `bridgeRecoverFailedTransfer` (`NTV:195-214`) and
  `_disburseFailedTransfer` (`NTV:264-286`) have the pin's guard and branch order; on L2 the
  override (`L2NTV:204-227`) first asserts `assertRecoveryIsAccountingNeutral` and routes this
  chain's base token to `BaseTokenHolder`. Off the base token it is the pin model's `ntvRecover`
  (`AtomicRecoveryAtHead.VaultRecoverAtHeadIsPinRefundOffBaseToken`).
- **The send side.** An atomic bundle to L1 is rejected at send (`InteropCenter.sol:552-553`).

## Topics

"Importers" lists every Lean file outside the topic's own three that imports one of them (all of
`EraSpec`, including `Protocol`). Prose mentions are listed where they name a moved statement.

| Topic | Commit it models (checked) | Model types | Importers | Duplicates | Decision |
|---|---|---|---|---|---|
| HandlerRegistration | no line cites; the quoted body of `_setAssetHandlerAddressThisChain` is `ARB:70-75` at `b17415d20` word for word | `Router`, `upd`, `IdAssumptions`, `IdInjOn`, `senderOf`, `writtenId`, `SetGuard`, `setHandler`, `Valid`, `Step`, `Reach` (namespace `Contracts.AssetRouter`) | AllWriters, HandlerRegistrationRuns, AtomicRecovery (in folder); DataEncoding `Proofs/AssetId`; Protocol/L2BridgeConfig `Specs/Consistency` | — | **canonical** router-map vocabulary; re-pin (cite `b17415d20`). The vacuous `IdAssumptions` statements `NoHijack`, `NtvTouchesOnlyItsOwnIds` stay untagged (README) |
| HandlerRegistrationRuns | `c67894b9` header cites; same code at `b17415d20` | `LoggedCall`, `ReachLog`, `stepLog` (over HandlerRegistration) | DataEncoding `Specs/AssetId`, `Proofs/AssetIdRuns` | — | **re-pin** cites to `b17415d20` |
| AllWriters | `c67894b9` (33 cites); the writer table is complete at `b17415d20` (above) | `Cfg`, `Op`, `Step`, `L1Step`, `L2Step`, `WeakValid`, `MintsOnlyNtvIds`, runs | AllWritersStrong, CounterpartGate, VaultMintGate, HandlerGateAtV35, AtomicRecoveryAtHead | HandlerRegistration is its register-only fragment (`SingleWriterIsRegisterOnlyFragment`) | **canonical** model of every router-map writer; re-pin every cite to `b17415d20`; note the one-shot `setNativeTokenVault` and the gate as over-approximations |
| AllWritersStrong | `c67894b9` (4 cites); statements over AllWriters | `LoggedOp`, `RunTrackerRecorded`, … | none | — | **re-pin** |
| CounterpartGate | `c67894b9` (8 cites): `_setAssetHandlerAddressOnCounterpart`, vault approval | `VaultApprovals`, `L1CounterpartStep` | none | — | **re-pin** (`L1AR:158-183`, `L1NativeTokenVault.sol` approval) |
| VaultMintGate | `c67894b9` (3 cites); over NativeTokenVaultBase `RegistryAndEscrow` | — | none | uses the assets unit's registry model (`NativeTokenVault.Vault`, a refinement-linked model of the canonical vault) | **re-pin** |
| HandlerGateAtV35 | `b17415d20` (header cites checked); mentions `d9f6789`, `3605e82`, `e561b9cc2` as history | `Event`, `GStep`, `GRun`, `Gate`, `Stranded` over AllWriters' L1 step | none | — (no pin original: the gate is new at v35) | **keep**, current; trim the stale pin sentences. It is linked to AllWriters by `RunProjectsToAllWriters` |
| AtomicRecovery | **mixed.** `c67894b9`: `recoverAtomicCall` (vault always), `recoverCall`/`recoverBundle`/`claimRefund`/`outcomes` (the pin loop with `recovered == 0`), `routerCall`/`directCall`/`AtomicBundleValid` (the pin send). Current at `b17415d20`: the call/mint-data types, `vaultRefund`/`ntvRecover` off the base token, `burnHandler` (`ARB:312-321`), `VaultUnaware`, `FailsAssetIdCheck` | `Config`, `CallData`, `Call`, `Hooks`, `World`, `vaultRefund`, `ntvRecover`, `recoverAtomicCall`, `burnHandler`, `recoverCall`, `recoverBundle`, `claimRefund`, `outcomes`, … | AtomicRecoveryAtHead, AtomicRecoveryFaithful, PausedRecovery (folder); AtomicFlowManager `RecoveryTargets` (Specs/Properties/Proofs, a kept pin record) and `History/RecoveryLimitsStrong`; DataEncoding `Properties/AssetId`, `Proofs/AssetId` (`Config`, `ntvId`), `History/AssetIdRecovery`; Protocol/AssetBridgePreparation `FullRecovery` (Specs/Proofs) | `vaultRefund` is a second transcription of the vault refund next to NativeTokenVaultBase `Resolution.bridgeRecoverFailedTransfer` (that one covers the registered-bridged branch of a per-token state); it already runs on the assets unit's registry model `NativeTokenVault.Vault` and its `MintData` | **split.** The 31 statements about the pin router or the pin loop go to **History** (`History/{Properties,Proofs}/AtomicRecovery.lean`, namespace `Contracts.AssetRouter.AtomicRecovery.History`), including the M1 custom-handler countermodels and the forged-refund `DirectCallIsRefunded`. The 6 vault/`_burn`/registry statements stay. The Specs stay in place: the current definitions are re-cited at `b17415d20`, the pin router/loop definitions are marked as the `c67894b9` record, kept in place because AtomicRecoveryAtHead's pin-vs-head statements, AtomicFlowManager `RecoveryTargets` and Protocol `FullRecovery` use them (move with those importers) |
| AtomicRecoveryFaithful | `c67894b9` (+ one check from `e561b9cc2`): the router-produced call's target by destination, and the pin send checks admitting an atomic L1 leg. At `b17415d20` the send rejects it (`InteropCenter.sol:552-553`) and `recoverAtomicCall` rejects an L1 destination (`L2AR:275`) | `routerCallTo`, `formedCall`, `CenterEnv`, `PinSendChecks`, `pinSend`, `CodelessAt` | none (prose in AtomicFlowManager `Properties/RecoveryTargets`, InteropCenter `History/AtomicRouting`, NativeTokenVaultBase `Properties/TrackerHooks`, Protocol `FullRecovery`) | — | **History** (whole topic, namespace `Contracts.AssetRouter.AtomicRecoveryFaithful.History`) |
| PausedRecovery | `c67894b9`: the vault pause on the pin loop | `pauseVault`, `unpauseVault`, `HasRouterDeposit`, `OthersLeavePause`, `OthersIgnorePause` | none (prose in Protocol/InteropAtomicity `Properties/Pause`, NativeTokenVaultBase README) | — | **History** (whole topic, namespace `Contracts.AssetRouter.PausedRecovery.History`). Restating it on AtomicRecoveryAtHead (the vault still has `whenNotPaused`, `NTV:199`) is a follow-up |
| AtomicRecoveryAtHead | `b17415d20` (header cites checked); mentions `d9f6789`, `70096e2ea`, `3605e82` as identical trees | `HeadConfig`, `HeadHooks`, `HandlerCode`, `headRecover`, … over AtomicRecovery's vault refund and AllWriters' runs | none | the pin loop (AtomicRecovery) is the record it is compared with | **canonical** refund model at `b17415d20`; trim the stale pin sentences. Its pin-vs-head statements (`…FailsAtHead`, `Pin…AtHead`) stay as untagged comparisons |

## Step 2 (one model per contract)

- **Router maps:** `AllWriters` is the model; `HandlerRegistration` is its register-only fragment
  (`SingleWriterIsRegisterOnlyFragment`), `HandlerRegistrationRuns` the logged runs of that
  fragment, `HandlerGateAtV35` the v35 L1 step relation projected onto it
  (`RunProjectsToAllWriters`). All share `HandlerRegistration.Router`.
- **Refund:** `AtomicRecoveryAtHead` is the `b17415d20` model; it reuses `AtomicRecovery`'s
  vault refund (`ntvRecover`) and is linked to the pin loop by `VaultRouterCallIsPinIterationAtHead`.
- **Vault:** `AtomicRecovery.vaultRefund` runs on the assets unit's registry model. A refinement
  lemma onto NativeTokenVaultBase `Resolution.bridgeRecoverFailedTransfer` is a follow-up.

## Edits planned outside the unit's folder

- `EraSpec.lean` (module list).
- AtomicFlowManager `Proofs/RecoveryTargets.lean`, DataEncoding `History/Proofs/AssetIdRecovery.lean`:
  certificate names of the History moves only.
- Prose references to moved names (no Lean change): AtomicFlowManager `Properties/RecoveryTargets`,
  InteropCenter `History/Properties/AtomicRouting`, NativeTokenVaultBase `Properties/TrackerHooks`,
  Protocol `AssetBridgePreparation/Specs/FullRecovery`, Protocol `InteropAtomicity/Properties/Pause`.
- `ASSUMPTIONS.md`: only rows naming moved statements, ids unchanged.

## Outcome

- **Step 1 (one commit).** Every non-History Specs file of the folder cites `b17415d20`, with every
  line checked: HandlerRegistration, HandlerRegistrationRuns, AllWriters, AllWritersStrong,
  CounterpartGate, VaultMintGate (re-cited), HandlerGateAtV35 and AtomicRecoveryAtHead (stale
  `d9f6789`/`3605e82`/`70096e2ea`/`e561b9cc2` sentences removed), AtomicRecovery (current parts
  re-cited; the pin router/loop/send definitions marked **`c67894b9` record** and kept in place for
  their importers). New notes in AllWriters/VaultMintGate: the router's and the vault's
  `BASE_TOKEN_ASSET_ID` are one value (`OPS-CONFIG`), on which the fallback's base-token exclusion
  relies; `setNativeTokenVault` is one-shot at `b17415d20` (the model's repeatable seed only adds
  runs); the v35 gate on L1 `finalizeDeposit` never stops the fallback.
- **History.** 59 statements moved unchanged (31 of AtomicRecovery, all 19 of
  AtomicRecoveryFaithful, all 9 of PausedRecovery), under `History/{Specs,Properties,Proofs}` with a
  `History` namespace segment. The M1 countermodels and the forged-refund countermodels are tagged
  `@[countermodel]` there.
- **Step 2 (one model).** As above. Added `AtomicRecovery.Properties.VaultRefundRefinesResolution`
  (with `resolutionHooks`): on the registered bridged branch the vault refund `vaultRefund` is the
  canonical NativeTokenVaultBase `bridgeRecoverFailedTransfer`, guards included, for every call. No
  statement was weakened or removed.
- **Step 3 (headlines).** 15 headlines, 15 witnesses, 18 countermodels (5 of them History); audit
  `FOLDER Contracts.AssetRouterBase : 15 / 15 / 18 / 209`. The README lists the 15 with their
  premises; each headline docstring ends with a Premises paragraph naming the model boundary.
- **Renames:** `renames/asset-router.json`, 59 entries, all `history`; checked with
  `ListProperties` before (`1ad0078`) and after: every removed name is an `old`, every `new` exists.
  The only added property is `VaultRefundRefinesResolution`.
- **Edits outside the folder:** `EraSpec.lean` (module list); AtomicFlowManager
  `Proofs/RecoveryTargets.lean` (History import, two certificate names) and
  `Properties/RecoveryTargets.lean` (docstring names); DataEncoding
  `History/Proofs/AssetIdRecovery.lean` (History import, three certificate names); InteropCenter
  `History/Properties/AtomicRouting.lean` (docstring names); Protocol
  `AssetBridgePreparation/Specs/FullRecovery.lean`, `InteropAtomicity/Properties/RefundStrong.lean`,
  `InteropAtomicity/Properties/Pause.lean` (docstring names); `ASSUMPTIONS.md` rows
  `MODEL-ATOMIC-RECOVERY`, `MODEL-ATOMIC-RECOVERY-DEST` and four summary rows (History markers and
  moved names; ids unchanged).

## Not done (follow-ups)

- The `c67894b9` record definitions in `Specs/AtomicRecovery.lean` (`recoverAtomicCall`,
  `recoverCall`, `recoverBundle`, `claimRefund`, `outcomes`, `outcomeOf`, `routerCall`, `directCall`,
  `AtomicBundleValid`, `RouterCallsOnFail`, `HasRouterCallOn`, `OthersLeaveAlone`) stay in place:
  AtomicRecoveryAtHead's pin-against-head statements, AtomicFlowManager `RecoveryTargets` (itself a
  kept pin record) and Protocol `AssetBridgePreparation/FullRecovery` use them. Move them to
  `History/` with those importers (the Protocol unit).
- PausedRecovery is History only; restating the paused-vault results on `AtomicRecoveryAtHead` (the
  vault keeps `whenNotPaused`, `NativeTokenVaultBase.sol:199`) is open.
- Topic names `HandlerGateAtV35` and `AtomicRecoveryAtHead` keep their suffixes (renaming would rename
  about 80 properties for no statement change); the README says they are the `b17415d20` topics.
- `AtomicRecovery`'s remaining statements (`VaultRejectsUnknownAsset`, …) are about `ntvRecover`,
  which is the `b17415d20` vault refund off an L2's base token; they are untagged supporting lemmas.
- `scripts/audit-selftest.sh` was not re-run (the audit script is unchanged).
