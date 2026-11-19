# Consolidation inventory: the small L1 contracts (unit `smalls-l1`)

Branch `consol9/smalls-l1`, from `claude/proof-round-9` at `35d2eb9`. Target commit: era-contracts
`draft/v0.35.0` head `b17415d20`. Folders: `AdminFacet`, `Bridgehub`, `ChainAssetHandler`,
`L1ChainAssetHandler`, `Diamond`, `ExecutorFacet`, `MailboxFacet`, `ValidatorTimelock`,
`Governance`, `ChainAdminOwnable`, `PriorityTree`, `L1Nullifier`, `BlobsL1DAValidatorZKsyncOS`
(all under `EraSpec/Contracts/`). At the branch point they hold 422 of the 4447 property
statements.

## Source check

Every Specs model of these folders already names `b17415d20` as its commit. Round 8 wrote several
of them at `d9f6789` and re-pinned them by a byte-identity argument. Both were re-checked here:

* **Byte identity.** Every era-contracts file these folders cite (151 file references, resolved to
  paths) is byte-identical between `d9f6789` and `b17415d20`
  (`git diff d9f6789 b17415d20 -- <files>` is empty). Between the two commits only
  `IChainTypeManager.sol` changed under `state-transition/`, and no folder here cites it.
  `Diamond.sol`, `DiamondProxy.sol`, `DiamondInit.sol`, `Governance.sol`, `ValidatorTimelock.sol`
  and its access-control base are also identical at `ccf00623c` (the v35-history equivalent of
  `e561b9cc2`). The extracted tree at `b17415d20` matches the git objects for every cited file.
* **Line numbers.** A script resolved every `file:line` citation in the 13 folders (1447 of them,
  including the per-file abbreviations `BB:`, `CAH:`, `VT:`, `Ex:`, `N:`, a bare `:N` for
  `Mailbox.sol`, ...) against the `b17415d20` tree. Every range is inside its file. For each
  citation it looked for an identifier of the citing sentence in the cited lines; the 71 citations
  without such a match, and the 29 where a function named right before the citation is not in the
  range, were read by hand. All of them cite the right lines (the identifier sits a line or two
  away, or the sentence describes the lines in other words). One false positive: `:532` in
  `MailboxFacet/Properties/RequestPaths.lean:40` continues an `Admin.sol` citation. OpenZeppelin
  citations were checked against `openzeppelin-contracts-v4` at `dc44c9f1` (v4.9.6) and
  `openzeppelin-contracts-upgradeable-v4` at `2d081f24`, the submodule commits `b17415d20` pins.
* **Logic differences.** None: no model in these folders was written against a commit whose
  cited code differs from `b17415d20`. The remaining mentions of other commits are notes on what
  differs at `main` (`70096e2ea`) or at the interop pin (`c67894b9`), which these models do not
  cover.

## Topics

"Importers" are modules outside the folder that import it (grep of all of `EraSpec`). "Overlap"
lists other models of the same Solidity code.

| Folder / topic | Commit | Model types | Importers | Overlap | Decision |
|---|---|---|---|---|---|
| `AdminFacet` Access, PriorityMode, Upgrade, Fees (48 props) | `b17415d20` | `State`, `Env`, `Config`, `Entry`, `Call`, `Label`, `Step`, `Run` (`Specs/AdminFacet.lean`); one-check mutants (`Specs/Mutants.lean`) | none | `Diamond` (freeze, the cut entries), `ExecutorFacet` (priority mode, `_revertBatches`, `setValidator`), `ChainAdminOwnable` (access checks only), the CTM and upgrade folders (other units) | keep as the facet's model |
| `Bridgehub` Registry (42) | `b17415d20` | `Config`, `State`, `Action`, `Outcome`, `Run` | none | `ChainAssetHandler` (per-hub `settlementLayer`, registration, `chainTypeManager`), `ChainAdminOwnable` (owner and admin slots) | keep |
| `ChainAssetHandler` Migration, Pause (34) | `b17415d20` | `World`, `Sys`, `Msg`, `Label`, `Step`, `Reach`, `Run` | none | `L1ChainAssetHandler` (the same burn, mint and confirmation code, with batch numbers and intervals), `Bridgehub` | keep; see below |
| `L1ChainAssetHandler` SettlementLayerValidation (22) | `b17415d20` (plus the loop of `main` `70096e2ea`, `isValidSettlementLayerMain`, compared on the model's runs) | `ValWorld`, `ValEnv`, `ValState`, `ValLabel`, `valStep` | none | `ChainAssetHandler` | keep; see below |
| `Diamond` DiamondProxy (27) | `b17415d20` | `ProxyState`, `Env`, `InitRun`, `Step`, `Run`; imports `ChainTypeManager/Specs/DiamondStorage.lean` and `LiveRouting.lean` (CTM unit) | none | `AdminFacet` (freeze at facet level), CTM `DiamondStorage` (reused, not duplicated) | keep; the CTM files it imports are another unit's |
| `ExecutorFacet` Pipeline, Checks (34) | `b17415d20` | `State`, `Env`, `Call`, `Init`, `Reach`, `Ablation`; witness runs (`Specs/Witness.lean`) | none | `PriorityTree` (`processBatch`, abstract here), `AdminFacet` | keep |
| `MailboxFacet` RequestPaths (19) | `b17415d20` | `Diamond`, `Env`, `Request`, `L2Tx`, `TreeStepL1`, `TreeRunL1` | `Protocol/PriorityRequests` | `PriorityTree` (counters and a ghost leaf map only) | keep |
| `MailboxFacet/Specs/PriorityTree.lean` (definitions only, 0 props) | `d9f6789` in its header; every cited file identical at `b17415d20` | `PushTree`, `PTree`, `TreeParams`, `TreeLabel`, `TreeRun` | `Protocol/PriorityMirror` | `PriorityTree` SegmentBinding (`processBatch`) | **move** to `PriorityTree/Specs/Library.lean`, re-pin the header to `b17415d20`, and prove that its `processBatch` is SegmentBinding's |
| `PriorityTree` SegmentBinding (12) | `b17415d20` | `BatchInfo`, `processBatch`, `executePriority`, `ProcessRun` | none | the library model above | keep; bridge added |
| `ValidatorTimelock` Model, Delay, Roles, Isolation, Ownership, LibMap (54) | `b17415d20` | `State`, `Env`, `Action`, `Call`, `Run` (`Specs/Model.lean`); `Isolation` and `LibMap` are layers on it | none | none | keep |
| `Governance` Timelock (48) | `b17415d20` | `State`, `Env`, `Operation`, `Effect`, `Callee`, `Frame`, `Tx`, `Variant` | none | none | keep |
| `ChainAdminOwnable` Authority, AdminRoles (25) | `b17415d20` | `State`, `Config`, `Sem`, `Origin`, `Event` (`Specs/Authority.lean`); `AdminRoles` is a layer on it | none | diamond admin pair (`AdminFacet`), Bridgehub admin slots (`Bridgehub`); access checks only | keep |
| `L1Nullifier` Model, Reentrancy (41) | `b17415d20` | `Sys`, `Env`, `Cfg`, `Checks`, `Label`, `Step`, `Reach`; `NestedRun` (`Specs/Reentrancy.lean`) on it | none | none in these folders | keep |
| `BlobsL1DAValidatorZKsyncOS` Model (16) | `b17415d20` | `VState`, `TxEnv`, `World`, `WStep` | `Protocol/ZKsyncOSDA` | none | keep |

## Decisions

* **One target commit.** All 13 folders model `b17415d20`; there is nothing to move to `History`.
  Sentences that only say a file is also identical at an earlier pin are removed from the READMEs
  and Specs headers; notes on what differs at `main` stay where they describe what is not covered.
* **The priority-tree library.** `MailboxFacet/Specs/PriorityTree.lean` is a model of
  `PriorityTree.sol`, not of the Mailbox. It moves to `PriorityTree/Specs/Library.lean`, namespace
  `Contracts.PriorityTree.Library`, and `PriorityTree/Properties/Library.lean` proves that its
  `processBatch`, with `calculateRootPaths` read as `MerkleSpec.RootPaths.rootPaths`, is
  SegmentBinding's `processBatch` (same reverts, same new `unprocessedIndex`, nothing else
  written). Edits outside the folders: the import, `open` lines and docs of
  `Protocol/PriorityMirror`, the module list in `EraSpec.lean`, and the file path in the
  `MODEL-PRIORITY-MIRROR` row of `ASSUMPTIONS.md`.
* **Overlapping models of different contracts stay.** `AdminFacet`/`Diamond`,
  `AdminFacet`/`ExecutorFacet`, `Bridgehub`/`ChainAssetHandler` and `ChainAdminOwnable`'s
  diamond and Bridgehub stand-ins each model a contract in its own folder and read only a few
  entry points of the other, at a different level of detail (the stand-ins keep access checks
  only, or one flag). Each contract has one Specs model of its own. One bridge is proved:
  `AdminFacet` `RevertBatchesAgreesWithExecutorModel` (the two transcriptions of
  `ZKChainBase._revertBatches` succeed together and write the same counters). The others are not
  done.
* **`ChainAssetHandler` and `L1ChainAssetHandler`.** Two models of the burn, mint and confirmation
  code. `ChainAssetHandler` follows every hub, the pauses and the migration numbers, without batch
  numbers; `L1ChainAssetHandler` follows one chain's intervals and batch numbers, for
  `isValidSettlementLayer`. Neither state is a projection of the other, so no property moves. A
  simulation lemma between them is not done; both READMEs say the models are not composed.
* **Headlines.** Tagged per the `EraSpec.Core.Headline` convention once it lands on
  `claude/proof-round-9`; each README starts with its headline list.
