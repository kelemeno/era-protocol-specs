# Consolidation inventory: atomic-proof unit

Unit `atomic-proof`, branch `consol9/atomic-proof`, from `claude/proof-round-9` at `1ad0078`.
Contract: the `AtomicInteropProof` library (`l1-contracts/contracts/atomic-interop/libraries/AtomicInteropProof.sol`,
190 lines at `b17415d20`). Target commit: era-contracts `draft/v0.35.0` head `b17415d20`, checked
against an extracted `b17415d20` tree. `c67894b9` (the abandoned interop pin, the
`ad-atomic-interop` feature line) and `e561b9cc2` are not in the local era-contracts clone, so their
line numbers are not re-checked: they survive only in History and in "what differs" notes, as
earlier rounds recorded them.

Property counts at the branch point (135 in the folder, all untagged): AuthenticateRootAtV35 12,
LastBatchInRoot 8, LastBatchInRootOffset 4, LastLeaf 13, LastLeafFaithful 10, ProofPolarity 7,
ProofPolarityStrong 14, ProofPolarityFaithful 14, StaleSnapshot 4, StaleSnapshotBranches 13,
StaleSnapshotFaithful 5, TimeoutSoundness 12, TimeoutSoundnessStrong 10, Timestamps 9. The
namespaces are `AttackVectors.<Topic>` and `MerkleSpec.LastLeaf{,Faithful}` (the audit's folder is
by module, so all of them count as `Contracts.AtomicInteropProof`).

Concurrent wave-2 units: merkle-libs (Merkle, FullMerkle, DynamicIncrementalMerkle) and
asset-router (AssetRouterBase). `LastLeaf` imports `Merkle.Specs.Verifier` / `PathCollision`, and
DynamicIncrementalMerkle `ChainTreeBacking` and Merkle `DomainSeparation` import `LastLeaf` /
`LastLeafFaithful`. This unit renames none of the declarations those folders use.

## What changed at `b17415d20` (checked)

* `verifyTimeoutAbsence` (`AtomicInteropProof.sol:77-124`): the declared flag picks the leaf
  (`:85-87`), `_authenticateRoot` (`:89`), the settlement-layer match (`:90-92`), the imported
  root's timestamp nonzero and after the deadline (`:94-100`), the begin branch `t > D`
  (`:103-106`), the end branch `t <= D` and `_verifyLastBatchInRoot` (`:107-114`), then
  `verifyNonInclusion` (`:116-123`). The same gate structure the pin-era topics model.
* `_verifyLastBatchInRoot` (`:130-143`) is the same loop; its NatSpec (`:126-129`) is shorter than
  the pin's (the sentence "a non-last leaf necessarily has a populated right subtree ..." is gone).
  The timeout and soundness argument quoted by `TimeoutSoundness` / `LastBatchInRoot` now lives in
  `protocol-docs/atomicity/proofs.md:72-115` (the library header points there, `:27-31`).
* `_authenticateRoot` (`:155-189`) reads the settlement-layer words by position
  (`MessageHashing.readSettlementLayerReference`); the pin re-ran `_getProofData`
  (`AuthenticateRootAtV35` already models both).
* `AtomicFlowManager.append` binds the declared chain: `legSourceChainIds[legIndex] == block.chainid`
  (`AtomicFlowManager.sol:140-146`). At the pin `append` did not (the H1 record in
  `ProofPolarityFaithful`); `e561b9cc2` added the check, and it is the `b17415d20` code.
* `IndexedMerkleTree.setup` pads with `IMT_EMPTY_LEAF_HASH` (`IndexedMerkleTree.sol:51`,
  `common/Config.sol:141`). At the pin it padded with `hashLeaf({0,0,0})` (the H2 record in
  `StaleSnapshotFaithful`). `verifyNonInclusion` (`:154-172`) is unchanged.
* `MessageRootBase`: `_addNewChain` (`:275-293`) starts an empty chain tree at
  `_startingBatchNumber`; `_recordChainBatchRoot` (`:183-197`) makes numbers consecutive;
  `_pushChainBatchRoot` (`:201-214`) appends `batchLeafHash(root, number, l1Timestamp)`;
  `seedGenesisRoot` (`:296-314`) pushes batch 0 for a fresh chain with a nonzero genesis root.
  `L1Bridgehub.createNewChain` calls `addNewChain(_chainId, 0)` then `seedGenesisRoot`
  (`L1Bridgehub.sol:134-135`) for every new chain (no ZKsync OS gate at this commit);
  `registerAlreadyDeployedZKChain` calls `addNewChain(_chainId, getTotalBatchesExecuted())`
  (`:316`). The executor calls only `addChainBatchRootV32` (`Executor.sol:165`); a Gateway return
  calls `setMigratingChainBatchNumber` (`ChainAssetHandlerBase.sol:414`).

## Topics

"Imported by" lists modules outside the topic's own Specs/Properties/Proofs triple that import it
(by `import`); prose-only references are noted where a name moves.

| Topic | Commit it models (checked) | Model types | Imported by | Decision |
|---|---|---|---|---|
| TimeoutSoundness | no pin in its Specs; quotes the pin's library header, which at `b17415d20` is `protocol-docs/atomicity/proofs.md:86-96` (same argument) | `BatchHistory` (end sets of values, `ℕ` times), `AppendOnly`, `TimeOrdered`, `beginSet`, `BatchHistory'`, `BeginIsPrevEnd`, `AppendOnly'` | in-folder (LastBatchInRoot, TimeoutSoundnessStrong, LastBatchInRootOffset); Examples/BurnMintBridge `EndBranch` (Specs, Proofs) | **keep**, abstract batch-history layer; **re-cite** to `b17415d20` |
| TimeoutSoundnessStrong | header `c67894b9`; the same gate at `b17415d20` `:77-124` (flag `:85-87`, root time `:94-100`, branches `:103-114`) | `ImtRootLeaf`, `deployedLeaf`, `FinalizedBy`, `TimeoutBranchChecks`, `TimeoutGateAt`, histories | none | **re-pin** to `b17415d20` (gate unchanged) |
| LastBatchInRoot | no pin; quotes the pin's `_verifyLastBatchInRoot` NatSpec and compiled Yul | `RightEmpty` (index level), `OutsideRootLate` (`ℕ` clock) | MessageRoot `Properties/Aggregation`; Examples `EndBranch`; in-folder | **keep** (index-level layer); **re-cite** the loop to `:130-143` and the argument to `proofs.md:90-95`; the Yul paragraph marked as compiled from the pin |
| LastBatchInRootOffset | header `c67894b9` (MessageRootBase lines, genesis helper) | `batchAt`, two histories | Protocol/InteropAtomicity `BatchPosition` (Properties) | **re-pin**: cite `MessageRootBase` at `b17415d20`, and state the difference: at `b17415d20` every chain created by `createNewChain` is genesis-seeded (`f = 0`) and a chain registered by `registerAlreadyDeployedZKChain` starts later, so the offset form is the one that covers both |
| LastLeaf | no pin (shape argument, hash level) | `HashBreak`, `EntriesNotEmpty`, `childPair`, `zeroPair`, `PinnedBreak`, `PairInjOn`, `TreePair`, `VerifiedPair`, `demoHash` | DynamicIncrementalMerkle `ChainTreeBacking` (Proofs), Merkle `DomainSeparation` (Specs, Proofs), Protocol/InteropAtomicity `BatchPosition`, `Timeout` | **keep** (hash-level layer of the last-leaf check); **re-cite** the NatSpec to `:126-129`. `NotHashBreak` and `AcceptedLastLeafOrBreak` take global pair-injectivity and stay vacuous, untagged |
| LastLeafFaithful | header `c67894b9` (MessageHashing, Merkle, AtomicInteropProof lines) | `LastBatchPathAccepted`, `LastLeafAnyLengthBreak`, `PathTreePair` | DynamicIncrementalMerkle `ChainTreeBacking`, Merkle `DomainSeparation`, Protocol/InteropAtomicity `RefundFaithful`; in-folder `AuthenticateRootAtV35` | **canonical** acceptance of the batch-leaf hop; **re-pin**: `MessageHashing.sol:129` (length byte), `:192-205` (leaf, mask, walk), `Merkle.sol:133-140`, `AtomicInteropProof.sol:130-143`, `:160-162`; same logic |
| AuthenticateRootAtV35 | `b17415d20` (header; spot-checked `:155-189`, `MessageHashing.sol:252-262`, `:285-299`); also transcribes the pin's `_authenticateRoot` and `readAggregationHopPath` | `Proof`, `Env`, `getProofData`, `readSL`, `readHop`, `proveShared`, `authenticateRootV35`, `LastBatchCheck`, `EndBranchPassesV35`, `SharedTreeBacking`, `SLHopBreak`, `ChainTreeEntries`, `AuthBreak`, `parseMeta`; pin: `readHopPin`, `authenticateRootPin`, `EndBranchPassesPin` | none | **canonical** v35 transcription of the library's proof-word layer. **split**: the pin transcriptions and the two pin-vs-v35 equalities (`AuthenticateRootRefactorExactV35`, `EndBranchRefactorExactV35`) go to **History** |
| ProofPolarity | no pin; quotes source comments, which at `b17415d20` read `AtomicFlowManager.sol:192-194` (finality) and `:221-223` (refund) | `HonestInsertion` over abstract `tree` | in-folder (ProofPolarityStrong) | **keep**, abstract set facts; **re-cite** the comments |
| ProofPolarityStrong | header `c67894b9`; the same two checks at `b17415d20` (`:196-199`, `:228-230`) | `CheckedInclusionGate`, `UncheckedInclusionGate`, `CheckedAbsenceGate`, `UncheckedAbsenceGate`, `liveKeys` (over L2ICT `Tree`, MultichainGate `Chain`) | none | **re-pin** (checks unchanged) |
| ProofPolarityFaithful | `c67894b9` (pinned `append` with no binding) and `e561b9cc2` (binding `append`) | `HonestInsertion` (duplicate of ProofPolarity's), `DeclaredInsertion`, `appendAt`, `PinnedReach`, `UpgradeReach`, gates, `cm*` | none (prose: Protocol `LocalHonesty`, InteropAtomicity `FlowBindingAtHead`) | **split**: the binding `append` is `b17415d20`'s (`:127-146`), so `UpgradeReach` and its results are current and re-cited. The pinned `append` (`PinnedReach`) and the three statements over it (`PinnedReachHonest`, `PinnedMisdeclaredDoubleMint`, `RefundNotBlockedWhenPinnedToDeclared`) are the **H1** record and go to **History**. Bridge lemma: the two `HonestInsertion`s agree |
| StaleSnapshot | no pin (`IMTAbstract` order theory, abstract pin `D < t (j+1)`) | `staleHistory` | none (prose: Protocol `NoTheft`) | **keep** (canonical `IMTAbstract`) |
| StaleSnapshotBranches | header `c67894b9` (`verifyTimeoutAbsence` lines) | `BatchSnapshots`, `BeginIsPrevEnd`, `OutsideRootLate` (`UInt256` clock), `LaterBatchesLate`, `BeginBranch`, `EndBranch`, histories | none (prose: IMT `Model`, Protocol `FlowAtomicity`, `NoTheft`) | **re-pin** to `:77-124`; bridge lemmas onto `TimeoutSoundness.BeginIsPrevEnd` and `LastBatchInRoot.OutsideRootLate` |
| StaleSnapshotFaithful | header `c67894b9` (padding `hashLeaf({0,0,0})`) and `e561b9cc2` | `paddedRun*` (pin padding), `oneInsertRun*`; over the canonical L2ICT layers `Tree`, `Run`, `root`, `NonInclusionAccepted`, `TreeRootBreak` (padding a parameter) | none (prose: L2ICT `TreeRoot`, `PaddingAtHead`; IMT `Model`; Protocol `FlowAtomicity`, MultichainGate; Examples `EndBranch`) | **split**: the general results take the padding as a parameter and hold at `b17415d20` (`z0 = IMT_EMPTY_LEAF_HASH`, `IndexedMerkleTree.sol:51`); re-cite. `PaddingReclaimRedeemsDeliveredLeg` and `paddedRun*` are the **H2** record and go to **History** |
| Timestamps | no pin (`IMTAbstract`) | `attackHistory`, `attackTime` | in-folder (StaleSnapshotBranches) | **keep** |

## Duplicates and model layering (step 2)

The folder is one library, modelled at four layers that are refinements of each other, not
competing models of the same state:

1. **Proof words** (`AuthenticateRootAtV35`): the `b17415d20` transcription of `_authenticateRoot`,
   the two readers and `_verifyLastBatchInRoot`. Canonical.
2. **Batch-leaf path acceptance** (`LastLeafFaithful`, over `LastLeaf`'s hash-level breaks and the
   Merkle folder's walk). Joined to layer 1 by `LastBatchCheckOnVerifiedWalkV35` (the path the
   v35 end branch inspects satisfies `LastBatchPathAccepted`'s `inBounds` and `zeroCheck`).
3. **Index level** (`LastBatchInRoot.RightEmpty`, `LastBatchInRootOffset`): the shape argument
   with hashes idealised.
4. **Batch histories and the abstract gates** (`TimeoutSoundness{,Strong}` over value sets,
   `StaleSnapshotBranches` over `IMTAbstract` leaf sets, `StaleSnapshot` / `Timestamps` over
   `IMTAbstract` runs, `StaleSnapshotFaithful` over the canonical L2ICT `Tree` runs,
   `ProofPolarity*` over abstract trees).

Definitions duplicated with identical or equivalent bodies, and their bridges:

| Definition | Copies | Bridge |
|---|---|---|
| honest insertion | `ProofPolarity.HonestInsertion`, `ProofPolarityFaithful.HonestInsertion` | new `ProofPolarityFaithful.Properties.HonestInsertionAgrees` (equal as propositions) |
| begin = previous end | `TimeoutSoundness.BeginIsPrevEnd` (value sets), `StaleSnapshotBranches.BeginIsPrevEnd` (leaf sets) | new `StaleSnapshotBranches.Properties.BeginIsPrevEndProjects` (the leaf-set form implies the value-set form of the key projection) |
| batches outside the root are late | `LastBatchInRoot.OutsideRootLate` (`ℕ` clock), `StaleSnapshotBranches.OutsideRootLate` (`UInt256` clock) | new `StaleSnapshotBranches.Properties.OutsideRootLateIffNat` |

Both IMT layers used here are the canonical ones the imt unit chose (`IMTAbstract`, and the L2ICT
list state `Tree` with `TreeRoot`'s padding parameter); no private IMT copy exists in this folder.

## History (H1, H2 and the pin transcription)

Moved under `EraSpec/Contracts/AtomicInteropProof/History/{Specs,Properties,Proofs}/`, with a
`History` namespace segment, statements and proofs unchanged:

* `AuthenticateRootAtV35`: `readHopPin`, `authenticateRootPin`, `EndBranchPassesPin`;
  `AuthenticateRootRefactorExactV35`, `EndBranchRefactorExactV35`.
* `ProofPolarityFaithful` (H1, the forged double-mint refund of a misdeclared leg under the pinned
  `append`): `PinnedReach`; `PinnedReachHonest`, `PinnedMisdeclaredDoubleMint`,
  `RefundNotBlockedWhenPinnedToDeclared`.
* `StaleSnapshotFaithful` (H2, the padding forgery): `paddedRun`, `paddedRunHeight`,
  `paddedRunTime`; `PaddingReclaimRedeemsDeliveredLeg`.

## Edits planned outside the folder

* `EraSpec.lean`: the three History Proofs modules.
* `ASSUMPTIONS.md`: the results-table rows for `ProofPolarityFaithful` and `StaleSnapshotFaithful`
  (moved names, commit labels) and `LastBatchInRootOffset`, `LastLeafFaithful`,
  `StaleSnapshotBranches` (commit labels); ids unchanged.
* Docstring references to the moved names (no code use): L2InteropCommitmentTree `Specs/TreeRoot`,
  `Properties/PaddingAtHead`; IndexedMerkleTree `Properties/Model`; Protocol `LocalHonesty`,
  `FlowAtomicity`, MultichainGate `Specs/Model`, `Properties/Model`; Examples/BurnMintBridge
  `Specs/EndBranch`. Each gains the `History` segment only.

## Outcome

* **Step 1.** Every Specs header in the folder cites `b17415d20` `file:line` (checked against the
  extracted tree); pin facts survive only as marked "at the extraction pin `c67894b9`" notes or in
  History. Logic differences stated: the binding `append` (H1 fixed), the `IMT_EMPTY_LEAF_HASH`
  padding (H2 fixed), the positional `_authenticateRoot`, the shorter `_verifyLastBatchInRoot`
  NatSpec (the argument moved to `protocol-docs/atomicity/proofs.md`), and, for
  `LastBatchInRootOffset`, that at `b17415d20` a chain registered by
  `registerAlreadyDeployedZKChain` has a first pushed batch above 0. Six statements moved to History
  (`renames/atomic-proof.json`, all `history`, checked with `ListProperties` before and after).
* **Step 2.** No second model of the same state exists in the folder (four layers, above). New
  bridge statements `ProofPolarityFaithful.Properties.HonestInsertionAgrees`,
  `StaleSnapshotBranches.Properties.BeginIsPrevEndProjects` and `OutsideRootLateIffNat`. No
  statement was weakened or removed.
* **Step 3.** 10 headlines, 6 witnesses, 9 countermodels (3 of them History); audit
  `FOLDER Contracts.AtomicInteropProof : 10 / 6 / 9 / 113`. The README lists the 10 headlines.
  Headline docstrings gained a "Premises" paragraph where a premise was only implicit.
* **Outside the folder:** `EraSpec.lean` (three History modules); `ASSUMPTIONS.md` results rows
  for LastBatchInRootOffset, LastLeafFaithful, ProofPolarityFaithful, StaleSnapshotFaithful,
  StaleSnapshotBranches (commit labels, moved names; ids unchanged); docstring-only name updates
  (`History` segment) in L2InteropCommitmentTree `Specs/TreeRoot`, `Properties/PaddingAtHead`,
  IndexedMerkleTree `Properties/Model`, Protocol `LocalHonesty`, `FlowAtomicity`, MultichainGate
  `Specs/Model`, `Properties/Model`, Examples/BurnMintBridge `Specs/EndBranch`.

## Not done

* The `AttackVectors.*` / `MerkleSpec.LastLeaf*` namespaces and the `…AtV35` / `…Faithful` topic
  names are kept (external references; the imt unit kept its names for the same reason).
* `TimeoutSoundness{,Strong}`, `LastBatchInRoot{,Offset}`, `LastLeaf`, `StaleSnapshot`,
  `Timestamps`, `ProofPolarity{,Strong}` are untagged: their statements are over abstract
  histories or idealised hashes whose model premises are not all Lean hypotheses.
* No formal refinement from `LastBatchInRoot.RightEmpty` (index level) to the hash-level
  `zeroCheck`; `LastLeaf` covers that argument in collision form.
* `ASSUMPTIONS.md` rows `PROTO-BATCH-SNAPSHOT` and `PROTO-CONTIGUOUS-PUSH` still describe
  `c67894b9` lines (true as statements about the pin); re-citing them belongs with the Protocol unit
  or the ASSUMPTIONS split.
* Prose elsewhere (Protocol/InteropAtomicity) that still calls these models "pinned `c67894b9`" is
  left to the Protocol unit.
