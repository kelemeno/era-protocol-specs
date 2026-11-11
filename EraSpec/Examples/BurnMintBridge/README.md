# Reference burn/mint bridge — not a deployed contract model

This is an illustrative application of `../../Core/PreparedApplication.lean`.
It is not a specification or verification of L2AssetRouter, NativeTokenVaultBase,
or BridgedStandardERC20. Their intended properties are tracked in `../../../REVIEW.md`.

- `Model.lean`: a single-obligation burn/mint/recovery model, preparation laws,
  stable execution, immutable input, replay prevention, value accounting, and
  countermodels for unlocked balances and conflicting protocol evidence.
- `ProtocolComposition.lean`: conditional composition with source-bound,
  time-pinned commitment histories across the complete flow.
- `Specs/EndBranch.lean`, `Properties/EndBranch.lean`, `Proofs/EndBranch.lean`
  (namespace `Applications.BurnMintBridge.EndBranch`): the halted-chain (END) timeout
  branch composed into the adapter's evidence. Over the adapter's history the
  abstract END form is already a successor-pinned `Missing`
  (`MissingEndImpliesMissing`, `EvidenceEitherRunsAreAdapterRuns`). As the contract
  runs it, both branches cite a batch inside an imported root created after the
  deadline (`checkedEvidence`); under `RootAggregates` every accepted timeout refines
  `Missing` (`TimeoutViaImpliesMissing`, `BeginViaNeverFinalized`,
  `EndViaNeverFinalized`), so `CheckedBridgeNoDoublePayment` and
  `CheckedBridgeValueConserved` hold. Completeness (`TimeoutComplete`) needs the END
  branch (`HaltedChainNeedsEndBranch`). `StaleRootDoublePays` and
  `UncheckedEndDoublePays` show `RootAggregates` and the last-batch check are
  load-bearing. At hash level the last-batch path is pinned
  (`PinnedBridgeNoDoublePaymentOrBreak`, no hash premise).
- `Specs/EndBranchStrong.lean`, `Properties/EndBranchStrong.lean`,
  `Proofs/EndBranchStrong.lean` (same namespace): the satisfiability witnesses of
  `EndBranch` pinned to the resolved transfer. `EndBranchRefundWitness`,
  `OnTimeLegExecutesWitness` and `BeginBranchRefundWitness` do not tie the run's record
  to their transfer `i`; the `…Gap` statements show runs that meet their bodies by
  resolving another transfer (for the BEGIN witness, a refund authorized by the END
  branch alone; for the on-time witness, a transfer with no prerequisite on a history
  where nothing is ever on time). The `…Pinned` forms record `s.record = some i` and
  run on single-branch evidence (`endFormEvidence`, `beginOnlyEvidence`), with no
  END-branch timeout on any leg of the BEGIN-pinned transfer.
  `ReachableResolutionAuthorizedByRecord` says every reachable delivery or refund is
  backed by evidence for the recorded transfer.

The model uses natural-number amounts, fixed token/endpoint identities, exact
full recovery, and a declared set of permitted interference steps. Concrete
amount bounds, access control, pauses, configuration changes, token behavior,
external calls, rollback, and real encoding/root authentication require further
work. The halted-chain timeout branch is composed in `EndBranch`; its IMT
membership and non-membership proofs stay abstract, and only the END submission's
batch-leaf path is checked at hash level. Full recovery here must not be confused with
the real manager's best-effort recovery.
