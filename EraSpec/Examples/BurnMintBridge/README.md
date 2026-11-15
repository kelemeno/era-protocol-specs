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
  (`PinnedBridgeNoDoublePaymentOrBreak`, no hash premise). The END branch reads a
  chain-tree leaf position as a batch number (exact at `c67894b9` for atomic-interop
  source chains, whose first pushed batch on L1 is 0, while pushes are contiguous:
  `PROTO-CONTIGUOUS-PUSH`), and at hash level takes the batch-leaf walk's length to be the
  tree's height and the batch to be an occupied leaf, which the deployed verifier does not
  check; `Properties/EndBranch.lean` carries a "Correction (LastBatchInRootOffset)" and a
  "Correction (LastLeafFaithful)" note.
- `Specs/EndBranchStrong.lean`, `Properties/EndBranchStrong.lean`,
  `Proofs/EndBranchStrong.lean` (same namespace): stronger forms of satisfiability
  witnesses of `EndBranch`. The bodies of `EndBranchRefundWitness`,
  `OnTimeLegExecutesWitness` and `BeginBranchRefundWitness` do not tie the run's record
  to their transfer `i`: `EndBranchRefundWitnessGap`, `OnTimeLegExecutesWitnessGap` and
  `BeginBranchRefundWitnessGap` show final states that resolve another transfer (for the
  BEGIN witness, a refund authorized by the END branch alone; for the on-time witness,
  `i` has no prerequisite and no nonzero commit value is ever on time). But in every
  world where such a body holds, the run that prepares and resolves `i` itself meets it
  too (`…RecordPinFree`), so the record pin of the `…Pinned` forms adds nothing world by
  world: `EndBranchRefundWitnessPinned` restates `EndBranchRefundWitness`, and in §1 its
  END-form evidence pins no branch. What the other two pinned forms add per world is at
  least one prerequisite, each with a nonzero commit value (on-time form), and the
  exclusion of an END-branch timeout on `i`'s legs (BEGIN form); without that exclusion
  the BEGIN witness does not show that the BEGIN branch is needed: the END-branch timeout
  may be on another leg of `i`, even against the same root
  (`BeginBranchRefundWitnessSingleRootGap`), or on the leg with the BEGIN-branch timeout,
  against another root (`BeginBranchRefundWitnessBranchGap`).
  `CheckedExecutionWitnessPinned` adds the on-time form's requirement to
  `CheckedExecutionWitness`, and `PinnedBridgeRefundWitnessLinked` ties
  `PinnedBridgeRefundWitness`'s refund to the END submission it names. Without those
  additions, `CheckedExecutionWitness`'s body holds for a transfer with no prerequisite, or
  with prerequisites of commit value `0`, on a history where no nonzero commit value is
  ever on time (`CheckedExecutionWitnessGap`, `CheckedExecutionWitnessZeroValueGap`), and
  `PinnedBridgeRefundWitness`'s for a refund on the BEGIN branch next to an END submission
  for a leg that is not a prerequisite (`PinnedBridgeRefundWitnessGap`).
  `ReachableResolutionAuthorizedByRecord` says every reachable delivery or refund is backed
  by evidence for the recorded transfer.

The model uses natural-number amounts, fixed token/endpoint identities, exact
full recovery, and a declared set of permitted interference steps. Concrete
amount bounds, access control, pauses, configuration changes, token behavior,
external calls, rollback, and real encoding/root authentication require further
work. The halted-chain timeout branch is composed in `EndBranch`; its IMT
membership and non-membership proofs stay abstract, and only the END submission's
batch-leaf path is checked at hash level. Full recovery here must not be confused with
the real manager's best-effort recovery.
