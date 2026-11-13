# AtomicInteropProof

Source: `contracts/atomic-interop/libraries/AtomicInteropProof.sol` in the pinned
era-contracts tree. This Solidity library owns the finalization/timeout proof gates.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| LastBatchInRoot | [Specs/LastBatchInRoot.lean](Specs/LastBatchInRoot.lean) | [Properties/LastBatchInRoot.lean](Properties/LastBatchInRoot.lean) | [Proofs/LastBatchInRoot.lean](Proofs/LastBatchInRoot.lean) |
| ProofPolarity | [Specs/ProofPolarity.lean](Specs/ProofPolarity.lean) | [Properties/ProofPolarity.lean](Properties/ProofPolarity.lean) | [Proofs/ProofPolarity.lean](Proofs/ProofPolarity.lean) |
| StaleSnapshot | [Specs/StaleSnapshot.lean](Specs/StaleSnapshot.lean) | [Properties/StaleSnapshot.lean](Properties/StaleSnapshot.lean) | [Proofs/StaleSnapshot.lean](Proofs/StaleSnapshot.lean) |
| TimeoutSoundness | [Specs/TimeoutSoundness.lean](Specs/TimeoutSoundness.lean) | [Properties/TimeoutSoundness.lean](Properties/TimeoutSoundness.lean) | [Proofs/TimeoutSoundness.lean](Proofs/TimeoutSoundness.lean) |
| Timestamps | [Specs/Timestamps.lean](Specs/Timestamps.lean) | [Properties/Timestamps.lean](Properties/Timestamps.lean) | [Proofs/Timestamps.lean](Proofs/Timestamps.lean) |
| LastLeaf | [Specs/LastLeaf.lean](Specs/LastLeaf.lean) | [Properties/LastLeaf.lean](Properties/LastLeaf.lean) | [Proofs/LastLeaf.lean](Proofs/LastLeaf.lean) |
| LastBatchInRootOffset | [Specs/LastBatchInRootOffset.lean](Specs/LastBatchInRootOffset.lean) | [Properties/LastBatchInRootOffset.lean](Properties/LastBatchInRootOffset.lean) | [Proofs/LastBatchInRootOffset.lean](Proofs/LastBatchInRootOffset.lean) |
| LastLeafFaithful | [Specs/LastLeafFaithful.lean](Specs/LastLeafFaithful.lean) | [Properties/LastLeafFaithful.lean](Properties/LastLeafFaithful.lean) | [Proofs/LastLeafFaithful.lean](Proofs/LastLeafFaithful.lean) |
| ProofPolarityFaithful | [Specs/ProofPolarityFaithful.lean](Specs/ProofPolarityFaithful.lean) | [Properties/ProofPolarityFaithful.lean](Properties/ProofPolarityFaithful.lean) | [Proofs/ProofPolarityFaithful.lean](Proofs/ProofPolarityFaithful.lean) |
| StaleSnapshotFaithful | [Specs/StaleSnapshotFaithful.lean](Specs/StaleSnapshotFaithful.lean) | [Properties/StaleSnapshotFaithful.lean](Properties/StaleSnapshotFaithful.lean) | [Proofs/StaleSnapshotFaithful.lean](Proofs/StaleSnapshotFaithful.lean) |
| StaleSnapshotBranches | [Specs/StaleSnapshotBranches.lean](Specs/StaleSnapshotBranches.lean) | [Properties/StaleSnapshotBranches.lean](Properties/StaleSnapshotBranches.lean) | [Proofs/StaleSnapshotBranches.lean](Proofs/StaleSnapshotBranches.lean) |

`LastLeaf` is the hash side of `_verifyLastBatchInRoot`: if every left-child
sibling on the path is the empty-subtree hash, the proven leaf is the last leaf,
**or** a concrete `HashBreak` (node collision, or an entry equal to the empty-entry
constant) is exhibited. No hash injectivity is assumed for that disjunction over the
tree's own siblings (`LastLeafOrBreak`), but `HashBreak`'s node-collision case takes any
four words, so it is always inhabited (`HashBreakAlways`) and the disjunction is
trivially true; `LastLeafOrPinnedBreak` and `AcceptedLastLeafOrPinnedBreak` pin the break to a
named tree node (`PinnedBreakNotAlways` shows it is not always inhabited). The submitted-path version
(`AcceptedLastLeafOrBreak`) and `NotHashBreak` take global pair-injectivity, which no
`UInt256` hash meets, so they are vacuous as stated (ASSUMPTIONS.md).

## Faithfulness repairs (pinned `c67894b9`)

Five topics restate earlier results against the Solidity as deployed, in new files.
The original statements are unchanged; each repair names the old reading it replaces.

* `LastBatchInRootOffset` — `LastBatchInRoot.end_branch_from_onchain_check` uses one
  `B` as the chain-tree leaf POSITION and as the BATCH NUMBER. In `MessageRootBase`
  leaf `p` is batch `f + p` (`batchAt`), with `f` the first pushed batch (`f = 0` for a
  genesis-seeded ZKsync OS chain, `f = 1` for a fresh EraVM chain), assuming every batch
  after `f` is pushed (ASSUMPTIONS.md `PROTO-CONTIGUOUS-PUSH`, not enforced by the
  contract). `EndBranchFromOnchainCheckOffset` keeps the two apart and asks
  `OutsideRootLate` only for batches after the root's last one.
  `PositionAsBatchMisreads` shows that on a fresh EraVM chain the original `hout` and
  conclusion are both false. `BatchNumberBoundOrCollision` is the pinned-collision
  restatement (a case split, no further premise): the proof's batch number equals the
  stored leaf's, or the two named preimages collide.
* `LastLeafFaithful` — the batch-leaf path length (`proofMetadata[2]`) and the mask are
  the prover's, and `Merkle.sol` accepts a padded index. `AcceptedLastLeafAnyLengthOrBreak`
  (no hash premise) is the replacement for `AcceptedLastLeafOrPinnedBreak` over every
  accepted submission. Two new break cases appear, a wrong length (`HeightBreak`) and a
  padded entry equal to the empty-entry constant. `WrongLengthLastLeafAccepted` and
  `PaddedIndexLastLeafAccepted` show that both are live. The old disjunction and the
  bounded collapse come back only under `k = height` and `x ≠ z0`, which the contract
  does not check. Open item: the outer chain-id hop into the imported settlement-layer
  root is not modelled; the `authenticated` field takes that hop's conclusion as given.
* `ProofPolarityFaithful` — the flow's DECLARED chain `legSourceChainIds[i]` is kept apart
  from the committing chain. The pinned `append` does not bind them. Both checks together
  are exclusive with no premise (`CheckedGatesExclusive`). Without the finality-side
  check, a live leg is executed and refunded exactly when it is misdeclared
  (`UncheckedDoubleMintIffMisdeclared`), and the pinned `append` reaches that state
  (`PinnedMisdeclaredDoubleMint`). So the "defense-in-depth" reading of that check is
  false at the pin. The upgrade's `append` (`e561b9cc2`) makes it redundant
  (`UpgradeCheckARedundant`).
* `StaleSnapshotFaithful` — the reclaim proof as `verifyNonInclusion` consumes it, over
  real contract runs. `StaleWitnessNotRedeemableOrBreak` gives no coexistence, or a
  located `TreeRootBreak`. `PaddingReclaimRedeemsDeliveredLeg` shows that the pinned
  padding constant `hashLeaf({0,0,0})` lets the sentinel at an empty slot reclaim a
  delivered leg (break exactly `paddingHit`). `StaleWitnessNotRedeemableOrCollision` is
  what a distinct padding constant buys.
* `StaleSnapshotBranches` — the abstract pin `D < t (j+1)` mapped onto the two deployed
  timeout branches. The begin branch reaches it only under `BeginIsPrevEnd`, and the end
  branch only under `LaterBatchesLate B` (every batch numbered after the proven batch `B`
  settles no earlier than the root; ASSUMPTIONS.md `PROTO-BATCH-SNAPSHOT`). Both are
  load-bearing. `LaterBatchesLate` is the restricted form, equal to
  `LastBatchInRootOffset`'s re-indexed premise (`LaterBatchesLateOfOffset`); the
  unrestricted "every batch not in the root is late" is false for EraVM chains and is
  not used. The end-branch satisfiability witness is a fresh EraVM chain. The pin does
  not make `j` on time.

These modules expose the hypotheses used by the library's argument. They do not
prove the compiled verifier, authenticate imported roots, or establish settlement
clocks. The cross-chain binding model is `../../Protocol/Spec.lean`; the reference
application composition is `../../Examples/BurnMintBridge/ProtocolComposition.lean`.
