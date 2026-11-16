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
`UInt256` hash meets, so they are vacuous as stated (ASSUMPTIONS.md).  The accepted-path
forms also take the walk's length to be the tree's height and the index to be occupied,
which the deployed verifier does not check; `LastLeafFaithful` (below) drops both.

## Faithfulness repairs (pinned `c67894b9`)

Five topics restate earlier results against the Solidity as deployed, in new files.
The original statements are unchanged; each repair names the old reading it replaces,
and the old docstrings in this folder carry a "Correction (<topic>)" note pointing to the
replacement.

* `LastBatchInRootOffset` — `LastBatchInRoot.end_branch_from_onchain_check` uses one
  `B` as the chain-tree leaf POSITION and as the BATCH NUMBER. In `MessageRootBase`
  leaf `p` is batch `f + p` (`batchAt`), with `f` the first pushed batch, assuming every
  batch after `f` is pushed (ASSUMPTIONS.md `PROTO-CONTIGUOUS-PUSH`, not enforced by the
  contract). At `c67894b9` every atomic-interop source chain is a ZKsync OS chain that
  got the built-ins at its genesis upgrade, so its first pushed batch on L1 is 0
  (`L2GenesisForceDeploymentsHelper.sol:448-461`; `L1Bridgehub.createNewChain` calls
  `addNewChain(_chainId, 0)` and `seedGenesisRoot`, `L1Bridgehub.sol:141-142`), and every
  flow settles on L1 (`AtomicFlowManager.sol:56`, `:134-151`). For these chains the
  original position-as-batch reading is exact while pushes are contiguous; the realistic
  gap at the pin is a non-contiguous push after a Gateway round trip
  (`setMigratingChainBatchNumber`), which is `PROTO-CONTIGUOUS-PUSH`.
  `EndBranchFromOnchainCheckOffset` keeps the two apart and asks `OutsideRootLate` only
  for batches after the root's last one; at `f = 0` it is the original statement, and
  the offset generalises it to a chain whose first pushed batch is later (for example
  if the built-ins reach existing chains by upgrade; not verified here).
  `PositionAsBatchMisreads` shows that on an abstract chain whose first pushed batch is
  1, which no atomic-interop chain has at the pin, the original `hout` and conclusion
  are both false. `BatchNumberBoundOrCollision` is a definitional case split with no
  derived content: the proof's batch number equals the stored leaf's, or the two named
  preimages collide.
* `LastLeafFaithful` — the batch-leaf path length (`proofMetadata[2]`) and the mask are
  the prover's, and `Merkle.sol` accepts a padded index. `AcceptedLastLeafAnyLengthOrBreak`
  (no hash premise) is the replacement for `AcceptedLastLeafOrPinnedBreak` over every
  accepted submission. Two new break cases appear, a wrong length (`HeightBreak`) and a
  padded entry equal to the empty-entry constant. `WrongLengthLastLeafAccepted` and
  `PaddedIndexLastLeafAccepted` show that both pass every check the contract performs.
  The model takes the claimed leaf hash `x` as free; on chain it is the batch-leaf hash
  of a 128-byte preimage, so each witness needs a cross-length keccak preimage (of a node
  hash, resp. of the empty-entry constant). "Live" here means not excluded by any check
  the contract performs, only by hash domain separation. The old disjunction and the
  bounded collapse come back under `k = height` and `x ≠ z0`, which the contract does
  not check (`AcceptedLastLeafPinnedLengthOrBreak`, `AcceptedLastLeafAnyLengthOn`), or
  with `k = height` replaced by an instance-located absence of `HeightBreak`
  (`AcceptedLastLeafNoHeightBreakOrBreak`, `AcceptedLastLeafNoHeightBreakOn`; premises
  satisfiable by `AcceptedLastLeafNoHeightBreakOnSatisfiable`). Preimage-length
  separation alone does not give that: `HeightBreak` also covers same-length 64-byte
  collisions. Open item: the outer chain-id hop into the imported settlement-layer root
  is not modelled; the `authenticated` field takes that hop's conclusion as given.
* `ProofPolarityFaithful` — the flow's DECLARED chain `legSourceChainIds[i]` is kept apart
  from the committing chain. The pinned `append` does not bind them. Both checks together
  are exclusive with no honesty premise in this abstraction (`CheckedGatesExclusive`),
  where a proof is the set fact it proves and each chain has one timeless tree. For the
  deployed gates, exclusivity further needs the timeout premises (`PROTO-AGGREGATES`,
  `PROTO-BATCH-SNAPSHOT`; `Contracts.Timeout.StaleRootRefundsDeliveredLeg`,
  `AttackVectors.StaleSnapshotBranches.BeginBranchNeedsBeginIsPrevEnd`,
  `AttackVectors.StaleSnapshotBranches.EndBranchNeedsLaterBatchesLate`) and sound IMT
  proofs, and the latter fail at `c67894b9` by the padding forgery
  (`Contracts.InteropCommitmentTree.CThreeLeafWitness`,
  `Contracts.Timeout.PaddingTimeoutLocatesAbsenceBreak`). Without the finality-side
  check, leg `v` passes the unchecked finality check and passes `authorizeRefund` as the
  missing leg iff it is committed on its real source chain and misdeclared
  (`UncheckedDoubleMintIffMisdeclared`), and a flow is double-minted (finalized on every
  leg, and `authorizeRefund` passed for some leg) iff every leg is committed on its real
  source chain and some leg is misdeclared (`FlowDoubleMintIffSomeMisdeclared`), under
  honest insertion in both; the pinned `append` reaches such a state
  (`PinnedMisdeclaredDoubleMint`). So the "defense-in-depth" reading of that check is
  false at the pin. This replaces the readings in `ProofPolarity` (its header,
  `inclusion_self_binds`, `refund_blocked_when_chain_pinned`), `ProofPolarityStrong`
  (`unchecked_inclusion_gate_iff_checked`) and `Protocol/LocalHonesty.lean`. The
  upgrade's `append` (`e561b9cc2`) makes the check redundant (`UpgradeCheckARedundant`)
  on histories in which every tree was written only by the binding `append` (for example
  a fresh deployment); values from a binding-free `append`, if any chain carries them,
  are outside these results, and the check stays load-bearing for flows that use them.
* `StaleSnapshotFaithful` — the reclaim proof as `verifyNonInclusion` consumes it, over
  real contract runs, with the deadline still the abstract pin `D < t (j+1)`.
  `StaleWitnessNotRedeemableOrBreak` gives no coexistence, or a located `TreeRootBreak`.
  `PaddingReclaimRedeemsDeliveredLeg` shows that the pinned padding constant
  `hashLeaf({0,0,0})` lets the sentinel at an empty slot pass the absence check for a
  delivered leg at a snapshot that meets the abstract pin (break exactly `paddingHit`).
  `StaleWitnessNotRedeemableOrCollision` is what a distinct padding constant buys.
* `StaleSnapshotBranches` — the abstract pin `D < t (j+1)` mapped onto the two deployed
  timeout branches. The begin branch reaches it only under `BeginIsPrevEnd`
  (ASSUMPTIONS.md `PROTO-BATCH-SNAPSHOT`), and the end branch only under
  `LaterBatchesLate B` (every batch numbered after the proven batch `B` settles no
  earlier than the root), which `PROTO-AGGREGATES` gives at the root's last batch of the
  chain. Both are load-bearing. `LaterBatchesLate` is the restricted form, equal to
  `LastBatchInRootOffset`'s re-indexed premise (`LaterBatchesLateOfOffset`); the
  unrestricted "every batch not in the root is late" fails when a batch that is in no
  root settled before the root (below a first pushed batch above 0, or in a gap left by
  a non-contiguous push), and no headline uses it. The satisfiability instances commit a
  value on time, so the headlines do work on them. The pin does not make `j` on time.

The deployed-branch results (`StaleSnapshotBranches`) and the verifier-faithfulness
results (`StaleSnapshotFaithful`) are separate: no theorem composes `StaleSnapshotBranches`
with `StaleSnapshotFaithful`. A composed statement is in the Atomicity model
(`Protocol/InteropAtomicity/Properties/Timeout.lean`):
`Contracts.Timeout.TimeoutMeansMissedDeadlineOrBreak`, the counterpart of
`StaleWitnessNotRedeemableOrBreak`. It takes a `Wf` system (every chain's trees reached
from `setup` by guarded inserts, batch times monotone, every tree within its height), the
`Contracts.Timeout.Aggregates` premise on the root (`PROTO-AGGREGATES`), and a timeout
verified on either deployed branch at batch `N`, with the absence proof accepted by
`verifyNonInclusion` (`Contracts.Atomicity.AbsenceAccepted`). Its BEGIN branch reads
`beginTree`, in which `begin(n+1) = end(n)` is built in (the counterpart of
`BeginIsPrevEnd`). Its END branch (`Contracts.Timeout.EndBranchVerified`) takes
`_verifyLastBatchInRoot` by its conclusion, and `Aggregates` is that branch's bridge. It
concludes that the leg's commit value is absent from its source chain's tree at every
batch that settled by the deadline, or the absence proof carries an `AbsenceBreak`.
`Contracts.Timeout.TimeoutExcludesFinalityOrBreak` takes the same premises and concludes,
for every batch `n` and inclusion proof `p'`, that `p'` does not finalize the leg at `n` on
time, or `p'` carries an `InclusionBreak`, or the absence proof carries an `AbsenceBreak`.
The padding instance `Contracts.Timeout.PaddingTimeoutLocatesAbsenceBreak` is the
deployed-branch counterpart of `PaddingReclaimRedeemsDeliveredLeg`: with the pinned padding
constant `hashLeaf({0,0,0})`, a leg committed on time passes that gate on the BEGIN branch
on the forged padding proof, and the break is an `AbsenceBreak` on that proof.
`Contracts.Timeout.AcceptedTimeoutMeansMissedDeadlineOrBreak` runs the END branch with the
last-batch proof instead and adds a `PinnedBreak` right after batch `N` in the chain tree or a
`PathCollision` on the submitted batch-leaf path. That proof is `LastBatchAccepted`, which
pins the walk's length to the tree's height and `N` to an occupied leaf, over `RootBacking`,
which reads leaf position `N` as batch `N` (see their Correction notes).

These modules expose the hypotheses used by the library's argument. They do not
prove the compiled verifier, authenticate imported roots, or establish settlement
clocks. The cross-chain binding model is `../../Protocol/Spec.lean`; the reference
application composition is `../../Examples/BurnMintBridge/ProtocolComposition.lean`.
