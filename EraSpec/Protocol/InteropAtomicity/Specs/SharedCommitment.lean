import EraSpec.Protocol.InteropAtomicity.Specs.OncePerLeg

/-!
# Model: what a shared commitment means, on a run, at the gate and at the timeout check

**This file is definitions only.**  Statements are in
`EraSpec.Protocol.InteropAtomicity.Properties.SharedCommitment`, proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.SharedCommitment`.

Source paths below are relative to `l1-contracts/contracts/` in the pinned era-contracts
tree (`c67894b9`).

## The statement being repaired

`Contracts.Refund.Properties.SharedCommitmentYieldsCollision` (`Properties/Refund.lean`) says:
two obligations with one commit value are the same leg (equal `(flowId, bundleHash)`), or
`cv` has *some* collision.  The colliding inputs are existentially quantified, and every map
`cv : UInt256 → UInt256 → UInt256` has a collision
(`Contracts.Refund.Properties.UnpinnedCollisionsAlwaysExist`).  So the statement holds for every
`cv` and carries no information.

Pinning the collision to the two obligations themselves gives
`Contracts.Refund.Properties.CommitmentPinsLegOrCollision`: the same leg, or `CommitClash cv o o'`.
That form is excluded middle.  Given equal commit values, two `(flowId, bundleHash)` pairs are
equal or they differ, and if they differ the values collide on exactly those inputs.  Drawing
`o` and `o'` from a run's log, as the backlog item asks, does not change this: the excluded
middle holds for any two obligations.  A statement with content has to say something the run
makes true or false.

## Where the run has something to say

The commit value is `commitValue(flowId, bundleHash)
= uint256(keccak256(abi.encode(ATOMIC_COMMIT_LEAF_TAG, flowId, bundleHash)))`
(`atomic-interop/libraries/AtomicInteropProof.sol:100-102`; the tag is a constant,
`atomic-interop/IAtomicInterop.sol:93-94`).  It carries no chain.  Three places decide what a
shared value does.

1. **Appending.**  `AtomicFlowManager.append` (`atomic-interop/AtomicFlowManager.sol:87-102`)
   inserts the value into this chain's tree, and `IndexedMerkleTree.insert` refuses a value that is
   already a key (`IMTValueAlreadyExists`, `common/libraries/IndexedMerkleTree.sol:72-74`) or zero
   (`IMTValueZero`, `:69-71`).  Topic `OncePerLeg` (`Contracts.AppendPath`) proved that this
   refutes a commit-value clash between two obligations appended on one chain.  `AppendableLog`
   below names the exact condition the append path puts on one chain's log, so the converse can be
   stated too: every log meeting it is the log of some run.
2. **The gate.**  `requireFlowFinalized` (`AtomicFlowManager.sol:105-131`) computes each leg's
   commit value from the presented flow (`:127`) and checks its inclusion against the leg's
   declared source chain's batch-end root (`:128`, `AtomicInteropProof.sol:113-139`).
   `IndexedMerkleTree.verifyInclusion` (`IndexedMerkleTree.sol:133-145`) checks only that the
   presented leaf carries the value and that its path recomputes the root.  So the gate learns
   that the *value* is in that tree, not *which leg* put it there.  The NatSpec draws the
   conclusion: "a leg's commit value can only be inserted into its own source chain's tree, and the
   membership check below can only pass against that chain" (`AtomicInteropProof.sol:107-110`; also
   `AtomicFlowManager.sol:117-119` and `atomic-interop/README.md:49-50`).  The gate is checked
   against the fixed history `S` of `Contracts.Atomicity`, which is not tied to what any chain
   appended.  `HistoryFromRuns` below is that tie, stated as a premise, and
   `HistoryFromSystemRun` is the same for a history cut from one run of every chain at once.
3. **The timeout check.**  `authorizeRefund` (`AtomicFlowManager.sol:134-162`) proves the missing
   leg's commit value absent from its declared chain's tree (`:150-151`,
   `AtomicInteropProof.sol:152-206`).  `absenceLog` below names the `append` log behind the root
   that check uses.

## Model boundary

`HistoryFromRuns` and `HistoryFromSystemRun` are premises, not theorems: they say each batch-end
tree in `S` is the tree of a state the chain's own run reaches.  Deriving it from an operational model, in which the
bootloader snapshots the live tree at every batch boundary (`atomic-interop/README.md:36-41`), is
the open projection (`Protocol/InteropAtomicity/README.md`).  The fact that `bundleHash` embeds
`block.chainid` (`interop/InteropCenter.sol:644`), which would make one `(flowId, bundleHash)` pair
unique across chains, is not modelled either (backlog S4).  In the model the same pair may be
appended on two chains.
-/

namespace Contracts.SharedCommitment

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund Contracts.AppendPath

/-- **THE OBLIGATIONS A SYSTEM RUN'S LOGS NAME.**  For a `Contracts.AppendPath.SysSteps` run,
`log` lists the obligations its `append` calls committed and `alog` its `authorizeRefund` calls.
Each logged call names the obligation it marked `Revertable`, `obligationOf a.flow a.leg`, which is
the object of `Contracts.Refund.RefundBreak`.  The leg a call proves absent (`a.missing`) is not
included: it is typically one that was never appended. -/
def runObligations (log : List Obligation) (alog : List AuthCall) : List Obligation :=
  log ++ alog.map (fun a => obligationOf a.flow a.leg)

/-- **WHAT THE APPEND PATH ASKS OF ONE CHAIN'S LOG.**  For chain `c` and commit value `cv`:

* every entry is on chain `c`, the chain whose center ran the `append`;
* every entry's commit value is nonzero (`IMTValueZero`, `IndexedMerkleTree.sol:69-71`);
* no entry appears twice (`ManagerLegAlreadyCommitted`, `AtomicFlowManager.sol:93`);
* no two entries have a `CommitClash` (`IMTValueAlreadyExists`, `IndexedMerkleTree.sol:72-74`).
  This is `CommitValueInjOn cv log`, the bounded premise of
  `Contracts.Refund.Properties.CommitmentPinsLegOn`. -/
def AppendableLog (cv : CommitValue) (c : Chain) (log : List Obligation) : Prop :=
  (∀ o ∈ log, o.chain = c) ∧ (∀ o ∈ log, commitOf cv o ≠ 0) ∧ log.Nodup ∧ CommitValueInjOn cv log

/-- **A BATCH HISTORY READ OFF RUNS.**  For every chain `c` and batch `n`:

* `snap c n` is a state chain `c` reaches from `genesis`, and `logAt c n` is that run's `append`
  log, i.e. the obligations chain `c`'s center had committed by the end of batch `n`;
* the tree `S` records for chain `c` at the end of batch `n` is `snap c n`'s tree.  This is the
  tree whose root `verifyInclusion` is checked against (`IMT_END_ROOT_LEAF_INDEX`,
  `AtomicInteropProof.sol:119-122`).

Only the tree is tied to the run: `S.time` and `S.height` stay free, and the runs for consecutive
batches need not extend one another.  `Contracts.AppendPath.Properties.RunSnapshotsMeetWfShape`
covers the histories cut from one run. -/
def HistoryFromRuns (cv : CommitValue) (S : System) (snap : Chain → ℕ → ChainState)
    (logAt : Chain → ℕ → List Obligation) : Prop :=
  ∀ c n, Steps cv c genesis (snap c n) (logAt c n) ∧ S.tree c n = (snap c n).tree

/-- **THE `append` LOG BEHIND THE ROOT A TIMEOUT PROOF IS CHECKED AGAINST.**  For a history read
off runs with logs `logAt`, deadline `D`, chain `c` and batch `N`.  `authorizeRefund`'s timeout
check (`AtomicInteropProof.verifyTimeoutAbsence`, `AtomicInteropProof.sol:152-206`;
`Contracts.Atomicity.LegRefundableBy`) proves absence from the BEGIN root of a late batch
(`D < S.time c N`) or from the END root of an on-time batch.  The END root of batch `N` is the
tree at the end of batch `N`, with log `logAt c N`.  The BEGIN root of batch `k + 1` is the END
root of batch `k` (`Contracts.Atomicity.beginTree`), with log `logAt c k`.  The BEGIN root of
batch `0` is the genesis tree, behind which nothing was appended. -/
def absenceLog (logAt : Chain → ℕ → List Obligation) (S : System) (D : ℕ) (c : Chain) :
    ℕ → List Obligation
  | 0 => if D < S.time c 0 then [] else logAt c 0
  | k + 1 => if D < S.time c (k + 1) then logAt c k else logAt c (k + 1)

/-- **A BATCH HISTORY READ OFF RUNS OF EVERY CHAIN AT ONCE.**  For every batch `n`, `snapY n` is a
state of all chains that a `Contracts.AppendPath.SysSteps` run reaches from `genesisAll`, with
`append` log `logs n` and authorize log `alogs n`; and `S` records, for every chain `c`, the tree of
`snapY n c` at the end of batch `n`.  The run's `authorizeRefund` calls are checked against the
history `S'`.  `S' = S` is allowed: the history the refund checks consult may be the one the run
itself produces.  As in `HistoryFromRuns`, only the trees are tied to the run. -/
def HistoryFromSystemRun (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S' S : System) (snapY : ℕ → Chains) (logs : ℕ → List Obligation)
    (alogs : ℕ → List AuthCall) : Prop :=
  ∀ n, SysSteps h z0 hl cv fh S' genesisAll (snapY n) (logs n) (alogs n)
    ∧ ∀ c, S.tree c n = (snapY n c).tree

end Contracts.SharedCommitment
