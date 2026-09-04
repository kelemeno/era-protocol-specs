import EraSpec.Contracts.TreeRoot

/-!
# Model: the atomicity gate, across chains and across batches

`Contracts.TreeRoot` models one chain's tree and the proofs over its root.  This
file models the multi-chain, multi-batch system those proofs are resolved against,
and the gate the destination runs before executing an atomic bundle:
`AtomicFlowManager.requireFlowFinalized`.

**This file is definitions only.**  The atomicity results are stated in
`EraSpec.Properties.Atomicity` and proved in `EraSpec.Proofs.Atomicity`.

## The question this exists to answer

`AttackVectors.FlowAtomicity` proves the sanctioned atomicity property at set
level and then records an honest limitation, verbatim:

> the abstract layer does NOT prove that all legs of a flow reach the SAME
> outcome. […] Whatever forces same-outcome (if anything) must live in the
> higher-level bundle/executor logic, not in the commitment tree.

It does live there, and this is it.  `requireFlowFinalized` loops over **every**
leg of the flow and requires an inclusion proof for each before the executing
bundle may run — the source comment says so in as many words:

    // Atomicity gate: replaces {executeBundle}'s L1-message inclusion proof. Proves every leg of the
    // flow was committed in its source chain's IMT before the deadline, and that this bundle is one
    // of the legs.
    IAtomicFlowManager(L2_ATOMIC_FLOW_MANAGER_ADDR).requireFlowFinalized(bundleHash, _finality);

So mixed *tree states* are reachable (that countermodel stands), but a mixed
*outcome* is not: in a state where one leg is missing, no leg executes.  That is
partial atomicity — none-or-all — and it is what `Properties.Atomicity` states.

## What the model has to carry that `TreeRoot` does not

1. **Many chains.** Each leg's proof is resolved against its own declared source
   chain's tree (`ProofSourceChainMismatch` enforces the match), so the state is a
   tree per chain.
2. **Many batches.** Proofs are checked against a batch-boundary root, not "the"
   current root, and the finality condition is a bound on the *batch's* timestamp.
   So the state is a tree per chain **per batch**, and a batch may contain any
   number of `append`s — hence `Reaches` rather than a single `insert` between
   consecutive batches.
3. **One clock.** `verifyInclusion` compares each leg's `l1BatchTimestamp` against
   the single flow `deadline`, and the flow's `settlementLayerChainId` must equal
   every proof's resolved settlement layer (`_checkSettlementLayerIsL1` plus the
   `ProofSettlementLayerMismatch` check).  That shared settlement layer is what
   licenses comparing different chains' batch timestamps to one deadline, and it
   is why `System.time` is a single ℕ-valued clock per chain rather than
   per-chain-incomparable.
4. **Data availability.** The verifier is a pure function: it accepts any
   well-formed proof.  But someone has to *build* the proof, and that needs the
   leaf preimage and the sibling path — chain data.  `Access` is what a prover can
   present and `DataAvailable` is the DA assumption about it.  Keeping them
   separate is the point: DA is an assumption about the world, not a theorem, and
   `Properties.Atomicity.WithoutDaCommittedLegIsStuck` shows the main result is
   false without it.

## Out of scope

The aggregation tree.  `IsLastOnTime` below is the *conclusion* that
`_verifyLastBatchInRoot` plus a post-deadline settlement-layer root establish
about the end-root timeout branch; the path argument itself is
`AttackVectors.LastBatchInRoot` and the aggregation machinery is not modelled
here.  Also out of scope: the destination's own replay guard
(`bundleStatus[bundleHash] = FullyExecuted`), which is
`AttackVectors.BundleStatusMachine`.
-/

namespace Contracts.Atomicity

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

/-- Chain ids, as `uint256`. -/
abbrev Chain := UInt256

/-! ## Flows -/

/-- One leg of a flow: its declared source chain (`legSourceChainIds[i]`) and its
commit value (`commitValue(flowId, legBundleHashes[i])`). -/
structure FlowLeg where
  chain : Chain
  commit : UInt256
deriving DecidableEq

/-- An `AtomicFlow`, at the level this file reasons about: the legs and the
deadline.  `flowId` and the settlement layer are not carried — `flowId` is the
hash that binds these fields together (`_checkFlowId`), and the settlement layer
is what makes the one `deadline` meaningful across chains (see the header). -/
structure Flow where
  legs : List FlowLeg
  deadline : ℕ

/-- Commit values are keccak hashes, so nonzero; `0` is the tree's sentinel key
and can never be a leg's commit value. -/
def FlowWf (F : Flow) : Prop := ∀ leg ∈ F.legs, leg.commit ≠ 0

/-! ## The system: a tree per chain per batch -/

/-- The multi-chain, multi-batch state.

* `tree c n` — chain `c`'s commitment-tree contract state at the **end** of batch
  `n`.  This is the state behind `ChainBatchRootTree.IMT_END_ROOT_LEAF_INDEX`, the
  root `verifyInclusion` authenticates.
* `time c n` — the batch's `l1BatchTimestamp`, the value compared against the
  flow deadline.
* `height c n` — the batch's `FullMerkle._height`, which `pushNewLeaf` grows as
  the tree fills. -/
structure System where
  tree : Chain → ℕ → Tree
  time : Chain → ℕ → ℕ
  height : Chain → ℕ → ℕ

/-- A well-formed system.

`batch` is where "a batch may contain many `append`s" lives: consecutive batch
boundaries are related by any number of guarded inserts, not by one. -/
structure Wf (S : System) : Prop where
  /-- Every chain starts from `setup` (the genesis upgrade) and may commit during
  its first batch. -/
  start : ∀ c, Reaches setup (S.tree c 0)
  /-- Each batch applies any number of guarded inserts. -/
  batch : ∀ c n, Reaches (S.tree c n) (S.tree c (n + 1))
  /-- Batch order follows settlement time — the parenthesis in
  `AtomicInteropProof`'s soundness paragraph, and the concrete counterpart of
  `AttackVectors.Timestamps`' `Monotone t`. -/
  timeOrdered : ∀ c, Monotone (S.time c)
  /-- The hash tree has room for its leaves (`pushNewLeaf` grows `_height`). -/
  capacity : ∀ c n, (S.tree c n).leafCount ≤ 2 ^ S.height c n

/-- The tree at the **beginning** of a batch (`IMT_BEGIN_ROOT_LEAF_INDEX`):
`begin(n+1) = end(n)`, and `begin(0)` is the genesis tree. -/
def beginTree (S : System) (c : Chain) : ℕ → Tree
  | 0 => setup
  | n + 1 => S.tree c n

/-- The height that goes with `beginTree`. -/
def beginHeight (S : System) (c : Chain) : ℕ → ℕ
  | 0 => 0
  | n + 1 => S.height c n

/-! ## Proofs a prover presents, and data availability -/

/-- The prover-supplied part of an `ImtProof`: exactly the fields
`IndexedMerkleTree.verifyInclusion` / `verifyNonInclusion` consume.  The chain and
batch the proof is *about* are the indices of `Access` below, matching the struct's
`sourceChainId` / `batchNumber`. -/
structure ImtProof where
  leaf : Leaf
  index : ℕ
  sibs : ℕ → UInt256
  pathLen : ℕ

/-- What a prover can actually present for chain `c`'s batch `n`.

This is not a property of the contracts — the verifier is a pure function and
will accept any well-formed proof.  It is a property of the *world*: to build a
proof you must know the leaf preimage and the sibling path, which means reading
chain `c`'s published data. -/
abbrev Access := Chain → ℕ → ImtProof → Prop

/-- The proof `FullMerkle.merklePath` yields for leaf `i` of chain `c`'s batch-`n`
tree: the honest sibling stream at the tree's own height. -/
def honestProof (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System)
    (c : Chain) (n i : ℕ) : ImtProof :=
  ⟨(S.tree c n).leaf i, i, honestSibs h z0 (leafHashes hl (S.tree c n)) i, S.height c n⟩

/-- **THE DATA-AVAILABILITY ASSUMPTION.**  For every occupied leaf of every chain
at every batch, the honest proof is presentable.

This is exactly what "DA is available on all chains" buys, stated as a hypothesis
about `Access` rather than derived: nothing in the protocol makes it true.
`Properties.Atomicity.WithoutDaCommittedLegIsStuck` is the countermodel showing
partial atomicity fails without it. -/
def DataAvailable (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System) (A : Access) : Prop :=
  ∀ (c : Chain) (n i : ℕ), i < (S.tree c n).leafCount → A c n (honestProof h z0 hl S c n i)

/-- No prover can present anything — total DA failure, for the countermodel. -/
def noAccess : Access := fun _ _ _ => False

/-! ## The finality signal -/

/-- `IndexedMerkleTree.verifyInclusion` accepts `p` for value `v` against chain
`c`'s batch-`n` END root. -/
def Accepts (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System)
    (c : Chain) (n : ℕ) (v : UInt256) (p : ImtProof) : Prop :=
  InclusionAccepted h hl (root h z0 hl (S.tree c n) (S.height c n)) v
    p.leaf p.index p.sibs p.pathLen

/-- **THE IMT FINALITY SIGNAL, for one leg.**  `AtomicInteropProof.verifyInclusion`
passed: there is a batch of the leg's DECLARED source chain whose timestamp is at
or before the deadline, and an accepted inclusion proof for the leg's commit value
against that batch's END root.

The declared source chain is the only chain considered, which is the
`ProofSourceChainMismatch` check; the timestamp bound is `ProofDeadlineExceeded`. -/
def LegFinalized (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System)
    (D : ℕ) (leg : FlowLeg) : Prop :=
  ∃ (n : ℕ) (p : ImtProof), S.time leg.chain n ≤ D ∧ Accepts h z0 hl S leg.chain n leg.commit p

/-- **THE ATOMICITY GATE.**  `requireFlowFinalized`: every leg of the flow carries
finality evidence.  The loop is over all `n` legs, so this is a conjunction over
the whole flow, not a statement about the executing leg. -/
def FlowFinalized (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System) (F : Flow) : Prop :=
  ∀ leg ∈ F.legs, LegFinalized h z0 hl S F.deadline leg

/-- A leg is executed on its destination only through the gate:
`executeAtomicBundle` calls `requireFlowFinalized` with the full flow, and
`ManagerExecutingBundleNotInFlow` requires the executing bundle to be one of the
legs, before any call runs. -/
def ExecutedVia (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System)
    (F : Flow) (leg : FlowLeg) : Prop :=
  leg ∈ F.legs ∧ FlowFinalized h z0 hl S F

/-- **THE GATE A NAIVE IMPLEMENTATION WOULD WRITE**: check only the executing
leg's own inclusion, the way a non-atomic bundle checks its own L1 message.
`Properties.Atomicity.SelfOnlyGateAdmitsMixedOutcome` is what that costs. -/
def SelfOnlyGate (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System)
    (F : Flow) (leg : FlowLeg) : Prop :=
  leg ∈ F.legs ∧ LegFinalized h z0 hl S F.deadline leg

/-! ## Finalizability — what a prover can actually do -/

/-- The leg **can** be finalized: there is an on-time batch, a proof a prover can
present for it, and the verifier accepts that proof.  This is `LegFinalized`
strengthened by presentability, which is what makes it an operational claim rather
than an existence claim. -/
def LegFinalizableBy (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System) (A : Access)
    (D : ℕ) (leg : FlowLeg) : Prop :=
  ∃ (n : ℕ) (p : ImtProof),
    S.time leg.chain n ≤ D ∧ A leg.chain n p ∧ Accepts h z0 hl S leg.chain n leg.commit p

/-- The whole flow's gate can be satisfied with presentable proofs: every leg's
destination can run `requireFlowFinalized` and pass. -/
def FlowFinalizableBy (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System) (A : Access)
    (F : Flow) : Prop :=
  ∀ leg ∈ F.legs, LegFinalizableBy h z0 hl S A F.deadline leg

/-! ## The refund side -/

/-- Batch `n` is the chain's last batch that settled by the deadline.

For the END-root timeout branch, this is what `_verifyLastBatchInRoot` together
with a post-deadline settlement-layer root establishes: the proven batch is the
chain's last one inside a root created after the deadline, so no later batch of
that chain settled in time.  Assumed here rather than derived — the aggregation
tree is not modelled (see the header). -/
def IsLastOnTime (S : System) (c : Chain) (D : ℕ) (n : ℕ) : Prop :=
  S.time c n ≤ D ∧ ∀ m, n < m → D < S.time c m

/-- `IndexedMerkleTree.verifyNonInclusion` accepts `p` as an absence proof for `v`
against the root of `T` at `height`. -/
def AbsenceAccepted (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (T : Tree) (height : ℕ) (v : UInt256) (p : ImtProof) : Prop :=
  NonInclusionAccepted h hl (root h z0 hl T height) v p.leaf p.index p.sibs p.pathLen

/-- **THE TIMEOUT GATE, for one leg.**  `AtomicInteropProof.verifyTimeoutAbsence`
passed on one of its two branches: absence from the BEGIN root of a batch that
settled after the deadline, or absence from the END root of the chain's last
in-time batch.

Both are against the leg's declared source chain — the `ProofSourceChainMismatch`
check in `authorizeRefund`, whose necessity is `Properties.Protocol`. -/
def LegRefundable (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System)
    (D : ℕ) (leg : FlowLeg) : Prop :=
  ∃ (N : ℕ) (p : ImtProof),
    (D < S.time leg.chain N ∧
        AbsenceAccepted h z0 hl (beginTree S leg.chain N) (beginHeight S leg.chain N)
          leg.commit p)
      ∨ (IsLastOnTime S leg.chain D N ∧
          AbsenceAccepted h z0 hl (S.tree leg.chain N) (S.height leg.chain N) leg.commit p)

/-! ## A concrete configuration, for the countermodels

Two chains.  Chain `0` commits `a` during batch 0; chain `1` never commits
anything.  Batch numbers double as settlement timestamps, so with deadline `0`
batch 0 is on time and every later batch is late. -/

/-- The mixed-state system: one leg committed, its sibling never committed. -/
def mixedSystem (a : UInt256) : System where
  tree := fun c _ => if c = 0 then insert setup a 0 else setup
  time := fun _ n => n
  height := fun c _ => if c = 0 then 1 else 0

/-- The two-leg flow over `mixedSystem`: leg `a` on chain `0`, leg `b` on chain `1`. -/
def mixedFlow (a b : UInt256) : Flow where
  legs := [⟨0, a⟩, ⟨1, b⟩]
  deadline := 0

end Contracts.Atomicity
