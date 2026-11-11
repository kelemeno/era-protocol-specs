import EraSpec.Protocol.InteropAtomicity.Specs.Atomicity
import EraSpec.Protocol.InteropAtomicity.Specs.Timeout

/-!
# Model: the gate as a destination runs it — imported roots and settlement proofs

`Contracts.Atomicity` checks each leg's IMT proof directly against the batch's true END
root (`Accepts`), and its finalizability predicates (`LegFinalizableBy`,
`FlowFinalizableBy`) add only that the IMT proof is presentable (`Access`,
`DataAvailable`).  The destination's gate does more.  Before it uses an IMT root at all,
it authenticates that root against a settlement-layer root the destination has itself
imported.  This file models that step per destination, so that "every leg can be
finalized" can be stated about the destination that has to do it.

**This file is definitions only.**  Statements are in
`EraSpec.Protocol.InteropAtomicity.Properties.RootImport`, proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.RootImport`.

## What a destination checks

Sources: the pinned era-contracts tree `c67894b9`, under `l1-contracts/contracts/`.

`requireFlowFinalized` (`atomic-interop/AtomicFlowManager.sol:105-131`) runs on the
destination, inside `L2InteropHandler.executeAtomicBundle`.  It checks the flow's
settlement layer against the destination's own `L1_CHAIN_ID` (`_checkSettlementLayerIsL1`,
`:111`, `:236-240`; the field is set once by `initL2`, `:57`, `:69-74`) and calls
`AtomicInteropProof.verifyInclusion` for every leg (`:122-129`).  `verifyInclusion`
(`atomic-interop/libraries/AtomicInteropProof.sol:113-139`) first runs `_authenticateRoot`
(`:256-290`):

1. `proveL2LeafInclusionShared(sourceChainId, batchNumber, mask, chainImtRoot,
   settlementProof)` must return true (`:265-272`, else `ProofImtRootInclusionFailed`).
   On an L2 this is `L2MessageVerification._proveL2LeafInclusionRecursive`
   (`interop/L2MessageVerification.sol:14-52`).  A multi-hop proof recurses once, to the
   settlement layer's chain id and block (`:42-51`).  There it must be a final node whose
   recomputed root equals the destination's
   `L2_INTEROP_ROOT_STORAGE.interopRoots(slChainId, slBlock).root`, and that root must be
   nonzero (`:29-33`).
2. A final-node proof, which carries no settlement-layer batch reference, is rejected
   (`ProofMissingSettlementLayerBatch`, `:283-285`).  So it is not enough for a
   destination to have imported the source chain's own batch root; the root it needs is
   a settlement-layer root.
3. `slChainId` and `l1BatchTimestamp` are read from that same proof (`:287-289`).  The
   caller requires `slChainId` to be the flow's `settlementLayerChainId`
   (`ProofSettlementLayerMismatch`, `:123-125`) and the timestamp to be on time
   (`ProofDeadlineExceeded`, `:128-130`).  Only then is IMT inclusion checked, against
   the authenticated `chainImtRoot` (`:131-138`).

`interopRoots` is per-destination storage (`interop/L2InteropRootStorage.sol:40`).  Roots
enter it only through `addSingleInteropRoot` / `addInteropRootsInBatch`, both
`onlyCallFromBootloader` (`:58-76`).  So an import is a separate state transition of the
destination.  Nothing on a source chain makes it happen, and neither does any source
chain's data availability.  Imported roots are never overwritten
(`InteropRootAlreadyExists`, `:97-100`) and there is no entry point that removes one.

`head-main-3605e82`, `upgrade-e561b9cc2` and `head-v35-d9f6789` have the same structure:
`_authenticateRoot` is `AtomicInteropProof.sol:155-189` there, with the final-node
rejection at `:177-179`, and `L2MessageVerification` terminates at `interopRoots` in the
same way.

## What is modelled

* `World` is the destination side.  It holds the settlement layer's aggregation roots
  (`slRoot`), which of them each destination has imported (`imported`, keyed on
  `(destination, slChainId, slBlock)`), and each destination's `L1_CHAIN_ID` (`l1`).
* `SettlementProof` is the `settlementProof` field, as far as `_authenticateRoot` reads
  it: the final-node bit and the settlement-layer reference.  `SettlementAccepted` is
  steps 1 and 2 above.  `AcceptsAt` adds the flow's settlement layer and the IMT check.
* The gate on a destination is `ExecutedAtBy`.  Finalizability on a destination is
  `LegFinalizableAt` / `FlowFinalizableAt`.  Two world assumptions in the style of
  `DataAvailable` go with them.  `ImportAvailable` says the destination holds imported
  roots covering every batch that settled by the deadline.  `SettlementDataAvailable`
  says the multi-hop proof for a batch inside a root is presentable.

## Model boundary

The aggregation paths inside a settlement proof are not modelled; `Specs/Atomicity.lean`
puts the aggregation tree out of scope in the same way.  A `SettlementProof` stands for a
well-formed proof (`ProofInvalidChainBatchRootDepth` passes) whose paths are the honest
ones for its root.  It is accepted exactly when that root is imported on the destination
and aggregates the batch.  This idealizes the soundness direction only: a forged
aggregation path is never accepted.  The results here are liveness results.  The
countermodel's rejection uses only the import half: with
`interopRoots[slChainId][slBlock]` zero, `proveL2LeafInclusionShared` returns false
whatever the path.

The world is a snapshot of which roots each destination holds when its gate runs.  Not
modelled: the import transitions themselves (`ImportsGrow` records only that imports
accumulate), the imported roots' timestamps (read only on the timeout side,
`Specs/Timeout.lean`), and the handler's own checks (pause, destination, `bundleStatus`;
`AttackVectors.BundleStatusMachine`).  `Flow` elides the settlement layer, so the flow's
`settlementLayerChainId` is a separate argument `sl` here.
-/

namespace Contracts.RootImport

open MerkleSpec Contracts.InteropCommitmentTree Contracts.Atomicity

/-- Destination chain ids: the chain whose `L2InteropHandler.executeAtomicBundle` runs the
gate. -/
abbrev Dest := Chain

/-! ## The destination side of the world -/

/-- The destination side of the world, at the moment a gate runs.

* `slRoot sl k` is the aggregation root settlement layer `sl` produced at block `k`.
  `Contracts.Timeout.SlRoot.upTo c` is the last batch of chain `c` inside it.  This is what
  `interopRoots[sl][k]` holds once a destination imports it: the imported tuple is checked
  on the settlement layer when the importing batch executes
  (`ExecutorFacet._verifyDependencyInteropRoots`, `L2InteropRootStorage.sol:27-31`).
* `imported d sl k` holds when destination `d`'s `interopRoots(sl, k)` is nonzero.
* `l1 d` is destination `d`'s `AtomicFlowManager.L1_CHAIN_ID`. -/
structure World where
  slRoot : Chain → ℕ → Contracts.Timeout.SlRoot
  imported : Dest → Chain → ℕ → Prop
  l1 : Dest → Chain

/-- **IMPORTS ONLY ACCUMULATE.**  `W'` is a later snapshot of `W`: the same settlement-layer
roots and configuration, and every root imported in `W` is still imported.  Roots are never
overwritten (`InteropRootAlreadyExists`) and never removed. -/
def ImportsGrow (W W' : World) : Prop :=
  W'.slRoot = W.slRoot ∧ W'.l1 = W.l1 ∧ ∀ d sl k, W.imported d sl k → W'.imported d sl k

/-! ## Settlement proofs -/

/-- The settlement part of an `ImtProof` (`settlementProof`), as far as `_authenticateRoot`
reads it.  The Merkle paths inside it are not modelled (see the header). -/
structure SettlementProof where
  /-- `ProofMetadata.finalProofNode`: a single-level proof with no settlement-layer batch
  reference. -/
  finalProofNode : Bool
  /-- `pd.settlementLayerChainId`. -/
  slChainId : Chain
  /-- `pd.settlementLayerBatchNumber`: the settlement-layer block whose imported root the
  proof terminates at. -/
  slBlock : ℕ

/-- **`_authenticateRoot` PASSES ON DESTINATION `d`** for chain `c`'s batch `n`.  The proof
is not a final node (`ProofMissingSettlementLayerBatch`).  It terminates at
`interopRoots[slChainId][slBlock]`, which `d` has imported (else
`proveL2LeafInclusionShared` returns false).  And that root aggregates the batch, so the
honest path recomputes it. -/
def SettlementAccepted (W : World) (d : Dest) (c : Chain) (n : ℕ) (sp : SettlementProof) :
    Prop :=
  sp.finalProofNode = false ∧ W.imported d sp.slChainId sp.slBlock
    ∧ n ≤ (W.slRoot sp.slChainId sp.slBlock).upTo c

/-- **`AtomicInteropProof.verifyInclusion` ON DESTINATION `d`**, for a flow settling on
`sl`, without the deadline comparison (which `LegFinalizedAtBy` adds).
`_authenticateRoot` passes, the proof's settlement layer is the flow's
(`ProofSettlementLayerMismatch`), and the IMT inclusion proof is accepted against the root
it authenticated, which is chain `c`'s batch-`n` END root. -/
def AcceptsAt (h : Hash) (z0 : UInt256) (hl : LeafHash) (W : World) (S : System) (d : Dest)
    (sl c : Chain) (n : ℕ) (v : UInt256) (p : ImtProof) (sp : SettlementProof) : Prop :=
  SettlementAccepted W d c n sp ∧ sp.slChainId = sl ∧ Accepts h z0 hl S c n v p

/-! ## The gate on a destination -/

/-- The evidence a destination's gate consumes, per leg: the batch, the IMT proof and the
settlement proof (one `ImtProof` struct of `_finality.proofs`). -/
abbrev GateEvidenceAt := FlowLeg → ℕ × ImtProof × SettlementProof

/-- The IMT half of destination evidence: what the destination-agnostic
`Contracts.Atomicity.ExecutedViaBy` consumes. -/
def imtEvidence (ev : GateEvidenceAt) : GateEvidence := fun l => ((ev l).1, (ev l).2.1)

/-- One leg verified on destination `d`, with its batch `n`, IMT proof `p` and settlement
proof `sp` named: the batch is on time (`ProofDeadlineExceeded`) and `verifyInclusion`
passes on `d`. -/
def LegFinalizedAtBy (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (W : World)
    (S : System) (d : Dest) (sl : Chain) (F : Flow) (leg : FlowLeg) (n : ℕ) (p : ImtProof)
    (sp : SettlementProof) : Prop :=
  S.time leg.chain n ≤ F.deadline ∧ AcceptsAt h z0 hl W S d sl leg.chain n (legValue cv F leg) p sp

/-- `LegFinalizedAtBy` for some batch and proofs: the evidence exists. -/
def LegFinalizedAt (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (W : World)
    (S : System) (d : Dest) (sl : Chain) (F : Flow) (leg : FlowLeg) : Prop :=
  ∃ (n : ℕ) (p : ImtProof) (sp : SettlementProof), LegFinalizedAtBy h z0 hl cv W S d sl F leg n p sp

/-- **`requireFlowFinalized` AS DESTINATION `d` RUNS IT**, for a flow settling on `sl`, on
the evidence `ev`.  `_checkSettlementLayerIsL1` is checked against `d`'s own
`L1_CHAIN_ID`, and every leg is verified against `d`'s imported roots. -/
def FlowFinalizedAtBy (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (W : World)
    (S : System) (d : Dest) (sl : Chain) (F : Flow) (ev : GateEvidenceAt) : Prop :=
  W.l1 d = sl ∧ ∀ leg ∈ F.legs, LegFinalizedAtBy h z0 hl cv W S d sl F leg (ev leg).1 (ev leg).2.1 (ev leg).2.2

/-- **A LEG EXECUTED ON DESTINATION `d`**, on the evidence `ev`.  As
`Contracts.Atomicity.ExecutedViaBy` (`_checkFlowId`, `ManagerExecutingBundleNotInFlow`, every
leg verified), with every leg verified the way `d` verifies it. -/
def ExecutedAtBy (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (W : World) (S : System) (d : Dest) (sl : Chain) (F : Flow) (ev : GateEvidenceAt)
    (leg : FlowLeg) : Prop :=
  leg ∈ F.legs ∧ FlowIdChecked fh F ∧ FlowFinalizedAtBy h z0 hl cv W S d sl F ev

/-- `ExecutedAtBy` on some evidence. -/
def ExecutedAt (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (W : World) (S : System) (d : Dest) (sl : Chain) (F : Flow) (leg : FlowLeg) : Prop :=
  ∃ ev : GateEvidenceAt, ExecutedAtBy h z0 hl cv fh W S d sl F ev leg

/-! ## Availability on a destination -/

/-- What a prover can present as the settlement part of a proof for chain `c`'s batch `n`.
Like `Contracts.Atomicity.Access`, this is a property of the world: the multi-hop proof is
built from the settlement layer's published aggregation data. -/
abbrev SettlementAccess := Chain → ℕ → SettlementProof → Prop

/-- The multi-hop proof the settlement layer's data yields for a batch inside the root of
settlement layer `sl` at block `k`.  It is not a final node and it terminates at
`interopRoots[sl][k]`. -/
def honestSettlementProof (sl : Chain) (k : ℕ) : SettlementProof := ⟨false, sl, k⟩

/-- **THE SETTLEMENT-PROOF AVAILABILITY ASSUMPTION.**  For every settlement-layer root and
every batch it aggregates, the honest multi-hop proof is presentable.  Like
`DataAvailable`, nothing in the protocol makes it true. -/
def SettlementDataAvailable (W : World) (SA : SettlementAccess) : Prop :=
  ∀ (c : Chain) (n : ℕ) (sl : Chain) (k : ℕ), n ≤ (W.slRoot sl k).upTo c →
    SA c n (honestSettlementProof sl k)

/-- Settlement access that is exactly the honest multi-hop proofs.  It meets
`SettlementDataAvailable` by construction. -/
def honestSettlementAccess (W : World) : SettlementAccess :=
  fun c n sp => ∃ (sl : Chain) (k : ℕ), n ≤ (W.slRoot sl k).upTo c ∧ sp = honestSettlementProof sl k

/-- No settlement proof can be presented, for the countermodel. -/
def noSettlementAccess : SettlementAccess := fun _ _ _ => False

/-- Destination `d` holds an imported root of settlement layer `sl` that aggregates chain
`c`'s batch `n`. -/
def RootImported (W : World) (d : Dest) (sl c : Chain) (n : ℕ) : Prop :=
  ∃ k, W.imported d sl k ∧ n ≤ (W.slRoot sl k).upTo c

/-- **THE IMPORT-AVAILABILITY ASSUMPTION.**  Destination `d` has imported roots of settlement
layer `sl` that together cover every batch, of every chain, that settled by time `D`.

This is an assumption about the destination, stated in the style of `DataAvailable`.  An
import is a destination-local transition by the bootloader
(`L2InteropRootStorage.sol:58-76`), and no source chain's data availability supplies it.
`Contracts.RootImport.Properties.ImportAvailableOfPostDeadlineImport` shows that one imported
root created at or after `D` is enough, given the settlement layer's `Aggregates`.
`Contracts.RootImport.Properties.WithoutImportFlowSitsHalfExecuted` is the countermodel
without it. -/
def ImportAvailable (W : World) (S : System) (d : Dest) (sl : Chain) (D : ℕ) : Prop :=
  ∀ (c : Chain) (n : ℕ), S.time c n ≤ D → RootImported W d sl c n

/-- **THE LEG CAN BE FINALIZED ON DESTINATION `d`.**  There is an on-time batch, an IMT proof
and a settlement proof a prover can present for it, and `d`'s `verifyInclusion` accepts
them.  `Contracts.Atomicity.LegFinalizableBy` is the IMT half of this
(`Contracts.RootImport.Properties.FinalizableAtImpliesBy`). -/
def LegFinalizableAt (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (W : World)
    (S : System) (A : Access) (SA : SettlementAccess) (d : Dest) (sl : Chain) (F : Flow)
    (leg : FlowLeg) : Prop :=
  ∃ (n : ℕ) (p : ImtProof) (sp : SettlementProof),
    S.time leg.chain n ≤ F.deadline ∧ A leg.chain n p ∧ SA leg.chain n sp
      ∧ AcceptsAt h z0 hl W S d sl leg.chain n (legValue cv F leg) p sp

/-- **THE WHOLE FLOW CAN BE FINALIZED ON DESTINATION `d`.**  `d` can run
`requireFlowFinalized` on presentable proofs and pass: its `L1_CHAIN_ID` is the flow's
settlement layer and every leg is finalizable on `d`. -/
def FlowFinalizableAt (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (W : World)
    (S : System) (A : Access) (SA : SettlementAccess) (d : Dest) (sl : Chain) (F : Flow) : Prop :=
  W.l1 d = sl ∧ ∀ leg ∈ F.legs, LegFinalizableAt h z0 hl cv W S A SA d sl F leg

/-- **THE FIRST LEG STRANDED ON DESTINATION `d`.**  `leg` is the first leg of `F`, in list
order, that is not finalizable on `d`. -/
def FirstStrandedLegAt (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (W : World)
    (S : System) (A : Access) (SA : SettlementAccess) (d : Dest) (sl : Chain) (F : Flow)
    (leg : FlowLeg) : Prop :=
  ∃ pre post : List FlowLeg, F.legs = pre ++ leg :: post
    ∧ (∀ l ∈ pre, LegFinalizableAt h z0 hl cv W S A SA d sl F l)
    ∧ ¬ LegFinalizableAt h z0 hl cv W S A SA d sl F leg

/-- **A GATE BREAK PINNED TO THE FIRST LEG STRANDED ON `d`.**  The inclusion proof `ev`
submitted for that leg, at the batch submitted for it, carries a located break. -/
def PinnedGateBreakAt (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (W : World)
    (S : System) (A : Access) (SA : SettlementAccess) (d : Dest) (sl : Chain) (F : Flow)
    (ev : GateEvidence) : Prop :=
  ∃ leg, FirstStrandedLegAt h z0 hl cv W S A SA d sl F leg
    ∧ InclusionBreak h z0 hl S leg.chain (ev leg).1 (ev leg).2

/-! ## Concrete configurations, for the countermodels and witnesses -/

/-- Both legs committed: chain `0` commits `a` and chain `1` commits `b`, each during batch
0, and every other chain stays at `setup`.  Batch numbers are timestamps, so with deadline
`0` batch 0 is on time.  The same system as the `FlowBinding` proofs' `pairSystem`. -/
def twoChainSystem (a b : UInt256) : System where
  tree := fun c _ => if c = 0 then insert setup a 0 else if c = 1 then insert setup b 0 else setup
  time := fun _ n => n
  height := fun c _ => if c = 0 ∨ c = 1 then 1 else 0

/-- The destination side of the witnesses.  Every key holds `Contracts.Timeout.timeOneRoot`,
created at time 1 and holding every chain's batches `0, 1`.  The destinations satisfying
`imp` have imported settlement layer `sl`'s root at block `0`, and no destination has
imported anything else.  Every destination's `L1_CHAIN_ID` is `sl`. -/
def importWorld (sl : Chain) (imp : Dest → Prop) : World where
  slRoot := fun _ _ => Contracts.Timeout.timeOneRoot
  imported := fun d c k => imp d ∧ c = sl ∧ k = 0
  l1 := fun _ => sl

end Contracts.RootImport
