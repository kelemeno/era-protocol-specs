import EraSpec.Protocol.InteropAtomicity.Specs.FlowBinding
import EraSpec.Protocol.InteropAtomicity.Specs.OncePerLeg

/-!
# Model at `draft/v0.35.0`: the receive filter `_checkLegSourceAllowed`

Source: matter-labs/era-contracts, branch `draft/v0.35.0` at `d9f678900` (the filter came in
with #2628, commit `2d08bdaba`).  Paths are relative to `l1-contracts/contracts/` unless they
start with `protocol-docs/`.  `main` at `3605e82` does not have this check; every other model in
this folder describes the pinned tree `c67894b9`.

**This file is definitions only.**  Statements are in
`EraSpec.Protocol.InteropAtomicity.Properties.LegSourceFilterAtV35`, proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.LegSourceFilterAtV35`.

## What changed

v35 adds one internal view function to the flow manager
(`atomic-interop/AtomicFlowManager.sol:335-344`):

    function _checkLegSourceAllowed(uint256 _legSourceChainId) internal view {
        if (
            _legSourceChainId != block.chainid
                && !IL2Bridgehub(address(L2_BRIDGEHUB)).isPeerAllowed(_legSourceChainId)
        ) {
            revert ManagerLegSourceChainNotAllowed(_legSourceChainId);
        }
    }

and calls it in the two entry points that accept cross-chain evidence:

* `requireFlowFinalized` (`AtomicFlowManager.sol:176-213`) calls it for EVERY leg, inside the
  loop that checks each leg's inclusion proof (`:201`).  It runs on the chain that executes the
  bundle: the handler first requires `bundle.destinationChainId == block.chainid`
  (`interop/interop-handler/InteropHandlerBase.sol:400-403`).
* `authorizeRefund` (`AtomicFlowManager.sol:216-247`) calls it for the MISSING leg only, the
  leg whose absence the timeout proof shows (`:231`).  It runs on whichever chain is asked to
  mark its own committed legs of the flow `Revertable` (`:238-246`).

`isPeerAllowed` is mutable storage of each chain's `L2Bridgehub`
(`core/bridgehub/L2Bridgehub.sol:42-43`).  `allowInteropPeer` sets it (`:94-99`) and
`deregisterChainForInterop` deletes it (`:101-105`).  Both are `onlyChainRegistrationSender`
(`:45-53`): they are service transactions sent by L1's `ChainRegistrationSender`, from
`allowInteropPeer` (chain admin only, `core/chain-registration/ChainRegistrationSender.sol:77-93`)
and `deregisterInteropPairs` (owner or chain admin, `:98-117`).

`append` does not apply the filter.  It requires every other leg's source chain to be
*registered* on this chain, `baseTokenAssetId != 0` (`AtomicFlowManager.sol:149-160`).
`deregisterChainForInterop` deletes that entry too, but legacy registrations and
settlement-layer migrations set it without `isPeerAllowed`
(`protocol-docs/interop-gating.md:162-177`, `core/bridgehub/BridgehubBase.sol:447`).

The handler runs the gate once per bundle.  `verifyAtomicBundle` runs `requireFlowFinalized`
and marks the bundle `Verified` (`interop/interop-handler/L2InteropHandler.sol:83-92`), and
`executeAtomicBundle` skips the gate for a `Verified` bundle (`:72-75`).  So the filter is read
when the gate runs: not at send time, and not when a bundle verified earlier is executed
(`protocol-docs/interop-gating.md:189-192`).

Upstream documents the liveness cost as a known limitation, "K1: stuck flows"
(`protocol-docs/interop-gating.md:250-260`, also `:155-158` and `:172-174`): a flow is stuck when
a chain's filter refuses one of its legs' sources, and whoever removes a pair answers for the
pair's unfinalized flows.  The stranding results here make K1 exact; they are not a new finding.

## What is modelled

* `Peers`: every chain's `isPeerAllowed` mapping.  `SourceAllowed P c s` is the filter run on
  chain `c` for source `s`.
* The two gates at v35: `ExecutedViaByAtV35` (the pin's `ExecutedViaBy` with the filter inside
  the per-leg loop, on the executing chain) and `LegRefundableByAtV35` (the pin's
  `LegRefundableBy` for the missing leg, with the filter on the refunding chain).
* `RunAtV35`: `Contracts.FlowBinding.RunLog` (append, gate, authorize and claim on one manager
  per chain) with the allow-lists in the state, the filter on the gate and authorize steps, and
  two admin steps `allowPeer` / `deregisterPeer` that may fire at any time.  The gate runs on
  the destination `dst b` of the bundle with hash `b`.  Every call that checks a flow id is
  logged with the allow-lists it was checked against; the admin steps are logged too.
* `SysStepsAtV35`: `Contracts.AppendPath.SysSteps` (every chain's manager and tree) with the
  allow-lists and the filter on `authorize`, for the once-per-leg results.

## What is not modelled

* The rest of the v35 diff.  The tree, the inclusion and timeout checks and the manager's state
  machine are the pin's models (`c67894b9`), with the filter added: this file isolates the
  filter.  At v35 the tree pads with `IMT_EMPTY_LEAF_HASH` instead of `hashLeaf({0,0,0})`
  (`common/libraries/IndexedMerkleTree.sol:44-52`, from `78e14b3bc`), the leg lists sit in
  `flow.preimage`, `_missingLegIndex` is bounds-checked (`AtomicFlowManager.sol:224-226`), and
  `AtomicInteropProof` reads the settlement-layer reference through a different helper.  The
  results quantify over the node hash, the padding constant `z0` and the leaf hash, so they
  cover v35's padding.  The two that fix a hash say so: the toy leaf hash in
  `Properties.ForgedSiblingExecutionNeedsAllowedForgerAtV35`, and the PIN's padding constant in
  `Properties.ForeignForgedRefundNeedsAllowedForgerAtV35`, whose forgery v35's padding removes.
* Who may send the admin steps (L1's `ChainRegistrationSender` checks, `InteropNotEnabled`,
  `InvalidInteropPeer`, `InteropPeerAlreadyAllowed`), the L1 mapping `interopPeerAllowed`, the
  service-transaction delay, and service transactions that fail on L2.  `allowPeer` and
  `deregisterPeer` are allowed for every pair at every moment, so the model has more runs than
  the contracts.
* `baseTokenAssetId`, and with it `append`'s registration check and the send-side check
  `isPeerAllowed(destination)` (`interop/InteropCenter.sol:694-704`).  Both only reject.
  `append` is the pin's manager guard (`RunAtV35`) or the pin's guard plus tree insert
  (`SysStepsAtV35`); v35's other new `append` checks (flow preimage, own source chain, expired
  flow, `AtomicFlowManager.sol:104-160`) are omitted as well.
* The handler's `Verified` status.  A `gate` step is one `requireFlowFinalized` that passed, from
  either handler entry point.  That a verified bundle later executes without a second gate is
  why a gate step stands for "this leg may execute from now on".
* As in `Contracts.FlowBinding`: pause, the settlement-layer check, the replay guard, deadlines
  of the handler, events.  The tree side is the fixed history `S`, the same for every chain that
  checks a proof: which settlement-layer roots a chain has imported is not modelled.  One
  `authorizeRefund` call marks every leg of the flow that is `Committed` in the manager it runs
  on (`AtomicFlowManager.sol:236-246`); a step here marks one, so a call is a sequence of steps
  under one allow-list.
-/

namespace Contracts.LegSourceFilterAtV35

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund Contracts.FlowBinding Contracts.AppendPath

/-! ## The allow-lists -/

/-- Every chain's `L2Bridgehub.isPeerAllowed` mapping (`core/bridgehub/L2Bridgehub.sol:42-43`):
`P c s` is chain `c`'s entry for peer chain `s`. -/
abbrev Peers := Chain → Chain → Bool

/-- **`_checkLegSourceAllowed(s)` PASSES ON CHAIN `c`** (`AtomicFlowManager.sol:338-344`): `s` is
`block.chainid`, or `c`'s bridgehub allows `s`. -/
def SourceAllowed (P : Peers) (c s : Chain) : Prop := s = c ∨ P c s = true

instance (P : Peers) (c s : Chain) : Decidable (SourceAllowed P c s) := by
  unfold SourceAllowed; infer_instance

/-- `L2Bridgehub.allowInteropPeer(s, _)` run on chain `c` (`L2Bridgehub.sol:94-99`):
`isPeerAllowed[s] = true`. -/
def Peers.allow (P : Peers) (c s : Chain) : Peers :=
  fun c' s' => if c' = c ∧ s' = s then true else P c' s'

/-- `L2Bridgehub.deregisterChainForInterop(s)` run on chain `c` (`L2Bridgehub.sol:101-105`):
`delete isPeerAllowed[s]`. -/
def Peers.deregister (P : Peers) (c s : Chain) : Peers :=
  fun c' s' => if c' = c ∧ s' = s then false else P c' s'

/-- Every chain allows every peer.  Under these allow-lists the filter passes everywhere, which
is the pin's behaviour. -/
def allPeersAllowed : Peers := fun _ _ => true

/-! ## The two gates at v35 -/

/-- One iteration of `requireFlowFinalized`'s loop at v35 (`AtomicFlowManager.sol:194-209`), run
on chain `d`: the leg's source passes the filter (`:201`), and the inclusion proof `p` submitted
for the leg verifies against an on-time batch `n` of the leg's declared source chain
(`:198-208`; the pin's `LegFinalizedBy`). -/
def LegFinalizedByAtV35 (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (S : System) (P : Peers) (d : Chain) (F : Flow) (leg : FlowLeg) (n : ℕ) (p : ImtProof) :
    Prop :=
  SourceAllowed P d leg.chain ∧ LegFinalizedBy h z0 hl cv S F leg n p

/-- The whole loop, on chain `d`, with each leg's evidence taken from `ev`. -/
def FlowFinalizedByAtV35 (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (S : System) (P : Peers) (d : Chain) (F : Flow) (ev : GateEvidence) : Prop :=
  ∀ leg ∈ F.legs, LegFinalizedByAtV35 h z0 hl cv S P d F leg (ev leg).1 (ev leg).2

/-- **`requireFlowFinalized` PASSES ON CHAIN `d` AT v35** (`AtomicFlowManager.sol:176-213`) for the
executing leg `leg`: `_checkFlowId` (`:182`), the loop over every leg, and `leg` is a leg of the
flow (`:210-212`).  The pin's `ExecutedViaBy` with the filter in the loop. -/
def ExecutedViaByAtV35 (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) (P : Peers) (d : Chain) (F : Flow) (ev : GateEvidence)
    (leg : FlowLeg) : Prop :=
  leg ∈ F.legs ∧ FlowIdChecked fh F ∧ FlowFinalizedByAtV35 h z0 hl cv S P d F ev

/-- **`authorizeRefund`'S TIMEOUT CHECK PASSES ON CHAIN `c` AT v35** for the missing leg `m`, on
the absence proof `q` at batch `N` (`AtomicFlowManager.sol:224-234`): the filter on `m`'s source
(`:231`), and the pin's timeout gate (`:227-230` binds the proof to `m`'s declared source chain,
`:233-234` verifies it; the pin's `LegRefundableBy`). -/
def LegRefundableByAtV35 (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (S : System) (P : Peers) (c : Chain) (F : Flow) (m : FlowLeg) (N : ℕ) (q : ImtProof) : Prop :=
  SourceAllowed P c m.chain ∧ LegRefundableBy h z0 hl cv S F m N q

/-! ## Calls and runs -/

/-- The destination chain of the bundle with hash `b`, its `destinationChainId`.  The handler
runs the gate only there (`InteropHandlerBase.sol:400-403`).  It is a function of the hash
because, as elsewhere in this package, a bundle is identified with its hash. -/
abbrev Dest := UInt256 → Chain

/-- The checks a logged `requireFlowFinalized` call `e` passed at v35: the gate, run on the
executing bundle's destination `dst e.leg.bundleHash`, under the allow-lists `P` of that
moment. -/
def GateCallPassesAtV35 (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) (dst : Dest) (P : Peers) (e : ExecCall) : Prop :=
  ExecutedViaByAtV35 h z0 hl cv fh S P (dst e.leg.bundleHash) e.flow e.evidence e.leg

/-- The checks a logged `authorizeRefund` call `a` passed at v35: the pin's checks
(`AuthCall.Verified`: `_checkFlowId`, both legs in the flow, the timeout gate) and the filter on
the missing leg's source, run on the chain whose leg `a.leg` it marks. -/
def AuthorizeCallPassesAtV35 (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) (P : Peers) (a : AuthCall) : Prop :=
  a.Verified h z0 hl cv fh S ∧ SourceAllowed P a.leg.chain a.missing.chain

/-- One logged call of a v35 run. -/
inductive CallAtV35 where
  /-- `requireFlowFinalized` passed for `e`, under the allow-lists `P` of the moment
  (`L2InteropHandler.sol:72-75` or `:88-89`). -/
  | gate (e : ExecCall) (P : Peers)
  /-- `authorizeRefund` passed for `a`, under the allow-lists `P` of the moment. -/
  | authorize (a : AuthCall) (P : Peers)
  /-- `L2Bridgehub.allowInteropPeer(s, _)` on chain `c`. -/
  | allowPeer (c s : Chain)
  /-- `L2Bridgehub.deregisterChainForInterop(s)` on chain `c`. -/
  | deregisterPeer (c s : Chain)

/-- The state of a v35 run: one flow manager per chain and every chain's allow-list. -/
structure WorldAtV35 where
  mgrs : Managers
  peers : Peers

/-- **EVERY INTERLEAVING AT v35, LOGGED.**  `RunAtV35 … dst X Y log`: from `X` the system
reaches `Y`, and `log` lists the calls, most recent first.

`append`, `authorize` and `claim` are `Contracts.FlowBinding.RunLog`'s steps with the same
guards; `authorize` also runs the filter on the chain it marks.  `gate` is `requireFlowFinalized`
passing on the bundle's destination; it reads the allow-lists and writes nothing.  `allowPeer` and
`deregisterPeer` change one allow-list entry and are enabled for every pair at every moment. -/
inductive RunAtV35 (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (dst : Dest) : WorldAtV35 → WorldAtV35 → List CallAtV35 → Prop
  | refl {X} : RunAtV35 h z0 hl cv fh S dst X X []
  | append {X Y log c f b} : RunAtV35 h z0 hl cv fh S dst X Y log → AppendGuard (Y.mgrs c) f b →
      RunAtV35 h z0 hl cv fh S dst X ⟨setAt Y.mgrs c ((Y.mgrs c).set f b .Committed), Y.peers⟩ log
  | gate {X Y log} (e : ExecCall) : RunAtV35 h z0 hl cv fh S dst X Y log →
      GateCallPassesAtV35 h z0 hl cv fh S dst Y.peers e →
      RunAtV35 h z0 hl cv fh S dst X Y (.gate e Y.peers :: log)
  | authorize {X Y log} (a : AuthCall) : RunAtV35 h z0 hl cv fh S dst X Y log →
      AuthorizeCallPassesAtV35 h z0 hl cv fh S Y.peers a →
      AuthorizeGuard (Y.mgrs a.leg.chain) a.flow.flowId a.leg.bundleHash →
      RunAtV35 h z0 hl cv fh S dst X
        ⟨setAt Y.mgrs a.leg.chain
          ((Y.mgrs a.leg.chain).set a.flow.flowId a.leg.bundleHash .Revertable), Y.peers⟩
        (.authorize a Y.peers :: log)
  | claim {X Y log c f b} : RunAtV35 h z0 hl cv fh S dst X Y log → ClaimGuard (Y.mgrs c) f b →
      RunAtV35 h z0 hl cv fh S dst X ⟨setAt Y.mgrs c ((Y.mgrs c).set f b .Reverted), Y.peers⟩ log
  | allowPeer {X Y log} (c s : Chain) : RunAtV35 h z0 hl cv fh S dst X Y log →
      RunAtV35 h z0 hl cv fh S dst X ⟨Y.mgrs, Y.peers.allow c s⟩ (.allowPeer c s :: log)
  | deregisterPeer {X Y log} (c s : Chain) : RunAtV35 h z0 hl cv fh S dst X Y log →
      RunAtV35 h z0 hl cv fh S dst X ⟨Y.mgrs, Y.peers.deregister c s⟩ (.deregisterPeer c s :: log)

/-- The call as the pin's `RunLog` logs it, if it is one: a gate call is the pin's `execute`, an
`authorizeRefund` call is the pin's `authorize`, and the admin steps have no pin counterpart. -/
def CallAtV35.toPin : CallAtV35 → Option CheckedCall
  | .gate e _ => some (.execute e)
  | .authorize a _ => some (.authorize a)
  | .allowPeer _ _ => none
  | .deregisterPeer _ _ => none

/-- A v35 log as the pin logs it. -/
def pinLog (log : List CallAtV35) : List CheckedCall := log.filterMap CallAtV35.toPin

/-- The `authorizeRefund` call, when the call is one. -/
def CallAtV35.authCall? : CallAtV35 → Option AuthCall
  | .authorize a _ => some a
  | _ => none

/-- The `authorizeRefund` calls of a v35 log, most recent first: the log `RefundBreak` reads. -/
def authLogAtV35 (log : List CallAtV35) : List AuthCall := log.filterMap CallAtV35.authCall?

/-! ## Every chain's manager and tree at v35 -/

/-- The state of a system run at v35: every chain's manager and tree, and every allow-list. -/
structure SysWorldAtV35 where
  chains : Chains
  peers : Peers

/-- **`Contracts.AppendPath.SysSteps` AT v35.**  Every chain's composed `append` (manager guard and
tree insert), `authorizeRefund` with the pin's checks AND the filter, `claimRefund`, the tree's
`initL2`, and the two admin steps.  `log` lists the appended obligations and `alog` the
`authorizeRefund` calls, most recent first, as in `SysSteps`. -/
inductive SysStepsAtV35 (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) (X : SysWorldAtV35) :
    SysWorldAtV35 → List Obligation → List AuthCall → Prop
  | refl : SysStepsAtV35 h z0 hl cv fh S X X [] []
  | append {Y log alog c f b hint low} : SysStepsAtV35 h z0 hl cv fh S X Y log alog →
      AppendSucceeds cv (Y.chains c) f b hint low →
      SysStepsAtV35 h z0 hl cv fh S X
        ⟨Y.chains.update c ((Y.chains c).appended cv f b low), Y.peers⟩ (⟨f, b, c⟩ :: log) alog
  | authorize {Y log alog} (a : AuthCall) : SysStepsAtV35 h z0 hl cv fh S X Y log alog →
      AuthorizeCallPassesAtV35 h z0 hl cv fh S Y.peers a →
      AuthorizeGuard (Y.chains a.leg.chain).mgr a.flow.flowId a.leg.bundleHash →
      SysStepsAtV35 h z0 hl cv fh S X
        ⟨Y.chains.update a.leg.chain
          ⟨(Y.chains a.leg.chain).mgr.set a.flow.flowId a.leg.bundleHash .Revertable,
            (Y.chains a.leg.chain).tree⟩, Y.peers⟩
        log (a :: alog)
  | claim {Y log alog c f b} : SysStepsAtV35 h z0 hl cv fh S X Y log alog →
      ClaimGuard (Y.chains c).mgr f b →
      SysStepsAtV35 h z0 hl cv fh S X
        ⟨Y.chains.update c ⟨(Y.chains c).mgr.set f b .Reverted, (Y.chains c).tree⟩, Y.peers⟩
        log alog
  | initL2 {Y log alog c} : SysStepsAtV35 h z0 hl cv fh S X Y log alog →
      (Y.chains c).tree.leafCount = 0 →
      SysStepsAtV35 h z0 hl cv fh S X
        ⟨Y.chains.update c ⟨(Y.chains c).mgr, reseed (Y.chains c).tree⟩, Y.peers⟩ log alog
  | allowPeer {Y log alog} (c s : Chain) : SysStepsAtV35 h z0 hl cv fh S X Y log alog →
      SysStepsAtV35 h z0 hl cv fh S X ⟨Y.chains, Y.peers.allow c s⟩ log alog
  | deregisterPeer {Y log alog} (c s : Chain) : SysStepsAtV35 h z0 hl cv fh S X Y log alog →
      SysStepsAtV35 h z0 hl cv fh S X ⟨Y.chains, Y.peers.deregister c s⟩ log alog

/-! ## Stranding -/

/-- Leg `leg` of `F` was committed on time: its commit value is a key of its declared source
chain's tree at a batch that settled by the deadline. -/
def CommittedOnTime (cv : CommitValue) (S : System) (F : Flow) (leg : FlowLeg) : Prop :=
  ∃ n, S.time leg.chain n ≤ F.deadline ∧ legValue cv F leg ∈ keys (toAbs (S.tree leg.chain n))

/-- The leg's source chain settled some batch after the deadline.  Settlement progress
(`OPS-PROGRESS`); the BEGIN branch of the timeout proof needs it. -/
def SettledAfterDeadline (S : System) (F : Flow) (leg : FlowLeg) : Prop :=
  ∃ N, F.deadline < S.time leg.chain N

/-- **A STRANDED LEG, UP TO LOCATED BREAKS.**  Under the allow-lists `P`:

* no evidence passes `requireFlowFinalized` for `leg` on its destination `d`, unless the
  evidence carries a located `TreeRootBreak` on one of the flow's own legs (`GateBreak`);
* on the leg's own source chain `leg.chain`, the chain whose manager holds it, no absence proof
  for any leg `m` of the flow passes `authorizeRefund`'s timeout check, unless that proof carries
  a located break (`AbsenceBreak`).

So the leg can neither execute nor be refunded, except through a forged proof that the theorems
name. -/
def StrandedOrBreakAtV35 (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) (P : Peers) (d : Chain) (F : Flow) (leg : FlowLeg) : Prop :=
  (∀ ev : GateEvidence,
      ¬ ExecutedViaByAtV35 h z0 hl cv fh S P d F ev leg ∨ GateBreak h z0 hl S F ev)
    ∧ ∀ m ∈ F.legs, ∀ (N : ℕ) (q : ImtProof),
        ¬ LegRefundableByAtV35 h z0 hl cv S P leg.chain F m N q
          ∨ AbsenceBreak h z0 hl S F.deadline m.chain N q

/-- **THE GATE CAN BE PASSED ON PRESENTABLE EVIDENCE**: some evidence a prover can present (`A`)
passes `requireFlowFinalized` for `leg` on chain `d` at v35.  The v35 counterpart of the pin's
`FlowFinalizableBy`, which has no destination. -/
def GateOpenAtV35 (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (A : Access) (P : Peers) (d : Chain) (F : Flow) (leg : FlowLeg) : Prop :=
  ∃ ev : GateEvidence, (∀ l ∈ F.legs, A l.chain (ev l).1 (ev l).2)
    ∧ ExecutedViaByAtV35 h z0 hl cv fh S P d F ev leg

/-! ## The witness worlds: a swap between chains `0` and `1`

Both countermodels are a two-leg swap: leg `⟨0, 1⟩` (bundle `1`) is sent from chain `0` to chain
`1`, and leg `⟨1, 2⟩` (bundle `2`) from chain `1` to chain `0`.  The commit value is
`cv _ b = b`, the deadline `0`, and batch numbers are timestamps, so batch 0 is on time and every
later batch is late.  In the complete swap (`swapSystem`) both legs commit in batch 0; in the
incomplete one (`Contracts.Atomicity.mixedSystem 1`) chain `1` never commits. -/

/-- The swap's destinations: bundle `1` goes to chain `1`, every other bundle to chain `0`. -/
def swapDest : Dest := fun b => if b = 1 then 1 else 0

/-- The complete swap: chain `0` commits `1` and chain `1` commits `2`, both in batch 0; every
other chain stays at `setup`.  (The same system as `Contracts.FlowBinding.pairSystem 1 2`.) -/
def swapSystem : System where
  tree := fun c _ => if c = 0 then insert setup 1 0 else if c = 1 then insert setup 2 0 else setup
  time := fun _ n => n
  height := fun c _ => if c = 0 ∨ c = 1 then 1 else 0

/-- Chain `0` holds the contract run `setup; insert a; insert b` (`threeLeafTree a b`, height 2,
one padding slot) and chain `1` holds `insert setup y`, from batch 0 on; every other chain stays at
`setup`.  Batch numbers are timestamps.  Used to show the refund filter keeps a forged absence
proof from a chain the refunding chain does not allow from authorizing a refund. -/
def foreignPaddedSystem (a b y : UInt256) : System where
  tree := fun c _ => if c = 0 then threeLeafTree a b else if c = 1 then insert setup y 0 else setup
  time := fun _ n => n
  height := fun c _ => if c = 0 then 2 else if c = 1 then 1 else 0

/-- A two-leg flow with id `0` and deadline `0`: leg `⟨0, a⟩` from chain `0`, leg `⟨1, y⟩` from
chain `1`.  With commit value `cv _ b = b` its legs' values are `a` and `y`. -/
def foreignFlow (a y : UInt256) : Flow := ⟨0, [⟨0, a⟩, ⟨1, y⟩], 0⟩

end Contracts.LegSourceFilterAtV35
