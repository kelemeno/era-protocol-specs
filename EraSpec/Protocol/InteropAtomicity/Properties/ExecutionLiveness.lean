import EraSpec.Protocol.InteropAtomicity.Specs.ExecutionLiveness

/-!
# Properties: what an atomic leg can still do on its destination

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.ExecutionLiveness`; proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.ExecutionLiveness`. The destination is
`Contracts.InteropHandler` (topic `Reentrancy`): (d), (e) and (h) hold for every re-entrant
behaviour of every target and every budget. (f) is on the gate model of topic
`SelfCallAuthorityFaithful`. Everything here is about the pin `c67894b9`; the Specs header ("At the
later trees") lists what differs at `e561b9cc2` and at the current heads.

## (d) Outside `Verified`, the public routes revert

Topic `BundleStatusMachineStrong` shows that along a run in which no call presents a valid inclusion
proof for a hash, the hash stays `Unreceived` or `FullyExecuted`
(`NoProofKeepsBundleInAtomicMachine`), and that an atomic dispatch's bundle hash stays so along any
destination run whose valid proofs are all for published messages, unless one of two named clashes
(`AtomicLegStaysAtomicAtDestinationOrClash`). Topic `BundleStatusMachineFaithful` shows that under
the same no-proof condition a committed effect of the hash needs a call that passed the flow gate
(`NeverPublishedBundleNeedsTheFlowGate`). This file adds the per-call form: in those two states,
without a valid proof, `executeBundle`, `verifyBundle` and `unbundleBundle` revert
(`PublicRoutesRevertOutsideVerified`).

## (e) A call that always reverts

* From a state where `h` is `Unreceived`, along a run with no valid proof for `h` in which every
  atomic attempt on `h`, at every depth, has a target that always reverts: `h` stays `Unreceived`
  and no effect of `h` is committed (`AtomicLegWithRevertingCallNeverExecutes`). The attempts may
  pass the flow gate; `BundleStatusMachineFaithful`'s `DeliveryNeedsInclusionOrFlowGate` is the
  case in which none does. For an atomic dispatch of a source run, the same holds under the
  source's publication premises, or one of the two named clashes
  (`AtomicLegWithRevertingCallNeverExecutesOrClash`).
* Headline (`FinalizedRevertingLegNeitherDeliveredNorRefunded`): for a leg of a flow that passed
  the gate for some leg, that destination result from fresh storage together with
  `Contracts.Refund`'s `OneExecutionFreezesTheFlowOrBreak` for the same leg: none of its calls is
  delivered on the destination, and in every logged run of the source managers its obligation is
  not refunded, or a located `RefundBreak`. The two halves are separate models, linked by the leg's
  bundle hash.
* A bundle that can be verified is different: whole-bundle execution reverts on such a target
  too, but after `verifyBundle`, `unbundleBundle` cancelling that call delivers every other call
  (`PublicBundleEscapesViaUnbundle`).

## (f) Who may execute an atomic leg

On `SelfCallAuthorityFaithful`'s gate model (Specs, "Permissions"), not composed with `exec`: a call
into `executeAtomicBundle` for a bundle whose `executionAddress` names `(ch, a)` passes the gate only
as a direct call from `a`, and only if `ch` is this chain or `0` (`ExecutorGatedLegNeedsExecutor`).
With any other `ch`, no call passes it, while `receiveMessage` relays `executeBundle` on the same
attributes for a message from `(ch, a)`, past that entry point's gate
(`ForeignChainExecutorHasNoAtomicRoute`).

## (h) The two routes are enabled

* `unbundleBundle` with a valid request on a `Verified` or `Unbundled` bundle, targets accepting and
  budget `calls + 2`, succeeds, records exactly the request and delivers exactly the requested
  calls (`UnbundleEnabled`). Topic `Reentrancy` shows this only on witnesses.
* Along every run from fresh storage with no valid proof for a bundle's hash, the bundle is
  `FullyExecuted`, or it is `Unreceived` and `executeAtomicBundle` with the gate passing, targets
  accepting and budget `calls + 2` runs it (`AtomicRouteStaysEnabled`).

## Non-vacuity

`RevertingLegWitness` meets every premise of the headline (e), on a two-leg flow, for every hash
family, with the gate passing and an attempt whose nested public execution, made before its
reverting target, is undone with it; its destination run also meets the premises of
`AtomicLegWithRevertingCallNeverExecutes` from fresh storage, which meets those of
`PublicRoutesRevertOutsideVerified`.
`RevertingLegFromSourceWitness` meets every premise of
`AtomicLegWithRevertingCallNeverExecutesOrClash` on the `InteropCenter` witness run, with a valid
proof in the destination run and both clashes false. `EscapeWitness` instantiates
`PublicBundleEscapesViaUnbundle` on a two-call bundle. `EnablednessWitness` meets the premises of
both results of (h), `AtomicRouteBothBranchesWitness` shows both branches of
`AtomicRouteStaysEnabled` on one run (`Unreceived` after a reverted attempt, then
`FullyExecuted`), and `ExecutorGateWitness` those of both results of (f), with one call passing
the gate and one failing it.
-/

namespace Contracts.ExecutionLiveness

open Contracts.InteropHandler (State Entry Callee Frame Tx Bundle BundleHash Effect exec submit
  submitAll toExecute NoProofRun SoundProofRun PublishedHash PublishesOnlyPublicDispatches)
open AttackVectors.BundleStatusMachine (Status CallStatus)
open AttackVectors.BundleHashEncoding (abiEncode HashCollision)
open MerkleSpec (Hash)
open Contracts.InteropCommitmentTree (LeafHash)
open Contracts.Atomicity (CommitValue FlowHash System Wf Flow FlowLeg GateEvidence ExecutedViaBy)
open Contracts.Refund (Managers AuthCall ReachLog emptyManagers Refunded RefundBreak obligationOf)
open AttackVectors.SelfCallAuthority.Faithful (GateCall GateAttrs Reaches pinnedTable InnerGate
  dispatch)

/-! ## (d) Outside `Verified`, the public routes revert -/

/-- **OUTSIDE `Verified` AND `Unbundled`, THE OTHER ROUTES REVERT WITHOUT A PROOF.** From a state
where the bundle is `Unreceived` or `FullyExecuted` (fresh storage is such a state for every
bundle), with no valid inclusion proof, `executeBundle` (`InteropHandlerBase.sol:117-123`) and
`verifyBundle` (`:157-160`) revert, and so does every `unbundleBundle` (`:195`), whatever the
targets and the budget. -/
def Properties.PublicRoutesRevertOutsideVerified : Prop :=
  ∀ (s : State) (b : Bundle), (s.bundle b.hash = .Unreceived ∨ s.bundle b.hash = .FullyExecuted) →
    ∀ (n : ℕ) (cs : List Callee),
      exec .deployed n (.entry (.executeBundle b false) cs) s = none ∧
      exec .deployed n (.entry (.verifyBundle b false) cs) s = none ∧
      ∀ req, exec .deployed n (.entry (.unbundleBundle b req) cs) s = none

/-! ## (e) A call that always reverts -/

/-- **AN ATOMIC LEG WHOSE EVERY ATTEMPT MEETS AN ALWAYS-REVERTING TARGET IS NEVER DELIVERED.** From
any state where `h` is `Unreceived`, along every sequence of transactions in which no call presents
a valid inclusion proof for `h` and every atomic attempt on `h`, at every depth, has a target that
reverts from every state: `h` is still `Unreceived` afterwards and no committed effect belongs to
`h`, so none of its calls was delivered. -/
def Properties.AtomicLegWithRevertingCallNeverExecutes : Prop :=
  ∀ (h : BundleHash) (s : State) (txs : List Tx), s.bundle h = .Unreceived →
    NoProofRun h txs → (∀ t ∈ txs, TxEvery (AtomicAttemptReverts h) t) →
      (submitAll .deployed s txs).1.bundle h = .Unreceived ∧
        ∀ e ∈ (submitAll .deployed s txs).2, e.bundleHash ≠ h

/-- **THE SAME FOR AN ATOMIC DISPATCH OF A SOURCE RUN, OR A NAMED CLASH.** Take a deployed
`InteropCenter` run `S` of chain `P` from fresh storage whose encoder separates its bundles
(`EncInjOn`, `SOL-ABI`), bundle messages `pubs` published to L1 of which chain `P`'s are the bytes
of its public dispatches, and an atomic dispatch `d` of `S`. At any destination state where `d`'s
bundle hash is `Unreceived`, along any sequence of transactions whose valid inclusion proofs are
all for published messages and in which every atomic attempt on that hash has a target that
always reverts: the hash is still `Unreceived` and no committed effect belongs to it; or a public
dispatch of `S` and `d` form a cross-sender salt clash; or keccak collides on `d`'s bundle-hash
preimage and a named published message's. -/
def Properties.AtomicLegWithRevertingCallNeverExecutesOrClash : Prop :=
  ∀ (P : Contracts.InteropCenter.Params) (S : Contracts.InteropCenter.State),
    Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed P
      Contracts.InteropCenter.init S →
    Contracts.InteropCenter.EncInjOn P.enc (S.log.map Contracts.InteropCenter.Dispatch.bundle) →
    ∀ (pubs : List (UInt256 × List UInt8)), PublishesOnlyPublicDispatches P S.log pubs →
    ∀ d ∈ S.log, d.isAtomic = true →
    ∀ (s : State) (txs : List Tx),
      s.bundle (Contracts.InteropCenter.bundleHash P d.bundle) = .Unreceived →
      SoundProofRun (PublishedHash P.keccak pubs) txs →
      (∀ t ∈ txs, TxEvery (AtomicAttemptReverts (Contracts.InteropCenter.bundleHash P d.bundle)) t) →
      ((submitAll .deployed s txs).1.bundle (Contracts.InteropCenter.bundleHash P d.bundle)
          = .Unreceived ∧
        ∀ e ∈ (submitAll .deployed s txs).2,
          e.bundleHash ≠ Contracts.InteropCenter.bundleHash P d.bundle)
      ∨ (∃ d' ∈ S.log, d'.isAtomic = false ∧ Contracts.InteropCenter.CrossSenderSaltClash P d d')
      ∨ (∃ p ∈ pubs, HashCollision P.keccak (Contracts.InteropCenter.bundlePreimage P d.bundle)
            (abiEncode p.1.val p.2))

/-- **HEADLINE (e): A LEG OF A FINALIZED FLOW WITH A CALL THAT ALWAYS REVERTS IS NEITHER DELIVERED
NOR REFUNDED, OR A LOCATED BREAK.** Take a well-formed history in which a flow `F` passed the
atomicity gate for some leg (`ExecutedViaBy`, so every leg of `F` has accepted gate evidence), and
a leg `other` of `F`. Along every destination run from fresh storage in which no call presents a
valid inclusion proof for `other`'s hash and every atomic attempt on it has a target that always
reverts, `other` stays `Unreceived` and none of its calls is delivered; and in every logged run of
the source managers its obligation is not refunded, or a call of the run's log that marked it
carries a located `RefundBreak`. The destination run and the source history are separate models,
linked by the leg's bundle hash; the second half is
`Contracts.Refund.Properties.OneExecutionFreezesTheFlowOrBreak` for `other`. Because the models
share no state and are not composed into one run, the statement does not require `other ≠ leg`: its destination half also holds
for the leg the history says executed, so it is a conjunction of two results, not one composed
run. -/
def Properties.FinalizedRevertingLegNeitherDeliveredNorRefunded : Prop :=
  ∀ (hh : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaBy hh z0 hl cv fh S F ev leg →
    ∀ other ∈ F.legs, ∀ txs : List Tx, NoProofRun other.bundleHash txs →
      (∀ t ∈ txs, TxEvery (AtomicAttemptReverts other.bundleHash) t) →
      ((submitAll .deployed Contracts.InteropHandler.init txs).1.bundle other.bundleHash
          = .Unreceived ∧
        ∀ e ∈ (submitAll .deployed Contracts.InteropHandler.init txs).2,
          e.bundleHash ≠ other.bundleHash) ∧
      ∀ (Ms : Managers) (log : List AuthCall),
        ReachLog hh z0 hl cv fh S emptyManagers Ms log →
          ¬ Refunded Ms (obligationOf F other) ∨
            RefundBreak hh z0 hl fh S F ev (obligationOf F other) log

/-- **A BUNDLE THAT CAN BE VERIFIED DELIVERS ITS OTHER CALLS THROUGH `unbundleBundle`.** For every
bundle `b` and every call `i` of it: `executeBundle` of `b` reverts whenever one of its first
`b.calls` targets always reverts, at every budget, from every state, with or without a valid proof,
as on the atomic route. But from fresh storage, `verifyBundle` with a valid proof and then
`unbundleBundle` cancelling call `i` and executing the others, with their targets accepting
(`escapeRun`), leave `b` `Unbundled`, call `i` `Cancelled` and every other call `Executed`, and
deliver exactly the other calls, in index order; call `i` is not among them. In the source the
second transaction must come from `b`'s unbundler (Specs, "The unbundler"). -/
def Properties.PublicBundleEscapesViaUnbundle : Prop :=
  ∀ (b : Bundle) (i : ℕ), i < b.calls →
    (∀ (n : ℕ) (ok : Bool) (cs : List Callee) (s : State),
      (∃ c ∈ cs.take b.calls, Contracts.InteropHandler.AlwaysReverts .deployed c) →
      exec .deployed n (.entry (.executeBundle b ok) cs) s = none) ∧
    (submitAll .deployed Contracts.InteropHandler.init (escapeRun b i)).1.bundle b.hash
      = .Unbundled ∧
    (submitAll .deployed Contracts.InteropHandler.init (escapeRun b i)).1.call b.hash i
      = .Cancelled ∧
    (∀ j < b.calls, j ≠ i →
      (submitAll .deployed Contracts.InteropHandler.init (escapeRun b i)).1.call b.hash j
        = .Executed) ∧
    (submitAll .deployed Contracts.InteropHandler.init (escapeRun b i)).2
      = ((List.range b.calls).filter (· ≠ i)).map (Effect.delivered b.hash)

/-! ## (f) Who may execute an atomic leg

On the gate model of topic `SelfCallAuthorityFaithful` (Specs, "Permissions"), for the handler at
address `handler` on chain `thisChain`: `Reaches pinnedTable handler thisChain gc` is a call `gc`
arriving at an entry point, direct or relayed by the pin's `receiveMessage`, and `InnerGate` is the
deployed permission gate. These results are not composed with `exec`. -/

/-- **AN EXECUTOR-GATED ATOMIC LEG PASSES THE GATE ONLY FOR ITS EXECUTOR, CALLING DIRECTLY.** At the
pin, a call into `executeAtomicBundle` for a bundle whose `executionAddress` parses to `(ch, a)`
passes the execution gate (`L2InteropHandler.sol:62-75`) only if it is a direct call (its
`msg.sender` is not the handler) from `a`, carrying the principal `(thisChain, a)`, and `ch` is
`thisChain` or `0`. -/
def Properties.ExecutorGatedLegNeedsExecutor : Prop :=
  ∀ (handler thisChain ch a : ℕ) (gc : GateCall), Reaches pinnedTable handler thisChain gc →
    gc.entry = .executeAtomicBundle → gc.attrs.execution = .evm ch a →
    InnerGate handler thisChain .execution gc.attrs gc.sender →
      gc.sender ≠ handler ∧ gc.sender = a ∧ gc.principal = (thisChain, a) ∧
        (ch = thisChain ∨ ch = 0)

/-- **WITH AN EXECUTOR ON ANOTHER CHAIN, NO CALL PASSES THE ATOMIC GATE; THE PUBLIC ONE IS
RELAYED.** At the pin, for bundle attributes whose `executionAddress` parses to `(ch, a)` with `ch`
neither `thisChain` nor `0`: no call the handler receives at `executeAtomicBundle` for those
attributes passes the execution gate. A rescue message from `(ch, a)` selecting `executeBundle` on
a bundle with the same attributes is dispatched by `receiveMessage` (`InteropHandlerBase.sol:351-352`,
`:379-391`) to a self-call of `executeBundle` carrying `(ch, a)`, which reaches `executeBundle` and
passes its gate. -/
def Properties.ForeignChainExecutorHasNoAtomicRoute : Prop :=
  ∀ (handler thisChain ch a : ℕ) (attrs : GateAttrs), attrs.execution = .evm ch a →
    ch ≠ thisChain → ch ≠ 0 →
    (∀ gc : GateCall, Reaches pinnedTable handler thisChain gc → gc.entry = .executeAtomicBundle →
        gc.attrs = attrs → ¬ InnerGate handler thisChain .execution gc.attrs gc.sender) ∧
    dispatch pinnedTable handler handler ⟨some (ch, a), some (.entry .executeBundle), attrs⟩ =
        some ⟨.executeBundle, attrs, (ch, a)⟩ ∧
    Reaches pinnedTable handler thisChain ⟨.executeBundle, attrs, handler, (ch, a)⟩ ∧
    InnerGate handler thisChain .execution attrs handler

/-! ## (h) The two routes are enabled -/

/-- **THE UNBUNDLED ROUTE IS ENABLED.** For every state where `b` is `Verified` or `Unbundled`, every
request of the right length that the first loop accepts (`RequestValid`), and targets that accept:
`unbundleBundle` with budget `b.calls + 2` succeeds, records exactly the request (`applyRequest`),
and delivers exactly the requested calls, in index order. -/
def Properties.UnbundleEnabled : Prop :=
  ∀ (s : State) (b : Bundle) (req : List CallStatus) (cs : List Callee),
    req.length = b.calls → (s.bundle b.hash = .Verified ∨ s.bundle b.hash = .Unbundled) →
    RequestValid s b.hash req → (∀ c ∈ cs, c = .returns) →
      submit .deployed s ⟨b.calls + 2, .unbundleBundle b req, cs⟩ =
        (applyRequest s b.hash req, (toExecute 0 req).map (Effect.delivered b.hash))

/-- **WITHOUT A VALID PROOF, THE ATOMIC ROUTE STAYS ENABLED UNTIL IT IS USED.** Along every run from
fresh storage in which no call presents a valid inclusion proof for `b`'s hash, `b` is
`FullyExecuted`, or it is `Unreceived` and `executeAtomicBundle` with the gate's verdict `true`,
targets accepting and budget `b.calls + 2` commits: `b` becomes `FullyExecuted` with its calls
`Executed`, each call is delivered once, in index order, and `b` is executed. The gate's verdict is
an input (Specs, "Gate verdict"); the permission check is not in this model, and (f) states it on
the gate model. -/
def Properties.AtomicRouteStaysEnabled : Prop :=
  ∀ (b : Bundle) (txs : List Tx), NoProofRun b.hash txs →
    (submitAll .deployed Contracts.InteropHandler.init txs).1.bundle b.hash = .FullyExecuted ∨
      ((submitAll .deployed Contracts.InteropHandler.init txs).1.bundle b.hash = .Unreceived ∧
        ∀ cs : List Callee, (∀ c ∈ cs, c = .returns) →
          submit .deployed (submitAll .deployed Contracts.InteropHandler.init txs).1
              ⟨b.calls + 2, .executeAtomicBundle b true, cs⟩ =
            ((((submitAll .deployed Contracts.InteropHandler.init txs).1.setBundle b.hash
                .FullyExecuted).executeAll b.hash b.calls),
              (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash]))

/-! ## Non-vacuity -/

/-- **THE HEADLINE'S PREMISES HOLD, ON A TWO-LEG FLOW.** For every node hash, padding constant and
leaf hash: in `RootImport`'s two-chain history (`twoChainSystem 1 2`, both legs committed on time),
the two-leg flow `mixedFlow 0 1 2` passed the gate for its leg `⟨0, 1⟩` on the honest evidence,
and its other leg `⟨1, 2⟩` (bundle hash `2`) meets the destination premises on a run of two
attempts at it, with the gate passing. The second attempt's first target executes the public
bundle `3` with a valid proof, and its second target reverts. No call presents a valid proof for
hash `2`, and every attempt on it has an always-reverting target. The nested public execution is
undone with the attempt (bundle `3` ends `Unreceived`), although the same public execution commits
when made at top level from fresh storage. -/
def Properties.RevertingLegWitness : Prop :=
  ∀ (hh : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (ev : GateEvidence),
      Wf (Contracts.RootImport.twoChainSystem 1 2) ∧
      ExecutedViaBy hh z0 hl (fun _ b => b)
        (Contracts.Atomicity.honestFlowHash (Contracts.Atomicity.mixedFlow 0 1 2))
        (Contracts.RootImport.twoChainSystem 1 2) (Contracts.Atomicity.mixedFlow 0 1 2) ev ⟨0, 1⟩ ∧
      (⟨1, 2⟩ : FlowLeg) ∈ (Contracts.Atomicity.mixedFlow 0 1 2).legs ∧
      (⟨1, 2⟩ : FlowLeg) ≠ ⟨0, 1⟩ ∧
      NoProofRun 2 [wRevertingAttempt 2, wNestedRevertingAttempt 2] ∧
      (∀ t ∈ [wRevertingAttempt 2, wNestedRevertingAttempt 2], TxEvery (AtomicAttemptReverts 2) t) ∧
      (submitAll .deployed Contracts.InteropHandler.init
        [wRevertingAttempt 2, wNestedRevertingAttempt 2]).1.bundle 3 = .Unreceived ∧
      (submit .deployed Contracts.InteropHandler.init wPublicRun).1.bundle 3 = .FullyExecuted

/-- **THE SOURCE-RUN FORM'S PREMISES HOLD, AND BOTH CLASHES ARE FALSE.** On the honest
`InteropCenter` witness chain (`wParams`, run `wS3`: atomic leg `wD1` with bundle hash `1`, public
bundle `wD2` with bundle hash `2`), with `wD2`'s bytes as the one published message: from fresh
storage, the destination run that verifies the public bundle with a valid proof and then attempts
the atomic leg with a reverting target meets every premise of
`AtomicLegWithRevertingCallNeverExecutesOrClash` for `d = wD1`. The run commits the verification
(`wD2`'s hash ends `Verified`), and neither clash disjunct holds. -/
def Properties.RevertingLegFromSourceWitness : Prop :=
  Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed Contracts.InteropCenter.wParams
      Contracts.InteropCenter.init Contracts.InteropCenter.wS3 ∧
    Contracts.InteropCenter.EncInjOn Contracts.InteropCenter.wParams.enc
      (Contracts.InteropCenter.wS3.log.map Contracts.InteropCenter.Dispatch.bundle) ∧
    PublishesOnlyPublicDispatches Contracts.InteropCenter.wParams Contracts.InteropCenter.wS3.log
      [(Contracts.InteropCenter.wParams.chainId,
        Contracts.InteropCenter.wParams.enc Contracts.InteropCenter.wD2.bundle)] ∧
    Contracts.InteropCenter.wD1 ∈ Contracts.InteropCenter.wS3.log ∧
    Contracts.InteropCenter.wD1.isAtomic = true ∧
    Contracts.InteropCenter.bundleHash Contracts.InteropCenter.wParams
      Contracts.InteropCenter.wD1.bundle = 1 ∧
    Contracts.InteropHandler.init.bundle 1 = .Unreceived ∧
    SoundProofRun (PublishedHash Contracts.InteropCenter.wParams.keccak
      [(Contracts.InteropCenter.wParams.chainId,
        Contracts.InteropCenter.wParams.enc Contracts.InteropCenter.wD2.bundle)])
      [wVerify 2 1, wRevertingAttempt 1] ∧
    (∀ t ∈ [wVerify 2 1, wRevertingAttempt 1], TxEvery (AtomicAttemptReverts 1) t) ∧
    (submitAll .deployed Contracts.InteropHandler.init [wVerify 2 1, wRevertingAttempt 1]).1.bundle 2
      = .Verified ∧
    ¬ (∃ d' ∈ Contracts.InteropCenter.wS3.log, d'.isAtomic = false ∧
        Contracts.InteropCenter.CrossSenderSaltClash Contracts.InteropCenter.wParams
          Contracts.InteropCenter.wD1 d') ∧
    ¬ (∃ p ∈ [(Contracts.InteropCenter.wParams.chainId,
          Contracts.InteropCenter.wParams.enc Contracts.InteropCenter.wD2.bundle)],
        HashCollision Contracts.InteropCenter.wParams.keccak
          (Contracts.InteropCenter.bundlePreimage Contracts.InteropCenter.wParams
            Contracts.InteropCenter.wD1.bundle)
          (abiEncode p.1.val p.2))

/-- **(e)'S CONTRAST, ON A TWO-CALL BUNDLE.** For bundle `⟨5, 2⟩` and call `1`: verifying it and
unbundling it with call `1` cancelled delivers call `0` only and records call `1` `Cancelled`. -/
def Properties.EscapeWitness : Prop :=
  (submitAll .deployed Contracts.InteropHandler.init (escapeRun ⟨5, 2⟩ 1)).2 = [.delivered 5 0] ∧
    (submitAll .deployed Contracts.InteropHandler.init (escapeRun ⟨5, 2⟩ 1)).1.call 5 1
      = .Cancelled

/-- **(h)'S PREMISES HOLD.** After `verifyBundle` of `⟨3, 2⟩`, the request `[Executed, Cancelled]`
is valid and `UnbundleEnabled` applies, delivering call `0`; the run `[wVerify 3 2]` presents a
valid proof, but none for hash `1`, and leaves bundle `1` `Unreceived`, so its atomic execution
runs. -/
def Properties.EnablednessWitness : Prop :=
  ((submit .deployed Contracts.InteropHandler.init (wVerify 3 2)).1.bundle 3 = .Verified ∧
    RequestValid (submit .deployed Contracts.InteropHandler.init (wVerify 3 2)).1 3
      [.Executed, .Cancelled] ∧
    toExecute 0 [.Executed, .Cancelled] = [0]) ∧
  (NoProofRun 1 [wVerify 3 2] ∧ ¬ NoProofRun 3 [wVerify 3 2] ∧
    (submitAll .deployed Contracts.InteropHandler.init [wVerify 3 2]).1.bundle 1 = .Unreceived)

/-- **BOTH BRANCHES OF `AtomicRouteStaysEnabled` OCCUR ON ONE RUN.** The run of
`wRevertingAttempt 1` and then a committing `executeAtomicBundle` of `⟨1, 1⟩` (gate passing, its
target returning) presents no valid proof for hash `1`. After the reverted attempt, bundle `1` is
still `Unreceived` (the second branch, after an attempt on `b`), and the committing attempt
leaves it `FullyExecuted` (the first branch, after an earlier transaction on `b` committed). -/
def Properties.AtomicRouteBothBranchesWitness : Prop :=
  NoProofRun 1 [wRevertingAttempt 1, (⟨5, .executeAtomicBundle ⟨1, 1⟩ true, [.returns]⟩ : Tx)] ∧
    (submitAll .deployed Contracts.InteropHandler.init [wRevertingAttempt 1]).1.bundle 1
      = .Unreceived ∧
    (submitAll .deployed Contracts.InteropHandler.init
        [wRevertingAttempt 1, (⟨5, .executeAtomicBundle ⟨1, 1⟩ true, [.returns]⟩ : Tx)]).1.bundle 1
      = .FullyExecuted

/-- **(f)'S PREMISES HOLD, AND THE GATE DECIDES.** For the handler at `0` on chain `324`: a direct
call from `7` into `executeAtomicBundle` for attributes naming `(324, 7)` reaches the gate and passes
it, so every premise of `ExecutorGatedLegNeedsExecutor` holds. For attributes naming `(325, 7)`,
whose chain is neither `324` nor `0` (the premises of `ForeignChainExecutorHasNoAtomicRoute`), the
same direct call reaches `executeAtomicBundle` with those attributes and fails the gate. -/
def Properties.ExecutorGateWitness : Prop :=
  Reaches pinnedTable 0 324 ⟨.executeAtomicBundle, ⟨.evm 324 7, .evm 324 7⟩, 7, (324, 7)⟩ ∧
    InnerGate 0 324 .execution ⟨.evm 324 7, .evm 324 7⟩ 7 ∧
    Reaches pinnedTable 0 324 ⟨.executeAtomicBundle, ⟨.evm 325 7, .evm 325 7⟩, 7, (324, 7)⟩ ∧
    ¬ InnerGate 0 324 .execution ⟨.evm 325 7, .evm 325 7⟩ 7 ∧
    (325 : ℕ) ≠ 324 ∧ (325 : ℕ) ≠ 0

end Contracts.ExecutionLiveness
