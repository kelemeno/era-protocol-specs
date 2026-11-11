import EraSpec.Protocol.InteropAtomicity.Specs.ExecutionLiveness

/-!
# Properties: an atomic leg has one route, and what that costs

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.ExecutionLiveness`; proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.ExecutionLiveness`. The destination is
`Contracts.InteropHandler` (topic `Reentrancy`): every result holds for every re-entrant behaviour
of every target and every budget.

## (d) An atomic leg never reaches `Verified`, so it has no unbundle route

* On the destination, a hash outside `Pub` that is `Unreceived` or `FullyExecuted` stays so along
  every backed run (`UnpublishedHashKeepsOnlyTheAtomicRoute`); from those two statuses, without a
  valid inclusion proof, `executeBundle`, `verifyBundle` and `unbundleBundle` all revert
  (`PublicRoutesRevertOutsideVerified`).
* On the source, an atomic leg's hash is the hash of no published item, unless a cross-sender salt
  clash with a public dispatch of the same run, or keccak collides on the two named preimages
  (`AtomicLegHashUnpublishedOrClash`). The salt-clash case is
  `Contracts.InteropCenter.Properties.AtomicBytesNeverPublished`.
* Together (`AtomicHasNoUnbundleRoute`): along every backed destination run from fresh storage,
  every atomic leg of the source run is `Unreceived` or `FullyExecuted`, never `Verified` or
  `Unbundled`, or one of the two pinned collisions holds.

## (e) A permanently reverting call strands a finalized leg

* If every atomic attempt on an unpublished hash meets a reverting target, the hash stays
  `Unreceived` and no effect of it is ever committed, along every backed run
  (`AtomicLegWithRevertingCallNeverExecutes`).
* Once the flow is finalized (some leg passed the gate), no leg of it is ever refunded, or a
  located break (`Contracts.Refund.Properties.OneExecutionFreezesTheFlowOrBreak`). So such a leg is
  stranded: never delivered, never refunded (`FinalizedLegStrandedByRevertingCall`).
* A public bundle with the same reverting call escapes: verify it, then unbundle it cancelling the
  bad call, and every other call is delivered (`PublicBundleEscapesViaUnbundle`).

## (f) An executor-gated leg needs its executor

An atomic leg with an `executionAddress` can be executed only by a direct call from that address,
and only if the address's chain is this chain or `0` (`ExecutorGatedLegNeedsExecutor`). With a
foreign chain nobody can ever execute it, while a public bundle with the same attribute is
executable through `receiveMessage` from that chain (`ForeignExecutorStrandsAtomicLeg`).

## (g) A `Verified` atomic hash closes the atomic route for good

If an atomic leg's hash ever became `Verified` (which (d) says needs a pinned collision), it never
returns to `Unreceived`, every later `executeAtomicBundle` of it reverts, and `executeBundle` runs
its calls with no inclusion proof and no flow gate (`GriefVerifiedBlocksAtomic`).

## (h) The two routes are enabled

* `unbundleBundle` with a valid request on a `Verified` or `Unbundled` bundle, targets accepting,
  succeeds and records exactly the request (`UnbundleEnabled`). This is the generic enabledness of
  the unbundled route that `Reentrancy` shows only on witnesses.
* Along every backed run, an unpublished leg is either already `FullyExecuted` or still
  `Unreceived`, and then `executeAtomicBundle` with the gate passing and targets accepting runs it
  (`FinalizedLegExecutableUnderEnabledness`).

## Non-vacuity

`NoUnbundleRouteWitness` meets every premise of (d) on a source run with an atomic and a public
dispatch and a destination run that verifies the public bundle and executes the atomic one, with
both collision disjuncts false. `StrandedLegWitness` meets every premise of (e), for every hash
family, with a nested attempt. `GriefWitness` reaches `Verified` for a hash and shows both effects
of (g). `EnablednessWitness` meets the premises of (h). `ExecutorGateWitness` meets the permission
premises of (f).
-/

namespace Contracts.ExecutionLiveness

open Contracts.InteropHandler (State Entry Callee Frame Tx Bundle BundleHash Effect exec submit
  submitAll toExecute)
open AttackVectors.BundleStatusMachine (Status CallStatus)
open AttackVectors.BundleHashEncoding (abiEncode)
open Contracts.InteropCenter (Params Dispatch CrossSenderSaltClash EncInjOn bundleHash bundlePreimage)
open MerkleSpec (Hash)
open Contracts.InteropCommitmentTree (LeafHash)
open Contracts.Atomicity (CommitValue FlowHash System Wf Flow FlowLeg GateEvidence ExecutedViaBy)
open Contracts.Refund (Managers AuthCall ReachLog emptyManagers Refunded RefundBreak obligationOf)

/-! ## (d) An atomic leg never reaches `Verified` -/

/-- **AN UNPUBLISHED HASH KEEPS ONLY THE ATOMIC ROUTE.** For every set `Pub` of published hashes and
every hash `h` outside it: from any state where `h` is `Unreceived` or `FullyExecuted`, along every
sequence of transactions whose inclusion-proof verdicts are backed by `Pub` at every depth, `h` is
still `Unreceived` or `FullyExecuted`. `Verified` and `Unbundled` are never reached. -/
def Properties.UnpublishedHashKeepsOnlyTheAtomicRoute : Prop :=
  ∀ (Pub : BundleHash → Prop) (h : BundleHash), ¬ Pub h →
    ∀ (s : State) (txs : List Tx), (s.bundle h = .Unreceived ∨ s.bundle h = .FullyExecuted) →
      (∀ t ∈ txs, TxEvery (ProofBacked Pub) t) →
      ((submitAll .deployed s txs).1.bundle h = .Unreceived ∨
        (submitAll .deployed s txs).1.bundle h = .FullyExecuted)

/-- **OUTSIDE `Verified` AND `Unbundled`, THE PUBLIC ROUTES REVERT WITHOUT A PROOF.** From a state
where the bundle is `Unreceived` or `FullyExecuted`, with no valid inclusion proof,
`executeBundle` (`:117-123`), `verifyBundle` (`:157`) and every `unbundleBundle` (`:195`) revert,
whatever the targets and the budget. -/
def Properties.PublicRoutesRevertOutsideVerified : Prop :=
  ∀ (s : State) (b : Bundle), (s.bundle b.hash = .Unreceived ∨ s.bundle b.hash = .FullyExecuted) →
    ∀ (n : ℕ) (cs : List Callee),
      exec .deployed n (.entry (.executeBundle b false) cs) s = none ∧
      exec .deployed n (.entry (.verifyBundle b false) cs) s = none ∧
      ∀ req, exec .deployed n (.entry (.unbundleBundle b req) cs) s = none

/-- **AN ATOMIC LEG'S HASH IS NO PUBLISHED ITEM'S HASH, OR A PINNED COLLISION.** Take a deployed
center run `S` of chain `P.chainId` from fresh storage whose encoder separates its bundles, and any
list `pub` of published items in which chain `P.chainId`'s items are bytes of public dispatches of
`S`. For every atomic dispatch `d` of `S` and every published item `p`, from any chain: the hash a
destination computes for `p` differs from `d`'s bundle hash; or a public dispatch of `S` and `d`
form a cross-sender salt clash; or keccak collides on the two named, distinct preimages
`abi.encode(p.chain, p.bytes)` and `abi.encode(block.chainid, abi.encode(d.bundle))`. -/
def Properties.AtomicLegHashUnpublishedOrClash : Prop :=
  ∀ (P : Params) (S : Contracts.InteropCenter.State),
    Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed P Contracts.InteropCenter.init S →
    EncInjOn P.enc (S.log.map Dispatch.bundle) →
    ∀ pub : List Published, PublishedOnlyPublicDispatches P S pub →
    ∀ d ∈ S.log, d.isAtomic = true → ∀ p ∈ pub,
      publishedHash P.keccak p ≠ bundleHash P d.bundle ∨
      (∃ d' ∈ S.log, d'.isAtomic = false ∧ CrossSenderSaltClash P d d') ∨
      (abiEncode p.1.val p.2 ≠ bundlePreimage P d.bundle ∧
        publishedHash P.keccak p = bundleHash P d.bundle)

/-- **HEADLINE (d): AN ATOMIC LEG HAS NO UNBUNDLE ROUTE, OR A PINNED COLLISION.** Take a deployed
center run `S` of chain `P.chainId` whose encoder separates its bundles; publications `pub` in
which chain `P.chainId` published only its public dispatches; and any sequence of destination
transactions from fresh storage whose inclusion-proof verdicts are backed by `pub`. Then every
atomic leg of `S` is, after the sequence, `Unreceived` or `FullyExecuted`; or a cross-sender salt
clash with a public dispatch of `S` holds; or keccak collides on a published item's preimage and
the leg's. Every prefix of a backed sequence is backed, so in the first case the leg is never
`Verified` or `Unbundled` between transactions, and there `PublicRoutesRevertOutsideVerified`
closes `verifyBundle`, `executeBundle` and `unbundleBundle` for it: `executeAtomicBundle` is its
only route. -/
def Properties.AtomicHasNoUnbundleRoute : Prop :=
  ∀ (P : Params) (S : Contracts.InteropCenter.State),
    Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed P Contracts.InteropCenter.init S →
    EncInjOn P.enc (S.log.map Dispatch.bundle) →
    ∀ pub : List Published, PublishedOnlyPublicDispatches P S pub →
    ∀ txs : List Tx, (∀ t ∈ txs, TxEvery (ProofBacked (PubHashes P.keccak pub)) t) →
    ∀ d ∈ S.log, d.isAtomic = true →
      ((submitAll .deployed Contracts.InteropHandler.init txs).1.bundle (bundleHash P d.bundle)
          = .Unreceived ∨
        (submitAll .deployed Contracts.InteropHandler.init txs).1.bundle (bundleHash P d.bundle)
          = .FullyExecuted) ∨
      (∃ d' ∈ S.log, d'.isAtomic = false ∧ CrossSenderSaltClash P d d') ∨
      (∃ p ∈ pub, abiEncode p.1.val p.2 ≠ bundlePreimage P d.bundle ∧
        publishedHash P.keccak p = bundleHash P d.bundle)

/-! ## (e) A permanently reverting call strands a finalized leg -/

/-- **AN ATOMIC LEG WITH A PERMANENTLY REVERTING CALL NEVER EXECUTES.** For an unpublished hash `h`
that is `Unreceived`: along every sequence of transactions whose proof verdicts are backed by `Pub`
and in which every atomic attempt on `h`, at every depth, meets a reverting target, `h` stays
`Unreceived` and no effect of `h` is ever committed: none of its calls is delivered. -/
def Properties.AtomicLegWithRevertingCallNeverExecutes : Prop :=
  ∀ (Pub : BundleHash → Prop) (h : BundleHash), ¬ Pub h →
    ∀ (s : State) (txs : List Tx), s.bundle h = .Unreceived →
      (∀ t ∈ txs, TxEvery (ProofBacked Pub) t) →
      (∀ t ∈ txs, TxEvery (AtomicAttemptReverts h) t) →
      (submitAll .deployed s txs).1.bundle h = .Unreceived ∧
        ∀ e ∈ (submitAll .deployed s txs).2, e.bundleHash ≠ h

/-- **HEADLINE (e): A FINALIZED LEG WITH A PERMANENTLY REVERTING CALL IS STRANDED.** Take a flow `F`
that passed the atomicity gate for some leg (`ExecutedViaBy`, so `F` is finalized) in a well-formed
history, and a leg `other` of `F` whose hash is unpublished. Along every backed destination run from
fresh storage in which every atomic attempt on `other` meets a reverting target, `other` stays
`Unreceived` and none of its calls is delivered; and in every logged run of the source managers its
obligation is never refunded, or a located `RefundBreak`. Neither resolution is available: its burn
is neither released on the destination nor returned on the source. -/
def Properties.FinalizedLegStrandedByRevertingCall : Prop :=
  ∀ (hh : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaBy hh z0 hl cv fh S F ev leg →
    ∀ other ∈ F.legs, ∀ (Pub : BundleHash → Prop), ¬ Pub other.bundleHash →
    ∀ txs : List Tx, (∀ t ∈ txs, TxEvery (ProofBacked Pub) t) →
      (∀ t ∈ txs, TxEvery (AtomicAttemptReverts other.bundleHash) t) →
      ((submitAll .deployed Contracts.InteropHandler.init txs).1.bundle other.bundleHash
          = .Unreceived ∧
        ∀ e ∈ (submitAll .deployed Contracts.InteropHandler.init txs).2,
          e.bundleHash ≠ other.bundleHash) ∧
      ∀ (Ms : Managers) (log : List AuthCall),
        ReachLog hh z0 hl cv fh S emptyManagers Ms log →
          ¬ Refunded Ms (obligationOf F other) ∨
            RefundBreak hh z0 hl fh S F ev (obligationOf F other) log

/-- **A PUBLIC BUNDLE WITH THE SAME REVERTING CALL ESCAPES THROUGH `unbundleBundle`.** For every
bundle `b` and every call `i` of it: whole-bundle execution reverts whenever a target reverts (as
for the atomic route); but from fresh storage, `verifyBundle` with a valid proof and then
`unbundleBundle` cancelling call `i` and executing the others, with their targets accepting, leave
`b` `Unbundled`, call `i` `Cancelled`, every other call `Executed`, and deliver every other call,
in order. The reverting target is never called. -/
def Properties.PublicBundleEscapesViaUnbundle : Prop :=
  ∀ (b : Bundle) (i : ℕ), i < b.calls →
    (∀ (n : ℕ) (ok : Bool) (cs : List Callee) (s : State), Callee.reverts ∈ cs.take b.calls →
      exec .deployed n (.entry (.executeBundle b ok) cs) s = none) ∧
    (submitAll .deployed Contracts.InteropHandler.init
        [⟨1, .verifyBundle b true, []⟩, ⟨b.calls + 2, .unbundleBundle b (escapeRequest b.calls i), []⟩]).1.bundle
        b.hash = .Unbundled ∧
    (submitAll .deployed Contracts.InteropHandler.init
        [⟨1, .verifyBundle b true, []⟩, ⟨b.calls + 2, .unbundleBundle b (escapeRequest b.calls i), []⟩]).1.call
        b.hash i = .Cancelled ∧
    (∀ j < b.calls, j ≠ i →
      (submitAll .deployed Contracts.InteropHandler.init
        [⟨1, .verifyBundle b true, []⟩, ⟨b.calls + 2, .unbundleBundle b (escapeRequest b.calls i), []⟩]).1.call
        b.hash j = .Executed) ∧
    (submitAll .deployed Contracts.InteropHandler.init
        [⟨1, .verifyBundle b true, []⟩, ⟨b.calls + 2, .unbundleBundle b (escapeRequest b.calls i), []⟩]).2
      = ((List.range b.calls).filter (· ≠ i)).map (Effect.delivered b.hash)

/-! ## (f) An executor-gated leg needs its executor -/

/-- **ONLY THE NAMED EXECUTOR, CALLING DIRECTLY FROM THIS CHAIN.** If `executeAtomicBundle` is
permitted on some route for an `executionAddress` `(ch, a)`, that route is a direct call from `a`
and `ch` is this chain or `0`. -/
def Properties.ExecutorGatedLegNeedsExecutor : Prop :=
  ∀ (thisChain ch a : ℕ) (r : Route),
    ExecutionPermitted thisChain (some (ch, a)) .executeAtomicBundle r →
      r = .direct a ∧ (ch = thisChain ∨ ch = 0)

/-- **A FOREIGN-CHAIN EXECUTOR STRANDS AN ATOMIC LEG, NOT A PUBLIC ONE.** For an `executionAddress`
on a chain `ch` that is neither this chain nor `0`: no route permits `executeAtomicBundle`, so the
leg can never be executed; `executeBundle` of a public bundle with the same attribute is permitted
through `receiveMessage` for a message from `ch`'s address. -/
def Properties.ForeignExecutorStrandsAtomicLeg : Prop :=
  ∀ (thisChain ch a : ℕ), ch ≠ thisChain → ch ≠ 0 →
    (∀ r, ¬ ExecutionPermitted thisChain (some (ch, a)) .executeAtomicBundle r) ∧
    ExecutionPermitted thisChain (some (ch, a)) .executeBundle (.rescue ch a)

/-! ## (g) A `Verified` atomic hash -/

/-- **A `Verified` HASH CLOSES THE ATOMIC ROUTE FOR GOOD AND OPENS AN UNGATED ONE.** From a state in
which `b`'s hash is `Verified`: after any sequence of transactions it is not `Unreceived`, so every
`executeAtomicBundle` of `b` reverts, whatever the gate's verdict; and `executeBundle` of `b` with
no valid inclusion proof, targets accepting, runs every call of `b` and executes it: the calls run
without the flow gate. -/
def Properties.GriefVerifiedBlocksAtomic : Prop :=
  ∀ (s : State) (b : Bundle), s.bundle b.hash = .Verified →
    (∀ txs : List Tx, (submitAll .deployed s txs).1.bundle b.hash ≠ .Unreceived) ∧
    (∀ (txs : List Tx) (n : ℕ) (ok : Bool) (cs : List Callee),
      exec .deployed n (.entry (.executeAtomicBundle b ok) cs) (submitAll .deployed s txs).1 = none) ∧
    ∀ cs : List Callee, (∀ c ∈ cs, c = .returns) →
      submit .deployed s ⟨b.calls + 2, .executeBundle b false, cs⟩ =
        ((s.setBundle b.hash .FullyExecuted).executeAll b.hash b.calls,
          (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash])

/-! ## (h) The two routes are enabled -/

/-- **THE UNBUNDLED ROUTE IS ENABLED.** For every state where `b` is `Verified` or `Unbundled`, every
request of the right length that the first loop accepts, and targets that accept: `unbundleBundle`
succeeds, records exactly the request (`applyRequest`), and delivers exactly the requested calls, in
index order. -/
def Properties.UnbundleEnabled : Prop :=
  ∀ (s : State) (b : Bundle) (req : List CallStatus) (cs : List Callee),
    req.length = b.calls → (s.bundle b.hash = .Verified ∨ s.bundle b.hash = .Unbundled) →
    RequestValid s b.hash req → (∀ c ∈ cs, c = .returns) →
      submit .deployed s ⟨b.calls + 2, .unbundleBundle b req, cs⟩ =
        (applyRequest s b.hash req, (toExecute 0 req).map (Effect.delivered b.hash))

/-- **A FINALIZED, UNPUBLISHED LEG IS EXECUTED OR EXECUTABLE.** Along every backed destination run
from fresh storage, an unpublished bundle is `FullyExecuted`, or it is `Unreceived` and
`executeAtomicBundle` with the gate passing (the flow is finalized and the executor presents the
proofs) and targets accepting runs each of its calls once and executes it. Permission is (f). -/
def Properties.FinalizedLegExecutableUnderEnabledness : Prop :=
  ∀ (Pub : BundleHash → Prop) (b : Bundle), ¬ Pub b.hash →
    ∀ txs : List Tx, (∀ t ∈ txs, TxEvery (ProofBacked Pub) t) →
      (submitAll .deployed Contracts.InteropHandler.init txs).1.bundle b.hash = .FullyExecuted ∨
        ((submitAll .deployed Contracts.InteropHandler.init txs).1.bundle b.hash = .Unreceived ∧
          ∀ cs : List Callee, (∀ c ∈ cs, c = .returns) →
            submit .deployed (submitAll .deployed Contracts.InteropHandler.init txs).1
                ⟨b.calls + 2, .executeAtomicBundle b true, cs⟩ =
              ((((submitAll .deployed Contracts.InteropHandler.init txs).1.setBundle b.hash
                  .FullyExecuted).executeAll b.hash b.calls),
                (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash]))

/-! ## Non-vacuity -/

/-- **(d)'S PREMISES HOLD ON NONEMPTY RUNS, AND BOTH COLLISIONS ARE FALSE.** The source run
`wS3` (atomic leg `wD1`, bundle hash `1`; public `wD2`, bundle hash `2`), chain `324` publishing
`wD2`'s bytes, and the destination run that verifies the public bundle and then executes the
atomic leg: every premise of `AtomicHasNoUnbundleRoute` holds, the atomic leg ends
`FullyExecuted` while the public bundle is `Verified`, and neither collision disjunct holds. -/
def Properties.NoUnbundleRouteWitness : Prop :=
  Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed Contracts.InteropCenter.wParams
      Contracts.InteropCenter.init Contracts.InteropCenter.wS3 ∧
    EncInjOn Contracts.InteropCenter.wParams.enc
      (Contracts.InteropCenter.wS3.log.map Dispatch.bundle) ∧
    PublishedOnlyPublicDispatches Contracts.InteropCenter.wParams Contracts.InteropCenter.wS3 wPub ∧
    (∀ t ∈ [wVerifyPublic, wExecAtomic],
      TxEvery (ProofBacked (PubHashes Contracts.InteropCenter.wParams.keccak wPub)) t) ∧
    Contracts.InteropCenter.wD1 ∈ Contracts.InteropCenter.wS3.log ∧
    Contracts.InteropCenter.wD1.isAtomic = true ∧
    bundleHash Contracts.InteropCenter.wParams Contracts.InteropCenter.wD1.bundle = 1 ∧
    (submitAll .deployed Contracts.InteropHandler.init [wVerifyPublic, wExecAtomic]).1.bundle 1
      = .FullyExecuted ∧
    (submitAll .deployed Contracts.InteropHandler.init [wVerifyPublic, wExecAtomic]).1.bundle 2
      = .Verified ∧
    ¬ (∃ d' ∈ Contracts.InteropCenter.wS3.log, d'.isAtomic = false ∧
        CrossSenderSaltClash Contracts.InteropCenter.wParams Contracts.InteropCenter.wD1 d') ∧
    ¬ (∃ p ∈ wPub, abiEncode p.1.val p.2 ≠
          bundlePreimage Contracts.InteropCenter.wParams Contracts.InteropCenter.wD1.bundle ∧
        publishedHash Contracts.InteropCenter.wParams.keccak p
          = bundleHash Contracts.InteropCenter.wParams Contracts.InteropCenter.wD1.bundle)

/-- **(e)'S PREMISES HOLD TOGETHER.** For every node hash, padding constant and leaf hash: a
well-formed history with a flow that passed the gate (from
`Contracts.Refund.Properties.ExecutedObligationNeverRefundedOrBreakWitness`), a leg of it, no
publication, and a destination run of two attempts at that leg, the second nesting a committed
public execution before its reverting target: every premise of
`FinalizedLegStrandedByRevertingCall` holds, and the nested execution is undone. -/
def Properties.StrandedLegWitness : Prop :=
  ∀ (hh : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (F : Flow) (ev : GateEvidence)
      (leg other : FlowLeg) (txs : List Tx),
      Wf S ∧ ExecutedViaBy hh z0 hl cv fh S F ev leg ∧ other ∈ F.legs ∧
        txs = [wRevertingAttempt other.bundleHash, wNestedRevertingAttempt other.bundleHash] ∧
        (∀ t ∈ txs, TxEvery (ProofBacked (· = 2)) t) ∧ ¬ (other.bundleHash = 2) ∧
        (∀ t ∈ txs, TxEvery (AtomicAttemptReverts other.bundleHash) t) ∧
        (submitAll .deployed Contracts.InteropHandler.init txs).1.bundle 2 = .Unreceived

/-- **(g) FIRES ON A REACHABLE STATE.** From fresh storage, `verifyBundle` of `⟨1, 1⟩` with a valid
proof (a published bundle whose hash is the atomic leg's, which (d) says needs a collision) makes
hash `1` `Verified`; then the atomic attempt with the gate passing reverts, and `executeBundle` with
no proof runs the call. -/
def Properties.GriefWitness : Prop :=
  (submit .deployed Contracts.InteropHandler.init (wVerify 1 1)).1.bundle 1 = .Verified ∧
    (submit .deployed (submit .deployed Contracts.InteropHandler.init (wVerify 1 1)).1
        ⟨4, .executeAtomicBundle ⟨1, 1⟩ true, [.returns]⟩).2 = [] ∧
    (submit .deployed (submit .deployed Contracts.InteropHandler.init (wVerify 1 1)).1
        ⟨4, .executeBundle ⟨1, 1⟩ false, [.returns]⟩).2 = [.delivered 1 0, .executed 1]

/-- **(h)'S PREMISES HOLD.** After `verifyBundle` of `⟨3, 2⟩`, the request
`[Executed, Cancelled]` is valid and `UnbundleEnabled` applies, delivering call `0`; with
`Pub = {3}`, the backed run `[wVerify 3 2]` leaves the unpublished bundle `⟨1, 2⟩` `Unreceived`,
so its atomic execution runs. -/
def Properties.EnablednessWitness : Prop :=
  ((submit .deployed Contracts.InteropHandler.init (wVerify 3 2)).1.bundle 3 = .Verified ∧
    RequestValid (submit .deployed Contracts.InteropHandler.init (wVerify 3 2)).1 3
      [.Executed, .Cancelled] ∧
    toExecute 0 [.Executed, .Cancelled] = [0]) ∧
  ((∀ t ∈ [wVerify 3 2], TxEvery (ProofBacked (· = 3)) t) ∧ ¬ ((1 : BundleHash) = 3) ∧
    (submitAll .deployed Contracts.InteropHandler.init [wVerify 3 2]).1.bundle 1 = .Unreceived)

/-- **(f)'S PERMISSION PREMISE HOLDS, AND THE PUBLIC RESCUE IS LIVE.** On chain `324`, an atomic
leg whose executor is `7` on chain `324` is permitted for a direct call from `7`; a public bundle
whose executor is `7` on chain `325` is permitted through `receiveMessage` for a message from it. -/
def Properties.ExecutorGateWitness : Prop :=
  ExecutionPermitted 324 (some (324, 7)) .executeAtomicBundle (.direct 7) ∧
    ExecutionPermitted 324 (some (325, 7)) .executeBundle (.rescue 325 7)

end Contracts.ExecutionLiveness
