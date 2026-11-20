import EraSpec.Contracts.L1InteropHandler.Specs.WithdrawalGate
import EraSpec.Core.Headline

/-!
# Properties: the L1 withdrawal finalization gate

Statements about `EraSpec.Contracts.L1InteropHandler.Specs.WithdrawalGate` (era-contracts
`draft/v0.35.0` head `b17415d20`). Proofs are in
`EraSpec.Contracts.L1InteropHandler.Proofs.WithdrawalGate`.

Every run-level result quantifies over every target behaviour (re-entrant calls of every entry point,
at any depth, caught or not), every budget, every caller and every oracle verdict. None takes a hash
premise; where keccak matters, the conclusion names a collision between two byte strings of the run's
own committed log.

## (a) Provenance

* `DeliveredCallIsProvenOrKeccakClash` (headline). From fresh storage, every committed delivery is
  `ProvenBy` a committed verification of the same bytes (the proven message was sent by
  `L2_INTEROP_CENTER_ADDR` with data `BUNDLE_IDENTIFIER ++ bytes`, from the chain the bundle names as
  its source; the bundle is for L1 with L1's ETH asset id; sender and payload are the call's), or the
  delivered bytes collide under keccak with the bytes of a committed verification. The second disjunct
  is the status shortcut: `executeBundle` of a `Verified` hash and `unbundleBundle` of a `Verified` or
  `Unbundled` hash check no proof of their own bytes (`L1InteropHandler.sol:92-95`,
  `InteropHandlerBase.sol:139`).
* `CollisionDisjunctIsNeeded`: with a codec where two byte strings collide, one verified bundle lets
  the other, from a chain no proof names, be delivered.
* `VerificationsAreChecked`: what a committed verification checked.
* `ProvenanceWitness`: from fresh storage, a direct `executeBundle` and a verify-then-unbundle run each
  deliver, and every delivery is `ProvenBy` a verification of its own bytes.

## (b) Target pin and value

* `DeliveriesAreCheckedRouterCalls`: from every state, every committed delivery went to
  `L1_ASSET_ROUTER` with value `0`, is a call of the bundle its bytes decode to with `to =
  L1_ASSET_ROUTER`, value `0`, version `1` and no shadow account, and carries that call's sender and
  payload. Also: a delivery by `executeBundle` is of a one-call bundle, and a delivery of a one-call
  bundle is call `0`, made while the handler was not paused.

## (c) Pause, owner, initialization

* `PausedHandlerStartsNoDelivery`: from a paused state `executeBundle` and `unbundleBundle` revert.
* `OnlyPauseAndUnpauseWritePaused`: along every run, the final pause flag is the last value a
  committed `pause`/`unpause` wrote, or the initial one.
* `PauseWritesAreOwnerCalls` (one step): an administrative call that writes the flag is `pause` or
  `unpause` by the owner of the state it runs in.
* `CommittedPauseWritesAreOwnerCalls` (along runs): the final owner is the last owner the committed log
  wrote, or the initial one; and every committed pause write's caller is the owner the committed log
  gives at that point (the last owner written before it, or the initial one), whether the call was made
  at top level or re-entrantly by a delivered call's target. `OwnerHandoverPauseWitness`: after an
  ownership handover, the old owner's `unpause` commits nothing and the new owner's commits.
* `InitializeRunsAtMostOnce`: at most one committed `initialize`, none once the guard slot is set.
* `PauseGateWitness`: a paused handler still commits `verifyBundle`, refuses `executeBundle`, and
  delivers after `unpause`. `InitializeOnceWitness`: a second `initialize` reverts.
* `OwnerPauseMidUnbundleWitness` (boundary): the pause check runs once, at entry. In an `unbundleBundle`
  of a two-call bundle whose first call's target re-enters `pause()` as the owner, the second call is
  delivered with the handler paused. Every delivery of a one-call bundle is unpaused (b).

## (d) The single-call rule

* `VerifyThenUnbundleDeliversEveryCall` (countermodel): the rule is checked only by `executeBundle`
  (`L1InteropHandler.sol:85`). A proven two-call bundle is refused by `executeBundle`, and is delivered
  call by call by `verifyBundle` then `unbundleBundle`.
* `SingleCallEvidenceDeliversOneCall` (repaired form): if every committed verification's bundle has one
  call, every committed delivery is call `0` of a one-call bundle, made unpaused, or the delivered bytes
  collide with verified ones. `SingleCallEvidenceWitness` instantiates it. `Protocol/L1WithdrawalProvenance`
  discharges the premise under `InclusionSoundOn`, `ChainsRunTheModelOn`, `HooksAsDocumentedOn` and
  `DispatchRoundTripOn`, from the modelled shape of the center's L1 branch (`WithdrawalShape`, argued
  from source in `L1Messenger/Specs/SenderKeying.lean`, not derived from transcribed center code), up to
  a named message collision (`ProvenBundlesAreDispatchedOrCollide`).

## (e) At most once, across routes

* `L1RunsProjectToPinRuns`: every run of this model is, on the replay mappings and on deliveries and
  completions, a run of the pin's re-entrant model `InteropHandlerBase` `Reentrancy` (`.deployed`).
* `EachCallDeliveredAtMostOnce`: no `(bundleHash, index)` is delivered twice, by either route or both
  (from `Reentrancy.NoEffectCommittedTwice`).
* `CallStatusRecordsDeliveries`: from fresh storage, `callStatus[h][i] == Executed` exactly when a
  committed delivery has hash `h` and index `i` (from
  `Reentrancy.StatusRecordsExactlyTheCommittedEffects`).
* `ReentrantRedeliveryRefusedWitness`: a target that re-enters both routes for the call it is running
  gets refused; caught, the transaction commits one delivery; uncaught, none.
-/

namespace Contracts.L1WithdrawalGate

open AttackVectors.BundleStatusMachine (Status CallStatus)

/-! ## (a) Provenance -/

/-- **EVERY DELIVERED CALL IS PROVEN, OR ITS BYTES COLLIDE WITH PROVEN ONES.** From fresh storage, along
every sequence of transactions, with every target behaviour, caller and oracle verdict: for every
committed delivery `d`, either a committed verification `v` of the same bytes satisfies
`ProvenBy P v d`, or a committed verification's bytes differ from `d.bytes` and have the same keccak. -/
@[headline] def Properties.DeliveredCallIsProvenOrKeccakClash : Prop :=
  ∀ (P : Params) (txs : List Tx), ∀ d ∈ deliveries (submitAll P init txs).2,
    (∃ v ∈ verifications (submitAll P init txs).2, ProvenBy P v d) ∨
      ∃ v ∈ verifications (submitAll P init txs).2, KeccakClash P.codec v.bytes d.bytes

/-- **EVERY COMMITTED VERIFICATION CHECKED THE BUNDLE'S CONTEXT, THE SENDER AND THE DATA.** From every
state, along every sequence of transactions: each committed verification's bytes decode to its bundle,
of version `1`, with source chain the proof's chain, destination L1 and L1's ETH asset id, and the
queried message has sender `L2_INTEROP_CENTER_ADDR` and data `BUNDLE_IDENTIFIER ++ bytes`. -/
def Properties.VerificationsAreChecked : Prop :=
  ∀ (P : Params) (s : State) (txs : List Tx),
    ∀ v ∈ verifications (submitAll P s txs).2, VerificationWellFormed P v

/-- **THE COLLISION DISJUNCT IS NEEDED.** Under `wClashCodec`, where `[3]` and `[1]` have the same
keccak: from fresh storage, after `verifyBundle` of `[1]`, an `executeBundle` of `[3]` whose oracle
verdict is `false` delivers `[3]`'s call, which names chain `999` as its sender's chain. No committed
verification proves that delivery, and the delivered bytes clash with the verified ones. -/
@[countermodel] def Properties.CollisionDisjunctIsNeeded : Prop :=
  (deliveries (submitAll wClashParams init [wVerify [1], wExecOther]).2).map
      (fun d => (d.bytes, d.senderChain)) = [([3], 999)] ∧
    (∀ d ∈ deliveries (submitAll wClashParams init [wVerify [1], wExecOther]).2,
      ¬ ∃ v ∈ verifications (submitAll wClashParams init [wVerify [1], wExecOther]).2,
        ProvenBy wClashParams v d) ∧
    ∀ d ∈ deliveries (submitAll wClashParams init [wVerify [1], wExecOther]).2,
      ∃ v ∈ verifications (submitAll wClashParams init [wVerify [1], wExecOther]).2,
        KeccakClash wClashCodec v.bytes d.bytes

/-- **PROVENANCE, ON RUNS.** From fresh storage, with `wParams`: `executeBundle` of `[1]` delivers one
call, and verify-then-unbundle of `[2]` delivers two; in both runs every delivery is `ProvenBy` a
committed verification of its own bytes. -/
@[witness] def Properties.ProvenanceWitness : Prop :=
  (deliveries (submitAll wParams init [wExecOne]).2).length = 1 ∧
    (∀ d ∈ deliveries (submitAll wParams init [wExecOne]).2,
      ∃ v ∈ verifications (submitAll wParams init [wExecOne]).2, ProvenBy wParams v d) ∧
    (deliveries (submitAll wParams init [wVerify [2], wUnbundleTwo]).2).length = 2 ∧
    ∀ d ∈ deliveries (submitAll wParams init [wVerify [2], wUnbundleTwo]).2,
      ∃ v ∈ verifications (submitAll wParams init [wVerify [2], wUnbundleTwo]).2, ProvenBy wParams v d

/-! ## (b) Target pin and value -/

/-- **EVERY DELIVERY IS A CHECKED, ZERO-VALUE CALL TO `L1_ASSET_ROUTER`.** From every state, along every
sequence of transactions, with every target behaviour: every committed delivery satisfies
`DeliveryWellFormed` (the target is `L1_ASSET_ROUTER`, the value `0`; it is call `index` of the bundle
its bytes decode to, with `to = L1_ASSET_ROUTER`, value `0`, call version `1` and no shadow account;
the ERC-7786 sender is `(sourceChainId, from)` and the payload `data`; a delivery by `executeBundle` is
of a one-call bundle; a delivery of a one-call bundle is call `0`, made while not paused). -/
@[headline] def Properties.DeliveriesAreCheckedRouterCalls : Prop :=
  ∀ (P : Params) (s : State) (txs : List Tx),
    ∀ d ∈ deliveries (submitAll P s txs).2, DeliveryWellFormed P d

/-! ## (c) Pause, owner, initialization -/

/-- **A PAUSED HANDLER STARTS NO DELIVERY.** From a paused state, `executeBundle` and `unbundleBundle`
revert, for every budget, caller, input and target. -/
@[headline] def Properties.PausedHandlerStartsNoDelivery : Prop :=
  ∀ (P : Params) (n : ℕ) (s : State), s.paused = true →
    (∀ (caller : Address) (B : Bytes) (pf : InclusionProof) (incl : Bool) (cs : List Callee),
      exec P n (.entry (.executeBundle caller B pf incl) cs) s = none) ∧
    ∀ (caller : Address) (B : Bytes) (req : List CallStatus) (cs : List Callee),
      exec P n (.entry (.unbundleBundle caller B req) cs) s = none

/-- **ONLY `pause` AND `unpause` WRITE `_paused`.** From every state, along every sequence of
transactions, with every target behaviour: the final pause flag is the last value written by a
committed `pause`/`unpause`, or the initial flag if none was. -/
def Properties.OnlyPauseAndUnpauseWritePaused : Prop :=
  ∀ (P : Params) (s : State) (txs : List Tx),
    (submitAll P s txs).1.paused = (pauseWrites (submitAll P s txs).2).getLastD s.paused

/-- **A PAUSE WRITE IS `pause` OR `unpause` BY THE OWNER (ONE STEP).** For one administrative call
(`adminStep`, which `exec` runs for an administrative entry at any depth): if it succeeds and logs a
pause write, it is `pause` or `unpause`, called by the owner of the state it ran in. The statement along
whole runs is `CommittedPauseWritesAreOwnerCalls`. -/
def Properties.PauseWritesAreOwnerCalls : Prop :=
  ∀ (caller : Address) (op : AdminOp) (s s' : State) (l : List Effect),
    adminStep caller op s = some (s', l) → pauseWrites l ≠ [] →
      caller = s.owner ∧ (op = .pause ∨ op = .unpause)

/-- **EVERY COMMITTED PAUSE WRITE IS BY THE OWNER OF THAT POINT OF THE LOG.** From every state, along
every sequence of transactions, with every target behaviour (administrative calls made re-entrantly by
a delivered call's target included): the final owner is the last owner written in the committed log, or
the initial owner if none was; and for every committed `pauseSet c v`, the caller `c` is the owner the
committed log gives just before it: the last owner written before it in the log, or the initial
owner. -/
@[headline] def Properties.CommittedPauseWritesAreOwnerCalls : Prop :=
  ∀ (P : Params) (s : State) (txs : List Tx),
    (submitAll P s txs).1.owner = (ownerWrites (submitAll P s txs).2).getLastD s.owner ∧
      ∀ (l₁ l₂ : List Effect) (c : Address) (v : Bool),
        (submitAll P s txs).2 = l₁ ++ .pauseSet c v :: l₂ → c = (ownerWrites l₁).getLastD s.owner

/-- **THE PAUSE WRITER FOLLOWS AN OWNERSHIP HANDOVER, ON A RUN.** From fresh storage, with `wParams`,
the run `wHandoverRun`: `wOwner` initializes as owner and pauses, then `transferOwnership(wUnbundler)`
and `acceptOwnership` by `wUnbundler` hand ownership over. The old owner's `unpause` then commits
nothing, and the new owner's commits. The committed log is exactly `initialized wOwner`, `ownerSet
wOwner`, `pauseSet wOwner true`, `pendingSet wUnbundler`, `ownerSet wUnbundler`, `pauseSet wUnbundler
false`, and the run ends unpaused with owner `wUnbundler`. -/
@[witness] def Properties.OwnerHandoverPauseWitness : Prop :=
  (submit wParams (submitAll wParams init (wHandoverRun.take 4)).1 (wAdmin .unpause)).2 = [] ∧
    (submitAll wParams init wHandoverRun).2 =
      [.initialized wOwner, .ownerSet wOwner, .pauseSet wOwner true, .pendingSet wUnbundler,
        .ownerSet wUnbundler, .pauseSet wUnbundler false] ∧
    (submitAll wParams init wHandoverRun).1.paused = false ∧
    (submitAll wParams init wHandoverRun).1.owner = wUnbundler

/-- **`initialize` RUNS AT MOST ONCE.** From every state, along every sequence of transactions, with
every target behaviour: the committed log holds at most one `initialize`, and none if the guard slot was
already set. -/
@[headline] def Properties.InitializeRunsAtMostOnce : Prop :=
  ∀ (P : Params) (s : State) (txs : List Tx),
    initCount (submitAll P s txs).2 ≤ 1 ∧
      (s.guardSet = true → initCount (submitAll P s txs).2 = 0)

/-- **THE PAUSE GATE, ON A RUN.** From fresh storage, with `wParams`: the owner initializes and
pauses; `verifyBundle` of `[1]` then commits and the bundle is `Verified`, while `executeBundle` of
`[1]` commits nothing; after `unpause`, the same `executeBundle` delivers the call, with the handler
unpaused. -/
@[witness] def Properties.PauseGateWitness : Prop :=
  (submitAll wParams init [wInit wOwner wOwner, wAdmin .pause, wVerify [1]]).1.paused = true ∧
    (submitAll wParams init [wInit wOwner wOwner, wAdmin .pause, wVerify [1]]).1.replay.bundle
      (wKeccak [1]) = .Verified ∧
    (submit wParams (submitAll wParams init [wInit wOwner wOwner, wAdmin .pause, wVerify [1]]).1
      wExecOne).2 = [] ∧
    (deliveries (submitAll wParams init
      [wInit wOwner wOwner, wAdmin .pause, wVerify [1], wAdmin .unpause, wExecOne]).2).map
        (fun d => (d.index, d.pausedNow)) = [(0, false)]

/-- **`initialize` ONCE, ON A RUN.** From fresh storage: `initialize(wOwner)` then
`initialize(wAnyone)`, both called by `wAnyone`, commit one `initialize`, and the owner is
`wOwner`. -/
@[witness] def Properties.InitializeOnceWitness : Prop :=
  initCount (submitAll wParams init [wInit wAnyone wOwner, wInit wAnyone wAnyone]).2 = 1 ∧
    (submitAll wParams init [wInit wAnyone wOwner, wInit wAnyone wAnyone]).1.owner = wOwner

/-- **THE PAUSE CHECK RUNS AT ENTRY (BOUNDARY).** From fresh storage, with `wParams`: `wUnbundler` is
initialized as owner and the two-call bundle `[2]` is verified; `unbundleBundle` of `[2]` by
`wUnbundler`, whose call-0 target calls `pause()` as the owner, commits both deliveries, the second one
with the handler paused, and the run ends paused. -/
@[countermodel] def Properties.OwnerPauseMidUnbundleWitness : Prop :=
  (deliveries (submitAll wParams init
      [wInit wUnbundler wUnbundler, wVerify [2], wUnbundlePausing]).2).map
      (fun d => (d.index, d.pausedNow)) = [(0, false), (1, true)] ∧
    (submitAll wParams init [wInit wUnbundler wUnbundler, wVerify [2], wUnbundlePausing]).1.paused
      = true

/-! ## (d) The single-call rule -/

/-- **VERIFY THEN UNBUNDLE DELIVERS EVERY CALL OF A PROVEN MULTI-CALL BUNDLE.** From fresh storage,
with `wParams` and the two-call bundle `[2]`, whose inclusion proof the oracle accepts: `executeBundle`
commits nothing (`L1InteropHandler.sol:85`), while
`verifyBundle` then `unbundleBundle` by the bundle's unbundler commits deliveries of calls `0` and `1`,
both on the unbundle route. -/
@[countermodel] def Properties.VerifyThenUnbundleDeliversEveryCall : Prop :=
  (submitAll wParams init [wExecTwo]).2 = [] ∧
    (deliveries (submitAll wParams init [wVerify [2], wUnbundleTwo]).2).map
      (fun d => (d.route, d.index)) = [(.unbundle, 0), (.unbundle, 1)]

/-- **WITH SINGLE-CALL EVIDENCE, EVERY DELIVERY IS CALL 0 OF A ONE-CALL BUNDLE, UNPAUSED.** From fresh
storage, along every sequence of transactions whose committed verifications all have one-call bundles:
every committed delivery is call `0` of the one-call bundle its bytes decode to, made while the handler
was not paused, or its bytes collide under keccak with a committed verification's bytes. -/
@[headline] def Properties.SingleCallEvidenceDeliversOneCall : Prop :=
  ∀ (P : Params) (txs : List Tx),
    (∀ v ∈ verifications (submitAll P init txs).2, v.bundle.calls.length = 1) →
    ∀ d ∈ deliveries (submitAll P init txs).2,
      (d.index = 0 ∧ d.pausedNow = false ∧
          ∃ b, P.codec.decode d.bytes = some b ∧ b.calls.length = 1) ∨
        ∃ v ∈ verifications (submitAll P init txs).2, KeccakClash P.codec v.bytes d.bytes

/-- **THE SINGLE-CALL PREMISE HOLDS ON A DELIVERING RUN.** From fresh storage, with `wParams`, the run
`[wExecOne]` commits one verification, of a one-call bundle, and one delivery. -/
@[witness] def Properties.SingleCallEvidenceWitness : Prop :=
  (verifications (submitAll wParams init [wExecOne]).2).map (fun v => v.bundle.calls.length) = [1] ∧
    (deliveries (submitAll wParams init [wExecOne]).2).length = 1

/-! ## (e) At most once, across routes -/

/-- **EVERY L1 RUN IS A RUN OF THE PIN'S RE-ENTRANT MODEL.** For every deployment, start state and
sequence of transactions, some sequence of transactions of `InteropHandlerBase` `Reentrancy`
(`.deployed`) leads from the start state's replay mappings to the final state's, committing exactly the
L1 log's deliveries (as `delivered hash index`) and `BundleExecuted` events, in order. -/
def Properties.L1RunsProjectToPinRuns : Prop :=
  ∀ (P : Params) (s : State) (txs : List Tx), ∃ txs' : List Contracts.InteropHandler.Tx,
    Contracts.InteropHandler.submitAll .deployed s.replay txs' =
      ((submitAll P s txs).1.replay, (submitAll P s txs).2.filterMap Effect.toPin)

/-- **EACH CALL IS DELIVERED AT MOST ONCE.** From every state, along every sequence of transactions,
with every target behaviour: no pair `(bundleHash, index)` is delivered twice, whether by
`executeBundle`, by `unbundleBundle`, or by both, in one transaction or several. -/
@[headline] def Properties.EachCallDeliveredAtMostOnce : Prop :=
  ∀ (P : Params) (s : State) (txs : List Tx),
    ((deliveries (submitAll P s txs).2).map (fun d => (d.hash, d.index))).Nodup

/-- **RE-ENTRY CANNOT DELIVER A CALL AGAIN, ON A RUN.** From fresh storage, with `wParams`, after
`verifyBundle` of `[1]`: an `unbundleBundle` of `[1]` executing call 0, whose target re-enters
`unbundleBundle` with the same request and then `executeBundle` of `[1]` and catches both failures,
commits exactly one delivery, of call 0; if the target does not catch them, the transaction commits
nothing. -/
@[witness] def Properties.ReentrantRedeliveryRefusedWitness : Prop :=
  (deliveries (submitAll wParams init [wVerify [1], wUnbundleReentering true]).2).map
      (fun d => (d.hash, d.index)) = [(wKeccak [1], 0)] ∧
    (submit wParams (submitAll wParams init [wVerify [1]]).1 (wUnbundleReentering false)).2 = []

/-- **THE CALL STATUS RECORDS THE DELIVERIES.** From fresh storage, along every sequence of
transactions: `callStatus[h][i]` is `Executed` if and only if a committed delivery has hash `h` and
index `i`. -/
@[headline] def Properties.CallStatusRecordsDeliveries : Prop :=
  ∀ (P : Params) (txs : List Tx) (h : Word) (i : ℕ),
    (submitAll P init txs).1.replay.call h i = .Executed ↔
      ∃ d ∈ deliveries (submitAll P init txs).2, d.hash = h ∧ d.index = i

end Contracts.L1WithdrawalGate
