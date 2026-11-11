import EraSpec.Contracts.InteropHandlerBase.Specs.BundleStatusMachineStrong

/-!
# Properties: the bundle status machine, derived from the handler's guards

Statements about `EraSpec.Contracts.InteropHandlerBase.Specs.BundleStatusMachineStrong` and the
handler model of topic `Reentrancy`. Proofs are in
`EraSpec.Contracts.InteropHandlerBase.Proofs.BundleStatusMachineStrong`.

These strengthen three groups of topic `BundleStatusMachine`, whose statements are facts about
the abstract relations alone.

## (a) The whole-bundle write does not read the call status (`wholeBundle_route_does_not_check_callStatus`)

* `WholeBundleWriteIgnoresCallStatus`: the deployed writes before the calls record every call of
  the bundle `Executed` from every state, leave every other call alone, are not a `CallStep`
  edge on a call already `Executed`, and give the same result whatever the bundle's own call
  statuses were.
* `CallStatusDoesNotStopWholeBundleRedelivery`: from a state where the bundle is admitted but a
  call is already `Executed`, the call is delivered again. Only the bundle status stops it.
* `AdmittedBundleHasOnlyUnprocessedCalls`: the deployed guards never reach such a state — from
  every `CallsClosed` state (fresh storage is one), an admitted bundle's calls are all
  `Unprocessed`, so the unread write is the `CallStep.execute` edge.

## (b) A verified bundle is never executed atomically (`verified_blocks_atomic_execution`)

* `VerifiedBundleNeverExecutesAtomically`: no path returns to `Unreceived` from `Verified`; after
  any run from a state where the hash is `Verified`, every `executeAtomicBundle` of that hash
  reverts; and `executeBundle` stays available there.

## (c) The atomic sub-machine, derived (`atomic_reach_two_states`, `atomic_never_unbundled`, `atomic_delivery_terminal`)

* `AtomicMachineIsDeployedMachineWithoutVerify`: `AtomicStep`'s edge is a `Step` edge, and
  `AtomicReach` from `Unreceived` is exactly `Reach` minus `Verified` and `Unbundled`.
* `NoProofKeepsBundleInAtomicMachine`: in the handler model, along any run (re-entrant calls at
  any depth included) in which no call presents a valid inclusion proof for hash `h`, the status
  of `h` moves along `AtomicReach`. This is the content `AtomicStep` assumed, now derived from
  the deployed guards with the premise named.
* `ProofForAtomicHashOpensUnbundledRoute`: the premise is satisfiable, and load-bearing: with a
  valid proof, `verifyBundle` then `unbundleBundle` reach `Unbundled` and deliver the call
  through the per-call route, after which atomic execution commits nothing.
* `AtomicLegStaysAtomicAtDestinationOrClash`: the source side discharges the premise. For an
  atomic dispatch of a deployed `InteropCenter` run, at any destination whose valid proofs are
  all for messages published to L1, the leg's bundle hash stays in the atomic sub-machine,
  unless a cross-sender salt clash (`InteropCenter.AtomicBytesNeverPublished`) or a keccak
  collision on two named preimages. `AtomicLegAtDestinationWitness` meets every premise on the
  honest witness chain, with a valid proof in the run, and both clashes false.
-/

namespace Contracts.InteropHandler

open AttackVectors.BundleStatusMachine (Status CallStatus Step Reach CallStep CallReach
  AtomicStep AtomicReach)
open AttackVectors.BundleHashEncoding (HashCollision abiEncode)

/-! ## (a) The whole-bundle write does not read the call status -/

/-- **THE WHOLE-BUNDLE WRITE DOES NOT READ THE CALL STATUSES IT OVERWRITES.** In the deployed
order, the writes `executeBundle` and `executeAtomicBundle` make before their calls
(`bundleStatus = FullyExecuted`, then `callStatus[bundleHash][i] = Executed` for every
`i < calls.length`, `:126-132`, `L2InteropHandler.sol:86-90`):
* record every call `i < b.calls` of `b.hash` as `Executed`, from every state;
* leave every other call status as it was;
* on a call that is already `Executed` are not an edge of the per-call machine — `CallStep` has
  no `Executed → Executed` edge, the write performs one;
* produce a state that does not depend on the statuses of `b.hash`'s calls `0, …, b.calls - 1`:
  two states that differ only there are written to the same state. -/
def Properties.WholeBundleWriteIgnoresCallStatus : Prop :=
  (∀ (b : Bundle) (s : State) (i : ℕ), i < b.calls →
      (beforeCalls .deployed b s).call b.hash i = .Executed) ∧
  (∀ (b : Bundle) (s : State) (h : BundleHash) (i : ℕ), ¬ (h = b.hash ∧ i < b.calls) →
      (beforeCalls .deployed b s).call h i = s.call h i) ∧
  (∀ (b : Bundle) (s : State) (i : ℕ), i < b.calls → s.call b.hash i = .Executed →
      ¬ CallStep (s.call b.hash i) ((beforeCalls .deployed b s).call b.hash i)) ∧
  (∀ (b : Bundle) (s s' : State), s.bundle = s'.bundle →
      (∀ h i, ¬ (h = b.hash ∧ i < b.calls) → s.call h i = s'.call h i) →
      beforeCalls .deployed b s = beforeCalls .deployed b s')

/-- **SO ONLY THE BUNDLE STATUS STOPS A SECOND PAYMENT.** From any state in which a bundle `b`
with at least one call is admitted by a whole-bundle route while its call 0 is already recorded
`Executed`, the deployed handler delivers call 0 again — `executeBundle(b)` from `Verified`, with
or without a valid proof, and `executeAtomicBundle(b)` from `Unreceived`, each with returning
targets. Nothing at the call level stops it. -/
def Properties.CallStatusDoesNotStopWholeBundleRedelivery : Prop :=
  ∀ (s : State) (b : Bundle) (ok : Bool), 0 < b.calls → s.call b.hash 0 = .Executed →
    (s.bundle b.hash = .Verified →
      Effect.delivered b.hash 0 ∈
        (submit .deployed s ⟨b.calls + 2, .executeBundle b ok, List.replicate b.calls .returns⟩).2) ∧
    (s.bundle b.hash = .Unreceived →
      Effect.delivered b.hash 0 ∈
        (submit .deployed s
          ⟨b.calls + 2, .executeAtomicBundle b true, List.replicate b.calls .returns⟩).2)

/-- **AND THE DEPLOYED GUARDS NEVER REACH SUCH A STATE.** Fresh storage satisfies `CallsClosed`.
From every state satisfying it, after any sequence of transactions: a bundle that a whole-bundle
route admits (`Unreceived` or `Verified`) has every call `Unprocessed`, so on each of its calls the
unread write is the edge `CallStep.execute`. -/
def Properties.AdmittedBundleHasOnlyUnprocessedCalls : Prop :=
  CallsClosed init ∧
  ∀ (s : State) (txs : List Tx), CallsClosed s →
    ∀ (b : Bundle), ((submitAll .deployed s txs).1.bundle b.hash = .Unreceived ∨
        (submitAll .deployed s txs).1.bundle b.hash = .Verified) →
      ∀ i, (submitAll .deployed s txs).1.call b.hash i = .Unprocessed ∧
        (i < b.calls → CallStep ((submitAll .deployed s txs).1.call b.hash i)
          ((beforeCalls .deployed b (submitAll .deployed s txs).1).call b.hash i))

/-! ## (b) A verified bundle is never executed atomically -/

/-- **ONCE VERIFIED, NEVER EXECUTED ATOMICALLY — WHILE THE PUBLIC ROUTE STAYS OPEN.**
* No path of the deployed machine returns from `Verified` to `Unreceived`.
* In the handler model, from any state in which bundle hash `b.hash` is `Verified`, after any
  sequence of transactions (re-entrant calls included), every `executeAtomicBundle` of a bundle
  with that hash reverts, at every budget, with every gate verdict and every target.
* From such a state `executeBundle(b)` with returning targets delivers each of `b`'s calls and
  executes `b`, with or without a valid proof (none is consulted once `Verified`). So the block
  is specific to the atomic entry point; the abstract `Step` cannot say so, since its
  `executeAtomic` and `executeFresh` edges are the same pair of states. -/
def Properties.VerifiedBundleNeverExecutesAtomically : Prop :=
  ¬ Reach .Verified .Unreceived ∧
  (∀ (s : State) (txs : List Tx) (b : Bundle), s.bundle b.hash = .Verified →
    ∀ (n : ℕ) (ok : Bool) (cs : List Callee),
      exec .deployed n (.entry (.executeAtomicBundle b ok) cs) (submitAll .deployed s txs).1 =
        none) ∧
  (∀ (s : State) (b : Bundle) (ok : Bool), s.bundle b.hash = .Verified →
    (submit .deployed s ⟨b.calls + 2, .executeBundle b ok, List.replicate b.calls .returns⟩).2 =
      (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash])

/-! ## (c) The atomic sub-machine, derived -/

/-- **THE ATOMIC SUB-MACHINE IS THE DEPLOYED MACHINE WITHOUT `verify`.** `AtomicStep`'s edge is an
edge of `Step`, and from `Unreceived` the atomic machine reaches exactly the states `Step` reaches
other than `Verified` and `Unbundled` — the two that need the `verify` edge. -/
def Properties.AtomicMachineIsDeployedMachineWithoutVerify : Prop :=
  (∀ a b : Status, AtomicStep a b → Step a b) ∧
  ∀ t : Status, AtomicReach .Unreceived t ↔ (Reach .Unreceived t ∧ t ≠ .Verified ∧ t ≠ .Unbundled)

/-- **WITHOUT A VALID PROOF FOR ITS HASH, A BUNDLE STAYS IN THE ATOMIC SUB-MACHINE.** In the
deployed order, from any state in which bundle hash `h` is `Unreceived` or `FullyExecuted`, along
any sequence of transactions in which no entry-point call — at top level or re-entrant, at any
depth — presents a valid inclusion proof for `h`, the status of `h` moves along `AtomicReach`. So
it is never `Verified` and never `Unbundled`. This derives the atomic sub-machine from the
deployed guards; the one premise is the one `AtomicStep`'s definition assumed. -/
def Properties.NoProofKeepsBundleInAtomicMachine : Prop :=
  ∀ (s : State) (txs : List Tx) (h : BundleHash),
    (s.bundle h = .Unreceived ∨ s.bundle h = .FullyExecuted) → NoProofRun h txs →
      AtomicReach (s.bundle h) ((submitAll .deployed s txs).1.bundle h)

/-- **THE NO-PROOF PREMISE IS SATISFIABLE, AND LOAD-BEARING.** From fresh storage:
* runs with no valid proof for hash `3` exist, atomic and re-entrant ones included, and
  `executeAtomicBundle(wC)` executes `wC`;
* with a valid proof for hash `3` (so the premise fails), `verifyBundle(wC)` then
  `unbundleBundle(wC)` reach `Unbundled` and deliver `wC`'s call through the per-call route, and
  a later `executeAtomicBundle(wC)` commits nothing. -/
def Properties.ProofForAtomicHashOpensUnbundledRoute : Prop :=
  NoProofRun wC.hash [wRunC] ∧ NoProofRun wC.hash [wReenterAtomic true] ∧
    (submitAll .deployed init [wRunC]).2 = [.delivered 3 0, .executed 3] ∧
    ¬ NoProofRun wC.hash [wVerifyC, wUnbundleC] ∧
    (submitAll .deployed init [wVerifyC, wUnbundleC]).1.bundle 3 = .Unbundled ∧
    (submitAll .deployed init [wVerifyC, wUnbundleC]).2 = [.delivered 3 0] ∧
    (submitAll .deployed init [wVerifyC, wUnbundleC, wRunC]).2 = [.delivered 3 0]

/-- **THE SOURCE SIDE DISCHARGES THE PREMISE: AN ATOMIC LEG STAYS ATOMIC AT THE DESTINATION, OR A
NAMED CLASH.** Let `S` be a state of a run of the deployed `InteropCenter` on chain `P` from fresh
storage, whose encoder separates its bundles (`EncInjOn`, `SOL-ABI`), and `d` an atomic dispatch
of that run. Let `pubs` be the bundle messages published to L1, of which chain `P`'s are the bytes
of its public dispatches. Then at any destination storage `s` where `d`'s bundle hash is
`Unreceived`, along any sequence of transactions whose valid inclusion proofs are all for
published messages, that hash moves along `AtomicReach` — or two different senders of the run
used one salt and keccak collides on their packed preimages (the clash of
`InteropCenter.AtomicBytesNeverPublished`, with a public dispatch), or keccak collides on `d`'s
bundle-hash preimage and that of a named published message. -/
def Properties.AtomicLegStaysAtomicAtDestinationOrClash : Prop :=
  ∀ (P : Contracts.InteropCenter.Params) (S : Contracts.InteropCenter.State),
    Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed P
      Contracts.InteropCenter.init S →
    Contracts.InteropCenter.EncInjOn P.enc (S.log.map Contracts.InteropCenter.Dispatch.bundle) →
    ∀ (pubs : List (UInt256 × List UInt8)), PublishesOnlyPublicDispatches P S.log pubs →
    ∀ d ∈ S.log, d.isAtomic = true →
    ∀ (s : State) (txs : List Tx),
      s.bundle (Contracts.InteropCenter.bundleHash P d.bundle) = .Unreceived →
      SoundProofRun (PublishedHash P.keccak pubs) txs →
      AtomicReach .Unreceived
          ((submitAll .deployed s txs).1.bundle (Contracts.InteropCenter.bundleHash P d.bundle))
      ∨ (∃ d' ∈ S.log, d'.isAtomic = false ∧ Contracts.InteropCenter.CrossSenderSaltClash P d d')
      ∨ (∃ p ∈ pubs, HashCollision P.keccak (Contracts.InteropCenter.bundlePreimage P d.bundle)
            (abiEncode p.1.val p.2))

/-- **THE CROSS-CONTRACT PREMISES HOLD ON A NONTRIVIAL RUN, AND BOTH CLASHES ARE FALSE ON IT.** On
the honest InteropCenter witness chain (`wParams`, run `wS3`: atomic leg `wD1`, public bundle
`wD2`), with `wD2`'s bytes as the one published message: every premise of
`AtomicLegStaysAtomicAtDestinationOrClash` holds for `d = wD1` and the destination run
`wDestRun` from fresh storage. That run does present a valid proof — for `wD2`'s hash, so it is
not a no-proof run for that hash — and it ends with `wD1`'s hash `FullyExecuted` and `wD2`'s
`Verified`. Neither clash disjunct holds. -/
def Properties.AtomicLegAtDestinationWitness : Prop :=
  Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed Contracts.InteropCenter.wParams
      Contracts.InteropCenter.init Contracts.InteropCenter.wS3 ∧
    Contracts.InteropCenter.EncInjOn Contracts.InteropCenter.wParams.enc
      (Contracts.InteropCenter.wS3.log.map Contracts.InteropCenter.Dispatch.bundle) ∧
    PublishesOnlyPublicDispatches Contracts.InteropCenter.wParams Contracts.InteropCenter.wS3.log
      [(Contracts.InteropCenter.wParams.chainId,
        Contracts.InteropCenter.wParams.enc Contracts.InteropCenter.wD2.bundle)] ∧
    Contracts.InteropCenter.wD1 ∈ Contracts.InteropCenter.wS3.log ∧
    Contracts.InteropCenter.wD1.isAtomic = true ∧
    init.bundle (Contracts.InteropCenter.bundleHash Contracts.InteropCenter.wParams
      Contracts.InteropCenter.wD1.bundle) = .Unreceived ∧
    SoundProofRun (PublishedHash Contracts.InteropCenter.wParams.keccak
      [(Contracts.InteropCenter.wParams.chainId,
        Contracts.InteropCenter.wParams.enc Contracts.InteropCenter.wD2.bundle)]) wDestRun ∧
    ¬ NoProofRun (Contracts.InteropCenter.bundleHash Contracts.InteropCenter.wParams
      Contracts.InteropCenter.wD2.bundle) wDestRun ∧
    (submitAll .deployed init wDestRun).1.bundle (Contracts.InteropCenter.bundleHash
      Contracts.InteropCenter.wParams Contracts.InteropCenter.wD1.bundle) = .FullyExecuted ∧
    (submitAll .deployed init wDestRun).1.bundle (Contracts.InteropCenter.bundleHash
      Contracts.InteropCenter.wParams Contracts.InteropCenter.wD2.bundle) = .Verified ∧
    ¬ Contracts.InteropCenter.CrossSenderSaltClash Contracts.InteropCenter.wParams
      Contracts.InteropCenter.wD1 Contracts.InteropCenter.wD2 ∧
    ¬ HashCollision Contracts.InteropCenter.wParams.keccak
      (Contracts.InteropCenter.bundlePreimage Contracts.InteropCenter.wParams
        Contracts.InteropCenter.wD1.bundle)
      (abiEncode Contracts.InteropCenter.wParams.chainId.val
        (Contracts.InteropCenter.wParams.enc Contracts.InteropCenter.wD2.bundle))

/-- **THE PREMISES OF (a) AND (b) ARE SATISFIABLE.** `wStaleCalls` (bundle `3` `Verified` with
call 0 already `Executed`) meets the premises of `CallStatusDoesNotStopWholeBundleRedelivery`
for `wC`, fails `CallsClosed`, and `executeBundle(wC)` re-delivers call 0 from it. After
`verifyBundle(wC)` from fresh storage, hash `3` is `Verified` (the premise of
`VerifiedBundleNeverExecutesAtomically`), and from there `executeBundle(wC)` with no valid
proof executes `wC` while `executeAtomicBundle(wC)` commits nothing. -/
def Properties.StatusMachineStrongWitness : Prop :=
  wStaleCalls.bundle wC.hash = .Verified ∧ wStaleCalls.call wC.hash 0 = .Executed ∧
    ¬ CallsClosed wStaleCalls ∧
    (submit .deployed wStaleCalls wExecuteC).2 = [.delivered 3 0, .executed 3] ∧
    (submitAll .deployed init [wVerifyC]).1.bundle wC.hash = .Verified ∧
    (submitAll .deployed init [wVerifyC, wExecuteC]).2 = [.delivered 3 0, .executed 3] ∧
    (submitAll .deployed init [wVerifyC, wRunC]).2 = []

end Contracts.InteropHandler
