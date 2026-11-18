import EraSpec.Contracts.InteropHandlerBase.Specs.BundleStatusMachineStrong
import EraSpec.Contracts.InteropHandlerBase.Specs.ReentrancyStrong
import EraSpec.Contracts.InteropHandlerBase.Specs.SelfCallAuthorityFaithful
import EraSpec.Protocol.InteropAtomicity.Specs.Refund
import EraSpec.Protocol.InteropAtomicity.Specs.RootImport

/-!
# Model: what an atomic leg can still do on its destination (execution liveness)

Source: era-contracts at the pin `c67894b9`. Paths are relative to `l1-contracts/contracts/`.
`UPG` is the upgrade-simplification tree `e561b9cc2`; `main` and `v35` are the current heads
`70096e2` (branch `main`) and `b17415d20` (branch `draft/v0.35.0`). They are cited only in "At the
later trees" below; the model is the pin's.

**This file is definitions only.** Statements are in
`EraSpec.Protocol.InteropAtomicity.Properties.ExecutionLiveness`, proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.ExecutionLiveness`.

The destination model is `Contracts.InteropHandler` (`Contracts/InteropHandlerBase/Specs/Reentrancy.lean`,
topic `Reentrancy`): the handler's `bundleStatus` and `callStatus`, its four entry points, every
re-entrant behaviour of every target as a finite `Callee` tree, `Option` rollback. Topic
`BundleStatusMachineStrong` (same folder) has the safety side of an atomic leg's position there:
along a run in which no call presents a valid inclusion proof for its hash, the hash stays
`Unreceived` or `FullyExecuted` (`NoProofKeepsBundleInAtomicMachine`), and an atomic leg's hash gets
no valid proof unless one of two named clashes (`AtomicLegStaysAtomicAtDestinationOrClash`). This
file asks what such a leg can still do: which entry points can deliver it, what a call that always
reverts does to it, who may execute it, and when each route is enabled.

## The routes at the pin

    executeBundle (interop/interop-handler/InteropHandlerBase.sol:86-147)
      require(status == Unreceived || status == Verified)                       // :117-120
      if (status != Verified) _verifyBundle(...)                                // :123
    verifyBundle (:150-161)            require(status == Unreceived); _verifyBundle(...)   // :157-160
    unbundleBundle (:164-231)          require(status == Verified || status == Unbundled)  // :195
    _verifyBundle (:296-316)
      require(_proof.message.sender == L2_INTEROP_CENTER_ADDR, ..);             // :302-305
      _proof.message.data = bytes.concat(BUNDLE_IDENTIFIER, _bundle);           // :308
      require(_proveInclusion(_proof), MessageNotIncluded());                   // :310
      bundleStatus[_bundleHash] = BundleStatus.Verified;                        // :312
    executeAtomicBundle (interop/interop-handler/L2InteropHandler.sol:49-100)
      require(status == BundleStatus.Unreceived, BundleAlreadyProcessed(bundleHash));      // :79
      IAtomicFlowManager(L2_ATOMIC_FLOW_MANAGER_ADDR).requireFlowFinalized(bundleHash, _finality); // :83

`Verified`, and with it `unbundleBundle`, is reached only through `_verifyBundle`, so only with a
valid inclusion proof for the hash. The source appends an atomic bundle to the flow manager instead
of publishing it (`interop/InteropCenter.sol:646-657`), and the NatSpec of `executeAtomicBundle`
(`L2InteropHandler.sol:39-42`) calls it the atomic bundle's only execution entry point, with no
atomic verify path. `executeAtomicBundle` needs `Unreceived`, runs every call in one frame and
reverts if any call reverts.

## Modelling choices

* **Which calls present a valid proof.** As in `BundleStatusMachineStrong`, an inclusion proof's
  verdict is the boolean an `executeBundle` or `verifyBundle` call carries. The statements take
  `NoProofRun h txs` (no call of the run, at any depth, presents a valid proof for `h`), or, for an
  atomic dispatch of a source run, `SoundProofRun (PublishedHash ..)` with the source's
  publication premise `PublishesOnlyPublicDispatches`, as `AtomicLegStaysAtomicAtDestinationOrClash`
  does.
* **A call that always reverts.** `AtomicAttemptReverts h` says that every `executeAtomicBundle`
  of a bundle with hash `h`, at top level or nested, has among the targets of its first `calls`
  calls one that reverts from every state at every budget (`Contracts.InteropHandler.AlwaysReverts`,
  topic `ReentrancyStrong`): for example the leaf `Callee.reverts`, or any target whose own
  continuation ends in a revert, whatever it calls first (`EndsInRevertAlwaysReverts`). In the
  source such a target is, for example, a call to an
  address with no code (decoding its empty return data as the selector reverts,
  `InteropHandlerBase.sol:282-287`) or to a contract whose `receiveMessage` always reverts. The
  premise is per attempt, over every transaction of the run and every nested call.
* **Permissions.** `Contracts.InteropHandler` omits the execution permission as a reject-only
  check. The statements about it, (f) of the Properties file, are made on the gate model of topic
  `SelfCallAuthorityFaithful` (`AttackVectors.SelfCallAuthority.Faithful`, same folder) instead:
  `Reaches pinnedTable` lists every call the handler receives at an entry point, a direct call or a
  self-call made by `receiveMessage` (`InteropHandlerBase.sol:334-362`, which dispatches on
  `executeBundle`, `verifyBundle` and `unbundleBundle` only, `:351-359`), and `InnerGate` is the
  deployed permission gate. The two models are not composed: (f) says which calls pass the gate,
  not what `exec` does after it. The center stores any `executionAddress` that `parseEvmV1` parses
  (`interop/InteropCenter.sol:811-820`, `:885-891`), whatever its chain.
* **The unbundler.** `unbundleBundle` also checks its caller against the bundle's
  `unbundlerAddress` (`InteropHandlerBase.sol:170-184`), which the handler model omits as well; the
  statements about the unbundled route hold for a caller that passes that check (`sendBundle` and
  `sendMessage` make the sender the unbundler when none is given, `interop/InteropCenter.sol:231-233`,
  `:314-316`).
* **Gate verdict.** `requireFlowFinalized` is a static call (`atomic-interop/IAtomicFlowManager.sol:53`),
  so its verdict is the input bit `gateOk`; `true` is "the flow is finalized and the executor
  presents the proofs" (`Contracts.Atomicity.FlowFinalizedBy`).

## At the later trees

At `UPG`, `main` and `v35` the L2 handler has other entry points:

* `executeBundle` and `verifyBundle` are on `L1InteropHandler` only
  (`interop/interop-handler/L1InteropHandler.sol:81`, `:103` at all three). On L2 the entry points
  are `executeAtomicBundle`, a new `verifyAtomicBundle` that runs the flow gate and marks the bundle
  `Verified` (`L2InteropHandler.sol:73-82` at `main`, `:83-92` at `v35` and `UPG`), and
  `unbundleBundle` (`InteropHandlerBase.sol:113` at all three). `executeAtomicBundle` accepts a
  `Verified` bundle (`_requireExecutable`, `InteropHandlerBase.sol:282-287` at `v35`) and then skips
  the gate (`L2InteropHandler.sol:62-65` at `main`, `:72-75` at `v35` and `UPG`). So an atomic leg
  has a verify-then-unbundle route there.
* `receiveMessage`'s execute selector dispatches to `executeAtomicBundle`, after checking the
  wrapped sender against the bundle's `executionAddress` (`_requireRescueExecutionAllowed`), and
  its verify selector to `verifyAtomicBundle` (`L2InteropHandler.sol:89-132` at `main`, `:99-142`
  at `v35` and `UPG`).

Every statement of the Properties file is about the pin's handler; those of (d), (e) and (f) turn
on the routes that differ, and nothing here is claimed for these trees.
-/

namespace Contracts.ExecutionLiveness

open Contracts.InteropHandler (Entry Callee Frame Tx BundleHash AlwaysReverts)
open AttackVectors.BundleStatusMachine (Status CallStatus)

/-! ## Predicates on every entry-point call of a run, with the targets it delivers to -/

/-- **EVERY ENTRY-POINT CALL OF A TARGET'S BEHAVIOUR SATISFIES `Q`**, at every depth: each
`Callee.calls e inner _ next` node has `Q e inner`, and so do the targets `inner` of the calls that
frame delivers, and the rest `next` of the behaviour. Unlike `Callee.Mentions` (topic
`BundleStatusMachineStrong`), `Q` also sees the targets each call delivers to. -/
inductive EveryEntry (Q : Entry → List Callee → Prop) : Callee → Prop
  | returns : EveryEntry Q .returns
  | reverts : EveryEntry Q .reverts
  | calls {e : Entry} {inner : List Callee} {caught : Bool} {next : Callee} :
      Q e inner → (∀ c ∈ inner, EveryEntry Q c) → EveryEntry Q next →
      EveryEntry Q (.calls e inner caught next)

/-- **EVERY ENTRY-POINT CALL OF A TRANSACTION SATISFIES `Q`**: the top-level call and every call
its delivered targets make, at every depth. -/
def TxEvery (Q : Entry → List Callee → Prop) (t : Tx) : Prop :=
  Q t.entry t.callees ∧ ∀ c ∈ t.callees, EveryEntry Q c

/-- **AN ATOMIC ATTEMPT ON `h` MEETS A TARGET THAT ALWAYS REVERTS.** An `executeAtomicBundle` of a
bundle with hash `h` has, among the targets of its `calls` calls, one that reverts from every state
at every budget in the deployed order. Other entry-point calls are unconstrained. -/
def AtomicAttemptReverts (h : BundleHash) : Entry → List Callee → Prop
  | .executeAtomicBundle b _, cs => b.hash = h → ∃ c ∈ cs.take b.calls, AlwaysReverts .deployed c
  | _, _ => True

/-! ## The unbundled route, as a function of the request -/

/-- What `unbundleBundle`'s first loop (`InteropHandlerBase.sol:200-219`) records for one call, from
its recorded status and the requested one: a requested execution is recorded `Executed`, a requested
cancellation `Cancelled`, anything else leaves the call as it was. -/
def requestedStatus : CallStatus → Option CallStatus → CallStatus
  | _, some .Executed => .Executed
  | _, some .Cancelled => .Cancelled
  | old, _ => old

/-- **A REQUEST THE FIRST LOOP ACCEPTS.** Executions are requested only for `Unprocessed` calls
(`CallNotExecutable`, `:207`) and cancellations only for calls not yet `Executed`
(`CallAlreadyExecuted`, `:212`). -/
def RequestValid (s : Contracts.InteropHandler.State) (h : BundleHash)
    (req : List CallStatus) : Prop :=
  ∀ (j : ℕ) (hj : j < req.length),
    (req[j] = .Executed → s.call h j = .Unprocessed) ∧ (req[j] = .Cancelled → s.call h j ≠ .Executed)

/-- The state after a successful `unbundleBundle` of `h` with request `req`: the bundle is
`Unbundled` (`:198`) and each call is recorded as requested. -/
def applyRequest (s : Contracts.InteropHandler.State) (h : BundleHash)
    (req : List CallStatus) : Contracts.InteropHandler.State where
  bundle := fun h' => if h' = h then .Unbundled else s.bundle h'
  call := fun h' j => if h' = h then requestedStatus (s.call h j) req[j]? else s.call h' j

/-- The request that cancels call `i` and executes every other call of an `n`-call bundle. -/
def escapeRequest (n i : ℕ) : List CallStatus :=
  (List.range n).map fun j => if j = i then .Cancelled else .Executed

/-! ## Witness data

On the destination, a handler bundle is its hash and its number of calls. -/

/-- `verifyBundle` of a bundle `⟨h, n⟩` with a valid inclusion proof. -/
def wVerify (h : BundleHash) (n : ℕ) : Tx := ⟨1, .verifyBundle ⟨h, n⟩ true, []⟩

/-- An attempt at the atomic leg `h` (one call, gate passing) whose target reverts. -/
def wRevertingAttempt (h : BundleHash) : Tx := ⟨5, .executeAtomicBundle ⟨h, 1⟩ true, [.reverts]⟩

/-- An attempt at the atomic leg `h` (two calls, gate passing) whose first target executes the
public bundle `⟨3, 1⟩` with a valid proof, and whose second target reverts: the nested execution
is undone with the attempt. -/
def wNestedRevertingAttempt (h : BundleHash) : Tx :=
  ⟨8, .executeAtomicBundle ⟨h, 2⟩ true,
    [.calls (.executeBundle ⟨3, 1⟩ true) [] false .returns, .reverts]⟩

/-- The same nested work at top level: `executeBundle` of the public bundle `⟨3, 1⟩` with a valid
proof. It commits on its own. -/
def wPublicRun : Tx := ⟨3, .executeBundle ⟨3, 1⟩ true, []⟩

/-- The verify-then-unbundle run of a public bundle `b` that cancels call `i`. -/
def escapeRun (b : Contracts.InteropHandler.Bundle) (i : ℕ) : List Tx :=
  [⟨1, .verifyBundle b true, []⟩, ⟨b.calls + 2, .unbundleBundle b (escapeRequest b.calls i), []⟩]

end Contracts.ExecutionLiveness
