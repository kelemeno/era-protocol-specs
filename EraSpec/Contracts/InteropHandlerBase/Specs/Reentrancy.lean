import EraSpec.Contracts.InteropHandlerBase.Specs.BundleStatusMachine
import EraSpec.Core.Word

/-!
# Model: re-entrant bundle execution in the interop handlers (the engine)

Source: era-contracts `draft/v0.35.0` at `b17415d20`, `l1-contracts/contracts/`. `IHB` is
`interop/interop-handler/InteropHandlerBase.sol`, `L1` is `interop/interop-handler/L1InteropHandler.sol`,
`L2` is `interop/interop-handler/L2InteropHandler.sol`; every line number is at `b17415d20`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.InteropHandlerBase.Properties.Reentrancy` and are proved in
`EraSpec.Contracts.InteropHandlerBase.Proofs.Reentrancy`.

## Two layers, one topic

This file is the topic's **engine** (namespace `Contracts.InteropHandler`): one re-entrant execution
semantics `exec` over a set of four entry points. `Specs/ReentrancyAtV35.lean` (namespace
`Contracts.InteropHandlerAtV35`) is the topic's **`b17415d20` layer**: the entry points of each
handler (`EntryAtV35 ℓ`, one layer per tree) and their semantics `execAtV35`, linked to the engine by
the proved refinement `ExecMatchesPinAtV35`/`SubmitAllMatchesPinAtV35` (a v35 frame runs as its
translation in `exec`, in the deployed order). The topic's headlines are stated on that layer and
proved through the translation from the engine statements in `Properties/Reentrancy.lean`.

The engine's entry points at `b17415d20`:

| engine entry | `b17415d20` |
|---|---|
| `executeBundle b ok` | L1 `executeBundle` (`L1:81-98`); the layer also sends L2 `executeAtomicBundle` (`L2:61-78`) here |
| `verifyBundle b ok` | L1 `verifyBundle` (`L1:103-110`); the layer also sends L2 `verifyAtomicBundle` (`L2:83-92`) here |
| `unbundleBundle b req` | `unbundleBundle` (`IHB:113-175`), both layers |
| `executeAtomicBundle b ok` | none: the pin `c67894b9`'s L2 entry (admits `Unreceived` only, gate always run). The translation never produces it; it only adds runs to the engine |

So the engine statements, which quantify over every tree of the four entries, cover every
translated `b17415d20` tree, and also mixed-layer trees and the pin entry, which only add runs.
They are supporting lemmas; the README's headline list names the layer's statements.

## The claim under test

`L2:55-58`, on `executeAtomicBundle`: "No nonReentrant guard: replay safety is by CEI
(`_markFullyExecutedAndRun` sets `FullyExecuted` before running any call), so a reentrant call for
this bundle hits the status check", and `IHB:322-324`: with `_executeAllCalls = true`, "any failing
call reverts the whole flow, leaving no state changes".

`BundleStatusMachine` reads the guards as one state machine, one transaction at a time. This file
adds what happens **inside** a transaction: every call a bundle delivers runs arbitrary code, and
that code may call the handler's entry points again, to any depth, before the outer execution has
finished.

## The handler's replay state

    mapping(bytes32 => BundleStatus) public bundleStatus;                      // IHB:55
    mapping(bytes32 => mapping(uint256 => CallStatus)) public callStatus;      // IHB:58

`BundleStatus` and `CallStatus` are the enums at `common/Messaging.sol:283-288` and `:253-257`; a
fresh mapping slot reads as the first member, `Unreceived` and `Unprocessed`. This model reuses
`BundleStatusMachine.Status` and `BundleStatusMachine.CallStatus` for them. The writes to the two
mappings in the three handler files are exactly `IHB:147`, `:155`, `:160`, `:318`, `:326`, `:330`.

## The engine's entry points (none carries `nonReentrant`)

    executeBundle (L1:81-98)
      require(status == Unreceived || status == Verified)            // _validateExecutable, IHB:282-287
      if (status != Verified) _verifyBundle(...)                      // L1:92-95; writes Verified, IHB:318
      bundleStatus[bundleHash] = FullyExecuted                        // IHB:326 (CEI)
      for i < calls.length: callStatus[bundleHash][i] = Executed      // IHB:329-331
      _executeCalls(_executeAllCalls: true)                           // IHB:333-339
      emit BundleExecuted(bundleHash)                                 // IHB:341

    verifyBundle (L1:103-110)
      require(status == Unreceived)                                   // IHB:313
      _verifyBundle(...)                                              // writes Verified, IHB:318

    unbundleBundle (IHB:113-175)
      require(calls.length == _providedCallStatus.length)             // IHB:134-137
      require(status == Verified || status == Unbundled)              // IHB:139
      bundleStatus[bundleHash] = Unbundled                            // IHB:147 (CEI)
      for each i: Executed requested  -> require(recorded == Unprocessed); recorded = Executed
                  Cancelled requested -> require(recorded != Executed);
                                         if (recorded == Unprocessed) recorded = Cancelled
                  otherwise skipped                                   // IHB:149-164
      _executeCalls(_executeAllCalls: false, _providedCallStatus)    // IHB:166-172

    _executeCalls (IHB:350-383)
      for i < calls.length:
        if (!_executeAllCalls && _providedCallStatus[i] != Executed) continue    // IHB:359-364
        require(version == INTEROP_CALL_VERSION); require(!shadowAccount)        // IHB:366, :369
        _handleCallValue(value, sourceChainId)                        // IHB:371
        selector = IERC7786Recipient(_interopCallTarget(to)).receiveMessage{value}(...)  // IHB:374-380
        require(selector == receiveMessage.selector)                  // IHB:381

## Where execution can re-enter

Only at the target's `receiveMessage` (`IHB:374-380`, no `try`/`catch`). The handler's other
external calls are static calls or reach no entry point; the `b17415d20` layer's header
(`Specs/ReentrancyAtV35.lean`, "Where execution can re-enter") lists them with their lines
(`requireFlowFinalized`, `_proveInclusion`, `BASE_TOKEN_ASSET_ID()`, `BaseTokenHolder.give`).

The target is arbitrary code. It may call any entry point, any number of times, directly or
through other contracts; it may catch a failing call (`try`/`catch`, or a low-level call) or
let the failure propagate; and it finally returns the expected selector or not. When the
target is the handler itself, `receiveMessage` (`IHB:188-213`) requires `msg.sender ==
address(this)`, makes exactly one of the layer's execute, verify and unbundle self-calls, and does
not catch its failure: in this model, the target `.calls e inner false .returns`.

## Modelling choices

* **The external world is data.** `Callee` is what one delivered call's target does, as a
  finite tree: the entry points it calls, the targets of the calls each of those delivers in
  turn, and whether it catches each failure. `exec` is deterministic given that tree, and the
  results quantify over every tree, so every re-entrant behaviour of every target, at every
  depth, is covered. A target whose later choices depend on how an earlier call went is the
  tree of the choices it actually made: the semantics is deterministic, so that outcome is
  fixed by the tree.
* **Fuel bounds the depth.** `exec v n` runs a frame with depth and loop budget `n`; when it
  runs out the frame reverts, like an exhausted gas allowance or the call-depth limit. The
  results hold for every `n`.
* **A revert is `none`, and leaves nothing.** A frame that reverts returns `none`; its caller
  continues from the state before the call (when the target catches the failure) or reverts
  too. A transaction that reverts leaves the state and the log as they were (`commit`). This
  is `VM-REVERT` as modelled (ASSUMPTIONS.md): a reverted frame's writes, including those of
  its nested frames, are undone, and so are its logs.
* **The committed log is the trace.** `Effect.delivered h i` records that call `i` of the
  bundle with hash `h` reached its target's `receiveMessage` in a frame that committed;
  `Effect.executed h` is `emit BundleExecuted(h)`. A frame's log lists its own deliveries
  with the logs of the frames nested in each delivery right after it, in execution order.
  Deliveries inside a frame that reverted are not in it: they were undone.
* **A bundle is its hash and its number of calls.** The hash is a free field, so two bundles
  may share one (a collision); the handler keys everything by the hash, and so do the
  results.
* **Oracles are inputs.** The proof verdict (`_verifyBundle`, `L1:203-224`, or on L2 the flow
  gate `requireFlowFinalized`, a static call) is a boolean supplied with the entry call.
* **Reject-only checks are omitted**: the execution and unbundling permissions
  (`IHB:239-255`, `:118-132`), the destination context (`IHB:390-410`), the bundle and call
  versions (`IHB:230`, `:366`), `require(!shadowAccount)` (`IHB:369`), L1's single-call rule
  (`L1:85`) and target pin (`L1:189-192`), the pause gate (`L1:168-170`), and the selector and
  value checks of a call (folded into its target's failure). Omitting a check that can only revert
  only adds runs. The handlers' other functions (`initL2`, `updateL2`, and on L1 `initialize`,
  `pause`, `unpause` and ownership) write neither mapping (`Specs/ReentrancyAtV35.lean`).
* **Two countermodel orders** (`Variant`) move one write after `_executeCalls`; everything
  else is shared with the deployed order. Their re-entrant calls pass the omitted permission
  checks for a bundle that names no execution address (execution is then permissionless,
  `IHB:240-242`) and names the re-entering target as its unbundler (`IHB:124-126`).
-/

namespace Contracts.InteropHandler

open AttackVectors.BundleStatusMachine (Status CallStatus)

/-- A bundle hash (`bytes32`), as a 256-bit word. -/
abbrev BundleHash := UInt256

/-- What the handler reads of a decoded bundle (`_getBundleData`, `IHB:224-233`). -/
structure Bundle where
  /-- `InteropDataEncoding.encodeInteropBundleHash(_bundle)` (`IHB:231`). -/
  hash : BundleHash
  /-- `interopBundle.calls.length`. -/
  calls : ℕ
deriving DecidableEq

/-- A call of one of the handler's entry points, at top level or re-entrantly. -/
inductive Entry
  /-- L1's `executeBundle(_bundle, _proof)` (`L1:81-98`); `proofOk` is `_verifyBundle`'s verdict on
  `_proof` (`L1:203-224`), consulted only when the bundle is still `Unreceived` (`L1:92-95`). The
  `b17415d20` layer also sends L2's `executeAtomicBundle` here, with the flow gate's verdict. -/
  | executeBundle (b : Bundle) (proofOk : Bool)
  /-- L1's `verifyBundle(_bundle, _proof)` (`L1:103-110`); the `b17415d20` layer also sends L2's
  `verifyAtomicBundle` here, with the flow gate's verdict. -/
  | verifyBundle (b : Bundle) (proofOk : Bool)
  /-- `unbundleBundle(_bundle, _providedCallStatus)` (`IHB:113-175`). -/
  | unbundleBundle (b : Bundle) (req : List CallStatus)
  /-- **The pin `c67894b9`'s** `executeAtomicBundle(_bundle, _finality)`: it admits an `Unreceived`
  bundle only and always consults `requireFlowFinalized`, whose verdict is `gateOk`. It has no own
  `b17415d20` counterpart: at `b17415d20` (`L2:61-78`) the L2 entry point also admits `Verified`, and
  the `b17415d20` layer below translates it to `executeBundle`, never to this constructor. It only
  adds runs to the engine. -/
  | executeAtomicBundle (b : Bundle) (gateOk : Bool)

/-- The bundle an entry-point call names. -/
def Entry.bundle : Entry → Bundle
  | .executeBundle b _ => b
  | .verifyBundle b _ => b
  | .unbundleBundle b _ => b
  | .executeAtomicBundle b _ => b

/-- What the target of one delivered call does, from the moment its `receiveMessage` is called
(`IHB:374-380`) until it returns. -/
inductive Callee
  /-- Returns the expected selector (`IHB:381`). -/
  | returns
  /-- Reverts, or returns another selector. This also stands for the call's own checks
  failing before the target runs (`IHB:366`, `:369`, `:371`). -/
  | reverts
  /-- Calls entry point `e`; `inner` are the targets of the calls that frame delivers, in
  order. If that frame reverts, the target either catches the failure (`caught`) and goes on
  from the state before the call, or reverts. Then it goes on as `next`. -/
  | calls (e : Entry) (inner : List Callee) (caught : Bool) (next : Callee)

/-- The handler's replay state. -/
structure State where
  /-- `bundleStatus` (`IHB:55`). -/
  bundle : BundleHash → Status
  /-- `callStatus` (`IHB:58`). -/
  call : BundleHash → ℕ → CallStatus

/-- Fresh storage: every bundle `Unreceived`, every call `Unprocessed`. -/
def init : State := ⟨fun _ => .Unreceived, fun _ _ => .Unprocessed⟩

/-- `bundleStatus[h] = st`. -/
def State.setBundle (s : State) (h : BundleHash) (st : Status) : State :=
  { s with bundle := fun h' => if h' = h then st else s.bundle h' }

/-- `callStatus[h][i] = st`. -/
def State.setCall (s : State) (h : BundleHash) (i : ℕ) (st : CallStatus) : State :=
  { s with call := fun h' i' => if h' = h ∧ i' = i then st else s.call h' i' }

/-- `for (i = 0; i < n; ++i) callStatus[h][i] = Executed` (`IHB:329-331`): written
without being read. -/
def State.executeAll (s : State) (h : BundleHash) (n : ℕ) : State :=
  { s with call := fun h' i => if h' = h ∧ i < n then .Executed else s.call h' i }

/-- `callStatus[h][i] = Executed` for each listed `i` (the countermodel's late write). -/
def State.executeEach (s : State) (h : BundleHash) (is : List ℕ) : State :=
  { s with call := fun h' i => if h' = h ∧ i ∈ is then .Executed else s.call h' i }

/-- `if (status != BundleStatus.Verified) _verifyBundle(...)` (`L1:92-95`): an `Unreceived`
bundle becomes `Verified` (`IHB:318`) before it is executed. -/
def State.verifyIfUnreceived (s : State) (h : BundleHash) : State :=
  if s.bundle h = .Unreceived then s.setBundle h .Verified else s

/-- Where the handler writes its replay state, relative to the calls the write guards. -/
inductive Variant
  /-- The deployed source: every write precedes `_executeCalls`. -/
  | deployed
  /-- Countermodel: `executeBundle` and `executeAtomicBundle` write
  `bundleStatus = FullyExecuted` (`IHB:326`) after `_executeCalls`. -/
  | statusWriteAfterCalls
  /-- Countermodel: `unbundleBundle`'s first loop checks a requested execution but writes
  `callStatus = Executed` (`IHB:155`) only after `_executeCalls`. -/
  | callWriteAfterCalls
deriving DecidableEq

/-- What a whole-bundle execution writes before its calls: the status write and the
call-status loop (`IHB:326-331`, `_markFullyExecutedAndRun`). -/
def beforeCalls : Variant → Bundle → State → State
  | .statusWriteAfterCalls, b, s => s.executeAll b.hash b.calls
  | _, b, s => (s.setBundle b.hash .FullyExecuted).executeAll b.hash b.calls

/-- What a whole-bundle execution writes after its calls: nothing in the source. -/
def afterCalls : Variant → Bundle → State → State
  | .statusWriteAfterCalls, b, s => s.setBundle b.hash .FullyExecuted
  | _, _, s => s

/-- Whether `unbundleBundle`'s first loop writes `Executed` (`IHB:155`) before the calls. -/
def writesCallsFirst : Variant → Bool
  | .callWriteAfterCalls => false
  | _ => true

/-- The first loop of `unbundleBundle` (`IHB:149-164`), from call `i` on, over the requested
statuses; `none` when a check reverts (`CallNotExecutable`, `IHB:154`; `CallAlreadyExecuted`,
`IHB:158`). With `writeNow = false` (the countermodel) a requested execution is checked but not
yet recorded. -/
def markCalls (writeNow : Bool) (h : BundleHash) :
    ℕ → List CallStatus → State → Option State
  | _, [], s => some s
  | i, .Executed :: req, s =>
      if s.call h i = .Unprocessed then
        markCalls writeNow h (i + 1) req (if writeNow then s.setCall h i .Executed else s)
      else none
  | i, .Cancelled :: req, s =>
      if s.call h i = .Executed then none
      else markCalls writeNow h (i + 1) req
        (if s.call h i = .Unprocessed then s.setCall h i .Cancelled else s)
  | i, .Unprocessed :: req, s => markCalls writeNow h (i + 1) req s

/-- The calls `_executeCalls` delivers on the unbundled route, from call `i` on: those
requested `Executed`, in index order (`IHB:359-364`). -/
def toExecute : ℕ → List CallStatus → List ℕ
  | _, [] => []
  | i, .Executed :: req => i :: toExecute (i + 1) req
  | i, .Cancelled :: req => toExecute (i + 1) req
  | i, .Unprocessed :: req => toExecute (i + 1) req

/-- What `unbundleBundle` writes after its calls: nothing in the source. -/
def afterUnbundle : Variant → BundleHash → List CallStatus → State → State
  | .callWriteAfterCalls, h, req, s => s.executeEach h (toExecute 0 req)
  | _, _, _, s => s

/-- A committed event. -/
inductive Effect
  /-- Call `i` of the bundle with hash `h` reached its target's `receiveMessage` (`IHB:374`). -/
  | delivered (h : BundleHash) (i : ℕ)
  /-- `emit BundleExecuted(h)` (`IHB:341`): a whole-bundle execution
  of `h` completed. -/
  | executed (h : BundleHash)
deriving DecidableEq

/-- The bundle an effect belongs to. -/
def Effect.bundleHash : Effect → BundleHash
  | .delivered h _ => h
  | .executed h => h

/-- What runs: an entry point, the call loop of one, or the target of one delivered call. -/
inductive Frame
  /-- Entry point `e`; `callees` are the targets of the calls it delivers, in order (a missing
  one returns). -/
  | entry (e : Entry) (callees : List Callee)
  /-- `_executeCalls` delivering calls `is` of bundle `h`, in order. -/
  | calls (h : BundleHash) (is : List ℕ) (callees : List Callee)
  /-- One delivered call's target. -/
  | target (c : Callee)

/-- **The semantics.** `exec v n f s` runs frame `f` from state `s` with budget `n`: the state
and committed log it leaves, or `none` if it reverts. -/
def exec (v : Variant) : ℕ → Frame → State → Option (State × List Effect)
  | 0, _, _ => none
  | n + 1, .entry (.executeBundle b proofOk) cs, s =>
      if s.bundle b.hash = .Verified ∨ (s.bundle b.hash = .Unreceived ∧ proofOk = true) then
        match exec v n (.calls b.hash (List.range b.calls) cs)
            (beforeCalls v b (s.verifyIfUnreceived b.hash)) with
        | some (s₂, l) => some (afterCalls v b s₂, l ++ [.executed b.hash])
        | none => none
      else none
  | n + 1, .entry (.executeAtomicBundle b gateOk) cs, s =>
      if s.bundle b.hash = .Unreceived ∧ gateOk = true then
        match exec v n (.calls b.hash (List.range b.calls) cs) (beforeCalls v b s) with
        | some (s₂, l) => some (afterCalls v b s₂, l ++ [.executed b.hash])
        | none => none
      else none
  | _ + 1, .entry (.verifyBundle b proofOk) _, s =>
      if s.bundle b.hash = .Unreceived ∧ proofOk = true then
        some (s.setBundle b.hash .Verified, [])
      else none
  | n + 1, .entry (.unbundleBundle b req) cs, s =>
      if req.length = b.calls ∧
          (s.bundle b.hash = .Verified ∨ s.bundle b.hash = .Unbundled) then
        match markCalls (writesCallsFirst v) b.hash 0 req (s.setBundle b.hash .Unbundled) with
        | some s₁ =>
            match exec v n (.calls b.hash (toExecute 0 req) cs) s₁ with
            | some (s₂, l) => some (afterUnbundle v b.hash req s₂, l)
            | none => none
        | none => none
      else none
  | _ + 1, .calls _ [] _, s => some (s, [])
  | n + 1, .calls h (i :: is) cs, s =>
      match exec v n (.target (cs.headD .returns)) s with
      | some (s₁, l₁) =>
          match exec v n (.calls h is cs.tail) s₁ with
          | some (s₂, l₂) => some (s₂, .delivered h i :: (l₁ ++ l₂))
          | none => none
      | none => none
  | _ + 1, .target .returns, s => some (s, [])
  | _ + 1, .target .reverts, _ => none
  | n + 1, .target (.calls e inner caught next), s =>
      match exec v n (.entry e inner) s with
      | some (s₁, l₁) =>
          match exec v n (.target next) s₁ with
          | some (s₂, l₂) => some (s₂, l₁ ++ l₂)
          | none => none
      | none => if caught then exec v n (.target next) s else none

/-- The commit rule: a transaction that reverts leaves the state and the log as they were.
`VM-REVERT` as modelled, like `transact` for the vault (`MODEL-COMMIT`). -/
def commit (s : State) : Option (State × List Effect) → State × List Effect
  | some r => r
  | none => (s, [])

/-- A submitted transaction: an entry point, the targets of the calls it delivers, and a
budget. -/
structure Tx where
  /-- The depth and loop budget. -/
  fuel : ℕ
  /-- The entry point called. -/
  entry : Entry
  /-- The targets of the calls it delivers, in order. -/
  callees : List Callee

/-- One transaction: the state after it and what it committed. -/
def submit (v : Variant) (s : State) (t : Tx) : State × List Effect :=
  commit s (exec v t.fuel (.entry t.entry t.callees) s)

/-- A sequence of transactions: the final state and the committed log, in order. -/
def submitAll (v : Variant) : State → List Tx → State × List Effect
  | s, [] => (s, [])
  | s, t :: ts =>
      ((submitAll v (submit v s t).1 ts).1, (submit v s t).2 ++ (submitAll v (submit v s t).1 ts).2)

/-- An effect is **spent** in a state when the handler has recorded it as consumed, so that no
guard admits it again: a call of a fully executed bundle (every route refuses that bundle,
`IHB:282-287`, `:139`), or a call of an unbundled bundle recorded
`Executed` (the whole-bundle routes refuse an unbundled bundle, and the unbundled route executes
only `Unprocessed` calls, `IHB:154`); and the execution of a fully executed bundle. -/
def Spent (s : State) : Effect → Prop
  | .delivered h i =>
      s.bundle h = .FullyExecuted ∨ (s.bundle h = .Unbundled ∧ s.call h i = .Executed)
  | .executed h => s.bundle h = .FullyExecuted

/-- The handler's own record of an effect: the call recorded `Executed`, the bundle recorded
`FullyExecuted`. -/
def Recorded (s : State) : Effect → Prop
  | .delivered h i => s.call h i = .Executed
  | .executed h => s.bundle h = .FullyExecuted

/-- A call has been processed only for a bundle that has left both entry states: the
reachable-state invariant that makes the whole-bundle route's unread call-status write
(`IHB:329-331`) an edge of `BundleStatusMachine.CallStep`. -/
def CallsClosed (s : State) : Prop :=
  ∀ h i, s.call h i ≠ .Unprocessed → s.bundle h = .FullyExecuted ∨ s.bundle h = .Unbundled

/-! ## Witness data

Bundle `1` with two calls and bundle `2` with one; bundle `3` with one call for the
countermodels. -/

/-- Bundle `1`, two calls. -/
def wA : Bundle := ⟨1, 2⟩

/-- Bundle `2`, one call. -/
def wB : Bundle := ⟨2, 1⟩

/-- Bundle `3`, one call. -/
def wC : Bundle := ⟨3, 1⟩

/-- A target that calls `e` (whose calls' targets return) and returns, catching a failure
or not. -/
def reenter (e : Entry) (caught : Bool) : Callee := .calls e [] caught .returns

/-- An `unbundleBundle` request for a bundle with `n` calls that executes call 0 and skips the
rest. -/
def requestFirst (n : ℕ) : List CallStatus := .Executed :: List.replicate (n - 1) .Unprocessed

/-- Atomic execution of `wA`. Call 0's target executes `wB` re-entrantly, then tries to execute
`wA` again and catches the failure; call 1's target returns. -/
def wNested : Tx :=
  ⟨8, .executeAtomicBundle wA true,
    [.calls (.executeAtomicBundle wB true) [] false
      (reenter (.executeAtomicBundle wA true) true)]⟩

/-- The same, but the target does not catch the failed re-entry into `wA`. -/
def wNestedUncaught : Tx :=
  ⟨8, .executeAtomicBundle wA true,
    [.calls (.executeAtomicBundle wB true) [] false
      (reenter (.executeAtomicBundle wA true) false)]⟩

/-- A failing attempt at `wA`: call 0's target executes `wB` re-entrantly and returns; call 1's
target reverts. -/
def wAttempt : Tx :=
  ⟨8, .executeAtomicBundle wA true,
    [.calls (.executeAtomicBundle wB true) [] false .returns, .reverts]⟩

/-- The same attempt with call 1's target returning. -/
def wAttemptOk : Tx :=
  ⟨8, .executeAtomicBundle wA true,
    [.calls (.executeAtomicBundle wB true) [] false .returns, .returns]⟩

/-- A retry of `wA` whose targets return. -/
def wRetry : Tx := ⟨4, .executeAtomicBundle wA true, [.returns, .returns]⟩

/-- Atomic execution of `wA`. Call 0's target executes `wB` re-entrantly; `wB`'s only call
reverts, so that frame reverts, and the target catches the failure and returns. -/
def wCaught : Tx :=
  ⟨8, .executeAtomicBundle wA true,
    [.calls (.executeAtomicBundle wB true) [.reverts] true .returns]⟩

/-- Atomic execution of `wB` on its own. -/
def wRunB : Tx := ⟨3, .executeAtomicBundle wB true, []⟩

/-- Atomic execution of `wC`, whose call's target executes `wC` again, catching a failure or
not. -/
def wReenterAtomic (caught : Bool) : Tx :=
  ⟨6, .executeAtomicBundle wC true, [reenter (.executeAtomicBundle wC true) caught]⟩

/-- `executeBundle` of `wC` with a valid inclusion proof, whose call's target calls
`executeBundle` of `wC` again with no valid proof, not catching a failure. -/
def wReenterPublic : Tx :=
  ⟨6, .executeBundle wC true, [reenter (.executeBundle wC false) false]⟩

/-- `verifyBundle` of `wC` with a valid inclusion proof. -/
def wVerifyC : Tx := ⟨1, .verifyBundle wC true, []⟩

/-- `unbundleBundle` of `wC` requesting its call, whose target makes the same request again,
catching a failure or not. -/
def wReenterUnbundle (caught : Bool) : Tx :=
  ⟨6, .unbundleBundle wC [.Executed], [reenter (.unbundleBundle wC [.Executed]) caught]⟩

/-! ## Which entry-point calls a run makes

Used by the History record `BundleStatusMachineStrong` and by `Protocol/InteropAtomicity`. -/

/-- **ENTRY-POINT CALL `e` OCCURS IN TARGET `c`.** `c` makes it, or one of the targets of the
calls that frame delivers makes it, or `c`'s continuation does. -/
inductive Callee.Mentions : Callee → Entry → Prop
  /-- `c` calls `e` itself. -/
  | here {e : Entry} {inner : List Callee} {caught : Bool} {next : Callee} :
      Callee.Mentions (.calls e inner caught next) e
  /-- A target of a call the frame of `c`'s call delivers makes it. -/
  | nested {e e' : Entry} {inner : List Callee} {caught : Bool} {next c : Callee} :
      c ∈ inner → Callee.Mentions c e' → Callee.Mentions (.calls e inner caught next) e'
  /-- `c`'s continuation makes it. -/
  | cont {e e' : Entry} {inner : List Callee} {caught : Bool} {next : Callee} :
      Callee.Mentions next e' → Callee.Mentions (.calls e inner caught next) e'

/-- Entry-point call `e'` occurs in frame `f`: it is the frame's own entry point, or occurs in
one of the frame's targets. -/
def Frame.Mentions : Frame → Entry → Prop
  | .entry e cs, e' => e' = e ∨ ∃ c ∈ cs, c.Mentions e'
  | .calls _ _ cs, e' => ∃ c ∈ cs, c.Mentions e'
  | .target c, e' => c.Mentions e'

/-- Entry-point call `e` occurs in transaction `t`. -/
def Tx.Mentions (t : Tx) (e : Entry) : Prop := Frame.Mentions (.entry t.entry t.callees) e

/-- **CALL `e` PRESENTS NO VALID INCLUSION PROOF FOR BUNDLE HASH `h`.** Only `executeBundle` and
`verifyBundle` carry a proof verdict, the carried boolean (at `b17415d20`, L1's `executeBundle` and
`verifyBundle`, `L1:81-98`, `:103-110`; the `b17415d20` layer below carries either layer's gate
verdict there). -/
def Entry.NoProofFor (h : BundleHash) : Entry → Prop
  | .executeBundle b ok => b.hash = h → ok = false
  | .verifyBundle b ok => b.hash = h → ok = false
  | .unbundleBundle _ _ => True
  | .executeAtomicBundle _ _ => True

/-- **NO CALL OF A RUN PRESENTS A VALID PROOF FOR `h`**, at any depth of re-entry. -/
def NoProofRun (h : BundleHash) (txs : List Tx) : Prop :=
  ∀ t ∈ txs, ∀ e, t.Mentions e → e.NoProofFor h

/-- **CALL `e` PRESENTS A VALID PROOF ONLY FOR A PUBLISHED HASH.** -/
def Entry.ProofSound (published : BundleHash → Prop) : Entry → Prop
  | .executeBundle b ok => ok = true → published b.hash
  | .verifyBundle b ok => ok = true → published b.hash
  | .unbundleBundle _ _ => True
  | .executeAtomicBundle _ _ => True

/-- **EVERY VALID PROOF A RUN PRESENTS IS FOR A PUBLISHED HASH** (soundness of the L1 message
inclusion proofs), at any depth of re-entry. -/
def SoundProofRun (published : BundleHash → Prop) (txs : List Tx) : Prop :=
  ∀ t ∈ txs, ∀ e, t.Mentions e → e.ProofSound published

end Contracts.InteropHandler
