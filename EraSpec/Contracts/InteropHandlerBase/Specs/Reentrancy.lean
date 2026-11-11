import EraSpec.Contracts.InteropHandlerBase.Specs.BundleStatusMachine
import EraSpec.Core.Word

/-!
# Model: re-entrant bundle execution in the interop handler

Source: era-contracts at the pin `c67894b9`. Paths are relative to
`l1-contracts/contracts/interop/interop-handler/` unless they name another directory of
`l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.InteropHandlerBase.Properties.Reentrancy` and are proved in
`EraSpec.Contracts.InteropHandlerBase.Proofs.Reentrancy`.

## The claim under test

`L2InteropHandler.sol:45-46`, on `executeAtomicBundle`:

    /// No `nonReentrant` guard, matching {executeBundle}: replay safety is by CEI (status is
    /// set to `FullyExecuted` before any call runs), so a reentrant call for this bundle hits the
    /// status check.

and `InteropHandlerBase.sol:135-136`, on `executeBundle`'s call loop:

    // Since we provide the flag `_executeAllCalls` to be true, if either of the calls fail,
    // the `_executeCalls` will fail as well, thus making the whole flow revert, no changes will
    // be applied to the state.

`BundleStatusMachine` reads the four guards as one state machine, one transaction at a time.
This file adds what happens **inside** a transaction: every call a bundle delivers runs
arbitrary code, and that code may call the handler's entry points again, to any depth,
before the outer execution has finished.

## The handler's replay state

    mapping(bytes32 => BundleStatus) public bundleStatus;                      // :54
    mapping(bytes32 => mapping(uint256 => CallStatus)) public callStatus;      // :57

`BundleStatus` and `CallStatus` are the enums at `common/Messaging.sol:303-308` and
`:270-274`; a fresh mapping slot reads as the first member, `Unreceived` and `Unprocessed`.
This model reuses `BundleStatusMachine.Status` and `BundleStatusMachine.CallStatus` for them.

## The entry points (none carries `nonReentrant`)

    executeBundle (:86-147)
      require(status == Unreceived || status == Verified)            // :117-120
      if (status != Verified) _verifyBundle(...)                      // :123; writes Verified, :312
      bundleStatus[bundleHash] = FullyExecuted                        // :126  (CEI)
      for i < calls.length: callStatus[bundleHash][i] = Executed      // :129-132
      _executeCalls(_executeAllCalls: true)                           // :137-143
      emit BundleExecuted(bundleHash)                                 // :146

    executeAtomicBundle (L2InteropHandler.sol:49-100)
      require(status == Unreceived)                                   // :79
      requireFlowFinalized(bundleHash, _finality)                     // :83
      bundleStatus[bundleHash] = FullyExecuted                        // :86  (CEI)
      for i < calls.length: callStatus[bundleHash][i] = Executed      // :87-90
      _executeCalls(_executeAllCalls: true)                           // :91-97
      emit BundleExecuted(bundleHash)                                 // :99

    verifyBundle (:150-161)
      require(status == Unreceived)                                   // :157
      _verifyBundle(...)                                              // :160; writes Verified, :312

    unbundleBundle (:164-231)
      require(calls.length == _providedCallStatus.length)             // :188-191
      require(status == Verified || status == Unbundled)              // :195
      bundleStatus[bundleHash] = Unbundled                            // :198  (CEI)
      for each i: Executed requested  -> require(recorded == Unprocessed); recorded = Executed
                  Cancelled requested -> require(recorded != Executed);
                                         if (recorded == Unprocessed) recorded = Cancelled
                  otherwise skipped                                   // :200-219
      _executeCalls(_executeAllCalls: false, _providedCallStatus)    // :221-227

    _executeCalls (:259-289)
      for i < calls.length:
        if (!_executeAllCalls && _providedCallStatus[i] != Executed) continue    // :268-274
        require(version == INTEROP_CALL_VERSION)                      // :276
        _handleCallValue(value, sourceChainId)                        // :279
        selector = IERC7786Recipient(to).receiveMessage{value}(...)   // :282-286, no try/catch
        require(selector == receiveMessage.selector)                  // :287

## Where execution can re-enter

Only at the target's `receiveMessage` (`:282-286`). The other external calls cannot reach an
entry point:

* `_proveInclusion` (`:65`; `L2InteropHandler.sol:103-112`, `L1InteropHandler.sol:68-77`) is
  `internal view`, so its call to `proveL2MessageInclusionShared`
  (`common/interfaces/IMessageVerification.sol:18-24`, `external view`) is a static call, which
  cannot write. So is `requireFlowFinalized` (`atomic-interop/IAtomicFlowManager.sol:53`,
  `external view`).
* `_handleCallValue` on L2 (`L2InteropHandler.sol:115-120`) calls `BaseTokenHolder.give`
  (`l2-system/BaseTokenHolder.sol:99-109`), which notifies the asset tracker
  (`bridge/asset-tracker/L2AssetTracker.sol:359-380`) and sends the value back to the
  handler's `receive()` (`L2InteropHandler.sol:130-134`), which writes nothing. On L1 it only
  checks the value is zero (`L1InteropHandler.sol:85-87`). Its only effect in this model is
  that it may revert.

The target is arbitrary code. It may call any entry point, any number of times, directly or
through other contracts; it may catch a failing call (`try`/`catch`, or a low-level call) or
let the failure propagate; and it finally returns the expected selector or not. When the
target is the handler itself, `receiveMessage` (`:334-362`) requires `msg.sender ==
address(this)`, makes exactly one of `this.executeBundle`, `this.verifyBundle` and
`this.unbundleBundle`, and does not catch its failure: in this model, the target
`.calls e inner false .returns`.

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
* **Oracles are inputs.** The inclusion proof's verdict (`_verifyBundle`, `:302-310`) and the
  atomic flow gate's verdict (`requireFlowFinalized`) are booleans supplied with the entry
  call: both are static calls, fixed for the call.
* **Reject-only checks are omitted**: the execution and unbundling permissions (`:95-112`,
  `:170-184`, `L2InteropHandler.sol:62-75`), the destination context (`:428-451`), the
  bundle and call versions (`:248`, `:276`), the pause gate (`_ensureNotPaused`,
  `L1InteropHandler.sol:62-64`), and the selector and value checks of a call (folded into its
  target's failure). Omitting a check that can only revert only adds runs. The handler's
  other functions (`initL2`, and on L1 `initialize`, `pause`, `unpause` and ownership) write
  neither mapping.
* **Two countermodel orders** (`Variant`) move one write after `_executeCalls`; everything
  else is shared with the deployed order. Their re-entrant calls pass the omitted permission
  checks for a bundle that names no execution address (execution is then permissionless,
  `:94-95`) and names the re-entering target as its unbundler (`:176-178`).
-/

namespace Contracts.InteropHandler

open AttackVectors.BundleStatusMachine (Status CallStatus)

/-- A bundle hash (`bytes32`), as a 256-bit word. -/
abbrev BundleHash := UInt256

/-- What the handler reads of a decoded bundle (`_getBundleData`, `:242-251`). -/
structure Bundle where
  /-- `InteropDataEncoding.encodeInteropBundleHash(sourceChainId, _bundle)` (`:249`). -/
  hash : BundleHash
  /-- `interopBundle.calls.length`. -/
  calls : ℕ
deriving DecidableEq

/-- A call of one of the handler's entry points, at top level or re-entrantly. -/
inductive Entry
  /-- `executeBundle(_bundle, _proof)` (`:86-147`); `proofOk` is `_verifyBundle`'s verdict on
  `_proof` (`:302-310`), consulted only when the bundle is still `Unreceived`. -/
  | executeBundle (b : Bundle) (proofOk : Bool)
  /-- `verifyBundle(_bundle, _proof)` (`:150-161`). -/
  | verifyBundle (b : Bundle) (proofOk : Bool)
  /-- `unbundleBundle(_bundle, _providedCallStatus)` (`:164-231`). -/
  | unbundleBundle (b : Bundle) (req : List CallStatus)
  /-- `executeAtomicBundle(_bundle, _finality)` (`L2InteropHandler.sol:49-100`); `gateOk` is
  `requireFlowFinalized`'s verdict on `_finality` (`L2InteropHandler.sol:83`). -/
  | executeAtomicBundle (b : Bundle) (gateOk : Bool)

/-- The bundle an entry-point call names. -/
def Entry.bundle : Entry → Bundle
  | .executeBundle b _ => b
  | .verifyBundle b _ => b
  | .unbundleBundle b _ => b
  | .executeAtomicBundle b _ => b

/-- What the target of one delivered call does, from the moment its `receiveMessage` is called
(`:282-286`) until it returns. -/
inductive Callee
  /-- Returns the expected selector (`:287`). -/
  | returns
  /-- Reverts, or returns another selector. This also stands for the call's own checks
  failing before the target runs (`:276`, `:279`). -/
  | reverts
  /-- Calls entry point `e`; `inner` are the targets of the calls that frame delivers, in
  order. If that frame reverts, the target either catches the failure (`caught`) and goes on
  from the state before the call, or reverts. Then it goes on as `next`. -/
  | calls (e : Entry) (inner : List Callee) (caught : Bool) (next : Callee)

/-- The handler's replay state. -/
structure State where
  /-- `bundleStatus` (`:54`). -/
  bundle : BundleHash → Status
  /-- `callStatus` (`:57`). -/
  call : BundleHash → ℕ → CallStatus

/-- Fresh storage: every bundle `Unreceived`, every call `Unprocessed`. -/
def init : State := ⟨fun _ => .Unreceived, fun _ _ => .Unprocessed⟩

/-- `bundleStatus[h] = st`. -/
def State.setBundle (s : State) (h : BundleHash) (st : Status) : State :=
  { s with bundle := fun h' => if h' = h then st else s.bundle h' }

/-- `callStatus[h][i] = st`. -/
def State.setCall (s : State) (h : BundleHash) (i : ℕ) (st : CallStatus) : State :=
  { s with call := fun h' i' => if h' = h ∧ i' = i then st else s.call h' i' }

/-- `for (i = 0; i < n; ++i) callStatus[h][i] = Executed` (`:129-132`,
`L2InteropHandler.sol:87-90`): written without being read. -/
def State.executeAll (s : State) (h : BundleHash) (n : ℕ) : State :=
  { s with call := fun h' i => if h' = h ∧ i < n then .Executed else s.call h' i }

/-- `callStatus[h][i] = Executed` for each listed `i` (the countermodel's late write). -/
def State.executeEach (s : State) (h : BundleHash) (is : List ℕ) : State :=
  { s with call := fun h' i => if h' = h ∧ i ∈ is then .Executed else s.call h' i }

/-- `if (status != BundleStatus.Verified) _verifyBundle(...)` (`:123`): an `Unreceived` bundle
becomes `Verified` (`:312`) before it is executed. -/
def State.verifyIfUnreceived (s : State) (h : BundleHash) : State :=
  if s.bundle h = .Unreceived then s.setBundle h .Verified else s

/-- Where the handler writes its replay state, relative to the calls the write guards. -/
inductive Variant
  /-- The pinned source: every write precedes `_executeCalls`. -/
  | deployed
  /-- Countermodel: `executeBundle` and `executeAtomicBundle` write
  `bundleStatus = FullyExecuted` (`:126`, `L2InteropHandler.sol:86`) after `_executeCalls`. -/
  | statusWriteAfterCalls
  /-- Countermodel: `unbundleBundle`'s first loop checks a requested execution but writes
  `callStatus = Executed` (`:208`) only after `_executeCalls`. -/
  | callWriteAfterCalls
deriving DecidableEq

/-- What a whole-bundle execution writes before its calls: the status write and the
call-status loop (`:126-132`, `L2InteropHandler.sol:86-90`). -/
def beforeCalls : Variant → Bundle → State → State
  | .statusWriteAfterCalls, b, s => s.executeAll b.hash b.calls
  | _, b, s => (s.setBundle b.hash .FullyExecuted).executeAll b.hash b.calls

/-- What a whole-bundle execution writes after its calls: nothing in the source. -/
def afterCalls : Variant → Bundle → State → State
  | .statusWriteAfterCalls, b, s => s.setBundle b.hash .FullyExecuted
  | _, _, s => s

/-- Whether `unbundleBundle`'s first loop writes `Executed` (`:208`) before the calls. -/
def writesCallsFirst : Variant → Bool
  | .callWriteAfterCalls => false
  | _ => true

/-- The first loop of `unbundleBundle` (`:200-219`), from call `i` on, over the requested
statuses; `none` when a check reverts (`CallNotExecutable`, `:207`; `CallAlreadyExecuted`,
`:212`). With `writeNow = false` (the countermodel) a requested execution is checked but not
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
requested `Executed`, in index order (`:268-274`). -/
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
  /-- Call `i` of the bundle with hash `h` reached its target's `receiveMessage` (`:282`). -/
  | delivered (h : BundleHash) (i : ℕ)
  /-- `emit BundleExecuted(h)` (`:146`, `L2InteropHandler.sol:99`): a whole-bundle execution
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
`:117-120`, `:195`, `L2InteropHandler.sol:79`), or a call of an unbundled bundle recorded
`Executed` (the whole-bundle routes refuse an unbundled bundle, and the unbundled route executes
only `Unprocessed` calls, `:207`); and the execution of a fully executed bundle. -/
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
(`:129-132`) an edge of `BundleStatusMachine.CallStep`. -/
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

end Contracts.InteropHandler
