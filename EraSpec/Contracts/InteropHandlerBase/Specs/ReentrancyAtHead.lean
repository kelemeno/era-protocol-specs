import EraSpec.Contracts.InteropHandlerBase.Specs.Reentrancy

/-!
# Model: re-entrant execution in the L2 interop handler at head

Source: era-contracts `main` at **`3605e82`**. Paths are relative to
`l1-contracts/contracts/interop/interop-handler/` unless they name another directory of
`l1-contracts/contracts/`.

The upgrade pin `e561b9cc2` and draft v0.35 (`d9f6789`) have the same handler logic. Their
`InteropHandlerBase.sol` differs from main's only in three hook names (`_getExecuteBundleSelector`,
`_getVerifyBundleSelector`, `_getExpectedDestinationBaseTokenAssetId`), so its line numbers below
are theirs too. Their `L2InteropHandler.sol` also has `updateL2` (`:38-43`), which clears one
fixed storage slot and writes neither mapping; from `:35` on, their line numbers are main's plus 10
(`verifyAtomicBundle` is at `:83-92` there). So this model covers all three revisions.

`Specs/Reentrancy.lean` models the pin `c67894b9` and is kept unchanged. This file is a separate
model in its own namespace (`Contracts.InteropHandlerAtHead`). It reuses that file's state, bundles,
effects, `markCalls` and `toExecute`, because the head source writes the two mappings the same way.

**This file is definitions only.** The results are in
`EraSpec.Contracts.InteropHandlerBase.Properties.ReentrancyAtHead` and
`EraSpec.Contracts.InteropHandlerBase.Properties.AtomicUnbundlingAtHead`, proved in the matching
`Proofs` modules.

## What changed since `c67894b9`

At the pin, `executeAtomicBundle` required `Unreceived` (`L2InteropHandler.sol:79`), and its NatSpec
said "there is no atomic verify path" (`:42`). At head:

    executeAtomicBundle (L2InteropHandler.sol:51-68)
      require(status == Unreceived || status == Verified)        // :55; InteropHandlerBase.sol:282-300
      if (status != Verified) requireFlowFinalized(bundleHash, _finality)        // :63-65
      _markFullyExecutedAndRun                                   // :67; InteropHandlerBase.sol:325-342
        bundleStatus[bundleHash] = FullyExecuted                 //   :326  (CEI)
        for i < calls.length: callStatus[bundleHash][i] = Executed               //   :328-331
        _executeCalls(_executeAllCalls: true)                    //   :333-339
        emit BundleExecuted(bundleHash)                          //   :341

    verifyAtomicBundle (L2InteropHandler.sol:73-82)              // new
      require(status == Unreceived)                              // :76; InteropHandlerBase.sol:306-314
      requireFlowFinalized(bundleHash, _finality)                // :79
      bundleStatus[bundleHash] = Verified; emit BundleVerified   // :81; InteropHandlerBase.sol:317-320

    unbundleBundle (InteropHandlerBase.sol:113-175)              // as at the pin
      require(calls.length == _providedCallStatus.length)        // :134-137
      require(status == Verified || status == Unbundled)         // :139
      bundleStatus[bundleHash] = Unbundled                       // :147  (CEI)
      for each i: Executed requested  -> require(recorded == Unprocessed); recorded = Executed
                  Cancelled requested -> require(recorded != Executed);
                                         if (recorded == Unprocessed) recorded = Cancelled
                  otherwise skipped                              // :149-164
      _executeCalls(_executeAllCalls: false, _providedCallStatus)               // :166-172

    _executeCalls (InteropHandlerBase.sol:350-383)
      for i < calls.length:
        if (!_executeAllCalls && _providedCallStatus[i] != Executed) continue    // :359-364
        _handleCallValue(value, sourceChainId)                   // :371
        selector = IERC7786Recipient(to).receiveMessage{value}(...)              // :374-380, no try/catch
        require(selector == receiveMessage.selector)             // :381

`unbundleBundle` checks nothing about atomicity or the flow, and on L2 every bundle is atomic:
`L2InteropHandler` has no other proof entry point (`:17-20`), because public L2->L2 interop was removed
(`InteropCenter.sol:228-229`, `:547-554`). So `verifyAtomicBundle` opens the unbundled route to atomic
bundles. After it, the bundle's unbundler can run its calls one at a time or cancel them, and a
cancelled call can never run (`InteropHandlerBase.sol:154`). main documents this as intended
(`docs/atomic-interop/03-reference.md:78-80`, `:147-151`; `protocol-docs/atomicity/security.md:17-24`).

The public route (`executeBundle`/`verifyBundle` with an L1 message-inclusion proof) now exists only
on `L1InteropHandler`, which is a different contract on another chain, with its own storage. It is
not part of this model.

## Where execution can re-enter

As at the pin (`Specs/Reentrancy.lean`, "Where execution can re-enter"), only at the target's
`receiveMessage` (`InteropHandlerBase.sol:374-380`). `requireFlowFinalized` is `external view`
(`atomic-interop/IAtomicFlowManager.sol`), so the handler's call to it is a static call.
`_handleCallValue` (`L2InteropHandler.sol:139-144`) calls `BaseTokenHolder.give`
(`l2-system/BaseTokenHolder.sol:69`), whose transfer reaches the handler's `receive()`
(`L2InteropHandler.sol:154-158`), which writes nothing. When the target is the handler itself,
`receiveMessage` (`InteropHandlerBase.sol:188-213`) requires `msg.sender == address(this)` and makes
exactly one of `this.executeAtomicBundle`, `this.verifyAtomicBundle` (`L2InteropHandler.sol:99-132`)
and `this.unbundleBundle` (`InteropHandlerBase.sol:413-433`), without catching its failure. In this
model that target is `.calls e inner false .returns`.

## Modelling choices

As at the pin (`Specs/Reentrancy.lean`, "Modelling choices"), with these differences:

* **The entry points** are `L2InteropHandler`'s three: `executeAtomicBundle`, `verifyAtomicBundle`
  and `unbundleBundle`. There is no `Variant`: this is the deployed write order only.
* **The flow gate is logged.** When `requireFlowFinalized` returns in a frame that commits, the log
  records it: `Event.gated h` from `executeAtomicBundle`, `Event.verified h` from
  `verifyAtomicBundle` (which then emits `BundleVerified(h)`). It is a static call and writes
  nothing. Logging it lets the properties say that a delivery came after the gate passed. Its
  verdict is an input bit (`gateOk`), consulted only where the source consults it:
  `executeAtomicBundle` of a `Verified` bundle ignores it. Deliveries and `BundleExecuted` are
  `Event.effect` of the pinned `Effect`, and `effects` recovers the pinned log.
* **Reject-only checks are omitted**, as at the pin: the execution and unbundling permissions
  (`InteropHandlerBase.sol:118-132`, `:239-255`, `:261-278`, `:423-430`), the destination context
  (`:390-410`), the bundle and call versions and the shadow-account flag (`:230`, `:366`, `:369`),
  the pause gate, which is a no-op on L2 (`:81`), and the selector and value checks of a call.
  `AtomicUnbundlingAtHead` states the unbundling permission separately. The handler's other
  function, `initL2` (`L2InteropHandler.sol:33`), writes neither mapping.
-/

namespace Contracts.InteropHandlerAtHead

open AttackVectors.BundleStatusMachine (Status CallStatus)
open Contracts.InteropHandler (BundleHash Bundle State Effect markCalls toExecute)

/-- A call of one of `L2InteropHandler`'s entry points at head, at top level or re-entrantly. -/
inductive Entry
  /-- `executeAtomicBundle(_bundle, _finality)` (`L2InteropHandler.sol:51-68`); `gateOk` is
  `requireFlowFinalized`'s verdict on `_finality` (`:64`), consulted only when the bundle is not
  `Verified`. -/
  | executeAtomicBundle (b : Bundle) (gateOk : Bool)
  /-- `verifyAtomicBundle(_bundle, _finality)` (`L2InteropHandler.sol:73-82`); `gateOk` is
  `requireFlowFinalized`'s verdict on `_finality` (`:79`). -/
  | verifyAtomicBundle (b : Bundle) (gateOk : Bool)
  /-- `unbundleBundle(_bundle, _providedCallStatus)` (`InteropHandlerBase.sol:113-175`). -/
  | unbundleBundle (b : Bundle) (req : List CallStatus)

/-- The bundle an entry-point call names. -/
def Entry.bundle : Entry → Bundle
  | .executeAtomicBundle b _ => b
  | .verifyAtomicBundle b _ => b
  | .unbundleBundle b _ => b

/-- What the target of one delivered call does, from the moment its `receiveMessage` is called
(`InteropHandlerBase.sol:374-380`) until it returns. As at the pin. -/
inductive Callee
  /-- Returns the expected selector (`:381`). -/
  | returns
  /-- Reverts, or returns another selector. This also stands for the call's own checks failing
  before the target runs (`:366`, `:369`, `:371`). -/
  | reverts
  /-- Calls entry point `e`; `inner` are the targets of the calls that frame delivers, in order. If
  that frame reverts, the target either catches the failure (`caught`) and goes on from the state
  before the call, or reverts. Then it goes on as `next`. -/
  | calls (e : Entry) (inner : List Callee) (caught : Bool) (next : Callee)

/-- A committed event. -/
inductive Event
  /-- A delivery or a `BundleExecuted`, as at the pin. -/
  | effect (e : Effect)
  /-- `executeAtomicBundle` of the bundle with hash `h` called `requireFlowFinalized`, and it
  returned (`L2InteropHandler.sol:63-65`). -/
  | gated (h : BundleHash)
  /-- `verifyAtomicBundle` of the bundle with hash `h`: `requireFlowFinalized` returned (`:79`) and
  `BundleVerified(h)` was emitted (`:81`; `InteropHandlerBase.sol:317-320`). -/
  | verified (h : BundleHash)
deriving DecidableEq

/-- The deliveries and `BundleExecuted` events of a log, in order: the pinned model's log. -/
def effects (l : List Event) : List Effect :=
  l.filterMap fun
    | .effect e => some e
    | _ => none

/-- The flow gate passed for the bundle hash `h` somewhere in `l`, through either entry point. -/
def GatePassed (h : BundleHash) (l : List Event) : Prop :=
  Event.gated h ∈ l ∨ Event.verified h ∈ l

/-- What runs: an entry point, the call loop of one, or the target of one delivered call. -/
inductive Frame
  /-- Entry point `e`; `callees` are the targets of the calls it delivers, in order (a missing
  one returns). -/
  | entry (e : Entry) (callees : List Callee)
  /-- `_executeCalls` delivering calls `is` of bundle `h`, in order. -/
  | calls (h : BundleHash) (is : List ℕ) (callees : List Callee)
  /-- One delivered call's target. -/
  | target (c : Callee)

/-- `_markFullyExecutedAndRun`'s writes before the calls (`InteropHandlerBase.sol:326-331`): the
pinned whole-bundle write, unread call statuses included. -/
def markFullyExecuted (b : Bundle) (s : State) : State :=
  (s.setBundle b.hash .FullyExecuted).executeAll b.hash b.calls

/-- What `executeAtomicBundle` logs before its calls: the flow gate, unless the bundle was already
`Verified` and the gate was skipped (`L2InteropHandler.sol:63-65`). -/
def gateLog (s : State) (h : BundleHash) : List Event :=
  if s.bundle h = .Verified then [] else [.gated h]

/-- **The semantics.** `exec n f s` runs frame `f` from state `s` with budget `n`: the state and
committed log it leaves, or `none` if it reverts. -/
def exec : ℕ → Frame → State → Option (State × List Event)
  | 0, _, _ => none
  | n + 1, .entry (.executeAtomicBundle b gateOk) cs, s =>
      if s.bundle b.hash = .Verified ∨ (s.bundle b.hash = .Unreceived ∧ gateOk = true) then
        match exec n (.calls b.hash (List.range b.calls) cs) (markFullyExecuted b s) with
        | some (s₂, l) => some (s₂, gateLog s b.hash ++ l ++ [.effect (.executed b.hash)])
        | none => none
      else none
  | _ + 1, .entry (.verifyAtomicBundle b gateOk) _, s =>
      if s.bundle b.hash = .Unreceived ∧ gateOk = true then
        some (s.setBundle b.hash .Verified, [.verified b.hash])
      else none
  | n + 1, .entry (.unbundleBundle b req) cs, s =>
      if req.length = b.calls ∧
          (s.bundle b.hash = .Verified ∨ s.bundle b.hash = .Unbundled) then
        match markCalls true b.hash 0 req (s.setBundle b.hash .Unbundled) with
        | some s₁ => exec n (.calls b.hash (toExecute 0 req) cs) s₁
        | none => none
      else none
  | _ + 1, .calls _ [] _, s => some (s, [])
  | n + 1, .calls h (i :: is) cs, s =>
      match exec n (.target (cs.headD .returns)) s with
      | some (s₁, l₁) =>
          match exec n (.calls h is cs.tail) s₁ with
          | some (s₂, l₂) => some (s₂, .effect (.delivered h i) :: (l₁ ++ l₂))
          | none => none
      | none => none
  | _ + 1, .target .returns, s => some (s, [])
  | _ + 1, .target .reverts, _ => none
  | n + 1, .target (.calls e inner caught next), s =>
      match exec n (.entry e inner) s with
      | some (s₁, l₁) =>
          match exec n (.target next) s₁ with
          | some (s₂, l₂) => some (s₂, l₁ ++ l₂)
          | none => none
      | none => if caught then exec n (.target next) s else none

/-- The commit rule: a transaction that reverts leaves the state and the log as they were, as at the
pin (`VM-REVERT` as modelled). -/
def commit (s : State) : Option (State × List Event) → State × List Event
  | some r => r
  | none => (s, [])

/-- A submitted transaction: an entry point, the targets of the calls it delivers, and a budget. -/
structure Tx where
  /-- The depth and loop budget. -/
  fuel : ℕ
  /-- The entry point called. -/
  entry : Entry
  /-- The targets of the calls it delivers, in order. -/
  callees : List Callee

/-- One transaction: the state after it and what it committed. -/
def submit (s : State) (t : Tx) : State × List Event :=
  commit s (exec t.fuel (.entry t.entry t.callees) s)

/-- A sequence of transactions: the final state and the committed log, in order. -/
def submitAll : State → List Tx → State × List Event
  | s, [] => (s, [])
  | s, t :: ts =>
      ((submitAll (submit s t).1 ts).1, (submit s t).2 ++ (submitAll (submit s t).1 ts).2)

/-! ## Witness data

The pinned witness bundles: `wA` (hash `1`, two calls) and `wB` (hash `2`, one call). -/

open Contracts.InteropHandler (wA wB)

/-- A target that calls `e` (whose calls' targets return) and returns, catching a failure or not. -/
def reenter (e : Entry) (caught : Bool) : Callee := .calls e [] caught .returns

/-- The pinned `wNested` at head: atomic execution of `wA`, whose call 0 target executes `wB`
re-entrantly, then tries `wA` again and catches the refusal. -/
def wNested : Tx :=
  ⟨8, .executeAtomicBundle wA true,
    [.calls (.executeAtomicBundle wB true) [] false
      (reenter (.executeAtomicBundle wA true) true)]⟩

/-- Atomic execution of `wA`, whose call 0 target verifies `wB` and then unbundles it, executing its
only call, both re-entrantly; then it tries to verify `wA` and catches the refusal. -/
def wNestedUnbundle : Tx :=
  ⟨12, .executeAtomicBundle wA true,
    [.calls (.verifyAtomicBundle wB true) [] false
      (.calls (.unbundleBundle wB [.Executed]) [] false
        (reenter (.verifyAtomicBundle wA true) true))]⟩

end Contracts.InteropHandlerAtHead
