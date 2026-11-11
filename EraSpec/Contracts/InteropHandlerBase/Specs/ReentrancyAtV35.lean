import EraSpec.Contracts.InteropHandlerBase.Specs.Reentrancy

/-!
# Model: re-entrant bundle execution in the interop handlers, at draft/v0.35.0

Source: era-contracts branch `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`
(`d9f6789`). Paths are relative to `l1-contracts/contracts/`. In this header `IHB` is
`interop/interop-handler/InteropHandlerBase.sol`, `L2` is
`interop/interop-handler/L2InteropHandler.sol` and `L1` is
`interop/interop-handler/L1InteropHandler.sol`; every line number is at `d9f6789`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.InteropHandlerBase.Properties.ReentrancyAtV35` and are proved in
`EraSpec.Contracts.InteropHandlerBase.Proofs.ReentrancyAtV35`. The pin model
(`Specs/Reentrancy.lean`, era-contracts `c67894b9`) is left as it is; this file adds a model of
the v35 code beside it.

**Also at main `3605e82`.** At main the three handler files differ from `d9f6789` only by the
getter names (`_executeBundleSelector`, `_verifyBundleSelector`,
`_expectedDestinationBaseTokenAssetId`) and by `L2InteropHandler.updateL2` (absent at main, so
main's `L2` line numbers after `:34` are 10 lower). Everything modelled here, and every result
about it, also describes main.

## What changed since the pin

* **Public L2→L2 interop is gone** (era-contracts `a1d5c34d4`, #2280). `executeBundle`,
  `verifyBundle` and `_verifyBundle` left the base and L2. L2 now has exactly the atomic pair
  `executeAtomicBundle` (`L2:61-78`) and `verifyAtomicBundle` (`L2:83-92`, new). L1 has the
  message-inclusion pair `executeBundle` (`L1:81-98`) and `verifyBundle` (`L1:103-110`), for
  L2→L1 withdrawals only. `unbundleBundle` (`IHB:113-175`) is shared and unchanged.
* **`executeAtomicBundle` admits `Verified`, and then skips the gate.** `_requireExecutable`
  (`IHB:282-287`) admits `Unreceived` or `Verified`, and `requireFlowFinalized` runs only
  `if (status != BundleStatus.Verified)` (`L2:73-75`). At the pin it admitted `Unreceived` only
  and always ran the gate (pin `L2:79`, `:83`).
* **An atomic bundle can now be verified, then unbundled.** `verifyAtomicBundle` runs the gate and
  then `_markVerified` (`IHB:317-320`), which is the only writer of `Verified` on L2. So an atomic
  bundle can take `Unreceived → Verified → Unbundled`, with calls executed or cancelled one by one
  (documented upstream at `protocol-docs/interop.md:256`).

## The handler's replay state (unchanged; reused from the pin model)

    mapping(bytes32 => BundleStatus) public bundleStatus;                      // IHB:55
    mapping(bytes32 => mapping(uint256 => CallStatus)) public callStatus;      // IHB:58
    uint256[50] private __gap;                                                 // IHB:63

The slots are the pin's (1 and 2). The gap is new and occupies slots 3-52. The enums are
`common/Messaging.sol:283-288` (`BundleStatus`) and `:253-257` (`CallStatus`), with the same
members in the same order. So this model reuses the pin model's `State`, `init`, `Bundle`,
`Effect`, the state updates `setBundle`/`setCall`/`executeAll`/`executeEach`/`verifyIfUnreceived`,
the unbundle loop `markCalls`/`toExecute`, the countermodel orders `Variant` and their write
functions `beforeCalls`/`afterCalls`/`writesCallsFirst`/`afterUnbundle`, and the predicates
`Spent`, `Recorded` and `CallsClosed`. Their docstrings cite the pin; at `d9f6789` the lines are:

| pin model cite | v35 line |
|---|---|
| `bundleStatus :54`, `callStatus :57` | `IHB:55`, `IHB:58` |
| `_getBundleData :242-251` (hash `:249`) | `IHB:224-233` (hash `:231`) |
| executeBundle's writes `:126`, `:129-132` | `_markFullyExecutedAndRun` `IHB:326`, `:329-331` |
| `_executeCalls(_executeAllCalls: true)` `:137-143`, `emit :146` | `IHB:333-339`, `:341` |
| `verifyIfUnreceived` (`:123`, write `:312`) | L1 only: `L1:92-95`, `_markVerified` `IHB:318` |
| unbundle status check `:195`, write `:198` | `IHB:139`, `IHB:147` |
| unbundle first loop `:200-219` (`:207`, `:208`, `:212`) | `IHB:149-164` (`:154`, `:155`, `:158`) |
| unbundle `_executeCalls` `:221-227` | `IHB:166-172` |
| `_executeCalls :259-289`; skip `:268-274`; version `:276`; value `:279`; call `:282-287` | `IHB:350-383`; `:359-364`; `:366`; `:371`; `:374-381` |
| `Messaging.sol:270-274`, `:303-308` | `common/Messaging.sol:253-257`, `:283-288` |

## The entry points, per layer (none carries `nonReentrant`)

    L2 executeAtomicBundle (L2:61-78)
      _getBundleData                                                   // L2:62
      _validateExecutable: pause (no-op on L2, IHB:81), permission,
        require(status == Unreceived || status == Verified)            // L2:65; IHB:292-300, :282-287
      _validateBundleDestinationContext(..., bundle.sourceChainId)     // L2:70 (reject-only)
      if (status != Verified) requireFlowFinalized(bundleHash, ...)    // L2:73-75
      _markFullyExecutedAndRun:                                        // L2:77
        bundleStatus = FullyExecuted                                   // IHB:326 (CEI)
        for i: callStatus[i] = Executed                                // IHB:329-331
        _executeCalls(_executeAllCalls: true)                          // IHB:333-339
        emit BundleExecuted                                            // IHB:341

    L2 verifyAtomicBundle (L2:83-92)
      _validateVerifiable: destination context, require(status == Unreceived)   // L2:86; IHB:306-314
      requireFlowFinalized(bundleHash, _finality)                      // L2:89
      _markVerified: bundleStatus = Verified, emit BundleVerified      // L2:91; IHB:317-320

    L1 executeBundle (L1:81-98)
      require(calls.length == 1)                                       // L1:85 (reject-only)
      _validateExecutable (pause, permission, Unreceived || Verified)  // L1:88
      if (status != Verified) _verifyBundle(...)                       // L1:92-95
        _validateVerifiable (destination context, Unreceived)          // L1:211
        message sender check, data substitution, _proveInclusion       // L1:213-221
        _markVerified: bundleStatus = Verified                         // L1:223; IHB:318
      _markFullyExecutedAndRun (as on L2)                              // L1:97

    L1 verifyBundle (L1:103-110) = _verifyBundle (L1:203-224)

    unbundleBundle (IHB:113-175), both layers, body unchanged from the pin
      _ensureNotPaused; unbundler permission                           // IHB:114, :118-132
      require(calls.length == _providedCallStatus.length)              // IHB:134-137
      require(status == Verified || status == Unbundled)               // IHB:139
      bundleStatus = Unbundled                                         // IHB:147 (CEI)
      first loop                                                       // IHB:149-164
      _executeCalls(_executeAllCalls: false, _providedCallStatus)      // IHB:166-172

    _executeCalls (IHB:350-383)
      skip unless requested Executed (unbundle route)                  // IHB:359-364
      require(version), require(!shadowAccount)                        // IHB:366, :369
      _handleCallValue(value, sourceChainId)                           // IHB:371
      selector = IERC7786Recipient(_interopCallTarget(to)).receiveMessage{value}(...)   // IHB:374-380
      require(selector == receiveMessage.selector)                     // IHB:381

On L2, under `.deployed`, `executeAtomicBundle` writes nothing before `FullyExecuted`, while
L1's `executeBundle` first writes `Verified` for an `Unreceived` bundle. The `Verified` write is
overwritten by `FullyExecuted` before any call runs, so the two are indistinguishable from the
calls' point of view. That is the content of the bisimulation `Properties.ExecMatchesPinAtV35`.

## Where execution can re-enter

Only at the target's `receiveMessage` (`IHB:374-380`, no `try`/`catch`). Every other external call
the handler makes is a static call or reaches no entry point:

* `requireFlowFinalized` (`atomic-interop/IAtomicFlowManager.sol:45`, `external view`;
  implementation `atomic-interop/AtomicFlowManager.sol:176-213`) is a static call. At v35 it also
  reads the mutable `L2Bridgehub.isPeerAllowed` through `_checkLegSourceAllowed`
  (`AtomicFlowManager.sol:201`, `:338-344`), still inside the static call. So its verdict for a
  fixed proof can change between transactions, never within one. The model takes the verdict as
  a per-entry input, which covers both.
* `_getExpectedDestinationBaseTokenAssetId` on L2 (`L2:157-159`) calls
  `L2_NATIVE_TOKEN_VAULT.BASE_TOKEN_ASSET_ID()` from an `internal view` function, so as a static
  call; on L1 it is pure computation (`L1:181-183`).
* `_proveInclusion` exists on L1 only (`L1:227-236`, `internal view`); its call to
  `MESSAGE_ROOT.proveL2MessageInclusionShared` (`common/interfaces/IMessageVerification.sol:18-24`,
  `external view`) is a static call. L2 no longer proves message inclusion.
* `_handleCallValue` on L2 (`L2:149-154`) calls `BaseTokenHolder.give`
  (`l2-system/BaseTokenHolder.sol:67-76`). That calls
  `L2AssetTracker.handleFinalizeBaseTokenBridgingOnL2` (`bridge/asset-tracker/L2AssetTracker.sol:277-298`),
  whose inner function (`:209-229`) reads system contracts (`L2_NATIVE_TOKEN_VAULT.originChainId`,
  `IERC20(L2_BASE_TOKEN_SYSTEM_CONTRACT).balanceOf`, `L2_SYSTEM_CONTEXT_SYSTEM_CONTRACT`) and
  writes only tracker storage. `give` then sends the value to the handler's `receive()`
  (`L2:164-168`), which writes nothing. None of these is the handler, and none calls it. On L1
  `_handleCallValue` only checks the value is zero (`L1:175-177`). In this model its only effect
  is that it may revert.

The target is arbitrary code, as in the pin model. On L1 the target is pinned to `L1_ASSET_ROUTER`
(`_interopCallTarget`, `L1:189-192`); the arbitrary target over-approximates it. When the target
is the handler itself, `receiveMessage` (`IHB:188-213`) requires `msg.sender == address(this)`,
makes exactly one of the layer's execute, verify and unbundle self-calls (`L2:130`, `L2:141`,
`IHB:432`; `L1:148`, `L1:159`), and does not catch its failure. In this model that is the target
`.calls e inner false .returns`.

## Modelling choices

* **Per-layer entry sets.** `EntryAtV35 ℓ` has three constructors, the same for both layers
  (`execute`, `verify`, `unbundleBundle`), which is how the base itself abstracts them
  (`_getExecuteBundleSelector`/`_getVerifyBundleSelector`, `IHB:89-106`). The layer `ℓ` is a type
  parameter, so one tree holds one layer's entry points only; there is no `executeAtomicBundle` on
  L1. On L2, `execute` is `executeAtomicBundle` and `verify` is `verifyAtomicBundle`; on L1 they
  are `executeBundle` and `verifyBundle` (abbreviations below).
* **Oracles are inputs.** `ok` is the verdict of the layer's proof oracle on the supplied proof:
  `requireFlowFinalized` on L2, `_verifyBundle`'s message checks and `_proveInclusion` on L1.
  `execute` consults it only when the bundle is `Unreceived`.
* **Everything else is the pin model's**: `Callee` trees, fuel, `none` for a revert that leaves
  nothing, the committed log as the trace, a bundle as its hash and its number of calls.
* **Reject-only checks are omitted**: the permission gates (`_requireExecutionAllowed`
  `IHB:239-255`, the unbundler gate `IHB:118-132`), the destination context (`IHB:390-410`), the
  versions (`IHB:230`, `:366`), `require(!shadowAccount)` (`IHB:369`), L1's single-call rule
  (`L1:85`) and target pin (`L1:189-192`), the pause gate (`L1:168-170`), and the selector and
  value checks of a call (folded into its target's failure). Omitting a check that can only revert
  only adds runs.
* **The handler's other functions write neither mapping.** `initL2` (`L2:34`) only locks the
  reentrancy guard. On L1, `initialize`, `pause`, `unpause` (`L1:59-72`) and ownership write OZ
  storage only. `updateL2` (`L2:38-43`, new in v35, `onlyUpgrader`) does `sstore(101, 0)`
  (`interop/InteropConstants.sol:12`). Slot 101 is past the gap (slots 3-52) and is neither
  mapping's base slot. A mapping entry lives at a keccak image, so slot 101 holds one only if
  keccak maps some `abi.encode(key, slot)` preimage to 101, which this model does not track.
* **Countermodel orders** reuse the pin's `Variant`: `statusWriteAfterCalls` moves
  `_markFullyExecutedAndRun`'s `FullyExecuted` write (`IHB:326`) after `_executeCalls`;
  `callWriteAfterCalls` moves `unbundleBundle`'s `Executed` write (`IHB:155`) after it.
* **Ghost state for the gate.** `GhostStateAtV35` adds `passed : BundleHash → Bool`, set when an
  entry evaluates its oracle and it says yes (`execute` on an `Unreceived` bundle, `verify`), in a
  frame that commits. `ghostExecAtV35` is `execAtV35 .deployed` with that bookkeeping; its
  erasure is `Properties.GhostErasesAtV35`.
-/

namespace Contracts.InteropHandlerAtV35

open AttackVectors.BundleStatusMachine (Status CallStatus)
open Contracts.InteropHandler (BundleHash Bundle State init Effect Variant beforeCalls afterCalls
  writesCallsFirst afterUnbundle markCalls toExecute commit)

/-- The layer a v35 handler is deployed on. -/
inductive LayerAtV35
  /-- `L1InteropHandler` (`L1:37`): L2→L1 withdrawals, proven by message inclusion. -/
  | l1
  /-- `L2InteropHandler` (`L2:22`): L2→L2 atomic interop, proven by the flow gate. -/
  | l2
deriving DecidableEq

/-- A call of one of a v35 handler's entry points on layer `ℓ`, at top level or re-entrantly. -/
inductive EntryAtV35 (ℓ : LayerAtV35)
  /-- The layer's proof-typed execution: `executeAtomicBundle(_bundle, _finality)` on L2
  (`L2:61-78`), `executeBundle(_bundle, _proof)` on L1 (`L1:81-98`). `ok` is the oracle's verdict,
  consulted only when the bundle is `Unreceived` (`L2:73-75`; `L1:92-95`). -/
  | execute (b : Bundle) (ok : Bool)
  /-- The layer's proof-typed verification: `verifyAtomicBundle` on L2 (`L2:83-92`),
  `verifyBundle` on L1 (`L1:103-110`, `_verifyBundle` `L1:203-224`). -/
  | verify (b : Bundle) (ok : Bool)
  /-- `unbundleBundle(_bundle, _providedCallStatus)` (`IHB:113-175`), on both layers. -/
  | unbundleBundle (b : Bundle) (req : List CallStatus)

/-- `executeAtomicBundle(_bundle, _finality)` (`L2:61-78`); `gateOk` is `requireFlowFinalized`'s
verdict (`L2:74`). -/
abbrev executeAtomicBundleAtV35 (b : Bundle) (gateOk : Bool) : EntryAtV35 .l2 := .execute b gateOk

/-- `verifyAtomicBundle(_bundle, _finality)` (`L2:83-92`); `gateOk` is `requireFlowFinalized`'s
verdict (`L2:89`). -/
abbrev verifyAtomicBundleAtV35 (b : Bundle) (gateOk : Bool) : EntryAtV35 .l2 := .verify b gateOk

/-- L1's `executeBundle(_bundle, _proof)` (`L1:81-98`); `proofOk` is `_verifyBundle`'s verdict. -/
abbrev executeBundleL1AtV35 (b : Bundle) (proofOk : Bool) : EntryAtV35 .l1 := .execute b proofOk

/-- L1's `verifyBundle(_bundle, _proof)` (`L1:103-110`). -/
abbrev verifyBundleL1AtV35 (b : Bundle) (proofOk : Bool) : EntryAtV35 .l1 := .verify b proofOk

/-- The bundle an entry-point call names. -/
def EntryAtV35.bundle {ℓ : LayerAtV35} : EntryAtV35 ℓ → Bundle
  | .execute b _ => b
  | .verify b _ => b
  | .unbundleBundle b _ => b

/-- What the target of one delivered call does, from the moment its `receiveMessage` is called
(`IHB:374-380`) until it returns. -/
inductive CalleeAtV35 (ℓ : LayerAtV35)
  /-- Returns the expected selector (`IHB:381`). -/
  | returns
  /-- Reverts, or returns another selector. This also stands for the call's own checks failing
  before the target runs (`IHB:366`, `:369`, `:371`, and on L1 `_interopCallTarget`, `L1:190`). -/
  | reverts
  /-- Calls entry point `e`; `inner` are the targets of the calls that frame delivers, in order.
  If that frame reverts, the target either catches the failure (`caught`) and goes on from the
  state before the call, or reverts. Then it goes on as `next`. -/
  | calls (e : EntryAtV35 ℓ) (inner : List (CalleeAtV35 ℓ)) (caught : Bool) (next : CalleeAtV35 ℓ)

/-- What runs: an entry point, the call loop of one, or the target of one delivered call. -/
inductive FrameAtV35 (ℓ : LayerAtV35)
  /-- Entry point `e`; `callees` are the targets of the calls it delivers, in order (a missing
  one returns). -/
  | entry (e : EntryAtV35 ℓ) (callees : List (CalleeAtV35 ℓ))
  /-- `_executeCalls` delivering calls `is` of bundle `h`, in order (`IHB:350-383`). -/
  | calls (h : BundleHash) (is : List ℕ) (callees : List (CalleeAtV35 ℓ))
  /-- One delivered call's target. -/
  | target (c : CalleeAtV35 ℓ)

/-- What a whole-bundle execution writes between its checks and `_markFullyExecutedAndRun`. On
L1, `_verifyBundle` ends in `_markVerified` for an `Unreceived` bundle (`L1:92-95`, `:223`,
`IHB:318`). On L2 nothing: `requireFlowFinalized` is a static call (`L2:73-75`). -/
def proofWriteAtV35 : LayerAtV35 → BundleHash → State → State
  | .l1, h, s => s.verifyIfUnreceived h
  | .l2, _, s => s

/-- **The v35 semantics.** `execAtV35 ℓ v n f s` runs frame `f` of a layer-`ℓ` handler from state
`s` with budget `n`, in write order `v`: the state and committed log it leaves, or `none` if it
reverts. -/
def execAtV35 (ℓ : LayerAtV35) (v : Variant) :
    ℕ → FrameAtV35 ℓ → State → Option (State × List Effect)
  | 0, _, _ => none
  | n + 1, .entry (.execute b ok) cs, s =>
      if s.bundle b.hash = .Verified ∨ (s.bundle b.hash = .Unreceived ∧ ok = true) then
        match execAtV35 ℓ v n (.calls b.hash (List.range b.calls) cs)
            (beforeCalls v b (proofWriteAtV35 ℓ b.hash s)) with
        | some (s₂, l) => some (afterCalls v b s₂, l ++ [.executed b.hash])
        | none => none
      else none
  | _ + 1, .entry (.verify b ok) _, s =>
      if s.bundle b.hash = .Unreceived ∧ ok = true then
        some (s.setBundle b.hash .Verified, [])
      else none
  | n + 1, .entry (.unbundleBundle b req) cs, s =>
      if req.length = b.calls ∧
          (s.bundle b.hash = .Verified ∨ s.bundle b.hash = .Unbundled) then
        match markCalls (writesCallsFirst v) b.hash 0 req (s.setBundle b.hash .Unbundled) with
        | some s₁ =>
            match execAtV35 ℓ v n (.calls b.hash (toExecute 0 req) cs) s₁ with
            | some (s₂, l) => some (afterUnbundle v b.hash req s₂, l)
            | none => none
        | none => none
      else none
  | _ + 1, .calls _ [] _, s => some (s, [])
  | n + 1, .calls h (i :: is) cs, s =>
      match execAtV35 ℓ v n (.target (cs.headD .returns)) s with
      | some (s₁, l₁) =>
          match execAtV35 ℓ v n (.calls h is cs.tail) s₁ with
          | some (s₂, l₂) => some (s₂, .delivered h i :: (l₁ ++ l₂))
          | none => none
      | none => none
  | _ + 1, .target .returns, s => some (s, [])
  | _ + 1, .target .reverts, _ => none
  | n + 1, .target (.calls e inner caught next), s =>
      match execAtV35 ℓ v n (.entry e inner) s with
      | some (s₁, l₁) =>
          match execAtV35 ℓ v n (.target next) s₁ with
          | some (s₂, l₂) => some (s₂, l₁ ++ l₂)
          | none => none
      | none => if caught then execAtV35 ℓ v n (.target next) s else none

/-- A submitted transaction to a layer-`ℓ` handler: an entry point, the targets of the calls it
delivers, and a budget. -/
structure TxAtV35 (ℓ : LayerAtV35) where
  /-- The depth and loop budget. -/
  fuel : ℕ
  /-- The entry point called. -/
  entry : EntryAtV35 ℓ
  /-- The targets of the calls it delivers, in order. -/
  callees : List (CalleeAtV35 ℓ)

/-- One transaction: the state after it and what it committed (`VM-REVERT` as modelled, the pin
model's `commit`). -/
def submitAtV35 (ℓ : LayerAtV35) (v : Variant) (s : State) (t : TxAtV35 ℓ) :
    State × List Effect :=
  commit s (execAtV35 ℓ v t.fuel (.entry t.entry t.callees) s)

/-- A sequence of transactions: the final state and the committed log, in order. -/
def submitAllAtV35 (ℓ : LayerAtV35) (v : Variant) : State → List (TxAtV35 ℓ) → State × List Effect
  | s, [] => (s, [])
  | s, t :: ts =>
      ((submitAllAtV35 ℓ v (submitAtV35 ℓ v s t).1 ts).1,
        (submitAtV35 ℓ v s t).2 ++ (submitAllAtV35 ℓ v (submitAtV35 ℓ v s t).1 ts).2)

/-! ## The translation into the pin model

A v35 entry is sent to the pin entry with the same writes once the overwritten `Verified` is
ignored: `execute` to the pin's `executeBundle` (not `executeAtomicBundle`), `verify` to
`verifyBundle`, `unbundleBundle` to itself. -/

/-- The pin entry point with the same behaviour under `.deployed`. -/
def EntryAtV35.toPin {ℓ : LayerAtV35} : EntryAtV35 ℓ → Contracts.InteropHandler.Entry
  | .execute b ok => .executeBundle b ok
  | .verify b ok => .verifyBundle b ok
  | .unbundleBundle b req => .unbundleBundle b req

mutual
/-- A v35 target, as a pin target. -/
def CalleeAtV35.toPin {ℓ : LayerAtV35} : CalleeAtV35 ℓ → Contracts.InteropHandler.Callee
  | .returns => .returns
  | .reverts => .reverts
  | .calls e inner caught next =>
      .calls e.toPin (CalleeAtV35.listToPin inner) caught (CalleeAtV35.toPin next)

/-- A list of v35 targets, as pin targets. -/
def CalleeAtV35.listToPin {ℓ : LayerAtV35} :
    List (CalleeAtV35 ℓ) → List Contracts.InteropHandler.Callee
  | [] => []
  | c :: cs => CalleeAtV35.toPin c :: CalleeAtV35.listToPin cs
end

/-- A v35 frame, as a pin frame. -/
def FrameAtV35.toPin {ℓ : LayerAtV35} : FrameAtV35 ℓ → Contracts.InteropHandler.Frame
  | .entry e cs => .entry e.toPin (CalleeAtV35.listToPin cs)
  | .calls h is cs => .calls h is (CalleeAtV35.listToPin cs)
  | .target c => .target c.toPin

/-- A v35 transaction, as a pin transaction. -/
def TxAtV35.toPin {ℓ : LayerAtV35} (t : TxAtV35 ℓ) : Contracts.InteropHandler.Tx :=
  ⟨t.fuel, t.entry.toPin, CalleeAtV35.listToPin t.callees⟩

/-! ## Ghost state: whether a bundle's gate has passed -/

/-- The replay state with a ghost record of the bundle hashes whose oracle has said yes in a
committed frame. -/
structure GhostStateAtV35 where
  /-- The handler's storage. -/
  core : State
  /-- `passed h`: an entry evaluated the oracle on bundle hash `h`, it said yes, and that frame
  committed. Not in storage. -/
  passed : BundleHash → Bool

/-- Fresh storage, no gate passed yet. -/
def ghostInitAtV35 : GhostStateAtV35 := ⟨init, fun _ => false⟩

/-- Record that `h`'s gate passed when `cond` holds. -/
def markPassedAtV35 (cond : Bool) (h : BundleHash) (p : BundleHash → Bool) : BundleHash → Bool :=
  fun h' => if cond ∧ h' = h then true else p h'

/-- `execAtV35 ℓ .deployed`, with the gate bookkeeping: `execute` on an `Unreceived` bundle
evaluates the oracle (`L2:73-75`, `L1:92-95`), and `verify` always does (`L2:89`, `L1:211-221`). -/
def ghostExecAtV35 (ℓ : LayerAtV35) :
    ℕ → FrameAtV35 ℓ → GhostStateAtV35 → Option (GhostStateAtV35 × List Effect)
  | 0, _, _ => none
  | n + 1, .entry (.execute b ok) cs, g =>
      if g.core.bundle b.hash = .Verified ∨ (g.core.bundle b.hash = .Unreceived ∧ ok = true) then
        match ghostExecAtV35 ℓ n (.calls b.hash (List.range b.calls) cs)
            ⟨beforeCalls .deployed b (proofWriteAtV35 ℓ b.hash g.core),
              markPassedAtV35 (decide (g.core.bundle b.hash = .Unreceived)) b.hash g.passed⟩ with
        | some (g₂, l) => some (g₂, l ++ [.executed b.hash])
        | none => none
      else none
  | _ + 1, .entry (.verify b ok) _, g =>
      if g.core.bundle b.hash = .Unreceived ∧ ok = true then
        some (⟨g.core.setBundle b.hash .Verified, markPassedAtV35 true b.hash g.passed⟩, [])
      else none
  | n + 1, .entry (.unbundleBundle b req) cs, g =>
      if req.length = b.calls ∧
          (g.core.bundle b.hash = .Verified ∨ g.core.bundle b.hash = .Unbundled) then
        match markCalls true b.hash 0 req (g.core.setBundle b.hash .Unbundled) with
        | some s₁ =>
            match ghostExecAtV35 ℓ n (.calls b.hash (toExecute 0 req) cs) ⟨s₁, g.passed⟩ with
            | some (g₂, l) => some (g₂, l)
            | none => none
        | none => none
      else none
  | _ + 1, .calls _ [] _, g => some (g, [])
  | n + 1, .calls h (i :: is) cs, g =>
      match ghostExecAtV35 ℓ n (.target (cs.headD .returns)) g with
      | some (g₁, l₁) =>
          match ghostExecAtV35 ℓ n (.calls h is cs.tail) g₁ with
          | some (g₂, l₂) => some (g₂, .delivered h i :: (l₁ ++ l₂))
          | none => none
      | none => none
  | _ + 1, .target .returns, g => some (g, [])
  | _ + 1, .target .reverts, _ => none
  | n + 1, .target (.calls e inner caught next), g =>
      match ghostExecAtV35 ℓ n (.entry e inner) g with
      | some (g₁, l₁) =>
          match ghostExecAtV35 ℓ n (.target next) g₁ with
          | some (g₂, l₂) => some (g₂, l₁ ++ l₂)
          | none => none
      | none => if caught then ghostExecAtV35 ℓ n (.target next) g else none

/-- One transaction, with the ghost: a reverted transaction leaves the ghost as it was too. -/
def ghostSubmitAtV35 (ℓ : LayerAtV35) (g : GhostStateAtV35) (t : TxAtV35 ℓ) :
    GhostStateAtV35 × List Effect :=
  match ghostExecAtV35 ℓ t.fuel (.entry t.entry t.callees) g with
  | some r => r
  | none => (g, [])

/-- A sequence of transactions, with the ghost. -/
def ghostSubmitAllAtV35 (ℓ : LayerAtV35) :
    GhostStateAtV35 → List (TxAtV35 ℓ) → GhostStateAtV35 × List Effect
  | g, [] => (g, [])
  | g, t :: ts =>
      ((ghostSubmitAllAtV35 ℓ (ghostSubmitAtV35 ℓ g t).1 ts).1,
        (ghostSubmitAtV35 ℓ g t).2 ++ (ghostSubmitAllAtV35 ℓ (ghostSubmitAtV35 ℓ g t).1 ts).2)

/-- **The gate invariant.** Every bundle that has left `Unreceived` has had its gate pass. -/
def GatedAtV35 (g : GhostStateAtV35) : Prop :=
  ∀ h, g.core.bundle h ≠ .Unreceived → g.passed h = true

/-! ## The v35 receive filter, as the gate's mutable input

`requireFlowFinalized` reverts unless every leg's source is this chain or an allowed peer
(`_checkLegSourceAllowed`, `AtomicFlowManager.sol:338-344`, called at `:201`). `isPeerAllowed` is
`L2Bridgehub` storage (`core/bridgehub/L2Bridgehub.sol:43`), set by `allowInteropPeer` (`:95-98`)
and deleted by `deregisterChainForInterop` (`:102-104`). The flow manager side (stranding of
committed legs, refunds) is the concurrent `H-4` model of `AtomicFlowManager`; this file models
only what the handler sees: a verdict that depends on `isPeerAllowed` at the moment the gate
runs. -/

/-- `_checkLegSourceAllowed(src)` passes (`AtomicFlowManager.sol:338-344`). -/
def legSourceAllowedAtV35 (self : ℕ) (isPeerAllowed : ℕ → Bool) (src : ℕ) : Bool :=
  src == self || isPeerAllowed src

/-- `requireFlowFinalized`'s verdict as a function of the receive filter: the per-leg proof
checks (`proofsOk`, the rest of `AtomicFlowManager.sol:180-212`) and the filter on every leg's
source. -/
def gateVerdictAtV35 (self : ℕ) (isPeerAllowed : ℕ → Bool) (legSources : List ℕ)
    (proofsOk : Bool) : Bool :=
  proofsOk && legSources.all (legSourceAllowedAtV35 self isPeerAllowed)

/-- `deregisterChainForInterop(c)`: `delete isPeerAllowed[c]` (`L2Bridgehub.sol:102-104`). -/
def deregisterAtV35 (isPeerAllowed : ℕ → Bool) (c : ℕ) : ℕ → Bool :=
  fun c' => if c' = c then false else isPeerAllowed c'

/-! ## Witness data

The pin model's bundles: `wA` (hash 1, two calls), `wB` (hash 2, one call), `wC` (hash 3, one
call). -/

/-- A target that calls `e` (whose calls' targets return) and returns, catching a failure or
not. -/
def reenterAtV35 {ℓ : LayerAtV35} (e : EntryAtV35 ℓ) (caught : Bool) : CalleeAtV35 ℓ :=
  .calls e [] caught .returns

open Contracts.InteropHandler (wA wB wC requestFirst)

/-- Atomic execution of `wA` on L2. Call 0's target executes `wB` re-entrantly, then tries to
execute `wA` again and catches the failure; call 1's target returns. -/
def wNestedAtV35 : TxAtV35 .l2 :=
  ⟨8, executeAtomicBundleAtV35 wA true,
    [.calls (executeAtomicBundleAtV35 wB true) [] false
      (reenterAtV35 (executeAtomicBundleAtV35 wA true) true)]⟩

/-- The same, but the target does not catch the failed re-entry into `wA`. -/
def wNestedUncaughtAtV35 : TxAtV35 .l2 :=
  ⟨8, executeAtomicBundleAtV35 wA true,
    [.calls (executeAtomicBundleAtV35 wB true) [] false
      (reenterAtV35 (executeAtomicBundleAtV35 wA true) false)]⟩

/-- A failing attempt at `wA`: call 0's target executes `wB` re-entrantly and returns; call 1's
target reverts. -/
def wAttemptAtV35 : TxAtV35 .l2 :=
  ⟨8, executeAtomicBundleAtV35 wA true,
    [.calls (executeAtomicBundleAtV35 wB true) [] false .returns, .reverts]⟩

/-- The same attempt with call 1's target returning. -/
def wAttemptOkAtV35 : TxAtV35 .l2 :=
  ⟨8, executeAtomicBundleAtV35 wA true,
    [.calls (executeAtomicBundleAtV35 wB true) [] false .returns, .returns]⟩

/-- A retry of `wA` whose targets return. -/
def wRetryAtV35 : TxAtV35 .l2 := ⟨4, executeAtomicBundleAtV35 wA true, [.returns, .returns]⟩

/-- Atomic execution of `wA`. Call 0's target executes `wB` re-entrantly; `wB`'s only call
reverts, so that frame reverts, and the target catches the failure and returns. -/
def wCaughtAtV35 : TxAtV35 .l2 :=
  ⟨8, executeAtomicBundleAtV35 wA true,
    [.calls (executeAtomicBundleAtV35 wB true) [.reverts] true .returns]⟩

/-- Atomic execution of `wB` on its own. -/
def wRunBAtV35 : TxAtV35 .l2 := ⟨3, executeAtomicBundleAtV35 wB true, []⟩

/-- Atomic execution of `wC` with a passing gate, whose call's target executes `wC` again with
gate verdict `gate'`, catching a failure or not. -/
def wReenterAtomicAtV35 (gate' caught : Bool) : TxAtV35 .l2 :=
  ⟨6, executeAtomicBundleAtV35 wC true, [reenterAtV35 (executeAtomicBundleAtV35 wC gate') caught]⟩

/-- `verifyAtomicBundle` of `wC` with a passing gate. -/
def wVerifyCAtV35 : TxAtV35 .l2 := ⟨1, verifyAtomicBundleAtV35 wC true, []⟩

/-- Atomic execution of a verified `wC` with no passing gate, whose call's target does the same
again, not catching a failure. -/
def wReenterVerifiedAtV35 : TxAtV35 .l2 :=
  ⟨6, executeAtomicBundleAtV35 wC false, [reenterAtV35 (executeAtomicBundleAtV35 wC false) false]⟩

/-- L1 `executeBundle` of `wC` with a valid proof, whose call's target calls `executeBundle` of
`wC` again with no valid proof, not catching a failure. -/
def wReenterL1AtV35 : TxAtV35 .l1 :=
  ⟨6, executeBundleL1AtV35 wC true, [reenterAtV35 (executeBundleL1AtV35 wC false) false]⟩

/-- `unbundleBundle` of `wC` on L2 requesting its call, whose target makes the same request again,
catching a failure or not. -/
def wReenterUnbundleAtV35 (caught : Bool) : TxAtV35 .l2 :=
  ⟨6, .unbundleBundle wC [.Executed], [reenterAtV35 (.unbundleBundle wC [.Executed]) caught]⟩

/-- `verifyAtomicBundle` of `wA` with a passing gate. -/
def wVerifyAAtV35 : TxAtV35 .l2 := ⟨1, verifyAtomicBundleAtV35 wA true, []⟩

/-- `unbundleBundle` of `wA` executing call 0 and cancelling call 1; both targets return. -/
def wUnbundleExecCancelAtV35 : TxAtV35 .l2 := ⟨4, .unbundleBundle wA [.Executed, .Cancelled], []⟩

/-- `executeAtomicBundle` of `wA` with no passing gate; both targets return. -/
def wExecANoGateAtV35 : TxAtV35 .l2 := ⟨4, executeAtomicBundleAtV35 wA false, []⟩

end Contracts.InteropHandlerAtV35
