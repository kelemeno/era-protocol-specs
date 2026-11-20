import EraSpec.Contracts.InteropHandlerBase.Specs.Reentrancy

/-!
# Model: re-entrant bundle execution in the interop handlers, at draft/v0.35.0

Source: era-contracts branch `draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`
(`b17415d20`). Paths are relative to `l1-contracts/contracts/`. In this file `IHB` is
`interop/interop-handler/InteropHandlerBase.sol`, `L2` is
`interop/interop-handler/L2InteropHandler.sol` and `L1` is
`interop/interop-handler/L1InteropHandler.sol`; every line number is at `b17415d20`.

**Pin history.** This model was first written against `d9f678900e1bc8286412b78f56d4a9f443983c29`
(`d9f6789`). Every file it cites is byte-identical at `d9f6789` and `b17415d20` (the three commits
between them touch upgrade and governance contracts only), so every line number below holds at
both.

**This file is definitions only.** The results are in
`EraSpec.Contracts.InteropHandlerBase.Properties.ReentrancyAtV35` and are proved in
`EraSpec.Contracts.InteropHandlerBase.Proofs.ReentrancyAtV35`. This is the `b17415d20` layer of
topic `Reentrancy`; the engine it is translated into is `Specs/Reentrancy.lean`
(`Contracts.InteropHandler`), and `EntryAtV35.toPin` below is the translation. (The `…Pin…` names
of this file refer to that engine, whose fourth entry point is the pin `c67894b9`'s
`executeAtomicBundle`.)

**Main.** At main `70096e2` the three handler files are those of main `3605e82`. They differ
from `b17415d20` only by the names of three internal getters (`_executeBundleSelector`,
`_verifyBundleSelector`, `_expectedDestinationBaseTokenAssetId` at main; the two selector getters
are also `view` there instead of `pure`) and by `L2InteropHandler.updateL2` and its import, which
main does not have (main's `L2` lines are 1 lower for `:9-35` and 10 lower from `:45` on). So
`execAtV35` models main's handlers too. The receive-filter section does not apply to main: main's
`requireFlowFinalized` (`atomic-interop/AtomicFlowManager.sol:175`) has no
`_checkLegSourceAllowed`, and main's `L2Bridgehub` has no `isPeerAllowed`. Lines cited in files
other than the three handlers can differ at main.

## What changed since the pin

* **Public L2→L2 interop is gone** (era-contracts `a1d5c34d4`, #2280). `executeBundle`,
  `verifyBundle` and `_verifyBundle` left the base and L2. L2 now has exactly the atomic pair
  `executeAtomicBundle` (`L2:61-78`) and `verifyAtomicBundle` (`L2:83-92`, new). L1 has the
  message-inclusion pair `executeBundle` (`L1:81-98`) and `verifyBundle` (`L1:103-110`), for
  L2→L1 withdrawals only. `unbundleBundle` (`IHB:113-175`) is shared; its code is the pin's,
  apart from comments.
* **`executeAtomicBundle` admits `Verified`, and then skips the gate.** `_requireExecutable`
  (`IHB:282-287`) admits `Unreceived` or `Verified`, and `requireFlowFinalized` runs only
  `if (status != BundleStatus.Verified)` (`L2:73-75`). At the pin it admitted `Unreceived` only
  and always ran the gate (pin `L2:79`, `:83`).
* **An atomic bundle can now be verified, then unbundled.** `verifyAtomicBundle` runs the gate and
  then `_markVerified` (`IHB:317-320`), which on L2 is called from `verifyAtomicBundle` only
  (`L2:91`). So an atomic bundle can take `Unreceived → Verified → Unbundled`, with calls
  executed or cancelled one by one (documented upstream at `protocol-docs/interop.md:256`).

## The handler's replay state (the engine's)

    mapping(bytes32 => BundleStatus) public bundleStatus;                      // IHB:55
    mapping(bytes32 => mapping(uint256 => CallStatus)) public callStatus;      // IHB:58
    uint256[50] private __gap;                                                 // IHB:63

The gap occupies slots 3-52. The writes to the two mappings in the three handler files are exactly
`IHB:147`, `:155`, `:160`, `:318`, `:326` and `:330`. So this layer reuses the engine's `State`,
`init`, `Bundle`, `Effect`, the state updates `setBundle`/`setCall`/`executeAll`/`executeEach`/
`verifyIfUnreceived`, the unbundle loop `markCalls`/`toExecute`, the countermodel orders `Variant`
and their write functions `beforeCalls`/`afterCalls`/`writesCallsFirst`/`afterUnbundle`, and the
predicates `Spent`, `Recorded` and `CallsClosed`, all cited at `b17415d20` in
`Specs/Reentrancy.lean`.

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

    unbundleBundle (IHB:113-175), both layers
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

On L2, `executeAtomicBundle` writes nothing before `FullyExecuted`, while L1's `executeBundle`
first writes `Verified` for an `Unreceived` bundle, as the engine's `executeBundle` does.
`_markFullyExecutedAndRun` overwrites that `Verified` with `FullyExecuted` before any call runs,
so in the deployed order both layers' `execute` run their calls from the state the pin's
`executeBundle` runs them from. That is why the translation below sends both layers' `execute` to
the engine's `executeBundle`.

## Where execution can re-enter

Only at the target's `receiveMessage` (`IHB:374-380`, no `try`/`catch`). The handler's other
external calls are static calls or reach no entry point:

* `requireFlowFinalized` (`atomic-interop/IAtomicFlowManager.sol:45`, `external view`;
  implementation `atomic-interop/AtomicFlowManager.sol:176-213`) is a static call. At v35 it also
  reads the mutable `L2Bridgehub.isPeerAllowed` through `_checkLegSourceAllowed`
  (`AtomicFlowManager.sol:201`, `:338-344`), inside the static call.
* `_getExpectedDestinationBaseTokenAssetId` on L2 (`L2:157-159`) calls
  `L2_NATIVE_TOKEN_VAULT.BASE_TOKEN_ASSET_ID()`, declared `external view`
  (`bridge/ntv/IL2NativeTokenVault.sol:34`), so as a static call; on L1 it is pure computation
  (`L1:181-183`).
* `_proveInclusion` exists on L1 only (`L1:227-236`, `internal view`); its call to
  `MESSAGE_ROOT.proveL2MessageInclusionShared` (`common/interfaces/IMessageVerification.sol:18-24`,
  `external view`) is a static call. L2 no longer proves message inclusion.
* `_handleCallValue` on L2 (`L2:149-154`) calls `BaseTokenHolder.give`
  (`l2-system/BaseTokenHolder.sol:67-76`) for a nonzero value. That calls
  `L2AssetTracker.handleFinalizeBaseTokenBridgingOnL2`
  (`bridge/asset-tracker/L2AssetTracker.sol:277-298`), whose inner function (`:209-229`) reads
  system contracts and writes only tracker storage, and then sends the value to the handler's
  `receive()` (`L2:164-168`), which checks the sender and writes nothing. That transfer is the only
  call back into the handler, and it reaches no entry point. On L1 `_handleCallValue` only checks
  the value is zero (`L1:175-177`). In this model its only effect is that it may revert.

The target is arbitrary code, as in the engine. On L1 the target is pinned to `L1_ASSET_ROUTER`
(`_interopCallTarget`, `L1:189-192`); the arbitrary target over-approximates it. When the target
is the handler itself, `receiveMessage` (`IHB:188-213`) requires `msg.sender == address(this)`,
makes exactly one of the layer's execute, verify and unbundle self-calls (`L2:130`, `L2:141`,
`IHB:432`; `L1:148`, `L1:159`), and does not catch its failure. In this model that is the target
`.calls e inner false .returns`.

## Modelling choices

* **Per-layer entry sets.** `EntryAtV35 ℓ` has three constructors, the same for both layers
  (`execute`, `verify`, `unbundleBundle`), which is how the base itself abstracts them
  (`_getExecuteBundleSelector`/`_getVerifyBundleSelector`, `IHB:89-94`). The layer `ℓ` is a type
  parameter, so one tree holds one layer's entry points only. On L2, `execute` is
  `executeAtomicBundle` and `verify` is `verifyAtomicBundle`; on L1 they are `executeBundle` and
  `verifyBundle`. L2 has no entry point that consults an inclusion proof.
* **Oracles are inputs.** `ok` is the verdict of the layer's proof check on the supplied proof:
  `requireFlowFinalized` on L2, `_verifyBundle`'s sender check and `_proveInclusion` on L1.
  `execute` consults it only when the bundle is `Unreceived`. The verdict is an input bit of each
  entry-point call, so two calls may get different verdicts, in one transaction or in two.
* **Everything else is the engine's**: `Callee` trees, fuel, `none` for a revert that leaves
  nothing, the committed log as the trace, a bundle as its hash and its number of calls.
* **Reject-only checks are omitted**: the permission gates (`_requireExecutionAllowed`
  `IHB:239-255`, the unbundler gate `IHB:118-132`), the destination context (`IHB:390-410`), the
  versions (`IHB:230`, `:366`), `require(!shadowAccount)` (`IHB:369`), L1's single-call rule
  (`L1:85`) and target pin (`L1:189-192`), the pause gate (`L1:168-170`), and the selector and
  value checks of a call (folded into its target's failure). Omitting a check that can only revert
  only adds runs.
* **The handler's other functions write neither mapping.** `initL2` (`L2:34`) only locks the
  reentrancy guard. On L1, `initialize`, `pause`, `unpause` (`L1:59-72`) and ownership write the
  guard and OpenZeppelin storage only. `updateL2` (`L2:38-43`, `onlyUpgrader`) does
  `sstore(101, 0)` (`interop/InteropConstants.sol:12`). Slot 101 is past the gap and is neither
  mapping's base slot; a mapping entry lives at a keccak image, which this model does not track.
* **Countermodel orders** reuse the engine's `Variant`: `statusWriteAfterCalls` moves
  `_markFullyExecutedAndRun`'s `FullyExecuted` write (`IHB:326`) after `_executeCalls`;
  `callWriteAfterCalls` moves `unbundleBundle`'s `Executed` write (`IHB:155`) after it.
* **Gate predicates.** `PassesGateAtV35 h e` says entry-point call `e` names a bundle with hash `h`
  and carries a passing verdict; `TxAllAtV35 P t` says every entry-point call of transaction `t`,
  at every depth, satisfies `P`. The gate results are stated with them.
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
  (`L2:61-78`), `executeBundle(_bundle, _proof)` on L1 (`L1:81-98`). `ok` is the proof check's
  verdict, consulted only when the bundle is `Unreceived` (`L2:73-75`; `L1:92-95`). -/
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
  | calls (e : EntryAtV35 ℓ) (inner : List (CalleeAtV35 ℓ)) (caught : Bool)
      (next : CalleeAtV35 ℓ)

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

/-- **The v35 semantics.** `execAtV35 ℓ v n f s` runs frame `f` of a layer-`ℓ` handler from
state `s` with budget `n`, in write order `v`: the state and committed log it leaves, or `none` if
it reverts. -/
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
def submitAllAtV35 (ℓ : LayerAtV35) (v : Variant) :
    State → List (TxAtV35 ℓ) → State × List Effect
  | s, [] => (s, [])
  | s, t :: ts =>
      ((submitAllAtV35 ℓ v (submitAtV35 ℓ v s t).1 ts).1,
        (submitAtV35 ℓ v s t).2 ++ (submitAllAtV35 ℓ v (submitAtV35 ℓ v s t).1 ts).2)

/-- **A TARGET THAT REVERTS FROM EVERY STATE.** Run as the target of a delivered call, `c` reverts
in the order `v` whatever the state and the budget (the v35 form of the pin's
`ReentrancyStrong.AlwaysReverts`). -/
def AlwaysRevertsAtV35 (ℓ : LayerAtV35) (v : Variant) (c : CalleeAtV35 ℓ) : Prop :=
  ∀ (m : ℕ) (t : State), execAtV35 ℓ v m (.target c) t = none

/-! ## The translation into the engine

A v35 entry is sent to the engine entry point with the same guard: `execute` to the pin's
`executeBundle` (not `executeAtomicBundle`, whose guard admits `Unreceived` only), `verify` to
`verifyBundle`, `unbundleBundle` to itself. -/

/-- The engine entry point with the same guard. -/
def EntryAtV35.toPin {ℓ : LayerAtV35} : EntryAtV35 ℓ → Contracts.InteropHandler.Entry
  | .execute b ok => .executeBundle b ok
  | .verify b ok => .verifyBundle b ok
  | .unbundleBundle b req => .unbundleBundle b req

mutual
/-- A v35 target, as an engine target. -/
def CalleeAtV35.toPin {ℓ : LayerAtV35} : CalleeAtV35 ℓ → Contracts.InteropHandler.Callee
  | .returns => .returns
  | .reverts => .reverts
  | .calls e inner caught next =>
      .calls e.toPin (CalleeAtV35.listToPin inner) caught (CalleeAtV35.toPin next)

/-- A list of v35 targets, as engine targets. -/
def CalleeAtV35.listToPin {ℓ : LayerAtV35} :
    List (CalleeAtV35 ℓ) → List Contracts.InteropHandler.Callee
  | [] => []
  | c :: cs => CalleeAtV35.toPin c :: CalleeAtV35.listToPin cs
end

/-- A v35 frame, as an engine frame. -/
def FrameAtV35.toPin {ℓ : LayerAtV35} : FrameAtV35 ℓ → Contracts.InteropHandler.Frame
  | .entry e cs => .entry e.toPin (CalleeAtV35.listToPin cs)
  | .calls h is cs => .calls h is (CalleeAtV35.listToPin cs)
  | .target c => .target c.toPin

/-- A v35 transaction, as an engine transaction. -/
def TxAtV35.toPin {ℓ : LayerAtV35} (t : TxAtV35 ℓ) : Contracts.InteropHandler.Tx :=
  ⟨t.fuel, t.entry.toPin, CalleeAtV35.listToPin t.callees⟩

/-! ## Gate predicates -/

/-- Entry-point call `e` names a bundle with hash `h` and carries a passing proof-check verdict:
`execute` or `verify` with `ok = true`. On L2 that is `requireFlowFinalized` accepting the
supplied `_finality` (`L2:74`, `:89`); on L1, `_verifyBundle` accepting `_proof` (`L1:213-221`).
`unbundleBundle` consults no proof. -/
def PassesGateAtV35 {ℓ : LayerAtV35} (h : BundleHash) : EntryAtV35 ℓ → Prop
  | .execute b ok => b.hash = h ∧ ok = true
  | .verify b ok => b.hash = h ∧ ok = true
  | .unbundleBundle _ _ => False

/-- Every entry-point call a target makes, at every depth, satisfies `P`. -/
inductive CalleeAllAtV35 {ℓ : LayerAtV35} (P : EntryAtV35 ℓ → Prop) : CalleeAtV35 ℓ → Prop
  | returns : CalleeAllAtV35 P .returns
  | reverts : CalleeAllAtV35 P .reverts
  | calls {e : EntryAtV35 ℓ} {inner : List (CalleeAtV35 ℓ)} {caught : Bool}
      {next : CalleeAtV35 ℓ} :
      P e → (∀ c ∈ inner, CalleeAllAtV35 P c) → CalleeAllAtV35 P next →
        CalleeAllAtV35 P (.calls e inner caught next)

/-- Every entry-point call of transaction `t` satisfies `P`: its own entry, and every one its
targets make, at every depth. -/
def TxAllAtV35 {ℓ : LayerAtV35} (P : EntryAtV35 ℓ → Prop) (t : TxAtV35 ℓ) : Prop :=
  P t.entry ∧ ∀ c ∈ t.callees, CalleeAllAtV35 P c

/-! ## The v35 receive filter, as the gate's mutable input

`requireFlowFinalized` reverts unless every leg's source is this chain or an allowed peer
(`_checkLegSourceAllowed`, `AtomicFlowManager.sol:338-344`, called at `:201`). `isPeerAllowed` is
`L2Bridgehub` storage (`core/bridgehub/L2Bridgehub.sol:43`), set by `allowInteropPeer` (`:95-99`)
and deleted by `deregisterChainForInterop` (`:102-105`). This section models only what the
handler sees: a verdict that depends on `isPeerAllowed` at the moment the gate runs. Upstream
documents the consequence (`protocol-docs/interop-gating.md:195-197`): the filter is read when the
bundle is verified, or executed if it was not verified first; a bundle from a removed peer stays
unreceived until the peer is allowed again, and one verified before the removal still executes.
The flow manager's own side (`authorizeRefund`'s filter, `:231`) is not modelled here. Not at main
(see the header). -/

/-- `_checkLegSourceAllowed(src)` passes (`AtomicFlowManager.sol:338-344`). -/
def legSourceAllowedAtV35 (self : ℕ) (isPeerAllowed : ℕ → Bool) (src : ℕ) : Bool :=
  src == self || isPeerAllowed src

/-- `requireFlowFinalized`'s verdict as a function of the receive filter: `proofsOk` stands for
every other check of `AtomicFlowManager.sol:180-212` (flow id, settlement layer, proof count,
per-leg source chain and inclusion, executing bundle is a leg), and the filter runs on every
leg's source. -/
def gateVerdictAtV35 (self : ℕ) (isPeerAllowed : ℕ → Bool) (legSources : List ℕ)
    (proofsOk : Bool) : Bool :=
  proofsOk && legSources.all (legSourceAllowedAtV35 self isPeerAllowed)

/-- `deregisterChainForInterop(c)`: `delete isPeerAllowed[c]` (`L2Bridgehub.sol:102-105`). -/
def deregisterAtV35 (isPeerAllowed : ℕ → Bool) (c : ℕ) : ℕ → Bool :=
  fun c' => if c' = c then false else isPeerAllowed c'

/-- `allowInteropPeer(c, _)`: `isPeerAllowed[c] = true` (`L2Bridgehub.sol:95-99`). -/
def allowAtV35 (isPeerAllowed : ℕ → Bool) (c : ℕ) : ℕ → Bool :=
  fun c' => if c' = c then true else isPeerAllowed c'

/-! ## Witness data

The engine's bundles: `wA` (hash 1, two calls), `wB` (hash 2, one call), `wC` (hash 3, one
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

/-- A target that executes `wB` re-entrantly (committing it in its own frame) and then reverts.
It is not the leaf `CalleeAtV35.reverts`. -/
def wRevertsAfterWorkAtV35 : CalleeAtV35 .l2 :=
  .calls (executeAtomicBundleAtV35 wB true) [] false .reverts

/-- A failing attempt at `wA`: call 0's target is `wRevertsAfterWorkAtV35`; call 1's target
returns. -/
def wAttemptAfterWorkAtV35 : TxAtV35 .l2 :=
  ⟨8, executeAtomicBundleAtV35 wA true, [wRevertsAfterWorkAtV35, .returns]⟩

/-- A failing attempt at `wA`: call 0's target executes `wB` re-entrantly and returns; call 1's
target calls `executeAtomicBundle(wA)` and does not catch the failure. It reverts inside `wA`'s
execution only because `wA` is `FullyExecuted` there. -/
def wLateReentryAtV35 : TxAtV35 .l2 :=
  ⟨8, executeAtomicBundleAtV35 wA true,
    [.calls (executeAtomicBundleAtV35 wB true) [] false .returns,
      reenterAtV35 (executeAtomicBundleAtV35 wA true) false]⟩

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
  ⟨6, executeAtomicBundleAtV35 wC true,
    [reenterAtV35 (executeAtomicBundleAtV35 wC gate') caught]⟩

/-- `verifyAtomicBundle` of `wC` with a passing gate. -/
def wVerifyCAtV35 : TxAtV35 .l2 := ⟨1, verifyAtomicBundleAtV35 wC true, []⟩

/-- Atomic execution of a verified `wC` with no passing gate, whose call's target does the same
again, not catching a failure. -/
def wReenterVerifiedAtV35 : TxAtV35 .l2 :=
  ⟨6, executeAtomicBundleAtV35 wC false,
    [reenterAtV35 (executeAtomicBundleAtV35 wC false) false]⟩

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

/-- `unbundleBundle` of `wA` executing call 0 and cancelling call 1; the target of call 0
returns. -/
def wUnbundleExecCancelAtV35 : TxAtV35 .l2 :=
  ⟨4, .unbundleBundle wA [.Executed, .Cancelled], []⟩

/-- `executeAtomicBundle` of `wA` with no passing gate; both targets return. -/
def wExecANoGateAtV35 : TxAtV35 .l2 := ⟨4, executeAtomicBundleAtV35 wA false, []⟩

/-- `executeAtomicBundle` of `b` with gate verdict `gate`, every target returning. -/
def runAtomicAtV35 (b : Bundle) (gate : Bool) : TxAtV35 .l2 :=
  ⟨b.calls + 2, executeAtomicBundleAtV35 b gate, List.replicate b.calls .returns⟩

/-- `verifyAtomicBundle` of `b` with gate verdict `gate`. -/
def verifyAtomicTxAtV35 (b : Bundle) (gate : Bool) : TxAtV35 .l2 :=
  ⟨1, verifyAtomicBundleAtV35 b gate, []⟩

/-- The receive-filter witness: chain `10` receiving a flow with legs from itself and from peer
`20`, which it allows. -/
def wFilterSelfAtV35 : ℕ := 10

/-- Legs from chain `10` (this chain) and chain `20`. -/
def wFilterLegsAtV35 : List ℕ := [10, 20]

/-- The whitelist before the removal: only chain `20` is an allowed peer. -/
def wFilterPeersAtV35 : ℕ → Bool := fun c => c == 20

end Contracts.InteropHandlerAtV35
