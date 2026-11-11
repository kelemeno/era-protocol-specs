import EraSpec.Contracts.InteropHandlerBase.Specs.BundleStatusMachineFaithful

/-!
# Model: the base-token ledger, derived from the handler

Source: era-contracts at the pin `c67894b9`, `l1-contracts/contracts/`; a bare `:N` is a line of
`interop/interop-handler/InteropHandlerBase.sol` there.

**This file is definitions only.** The statements are in
`EraSpec.Contracts.InteropHandlerBase.Properties.ValueLedgerFaithful` and are proved in
`EraSpec.Contracts.InteropHandlerBase.Proofs.ValueLedgerFaithful`.

## Why a second model

`BundleStatusMachine`'s "no inflation" results are about an arbitrary `Ledger`, a list of
`(value, status)` pairs that nothing ties to the handler: not that it has one entry per call of the
bundle, nor that an entry's status is the call's final `callStatus`, nor that what the handler
pays out is `releasedSum` of it. So `released_le_collected` is a list identity. This file derives
the ledger from the handler's own state, in the re-entrant model `Contracts.InteropHandler`
(`Reentrancy`), and measures the release where it happens.

## The code

    // _executeCalls (:259-289), for each call i it executes:
    _handleCallValue(interopCall.value, _sourceChainId);                          // :279
    selector = IERC7786Recipient(to).receiveMessage{value: interopCall.value}(...) // :282-286
    require(selector == receiveMessage.selector);                                 // :287
    // L2InteropHandler._handleCallValue (:115-120): if (_value > 0) L2_BASE_TOKEN_HOLDER.give(...)

`_handleCallValue` has one call site (:279), `give` one (`L2InteropHandler.sol:118`), and the loop
has no `try`: a call whose target fails reverts the whole frame, release included. So in a
committed frame, call `i` of the bundle with hash `h` releases `interopCall.value` exactly when
the Reentrancy model logs `Effect.delivered h i`, once per such entry. The source side is
`InteropCenter.sol:541`, `totalBurnedCallsValue += interopCallValue` over every call, and the
value placed in the bundle is that same field (:738, :747).

## Modelling choices

* **Call values are a function** `val : ℕ → ℕ`, call `i`'s `interopCall.value`. The Reentrancy
  model's bundle is its hash and its call count, so `val` is the value vector of the bundle bytes
  the hash names. That two byte strings with one hash and one call count carry different values is
  outside the model; it is the bytes-to-hash binding (`InteropDataEncoding`), already listed as a
  separate obligation in the folder README.
* **The binding premise** (`NamesOnly b`): every entry-point call that names hash `b.hash` names
  the bundle `b`, so all of `b.hash`'s deliveries are of `b`'s calls. It is a premise about the
  run's own inputs, satisfiable (`LedgerWitness`), and load-bearing
  (`SharedHashBreaksTheLedger`).
* **Values are naturals**, where the source sums `uint256` with checked arithmetic; an overflow
  reverts the send, so every collected sum the destination sees is a natural.
* `scripts/check-interop-handler-inventory.sh` checks the two release call sites above against the
  pinned tree.
-/

namespace Contracts.InteropHandler.Faithful

open AttackVectors.BundleStatusMachine (Ledger CallStatus)

/-- The values of a bundle's calls: `interopBundle.calls[i].value` for call `i`. -/
abbrev CallValues := ℕ → ℕ

/-- **What the handler releases** for bundle hash `h`, read off a committed log: the value of call
`i` once per committed delivery of call `i` of `h` (`_handleCallValue`, :279). -/
def releasedFor (val : CallValues) (h : BundleHash) : List Effect → ℕ
  | [] => 0
  | .delivered h' i :: l => (if h' = h then val i else 0) + releasedFor val h l
  | .executed _ :: l => releasedFor val h l

/-- **What the source collected** for bundle `b`: the value of every one of its calls
(`InteropCenter.sol:541`). -/
def collectedFor (val : CallValues) (b : Bundle) : ℕ :=
  ((List.range b.calls).map val).sum

/-- **The handler's ledger** for bundle `b` in state `s`: one entry per call of `b`, in index
order, holding the call's value and its recorded `callStatus[bundleHash][i]` (:57). -/
def handlerLedger (val : CallValues) (b : Bundle) (s : State) : Ledger :=
  (List.range b.calls).map fun i => (val i, s.call b.hash i)

/-- **The binding premise**: an entry-point call that names hash `b.hash` names the bundle `b`. -/
def NamesOnly (b : Bundle) (e : Entry) : Prop :=
  e.bundle.hash = b.hash → e.bundle = b

/-! ## Witness data -/

/-- Bundle `7`, two calls. -/
def wL : Bundle := ⟨7, 2⟩

/-- Its call values: `3` and `5`. -/
def wLVal : CallValues := fun i => if i = 0 then 3 else 5

/-- `verifyBundle(wL)` with an accepted proof. -/
def wLVerify : Tx := ⟨1, .verifyBundle wL true, []⟩

/-- `unbundleBundle(wL)` executing call 0 and cancelling call 1. -/
def wLUnbundle : Tx := ⟨4, .unbundleBundle wL [.Executed, .Cancelled], []⟩

/-- `executeAtomicBundle(wL)` with a passing gate. -/
def wLExecute : Tx := ⟨4, .executeAtomicBundle wL true, []⟩

/-- Bundle `5`, one call. -/
def wShort : Bundle := ⟨5, 1⟩

/-- Another bundle with hash `5`, two calls. -/
def wLong : Bundle := ⟨5, 2⟩

/-- `executeAtomicBundle(wLong)` with a passing gate. -/
def wLongRun : Tx := ⟨4, .executeAtomicBundle wLong true, []⟩

end Contracts.InteropHandler.Faithful
