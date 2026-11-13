import EraSpec.Contracts.InteropHandlerBase.Specs.Reentrancy

/-!
# Model: which check each bundle-status edge consults, and what the never-published premise buys

Source: era-contracts at the pin `c67894b9`,
`l1-contracts/contracts/interop/interop-handler/`; a bare `:N` is a line of
`InteropHandlerBase.sol` there.

**This file is definitions only.** The statements are in
`EraSpec.Contracts.InteropHandlerBase.Properties.BundleStatusMachineFaithful` and are proved in
`EraSpec.Contracts.InteropHandlerBase.Proofs.BundleStatusMachineFaithful`.

## Why a second model

`BundleStatusMachine.Step` does not say which entry point takes an edge, or what it checks:
`executeFresh` and `executeAtomic` are both `Step .Unreceived .FullyExecuted`. So
`verified_blocks_atomic_execution`, `¬ Step .Verified .Unreceived`, cannot say "via the atomic
entry point", and the prose around it draws the wrong conclusion from it: that if atomic bundles
were published to L1, `verifyBundle` would succeed on them and "permanently brick their
execution". In the source it is the other way round.

    executeBundle   require(status == Unreceived || status == Verified)      // :117-120
                    if (status != Verified) _verifyBundle(...)               // :123  (inclusion proof)
                    bundleStatus = FullyExecuted; ...; _executeCalls(...)    // :126-143
    verifyBundle    require(status == Unreceived); _verifyBundle(...)        // :157-160
    _verifyBundle   require(sender == L2_INTEROP_CENTER_ADDR);
                    require(_proveInclusion(_proof)); bundleStatus = Verified // :302-312
    executeAtomicBundle
                    require(status == Unreceived)                            // L2InteropHandler.sol:79
                    requireFlowFinalized(bundleHash, _finality)              // L2InteropHandler.sol:83
                    bundleStatus = FullyExecuted; ...; _executeCalls(...)    // L2InteropHandler.sol:86-97

`requireFlowFinalized`, the atomicity gate, has one call site, in `executeAtomicBundle`. Neither
`executeBundle` nor `verifyBundle` nor `unbundleBundle` consults it, and none of them can tell an
atomic bundle from a public one: the bundle carries no atomic flag (`BundleAttributes`,
`common/Messaging.sol:241-246`; the atomic send metadata travels out of band,
`InteropCenter.sol:569-572`). What keeps an atomic bundle out of `executeBundle` is only that no
inclusion proof for its bytes is accepted. If one were, `executeBundle` would run it with no flow
gate, fresh (`:123` consults the proof) or after `verifyBundle` (`Verified` skips `:123`). That is a
bypass of the atomicity gate, not a liveness loss.

## What is modelled

* **The labelled machine** (`LStep`): `BundleStatusMachine.Step`'s six edges, each labelled with
  its entry point and the authentication it consults: the inclusion proof, the flow gate, or
  neither (`noCheck`). The labels record only these two checks. The reject-only checks the source
  also runs are left out, as in `MODEL-HANDLER-REENTRY`: `_ensureNotPaused`, the caller-permission
  gate (`executeBundle`'s execution-address check :94-112, `unbundleBundle`'s unbundler check
  :170-184) and `executeBundle`'s `_validateBundleDestinationContext` (:92). `executeAtomicBundle`
  runs the same pause, destination-context and execution-address checks
  (`L2InteropHandler.sol:50-75`), so they do not separate the atomic route from the others; only
  the inclusion proof and the flow gate do.
* **The operational premises**, over `Contracts.InteropHandler.exec` (re-entrant, every target
  behaviour, every depth): `ProvesInclusion h e` (an entry-point call presenting an inclusion proof
  `_proveInclusion` accepts for a bundle with hash `h`) and `PassesFlowGate h e` (an
  `executeAtomicBundle` call for hash `h` whose `requireFlowFinalized` verdict is `true`).
  `TxAll P t` says every entry-point call of transaction `t`, its own and every one its targets make
  at any depth, satisfies `P`. The never-published premise for `h` is
  `∀ t ∈ txs, TxAll (fun e => ¬ ProvesInclusion h e) t`.

The verdicts are the Reentrancy model's input bits, so these premises are statements about the
inputs a run is given, not about the encoding. `InteropCenter`'s `AtomicBytesNeverPublished` is
this chain's half of why the never-published premise holds for an atomic bundle (under its
encoder premise, except a pinned cross-sender salt clash); bundles published by other chains are
outside both models. `scripts/check-interop-handler-inventory.sh` checks the call sites above
(`requireFlowFinalized`, `_verifyBundle`, `_proveInclusion`) against the pinned tree.
-/

namespace AttackVectors.BundleStatusMachine.Faithful

/-- The four entry points, as edge labels. -/
inductive EntryPoint
  | verifyBundle
  | executeBundle
  | unbundleBundle
  | executeAtomicBundle
  deriving DecidableEq, Repr

/-- The authentication an edge consults before it is taken. -/
inductive Check
  /-- `_verifyBundle`'s L1 message-inclusion proof for the bundle's bytes (:296-316). -/
  | inclusionProof
  /-- `requireFlowFinalized`, the atomicity gate (`L2InteropHandler.sol:83`). -/
  | flowGate
  /-- Neither the inclusion proof nor the flow gate: the edge is admitted on the bundle's status and
  the reject-only checks (pause, caller permission, destination context) that the model omits. -/
  | noCheck
  deriving DecidableEq, Repr

/-- **The deployed edges**, each labelled by the entry point that takes it and the check it
consults. -/
inductive LStep : Status → EntryPoint → Check → Status → Prop
  /-- `verifyBundle` (:157-160). -/
  | verify : LStep .Unreceived .verifyBundle .inclusionProof .Verified
  /-- `executeBundle` of an `Unreceived` bundle: `_verifyBundle` first (:123). -/
  | executeFresh : LStep .Unreceived .executeBundle .inclusionProof .FullyExecuted
  /-- `executeBundle` of a `Verified` bundle: `:123` is skipped, so no inclusion proof and no flow
  gate is consulted (only the pause, destination-context and execution-address checks of :87-112,
  which `executeAtomicBundle` shares). -/
  | executeVerified : LStep .Verified .executeBundle .noCheck .FullyExecuted
  /-- `unbundleBundle` of a `Verified` bundle (:195-198). -/
  | unbundleFirst : LStep .Verified .unbundleBundle .noCheck .Unbundled
  /-- `unbundleBundle` of an `Unbundled` bundle. -/
  | unbundleAgain : LStep .Unbundled .unbundleBundle .noCheck .Unbundled
  /-- `executeAtomicBundle` (`L2InteropHandler.sol:79-86`). -/
  | executeAtomic : LStep .Unreceived .executeAtomicBundle .flowGate .FullyExecuted

/-- Labelled paths, recording the checks consulted along the way in order. -/
inductive LReach : Status → List Check → Status → Prop
  | refl (s : Status) : LReach s [] s
  | tail {a b d : Status} {cs : List Check} {e : EntryPoint} {c : Check} :
      LReach a cs b → LStep b e c d → LReach a (cs ++ [c]) d

end AttackVectors.BundleStatusMachine.Faithful

namespace Contracts.InteropHandler.Faithful

open AttackVectors.BundleStatusMachine (Status)

/-- Every entry-point call a target makes, at every depth, satisfies `P`. -/
inductive CalleeAll (P : Entry → Prop) : Callee → Prop
  | returns : CalleeAll P .returns
  | reverts : CalleeAll P .reverts
  | calls {e : Entry} {inner : List Callee} {caught : Bool} {next : Callee} :
      P e → (∀ c ∈ inner, CalleeAll P c) → CalleeAll P next →
        CalleeAll P (.calls e inner caught next)

/-- Every entry-point call of transaction `t` satisfies `P`: its own entry, and every one its
targets make, at every depth. -/
def TxAll (P : Entry → Prop) (t : Tx) : Prop :=
  P t.entry ∧ ∀ c ∈ t.callees, CalleeAll P c

/-- Entry-point call `e` presents an inclusion proof `_proveInclusion` accepts for a bundle with hash
`h`: `executeBundle` or `verifyBundle` of such a bundle with proof verdict `true` (:123, :160 →
:310). -/
def ProvesInclusion (h : BundleHash) : Entry → Prop
  | .executeBundle b ok => b.hash = h ∧ ok = true
  | .verifyBundle b ok => b.hash = h ∧ ok = true
  | .unbundleBundle _ _ => False
  | .executeAtomicBundle _ _ => False

/-- Entry-point call `e` passes the atomicity gate for hash `h`: `executeAtomicBundle` of a bundle
with that hash whose `requireFlowFinalized` verdict is `true` (`L2InteropHandler.sol:83`). -/
def PassesFlowGate (h : BundleHash) : Entry → Prop
  | .executeAtomicBundle b ok => b.hash = h ∧ ok = true
  | .executeBundle _ _ => False
  | .verifyBundle _ _ => False
  | .unbundleBundle _ _ => False

/-- `executeBundle(b)` with an accepted inclusion proof, every target returning. -/
def freshPublicRun (b : Bundle) : Tx :=
  ⟨b.calls + 2, .executeBundle b true, List.replicate b.calls .returns⟩

/-- `executeBundle(b)` with no accepted proof, every target returning. -/
def provelessPublicRun (b : Bundle) : Tx :=
  ⟨b.calls + 2, .executeBundle b false, List.replicate b.calls .returns⟩

/-! ## Witness data -/

/-- `unbundleBundle` of `wC` (bundle `3`, one call) executing its call, the target returning. -/
def wUnbundleC : Tx := ⟨4, .unbundleBundle wC [.Executed], []⟩

/-- `executeBundle` of `wC` with no accepted proof. -/
def wProvelessC : Tx := ⟨4, .executeBundle wC false, []⟩

/-- `executeBundle` of `wC` with an accepted proof. -/
def wFreshC : Tx := ⟨4, .executeBundle wC true, []⟩

/-- `executeAtomicBundle` of `wC` with a passing flow gate. -/
def wAtomicC : Tx := ⟨4, .executeAtomicBundle wC true, []⟩

end Contracts.InteropHandler.Faithful
