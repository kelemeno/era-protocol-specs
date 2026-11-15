import EraSpec.Contracts.InteropHandlerBase.Specs.Reentrancy
import EraSpec.Contracts.InteropCenter.Specs.Dispatch
import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashPinned

/-!
# Model additions: the bundle status machine, read off the handler model

Source: era-contracts at the pin `c67894b9`, as in `Specs/Reentrancy.lean` and
`../../InteropCenter/Specs/Dispatch.lean`. Paths are relative to
`l1-contracts/contracts/interop/interop-handler/` unless they name another file.

**This file is definitions only.** The results are in
`EraSpec.Contracts.InteropHandlerBase.Properties.BundleStatusMachineStrong` and are proved in
`EraSpec.Contracts.InteropHandlerBase.Proofs.BundleStatusMachineStrong`.

## Why this file exists

Three statements of topic `BundleStatusMachine` are facts about the abstract relations alone:

* `wholeBundle_route_does_not_check_callStatus` is `CallReach .Unprocessed .Executed ∧
  ¬ CallStep .Executed .Executed`: the per-call graph, with no mention of the whole-bundle write
  (`:129-132`, `L2InteropHandler.sol:87-90`) it is named after.
* `verified_blocks_atomic_execution` is the one edge `¬ Step .Verified .Unreceived`.
* `atomic_reach_two_states`, `atomic_never_unbundled` and `atomic_delivery_terminal` hold because
  `AtomicStep` is DEFINED with the single edge `Unreceived → FullyExecuted`. The fact that carries
  the weight — `verifyBundle` cannot succeed on an atomic bundle, because atomic bundles are never
  published to L1 — is assumed in that definition.

The handler model of topic `Reentrancy` (`exec`, `submitAll`) transcribes the four guards and the
writes, re-entrancy included. This file adds what is needed to state the three facts over it:

* **Which entry-point calls a run makes.** `Callee.Mentions` / `Frame.Mentions` / `Tx.Mentions`:
  every entry-point call in a transaction's tree of targets, at any depth.
* **Which inclusion-proof verdicts it presents.** In the model, `_proveInclusion`'s verdict is
  the boolean an `executeBundle` or `verifyBundle` call carries (`Specs/Reentrancy.lean`,
  "Oracles are inputs"). `Entry.NoProofFor h` says a call presents no valid proof for bundle
  hash `h`; `Entry.ProofSound published` says a valid proof is presented only for a hash in
  `published`.
* **Where valid proofs come from.** `_verifyBundle` (`:296-316`) accepts a proof only for the
  message `BUNDLE_IDENTIFIER ++ _bundle` sent by `L2_INTEROP_CENTER_ADDR`, and
  `_validateBundleDestinationContext` (`:428-437`) requires the proof's chain to be the bundle's
  `sourceChainId`, which is also the chain id `encodeInteropBundleHash` hashes (`:249`). So a
  hash with a valid proof is `keccak(abi.encode(c, x))` for a bundle message `(c, x)` that chain
  `c`'s center published to L1 (`PublishedHash`). On the source chain, the center publishes
  bundle bytes only in `_sendBundleToL1`, on the non-atomic branch of `_dispatchBundle`
  (`InteropCenter.sol:645-658`) — the premise `PublishesOnlyPublicDispatches`, a whole-program
  fact of the same kind as `append`'s single call site.
-/

namespace Contracts.InteropHandler

open AttackVectors.BundleStatusMachine (Status CallStatus)

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
`verifyBundle` take a proof (`:86`, `:150`); their verdict is the carried boolean. -/
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

/-- **A HASH THE DESTINATION CAN BE SHOWN A VALID PROOF FOR.** `pubs` lists the bundle messages
published to L1, each as (source chain id, bundle bytes); the destination keys a bundle by
`encodeInteropBundleHash(sourceChainId, _bundle) = keccak(abi.encode(sourceChainId, _bundle))`
(`:249`, `InteropDataEncoding.sol:11-13`). -/
def PublishedHash (keccak : List UInt8 → UInt256) (pubs : List (UInt256 × List UInt8))
    (h : BundleHash) : Prop :=
  ∃ p ∈ pubs, h = keccak (AttackVectors.BundleHashEncoding.abiEncode p.1.val p.2)

/-- **CHAIN `P` PUBLISHES ONLY THE BYTES OF ITS PUBLIC DISPATCHES.** Every bundle message of
`pubs` from chain `P.chainId` is `abi.encode(bundle)` of a non-atomic dispatch in chain `P`'s
center log: `_sendBundleToL1` (`InteropCenter.sol:657`) is reached only on the non-atomic branch
of `_dispatchBundle`, and it is the center's only bundle publication. -/
def PublishesOnlyPublicDispatches (P : Contracts.InteropCenter.Params)
    (log : List Contracts.InteropCenter.Dispatch) (pubs : List (UInt256 × List UInt8)) : Prop :=
  ∀ p ∈ pubs, p.1 = P.chainId → ∃ d' ∈ log, d'.isAtomic = false ∧ p.2 = P.enc d'.bundle

/-! ## Witness data -/

/-- `unbundleBundle` of `wC` requesting its one call, whose target returns. -/
def wUnbundleC : Tx := ⟨3, .unbundleBundle wC [.Executed], []⟩

/-- Atomic execution of `wC`, whose target returns. -/
def wRunC : Tx := ⟨3, .executeAtomicBundle wC true, []⟩

/-- A destination run on the honest InteropCenter witness chain: verify, with a valid proof, the
public bundle whose hash is `2` (`wD2`'s), then atomically execute the bundle whose hash is `1`
(`wD1`'s atomic leg). -/
def wDestRun : List Tx :=
  [⟨1, .verifyBundle ⟨2, 1⟩ true, []⟩, ⟨3, .executeAtomicBundle ⟨1, 1⟩ true, []⟩]

/-- A state the deployed guards never reach (`CallsClosed` fails): bundle `3` is `Verified`, yet
its call 0 is already recorded `Executed`. -/
def wStaleCalls : State := (init.setBundle 3 .Verified).setCall 3 0 .Executed

/-- `executeBundle` of `wC` with no valid proof, whose target returns. -/
def wExecuteC : Tx := ⟨3, .executeBundle wC false, [.returns]⟩

end Contracts.InteropHandler
