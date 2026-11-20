import EraSpec.Contracts.InteropHandlerBase.Specs.Reentrancy
import EraSpec.Contracts.InteropCenter.History.Specs.Dispatch
import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashPinned
import EraSpec.Contracts.InteropHandlerBase.History.Specs.BundleStatusMachine

/-! **History: a record of the interop pin `c67894b9`, not a claim about era-contracts `b17415d20`.**
This topic composes the re-entrant engine (topic `Reentrancy`) with the pin's atomic entry point
(`executeAtomicBundle` admitting `Unreceived` only, gate always run), the pin's source-chain
`InteropCenter` model (`Contracts.InteropCenter` `Dispatch`) and the pin's bundle-hash preimage
(`BundleHashPinned`'s History layer). At `b17415d20` `executeAtomicBundle`
(`interop/interop-handler/L2InteropHandler.sol:61-78`) admits a `Verified` bundle and skips
`requireFlowFinalized` for it, the new `verifyAtomicBundle` (`:83-92`) verifies an atomic bundle,
and the bundle hash is `keccak256(_bundle)` (`interop/interop-handler/InteropHandlerBase.sol:231`).
So the atomic sub-machine derived here does not describe `b17415d20`. The engine statements of
section (a) (`WholeBundleWriteIgnoresCallStatus`, `CallStatusDoesNotStopWholeBundleRedelivery`,
`AdmittedBundleHasOnlyUnprocessedCalls`) moved with the topic; the `b17415d20` re-entrancy results
are in topic `Reentrancy`. Namespaces carry a `History` segment. -/

/-!
# Model additions: the bundle status machine, read off the handler model

Source: era-contracts at the pin `c67894b9`, as in `Specs/Reentrancy.lean` and
`../../InteropCenter/History/Specs/Dispatch.lean`. Paths are relative to
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

namespace Contracts.InteropHandler.History

open AttackVectors.BundleStatusMachine (Status CallStatus)

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
def PublishesOnlyPublicDispatches (P : Contracts.InteropCenter.History.Params)
    (log : List Contracts.InteropCenter.History.Dispatch) (pubs : List (UInt256 × List UInt8)) : Prop :=
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

end Contracts.InteropHandler.History
