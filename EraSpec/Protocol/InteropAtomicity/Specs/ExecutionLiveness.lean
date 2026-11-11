import EraSpec.Contracts.InteropHandlerBase.Specs.Reentrancy
import EraSpec.Contracts.InteropCenter.Specs.Dispatch
import EraSpec.Protocol.InteropAtomicity.Specs.Refund

/-!
# Model: what can still happen to a dispatched leg on its destination (execution liveness)

Source: era-contracts at the pin `c67894b9`. Paths are relative to `l1-contracts/contracts/`.
`UPG` is the upgrade-simplification tree `e561b9cc2`, cited only for the comparison at the end.

**This file is definitions only.** Statements are in
`EraSpec.Protocol.InteropAtomicity.Properties.ExecutionLiveness`, proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.ExecutionLiveness`.

The destination model is `Contracts.InteropHandler` (`Contracts/InteropHandlerBase/Specs/Reentrancy.lean`,
topic `Reentrancy`): the handler's `bundleStatus` and `callStatus`, its four entry points, every
re-entrant behaviour of every target as a finite `Callee` tree, `Option` rollback. This file adds
predicates on those trees, the publication side of the source chain, and the execution-permission
check that model omits.

## The two routes, and which bundles have which

    executeBundle (interop-handler/InteropHandlerBase.sol:86-147)
      require(status == Unreceived || status == Verified)                       // :117-120
      if (status != Verified) _verifyBundle(...)                                // :123
    verifyBundle (:150-161)            require(status == Unreceived); _verifyBundle(...)   // :157-160
    unbundleBundle (:164-231)          require(status == Verified || status == Unbundled)  // :195
    _verifyBundle (:296-316)
      require(_proof.message.sender == L2_INTEROP_CENTER_ADDR, ..);             // :302-305
      _proof.message.data = bytes.concat(BUNDLE_IDENTIFIER, _bundle);           // :308
      require(_proveInclusion(_proof), MessageNotIncluded());                   // :310
      bundleStatus[_bundleHash] = BundleStatus.Verified;                        // :312
    executeAtomicBundle (interop-handler/L2InteropHandler.sol:49-100)
      require(status == BundleStatus.Unreceived, BundleAlreadyProcessed(bundleHash));      // :79
      IAtomicFlowManager(L2_ATOMIC_FLOW_MANAGER_ADDR).requireFlowFinalized(bundleHash, _finality); // :83

`Verified`, and with it the per-call route `unbundleBundle`, is reachable only through an
inclusion proof of the L2→L1 message `BUNDLE_IDENTIFIER ++ bytes` sent by `L2_INTEROP_CENTER_ADDR`
on the chain `_proof.chainId`, which `_validateBundleDestinationContext` (:428-437) forces to be the
decoded bundle's `sourceChainId`; and the status key is
`encodeInteropBundleHash(sourceChainId, bytes)` (:249). On the source, the center's only
`sendToL1` (`interop/InteropCenter.sol:626`, inside `_sendBundleToL1`) is reached only from the
public branch of `_dispatchBundle` (:657), with the bytes `abi.encode(bundle)` (:643). An atomic
bundle is appended to the flow manager instead (:646-655) and never published.

So an atomic leg has exactly one route: `executeAtomicBundle`, which needs `Unreceived`, runs every
call in one frame and reverts if any call reverts. It has no per-call route that could skip a bad
call. The `L2InteropHandler.sol:39-42` NatSpec says so: "Atomic bundles are never published to L1,
so this is their only execution entry point; there is no atomic verify path."

## Modelling choices

* **Proof verdicts are backed by publication.** `Contracts.InteropHandler` takes the inclusion
  proof's verdict `proofOk` as an input bit. `ProofBacked Pub` says a verdict is `true` only for a
  bundle whose hash is in `Pub`, the hashes of what was published; a run is backed when every
  entry of every transaction, at every depth, is (`TxEvery`). This is message-verification
  soundness (`proveL2MessageInclusionShared` accepts only messages that were sent, `PROTO-EVIDENCE`)
  together with the destination's own recomputation of the hash from the presented bytes. It is a
  premise, stated per run.
* **What was published.** `Published` is a source chain and the bytes it published.
  `PublishedOnlyPublicDispatches P S pub` is the local-honesty premise for chain `P.chainId`: every
  item that chain published is `abi.encode` of a public dispatch of its center run `S`. It is the
  enumeration above (one `sendToL1` site, reached only from the public branch; the messenger records
  `msg.sender`, so no other contract can publish as `L2_INTEROP_CENTER_ADDR`), stated rather than
  derived, like `AttackVectors.LocalHonesty.Guards`. Other chains' publications are arbitrary.
* **A permanently reverting call.** `AtomicAttemptReverts h` says every `executeAtomicBundle` of a
  bundle with hash `h`, at top level or nested, meets a target that reverts outright among the
  bundle's calls: for instance a call to an address with no code (the `receiveMessage` selector
  check at `InteropHandlerBase.sol:287` fails) or to a destination contract that always reverts.
  All attempts present the same bytes, so the same targets, unless the destination's keccak
  collides on two bundle encodings, which this file does not model. The quantification is over
  every transaction, so it is a property of the target code, not of one attempt.
* **Permissions.** `Contracts.InteropHandler` omits the execution permission as a reject-only check.
  The liveness statements need it, so `ExecutionPermitted` models it on its own, for the two ways an
  execute entry point is reached: a direct call, or the handler's `receiveMessage` (:334-362), which
  dispatches on `executeBundle`, `verifyBundle` and `unbundleBundle` only (:351-359).
* **Gate verdict.** `requireFlowFinalized` is a static call (`atomic-interop/IAtomicFlowManager.sol:53`),
  so its verdict is the input bit `gateOk`; `true` is "the flow is finalized and the executor
  presents the proofs" (`Contracts.Atomicity.FlowFinalizedBy`). Data availability is what makes such
  proofs presentable (`Contracts.Atomicity.DataAvailable`).

## At `UPG`

`UPG/interop/interop-handler/L2InteropHandler.sol` adds `verifyAtomicBundle` (:83), which runs the
flow gate and marks the bundle `Verified`, so an atomic leg gains the verify→unbundle route; and its
`receiveMessage` dispatches the execute selector to `executeAtomicBundle` (:99-100, :109-131), so a
foreign-chain executor gains a rescue route. Both statements below that turn on the missing routes
(`FinalizedLegStrandedByRevertingCall`, `ForeignExecutorStrandsAtomicLeg`) are pin-only.
-/

namespace Contracts.ExecutionLiveness

open Contracts.InteropHandler (Entry Callee Frame Tx BundleHash)
open AttackVectors.BundleStatusMachine (Status CallStatus)
open AttackVectors.BundleHashEncoding (abiEncode)

/-! ## Predicates on every entry-point call of a run -/

/-- **EVERY ENTRY-POINT CALL OF A TARGET'S BEHAVIOUR SATISFIES `Q`**, at every depth: each
`Callee.calls e inner _ next` node has `Q e inner`, and so do the targets `inner` of the calls that
frame delivers, and the rest `next` of the behaviour. -/
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

/-- **THE INCLUSION-PROOF VERDICT IS BACKED BY `Pub`.** `executeBundle` and `verifyBundle` are told
`proofOk = true` only for a bundle whose hash is in `Pub` (`_verifyBundle`, `:302-312`). The other
two entry points take no inclusion proof. -/
def ProofBacked (Pub : BundleHash → Prop) : Entry → List Callee → Prop
  | .executeBundle b ok, _ => ok = true → Pub b.hash
  | .verifyBundle b ok, _ => ok = true → Pub b.hash
  | _, _ => True

/-- **EVERY ATOMIC ATTEMPT ON `h` MEETS A REVERTING TARGET.** An `executeAtomicBundle` of a bundle
with hash `h` has a target that reverts outright among the targets of its calls. -/
def AtomicAttemptReverts (h : BundleHash) : Entry → List Callee → Prop
  | .executeAtomicBundle b _, cs => b.hash = h → Callee.reverts ∈ cs.take b.calls
  | _, _ => True

/-! ## The source chain's publications -/

/-- An item published to L1: the chain that sent `BUNDLE_IDENTIFIER ++ bytes` from
`L2_INTEROP_CENTER_ADDR` (`InteropCenter.sol:626`), and the bytes. -/
abbrev Published := Contracts.InteropCenter.Word × List UInt8

/-- The bundle hash a destination computes for a published item:
`encodeInteropBundleHash(sourceChainId, bytes)` (`InteropHandlerBase.sol:249`, with `sourceChainId`
the proof's chain by `:434-437`). -/
def publishedHash (keccak : List UInt8 → Contracts.InteropCenter.Word) (p : Published) :
    BundleHash :=
  keccak (abiEncode p.1.val p.2)

/-- The hashes for which an inclusion proof exists: those of published items. -/
def PubHashes (keccak : List UInt8 → Contracts.InteropCenter.Word) (pub : List Published) :
    BundleHash → Prop :=
  fun h => ∃ p ∈ pub, publishedHash keccak p = h

/-- **LOCAL HONESTY OF PUBLICATION, FOR CHAIN `P.chainId`.** Every item chain `P.chainId` published
is `abi.encode` of the bundle of a public dispatch of its center run `S`. -/
def PublishedOnlyPublicDispatches (P : Contracts.InteropCenter.Params)
    (S : Contracts.InteropCenter.State) (pub : List Published) : Prop :=
  ∀ x, (P.chainId, x) ∈ pub → ∃ d ∈ S.log, d.isAtomic = false ∧ x = P.enc d.bundle

/-! ## The unbundled route, as a function of the request -/

/-- What `unbundleBundle`'s first loop (`InteropHandlerBase.sol:200-219`) records for one call, from
its recorded status and the requested one: a requested execution is recorded `Executed`, a requested
cancellation `Cancelled`, anything else leaves the call as it was. -/
def requestedStatus : CallStatus → Option CallStatus →
    CallStatus
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

/-! ## Who may execute -/

/-- `executionAddress` (`common/Messaging.sol:241-246`, parsed by `InteroperableAddress.parseEvmV1`):
absent, so execution is permissionless (`InteropHandlerBase.sol:94`), or an EVM address
`(chainId, address)`. -/
abbrev ExecAttr := Option (ℕ × ℕ)

/-- How an execute entry point is reached. -/
inductive Route
  /-- A call from `caller`, an account or contract on this chain other than the handler. -/
  | direct (caller : ℕ)
  /-- The handler's own `receiveMessage` (`:334-362`), while executing a delivered interop call
  whose sender is `senderAddr` on `senderChain`; it calls the entry point on itself (`:391`), so
  `msg.sender == address(this)`. -/
  | rescue (senderChain senderAddr : ℕ)

/-- The two execute entry points. -/
inductive ExecEntry
  | executeBundle
  | executeAtomicBundle
deriving DecidableEq

/-- **THE EXECUTION PERMISSION, BY ROUTE.**

* Direct, both entry points (`InteropHandlerBase.sol:95-112`, `L2InteropHandler.sol:62-75`): no
  `executionAddress`, or `(executionChainId == block.chainid || executionChainId == 0) &&
  executionAddress == msg.sender`.
* `receiveMessage` into `executeBundle` (`:351-352`, `:364-392`): the same test against the wrapped
  message's sender chain and address (`:385-388`); the self-call then passes the entry point's own
  test through `msg.sender == address(this)`.
* `receiveMessage` into `executeAtomicBundle`: there is no such branch (`:351-359` dispatch on
  `executeBundle`, `verifyBundle` and `unbundleBundle` only), and no other code of the handler calls
  it, so the `msg.sender == address(this)` disjunct at `L2InteropHandler.sol:67` is dead
  (`AttackVectors.SelfCallAuthority`). -/
def ExecutionPermitted (thisChain : ℕ) (attr : ExecAttr) : ExecEntry → Route → Prop
  | _, .direct caller =>
      attr = none ∨ ∃ ch a, attr = some (ch, a) ∧ (ch = thisChain ∨ ch = 0) ∧ a = caller
  | .executeBundle, .rescue senderChain senderAddr =>
      attr = none ∨ ∃ ch a, attr = some (ch, a) ∧ (ch = senderChain ∨ ch = 0) ∧ a = senderAddr
  | .executeAtomicBundle, .rescue _ _ => False

/-! ## Witness data

The source run is `Contracts.InteropCenter.wS3` on the honest chain `wParams` (chain `324`):
sender `1`'s atomic leg `wD1` (bundle hash `1`) and sender `2`'s public bundle `wD2` (bundle hash
`2`). On the destination, a handler bundle is its hash and its number of calls. -/

/-- Chain `324` published exactly `wD2`'s bytes. -/
def wPub : List Published :=
  [(Contracts.InteropCenter.wParams.chainId,
    Contracts.InteropCenter.wParams.enc Contracts.InteropCenter.wD2.bundle)]

/-- `verifyBundle` of the public bundle (hash `2`, one call) with a valid inclusion proof. -/
def wVerifyPublic : Tx := ⟨2, .verifyBundle ⟨2, 1⟩ true, []⟩

/-- `executeAtomicBundle` of the atomic leg (hash `1`, one call) with the gate passing. -/
def wExecAtomic : Tx := ⟨3, .executeAtomicBundle ⟨1, 1⟩ true, []⟩

/-- An attempt at the atomic leg `h` (one call) whose target reverts. -/
def wRevertingAttempt (h : BundleHash) : Tx := ⟨5, .executeAtomicBundle ⟨h, 1⟩ true, [.reverts]⟩

/-- An attempt whose first target executes the public bundle `⟨2, 1⟩` with a valid proof, and
whose second target is the reverting one: the nested execution is undone with the attempt. -/
def wNestedRevertingAttempt (h : BundleHash) : Tx :=
  ⟨8, .executeAtomicBundle ⟨h, 2⟩ true,
    [.calls (.executeBundle ⟨2, 1⟩ true) [] false .returns, .reverts]⟩

/-- `verifyBundle` of a bundle `⟨h, n⟩` with a valid inclusion proof. -/
def wVerify (h : BundleHash) (n : ℕ) : Tx := ⟨1, .verifyBundle ⟨h, n⟩ true, []⟩

end Contracts.ExecutionLiveness
