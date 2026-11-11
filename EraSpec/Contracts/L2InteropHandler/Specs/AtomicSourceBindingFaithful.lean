import EraSpec.Contracts.InteropCenter.Specs.Dispatch
import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashPinned

/-!
# Model: where the atomic path's source chain comes from, over `executeAtomicBundle` itself

Source: the pinned era-contracts tree (`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`), under
`l1-contracts/contracts/`. File names below are relative to that directory.

**This file is definitions only.** The results are stated in
`EraSpec.Contracts.L2InteropHandler.Properties.AtomicSourceBindingFaithful` and proved in
`EraSpec.Contracts.L2InteropHandler.Proofs.AtomicSourceBindingFaithful`.

## Why this topic exists

Topic `AtomicSourceBinding` (same folder) states the atomic path's source binding over three free
symbols, `declared : Hash → Chain`, `commit : Hash → Value` and `tree : Chain → Set Value`. Its
headline `atomic_source_bound` concludes `declared h = c` from `HonestCommits` and
`commit h ∈ tree c`, and `HonestCommits` is that implication for all `c` and `h`, so the headline
restates its premise. Three links to the contract are assumed there and not modelled:

* (a) a successful atomicity gate gives an accepted inclusion proof of `commitValue(flowId, h)` for
  the executing bundle hash `h`;
* (b) the chain that proof is authenticated against is `proofs[i].sourceChainId`, which the gate
  pins to `legSourceChainIds[i]`;
* (c) the chain `declared h` is the one `_executeCalls` hands to the recipient.

Two further gaps:

* `declared` is a function of the 32-byte hash. That is justified there by keccak injectivity,
  which no map into `bytes32` has (`CRYPTO-PAIR-INJ`). In the contract two bundles with different
  `sourceChainId` can share a bundle hash, and then the honest chain's commit vouches for a bundle
  that declares another chain. `Properties.DeclaredOfHashForcesBundleBlindHash` shows what a
  function `declared` of the hash would cost: every bundle of one chain would share one hash.
* The countermodel `atomic_source_unbound_without_honest` is an existential over arbitrary types.
  It does not show that the gate accepts such a configuration.

This topic models `executeAtomicBundle`, the gate `requireFlowFinalized` it calls, and the
`_executeCalls` delivery, at byte level where the binding is decided (the two keccak preimages), and
restates the headline over that model.

## The code (pinned tree)

    // interop/interop-handler/L2InteropHandler.sol:49-100
    function executeAtomicBundle(bytes memory _bundle, AtomicFinalityProof calldata _finality) public {
        _ensureNotPaused();                                                          // :50 (no-op on L2)
        (InteropBundle memory interopBundle, bytes32 bundleHash, BundleStatus status) = _getBundleData(_bundle); // :53
        _validateBundleDestinationContext(bundleHash, interopBundle, interopBundle.sourceChainId);           // :57
        if (interopBundle.bundleAttributes.executionAddress.length != 0) { ... ExecutingNotAllowed ... }      // :62-75
        require(status == BundleStatus.Unreceived, BundleAlreadyProcessed(bundleHash));                       // :79
        IAtomicFlowManager(L2_ATOMIC_FLOW_MANAGER_ADDR).requireFlowFinalized(bundleHash, _finality);          // :83
        bundleStatus[bundleHash] = BundleStatus.FullyExecuted;                                                // :86
        ...                                                                                                   // :87-90
        _executeCalls({_sourceChainId: interopBundle.sourceChainId, _bundleHash: bundleHash, ...});            // :91-97
    }

    // interop/interop-handler/InteropHandlerBase.sol
    _getBundleData:                                                                  // :242-251
        require(_bundle.length != 0, EmptyBundle());                                 // :246
        interopBundle = abi.decode(_bundle, (InteropBundle));                        // :247
        require(interopBundle.version == INTEROP_BUNDLE_VERSION, ...);               // :248
        bundleHash = InteropDataEncoding.encodeInteropBundleHash(interopBundle.sourceChainId, _bundle); // :249
    _executeCalls, per call i:                                                       // :259-289
        require(interopCall.version == INTEROP_CALL_VERSION, ...);                   // :276
        _handleCallValue(interopCall.value, _sourceChainId);                         // :279
        IERC7786Recipient(interopCall.to).receiveMessage{value: interopCall.value}({
            receiveId: keccak256(abi.encodePacked(_bundleHash, i)),
            sender: InteroperableAddress.formatEvmV1(_sourceChainId, interopCall.from),
            payload: interopCall.data });                                            // :282-286
    _validateBundleDestinationContext(bundleHash, b, proofChainId):                  // :428-451
        require(b.sourceChainId == proofChainId, ...);                               // :434-437
        require(b.destinationChainId == block.chainid, ...);                         // :440-443
        require(b.destinationBaseTokenAssetId == _expectedDestinationBaseTokenAssetId(), ...); // :446-450

    // interop/interop-handler/L2InteropHandler.sol:115-120, l2-system/BaseTokenHolder.sol:99-109
    _handleCallValue(_value, _sourceChainId): if (_value > 0) L2_BASE_TOKEN_HOLDER.give(address(this), _value, _sourceChainId);
    give(_to, _amount, _fromChainId): ... L2_ASSET_TRACKER.handleFinalizeBaseTokenBridgingOnL2(_fromChainId, _amount); ...

    // atomic-interop/AtomicFlowManager.sol:105-131
    function requireFlowFinalized(bytes32 _executingBundleHash, AtomicFinalityProof calldata _finality)
        external view onlyInteropHandler {
        _checkFlowId(flow);                                                          // :110, body :247-259
        _checkSettlementLayerIsL1(flow.settlementLayerChainId);                      // :111, body :236-240
        if (_finality.proofs.length != n) revert ManagerProofCountMismatch(...);     // :114
        for (uint256 i = 0; i < n; ++i) {
            if (flow.legBundleHashes[i] == _executingBundleHash) executingIsLeg = true;              // :123
            if (_finality.proofs[i].sourceChainId != flow.legSourceChainIds[i]) revert ProofSourceChainMismatch(...); // :124-126
            uint256 value = AtomicInteropProof.commitValue(flow.flowId, flow.legBundleHashes[i]);   // :127
            AtomicInteropProof.verifyInclusion(_finality.proofs[i], value, flow.deadline, flow.settlementLayerChainId); // :128
        }
        if (!executingIsLeg) revert ManagerExecutingBundleNotInFlow(...);            // :130
    }

    // atomic-interop/libraries/AtomicInteropProof.sol:100-102, atomic-interop/IAtomicInterop.sol:94
    commitValue(_flowId, _specHash) = uint256(keccak256(abi.encode(ATOMIC_COMMIT_LEAF_TAG, _flowId, _specHash)));
    ATOMIC_COMMIT_LEAF_TAG = bytes4(keccak256("AtomicInterop.commit.v1"));

    // the source side, interop/InteropCenter.sol:639-659 (sole `append` call site :650-655)
    bytes memory interopBundleBytes = abi.encode(_bundle);                                    // :643
    bundleHash = InteropDataEncoding.encodeInteropBundleHash(block.chainid, interopBundleBytes); // :644
    IAtomicFlowManager(L2_ATOMIC_FLOW_MANAGER_ADDR).append({_flowId: ..., _bundleHash: bundleHash, ...}); // :650-655

The destination computes the bundle hash with the bundle's OWN `sourceChainId` field as the leading
word of the keccak preimage, and an honest source chain computes it with `block.chainid`. The gate
compares only hashes: `requireFlowFinalized` receives `bundleHash` and `_finality` and nothing else,
and the destination-context check compares the field with itself. So the field is bound to the
vouching chain exactly when the two keccak preimages agree, and that is what the model tracks.

## Modelling choices

* **Bundle type.** The decoded bundle is `Contracts.InteropCenter.Bundle`, the same structure the
  source-side `Dispatch` model builds, so source and destination talk about one type. It omits the
  constant `version` fields and the reserved `shadowAccount`.
* **Decoding.** `Dest.decode B = some b` means: `abi.decode(_bundle, (InteropBundle))` succeeds, the
  bundle version check (:248) passes, every call's version check (:276) passes, and `b` is the
  decoded struct. The call version check runs inside `_executeCalls`, after the status write, but a
  failure there reverts the whole transaction, so where it is checked does not change which
  transactions succeed. `decode` is abstract: no result depends on how the ABI decoder works.
* **Byte level where it matters.** The bundle hash is `keccak (abiEncode s B)` with `abiEncode` the
  byte model of `abi.encode(uint256, bytes)` from `InteropDataEncoding` `BundleHashEncoding`, and the
  commit value is `keccak` of the three-word `abi.encode(bytes4, bytes32, bytes32)`. `keccak` is one
  arbitrary function `List UInt8 → UInt256`, shared by every chain. Nothing about it is assumed.
* **The inclusion verifier is abstract.** `Dest.verifyInclusion p v deadline sl` says that
  `AtomicInteropProof.verifyInclusion(p, v, deadline, sl)` returns. Its internals (root
  authentication against an imported settlement-layer root, the deadline and settlement-layer checks,
  IMT membership) are modelled in `AtomicInteropProof` and `L2InteropCommitmentTree`. Here only one
  fact about it is used, and it is a premise: on proofs naming the vouching chain it accepts only
  that chain's honest commit values (`HonestVouching`). `VerifierSoundFor` and `TreeHoldsOnlyLog`
  split that premise into its two halves.
* **The honest chain's log.** An honest chain inserts into its tree only through `append`, whose
  sole call site (`InteropCenter.sol:650`) passes `encodeInteropBundleHash(block.chainid, B)`
  (`Protocol/LocalHonesty.lean`). A `CommittedLeg` is one such call: the flow id and the bytes `B`.
  Its commit value is computed with the chain's own id, as `:644` computes it. The log is a finite
  list given by the instance, so a collision with one of its entries is pinned
  (ASSUMPTIONS.md, "Results whose premises cannot hold").
* **What a delivery is.** A `Delivery` is one recipient call `_executeCalls` makes: target,
  `receiveId`, the chain and address `formatEvmV1` encodes as the ERC-7930 sender, payload and value.
  `sourceChainId` is also the chain `_handleCallValue` passes to `BaseTokenHolder.give` when the call
  carries value, which the asset tracker books the released base token against. Whether the
  recipient accepts (returns the selector, :287) is the recipient's business: a rejecting recipient
  reverts the transaction, which only removes runs.
* **Checks kept, checks omitted.** Every check of `executeAtomicBundle` and `requireFlowFinalized` is
  kept, so a countermodel that passes them passes the deployed checks. Omitted: events,
  `callStatus` (written `Executed` for every call, :88-90, and read by nothing here),
  `_ensureNotPaused` (empty on L2), and `onlyInteropHandler` (the handler is the caller).
  Reentrancy through a recipient is a separate execution with its own bundle (topic
  `InteropHandlerBase` `Reentrancy`).

## The upgrade tree (e561b9cc2), not modelled here

At e561b9cc2 the same question has three differences: the bundle hash is `keccak256(_bundle)` with
no leading chain word (`InteropDataEncoding.sol:14-16`), so the declared field is bound only through
the bytes and needs the ABI decoder to read back the honest chain's own field; `append` requires the
committing chain to be the leg's `legSourceChainIds` entry (`AtomicFlowManager.sol:139-145`); and
`executeAtomicBundle` skips the gate for a bundle already `Verified` by `verifyAtomicBundle`, which
runs the same gate first (`L2InteropHandler.sol:73-75`, :83-92). The destination-side gap is the
same: the gate never compares the bundle's `sourceChainId` with the vouching chain
(`AtomicFlowManager.sol:193-198`, `L2InteropHandler.sol:70`).
-/

namespace Contracts.L2InteropHandler.AtomicSourceFaithful

open AttackVectors.BundleHashEncoding (abiEncode word HashCollision)
open Contracts.InteropCenter (Address Bundle)

/-! ## Statuses, proofs and flows -/

/-- `BundleStatus` (`common/Messaging.sol:303-308`). -/
inductive BundleStatus
  | Unreceived
  | Verified
  | FullyExecuted
  | Unbundled
deriving DecidableEq

/-- `ImtProof` (`IAtomicInterop.sol:52-61`). `requireFlowFinalized` reads `sourceChainId` itself
(:124). Every other field is consumed only by `AtomicInteropProof.verifyInclusion`, which the model
keeps abstract, so they are carried as one opaque payload. -/
structure ImtProof where
  sourceChainId : UInt256
  payload : List UInt256
deriving DecidableEq

/-- `AtomicFlow` (`IAtomicInterop.sol:73-79`): the claimed `flowId` next to the fields it hashes. -/
structure AtomicFlow where
  flowId : UInt256
  /-- `uint64` in the source. -/
  deadline : UInt256
  settlementLayerChainId : UInt256
  legBundleHashes : List UInt256
  legSourceChainIds : List UInt256
deriving DecidableEq

/-- `AtomicFinalityProof` (`IAtomicInterop.sol:86-89`): the flow and one proof per leg. -/
structure AtomicFinalityProof where
  flow : AtomicFlow
  proofs : List ImtProof
deriving DecidableEq

/-- Leg `i` of the presented flow, with its proof: `legBundleHashes[i] = bh`,
`legSourceChainIds[i] = c` and `proofs[i] = p`, all three in range. -/
def LegAt (fin : AtomicFinalityProof) (i : ℕ) (bh c : UInt256) (p : ImtProof) : Prop :=
  fin.flow.legBundleHashes[i]? = some bh ∧ fin.flow.legSourceChainIds[i]? = some c ∧
    fin.proofs[i]? = some p

/-! ## The two keccak preimages, and the flow id's -/

/-- The bytes of the string `"AtomicInterop.commit.v1"`. -/
def commitTagString : List UInt8 := "AtomicInterop.commit.v1".toUTF8.toList

/-- `abi.encode` of `ATOMIC_COMMIT_LEAF_TAG = bytes4(keccak256("AtomicInterop.commit.v1"))`
(`IAtomicInterop.sol:94`): the four leading bytes of the hash, left-aligned in a word. -/
def commitTagWord (keccak : List UInt8 → UInt256) : List UInt8 :=
  (word (keccak commitTagString).val).take 4 ++ List.replicate 28 0

/-- `abi.encode(ATOMIC_COMMIT_LEAF_TAG, _flowId, _specHash)`: three static words. -/
def commitPreimage (keccak : List UInt8 → UInt256) (flowId bundleHash : UInt256) : List UInt8 :=
  commitTagWord keccak ++ (word flowId.val ++ word bundleHash.val)

/-- `AtomicInteropProof.commitValue(_flowId, _specHash)` (`AtomicInteropProof.sol:100-102`). -/
def commitValue (keccak : List UInt8 → UInt256) (flowId bundleHash : UInt256) : UInt256 :=
  keccak (commitPreimage keccak flowId bundleHash)

/-- The ABI words of an array's elements, in order. -/
def wordsOf (xs : List UInt256) : List UInt8 := (xs.map fun x => word x.val).flatten

/-- `abi.encode(legBundleHashes, legSourceChainIds, deadline, settlementLayerChainId)`, the input of
`_checkFlowId`'s keccak (`AtomicFlowManager.sol:255-257`). The head holds the two array offsets,
counted from the start, and the two static values; each array follows as its length and its
elements. No result depends on this layout: `_checkFlowId` binds the leg list to the claimed id,
which is an atomicity question (`InteropAtomicity` `FlowBinding`), not a source-binding one. -/
def flowIdPreimage (F : AtomicFlow) : List UInt8 :=
  word 128 ++ (word (128 + 32 * (F.legBundleHashes.length + 1)) ++ (word F.deadline.val ++
    (word F.settlementLayerChainId.val ++
      ((word F.legBundleHashes.length ++ wordsOf F.legBundleHashes) ++
        (word F.legSourceChainIds.length ++ wordsOf F.legSourceChainIds)))))

/-- `abi.encode(interopBundle.sourceChainId, _bundle)`: the keccak preimage of the destination's
bundle hash (`InteropHandlerBase.sol:249`, `InteropDataEncoding.sol:11-13`). Its leading word is the
decoded bundle's own `sourceChainId`. -/
def executedPreimage (B : List UInt8) (b : Bundle) : List UInt8 := abiEncode b.sourceChainId.val B

/-! ## The destination -/

/-- The destination chain's constants and the library functions the atomic path calls. -/
structure Dest where
  /-- `keccak256`. The same function on every chain. -/
  keccak : List UInt8 → UInt256
  /-- `block.chainid`. -/
  chainId : UInt256
  /-- `address(this)`, the handler (`L2_INTEROP_HANDLER_ADDR`). -/
  self : Address
  /-- `_expectedDestinationBaseTokenAssetId()`, `L2_NATIVE_TOKEN_VAULT.BASE_TOKEN_ASSET_ID()`
  (`L2InteropHandler.sol:123-125`). -/
  baseTokenAssetId : UInt256
  /-- The flow manager's `L1_CHAIN_ID` (`AtomicFlowManager.sol:57`). -/
  l1ChainId : UInt256
  /-- `abi.decode(_bundle, (InteropBundle))` with the bundle and call version checks; `none` is a
  revert. See the header. -/
  decode : List UInt8 → Option Bundle
  /-- `InteroperableAddress.parseEvmV1`; `none` is a revert. -/
  parseEvmV1 : List UInt8 → Option (UInt256 × Address)
  /-- `AtomicInteropProof.verifyInclusion(proof, value, deadline, slChainId)` returns
  (`AtomicInteropProof.sol:113-139`). Abstract: see the header. -/
  verifyInclusion : ImtProof → UInt256 → UInt256 → UInt256 → Prop

/-- The bundle hash `_getBundleData` computes for the bytes `B` that decode to `b`
(`InteropHandlerBase.sol:249`). -/
def executedHash (D : Dest) (B : List UInt8) (b : Bundle) : UInt256 :=
  D.keccak (executedPreimage B b)

/-- `_validateBundleDestinationContext(bundleHash, b, proofChainId)` does not revert
(`InteropHandlerBase.sol:428-451`). The public path passes the message proof's chain as
`proofChainId`; the atomic path passes `b.sourceChainId` (`L2InteropHandler.sol:57`). -/
def DestinationContextValid (D : Dest) (b : Bundle) (proofChainId : UInt256) : Prop :=
  b.sourceChainId = proofChainId ∧ b.destinationChainId = D.chainId ∧
    b.destinationBaseTokenAssetId = D.baseTokenAssetId

/-- The execution-address gate (`L2InteropHandler.sol:62-75`): permissionless when the attribute
is empty; otherwise it must parse, and the caller must be the handler itself or the named address
on this chain or on chain `0`. -/
def ExecutionPermitted (D : Dest) (caller : Address) (b : Bundle) : Prop :=
  b.bundleAttributes.executionAddress = [] ∨
    ∃ (ec : UInt256) (ea : Address), D.parseEvmV1 b.bundleAttributes.executionAddress = some (ec, ea) ∧
      (caller = D.self ∨ ((ec = D.chainId ∨ ec = 0) ∧ ea = caller))

/-- **THE ATOMICITY GATE.** `requireFlowFinalized(h, fin)` returns (`AtomicFlowManager.sol:105-131`).
Each field is one `revert` of the source. `legs` is the loop body for every leg, and
`executingIsLeg` is the flag checked after the loop. The executing bundle hash `h` appears only in
`executingIsLeg`: the gate never sees the bundle or its `sourceChainId`. -/
structure FlowGateAccepts (D : Dest) (h : UInt256) (fin : AtomicFinalityProof) : Prop where
  /-- `_checkFlowId`: `legBundleHashes` strictly ascending (`ManagerBundleHashesNotSorted`, :249-251). -/
  sorted : fin.flow.legBundleHashes.IsChain (· < ·)
  /-- `_checkFlowId`: `ManagerLegSourceChainIdsLengthMismatch` (:252-254). -/
  chainsLength : fin.flow.legSourceChainIds.length = fin.flow.legBundleHashes.length
  /-- `_checkFlowId`: `ManagerFlowIdMismatch` (:255-258). -/
  flowId : D.keccak (flowIdPreimage fin.flow) = fin.flow.flowId
  /-- `_checkSettlementLayerIsL1`: `ManagerSettlementLayerNotL1` (:236-240). -/
  settlementLayer : fin.flow.settlementLayerChainId = D.l1ChainId
  /-- `ManagerProofCountMismatch` (:114). -/
  proofCount : fin.proofs.length = fin.flow.legBundleHashes.length
  /-- The loop body, for every leg: `ProofSourceChainMismatch` (:124-126), then
  `verifyInclusion` of the leg's commit value under the claimed flow id (:127-128). -/
  legs : ∀ (i : ℕ) (bh c : UInt256) (p : ImtProof), LegAt fin i bh c p →
    p.sourceChainId = c ∧
      D.verifyInclusion p (commitValue D.keccak fin.flow.flowId bh) fin.flow.deadline
        fin.flow.settlementLayerChainId
  /-- `ManagerExecutingBundleNotInFlow` (:123, :130). -/
  executingIsLeg : ∃ i : ℕ, fin.flow.legBundleHashes[i]? = some h

/-- The destination handler's `bundleStatus` mapping (`InteropHandlerBase.sol:54`). -/
structure HandlerState where
  bundleStatus : UInt256 → BundleStatus

/-- `bundleStatus[h] = BundleStatus.FullyExecuted` (`L2InteropHandler.sol:86`). -/
def HandlerState.markExecuted (st : HandlerState) (h : UInt256) : HandlerState :=
  ⟨fun h' => if h' = h then .FullyExecuted else st.bundleStatus h'⟩

/-- One recipient call `_executeCalls` makes (`InteropHandlerBase.sol:279-286`). The sender the
recipient sees is `formatEvmV1(sourceChainId, fromAddr)`, and `sourceChainId` is also the chain
`_handleCallValue` passes to `BaseTokenHolder.give` when `value > 0`. -/
structure Delivery where
  target : Address
  /-- `keccak256(abi.encodePacked(_bundleHash, i))`. -/
  receiveId : UInt256
  /-- `_sourceChainId`. -/
  sourceChainId : UInt256
  /-- `interopCall.from`. -/
  fromAddr : Address
  payload : List UInt8
  value : ℕ

/-- The calls `_executeCalls(_sourceChainId: b.sourceChainId, _bundleHash: h, ...)` makes, in order
(`L2InteropHandler.sol:91-97`; `_executeAllCalls` is `true`, so every call runs). -/
def deliveries (D : Dest) (h : UInt256) (b : Bundle) : List Delivery :=
  b.calls.zipIdx.map fun ci =>
    { target := ci.1.target, receiveId := D.keccak (word h.val ++ word ci.2),
      sourceChainId := b.sourceChainId, fromAddr := ci.1.fromAddr, payload := ci.1.data,
      value := ci.1.value }

/-- Every check `executeAtomicBundle(B, fin)` makes, called by `caller` in state `st`, passes, and
`B` decodes to `b`. One field per `require`/`revert` of `L2InteropHandler.sol:49-83`. -/
structure AtomicChecksPass (D : Dest) (st : HandlerState) (caller : Address) (B : List UInt8)
    (fin : AtomicFinalityProof) (b : Bundle) : Prop where
  /-- `EmptyBundle` (`InteropHandlerBase.sol:246`). -/
  nonEmpty : B ≠ []
  /-- `abi.decode` and the version checks. -/
  decoded : D.decode B = some b
  /-- `_validateBundleDestinationContext(bundleHash, interopBundle, interopBundle.sourceChainId)` (:57). -/
  context : DestinationContextValid D b b.sourceChainId
  /-- The execution-address gate (:62-75). -/
  permitted : ExecutionPermitted D caller b
  /-- `BundleAlreadyProcessed` (:79). -/
  fresh : st.bundleStatus (executedHash D B b) = .Unreceived
  /-- `requireFlowFinalized(bundleHash, _finality)` (:83). -/
  gate : FlowGateAccepts D (executedHash D B b) fin

/-- **A SUCCESSFUL `executeAtomicBundle(B, fin)`.** The checks pass, the bundle hash is marked
`FullyExecuted`, and `_executeCalls` makes the calls `ds`. -/
structure ExecutesAtomic (D : Dest) (st : HandlerState) (caller : Address) (B : List UInt8)
    (fin : AtomicFinalityProof) (b : Bundle) (st' : HandlerState) (ds : List Delivery) : Prop where
  checks : AtomicChecksPass D st caller B fin b
  marked : st' = st.markExecuted (executedHash D B b)
  delivered : ds = deliveries D (executedHash D B b) b

/-! ## The vouching chain's side -/

/-- One `append` an honest chain's center made (`InteropCenter.sol:643-655`): the flow id it passed
and the bytes `abi.encode(_bundle)` it hashed. -/
structure CommittedLeg where
  flowId : UInt256
  bundleBytes : List UInt8
deriving DecidableEq

/-- `abi.encode(block.chainid, interopBundleBytes)` on chain `c` (`InteropCenter.sol:644`). -/
def CommittedLeg.preimage (c : UInt256) (e : CommittedLeg) : List UInt8 :=
  abiEncode c.val e.bundleBytes

/-- The bundle hash chain `c` passed to `append` for `e`. -/
def CommittedLeg.bundleHash (keccak : List UInt8 → UInt256) (c : UInt256) (e : CommittedLeg) :
    UInt256 :=
  keccak (e.preimage c)

/-- The value `append` inserted into chain `c`'s tree for `e`: `commitValue(flowId, bundleHash)`
(`AtomicFlowManager.sol:97`). -/
def CommittedLeg.value (keccak : List UInt8 → UInt256) (c : UInt256) (e : CommittedLeg) : UInt256 :=
  commitValue keccak e.flowId (e.bundleHash keccak c)

/-- **HONEST VOUCHING BY CHAIN `c`, AGAINST ITS OWN LOG.** On every proof that names chain `c`, the
destination's `verifyInclusion` accepts only commit values of legs in `log`, computed as chain `c`'s
sole `append` call site computes them, with `c` as the leading word.

This is the faithful form of `HonestCommits`, for the one chain the gate names. It packs two facts:
chain `c` runs the deployed send path (`LocalHonesty`: its tree holds only values its `append`
inserted, and `append` is reached only from `_dispatchBundle`), and the verifier is sound for chain
`c`'s tree (Merkle and root authentication). `VerifierSoundFor` and `TreeHoldsOnlyLog` are the two
halves. It is a premise, satisfiable (`Properties.AtomicSourceBoundWitness`), and it is the premise
`Properties.MisbehavingLegChainImpersonates` drops. -/
def HonestVouching (D : Dest) (c : UInt256) (log : List CommittedLeg) : Prop :=
  ∀ (p : ImtProof) (v deadline sl : UInt256), p.sourceChainId = c →
    D.verifyInclusion p v deadline sl → ∃ e ∈ log, v = e.value D.keccak c

/-- The verifier is sound for chain `c`'s tree: an accepted proof naming `c` proves a member of
`tree c`. Here `tree c` is the set of values chain `c`'s authenticated batch-end trees held in
on-time batches. -/
def VerifierSoundFor (D : Dest) (tree : UInt256 → Set UInt256) (c : UInt256) : Prop :=
  ∀ (p : ImtProof) (v deadline sl : UInt256), p.sourceChainId = c →
    D.verifyInclusion p v deadline sl → v ∈ tree c

/-- Chain `c`'s tree holds only the commit values of the legs in `log`. -/
def TreeHoldsOnlyLog (keccak : List UInt8 → UInt256) (tree : UInt256 → Set UInt256) (c : UInt256)
    (log : List CommittedLeg) : Prop :=
  ∀ v ∈ tree c, ∃ e ∈ log, v = e.value keccak c

/-- The verifier that accepts exactly the members of the named chain's tree. Sound and complete for
`tree` by construction (`Properties.IdealVerifierSound`); used by the witnesses and countermodels,
where `tree c` stands for the values chain `c`'s on-time batch-end trees held. -/
def idealVerifier (tree : UInt256 → Set UInt256) :
    ImtProof → UInt256 → UInt256 → UInt256 → Prop :=
  fun p v _ _ => v ∈ tree p.sourceChainId

/-! ## Pinned collisions -/

/-- **A PINNED COMMIT-VALUE COLLISION.** keccak collides on the commit preimage of the executing leg
(the flow's claimed id and the executed bundle hash `h`) and the commit preimage of the logged leg
`e` of chain `c`. Both inputs are named by the instance. -/
def CommitPreimageClash (keccak : List UInt8 → UInt256) (flowId h c : UInt256) (e : CommittedLeg) :
    Prop :=
  HashCollision keccak (commitPreimage keccak flowId h)
    (commitPreimage keccak e.flowId (e.bundleHash keccak c))

/-- **A PINNED BUNDLE-HASH COLLISION.** keccak collides on the executed bundle's hash preimage
`abi.encode(b.sourceChainId, B)` and the logged leg's `abi.encode(c, e.bundleBytes)`. -/
def BundlePreimageClash (keccak : List UInt8 → UInt256) (B : List UInt8) (b : Bundle) (c : UInt256)
    (e : CommittedLeg) : Prop :=
  HashCollision keccak (executedPreimage B b) (e.preimage c)

/-! ## The vouching chain's run, from the `InteropCenter` `Dispatch` model -/

/-- The legs a chain's center appended along a run: one per atomic dispatch in the `Dispatch` ghost
log, with the flow id passed to `append` and the bytes `abi.encode(bundle)` hashed at `:643-644`. -/
def dispatchLegs (P : Contracts.InteropCenter.Params) (S : Contracts.InteropCenter.State) :
    List CommittedLeg :=
  (S.log.filter Contracts.InteropCenter.Dispatch.isAtomic).map fun d =>
    ⟨d.atomicSend.flowId, P.enc d.bundle⟩

/-- **THE VERIFIER ACCEPTS ONLY THE CHAIN'S COMMITTED LEGS.** On a proof naming chain `P.chainId`,
the destination's `verifyInclusion` accepts only `commitValue(f, h)` for a leg `(f, h)` that chain's
manager holds as non-`Unset`. Its content: the tree's only inserter is the manager
(`L2InteropCommitmentTree.sol:53-54`), `append` inserts exactly `commitValue(_flowId, _bundleHash)`
right after marking that leg `Committed` (`AtomicFlowManager.sol:93-99`), the tree is append-only,
and the verifier is sound for that chain's tree. The `Dispatch` model omits the tree insertion, so
this is the link stated as a premise. -/
def AcceptsOnlyCommittedLegs (D : Dest) (P : Contracts.InteropCenter.Params)
    (S : Contracts.InteropCenter.State) : Prop :=
  ∀ (p : ImtProof) (v deadline sl : UInt256), p.sourceChainId = P.chainId →
    D.verifyInclusion p v deadline sl →
      ∃ f h : UInt256, S.manager.legState f h ≠ .Unset ∧ v = commitValue D.keccak f h

end Contracts.L2InteropHandler.AtomicSourceFaithful
