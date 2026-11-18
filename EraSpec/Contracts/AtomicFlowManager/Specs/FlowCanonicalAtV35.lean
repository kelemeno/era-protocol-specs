import EraSpec.Core.Word
import EraSpec.Contracts.AtomicFlowManager.Specs.FlowCanonical
import EraSpec.Contracts.AtomicFlowManager.Specs.Model

/-!
# Contract spec at `draft/v0.35.0`: the flow preimage, `_validateAndComputeFlowId`, and the leg writes

Source: matter-labs/era-contracts, branch `draft/v0.35.0` at commit `b17415d20`
(`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`). Paths are relative to `l1-contracts/contracts/` at
that commit. The topic was first written against `d9f678900`; no file under `atomic-interop/`
changed between the two commits, so every line cited here reads the same at both. The pin models
(`Specs/FlowCanonical.lean` and `Specs/Model.lean`, era-contracts `c67894b9`) are not changed;
this file models the v35 code next to them.

**This file is definitions only.** Statements are in
`EraSpec.Contracts.AtomicFlowManager.Properties.FlowCanonicalAtV35`, proofs in
`EraSpec.Contracts.AtomicFlowManager.Proofs.FlowCanonicalAtV35`.

## The code at `b17415d20`

    // atomic-interop/IAtomicInterop.sol:50-56
    struct AtomicFlowPreimage {
        bytes1 version;
        uint64 deadline;
        uint256 settlementLayerChainId;
        bytes32[] legBundleHashes;
        uint256[] legSourceChainIds;
    }
    // IAtomicInterop.sol:64-67
    struct AtomicFlow { bytes32 flowId; AtomicFlowPreimage preimage; }
    // IAtomicInterop.sol:91 and :99
    bytes1 constant ATOMIC_FLOW_PREIMAGE_VERSION = 0x01;
    uint256 constant MAX_ATOMIC_FLOW_LEGS = 8;

    // atomic-interop/AtomicFlowManager.sol:360-379
    function _validateAndComputeFlowId(AtomicFlowPreimage calldata _preimage) internal pure returns (bytes32) {
        if (_preimage.version != ATOMIC_FLOW_PREIMAGE_VERSION) revert ManagerFlowPreimageVersionMismatch(..); // :361-363
        uint256 n = _preimage.legBundleHashes.length;                                                     // :364
        if (n > MAX_ATOMIC_FLOW_LEGS) revert ManagerTooManyLegs(MAX_ATOMIC_FLOW_LEGS, n);                   // :367-369
        for (uint256 i = 1; i < n; ++i) {
            if (_preimage.legBundleHashes[i] <= _preimage.legBundleHashes[i - 1]) revert ManagerBundleHashesNotSorted();
        }                                                                                                 // :370-374
        if (_preimage.legSourceChainIds.length != n) revert ManagerLegSourceChainIdsLengthMismatch(..);     // :375-377
        return keccak256(abi.encode(_preimage));                                                          // :378
    }
    // AtomicFlowManager.sol:348-353
    function _checkFlowId(AtomicFlow calldata _flow) internal pure {
        bytes32 computed = _validateAndComputeFlowId(_flow.preimage);
        if (computed != _flow.flowId) revert ManagerFlowIdMismatch(_flow.flowId, computed);
    }

`append` calls `_validateAndComputeFlowId` directly (`AtomicFlowManager.sol:109`), and
`requireFlowFinalized` (`:182`) and `authorizeRefund` (`:217`) call `_checkFlowId`; in each the
call comes before every other check of the body. `claimRefund` (`:250-265`) calls neither: it
acts on the `(flowId, bundleHash)` it is given, if that leg is `Revertable`.

The two functions read the same on `main` (`70096e2ea`, and `3605e82`), at `:346-365` and
`:334-339`.

## What changed from the pin

At `c67894b9` (`AtomicFlowManager.sol:247-259`) `_checkFlowId` ran the neighbour sort check and
the length check, then hashed
`abi.encode(legBundleHashes, legSourceChainIds, deadline, settlementLayerChainId)`, and `append`
(`:87-101`) took an opaque `flowId` and ran neither. At `b17415d20`:

1. the preimage is one struct with a version byte, hashed as a whole (`:378`), with a new field
   order;
2. two checks are new and come first: the version byte (`:361-363`) and the leg cap (`:367-369`);
3. the sort check and the length check are unchanged (`:370-377`);
4. one function serves all three entry points, `append` included.

So the pin's `Valid` is still necessary for acceptance but no longer sufficient. The pin
docstring's pairing with `BundleHashEncoding.abiEncode_inj` does not cover the new layout: that
lemma is about `abi.encode(uint256, bytes)`, and no `abi.encode` injectivity for the v35 struct is
proved here. The whole composite `keccak256 ∘ abi.encode` is the free parameter `enc`, and
binding results name a `PreimageClashV35` on two given preimages instead of assuming
injectivity (see `CRYPTO-ID` in `ASSUMPTIONS.md`).

## Modelling choices

* `bytes1 version` is `UInt8`; `bytes32`/`uint256` words are `UInt256`; `uint64 deadline` is `ℕ`,
  as in the pin's `Contracts.Atomicity.Flow`. The `uint64` bound is not modelled: statements
  quantify over a superset of the decodable preimages, and every witness uses deadlines below
  `2^64`.
* `bytes32` values are compared with `<=` (`:371`), which orders them as big-endian unsigned
  integers: the order of `UInt256`.
* A revert is `none`. Which error is raised is not modelled.
* The sort check is `AttackVectors.FlowCanonical.Ascending`, the pin's transcription of the same
  neighbour loop; the two arrays form the pin's `AttackVectors.FlowCanonical.Flow`.

## The leg writes (`MODEL-AFM-V35` in `ASSUMPTIONS.md`)

`_state` (`AtomicFlowManager.sol:61`) is written by three entry points only: `append` (`:166`),
`authorizeRefund` (`:244`) and `claimRefund` (`:260`). Below, each entry point that reads or
writes it is a function on the pin's `Contracts.AtomicFlowManager.Manager`, the same mapping.
Each function transcribes, in source order, the flow-id check, the checks that pick out legs of
the presented preimage, the `_state` guard and the write; its docstring lists the checks it
leaves out. Each left-out check only reverts, so leaving it out only adds successful calls; it
never changes what a successful call writes.

A run (`runV35`) is a sequence of calls, each succeeding on the state the previous ones left.
Before its write, each writer makes only `view` external calls (`append`: `:120-122`, `:157`;
`authorizeRefund`: `:231`, `:234`; `claimRefund`: none), and none between its `_state` guard and
its write; after its write, `append` calls the tree (`:170`) and `claimRefund` runs
`_recoverBundle` (`:262`). So a call that re-enters the manager appears in a run as its own call,
after the write of the call it re-entered, and a call that reverts is absent from the run
together with every call it made. These two sentences are a reading of the source, not a
theorem.

The hash `enc` and this chain's `block.chainid` are fixed for a run. The transcribed parts of
the four entry points read the same on `main` `70096e2ea`, at other lines; there
`requireFlowFinalized` and `authorizeRefund` have no receive filter, a check left out here.
-/

namespace Contracts.FlowCanonicalAtV35

open AttackVectors.FlowCanonical
open Contracts.AtomicFlowManager (Manager LegState)

/-! ## The preimage and the check -/

/-- `AtomicFlowPreimage` (`atomic-interop/IAtomicInterop.sol:50-56`). -/
structure PreimageV35 where
  /-- `bytes1 version`. -/
  version : UInt8
  /-- `uint64 deadline`, a settlement-layer timestamp. -/
  deadline : ℕ
  /-- `uint256 settlementLayerChainId`. -/
  settlementLayerChainId : UInt256
  /-- `bytes32[] legBundleHashes`, required strictly ascending. -/
  legBundleHashes : List UInt256
  /-- `uint256[] legSourceChainIds`, aligned 1:1 with `legBundleHashes`. -/
  legSourceChainIds : List UInt256
deriving DecidableEq

/-- `AtomicFlow` (`IAtomicInterop.sol:64-67`): the claimed id next to its preimage. -/
structure AtomicFlowV35 where
  /-- `bytes32 flowId`, recomputed from `preimage` and matched before use. -/
  flowId : UInt256
  /-- `AtomicFlowPreimage preimage`. -/
  preimage : PreimageV35
deriving DecidableEq

/-- `ATOMIC_FLOW_PREIMAGE_VERSION = 0x01` (`IAtomicInterop.sol:91`). -/
def ATOMIC_FLOW_PREIMAGE_VERSION_V35 : UInt8 := 0x01

/-- `MAX_ATOMIC_FLOW_LEGS = 8` (`IAtomicInterop.sol:99`). -/
def MAX_ATOMIC_FLOW_LEGS_V35 : ℕ := 8

/-- `keccak256(abi.encode(preimage))` (`AtomicFlowManager.sol:378`), kept abstract. -/
abbrev PreimageHashV35 := PreimageV35 → UInt256

/-- The two arrays of a preimage, as the pin's `AttackVectors.FlowCanonical.Flow`. -/
def PreimageV35.arrays (p : PreimageV35) : Flow UInt256 UInt256 :=
  ⟨p.legBundleHashes, p.legSourceChainIds⟩

/-- The sort check is decidable: it is a neighbour scan. -/
instance (l : List UInt256) : Decidable (Ascending l) :=
  inferInstanceAs (Decidable (l.IsChain (· < ·)))

/-- **`_validateAndComputeFlowId`** (`AtomicFlowManager.sol:360-379`), in source order:
the version byte (`:361-363`), the leg cap (`:367-369`), the neighbour sort check
(`:370-374`), the length check (`:375-377`), then the hash (`:378`). `none` is a
revert. -/
def validateV35 (enc : PreimageHashV35) (p : PreimageV35) : Option UInt256 :=
  if p.version ≠ ATOMIC_FLOW_PREIMAGE_VERSION_V35 then none
  else if MAX_ATOMIC_FLOW_LEGS_V35 < p.legBundleHashes.length then none
  else if ¬ Ascending p.legBundleHashes then none
  else if p.legSourceChainIds.length ≠ p.legBundleHashes.length then none
  else some (enc p)

/-- **`_checkFlowId`** (`AtomicFlowManager.sol:348-353`): the preimage is accepted and
its hash is the claimed id. -/
def CheckFlowIdV35 (enc : PreimageHashV35) (F : AtomicFlowV35) : Prop :=
  validateV35 enc F.preimage = some F.flowId

instance (enc : PreimageHashV35) (F : AtomicFlowV35) : Decidable (CheckFlowIdV35 enc F) :=
  inferInstanceAs (Decidable (validateV35 enc F.preimage = some F.flowId))

/-- The four checks of `_validateAndComputeFlowId` at v35, as one proposition. -/
structure AcceptedV35 (p : PreimageV35) : Prop where
  /-- `ManagerFlowPreimageVersionMismatch` (`:361-363`). -/
  version : p.version = ATOMIC_FLOW_PREIMAGE_VERSION_V35
  /-- `ManagerTooManyLegs` (`:367-369`). -/
  legCap : p.legBundleHashes.length ≤ MAX_ATOMIC_FLOW_LEGS_V35
  /-- `ManagerBundleHashesNotSorted` (`:370-374`). -/
  sorted : Ascending p.legBundleHashes
  /-- `ManagerLegSourceChainIdsLengthMismatch` (`:375-377`). -/
  lengths : p.legSourceChainIds.length = p.legBundleHashes.length

/-- **A NAMED PREIMAGE COLLISION.** `enc` maps the two given, distinct preimages to one id. This
is a keccak collision on two named `abi.encode` images (or an `abi.encode` non-injectivity on
them); it is false for any hash that separates the two. -/
def PreimageClashV35 (enc : PreimageHashV35) (p q : PreimageV35) : Prop :=
  p ≠ q ∧ enc p = enc q

/-- A preimage hash that is honest about one preimage `p0`: `id` on `p0`, `id + 1`
everywhere else. Used to show the clash disjuncts are not tautologies. -/
def honestPreimageHashV35 (p0 : PreimageV35) (id : UInt256) : PreimageHashV35 :=
  fun p => if p = p0 then id else id + 1

/-- A preimage hash that maps exactly the two named preimages `p0` and `q0` to `id`, and every
other preimage to `id + 1`: the only clash it has with `p0` or `q0` is between them. Used to show
the clash disjuncts are reachable. -/
def pairClashHashV35 (p0 q0 : PreimageV35) (id : UInt256) : PreimageHashV35 :=
  fun p => if p = p0 ∨ p = q0 then id else id + 1

/-! ## The leg writes -/

/-- One call of an `AtomicFlowManager` entry point that reads or writes `_state`, with the
arguments the transcribed checks read. -/
inductive CallV35 where
  /-- `append(_bundleHash, _lowNullifierIndex, _flowPreimage)` (`AtomicFlowManager.sol:104-173`). -/
  | append (bundleHash : UInt256) (preimage : PreimageV35)
  /-- `requireFlowFinalized(_executingBundleHash, _finality)` (`:176-213`), with
  `_finality.flow`. -/
  | requireFinalized (executingBundleHash : UInt256) (flow : AtomicFlowV35)
  /-- `authorizeRefund(_flow, _missingLegIndex, _absence)` (`:216-247`). -/
  | authorizeRefund (flow : AtomicFlowV35) (missingLegIndex : ℕ)
  /-- `claimRefund(_flowId, _bundle)` (`:250-265`), with `bundleHash` the hash of `_bundle`
  computed at `:252`. -/
  | claimRefund (flowId bundleHash : UInt256)
deriving DecidableEq

/-- `legIndex` in `append` (`AtomicFlowManager.sol:130-137`): the first position whose bundle
hash is `h`, or `n` if there is none. -/
def legIndexV35 (p : PreimageV35) (h : UInt256) : ℕ :=
  p.legBundleHashes.idxOf h

/-- **`append` at v35** (`AtomicFlowManager.sol:104-173`), on `_state`. Transcribed checks, in
source order: `_validateAndComputeFlowId` (`:109`); the committing bundle is a leg
(`:130-140`); that leg's declared source chain is this chain (`:141-147`); the leg is `Unset`
(`:162-164`). Then `_state[flowId][_bundleHash] = Committed` (`:166`). Left out (each only
reverts): the caller (`onlyInteropCenter`), the settlement layer (`:110`), the imported-root
deadline check (`:120-125`), the other legs' registration (`:149-160`), and the tree insert
(`:168-170`). -/
def appendV35 (enc : PreimageHashV35) (chainId : UInt256) (M : Manager) (h : UInt256)
    (p : PreimageV35) : Option Manager :=
  match validateV35 enc p with
  | none => none
  | some id =>
    if legIndexV35 p h = p.legBundleHashes.length then none
    else if p.legSourceChainIds[legIndexV35 p h]? ≠ some chainId then none
    else if M.legState id h ≠ .Unset then none
    else some (M.set id h .Committed)

/-- **`requireFlowFinalized` at v35** (`AtomicFlowManager.sol:176-213`), a `view`: it returns
the state unchanged or reverts. Transcribed checks: `_checkFlowId` (`:182`) and that the
executing bundle is a leg (`:193-197`, `:210-212`). Left out (each only reverts): the caller
(`onlyInteropHandler`), the settlement layer (`:183`), the proof count (`:185-188`), and per leg
the proof's source chain, the receive filter and the inclusion proof (`:198-208`). -/
def requireFinalizedV35 (enc : PreimageHashV35) (M : Manager) (e : UInt256)
    (F : AtomicFlowV35) : Option Manager :=
  if validateV35 enc F.preimage = some F.flowId ∧ e ∈ F.preimage.legBundleHashes then some M
  else none

/-- The marking loop of `authorizeRefund` (`AtomicFlowManager.sol:238-246`): for each leg hash
`h` of the flow, in order, `_state[flowId][h]` moves from `Committed` to `Revertable`; a leg in
any other state is skipped. -/
def markRevertableV35 (id : UInt256) (M : Manager) (legs : List UInt256) : Manager :=
  legs.foldl (fun M h => if M.legState id h = .Committed then M.set id h .Revertable else M) M

/-- **`authorizeRefund` at v35** (`AtomicFlowManager.sol:216-247`), on `_state`. Transcribed
checks: `_checkFlowId` (`:217`) and `_missingLegIndex < n` (`:224-226`); then the marking loop
under the presented `flowId` (`:238-246`). Left out (each only reverts): the settlement layer
(`:218`), the absence proof's source chain (`:227-230`), the receive filter (`:231`) and the
absence proof (`:233-234`). The function has no caller check. -/
def authorizeRefundV35 (enc : PreimageHashV35) (M : Manager) (F : AtomicFlowV35) (k : ℕ) :
    Option Manager :=
  if validateV35 enc F.preimage = some F.flowId ∧ k < F.preimage.legBundleHashes.length then
    some (markRevertableV35 F.flowId M F.preimage.legBundleHashes)
  else none

/-- **`claimRefund` at v35** (`AtomicFlowManager.sol:250-265`), on `_state`: the leg must be
`Revertable` (`:254-257`) and becomes `Reverted` (`:260`). No flow-id check runs. Left out:
decoding `_bundle` and hashing it (`:251-252`; `h` is that hash), and `_recoverBundle` (`:262`),
whose external calls follow the write and whose revert reverts the claim. -/
def claimRefundV35 (M : Manager) (id h : UInt256) : Option Manager :=
  if M.legState id h = .Revertable then some (M.set id h .Reverted) else none

/-- One successful-or-reverting call, on this chain's manager (`chainId` is `block.chainid`). -/
def stepV35 (enc : PreimageHashV35) (chainId : UInt256) (M : Manager) : CallV35 → Option Manager
  | .append h p => appendV35 enc chainId M h p
  | .requireFinalized e F => requireFinalizedV35 enc M e F
  | .authorizeRefund F k => authorizeRefundV35 enc M F k
  | .claimRefund id h => claimRefundV35 M id h

/-- A run: the calls in order, each succeeding on the state the previous ones left; `none` if
one of them reverts. -/
def runV35 (enc : PreimageHashV35) (chainId : UInt256) : Manager → List CallV35 → Option Manager
  | M, [] => some M
  | M, c :: cs => (stepV35 enc chainId M c).bind fun M' => runV35 enc chainId M' cs

/-- The call is `append(h, p)` for a preimage `p` with `enc p = id`: an `append` whose write
would be to leg `(id, h)`. -/
def CallV35.appendsLegV35 (enc : PreimageHashV35) (id h : UInt256) : CallV35 → Bool
  | .append h' p => decide (h' = h ∧ enc p = id)
  | _ => false

/-! ## Witness data -/

/-- This chain's id in the witnesses. -/
def wChainV35 : UInt256 := 270

/-- An accepted three-leg flow: legs `11`, `22`, `33`, declared on chains `270`, `271`, `270`
(a source chain may repeat), deadline `1000`, settlement layer `1`. -/
def wFlowV35 : PreimageV35 :=
  { version := 0x01, deadline := 1000, settlementLayerChainId := 1,
    legBundleHashes := [11, 22, 33], legSourceChainIds := [270, 271, 270] }

/-- `wFlowV35` with deadline `2000`: the same legs and source chains. -/
def wFlowLateV35 : PreimageV35 := { wFlowV35 with deadline := 2000 }

/-- `wFlowV35` with version byte `0x02`. -/
def wWrongVersionV35 : PreimageV35 := { wFlowV35 with version := 0x02 }

/-- Nine legs `1, …, 9`, all declared on chain `270`, version `0x01`: sorted, lengths equal. -/
def wOversizedV35 : PreimageV35 :=
  { version := 0x01, deadline := 1000, settlementLayerChainId := 1,
    legBundleHashes := [1, 2, 3, 4, 5, 6, 7, 8, 9],
    legSourceChainIds := [270, 270, 270, 270, 270, 270, 270, 270, 270] }

/-- `wOversizedV35` without its last leg: eight legs. -/
def wCappedV35 : PreimageV35 :=
  { wOversizedV35 with
    legBundleHashes := wOversizedV35.legBundleHashes.dropLast,
    legSourceChainIds := wOversizedV35.legSourceChainIds.dropLast }

/-- Commit legs `11` and `33` of `wFlowV35` (both declared on this chain) under id `7`,
authorize the refund of the flow, then claim leg `11`. -/
def wRunV35 : List CallV35 :=
  [.append 11 wFlowV35, .append 33 wFlowV35, .authorizeRefund ⟨7, wFlowV35⟩ 1, .claimRefund 7 11]

/-- Commit leg `11` under `wFlowV35`, then authorize a refund presenting `wFlowLateV35` under
the same id `7`. -/
def wLateRefundRunV35 : List CallV35 :=
  [.append 11 wFlowV35, .authorizeRefund ⟨7, wFlowLateV35⟩ 0]

end Contracts.FlowCanonicalAtV35
