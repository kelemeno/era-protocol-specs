import EraSpec.Contracts.InteropRootStorage.Specs.Storage

/-!
# Model: `L2MessageVerification` — proving inclusion against the imported roots

**This file is definitions only.**  Statements are in
`EraSpec.Contracts.InteropRootStorage.Properties.Verification`, proofs in
`EraSpec.Contracts.InteropRootStorage.Proofs.Verification`.

## Source (era-contracts `d9f678900e1bc8286412b78f56d4a9f443983c29`, `l1-contracts/contracts/`)

`interop/L2MessageVerification.sol:18-56`, the one function the contract adds:

    function _proveL2LeafInclusionRecursive(uint256 _chainId, uint256 _blockOrBatchNumber,
        uint256 _leafProofMask, bytes32 _leaf, bytes32[] calldata _proof, uint256 _depth
    ) internal view override returns (bool) {
        ProofData memory proofData = MessageHashing._getProofData({…});             // :26-32
        if (proofData.finalProofNode) {                                             // :33
            bytes32 correctBatchRoot =
                L2_INTEROP_ROOT_STORAGE.interopRoots(_chainId, _blockOrBatchNumber).root;   // :37
            return correctBatchRoot == proofData.batchSettlementRoot
                && correctBatchRoot != bytes32(0);                                  // :38
        }
        if (_depth == 1) revert DepthMoreThanOneForRecursiveMerkleProof();          // :40-42
        return this.proveL2LeafInclusionSharedRecursive({                           // :46-55
            _chainId: proofData.settlementLayerChainId,
            _blockOrBatchNumber: proofData.settlementLayerBatchNumber,
            _leafProofMask: proofData.settlementLayerBatchRootMask,
            _leaf: proofData.chainIdLeaf,
            _proof: MessageHashing.extractSliceUntilEnd(_proof, proofData.ptr),
            _depth: _depth + 1 });
    }

`common/MessageVerification.sol` supplies the external entry points, all of which end in
that function: `proveL2LeafInclusionShared` (`:35-50`, `_depth = 0` via `_proveL2LeafInclusion`,
`:64-73`), `proveL2LeafInclusionSharedRecursive` (`:52-62`, `public`, the caller's `_depth`),
and the log, message, transaction-status and deposit-parameter forms (`:17-32`, `:111-126`,
`:129-147`, `:149-165`), which call `_proveL2LeafInclusion` with `_leafProofMask = _index`
and `_leaf = MessageHashing.getLeafHashFromLog(log)` for a log they build (`:85-108`).

`common/libraries/MessageHashing.sol`: `parseProofMetadata` (`:101-143`), `_getProofData`
(`:152-236`), `extractSlice` (`:306-315`), `extractSliceUntilEnd` (`:319-324`), `batchLeafHash`
(`:76-82`), `chainIdLeafHash` (`:87-89`).  `common/libraries/Merkle.sol`: `calculateRootMemory`
(`:53-70`), `_validatePathLengthForSingleProof` (`:133-140`), `efficientHash` (`:125-131`).
`L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH` and `SUPPORTED_PROOF_METADATA_VERSION = 1` are
`common/Config.sol:27`, `:30`.

## What is modelled

* `_getProofData` word for word: the two reverts on an empty proof and on the default leaf,
  the metadata parse (both proof formats, the version check, the final-node/batch-length
  check), both Merkle walks with their length and index checks, every bounds-checked read of
  `_proof`, and the unpacking of the settlement-layer words.  A revert or panic is `none`.
* The recursion, the depth check, the checked `_depth + 1`, and the terminal read of
  `L2_INTEROP_ROOT_STORAGE.interopRoots(…).root` — the `State` of `Specs/Storage.lean`.
* `Anchor`/`anchorRec`: the same recursion with the storage read left out, returning the key
  the terminal step would read and the root it would compare with.  It is a specification
  device; `Properties.ProveIsOneStorageRead` proves the contract is exactly "compute the
  anchor, then one comparison".

## What is not modelled

* The three hashes.  `Hashes` is a parameter: `node` for `Merkle.efficientHash`
  (`keccak256` of 64 bytes), `batchLeaf` for `MessageHashing.batchLeafHash`, `chainIdLeaf` for
  `MessageHashing.chainIdLeafHash`.  No result here assumes anything about them; in particular
  none assumes injectivity.  That an accepted walk opens a tree is the `Merkle` folder's
  subject (`../Merkle/`), not this one's.
* The log-shaped entry points' leaf: `getLeafHashFromLog` is `keccak256` of a packed log, a
  `SOL-ABI` matter.  They are `proveL2LeafInclusionShared` at `leaf :=` that hash,
  `leafProofMask := _index`, and are covered through it.
* The self-call `this.proveL2LeafInclusionSharedRecursive` is modelled as a direct recursive
  call whose revert propagates (`SOL-CONTROL`); gas is not modelled.  Recursion is by `fuel`,
  with `proof.length` supplied by the entry points — every hop consumes at least five proof
  words, so that is always enough (`Properties.FuelIrrelevant`).
* Proof pointers (`ptr`, slice bounds) are natural numbers: they never exceed the proof's
  length plus 510, far below `2^256`, so the checked additions cannot overflow.
* That `L2_INTEROP_ROOT_STORAGE` is the contract of `Specs/Storage.lean` (deployment,
  `BUILD-IDENTITY`).
-/

namespace Contracts.InteropRootStorage

/-- The three hash functions the proof format uses, uninterpreted. -/
structure Hashes where
  /-- `Merkle.efficientHash(lhs, rhs)` (`Merkle.sol:125-131`). -/
  node : UInt256 → UInt256 → UInt256
  /-- `MessageHashing.batchLeafHash(batchRoot, batchNumber, l1Timestamp)` (`:76-82`). -/
  batchLeaf : UInt256 → UInt256 → UInt256 → UInt256
  /-- `MessageHashing.chainIdLeafHash(chainIdRoot, chainId)` (`:87-89`). -/
  chainIdLeaf : UInt256 → UInt256 → UInt256

/-- `L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH` (`common/Config.sol:27`). -/
def L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH : UInt256 :=
  0x72abee45b59e344af8a6e520241c4744aff26ed411f4c4b00f8af09adada43ba

/-- `SUPPORTED_PROOF_METADATA_VERSION` (`common/Config.sol:30`). -/
def SUPPORTED_PROOF_METADATA_VERSION : ℕ := 1

/-! ## `Merkle.calculateRootMemory` -/

/-- The loop of `calculateRootMemory` (`Merkle.sol:61-67`): fold the path into the item,
orienting each hash by the current index's parity and halving the index. -/
def walk (h : UInt256 → UInt256 → UInt256) : List UInt256 → ℕ → UInt256 → UInt256
  | [], _, x => x
  | s :: path, idx, x => walk h path (idx / 2) (if idx % 2 = 0 then h x s else h s x)

/-- `Merkle.calculateRootMemory(_path, _index, _itemHash)` (`Merkle.sol:53-70`) with
`_validatePathLengthForSingleProof` (`:133-140`). -/
def calculateRootMemory (h : UInt256 → UInt256 → UInt256) (path : List UInt256) (index item : UInt256) :
    Option UInt256 :=
  if 256 ≤ path.length then none                    -- :134 MerklePathOutOfBounds
  else if 2 ^ path.length ≤ index.val then none     -- :137 MerkleIndexOutOfBounds
  else some (walk h path index.val item)

/-! ## `MessageHashing` -/

/-- `extractSlice(_proof, _left, _right)` (`MessageHashing.sol:306-315`): the checked
`_right - _left`, and a bounds panic if any index in `[_left, _right)` is past the end. -/
def extractSlice (proof : List UInt256) (left right : ℕ) : Option (List UInt256) :=
  if right < left then none
  else if left < right ∧ proof.length < right then none
  else some ((proof.drop left).take (right - left))

/-- `MessageHashing.ProofMetadata` (`:91-96`). -/
structure ProofMetadata where
  proofStartIndex : ℕ
  logLeafProofLen : ℕ
  batchLeafProofLen : ℕ
  finalProofNode : Bool
  deriving DecidableEq

/-- `parseProofMetadata(_proof)` (`:101-143`).  `m * 2^32 mod 2^256` is `uint256(m) << 32`;
`m / 2^248` is the first byte, `m / 2^240 % 256` the second, and so on. -/
def parseProofMetadata (proof : List UInt256) : Option ProofMetadata :=
  match proof[0]? with
  | none => none                                                         -- :102 index panic
  | some m =>
    if m.val * 2 ^ 32 % UInt256.size = 0 then                            -- :118-120 new format
      if m.val / 2 ^ 248 ≠ SUPPORTED_PROOF_METADATA_VERSION then none    -- :123 UnsupportedProofMetadataVersion
      else if m.val / 2 ^ 224 % 256 ≠ 0 ∧ m.val / 2 ^ 232 % 256 ≠ 0 then none   -- :140 InvalidProofLengthForFinalNode
      else some
        { proofStartIndex := 1                                           -- :127
          logLeafProofLen := m.val / 2 ^ 240 % 256                       -- :128
          batchLeafProofLen := m.val / 2 ^ 232 % 256                     -- :129
          finalProofNode := decide (m.val / 2 ^ 224 % 256 ≠ 0) }         -- :130
    else some                                                            -- :131-139 old format
      { proofStartIndex := 0
        logLeafProofLen := proof.length
        batchLeafProofLen := 0
        finalProofNode := true }

/-- `ProofData` (`common/Messaging.sol:332-345`). -/
structure ProofData where
  settlementLayerChainId : UInt256
  settlementLayerBatchNumber : UInt256
  settlementLayerBatchRootMask : UInt256
  batchLeafProofLen : ℕ
  batchSettlementRoot : UInt256
  chainIdLeaf : UInt256
  l1BatchTimestamp : UInt256
  ptr : ℕ
  finalProofNode : Bool
  deriving DecidableEq

/-- `MessageHashing._getProofData` (`:152-236`).  `none` is a revert or a panic. -/
def getProofData (H : Hashes) (chainId batchNumber leafProofMask leaf : UInt256)
    (proof : List UInt256) : Option ProofData :=
  if proof.length = 0 then none                                          -- :159 MerklePathEmpty
  else if leaf = L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH then none             -- :165 HashedLogIsDefault
  else
    (parseProofMetadata proof).bind fun md =>                            -- :169
    let ptr := md.proofStartIndex                                        -- :170
    (extractSlice proof ptr (ptr + md.logLeafProofLen)).bind fun logPath =>      -- :175
    (calculateRootMemory H.node logPath leafProofMask leaf).bind fun batchSettlementRoot =>  -- :174-178
    let ptr := ptr + md.logLeafProofLen                                  -- :179
    if md.finalProofNode then                                            -- :183
      some
        { settlementLayerChainId := 0
          settlementLayerBatchNumber := 0
          settlementLayerBatchRootMask := 0
          batchLeafProofLen := 0
          batchSettlementRoot := batchSettlementRoot                     -- :180
          chainIdLeaf := 0
          l1BatchTimestamp := 0
          ptr := ptr
          finalProofNode := true }                                       -- :181, :184
    else
      proof[ptr]?.bind fun l1BatchTimestamp =>                           -- :188
      proof[ptr + 1]?.bind fun batchLeafProofMask =>                     -- :198
      (extractSlice proof (ptr + 2) (ptr + 2 + md.batchLeafProofLen)).bind fun batchPath =>   -- :202
      (calculateRootMemory H.node batchPath batchLeafProofMask
        (H.batchLeaf batchSettlementRoot batchNumber l1BatchTimestamp)).bind fun chainIdRoot =>  -- :192-205
      proof[ptr + 2 + md.batchLeafProofLen]?.bind fun packedBatchInfo =>         -- :216
      proof[ptr + 3 + md.batchLeafProofLen]?.bind fun settlementLayerChainId =>  -- :221
      some
        { settlementLayerChainId := settlementLayerChainId
          settlementLayerBatchNumber := Nat.toUInt256 (packedBatchInfo.val / 2 ^ 128)      -- :218
          settlementLayerBatchRootMask := Nat.toUInt256 (packedBatchInfo.val % 2 ^ 128)    -- :219
          batchLeafProofLen := md.batchLeafProofLen
          batchSettlementRoot := batchSettlementRoot
          chainIdLeaf := H.chainIdLeaf chainIdRoot chainId               -- :208
          l1BatchTimestamp := l1BatchTimestamp
          ptr := ptr + 4 + md.batchLeafProofLen                          -- :222
          finalProofNode := false }

/-! ## `L2MessageVerification` -/

/-- `_proveL2LeafInclusionRecursive` (`L2MessageVerification.sol:18-56`) reading the roots of
storage `S`, with `fuel` bounding the number of nested self-calls.  `none` is a revert (or, at
`fuel = 0`, the model running out — impossible from the entry points below). -/
def proveRecursive (H : Hashes) (S : State) :
    ℕ → UInt256 → UInt256 → UInt256 → UInt256 → List UInt256 → UInt256 → Option Bool
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, chainId, blockOrBatchNumber, leafProofMask, leaf, proof, depth =>
    match getProofData H chainId blockOrBatchNumber leafProofMask leaf proof with     -- :26
    | none => none
    | some pd =>
      if pd.finalProofNode then                                                       -- :33
        some ((interopRoots S chainId blockOrBatchNumber).root == pd.batchSettlementRoot
          && (interopRoots S chainId blockOrBatchNumber).root != 0)                   -- :37-38
      else if depth = 1 then none                               -- :40 DepthMoreThanOneForRecursiveMerkleProof
      else if UInt256.size ≤ depth.val + 1 then none            -- :54 checked `_depth + 1`
      else
        proveRecursive H S fuel pd.settlementLayerChainId pd.settlementLayerBatchNumber
          pd.settlementLayerBatchRootMask pd.chainIdLeaf (proof.drop pd.ptr) (depth + 1)   -- :46-55

/-- `proveL2LeafInclusionSharedRecursive` (`MessageVerification.sol:52-62`): external, with a
caller-chosen `_depth`. -/
def proveL2LeafInclusionSharedRecursive (H : Hashes) (S : State)
    (chainId blockOrBatchNumber leafProofMask leaf : UInt256) (proof : List UInt256)
    (depth : UInt256) : Option Bool :=
  proveRecursive H S proof.length chainId blockOrBatchNumber leafProofMask leaf proof depth

/-- `proveL2LeafInclusionShared` (`MessageVerification.sol:35-50`, `:64-73`): `_depth = 0`.
The log, message, transaction-status and deposit-parameter entry points are this function at
`leaf := getLeafHashFromLog(log)` and `leafProofMask := _index`. -/
def proveL2LeafInclusionShared (H : Hashes) (S : State)
    (chainId blockOrBatchNumber leafProofMask leaf : UInt256) (proof : List UInt256) : Option Bool :=
  proveL2LeafInclusionSharedRecursive H S chainId blockOrBatchNumber leafProofMask leaf proof 0

/-! ## The anchor: what the terminal step reads -/

/-- The terminal step of a call: the storage key it reads, the root it compares the stored
root with, and how many self-calls were made to get there. -/
structure Anchor where
  /-- First argument of the terminal `interopRoots` read. -/
  chainId : UInt256
  /-- Second argument of the terminal `interopRoots` read. -/
  blockOrBatchNumber : UInt256
  /-- `proofData.batchSettlementRoot` at the terminal step. -/
  computedRoot : UInt256
  /-- Number of nested `this.proveL2LeafInclusionSharedRecursive` calls made. -/
  hops : ℕ
  deriving DecidableEq

/-- `proveRecursive` with the storage read left out: the same parse, the same reverts, the
same recursion, ending with the key and the computed root instead of the comparison.  It does
not take a `State`. -/
def anchorRec (H : Hashes) :
    ℕ → UInt256 → UInt256 → UInt256 → UInt256 → List UInt256 → UInt256 → Option Anchor
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, chainId, blockOrBatchNumber, leafProofMask, leaf, proof, depth =>
    match getProofData H chainId blockOrBatchNumber leafProofMask leaf proof with
    | none => none
    | some pd =>
      if pd.finalProofNode then some ⟨chainId, blockOrBatchNumber, pd.batchSettlementRoot, 0⟩
      else if depth = 1 then none
      else if UInt256.size ≤ depth.val + 1 then none
      else
        (anchorRec H fuel pd.settlementLayerChainId pd.settlementLayerBatchNumber
          pd.settlementLayerBatchRootMask pd.chainIdLeaf (proof.drop pd.ptr) (depth + 1)).map
          fun a => { a with hops := a.hops + 1 }

/-- The anchor of an external call with the caller's `_depth`. -/
def anchor (H : Hashes) (chainId blockOrBatchNumber leafProofMask leaf : UInt256)
    (proof : List UInt256) (depth : UInt256) : Option Anchor :=
  anchorRec H proof.length chainId blockOrBatchNumber leafProofMask leaf proof depth

/-- The terminal comparison (`L2MessageVerification.sol:37-38`) for an anchor, in storage `S`. -/
def anchorHolds (S : State) (a : Anchor) : Bool :=
  (interopRoots S a.chainId a.blockOrBatchNumber).root == a.computedRoot
    && (interopRoots S a.chainId a.blockOrBatchNumber).root != 0

/-! ## Mutant (for a countermodel only) -/

/-- The terminal comparison with the `correctBatchRoot != bytes32(0)` conjunct (`:38`) deleted. -/
def anchorHoldsNoZeroCheck (S : State) (a : Anchor) : Bool :=
  (interopRoots S a.chainId a.blockOrBatchNumber).root == a.computedRoot

end Contracts.InteropRootStorage
