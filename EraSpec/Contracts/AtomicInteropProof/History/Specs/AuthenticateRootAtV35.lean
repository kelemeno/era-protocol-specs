import EraSpec.Contracts.AtomicInteropProof.Specs.AuthenticateRootAtV35

/-!
# Spec (History): `_authenticateRoot` and `readAggregationHopPath` at the extraction pin

**History.** This is the record of `_authenticateRoot` at era-contracts `c67894b9`, not a claim about
`draft/v0.35.0` `b17415d20`. Line numbers marked `@c67894b9` are as earlier rounds recorded them
(`c67894b9` is not in the local era-contracts clone and was not re-checked). At the pin
`_authenticateRoot` obtained the settlement-layer metadata by running `MessageHashing._getProofData`
a second time on the verified proof and rejected a final node on that result, and
`readAggregationHopPath` had no final-node check. At `b17415d20` both are as transcribed in
`../../Specs/AuthenticateRootAtV35.lean` (`authenticateRootV35`, `readHop`).

The two pin-vs-v35 statements over these definitions are in `../Properties/AuthenticateRootAtV35.lean`.
-/

namespace AttackVectors.AuthenticateRootAtV35.History

open MerkleSpec MerkleSpec.Verifier

/-- The pin's `readAggregationHopPath` (`MessageHashing.sol:258-265@c67894b9`): the same reads,
without the final-node check. -/
def readHopPin (E : Env) (w : Proof) : Option HopPath :=
  (E.parse w).bind fun md =>
  (word w (md.proofStartIndex + md.logLeafProofLen + 1)).bind fun mask =>
  (slice w (md.proofStartIndex + md.logLeafProofLen + 2)
      (md.proofStartIndex + md.logLeafProofLen + 2 + md.batchLeafProofLen)).bind fun sibs =>
  some ⟨mask, sibs⟩

/-- **`_authenticateRoot` at the pin** (`AtomicInteropProof.sol:256-290@c67894b9`). It is the same
up to the verifier (`:260-272@c67894b9`), then re-runs `_getProofData` with the same arguments
(`:276-282@c67894b9`) and rejects a final node on the result (`:285@c67894b9`). -/
def authenticateRootPin (E : Env) (roots : UInt256 → UInt256 → UInt256)
    (src batch leafIndex imtRoot : UInt256) (w : Proof) : Option SLRef :=
  (E.parse w).bind fun md =>
  if md.logLeafProofLen ≠ treeDepth then none else
  (proveShared E roots src batch leafIndex imtRoot w).bind fun ok =>
  if ok = false then none else
  (getProofData E src batch leafIndex imtRoot w).bind fun pd =>
  if pd.finalProofNode then none else
  some ⟨pd.slBatchNumber, pd.slChainId, pd.l1BatchTimestamp⟩

/-- The same at the pin (`AtomicInteropProof.sol:152-206@c67894b9`): the pin's `_authenticateRoot`
and the pin's `readAggregationHopPath`. -/
structure EndBranchPassesPin (E : Env) (roots : UInt256 → UInt256 → UInt256) (z0 : UInt256)
    (src batch imtRoot : UInt256) (w : Proof) (sl : SLRef) (hop : HopPath) : Prop where
  auth : authenticateRootPin E roots src batch imtEndLeafIndex imtRoot w = some sl
  hop_eq : readHopPin E w = some hop
  last : LastBatchCheck E.node z0 hop

end AttackVectors.AuthenticateRootAtV35.History
