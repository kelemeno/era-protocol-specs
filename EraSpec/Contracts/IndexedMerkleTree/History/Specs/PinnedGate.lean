import EraSpec.Contracts.IndexedMerkleTree.Specs.ReclaimGateFaithful

/-!
# History: the deployed reclaim gate at the interop pin `c67894b9`

**This is the record of an older commit, not a claim about `b17415d20`.**  At era-contracts
`c67894b9`, `IndexedMerkleTree.setup` padded every empty slot with `hashLeaf({0,0,0})`, the hash
of the sentinel leaf (finding H2, fixed upstream by `78e14b3bc`, audit item F-04).  At
`b17415d20` the padding is `IMT_EMPTY_LEAF_HASH` (`common/libraries/IndexedMerkleTree.sol:51`,
`common/Config.sol:141`).

The model is the canonical one of `../../Specs/ReclaimGateFaithful.lean` (`DeployedGate`, the two
capstone readings, `HState` runs from `setup`, `CReachesPad`) at the padding constant
`hl ⟨0, 0, 0⟩`.  The statements in
`EraSpec.Contracts.IndexedMerkleTree.History.Properties.PinnedGate` show that at that padding the
deployed check accepts a reclaim for every nonzero value on most reached snapshots, so both
capstone readings fail.  At every padding constant, the canonical
`Properties.DeliveredRefundLocatesCollisionOrPaddingHit` and `Properties.BreakFreeGateDichotomy`
state what does hold.

No new definitions.
-/

namespace IMTAbstract.ReclaimGateFaithful.History

end IMTAbstract.ReclaimGateFaithful.History
