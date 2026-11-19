import EraSpec.Contracts.L2InteropCommitmentTree.Specs.CachedRoot

/-!
# History: the padding forgery at the interop pin `c67894b9`

**This is the record of an older commit, not a claim about `b17415d20`.**  At era-contracts
`c67894b9`, `IndexedMerkleTree.setup` passed `hashLeaf({0,0,0})` both to `FullMerkle.setup` (the
padding of every empty slot) and to `pushNewLeaf` (the sentinel), so an empty slot verified as the
zero leaf `{0,0,0}`, whose window straddles every value (finding H2, fixed upstream by `78e14b3bc`,
audit item F-04).  At `b17415d20` `setup` pads with `IMT_EMPTY_LEAF_HASH`
(`common/libraries/IndexedMerkleTree.sol:51`, `common/Config.sol:141`).

The models used here are the canonical ones: `TreeRoot.root` with the padding parameter `z0`,
`RunHeight`'s `HState`, and `CachedRoot`'s storage with `cSetup`, the instance of `cSetupPad` at
`ze = hashLeaf({0,0,0})` (`Properties.PinSetupIsPadAtZeroLeafHash`).  The statements in
`EraSpec.Contracts.L2InteropCommitmentTree.History.Properties.PaddingForgeryPinned` instantiate
the padding with the pin's `hashLeaf({0,0,0})` and show the forgery is accepted.  At `b17415d20`
the same proof is accepted only on a keccak collision
(`Properties.PinForgeryAtHeadNeedsKeccakCollision`, `Properties.PaddingForgeryAtV35Witness` for
the canonical machine at the pin's constant).

No new definitions.
-/

namespace Contracts.InteropCommitmentTree.History

end Contracts.InteropCommitmentTree.History
