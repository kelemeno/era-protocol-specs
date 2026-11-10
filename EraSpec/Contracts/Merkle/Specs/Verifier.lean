import EraSpec.Contracts.FullMerkle.Specs.Model

/-!
# The verifier's walk at EVERY index and EVERY path length

`EraSpec.Contracts.Merkle.Proofs.ProofSound` proves that an accepted Merkle path pins the leaf
it opens — for an index inside the occupied range, and for a path exactly as long
as the tree is high.  The on-chain verifier (`Merkle.calculateRootMemory`) checks
neither of those things: it accepts any index below `2^pathLength` and any path
length below 256, because it is a pure function of a 32-byte root and has no way
to know how many leaves the tree holds or how high it is.  So the two hypotheses
that file carries are exactly the two degrees of freedom an attacker keeps, and
a soundness statement that assumes them says nothing about the verifier as
deployed.

This file removes both.

## Padded indices

`FullMerkle` fills the positions between `_leafNumber` and `2^_height` with the
zero cascade: the level-0 slot reads `_zeros[0]`, the level-`l` node above only
empty slots reads `_zeros[l]`.  `levelUp_getD_all` is the observation that makes
this uniform: when the `getD` default is the level's own zero, the parent-child
equation `node[l+1][m] = h node[l][2m] node[l][2m+1]` holds at EVERY index, not
just the occupied ones.  With that, the pinning induction needs no range
hypothesis (`walk_pins`), and the root form (`accept_pins_entry`) says an
accepted walk at index `j < 2^k` pins `L.getD j z0` — the real leaf hash if
`j` is occupied, the padding constant `z0` if it is not.

That second case is not a technicality.  `padded_slot_verifies` shows the
honest sibling stream for an EMPTY slot is accepted by the verifier with the
padding constant as its "leaf hash".  Whether that is an attack depends on
whether `z0` collides with a leaf hash — which is precisely what
`EraSpec.Contracts.L2InteropCommitmentTree.Specs.TreeRoot` settles for the indexed Merkle tree.

## Wrong path lengths

A path shorter than the tree's height, if accepted, presents an INTERIOR node as
the leaf: `accept_forces_height`'s first case re-anchors the walk at level
`height - k` and finds the claimed leaf hash is `h _ _`.  A path longer than the
height, if accepted, must pass through a level-0 entry with a nontrivial walk
still below it: `walkPure_add` splits the walk, and the level-0 entry — a leaf
hash or the padding constant — is again forced to be `h _ _`.  So under the
domain-separation hypotheses "no leaf hash is a node hash" and "the padding
constant is not a node hash" (both true of `keccak` on 96-byte leaf encodings
versus 64-byte node pairs, which is what the `hashLeaf` source comment about
64-byte preimages is protecting), the accepted path length IS the tree height.

Everything here is pure list arithmetic over `MerkleSpec`; node-hash
pair-injectivity is a hypothesis where used, as throughout the corpus.

Ported from the `claude/proof-attempt-4f3778` line, where it was the Core module
`EraSpec/Core/MerkleVerifier.lean`. It models `Merkle.calculateRootMemory`, so it
lives with the `Merkle` library here. Results: `../Properties/Verifier.lean`.
-/

namespace MerkleSpec.Verifier

open Clear MerkleSpec

/-- The sibling stream `FullMerkle.merklePath(j)` returns: at each level the
entry next to the path, or that level's zero at the frontier. -/
def honestSibs (h : Hash) (z0 : UInt256) (L : List UInt256) (j : ℕ) : ℕ → UInt256 :=
  fun l => (levels h z0 L l).getD (sibIdx (j / 2 ^ l)) (zeros h z0 l)

end MerkleSpec.Verifier
