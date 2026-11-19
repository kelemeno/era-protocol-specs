# L2MessageVerification

## Headline guarantees

All about `l1-contracts/contracts/interop/L2MessageVerification.sol` with
`common/MessageVerification.sol`, `MessageHashing.sol` and `Merkle.sol` at era-contracts
`draft/v0.35.0` head `b17415d20`. The three hashes are arbitrary functions; no statement assumes
injectivity. The storage read is the canonical model of `../L2InteropRootStorage/`.

- `Contracts.MessageVerification.Properties.AcceptedIffStoredRootAtAnchor`: for any storage, a
  proof is accepted exactly when the storage-free computation names a key and a recomputed root,
  and the root stored at that key is that root and nonzero.
- `Contracts.MessageVerification.Properties.SharedEntryAcceptsIff`: the depth-0 entry that
  `AtomicInteropProof._authenticateRoot` calls accepts exactly a direct proof against the root at
  its own key, or a proof with one self-call against the root at the settlement-layer key the proof
  names.
- `Contracts.MessageVerification.Properties.AcceptanceSurvivesRuns`: along any run of the storage
  contract, an accepted proof stays accepted.
- `Contracts.MessageVerification.Properties.AcceptedFromFreshStorageWasImported`: for storage
  reached from fresh storage by a logged run, every accepted proof names a key that a logged
  bootloader call imported with exactly the recomputed root.
- `Contracts.MessageVerification.Properties.AcceptedAnchorHasNonzeroTimestamp`: for storage reached
  from fresh storage, the key an accepted proof names has a nonzero stored timestamp.

## Topics

Source: `contracts/interop/L2MessageVerification.sol`, with `common/MessageVerification.sol`,
`common/libraries/MessageHashing.sol` and `common/libraries/Merkle.sol`, at era-contracts
`draft/v0.35.0` head `b17415d20` (other commits are compared in the Specs header). The roots it
reads are those of [`../L2InteropRootStorage/`](../L2InteropRootStorage/README.md).

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Verification | [Specs/Verification.lean](Specs/Verification.lean) | [Properties/Verification.lean](Properties/Verification.lean) | [Proofs/Verification.lean](Proofs/Verification.lean) |

Namespace `Contracts.MessageVerification`. Statements are
`Contracts.MessageVerification.Properties.*`; each certificate has the same name without the
`Properties` segment. The three hashes (`Merkle.efficientHash`, `batchLeafHash`,
`chainIdLeafHash`) are uninterpreted parameters, and no result assumes injectivity of any of them.

- **One storage read.** The verdict is a computation that takes no storage (`anchorRec`: the
  metadata parse, both Merkle walks, every bounds-checked read, the recursion and its reverts)
  followed by one comparison against `interopRoots(key).root` at the key it names
  (`ProveIsOneStorageRead`). So whether a call reverts does not depend on the storage
  (`RevertIsStorageIndependent`), and a call is accepted exactly when the root stored at that key
  is the recomputed root and nonzero (`AcceptedIffStoredRootAtAnchor`). The fuel bounding the
  recursion is never reached from the entry points (`FuelIrrelevant`).
- **What the depth-0 entry accepts.** `proveL2LeafInclusionShared`, which
  `AtomicInteropProof._authenticateRoot` calls, accepts exactly a direct proof (a final step whose
  recomputed root is the nonzero root stored at the call's own key) or a proof with one self-call
  (a non-final step, then a final step on the rest of the proof whose recomputed root is the
  nonzero root stored at the settlement-layer key the first step read from the proof)
  (`SharedEntryAcceptsIff`, `SharedEntryAnchorIff`). At `_depth = 1` only the direct form is
  accepted (`DepthOneAnchorIff`). For a proof with one self-call, the settlement-layer block and
  chain that `readSettlementLayerReference` reads afterwards are that key
  (`SettlementLayerReferenceIsTheAnchorKey`), and the compared root is a walk of
  `chainIdLeaf(·, chainId)` of a walk of `batchLeaf(·, blockOrBatchNumber, ts)` of a walk of the
  call's leaf, with `ts` the timestamp read there (`SharedEntryRootShape`; the paths and masks are
  the prover's).
- **The walk.** `calculateRootMemory` is `MerkleSpec.walkPure` of `../FullMerkle/Specs/Model.lean`
  with the path as its sibling stream, under its two range checks
  (`CalculateRootMemoryIsMerkleSpecWalk`), so the `Merkle` folder's results stated for
  `walkPure` can be applied to the walks here, under their own premises. Nothing here says an
  accepted walk opens a tree.
- **Against the storage's runs.** An accepted proof stays accepted (`AcceptanceSurvivesRuns`). A
  proof that becomes accepted along a logged run was accepted at its start or names a key the
  run's log imported with exactly the recomputed root
  (`AcceptedAfterRunWasAcceptedOrImported`). From fresh storage, every accepted proof names a key
  that a logged bootloader call imported with `sides = [recomputed root]`
  (`AcceptedFromFreshStorageWasImported`), and that key's stored timestamp is nonzero
  (`AcceptedAnchorHasNonzeroTimestamp`).
- **The zero check is load-bearing.** With `correctBatchRoot != bytes32(0)` deleted, for every
  hash, the one-word final-node proof of the zero leaf is accepted at every key holding no root;
  the contract rejects it there (`WithoutNonzeroCheckUnimportedKeyAccepts`).

Witnesses: `HonestOneHopProofAccepted` (for every hash meeting three pinned inequalities on the
example's own values: the one-self-call example proof is rejected on fresh storage, not reverted,
and accepted once its recomputed root is stored at the key it names) and `OneHopProofWitness`
(one concrete hash, along a logged run of the storage contract from fresh storage).

Model boundaries (`MODEL-MESSAGE-VERIFICATION` in `ASSUMPTIONS.md`): the log-shaped entry points
are covered through `proveL2LeafInclusionShared`, with their leaf (`getLeafHashFromLog`, a
`SOL-ABI` matter) a parameter. The external self-call is a direct recursive call whose revert
propagates (`SOL-CONTROL`); gas is not modelled. That `L2_INTEROP_ROOT_STORAGE` is the storage
contract of `../L2InteropRootStorage/` is `BUILD-IDENTITY`. Consumers, `AtomicInteropProof` among
them, are not modelled; the results that cite them say what they read, not what they then do.
