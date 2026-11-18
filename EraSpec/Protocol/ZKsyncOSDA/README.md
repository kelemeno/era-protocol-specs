# ZKsync OS data availability: each validator composed with the committer

Source: era-contracts `draft/v0.35.0` commit **`b17415d20`**: `CommitterFacet._commitOneBatch`
(`state-transition/chain-deps/facets/Committer.sol:179-210`), the DA validators under
`state-transition/data-availability/`, `Admin.setDAValidatorPair` (`Admin.sol:387-401`) and
`RollupDAManager` (`RollupDAManager.sol:58-78`). Main at `70096e2ea` has the same check on its ZKsync OS path
(`Committer.sol:433-464` there); the results are stated at `b17415d20` only.

On ZKsync OS the committer calls the chain's validator with `_maxBlobsSupported = 16` and then only
requires the returned arrays to be empty or all zeros. So the on-L1 DA guarantee of a ZKsync OS batch
is exactly what the validator's `checkDA` enforces. This topic characterises, per validator, the
inputs that pass both, and the publication evidence an acceptance implies.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| CommitterDA | [Specs/CommitterDA.lean](Specs/CommitterDA.lean), [Specs/Validators.lean](Specs/Validators.lean) | [Properties/CommitterDA.lean](Properties/CommitterDA.lean) | [Proofs/CommitterDA.lean](Proofs/CommitterDA.lean), [Proofs/Bytes.lean](Proofs/Bytes.lean) |

Namespace: `Contracts.ZKsyncOSCommitterDA`. Statements are
`Contracts.ZKsyncOSCommitterDA.Properties.*`; each certificate has the same name without the
`Properties` segment. `Specs/Validators.lean` transcribes `RollupL1DAValidator`,
`RelayedSLDAValidator`, `ValidiumL1DAValidator` and their `CalldataDA` helpers, adapted from an
earlier draft DA model and re-checked line by line against `b17415d20`; the ZKsync OS blobs validator is
`../../Contracts/BlobsL1DAValidatorZKsyncOS/`.

## What to check

**The committer's check** passes exactly when both arrays are empty or both are sixteen zeros
(`CommitterDACheckIff`).

**Per validator** (`…Accepted` = the validator returns and the committer's check passes):

- `RollupL1DAValidator`: accepted inputs have one of two shapes, or keccak maps a named input (the
  first blob record's commitment preimage) to zero (`RollupAcceptedCases`); both shapes are accepted
  in every state (`RollupFormsAccepted`); exact when that input is not mapped to zero
  (`RollupAcceptedIff`). The **zero-blob shape**: blob count 0, the blob source byte and nothing
  after it, no blob attached; the full pubdata hash is compared with nothing. The **calldata
  shape**: blob count 1, a zero linear hash, then the pubdata and a zero commitment; the pubdata's
  keccak must be the full pubdata hash.
- `RelayedSLDAValidator`: exactly the gateway shape, which relays the pubdata to L1 with keccak equal
  to the full pubdata hash (`RelayedAcceptedIff`).
- `ValidiumL1DAValidator`: exactly the 32-byte inputs, whatever the commitment
  (`ValidiumAcceptedIff`).
- `BlobsL1DAValidatorZKsyncOS`: exactly its own `checkDA` (`BlobsAcceptedIffCheckDA`).

**Headlines.** Let the commitment be the program's, `keccak (l2Output sd (keccak pub) lin)` for the
batch's pubdata `pub` (the layout `CalldataDA.sol:44-48` documents).

- `RollupPubdataPublishedOrCollision`: with the premise `pub ≠ [] → lin ≠ []` (the program never
  commits zero blobs for nonempty pubdata), an input the rollup validator and the committer accept
  carries `pub` in the commit calldata, or `pub` is empty, or keccak collides on two named inputs, or
  maps the named first-blob preimage to zero.
- `RollupProgramPremiseLoadBearing`, `RollupZeroBlobAcceptsUnpublishedPubdata`: without the premise
  the headline is false; a zero-blob commitment to nonempty pubdata is accepted from a 66-byte input
  with no blob attached, for every keccak.
- `CommitterZeroCheckLoadBearing`: without the committer's all-zero check the headline is false too,
  for a commitment with a nonzero linear hash, through the blob branch.
- `RelayedPubdataRelayedOrCollision`: the gateway validator needs no program premise.
- `BlobsCommittedHashesFreshOrCollision`: under the blobs validator, every committed versioned hash
  was attached to the commit transaction or published within the window, or a named collision.

**Witnesses.** `RollupHeadlineWitness`, `RollupHeadlineCollisionFires`, `RollupFormsWitness`,
`RelayedHeadlineWitness`, `RelayedCollisionFires`, `BlobsHeadlineWitness`; each docstring in
`Proofs/CommitterDA.lean` names its instance.

## Not modelled

- What the ZKsync OS program computes as `daCommitment` for each scheme (ASSUMPTIONS.md
  `PROTO-PROG-DA`). On the calldata branch the accepted prefix always has one blob and a zero linear
  hash, so `lin = [0]` is the one-blob commitment that can match it without a collision; the
  witnesses use it.
- Which validator and scheme a chain is configured with. `setDAValidatorPair` checks no compatibility
  between the two; for a permanent rollup only `RollupDAManager`-allowed pairs can be set.
- The other checks of `_commitOneBatch` (they only add conditions), proving and execution.
- The point-evaluation precompile (an oracle), the L2 bridgehub lookup, and the L2→L1 messenger
  (its effect is the returned message).
