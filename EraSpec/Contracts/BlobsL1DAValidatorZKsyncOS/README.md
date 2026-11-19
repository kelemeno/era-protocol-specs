# BlobsL1DAValidatorZKsyncOS

The L1 DA validator of ZKsync OS chains under the `BLOBS_ZKSYNC_OS` scheme,
`BlobsL1DAValidatorZKsyncOS`, at era-contracts `draft/v0.35.0` `b17415d20`.

## Headline guarantees

The folder's real guarantees about `b17415d20`, each with every premise. They are meant to carry
`@[headline]` (the lists after the table: `@[witness]`, `@[countermodel]`) once the tag attributes
of `EraSpec.Core.Headline` are on this branch; they are not tagged yet.
"Reachable" means reached from a fresh deployment by `publishBlobs` calls and block advances. The
transaction's `blobhash` values and keccak are arbitrary; no statement takes a hash premise.

| Guarantee | Premises | Statement |
|---|---|---|
| `publishBlobs` sets `publishedBlobs[v]` to the current block for exactly the transaction's attached hashes, and changes nothing else | None | `BlobsPublishWritesExactlyAttached` |
| `checkDA` returns iff the input is whole 32-byte entries, every nonzero entry is available, the transaction's blob hashes `0 … z - 1` are nonzero and hash `z` is zero (`z` the number of zero entries), and keccak of the resolved hashes is the commitment; the output is always empty | None (any `blobhash`) | `BlobsCheckDAAcceptsIff` |
| On a transaction with nonzero versioned hashes, `checkDA` accepts iff some resolved list keeps every nonzero entry and fills the zero entries with exactly the attached blobs, in order | The transaction's versioned hashes are nonzero (as on Ethereum) | `BlobsCheckDAAcceptsIffWellFormed` |
| An accepted input uses every attached blob, in order | The transaction's versioned hashes are nonzero | `BlobsAcceptedUsesEveryAttachedBlob` |
| A hash is available iff a logged `publishBlobs` call wrote it at a nonzero block at most `BLOB_EXPIRATION_BLOCKS` ago | Reachable state | `BlobsAvailableIffLoggedInWindow` |
| Every resolved hash of an accepted input is a blob of the checking transaction or was published in the window | Reachable state | `BlobsAcceptedHashesFresh` |
| An input accepted for the commitment `keccak(vs)` resolves to `vs`, or keccak collides on the two named concatenations | None | `BlobsAcceptedBindsOrCollision` |

Witnesses: `BlobsAcceptanceWitness`, `BlobsBindingWitness`,
`BlobsTwoInputsOneListWitness`. Countermodels:
`BlobsExtraBlobCheckLoadBearing`, `BlobsWindowCheckLoadBearing`. The other statements are
supporting lemmas.

## Source

`l1-contracts/contracts/state-transition/data-availability/BlobsL1DAValidatorZKsyncOS.sol`
and `DAConstants.sol:28,31` at era-contracts `draft/v0.35.0` commit **`b17415d20`**; every
`file:line` is at that commit.

This is the L1 DA validator of ZKsync OS chains under the `BLOBS_ZKSYNC_OS` scheme. For such a chain
the committer discards the validator's output (see `../../Protocol/ZKsyncOSDA/`), so what `checkDA`
enforces is the whole on-L1 DA check.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the guarantees and
their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact named propositions,
plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |

Namespace: `Contracts.ZKsyncOSBlobsDA`. Statements are `Contracts.ZKsyncOSBlobsDA.Properties.*`; each
certificate has the same name without the `Properties` segment.

## What to check

**Writes.** `publishBlobs()` has no caller check and no argument. It sets `publishedBlobs[v]` to the
current block for exactly the transaction's blob hashes before the first zero one, and changes
nothing else (`BlobsPublishWritesExactlyAttached`); for an EIP-4844 transaction that is every blob
(`BlobsAttachedIsAllBlobs`). It is the contract's only state change.

**Exact acceptance.** `checkDA` returns iff the input is a whole number of 32-byte entries, every
nonzero entry is available, the transaction's blob hashes `0 … z - 1` are nonzero and hash `z` is
zero for `z` the number of zero entries, and keccak of the resolved hashes is the commitment
(`BlobsCheckDAAcceptsIff`). For a transaction with nonzero versioned hashes this says: there is a
resolved list that keeps every nonzero entry and fills the zero entries with exactly the attached
blobs, in order (`BlobsCheckDAAcceptsIffWellFormed`); every attached blob is used
(`BlobsAcceptedUsesEveryAttachedBlob`). The output is always `(0, [], [])`.

**Freshness, along runs** of `publishBlobs` calls and block advances from a fresh deployment, with a
ghost log of the calls: `isBlobAvailable` never panics (`BlobsAvailabilityNeverPanics`); a hash is
available iff a logged call wrote it at a nonzero block at most `BLOB_EXPIRATION_BLOCKS` before the
current one (`BlobsAvailableIffLoggedInWindow`); so every resolved hash of an accepted input is a
blob of the checking transaction or was written in the window (`BlobsAcceptedHashesFresh`).

**Pinned binding.** An accepted input resolves to the list the commitment hashes, or keccak collides
on the two named concatenations (`BlobsAcceptedBindsOrCollision`,
`BlobsTwoAcceptancesAgreeOrCollision`); concatenating words is injective (`BlobsEncWordsInjective`).
No hash premise is taken.

**Countermodels.** Deleting the extra-blob check (`:83-88`) accepts an input that leaves an attached
blob unused (`BlobsExtraBlobCheckLoadBearing`). Deleting the window conjunct (`:39`) accepts a hash
last written more than `BLOB_EXPIRATION_BLOCKS` ago (`BlobsWindowCheckLoadBearing`).

**Witnesses.** `BlobsAcceptanceWitness` (a reachable world, an input with one published entry and one
zero entry, a transaction with one blob, every keccak), `BlobsBindingWitness` (the collision false on
an accepted instance, and firing under the constant hash), `BlobsTwoInputsOneListWitness` (two
different inputs, one resolved list).

## Not modelled

* That the resolved hashes are those of the blobs carrying the batch's pubdata: that is what the
  ZKsync OS program commits to under `BLOBS_ZKSYNC_OS`, off-chain (ASSUMPTIONS.md `PROTO-PROG-DA`).
* Blob contents, and whether a blob is retrievable during its window: `checkDA` sees only versioned
  hashes.
* `BLOBHASH` semantics and storage correspondence (`MODEL-ZKSYNCOS-BLOBS-DA`).
