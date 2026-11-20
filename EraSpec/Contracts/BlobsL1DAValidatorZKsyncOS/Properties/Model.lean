import EraSpec.Contracts.BlobsL1DAValidatorZKsyncOS.Specs.Model
import EraSpec.Core.Headline

/-!
# Properties: what `BlobsL1DAValidatorZKsyncOS` accepts, and what an acceptance implies

Statements about `../Specs/Model.lean` (source `b17415d20`). Proofs: `../Proofs/Model.lean`.
No statement takes a hash premise.

* **Writes.** `publishBlobs` sets `publishedBlobs[v]` to the current block for exactly the attached
  hashes before the first zero one, and changes nothing else (`BlobsPublishWritesExactlyAttached`).
  On Ethereum that is every attached blob (`BlobsAttachedIsAllBlobs`). It is the contract's only
  writer (the step relation `WStep`).
* **Exact acceptance.** `BlobsCheckDAAcceptsIff` characterises `checkDA` for any `blobhash`;
  `BlobsCheckDAAcceptsIffWellFormed` restates it for a transaction with nonzero versioned hashes as
  "there is a resolved list `vs`" with the zero entries filled by exactly the attached blobs, in
  order. In particular every attached blob is used (`BlobsAcceptedUsesEveryAttachedBlob`).
* **Freshness.** On reachable states `isBlobAvailable` never panics
  (`BlobsAvailabilityNeverPanics`), a hash is available iff a logged `publishBlobs` call wrote it at
  a nonzero block in the window (`BlobsAvailableIffLoggedInWindow`), and every hash an accepted
  input resolves to was attached to the checking transaction or written in the window
  (`BlobsAcceptedHashesFresh`).
* **Pinned binding.** The concatenation of resolved hashes is injective (`BlobsEncWordsInjective`).
  An accepted input resolves to the list `h` commits to, or keccak collides on the two named
  concatenations (`BlobsAcceptedBindsOrCollision`, `BlobsTwoAcceptancesAgreeOrCollision`).
* **Countermodels.** Without the extra-blob check an attached blob can go unused
  (`BlobsExtraBlobCheckLoadBearing`); without the window conjunct an expired hash is accepted
  (`BlobsWindowCheckLoadBearing`).
* **Witnesses.** `BlobsAcceptanceWitness` meets the premises of the acceptance, freshness and
  availability results on a reachable world with both kinds of entry; `BlobsBindingWitness` meets
  the binding results with the collision false, and shows the collision firing under a constant
  hash; `BlobsTwoInputsOneListWitness` gives two different accepted inputs for one commitment.

What these results do not say: that the blob contents are the batch's pubdata. `checkDA` sees only
versioned hashes. That the hashes `h` commits to are those of the blobs carrying the batch's
pubdata is the ZKsync OS program's obligation (scheme `BLOBS_ZKSYNC_OS`), not modelled here.
-/

namespace Contracts.ZKsyncOSBlobsDA

open AttackVectors.BundleHashEncoding

/-! ## Writes -/

/-- **`publishBlobs` WRITES EXACTLY THE ATTACHED HASHES, AT THE CURRENT BLOCK.** After the call,
`publishedBlobs[v]` is the current block for every hash in `attached env` and is unchanged for every
other hash. The block number is unchanged. -/
@[headline] def Properties.BlobsPublishWritesExactlyAttached : Prop :=
  ∀ (env : TxEnv) (S : VState) (v : UInt256),
    (publishBlobs env S).published v = (if v ∈ attached env then S.block else S.published v)
      ∧ (publishBlobs env S).block = S.block

/-- **ON ETHEREUM EVERY ATTACHED BLOB IS WRITTEN.** For a transaction whose versioned hashes are all
nonzero, `attached env` is the whole list. -/
def Properties.BlobsAttachedIsAllBlobs : Prop :=
  ∀ env : TxEnv, env.WellFormed → attached env = env.blobs

/-! ## Exact acceptance -/

/-- **EXACT ACCEPTANCE, ANY `blobhash`.** `checkDA` returns `out` iff

* the input is a whole number of 32-byte entries;
* every nonzero entry is `Available` in the current state;
* the transaction's blob hashes `0 … z - 1` are nonzero and hash `z` is zero, where `z` is the number
  of zero entries;
* keccak of the resolved hashes (`resolvedHashes`), concatenated, is `h`;
* and `out` is the empty output. -/
@[headline] def Properties.BlobsCheckDAAcceptsIff : Prop :=
  ∀ (K : Bytes → UInt256) (env : TxEnv) (S : VState) (h : UInt256) (input : Bytes)
    (out : DAOutput),
    checkDA K env S h input = some out ↔
      input.length % 32 = 0
        ∧ (∀ w ∈ inputWords input, w ≠ 0 → Available S w)
        ∧ (∀ j < zeroCount (inputWords input), env.blobhash j ≠ 0)
        ∧ env.blobhash (zeroCount (inputWords input)) = 0
        ∧ K (encWords (resolvedHashes env input)) = h
        ∧ out = DAOutput.empty

/-- **EXACT ACCEPTANCE ON ETHEREUM.** For a transaction whose blob versioned hashes are nonzero,
`checkDA` returns `out` iff the input is a whole number of 32-byte entries and there is a list `vs`,
one hash per entry, such that

* at every nonzero entry `vs` holds that entry, and the entry is `Available`;
* the entries of `vs` at the zero entries are exactly the transaction's blobs, in order (so there
  are as many zero entries as attached blobs);
* keccak of `vs`, concatenated, is `h`;

and `out` is the empty output. -/
@[headline] def Properties.BlobsCheckDAAcceptsIffWellFormed : Prop :=
  ∀ (K : Bytes → UInt256) (env : TxEnv) (S : VState) (h : UInt256) (input : Bytes)
    (out : DAOutput),
    env.WellFormed →
    (checkDA K env S h input = some out ↔
      input.length % 32 = 0
        ∧ ∃ vs : List UInt256, vs.length = (inputWords input).length
          ∧ (∀ i < vs.length, (inputWords input).getD i 0 ≠ 0 →
              vs.getD i 0 = (inputWords input).getD i 0
                ∧ Available S ((inputWords input).getD i 0))
          ∧ atZeroEntries (inputWords input) vs = env.blobs
          ∧ K (encWords vs) = h
          ∧ out = DAOutput.empty)

/-- **EVERY ATTACHED BLOB IS USED, IN ORDER.** For a transaction with nonzero versioned hashes, an
accepted input has exactly as many zero entries as the transaction has blobs, and its resolved
hashes at those entries are the transaction's blobs in order. -/
@[headline] def Properties.BlobsAcceptedUsesEveryAttachedBlob : Prop :=
  ∀ (K : Bytes → UInt256) (env : TxEnv) (S : VState) (h : UInt256) (input : Bytes)
    (out : DAOutput),
    env.WellFormed → checkDA K env S h input = some out →
      zeroCount (inputWords input) = env.blobs.length
        ∧ atZeroEntries (inputWords input) (resolvedHashes env input) = env.blobs

/-! ## Freshness along runs -/

/-- **`isBlobAvailable` DOES NOT PANIC ON A REACHABLE STATE**: no recorded block is in the future. -/
def Properties.BlobsAvailabilityNeverPanics : Prop :=
  ∀ (W : World) (v : UInt256), W.Reachable → isBlobAvailable W.st v ≠ none

/-- **AVAILABLE IFF WRITTEN IN THE WINDOW.** On a reachable state a hash is `Available` iff a logged
`publishBlobs` call wrote it at a nonzero block between `block - BLOB_EXPIRATION_BLOCKS` and the
current block. -/
@[headline] def Properties.BlobsAvailableIffLoggedInWindow : Prop :=
  ∀ (W : World) (v : UInt256), W.Reachable → (Available W.st v ↔ LoggedInWindow W v)

/-- **FRESHNESS OF AN ACCEPTED INPUT.** On a reachable state, for an accepted input:

* at a nonzero entry the resolved hash is the entry, and a logged `publishBlobs` call wrote it in
  the window;
* at a zero entry the resolved hash is a nonzero blob of the checking transaction. -/
@[headline] def Properties.BlobsAcceptedHashesFresh : Prop :=
  ∀ (K : Bytes → UInt256) (env : TxEnv) (W : World) (h : UInt256) (input : Bytes)
    (out : DAOutput),
    W.Reachable → checkDA K env W.st h input = some out →
      ∀ i < (inputWords input).length,
        ((inputWords input).getD i 0 ≠ 0 →
            (resolvedHashes env input).getD i 0 = (inputWords input).getD i 0
              ∧ LoggedInWindow W ((inputWords input).getD i 0))
        ∧ ((inputWords input).getD i 0 = 0 →
            (resolvedHashes env input).getD i 0 ∈ env.blobs
              ∧ (resolvedHashes env input).getD i 0 ≠ 0)

/-! ## Pinned binding -/

/-- **CONCATENATING 32-BYTE WORDS IS INJECTIVE.** Different resolved lists are different keccak
inputs, so equal keccak values of different lists are a collision on named inputs. -/
def Properties.BlobsEncWordsInjective : Prop :=
  ∀ a b : List UInt256, encWords a = encWords b → a = b

/-- **AN ACCEPTED INPUT RESOLVES TO THE COMMITTED LIST, OR A NAMED COLLISION.** If `h` is keccak of
the concatenation of a list `vs`, every input `checkDA` accepts for `h` resolves to `vs`, or keccak
collides on the two concatenations. Under the `BLOBS_ZKSYNC_OS` scheme `vs` is meant to be the batch's
blob versioned hashes; that is the program's side and is not modelled. -/
@[headline] def Properties.BlobsAcceptedBindsOrCollision : Prop :=
  ∀ (K : Bytes → UInt256) (env : TxEnv) (S : VState) (input : Bytes) (vs : List UInt256)
    (out : DAOutput),
    checkDA K env S (K (encWords vs)) input = some out →
      resolvedHashes env input = vs
        ∨ HashCollision K (encWords (resolvedHashes env input)) (encWords vs)

/-- **TWO ACCEPTANCES OF ONE COMMITMENT RESOLVE TO ONE LIST, OR A NAMED COLLISION**, whatever the
two states, transactions and inputs. -/
def Properties.BlobsTwoAcceptancesAgreeOrCollision : Prop :=
  ∀ (K : Bytes → UInt256) (env₁ env₂ : TxEnv) (S₁ S₂ : VState) (h : UInt256)
    (input₁ input₂ : Bytes) (out₁ out₂ : DAOutput),
    checkDA K env₁ S₁ h input₁ = some out₁ → checkDA K env₂ S₂ h input₂ = some out₂ →
      resolvedHashes env₁ input₁ = resolvedHashes env₂ input₂
        ∨ HashCollision K (encWords (resolvedHashes env₁ input₁))
            (encWords (resolvedHashes env₂ input₂))

/-! ## Countermodels -/

/-- **THE EXTRA-BLOB CHECK IS LOAD-BEARING** for `BlobsAcceptedUsesEveryAttachedBlob`. With
`:83-88` deleted, the empty input is accepted from a transaction carrying the one blob `1`, for every
keccak and state, although it has no zero entry. The source rejects it. -/
@[countermodel] def Properties.BlobsExtraBlobCheckLoadBearing : Prop :=
  ∀ (K : Bytes → UInt256) (S : VState),
    (⟨[1]⟩ : TxEnv).WellFormed
      ∧ checkDAWith { extraBlob := false } K ⟨[1]⟩ S (K (encWords [])) [] = some DAOutput.empty
      ∧ zeroCount (inputWords []) ≠ (⟨[1]⟩ : TxEnv).blobs.length
      ∧ checkDA K ⟨[1]⟩ S (K (encWords [])) [] = none

/-- **THE WINDOW CONJUNCT IS LOAD-BEARING** for freshness. For every keccak there is a reachable
world whose only logged `publishBlobs` call wrote hash `1` at block 1, now at block
`2 + BLOB_EXPIRATION_BLOCKS`. With the window conjunct of `:39` deleted, `checkDA` accepts the
one-entry input naming hash `1` from a transaction with no blob, although no logged call wrote it in
the window. The source rejects it. -/
@[countermodel] def Properties.BlobsWindowCheckLoadBearing : Prop :=
  ∀ K : Bytes → UInt256, ∃ W : World, W.Reachable ∧ W.log = [(1, [1])]
    ∧ W.st.block = 2 + BLOB_EXPIRATION_BLOCKS
    ∧ checkDAWith { window := false } K ⟨[]⟩ W.st (K (encWords [1])) (toB32 1)
        = some DAOutput.empty
    ∧ ¬ LoggedInWindow W 1
    ∧ checkDA K ⟨[]⟩ W.st (K (encWords [1])) (toB32 1) = none

/-! ## Witnesses -/

/-- **WITNESS** for the acceptance, freshness and availability results. Deploy at block 1, publish
hash `7` there, move to block 10. A transaction carrying the one blob `9` submits the two entries
`[7, 0]`: they resolve to `[7, 9]`, and `checkDA` accepts them for `h = keccak([7, 9])`, for every
keccak. Hash `7` was written in the window. -/
@[witness] def Properties.BlobsAcceptanceWitness : Prop :=
  ∀ K : Bytes → UInt256, ∃ W : World, W.Reachable ∧ W.log = [(1, [7])] ∧ W.st.block = 10
    ∧ (⟨[9]⟩ : TxEnv).WellFormed ∧ attached ⟨[9]⟩ = [9]
    ∧ inputWords (toB32 7 ++ toB32 0) = [7, 0]
    ∧ resolvedHashes ⟨[9]⟩ (toB32 7 ++ toB32 0) = [7, 9]
    ∧ checkDA K ⟨[9]⟩ W.st (K (encWords [7, 9])) (toB32 7 ++ toB32 0) = some DAOutput.empty
    ∧ Available W.st 7 ∧ LoggedInWindow W 7

/-- **WITNESS** for the binding results, both ways. First, for every keccak, an accepted input for
`h = keccak([7, 9])` resolves to `[7, 9]`, and the named collision is false. Second, under the
constant hash, an input resolving to `[7, 9]` is accepted for `h = keccak([8])`: the lists differ
and the named collision holds. -/
@[witness] def Properties.BlobsBindingWitness : Prop :=
  (∀ K : Bytes → UInt256, ∃ W : World, W.Reachable
      ∧ checkDA K ⟨[9]⟩ W.st (K (encWords [7, 9])) (toB32 7 ++ toB32 0) = some DAOutput.empty
      ∧ resolvedHashes ⟨[9]⟩ (toB32 7 ++ toB32 0) = [7, 9]
      ∧ ¬ HashCollision K (encWords (resolvedHashes ⟨[9]⟩ (toB32 7 ++ toB32 0)))
          (encWords [7, 9]))
  ∧ (∃ W : World, W.Reachable
      ∧ checkDA (fun _ => 0) ⟨[9]⟩ W.st ((fun _ => (0 : UInt256)) (encWords [8]))
          (toB32 7 ++ toB32 0) = some DAOutput.empty
      ∧ resolvedHashes ⟨[9]⟩ (toB32 7 ++ toB32 0) ≠ [8]
      ∧ HashCollision (fun _ => (0 : UInt256))
          (encWords (resolvedHashes ⟨[9]⟩ (toB32 7 ++ toB32 0))) (encWords [8]))

/-- **WITNESS** that two different inputs from two different transactions can be accepted for one
commitment and resolve to one list. Deploy at block 1, publish hashes `7` and `9` there, move to
block 10. The input `[7, 0]` from a transaction carrying blob `9` and the input `[7, 9]` from a
transaction carrying no blob both resolve to `[7, 9]` and are accepted for `h = keccak([7, 9])`, for
every keccak. -/
@[witness] def Properties.BlobsTwoInputsOneListWitness : Prop :=
  ∀ K : Bytes → UInt256, ∃ W : World, W.Reachable
    ∧ checkDA K ⟨[9]⟩ W.st (K (encWords [7, 9])) (toB32 7 ++ toB32 0) = some DAOutput.empty
    ∧ checkDA K ⟨[]⟩ W.st (K (encWords [7, 9])) (toB32 7 ++ toB32 9) = some DAOutput.empty
    ∧ toB32 7 ++ toB32 0 ≠ toB32 7 ++ toB32 9
    ∧ resolvedHashes ⟨[9]⟩ (toB32 7 ++ toB32 0) = resolvedHashes ⟨[]⟩ (toB32 7 ++ toB32 9)

end Contracts.ZKsyncOSBlobsDA
