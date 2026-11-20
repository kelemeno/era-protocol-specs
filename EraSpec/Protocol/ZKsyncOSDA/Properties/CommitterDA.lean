import EraSpec.Protocol.ZKsyncOSDA.Specs.CommitterDA
import EraSpec.Core.Headline

/-!
# Properties: the DA guarantee each validator leaves once the committer discards its output

Statements about `../Specs/CommitterDA.lean` and `../Specs/Validators.lean` (source `b17415d20`).
Proofs: `../Proofs/CommitterDA.lean`. No statement takes a global hash premise;
`RollupAcceptedIff` takes the pinned premise that keccak does not map the named first-blob
preimage to zero, and the binding results end in a collision on two named inputs, or in keccak
mapping one named input to zero.

`CommitterFacet` keeps nothing of the validator's output: it only requires both arrays to be
empty or both to be sixteen zeros (`CommitterDACheckIff`). So on ZKsync OS the on-L1 DA guarantee
is what `checkDA` itself enforces. Per validator, with `_maxBlobsSupported = 16` and the committer's
check (`…Accepted` in the spec):

| Validator | Accepted iff | What the acceptance puts on L1 |
|---|---|---|
| `RollupL1DAValidator`, blob source | `RollupZeroBlobForm`: blob count 0, the source byte `1` and nothing after it, no blob attached (*) | nothing: the full pubdata hash is compared with nothing |
| `RollupL1DAValidator`, calldata source | `RollupCalldataForm`: blob count 1, zero linear hash, then the pubdata and a zero commitment (*) | the pubdata, in the commit calldata, with keccak equal to the full pubdata hash |
| `RelayedSLDAValidator` | `RelayedForm`: blob count `n ≤ 16`, zero linear hashes and commitments (`RelayedAcceptedIff`) | the pubdata, in the message relayed to L1, with keccak equal to the full pubdata hash |
| `ValidiumL1DAValidator` | a 32-byte input, whatever the commitment (`ValidiumAcceptedIff`) | nothing |
| `BlobsL1DAValidatorZKsyncOS` | its own `checkDA` (`BlobsAcceptedIffCheckDA`) | blob versioned hashes, each a blob of the commit transaction or written by `publishBlobs` in the window |

(*) `RollupAcceptedCases`, `RollupFormsAccepted`. The two rollup rows are exact
(`RollupAcceptedIff`) when keccak does not map the named input `firstBlobCommitmentPreimage env input`
to zero; the blob branch with at least one record passes only if it does.

**Headlines.**

* `RollupPubdataPublishedOrCollision`: under the program premise "a batch with nonempty pubdata
  never commits zero blobs" (`pub ≠ [] → lin ≠ []`), an input the rollup validator and the committer
  accept for the commitment `keccak (l2Output sd (keccak pub) lin)` carries `pub` in the commit
  calldata, or `pub` is empty, or keccak collides on two named inputs, or maps the named first-blob
  preimage to zero.
* `RollupProgramPremiseLoadBearing`: without that premise the statement is false. A zero-blob
  commitment to a nonempty `pub` is accepted from a 66-byte input with no blob attached
  (`RollupZeroBlobAcceptsUnpublishedPubdata`, for every keccak).
* `CommitterZeroCheckLoadBearing`: the committer's all-zero check is needed as well. For a
  commitment whose linear hash is nonzero, the rollup validator can return an output that passes
  the committer's length check but not its all-zero check, while no disjunct of the headline's
  conclusion holds.
* `RelayedPubdataRelayedOrCollision`: the gateway validator needs no program premise. Every
  acceptance relays the committed pubdata, or keccak collides on two named inputs.
* `BlobsCommittedHashesFreshOrCollision`: through the ZKsync OS blobs validator, every hash of the
  committed list is a blob of the commit transaction or was written in the window, or keccak
  collides on two named inputs.

**Witnesses.** `RollupHeadlineWitness` meets every premise of the rollup headline (nonempty
pubdata, a one-blob commitment) through the calldata shape, with no collision and no zero hash;
`RollupHeadlineCollisionFires` shows the collision disjunct is what the constant hash reaches;
`RollupFormsWitness` meets the premise of `RollupAcceptedIff` with each shape;
`RelayedHeadlineWitness` and `BlobsHeadlineWitness` do the same for the other two headlines, and
`RelayedCollisionFires` reaches the gateway headline's pubdata collision.

What the program computes is not modelled; the premises on it are named where used
(ASSUMPTIONS.md `PROTO-PROG-DA`). On the calldata branch the accepted prefix always has one blob and
a zero linear hash (`RollupAcceptedCases`), so `lin = [0]` is the one-blob commitment that can match
it without a collision; the witnesses use it.
-/

namespace Contracts.ZKsyncOSCommitterDA

open AttackVectors.BundleHashEncoding
open Contracts.ZKsyncOSBlobsDA (Bytes toB32 b32At DAOutput TxEnv encWords World LoggedInWindow
  resolvedHashes)

/-! ## The committer's check -/

/-- **THE COMMITTER ACCEPTS AN OUTPUT IFF BOTH ARRAYS ARE EMPTY OR BOTH ARE SIXTEEN ZEROS.** -/
@[headline] def Properties.CommitterDACheckIff : Prop :=
  ∀ o : DAOutput, committerDACheck o = true ↔
    (o.blobsLinearHashes = [] ∧ o.blobsOpeningCommitments = [])
    ∨ (o.blobsLinearHashes = List.replicate TOTAL_BLOBS_IN_COMMITMENT 0
        ∧ o.blobsOpeningCommitments = List.replicate TOTAL_BLOBS_IN_COMMITMENT 0)

/-! ## `RollupL1DAValidator` -/

/-- **EVERY ROLLUP ACCEPTANCE HAS ONE OF TWO SHAPES, OR KECCAK MAPS A NAMED INPUT TO ZERO.** In every
state, an input the rollup validator and the committer accept has the zero-blob shape or the
calldata shape, or keccak maps `firstBlobCommitmentPreimage env input` to zero. -/
def Properties.RollupAcceptedCases : Prop :=
  ∀ (K : Crypto) (env : TxEnv) (S : RollupState) (h : UInt256) (input : Bytes),
    RollupAccepted K env S h input →
      RollupZeroBlobForm K env h input ∨ RollupCalldataForm K h input
        ∨ K.keccak (firstBlobCommitmentPreimage env input) = 0

/-- **BOTH SHAPES ARE ACCEPTED**, in every state and for every keccak and precompile. -/
def Properties.RollupFormsAccepted : Prop :=
  ∀ (K : Crypto) (env : TxEnv) (S : RollupState) (h : UInt256) (input : Bytes),
    RollupZeroBlobForm K env h input ∨ RollupCalldataForm K h input →
      RollupAccepted K env S h input

/-- **EXACT ROLLUP ACCEPTANCE.** When keccak does not map the named first-blob preimage to zero,
the rollup validator and the committer accept exactly the two shapes. -/
@[headline] def Properties.RollupAcceptedIff : Prop :=
  ∀ (K : Crypto) (env : TxEnv) (S : RollupState) (h : UInt256) (input : Bytes),
    K.keccak (firstBlobCommitmentPreimage env input) ≠ 0 →
      (RollupAccepted K env S h input
        ↔ RollupZeroBlobForm K env h input ∨ RollupCalldataForm K h input)

/-- **HEADLINE: A ROLLUP ACCEPTANCE CARRIES THE PUBDATA, GIVEN THE PROGRAM PREMISE.** Let the
batch's commitment be `keccak (l2Output sd (keccak pub) lin)` for its pubdata `pub`. Assume the
program premise: if `pub` is nonempty then `lin` (the committed blobs) is nonempty. Then every input
the rollup validator and the committer accept for that commitment, in any state and transaction,
satisfies one of:

* `pub` is empty;
* the commit calldata carries `pub` (`CalldataCarries`);
* keccak collides on the validator's hashed prefix and the program's preimage;
* keccak collides on the calldata branch's pubdata and `pub`;
* keccak maps the named first-blob preimage to zero. -/
@[headline] def Properties.RollupPubdataPublishedOrCollision : Prop :=
  ∀ (K : Crypto) (env : TxEnv) (S : RollupState) (sd : UInt256) (lin : List UInt256)
    (pub input : Bytes),
    (pub ≠ [] → lin ≠ []) →
    RollupAccepted K env S (K.keccak (l2Output sd (K.keccak pub) lin)) input →
      pub = [] ∨ CalldataCarries input pub
        ∨ HashCollision K.keccak (l2Prefix input) (l2Output sd (K.keccak pub) lin)
        ∨ HashCollision K.keccak (calldataPubdata input) pub
        ∨ K.keccak (firstBlobCommitmentPreimage env input) = 0

/-- **A ZERO-BLOB COMMITMENT IS ACCEPTED FROM 66 BYTES AND NO BLOB.** For every keccak, precompile,
state and pubdata `pub`: the commitment `keccak (l2Output sd (keccak pub) [])` is accepted from the
66-byte input `l2Output sd (keccak pub) [] ++ [1]` by a transaction with no blob, and that input
does not carry `pub` (`CalldataCarries`). -/
@[countermodel] def Properties.RollupZeroBlobAcceptsUnpublishedPubdata : Prop :=
  ∀ (K : Crypto) (S : RollupState) (sd : UInt256) (pub : Bytes),
    RollupAccepted K ⟨[]⟩ S (K.keccak (l2Output sd (K.keccak pub) []))
        (l2Output sd (K.keccak pub) [] ++ [1])
      ∧ (l2Output sd (K.keccak pub) [] ++ [1]).length = 66
      ∧ ¬ CalldataCarries (l2Output sd (K.keccak pub) [] ++ [1]) pub

/-- **THE PROGRAM PREMISE IS LOAD-BEARING.** There is a keccak, a nonempty pubdata and a zero-blob
commitment to it that the rollup validator and the committer accept, for which every disjunct of
the headline's conclusion is false. -/
@[countermodel] def Properties.RollupProgramPremiseLoadBearing : Prop :=
  ∃ (K : Crypto) (env : TxEnv) (S : RollupState) (sd : UInt256) (pub input : Bytes),
    pub ≠ []
      ∧ RollupAccepted K env S (K.keccak (l2Output sd (K.keccak pub) [])) input
      ∧ ¬ (pub = [] ∨ CalldataCarries input pub
        ∨ HashCollision K.keccak (l2Prefix input) (l2Output sd (K.keccak pub) [])
        ∨ HashCollision K.keccak (calldataPubdata input) pub
        ∨ K.keccak (firstBlobCommitmentPreimage env input) = 0)

/-- **THE COMMITTER'S ALL-ZERO CHECK IS LOAD-BEARING.** There is a keccak, a precompile oracle, a
nonempty pubdata, a commitment to it whose one linear hash is nonzero (so the program premise holds)
and an input for which the rollup validator returns an output that passes the committer's length
check (both arrays have 16 entries) but not its all-zero check, and for which every disjunct of the
headline's conclusion is false. -/
@[countermodel] def Properties.CommitterZeroCheckLoadBearing : Prop :=
  ∃ (K : Crypto) (env : TxEnv) (S : RollupState) (sd x : UInt256) (pub input : Bytes)
    (o : DAOutput),
    x ≠ 0 ∧ pub ≠ []
      ∧ rollupCheckDA K env S (K.keccak (l2Output sd (K.keccak pub) [x])) input
          TOTAL_BLOBS_IN_COMMITMENT = some o
      ∧ o.blobsLinearHashes.length = TOTAL_BLOBS_IN_COMMITMENT
      ∧ o.blobsOpeningCommitments.length = TOTAL_BLOBS_IN_COMMITMENT
      ∧ committerDACheck o = false
      ∧ ¬ (pub = [] ∨ CalldataCarries input pub
        ∨ HashCollision K.keccak (l2Prefix input) (l2Output sd (K.keccak pub) [x])
        ∨ HashCollision K.keccak (calldataPubdata input) pub
        ∨ K.keccak (firstBlobCommitmentPreimage env input) = 0)

/-! ## `RelayedSLDAValidator` -/

/-- **EXACT GATEWAY ACCEPTANCE.** The gateway validator and the committer accept, with relayed
message `msg`, exactly the gateway shape. -/
@[headline] def Properties.RelayedAcceptedIff : Prop :=
  ∀ (K : Crypto) (G : GatewayEnv) (caller chainId batchNumber h : UInt256) (input : Bytes)
    (msg : RelayMessage),
    RelayedAccepted K G caller chainId batchNumber h input msg
      ↔ RelayedForm K G caller chainId batchNumber h input msg

/-- **HEADLINE: THE GATEWAY VALIDATOR RELAYS THE PUBDATA, WITH NO PROGRAM PREMISE.** For the
commitment `keccak (l2Output sd (keccak pub) lin)`, any `lin`, every accepted input relays `pub` to
L1 for this chain and batch, or keccak collides on the hashed prefix and the program's preimage, or
on the relayed pubdata and `pub`. -/
@[headline] def Properties.RelayedPubdataRelayedOrCollision : Prop :=
  ∀ (K : Crypto) (G : GatewayEnv) (caller chainId batchNumber sd : UInt256) (lin : List UInt256)
    (pub input : Bytes) (msg : RelayMessage),
    RelayedAccepted K G caller chainId batchNumber (K.keccak (l2Output sd (K.keccak pub) lin))
        input msg →
      msg.chainId = chainId ∧ msg.batchNumber = batchNumber
        ∧ (msg.pubdata = pub
          ∨ HashCollision K.keccak (l2Prefix input) (l2Output sd (K.keccak pub) lin)
          ∨ HashCollision K.keccak msg.pubdata pub)

/-! ## `ValidiumL1DAValidator` -/

/-- **VALIDIUM: ANY 32-BYTE INPUT, ANY COMMITMENT.** The validium validator and the committer accept
exactly the 32-byte inputs; the commitment is not an argument of the model, because the source does
not read it. -/
@[headline] def Properties.ValidiumAcceptedIff : Prop :=
  ∀ input : Bytes, ValidiumAccepted input ↔ input.length = 32

/-! ## `BlobsL1DAValidatorZKsyncOS` -/

/-- **THE COMMITTER ADDS NOTHING TO THE ZKSYNC OS BLOBS VALIDATOR.** Accepted iff its `checkDA`
returns. -/
def Properties.BlobsAcceptedIffCheckDA : Prop :=
  ∀ (K : Crypto) (env : TxEnv) (S : Contracts.ZKsyncOSBlobsDA.VState) (h : UInt256) (input : Bytes),
    BlobsAccepted K env S h input
      ↔ ∃ o, Contracts.ZKsyncOSBlobsDA.checkDA K.keccak env S h input = some o

/-- **HEADLINE: THE COMMITTED BLOB HASHES ARE ATTACHED OR FRESH, OR A NAMED COLLISION.** On a
reachable state of the ZKsync OS blobs validator, let the commitment be keccak of the concatenation
of a list `vs`. For every input the validator and the committer accept, each hash of `vs` is a
nonzero blob of the commit transaction or was written by a logged `publishBlobs` call in the window,
or keccak collides on the input's resolved concatenation and that of `vs`. -/
@[headline] def Properties.BlobsCommittedHashesFreshOrCollision : Prop :=
  ∀ (K : Crypto) (env : TxEnv) (W : World) (vs : List UInt256) (input : Bytes),
    W.Reachable → BlobsAccepted K env W.st (K.keccak (encWords vs)) input →
      (∀ v ∈ vs, (v ∈ env.blobs ∧ v ≠ 0) ∨ LoggedInWindow W v)
        ∨ HashCollision K.keccak (encWords (resolvedHashes env input)) (encWords vs)

/-! ## Witnesses -/

/-- **WITNESS** for the rollup headline: a nonempty pubdata and a commitment with nonempty `lin` (so
the program premise holds with both sides nonempty), accepted from an input that carries the
pubdata; neither named collision holds and the named first-blob preimage is not mapped to zero. -/
@[witness] def Properties.RollupHeadlineWitness : Prop :=
  ∃ (K : Crypto) (env : TxEnv) (S : RollupState) (sd : UInt256) (lin : List UInt256)
    (pub input : Bytes),
    pub ≠ [] ∧ lin ≠ []
      ∧ RollupAccepted K env S (K.keccak (l2Output sd (K.keccak pub) lin)) input
      ∧ CalldataCarries input pub
      ∧ ¬ HashCollision K.keccak (l2Prefix input) (l2Output sd (K.keccak pub) lin)
      ∧ ¬ HashCollision K.keccak (calldataPubdata input) pub
      ∧ K.keccak (firstBlobCommitmentPreimage env input) ≠ 0

/-- **THE COLLISION DISJUNCT FIRES.** There is a keccak, a nonempty pubdata and a commitment with
nonempty `lin` to it, accepted from an input that does not carry the pubdata, where the named prefix
collision holds. (The proof uses the constant hash and a zero-blob input.) -/
@[countermodel] def Properties.RollupHeadlineCollisionFires : Prop :=
  ∃ (K : Crypto) (env : TxEnv) (S : RollupState) (sd : UInt256) (lin : List UInt256)
    (pub input : Bytes),
    pub ≠ [] ∧ lin ≠ []
      ∧ RollupAccepted K env S (K.keccak (l2Output sd (K.keccak pub) lin)) input
      ∧ ¬ CalldataCarries input pub
      ∧ HashCollision K.keccak (l2Prefix input) (l2Output sd (K.keccak pub) lin)

/-- **WITNESS** for `RollupAcceptedIff`: one keccak under which the named first-blob preimage of a
zero-blob input and of a calldata input with nonempty pubdata are not mapped to zero, and both are
accepted. -/
@[witness] def Properties.RollupFormsWitness : Prop :=
  ∃ (K : Crypto) (S : RollupState) (h₁ h₂ : UInt256) (input₁ input₂ : Bytes),
    K.keccak (firstBlobCommitmentPreimage ⟨[]⟩ input₁) ≠ 0
      ∧ K.keccak (firstBlobCommitmentPreimage ⟨[]⟩ input₂) ≠ 0
      ∧ RollupZeroBlobForm K ⟨[]⟩ h₁ input₁ ∧ RollupAccepted K ⟨[]⟩ S h₁ input₁
      ∧ RollupCalldataForm K h₂ input₂ ∧ RollupAccepted K ⟨[]⟩ S h₂ input₂
      ∧ calldataPubdata input₂ ≠ []

/-- **WITNESS** for the gateway headline: a commitment with nonempty `lin` to a nonempty pubdata,
accepted with the pubdata relayed, and neither named collision holding. -/
@[witness] def Properties.RelayedHeadlineWitness : Prop :=
  ∃ (K : Crypto) (G : GatewayEnv) (caller chainId batchNumber sd : UInt256) (lin : List UInt256)
    (pub input : Bytes) (msg : RelayMessage),
    pub ≠ [] ∧ lin ≠ []
      ∧ RelayedAccepted K G caller chainId batchNumber (K.keccak (l2Output sd (K.keccak pub) lin))
          input msg
      ∧ msg.pubdata = pub
      ∧ ¬ HashCollision K.keccak (l2Prefix input) (l2Output sd (K.keccak pub) lin)
      ∧ ¬ HashCollision K.keccak msg.pubdata pub

/-- **THE GATEWAY COLLISION DISJUNCT FIRES.** There is a keccak, a nonempty pubdata, a commitment
with nonempty `lin` to it, and an accepted input that relays a different pubdata, where the named
pubdata collision holds. (The proof uses the constant hash.) -/
@[countermodel] def Properties.RelayedCollisionFires : Prop :=
  ∃ (K : Crypto) (G : GatewayEnv) (caller chainId batchNumber sd : UInt256) (lin : List UInt256)
    (pub input : Bytes) (msg : RelayMessage),
    pub ≠ [] ∧ lin ≠ []
      ∧ RelayedAccepted K G caller chainId batchNumber (K.keccak (l2Output sd (K.keccak pub) lin))
          input msg
      ∧ msg.pubdata ≠ pub
      ∧ HashCollision K.keccak msg.pubdata pub

/-- **WITNESS** for the ZKsync OS blobs headline: for every keccak, on a reachable world, a
two-hash commitment accepted from a transaction that carries a blob; each committed hash is attached
or fresh, and the named collision is false. -/
@[witness] def Properties.BlobsHeadlineWitness : Prop :=
  ∀ K : Crypto, ∃ (env : TxEnv) (W : World) (vs : List UInt256) (input : Bytes),
    W.Reachable ∧ vs.length = 2 ∧ env.blobs ≠ []
      ∧ BlobsAccepted K env W.st (K.keccak (encWords vs)) input
      ∧ (∀ v ∈ vs, (v ∈ env.blobs ∧ v ≠ 0) ∨ LoggedInWindow W v)
      ∧ ¬ HashCollision K.keccak (encWords (resolvedHashes env input)) (encWords vs)

end Contracts.ZKsyncOSCommitterDA
