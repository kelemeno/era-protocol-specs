import EraSpec.Contracts.L2InteropHandler.Specs.AtomicSourceBindingFaithful

/-!
# Properties: the atomic path's source binding, over `executeAtomicBundle`

Statements about `EraSpec.Contracts.L2InteropHandler.Specs.AtomicSourceBindingFaithful`. Proofs are
in `EraSpec.Contracts.L2InteropHandler.Proofs.AtomicSourceBindingFaithful`.

None of these takes an injectivity premise on a hash over its whole domain. Hash events appear only
in pinned form: the executing leg's commit preimage mapped to the sentinel `0`
(`CommitValueIsSentinel`), and collisions of the executing leg's own preimages with an entry of the
vouching chain's own log (`CommitPreimageClash`, `BundlePreimageClash`), or injectivity on those
named pairs (the `…On` form). The premises about the destination's inclusion verifier
(`HonestVouching`, `AcceptsOnlyKeysOf`, `VerifierSoundFor`) are about the abstract
`Dest.verifyInclusion`: for the deployed verifier they idealize Merkle-path soundness and root
authentication, which are not modelled here (see the Specs header).

Groups, in order:

* **The three links** the original topic assumed, proved with no premise: a successful execution
  locates exactly one leg whose accepted proof names chain `c = legSourceChainIds[i]`
  (`AtomicExecutionLocatesVouchingLeg`, `VouchingLegUnique`), and every call is delivered with the
  bundle's own `sourceChainId` (`DeliveriesCarryDeclaredSource`). The checks see that field only
  through the hash (`DeclaredSourceSeenOnlyThroughHash`). That the validator's source check is
  vacuous on the atomic call site is `AtomicSourceBindingStrong`'s `DestContextCheckBySite`.
* **The headline** `AtomicSenderIsVouchingChainOrBreak`, its byte form, its bounded form, and the
  split of its premise.
* **The register.** `DeclaredOfHashForcesBundleBlindHash`: the original's `declared : Hash → Chain`
  exists only for a hash under which all of one chain's bundles share one hash.
* **Witnesses and countermodels.** The headline's premises hold together with no break
  (`AtomicSenderBindingWitness`), and so do those of the other results with premises
  (`DeclaredSourceSeenOnlyThroughHashWitness`, `HonestVouchingSplitWitness`,
  `DeclaredOfHashWitness`); without honest vouching any chain impersonates any other, for every
  keccak (`MisbehavingLegChainImpersonates`); and each break disjunct fires alone
  (`SentinelCommitFires`, `CommitPreimageClashFires`, `BundlePreimageClashFires`).
* **The vouching chain's deployed run**, from topic `SourceBindingReduced`: honest vouching is what a
  run of the deployed send path gives, with the verifier half as the only premise
  (`DeployedRunVouchesHonestly`); a successful atomic execution runs a validated dispatch of the
  vouching chain, or a break holds (`AtomicExecutionRunsADispatchedBundleOrBreak`); with the ABI
  decoder inverting the encoder, it runs exactly that dispatch's bundle, and every recipient sees a
  sender on the vouching chain that took part in the send and receives no base-token value
  (`AtomicExecutionRunsTheDispatchedBundleOrBreak`). Witness: `DeployedRunExecutionWitness`.
-/

namespace Contracts.L2InteropHandler.AtomicSourceFaithful

open AttackVectors.BundleHashEncoding (abiEncode word HashCollision)
open Contracts.InteropCenter (Address Bundle)
open IMTAbstract (keys)
open Contracts.InteropCommitmentTree (toAbs)

/-! ## The three links -/

/-- **(a) AND (b): A SUCCESSFUL EXECUTION LOCATES ITS VOUCHING LEG.** If `executeAtomicBundle(B, fin)`
succeeds, there is a leg `i` of the flow whose bundle hash is the executed bundle hash, whose
declared chain `legSourceChainIds[i] = c` is the chain its proof names, and whose inclusion proof
`verifyInclusion` accepted for `commitValue(flowId, bundleHash)`. No premise. -/
def Properties.AtomicExecutionLocatesVouchingLeg : Prop :=
  ∀ (D : Dest) (st st' : HandlerState) (caller : Address) (B : List UInt8)
    (fin : AtomicFinalityProof) (b : Bundle) (ds : List Delivery),
    ExecutesAtomic D st caller B fin b st' ds →
      ∃ (i : ℕ) (c : UInt256) (p : ImtProof), LegAt fin i (executedHash D B b) c p ∧
        p.sourceChainId = c ∧
        D.verifyInclusion p (commitValue D.keccak fin.flow.flowId (executedHash D B b))
          fin.flow.deadline fin.flow.settlementLayerChainId

/-- **THE VOUCHING LEG IS UNIQUE.** `_checkFlowId` requires the leg hashes to be strictly ascending,
so a bundle hash names at most one leg, and with it one declared chain and one proof. So "the"
vouching chain of an execution is well defined. -/
def Properties.VouchingLegUnique : Prop :=
  ∀ (D : Dest) (h : UInt256) (fin : AtomicFinalityProof), FlowGateAccepts D h fin →
    ∀ (i j : ℕ) (c c' : UInt256) (p p' : ImtProof), LegAt fin i h c p → LegAt fin j h c' p' →
      i = j ∧ c = c' ∧ p = p'

/-- **(c): EVERY CALL IS DELIVERED WITH THE BUNDLE'S OWN `sourceChainId`.** `_executeCalls` makes
one call per bundle call, and each carries `b.sourceChainId`: as the chain of the ERC-7930 sender
`formatEvmV1(_sourceChainId, from)` and as the chain `_handleCallValue` passes to
`BaseTokenHolder.give`. No premise. -/
def Properties.DeliveriesCarryDeclaredSource : Prop :=
  ∀ (D : Dest) (st st' : HandlerState) (caller : Address) (B : List UInt8)
    (fin : AtomicFinalityProof) (b : Bundle) (ds : List Delivery),
    ExecutesAtomic D st caller B fin b st' ds →
      ds.length = b.calls.length ∧ ∀ d ∈ ds, d.sourceChainId = b.sourceChainId

/-- **THE CHECKS SEE THE DECLARED CHAIN ONLY THROUGH THE HASH.** If `executeAtomicBundle(B, fin)`'s
checks pass for a bundle `b`, they also pass for any nonempty bytes `B'` that decode to `b` with a
different `sourceChainId` and have the same bundle hash. No check of `executeAtomicBundle` or
`requireFlowFinalized`, as modelled, reads the field except through the hash and the validator's
comparison of the field with itself. This is an observation about the model, not a binding
result: the statement also covers `s' = b.sourceChainId`, and for a different `s'` the hash
equality it assumes is a keccak collision on two different `abiEncode` preimages. -/
def Properties.DeclaredSourceSeenOnlyThroughHash : Prop :=
  ∀ (D : Dest) (st : HandlerState) (caller : Address) (fin : AtomicFinalityProof)
    (B B' : List UInt8) (b : Bundle) (s' : UInt256),
    AtomicChecksPass D st caller B fin b →
    B' ≠ [] → D.decode B' = some { b with sourceChainId := s' } →
    executedHash D B' { b with sourceChainId := s' } = executedHash D B b →
      AtomicChecksPass D st caller B' fin { b with sourceChainId := s' }

/-! ## The headline -/

/-- **HEADLINE: THE DELIVERED SOURCE CHAIN IS THE VOUCHING CHAIN, OR A PINNED BREAK.** Let
`executeAtomicBundle(B, fin)` succeed, with `B` decoding to `b`. Let leg `i` be the leg of the
executed bundle hash, with declared chain `c` and proof `p` (it exists and is unique:
`AtomicExecutionLocatesVouchingLeg`, `VouchingLegUnique`). If chain `c` vouches honestly against
its own log, then one of:

* some logged leg `e` of chain `c` matches: the bundle declares `c`, every call is delivered with
  source chain `c`, `e` was committed under the executing flow's id, and the executed bundle's hash
  preimage is `e`'s (`abi.encode(c, e.bundleBytes)`);
* some logged leg `e` of chain `c` collides with the executing leg: keccak collides on the two
  commit preimages (`CommitPreimageClash`) or on the two bundle-hash preimages
  (`BundlePreimageClash`);
* the executing leg's commit value is the sentinel `0` (`CommitValueIsSentinel`).

This replaces `AtomicSourceBinding.Properties.atomic_source_bound`, which concluded
`declared h = c` from a premise saying exactly that. Here the premise is about the vouching chain
only, the conclusion is about the identity `_executeCalls` hands out, and the gap between them is
the gate, the two keccak preimages and the encoding (`abiEncode_inj`). -/
def Properties.AtomicSenderIsVouchingChainOrBreak : Prop :=
  ∀ (D : Dest) (st st' : HandlerState) (caller : Address) (B : List UInt8)
    (fin : AtomicFinalityProof) (b : Bundle) (ds : List Delivery),
    ExecutesAtomic D st caller B fin b st' ds →
    ∀ (i : ℕ) (c : UInt256) (p : ImtProof), LegAt fin i (executedHash D B b) c p →
    ∀ log : List CommittedLeg, HonestVouching D c log →
      (∃ e ∈ log,
        (b.sourceChainId = c ∧ (∀ d ∈ ds, d.sourceChainId = c) ∧ e.flowId = fin.flow.flowId ∧
            executedPreimage B b = e.preimage c)
          ∨ CommitPreimageClash D.keccak fin.flow.flowId (executedHash D B b) c e
          ∨ BundlePreimageClash D.keccak B b c e)
      ∨ CommitValueIsSentinel D.keccak fin.flow.flowId (executedHash D B b)

/-- **THE EXECUTED BYTES ARE THE COMMITTED BYTES, OR A PINNED BREAK.** The headline with length
bounds below `2^256` bytes on the two byte strings: the first disjunct then says the destination ran
exactly the bytes chain `c` hashed when it committed `e`. -/
def Properties.AtomicExecutesCommittedBytesOrBreak : Prop :=
  ∀ (D : Dest) (st st' : HandlerState) (caller : Address) (B : List UInt8)
    (fin : AtomicFinalityProof) (b : Bundle) (ds : List Delivery),
    ExecutesAtomic D st caller B fin b st' ds →
    ∀ (i : ℕ) (c : UInt256) (p : ImtProof), LegAt fin i (executedHash D B b) c p →
    ∀ log : List CommittedLeg, HonestVouching D c log →
    B.length < 256 ^ 32 → (∀ e ∈ log, e.bundleBytes.length < 256 ^ 32) →
      (∃ e ∈ log,
        (b.sourceChainId = c ∧ (∀ d ∈ ds, d.sourceChainId = c) ∧ e.flowId = fin.flow.flowId ∧
            B = e.bundleBytes)
          ∨ CommitPreimageClash D.keccak fin.flow.flowId (executedHash D B b) c e
          ∨ BundlePreimageClash D.keccak B b c e)
      ∨ CommitValueIsSentinel D.keccak fin.flow.flowId (executedHash D B b)

/-- **BOUNDED FORM.** The headline with its break disjuncts turned into premises: the executing
leg's commit value is not `0`, and keccak is injective on the two named pairs, for every leg of the
vouching chain's log. Then the delivered source chain is the vouching chain. These are the
explicitly bounded no-collision premises ASSUMPTIONS.md asks for; they hold together with the
others (`AtomicSenderBindingWitness`). -/
def Properties.AtomicSenderIsVouchingChainOn : Prop :=
  ∀ (D : Dest) (st st' : HandlerState) (caller : Address) (B : List UInt8)
    (fin : AtomicFinalityProof) (b : Bundle) (ds : List Delivery),
    ExecutesAtomic D st caller B fin b st' ds →
    ∀ (i : ℕ) (c : UInt256) (p : ImtProof), LegAt fin i (executedHash D B b) c p →
    ∀ log : List CommittedLeg, HonestVouching D c log →
    commitValue D.keccak fin.flow.flowId (executedHash D B b) ≠ 0 →
    (∀ e ∈ log, Set.InjOn D.keccak
      {commitPreimage D.keccak fin.flow.flowId (executedHash D B b),
        commitPreimage D.keccak e.flowId (e.bundleHash D.keccak c)}) →
    (∀ e ∈ log, Set.InjOn D.keccak {executedPreimage B b, e.preimage c}) →
      b.sourceChainId = c ∧ ∀ d ∈ ds, d.sourceChainId = c

/-- **THE PREMISE, SPLIT.** A verifier sound for chain `c`'s tree, and a tree holding only the
sentinel and the commit values of chain `c`'s log, give honest vouching by `c`. -/
def Properties.HonestVouchingOfSoundVerifier : Prop :=
  ∀ (D : Dest) (tree : UInt256 → Set UInt256) (c : UInt256) (log : List CommittedLeg),
    VerifierSoundFor D tree c → TreeHoldsSentinelAndLog D.keccak tree c log →
      HonestVouching D c log

/-- The ideal verifier is sound for its tree, at every chain. -/
def Properties.IdealVerifierSound : Prop :=
  ∀ (D : Dest) (tree : UInt256 → Set UInt256) (c : UInt256),
    D.verifyInclusion = idealVerifier tree → VerifierSoundFor D tree c

/-! ## The register -/

/-- **A SOURCE CHAIN DETERMINED BY THE HASH NEEDS A HASH BLIND TO THE BUNDLE.** The original topic
takes `declared : Hash → Chain`, "the `sourceChainId` field baked into bundle hash `h`". Suppose some
map `declared` recovers the chain from every bundle hash `keccak(abi.encode(s, B))`. Then that
keccak gives every bundle of one chain the same hash, whatever its bytes: the map
`s ↦ keccak(abi.encode(s, B₀))` from `bytes32` to `bytes32` is then injective and so onto, which
leaves no second hash for any chain. So the map the original topic takes exists only for a keccak
under which a chain's bundles cannot be told apart by their hash. -/
def Properties.DeclaredOfHashForcesBundleBlindHash : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (declared : UInt256 → UInt256),
    (∀ (s : UInt256) (B : List UInt8), declared (keccak (abiEncode s.val B)) = s) →
      ∀ (s : UInt256) (B B' : List UInt8), keccak (abiEncode s.val B) = keccak (abiEncode s.val B')

/-! ## Witnesses and countermodels -/

/-- **THE HEADLINE'S PREMISES HOLD TOGETHER, AND NO BREAK DISJUNCT IS A TAUTOLOGY.** There is an
`executeAtomicBundle` whose every check passes (`ExecutesAtomic`), delivering at least one call,
whose vouching leg is leg `0`, declared on chain `c`, with chain `c` vouching honestly against a
one-leg log `[e]`; the executed bytes have length below `2^256`, as do `e`'s. The executing commit
value is not `0`, neither clash holds on `e`, the bounded premises hold, and every call is delivered
with source chain `c`. In the proof, `[e]` is the dispatch log of the run of
`DeployedRunExecutionWitness`, the verifier accepts on chain `c` exactly the keys of that run's
tree (the sentinel and `e`'s commit value), and the keccak is topic `Dispatch`'s toy `lastWord`
(the last 32 bytes, read as a word). -/
def Properties.AtomicSenderBindingWitness : Prop :=
  ∃ (D : Dest) (st st' : HandlerState) (caller : Address) (B : List UInt8)
    (fin : AtomicFinalityProof) (b : Bundle) (ds : List Delivery) (c : UInt256) (p : ImtProof)
    (e : CommittedLeg),
    ExecutesAtomic D st caller B fin b st' ds ∧
    LegAt fin 0 (executedHash D B b) c p ∧ HonestVouching D c [e] ∧
    B.length < 256 ^ 32 ∧ e.bundleBytes.length < 256 ^ 32 ∧
    ¬ CommitValueIsSentinel D.keccak fin.flow.flowId (executedHash D B b) ∧
    ¬ CommitPreimageClash D.keccak fin.flow.flowId (executedHash D B b) c e ∧
    ¬ BundlePreimageClash D.keccak B b c e ∧
    commitValue D.keccak fin.flow.flowId (executedHash D B b) ≠ 0 ∧
    Set.InjOn D.keccak {commitPreimage D.keccak fin.flow.flowId (executedHash D B b),
      commitPreimage D.keccak e.flowId (e.bundleHash D.keccak c)} ∧
    Set.InjOn D.keccak {executedPreimage B b, e.preimage c} ∧
    ds ≠ [] ∧ b.sourceChainId = c ∧ ∀ d ∈ ds, d.sourceChainId = c

/-- **`DeclaredSourceSeenOnlyThroughHash` IS NOT VACUOUS.** Its premises hold with a different
declared chain and different bytes: the checks pass for bytes `B` decoding to `b`, and other
nonempty bytes `B'` decode to `b` with another `sourceChainId` and have the same bundle hash. In the
proof the keccak maps every input to `1`, so the two bundle-hash preimages collide. -/
def Properties.DeclaredSourceSeenOnlyThroughHashWitness : Prop :=
  ∃ (D : Dest) (st : HandlerState) (caller : Address) (fin : AtomicFinalityProof)
    (B B' : List UInt8) (b : Bundle) (s' : UInt256),
    AtomicChecksPass D st caller B fin b ∧ B' ≠ [] ∧ B' ≠ B ∧
    D.decode B' = some { b with sourceChainId := s' } ∧
    executedHash D B' { b with sourceChainId := s' } = executedHash D B b ∧
    s' ≠ b.sourceChainId

/-- **THE PREMISE'S TWO HALVES HOLD TOGETHER, ON A TREE WITH A REAL LEG.** A verifier equal to the
ideal verifier on a tree (`IdealVerifierSound`'s premise), sound for that tree at chain `c`, with
the tree holding only the sentinel and the commit values of a one-leg log, whose leg's commit value
is nonzero and in the tree. In the proof the keccak maps every input to `1`. -/
def Properties.HonestVouchingSplitWitness : Prop :=
  ∃ (D : Dest) (tree : UInt256 → Set UInt256) (c : UInt256) (log : List CommittedLeg),
    VerifierSoundFor D tree c ∧ TreeHoldsSentinelAndLog D.keccak tree c log ∧
    D.verifyInclusion = idealVerifier tree ∧
    ∃ e ∈ log, e.value D.keccak c ≠ 0 ∧ e.value D.keccak c ∈ tree c

/-- **`DeclaredOfHashForcesBundleBlindHash` IS NOT VACUOUS.** Its premise holds for some keccak and
map `declared`, and that keccak gives two different byte strings of one chain the same bundle hash.
In the proof the keccak reads its input's leading word and `declared` is the identity. -/
def Properties.DeclaredOfHashWitness : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (declared : UInt256 → UInt256),
    (∀ (s : UInt256) (B : List UInt8), declared (keccak (abiEncode s.val B)) = s) ∧
    ∃ (s : UInt256) (B B' : List UInt8), B ≠ B' ∧
      keccak (abiEncode s.val B) = keccak (abiEncode s.val B')

/-- **COUNTERMODEL: WITHOUT HONEST VOUCHING, ANY CHAIN IMPERSONATES ANY OTHER.** For every keccak
and every two distinct chains, `s` declared and `c` vouching, there is an `executeAtomicBundle`
whose every check passes (`ExecutesAtomic`):

* the flow's only leg declares chain `c` (`legSourceChainIds = [c]`), and its proof names `c`;
* chain `c`'s tree holds the sentinel and the commit value of a bundle that declares `s`, so the
  gate accepts;
* every call is delivered with source chain `s`;
* the declared chain `s` vouches for nothing: on a proof naming `s` only the sentinel is accepted;
* reading chain `c` as honest, against any log, forces a break: a clash with one of the log's legs,
  or the sentinel.

So the gate does not bind the declared chain to the chain that vouched, and no collision is needed
(the statement holds for every keccak). This is the entry-point form of
`AtomicSourceBinding.Properties.atomic_source_unbound_without_honest`. -/
def Properties.MisbehavingLegChainImpersonates : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (s c : UInt256), s ≠ c →
    ∃ (D : Dest) (st st' : HandlerState) (caller : Address) (B : List UInt8)
      (fin : AtomicFinalityProof) (b : Bundle) (ds : List Delivery) (p : ImtProof),
      D.keccak = keccak ∧ ExecutesAtomic D st caller B fin b st' ds ∧
      LegAt fin 0 (executedHash D B b) c p ∧ fin.flow.legSourceChainIds = [c] ∧
      b.sourceChainId = s ∧ ds ≠ [] ∧ (∀ d ∈ ds, d.sourceChainId = s) ∧
      (∀ (q : ImtProof) (v deadline sl : UInt256), q.sourceChainId = s →
        D.verifyInclusion q v deadline sl → v = 0) ∧
      ∀ log : List CommittedLeg, HonestVouching D c log →
        (∃ e ∈ log, CommitPreimageClash keccak fin.flow.flowId (executedHash D B b) c e ∨
          BundlePreimageClash keccak B b c e)
        ∨ CommitValueIsSentinel keccak fin.flow.flowId (executedHash D B b)

/-- **THE SENTINEL DISJUNCT CANNOT BE DROPPED.** An execution whose checks all pass, whose vouching
chain `c` vouches honestly against `[e]` with `e`'s commit value nonzero (its tree holds the
sentinel and that value), and whose bundle declares another chain, so that every call is delivered
with a chain other than `c`: the executing commit value is the sentinel, and neither clash holds on
`e`. The keccak maps every 96-byte input (every commit preimage) to its last word minus one, and
reads any other input's leading word, so the executing leg (bundle hash `1`) commits to `0` and `e`
(bundle hash `2`) to `1`. -/
def Properties.SentinelCommitFires : Prop :=
  ∃ (D : Dest) (st st' : HandlerState) (caller : Address) (B : List UInt8)
    (fin : AtomicFinalityProof) (b : Bundle) (ds : List Delivery) (c : UInt256) (p : ImtProof)
    (e : CommittedLeg),
    ExecutesAtomic D st caller B fin b st' ds ∧ LegAt fin 0 (executedHash D B b) c p ∧
    HonestVouching D c [e] ∧ e.value D.keccak c ≠ 0 ∧ b.sourceChainId ≠ c ∧ ds ≠ [] ∧
    (∀ d ∈ ds, d.sourceChainId ≠ c) ∧
    CommitValueIsSentinel D.keccak fin.flow.flowId (executedHash D B b) ∧
    ¬ CommitPreimageClash D.keccak fin.flow.flowId (executedHash D B b) c e ∧
    ¬ BundlePreimageClash D.keccak B b c e

/-- **THE COMMIT-VALUE CLASH CANNOT BE DROPPED.** An execution whose checks all pass, whose vouching
chain `c` vouches honestly against `[e]`, and whose bundle declares another chain, on which the
executing commit value is not the sentinel and the bundle-hash clash is false (the two bundle
hashes differ): only the commit-preimage clash holds. The keccak maps every 96-byte input, so every
commit preimage, to `1`, and reads any other input's leading word. -/
def Properties.CommitPreimageClashFires : Prop :=
  ∃ (D : Dest) (st st' : HandlerState) (caller : Address) (B : List UInt8)
    (fin : AtomicFinalityProof) (b : Bundle) (ds : List Delivery) (c : UInt256) (p : ImtProof)
    (e : CommittedLeg),
    ExecutesAtomic D st caller B fin b st' ds ∧ LegAt fin 0 (executedHash D B b) c p ∧
    HonestVouching D c [e] ∧ b.sourceChainId ≠ c ∧ ds ≠ [] ∧ (∀ d ∈ ds, d.sourceChainId ≠ c) ∧
    ¬ CommitValueIsSentinel D.keccak fin.flow.flowId (executedHash D B b) ∧
    CommitPreimageClash D.keccak fin.flow.flowId (executedHash D B b) c e ∧
    ¬ BundlePreimageClash D.keccak B b c e

/-- **THE BUNDLE-HASH CLASH CANNOT BE DROPPED.** An execution whose checks all pass, whose vouching
chain `c` vouches honestly against `[e]`, and whose bundle declares another chain, on which the
executing commit value is not the sentinel and the commit-preimage clash is false: only the
bundle-hash clash holds. The keccak maps every input to `1`. This is the case the original's
`declared : Hash → Chain` rules out by construction. -/
def Properties.BundlePreimageClashFires : Prop :=
  ∃ (D : Dest) (st st' : HandlerState) (caller : Address) (B : List UInt8)
    (fin : AtomicFinalityProof) (b : Bundle) (ds : List Delivery) (c : UInt256) (p : ImtProof)
    (e : CommittedLeg),
    ExecutesAtomic D st caller B fin b st' ds ∧ LegAt fin 0 (executedHash D B b) c p ∧
    HonestVouching D c [e] ∧ b.sourceChainId ≠ c ∧ ds ≠ [] ∧ (∀ d ∈ ds, d.sourceChainId ≠ c) ∧
    ¬ CommitValueIsSentinel D.keccak fin.flow.flowId (executedHash D B b) ∧
    ¬ CommitPreimageClash D.keccak fin.flow.flowId (executedHash D B b) c e ∧
    BundlePreimageClash D.keccak B b c e

/-! ## The vouching chain's deployed run -/

/-- **A DEPLOYED SEND PATH VOUCHES HONESTLY.** Let chain `P.chainId`'s send side reach `S` from
genesis by the deployed code (`SourceBindingReduced`'s `SourceReach deployed`: the center, the flow
manager and the commitment tree, with `append`'s tree insert and every check of it), with the
destination's keccak and commit value. If the destination's verifier accepts, on proofs naming that
chain, only keys of `S`'s tree, then the chain vouches honestly against the legs its center
dispatched. The tree half of `HonestVouching` is `SourceBindingReduced`'s
`SourceKeysAreDispatchedCommitValues`; the verifier half is the premise. -/
def Properties.DeployedRunVouchesHonestly : Prop :=
  ∀ (D : Dest) (P : Contracts.InteropCenter.Params) (S : Contracts.SourceBinding.SourceState),
    P.keccak = D.keccak →
    Contracts.SourceBinding.SourceReach Contracts.InteropCenter.deployed P (commitValue P.keccak)
      Contracts.SourceBinding.sourceGenesis S →
    AcceptsOnlyKeysOf D P.chainId S →
      HonestVouching D P.chainId (dispatchLegs P S.center)

/-- **A SUCCESSFUL ATOMIC EXECUTION RUNS A DISPATCH OF THE VOUCHING CHAIN, OR A PINNED BREAK.** Let
the vouching leg's declared chain `P.chainId` reach `S` by the deployed send path, as in
`DeployedRunVouchesHonestly`, with the verifier accepting on that chain only keys of `S`'s tree.
Then one of:

* some atomic dispatch `d` of that run, whose bundle carries no native value and was built with
  `sourceChainId = P.chainId`, matches: the executed bundle declares `P.chainId`, every call is
  delivered with that chain, `d` was sent under the executing flow's id, and the executed bundle's
  hash preimage is `d`'s;
* some atomic dispatch `d` of that run clashes with the executing leg on a named pair of preimages;
* the executing leg's commit value is the sentinel `0`. -/
def Properties.AtomicExecutionRunsADispatchedBundleOrBreak : Prop :=
  ∀ (D : Dest) (P : Contracts.InteropCenter.Params) (S : Contracts.SourceBinding.SourceState),
    P.keccak = D.keccak →
    Contracts.SourceBinding.SourceReach Contracts.InteropCenter.deployed P (commitValue P.keccak)
      Contracts.SourceBinding.sourceGenesis S →
    AcceptsOnlyKeysOf D P.chainId S →
    ∀ (st st' : HandlerState) (caller : Address) (B : List UInt8) (fin : AtomicFinalityProof)
      (b : Bundle) (ds : List Delivery),
      ExecutesAtomic D st caller B fin b st' ds →
      ∀ (i : ℕ) (p : ImtProof), LegAt fin i (executedHash D B b) P.chainId p →
        (∃ d ∈ S.center.log, d.isAtomic = true ∧ Contracts.InteropCenter.Validated d.bundle ∧
          d.bundle.sourceChainId = P.chainId ∧
          ((b.sourceChainId = P.chainId ∧ (∀ x ∈ ds, x.sourceChainId = P.chainId) ∧
              d.atomicSend.flowId = fin.flow.flowId ∧
              executedPreimage B b = Contracts.InteropCenter.bundlePreimage P d.bundle)
            ∨ CommitPreimageClash D.keccak fin.flow.flowId (executedHash D B b) P.chainId
                ⟨d.atomicSend.flowId, P.enc d.bundle⟩
            ∨ BundlePreimageClash D.keccak B b P.chainId ⟨d.atomicSend.flowId, P.enc d.bundle⟩))
        ∨ CommitValueIsSentinel D.keccak fin.flow.flowId (executedHash D B b)

/-- **THE EXECUTED BUNDLE IS THE DISPATCHED BUNDLE, OR A PINNED BREAK.** As above, with the ABI
decoder inverting the encoder on the run's dispatched bundles (`SOL-ABI`, the premise of
`InteropCenter` `ClaimedBundleValidatedOrCollision`) and length bounds below `2^256` bytes. The
first disjunct then says the destination decoded and ran exactly the bundle of an atomic dispatch
`d` of the vouching chain, sent under the executing flow's id and declaring that chain, and that
every recipient call carries that chain, no base-token value (so `_handleCallValue` releases
nothing), and as `from` either `d`'s sender (a direct call, `InteropCenter.sol:742-749`) or the
indirect sender contract one of `d`'s indirect starters named (`:739`). So the identity
`formatEvmV1(sourceChainId, from)` each recipient sees is an account on the vouching chain that took
part in the send. -/
def Properties.AtomicExecutionRunsTheDispatchedBundleOrBreak : Prop :=
  ∀ (D : Dest) (P : Contracts.InteropCenter.Params) (S : Contracts.SourceBinding.SourceState),
    P.keccak = D.keccak →
    Contracts.SourceBinding.SourceReach Contracts.InteropCenter.deployed P (commitValue P.keccak)
      Contracts.SourceBinding.sourceGenesis S →
    AcceptsOnlyKeysOf D P.chainId S →
    (∀ d ∈ S.center.log, D.decode (P.enc d.bundle) = some d.bundle) →
    (∀ d ∈ S.center.log, (P.enc d.bundle).length < 256 ^ 32) →
    ∀ (st st' : HandlerState) (caller : Address) (B : List UInt8) (fin : AtomicFinalityProof)
      (b : Bundle) (ds : List Delivery),
      ExecutesAtomic D st caller B fin b st' ds → B.length < 256 ^ 32 →
      ∀ (i : ℕ) (p : ImtProof), LegAt fin i (executedHash D B b) P.chainId p →
        (∃ d ∈ S.center.log, d.isAtomic = true ∧
          ((b = d.bundle ∧ B = P.enc d.bundle ∧ d.atomicSend.flowId = fin.flow.flowId ∧
              Contracts.InteropCenter.Validated b ∧ b.sourceChainId = P.chainId ∧
              ∀ x ∈ ds, x.sourceChainId = P.chainId ∧ x.value = 0 ∧
                (x.fromAddr = d.sender ∨ ∃ cs ∈ d.starters,
                  cs.callAttributes.indirectCall = true ∧ x.fromAddr = cs.target))
            ∨ CommitPreimageClash D.keccak fin.flow.flowId (executedHash D B b) P.chainId
                ⟨d.atomicSend.flowId, P.enc d.bundle⟩
            ∨ BundlePreimageClash D.keccak B b P.chainId ⟨d.atomicSend.flowId, P.enc d.bundle⟩))
        ∨ CommitValueIsSentinel D.keccak fin.flow.flowId (executedHash D B b)

/-- **THE RUN-LEVEL PREMISES HOLD TOGETHER, WITH NO BREAK.** Chain `324` of topic `Dispatch`'s
witness parameters (the toy keccak `lastWord` and encoder `saltWordsEncoder`) runs the deployed send
path: sender `1` dispatches one atomic leg with one zero-value direct call, and `append` inserts its
nonzero commit value into the tree seeded at genesis. The destination accepts on chain `324` exactly
the keys of that tree and decodes the dispatched bytes back. Every premise of
`AtomicExecutionRunsTheDispatchedBundleOrBreak` holds; the bundle executes, its vouching leg names
chain `324`, the executing commit value is not `0`, neither clash holds on the dispatch, and the
executed bundle is the dispatched one. -/
def Properties.DeployedRunExecutionWitness : Prop :=
  ∃ (P : Contracts.InteropCenter.Params) (D : Dest) (S : Contracts.SourceBinding.SourceState)
    (st st' : HandlerState) (caller : Address) (B : List UInt8) (fin : AtomicFinalityProof)
    (b : Bundle) (ds : List Delivery) (p : ImtProof) (d : Contracts.InteropCenter.Dispatch),
    P.keccak = D.keccak ∧
    Contracts.SourceBinding.SourceReach Contracts.InteropCenter.deployed P (commitValue P.keccak)
      Contracts.SourceBinding.sourceGenesis S ∧
    AcceptsOnlyKeysOf D P.chainId S ∧
    (∀ d' ∈ S.center.log, D.decode (P.enc d'.bundle) = some d'.bundle) ∧
    (∀ d' ∈ S.center.log, (P.enc d'.bundle).length < 256 ^ 32) ∧
    ExecutesAtomic D st caller B fin b st' ds ∧ B.length < 256 ^ 32 ∧
    LegAt fin 0 (executedHash D B b) P.chainId p ∧
    d ∈ S.center.log ∧ d.isAtomic = true ∧ b = d.bundle ∧ ds ≠ [] ∧
    ¬ CommitValueIsSentinel D.keccak fin.flow.flowId (executedHash D B b) ∧
    ¬ CommitPreimageClash D.keccak fin.flow.flowId (executedHash D B b) P.chainId
      ⟨d.atomicSend.flowId, P.enc d.bundle⟩ ∧
    ¬ BundlePreimageClash D.keccak B b P.chainId ⟨d.atomicSend.flowId, P.enc d.bundle⟩

end Contracts.L2InteropHandler.AtomicSourceFaithful
