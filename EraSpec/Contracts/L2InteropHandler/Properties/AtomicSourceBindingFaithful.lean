import EraSpec.Contracts.L2InteropHandler.Specs.AtomicSourceBindingFaithful

/-!
# Properties: the atomic path's source binding, over `executeAtomicBundle`

Statements about `EraSpec.Contracts.L2InteropHandler.Specs.AtomicSourceBindingFaithful`. Proofs are
in `EraSpec.Contracts.L2InteropHandler.Proofs.AtomicSourceBindingFaithful`.

None of these takes a global injectivity premise on a hash. Collisions appear only in pinned form:
on the executing leg's own preimages against an entry of the vouching chain's own log
(`CommitPreimageClash`, `BundlePreimageClash`), or as injectivity on those named pairs (the `…On`
form).

Groups, in order:

* **The three links** the original topic assumed, now proved with no premise: a successful
  execution locates exactly one leg whose accepted proof names chain `c = legSourceChainIds[i]`
  (`AtomicExecutionLocatesVouchingLeg`, `VouchingLegUnique`), and every call is delivered with the
  bundle's own `sourceChainId` (`DeliveriesCarryDeclaredSource`). The destination check on the
  atomic path is vacuous in its source conjunct (`AtomicPathSourceCheckVacuous`), and the checks see
  the declared field only through the hash (`DeclaredSourceSeenOnlyThroughHash`).
* **The headline** `AtomicSenderIsVouchingChainOrLoggedClash`, its byte form, its bounded form, and
  the split of its premise.
* **The register.** `DeclaredOfHashForcesBundleBlindHash`: the original's `declared : Hash → Chain`
  exists only for a hash that ignores the bundle bytes.
* **Witnesses and countermodels.** The headline's premises hold together with no clash
  (`AtomicSourceBoundWitness`); without honest vouching any chain impersonates any other, for every
  keccak (`MisbehavingLegChainImpersonates`); and each clash disjunct fires alone
  (`BundlePreimageClashFires`, `CommitPreimageClashFires`).
* **The vouching chain's run**, from the `InteropCenter` `Dispatch` model: honest vouching is what
  a deployed send path gives (`DispatchRunVouchesHonestly`), and a successful atomic execution runs
  a validated dispatched bundle of the vouching chain, or a logged clash fires
  (`AtomicExecutionRunsADispatchedBundleOrLoggedClash`,
  `AtomicExecutionRunsTheDispatchedBundleOrLoggedClash`, witness `DispatchRunWitness`).
-/

namespace Contracts.L2InteropHandler.AtomicSourceFaithful

open AttackVectors.BundleHashEncoding (abiEncode word HashCollision)
open Contracts.InteropCenter (Address Bundle)

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

/-- **ON THE ATOMIC PATH THE SOURCE CHECK IS VACUOUS.** `_validateBundleDestinationContext` called
with `proofChainId = b.sourceChainId` (`L2InteropHandler.sol:57`) is exactly its two destination
checks. -/
def Properties.AtomicPathSourceCheckVacuous : Prop :=
  ∀ (D : Dest) (b : Bundle),
    DestinationContextValid D b b.sourceChainId ↔
      (b.destinationChainId = D.chainId ∧ b.destinationBaseTokenAssetId = D.baseTokenAssetId)

/-- **ON THE PUBLIC PATH IT BINDS.** The same validator with the message proof's chain as
`proofChainId` (`InteropHandlerBase.sol:92`) forces the declared chain to be the proof's. -/
def Properties.PublicPathSourceCheckBinds : Prop :=
  ∀ (D : Dest) (b : Bundle) (proofChainId : UInt256),
    DestinationContextValid D b proofChainId → b.sourceChainId = proofChainId

/-- **THE CHECKS SEE THE DECLARED CHAIN ONLY THROUGH THE HASH.** If `executeAtomicBundle(B, fin)`'s
checks pass for a bundle `b`, they also pass for any nonempty bytes `B'` that decode to `b` with a
different `sourceChainId` and have the same bundle hash. Nothing in `executeAtomicBundle` or
`requireFlowFinalized` compares the field with anything; only the hash carries it. -/
def Properties.DeclaredSourceSeenOnlyThroughHash : Prop :=
  ∀ (D : Dest) (st : HandlerState) (caller : Address) (fin : AtomicFinalityProof)
    (B B' : List UInt8) (b : Bundle) (s' : UInt256),
    AtomicChecksPass D st caller B fin b →
    B' ≠ [] → D.decode B' = some { b with sourceChainId := s' } →
    executedHash D B' { b with sourceChainId := s' } = executedHash D B b →
      AtomicChecksPass D st caller B' fin { b with sourceChainId := s' }

/-! ## The headline -/

/-- **HEADLINE: THE DELIVERED SOURCE CHAIN IS THE VOUCHING CHAIN, OR A LOGGED CLASH.** Let
`executeAtomicBundle(B, fin)` succeed, with `B` decoding to `b`. Let leg `i` be the leg of the
executed bundle hash, with declared chain `c` and proof `p` (it exists and is unique:
`AtomicExecutionLocatesVouchingLeg`, `VouchingLegUnique`). If chain `c` vouches honestly against
its own log, then some logged leg `e` of chain `c` satisfies one of:

* the bundle declares `c`, every call is delivered with source chain `c`, `e` was committed under
  the executing flow's id, and the executed bundle's hash preimage is `e`'s
  (`abi.encode(c, e.bundleBytes)`);
* keccak collides on the executing leg's commit preimage and `e`'s (`CommitPreimageClash`);
* keccak collides on the executed bundle's hash preimage and `e`'s (`BundlePreimageClash`).

This replaces `AtomicSourceBinding.Properties.atomic_source_bound`, which concluded
`declared h = c` from a premise saying exactly that. Here the premise is about the vouching chain
only, the conclusion is about the identity `_executeCalls` hands out, and the gap between them is
the gate, the two keccak preimages and the encoding (`abiEncode_inj`). -/
def Properties.AtomicSenderIsVouchingChainOrLoggedClash : Prop :=
  ∀ (D : Dest) (st st' : HandlerState) (caller : Address) (B : List UInt8)
    (fin : AtomicFinalityProof) (b : Bundle) (ds : List Delivery),
    ExecutesAtomic D st caller B fin b st' ds →
    ∀ (i : ℕ) (c : UInt256) (p : ImtProof), LegAt fin i (executedHash D B b) c p →
    ∀ log : List CommittedLeg, HonestVouching D c log →
      ∃ e ∈ log,
        (b.sourceChainId = c ∧ (∀ d ∈ ds, d.sourceChainId = c) ∧ e.flowId = fin.flow.flowId ∧
            executedPreimage B b = e.preimage c)
          ∨ CommitPreimageClash D.keccak fin.flow.flowId (executedHash D B b) c e
          ∨ BundlePreimageClash D.keccak B b c e

/-- **THE EXECUTED BYTES ARE THE COMMITTED BYTES, OR A LOGGED CLASH.** The headline with the EVM
length bounds on the two byte strings (memory and calldata are far below `2^256` bytes): the first
disjunct then says the destination ran exactly the bytes chain `c` hashed when it committed `e`. -/
def Properties.AtomicExecutesCommittedBytesOrLoggedClash : Prop :=
  ∀ (D : Dest) (st st' : HandlerState) (caller : Address) (B : List UInt8)
    (fin : AtomicFinalityProof) (b : Bundle) (ds : List Delivery),
    ExecutesAtomic D st caller B fin b st' ds →
    ∀ (i : ℕ) (c : UInt256) (p : ImtProof), LegAt fin i (executedHash D B b) c p →
    ∀ log : List CommittedLeg, HonestVouching D c log →
    B.length < 256 ^ 32 → (∀ e ∈ log, e.bundleBytes.length < 256 ^ 32) →
      ∃ e ∈ log,
        (b.sourceChainId = c ∧ (∀ d ∈ ds, d.sourceChainId = c) ∧ e.flowId = fin.flow.flowId ∧
            B = e.bundleBytes)
          ∨ CommitPreimageClash D.keccak fin.flow.flowId (executedHash D B b) c e
          ∨ BundlePreimageClash D.keccak B b c e

/-- **BOUNDED FORM.** The headline with its clash disjuncts turned into premises: keccak is
injective on the two named pairs, for every leg of the vouching chain's log. Then the delivered
source chain is the vouching chain. This is the explicitly bounded no-collision premise
ASSUMPTIONS.md asks for; it is satisfiable (`AtomicSourceBoundWitness`). -/
def Properties.AtomicSenderIsVouchingChainOn : Prop :=
  ∀ (D : Dest) (st st' : HandlerState) (caller : Address) (B : List UInt8)
    (fin : AtomicFinalityProof) (b : Bundle) (ds : List Delivery),
    ExecutesAtomic D st caller B fin b st' ds →
    ∀ (i : ℕ) (c : UInt256) (p : ImtProof), LegAt fin i (executedHash D B b) c p →
    ∀ log : List CommittedLeg, HonestVouching D c log →
    (∀ e ∈ log, Set.InjOn D.keccak
      {commitPreimage D.keccak fin.flow.flowId (executedHash D B b),
        commitPreimage D.keccak e.flowId (e.bundleHash D.keccak c)}) →
    (∀ e ∈ log, Set.InjOn D.keccak {executedPreimage B b, e.preimage c}) →
      b.sourceChainId = c ∧ ∀ d ∈ ds, d.sourceChainId = c

/-- **THE PREMISE, SPLIT.** A verifier sound for chain `c`'s tree, and a tree holding only the
commit values of chain `c`'s log, give honest vouching by `c`. -/
def Properties.HonestVouchingOfSoundVerifier : Prop :=
  ∀ (D : Dest) (tree : UInt256 → Set UInt256) (c : UInt256) (log : List CommittedLeg),
    VerifierSoundFor D tree c → TreeHoldsOnlyLog D.keccak tree c log → HonestVouching D c log

/-- The ideal verifier is sound for its tree, at every chain. -/
def Properties.IdealVerifierSound : Prop :=
  ∀ (D : Dest) (tree : UInt256 → Set UInt256) (c : UInt256),
    D.verifyInclusion = idealVerifier tree → VerifierSoundFor D tree c

/-! ## The register -/

/-- **A SOURCE CHAIN DETERMINED BY THE HASH NEEDS A HASH BLIND TO THE BUNDLE.** The original topic
takes `declared : Hash → Chain`, "the `sourceChainId` field baked into bundle hash `h`". Suppose some
map `declared` recovers the chain from every bundle hash `keccak(abi.encode(s, B))`. Then that
keccak gives every bundle of one chain the same hash, whatever its bytes: on `bytes32`, the map
`s ↦ keccak(abi.encode(s, B₀))` is injective and so onto, which leaves no room for a second hash
per chain. Every replay guard keyed by the bundle hash would then confuse all of a chain's bundles.
So `declared` is not a quantity of the deployed contract, and the headline above does not use it. -/
def Properties.DeclaredOfHashForcesBundleBlindHash : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (declared : UInt256 → UInt256),
    (∀ (s : UInt256) (B : List UInt8), declared (keccak (abiEncode s.val B)) = s) →
      ∀ (s : UInt256) (B B' : List UInt8), keccak (abiEncode s.val B) = keccak (abiEncode s.val B')

/-! ## Witnesses and countermodels -/

/-- **THE HEADLINE'S PREMISES HOLD TOGETHER, AND ITS CLASHES ARE NOT TAUTOLOGIES.** For every
keccak there is a successful `executeAtomicBundle` whose vouching leg is leg `0`, declared on
chain `c`, with chain `c` vouching honestly against a one-leg log `[e]`, delivering at least one
call; neither clash holds on `e`, the bounded premises hold, and every call is delivered with
source chain `c`. -/
def Properties.AtomicSourceBoundWitness : Prop :=
  ∀ keccak : List UInt8 → UInt256,
    ∃ (D : Dest) (st st' : HandlerState) (caller : Address) (B : List UInt8)
      (fin : AtomicFinalityProof) (b : Bundle) (ds : List Delivery) (c : UInt256) (p : ImtProof)
      (e : CommittedLeg),
      D.keccak = keccak ∧ ExecutesAtomic D st caller B fin b st' ds ∧
      LegAt fin 0 (executedHash D B b) c p ∧ HonestVouching D c [e] ∧
      ¬ CommitPreimageClash keccak fin.flow.flowId (executedHash D B b) c e ∧
      ¬ BundlePreimageClash keccak B b c e ∧
      Set.InjOn keccak {commitPreimage keccak fin.flow.flowId (executedHash D B b),
        commitPreimage keccak e.flowId (e.bundleHash keccak c)} ∧
      Set.InjOn keccak {executedPreimage B b, e.preimage c} ∧
      ds ≠ [] ∧ b.sourceChainId = c ∧ ∀ d ∈ ds, d.sourceChainId = c

/-- **COUNTERMODEL: WITHOUT HONEST VOUCHING, ANY CHAIN IMPERSONATES ANY OTHER.** For every keccak
and every two distinct chains, `s` declared and `c` vouching, there is a successful
`executeAtomicBundle`:

* the flow's only leg declares chain `c` (`legSourceChainIds = [c]`), and its proof names `c`;
* chain `c`'s tree holds the commit value of a bundle that declares `s`, so the gate accepts;
* every call is delivered with source chain `s`;
* the declared chain `s` vouches for nothing: no proof naming `s` is accepted;
* reading chain `c` as honest, against any log, forces a clash with one of the log's legs.

So the gate does not bind the declared chain to the chain that vouched, and a collision is not
needed (the statement holds for every keccak). This is the contract-level form of
`AtomicSourceBinding.Properties.atomic_source_unbound_without_honest`. The threat model of
`_verifyBundle` ("chains are not malicious") excludes chain `c`; nothing on the atomic path does. -/
def Properties.MisbehavingLegChainImpersonates : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (s c : UInt256), s ≠ c →
    ∃ (D : Dest) (st st' : HandlerState) (caller : Address) (B : List UInt8)
      (fin : AtomicFinalityProof) (b : Bundle) (ds : List Delivery) (p : ImtProof),
      D.keccak = keccak ∧ ExecutesAtomic D st caller B fin b st' ds ∧
      LegAt fin 0 (executedHash D B b) c p ∧ fin.flow.legSourceChainIds = [c] ∧
      b.sourceChainId = s ∧ ds ≠ [] ∧ (∀ d ∈ ds, d.sourceChainId = s) ∧
      (∀ (q : ImtProof) (v deadline sl : UInt256), q.sourceChainId = s →
        ¬ D.verifyInclusion q v deadline sl) ∧
      ∀ log : List CommittedLeg, HonestVouching D c log →
        ∃ e ∈ log, CommitPreimageClash keccak fin.flow.flowId (executedHash D B b) c e ∨
          BundlePreimageClash keccak B b c e

/-- **THE BUNDLE-HASH CLASH CANNOT BE DROPPED.** A successful execution whose vouching chain `c`
vouches honestly against `[e]`, whose bundle declares another chain, and on which the
commit-preimage clash is false: only the bundle-hash clash holds. The keccak maps every input to
`0`. This is the case the original's `declared : Hash → Chain` rules out by construction. -/
def Properties.BundlePreimageClashFires : Prop :=
  ∃ (D : Dest) (st st' : HandlerState) (caller : Address) (B : List UInt8)
    (fin : AtomicFinalityProof) (b : Bundle) (ds : List Delivery) (c : UInt256) (p : ImtProof)
    (e : CommittedLeg),
    ExecutesAtomic D st caller B fin b st' ds ∧ LegAt fin 0 (executedHash D B b) c p ∧
    HonestVouching D c [e] ∧ b.sourceChainId ≠ c ∧ ds ≠ [] ∧ (∀ d ∈ ds, d.sourceChainId ≠ c) ∧
    ¬ CommitPreimageClash D.keccak fin.flow.flowId (executedHash D B b) c e ∧
    BundlePreimageClash D.keccak B b c e

/-- **THE COMMIT-VALUE CLASH CANNOT BE DROPPED.** A successful execution whose vouching chain `c`
vouches honestly against `[e]`, whose bundle declares another chain, and on which the bundle-hash
clash is false (the two bundle hashes differ): only the commit-preimage clash holds. The keccak
maps every 96-byte input, so every commit preimage, to `0`, and reads any other input's leading
word. -/
def Properties.CommitPreimageClashFires : Prop :=
  ∃ (D : Dest) (st st' : HandlerState) (caller : Address) (B : List UInt8)
    (fin : AtomicFinalityProof) (b : Bundle) (ds : List Delivery) (c : UInt256) (p : ImtProof)
    (e : CommittedLeg),
    ExecutesAtomic D st caller B fin b st' ds ∧ LegAt fin 0 (executedHash D B b) c p ∧
    HonestVouching D c [e] ∧ b.sourceChainId ≠ c ∧ ds ≠ [] ∧ (∀ d ∈ ds, d.sourceChainId ≠ c) ∧
    CommitPreimageClash D.keccak fin.flow.flowId (executedHash D B b) c e ∧
    ¬ BundlePreimageClash D.keccak B b c e

/-! ## The vouching chain's run -/

/-- **A DEPLOYED SEND PATH VOUCHES HONESTLY.** Along any run of the deployed `InteropCenter` and
flow manager from fresh storage (`Contracts.InteropCenter.Reach deployed`), if the destination's
verifier accepts on that chain only commit values of its committed legs, then the chain vouches
honestly against the legs its center dispatched. This discharges `HonestVouching` from the
`Dispatch` model plus the tree link `AcceptsOnlyCommittedLegs`. -/
def Properties.DispatchRunVouchesHonestly : Prop :=
  ∀ (D : Dest) (P : Contracts.InteropCenter.Params) (S : Contracts.InteropCenter.State),
    Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed P Contracts.InteropCenter.init S →
    P.keccak = D.keccak → AcceptsOnlyCommittedLegs D P S →
      HonestVouching D P.chainId (dispatchLegs P S)

/-- **A SUCCESSFUL ATOMIC EXECUTION RUNS A DISPATCH OF THE VOUCHING CHAIN, OR A LOGGED CLASH.** Let
the vouching leg's chain run the deployed send path (`Reach deployed P init S`, `P.chainId` the
leg's declared chain), with the tree link `AcceptsOnlyCommittedLegs`. Then some atomic dispatch `d`
of that run, whose bundle carries no native value and was built with `sourceChainId = P.chainId`,
satisfies one of: the executed bundle declares `P.chainId`, every call is delivered with that
chain, `d` was sent under the executing flow's id, and the executed bundle's hash preimage is
`d`'s; or a clash on `d`'s two named preimages. -/
def Properties.AtomicExecutionRunsADispatchedBundleOrLoggedClash : Prop :=
  ∀ (D : Dest) (P : Contracts.InteropCenter.Params) (S : Contracts.InteropCenter.State),
    Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed P Contracts.InteropCenter.init S →
    P.keccak = D.keccak → AcceptsOnlyCommittedLegs D P S →
    ∀ (st st' : HandlerState) (caller : Address) (B : List UInt8) (fin : AtomicFinalityProof)
      (b : Bundle) (ds : List Delivery),
      ExecutesAtomic D st caller B fin b st' ds →
      ∀ (i : ℕ) (p : ImtProof), LegAt fin i (executedHash D B b) P.chainId p →
        ∃ d ∈ S.log, d.isAtomic = true ∧ Contracts.InteropCenter.Validated d.bundle ∧
          d.bundle.sourceChainId = P.chainId ∧
          ((b.sourceChainId = P.chainId ∧ (∀ x ∈ ds, x.sourceChainId = P.chainId) ∧
              d.atomicSend.flowId = fin.flow.flowId ∧
              executedPreimage B b = Contracts.InteropCenter.bundlePreimage P d.bundle)
            ∨ CommitPreimageClash D.keccak fin.flow.flowId (executedHash D B b) P.chainId
                ⟨d.atomicSend.flowId, P.enc d.bundle⟩
            ∨ BundlePreimageClash D.keccak B b P.chainId ⟨d.atomicSend.flowId, P.enc d.bundle⟩)

/-- **THE EXECUTED BUNDLE IS THE DISPATCHED BUNDLE, OR A LOGGED CLASH.** As above, with the ABI
decoder inverting the encoder on the run's dispatched bundles (`SOL-ABI`, the premise of
`InteropCenter` `ClaimedBundleValidatedOrCollision`) and the EVM length bounds. The first disjunct
then says the destination decoded and ran exactly a bundle the vouching chain dispatched
atomically: same bytes, same flow, no native value, source chain the vouching chain. -/
def Properties.AtomicExecutionRunsTheDispatchedBundleOrLoggedClash : Prop :=
  ∀ (D : Dest) (P : Contracts.InteropCenter.Params) (S : Contracts.InteropCenter.State),
    Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed P Contracts.InteropCenter.init S →
    P.keccak = D.keccak → AcceptsOnlyCommittedLegs D P S →
    (∀ d ∈ S.log, D.decode (P.enc d.bundle) = some d.bundle) →
    (∀ d ∈ S.log, (P.enc d.bundle).length < 256 ^ 32) →
    ∀ (st st' : HandlerState) (caller : Address) (B : List UInt8) (fin : AtomicFinalityProof)
      (b : Bundle) (ds : List Delivery),
      ExecutesAtomic D st caller B fin b st' ds → B.length < 256 ^ 32 →
      ∀ (i : ℕ) (p : ImtProof), LegAt fin i (executedHash D B b) P.chainId p →
        ∃ d ∈ S.log, d.isAtomic = true ∧
          ((b = d.bundle ∧ B = P.enc d.bundle ∧ d.atomicSend.flowId = fin.flow.flowId ∧
              Contracts.InteropCenter.Validated b ∧ b.sourceChainId = P.chainId ∧
              ∀ x ∈ ds, x.sourceChainId = P.chainId)
            ∨ CommitPreimageClash D.keccak fin.flow.flowId (executedHash D B b) P.chainId
                ⟨d.atomicSend.flowId, P.enc d.bundle⟩
            ∨ BundlePreimageClash D.keccak B b P.chainId ⟨d.atomicSend.flowId, P.enc d.bundle⟩)

/-- **THE RUN-LEVEL PREMISES HOLD TOGETHER.** For every keccak: one atomic dispatch on chain `324`
of the deployed `InteropCenter` (sender `1`, salt `1`, one zero-value direct call, the `Dispatch`
witness encoder), and a destination that accepts on chain `324` exactly that leg's commit value
and decodes the dispatched bytes back. Every premise of
`AtomicExecutionRunsTheDispatchedBundleOrLoggedClash` holds; the bundle executes, its vouching leg
names chain `324`, neither clash holds on the dispatch, and the executed bundle is the dispatched
one. -/
def Properties.DispatchRunWitness : Prop :=
  ∀ keccak : List UInt8 → UInt256,
    ∃ (P : Contracts.InteropCenter.Params) (D : Dest) (S : Contracts.InteropCenter.State)
      (st st' : HandlerState) (caller : Address) (B : List UInt8) (fin : AtomicFinalityProof)
      (b : Bundle) (ds : List Delivery) (p : ImtProof) (d : Contracts.InteropCenter.Dispatch),
      P.keccak = keccak ∧
      Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed P
        Contracts.InteropCenter.init S ∧
      P.keccak = D.keccak ∧ AcceptsOnlyCommittedLegs D P S ∧
      (∀ d' ∈ S.log, D.decode (P.enc d'.bundle) = some d'.bundle) ∧
      (∀ d' ∈ S.log, (P.enc d'.bundle).length < 256 ^ 32) ∧
      ExecutesAtomic D st caller B fin b st' ds ∧ B.length < 256 ^ 32 ∧
      LegAt fin 0 (executedHash D B b) P.chainId p ∧
      d ∈ S.log ∧ d.isAtomic = true ∧ b = d.bundle ∧ ds ≠ [] ∧
      ¬ CommitPreimageClash D.keccak fin.flow.flowId (executedHash D B b) P.chainId
        ⟨d.atomicSend.flowId, P.enc d.bundle⟩ ∧
      ¬ BundlePreimageClash D.keccak B b P.chainId ⟨d.atomicSend.flowId, P.enc d.bundle⟩

end Contracts.L2InteropHandler.AtomicSourceFaithful
