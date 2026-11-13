import EraSpec.Contracts.L2InteropHandler.Specs.AtomicSourceBindingStrong

/-!
# Properties: the atomic path's source binding, derived from one tree and named collisions

Statements about `EraSpec.Contracts.L2InteropHandler.Specs.AtomicSourceBindingStrong`. Proofs are
in `EraSpec.Contracts.L2InteropHandler.Proofs.AtomicSourceBindingStrong`.

These replace `Properties.atomic_source_bound` (topic `AtomicSourceBinding`), whose premise
`HonestCommits` is its conclusion quantified, and whose `declared : Hash → Chain` assumes the
bundle hash determines the source chain.

* **Check (1) by call site** (`DestContextCheckBySite`): on the atomic site the validator's first
  check holds of every bundle, so the validator is its two other checks; on the public site it
  forces the bundle's `sourceChainId` to be the proof's chain. One bundle passes the atomic site
  and fails the public one.
* **The binding, from the one tree that vouched** (headline,
  `AtomicSourceBoundToVouchingTreeOrLoggedClash`): if chain `P`'s tree holds only its own
  center's legs, and it holds the commit value of the bytes `x` presented with decoded source
  chain `src`, then `src` is chain `P` and `x` are exactly the bytes of an atomic dispatch of
  `P`'s log with the same flow id — or the presented commit value is the tree's sentinel, or
  keccak collides on a named pair of preimages (the presented commit or bundle-hash preimage,
  and that of a logged atomic dispatch). No hash is assumed to determine anything.
* **Bounded form** (`AtomicSourceBoundOn`): with keccak injective on the explicit finite lists of
  those preimages and a nonzero commit value, the binding holds outright.
* **From the deployed center** (`CenterRunTreeHoldsOwnLegs`,
  `AtomicSourceBoundOnCenterRunOrLoggedClash`): on a run of the deployed `InteropCenter`, the
  tree/manager link gives the honest-tree premise, and the dispatch found carries no native
  value and was built with `sourceChainId = block.chainid`.
* **At the flow gate** (`ExecutingBundleSenderChainIsItsLegChainOrLoggedClash`): the sender chain
  shown to recipients is the chain the flow declares for the executing leg.
* **What it rests on** (`ForeignCommitInTreeUnbindsSource`): a tree holding one foreign commit
  value lets bytes declaring chain `325` pass as vouched by chain `324`, with no collision on any
  named preimage. `AtomicSourceBindingStrongWitness` meets every premise on the honest run.

Topic `SourceBindingReduced` (namespace `Contracts.SourceBinding`) proves the same binding from
the vouching chain's whole source run, with links 1–2 derived rather than taken as
`TreeBackedByManager`. This topic adds the validator by call site, the decoded field used by both
the hash and the recipient's `sender`, and the flow-gate reading; its premise about the tree is
`TreeHoldsOwnLegs` for that one tree.
-/

namespace AttackVectors.AtomicSourceBinding

open AttackVectors.BundleHashEncoding (abiEncode HashCollision)
open Contracts.InteropCenter (Params Dispatch Word bundleHash bundlePreimage KeccakInjOn)

/-- **CHECK (1) BY CALL SITE.** On the atomic site (`L2InteropHandler.sol:57`) the validator is
exactly its destination-chain and base-token checks: its first check compares the bundle's
`sourceChainId` with itself. On a public site (`:92`, `:154`) it forces the bundle's
`sourceChainId` to be the proof's chain. And one bundle passes the atomic site and fails a public
one: the first check is the only difference. -/
def Properties.DestContextCheckBySite : Prop :=
  (∀ (chainId base : Word) (b : DestCtx),
      DestContextValid chainId base b (CtxSite.atomicSite.proofChainId b) ↔
        b.destinationChainId = chainId ∧ b.destinationBaseTokenAssetId = base) ∧
  (∀ (chainId base c : Word) (b : DestCtx),
      DestContextValid chainId base b ((CtxSite.publicSite c).proofChainId b) →
        b.sourceChainId = c) ∧
  ∃ (chainId base c : Word) (b : DestCtx),
    DestContextValid chainId base b (CtxSite.atomicSite.proofChainId b) ∧
      ¬ DestContextValid chainId base b ((CtxSite.publicSite c).proofChainId b)

/-- **THE ATOMIC PATH'S SOURCE BINDING, FROM THE ONE TREE THAT VOUCHED.** Let `T` be chain `P`'s
tree, holding only its own center's legs (`TreeHoldsOwnLegs`, for chain `P`'s log `log`). If `T`
holds `commitValue(f, encodeInteropBundleHash(src, x))` for the bytes `x` presented with decoded
source chain `src`, then:
* `src = P.chainId` — the chain in the identity `formatEvmV1(src, from)` handed to every
  recipient is the vouching chain — and `x` are the bytes `abi.encode(bundle)` of an atomic
  dispatch of `log` with flow id `f`; or
* the presented commit value is the tree's sentinel `0`; or
* keccak collides on two named preimages, for some atomic dispatch `d` of `log`: the presented
  commit preimage and `d`'s, or the presented bundle-hash preimage `abi.encode(src, x)` and `d`'s.
-/
def Properties.AtomicSourceBoundToVouchingTreeOrLoggedClash : Prop :=
  ∀ (P : Params) (tag : Word) (log : List Dispatch) (T : Set Word) (f src : Word)
    (x : List UInt8),
    TreeHoldsOwnLegs P tag log T →
    commitValue P.keccak tag f (destBundleHash P.keccak src x) ∈ T →
    (src = P.chainId ∧
        ∃ d ∈ log, d.isAtomic = true ∧ d.atomicSend.flowId = f ∧ x = P.enc d.bundle)
    ∨ commitValue P.keccak tag f (destBundleHash P.keccak src x) = 0
    ∨ ∃ d ∈ log, d.isAtomic = true ∧
        (HashCollision P.keccak (commitPreimage tag f (destBundleHash P.keccak src x))
            (commitPreimage tag d.atomicSend.flowId (bundleHash P d.bundle))
          ∨ HashCollision P.keccak (abiEncode src.val x) (bundlePreimage P d.bundle))

/-- **BOUNDED FORM.** As the headline, with the two collision disjuncts turned into keccak
injectivity on the explicit finite lists of the preimages compared — the presented one and those
of the log's atomic dispatches — and the sentinel disjunct into a nonzero commit value. -/
def Properties.AtomicSourceBoundOn : Prop :=
  ∀ (P : Params) (tag : Word) (log : List Dispatch) (T : Set Word) (f src : Word)
    (x : List UInt8),
    TreeHoldsOwnLegs P tag log T →
    commitValue P.keccak tag f (destBundleHash P.keccak src x) ∈ T →
    commitValue P.keccak tag f (destBundleHash P.keccak src x) ≠ 0 →
    KeccakInjOn P.keccak (commitPreimage tag f (destBundleHash P.keccak src x) ::
      (log.filter Dispatch.isAtomic).map
        (fun d => commitPreimage tag d.atomicSend.flowId (bundleHash P d.bundle))) →
    KeccakInjOn P.keccak (abiEncode src.val x ::
      (log.filter Dispatch.isAtomic).map (fun d => bundlePreimage P d.bundle)) →
    src = P.chainId ∧
      ∃ d ∈ log, d.isAtomic = true ∧ d.atomicSend.flowId = f ∧ x = P.enc d.bundle

/-- **THE DEPLOYED CENTER GIVES THE HONEST-TREE PREMISE.** Along a run of the deployed
`InteropCenter` on chain `P` from fresh storage, a tree backed by the manager (every key the
sentinel or the commit value of a leg not `Unset`) holds only the center's own legs: link 3, the
center's sole `append` call site computing the bundle hash with `block.chainid`
(`Contracts.InteropCenter.CommittedLegsAreValidatedDispatches`). -/
def Properties.CenterRunTreeHoldsOwnLegs : Prop :=
  ∀ (P : Params) (S : Contracts.InteropCenter.State) (tag : Word) (T : Set Word),
    Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed P
      Contracts.InteropCenter.init S →
    TreeBackedByManager P tag S T → TreeHoldsOwnLegs P tag S.log T

/-- **THE BINDING ON A DEPLOYED CENTER RUN.** As the headline, for the tree of a chain running the
deployed center, with the tree/manager link as the only premise about that tree. The dispatch found
also carries no native value (`_validateAtomicBundle`) and was built with
`sourceChainId = block.chainid` (`InteropCenter.sol:500`). -/
def Properties.AtomicSourceBoundOnCenterRunOrLoggedClash : Prop :=
  ∀ (P : Params) (S : Contracts.InteropCenter.State) (tag : Word) (T : Set Word) (f src : Word)
    (x : List UInt8),
    Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed P
      Contracts.InteropCenter.init S →
    TreeBackedByManager P tag S T →
    commitValue P.keccak tag f (destBundleHash P.keccak src x) ∈ T →
    (src = P.chainId ∧ ∃ d ∈ S.log, d.isAtomic = true ∧ d.atomicSend.flowId = f ∧
        x = P.enc d.bundle ∧ Contracts.InteropCenter.Validated d.bundle ∧
        d.bundle.sourceChainId = P.chainId)
    ∨ commitValue P.keccak tag f (destBundleHash P.keccak src x) = 0
    ∨ ∃ d ∈ S.log, d.isAtomic = true ∧
        (HashCollision P.keccak (commitPreimage tag f (destBundleHash P.keccak src x))
            (commitPreimage tag d.atomicSend.flowId (bundleHash P d.bundle))
          ∨ HashCollision P.keccak (abiEncode src.val x) (bundlePreimage P d.bundle))

/-- **AT THE FLOW GATE: THE SENDER CHAIN IS THE EXECUTING LEG'S DECLARED CHAIN.** If
`requireFlowFinalized` passed for the bytes `x` with decoded source chain `src`, and the flow
declares chain `P.chainId` for the executing leg, and that chain's tree holds only its own legs,
then `src = P.chainId` and `x` is one of its atomic dispatches with the flow's id — or the
sentinel, or a named collision as in the headline. -/
def Properties.ExecutingBundleSenderChainIsItsLegChainOrLoggedClash : Prop :=
  ∀ (P : Params) (tag : Word) (trees : Word → Set Word) (log : List Dispatch) (flowId src : Word)
    (x : List UInt8) (legs : List (Word × Word)),
    FlowGatePassed P.keccak tag trees flowId legs (destBundleHash P.keccak src x) →
    (destBundleHash P.keccak src x, P.chainId) ∈ legs →
    TreeHoldsOwnLegs P tag log (trees P.chainId) →
    (src = P.chainId ∧
        ∃ d ∈ log, d.isAtomic = true ∧ d.atomicSend.flowId = flowId ∧ x = P.enc d.bundle)
    ∨ commitValue P.keccak tag flowId (destBundleHash P.keccak src x) = 0
    ∨ ∃ d ∈ log, d.isAtomic = true ∧
        (HashCollision P.keccak (commitPreimage tag flowId (destBundleHash P.keccak src x))
            (commitPreimage tag d.atomicSend.flowId (bundleHash P d.bundle))
          ∨ HashCollision P.keccak (abiEncode src.val x) (bundlePreimage P d.bundle))

/-- **THE HONEST-TREE PREMISE IS THE WHOLE OF IT.** On chain `324` (`wParams`) with `wD1`'s atomic
leg dispatched (`wS1`), a tree that also holds one foreign commit value — that of bytes declaring
chain `325` — accepts those bytes: the presented commit value is in it and nonzero, the presented
sender chain is `325`, and keccak collides on no named pair of preimages. So all three disjuncts of
the headline fail, and the tree fails `TreeHoldsOwnLegs`. On the atomic path nothing else looks at
the declared chain: check (1) compares it to itself. -/
def Properties.ForeignCommitInTreeUnbindsSource : Prop :=
  commitValue Contracts.InteropCenter.wParams.keccak wTag 7
      (destBundleHash Contracts.InteropCenter.wParams.keccak 325 wForeignBytes) ∈ wForeignTree ∧
    commitValue Contracts.InteropCenter.wParams.keccak wTag 7
      (destBundleHash Contracts.InteropCenter.wParams.keccak 325 wForeignBytes) ≠ 0 ∧
    (325 : Word) ≠ Contracts.InteropCenter.wParams.chainId ∧
    (∀ d ∈ Contracts.InteropCenter.wS1.log, d.isAtomic = true →
      ¬ HashCollision Contracts.InteropCenter.wParams.keccak
          (commitPreimage wTag 7
            (destBundleHash Contracts.InteropCenter.wParams.keccak 325 wForeignBytes))
          (commitPreimage wTag d.atomicSend.flowId
            (bundleHash Contracts.InteropCenter.wParams d.bundle)) ∧
        ¬ HashCollision Contracts.InteropCenter.wParams.keccak
          (abiEncode (325 : Word).val wForeignBytes)
          (bundlePreimage Contracts.InteropCenter.wParams d.bundle)) ∧
    ¬ TreeHoldsOwnLegs Contracts.InteropCenter.wParams wTag Contracts.InteropCenter.wS1.log
      wForeignTree

/-- **EVERY PREMISE HOLDS ON THE HONEST RUN, AND THE COLLISIONS ARE FALSE ON IT.** On chain `324`
after `wD1`'s atomic leg of flow `7`: the run is a run of the deployed center; its tree `wTree`
is backed by the manager and holds only the center's legs; the destination is shown `wD1`'s bytes
with decoded source chain `324`, and the flow gate passes for them with that leg declared on
chain `324`; the commit value is in the tree and nonzero; keccak collides on no named pair of
preimages; and the two bounded injectivity premises of `AtomicSourceBoundOn` hold. -/
def Properties.AtomicSourceBindingStrongWitness : Prop :=
  Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed Contracts.InteropCenter.wParams
      Contracts.InteropCenter.init Contracts.InteropCenter.wS1 ∧
    TreeBackedByManager Contracts.InteropCenter.wParams wTag Contracts.InteropCenter.wS1 wTree ∧
    TreeHoldsOwnLegs Contracts.InteropCenter.wParams wTag Contracts.InteropCenter.wS1.log wTree ∧
    FlowGatePassed Contracts.InteropCenter.wParams.keccak wTag
      (fun c => if c = Contracts.InteropCenter.wParams.chainId then wTree else ∅) 7
      [(bundleHash Contracts.InteropCenter.wParams Contracts.InteropCenter.wD1.bundle,
        Contracts.InteropCenter.wParams.chainId)]
      (destBundleHash Contracts.InteropCenter.wParams.keccak
        Contracts.InteropCenter.wParams.chainId
        (Contracts.InteropCenter.wParams.enc Contracts.InteropCenter.wD1.bundle)) ∧
    commitValue Contracts.InteropCenter.wParams.keccak wTag 7
        (destBundleHash Contracts.InteropCenter.wParams.keccak
          Contracts.InteropCenter.wParams.chainId
          (Contracts.InteropCenter.wParams.enc Contracts.InteropCenter.wD1.bundle)) ∈ wTree ∧
    commitValue Contracts.InteropCenter.wParams.keccak wTag 7
        (destBundleHash Contracts.InteropCenter.wParams.keccak
          Contracts.InteropCenter.wParams.chainId
          (Contracts.InteropCenter.wParams.enc Contracts.InteropCenter.wD1.bundle)) ≠ 0 ∧
    (∀ d ∈ Contracts.InteropCenter.wS1.log, d.isAtomic = true →
      ¬ HashCollision Contracts.InteropCenter.wParams.keccak
          (commitPreimage wTag 7
            (destBundleHash Contracts.InteropCenter.wParams.keccak
              Contracts.InteropCenter.wParams.chainId
              (Contracts.InteropCenter.wParams.enc Contracts.InteropCenter.wD1.bundle)))
          (commitPreimage wTag d.atomicSend.flowId
            (bundleHash Contracts.InteropCenter.wParams d.bundle)) ∧
        ¬ HashCollision Contracts.InteropCenter.wParams.keccak
          (abiEncode Contracts.InteropCenter.wParams.chainId.val
            (Contracts.InteropCenter.wParams.enc Contracts.InteropCenter.wD1.bundle))
          (bundlePreimage Contracts.InteropCenter.wParams d.bundle)) ∧
    KeccakInjOn Contracts.InteropCenter.wParams.keccak
      (commitPreimage wTag 7
          (destBundleHash Contracts.InteropCenter.wParams.keccak
            Contracts.InteropCenter.wParams.chainId
            (Contracts.InteropCenter.wParams.enc Contracts.InteropCenter.wD1.bundle)) ::
        (Contracts.InteropCenter.wS1.log.filter Dispatch.isAtomic).map
          (fun d => commitPreimage wTag d.atomicSend.flowId
            (bundleHash Contracts.InteropCenter.wParams d.bundle))) ∧
    KeccakInjOn Contracts.InteropCenter.wParams.keccak
      (abiEncode Contracts.InteropCenter.wParams.chainId.val
          (Contracts.InteropCenter.wParams.enc Contracts.InteropCenter.wD1.bundle) ::
        (Contracts.InteropCenter.wS1.log.filter Dispatch.isAtomic).map
          (fun d => bundlePreimage Contracts.InteropCenter.wParams d.bundle))

end AttackVectors.AtomicSourceBinding
