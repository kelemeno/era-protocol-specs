import EraSpec.Contracts.L2InteropHandler.Specs.SourceBindingReduced

/-!
# Properties: the atomic path's source binding, from the vouching chain's code

Statements about `EraSpec.Contracts.L2InteropHandler.Specs.SourceBindingReduced`. Proofs are in
`EraSpec.Contracts.L2InteropHandler.Proofs.SourceBindingReduced`.

## The reduction

`AttackVectors.AtomicSourceBinding.Properties.atomic_source_bound` takes
`HonestCommits` ("a chain's tree holds only commit values whose bundle hash declares that chain")
and concludes it at one point. Here nothing of the kind is assumed. The premises are:

1. **Chain `c = P.chainId` runs the deployed code.** Its state `S` is reached from
   `sourceGenesis` by `SourceStep deployed`. This is the `PROTO-EVIDENCE` premise, and it is about
   the vouching chain only: no other chain is assumed to be honest.
2. **The destination hashed the presented bytes `x` to `h`.** `executedHash P.keccak dec x = h`,
   as `_getBundleData` computes it (`InteropHandlerBase.sol:247-249`), for any decoder `dec`.
3. **The leg's commit value is a key of chain `c`'s tree.** `cv f h ∈ keys (toAbs S.tree)` is what
   an accepted inclusion proof establishes, up to a located tree break
   (`Contracts.Atomicity.Properties.FinalitySignalMeansMembershipOrBreak`). The gate form below
   composes the two.

The conclusion is that the source chain the bundle declares is `c`. That chain is the one
`_executeCalls` hands to every recipient (`L2InteropHandler.sol:92`,
`InteropHandlerBase.sol:284`). Otherwise there is a `SourceBindingBreak`: a zero (sentinel) commit
value, a commit-value clash with a leg `c` appended, or a keccak collision on the handler's
bundle-hash preimage and the center's preimage of the dispatch behind the leg. For the deployed
commit value all three are events of keccak alone, on named inputs
(`Properties.AtomicSourceBoundOrKeccakEvent`).

Stronger forms say the executed bytes are the dispatched bytes
(`Properties.ExecutedBytesAreDispatchedOrBreak`) and every caller identity is an account on `c`
that took part in the send (`Properties.ExecutedCallersAreSourceSendersOrBreak`). The source's
own claim, that a commit value "can only exist in its true source chain's tree", is
`Properties.CommitValueOnlyInItsSourceTreeOrBreak`. The gate form is
`Properties.GateBindsExecutingSourceOrBreak`.

## Where each link is used

* Links 1 and 2 of `Protocol/LocalHonesty.lean`: the tree changes only inside `append`, and
  `append` runs only inside a dispatch. `Properties.SourceRunProjectsToAppendPath` makes the run a
  `Contracts.AppendPath` run whose append log is the run's atomic dispatches. So every key is `0`
  or a dispatched leg's commit value (`Properties.SourceKeysAreDispatchedCommitValues`), and a
  presented leg whose commit value is a nonzero key is that dispatched leg or clashes with it
  (`Contracts.AppendPath.Properties.KeyPinsAppendedLegOrClash`).
* Link 3: the center hashes with `block.chainid` (`InteropCenter.sol:644`). The dispatched leg's
  bundle hash is `keccak(abi.encode(c, abi.encode(bundle)))`. Equal hashes give equal preimages
  or a keccak collision. Equal preimages give the source chain, because `abi.encode(uint256, bytes)`
  starts with the `uint256` word (the head half of `BundleHashEncoding.abiDecode_abiEncode`). They
  also give the bytes, because the rest determines the `bytes` argument with no length bound
  (`Contracts.InteropCenter.abiEncode_right_inj`).

## Non-vacuity and countermodels

`Properties.SourceBindingWitness` is an honest run of the deployed code with an authorized atomic
leg and a public bundle. It meets every premise above, including those of the bounded and
round-trip forms, with the deployed commit value. Every break and every keccak event is false on
it. `Properties.SentinelBreakFires`, `Properties.CommitClashBreakFires` and
`Properties.BundleClashBreakFires` each make the declared source differ from the vouching chain,
with exactly one kind of break holding. So no disjunct can be dropped.
`Properties.CommitValueOnlyInItsSourceTreeWitness` puts one commit value in two honest chains'
trees and shows the break is what explains it.
`Properties.WithoutOnlyInteropCenterSourceUnbound` shows that the vouching chain's code is
load-bearing. Without `onlyInteropCenter`, chain `324`'s tree vouches for a bundle declaring
chain `325`, and there is no break of any kind. `Properties.GateSourceBindingWitness` meets the
gate form's premises with the inclusion break and the source-binding break both false.
-/

namespace Contracts.SourceBinding

open MerkleSpec IMTAbstract
open AttackVectors.BundleHashEncoding (HashCollision)
open Contracts.InteropCenter (Params Address Word Bundle Dispatch FormedBy Validated bundleHash
  Checks deployed withoutOnlyInteropCenter KeccakInjOn bundlePreimages)
open Contracts.AtomicFlowManager (LegState)
open Contracts.Atomicity (CommitValue FlowHash System Flow FlowLeg GateEvidence ExecutedViaBy
  InclusionBreak Wf)
open Contracts.Refund (Obligation CommitClash CommitValueInjOn)
open Contracts.InteropCommitmentTree (toAbs LeafHash)

/-! ## The composed run refines both component models -/

/-- **A RUN OF THE VOUCHING CHAIN IS A RUN OF THE CENTER MODEL.** Forget the tree. Then every
step is a `Contracts.InteropCenter.Step` with the same checks, or leaves the center unchanged
(`initL2`). So every result of topic `Dispatch` holds of the center half: salt uniqueness,
validated atomic dispatches, and distinct bundle hashes up to pinned clashes. -/
def Properties.SourceRunProjectsToCenterReach : Prop :=
  ∀ (K : Checks) (P : Params) (cv : CommitValue) (S T : SourceState),
    SourceReach K P cv S T → Contracts.InteropCenter.Reach K P S.center T.center

/-- **A RUN OF THE VOUCHING CHAIN IS A RUN OF THE APPEND PATH.** With `onlyInteropCenter` in place
(whatever the other two checks), forget the salt flags and the dispatch log. Then a run from
genesis is a `Contracts.AppendPath.Steps` run (topic `OncePerLeg`) on chain `P.chainId`, and its
append log is the run's atomic dispatches, most recent first. So every result of that topic holds
of the manager and tree. -/
def Properties.SourceRunProjectsToAppendPath : Prop :=
  ∀ (K : Checks) (P : Params) (cv : CommitValue) (S : SourceState),
    K.onlyInteropCenter = true → SourceReach K P cv sourceGenesis S →
      Contracts.AppendPath.Steps cv P.chainId Contracts.AppendPath.genesis S.toChain
        (appendLog P S.center.log)

/-! ## LocalHonesty, derived rather than assumed -/

/-- **EVERY KEY OF THE VOUCHING CHAIN'S TREE IS THE SENTINEL OR A DISPATCHED LEG'S COMMIT VALUE.**
On every run of the deployed code from genesis, a value is a key of the tree iff it is `0` or the
commit value of an atomic dispatch of the chain's own center. This is links 1 and 2 of
`Protocol/LocalHonesty.lean`, proved for this model. Link 3 is the definition of `bundleHash P`:
the leg of a dispatch `d` is keyed by `keccak(abi.encode(block.chainid, abi.encode(d.bundle)))`
(`InteropCenter.sol:643-644`). -/
def Properties.SourceKeysAreDispatchedCommitValues : Prop :=
  ∀ (P : Params) (cv : CommitValue) (S : SourceState),
    SourceReach deployed P cv sourceGenesis S →
      ∀ v : Word, v ∈ keys (toAbs S.tree) ↔
        v = 0 ∨ ∃ d ∈ S.center.log, d.isAtomic = true
          ∧ cv d.atomicSend.flowId (bundleHash P d.bundle) = v

/-! ## The source binding -/

/-- **THE ATOMIC PATH'S SOURCE BINDING, OR A PINNED BREAK (HEADLINE).** Take a run of the deployed
code on chain `P.chainId` from genesis. This premise says the vouching chain executes honestly
(`PROTO-EVIDENCE`); no other chain is assumed. Take bytes `x` that the destination decodes with
`dec` and hashes to `h` (`InteropHandlerBase.sol:247-249`), presented as a leg of flow `f`.
Suppose the leg's commit value `cv f h` is a key of the chain's tree, which is what the gate's
inclusion proof shows. Then the source chain the bundle declares, the chain `_executeCalls` gives
every recipient, is `P.chainId`. Otherwise a `SourceBindingBreak` holds: the commit value is the
sentinel `0`; or it clashes with that of a leg this chain appended; or keccak collides on the
handler's preimage of `x` and the center's preimage of the dispatch that committed `(f, h)`.
This holds for every commit-value function, keccak and encoder. -/
def Properties.AtomicSourceBoundOrBreak : Prop :=
  ∀ (P : Params) (cv : CommitValue) (S : SourceState), SourceReach deployed P cv sourceGenesis S →
    ∀ (dec : List UInt8 → Bundle) (x : List UInt8) (f h : Word), executedHash P.keccak dec x = h →
      cv f h ∈ keys (toAbs S.tree) →
        (dec x).sourceChainId = P.chainId ∨ SourceBindingBreak P cv S dec x f h

/-- **THE EXECUTED BYTES ARE THE BYTES THE VOUCHING CHAIN DISPATCHED, OR A PINNED BREAK.** Same
premises. Then some atomic dispatch of the chain's center committed exactly the leg `(f, h)`, and
`x` is that dispatch's `abi.encode(bundle)`. Its bundle was formed by `_sendBundle` on this chain
and carries no native value. The declared source is `P.chainId`. Otherwise a
`SourceBindingBreak` holds. -/
def Properties.ExecutedBytesAreDispatchedOrBreak : Prop :=
  ∀ (P : Params) (cv : CommitValue) (S : SourceState), SourceReach deployed P cv sourceGenesis S →
    ∀ (dec : List UInt8 → Bundle) (x : List UInt8) (f h : Word), executedHash P.keccak dec x = h →
      cv f h ∈ keys (toAbs S.tree) →
        (∃ d ∈ S.center.log, d.isAtomic = true ∧ d.atomicSend.flowId = f ∧ bundleHash P d.bundle = h
            ∧ x = P.enc d.bundle ∧ (dec x).sourceChainId = P.chainId ∧ FormedBy P d
            ∧ Validated d.bundle)
          ∨ SourceBindingBreak P cv S dec x f h

/-- **EVERY CALLER IDENTITY A RECIPIENT SEES IS THE VOUCHING CHAIN AND A REAL SENDER ON IT, OR A
PINNED BREAK.** Same premises, and the decoder inverts the encoder on the chain's own dispatched
bundles (`abi.decode` after `abi.encode`, `SOL-ABI`). Then the executed bundle is exactly the
bundle of an atomic dispatch of the chain's center, and it declares `P.chainId`. Each of its
calls carries no native value. Each call's `from` is either the dispatch's `msg.sender` (a direct
call, `InteropCenter.sol:742-749`) or an indirect sender contract that `msg.sender` called through
(`:739`). So the identity `formatEvmV1(sourceChainId, from)` handed to each recipient
(`InteropHandlerBase.sol:284`) is an account on the vouching chain that took part in the send.
Otherwise a `SourceBindingBreak` holds. -/
def Properties.ExecutedCallersAreSourceSendersOrBreak : Prop :=
  ∀ (P : Params) (cv : CommitValue) (S : SourceState), SourceReach deployed P cv sourceGenesis S →
    ∀ (dec : List UInt8 → Bundle), (∀ d ∈ S.center.log, dec (P.enc d.bundle) = d.bundle) →
    ∀ (x : List UInt8) (f h : Word), executedHash P.keccak dec x = h →
      cv f h ∈ keys (toAbs S.tree) →
        (∃ d ∈ S.center.log, d.isAtomic = true ∧ d.atomicSend.flowId = f ∧ dec x = d.bundle
            ∧ (dec x).sourceChainId = P.chainId
            ∧ ∀ k ∈ (dec x).calls, k.value = 0
                ∧ (k.fromAddr = d.sender
                    ∨ ∃ cs ∈ d.starters, cs.callAttributes.indirectCall = true
                        ∧ k.fromAddr = cs.target))
          ∨ SourceBindingBreak P cv S dec x f h

/-- **`HonestCommits`, RESTATED WITH A SATISFIABLE PREMISE.** The bounded form. No injectivity of
any function is assumed. The premises rule out exactly the three breaks, on the inputs the
instance names: the presented commit value is nonzero; `cv` separates the presented leg from the
chain's own append log; and keccak separates the handler's preimage from the chain's own
bundle-hash preimages (at most one per dispatch). Then the declared source is the vouching
chain. -/
def Properties.AtomicSourceBoundOn : Prop :=
  ∀ (P : Params) (cv : CommitValue) (S : SourceState), SourceReach deployed P cv sourceGenesis S →
    ∀ (dec : List UInt8 → Bundle) (x : List UInt8) (f h : Word), executedHash P.keccak dec x = h →
      cv f h ≠ 0 →
      CommitValueInjOn cv (⟨f, h, P.chainId⟩ :: appendLog P S.center.log) →
      KeccakInjOn P.keccak (executedPreimage dec x :: bundlePreimages P S.center.log) →
      cv f h ∈ keys (toAbs S.tree) → (dec x).sourceChainId = P.chainId

/-- **A DISPATCHED LEG'S COMMIT VALUE SITS ONLY IN ITS OWN CHAIN'S TREE, OR A PINNED BREAK.** This
is the claim of `AtomicInteropProof.sol:107-110` ("a leg's commit value can only be inserted into
its own source chain's tree, and the membership check below can only pass against that chain")
and of `atomic-interop/README.md:49-50`, for honest chains. Chains `c` and `c'` run the deployed
code with one keccak, encoder, center address and commit value. Let `d` be an atomic dispatch of
chain `c`. Suppose `d`'s commit value is a key of chain `c'`'s tree. Then `c' = c`, or a pinned
break holds against chain `c'`'s run, with `d`'s own bytes presented. -/
def Properties.CommitValueOnlyInItsSourceTreeOrBreak : Prop :=
  ∀ (keccak : List UInt8 → Word) (enc : Bundle → List UInt8) (center : Address) (cv : CommitValue)
    (c c' : Word) (S S' : SourceState),
    SourceReach deployed ⟨c, center, enc, keccak⟩ cv sourceGenesis S →
    SourceReach deployed ⟨c', center, enc, keccak⟩ cv sourceGenesis S' →
    ∀ d ∈ S.center.log, d.isAtomic = true →
      cv d.atomicSend.flowId (bundleHash ⟨c, center, enc, keccak⟩ d.bundle)
          ∈ keys (toAbs S'.tree) →
        c' = c
          ∨ SourceBindingBreak ⟨c', center, enc, keccak⟩ cv S' (fun _ => d.bundle) (enc d.bundle)
              d.atomicSend.flowId (bundleHash ⟨c, center, enc, keccak⟩ d.bundle)

/-! ## The deployed commit value: every break is a keccak event on named inputs -/

/-- **A COMMIT-VALUE CLASH IS A KECCAK COLLISION ON TWO NAMED PREIMAGES.** For the deployed commit
value `keccak(abi.encode(TAG, flowId, bundleHash))`, two obligations clash iff keccak collides on
their two `abi.encode` preimages. The tag is fixed and both words are 32 bytes, so the preimages
differ exactly when the `(flowId, bundleHash)` pairs do. -/
def Properties.CommitClashIsKeccakClash : Prop :=
  ∀ (keccak : List UInt8 → Word) (tag : List UInt8) (o o' : Obligation),
    CommitClash (deployedCommitValue keccak tag) o o' ↔
      HashCollision keccak (commitPreimage tag o.flowId o.bundleHash)
        (commitPreimage tag o'.flowId o'.bundleHash)

/-- **FOR THE DEPLOYED COMMIT VALUE, A BREAK IS A KECCAK EVENT.** `SourceBindingBreak` with
`cv = deployedCommitValue` is equivalent to `KeccakEvent`. It is a keccak preimage of `0`, or a
keccak collision on two named commit-value preimages, or one on two named bundle-hash
preimages. -/
def Properties.BreakIsKeccakEvent : Prop :=
  ∀ (P : Params) (tag : List UInt8) (S : SourceState) (dec : List UInt8 → Bundle) (x : List UInt8)
    (f h : Word),
    SourceBindingBreak P (deployedCommitValue P.keccak tag) S dec x f h ↔
      KeccakEvent P tag S dec x f h

/-- **THE HEADLINE FOR THE DEPLOYED COMMIT VALUE: THE SOURCE IS BOUND, OR KECCAK BROKE ON NAMED
INPUTS.** As `Properties.AtomicSourceBoundOrBreak`, with
`commitValue = keccak(abi.encode(TAG, flowId, bundleHash))` for any fixed tag. Every way the
binding can fail is a property of the one function `keccak` on byte strings the instance names. -/
def Properties.AtomicSourceBoundOrKeccakEvent : Prop :=
  ∀ (P : Params) (tag : List UInt8) (S : SourceState),
    SourceReach deployed P (deployedCommitValue P.keccak tag) sourceGenesis S →
    ∀ (dec : List UInt8 → Bundle) (x : List UInt8) (f h : Word), executedHash P.keccak dec x = h →
      deployedCommitValue P.keccak tag f h ∈ keys (toAbs S.tree) →
        (dec x).sourceChainId = P.chainId ∨ KeccakEvent P tag S dec x f h

/-! ## At the gate -/

/-- **THE ATOMICITY GATE BINDS THE EXECUTING BUNDLE'S SOURCE, OR A BREAK IS LOCATED.** Let bundle
bytes `x` execute through `requireFlowFinalized` as leg `leg` of flow `F`, on the evidence `ev`.
So `ExecutedViaBy` holds and `x`'s hash is `leg.bundleHash` (`AtomicFlowManager.sol:123`). The leg's
inclusion proof was checked against batch `(ev leg).1` of its declared chain `leg.chain`
(`:124-128`). Suppose that batch's tree is a state that `leg.chain` reached by running the
deployed code with `block.chainid = leg.chain` and the system's keccak and encoder (the
operational link the fixed history leaves open, and `PROTO-EVIDENCE` for that one chain). Then the
bundle declares `leg.chain`. Otherwise the gate's inclusion proof for that leg carries a located
`InclusionBreak`, or a `SourceBindingBreak` holds against that chain's run. The destination never
compares the two chain ids; this is why it need not. -/
def Properties.GateBindsExecutingSourceOrBreak : Prop :=
  ∀ (hN : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (Sys : System)
    (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaBy hN z0 hl cv fh Sys F ev leg →
    ∀ (center : Address) (enc : Bundle → List UInt8) (keccak : List UInt8 → Word)
      (dec : List UInt8 → Bundle) (x : List UInt8),
      executedHash keccak dec x = leg.bundleHash →
      ∀ S : SourceState, SourceReach deployed ⟨leg.chain, center, enc, keccak⟩ cv sourceGenesis S →
        S.tree = Sys.tree leg.chain (ev leg).1 →
          (dec x).sourceChainId = leg.chain
            ∨ InclusionBreak hN z0 hl Sys leg.chain (ev leg).1 (ev leg).2
            ∨ SourceBindingBreak ⟨leg.chain, center, enc, keccak⟩ cv S dec x F.flowId leg.bundleHash

/-! ## Non-vacuity, firing witnesses and the countermodel -/

/-- **EVERY PREMISE HOLDS ON AN HONEST RUN, AND NO BREAK DOES.** Chain `324` runs the deployed code
with the deployed commit-value shape. It dispatches an atomic leg of flow `7` and a public bundle,
and the leg is then authorized for refund. The destination presents the atomic bundle's own bytes.
The decoder round trip, the bounded premises, the key membership and the nonzero commit value all
hold. The declared source is the vouching chain. No `SourceBindingBreak` and no `KeccakEvent`
holds. So the premises of every headline above are jointly satisfiable, and the break disjunct is
no tautology. -/
def Properties.SourceBindingWitness : Prop :=
  ∃ (P : Params) (tag : List UInt8) (S : SourceState) (dec : List UInt8 → Bundle) (x : List UInt8)
    (f h : Word),
    SourceReach deployed P (deployedCommitValue P.keccak tag) sourceGenesis S
      ∧ (∀ d ∈ S.center.log, dec (P.enc d.bundle) = d.bundle)
      ∧ executedHash P.keccak dec x = h
      ∧ deployedCommitValue P.keccak tag f h ∈ keys (toAbs S.tree)
      ∧ deployedCommitValue P.keccak tag f h ≠ 0
      ∧ CommitValueInjOn (deployedCommitValue P.keccak tag)
          (⟨f, h, P.chainId⟩ :: appendLog P S.center.log)
      ∧ KeccakInjOn P.keccak (executedPreimage dec x :: bundlePreimages P S.center.log)
      ∧ (dec x).sourceChainId = P.chainId
      ∧ ¬ SourceBindingBreak P (deployedCommitValue P.keccak tag) S dec x f h
      ∧ ¬ KeccakEvent P tag S dec x f h
      ∧ (∃ d ∈ S.center.log, d.isAtomic = false)
      ∧ (∃ d ∈ S.center.log, d.isAtomic = true ∧ d.atomicSend.flowId = f
          ∧ S.center.manager.legState d.atomicSend.flowId (bundleHash P d.bundle) = .Revertable)

/-- **THE SENTINEL DISJUNCT IS NEEDED.** Chain `324` appends a leg with a nonzero commit value.
The commit value is `0` on the presented leg of another flow, and the genesis sentinel `0` is
still a key of the tree. Bytes declaring chain `325` then pass, and the only break is the
sentinel. -/
def Properties.SentinelBreakFires : Prop :=
  ∃ (P : Params) (cv : CommitValue) (S : SourceState) (dec : List UInt8 → Bundle) (x : List UInt8)
    (f h : Word),
    SourceReach deployed P cv sourceGenesis S ∧ executedHash P.keccak dec x = h
      ∧ cv f h ∈ keys (toAbs S.tree) ∧ (dec x).sourceChainId ≠ P.chainId
      ∧ SentinelHit cv f h ∧ ¬ LoggedCommitClash P cv S f h ∧ ¬ LoggedBundleClash P S dec x f h

/-- **THE COMMIT-CLASH DISJUNCT IS NEEDED.** With a constant commit value, chain `324` appends one
leg. Bytes declaring chain `325`, under the same flow, then have a commit value that is a key of
chain `324`'s tree. The only break is the commit-value clash with the appended leg. -/
def Properties.CommitClashBreakFires : Prop :=
  ∃ (P : Params) (cv : CommitValue) (S : SourceState) (dec : List UInt8 → Bundle) (x : List UInt8)
    (f h : Word),
    SourceReach deployed P cv sourceGenesis S ∧ executedHash P.keccak dec x = h
      ∧ cv f h ∈ keys (toAbs S.tree) ∧ (dec x).sourceChainId ≠ P.chainId
      ∧ ¬ SentinelHit cv f h ∧ LoggedCommitClash P cv S f h ∧ ¬ LoggedBundleClash P S dec x f h

/-- **THE BUNDLE-CLASH DISJUNCT IS NEEDED.** With a constant keccak, chain `324` appends one leg.
Bytes declaring chain `325` hash to the same bundle hash. The only break is the keccak collision on
the handler's preimage and the center's preimage of that leg's dispatch. These two preimages
differ in their first word. -/
def Properties.BundleClashBreakFires : Prop :=
  ∃ (P : Params) (cv : CommitValue) (S : SourceState) (dec : List UInt8 → Bundle) (x : List UInt8)
    (f h : Word),
    SourceReach deployed P cv sourceGenesis S ∧ executedHash P.keccak dec x = h
      ∧ cv f h ∈ keys (toAbs S.tree) ∧ (dec x).sourceChainId ≠ P.chainId
      ∧ ¬ SentinelHit cv f h ∧ ¬ LoggedCommitClash P cv S f h ∧ LoggedBundleClash P S dec x f h

/-- **TWO HONEST CHAINS, ONE COMMIT VALUE IN BOTH TREES: THE BREAK IS NEEDED.** Chains `324` and
`325` both run the deployed code under a constant commit value. Each appends a leg of flow `7`.
Chain `324`'s leg then has its commit value in chain `325`'s tree too. The chains differ, and the
break that `Properties.CommitValueOnlyInItsSourceTreeOrBreak` names is the commit-value clash with
chain `325`'s own leg. So its premises hold with `c' ≠ c`, and its break disjunct can fire. Topic
`OncePerLeg` calls this cross-chain clash harmless for once-per-leg. For the source binding, it
is exactly a pinned break. -/
def Properties.CommitValueOnlyInItsSourceTreeWitness : Prop :=
  ∃ (keccak : List UInt8 → Word) (enc : Bundle → List UInt8) (center : Address) (cv : CommitValue)
    (c c' : Word) (S S' : SourceState) (d : Dispatch),
    SourceReach deployed ⟨c, center, enc, keccak⟩ cv sourceGenesis S
      ∧ SourceReach deployed ⟨c', center, enc, keccak⟩ cv sourceGenesis S'
      ∧ d ∈ S.center.log ∧ d.isAtomic = true
      ∧ cv d.atomicSend.flowId (bundleHash ⟨c, center, enc, keccak⟩ d.bundle) ∈ keys (toAbs S'.tree)
      ∧ c' ≠ c
      ∧ LoggedCommitClash ⟨c', center, enc, keccak⟩ cv S' d.atomicSend.flowId
          (bundleHash ⟨c, center, enc, keccak⟩ d.bundle)

/-- **COUNTERMODEL: WITHOUT `onlyInteropCenter`, THE VOUCHING CHAIN BINDS NOTHING.** In the code
without `AtomicFlowManager.sol:76-79`, an account other than the center appends a leg directly.
Chain `324`'s tree then holds the commit value of bytes that declare chain `325`. The keccak and
the commit value are honest on every input involved, and no break of any kind holds. So the
headline's premise that the vouching chain runs the deployed code is load-bearing. -/
def Properties.WithoutOnlyInteropCenterSourceUnbound : Prop :=
  ∃ (P : Params) (cv : CommitValue) (S : SourceState) (dec : List UInt8 → Bundle) (x : List UInt8)
    (f h : Word),
    SourceReach withoutOnlyInteropCenter P cv sourceGenesis S ∧ executedHash P.keccak dec x = h
      ∧ cv f h ∈ keys (toAbs S.tree) ∧ (dec x).sourceChainId ≠ P.chainId
      ∧ ¬ SourceBindingBreak P cv S dec x f h

/-- **THE GATE FORM'S PREMISES HOLD TOGETHER, WITH BOTH BREAKS FALSE.** For every node hash, padding
constant and leaf hash: a well-formed history whose chain-`0` batch tree is the tree of an honest
run of chain `0`. That run dispatches the leg of a one-leg flow. The leg executes through the gate
on its honest inclusion proof, from the dispatched bytes. The declared source is the leg's chain.
The inclusion proof carries no break, and no `SourceBindingBreak` holds. -/
def Properties.GateSourceBindingWitness : Prop :=
  ∀ (hN : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (Sys : System) (F : Flow) (ev : GateEvidence)
      (leg : FlowLeg) (center : Address) (enc : Bundle → List UInt8) (keccak : List UInt8 → Word)
      (dec : List UInt8 → Bundle) (x : List UInt8) (S : SourceState),
      Wf Sys ∧ ExecutedViaBy hN z0 hl cv fh Sys F ev leg
        ∧ executedHash keccak dec x = leg.bundleHash
        ∧ SourceReach deployed ⟨leg.chain, center, enc, keccak⟩ cv sourceGenesis S
        ∧ S.tree = Sys.tree leg.chain (ev leg).1
        ∧ (dec x).sourceChainId = leg.chain
        ∧ ¬ InclusionBreak hN z0 hl Sys leg.chain (ev leg).1 (ev leg).2
        ∧ ¬ SourceBindingBreak ⟨leg.chain, center, enc, keccak⟩ cv S dec x F.flowId leg.bundleHash

end Contracts.SourceBinding
