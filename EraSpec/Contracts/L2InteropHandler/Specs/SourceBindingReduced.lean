import EraSpec.Contracts.InteropCenter.Specs.Dispatch
import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashPinned
import EraSpec.Protocol.InteropAtomicity.Specs.OncePerLeg

/-!
# Model: the atomic path's source binding, traced to the vouching chain's code

Source paths are relative to `l1-contracts/contracts/` in the pinned era-contracts tree
(`c67894b9`).

**This file is definitions only.** The statements are in
`EraSpec.Contracts.L2InteropHandler.Properties.SourceBindingReduced`, the proofs in
`EraSpec.Contracts.L2InteropHandler.Proofs.SourceBindingReduced`.

## What was open

`AttackVectors.AtomicSourceBinding.Properties.atomic_source_bound`
(`Properties/AtomicSourceBinding.lean`) concludes `declared h = c` from
`HonestCommits : ∀ c h, commit h ∈ tree c → declared h = c`. That premise is the conclusion,
quantified, so the result says nothing. Its `declared : Hash → Chain` also treats the bundle hash
as if it determined the source chain, which is global keccak injectivity. This file replaces the
premise with the code of the chain whose tree vouches, and the injectivity with pinned
collisions.

## The destination: what is checked, and what is not

`L2InteropHandler.executeAtomicBundle(_bundle, _finality)` (`L2InteropHandler.sol:49-100`, in
`interop/interop-handler/`) gets the bundle hash from `_getBundleData`
(`InteropHandlerBase.sol:242-251`):

    interopBundle = abi.decode(_bundle, (InteropBundle));                       // :247
    bundleHash = InteropDataEncoding.encodeInteropBundleHash(
        interopBundle.sourceChainId, _bundle);                                  // :249

so the hash is `keccak(abi.encode(interopBundle.sourceChainId, _bundle))`
(`InteropDataEncoding.sol:11-13`), with the source chain read from the bundle itself. The source
check `_validateBundleDestinationContext(bundleHash, interopBundle, interopBundle.sourceChainId)`
(`L2InteropHandler.sol:57`) compares that field with itself. `requireFlowFinalized`
(`AtomicFlowManager.sol:105-131`) then needs some leg `i` of the flow with
`legBundleHashes[i] == bundleHash` (`:123`, `:130`), and an inclusion proof of
`commitValue(flow.flowId, legBundleHashes[i])` against the IMT root of chain
`legSourceChainIds[i]` (`:124-128`). Nothing compares `legSourceChainIds[i]` with
`interopBundle.sourceChainId`. Yet that field is what `_executeCalls` hands to every recipient as
the caller's chain: `sender: InteroperableAddress.formatEvmV1(_sourceChainId, interopCall.from)`
(`L2InteropHandler.sol:92`, `InteropHandlerBase.sol:284`).

The source says why this is enough. `AtomicInteropProof.sol:107-110`: "it bakes in the
chain-specific `bundleHash`, so a leg's commit value can only be inserted into its own source
chain's tree, and the membership check below can only pass against that chain". And
`atomic-interop/README.md:49-50`: "A `commitValue` can only exist in its true source chain's
tree, so inclusion is self-binding". This file makes that argument a theorem about the vouching
chain's code.

`executedPreimage` and `executedHash` are the handler's computation. Because `dec` is any function,
they cover every byte string a caller can submit, canonical or not.

## The vouching chain: the three links of `Protocol/LocalHonesty.lean`, as one model

Chain `c` runs the deployed code. Its send side is one state, `SourceState`. It holds the
center's salt flags, the flow manager's `_state`, the ghost dispatch log
(`Contracts.InteropCenter.State`, topic `Dispatch`), and the commitment tree's list state
(`Contracts.InteropCommitmentTree.Tree`). One step is one transaction:

* `sendAtomic` / `sendPublic` — `InteropCenter._sendBundle` through `_dispatchBundle`
  (`interop/InteropCenter.sol:464-586, 639-659`), as in `Contracts.InteropCenter.Step.send`. In
  the atomic branch it also makes `AtomicFlowManager.append`'s tree insert
  (`AtomicFlowManager.sol:97-99`): `Contracts.AppendPath.AppendSucceeds` is the manager's `Unset`
  guard (`:93`) plus every check of `IndexedMerkleTree.insert`, with the deployed five-hop search
  (`common/libraries/IndexedMerkleTree.sol:60-106`). `Contracts.InteropCenter.Step` omitted that
  insert as a reject-only check. Here it is tracked, because the tree is what the destination
  reads.
* `authorize` / `claim` — `authorizeRefund` and `claimRefund` on one leg
  (`AtomicFlowManager.sol:155-161`, `:165-180`), with their proof checks omitted.
* `initL2` — `L2InteropCommitmentTree.initL2` (`atomic-interop/L2InteropCommitmentTree.sol:47-50`).
  `IndexedMerkleTree.setup` reverts once the tree has a leaf (`IndexedMerkleTree.sol:43-45`).
* `foreignAppend` — a direct call of `append` from an account other than the center. With
  `onlyInteropCenter` (`AtomicFlowManager.sol:76-79, 92`) it never succeeds. The switch
  `Checks.onlyInteropCenter` turns that guard off for the countermodel.

This is LocalHonesty's chain, now with the code in it:

1. `L2InteropCommitmentTree.insert` reverts unless the caller is the manager
   (`L2InteropCommitmentTree.sol:54`), and the tree's only other mutator is `initL2`. So the tree
   changes only inside `append`.
2. `append` is `onlyInteropCenter`, and the center calls it only at `InteropCenter.sol:650`,
   inside `_dispatchBundle`. So every tree insert is a dispatch.
3. That dispatch keys the leg by `bundleHash = encodeInteropBundleHash(block.chainid,
   abi.encode(_bundle))` (`InteropCenter.sol:643-644`): the first word of the hash preimage is the
   chain's own `block.chainid`, `P.chainId`. The bundle's field `sourceChainId` is also
   `block.chainid` (`InteropCenter.sol:500`, `FormedBy.source`). The source-chain conclusion below
   uses only the preimage's first word.

The center's `nonReentrant` (`InteropCenter.sol:217, 266`) and the argument in topic `Dispatch`
make a send one step. The indirect sender called inside it (`InteropCenter.sol:714`) can run
`authorizeRefund` and `claimRefund`, which do not touch the tree. It cannot reach `insert`
(link 1) or `append` (link 2).

## Model boundaries

* **The vouching chain executes this code (`PROTO-EVIDENCE`).** The premise of every positive
  result is that chain `P.chainId`'s state is reached from `sourceGenesis` by these steps. The
  destination authenticates a root that chain `c`'s batch committed. The premise says that root
  is the root of a state chain `c`'s deployed code reached: the proofs are correct and chain `c`
  is not malicious, as `_verifyBundle`'s comment puts it (`InteropHandlerBase.sol:298-301`).
  Other chains may run anything. Only the vouching chain is assumed.
* **One hash function and one encoder on every chain.** `P.keccak` and `P.enc` serve both the
  vouching chain's center and the destination's handler. The model does not assume either is
  injective. `cv` is the commit value `commitValue(flowId, bundleHash)`. The general results take
  any `cv`. `deployedCommitValue` is the deployed one,
  `uint256(keccak256(abi.encode(ATOMIC_COMMIT_LEAF_TAG, flowId, bundleHash)))`
  (`AtomicInteropProof.sol:100-102`).
* **Inherited omissions.** Everything topic `Dispatch` omits: fees, the pause flag, events, the
  destination checks, and attribute parsing. Everything topic `OncePerLeg` omits: the `FullMerkle`
  hash tree, upgrades (`OPS-CONFIG`), and `deadline`. The inclusion proof is not re-verified here.
  The gate form composes with `Contracts.Atomicity.Properties.FinalitySignalMeansMembershipOrBreak`
  for that.
-/

namespace Contracts.SourceBinding

open AttackVectors.BundleHashEncoding (abiEncode word HashCollision)
open Contracts.InteropCenter (Params Address Word Bundle Dispatch FormedBy Validated bundleHash
  bundlePreimage Checks)
open Contracts.AtomicFlowManager (AuthorizeGuard ClaimGuard LegState)
open Contracts.Atomicity (CommitValue)
open Contracts.Refund (Obligation CommitClash)
open Contracts.AppendPath (ChainState AppendSucceeds reseed)
open Contracts.InteropCommitmentTree (Tree setup)

/-! ## The vouching chain's send side -/

/-- **ONE SOURCE CHAIN'S SEND SIDE.** The center and its flow manager, as topic `Dispatch` models
them, and the commitment tree the manager inserts into. -/
structure SourceState where
  /-- `isInteropBundleSaltUsed` (`InteropCenter.sol:129`), the manager's `_state`
  (`AtomicFlowManager.sol:53`), and the ghost log of successful dispatches, oldest first. -/
  center : Contracts.InteropCenter.State
  /-- The commitment tree's list state (`L2InteropCommitmentTree.sol:33`,
  `IndexedMerkleTree.sol:30-34`). -/
  tree : Tree

/-- The manager and the tree: the state `Contracts.AppendPath` (topic `OncePerLeg`) reasons
about. -/
def SourceState.toChain (S : SourceState) : ChainState := ⟨S.center.manager, S.tree⟩

/-- After the genesis upgrade: fresh center and manager storage, and the tree seeded by
`initL2` with the `{0, 0, 0}` sentinel (`IndexedMerkleTree.sol:42-51`). -/
def sourceGenesis : SourceState := ⟨Contracts.InteropCenter.init, setup⟩

/-- The obligation an atomic dispatch commits. `append(flowId, bundleHash, ..)` runs on the chain
that dispatched, so the obligation's chain is that chain's `block.chainid`. -/
def dispatchObligation (P : Params) (d : Dispatch) : Obligation :=
  ⟨d.atomicSend.flowId, bundleHash P d.bundle, P.chainId⟩

/-- **THE APPEND LOG OF A DISPATCH LOG.** The obligations of its atomic dispatches, most recent
first, which is the order `Contracts.AppendPath.Steps` logs them in. -/
def appendLog (P : Params) (log : List Dispatch) : List Obligation :=
  ((log.filter Dispatch.isAtomic).map (dispatchObligation P)).reverse

/-- **ONE TRANSACTION ON THE VOUCHING CHAIN.** `K` says which of the guards are in place;
the deployed code is `Contracts.InteropCenter.deployed`. -/
inductive SourceStep (K : Checks) (P : Params) (cv : CommitValue) : SourceState → SourceState → Prop
  /-- `sendBundle` / `sendMessage` of a public bundle: the salt is marked
  (`InteropCenter.sol:479-483`) and the bundle is published to L1 (`InteropCenter.sol:657`). The
  tree is untouched. -/
  | sendPublic {S : SourceState} (d : Dispatch) :
      d.isAtomic = false →
      (K.saltCheck = true → S.center.saltUsed d.sender d.salt = false) →
      FormedBy P d →
      SourceStep K P cv S ⟨S.center.afterSend P d, S.tree⟩
  /-- `sendBundle` of an atomic bundle: the salt is marked, `_validateAtomicBundle` passes
  (`InteropCenter.sol:649`), and `append(flowId, bundleHash, _, hint)` (`InteropCenter.sol:650-655`)
  commits the leg in the manager (`AtomicFlowManager.sol:93-95`) and inserts its commit value
  through low leaf `low` (`AtomicFlowManager.sol:97-99`). -/
  | sendAtomic {S : SourceState} (d : Dispatch) (hint low : ℕ) :
      d.isAtomic = true →
      (K.saltCheck = true → S.center.saltUsed d.sender d.salt = false) →
      FormedBy P d →
      (K.atomicValueCheck = true → Validated d.bundle) →
      AppendSucceeds cv S.toChain d.atomicSend.flowId (bundleHash P d.bundle) hint low →
      SourceStep K P cv S
        ⟨S.center.afterSend P d,
          Contracts.InteropCommitmentTree.insert S.tree
            (cv d.atomicSend.flowId (bundleHash P d.bundle)) low⟩
  /-- `authorizeRefund` marking one `Committed` leg `Revertable` (`AtomicFlowManager.sol:158-159`).
  Its proof checks are omitted. -/
  | authorize {S : SourceState} (f h : Word) :
      AuthorizeGuard S.center.manager f h →
      SourceStep K P cv S
        ⟨{ S.center with manager := S.center.manager.set f h .Revertable }, S.tree⟩
  /-- `claimRefund` (`AtomicFlowManager.sol:170, 175`). The recovery calls are external. -/
  | claim {S : SourceState} (f h : Word) :
      ClaimGuard S.center.manager f h →
      SourceStep K P cv S
        ⟨{ S.center with manager := S.center.manager.set f h .Reverted }, S.tree⟩
  /-- `L2InteropCommitmentTree.initL2`. `setup` lets it through only on an empty tree. -/
  | initL2 {S : SourceState} :
      S.tree.leafCount = 0 →
      SourceStep K P cv S ⟨S.center, reseed S.tree⟩
  /-- `append(f, h, _, hint)` called directly by `caller`, not by the center. `onlyInteropCenter`
  rejects it. Without that guard it would commit the leg and insert its commit value, with no
  dispatch behind it. -/
  | foreignAppend {S : SourceState} (caller : Address) (f h : Word) (hint low : ℕ) :
      caller ≠ P.center →
      (K.onlyInteropCenter = true → caller = P.center) →
      AppendSucceeds cv S.toChain f h hint low →
      SourceStep K P cv S
        ⟨{ S.center with manager := S.center.manager.set f h .Committed },
          Contracts.InteropCommitmentTree.insert S.tree (cv f h) low⟩

/-- Every finite run of the vouching chain from `S`. -/
inductive SourceReach (K : Checks) (P : Params) (cv : CommitValue) (S : SourceState) :
    SourceState → Prop
  | refl : SourceReach K P cv S S
  | tail {T U : SourceState} : SourceReach K P cv S T → SourceStep K P cv T U →
      SourceReach K P cv S U

/-! ## The destination's computation -/

/-- **WHAT THE HANDLER HASHES FOR THE BYTES `x`** (`InteropHandlerBase.sol:247-249`):
`abi.encode(interopBundle.sourceChainId, _bundle)`, where `interopBundle = abi.decode(_bundle)`
is `dec x`. `claimRefund` hashes the same bytes the same way (`AtomicFlowManager.sol:166-167`,
`Contracts.InteropCenter.claimPreimage`). -/
def executedPreimage (dec : List UInt8 → Bundle) (x : List UInt8) : List UInt8 :=
  abiEncode (dec x).sourceChainId.val x

/-- **THE BUNDLE HASH THE DESTINATION COMPUTES** for the bytes `x` (`InteropHandlerBase.sol:249`).
`executeAtomicBundle` passes it to `requireFlowFinalized`, which needs it to be one of the flow's
`legBundleHashes` (`AtomicFlowManager.sol:123`). -/
def executedHash (keccak : List UInt8 → Word) (dec : List UInt8 → Bundle) (x : List UInt8) : Word :=
  keccak (executedPreimage dec x)

/-! ## The pinned breaks

Each names its inputs from the instance: the presented leg `(f, h)`, the presented bytes `x`, and
the vouching chain's own logs. None is an unpinned "some collision exists". The witnesses in
the property file show that each can be false, and that each can hold alone. -/

/-- **THE COMMIT VALUE IS THE TREE'S ZERO SENTINEL.** `0` is a key of every tree from genesis
on (`IndexedMerkleTree.sol:47-50`). `IndexedMerkleTree.verifyInclusion`
(`IndexedMerkleTree.sol:133-145`) has no `_value == 0` check, unlike `verifyNonInclusion`
(`IndexedMerkleTree.sol:160-162`). So a zero commit value is "included" in every chain's tree.
With the deployed commit value this is a keccak preimage of `0` for the named input
`abi.encode(TAG, f, h)`. -/
def SentinelHit (cv : CommitValue) (f h : Word) : Prop := cv f h = 0

/-- **THE COMMIT VALUE CLASHES WITH THAT OF A LEG THE CHAIN APPENDED.** `cv` collides on the
presented `(f, h)` and on the `(flowId, bundleHash)` of an obligation in the chain's own append
log. For the deployed commit value this is a keccak collision on the two named
`abi.encode(TAG, flowId, bundleHash)` preimages
(`Contracts.SourceBinding.Properties.CommitClashIsKeccakClash`). -/
def LoggedCommitClash (P : Params) (cv : CommitValue) (S : SourceState) (f h : Word) : Prop :=
  ∃ o ∈ appendLog P S.center.log, CommitClash cv ⟨f, h, P.chainId⟩ o

/-- **KECCAK COLLIDES ON THE TWO BUNDLE-HASH PREIMAGES.** The handler's preimage of the
presented bytes and the center's preimage of the logged atomic dispatch that committed the leg
`(f, h)` differ, and hash to the same bundle hash `h`. -/
def LoggedBundleClash (P : Params) (S : SourceState) (dec : List UInt8 → Bundle) (x : List UInt8)
    (f h : Word) : Prop :=
  ∃ d ∈ S.center.log, d.isAtomic = true ∧ d.atomicSend.flowId = f ∧ bundleHash P d.bundle = h ∧
    HashCollision P.keccak (executedPreimage dec x) (bundlePreimage P d.bundle)

/-- **A PINNED BREAK OF THE ATOMIC PATH'S SOURCE BINDING**, for the bytes `x` presented under
flow `f` with bundle hash `h`, against chain `P.chainId`'s state `S`. -/
def SourceBindingBreak (P : Params) (cv : CommitValue) (S : SourceState)
    (dec : List UInt8 → Bundle) (x : List UInt8) (f h : Word) : Prop :=
  SentinelHit cv f h ∨ LoggedCommitClash P cv S f h ∨ LoggedBundleClash P S dec x f h

/-! ## The deployed commit value -/

/-- `abi.encode(ATOMIC_COMMIT_LEAF_TAG, flowId, bundleHash)` (`AtomicInteropProof.sol:101`): the
tag's word, then the two `bytes32` words. `ATOMIC_COMMIT_LEAF_TAG` is the constant `bytes4`
`bytes4(keccak256("AtomicInterop.commit.v1"))` (`atomic-interop/IAtomicInterop.sol:91-94`). Its
ABI word is the four bytes followed by 28 zero bytes. The results take any fixed `tag`. -/
def commitPreimage (tag : List UInt8) (f b : Word) : List UInt8 := tag ++ (word f.val ++ word b.val)

/-- `AtomicInteropProof.commitValue` (`:100-102`): keccak of `commitPreimage`. -/
def deployedCommitValue (keccak : List UInt8 → Word) (tag : List UInt8) : CommitValue :=
  fun f b => keccak (commitPreimage tag f b)

/-- **THE THREE BREAKS, FOR THE DEPLOYED COMMIT VALUE, AS EVENTS OF `keccak` ALONE.** A keccak
preimage of `0`; a keccak collision on two named commit-value preimages; a keccak collision on two
named bundle-hash preimages. -/
def KeccakEvent (P : Params) (tag : List UInt8) (S : SourceState) (dec : List UInt8 → Bundle)
    (x : List UInt8) (f h : Word) : Prop :=
  P.keccak (commitPreimage tag f h) = 0
    ∨ (∃ o ∈ appendLog P S.center.log,
        HashCollision P.keccak (commitPreimage tag f h) (commitPreimage tag o.flowId o.bundleHash))
    ∨ LoggedBundleClash P S dec x f h

end Contracts.SourceBinding
