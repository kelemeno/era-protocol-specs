import EraSpec.Protocol.InteropAtomicity.Specs.OncePerLeg
import EraSpec.Contracts.InteropCenter.Specs.Dispatch

/-!
# Model: when an atomic dispatch is enabled (liveness of the send path)

Source: era-contracts at the pin `c67894b9`. Paths are relative to `l1-contracts/contracts/`.

**This file is definitions only.** Statements are in
`EraSpec.Protocol.InteropAtomicity.Properties.DispatchLiveness`, proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.DispatchLiveness`.

The existing results on the send path are about safety: a salt dispatches once, a leg is
appended once, a commit value occupies one index (`Contracts.InteropCenter`, topic `Dispatch`;
`Contracts.AppendPath`, topic `OncePerLeg`). The positive side is unstated:

* `HintSearch` shows the deployed loop can make an honest insert revert
  (`HonestInsertRevertsAtDeployedFuel`) and that `leafCount` hops suffice, but not how many hops
  a given hint needs, nor that the shortfall can be made arbitrarily large.
* O1 notes that no result says an honest new dispatch avoids `ManagerLegAlreadyCommitted`.

This file adds the two notions those statements need, and one composed model.

## The hint search, counted

`IndexedMerkleTree.insert` (`common/libraries/IndexedMerkleTree.sol:60-106`) starts at the
caller's `_lowLeafIndex` and walks the sorted linked list (`:85-92`):

    for (uint256 attempts = 0; lowLeaf.nextValue != 0 && lowLeaf.nextValue < _value; ++attempts) {
        if (attempts == MAX_LOW_INDEX_SEARCH_ATTEMPTS) revert IMTLowLeafNextTooSmall(..);   // :86-88
        lowLeafIndex = lowLeaf.nextIndex;
        lowLeaf = self.leaves[lowLeafIndex];
    }

with `MAX_LOW_INDEX_SEARCH_ATTEMPTS = 5` (`common/Config.sol:66`). This is `lowSearch` with fuel
`maxLowIndexSearchAttempts` (`Contracts/L2InteropCommitmentTree/Specs/Model.lean`, topic
`HintSearch`). `hopsNeeded T v hint` counts the occupied leaves whose value lies strictly
between the hint's value and `v`: the sorted walk has to pass every one of them.
`ExactHint T v hint` is the hint at which the loop exits at once.

## One chain's send path, composed

`Contracts.InteropCenter.State` has the center's salt flags and the manager, but no tree: its
`send` step omits the tree insertion inside `append` (`Contracts/InteropCenter/Specs/Dispatch.lean`,
"Checks that only reject ... are omitted"). `Contracts.AppendPath.ChainState` has the manager and
the tree, but no center: its `append` step admits any `(flowId, bundleHash)`. A liveness
statement needs both, because the hint is the dispatch's own `lowNullifierIndex`
(`interop/InteropCenter.sol:650-655`) and the tree's checks are part of the send:

    // _sendBundle
    require(!isInteropBundleSaltUsed[msg.sender][_bundleAttributes.salt], ..);      // :479-482
    isInteropBundleSaltUsed[msg.sender][_bundleAttributes.salt] = true;              // :483
    ...
    (bundleHash, msgHash) = _dispatchBundle(bundle, _atomicSend);                    // :574
    // _dispatchBundle
    bundleHash = InteropDataEncoding.encodeInteropBundleHash(block.chainid, abi.encode(_bundle)); // :643-644
    if (_atomicSend.isAtomic) {
        _validateAtomicBundle(_bundle);                                              // :649
        IAtomicFlowManager(L2_ATOMIC_FLOW_MANAGER_ADDR).append({.., _lowNullifierIndex:
            _atomicSend.lowNullifierIndex});                                         // :650-655
    } else { msgHash = _sendBundleToL1(interopBundleBytes, _bundle.calls.length); }   // :657
    // AtomicFlowManager.append (atomic-interop/AtomicFlowManager.sol:87-102)
    if (_state[_flowId][_bundleHash] != LegState.Unset) revert ManagerLegAlreadyCommitted(..);  // :93
    _state[_flowId][_bundleHash] = LegState.Committed;                                           // :95
    (uint256 index, ) = IL2InteropCommitmentTree(commitmentTree()).insert(value, _lowNullifierIndex); // :97-99

`State` below is the product: the salt flags, `Contracts.AppendPath.ChainState` (manager and
tree), and the center's ghost dispatch log. Its steps are the deployed code only (all three
checks of `Contracts.InteropCenter.deployed`):

* `sendPublic`: a non-atomic `_sendBundle` (salt check and write, `FormedBy`, log).
* `sendAtomic`: an atomic `_sendBundle`: the salt check, `FormedBy`, `_validateAtomicBundle`, and
  `Contracts.AppendPath.AppendSucceeds` with the dispatch's own hint, i.e. the manager's `Unset`
  guard and every check of the tree's `insert`; it makes all the writes.
* `authorize`, `claim`: one leg of `authorizeRefund` (`AtomicFlowManager.sol:155-161`, proof
  checks dropped as in both component models) and `claimRefund` (`:169-175`).
* `initL2`: `L2InteropCommitmentTree.initL2` (`atomic-interop/L2InteropCommitmentTree.sol:47-50`),
  which `IndexedMerkleTree.setup` lets through only on an empty tree (`IndexedMerkleTree.sol:43-45`).

The `foreignAppend` step of `Contracts.InteropCenter.Step` is absent: under `deployed` its two
premises (`caller ≠ center` and `caller = center`) contradict, so it never fires. The two
projections (`Properties.DispatchRunProjectsToCenter`, `Properties.DispatchRunProjectsToAppendPath`)
carry every result of both component models to this one.

## What "enabled" means here

A step of this model is a transaction that does not revert **on the modelled checks**. The checks
`Contracts.InteropCenter` omits as reject-only (pause, destination registration, fees and
`msg.value`, attribute parsing, the indirect sender's own code) are not modelled here either. For
a liveness statement they are preconditions the sender controls (payment, a registered
destination) or protocol configuration (`OPS-CONFIG`, the pause flag); gas is `OPS-PROGRESS`. So
"the dispatch has a step" reads: once the sender pays, the destination is registered and the
center is not paused, nothing the run has done can make this transaction revert, except a pinned
collision.
-/

namespace Contracts.DispatchLiveness

open IMTAbstract
open Contracts.InteropCommitmentTree (Tree Valid lowSearch InsertGuard maxLowIndexSearchAttempts
  chainTree Reaches Initialized toAbs setup)
open Contracts.AppendPath (ChainState AppendSucceeds InsertSucceeds reseed)
open Contracts.InteropCenter (Params Dispatch FormedBy Validated bundleHash markSalt
  CrossSenderSaltClash BundleClash Address Word)
open Contracts.AtomicFlowManager (LegState AppendGuard AuthorizeGuard ClaimGuard)
open Contracts.Atomicity (Chain CommitValue)
open Contracts.Refund (Obligation CommitClash)

/-! ## The hint search, counted -/

/-- **THE HOPS A HINT NEEDS.** The occupied leaves whose value lies strictly between the hint's
value and `v`. The loop at `IndexedMerkleTree.sol:85-92` walks the sorted list from the hint, one
leaf per hop, and stops at the first leaf whose successor is not below `v`; so it must pass each
of these leaves. In a valid tree it hops exactly this many times
(`Properties.SearchSucceedsIffHopsWithinFuel`). -/
def hopsNeeded (T : Tree) (v : UInt256) (hint : ℕ) : ℕ :=
  ((Finset.range T.leafCount).filter
    (fun k => (T.leaf hint).value < (T.leaf k).value ∧ (T.leaf k).value < v)).card

/-- **THE EXACT HINT.** `hint` is an occupied leaf below `v` (`IMTLowLeafIndexOutOfBounds`,
`IMTLowLeafValueTooLarge`, `IndexedMerkleTree.sol:75-83`) at which the loop condition
`lowLeaf.nextValue != 0 && lowLeaf.nextValue < _value` (`:85`) is already false. An off-chain
sender computes it by reading the tree: it is the leaf holding the largest value below `v`
(`Properties.ExactHintExistsAndIsUnique`). -/
structure ExactHint (T : Tree) (v : UInt256) (hint : ℕ) : Prop where
  inBounds : hint < T.leafCount
  below : (T.leaf hint).value < v
  window : (T.leaf hint).nextValue = 0 ∨ v ≤ (T.leaf hint).nextValue

/-- `U` is `T` after exactly `m` guarded inserts: `Reaches`, counted. This is what other senders'
appends do to the tree between the moment a sender reads it to compute a hint and the moment its
own transaction lands. -/
inductive ReachesIn (T : Tree) : ℕ → Tree → Prop
  | refl : ReachesIn T 0 T
  | tail {m : ℕ} {U : Tree} (h : ReachesIn T m U) {v : UInt256} {low : ℕ}
      (hg : InsertGuard U v low) :
      ReachesIn T (m + 1) (Contracts.InteropCommitmentTree.insert U v low)

/-! ## One chain's send path, composed -/

/-- One source chain's send-path storage: the center's `isInteropBundleSaltUsed`
(`interop/InteropCenter.sol:129`), the manager's `_state` and the commitment tree's list state
(`Contracts.AppendPath.ChainState`), and the ghost log of successful dispatches, oldest first. -/
structure State where
  /-- `isInteropBundleSaltUsed[user][salt]` (`InteropCenter.sol:129`). -/
  saltUsed : Address → Word → Bool
  /-- The manager's `_state` and the tree's list state. -/
  chain : ChainState
  /-- Ghost: every successful dispatch, oldest first. -/
  log : List Dispatch

/-- After the genesis upgrade: no salt used, every leg `Unset`, the tree seeded with `setup`,
nothing dispatched. -/
def genesis : State := ⟨fun _ _ => false, Contracts.AppendPath.genesis, []⟩

/-- The center's view of the state: what `Contracts.InteropCenter` reasons about. -/
def State.center (X : State) : Contracts.InteropCenter.State := ⟨X.saltUsed, X.chain.mgr, X.log⟩

/-- The obligation an atomic dispatch commits on the chain `P.chainId` that ran it. -/
def legOf (P : Params) (d : Dispatch) : Obligation :=
  ⟨d.atomicSend.flowId, bundleHash P d.bundle, P.chainId⟩

/-- The value `append` inserts for a dispatch: `commitValue(flowId, bundleHash)`
(`AtomicFlowManager.sol:97`). -/
def commitValueOf (P : Params) (cv : CommitValue) (d : Dispatch) : UInt256 :=
  cv d.atomicSend.flowId (bundleHash P d.bundle)

/-- The obligations the run's atomic dispatches committed, most recent first: the log
`Contracts.AppendPath.Steps` keeps. -/
def appendLog (P : Params) (log : List Dispatch) : List Obligation :=
  ((log.filter Dispatch.isAtomic).map (legOf P)).reverse

/-- The state after a successful non-atomic `_sendBundle`: the salt is marked (`:483`), the
bundle is published to L1 (`:657`, not modelled as state), the log records `d`. -/
def State.afterPublic (X : State) (d : Dispatch) : State :=
  { X with saltUsed := markSalt X.saltUsed d.sender d.salt, log := X.log ++ [d] }

/-- The state after a successful atomic `_sendBundle` whose search landed on low leaf `low`: the
salt is marked, the leg is `Committed` and its commit value inserted through `low`
(`Contracts.AppendPath.ChainState.appended`), and the log records `d`. -/
def State.afterAtomic (P : Params) (cv : CommitValue) (X : State) (d : Dispatch) (low : ℕ) :
    State where
  saltUsed := markSalt X.saltUsed d.sender d.salt
  chain := X.chain.appended cv d.atomicSend.flowId (bundleHash P d.bundle) low
  log := X.log ++ [d]

/-- **ONE TRANSACTION OF THE DEPLOYED SEND PATH.** -/
inductive Step (P : Params) (cv : CommitValue) : State → State → Prop
  /-- `sendBundle` / `sendMessage` of a non-atomic bundle (`InteropCenter.sol:479-483`, `:498-546`,
  `:657`). -/
  | sendPublic {X : State} (d : Dispatch) :
      d.isAtomic = false → X.saltUsed d.sender d.salt = false → FormedBy P d →
      Step P cv X (X.afterPublic d)
  /-- `sendBundle` of an atomic bundle: the salt check, bundle formation, `_validateAtomicBundle`
  (`:649`) and the whole `append` (`AtomicFlowManager.sol:93-99`) with the dispatch's own hint,
  landing on low leaf `low`. -/
  | sendAtomic {X : State} (d : Dispatch) (low : ℕ) :
      d.isAtomic = true → X.saltUsed d.sender d.salt = false → FormedBy P d → Validated d.bundle →
      AppendSucceeds cv X.chain d.atomicSend.flowId (bundleHash P d.bundle)
        d.atomicSend.lowNullifierIndex low →
      Step P cv X (X.afterAtomic P cv d low)
  /-- One leg of `authorizeRefund` (`AtomicFlowManager.sol:155-161`); its proof checks dropped. -/
  | authorize {X : State} (f h : Word) : AuthorizeGuard X.chain.mgr f h →
      Step P cv X { X with chain := ⟨X.chain.mgr.set f h .Revertable, X.chain.tree⟩ }
  /-- `claimRefund` (`AtomicFlowManager.sol:169-175`). -/
  | claim {X : State} (f h : Word) : ClaimGuard X.chain.mgr f h →
      Step P cv X { X with chain := ⟨X.chain.mgr.set f h .Reverted, X.chain.tree⟩ }
  /-- `L2InteropCommitmentTree.initL2`; `setup` lets it through only on an empty tree. -/
  | initL2 {X : State} : X.chain.tree.leafCount = 0 →
      Step P cv X { X with chain := ⟨X.chain.mgr, reseed X.chain.tree⟩ }

/-- Reachability. -/
inductive Reach (P : Params) (cv : CommitValue) : State → State → Prop
  | refl {X : State} : Reach P cv X X
  | tail {X Y Z : State} : Reach P cv X Y → Step P cv Y Z → Reach P cv X Z

/-- **THE ATOMIC SEND IS ENABLED.** Some low leaf makes the composed `append` of `d`'s leg with
`d`'s own hint succeed. The center's own checks are separate premises of the statements. -/
def AtomicSendEnabled (P : Params) (cv : CommitValue) (X : State) (d : Dispatch) : Prop :=
  ∃ low, AppendSucceeds cv X.chain d.atomicSend.flowId (bundleHash P d.bundle)
    d.atomicSend.lowNullifierIndex low

/-- **WHAT CAN BLOCK AN HONEST ATOMIC DISPATCH: A PINNED CLASH WITH THE LOG.** Some atomic
dispatch `d'` of the run either already committed `d`'s very leg, which needs two distinct
dispatches with one leg (the cross-sender salt clash makes the two bundles equal; otherwise two
different bundles share a bundle hash), or has a commit value equal to `d`'s on a different
`(flowId, bundleHash)` (`CommitClash`, a keccak collision on the two named
`abi.encode(ATOMIC_COMMIT_LEAF_TAG, flowId, bundleHash)` preimages). Every disjunct names `d` and a
dispatch of the log. -/
def DispatchClash (P : Params) (cv : CommitValue) (log : List Dispatch) (d : Dispatch) : Prop :=
  ∃ d' ∈ log, d'.isAtomic = true ∧
    ((legOf P d' = legOf P d ∧ (CrossSenderSaltClash P d d' ∨ BundleClash P d.bundle d'.bundle))
      ∨ CommitClash cv (legOf P d) (legOf P d'))

/-- `d` with another hint: the same bundle and flow, `lowNullifierIndex := i`. -/
def withHint (d : Dispatch) (i : ℕ) : Dispatch :=
  { d with atomicSend := { d.atomicSend with lowNullifierIndex := i } }

/-! ## Witness data

Chain `324` with the honest toy keccak of `Contracts.InteropCenter.wParams` (the last 32 bytes as a
word), so that a bundle's hash is its user salt. -/

/-- Commit value `fun _ b => b`: the leg's commit value is its bundle hash. -/
def bundleCv : CommitValue := fun _ b => b

/-- A constant commit value: every two legs clash. -/
def constCv : CommitValue := fun _ _ => 1

/-- Sender `s`, salt `s`: an atomic leg of flow `7` with one direct zero-value call, hint `hint`. -/
def atomicDispatch (P : Params) (s : Address) (salt : Word) (hint : ℕ) : Dispatch :=
  ⟨s, [Contracts.InteropCenter.wDirect 0],
    Contracts.InteropCenter.wBundle P s salt [⟨5, s, 0, []⟩], ⟨7, hint, 100, true⟩⟩

/-- The honest send-path run: sender `1` dispatches an atomic leg (salt `1`, hint `0`). -/
def wX1 : State :=
  genesis.afterAtomic Contracts.InteropCenter.wParams bundleCv
    (atomicDispatch Contracts.InteropCenter.wParams 1 1 0) 0

/-- The next honest dispatch: sender `2`, salt `2`, with the exact hint `1` (the leaf holding `1`). -/
def wNext : Dispatch := atomicDispatch Contracts.InteropCenter.wParams 2 2 1

/-- `setup` after one insert of the value `1` through the sentinel. -/
def wOneInsertTree : Tree := Contracts.InteropCommitmentTree.insert setup 1 0

end Contracts.DispatchLiveness
