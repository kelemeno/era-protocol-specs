import EraSpec.Protocol.NativeValueLegs.Specs.LegConservation

/-!
# Model at head: runs of sends, refund authorizations, refund claims and other activity

Source: era-contracts `draft/v0.35.0` at `b17415d20`, as in `LegConservation`; paths are relative
to `l1-contracts/contracts/`.

**This file is definitions only.**  The statements are in
`EraSpec.Protocol.NativeValueLegs.Properties.LegConservationRuns` and are proved in
`EraSpec.Protocol.NativeValueLegs.Proofs.LegConservationRuns`.

`LegConservation` relates one collection and one refund of a bundle the caller supplies.  This file
puts them in a run of the source chain, where the refund names its bundle only by the bytes a
claimant passes, and binds each successful refund to the send that committed its leg.

## The leg state (`atomic-interop/AtomicFlowManager.sol`)

    // append (:104-173), called by the center's _dispatchBundle (InteropCenter.sol:742-746)
    if (_state[flowId][_bundleHash] != LegState.Unset) revert ManagerLegAlreadyCommitted(...); // :162-163
    _state[flowId][_bundleHash] = LegState.Committed;                                          // :166

    // authorizeRefund (:216-247): every Committed leg of the flow on this chain
    _state[_flow.flowId][h] = LegState.Revertable;                                             // :244

    // claimRefund (:250-265)
    InteropBundle memory bundle = abi.decode(_bundle, (InteropBundle));                        // :251
    bytes32 bundleHash = InteropDataEncoding.encodeInteropBundleHash(_bundle);                 // :252
    if (_state[_flowId][bundleHash] != LegState.Revertable) revert ManagerLegNotRevertable(...); // :254-257
    _state[_flowId][bundleHash] = LegState.Reverted;                                           // :260
    _recoverBundle(bundle);                                                                    // :262

The center hashes `keccak256(abi.encode(bundle))` (`InteropCenter.sol:690-692`,
`InteropDataEncoding.sol:14-16`); the claim hashes the bytes it is given.

## What is modelled

* `State` is the source chain's `World`, the manager's `_state`, and two ghost logs: every
  successful atomic send (`Sent`, with the route its collection took) and every successful claim
  (`Claimed`, with the bytes, the decoded bundle and the worlds before and after).
* `Step.send` is one successful atomic `sendBundle`/`sendMessage`: the bundle is formed under the
  deployed checks, its destination is not L1 (`AtomicBundleToL1NotSupported`,
  `InteropCenter.sol:552-553`), the collection is `collect` (`LegConservation`), and the leg is
  committed behind the `Unset` guard.  What the send does before the collection (the salt, the
  indirect calls' processing, the ZK fee) and after it (the fee accrual, the tree insert, the
  fee-units counter) is an arbitrary change of the world (`RegMono`, below).  The remaining checks
  of `append` (flow id, deadline, legs, source chains) only reject.
* `Step.authorize` moves one `Committed` leg to `Revertable`; its proof checks are omitted (more
  runs).  `Step.claim` is `claimRefund` on bytes `x`: the leg `(flowId, keccak x)` must be
  `Revertable`, `x` must decode (`RunParams.dec`), and `LegConservation.claimRefund` of the decoded
  bundle must succeed.  `Step.other` is any other activity on the chain: an arbitrary change of the
  world.
* **One frame everywhere: tracker registrations are never cleared.**  The tracker's
  `isAssetRegistered` is only ever set to `true` (`L2AssetTracker.sol:106, :261`), so the arbitrary
  world changes are `RegMono`, and the abstract code (`Params.routerRecover`, `Params.customBurn`)
  is assumed to be (`CodeFrames`).
* `abi.encode(InteropBundle)`, `abi.decode` and keccak are the abstract `RunParams.enc`, `.dec` and
  `.keccak`.  Results assume the decoder round trip only on the run's own bundles, and never
  injectivity of keccak: a claim that consumes a leg with bytes other than the sent bundle's is the
  pinned keccak collision on those two byte strings.
* Calls made by the refund recipient's code inside a claim are separate steps (see
  `LegConservation`).
-/

namespace Contracts.NativeValueLegs

/-! ## Routes, logs and parameters -/

/-- How a send's collection reached the destination's base-token asset `A`
(`InteropCenter.sol:432-453`, `AssetRouterBase.sol:103-113`). -/
inductive Route where
  /-- `A` is this chain's base token: `BaseTokenHolder.burnAndStartBridging`. -/
  | holder
  /-- The router's handler for `A` is the vault: `NativeTokenVault.bridgeBurn`. -/
  | vault
  /-- The router's handler for `A` is `h`, another contract. -/
  | custom (h : Address)
deriving DecidableEq

/-- The route of a collection of asset `A` in world `w`. -/
def routeOf (cfg : Config) (w : World) (A : AssetId) : Route :=
  if A = cfg.baseAsset then .holder
  else if w.handler A = cfg.ntv then .vault
  else .custom (w.handler A)

/-- The route went through a handler other than the vault. -/
def Route.IsCustom : Route → Prop
  | .custom _ => True
  | _ => False

/-- `AtomicFlowManager`'s `LegState` (`atomic-interop/IAtomicInterop.sol`). -/
inductive LegState where
  | Unset
  | Committed
  | Revertable
  | Reverted
deriving DecidableEq

/-- Ghost record of one successful atomic send. -/
structure Sent where
  /-- `msg.sender` of the send. -/
  sender : Address
  /-- The parsed call starters. -/
  starters : List Starter
  /-- The bundle the center formed and hashed. -/
  bundle : Bundle
  /-- The flow id of the leg committed. -/
  flowId : Word
  /-- The route of its collection. -/
  route : Route

/-- Ghost record of one successful `claimRefund`. -/
structure Claimed where
  /-- `_flowId`. -/
  flowId : Word
  /-- `_bundle`: the bytes the claimant passed. -/
  bytes : Bytes
  /-- `abi.decode(_bundle, (InteropBundle))`. -/
  bundle : Bundle
  /-- The world before the claim. -/
  before : World
  /-- The world after the claim. -/
  after : World

/-- `Params` with the encoder, decoder and keccak the leg keys use. -/
structure RunParams extends Params where
  /-- `abi.encode(InteropBundle)` (`InteropCenter.sol:691`). -/
  enc : Bundle → Bytes
  /-- `abi.decode(_bundle, (InteropBundle))` (`AtomicFlowManager.sol:251`); `none` reverts. -/
  dec : Bytes → Option Bundle
  /-- `keccak256`. -/
  keccak : Bytes → Word

/-! ## State and steps -/

/-- The source chain during a run. -/
structure State where
  /-- The world of `LegConservation`. -/
  world : World
  /-- The manager's `_state[flowId][bundleHash]` (`AtomicFlowManager.sol:61`). -/
  legs : Word → Word → LegState
  /-- Ghost: every successful atomic send, oldest first. -/
  sent : List Sent
  /-- Ghost: every successful claim, oldest first. -/
  claimed : List Claimed

/-- Fresh manager storage and empty logs over world `w`. -/
def State.init (w : World) : State := ⟨w, fun _ _ => .Unset, [], []⟩

/-- `_state[f][h] = s`. -/
def setLeg (legs : Word → Word → LegState) (f h : Word) (s : LegState) : Word → Word → LegState :=
  fun f' h' => if f' = f ∧ h' = h then s else legs f' h'

/-- No tracker registration is cleared from `w` to `w'`. -/
def RegMono (w w' : World) : Prop := ∀ a, w.registered a = true → w'.registered a = true

/-- The leg key a send commits: `(flowId, keccak256(abi.encode(bundle)))`. -/
def Sent.key (R : RunParams) (s : Sent) : Word × Word := (s.flowId, R.keccak (R.enc s.bundle))

/-- The leg key a claim consumes: `(flowId, keccak256(_bundle))`. -/
def Claimed.key (R : RunParams) (r : Claimed) : Word × Word := (r.flowId, R.keccak r.bytes)

/-- One transaction on the source chain. -/
inductive Step (R : RunParams) : State → State → Prop
  /-- A successful atomic send by `u` of bundle `B` as a leg of flow `F`. -/
  | send {S : State} (u : Address) (starters : List Starter) (B : Bundle) (F : Word)
      (w₁ w₂ w₃ : World) :
      B.destChain ≠ R.cfg.l1Chain →
      (∀ s ∈ starters, StarterPasses deployed R.cfg s) →
      List.Forall₂ (FormsCall R.cfg B.destBaseAsset u) starters B.calls →
      RegMono S.world w₁ →
      collect R.toParams w₁ u B.destChain B.destBaseAsset (collected starters) = some w₂ →
      RegMono w₂ w₃ →
      S.legs F (R.keccak (R.enc B)) = .Unset →
      Step R S ⟨w₃, setLeg S.legs F (R.keccak (R.enc B)) .Committed,
        S.sent ++ [⟨u, starters, B, F, routeOf R.cfg w₁ B.destBaseAsset⟩], S.claimed⟩
  /-- `authorizeRefund` moving one committed leg to `Revertable`; proof checks omitted. -/
  | authorize {S : State} (F h : Word) :
      S.legs F h = .Committed →
      Step R S { S with legs := setLeg S.legs F h .Revertable }
  /-- A successful `claimRefund(F, x)`. -/
  | claim {S : State} (F : Word) (x : Bytes) (B : Bundle) (w' : World) :
      S.legs F (R.keccak x) = .Revertable →
      R.dec x = some B →
      claimRefund R.toParams S.world B = some w' →
      Step R S ⟨w', setLeg S.legs F (R.keccak x) .Reverted, S.sent,
        S.claimed ++ [⟨F, x, B, S.world, w'⟩]⟩
  /-- Any other activity on the chain. -/
  | other {S : State} (w' : World) :
      RegMono S.world w' →
      Step R S { S with world := w' }

/-- Reachability. -/
inductive Reach (R : RunParams) : State → State → Prop
  | refl {S : State} : Reach R S S
  | tail {S T U : State} : Reach R S T → Step R T U → Reach R S U

/-! ## Notions the statements use -/

/-- **THE FRAME PREMISE ON THE ABSTRACT CODE.**  Router-call recovery leaves every asset its data
does not name alone (`RecoveryFramesOthers`), and neither it nor a custom handler's burn clears a
tracker registration. -/
structure CodeFrames (P : Params) : Prop where
  /-- `RecoveryFramesOthers` for every asset. -/
  recover : ∀ A, RecoveryFramesOthers P A
  /-- Router-call recovery clears no registration. -/
  recoverMono : ∀ w d cd w', P.routerRecover w d cd = some w' → RegMono w w'
  /-- A custom handler's burn clears no registration. -/
  customMono : ∀ h w d a u v w', P.customBurn h w d a u v = some w' → RegMono w w'

/-- **WHAT A CLAIM IS BOUND TO.**  The claim `r` consumed the leg of a logged send `s`: same flow
id and same leg hash.  Either the claimant passed `s`'s own bytes, the decoded bundle is `s`'s, and
the claim moved exactly `collected s.starters` of `s`'s asset to `s.sender` whenever `s` collected
nothing, or collected through the holder or the vault, or the asset was registered in the tracker
before the claim, or it does not originate on the source chain; or the claimant passed other bytes
with the same keccak: a keccak collision on the two named byte strings `r.bytes` and
`R.enc s.bundle`.  (Left out: a successful claim of a send that collected something through a
handler other than the vault, in a token native to the source chain and not registered before the
claim.  Its first value refund is the tracker's first registration of the token, which also sets
its `chainBalance`; `LegConservation` `UnregisteredNativeRefundSetsChainBalance`.) -/
def ClaimMatches (R : RunParams) (sent : List Sent) (r : Claimed) : Prop :=
  ∃ s ∈ sent, s.flowId = r.flowId ∧ R.keccak (R.enc s.bundle) = R.keccak r.bytes ∧
    ((r.bytes = R.enc s.bundle ∧ r.bundle = s.bundle ∧
        (collected s.starters = 0 ∨ ¬ s.route.IsCustom ∨
            r.before.registered s.bundle.destBaseAsset = true ∨
            ¬ NativeHere R.cfg s.bundle.destBaseAsset →
          Shifted R.cfg s.bundle.destBaseAsset s.sender (collected s.starters) r.before r.after)) ∨
      r.bytes ≠ R.enc s.bundle)

/-! ## Witness data -/

/-- The witness bundle bytes: one constant encoding, which separates the single bundle each
witness run sends. -/
def wEnc (_ : Bundle) : Bytes := [7]

/-- The witness hash: the length of the bytes. -/
def wKeccak (x : Bytes) : Word := x.length

/-- Run parameters over `wParams` decoding `[7]` to bundle `B`. -/
def wRun (B : Bundle) : RunParams :=
  { wParams with enc := wEnc, dec := fun x => if x = [7] then some B else none, keccak := wKeccak }

end Contracts.NativeValueLegs
