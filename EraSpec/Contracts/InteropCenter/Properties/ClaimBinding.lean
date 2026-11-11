import EraSpec.Contracts.InteropCenter.Specs.ClaimBinding
import EraSpec.Contracts.InteropCenter.Properties.Dispatch

/-!
# Properties: a claimed bundle is a dispatched bundle

Statements about what `claimRefund(f, x)` (AtomicFlowManager.sol:165-180) recovers, on the dispatch
model of `EraSpec.Contracts.InteropCenter.Specs.Dispatch`, with the claim-side names of
`EraSpec.Contracts.InteropCenter.Specs.ClaimBinding`. Proofs are in
`EraSpec.Contracts.InteropCenter.Proofs.ClaimBinding`. Every run starts from fresh storage
(`init`) on one chain; `deployed` is the code with all three of its checks. No result assumes
anything about keccak. The only collisions a conclusion allows are pinned to named preimages of
the instance.

## The headline

`ClaimedBundleValidatedOrCollision` (Dispatch, O1) says that the bundle `claimRefund` decodes
carries no native value, or a pinned collision holds. `ClaimedBundleIsDispatchedOrCollision` says
more. The bytes are the canonical bytes `abi.encode(bundle)` of an atomic dispatch of that very
flow in the run's log, and they decode to that dispatch's bundle; or the same pinned collision
holds. Its premises are O1's:
- a run of the deployed code;
- the `SOL-ABI` round trip on the run's own bundles;
- a leg, computed the way `claimRefund` computes it, that is not `Unset`.

O1's form follows from it (`ClaimedBundleIsDispatchedImpliesValidated`). Of the deployed code's
three checks, it uses only `onlyInteropCenter` on `append`
(`ClaimBindingIndependentOfSaltAndValueChecks`).

Once the two hashes are equal, the collision disjunct says only that the two preimages differ. So
the content is elsewhere: every leg that is not `Unset` belongs to a logged atomic dispatch;
`abi.encode(uint256, bytes)` adds no collision of its own (an equal preimage forces equal bytes,
whatever source chain was decoded); and the decoder round trip. The bounded form states this
without a disjunct. If keccak is injective on the claim's preimage and the run's own bundle-hash
preimages, an explicit finite list, then the claimed bytes are a dispatched bundle's
(`ClaimedBundleIsDispatchedOn`).

## Corollaries

* **This chain's bundle.** The source chain `claimRefund` decodes and hashes is `block.chainid`.
  So its recomputation `abi.encode(bundle.sourceChainId, x)` is byte for byte the center's
  `abi.encode(block.chainid, abi.encode(bundle))` (`ClaimSourceChainIsThisChainOrCollision`).
* **The user's calls.** The external calls `_recoverBundle` makes are the dispatched bundle's:
  each call's target and data, and the bundle's destination chain. Those calls are the ones
  `_processCallStarter` formed from the dispatch's own call starters for its own sender, and none
  carries value (`RecoveredCallsAreDispatchedCalls`). This is `IAtomicRecoverable.sol:15-16`
  ("`_callData` is the original `InteropCall.data`"; the destination chain is the one "the
  original call targeted") as a theorem, up to the pinned collision.
* **One dispatch.** At most one log position holds an atomic dispatch of a given flow with given
  canonical bytes (`ClaimIdentifiesOneDispatch`). So the dispatch a claim recovers is unique.
* **Recovered at most once.** Two successful claims along one run recover two different bundles,
  whatever bytes and flow the second one uses. The exceptions are that one of the claims is a
  pinned claim collision, or that the two recovered dispatches share one bundle through O1 (c)'s
  cross-sender salt clash (`EachBundleRecoveredAtMostOnce`). With keccak injective on the claims'
  preimages and the run's own bundle-hash and salt preimages, there is no exception
  (`EachBundleRecoveredAtMostOnceOn`).
* **Liveness note.** The canonical bytes always reach the committed leg, for any keccak
  (`CanonicalBytesReadTheirLeg`). So `claimRefund(d.flowId, abi.encode(d.bundle))` passes its
  state check exactly when the leg is `Revertable`, and the bundle to encode is in the
  `InteropBundleSent` event (`InteropCenter.sol:585`). Bytes that are not the canonical encoding
  of any atomic dispatch of the flow read an `Unset` leg, so `claimRefund`
  reverts with `ManagerLegNotRevertable` (AtomicFlowManager.sol:170), or the pinned collision holds
  (`NonCanonicalBytesNeverClaim`). That covers every other encoding that `abi.decode` maps to a
  dispatched bundle, such as one with trailing bytes (`ReencodedBundleNeverClaims`).

## Each premise and disjunct is needed

* `CollisionLetsAClaimRecoverUndispatchedCalls`: under a colliding keccak, the canonical bytes of a
  bundle that was never dispatched find a `Revertable` leg. The claim would execute calls no
  dispatch made, one of them carrying value. The collision disjunct is what fires.
* `WithoutRoundTripClaimRecoversUndispatchedCalls`: with the honest witness keccak and no
  collision at all, a decoder that does not invert the encoder on a dispatched bundle makes that
  bundle's own canonical bytes recover other calls. So the `SOL-ABI` premise is load-bearing here,
  and also in O1's `ClaimedBundleValidatedOrCollision`, whose conclusion fails on the same run.
* `WithoutOnlyInteropCenterClaimRecoversUndispatchedCalls`: without `onlyInteropCenter` on
  `append`, a claim with honest keccak and canonical bytes recovers a bundle on a run that
  dispatched nothing. So the headline rests on the deployed code's caller check, through O1's
  `CommittedLegsAreValidatedDispatches`.
* `SaltClashLetsOneBundleBeRecoveredTwice`: under a colliding keccak, two senders dispatch one
  bundle on two flows. Two successful claims with the same canonical bytes then recover it twice,
  and neither claim is a claim collision.
* `WithoutSaltCheckOneBundleRecoveredTwice`: without the salt check, one sender dispatches one
  bundle on two flows, and with honest keccak two successful claims recover it twice. Every
  disjunct of `EachBundleRecoveredAtMostOnce` fails there. So at-most-once rests on the salt check.

## Non-vacuity

* `ClaimBindingWitness` (built from O1's `ClaimWitness`) meets every premise of the headline, of
  its bounded form and of the corollaries on the honest run. The leg is `Revertable`, the first
  disjunct is true and the collision false, and it names the one recovery call.
* `ClaimBindingNonCanonicalWitness` meets the premises of the two negative liveness results, with
  bytes that decode to the dispatched bundle but carry a trailing zero byte. The leg they read is
  `Unset`, and the collision is false.
* `ClaimBindingTwoClaimsWitness` meets every premise of `EachBundleRecoveredAtMostOnce` and of its
  bounded form with two successful claims. The two bundles differ, and every break disjunct is
  false.
-/

namespace Contracts.InteropCenter

open Contracts.AtomicFlowManager (LegState)

/-! ## The headline -/

/-- **HEADLINE: A CLAIMED BUNDLE IS A DISPATCHED BUNDLE, OR KECCAK COLLIDES ON TWO NAMED
PREIMAGES.** Take any run of the deployed code from fresh storage whose decoder inverts the
encoder on the run's bundles (`abi.decode` after `abi.encode`, `SOL-ABI`). Suppose
`claimRefund(f, x)` finds the leg it computes from the bytes `x` not `Unset`
(AtomicFlowManager.sol:166-169). Then one of these holds:
- `x` is the canonical encoding `abi.encode(bundle)` of the bundle of an atomic dispatch of flow
  `f` in the run's log, and `x` decodes to that bundle;
- keccak collides on the preimage `claimRefund` hashed and the preimage the center hashed for a
  logged atomic dispatch of flow `f`.

This holds for any bytes `x`, any flow and any decoded source chain. -/
def Properties.ClaimedBundleIsDispatchedOrCollision : Prop :=
  ∀ (P : Params) (dec : List UInt8 → Bundle) (S : State), Reach deployed P init S →
    DecodesDispatchedBundles P dec S.log →
    ∀ (f : Word) (x : List UInt8), S.manager.legState f (claimRefundHash P dec x) ≠ .Unset →
      ClaimRecoversDispatch P dec S.log f x ∨ ClaimHashCollision P dec S.log f x

/-- **THE BINDING RESTS ON `onlyInteropCenter` ALONE.** The headline holds for every variant of the
code that keeps `onlyInteropCenter` on `append` (AtomicFlowManager.sol:76-79), with or without the
salt check and `_validateAtomicBundle`. Together with
`WithoutOnlyInteropCenterClaimRecoversUndispatchedCalls`, this pins the binding to the caller
check, among the three checks the model switches. -/
def Properties.ClaimBindingIndependentOfSaltAndValueChecks : Prop :=
  ∀ (K : Checks), K.onlyInteropCenter = true →
    ∀ (P : Params) (dec : List UInt8 → Bundle) (S : State), Reach K P init S →
      DecodesDispatchedBundles P dec S.log →
      ∀ (f : Word) (x : List UInt8), S.manager.legState f (claimRefundHash P dec x) ≠ .Unset →
        ClaimRecoversDispatch P dec S.log f x ∨ ClaimHashCollision P dec S.log f x

/-- **BOUNDED FORM: WITH KECCAK INJECTIVE ON THE INSTANCE'S OWN PREIMAGES, THE CLAIMED BYTES ARE A
DISPATCHED BUNDLE'S.** Take the headline's premises, and suppose keccak is injective on an explicit
finite list: the preimage `claimRefund(f, x)` hashed, together with the run's own bundle-hash
preimages, one per dispatch. Then `x` is the canonical encoding of the bundle of an atomic
dispatch of flow `f` in the log, and decodes to that bundle, with no disjunct. -/
def Properties.ClaimedBundleIsDispatchedOn : Prop :=
  ∀ (P : Params) (dec : List UInt8 → Bundle) (S : State), Reach deployed P init S →
    DecodesDispatchedBundles P dec S.log →
    ∀ (f : Word) (x : List UInt8),
      KeccakInjOn P.keccak (claimPreimage dec x :: bundlePreimages P S.log) →
      S.manager.legState f (claimRefundHash P dec x) ≠ .Unset →
      ClaimRecoversDispatch P dec S.log f x

/-- **O1'S FORM FOLLOWS.** Along any run of the deployed code, the headline's conclusion implies
the conclusion of `ClaimedBundleValidatedOrCollision`. A recovered dispatch's bundle carries no
native value, and the claim collision is O1's collision. So the headline strengthens O1's. -/
def Properties.ClaimedBundleIsDispatchedImpliesValidated : Prop :=
  ∀ (P : Params) (dec : List UInt8 → Bundle) (S : State), Reach deployed P init S →
    ∀ (f : Word) (x : List UInt8),
      ClaimRecoversDispatch P dec S.log f x ∨ ClaimHashCollision P dec S.log f x →
      Validated (dec x) ∨
        ∃ d ∈ S.log, d.isAtomic = true ∧ d.atomicSend.flowId = f ∧
          claimPreimage dec x ≠ bundlePreimage P d.bundle ∧
          P.keccak (claimPreimage dec x) = bundleHash P d.bundle

/-! ## Corollaries -/

/-- **THE CLAIMED SOURCE CHAIN IS THIS CHAIN, OR KECCAK COLLIDES.** Under the headline's premises,
the source chain that `claimRefund` decodes from `x` and hashes (AtomicFlowManager.sol:167) is
`block.chainid`. The bytes it hashes, `abi.encode(bundle.sourceChainId, x)`, are then exactly the
bytes the center hashes for the decoded bundle, `abi.encode(block.chainid, abi.encode(bundle))`
(InteropCenter.sol:643-644). Otherwise the pinned claim collision holds. -/
def Properties.ClaimSourceChainIsThisChainOrCollision : Prop :=
  ∀ (P : Params) (dec : List UInt8 → Bundle) (S : State), Reach deployed P init S →
    DecodesDispatchedBundles P dec S.log →
    ∀ (f : Word) (x : List UInt8), S.manager.legState f (claimRefundHash P dec x) ≠ .Unset →
      ((dec x).sourceChainId = P.chainId ∧ claimPreimage dec x = bundlePreimage P (dec x)) ∨
        ClaimHashCollision P dec S.log f x

/-- **THE CALLS A CLAIM RECOVERS ARE THE DISPATCHED CALLS, OR KECCAK COLLIDES.** Under the
headline's premises, either the pinned claim collision holds, or there is an atomic dispatch `d`
of flow `f` in the log such that:
- the leg the claim reads is `d`'s, `(f, bundleHash d.bundle)`;
- the external calls `_recoverBundle` makes (AtomicFlowManager.sol:220-228) are those of `d`'s
  bundle: the same targets, data and destination chain;
- the decoded calls are the calls `_processCallStarter` formed from `d`'s own call starters for
  `d`'s own sender (InteropCenter.sol:539-540, :701-751);
- no decoded call carries native value. -/
def Properties.RecoveredCallsAreDispatchedCalls : Prop :=
  ∀ (P : Params) (dec : List UInt8 → Bundle) (S : State), Reach deployed P init S →
    DecodesDispatchedBundles P dec S.log →
    ∀ (f : Word) (x : List UInt8), S.manager.legState f (claimRefundHash P dec x) ≠ .Unset →
      (∃ d ∈ S.log, d.isAtomic = true ∧ d.atomicSend.flowId = f ∧
        claimRefundHash P dec x = bundleHash P d.bundle ∧
        recoverBundleCalls (dec x) = recoverBundleCalls d.bundle ∧
        List.Forall₂ (FormsCall d.sender) d.starters (dec x).calls ∧
        Validated (dec x)) ∨
      ClaimHashCollision P dec S.log f x

/-- **ONE DISPATCH PER FLOW AND BYTES.** Along any run, with or without the checks, two atomic
dispatches of the same flow with the same canonical bytes `abi.encode(bundle)` are at the same log
position. The reason is that the manager's `Unset` check (AtomicFlowManager.sol:93) commits each
leg once. So the dispatch the headline names for a claim is unique. -/
def Properties.ClaimIdentifiesOneDispatch : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), Reach K P init S →
    ∀ (i j : ℕ) (hi : i < S.log.length) (hj : j < S.log.length),
      S.log[i].isAtomic = true → S.log[j].isAtomic = true →
      S.log[i].atomicSend.flowId = S.log[j].atomicSend.flowId →
      P.enc S.log[i].bundle = P.enc S.log[j].bundle → i = j

/-- **EACH BUNDLE IS RECOVERED AT MOST ONCE, OR A PINNED BREAK.** Take a run of the deployed code
with these steps:
- a successful `claimRefund(f, x)` at the reachable state `S₀` (its state check,
  AtomicFlowManager.sol:169-170);
- the claim's write (AtomicFlowManager.sol:175), then any continuation to `S₂`;
- a successful `claimRefund(f', x')` at `S₂`.

Suppose the decoder inverts the encoder on the bundles dispatched by `S₂`. Then the two claims
recover two different bundles, whatever bytes `x'` and flow `f'` the second caller uses, unless
one of the following breaks holds:
- the first claim is a pinned claim collision;
- the second claim is a pinned claim collision;
- the two claims recover the bundles of two different dispatches that carry one bundle, with O1
  (c)'s cross-sender salt clash between them.

The second claim may also run inside the first claim's recovery calls, since the manager has no
reentrancy guard. The write at AtomicFlowManager.sol:175 precedes `_recoverBundle` (:177), so such
a nested claim is a later step from the post-write state, which this statement covers. -/
def Properties.EachBundleRecoveredAtMostOnce : Prop :=
  ∀ (P : Params) (dec : List UInt8 → Bundle) (S₀ S₂ : State) (f f' : Word)
    (x x' : List UInt8),
    Reach deployed P init S₀ →
    S₀.manager.legState f (claimRefundHash P dec x) = .Revertable →
    Reach deployed P
      { S₀ with manager := S₀.manager.set f (claimRefundHash P dec x) .Reverted } S₂ →
    DecodesDispatchedBundles P dec S₂.log →
    S₂.manager.legState f' (claimRefundHash P dec x') = .Revertable →
    dec x' ≠ dec x ∨ ClaimHashCollision P dec S₀.log f x ∨ ClaimHashCollision P dec S₂.log f' x' ∨
      ∃ d ∈ S₂.log, ∃ d' ∈ S₂.log,
        d.isAtomic = true ∧ d.atomicSend.flowId = f ∧ x = P.enc d.bundle ∧
        d'.isAtomic = true ∧ d'.atomicSend.flowId = f' ∧ x' = P.enc d'.bundle ∧
        d.bundle = d'.bundle ∧ CrossSenderSaltClash P d d'

/-- **BOUNDED FORM: WITH KECCAK INJECTIVE ON THE INSTANCE'S OWN PREIMAGES, NO BUNDLE IS RECOVERED
TWICE.** Take the premises of `EachBundleRecoveredAtMostOnce`, and suppose keccak is injective on
two explicit finite lists:
- the two preimages the claims hashed, together with the bundle-hash preimages of the run's
  dispatches;
- the run's salt preimages `abi.encodePacked(sender, salt)`.

Then the two claims recover two different bundles, with no disjunct. -/
def Properties.EachBundleRecoveredAtMostOnceOn : Prop :=
  ∀ (P : Params) (dec : List UInt8 → Bundle) (S₀ S₂ : State) (f f' : Word)
    (x x' : List UInt8),
    Reach deployed P init S₀ →
    S₀.manager.legState f (claimRefundHash P dec x) = .Revertable →
    Reach deployed P
      { S₀ with manager := S₀.manager.set f (claimRefundHash P dec x) .Reverted } S₂ →
    DecodesDispatchedBundles P dec S₂.log →
    S₂.manager.legState f' (claimRefundHash P dec x') = .Revertable →
    KeccakInjOn P.keccak (claimPreimage dec x :: claimPreimage dec x' :: bundlePreimages P S₂.log) →
    KeccakInjOn P.keccak (saltPreimages S₂.log) →
    dec x' ≠ dec x

/-! ## The liveness note -/

/-- **LIVENESS NOTE, POSITIVE: THE CANONICAL BYTES READ THE COMMITTED LEG.** Take any run, with or
without the checks, whose decoder inverts the encoder on the run's bundles, and any atomic
dispatch `d` of the run. The bytes `claimRefund(d.flowId, abi.encode(d.bundle))` hashes are
exactly the bytes the center hashed. So for any keccak, the claim reads and writes the leg the
center committed, and that leg is not `Unset`. The claim with the canonical bytes therefore passes
its state check exactly when that leg is `Revertable`. -/
def Properties.CanonicalBytesReadTheirLeg : Prop :=
  ∀ (K : Checks) (P : Params) (dec : List UInt8 → Bundle) (S : State), Reach K P init S →
    DecodesDispatchedBundles P dec S.log →
    ∀ d ∈ S.log, d.isAtomic = true →
      claimPreimage dec (P.enc d.bundle) = bundlePreimage P d.bundle ∧
        S.manager.legState d.atomicSend.flowId (bundleHash P d.bundle) ≠ .Unset

/-- **LIVENESS NOTE, NEGATIVE: NON-CANONICAL BYTES NEVER CLAIM.** Take any run of the deployed code
whose decoder inverts the encoder on the run's bundles. Suppose the bytes `x` are not the
canonical encoding `abi.encode(bundle)` of any atomic dispatch of flow `f` in the log. Then the leg
`claimRefund(f, x)` reads is `Unset`, so the claim reverts with `ManagerLegNotRevertable`
(AtomicFlowManager.sol:170); or the pinned claim collision holds. -/
def Properties.NonCanonicalBytesNeverClaim : Prop :=
  ∀ (P : Params) (dec : List UInt8 → Bundle) (S : State), Reach deployed P init S →
    DecodesDispatchedBundles P dec S.log →
    ∀ (f : Word) (x : List UInt8),
      (∀ d ∈ S.log, d.isAtomic = true → d.atomicSend.flowId = f → x ≠ P.enc d.bundle) →
      S.manager.legState f (claimRefundHash P dec x) = .Unset ∨ ClaimHashCollision P dec S.log f x

/-- **A RE-ENCODED BUNDLE NEVER CLAIMS.** Take any run of the deployed code whose decoder inverts
the encoder on the run's bundles, and any dispatch `d` of the run. Suppose the bytes `x` decode to
`d`'s bundle but are not its canonical encoding: for example, they carry trailing bytes, or other
offsets that `abi.decode` accepts. Then for every flow `f`, the leg `claimRefund(f, x)` reads is
`Unset`, or the pinned claim collision holds. -/
def Properties.ReencodedBundleNeverClaims : Prop :=
  ∀ (P : Params) (dec : List UInt8 → Bundle) (S : State), Reach deployed P init S →
    DecodesDispatchedBundles P dec S.log →
    ∀ d ∈ S.log, ∀ (f : Word) (x : List UInt8), dec x = d.bundle → x ≠ P.enc d.bundle →
      S.manager.legState f (claimRefundHash P dec x) = .Unset ∨ ClaimHashCollision P dec S.log f x

/-! ## Countermodels: each premise and disjunct is needed -/

/-- **THE COLLISION DISJUNCT IS NEEDED: A COLLISION LETS A CLAIM RECOVER UNDISPATCHED CALLS.** There
is a run of the deployed code, with a colliding keccak and a decoder that inverts the encoder on the
run's bundles, and bytes `x` such that:
- `claimRefund(f, x)` finds its leg `Revertable`, so the claim succeeds;
- `x` is not a dispatched bundle's (the headline's first disjunct fails), and the claim collision
  holds;
- the calls `_recoverBundle` would make are those of no dispatch of the run;
- one of the decoded calls carries native value. -/
def Properties.CollisionLetsAClaimRecoverUndispatchedCalls : Prop :=
  ∃ (P : Params) (dec : List UInt8 → Bundle) (S : State) (f : Word) (x : List UInt8),
    Reach deployed P init S ∧ DecodesDispatchedBundles P dec S.log ∧
    S.manager.legState f (claimRefundHash P dec x) = .Revertable ∧
    ¬ ClaimRecoversDispatch P dec S.log f x ∧ ClaimHashCollision P dec S.log f x ∧
    (∀ d ∈ S.log, recoverBundleCalls (dec x) ≠ recoverBundleCalls d.bundle) ∧ ¬ Validated (dec x)

/-- **THE ROUND-TRIP PREMISE IS NEEDED.** There is a run of the deployed code whose decoder does not
invert the encoder on the run's bundles, and bytes `x` such that:
- `claimRefund(f, x)` finds its leg `Revertable`;
- neither disjunct of the headline holds, and in particular there is no claim collision;
- the calls `_recoverBundle` would make are those of no dispatch of the run;
- a decoded call carries native value, so the conclusion of O1's
  `ClaimedBundleValidatedOrCollision` fails as well. -/
def Properties.WithoutRoundTripClaimRecoversUndispatchedCalls : Prop :=
  ∃ (P : Params) (dec : List UInt8 → Bundle) (S : State) (f : Word) (x : List UInt8),
    Reach deployed P init S ∧ ¬ DecodesDispatchedBundles P dec S.log ∧
    S.manager.legState f (claimRefundHash P dec x) = .Revertable ∧
    ¬ ClaimRecoversDispatch P dec S.log f x ∧ ¬ ClaimHashCollision P dec S.log f x ∧
    (∀ d ∈ S.log, recoverBundleCalls (dec x) ≠ recoverBundleCalls d.bundle) ∧ ¬ Validated (dec x)

/-- **`onlyInteropCenter` IS NEEDED: WITHOUT IT, A CLAIM RECOVERS A BUNDLE NO ONE DISPATCHED.** With
the honest witness keccak, there is a run of the code without `onlyInteropCenter` on `append`
(AtomicFlowManager.sol:76-79) and bytes `x` such that:
- `x` is the canonical encoding of the bundle it decodes to;
- `claimRefund(f, x)` finds its leg `Revertable`, although the run dispatched nothing;
- neither disjunct of the headline holds;
- a decoded call carries native value. -/
def Properties.WithoutOnlyInteropCenterClaimRecoversUndispatchedCalls : Prop :=
  ∃ (P : Params) (dec : List UInt8 → Bundle) (S : State) (f : Word) (x : List UInt8),
    Reach withoutOnlyInteropCenter P init S ∧ DecodesDispatchedBundles P dec S.log ∧
    x = P.enc (dec x) ∧ S.manager.legState f (claimRefundHash P dec x) = .Revertable ∧
    ¬ ClaimRecoversDispatch P dec S.log f x ∧ ¬ ClaimHashCollision P dec S.log f x ∧
    ¬ Validated (dec x)

/-- **THE SALT CHECK IS NEEDED FOR AT-MOST-ONCE: WITHOUT IT, ONE BUNDLE IS RECOVERED TWICE.** With
the honest witness keccak, there is a run of the code without the salt check
(InteropCenter.sol:479-482) meeting every other premise of `EachBundleRecoveredAtMostOnce`. In
it, one sender dispatches one bundle on two flows `f` and `f'`, and two successful claims with the
same canonical bytes `x` recover that bundle twice. Every disjunct of the conclusion fails: the
two recovered bundles are equal, neither claim is a claim collision, and no two dispatches of the
run have the cross-sender salt clash. -/
def Properties.WithoutSaltCheckOneBundleRecoveredTwice : Prop :=
  ∃ (P : Params) (dec : List UInt8 → Bundle) (S₀ S₂ : State) (f f' : Word) (x : List UInt8),
    Reach withoutSaltCheck P init S₀ ∧
    S₀.manager.legState f (claimRefundHash P dec x) = .Revertable ∧
    Reach withoutSaltCheck P
      { S₀ with manager := S₀.manager.set f (claimRefundHash P dec x) .Reverted } S₂ ∧
    DecodesDispatchedBundles P dec S₂.log ∧
    S₂.manager.legState f' (claimRefundHash P dec x) = .Revertable ∧
    ¬ ClaimHashCollision P dec S₀.log f x ∧ ¬ ClaimHashCollision P dec S₂.log f' x ∧
    ¬ ∃ d ∈ S₂.log, ∃ d' ∈ S₂.log, CrossSenderSaltClash P d d'

/-- **THE SALT-CLASH DISJUNCT IS NEEDED: ONE BUNDLE RECOVERED TWICE.** Under a colliding keccak,
there is a run of the deployed code meeting every premise of `EachBundleRecoveredAtMostOnce`, in
which both claims use the same bytes `x`, on two flows `f` and `f'`:
- the claim `claimRefund(f, x)` succeeds;
- after it, the claim `claimRefund(f', x)` succeeds too;
- neither claim is a claim collision.

So the same bundle's recovery calls run twice, and only the salt-clash disjunct can hold. -/
def Properties.SaltClashLetsOneBundleBeRecoveredTwice : Prop :=
  ∃ (P : Params) (dec : List UInt8 → Bundle) (S₀ S₂ : State) (f f' : Word) (x : List UInt8),
    Reach deployed P init S₀ ∧
    S₀.manager.legState f (claimRefundHash P dec x) = .Revertable ∧
    Reach deployed P
      { S₀ with manager := S₀.manager.set f (claimRefundHash P dec x) .Reverted } S₂ ∧
    DecodesDispatchedBundles P dec S₂.log ∧
    S₂.manager.legState f' (claimRefundHash P dec x) = .Revertable ∧
    ¬ ClaimHashCollision P dec S₀.log f x ∧ ¬ ClaimHashCollision P dec S₂.log f' x

/-! ## Non-vacuity -/

/-- **THE HEADLINE'S PREMISES HOLD, AND ITS COLLISION IS FALSE.** On O1's honest run `wS3`, the
following hold for `x`, the canonical bytes of `wD1`'s bundle:
- the decoder `wDec` inverts the encoder on the run's bundles;
- `claimRefund(7, x)` finds its leg `Revertable`, so not `Unset`, and the claim succeeds;
- the witness keccak is injective on the claim's preimage and the run's bundle-hash preimages
  (the premise of `ClaimedBundleIsDispatchedOn`);
- the claim recovers the dispatch `wD1`, and the claim collision is false;
- `_recoverBundle` makes exactly one call: to contract `5`, for destination chain `325`, with
  empty data.

The log is `[wD1, wD2]` with `wD1` atomic, so the premises of the per-run corollaries hold too. -/
def Properties.ClaimBindingWitness : Prop :=
  Reach deployed wParams init wS3 ∧ wS3.log = [wD1, wD2] ∧ wD1.isAtomic = true ∧
    DecodesDispatchedBundles wParams wDec wS3.log ∧
    wS3.manager.legState 7 (claimRefundHash wParams wDec (wParams.enc wD1.bundle)) = .Revertable ∧
    KeccakInjOn wParams.keccak
      (claimPreimage wDec (wParams.enc wD1.bundle) :: bundlePreimages wParams wS3.log) ∧
    ClaimRecoversDispatch wParams wDec wS3.log 7 (wParams.enc wD1.bundle) ∧
    ¬ ClaimHashCollision wParams wDec wS3.log 7 (wParams.enc wD1.bundle) ∧
    recoverBundleCalls (wDec (wParams.enc wD1.bundle)) = [⟨5, 325, []⟩]

/-- **THE NEGATIVE LIVENESS PREMISES HOLD, ON A RE-ENCODING WITH A TRAILING BYTE.** On the honest
run `wS3`, take the bytes `x`: the canonical bytes of `wD1`'s bundle followed by one zero byte.
Then:
- the lenient decoder `wDec` maps `x` to `wD1`'s bundle;
- `x` is not the canonical encoding of any atomic dispatch of flow `7`;
- the leg `claimRefund(7, x)` reads is `Unset`;
- the claim collision is false. -/
def Properties.ClaimBindingNonCanonicalWitness : Prop :=
  Reach deployed wParams init wS3 ∧ DecodesDispatchedBundles wParams wDec wS3.log ∧
    wD1 ∈ wS3.log ∧ wDec (wParams.enc wD1.bundle ++ [0]) = wD1.bundle ∧
    wParams.enc wD1.bundle ++ [0] ≠ wParams.enc wD1.bundle ∧
    (∀ d ∈ wS3.log, d.isAtomic = true → d.atomicSend.flowId = 7 →
      wParams.enc wD1.bundle ++ [0] ≠ wParams.enc d.bundle) ∧
    wS3.manager.legState 7 (claimRefundHash wParams wDec (wParams.enc wD1.bundle ++ [0]))
      = .Unset ∧
    ¬ ClaimHashCollision wParams wDec wS3.log 7 (wParams.enc wD1.bundle ++ [0])

/-- **TWO SUCCESSFUL CLAIMS ON ONE RUN, AND NO BREAK.** There is a run of the deployed code meeting
every premise of `EachBundleRecoveredAtMostOnce`, and both keccak premises of
`EachBundleRecoveredAtMostOnceOn`. The two claims recover different bundles, neither claim is a
claim collision, and no two dispatches of the run have the cross-sender salt clash. -/
def Properties.ClaimBindingTwoClaimsWitness : Prop :=
  ∃ (P : Params) (dec : List UInt8 → Bundle) (S₀ S₂ : State) (f f' : Word) (x x' : List UInt8),
    Reach deployed P init S₀ ∧
    S₀.manager.legState f (claimRefundHash P dec x) = .Revertable ∧
    Reach deployed P
      { S₀ with manager := S₀.manager.set f (claimRefundHash P dec x) .Reverted } S₂ ∧
    DecodesDispatchedBundles P dec S₂.log ∧
    S₂.manager.legState f' (claimRefundHash P dec x') = .Revertable ∧
    KeccakInjOn P.keccak
      (claimPreimage dec x :: claimPreimage dec x' :: bundlePreimages P S₂.log) ∧
    KeccakInjOn P.keccak (saltPreimages S₂.log) ∧
    dec x' ≠ dec x ∧ ¬ ClaimHashCollision P dec S₀.log f x ∧
    ¬ ClaimHashCollision P dec S₂.log f' x' ∧
    ¬ ∃ d ∈ S₂.log, ∃ d' ∈ S₂.log, CrossSenderSaltClash P d d'

end Contracts.InteropCenter
