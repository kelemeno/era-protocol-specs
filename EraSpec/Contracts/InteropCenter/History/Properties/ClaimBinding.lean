import EraSpec.Contracts.InteropCenter.History.Specs.ClaimBinding
import EraSpec.Contracts.InteropCenter.History.Properties.Dispatch

/-!
# Properties: a claimed bundle is a dispatched bundle

Statements about what `claimRefund(f, x)` (AtomicFlowManager.sol:165-180) recovers, on the dispatch
model of `EraSpec.Contracts.InteropCenter.History.Specs.Dispatch`, with the claim-side names of
`EraSpec.Contracts.InteropCenter.History.Specs.ClaimBinding`. Proofs are in
`EraSpec.Contracts.InteropCenter.History.Proofs.ClaimBinding`. Every run starts from fresh storage
(`init`) on one chain; `deployed` is the code with all three of its checks. The source is the pin
`c67894b9`; `Specs/ClaimBinding.lean` lists what differs at the current heads.

Hash premises: the headline, its corollaries and the liveness results assume nothing about keccak,
and the collisions their conclusions allow are pinned to named preimages of the instance. The two
bounded forms, `ClaimedBundleIsDispatchedOn` and `EachBundleRecoveredAtMostOnceOn`, assume keccak
injective on explicit finite lists of the instance's own preimages. The decoder premise is the
`SOL-ABI` round trip on the run's own bundles (`DecodesDispatchedBundles`), never global.

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

How much the collision disjunct leaves: when the leg is not `Unset`, a logged atomic dispatch of
flow `f` stands behind it (O1's `CommittedLegsAreValidatedDispatches`), and for that dispatch the
two hashes in the disjunct are equal. So for it the disjunct says only that the claim's preimage
differs from the center's preimage. The headline is therefore the statement that equal preimages
force the canonical bytes, plus the round trip. `abi.encode(uint256, bytes)` adds no collision of
its own: an equal preimage forces equal bytes, whatever source chain was decoded.
The bounded form states the result without a disjunct. If keccak is injective on the claim's
preimage and the run's own bundle-hash preimages, an explicit finite list, then the claimed bytes
are a dispatched bundle's (`ClaimedBundleIsDispatchedOn`).

## Corollaries

* **This chain's bundle.** Under the headline's premises, the source chain `claimRefund` decodes
  and hashes is `block.chainid`, so its recomputation `abi.encode(bundle.sourceChainId, x)` is byte
  for byte the center's `abi.encode(block.chainid, abi.encode(bundle))`; or the pinned collision
  holds (`ClaimSourceChainIsThisChainOrCollision`).
* **The user's calls.** Under the same premises, or else the pinned collision: the external calls
  `_recoverBundle` makes are the dispatched bundle's (each call's target and data, and the
  bundle's destination chain); the decoded calls are related to the dispatch's own call starters
  by O1's `FormsCall` for its own sender (the fields `_processCallStarter` itself writes); and none
  carries value (`RecoveredCallsAreDispatchedCalls`). This is `IAtomicRecoverable.sol:15-16`
  ("`_callData` is the original `InteropCall.data`"; the destination chain is the one "the
  original call targeted") as a theorem, up to the pinned collision.
* **One dispatch.** At most one log position holds an atomic dispatch of a given flow with given
  canonical bytes (`ClaimIdentifiesOneDispatch`), so the dispatch the headline names is unique.
  Neither match alone suffices (`ClaimIdentifiesOneDispatchNeedsBothMatches`); for the bytes
  match this holds only up to a cross-sender salt clash, which that countermodel's second run
  uses.
* **Recovered at most once.** Along one run of the deployed code whose decoder inverts the encoder
  on the run's bundles, two successful claims (each passing its state check, the second after the
  first one's write) recover two different bundles, whatever bytes and flow the second one uses.
  The exceptions are that one of the claims is a pinned claim collision, or that the two recovered
  dispatches share one bundle through O1 (c)'s cross-sender salt clash
  (`EachBundleRecoveredAtMostOnce`). With keccak injective on the claims' preimages and the run's
  own bundle-hash and salt preimages, there is no exception (`EachBundleRecoveredAtMostOnceOn`).
* **Liveness note.** Under the round trip, the canonical bytes always reach the committed leg, for
  any keccak and with or without the checks (`CanonicalBytesReadTheirLeg`). So
  `claimRefund(d.flowId, abi.encode(d.bundle))` passes its state check exactly when the leg is
  `Revertable`; the bundle to encode is in the `InteropBundleSent` event
  (`InteropCenter.sol:585`). On a run of the deployed code, under the round trip, bytes that are
  not the canonical encoding of any atomic dispatch of the flow read an `Unset` leg, so
  `claimRefund` reverts with `ManagerLegNotRevertable` (AtomicFlowManager.sol:170), or the pinned
  collision holds (`NonCanonicalBytesNeverClaim`). That covers every other encoding that the
  decoder maps to a dispatched bundle, such as one with a trailing byte
  (`ReencodedBundleNeverClaims`).

## Each premise and disjunct of the headline and of at-most-once is needed

The countermodels below show that the headline needs `onlyInteropCenter`, the round trip and its
collision disjunct; and that `EachBundleRecoveredAtMostOnce` needs the salt check,
`onlyInteropCenter`, the round trip, and each of its three break disjuncts. The headline does not
need the salt check or the value check (`ClaimBindingIndependentOfSaltAndValueChecks`).

* `CollisionLetsAClaimRecoverUndispatchedCalls`: under a colliding keccak, the canonical bytes of a
  bundle that no dispatch of the run carries find a `Revertable` leg. The claim would make calls no
  dispatch of the run made, and one decoded call carries value. The collision disjunct is what
  holds.
* `WithoutRoundTripClaimRecoversUndispatchedCalls`: on a run of the deployed code with no claim
  collision, a decoder that does not invert the encoder on a dispatched bundle makes that bundle's
  own canonical bytes recover other calls. So the `SOL-ABI` premise is load-bearing here, and also
  in O1's `ClaimedBundleValidatedOrCollision`, whose conclusion fails on the same run.
* `WithoutOnlyInteropCenterClaimRecoversUndispatchedCalls`: without `onlyInteropCenter` on
  `append`, on a run that dispatched nothing, a claim with canonical bytes finds a `Revertable` leg.
  So the headline rests on the deployed code's caller check, through O1's
  `CommittedLegsAreValidatedDispatches`.
* `SaltClashLetsOneBundleBeRecoveredTwice`: under a colliding keccak, two senders dispatch one
  bundle on two flows. Two successful claims with the same canonical bytes then recover it twice,
  neither claim is a claim collision, and the salt-clash disjunct of
  `EachBundleRecoveredAtMostOnce` holds.
* `WithoutSaltCheckOneBundleRecoveredTwice`: without the salt check, one sender dispatches one
  bundle on two flows, and two successful claims with the same canonical bytes recover it twice.
  Every disjunct of `EachBundleRecoveredAtMostOnce` fails there. So at-most-once rests on the salt
  check.
* `ClaimCollisionLetsOneBundleBeRecoveredTwice`: under a colliding keccak, two successful claims
  on two flows with the same bytes, the canonical bytes of a dispatch of one of the flows, recover
  that dispatch's bundle twice. One claim reads that dispatch's leg; the other reads a leg of the
  other flow through a claim collision, in either order. The colliding claim's disjunct is the only
  disjunct of `EachBundleRecoveredAtMostOnce` that holds.
* `WithoutRoundTripOneBundleRecoveredTwice`: on a run of the deployed code with no collision, two
  successful claims read two different legs of one flow, with the canonical bytes of two
  dispatches of that flow. A decoder that does not invert the encoder reads the second claim's
  bytes as the first claim's bundle, which is then recovered twice. Every disjunct of
  `EachBundleRecoveredAtMostOnce` fails there.
* `WithoutOnlyInteropCenterOneBundleRecoveredTwice`: without `onlyInteropCenter`, a leg of a
  second flow that no dispatch backs is `Revertable`, and two successful claims with one
  dispatch's canonical bytes recover its bundle twice, once per flow. Every disjunct of
  `EachBundleRecoveredAtMostOnce` fails there.

## Non-vacuity

* `ClaimBindingWitness` (built from O1's `ClaimWitness`) meets, on the honest run, every premise of
  the headline, of its bounded form, of `ClaimSourceChainIsThisChainOrCollision`,
  `RecoveredCallsAreDispatchedCalls` and `CanonicalBytesReadTheirLeg`. The leg is `Revertable`, the
  first disjunct is true and the collision false, and it names the one recovery call. Its log
  `[wD1, wD2]` with `wD1` atomic also meets the premises of `ClaimIdentifiesOneDispatch`, which can
  hold only with `i = j`.
* `ClaimBindingWithoutValueCheckWitness` and `ClaimBindingWithoutSaltCheckWitness` meet the
  premises of `ClaimBindingIndependentOfSaltAndValueChecks` with the two other variants of the
  code that keep `onlyInteropCenter`. Without `_validateAtomicBundle`, the claim recovers a
  dispatched bundle that carries value. Without the salt check, it recovers a dispatch on a run
  in which one sender dispatched one bundle on two flows.
* `ClaimBindingNonCanonicalWitness` meets the premises of the two negative liveness results, with
  bytes that decode to the dispatched bundle but carry a trailing zero byte. The leg they read is
  `Unset`, and the collision is false.
* `ClaimBindingTwoClaimsWitness` meets every premise of `EachBundleRecoveredAtMostOnce` and of its
  bounded form with two successful claims. The two bundles differ, and every break disjunct is
  false.
* `ClaimedBundleIsDispatchedImpliesValidated` takes the headline's conclusion as its premise: its
  first disjunct holds in `ClaimBindingWitness`, its second in
  `CollisionLetsAClaimRecoverUndispatchedCalls`.
-/

namespace Contracts.InteropCenter.History

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
- the decoded calls are related to `d`'s own call starters by `FormsCall` for `d`'s own sender
  (InteropCenter.sol:539-540, :701-751): each call's value is its starter's `interopCallValue`, a
  direct call's target, data and `from` are its starter's recipient and data and `d`'s sender, and
  an indirect call's `from` is its starter's recipient;
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
`d`'s bundle but are not its canonical encoding: for example, they carry trailing bytes, or another
`version`, or any other encoding the decoder accepts. Then for every flow `f`, the leg
`claimRefund(f, x)` reads is `Unset`, or the pinned claim collision holds. -/
def Properties.ReencodedBundleNeverClaims : Prop :=
  ∀ (P : Params) (dec : List UInt8 → Bundle) (S : State), Reach deployed P init S →
    DecodesDispatchedBundles P dec S.log →
    ∀ d ∈ S.log, ∀ (f : Word) (x : List UInt8), dec x = d.bundle → x ≠ P.enc d.bundle →
      S.manager.legState f (claimRefundHash P dec x) = .Unset ∨ ClaimHashCollision P dec S.log f x

/-! ## Countermodels: each premise and disjunct is needed -/

/-- **THE COLLISION DISJUNCT IS NEEDED: A COLLISION LETS A CLAIM RECOVER UNDISPATCHED CALLS.** There
is a run of the deployed code, with a colliding keccak and a decoder that inverts the encoder on the
run's bundles, and bytes `x` such that:
- `x` is the canonical encoding of the bundle it decodes to;
- `claimRefund(f, x)` finds its leg `Revertable`, so the claim passes its state check;
- `x` is not a dispatched bundle's (the headline's first disjunct fails), and the claim collision
  holds;
- the calls `_recoverBundle` would make are those of no dispatch of the run, so the decoded bundle
  is no dispatch's;
- one of the decoded calls carries native value. -/
def Properties.CollisionLetsAClaimRecoverUndispatchedCalls : Prop :=
  ∃ (P : Params) (dec : List UInt8 → Bundle) (S : State) (f : Word) (x : List UInt8),
    Reach deployed P init S ∧ DecodesDispatchedBundles P dec S.log ∧ x = P.enc (dec x) ∧
    S.manager.legState f (claimRefundHash P dec x) = .Revertable ∧
    ¬ ClaimRecoversDispatch P dec S.log f x ∧ ClaimHashCollision P dec S.log f x ∧
    (∀ d ∈ S.log, recoverBundleCalls (dec x) ≠ recoverBundleCalls d.bundle) ∧ ¬ Validated (dec x)

/-- **THE ROUND-TRIP PREMISE IS NEEDED.** There is a run of the deployed code whose decoder does not
invert the encoder on the run's bundles, and bytes `x` such that:
- `x` is the canonical encoding of the bundle of an atomic dispatch of flow `f` in the log;
- `claimRefund(f, x)` finds its leg `Revertable`;
- neither disjunct of the headline holds, and in particular there is no claim collision;
- the calls `_recoverBundle` would make are those of no dispatch of the run;
- a decoded call carries native value, so the conclusion of O1's
  `ClaimedBundleValidatedOrCollision` fails as well. -/
def Properties.WithoutRoundTripClaimRecoversUndispatchedCalls : Prop :=
  ∃ (P : Params) (dec : List UInt8 → Bundle) (S : State) (f : Word) (x : List UInt8),
    Reach deployed P init S ∧ ¬ DecodesDispatchedBundles P dec S.log ∧
    (∃ d ∈ S.log, d.isAtomic = true ∧ d.atomicSend.flowId = f ∧ x = P.enc d.bundle) ∧
    S.manager.legState f (claimRefundHash P dec x) = .Revertable ∧
    ¬ ClaimRecoversDispatch P dec S.log f x ∧ ¬ ClaimHashCollision P dec S.log f x ∧
    (∀ d ∈ S.log, recoverBundleCalls (dec x) ≠ recoverBundleCalls d.bundle) ∧ ¬ Validated (dec x)

/-- **`onlyInteropCenter` IS NEEDED: WITHOUT IT, A CLAIM RECOVERS A BUNDLE NO ONE DISPATCHED.** There
is a run of the code without `onlyInteropCenter` on `append` (AtomicFlowManager.sol:76-79) that
dispatches nothing, and bytes `x` such that:
- `x` is the canonical encoding of the bundle it decodes to;
- `claimRefund(f, x)` finds its leg `Revertable`;
- neither disjunct of the headline holds;
- a decoded call carries native value. -/
def Properties.WithoutOnlyInteropCenterClaimRecoversUndispatchedCalls : Prop :=
  ∃ (P : Params) (dec : List UInt8 → Bundle) (S : State) (f : Word) (x : List UInt8),
    Reach withoutOnlyInteropCenter P init S ∧ S.log = [] ∧ DecodesDispatchedBundles P dec S.log ∧
    x = P.enc (dec x) ∧ S.manager.legState f (claimRefundHash P dec x) = .Revertable ∧
    ¬ ClaimRecoversDispatch P dec S.log f x ∧ ¬ ClaimHashCollision P dec S.log f x ∧
    ¬ Validated (dec x)

/-- **THE SALT CHECK IS NEEDED FOR AT-MOST-ONCE: WITHOUT IT, ONE BUNDLE IS RECOVERED TWICE.** There
is a run of the code without the salt check (InteropCenter.sol:479-482) meeting every other premise
of `EachBundleRecoveredAtMostOnce`, with both claims on the same bytes `x`, such that:
- one sender dispatches one bundle atomically on two flows `f ≠ f'`, and `x` is its canonical
  encoding;
- the claim `claimRefund(f, x)` passes its state check, and after its write the claim
  `claimRefund(f', x)` passes its state check too;
- neither claim is a claim collision, and no two dispatches of the run have the cross-sender salt
  clash.

Every disjunct of the conclusion of `EachBundleRecoveredAtMostOnce` fails: the two recovered
bundles are both `dec x`. -/
def Properties.WithoutSaltCheckOneBundleRecoveredTwice : Prop :=
  ∃ (P : Params) (dec : List UInt8 → Bundle) (S₀ S₂ : State) (f f' : Word) (x : List UInt8),
    Reach withoutSaltCheck P init S₀ ∧
    S₀.manager.legState f (claimRefundHash P dec x) = .Revertable ∧
    Reach withoutSaltCheck P
      { S₀ with manager := S₀.manager.set f (claimRefundHash P dec x) .Reverted } S₂ ∧
    DecodesDispatchedBundles P dec S₂.log ∧
    S₂.manager.legState f' (claimRefundHash P dec x) = .Revertable ∧
    f ≠ f' ∧
    (∃ d ∈ S₂.log, ∃ d' ∈ S₂.log, d.sender = d'.sender ∧ d.bundle = d'.bundle ∧
      d.isAtomic = true ∧ d.atomicSend.flowId = f ∧ d'.isAtomic = true ∧
      d'.atomicSend.flowId = f' ∧ x = P.enc d.bundle) ∧
    ¬ ClaimHashCollision P dec S₀.log f x ∧ ¬ ClaimHashCollision P dec S₂.log f' x ∧
    ¬ ∃ d ∈ S₂.log, ∃ d' ∈ S₂.log, CrossSenderSaltClash P d d'

/-- **THE SALT-CLASH DISJUNCT IS NEEDED: ONE BUNDLE RECOVERED TWICE.** Under a colliding keccak,
there is a run of the deployed code meeting every premise of `EachBundleRecoveredAtMostOnce`, with
both claims on the same bytes `x`, on two flows `f ≠ f'`:
- the claim `claimRefund(f, x)` passes its state check;
- after its write, the claim `claimRefund(f', x)` passes its state check too;
- neither claim is a claim collision;
- the salt-clash disjunct holds: `x` is the canonical encoding of the one bundle that two dispatches
  of the run carry, one atomic on `f` and one on `f'`, with the cross-sender salt clash between
  them.

So the same bundle's recovery calls run twice, and the salt-clash disjunct is the only one that
holds. -/
def Properties.SaltClashLetsOneBundleBeRecoveredTwice : Prop :=
  ∃ (P : Params) (dec : List UInt8 → Bundle) (S₀ S₂ : State) (f f' : Word) (x : List UInt8),
    Reach deployed P init S₀ ∧
    S₀.manager.legState f (claimRefundHash P dec x) = .Revertable ∧
    Reach deployed P
      { S₀ with manager := S₀.manager.set f (claimRefundHash P dec x) .Reverted } S₂ ∧
    DecodesDispatchedBundles P dec S₂.log ∧
    S₂.manager.legState f' (claimRefundHash P dec x) = .Revertable ∧
    f ≠ f' ∧ ¬ ClaimHashCollision P dec S₀.log f x ∧ ¬ ClaimHashCollision P dec S₂.log f' x ∧
    ∃ d ∈ S₂.log, ∃ d' ∈ S₂.log,
      d.isAtomic = true ∧ d.atomicSend.flowId = f ∧ x = P.enc d.bundle ∧
      d'.isAtomic = true ∧ d'.atomicSend.flowId = f' ∧ x = P.enc d'.bundle ∧
      d.bundle = d'.bundle ∧ CrossSenderSaltClash P d d'

/-- **THE CLAIM-COLLISION DISJUNCTS ARE NEEDED: ONE BUNDLE RECOVERED TWICE.** Under a colliding
keccak, there are two runs of the deployed code, each meeting every premise of
`EachBundleRecoveredAtMostOnce` with both claims on the same bytes `x`, on two flows `f ≠ f'`, so
that the two recovered bundles are both `dec x`:
- in the first run, the first claim recovers a dispatch of flow `f` and is not a claim collision,
  and the second claim is a claim collision;
- in the second run, the first claim is a claim collision, and the second claim recovers a dispatch
  of flow `f'` and is not a claim collision;
- in both runs the salt-clash disjunct fails.

So in each run exactly one disjunct of the conclusion of `EachBundleRecoveredAtMostOnce` holds: the
second claim's collision in the first run, the first claim's in the second. -/
def Properties.ClaimCollisionLetsOneBundleBeRecoveredTwice : Prop :=
  (∃ (P : Params) (dec : List UInt8 → Bundle) (S₀ S₂ : State) (f f' : Word) (x : List UInt8),
    Reach deployed P init S₀ ∧
    S₀.manager.legState f (claimRefundHash P dec x) = .Revertable ∧
    Reach deployed P
      { S₀ with manager := S₀.manager.set f (claimRefundHash P dec x) .Reverted } S₂ ∧
    DecodesDispatchedBundles P dec S₂.log ∧
    S₂.manager.legState f' (claimRefundHash P dec x) = .Revertable ∧
    f ≠ f' ∧ ClaimRecoversDispatch P dec S₀.log f x ∧ ¬ ClaimHashCollision P dec S₀.log f x ∧
    ClaimHashCollision P dec S₂.log f' x ∧
    ¬ ∃ d ∈ S₂.log, ∃ d' ∈ S₂.log,
      d.isAtomic = true ∧ d.atomicSend.flowId = f ∧ x = P.enc d.bundle ∧
      d'.isAtomic = true ∧ d'.atomicSend.flowId = f' ∧ x = P.enc d'.bundle ∧
      d.bundle = d'.bundle ∧ CrossSenderSaltClash P d d') ∧
  (∃ (P : Params) (dec : List UInt8 → Bundle) (S₀ S₂ : State) (f f' : Word) (x : List UInt8),
    Reach deployed P init S₀ ∧
    S₀.manager.legState f (claimRefundHash P dec x) = .Revertable ∧
    Reach deployed P
      { S₀ with manager := S₀.manager.set f (claimRefundHash P dec x) .Reverted } S₂ ∧
    DecodesDispatchedBundles P dec S₂.log ∧
    S₂.manager.legState f' (claimRefundHash P dec x) = .Revertable ∧
    f ≠ f' ∧ ClaimHashCollision P dec S₀.log f x ∧ ClaimRecoversDispatch P dec S₂.log f' x ∧
    ¬ ClaimHashCollision P dec S₂.log f' x ∧
    ¬ ∃ d ∈ S₂.log, ∃ d' ∈ S₂.log,
      d.isAtomic = true ∧ d.atomicSend.flowId = f ∧ x = P.enc d.bundle ∧
      d'.isAtomic = true ∧ d'.atomicSend.flowId = f' ∧ x = P.enc d'.bundle ∧
      d.bundle = d'.bundle ∧ CrossSenderSaltClash P d d')

/-- **THE ROUND TRIP IS NEEDED FOR AT-MOST-ONCE.** There is a run of the deployed code meeting every
premise of `EachBundleRecoveredAtMostOnce` except the decoder round trip, with two successful
claims on two different legs of one flow, such that:
- the first claim's bytes are the canonical bytes of a dispatch of that flow, and decode to its
  bundle;
- the second claim's bytes are the canonical bytes of a dispatch of that flow, and decode not to
  its bundle but to the bundle the first claim decodes;
- neither claim is a claim collision, and the salt-clash disjunct fails.

So every disjunct of the conclusion of `EachBundleRecoveredAtMostOnce` fails. -/
def Properties.WithoutRoundTripOneBundleRecoveredTwice : Prop :=
  ∃ (P : Params) (dec : List UInt8 → Bundle) (S₀ S₂ : State) (f f' : Word)
    (x x' : List UInt8),
    Reach deployed P init S₀ ∧
    S₀.manager.legState f (claimRefundHash P dec x) = .Revertable ∧
    Reach deployed P
      { S₀ with manager := S₀.manager.set f (claimRefundHash P dec x) .Reverted } S₂ ∧
    ¬ DecodesDispatchedBundles P dec S₂.log ∧
    S₂.manager.legState f' (claimRefundHash P dec x') = .Revertable ∧
    f = f' ∧ claimRefundHash P dec x ≠ claimRefundHash P dec x' ∧
    ClaimRecoversDispatch P dec S₀.log f x ∧
    (∃ d' ∈ S₂.log, d'.isAtomic = true ∧ d'.atomicSend.flowId = f' ∧ x' = P.enc d'.bundle ∧
      dec x' ≠ d'.bundle) ∧
    dec x' = dec x ∧
    ¬ ClaimHashCollision P dec S₀.log f x ∧ ¬ ClaimHashCollision P dec S₂.log f' x' ∧
    ¬ ∃ d ∈ S₂.log, ∃ d' ∈ S₂.log,
      d.isAtomic = true ∧ d.atomicSend.flowId = f ∧ x = P.enc d.bundle ∧
      d'.isAtomic = true ∧ d'.atomicSend.flowId = f' ∧ x' = P.enc d'.bundle ∧
      d.bundle = d'.bundle ∧ CrossSenderSaltClash P d d'

/-- **`onlyInteropCenter` IS NEEDED FOR AT-MOST-ONCE.** There is a run of the code without
`onlyInteropCenter` on `append` (AtomicFlowManager.sol:76-79) meeting every other premise of
`EachBundleRecoveredAtMostOnce`, with both claims on the same bytes `x`, on two flows `f ≠ f'`,
such that:
- the first claim recovers a dispatch of flow `f` and is not a claim collision;
- no logged atomic dispatch has flow `f'`, so the leg the second claim reads is backed by no
  dispatch, and that claim is not a claim collision;
- the salt-clash disjunct fails.

So every disjunct of the conclusion of `EachBundleRecoveredAtMostOnce` fails: the two recovered
bundles are both `dec x`. -/
def Properties.WithoutOnlyInteropCenterOneBundleRecoveredTwice : Prop :=
  ∃ (P : Params) (dec : List UInt8 → Bundle) (S₀ S₂ : State) (f f' : Word) (x : List UInt8),
    Reach withoutOnlyInteropCenter P init S₀ ∧
    S₀.manager.legState f (claimRefundHash P dec x) = .Revertable ∧
    Reach withoutOnlyInteropCenter P
      { S₀ with manager := S₀.manager.set f (claimRefundHash P dec x) .Reverted } S₂ ∧
    DecodesDispatchedBundles P dec S₂.log ∧
    S₂.manager.legState f' (claimRefundHash P dec x) = .Revertable ∧
    f ≠ f' ∧ ClaimRecoversDispatch P dec S₀.log f x ∧ ¬ ClaimHashCollision P dec S₀.log f x ∧
    (¬ ∃ d ∈ S₂.log, d.isAtomic = true ∧ d.atomicSend.flowId = f') ∧
    ¬ ClaimHashCollision P dec S₂.log f' x ∧
    ¬ ∃ d ∈ S₂.log, ∃ d' ∈ S₂.log,
      d.isAtomic = true ∧ d.atomicSend.flowId = f ∧ x = P.enc d.bundle ∧
      d'.isAtomic = true ∧ d'.atomicSend.flowId = f' ∧ x = P.enc d'.bundle ∧
      d.bundle = d'.bundle ∧ CrossSenderSaltClash P d d'

/-- **BOTH MATCHES OF `ClaimIdentifiesOneDispatch` ARE NEEDED.** There are two runs of the deployed
code, each with two atomic dispatches at different log positions:
- in the first, the two dispatches are of one flow, and their canonical bytes differ;
- in the second, they have the same canonical bytes, and their flows differ.
The second run is on `collidingParams`, a constant keccak, and works through O1 (c)'s
cross-sender salt clash (`clashLeg7`, `clashLeg8`). On a chain where keccak separates the salt
preimages, equal canonical bytes already force equal positions
(`Contracts.InteropCenter.History.Properties.DistinctDispatchesDistinctBundles` with the round trip), so
the flow match is needed only because the statement takes no hash premise. -/
def Properties.ClaimIdentifiesOneDispatchNeedsBothMatches : Prop :=
  (∃ (P : Params) (S : State), Reach deployed P init S ∧
    ∃ (i j : ℕ) (hi : i < S.log.length) (hj : j < S.log.length), i ≠ j ∧
      S.log[i].isAtomic = true ∧ S.log[j].isAtomic = true ∧
      S.log[i].atomicSend.flowId = S.log[j].atomicSend.flowId ∧
      P.enc S.log[i].bundle ≠ P.enc S.log[j].bundle) ∧
  (∃ (P : Params) (S : State), Reach deployed P init S ∧
    ∃ (i j : ℕ) (hi : i < S.log.length) (hj : j < S.log.length), i ≠ j ∧
      S.log[i].isAtomic = true ∧ S.log[j].isAtomic = true ∧
      S.log[i].atomicSend.flowId ≠ S.log[j].atomicSend.flowId ∧
      P.enc S.log[i].bundle = P.enc S.log[j].bundle)

/-! ## Non-vacuity -/

/-- **THE HEADLINE'S PREMISES HOLD, AND ITS COLLISION IS FALSE.** On O1's honest run `wS3`, the
following hold for `x`, the canonical bytes of `wD1`'s bundle:
- the decoder `wDec` inverts the encoder on the run's bundles;
- `claimRefund(7, x)` finds its leg `Revertable`, so not `Unset`, and the claim passes its state
  check;
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

/-- **THE BINDING WITHOUT THE VALUE CHECK.** The premises of
`ClaimBindingIndependentOfSaltAndValueChecks` hold for a variant of the code other than `deployed`:
there is a run of the code without `_validateAtomicBundle` (InteropCenter.sol:649), which keeps
`onlyInteropCenter`, and bytes `x` such that:
- the decoder inverts the encoder on the run's bundles;
- `claimRefund(f, x)` finds its leg `Revertable`;
- the claim recovers a dispatch of the run (the headline's first disjunct), and the claim
  collision is false;
- the recovered bundle carries native value, so O1's `Validated` conclusion fails on this run
  while the binding holds. -/
def Properties.ClaimBindingWithoutValueCheckWitness : Prop :=
  ∃ (P : Params) (dec : List UInt8 → Bundle) (S : State) (f : Word) (x : List UInt8),
    withoutValueCheck.onlyInteropCenter = true ∧
    Reach withoutValueCheck P init S ∧ DecodesDispatchedBundles P dec S.log ∧
    S.manager.legState f (claimRefundHash P dec x) = .Revertable ∧
    ClaimRecoversDispatch P dec S.log f x ∧ ¬ ClaimHashCollision P dec S.log f x ∧
    ¬ Validated (dec x)

/-- **THE BINDING WITHOUT THE SALT CHECK.** The premises of
`ClaimBindingIndependentOfSaltAndValueChecks` hold for the code without the salt check
(InteropCenter.sol:479-482), which keeps `onlyInteropCenter`, on a run in which one sender has
dispatched one bundle atomically on two different flows. There are bytes `x` such that:
- the decoder inverts the encoder on the run's bundles;
- `claimRefund(f, x)` finds its leg `Revertable`;
- the claim recovers a dispatch of the run (the headline's first disjunct), and the claim
  collision is false. -/
def Properties.ClaimBindingWithoutSaltCheckWitness : Prop :=
  ∃ (P : Params) (dec : List UInt8 → Bundle) (S : State) (f : Word) (x : List UInt8),
    withoutSaltCheck.onlyInteropCenter = true ∧
    Reach withoutSaltCheck P init S ∧ DecodesDispatchedBundles P dec S.log ∧
    (∃ d ∈ S.log, ∃ d' ∈ S.log, d.sender = d'.sender ∧ d.bundle = d'.bundle ∧
      d.isAtomic = true ∧ d'.isAtomic = true ∧ d.atomicSend.flowId ≠ d'.atomicSend.flowId) ∧
    S.manager.legState f (claimRefundHash P dec x) = .Revertable ∧
    ClaimRecoversDispatch P dec S.log f x ∧ ¬ ClaimHashCollision P dec S.log f x

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

end Contracts.InteropCenter.History
