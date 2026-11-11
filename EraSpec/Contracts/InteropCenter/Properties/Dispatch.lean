import EraSpec.Contracts.InteropCenter.Specs.Dispatch
import EraSpec.Contracts.AtomicFlowManager.Properties.RecoveryLimits

/-!
# Properties: what a dispatch guarantees

Statements about `EraSpec.Contracts.InteropCenter.Specs.Dispatch`. Proofs are in
`EraSpec.Contracts.InteropCenter.Proofs.Dispatch`. Every run starts from fresh storage (`init`) on
one chain; `deployed` is the code with all three of its checks.

## (a) A sender's salt dispatches at most once

The salt flag records exactly the `(sender, salt)` keys of the run's dispatches
(`SaltFlagRecordsDispatches`), is never cleared (`SaltFlagsNeverCleared`), and a used key has no
further dispatch (`UsedSaltHasNoDispatch`). So the run's keys are pairwise distinct
(`EachSaltDispatchesOnce`). Without the check, a sender dispatches the same bundle twice, hence the
same bundle hash with no hash collision (`WithoutSaltCheckABundleRepeats`).

## (b) An appended bundle carries no native value

`AttackVectors.RecoveryLimits.Properties.validation_unbypassable` takes its funnel as a premise,
`sole_path : ∀ b, Committed b → Validated b`, and concludes `Validated b`; as stated it is the
premise applied. Here the premise is a theorem about the center's only `append` call site
(`SolePath`, and `ValidationUnbypassableDischarged` instantiates the abstract statement with it).
On the manager's own state: every leg that is not `Unset` was committed by an atomic dispatch of
this chain, with that flow id and bundle hash, whose bundle passed `_validateAtomicBundle`
(`CommittedLegsAreValidatedDispatches`); a step commits a fresh leg only that way
(`OnlyADispatchCommitsALeg`). The bundle `claimRefund` decodes and recovers for such a leg carries
no value, or keccak collides on two named preimages (`ClaimedBundleValidatedOrCollision`, which
follows `claimRefund`'s own hash of the bytes it is given); any bundle whose hash is a committed
leg carries no value or clashes with the logged one (`PresentedBundleValidatedOrClash`). Every
atomic dispatch burns no base token
(`AtomicDispatchBurnsNothing`), because the burned total is the calls' values
(`BurnedTotalIsCallValues`). Each leg is appended at most once and never returns to `Unset`
(`EachLegAppendedOnce`, `AppendedLegsStayCommitted`), so the dispatch behind a committed leg is
unique.

Each of the two checks is load-bearing: without `_validateAtomicBundle` a value-carrying leg is
committed (`WithoutValueCheckValueLegCommits`); without `onlyInteropCenter` a leg backed by no
dispatch at all is committed (`WithoutOnlyInteropCenterUnbackedLegCommits`). The collision
disjunct is needed (`CollisionLetsAValueBundleMatchACommittedLeg`).

## (c) Distinct dispatches, distinct bundle-hash preimages

Two dispatches at different positions of a run carry different bundles, unless two **different
senders** used the **same salt** and keccak collides on their two packed preimages
(`DistinctDispatchesDistinctBundles`, no hash premise). For one sender no hash assumption is
needed at all: the bundle carries the user salt itself (:509). If the encoder separates the run's
bundles, the bundle-hash preimages differ too (`DistinctDispatchesDistinctPreimages`), and the
bundle hashes differ or keccak collides on those two preimages
(`DistinctDispatchesDistinctBundleHashes`). With keccak injective on the run's own preimages — at
most two per dispatch — every bundle hash of the run is unique (`LoggedRunBundleHashesUnique`).
An atomic bundle's bytes are never the bytes of a bundle published to L1, unless the same
cross-sender clash (`AtomicBytesNeverPublished`).

## Non-vacuity

`EncInjOnSatisfiable` and `KeccakInjOnSatisfiable` show the run-local premises can hold for any
list. `DispatchWitness` is a run meeting every premise of the (b) and (c) headlines, with an atomic
leg committed and then authorized, a value-carrying public bundle, distinct bundle hashes, and both
clash predicates false on it; `StepWitness` meets the per-step premises on the same run, and
`ClaimWitness` the premises of `ClaimedBundleValidatedOrCollision`, with its collision false.
`SaltClashLetsTwoSendersShareABundle` fires the clash disjunct of (c): under a colliding keccak,
two senders dispatch one bundle.
-/

namespace Contracts.InteropCenter

open Contracts.AtomicFlowManager (LegState)

/-! ## (a) Sender salts -/

/-- **THE SALT FLAG RECORDS EXACTLY THE DISPATCHED KEYS.** Along any run from fresh storage, with
or without the checks, `isInteropBundleSaltUsed[a][s]` is set iff some dispatch of the run was by
`a` with salt `s`. -/
def Properties.SaltFlagRecordsDispatches : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), Reach K P init S →
    ∀ (a : Address) (s : Word), S.saltUsed a s = true ↔ ∃ d ∈ S.log, d.sender = a ∧ d.salt = s

/-- **A SET SALT FLAG STAYS SET.** No step clears `isInteropBundleSaltUsed`. -/
def Properties.SaltFlagsNeverCleared : Prop :=
  ∀ (K : Checks) (P : Params) (S S' : State), Step K P S S' →
    ∀ (a : Address) (s : Word), S.saltUsed a s = true → S'.saltUsed a s = true

/-- **A USED SALT HAS NO FURTHER DISPATCH.** If `d`'s sender has used `d`'s salt, no step of the
deployed code appends `d` to the log. -/
def Properties.UsedSaltHasNoDispatch : Prop :=
  ∀ (P : Params) (S S' : State) (d : Dispatch), S.saltUsed d.sender d.salt = true →
    Step deployed P S S' → S'.log ≠ S.log ++ [d]

/-- **HEADLINE (a): EACH `(sender, salt)` DISPATCHES AT MOST ONE BUNDLE.** Along any run from
fresh storage, the `(sender, salt)` keys of the run's dispatches are pairwise distinct. -/
def Properties.EachSaltDispatchesOnce : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S → (S.log.map Dispatch.key).Nodup

/-- **WITHOUT THE SALT CHECK, ONE BUNDLE IS DISPATCHED TWICE.** A run of the code without
:479-482 in which two dispatches at different positions carry the same bundle, so the same bundle
hash, whatever keccak is: no collision is needed. -/
def Properties.WithoutSaltCheckABundleRepeats : Prop :=
  ∃ (P : Params) (S : State), Reach withoutSaltCheck P init S ∧
    ∃ (i j : ℕ) (hi : i < S.log.length) (hj : j < S.log.length), i ≠ j ∧
      S.log[i].bundle = S.log[j].bundle ∧
      bundleHash P S.log[i].bundle = bundleHash P S.log[j].bundle

/-! ## (b) The atomic-value check and the only `append` -/

/-- **EVERY ATOMIC DISPATCH PASSED `_validateAtomicBundle`.** Every atomic dispatch of a run of
the deployed code has no call carrying native value. -/
def Properties.AtomicDispatchesCarryNoValue : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∀ d ∈ S.log, d.isAtomic = true → Validated d.bundle

/-- **THE BURNED TOTAL IS THE CALLS' VALUES.** For every dispatch of any run, `_sendBundle`'s
`totalBurnedCallsValue` equals the sum of the values of the bundle's calls, since each call's
`value` is its starter's `interopCallValue` (:738, :747). -/
def Properties.BurnedTotalIsCallValues : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), Reach K P init S →
    ∀ d ∈ S.log, totalBurnedCallsValue d.starters = (d.bundle.calls.map InteropCall.value).sum

/-- **AN ATOMIC DISPATCH BURNS NO BASE TOKEN.** For every atomic dispatch of a run of the deployed
code, `totalBurnedCallsValue = 0`, so `_ensureCorrectTotalValue` calls neither
`L2_BASE_TOKEN_HOLDER.burnAndStartBridging` (:429-434) nor `bridgehubDepositBaseToken` (:440-447):
the value no `recoverAtomicCall` can reverse never leaves on an atomic leg. -/
def Properties.AtomicDispatchBurnsNothing : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∀ d ∈ S.log, d.isAtomic = true → totalBurnedCallsValue d.starters = 0

/-- **ONLY A DISPATCH COMMITS A LEG.** One step of the deployed code moves a leg out of `Unset`
only by appending to the log an atomic dispatch with that flow id and bundle hash whose bundle
passed `_validateAtomicBundle`: the per-step form of the funnel. -/
def Properties.OnlyADispatchCommitsALeg : Prop :=
  ∀ (P : Params) (S S' : State), Step deployed P S S' →
    ∀ (f h : Word), S.manager.legState f h = .Unset → S'.manager.legState f h ≠ .Unset →
      ∃ d, S'.log = S.log ++ [d] ∧ d.isAtomic = true ∧ d.atomicSend.flowId = f ∧
        bundleHash P d.bundle = h ∧ Validated d.bundle

/-- **HEADLINE (b): EVERY COMMITTED LEG IS A VALIDATED ATOMIC DISPATCH OF THIS CHAIN.** Along any
run of the deployed code from fresh storage, every leg `(f, h)` of the manager that is not `Unset`
(`Committed`, `Revertable` or `Reverted`) was committed by an atomic dispatch of the run with flow id
`f` and bundle hash `h`; that dispatch's bundle carries no native value, was built with
`sourceChainId = block.chainid`, and `h` is keccak of `abi.encode(block.chainid, abi.encode(bundle))`. -/
def Properties.CommittedLegsAreValidatedDispatches : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∀ (f h : Word), S.manager.legState f h ≠ .Unset →
      ∃ d ∈ S.log, d.isAtomic = true ∧ d.atomicSend.flowId = f ∧ bundleHash P d.bundle = h ∧
        Validated d.bundle ∧ d.bundle.sourceChainId = P.chainId

/-- **`sole_path`, DERIVED.** Along any run of the deployed code, every bundle the center appended
passed `_validateAtomicBundle`. This is the premise `sole_path` of
`AttackVectors.RecoveryLimits.Properties.validation_unbypassable`, with `Committed := AppendedOn S`. -/
def Properties.SolePath : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S → ∀ b, AppendedOn S b → Validated b

/-- **`validation_unbypassable` WITH ITS PREMISE DISCHARGED.** For every reachable state of the
deployed code, the abstract funnel statement holds for the center's appended bundles with a
`sole_path` that is proved, not assumed. -/
def Properties.ValidationUnbypassableDischarged : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∃ sole_path : (∀ b, AppendedOn S b → Validated b),
      ∀ (b : Bundle) (h : AppendedOn S b),
        AttackVectors.RecoveryLimits.Properties.validation_unbypassable
          Validated (AppendedOn S) sole_path h

/-- **ANY BUNDLE WHOSE HASH IS A COMMITTED LEG CARRIES NO VALUE, OR CLASHES.** Along any run of the
deployed code, if the leg `(f, bundleHash b)` of some bundle `b` is not `Unset`, then `b` carries no
native value, or `b` and the atomic dispatch of flow `f` logged for that leg are two different
bundles with one bundle hash. (`ClaimedBundleValidatedOrCollision` is the form that follows
`claimRefund`'s own computation.) -/
def Properties.PresentedBundleValidatedOrClash : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∀ (f : Word) (b : Bundle), S.manager.legState f (bundleHash P b) ≠ .Unset →
      Validated b ∨
        ∃ d ∈ S.log, d.isAtomic = true ∧ d.atomicSend.flowId = f ∧ BundleClash P b d.bundle

/-- **THE BUNDLE `claimRefund` RECOVERS CARRIES NO VALUE, OR KECCAK COLLIDES.** Along any run of the
deployed code whose decoder inverts the encoder on the run's bundles (`abi.decode` after
`abi.encode`, `SOL-ABI`): if `claimRefund(f, x)` finds the leg it computes from the bytes `x` not
`Unset` (AtomicFlowManager.sol:166-170), then the bundle it decodes from `x` — whose calls
`_recoverBundle` asks to reverse (:219-230) — carries no native value; or keccak collides on two
named preimages: the one `claimRefund` hashed and the one the center hashed for the logged atomic
dispatch behind that leg. Any bytes `x`, any decoded source chain. -/
def Properties.ClaimedBundleValidatedOrCollision : Prop :=
  ∀ (P : Params) (dec : List UInt8 → Bundle) (S : State), Reach deployed P init S →
    (∀ d ∈ S.log, dec (P.enc d.bundle) = d.bundle) →
    ∀ (f : Word) (x : List UInt8), S.manager.legState f (P.keccak (claimPreimage dec x)) ≠ .Unset →
      Validated (dec x) ∨
        ∃ d ∈ S.log, d.isAtomic = true ∧ d.atomicSend.flowId = f ∧
          claimPreimage dec x ≠ bundlePreimage P d.bundle ∧
          P.keccak (claimPreimage dec x) = bundleHash P d.bundle

/-- **AN APPENDED LEG NEVER RETURNS TO `Unset`.** Along any run, with or without the checks, the leg
`(flowId, bundleHash)` of every atomic dispatch of the run is not `Unset`: no step writes `Unset`. -/
def Properties.AppendedLegsStayCommitted : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), Reach K P init S →
    ∀ d ∈ S.log, d.isAtomic = true →
      S.manager.legState d.atomicSend.flowId (bundleHash P d.bundle) ≠ .Unset

/-- **EACH LEG IS APPENDED AT MOST ONCE.** Along any run, with or without the checks, the
`(flowId, bundleHash)` pairs of the run's atomic dispatches are pairwise distinct: `append`'s
`Unset` check (AtomicFlowManager.sol:93) rejects a second one, and no step returns a leg to `Unset`. -/
def Properties.EachLegAppendedOnce : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), Reach K P init S →
    ((S.log.filter Dispatch.isAtomic).map fun d => (d.atomicSend.flowId, bundleHash P d.bundle)).Nodup

/-- **WITHOUT `_validateAtomicBundle`, A VALUE-CARRYING LEG IS COMMITTED.** A run of the code
without :649 in which an atomic dispatch whose bundle has a call carrying native value is committed
in the manager. -/
def Properties.WithoutValueCheckValueLegCommits : Prop :=
  ∃ (P : Params) (S : State), Reach withoutValueCheck P init S ∧
    ∃ d ∈ S.log, d.isAtomic = true ∧ ¬ Validated d.bundle ∧
      S.manager.legState d.atomicSend.flowId (bundleHash P d.bundle) = .Committed

/-- **WITHOUT `onlyInteropCenter`, A LEG BACKED BY NO DISPATCH IS COMMITTED.** A run of the code
without AtomicFlowManager.sol:76-79 that dispatches nothing yet ends with a `Committed` leg. -/
def Properties.WithoutOnlyInteropCenterUnbackedLegCommits : Prop :=
  ∃ (P : Params) (S : State) (f h : Word), Reach withoutOnlyInteropCenter P init S ∧
    S.log = [] ∧ S.manager.legState f h = .Committed

/-- **THE COLLISION DISJUNCT IS NEEDED.** Under a colliding keccak, a run of the deployed code and a
bundle carrying native value whose bundle hash is a committed leg's. -/
def Properties.CollisionLetsAValueBundleMatchACommittedLeg : Prop :=
  ∃ (P : Params) (S : State) (f : Word) (b : Bundle), Reach deployed P init S ∧
    S.manager.legState f (bundleHash P b) ≠ .Unset ∧ ¬ Validated b

/-! ## (c) Distinct dispatches -/

/-- **(c), BUNDLES.** Along any run of the deployed code, two dispatches at different positions
carry different bundles, unless two different senders used the same salt and keccak collides on
their two `abi.encodePacked(sender, salt)` preimages. No hash premise. -/
def Properties.DistinctDispatchesDistinctBundles : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∀ (i j : ℕ) (hi : i < S.log.length) (hj : j < S.log.length), i ≠ j →
      S.log[i].bundle ≠ S.log[j].bundle ∨ CrossSenderSaltClash P S.log[i] S.log[j]

/-- **(c), BUNDLE-HASH PREIMAGES.** As above, for the bytes `encodeInteropBundleHash` hashes, if the
encoder separates the run's bundles. -/
def Properties.DistinctDispatchesDistinctPreimages : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    EncInjOn P.enc (S.log.map Dispatch.bundle) →
    ∀ (i j : ℕ) (hi : i < S.log.length) (hj : j < S.log.length), i ≠ j →
      bundlePreimage P S.log[i].bundle ≠ bundlePreimage P S.log[j].bundle ∨
        CrossSenderSaltClash P S.log[i] S.log[j]

/-- **(c), BUNDLE HASHES.** As above: the two bundle hashes differ, or the cross-sender salt
clash, or keccak collides on the two dispatches' bundle-hash preimages. -/
def Properties.DistinctDispatchesDistinctBundleHashes : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    EncInjOn P.enc (S.log.map Dispatch.bundle) →
    ∀ (i j : ℕ) (hi : i < S.log.length) (hj : j < S.log.length), i ≠ j →
      bundleHash P S.log[i].bundle ≠ bundleHash P S.log[j].bundle ∨
        CrossSenderSaltClash P S.log[i] S.log[j] ∨
        BundleHashClash P S.log[i].bundle S.log[j].bundle

/-- **(c), RUN-LOCAL: EVERY BUNDLE HASH OF A RUN IS UNIQUE.** Along any run of the deployed code, if
the encoder separates the run's bundles and keccak is injective on the run's own salt preimages
and on its own bundle-hash preimages, the run's bundle hashes are pairwise distinct. -/
def Properties.LoggedRunBundleHashesUnique : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    EncInjOn P.enc (S.log.map Dispatch.bundle) →
    KeccakInjOn P.keccak (saltPreimages S.log) →
    KeccakInjOn P.keccak (bundlePreimages P S.log) →
    (S.log.map fun d => bundleHash P d.bundle).Nodup

/-- **AN ATOMIC BUNDLE'S BYTES ARE NEVER PUBLISHED TO L1, OR THE CROSS-SENDER CLASH.** Along any
run of the deployed code whose encoder separates its bundles, the bytes `abi.encode(bundle)` of an
atomic dispatch differ from those of every public dispatch, which `_sendBundleToL1` publishes
(:657), unless the cross-sender salt clash between the two. This is this chain's own half of the
fact `InteropHandlerBase/Properties/BundleStatusMachine.lean` relies on ("atomic bundles are never
published to L1"); bundles published by other chains are outside the one-chain model. -/
def Properties.AtomicBytesNeverPublished : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    EncInjOn P.enc (S.log.map Dispatch.bundle) →
    ∀ d ∈ S.log, d.isAtomic = true → ∀ d' ∈ S.log, d'.isAtomic = false →
      P.enc d.bundle ≠ P.enc d'.bundle ∨ CrossSenderSaltClash P d d'

/-! ## Non-vacuity -/

/-- **THE ENCODER PREMISE IS SATISFIABLE FOR EVERY LIST OF BUNDLES.** -/
def Properties.EncInjOnSatisfiable : Prop :=
  ∀ L : List Bundle, ∃ enc : Bundle → List UInt8, EncInjOn enc L

/-- **THE KECCAK PREMISE IS SATISFIABLE FOR EVERY LIST NO LONGER THAN THE WORD SPACE.** -/
def Properties.KeccakInjOnSatisfiable : Prop :=
  ∀ L : List (List UInt8), L.length ≤ UInt256.size → ∃ k : List UInt8 → Word, KeccakInjOn k L

/-- **THE HEADLINES' PREMISES HOLD ON A NONTRIVIAL RUN, AND THE CLASHES ARE FALSE ON IT.** On the
honest witness chain: sender `1` dispatches an atomic leg of flow `7`, sender `2` dispatches a public
bundle whose call carries value `9`, and the leg is authorized. Every premise of the (b) and (c)
headlines holds; the leg is `Revertable`; the public bundle is not `Validated` (the check is the
atomic branch's only); the two bundle hashes differ; and neither clash predicate holds on the two
dispatches. -/
def Properties.DispatchWitness : Prop :=
  Reach deployed wParams init wS3 ∧ wS3.log = [wD1, wD2] ∧
    EncInjOn wParams.enc (wS3.log.map Dispatch.bundle) ∧
    KeccakInjOn wParams.keccak (saltPreimages wS3.log) ∧
    KeccakInjOn wParams.keccak (bundlePreimages wParams wS3.log) ∧
    wD1.isAtomic = true ∧
    wS3.manager.legState wD1.atomicSend.flowId (bundleHash wParams wD1.bundle) = .Revertable ∧
    wD2.isAtomic = false ∧ ¬ Validated wD2.bundle ∧
    bundleHash wParams wD1.bundle ≠ bundleHash wParams wD2.bundle ∧
    ¬ SaltClash wParams wD1 wD2 ∧ ¬ BundleHashClash wParams wD1.bundle wD2.bundle

/-- **THE PER-STEP PREMISES ARE SATISFIABLE, ON THE SAME RUN.** The step `wS1 → wS2` starts from a
state in which `wD1`'s salt is used (the premises of `UsedSaltHasNoDispatch` and
`SaltFlagsNeverCleared`); the step `init → wS1` moves `wD1`'s leg out of `Unset` (the premises of
`OnlyADispatchCommitsALeg`); and `wD1`'s bundle is appended in `wS3` (the premise of `SolePath`). -/
def Properties.StepWitness : Prop :=
  Step deployed wParams wS1 wS2 ∧ wS1.saltUsed wD1.sender wD1.salt = true ∧
    Step deployed wParams init wS1 ∧
    init.manager.legState wD1.atomicSend.flowId (bundleHash wParams wD1.bundle) = .Unset ∧
    wS1.manager.legState wD1.atomicSend.flowId (bundleHash wParams wD1.bundle) ≠ .Unset ∧
    AppendedOn wS3 wD1.bundle

/-- **`ClaimedBundleValidatedOrCollision`'S PREMISES HOLD, AND ITS COLLISION IS FALSE.** On the
honest run, the decoder `wDec` inverts the encoder on the run's bundles, and `claimRefund(7, x)` with
`x` the bytes of `wD1`'s bundle finds its leg (`Revertable`, so not `Unset`): the preimage it hashes
is the one the center hashed, so no collision. -/
def Properties.ClaimWitness : Prop :=
  (∀ d ∈ wS3.log, wDec (wParams.enc d.bundle) = d.bundle) ∧
    wS3.manager.legState 7 (wParams.keccak (claimPreimage wDec (wParams.enc wD1.bundle)))
      = .Revertable ∧
    claimPreimage wDec (wParams.enc wD1.bundle) = bundlePreimage wParams wD1.bundle

/-- **THE (c) CLASH DISJUNCT FIRES.** Under a colliding keccak, a run of the deployed code in which
two different senders, with the same salt and the same indirect call, dispatch one and the same
bundle — so one bundle hash — and the clash is the cross-sender salt clash. -/
def Properties.SaltClashLetsTwoSendersShareABundle : Prop :=
  ∃ (P : Params) (S : State), Reach deployed P init S ∧
    ∃ (i j : ℕ) (hi : i < S.log.length) (hj : j < S.log.length), i ≠ j ∧
      S.log[i].bundle = S.log[j].bundle ∧ CrossSenderSaltClash P S.log[i] S.log[j]

end Contracts.InteropCenter
