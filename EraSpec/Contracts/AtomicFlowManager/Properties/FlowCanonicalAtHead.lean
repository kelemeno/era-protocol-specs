import EraSpec.Contracts.AtomicFlowManager.Specs.FlowCanonicalAtHead

/-!
# Properties: what `_validateAndComputeFlowId` accepts, at head (`3605e82`)

Statements about `EraSpec.Contracts.AtomicFlowManager.Specs.FlowCanonicalAtHead`; proofs in
`EraSpec.Contracts.AtomicFlowManager.Proofs.FlowCanonicalAtHead`.

## Necessary and sufficient

The pin's `AttackVectors.FlowCanonical.Valid` is the conjunction of the two checks the pin
ran: the neighbour sort check and the length check. At head those two checks are
unchanged and two more run before them, so:

* `Valid` is still **necessary** (`Properties.AcceptedPreimageIsValid`). Every
  `AttackVectors.FlowCanonical` consequence of `Valid` (no duplicated leg, a functional
  pairing, one presentation per leg set) therefore holds of every accepted preimage
  (`Properties.AcceptedPreimageIsCanonical`, `Properties.DeclaredSourceChainUnique`).
* `Valid` is **no longer sufficient** (`Properties.ValidNoLongerSufficient`, one
  countermodel per new check). What is now sufficient, and necessary, is `Valid` plus
  `version = 0x01` plus at most eight legs (`Properties.AcceptedIffValidVersionCap`).

## One function, three paths

`append`, `requireFlowFinalized` and `authorizeRefund` all call
`_validateAndComputeFlowId`. So the flow id `append` computes for a preimage is exactly
the id the other two accept with it (`Properties.SharedValidationNoDrift`), and a preimage
the new checks reject is rejected on all three (`Properties.NewChecksRejectOnEveryPath`).
This is the source's "canonicalization cannot drift" (`AtomicFlowManager.sol:345`) and the
cap's "rejected identically on the append, finalize and refund paths"
(`IAtomicInterop.sol:97-98`), as theorems about the model.

## Binding

Two flows that pass `_checkFlowId` with one id are the same flow, or `enc` collides on
their two preimages (`Properties.CheckedFlowsAgreeOrClash`). That is an unfolding, as for
the pin (`ASSUMPTIONS.md`, "Recorded but without protocol content"), and so is
`Properties.DifferentVersionsShareAnIdOnlyByClash`. Its use is in the
protocol topic `FlowBindingAtHead`, where both preimages come from a run's own log.
-/

namespace Contracts.FlowCanonicalAtHead

open AttackVectors.FlowCanonical

/-! ## What the function accepts -/

/-- **ACCEPTANCE IS EXACTLY THE FOUR CHECKS, AND THE ID IS THE HASH OF THE PREIMAGE.** -/
def Properties.ValidateIsSomeIffAccepted : Prop :=
  ∀ (enc : PreimageHash) (P : FlowPreimage) (id : UInt256),
    validateAndComputeFlowId enc P = some id ↔ PreimageAccepted P ∧ id = enc P

/-- **`_checkFlowId` PASSES IFF THE PREIMAGE IS ACCEPTED AND HASHES TO THE CLAIMED ID.** -/
def Properties.CheckFlowIdIff : Prop :=
  ∀ (enc : PreimageHash) (F : AtomicFlow),
    CheckFlowId enc F ↔ PreimageAccepted F.preimage ∧ enc F.preimage = F.flowId

/-- **`Valid` IS STILL NECESSARY.** Every preimage `_validateAndComputeFlowId` accepts passes
the pin's two checks, `AttackVectors.FlowCanonical.Valid`. -/
def Properties.AcceptedPreimageIsValid : Prop :=
  ∀ (enc : PreimageHash) (P : FlowPreimage) (id : UInt256),
    validateAndComputeFlowId enc P = some id → Valid P.arrays

/-- **WHAT IS NOW SUFFICIENT.** A preimage is accepted iff it is `Valid`, carries version
`0x01`, and has at most `MAX_ATOMIC_FLOW_LEGS` legs. -/
def Properties.AcceptedIffValidVersionCap : Prop :=
  ∀ P : FlowPreimage, PreimageAccepted P ↔
    Valid P.arrays ∧ P.version = ATOMIC_FLOW_PREIMAGE_VERSION
      ∧ P.legBundleHashes.length ≤ MAX_ATOMIC_FLOW_LEGS

/-- **`Valid` IS NO LONGER SUFFICIENT: ONE COUNTERMODEL PER NEW CHECK.**

1. A `Valid` preimage with two legs and version `0x02` is rejected, for every hash.
2. A `Valid` preimage with version `0x01` and nine legs is rejected, for every hash. -/
def Properties.ValidNoLongerSufficient : Prop :=
  (∃ P : FlowPreimage, Valid P.arrays ∧ P.legBundleHashes.length ≤ MAX_ATOMIC_FLOW_LEGS
      ∧ P.version ≠ ATOMIC_FLOW_PREIMAGE_VERSION
      ∧ ∀ enc : PreimageHash, validateAndComputeFlowId enc P = none)
    ∧ (∃ P : FlowPreimage, Valid P.arrays ∧ P.version = ATOMIC_FLOW_PREIMAGE_VERSION
      ∧ MAX_ATOMIC_FLOW_LEGS < P.legBundleHashes.length
      ∧ ∀ enc : PreimageHash, validateAndComputeFlowId enc P = none)

/-- **THE NEW CHECKS REJECT ON EVERY PATH.** A preimage with another version byte, or with
more than eight legs, makes `append` revert (no id is computed) and makes `_checkFlowId`
revert for every claimed id, so `requireFlowFinalized` and `authorizeRefund` revert too. -/
def Properties.NewChecksRejectOnEveryPath : Prop :=
  ∀ (enc : PreimageHash) (P : FlowPreimage),
    (P.version ≠ ATOMIC_FLOW_PREIMAGE_VERSION ∨ MAX_ATOMIC_FLOW_LEGS < P.legBundleHashes.length) →
      validateAndComputeFlowId enc P = none ∧ ∀ id : UInt256, ¬ CheckFlowId enc ⟨id, P⟩

/-- **ONE FUNCTION FOR ALL THREE PATHS.** `append` computes id `f` from preimage `P` iff the
flow `⟨f, P⟩` passes `_checkFlowId`, which `requireFlowFinalized` and `authorizeRefund`
run. This holds by unfolding `CheckFlowId`: the model has one validation function because the
source has one (`AtomicFlowManager.sol:108, :335`). It records that fact; it is not evidence
beyond the transcription. -/
def Properties.SharedValidationNoDrift : Prop :=
  ∀ (enc : PreimageHash) (P : FlowPreimage) (f : UInt256),
    validateAndComputeFlowId enc P = some f ↔ CheckFlowId enc ⟨f, P⟩

/-- **THE CAP BOUNDS THE GATE'S WORK.** An accepted preimage has at most eight legs, so
`requireFlowFinalized`, which verifies one inclusion proof per leg
(`AtomicFlowManager.sol:184-207`), verifies at most eight. -/
def Properties.AcceptedHasAtMostMaxLegs : Prop :=
  ∀ P : FlowPreimage, PreimageAccepted P → P.legPairs.length ≤ MAX_ATOMIC_FLOW_LEGS

/-! ## What acceptance buys -/

/-- **AN ACCEPTED PREIMAGE IS CANONICAL.** Its bundle hashes are distinct; the positional
pairing loses no leg and has distinct keys; and any accepted preimage whose bundle hashes
are a permutation of these has the very same list. These are the pin's `FlowCanonical`
consequences of `Valid`, applied through `Properties.AcceptedPreimageIsValid`. -/
def Properties.AcceptedPreimageIsCanonical : Prop :=
  ∀ P : FlowPreimage, PreimageAccepted P →
    P.legBundleHashes.Nodup
      ∧ (P.legPairs.map Prod.fst).Nodup ∧ P.legPairs.length = P.legBundleHashes.length
      ∧ ∀ Q : FlowPreimage, PreimageAccepted Q → Q.legBundleHashes.Perm P.legBundleHashes →
          Q.legBundleHashes = P.legBundleHashes

/-- **EVERY LEG OF AN ACCEPTED PREIMAGE HAS EXACTLY ONE DECLARED SOURCE CHAIN.** -/
def Properties.DeclaredSourceChainUnique : Prop :=
  ∀ P : FlowPreimage, PreimageAccepted P → ∀ b c c' : UInt256,
    P.Declares b c → P.Declares b c' → c = c'

/-- **EVERY LISTED BUNDLE HASH IS DECLARED ON SOME CHAIN.** The length check means the
positional pairing covers every listed bundle hash. -/
def Properties.ListedLegIsDeclared : Prop :=
  ∀ P : FlowPreimage, PreimageAccepted P → ∀ b ∈ P.legBundleHashes, ∃ c, P.Declares b c

/-- **A DECLARED LEG IS LISTED.** -/
def Properties.DeclaredLegIsListed : Prop :=
  ∀ (P : FlowPreimage) (b c : UInt256), P.Declares b c →
    b ∈ P.legBundleHashes ∧ c ∈ P.legSourceChainIds

/-! ## Binding, in pinned form -/

/-- **TWO CHECKED FLOWS WITH ONE ID ARE EQUAL, OR THEIR PREIMAGES CLASH.** -/
def Properties.CheckedFlowsAgreeOrClash : Prop :=
  ∀ (enc : PreimageHash) (F F' : AtomicFlow), CheckFlowId enc F → CheckFlowId enc F' →
    F.flowId = F'.flowId → F = F' ∨ PreimageClash enc F.preimage F'.preimage

/-- **TWO VERSIONS SHARE AN ID ONLY BY A COLLISION ON THE TWO PREIMAGES.** The pinned form
of the NatSpec claim that a preimage of one version can never "hash to the same `flowId`"
under the rules of another (`IAtomicInterop.sol:86-88`): the version byte is part of the
hashed preimage, so equal ids for different versions are a `PreimageClash`. An unfolding:
different version bytes make the two preimages different. It does not say the collision
cannot happen. -/
def Properties.DifferentVersionsShareAnIdOnlyByClash : Prop :=
  ∀ (enc : PreimageHash) (P P' : FlowPreimage), P.version ≠ P'.version →
    enc P = enc P' → PreimageClash enc P P'

/-- **THE CLASH DISJUNCT IS NOT A TAUTOLOGY.** The hash honest about `P0` passes `P0`'s own
flow and clashes with no preimage at all. -/
def Properties.HonestPreimageHashNoClash : Prop :=
  ∀ (P0 : FlowPreimage) (id : UInt256), PreimageAccepted P0 →
    CheckFlowId (honestPreimageHash P0 id) ⟨id, P0⟩
      ∧ ∀ P : FlowPreimage, ¬ PreimageClash (honestPreimageHash P0 id) P0 P

/-- **BOUNDED INJECTIVITY IS SATISFIABLE.** For every list of fewer than `2^256` preimages
there is a hash with no clash on it. So the `…On` premise is a real assumption about a
run's own preimages, unlike global injectivity, which no function from preimages to words
satisfies. -/
def Properties.PreimageHashInjOnSatisfiable : Prop :=
  ∀ Ps : List FlowPreimage, Ps.length < UInt256.size → ∃ enc : PreimageHash, PreimageHashInjOn enc Ps

/-! ## Witness -/

/-- **THE PREMISES ARE SATISFIABLE, AND BOTH DISJUNCTS OF THE BINDING ARE LIVE.**

* The two-leg preimage `P` (bundle `1` on chain `0`, bundle `2` on chain `1`) is accepted,
  and the flow `⟨enc P, P⟩` passes `_checkFlowId`, for every hash `enc`.
* Under the constant hash, a second accepted preimage `P'` gives a checked flow with the
  same id that differs from the first, so `Properties.CheckedFlowsAgreeOrClash` lands in its
  clash disjunct.
* Under the constant hash, two preimages that differ only in the version byte share an id,
  so `Properties.DifferentVersionsShareAnIdOnlyByClash` has satisfiable premises. -/
def Properties.FlowCanonicalAtHeadWitness : Prop :=
  ∃ (P P' Q : FlowPreimage),
    PreimageAccepted P ∧ P.legBundleHashes.length = 2 ∧ P.Declares 1 0 ∧ P.Declares 2 1
      ∧ (∀ enc : PreimageHash, CheckFlowId enc ⟨enc P, P⟩)
      ∧ PreimageAccepted P' ∧ P ≠ P'
      ∧ CheckFlowId (fun _ => 0) ⟨0, P⟩ ∧ CheckFlowId (fun _ => 0) ⟨0, P'⟩
      ∧ PreimageClash (fun _ => 0) P P'
      ∧ P.version ≠ Q.version ∧ PreimageClash (fun _ => 0) P Q

end Contracts.FlowCanonicalAtHead
