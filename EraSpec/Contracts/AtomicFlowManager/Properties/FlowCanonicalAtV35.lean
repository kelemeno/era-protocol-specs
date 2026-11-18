import EraSpec.Contracts.AtomicFlowManager.Specs.FlowCanonicalAtV35

/-!
# Properties at `draft/v0.35.0`: what `_validateAndComputeFlowId` accepts, and what it binds

Statements about `EraSpec.Contracts.AtomicFlowManager.Specs.FlowCanonicalAtV35` (era-contracts
`draft/v0.35.0`, commit `b17415d20`). Proofs are in
`EraSpec.Contracts.AtomicFlowManager.Proofs.FlowCanonicalAtV35`. No statement takes a hash
premise: the results hold for every hash `enc`, and each witness names its hash.

* **Acceptance.** `AcceptedV35Iff` is the exact acceptance condition: version byte `0x01`, at most
  eight legs, and the pin's `Valid`. `ValidateV35SomeIff` and `CheckFlowIdV35Iff` tie the
  transcription of `AtomicFlowManager.sol:348-379` to it. The pin's `Valid` is still necessary
  (`AcceptedV35ImpliesValid`), so the pin's results of the form `Valid f → …` apply to every
  preimage v35 accepts; three are restated over `AcceptedV35` (`AcceptedV35NoDuplicateLeg`,
  `AcceptedV35UniquePerLegSet`, `AcceptedV35PairingFunctional`). It is no longer sufficient
  (`ValidNotSufficientVersionV35`, `ValidNotSufficientLegCapV35`).
* **The cap.** More than eight legs make `_validateAndComputeFlowId` revert whatever the hash
  (`TooManyLegsRejectedV35`), and so make the transcribed `append`, `requireFlowFinalized` and
  `authorizeRefund` revert from every state (`TooManyLegsRevertsEveryEntryPointV35`).
* **The leg writes** (`runV35`; model boundary `MODEL-AFM-V35`). `AppendV35SomeIff` says exactly
  when the transcribed `append` succeeds and what it writes. Every run is a run of the pin's leg
  machine (`RunV35IsPinLegRun`), so legs only move forward (`RunV35LegRankMonotone`); a run
  claims each leg at most once and appends each leg at most once
  (`RunV35ClaimsEachLegAtMostOnce`, `RunV35AppendsEachLegAtMostOnce`).
* **Who wrote a leg, over runs.** A leg first written in a run was appended in that run under a
  preimage that passes the checks, declares the leg on this chain and hashes to the leg's flow id
  (`WrittenLegAppendedUnderAcceptedPreimageV35`). So a run writes no `Unset` leg under the flow id
  of a rejected preimage, an oversized one for instance, unless it appended under an accepted
  preimage that clashes with it
  (`RejectedPreimageLegsUntouchedOrLoggedClashV35`, `OversizedFlowCommitsNoLegOrLoggedClashV35`).
  A leg first written in a run and refunded in it was marked by an `authorizeRefund` whose
  preimage is the one the leg was appended under, or clashes with it
  (`RefundedLegSameFlowOrLoggedClashV35`). Each clash is between preimages that calls of the run
  presented.
* **One check, unfolded.** `SameFlowIdSamePreimageOrClashV35`: two flows that pass `_checkFlowId`
  with one id are equal, or their preimages clash. Given the two checks its clash disjunct is just
  "the preimages differ", so it has no content beyond its definitions; the run results are its
  forms with content. `PreimageClashNotForcedV35`: for two distinct preimages some hash does not
  clash on them.
* **Witnesses.** `AcceptanceWitnessV35`, `TooManyLegsWitnessV35` and `LegWritesWitnessV35`
  instantiate the premises; `SecondClaimOrAppendRevertsWitnessV35` shows the at-most-once bounds
  bite; `SameFlowIdClashFiresV35`, `OversizedFlowWitnessV35` and
  `RefundUnderOtherPreimageWitnessV35` show each clash disjunct is reachable.

The leg-write results are about the transcribed checks and writes of `MODEL-AFM-V35`; the checks
the transcription leaves out only revert, so they can only remove runs.
-/

namespace Contracts.FlowCanonicalAtV35

open AttackVectors.FlowCanonical
open Contracts.AtomicFlowManager (Manager LegState)

/-! ## Acceptance -/

/-- **THE EXACT ACCEPTANCE CONDITION.** A preimage passes the four checks of
`_validateAndComputeFlowId` (`AtomicFlowManager.sol:360-377`) if and only if its version byte is
`0x01`, it has at most eight legs, and it is the pin's `Valid` (strictly ascending bundle hashes,
as many source chains as legs). -/
def Properties.AcceptedV35Iff : Prop :=
  ∀ p : PreimageV35, AcceptedV35 p ↔
    p.version = ATOMIC_FLOW_PREIMAGE_VERSION_V35
      ∧ p.legBundleHashes.length ≤ MAX_ATOMIC_FLOW_LEGS_V35 ∧ Valid p.arrays

/-- **`Valid` IS STILL NECESSARY.** Every preimage v35 accepts passes the pin's two checks
(`AtomicFlowManager.sol:370-377`). -/
def Properties.AcceptedV35ImpliesValid : Prop :=
  ∀ p : PreimageV35, AcceptedV35 p → Valid p.arrays

/-- **`Valid` IS NOT SUFFICIENT: THE VERSION BYTE.** Some preimage with at most eight legs passes
the pin's checks and is rejected at v35: `_validateAndComputeFlowId` reverts on it for every hash
(`:361-363`). -/
def Properties.ValidNotSufficientVersionV35 : Prop :=
  ∃ p : PreimageV35, Valid p.arrays ∧ p.legBundleHashes.length ≤ MAX_ATOMIC_FLOW_LEGS_V35
    ∧ ¬ AcceptedV35 p ∧ ∀ enc : PreimageHashV35, validateV35 enc p = none

/-- **`Valid` IS NOT SUFFICIENT: THE LEG CAP.** Some preimage with version byte `0x01` and nine
legs passes the pin's checks and is rejected at v35: `_validateAndComputeFlowId` reverts on it for
every hash (`:367-369`). -/
def Properties.ValidNotSufficientLegCapV35 : Prop :=
  ∃ p : PreimageV35, Valid p.arrays ∧ p.version = ATOMIC_FLOW_PREIMAGE_VERSION_V35
    ∧ p.legBundleHashes.length = MAX_ATOMIC_FLOW_LEGS_V35 + 1
    ∧ ¬ AcceptedV35 p ∧ ∀ enc : PreimageHashV35, validateV35 enc p = none

/-- **THE TRANSCRIPTION MEANS WHAT IT SAYS.** `validateV35` returns `id` exactly when the
preimage is accepted and its hash is `id` (`AtomicFlowManager.sol:360-379`). -/
def Properties.ValidateV35SomeIff : Prop :=
  ∀ (enc : PreimageHashV35) (p : PreimageV35) (id : UInt256),
    validateV35 enc p = some id ↔ AcceptedV35 p ∧ enc p = id

/-- **`_checkFlowId` AT v35** (`AtomicFlowManager.sol:348-353`) passes exactly when the preimage
is accepted and hashes to the claimed id. -/
def Properties.CheckFlowIdV35Iff : Prop :=
  ∀ (enc : PreimageHashV35) (F : AtomicFlowV35),
    CheckFlowIdV35 enc F ↔ AcceptedV35 F.preimage ∧ enc F.preimage = F.flowId

/-! ## The cap -/

/-- **MORE THAN EIGHT LEGS: `_validateAndComputeFlowId` REVERTS**, whatever the hash
(`AtomicFlowManager.sol:367-369`). -/
def Properties.TooManyLegsRejectedV35 : Prop :=
  ∀ (enc : PreimageHashV35) (p : PreimageV35),
    MAX_ATOMIC_FLOW_LEGS_V35 < p.legBundleHashes.length → validateV35 enc p = none

/-- **MORE THAN EIGHT LEGS: THE THREE ENTRY POINTS THAT TAKE A PREIMAGE REVERT.** For every hash,
chain, manager state and every other argument, the transcribed `append` (`:104-173`),
`requireFlowFinalized` (`:176-213`) and `authorizeRefund` (`:216-247`) revert on a preimage with
more than eight legs. -/
def Properties.TooManyLegsRevertsEveryEntryPointV35 : Prop :=
  ∀ (enc : PreimageHashV35) (chainId : UInt256) (M : Manager) (p : PreimageV35),
    MAX_ATOMIC_FLOW_LEGS_V35 < p.legBundleHashes.length →
      ∀ (h id e : UInt256) (k : ℕ),
        stepV35 enc chainId M (.append h p) = none ∧
        stepV35 enc chainId M (.requireFinalized e ⟨id, p⟩) = none ∧
        stepV35 enc chainId M (.authorizeRefund ⟨id, p⟩ k) = none

/-! ## The pin's canonicity results, over v35's acceptance -/

/-- **NO DUPLICATED LEG.** Distinct positions of an accepted preimage carry distinct bundle
hashes: the neighbour scan (`:370-374`) lifts to all pairs. -/
def Properties.AcceptedV35NoDuplicateLeg : Prop :=
  ∀ (p : PreimageV35), AcceptedV35 p → ∀ (i j : Fin p.legBundleHashes.length), i ≠ j →
    p.legBundleHashes.get i ≠ p.legBundleHashes.get j

/-- **THE PRESENTATION IS UNIQUE PER LEG SET.** Two accepted preimages whose leg lists are
permutations of each other have identical leg lists. -/
def Properties.AcceptedV35UniquePerLegSet : Prop :=
  ∀ (p q : PreimageV35), AcceptedV35 p → AcceptedV35 q →
    p.legBundleHashes.Perm q.legBundleHashes → p.legBundleHashes = q.legBundleHashes

/-- **EVERY LEG HAS EXACTLY ONE SOURCE CHAIN.** In an accepted preimage the zipped
`(bundleHash, sourceChainId)` pairing has distinct keys and loses no leg (`:370-377`). -/
def Properties.AcceptedV35PairingFunctional : Prop :=
  ∀ (p : PreimageV35), AcceptedV35 p →
    ((p.legBundleHashes.zip p.legSourceChainIds).map Prod.fst).Nodup
      ∧ (p.legBundleHashes.zip p.legSourceChainIds).length = p.legBundleHashes.length

/-! ## The leg writes -/

/-- **`append` AT v35, EXACTLY.** For every hash and chain, the transcribed `append(h, p)`
succeeds from state `M` with end state `M'` if and only if `p` passes
`_validateAndComputeFlowId`, `p` declares leg `h` with source chain `chainId`, leg `(enc p, h)`
is `Unset` in `M`, and `M'` is `M` with that leg `Committed` (`AtomicFlowManager.sol:109`,
`:130-147`, `:162-166`). -/
def Properties.AppendV35SomeIff : Prop :=
  ∀ (enc : PreimageHashV35) (chainId : UInt256) (M M' : Manager) (h : UInt256) (p : PreimageV35),
    appendV35 enc chainId M h p = some M' ↔
      AcceptedV35 p ∧ (h, chainId) ∈ p.legBundleHashes.zip p.legSourceChainIds ∧
        M.legState (enc p) h = .Unset ∧ M' = M.set (enc p) h .Committed

/-- **EVERY RUN IS A RUN OF THE PIN'S LEG MACHINE.** For every hash, chain, starting state `M₀`
and successful run ending in `M`, `M` is reachable from `M₀` in the pin's
`Contracts.AtomicFlowManager.Reach`. So every result of the pin's `Model` topic that takes a
`Reach` premise (`reach_rank_mono`, `reverted_absorbing`, `no_double_claim`,
`no_double_append`) applies to every run here, with the run's start and end states as the two
ends of that `Reach`. -/
def Properties.RunV35IsPinLegRun : Prop :=
  ∀ (enc : PreimageHashV35) (chainId : UInt256) (M₀ M : Manager) (calls : List CallV35),
    runV35 enc chainId M₀ calls = some M → Contracts.AtomicFlowManager.Reach M₀ M

/-- **NO LEG MOVES BACKWARD IN A RUN.** For every hash, chain, starting state `M₀` and successful
run ending in `M`, every leg's rank (`Unset` 0, `Committed` 1, `Revertable` 2, `Reverted` 3) in
`M` is at least its rank in `M₀` (the pin's `reach_rank_mono`, through `RunV35IsPinLegRun`). -/
def Properties.RunV35LegRankMonotone : Prop :=
  ∀ (enc : PreimageHashV35) (chainId : UInt256) (M₀ M : Manager) (calls : List CallV35),
    runV35 enc chainId M₀ calls = some M → ∀ id h : UInt256,
      Contracts.AtomicFlowManager.rank (M₀.legState id h) ≤
        Contracts.AtomicFlowManager.rank (M.legState id h)

/-- **EACH LEG IS CLAIMED AT MOST ONCE IN A RUN.** For every hash, chain, starting state and
successful run, and every leg `(id, h)`: the run has at most one call `claimRefund(id, h)`, and
none if the leg is `Reverted` at the start. -/
def Properties.RunV35ClaimsEachLegAtMostOnce : Prop :=
  ∀ (enc : PreimageHashV35) (chainId : UInt256) (M₀ M : Manager) (calls : List CallV35),
    runV35 enc chainId M₀ calls = some M → ∀ id h : UInt256,
      calls.count (.claimRefund id h) ≤ 1 ∧
        (M₀.legState id h = .Reverted → calls.count (.claimRefund id h) = 0)

/-- **EACH LEG IS APPENDED AT MOST ONCE IN A RUN.** For every hash, chain, starting state and
successful run, and every leg `(id, h)`: at most one call of the run is an `append(h, p)` with
`enc p = id`, and none if the leg is not `Unset` at the start. -/
def Properties.RunV35AppendsEachLegAtMostOnce : Prop :=
  ∀ (enc : PreimageHashV35) (chainId : UInt256) (M₀ M : Manager) (calls : List CallV35),
    runV35 enc chainId M₀ calls = some M → ∀ id h : UInt256,
      calls.countP (CallV35.appendsLegV35 enc id h) ≤ 1 ∧
        (M₀.legState id h ≠ .Unset → calls.countP (CallV35.appendsLegV35 enc id h) = 0)

/-! ## Who wrote a leg, over runs -/

/-- **A LEG FIRST WRITTEN IN A RUN WAS APPENDED UNDER AN ACCEPTED PREIMAGE WITH ITS FLOW ID.**
For every hash `enc`, chain `chainId`, starting state `M₀` and successful run `calls` ending in
`M`: if leg `(id, h)` is `Unset` in `M₀` and not `Unset` in `M`, some call of the run is
`append h p` where `p` passes `_validateAndComputeFlowId`, `enc p = id`, and `p` declares leg `h`
with source chain `chainId` (`AtomicFlowManager.sol:109`, `:130-147`, `:166`). -/
def Properties.WrittenLegAppendedUnderAcceptedPreimageV35 : Prop :=
  ∀ (enc : PreimageHashV35) (chainId : UInt256) (M₀ M : Manager) (calls : List CallV35),
    runV35 enc chainId M₀ calls = some M →
    ∀ id h : UInt256, M₀.legState id h = .Unset → M.legState id h ≠ .Unset →
      ∃ p, CallV35.append h p ∈ calls ∧ AcceptedV35 p ∧ enc p = id ∧
        (h, chainId) ∈ p.legBundleHashes.zip p.legSourceChainIds

/-- **NO LEG IS WRITTEN UNDER A REJECTED PREIMAGE'S FLOW ID, UNLESS A LOGGED CLASH.** For every
hash, chain, starting state `M₀`, successful run `calls` ending in `M`, and preimage `p` that
`_validateAndComputeFlowId` rejects: every leg `(enc p, h)` that is `Unset` in `M₀` is `Unset` in
`M`, or some call of the run is `append h q` with `q` accepted and `PreimageClashV35 enc p q`. -/
def Properties.RejectedPreimageLegsUntouchedOrLoggedClashV35 : Prop :=
  ∀ (enc : PreimageHashV35) (chainId : UInt256) (M₀ M : Manager) (calls : List CallV35)
    (p : PreimageV35), ¬ AcceptedV35 p → runV35 enc chainId M₀ calls = some M →
    ∀ h : UInt256, M₀.legState (enc p) h = .Unset →
      M.legState (enc p) h = .Unset ∨
        ∃ q, CallV35.append h q ∈ calls ∧ AcceptedV35 q ∧ PreimageClashV35 enc p q

/-- **AN OVERSIZED FLOW COMMITS NO LEG, UNLESS A LOGGED CLASH.** The previous statement for a
preimage `p` with more than eight legs (the claim of `IAtomicInterop.sol:93-98` that such a flow
"can never commit a leg"): every leg `(enc p, h)` that is `Unset` in `M₀` is `Unset` after every
successful run, or the run appended `h` under an accepted preimage that clashes with `p`. -/
def Properties.OversizedFlowCommitsNoLegOrLoggedClashV35 : Prop :=
  ∀ (enc : PreimageHashV35) (chainId : UInt256) (M₀ M : Manager) (calls : List CallV35)
    (p : PreimageV35), MAX_ATOMIC_FLOW_LEGS_V35 < p.legBundleHashes.length →
    runV35 enc chainId M₀ calls = some M →
    ∀ h : UInt256, M₀.legState (enc p) h = .Unset →
      M.legState (enc p) h = .Unset ∨
        ∃ q, CallV35.append h q ∈ calls ∧ AcceptedV35 q ∧ PreimageClashV35 enc p q

/-- **A LEG IS REFUNDED UNDER THE PREIMAGE IT WAS COMMITTED UNDER, UNLESS A LOGGED CLASH.** For
every hash, chain, starting state `M₀` and successful run `calls` ending in `M`: if leg `(id, h)`
is `Unset` in `M₀` and `Revertable` or `Reverted` in `M`, the run has a call `append h p` and a
call `authorizeRefund F k` such that `p` is accepted with `enc p = id`, `F` passes `_checkFlowId`
with `F.flowId = id` and lists `h`, and either `F.preimage = p` (the same version, deadline,
settlement layer, legs and source chains) or `PreimageClashV35 enc p F.preimage`.

Given `enc p = id` and the check on `F`, the last disjunct is excluded middle. The content is
that both preimages were presented by calls of the run, so a hash injective on the run's
presented preimages forces `F.preimage = p`. -/
def Properties.RefundedLegSameFlowOrLoggedClashV35 : Prop :=
  ∀ (enc : PreimageHashV35) (chainId : UInt256) (M₀ M : Manager) (calls : List CallV35),
    runV35 enc chainId M₀ calls = some M →
    ∀ id h : UInt256, M₀.legState id h = .Unset →
      (M.legState id h = .Revertable ∨ M.legState id h = .Reverted) →
      ∃ p F k, CallV35.append h p ∈ calls ∧ CallV35.authorizeRefund F k ∈ calls ∧
        AcceptedV35 p ∧ enc p = id ∧ CheckFlowIdV35 enc F ∧ F.flowId = id ∧
        h ∈ F.preimage.legBundleHashes ∧ (F.preimage = p ∨ PreimageClashV35 enc p F.preimage)

/-! ## One check, unfolded -/

/-- **ONE ID, ONE FLOW, OR A CLASH.** Two flows that pass `_checkFlowId` with the same id are
equal (id, version, deadline, settlement layer, legs and source chains), or their two preimages
are a `PreimageClashV35`. Given the two checks the clash disjunct is just "the preimages differ",
so this statement has no content beyond its definitions; the run results above pin the clash to
preimages a run presented. -/
def Properties.SameFlowIdSamePreimageOrClashV35 : Prop :=
  ∀ (enc : PreimageHashV35) (F G : AtomicFlowV35), CheckFlowIdV35 enc F → CheckFlowIdV35 enc G →
    F.flowId = G.flowId → F = G ∨ PreimageClashV35 enc F.preimage G.preimage

/-- **THE CLASH DISJUNCT IS NOT A TAUTOLOGY.** For any two distinct preimages there is a hash that
does not clash on them. -/
def Properties.PreimageClashNotForcedV35 : Prop :=
  ∀ (p q : PreimageV35), p ≠ q → ∃ enc : PreimageHashV35, ¬ PreimageClashV35 enc p q

/-! ## Witnesses -/

/-- **THE ACCEPTANCE PREMISES HOLD.** `wFlowV35` (three legs) and `wFlowLateV35` (the same legs
and source chains, a later deadline) are accepted and distinct, and their leg lists are
permutations of each other; under the hash honest about `wFlowV35` at `7`, the flow
`⟨7, wFlowV35⟩` passes `_checkFlowId` and `⟨7, wFlowLateV35⟩` does not. -/
def Properties.AcceptanceWitnessV35 : Prop :=
  AcceptedV35 wFlowV35 ∧ AcceptedV35 wFlowLateV35 ∧ wFlowV35 ≠ wFlowLateV35 ∧
    wFlowV35.legBundleHashes.length = 3 ∧
    wFlowV35.legBundleHashes.Perm wFlowLateV35.legBundleHashes ∧
    CheckFlowIdV35 (honestPreimageHashV35 wFlowV35 7) ⟨7, wFlowV35⟩ ∧
    ¬ CheckFlowIdV35 (honestPreimageHashV35 wFlowV35 7) ⟨7, wFlowLateV35⟩

/-- **TWO CHECKED FLOWS WITH ONE ID DIFFER UNDER A CLASHING HASH.** Under the hash that maps
exactly `wFlowV35` and `wFlowLateV35` to `7`, both `⟨7, wFlowV35⟩` and `⟨7, wFlowLateV35⟩` pass
`_checkFlowId`; they are different flows, and their preimages are a `PreimageClashV35`. -/
def Properties.SameFlowIdClashFiresV35 : Prop :=
  CheckFlowIdV35 (pairClashHashV35 wFlowV35 wFlowLateV35 7) ⟨7, wFlowV35⟩ ∧
    CheckFlowIdV35 (pairClashHashV35 wFlowV35 wFlowLateV35 7) ⟨7, wFlowLateV35⟩ ∧
    (⟨7, wFlowV35⟩ : AtomicFlowV35) ≠ ⟨7, wFlowLateV35⟩ ∧
    PreimageClashV35 (pairClashHashV35 wFlowV35 wFlowLateV35 7) wFlowV35 wFlowLateV35

/-- **THE CAP IS WHAT REJECTS `wOversizedV35`.** `wOversizedV35` has version `0x01`, is `Valid`,
has nine legs, one over the cap, and declares leg `1` on chain `270`. From fresh storage on chain
`270`, under the hash honest about `wCappedV35` at `7`, `append(1, wOversizedV35)` reverts, while
`wCappedV35` (the same preimage without its ninth leg) passes `append(1, ·)`,
`requireFlowFinalized(1, ⟨7, ·⟩)` and `authorizeRefund(⟨7, ·⟩, 0)`. -/
def Properties.TooManyLegsWitnessV35 : Prop :=
  Valid wOversizedV35.arrays ∧ wOversizedV35.version = ATOMIC_FLOW_PREIMAGE_VERSION_V35 ∧
    wOversizedV35.legBundleHashes.length = 9 ∧
    MAX_ATOMIC_FLOW_LEGS_V35 < wOversizedV35.legBundleHashes.length ∧
    ((1 : UInt256), wChainV35) ∈ wOversizedV35.legBundleHashes.zip wOversizedV35.legSourceChainIds ∧
    stepV35 (honestPreimageHashV35 wCappedV35 7) wChainV35 Contracts.AtomicFlowManager.empty
      (.append 1 wOversizedV35) = none ∧
    (stepV35 (honestPreimageHashV35 wCappedV35 7) wChainV35 Contracts.AtomicFlowManager.empty
      (.append 1 wCappedV35)).isSome ∧
    (stepV35 (honestPreimageHashV35 wCappedV35 7) wChainV35 Contracts.AtomicFlowManager.empty
      (.requireFinalized 1 ⟨7, wCappedV35⟩)).isSome ∧
    (stepV35 (honestPreimageHashV35 wCappedV35 7) wChainV35 Contracts.AtomicFlowManager.empty
      (.authorizeRefund ⟨7, wCappedV35⟩ 0)).isSome

/-- **A RUN WITH THE PREMISES OF THE RUN RESULTS.** Under the hash honest about `wFlowV35` at
`7`, on chain `270`, from fresh storage, the run `wRunV35` (append legs `11` and `33`, authorize
the flow's refund, claim leg `11`) succeeds and leaves leg `(7, 11)` `Reverted`, leg `(7, 33)`
`Revertable` and leg `(7, 22)`, declared on chain `271`, `Unset`. The rejected `wWrongVersionV35`
hashes to `8` there, and its leg `(8, 11)` stays `Unset`. -/
def Properties.LegWritesWitnessV35 : Prop :=
  (runV35 (honestPreimageHashV35 wFlowV35 7) wChainV35 Contracts.AtomicFlowManager.empty
      wRunV35).map (fun M => (M.legState 7 11, M.legState 7 33, M.legState 7 22)) =
    some (.Reverted, .Revertable, .Unset) ∧
  ¬ AcceptedV35 wWrongVersionV35 ∧ honestPreimageHashV35 wFlowV35 7 wWrongVersionV35 = 8 ∧
  (runV35 (honestPreimageHashV35 wFlowV35 7) wChainV35 Contracts.AtomicFlowManager.empty
      wRunV35).map (fun M => M.legState 8 11) = some .Unset

/-- **THE OVERSIZED FLOW, BOTH WAYS.** On chain `270`, from fresh storage, the run
`[append(1, wCappedV35)]` commits leg `(7, 1)` under the two hashes below. Under the hash honest
about `wCappedV35` at `7`, `wOversizedV35` hashes to `8` and leg `(8, 1)` stays `Unset`. Under the
hash that maps exactly `wOversizedV35` and `wCappedV35` to `7`, `wOversizedV35` hashes to `7`, so
its flow id has leg `1` `Committed`; the run's one preimage, `wCappedV35`, is accepted and clashes
with it. -/
def Properties.OversizedFlowWitnessV35 : Prop :=
  ¬ AcceptedV35 wOversizedV35 ∧ AcceptedV35 wCappedV35 ∧
  honestPreimageHashV35 wCappedV35 7 wOversizedV35 = 8 ∧
  (runV35 (honestPreimageHashV35 wCappedV35 7) wChainV35 Contracts.AtomicFlowManager.empty
      [.append 1 wCappedV35]).map (fun M => (M.legState 7 1, M.legState 8 1)) =
    some (.Committed, .Unset) ∧
  pairClashHashV35 wOversizedV35 wCappedV35 7 wOversizedV35 = 7 ∧
  PreimageClashV35 (pairClashHashV35 wOversizedV35 wCappedV35 7) wOversizedV35 wCappedV35 ∧
  (runV35 (pairClashHashV35 wOversizedV35 wCappedV35 7) wChainV35
      Contracts.AtomicFlowManager.empty [.append 1 wCappedV35]).map (fun M => M.legState 7 1) =
    some .Committed

/-- **A SECOND CLAIM OR A SECOND APPEND OF ONE LEG REVERTS.** Under the hash honest about
`wFlowV35` at `7`, on chain `270`, from fresh storage: `wRunV35` followed by a second
`claimRefund(7, 11)` reverts, and so does appending leg `11` of `wFlowV35` twice in a row. -/
def Properties.SecondClaimOrAppendRevertsWitnessV35 : Prop :=
  (runV35 (honestPreimageHashV35 wFlowV35 7) wChainV35 Contracts.AtomicFlowManager.empty
      (wRunV35 ++ [.claimRefund 7 11])).isNone ∧
  (runV35 (honestPreimageHashV35 wFlowV35 7) wChainV35 Contracts.AtomicFlowManager.empty
      [.append 11 wFlowV35, .append 11 wFlowV35]).isNone

/-- **A LEG REFUNDED UNDER ANOTHER PREIMAGE NEEDS THE CLASH.** Under the hash that maps exactly
`wFlowV35` and `wFlowLateV35` to `7`, on chain `270`, from fresh storage, the run
`wLateRefundRunV35` (append leg `11` under `wFlowV35`, then authorize a refund presenting
`wFlowLateV35`, a later deadline, under id `7`) succeeds and leaves leg `(7, 11)` `Revertable`.
The two presented preimages differ and clash. -/
def Properties.RefundUnderOtherPreimageWitnessV35 : Prop :=
  (runV35 (pairClashHashV35 wFlowV35 wFlowLateV35 7) wChainV35 Contracts.AtomicFlowManager.empty
      wLateRefundRunV35).map (fun M => M.legState 7 11) = some .Revertable ∧
  wFlowLateV35 ≠ wFlowV35 ∧
  PreimageClashV35 (pairClashHashV35 wFlowV35 wFlowLateV35 7) wFlowV35 wFlowLateV35

end Contracts.FlowCanonicalAtV35
