import EraSpec.Contracts.AtomicFlowManager.Specs.RefundClosesAppend

-- Named propositions are transparent definitions; proofs reference these statements.
set_option linter.unusedVariables false

/-!
# Properties: an authorized refund closes `append` for its flow, on that chain

Statements about `EraSpec.Contracts.AtomicFlowManager.Specs.RefundClosesAppend` (era-contracts
`draft/v0.35.0` at `b17415d20`); proofs are in
`EraSpec.Contracts.AtomicFlowManager.Proofs.RefundClosesAppend`.  The positive results quantify
over all hash functions, commitment trees, proof oracles, callers and Bridgehub answers, and none
takes a hash premise; the countermodels and the witness each exhibit one configuration.

## Runs

A run is its calls run in order (`ChainRunIffRunCalls`), and its leg map moves as the
abstract manager `Contracts.AtomicFlowManager.Reach` (`ChainRunLegsReach`), so that machine's
results apply to the leg map of every run here.

## The root storage

`LatestBoundsStored` (every stored timestamp is at most the chain's tracked timestamp) holds of
fresh storage and of any storage whose stored timestamps are all zero, and every run of code
whose root storage keeps the maximum preserves it (`LatestBoundsStoredInvariant`).  The Specs
header argues from source, outside the model, that the storage an upgrade from v31 leaves has
all stored timestamps zero.  The tracked timestamp never decreases (`LatestNeverDecreases`).

## The ordering claim (`A:116-119`)

Fix a run of the deployed code from a state with `LatestBoundsStored`, in which
`authorizeRefund(flowId, p, i, a)` succeeds at some step.  Afterwards:

* `append` of the same preimage `p` reverts, whatever the caller, bundle hash, hint and
  Bridgehub answers (`AuthorizedPreimageNeverAppendedAgain`).  If `L1_CHAIN_ID` was set at the
  authorization, the interop center's call reverts with exactly
  `ManagerFlowDeadlinePassed(deadline, latest)` (`AuthorizedPreimageAppendHitsDeadlineGate`).
  Keyed on the flow id: every later `append` of a preimage hashing to `flowId` reverts, or its
  preimage is not `p` and collides with it (`AuthorizedFlowIdAppendRevertsOrLoggedClash`).
* With `L1_CHAIN_ID` set at the authorization, every `append` that succeeds later, of any flow,
  has a deadline strictly later than `p.deadline` (`LaterAppendsHaveLaterDeadlines`).
* From a fresh manager, no leg `(flowId, h)` is `Committed` afterwards, unless the run contains a
  successful `append` of that leg whose preimage is not `p` but has the same `flowHash`: a
  collision between two preimages that are both in the run
  (`RefundedFlowHasNoCommittedLegOrLoggedClash`).
* Every leg of `p` that was `Committed` just before the authorization is `Revertable` just after
  it, stays claimable until claimed, and is claimed at most once in any continuation
  (`CommittedLegsBecomeClaimableOnce`).
* The source comment's own form: from a fresh manager, once a leg of flow id `flowId` is
  `Revertable` or `Reverted`, the run contains an authorization of `flowId` with a preimage `p`,
  and no later `append` of a preimage hashing to `flowId` succeeds unless that preimage differs
  from `p` (`RevertedLegClosesFlowOrLoggedClash`).

## Each ingredient is needed (countermodels)

* Without the expired-flow gate, a leg of a flow is committed after the flow's refund was
  authorized, in a state where the deployed code reverts that `append` at the gate; repeating the
  same `authorizeRefund` call then marks the late leg (`WithoutDeadlineGateLegCommittedAfterRefund`).
* A root storage keeping the last imported timestamp instead of the maximum readmits the
  `append` after an older root is imported later (`LastValueLatestReadmitsAppend`).
* Without the proof's settlement-layer check, a root imported under another chain id authorizes
  the refund, and the `append` then passes the gate, which reads the flow's settlement layer
  (`UnboundProofSettlementLayerReadmitsAppend`).
* With a non-strict root-timestamp check, a root created exactly at the deadline authorizes the
  refund and the gate, which is strict, lets the `append` through
  (`NonStrictRootTimestampReadmitsAppend`).
* From a state violating `LatestBoundsStored`, the deployed code admits the `append` after the
  authorization (`WithoutLatestBoundAppendAfterRefund`).

## Non-vacuity

`RefundClosesAppendWitness` meets every premise of the positive results above on one run of the
deployed code from genesis: `initL2`, an `append` of one leg of a three-leg flow, a root import,
an authorization that marks that leg, its claim, and an `append` of a second flow with a later
deadline.  The run's two preimages have distinct flow ids, and a leg of the first flow that could
have been appended before the import is refused at the gate afterwards.
-/

namespace Contracts.AtomicFlowManager.RefundClosesAppend

/-! ## Runs as a function -/

/-- **A RUN IS ITS CALLS, RUN IN ORDER.**  `ChainRun` relates exactly the states `runCalls`
returns. -/
def Properties.ChainRunIffRunCalls : Prop :=
  ∀ {τ : Type} (P : ChainParams τ) (K : Checks) (S S' : ChainState τ) (cs : List ChainCall),
    ChainRun P K S cs S' ↔ runCalls P K S cs = some S'

/-- **THE LEG MAP MOVES AS THE ABSTRACT MANAGER.**  For any checks, the leg map at the end of a
run is reachable from the one at its start in `Contracts.AtomicFlowManager.Reach` (the
lifecycle machine of `Specs/Model.lean`): each `append` is one `append` step, each
`authorizeRefund` one `authorize` step per leg it marks, each `claimRefund` one `claim` step, and
the other calls leave the leg map alone. -/
def Properties.ChainRunLegsReach : Prop :=
  ∀ {τ : Type} (P : ChainParams τ) (K : Checks) (S S' : ChainState τ) (cs : List ChainCall),
    ChainRun P K S cs S' → Contracts.AtomicFlowManager.Reach S.legs S'.legs

/-! ## The root storage -/

/-- **THE TRACKED TIMESTAMP BOUNDS EVERY STORED ONE, ON EVERY RUN.**  `LatestBoundsStored` holds
of fresh root storage, and of every root storage whose stored timestamps are all zero (whatever
its tracked timestamps).  Every run of code whose root storage keeps the maximum
(`latestKeepsMax`; the other three switches are arbitrary) preserves it. -/
def Properties.LatestBoundsStoredInvariant : Prop :=
  LatestBoundsStored RootStore.fresh ∧
  (∀ R : RootStore, (∀ c b, (R.storedInteropRoots c b).timestamp = 0) → LatestBoundsStored R) ∧
  ∀ {τ : Type} (P : ChainParams τ) (K : Checks) (S S' : ChainState τ) (cs : List ChainCall),
    K.latestKeepsMax = true → ChainRun P K S cs S' → LatestBoundsStored S.roots →
      LatestBoundsStored S'.roots

/-- **THE TRACKED TIMESTAMP NEVER DECREASES.**  On every run of code whose root storage keeps the
maximum, from any state, each chain's `latestInteropRootTimestamp` at the end is at least its
value at the start. -/
def Properties.LatestNeverDecreases : Prop :=
  ∀ {τ : Type} (P : ChainParams τ) (K : Checks) (S S' : ChainState τ) (cs : List ChainCall),
    K.latestKeepsMax = true → ChainRun P K S cs S' →
      ∀ c, S.roots.latestInteropRootTimestamp c ≤ S'.roots.latestInteropRootTimestamp c

/-! ## The ordering claim -/

/-- **AN AUTHORIZED REFUND CLOSES `append` FOR ITS PREIMAGE, FOREVER.**  A run of the deployed
code from a state `S₀` whose root storage satisfies `LatestBoundsStored`: calls `pre` reach `S₁`,
`authorizeRefund(flowId, p, i, a)` succeeds there and leaves `S₂`, and calls `post` reach `S₃`.
In `S₃`, `append` of preimage `p` reverts, for every caller, registration answer, bundle hash and
low-nullifier index. -/
def Properties.AuthorizedPreimageNeverAppendedAgain : Prop :=
  ∀ {τ : Type} (P : ChainParams τ) (S₀ S₁ S₂ S₃ : ChainState τ) (pre post : List ChainCall)
    (peerAllowed : ℕ → Bool) (flowId : Word) (p : FlowPreimage) (i : ℕ) (a : AbsenceProof),
    LatestBoundsStored S₀.roots → ChainRun P deployed S₀ pre S₁ →
    execCall P deployed S₁ (.authorizeRefund peerAllowed flowId p i a) = some S₂ →
    ChainRun P deployed S₂ post S₃ →
    ∀ (caller : ℕ) (registered : ℕ → Bool) (b : Word) (idx : ℕ),
      ∃ e, appendCall P deployed S₃ caller registered b idx p = .error e

/-- **…AND THE CENTER'S `append` REVERTS WITH `ManagerFlowDeadlinePassed`.**  The same run, with
`L1_CHAIN_ID` set (nonzero) when the refund was authorized.  In `S₃` the tracked timestamp of the
flow's settlement layer is past `p.deadline`, and `append` of `p` by the interop center reverts
with exactly `ManagerFlowDeadlinePassed(p.deadline, latestInteropRootTimestamp(sl))`, for every
registration answer, bundle hash and low-nullifier index. -/
def Properties.AuthorizedPreimageAppendHitsDeadlineGate : Prop :=
  ∀ {τ : Type} (P : ChainParams τ) (S₀ S₁ S₂ S₃ : ChainState τ) (pre post : List ChainCall)
    (peerAllowed : ℕ → Bool) (flowId : Word) (p : FlowPreimage) (i : ℕ) (a : AbsenceProof),
    LatestBoundsStored S₀.roots → ChainRun P deployed S₀ pre S₁ →
    execCall P deployed S₁ (.authorizeRefund peerAllowed flowId p i a) = some S₂ →
    ChainRun P deployed S₂ post S₃ → S₁.l1ChainId ≠ 0 →
    p.deadline < S₃.roots.latestInteropRootTimestamp p.settlementLayerChainId ∧
    ∀ (registered : ℕ → Bool) (b : Word) (idx : ℕ),
      appendCall P deployed S₃ P.interopCenter registered b idx p =
        .error (.flowDeadlinePassed p.deadline
          (S₃.roots.latestInteropRootTimestamp p.settlementLayerChainId))

/-- **EVERY LATER `append` OF THE FLOW ID REVERTS, UP TO A LOGGED CLASH.**  The same run.  The
authorization checked `flowHash p = flowId`, and every `append` in `S₃` of a preimage `q` with
`flowHash q = flowId` reverts, or else `q ≠ p`: a collision of the flow-id hash between the
authorization's preimage `p` and the `append`'s preimage `q`. -/
def Properties.AuthorizedFlowIdAppendRevertsOrLoggedClash : Prop :=
  ∀ {τ : Type} (P : ChainParams τ) (S₀ S₁ S₂ S₃ : ChainState τ) (pre post : List ChainCall)
    (peerAllowed : ℕ → Bool) (flowId : Word) (p : FlowPreimage) (i : ℕ) (a : AbsenceProof),
    LatestBoundsStored S₀.roots → ChainRun P deployed S₀ pre S₁ →
    execCall P deployed S₁ (.authorizeRefund peerAllowed flowId p i a) = some S₂ →
    ChainRun P deployed S₂ post S₃ →
    P.flowHash p = flowId ∧
    ∀ (caller : ℕ) (registered : ℕ → Bool) (b : Word) (idx : ℕ) (q : FlowPreimage),
      P.flowHash q = flowId →
        (∃ e, appendCall P deployed S₃ caller registered b idx q = .error e) ∨
          (q ≠ p ∧ P.flowHash q = P.flowHash p)

/-- **EVERY LATER `append` IS OF A LATER DEADLINE.**  The same run, with `L1_CHAIN_ID` set when
the refund was authorized.  Every `append` that succeeds in `S₃`, of any preimage `q`, is on the
same settlement layer as `p` and has a deadline strictly later than `p.deadline`. -/
def Properties.LaterAppendsHaveLaterDeadlines : Prop :=
  ∀ {τ : Type} (P : ChainParams τ) (S₀ S₁ S₂ S₃ : ChainState τ) (pre post : List ChainCall)
    (peerAllowed : ℕ → Bool) (flowId : Word) (p : FlowPreimage) (i : ℕ) (a : AbsenceProof),
    LatestBoundsStored S₀.roots → ChainRun P deployed S₀ pre S₁ →
    execCall P deployed S₁ (.authorizeRefund peerAllowed flowId p i a) = some S₂ →
    ChainRun P deployed S₂ post S₃ → S₁.l1ChainId ≠ 0 →
    ∀ (caller : ℕ) (registered : ℕ → Bool) (b : Word) (idx : ℕ) (q : FlowPreimage)
      (S₄ : ChainState τ),
      appendCall P deployed S₃ caller registered b idx q = .ok S₄ →
        q.settlementLayerChainId = p.settlementLayerChainId ∧ p.deadline < q.deadline

/-- **NO LEG OF THE REFUNDED FLOW IS `Committed` AFTERWARDS, UP TO A LOGGED CLASH.**  The same
run, from a state whose manager is fresh.  If a leg `(flowId, h)` is `Committed` in `S₃`, then
`pre ++ post` contains a successful `append` of that leg with a preimage `q` that is not `p` and
has `flowHash q = flowHash p`: a collision of the flow-id hash between two preimages of the run. -/
def Properties.RefundedFlowHasNoCommittedLegOrLoggedClash : Prop :=
  ∀ {τ : Type} (P : ChainParams τ) (S₀ S₁ S₂ S₃ : ChainState τ) (pre post : List ChainCall)
    (peerAllowed : ℕ → Bool) (flowId : Word) (p : FlowPreimage) (i : ℕ) (a : AbsenceProof),
    S₀.legs = Contracts.AtomicFlowManager.empty → LatestBoundsStored S₀.roots →
    ChainRun P deployed S₀ pre S₁ →
    execCall P deployed S₁ (.authorizeRefund peerAllowed flowId p i a) = some S₂ →
    ChainRun P deployed S₂ post S₃ →
    ∀ h : Word, S₃.legs.legState flowId h = .Committed →
      ∃ c ∈ pre ++ post, ∃ q : FlowPreimage,
        c.AppendsLeg P flowId h q ∧ q ≠ p ∧ P.flowHash q = P.flowHash p

/-- **EVERY LEG COMMITTED AT THE AUTHORIZATION IS CLAIMABLE, ONCE.**  A successful
`authorizeRefund(flowId, p, i, a)` from `S₁` to `S₂` (any start state).  Every leg `h` of `p` that
is `Committed` in `S₁` is `Revertable` in `S₂`.  In every state a continuation `post` reaches, it
is `Revertable` if `post` has no `claimRefund` of `(flowId, h)` and `Reverted` otherwise; `post`
has at most one such claim; and while it has none, `claimRefund` of the leg succeeds whenever its
recovery returns. -/
def Properties.CommittedLegsBecomeClaimableOnce : Prop :=
  ∀ {τ : Type} (P : ChainParams τ) (S₁ S₂ : ChainState τ) (peerAllowed : ℕ → Bool)
    (flowId : Word) (p : FlowPreimage) (i : ℕ) (a : AbsenceProof),
    execCall P deployed S₁ (.authorizeRefund peerAllowed flowId p i a) = some S₂ →
    ∀ h ∈ p.legBundleHashes, S₁.legs.legState flowId h = .Committed →
      S₂.legs.legState flowId h = .Revertable ∧
      ∀ (post : List ChainCall) (S₃ : ChainState τ), ChainRun P deployed S₂ post S₃ →
        post.countP (ChainCall.isClaimOf flowId h) ≤ 1 ∧
        S₃.legs.legState flowId h =
          (if post.countP (ChainCall.isClaimOf flowId h) = 0 then .Revertable else .Reverted) ∧
        (post.countP (ChainCall.isClaimOf flowId h) = 0 →
          ∃ S₄, execCall P deployed S₃ (.claimRefund flowId h true) = some S₄)

/-- **THE SOURCE COMMENT'S FORM: A REVERTED LEG CLOSES ITS FLOW, UP TO A LOGGED CLASH.**  A run
of the deployed code from a state with a fresh manager and `LatestBoundsStored` reaches `S₁`, in
which a leg `(flowId, h)` is `Revertable` or `Reverted`.  Then the run contains a successful
`authorizeRefund` of `flowId` with some preimage `p`, `flowHash p = flowId`, and in every state
reachable from `S₁` an `append` of a preimage `q` with `flowHash q = flowId` succeeds only if
`q ≠ p`. -/
def Properties.RevertedLegClosesFlowOrLoggedClash : Prop :=
  ∀ {τ : Type} (P : ChainParams τ) (S₀ S₁ : ChainState τ) (pre : List ChainCall),
    S₀.legs = Contracts.AtomicFlowManager.empty → LatestBoundsStored S₀.roots →
    ChainRun P deployed S₀ pre S₁ →
    ∀ (flowId h : Word),
      (S₁.legs.legState flowId h = .Revertable ∨ S₁.legs.legState flowId h = .Reverted) →
      ∃ (peerAllowed : ℕ → Bool) (p : FlowPreimage) (i : ℕ) (a : AbsenceProof),
        ChainCall.authorizeRefund peerAllowed flowId p i a ∈ pre ∧ P.flowHash p = flowId ∧
        ∀ (post : List ChainCall) (S₃ : ChainState τ), ChainRun P deployed S₁ post S₃ →
          ∀ (caller : ℕ) (registered : ℕ → Bool) (b : Word) (idx : ℕ) (q : FlowPreimage)
            (S₄ : ChainState τ),
            appendCall P deployed S₃ caller registered b idx q = .ok S₄ → P.flowHash q = flowId →
              q ≠ p

/-! ## Countermodels -/

/-- **WITHOUT THE EXPIRED-FLOW GATE, A LEG IS COMMITTED AFTER THE FLOW'S REFUND.**  Under
`withoutDeadlineGate`, a run from genesis reaches `S₁`; `authorizeRefund(flowId, p, i, a)`
succeeds and leaves `S₂`; then the interop center's `append` of leg `b` of `p` succeeds and the
leg is `Committed`.  The deployed code runs the same calls to the same `S₂`, and there that
`append` reverts with `ManagerFlowDeadlinePassed`.  In the mutant, repeating the same
`authorizeRefund` call from the new state succeeds and marks the leg `Revertable`. -/
def Properties.WithoutDeadlineGateLegCommittedAfterRefund : Prop :=
  ∃ (P : ChainParams (List Word)) (pre : List ChainCall) (S₁ S₂ S₃ S₄ : ChainState (List Word))
    (peerAllowed : ℕ → Bool) (flowId : Word) (p : FlowPreimage) (i : ℕ) (a : AbsenceProof)
    (registered : ℕ → Bool) (b : Word) (idx : ℕ),
    ChainRun P withoutDeadlineGate (genesis []) pre S₁ ∧
    execCall P withoutDeadlineGate S₁ (.authorizeRefund peerAllowed flowId p i a) = some S₂ ∧
    appendCall P withoutDeadlineGate S₂ P.interopCenter registered b idx p = .ok S₃ ∧
    S₃.legs.legState flowId b = .Committed ∧
    ChainRun P deployed (genesis []) pre S₁ ∧
    execCall P deployed S₁ (.authorizeRefund peerAllowed flowId p i a) = some S₂ ∧
    appendCall P deployed S₂ P.interopCenter registered b idx p =
      .error (.flowDeadlinePassed p.deadline
        (S₂.roots.latestInteropRootTimestamp p.settlementLayerChainId)) ∧
    execCall P withoutDeadlineGate S₃ (.authorizeRefund peerAllowed flowId p i a) = some S₄ ∧
    S₄.legs.legState flowId b = .Revertable

/-- **KEEPING THE LAST IMPORTED TIMESTAMP INSTEAD OF THE MAXIMUM READMITS THE `append`.**  Under
`lastValueLatest`, a run from genesis reaches `S₁`; `authorizeRefund(flowId, p, i, a)` succeeds;
the continuation `post` imports a root with an earlier timestamp; then the interop center's
`append` of leg `b` of `p` succeeds and the leg is `Committed`.  `LatestBoundsStored` fails in
the state `post` reaches.  The deployed code runs the same calls, and there that `append`
reverts. -/
def Properties.LastValueLatestReadmitsAppend : Prop :=
  ∃ (P : ChainParams (List Word)) (pre post : List ChainCall)
    (S₁ S₂ S₃ S₄ D₁ D₂ D₃ : ChainState (List Word))
    (peerAllowed : ℕ → Bool) (flowId : Word) (p : FlowPreimage) (i : ℕ) (a : AbsenceProof)
    (registered : ℕ → Bool) (b : Word) (idx : ℕ),
    ChainRun P lastValueLatest (genesis []) pre S₁ ∧
    execCall P lastValueLatest S₁ (.authorizeRefund peerAllowed flowId p i a) = some S₂ ∧
    ChainRun P lastValueLatest S₂ post S₃ ∧
    appendCall P lastValueLatest S₃ P.interopCenter registered b idx p = .ok S₄ ∧
    S₄.legs.legState flowId b = .Committed ∧ ¬ LatestBoundsStored S₃.roots ∧
    ChainRun P deployed (genesis []) pre D₁ ∧
    execCall P deployed D₁ (.authorizeRefund peerAllowed flowId p i a) = some D₂ ∧
    ChainRun P deployed D₂ post D₃ ∧
    ∃ e, appendCall P deployed D₃ P.interopCenter registered b idx p = .error e

/-- **WITHOUT THE PROOF'S SETTLEMENT-LAYER CHECK, ANOTHER CHAIN'S ROOT AUTHORIZES THE REFUND AND
THE `append` STILL PASSES.**  Under `unboundProofSettlementLayer`, a run from genesis reaches
`S₁`; `authorizeRefund(flowId, p, i, a)` succeeds with an absence proof whose settlement-layer
chain id is not the flow's; then the interop center's `append` of leg `b` of `p` succeeds and the
leg is `Committed`.  The deployed code runs the same calls to `S₁`, and there that
`authorizeRefund` reverts. -/
def Properties.UnboundProofSettlementLayerReadmitsAppend : Prop :=
  ∃ (P : ChainParams (List Word)) (pre : List ChainCall) (S₁ S₂ S₃ : ChainState (List Word))
    (peerAllowed : ℕ → Bool) (flowId : Word) (p : FlowPreimage) (i : ℕ) (a : AbsenceProof)
    (registered : ℕ → Bool) (b : Word) (idx : ℕ),
    ChainRun P unboundProofSettlementLayer (genesis []) pre S₁ ∧
    execCall P unboundProofSettlementLayer S₁ (.authorizeRefund peerAllowed flowId p i a) =
      some S₂ ∧
    a.settlementLayerChainId ≠ p.settlementLayerChainId ∧
    appendCall P unboundProofSettlementLayer S₂ P.interopCenter registered b idx p = .ok S₃ ∧
    S₃.legs.legState flowId b = .Committed ∧
    ChainRun P deployed (genesis []) pre S₁ ∧
    execCall P deployed S₁ (.authorizeRefund peerAllowed flowId p i a) = none

/-- **A NON-STRICT ROOT-TIMESTAMP CHECK READMITS THE `append`.**  Under `nonStrictRootTimestamp`,
a run from genesis reaches `S₁`; `authorizeRefund(flowId, p, i, a)` succeeds with a root whose
timestamp equals `p.deadline`; then the interop center's `append` of leg `b` of `p` succeeds and
the leg is `Committed`.  The deployed code runs the same calls to `S₁`, and there that
`authorizeRefund` reverts. -/
def Properties.NonStrictRootTimestampReadmitsAppend : Prop :=
  ∃ (P : ChainParams (List Word)) (pre : List ChainCall) (S₁ S₂ S₃ : ChainState (List Word))
    (peerAllowed : ℕ → Bool) (flowId : Word) (p : FlowPreimage) (i : ℕ) (a : AbsenceProof)
    (registered : ℕ → Bool) (b : Word) (idx : ℕ),
    ChainRun P nonStrictRootTimestamp (genesis []) pre S₁ ∧
    execCall P nonStrictRootTimestamp S₁ (.authorizeRefund peerAllowed flowId p i a) = some S₂ ∧
    (S₁.roots.storedInteropRoots a.settlementLayerChainId
      a.settlementLayerBatchNumber).timestamp = p.deadline ∧
    appendCall P nonStrictRootTimestamp S₂ P.interopCenter registered b idx p = .ok S₃ ∧
    S₃.legs.legState flowId b = .Committed ∧
    ChainRun P deployed (genesis []) pre S₁ ∧
    execCall P deployed S₁ (.authorizeRefund peerAllowed flowId p i a) = none

/-- **THE `LatestBoundsStored` PREMISE IS NEEDED.**  A state `S₁` whose root storage holds a
root with a nonzero timestamp above the chain's tracked timestamp (so `LatestBoundsStored` fails;
by `LatestBoundsStoredInvariant` no run from fresh or all-zero-timestamp storage reaches it).
From it, the deployed `authorizeRefund(flowId, p, i, a)` succeeds and then the interop center's
`append` of leg `b` of `p` succeeds, leaving the leg `Committed`. -/
def Properties.WithoutLatestBoundAppendAfterRefund : Prop :=
  ∃ (P : ChainParams (List Word)) (S₁ S₂ S₃ : ChainState (List Word))
    (peerAllowed : ℕ → Bool) (flowId : Word) (p : FlowPreimage) (i : ℕ) (a : AbsenceProof)
    (registered : ℕ → Bool) (b : Word) (idx : ℕ),
    ¬ LatestBoundsStored S₁.roots ∧
    execCall P deployed S₁ (.authorizeRefund peerAllowed flowId p i a) = some S₂ ∧
    appendCall P deployed S₂ P.interopCenter registered b idx p = .ok S₃ ∧
    S₃.legs.legState flowId b = .Committed

/-! ## Non-vacuity -/

/-- **EVERY PREMISE MET, ON A RUN WITH CONTENT.**  The deployed code, from genesis `S₀` (whose
root storage satisfies `LatestBoundsStored`).  `pre₁` (`initL2`, then the interop center's
`append` of leg `h₁` of a three-leg flow `p`) reaches `M`, where the proof `a` does not yet
authenticate and the center's `append` of `p`'s leg `h₃` would succeed.  The root import `imp`
leads to `S₁`, where `a` authenticates, `L1_CHAIN_ID` is set and `h₁` is `Committed`.
`authorizeRefund(flowId, p, i, a)` succeeds with `flowHash p = flowId` and marks `h₁`
`Revertable`.  The continuation `post` claims `h₁` once and appends a leg of a second flow `q`,
whose deadline is later and whose flow id differs from `p`'s; every `append` of the run is of
`p` or `q`.  In the state `post` reaches, `h₁` is `Reverted`, `h₃` is still `Unset`, and the
center's `append` of `h₃` reverts with `ManagerFlowDeadlinePassed`. -/
def Properties.RefundClosesAppendWitness : Prop :=
  ∃ (P : ChainParams (List Word)) (pre₁ post : List ChainCall) (imp : ChainCall)
    (S₀ M S₁ S₂ S₃ M' : ChainState (List Word))
    (peerAllowed : ℕ → Bool) (flowId : Word) (p q : FlowPreimage) (i : ℕ) (a : AbsenceProof)
    (registered : ℕ → Bool) (h₁ h₃ : Word),
    S₀ = genesis [] ∧ LatestBoundsStored S₀.roots ∧
    ChainRun P deployed S₀ pre₁ M ∧ P.rootAuthenticated M.roots a = false ∧
    appendCall P deployed M P.interopCenter registered h₃ 0 p = .ok M' ∧
    execCall P deployed M imp = some S₁ ∧ ChainRun P deployed S₀ (pre₁ ++ [imp]) S₁ ∧
    P.rootAuthenticated S₁.roots a = true ∧ S₁.l1ChainId ≠ 0 ∧
    h₁ ∈ p.legBundleHashes ∧ h₃ ∈ p.legBundleHashes ∧ h₁ ≠ h₃ ∧
    S₁.legs.legState flowId h₁ = .Committed ∧
    execCall P deployed S₁ (.authorizeRefund peerAllowed flowId p i a) = some S₂ ∧
    P.flowHash p = flowId ∧ S₂.legs.legState flowId h₁ = .Revertable ∧
    ChainRun P deployed S₂ post S₃ ∧
    post.countP (ChainCall.isClaimOf flowId h₁) = 1 ∧ S₃.legs.legState flowId h₁ = .Reverted ∧
    (∃ c ∈ post, ∃ caller reg b idx, c = .append caller reg b idx q) ∧ p.deadline < q.deadline ∧
    P.flowHash q ≠ P.flowHash p ∧
    (∀ c ∈ pre₁ ++ imp :: .authorizeRefund peerAllowed flowId p i a :: post,
      ∀ caller reg b idx r, c = .append caller reg b idx r → r = p ∨ r = q) ∧
    S₃.legs.legState flowId h₃ = .Unset ∧
    appendCall P deployed S₃ P.interopCenter registered h₃ 0 p =
      .error (.flowDeadlinePassed p.deadline
        (S₃.roots.latestInteropRootTimestamp p.settlementLayerChainId))

end Contracts.AtomicFlowManager.RefundClosesAppend
