import EraSpec.Protocol.InteropAtomicity.Specs.FlowBindingAtHead

/-!
# Properties: the committed leg is bound to a logged preimage, at head (`3605e82`)

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.FlowBindingAtHead`; proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.FlowBindingAtHead`. No statement takes a hash
premise. Every collision a conclusion mentions is a `PreimageClash` or `CommitClash` on two
named items of the run's own log.

## What the pin needed, and what is gone

* **The real flow.** At the pin, `append` took an opaque `flowId`, so the flow a leg was
  committed under was never on chain. `Contracts.FlowBinding`'s headline could only range
  over flows presented to some later call (its premise `c ∈ log`). At head `append` logs the
  preimage itself. `Properties.CommittedLegHasLoggedPreimage` says every leg that is not
  `Unset` was committed under one logged preimage that contains it, declares it on the
  committing chain, and passes `_checkFlowId` verbatim. So
  `Properties.ExecutedImpliesCommittedFlowFinalizableOrLoggedClash` ranges over the flows the
  legs were committed under, without the `c ∈ log` premise.
* **The declared chain.** At the pin nothing tied a leg's declared source chain
  (`legSourceChainIds[i]`) to the chain that committed it. That half of `A3`'s chain binding
  was left to `bundleHash` embedding `block.chainid` (backlog S4), and the pin's refund model
  marks a leg in the manager of its declared chain as a modelling choice. At head `append`
  checks `legSourceChainIds[legIndex] == block.chainid` on chain. So a leg's declared chain is
  the committing chain, in every logged preimage with its id, unless two logged preimages
  clash (`Properties.DeclaredSourceIsCommittingChainOrLoggedClash`). The same key on two
  chains is such a clash (`Properties.SameKeyAppendedOnTwoChainsIsLoggedClash`). The
  code's `authorizeRefund` marks legs of the chain that runs it, and those are the legs the
  flow declares there, unless two logged preimages clash
  (`Properties.AuthorizeMarksDeclaredLegOrLoggedClash`). A key of a chain's tree is declared
  on that chain by every presented flow with its id
  (`Properties.KeyIsDeclaredOnItsChainOrLoggedClash`), which is
  `AttackVectors.ProofPolarity.HonestInsertion`'s declared-chain side, for a chain running the
  head code, without the bundle-hash premise.
* **"On one chain".** `Contracts.AppendPath.Properties.SystemOncePerLeg` item 3 needs two
  obligations to be on one chain. `Properties.SystemOncePerLegAtHead` drops that premise:
  across chains, one commit value is a pinned `CommitClash` or a pinned `PreimageClash`.

## The pin countermodel and the fix

At the pin a sender could commit a leg under an id that no checked flow listing the leg
hashes to (a wrong or stale `flowId`). `Properties.PinUnboundLegIsStranded` shows such a leg
is stuck in the pin's own model: never refunded, never executed, while its burned funds stay
burned. `Properties.PinUnboundLegWitness` builds one next to a refunded sibling of the same
id. At head that instance has no `append` step (`Properties.PinUnboundLegRejectedAtHead`), and
every committed leg can be marked `Revertable` once a timeout of its own flow is proved
(`Properties.CommittedLegRefundableOnTimeout`).

## Reuse of the pin results

Each chain of a head run is a run of the pin's one-chain model `Contracts.AppendPath.Steps`
(`Properties.RunAtHeadProjectsToChainRuns`), so every result of
`Properties/OncePerLeg.lean` about one chain holds at head. The unbounded low-leaf walk does
not get in the way: a head insert lands where a pin insert with the landing hint lands
(`Properties.HeadInsertLandsWherePinInsertLands`), although it accepts hints the pin's
five-hop walk rejects (`Properties.HeadWalkAcceptsHintPinRejects`).
-/

namespace Contracts.FlowBindingAtHead

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund Contracts.AppendPath
open Contracts.FlowCanonicalAtHead

/-! ## The head check, in the pin's terms -/

/-- **A HEAD FLOW THAT PASSES `_checkFlowId` PASSES THE PIN'S CHECK.** For the pin flow hash
the head preimage hash induces, `pinFlowHash enc l1`. -/
def Properties.HeadCheckIsPinCheck : Prop :=
  ∀ (enc : PreimageHash) (l1 : UInt256) (F : AtomicFlow),
    CheckFlowId enc F → F.preimage.settlementLayerChainId = l1 →
      FlowIdChecked (pinFlowHash enc l1) (pinFlow F)

/-- **THE PIN'S FLOW-ID CLASH IS A PREIMAGE CLASH.** For two checked head flows settling on
`l1`, the pin's `FlowIdClash` between their pin views is exactly a `PreimageClash` between
their preimages. -/
def Properties.PinClashIsPreimageClash : Prop :=
  ∀ (enc : PreimageHash) (l1 : UInt256) (F G : AtomicFlow),
    CheckFlowId enc F → F.preimage.settlementLayerChainId = l1 →
    CheckFlowId enc G → G.preimage.settlementLayerChainId = l1 →
      (FlowIdClash (pinFlowHash enc l1) (pinFlow F) (pinFlow G)
        ↔ PreimageClash enc F.preimage G.preimage)

/-- **A DECLARED LEG IS A PIN LEG.** `⟨c, b⟩` is a leg of the pin view iff the preimage
declares bundle `b` on chain `c`. -/
def Properties.PinLegIffDeclares : Prop :=
  ∀ (P : FlowPreimage) (c b : UInt256), (⟨c, b⟩ : FlowLeg) ∈ pinLegs P ↔ P.Declares b c

/-! ## The unbounded walk -/

/-- **THE HEAD INSERT LANDS WHERE A PIN INSERT LANDS.** On a valid tree, some hint makes the
head insert land on `low` iff some hint makes the pin's bounded insert land there (the landing
hint `low` itself, with no hop). The insert's writes depend only on `low`. -/
def Properties.HeadInsertLandsWherePinInsertLands : Prop :=
  ∀ (T : Tree) (v : UInt256) (low : ℕ), Valid T →
    ((∃ hint, InsertSucceedsAtHead T v hint low) ↔ ∃ hint, InsertSucceeds T v hint low)

/-- **…ALTHOUGH THE HEAD WALK ACCEPTS A HINT THE PIN REJECTS.** On the honest seven-leaf
tree `chainTree 6`, inserting `7` from hint `0` needs six hops: the head insert succeeds and
the pin's five-hop insert reverts for every landing. -/
def Properties.HeadWalkAcceptsHintPinRejects : Prop :=
  InsertSucceedsAtHead (chainTree 6) 7 0 6 ∧ ∀ low, ¬ InsertSucceeds (chainTree 6) 7 0 low

/-! ## The shape of every run -/

/-- **EACH CHAIN OF A HEAD RUN IS A PIN CHAIN RUN.** From every chain at genesis, chain `c`'s
state with the obligations appended on `c` is a run of `Contracts.AppendPath.Steps`. So every
one-chain result of `Properties/OncePerLeg.lean` holds at head. -/
def Properties.RunAtHeadProjectsToChainRuns : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (enc : PreimageHash)
    (l1 : UInt256) (S : System) (Y : Chains) (log : List CallAtHead),
    RunAtHead h z0 hl cv enc l1 S genesisAll Y log →
      ∀ c, Steps cv c genesis (Y c) ((appendLog enc log).filter (fun o => o.chain = c))

/-- **EVERY LOGGED CALL PASSED ITS CHECKS.** Every logged `append`'s preimage is accepted and
computes its id, settles on L1, was not expired when the call read the root storage, declares
the committed bundle on the committing chain, and names only registered chains besides it.
Every logged execution and refund authorization passed its checks. -/
def Properties.LoggedCallsPassedTheirChecks : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (enc : PreimageHash)
    (l1 : UInt256) (S : System) (X Y : Chains) (log : List CallAtHead),
    RunAtHead h z0 hl cv enc l1 S X Y log →
      (∀ a ∈ appendCalls log,
        CheckFlowId enc (committedFlow enc a.preimage)
          ∧ a.preimage.settlementLayerChainId = l1
          ∧ a.env.latestRootTimestamp l1 ≤ a.preimage.deadline
          ∧ a.preimage.Declares a.bundleHash a.chain
          ∧ ∀ src ∈ a.preimage.legSourceChainIds, src ≠ a.chain → a.env.registered src)
      ∧ (∀ e, CallAtHead.execute e ∈ log → e.Verified h z0 hl cv enc l1 S)
      ∧ (∀ a, CallAtHead.authorize a ∈ log → a.Verified h z0 hl cv enc l1 S)

/-! ## The stronger flow binding -/

/-- **THE FLOW A LEG WAS COMMITTED UNDER IS A LOGGED PREIMAGE (HEADLINE).** On every head run
from genesis, every leg `(f, b)` that is not `Unset` in chain `c`'s manager was committed by
exactly one logged `append` on `c`. Its preimage hashes to `f`, passes `_checkFlowId` as the
flow `⟨f, P⟩`, settles on L1, and declares `b` on `c`. -/
def Properties.CommittedLegHasLoggedPreimage : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (enc : PreimageHash)
    (l1 : UInt256) (S : System) (Y : Chains) (log : List CallAtHead),
    RunAtHead h z0 hl cv enc l1 S genesisAll Y log →
      ∀ (c f b : UInt256), (Y c).mgr.legState f b ≠ .Unset →
        ∃! a, a ∈ appendCalls log ∧ a.obligation enc = ⟨f, b, c⟩
          ∧ CheckFlowId enc ⟨f, a.preimage⟩ ∧ a.preimage.settlementLayerChainId = l1
          ∧ a.preimage.Declares b c

/-- **AND A LEG NEVER APPENDED IS `Unset`.** The converse: on every head run from genesis,
`(f, b)` is `Unset` on `c` iff no logged `append` on `c` committed it. -/
def Properties.UnsetIffNotAppended : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (enc : PreimageHash)
    (l1 : UInt256) (S : System) (Y : Chains) (log : List CallAtHead),
    RunAtHead h z0 hl cv enc l1 S genesisAll Y log →
      ∀ (c f b : UInt256), (Y c).mgr.legState f b = .Unset ↔
        ∀ a ∈ appendCalls log, a.obligation enc ≠ ⟨f, b, c⟩

/-- **EVERY COMMITTED LEG IS A LEG OF A FLOW THAT PASSES THE PIN'S CHECK.** The negation of
the pin countermodel's condition, for the pin flow hash the head hash induces. -/
def Properties.CommittedLegIsInACheckedPinFlow : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (enc : PreimageHash)
    (l1 : UInt256) (S : System) (Y : Chains) (log : List CallAtHead),
    RunAtHead h z0 hl cv enc l1 S genesisAll Y log →
      ∀ (c f b : UInt256), (Y c).mgr.legState f b ≠ .Unset →
        ∃ F : Flow, FlowIdChecked (pinFlowHash enc l1) F ∧ F.flowId = f ∧ (⟨c, b⟩ : FlowLeg) ∈ F.legs

/-! ## The declared source chain is the committing chain -/

/-- **A PRESENTED FLOW DECLARES A COMMITTED LEG ON ITS COMMITTING CHAIN, OR TWO LOGGED
PREIMAGES CLASH.** Take a logged `append` of bundle `b` on chain `c` and any logged call (an
`append`, an execution or a refund authorization) with the same flow id whose preimage lists
`b` with chain `c'`. Then `c' = c`, or the two logged preimages clash. -/
def Properties.DeclaredSourceIsCommittingChainOrLoggedClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (enc : PreimageHash)
    (l1 : UInt256) (S : System) (X Y : Chains) (log : List CallAtHead),
    RunAtHead h z0 hl cv enc l1 S X Y log →
      ∀ a ∈ appendCalls log, ∀ k ∈ log, k.flowId enc = enc a.preimage →
        ∀ c' : UInt256, k.preimage.Declares a.bundleHash c' →
          c' = a.chain ∨ PreimageClash enc k.preimage a.preimage

/-- **THE SAME KEY ON TWO CHAINS IS A LOGGED PREIMAGE CLASH.** Two logged `append`s of one
`(flowId, bundleHash)` on two different chains were made under clashing preimages. -/
def Properties.SameKeyAppendedOnTwoChainsIsLoggedClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (enc : PreimageHash)
    (l1 : UInt256) (S : System) (X Y : Chains) (log : List CallAtHead),
    RunAtHead h z0 hl cv enc l1 S X Y log →
      ∀ a ∈ appendCalls log, ∀ a' ∈ appendCalls log,
        enc a.preimage = enc a'.preimage → a.bundleHash = a'.bundleHash → a.chain ≠ a'.chain →
          PreimageClash enc a.preimage a'.preimage

/-- **`authorizeRefund` MARKS ONLY LEGS ITS FLOW DECLARES ON THE CHAIN RUNNING IT, OR TWO LOGGED
PREIMAGES CLASH.** The code marks the presented flow's `Committed` legs in the manager that
runs the call (`AtomicFlowManager.sol:235-243`). For every logged refund authorization on
chain `x` that marked `b`: the flow declares `b` on `x`, or the leg was appended on `x` under a
logged preimage with the same id that clashes with the presented one. So the pin's
`Contracts.Refund.ReachLog`, which marks a leg on its declared chain, is the code's behaviour
at head up to a logged clash. -/
def Properties.AuthorizeMarksDeclaredLegOrLoggedClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (enc : PreimageHash)
    (l1 : UInt256) (S : System) (Y : Chains) (log : List CallAtHead),
    RunAtHead h z0 hl cv enc l1 S genesisAll Y log →
      ∀ a, CallAtHead.authorize a ∈ log →
        a.flow.preimage.Declares a.marked a.chain
          ∨ ∃ ap ∈ appendCalls log, ap.obligation enc = ⟨a.flow.flowId, a.marked, a.chain⟩
              ∧ PreimageClash enc a.flow.preimage ap.preimage

/-- **A KEY OF CHAIN `c`'S TREE IS DECLARED ON `c` (HONEST INSERTION AT HEAD).** Let a logged
call present a preimage that lists bundle `b` with chain `c'`, and let the commit value of
`(its flow id, b)` be a nonzero key of chain `c`'s tree. Then `c' = c`, or that commit value
clashes with a leg appended on `c`, or the presented preimage clashes with a logged `append`
preimage on `c`. This is `AttackVectors.ProofPolarity.HonestInsertion`'s declared-chain side
for chain `c` running the head code. It takes no premise about other chains and none about
how `bundleHash` is computed. -/
def Properties.KeyIsDeclaredOnItsChainOrLoggedClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (enc : PreimageHash)
    (l1 : UInt256) (S : System) (Y : Chains) (log : List CallAtHead),
    RunAtHead h z0 hl cv enc l1 S genesisAll Y log →
      ∀ k ∈ log, ∀ (c c' b : UInt256), k.preimage.Declares b c' →
        cv (k.flowId enc) b ≠ 0 → cv (k.flowId enc) b ∈ keys (toAbs (Y c).tree) →
          c' = c
            ∨ (∃ o ∈ appendLog enc log, o.chain = c ∧ CommitClash cv ⟨k.flowId enc, b, c⟩ o)
            ∨ (∃ ap ∈ appendCalls log, ap.chain = c ∧ PreimageClash enc k.preimage ap.preimage)

/-! ## Once per leg -/

/-- **ONCE PER LEG ON EACH CHAIN, AT HEAD.** The pin's one-chain headline
`Contracts.AppendPath.Properties.OncePerLeg`, on each chain `c` of a head run from genesis,
whose log is the obligations appended on `c`: no obligation twice; each on `c` and at exactly
one index of `c`'s tree; two with one commit value are equal. In addition, each was committed
under a preimage that declares it on `c`. -/
def Properties.OncePerLegAtHead : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (enc : PreimageHash)
    (l1 : UInt256) (S : System) (Y : Chains) (log : List CallAtHead),
    RunAtHead h z0 hl cv enc l1 S genesisAll Y log → ∀ c : Chain,
      (chainLog enc c log).Nodup
        ∧ (∀ o ∈ chainLog enc c log, o.chain = c
            ∧ ∃! i, i < (Y c).tree.leafCount ∧ ((Y c).tree.leaf i).value = commitOf cv o)
        ∧ (∀ o ∈ chainLog enc c log, ∀ o' ∈ chainLog enc c log,
            commitOf cv o = commitOf cv o' → o = o')
        ∧ (∀ a ∈ appendCalls log, a.chain = c → a.preimage.Declares a.bundleHash c)

/-! ## Once per leg, every chain at once -/

/-- **ONCE PER LEG AT HEAD, WITHOUT "ON ONE CHAIN".** On every head run from genesis:

1. no obligation is appended twice;
2. each appended obligation occupies exactly one index of its own chain's tree;
3. two logged `append`s with one commit value committed the same obligation, or they ran on
   different chains and their keys clash under `cv`, or their preimages clash.

Item 3 is `Contracts.AppendPath.Properties.SystemOncePerLeg` item 3 without its premise that
the two obligations are on one chain. -/
def Properties.SystemOncePerLegAtHead : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (enc : PreimageHash)
    (l1 : UInt256) (S : System) (Y : Chains) (log : List CallAtHead),
    RunAtHead h z0 hl cv enc l1 S genesisAll Y log →
      (appendLog enc log).Nodup
        ∧ (∀ o ∈ appendLog enc log, ∃! i, i < (Y o.chain).tree.leafCount
            ∧ ((Y o.chain).tree.leaf i).value = commitOf cv o)
        ∧ (∀ a ∈ appendCalls log, ∀ a' ∈ appendCalls log,
            commitOf cv (a.obligation enc) = commitOf cv (a'.obligation enc) →
              a.obligation enc = a'.obligation enc
                ∨ (a.chain ≠ a'.chain ∧ CommitClash cv (a.obligation enc) (a'.obligation enc))
                ∨ PreimageClash enc a.preimage a'.preimage)

/-! ## The flow-binding headlines, at head -/

/-- **AN EXECUTION FINALIZES EVERY FLOW A LEG WAS COMMITTED UNDER WITH ITS ID, OR A LOCATED
BREAK, OR A LOGGED CLASH (HEADLINE).** The head form of
`Contracts.FlowBinding.Properties.ExecutedImpliesRealFlowFinalizableOrLoggedClash`. Premises: a
well-formed system and data availability. Take any head run, any logged execution `e`, and any
logged `append` whose preimage hashes to `e`'s flow id. Then one of three holds:

* every leg of the flow that `append` committed under is finalizable;
* `e`'s gate evidence carries a `TreeRootBreak` on the first leg of `e`'s flow that is not
  finalizable (`PinnedGateBreak`);
* `e`'s preimage and the `append`'s preimage clash.

The "real flow" is now the committed-under flow, recorded by `append` itself, rather than a
flow some later call happened to present. -/
def Properties.ExecutedImpliesCommittedFlowFinalizableOrLoggedClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (enc : PreimageHash)
    (l1 : UInt256) (S : System), Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (X Y : Chains) (log : List CallAtHead), RunAtHead h z0 hl cv enc l1 S X Y log →
    ∀ (e : ExecCallAtHead), CallAtHead.execute e ∈ log →
    ∀ a ∈ appendCalls log, enc a.preimage = e.flow.flowId →
      FlowFinalizableBy h z0 hl cv S A (pinFlow (committedFlow enc a.preimage))
        ∨ PinnedGateBreak h z0 hl cv S A (pinFlow e.flow) e.evidence
        ∨ PreimageClash enc e.flow.preimage a.preimage

/-- **THE SAME, PER LEG.** For every leg `other` of the committed-under flow: `other` is
finalizable, or `e`'s inclusion proof for `other` carries a break, or the two logged preimages
clash. In particular for the committed leg itself. -/
def Properties.ExecutedImpliesCommittedLegFinalizableOrLoggedClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (enc : PreimageHash)
    (l1 : UInt256) (S : System), Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (X Y : Chains) (log : List CallAtHead), RunAtHead h z0 hl cv enc l1 S X Y log →
    ∀ (e : ExecCallAtHead), CallAtHead.execute e ∈ log →
    ∀ a ∈ appendCalls log, enc a.preimage = e.flow.flowId →
    ∀ other ∈ pinLegs a.preimage,
      LegFinalizableBy h z0 hl cv S A (pinFlow (committedFlow enc a.preimage)) other
        ∨ InclusionBreak h z0 hl S other.chain (e.evidence other).1 (e.evidence other).2
        ∨ PreimageClash enc e.flow.preimage a.preimage

/-- **A LOGGED EXECUTION AND A LOGGED REFUND AUTHORIZATION OF ONE ID: A LOCATED BREAK OR A
LOGGED CLASH.** The head form of
`Contracts.FlowBinding.Properties.LoggedExecutionExcludesLoggedRefundOrBreak`. -/
def Properties.LoggedExecutionExcludesLoggedRefundOrBreakAtHead : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (enc : PreimageHash)
    (l1 : UInt256) (S : System), Wf S →
    ∀ (X Y : Chains) (log : List CallAtHead), RunAtHead h z0 hl cv enc l1 S X Y log →
    ∀ (e : ExecCallAtHead), CallAtHead.execute e ∈ log →
    ∀ (r : AuthCallAtHead), CallAtHead.authorize r ∈ log → r.flow.flowId = e.flow.flowId →
      InclusionBreak h z0 hl S r.missing.chain (e.evidence r.missing).1 (e.evidence r.missing).2
        ∨ AbsenceBreak h z0 hl S r.flow.preimage.deadline r.missing.chain r.batch r.proof
        ∨ PreimageClash enc e.flow.preimage r.flow.preimage

/-- **ONE EXECUTION FREEZES ITS FLOW ID, OR A LOCATED BREAK OR CLASH SITS ON TWO LOGGED
CALLS.** On every head run from genesis, take a logged execution `e`. For every chain `c` and
bundle hash `b`, either the obligation `(e.flow.flowId, b)` on `c` is not past `Committed`, or
a logged `authorizeRefund` that ran on `c` and marked `(e.flow.flowId, b)` carries one of: a
break on `e`'s inclusion proof for its missing leg, a break on its own absence proof, or a
clash between the two logged preimages. In particular no leg of the executed flow is refunded
without such a witness. Unlike the pin's
`Contracts.AppendPath.Properties.SystemExecutedObligationNeverRefundedOrBreak`, the executed
flow comes from the log, and `authorizeRefund` marks legs where the code marks them. -/
def Properties.ExecutionFreezesItsFlowOrLoggedBreakAtHead : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (enc : PreimageHash)
    (l1 : UInt256) (S : System), Wf S →
    ∀ (Y : Chains) (log : List CallAtHead), RunAtHead h z0 hl cv enc l1 S genesisAll Y log →
    ∀ (e : ExecCallAtHead), CallAtHead.execute e ∈ log →
    ∀ (c b : UInt256),
      ¬ Refunded Y.mgrs ⟨e.flow.flowId, b, c⟩
        ∨ ∃ r, CallAtHead.authorize r ∈ log ∧ r.chain = c ∧ r.flow.flowId = e.flow.flowId
            ∧ r.marked = b
            ∧ (InclusionBreak h z0 hl S r.missing.chain (e.evidence r.missing).1
                  (e.evidence r.missing).2
                ∨ AbsenceBreak h z0 hl S r.flow.preimage.deadline r.missing.chain r.batch r.proof
                ∨ PreimageClash enc e.flow.preimage r.flow.preimage)

/-- **A LEG PAST `Committed` WAS MARKED BY A LOGGED `authorizeRefund` ON ITS CHAIN.** On every
head run from genesis, if `(f, b)` is `Revertable` or `Reverted` on chain `c`, some logged
refund authorization ran on `c` and marked exactly `(f, b)`. -/
def Properties.RefundedLegWasAuthorizedOnItsChain : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (enc : PreimageHash)
    (l1 : UInt256) (S : System) (Y : Chains) (log : List CallAtHead),
    RunAtHead h z0 hl cv enc l1 S genesisAll Y log →
      ∀ (c f b : UInt256), 2 ≤ rank ((Y c).mgr.legState f b) →
        ∃ r, CallAtHead.authorize r ∈ log ∧ r.chain = c ∧ r.flow.flowId = f ∧ r.marked = b

/-! ## The pin countermodel, and the fix -/

/-- **AT THE PIN, A LEG COMMITTED UNDER AN ID THAT NO CHECKED FLOW LISTING IT HASHES TO IS
STRANDED.** Over the pin's `Contracts.Refund.ReachLog` (unchanged): suppose obligation `o` is
`Committed` at the start of a run, and every flow that passes `_checkFlowId` with `o`'s id
lists no leg with `o`'s bundle hash. Then `o` is still `Committed` at the end of the run, and
no execution through a checked flow with `o`'s id executes a leg with its bundle hash. So its
funds, burned at send time, are never released by either path. The pin's `append`
(`c67894b9` `AtomicFlowManager.sol:87-102`) takes any `flowId`, so such a leg is committable
there (`Properties.PinUnboundLegWitness`). -/
def Properties.PinUnboundLegIsStranded : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (Ms Ns : Managers) (alog : List AuthCall) (o : Obligation),
    ReachLog h z0 hl cv fh S Ms Ns alog →
    (∀ F : Flow, FlowIdChecked fh F → F.flowId = o.flowId →
      ∀ leg ∈ F.legs, leg.bundleHash ≠ o.bundleHash) →
    stateOf Ms o = .Committed →
      stateOf Ns o = .Committed
        ∧ ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
            ExecutedViaBy h z0 hl cv fh S F ev leg → F.flowId = o.flowId →
              leg.bundleHash ≠ o.bundleHash

/-- **THE PIN COUNTERMODEL'S PREMISES HOLD, NEXT TO A REFUNDED SIBLING.** For every node hash,
padding constant and leaf hash: in the pin's `Contracts.Refund.ReachLog`, chain `1` appends
leg `(0, 1)` of the one-leg flow `F0` (id `0`) and the leg `(0, 2)` under the same id, which
`F0` does not list. A timeout of `F0` is verified and `(0, 1)` is marked `Revertable`. The flow
hash is honest about `F0`, so `(0, 2)` is unbound, and it is still `Committed`. -/
def Properties.PinUnboundLegWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (Ms : Managers) (alog : List AuthCall)
      (o : Obligation),
      ReachLog h z0 hl cv fh S emptyManagers Ms alog
        ∧ (∀ F : Flow, FlowIdChecked fh F → F.flowId = o.flowId →
            ∀ leg ∈ F.legs, leg.bundleHash ≠ o.bundleHash)
        ∧ stateOf Ms o = .Committed
        ∧ (∃ a ∈ alog, a.flow.flowId = o.flowId ∧ a.leg.chain = o.chain)
        ∧ Refunded Ms ⟨o.flowId, 1, o.chain⟩

/-- **THE PIN INSTANCE IS REJECTED AT HEAD.** If no flow that passes the pin's check under
`pinFlowHash enc l1` with id `enc P` lists bundle `b`, then no head `append` of `b` under `P`
succeeds, on any chain, in any state, with any environment. -/
def Properties.PinUnboundLegRejectedAtHead : Prop :=
  ∀ (enc : PreimageHash) (cv : CommitValue) (l1 : UInt256) (env : AppendEnv) (c : Chain)
    (s : ChainState) (b : UInt256) (P : FlowPreimage) (hint low : ℕ),
    (∀ F : Flow, FlowIdChecked (pinFlowHash enc l1) F → F.flowId = enc P →
      ∀ leg ∈ F.legs, leg.bundleHash ≠ b) →
      ¬ AppendSucceedsAtHead enc cv l1 env c s b P hint low

/-- **`PinUnboundLegRejectedAtHead`'S PREMISE IS SATISFIABLE.** Under the hash honest about the
one-leg preimage `P` (bundle `1` on chain `0`), no flow that passes the pin's check with `P`'s
id lists bundle `2`, so appending `2` under `P` is rejected at head; and `1` itself is listed. -/
def Properties.PinUnboundLegRejectedAtHeadWitness : Prop :=
  ∃ (enc : PreimageHash) (l1 : UInt256) (P : FlowPreimage),
    PreimageAccepted P ∧ P.settlementLayerChainId = l1
      ∧ (∀ F : Flow, FlowIdChecked (pinFlowHash enc l1) F → F.flowId = enc P →
          ∀ leg ∈ F.legs, leg.bundleHash ≠ 2)
      ∧ P.Declares 1 0

/-- **AT HEAD A COMMITTED LEG IS REFUNDABLE ONCE ITS OWN FLOW TIMES OUT.** On every head run
from genesis, a leg `(f, b)` `Committed` on chain `c` has a logged `append` that committed it.
For every leg `m` of that flow and every verified timeout of `m`, the run extends by the
`authorizeRefund` on `c` that presents the committed-under flow, and that step marks `(f, b)`
`Revertable`. -/
def Properties.CommittedLegRefundableOnTimeout : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (enc : PreimageHash)
    (l1 : UInt256) (S : System) (Y : Chains) (log : List CallAtHead),
    RunAtHead h z0 hl cv enc l1 S genesisAll Y log →
      ∀ (c f b : UInt256), (Y c).mgr.legState f b = .Committed →
        ∃ a ∈ appendCalls log, a.obligation enc = ⟨f, b, c⟩
          ∧ ∀ (m : FlowLeg) (N : ℕ) (q : ImtProof), m ∈ pinLegs a.preimage →
              LegRefundableBy h z0 hl cv S (pinFlow (committedFlow enc a.preimage)) m N q →
                RunAtHead h z0 hl cv enc l1 S genesisAll
                  (Y.update c ⟨(Y c).mgr.set f b .Revertable, (Y c).tree⟩)
                  (.authorize ⟨c, committedFlow enc a.preimage, b, m, N, q⟩ :: log)

/-! ## Witnesses -/

/-- **AN HONEST HEAD RUN THAT USES EVERY CALL, AND THE HEADLINES' CONTENT ON IT.** For every
node hash, padding constant and leaf hash, there is a well-formed system with data
availability and a head run from genesis whose log holds:

* `append`s of both legs of a two-leg flow (on chains `0` and `1`) and of a one-leg flow with
  a different id (on chain `2`);
* an execution `e` of the two-leg flow;
* a refund authorization `r` of the one-leg flow, on chain `2`.

On it: the logged preimages have no clash; the leg `a` committed on chain `0` is still
`Committed`, and its commit value is a nonzero key of chain `0`'s tree; that leg's flow has
the executed id and is all finalizable, with no pinned break; for the `append` with the other
id, all three disjuncts of `Properties.ExecutedImpliesCommittedFlowFinalizableOrLoggedClash`
fail, so its same-id premise is load-bearing; `r` marked a leg its flow declares on chain
`2`; and that leg is past `Committed`. -/
def Properties.FlowBindingAtHeadWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (enc : PreimageHash) (l1 : UInt256) (S : System) (A : Access)
      (Y : Chains) (log : List CallAtHead) (e : ExecCallAtHead) (r : AuthCallAtHead)
      (a a' : AppendCall),
      Wf S ∧ DataAvailable h z0 hl S A ∧ RunAtHead h z0 hl cv enc l1 S genesisAll Y log
        ∧ CallAtHead.execute e ∈ log ∧ CallAtHead.authorize r ∈ log
        ∧ a ∈ appendCalls log ∧ a' ∈ appendCalls log ∧ (appendCalls log).length = 3
        ∧ ¬ LoggedPreimageClash enc log
        ∧ (Y a.chain).mgr.legState (enc a.preimage) a.bundleHash = .Committed
        ∧ cv (enc a.preimage) a.bundleHash ≠ 0
        ∧ cv (enc a.preimage) a.bundleHash ∈ keys (toAbs (Y a.chain).tree)
        ∧ enc a.preimage = e.flow.flowId
        ∧ FlowFinalizableBy h z0 hl cv S A (pinFlow (committedFlow enc a.preimage))
        ∧ ¬ PinnedGateBreak h z0 hl cv S A (pinFlow e.flow) e.evidence
        ∧ enc a'.preimage ≠ e.flow.flowId
        ∧ ¬ (FlowFinalizableBy h z0 hl cv S A (pinFlow (committedFlow enc a'.preimage))
              ∨ PinnedGateBreak h z0 hl cv S A (pinFlow e.flow) e.evidence
              ∨ PreimageClash enc e.flow.preimage a'.preimage)
        ∧ r.flow.preimage.Declares r.marked r.chain
        ∧ Refunded Y.mgrs ⟨r.flow.flowId, r.marked, r.chain⟩

/-- **THE SUBSET-FLOW ATTACK AT HEAD LANDS IN THE LOGGED CLASH, AND ONLY THERE.**
`Contracts.FlowBinding.Properties.SubsetFlowAttackLandsInLoggedClash`, replayed against the
head code. For every node hash, padding constant and leaf hash, under a preimage hash that
gives one id to a two-leg preimage (bundle `1` on chain `0`, bundle `2` on chain `1`) and its
one-leg truncation (bundle `1` on chain `0` only), a head run:

1. appends the real flow's leg `2` on chain `1`, under the real preimage;
2. executes leg `1` through the truncated preimage, on honest evidence (chain `0` committed
   leg `1` in the fixed history);
3. authorizes a refund of the real flow on chain `1`, on the honest absence proof for leg `2`.

All three calls claim one id. The committed-under flow of the logged `append` is not
finalizable and the execution's evidence carries no pinned break, so in
`Properties.ExecutedImpliesCommittedFlowFinalizableOrLoggedClash` only the clash holds. In
`Properties.LoggedExecutionExcludesLoggedRefundOrBreakAtHead` neither break holds and the clash
does. So the same-id premises of both results are satisfiable, and the attack the flow-id check
exists to stop is exactly a collision between two preimages the run itself logged. -/
def Properties.SubsetFlowAttackAtHeadLandsInLoggedClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (enc : PreimageHash) (l1 : UInt256) (S : System) (A : Access)
      (Y : Chains) (log : List CallAtHead) (e : ExecCallAtHead) (r : AuthCallAtHead)
      (a : AppendCall),
      Wf S ∧ DataAvailable h z0 hl S A ∧ RunAtHead h z0 hl cv enc l1 S genesisAll Y log
        ∧ CallAtHead.execute e ∈ log ∧ CallAtHead.authorize r ∈ log ∧ a ∈ appendCalls log
        ∧ enc a.preimage = e.flow.flowId ∧ r.flow.flowId = e.flow.flowId
        ∧ ¬ FlowFinalizableBy h z0 hl cv S A (pinFlow (committedFlow enc a.preimage))
        ∧ ¬ PinnedGateBreak h z0 hl cv S A (pinFlow e.flow) e.evidence
        ∧ PreimageClash enc e.flow.preimage a.preimage
        ∧ ¬ InclusionBreak h z0 hl S r.missing.chain (e.evidence r.missing).1
            (e.evidence r.missing).2
        ∧ ¬ AbsenceBreak h z0 hl S r.flow.preimage.deadline r.missing.chain r.batch r.proof
        ∧ PreimageClash enc e.flow.preimage r.flow.preimage

/-- **THE CLASH DISJUNCTS ARE LIVE: ONE KEY ON TWO CHAINS.** Under the constant preimage hash,
chain `0` appends bundle `5` under a preimage that declares it on chain `0`, and chain `1`
appends bundle `5` under one that declares it on chain `1`. Both runs' checks pass, the one
key `(0, 5)` is committed on two chains, and the two logged preimages clash. So
`Properties.SameKeyAppendedOnTwoChainsIsLoggedClash` has satisfiable premises, and in
`Properties.DeclaredSourceIsCommittingChainOrLoggedClash` the clash is the only disjunct that
holds. -/
def Properties.SameKeyOnTwoChainsWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (enc : PreimageHash) (l1 : UInt256) (S : System) (Y : Chains)
      (log : List CallAtHead) (a a' : AppendCall),
      RunAtHead h z0 hl cv enc l1 S genesisAll Y log
        ∧ a ∈ appendCalls log ∧ a' ∈ appendCalls log
        ∧ enc a.preimage = enc a'.preimage ∧ a.bundleHash = a'.bundleHash ∧ a.chain ≠ a'.chain
        ∧ a'.preimage.Declares a.bundleHash a'.chain
        ∧ PreimageClash enc a'.preimage a.preimage

end Contracts.FlowBindingAtHead
