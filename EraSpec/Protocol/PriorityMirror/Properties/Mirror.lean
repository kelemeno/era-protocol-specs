import EraSpec.Protocol.PriorityMirror.Specs.Mirror

/-!
# Properties: the gateway's priority tree mirrors L1's, and a migration out and back loses or
repeats no L1 priority operation

Statements about `EraSpec.Protocol.PriorityMirror.Specs.Mirror`. Proofs are in
`EraSpec.Protocol.PriorityMirror.Proofs.Mirror`. No statement has a hash premise.

Three kinds of run appear. `Unrestricted` runs have no premise. `ConsistentProcessing` runs only
process leaves a copy holds. `Honest` runs also respect FREEZE-ORDER: until the L1 mint, no relay
for the chain executes on the gateway while its gateway copy is frozen. "Processed" means that a
copy's `processBatch` advanced over the leaf; L2 execution is not modelled.

* The L1 copy during the move to the gateway (`InProgressIffInFlight`, `L1SnapshotFrozen`,
  `FailureRestoresL1`).
* **Relays**, with no FREEZE-ORDER premise. Before the L1 mint a relay is dropped exactly when the
  gateway copy is frozen (`RelayDropsIffFrozen`). From the gateway copy's creation until the L1
  mint, the gateway leaves followed by the pending relays are the L1 leaves exactly when no relay
  has been dropped (`MirrorIffNoDrop`); after a drop that equality fails until the L1 mint
  (`MirrorBreakPermanent`).
* **Mirror** (`MirrorPrefix`): in honest runs, from the gateway copy's creation until the L1
  mint, the gateway tree's leaves followed by the pending relays are exactly the L1 tree's
  leaves, and both trees' storage is the result of pushing those leaves from the setup state. No
  relay is dropped before the L1 mint (`NoRelayDroppedBeforeReturn`).
* **No operation lost or repeated** (`ExecutedIsL1Prefix`, headline): in honest runs, the
  operations processed by either copy, in processing order, are a prefix of the L1 tree's leaves;
  whenever the L1 copy settles they are exactly the leaves below its unprocessed index.
  `ReturnMintChecksPass`: with migrations enabled and the L1 pause timestamp set, the L1 mint's
  modelled checks pass.
* **Without FREEZE-ORDER** (`DroppedRelayCountermodel`): a relay executed while the gateway copy
  is frozen is dropped, the next operation takes its index on the gateway, the processed
  sequence stops being a prefix of the L1 leaves (`ExecutedDivergencePermanent`: for good), and
  the L1 mint step reverts on its historical-root check. In every consistent run the check passes in
  that situation only through a root collision between two named leaf lists
  (`ReturnRootCheckIffRootMatch`, `BrokenReturnNeedsRootCollision`). If instead the processed
  operations are still an L1 prefix at the return, the return goes through as in honest runs
  (`ReturnMintPassesOnPrefix`); its witness drops a relay and processes that operation on L1
  after the return.
* At this commit (`MigrationsDisabledKeepL1Settling`): with migrations disabled the L1 copy
  always settles, no relay is ever queued and no gateway copy exists.
* Witnesses for every statement with premises.
-/

namespace Protocol.PriorityMirror

open Contracts.MailboxFacet

/-! ## The L1 copy during the move to the gateway -/

/-- **`isMigrationInProgress` MARKS EXACTLY THE WINDOW.** In every reachable state, the chain
asset handler's flag for the chain is set exactly between an L1 burn and its confirmation. -/
def Properties.InProgressIffInFlight : Prop :=
  ∀ (P : Params) (s : St), Reach P Unrestricted s → (s.inProgress = true ↔ s.phase.InFlight)

/-- **THE L1 COPY IS FROZEN BETWEEN THE BURN AND ITS CONFIRMATION.** In every reachable state
between an L1 burn and its confirmation, with `pre` the L1 diamond just before the burn:
`isMigrationInProgress` is set, so `depositsPaused()` is true and every L1 request step reverts;
`pre` settled and had a nonzero pause timestamp; the L1 copy no longer settles; its priority tree,
batch counters and stored batch hashes, and pause timestamp are those of `pre`; no relay is queued.
While the gateway transaction is in flight it carries `prepareChainCommitment` of `pre`. (The
frozen flag is not part of the statement: `freezeDiamond` may run in between.) -/
def Properties.L1SnapshotFrozen : Prop :=
  ∀ (P : Params) (s : St) (pre : ChainDiamond), Reach P Unrestricted s →
    s.phase.preBurn = some pre →
    s.inProgress = true ∧ depositsPausedL1 P s = true
    ∧ pre.settling = true ∧ pre.pausedTs ≠ 0 ∧ s.d1.settling = false
    ∧ s.d1.tree = pre.tree ∧ s.d1.batches = pre.batches ∧ s.d1.pausedTs = pre.pausedTs
    ∧ s.relays = []
    ∧ (∀ h, step P s (.request h) = none)
    ∧ (∀ c, s.phase = .toGW pre c → prepare pre = some c)

/-- **A FAILED MOVE RESTORES THE L1 COPY.** A successful failure confirmation from a reachable
state follows a failed gateway transaction; afterwards the chain settles on L1 again, the flag
is clear, and the L1 diamond is the one just before the burn except that deposits are unpaused
(and the frozen flag is whatever it was). -/
def Properties.FailureRestoresL1 : Prop :=
  ∀ (P : Params) (s s' : St), Reach P Unrestricted s → step P s (.confirm false) = some s' →
    ∃ pre, s.phase = .gwFailed pre ∧ s'.phase = .onL1 ∧ s'.inProgress = false
      ∧ s'.d1 = { pre with pausedTs := 0, frozen := s.d1.frozen }

/-! ## The mirror -/

/-- **THE GATEWAY TREE IS A PREFIX OF THE L1 TREE.** In every honest reachable state from the
gateway copy's creation until the L1 mint: the gateway copy exists with the L1 copy's start
index; its leaves followed by the pending relays, in order, are exactly the L1 tree's leaves; and
each copy's incremental-tree storage (`_nextLeafIndex`, `_sides`, `_zeros`) is what pushing its
leaves in order from the setup state gives. -/
def Properties.MirrorPrefix : Prop :=
  ∀ (P : Params) (s : St), Reach P Honest s → s.phase.Mirrored →
    ∃ d, s.d2 = some d ∧ d.tree.startIndex = s.d1.tree.startIndex
      ∧ s.leaves2 ++ s.relays = s.log1
      ∧ pushAll P.tree.node (setupTree P.tree) s.leaves2 = some d.tree.tree
      ∧ pushAll P.tree.node (setupTree P.tree) s.log1 = some s.d1.tree.tree

/-- **IN HONEST RUNS NO RELAY IS DROPPED BEFORE THE RETURN.** In every honest reachable state
before the L1 mint, no relay has been dropped. -/
def Properties.NoRelayDroppedBeforeReturn : Prop :=
  ∀ (P : Params) (s : St), Reach P Honest s → s.phase ≠ .back → s.dropped = []

/-! ## Relays, without FREEZE-ORDER -/

/-- **A RELAY IS DROPPED EXACTLY WHEN THE GATEWAY COPY IS FROZEN.** In every consistent reachable
state before the L1 mint with relay `h` pending (and `rest` behind it), the gateway copy exists.
If it is frozen, the relay step consumes `h`, records it as dropped and changes nothing else. If
it is not frozen, the Mailbox write of `h` into the gateway tree succeeds, and the relay step
consumes `h`, stores that tree and appends `h` to the gateway leaves. -/
def Properties.RelayDropsIffFrozen : Prop :=
  ∀ (P : Params) (s : St) (h : UInt256) (rest : List UInt256),
    Reach P ConsistentProcessing s → s.phase ≠ .back → s.relays = h :: rest →
    ∃ d, s.d2 = some d
      ∧ (d.frozen = true →
          step P s .relay = some { s with relays := rest, dropped := s.dropped ++ [h] })
      ∧ (d.frozen = false → ∃ t, mailboxWrite P.tree d.tree h = some t
          ∧ step P s .relay = some { s with relays := rest, d2 := some { d with tree := t },
                                            leaves2 := s.leaves2 ++ [h] })

/-- **THE MIRROR HOLDS EXACTLY WHILE NO RELAY HAS BEEN DROPPED.** In every reachable state (no
premise on the run) from the gateway copy's creation until the L1 mint: the gateway leaves, the
pending relays and the dropped relays are together as many as the L1 tree's leaves; and the
gateway leaves followed by the pending relays are exactly the L1 tree's leaves if and only if no
relay has been dropped. -/
def Properties.MirrorIffNoDrop : Prop :=
  ∀ (P : Params) (s : St), Reach P Unrestricted s → s.phase.Mirrored →
    s.leaves2.length + s.relays.length + s.dropped.length = s.log1.length
    ∧ (s.leaves2 ++ s.relays = s.log1 ↔ s.dropped = [])

/-- **A DROP BREAKS THE MIRROR UNTIL THE RETURN.** If a relay has been dropped in a reachable
state, then in every later state before the L1 mint, the gateway leaves followed by the pending
relays are not the L1 tree's leaves. -/
def Properties.MirrorBreakPermanent : Prop :=
  ∀ (P : Params) (s s' : St), Reach P Unrestricted s → Steps P Unrestricted s s' →
    s.dropped ≠ [] → s'.phase.Mirrored → s'.leaves2 ++ s'.relays ≠ s'.log1

/-! ## No operation lost or repeated -/

/-- **HEADLINE: EVERY L1 OPERATION IS PROCESSED AT MOST ONCE, IN ORDER.** In every honest
reachable state, the sequence of leaves that `processBatch` of either copy advanced over, in
processing order, is a prefix of the L1 tree's leaves. Whenever the L1 copy settles (before any
migration, after a failed one, and after the return), that sequence is exactly the L1 leaves
below the L1 tree's unprocessed index, and the rest of the L1 leaves are its unprocessed range. -/
def Properties.ExecutedIsL1Prefix : Prop :=
  ∀ (P : Params) (s : St), Reach P Honest s →
    s.executed <+: s.log1
    ∧ (s.d1.settling = true →
        s.executed = s.log1.take s.d1.tree.unprocessedIndex
        ∧ s.d1.tree.unprocessedIndex ≤ s.log1.length)

/-- **THE RETURN MINT'S CHECKS PASS.** In every honest reachable state where the gateway burn's
message is in flight, with migrations enabled and a nonzero L1 pause timestamp (the mint's own
`pausedDepositsTimestamp != 0` check): the commitment has a root, that root is historical in the L1
tree, `l1Reinit` and the batch checks pass, and the modelled L1 mint step succeeds. It sets the L1
unprocessed index to the number of processed operations, which are then the L1 leaves below it. The
checks the model omits as reject-only (protocol versions, permanent rollup, the chain asset
handler's pauses, and the bridgehub, message-root and asset-router steps around the mint) are not
covered. -/
def Properties.ReturnMintChecksPass : Prop :=
  ∀ (P : Params) (s : St) (c : ChainCommitment), Reach P Honest s → s.phase = .toL1 c →
    P.migrationsEnabled = true → s.d1.pausedTs ≠ 0 →
    c.priorityTree.sides ≠ []
    ∧ s.d1.tree.isHistoricalRoot (lastSide c.priorityTree) = true
    ∧ (s.d1.tree.l1Reinit c.priorityTree).isSome = true
    ∧ (mintBatches s.d1.batches c).isSome = true
    ∧ ∃ s', step P s .l1Mint = some s' ∧ s'.phase = .back
      ∧ s'.d1.tree.unprocessedIndex = s.executed.length
      ∧ s'.executed = s'.log1.take s'.d1.tree.unprocessedIndex

/-! ## Without FREEZE-ORDER -/

/-- **A RETURN WHOSE PROCESSED OPERATIONS ARE AN L1 PREFIX GOES THROUGH.** In every consistent
reachable state (no FREEZE-ORDER premise) where the gateway burn's message is in flight, with
migrations enabled, a nonzero L1 pause timestamp, and the processed operations a prefix of the L1
leaves: the commitment has a root, that root is historical in the L1 tree, `l1Reinit` and the batch
checks pass, and the modelled L1 mint step succeeds. It sets the L1 unprocessed index to the number
of processed operations, which are then the L1 leaves below it. -/
def Properties.ReturnMintPassesOnPrefix : Prop :=
  ∀ (P : Params) (s : St) (c : ChainCommitment), Reach P ConsistentProcessing s →
    s.phase = .toL1 c → P.migrationsEnabled = true → s.d1.pausedTs ≠ 0 →
    s.executed <+: s.log1 →
    c.priorityTree.sides ≠ []
    ∧ s.d1.tree.isHistoricalRoot (lastSide c.priorityTree) = true
    ∧ (s.d1.tree.l1Reinit c.priorityTree).isSome = true
    ∧ (mintBatches s.d1.batches c).isSome = true
    ∧ ∃ s', step P s .l1Mint = some s' ∧ s'.phase = .back
      ∧ s'.d1.tree.unprocessedIndex = s.executed.length
      ∧ s'.executed = s'.log1.take s'.d1.tree.unprocessedIndex

/-- **WHAT THE RETURN'S ROOT CHECK COMPARES.** In every consistent reachable state where the
gateway burn's message is in flight: the commitment's root is the root of the tree whose leaves
are the processed operations; and the L1 mint's historical-root check passes exactly when some
prefix of the L1 leaves has that same root. -/
def Properties.ReturnRootCheckIffRootMatch : Prop :=
  ∀ (P : Params) (s : St) (c : ChainCommitment), Reach P ConsistentProcessing s →
    s.phase = .toL1 c →
    rootAfter P.tree s.executed = some (lastSide c.priorityTree)
    ∧ (s.d1.tree.isHistoricalRoot (lastSide c.priorityTree) = true ↔
        ∃ p, p <+: s.log1 ∧ rootAfter P.tree p = rootAfter P.tree s.executed)

/-- **A BROKEN MIRROR RETURNS ONLY THROUGH A ROOT COLLISION.** In every consistent reachable
state where the gateway burn's message is in flight and the processed operations are not a
prefix of the L1 leaves, if the L1 mint's historical-root check passes then a prefix of the L1
leaves different from the processed sequence has the same tree root. -/
def Properties.BrokenReturnNeedsRootCollision : Prop :=
  ∀ (P : Params) (s : St) (c : ChainCommitment), Reach P ConsistentProcessing s →
    s.phase = .toL1 c → ¬ s.executed <+: s.log1 →
    s.d1.tree.isHistoricalRoot (lastSide c.priorityTree) = true →
    ∃ p, p <+: s.log1 ∧ p ≠ s.executed ∧ rootAfter P.tree p = rootAfter P.tree s.executed

/-- **A DIVERGENCE IS PERMANENT.** If, in a consistent reachable state, the processed operations
are not a prefix of the L1 leaves, then in every state consistently reachable from it they are
not either. -/
def Properties.ExecutedDivergencePermanent : Prop :=
  ∀ (P : Params) (s s' : St), Reach P ConsistentProcessing s →
    Steps P ConsistentProcessing s s' → ¬ s.executed <+: s.log1 → ¬ s'.executed <+: s'.log1

/-- **COUNTERMODEL: FREEZING THE GATEWAY COPY WHILE L1 IS OPEN DROPS AN OPERATION.** With the
witness constants (`wParams`), in a consistent run: the gateway copy is frozen with relay `2`
pending; the relay executes and is dropped; ops `1` and `3` were relayed and processed on the
gateway, so `3` sits at the index of `2`; after the gateway burn the processed sequence
`[11, 1, 3]` is not a prefix of the L1 leaves `[11, 1, 2, 3]`. With a nonzero L1 pause timestamp,
`l1Reinit` and the batch checks would pass, but the commitment's root is not historical in the L1
tree and the L1 mint step reverts. `ConsistentProcessing` bounds only the count, so the gateway step
that processes op `3` at gateway index `2` is not shown to be realizable on L2: read it as the
gateway copy advancing over op `3`. If the L2 refused op `3` at index `2`, the gateway copy could
not reach `getSize = 0`, the gateway burn would be blocked, and op `2` would still never execute
on either copy. -/
def Properties.DroppedRelayCountermodel : Prop :=
  ∃ (s₀ s₁ s : St) (d : ChainDiamond) (c : ChainCommitment),
    Reach wParams ConsistentProcessing s₀
    ∧ s₀.d2 = some d ∧ d.frozen = true ∧ s₀.relays = [2]
    ∧ step wParams s₀ .relay = some s₁ ∧ s₁.dropped = [2]
    ∧ Steps wParams ConsistentProcessing s₁ s
    ∧ s.phase = .toL1 c
    ∧ s.log1 = [11, 1, 2, 3] ∧ s.leaves2 = [11, 1, 3] ∧ s.executed = [11, 1, 3]
    ∧ ¬ s.executed <+: s.log1
    ∧ s.d1.pausedTs ≠ 0
    ∧ s.d1.tree.isHistoricalRoot (lastSide c.priorityTree) = false
    ∧ (s.d1.tree.l1Reinit c.priorityTree).isSome = true
    ∧ (mintBatches s.d1.batches c).isSome = true
    ∧ step wParams s .l1Mint = none

/-! ## At this commit -/

/-- **WITH MIGRATIONS DISABLED NOTHING LEAVES L1.** With `CHAIN_MIGRATIONS_ENABLED = false`, in
every reachable state the chain settles on L1 with no migration in progress, no gateway copy and
no queued relay. -/
def Properties.MigrationsDisabledKeepL1Settling : Prop :=
  ∀ (P : Params) (s : St), P.migrationsEnabled = false → Reach P Unrestricted s →
    s.phase = .onL1 ∧ s.d1.settling = true ∧ s.inProgress = false ∧ s.d2 = none
    ∧ s.relays = []

/-! ## Witnesses -/

/-- **WITNESS FOR `InProgressIffInFlight`.** With `wParams`, a reachable state with the flag set
(the gateway transaction in flight) and a later one with it clear after a successful
confirmation. -/
def Properties.InProgressIffInFlightWitness : Prop :=
  ∃ s s' : St, Reach wParams Unrestricted s ∧ s.inProgress = true ∧ s.phase.InFlight
    ∧ Reach wParams Unrestricted s' ∧ s'.inProgress = false ∧ s'.phase = .onGW

/-- **WITNESS FOR `L1SnapshotFrozen`.** With `wParams`, a reachable state after a failed gateway
transaction, before confirmation: one operation was pushed and processed before the burn, and
the L1 copy was frozen during the window. -/
def Properties.L1SnapshotFrozenWitness : Prop :=
  ∃ (s : St) (pre : ChainDiamond), Reach wParams Unrestricted s ∧ s.phase.preBurn = some pre
    ∧ pre.tree.tree.nextLeafIndex = 1 ∧ pre.tree.unprocessedIndex = 1 ∧ pre.frozen = false
    ∧ s.d1.frozen = true

/-- **WITNESS FOR `FailureRestoresL1`.** With `wParams`, a successful failure confirmation from a
reachable state whose L1 tree holds one processed operation; afterwards the chain settles on L1
with that tree. -/
def Properties.FailureRestoresL1Witness : Prop :=
  ∃ s s' : St, Reach wParams Unrestricted s ∧ step wParams s (.confirm false) = some s'
    ∧ s.d1.pausedTs ≠ 0 ∧ s'.d1.settling = true ∧ s'.d1.tree.tree.nextLeafIndex = 1
    ∧ s'.d1.tree.unprocessedIndex = 1

/-- **WITNESS FOR `MirrorPrefix`.** With `wParams`, an honest run in which the gateway copy is
frozen while relay `1` is pending, and later the gateway burn's message is in flight with relay
`3` still pending: the gateway tree holds `[11, 1, 2]` and the L1 tree `[11, 1, 2, 3]`. -/
def Properties.MirrorPrefixWitness : Prop :=
  ∃ (s₀ s : St) (d : ChainDiamond), Reach wParams Honest s₀
    ∧ s₀.d2 = some d ∧ d.frozen = true ∧ s₀.relays = [1]
    ∧ Steps wParams Honest s₀ s ∧ s.phase.Mirrored
    ∧ s.leaves2 = [11, 1, 2] ∧ s.relays = [3] ∧ s.log1 = [11, 1, 2, 3]

/-- **WITNESS FOR `ExecutedIsL1Prefix`.** With `wParams`, an honest round trip ending with the
chain settling on L1 again: ops `1`, `2` were processed on the gateway (its unprocessed index is
`3`), op `4` was requested during the return window, all five L1 operations are processed, and
relay `4` was dropped on the frozen idle gateway copy after the L1 mint. -/
def Properties.ExecutedIsL1PrefixWitness : Prop :=
  ∃ (s : St) (d : ChainDiamond), Reach wParams Honest s ∧ s.phase = .back
    ∧ s.d1.settling = true ∧ s.d2 = some d ∧ d.tree.unprocessedIndex = 3
    ∧ s.executed = [11, 1, 2, 3, 4] ∧ s.log1 = [11, 1, 2, 3, 4]
    ∧ s.d1.tree.unprocessedIndex = 5 ∧ s.dropped = [4]

/-- **WITNESS FOR `ReturnMintChecksPass`.** With `wParams` (migrations enabled), an honest state
with the gateway burn's message in flight: L1 deposits were unpaused before the gateway burn, op `4`
was requested and relayed after it, and then deposits were paused again. The commitment carries
three processed operations, the L1 copy's unprocessed index is `1`, and the L1 tree holds five
leaves. -/
def Properties.ReturnMintChecksPassWitness : Prop :=
  ∃ (s : St) (c : ChainCommitment), Reach wParams Honest s ∧ s.phase = .toL1 c
    ∧ wParams.migrationsEnabled = true ∧ s.d1.pausedTs ≠ 0
    ∧ c.priorityTree.unprocessedIndex = 3 ∧ s.d1.tree.unprocessedIndex = 1
    ∧ s.log1.length = 5

/-- **WITNESS FOR `ReturnMintPassesOnPrefix`.** With `wParams`, a consistent run that breaks
FREEZE-ORDER: relay `2` was dropped on the frozen gateway copy, which then burned, so the gateway
burn's message is in flight with the processed operations `[11, 1]` a prefix of the L1 leaves
`[11, 1, 2]` and a nonzero L1 pause timestamp. Later, after the L1 mint, op `2` has been processed
on L1. -/
def Properties.ReturnMintPassesOnPrefixWitness : Prop :=
  ∃ (s s' : St) (c : ChainCommitment), Reach wParams ConsistentProcessing s ∧ s.phase = .toL1 c
    ∧ wParams.migrationsEnabled = true ∧ s.d1.pausedTs ≠ 0
    ∧ s.dropped = [2] ∧ s.executed = [11, 1] ∧ s.log1 = [11, 1, 2] ∧ s.executed <+: s.log1
    ∧ Steps wParams ConsistentProcessing s s' ∧ s'.phase = .back ∧ s'.executed = [11, 1, 2]

/-- **WITNESS FOR `ReturnRootCheckIffRootMatch`.** With `wParams`, two consistent states with the
gateway burn's message in flight: in the honest one the check passes, in the one with a dropped
relay it does not. -/
def Properties.ReturnRootCheckIffRootMatchWitness : Prop :=
  ∃ (s s' : St) (c c' : ChainCommitment),
    Reach wParams ConsistentProcessing s ∧ s.phase = .toL1 c
    ∧ s.d1.tree.isHistoricalRoot (lastSide c.priorityTree) = true
    ∧ Reach wParams ConsistentProcessing s' ∧ s'.phase = .toL1 c'
    ∧ s'.d1.tree.isHistoricalRoot (lastSide c'.priorityTree) = false

/-- **WITNESS FOR `BrokenReturnNeedsRootCollision`.** With the degenerate node hash of `cParams`
(every node hashes to `0`), the dropped-relay run: the processed sequence `[11, 1, 3]` is not a
prefix of the L1 leaves, the root check passes, and the L1 mint step succeeds with the L1
unprocessed index at `3`, where the L1 leaf is op `3`, already processed on the gateway, while op
`2` was never processed. -/
def Properties.BrokenReturnNeedsRootCollisionWitness : Prop :=
  ∃ (s s' : St) (c : ChainCommitment), Reach cParams ConsistentProcessing s ∧ s.phase = .toL1 c
    ∧ ¬ s.executed <+: s.log1
    ∧ s.d1.tree.isHistoricalRoot (lastSide c.priorityTree) = true
    ∧ s.executed = [11, 1, 3] ∧ s.log1 = [11, 1, 2, 3]
    ∧ step cParams s .l1Mint = some s' ∧ s'.d1.tree.unprocessedIndex = 3
    ∧ s'.log1.drop s'.d1.tree.unprocessedIndex = [3]

/-- **WITNESS FOR `ExecutedDivergencePermanent`.** With `wParams`, a consistent state where the
processed sequence `[11, 1, 3]` is not a prefix of the L1 leaves, and a later state, after the
gateway burn and a further L1 request, with one more L1 leaf. -/
def Properties.ExecutedDivergencePermanentWitness : Prop :=
  ∃ s s' : St, Reach wParams ConsistentProcessing s ∧ Steps wParams ConsistentProcessing s s'
    ∧ ¬ s.executed <+: s.log1 ∧ s.executed = [11, 1, 3]
    ∧ s.log1.length = 4 ∧ s'.log1.length = 5 ∧ s'.phase ≠ s.phase

/-- **WITNESS FOR `NoRelayDroppedBeforeReturn`.** With `wParams`: an honest reachable state in which
the gateway copy is frozen with relay `1` pending; a later honest state with the gateway burn's
message in flight, after relays `1` and `2` were pushed into the gateway tree; and, after the L1
mint, an honest state in which relay `4` was dropped on the frozen idle gateway copy, so the premise
that the L1 mint has not happened cannot be left out. -/
def Properties.NoRelayDroppedBeforeReturnWitness : Prop :=
  ∃ (s₀ s s' : St) (d : ChainDiamond) (c : ChainCommitment), Reach wParams Honest s₀
    ∧ s₀.d2 = some d ∧ d.frozen = true ∧ s₀.relays = [1]
    ∧ Steps wParams Honest s₀ s ∧ s.phase = .toL1 c ∧ s.leaves2 = [11, 1, 2]
    ∧ Steps wParams Honest s s' ∧ s'.phase = .back ∧ s'.dropped = [4]

/-- **WITNESS FOR `RelayDropsIffFrozen`.** With `wParams`, two consistent reachable states with the
chain settling on the gateway and one relay pending: in the first the gateway copy is not frozen and
the relay step pushes relay `1` into the gateway tree; in the second the gateway copy is frozen and
the relay step drops relay `2`. -/
def Properties.RelayDropsIffFrozenWitness : Prop :=
  ∃ (s₀ s₁ t₀ t₁ : St) (d₀ d₁ : ChainDiamond),
    Reach wParams ConsistentProcessing s₀ ∧ s₀.phase = .onGW ∧ s₀.relays = [1]
    ∧ s₀.d2 = some d₀ ∧ d₀.frozen = false
    ∧ step wParams s₀ .relay = some t₀ ∧ t₀.leaves2 = [11, 1] ∧ t₀.dropped = []
    ∧ Reach wParams ConsistentProcessing s₁ ∧ s₁.phase = .onGW ∧ s₁.relays = [2]
    ∧ s₁.d2 = some d₁ ∧ d₁.frozen = true
    ∧ step wParams s₁ .relay = some t₁ ∧ t₁.leaves2 = [11, 1] ∧ t₁.dropped = [2]

/-- **WITNESS FOR `MirrorIffNoDrop`.** With `wParams`, two reachable states with the chain settling
on the gateway. In the first nothing has been dropped, and the gateway leaves `[11]` followed by the
pending relay `1` are the L1 leaves. In the second relay `2` was dropped and op `3` relayed after
it: the gateway leaves are `[11, 1, 3]` and the L1 leaves `[11, 1, 2, 3]`. -/
def Properties.MirrorIffNoDropWitness : Prop :=
  ∃ s₀ s₁ : St, Reach wParams Unrestricted s₀ ∧ s₀.phase = .onGW ∧ s₀.dropped = []
    ∧ s₀.leaves2 = [11] ∧ s₀.relays = [1] ∧ s₀.log1 = [11, 1]
    ∧ Reach wParams Unrestricted s₁ ∧ s₁.phase = .onGW ∧ s₁.dropped = [2]
    ∧ s₁.leaves2 = [11, 1, 3] ∧ s₁.relays = [] ∧ s₁.log1 = [11, 1, 2, 3]

/-- **WITNESS FOR `MirrorBreakPermanent`.** With `wParams`, a reachable state just after relay `2`
was dropped, and a later state with the gateway burn's message in flight, after op `3` was
requested, relayed and processed on the gateway. -/
def Properties.MirrorBreakPermanentWitness : Prop :=
  ∃ (s s' : St) (c : ChainCommitment), Reach wParams Unrestricted s
    ∧ Steps wParams Unrestricted s s' ∧ s.dropped = [2] ∧ s.relays = [] ∧ s'.phase = .toL1 c
    ∧ s'.log1 = [11, 1, 2, 3] ∧ s'.leaves2 = [11, 1, 3]

/-- **WITNESS FOR `MigrationsDisabledKeepL1Settling`.** With `wParamsDisabled` (migrations
disabled, as at this commit), a reachable state where one operation was pushed and processed and
deposits are paused: every other modelled check of the L1 burn passes, and the burn reverts. -/
def Properties.MigrationsDisabledKeepL1SettlingWitness : Prop :=
  ∃ s : St, Reach wParamsDisabled Unrestricted s ∧ wParamsDisabled.migrationsEnabled = false
    ∧ s.log1 = [11] ∧ s.executed = [11] ∧ s.d1.tree.getSize = some 0
    ∧ inPausedWindow wParamsDisabled.migrationWindow s.d1.pausedTs s.now = true
    ∧ s.d1.batches.committed = s.d1.batches.executed ∧ (prepare s.d1).isSome = true
    ∧ step wParamsDisabled s .l1Burn = none

end Protocol.PriorityMirror
