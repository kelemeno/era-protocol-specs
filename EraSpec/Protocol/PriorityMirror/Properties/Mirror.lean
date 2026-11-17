import EraSpec.Protocol.PriorityMirror.Specs.Mirror

/-!
# Properties: the gateway's priority tree mirrors L1's, and a migration out and back loses or
repeats no L1 priority operation

Statements about `EraSpec.Protocol.PriorityMirror.Specs.Mirror`. Proofs are in
`EraSpec.Protocol.PriorityMirror.Proofs.Mirror`. No statement has a hash premise.

Three kinds of run appear. `Unrestricted` runs have no premise. `ConsistentProcessing` runs only
process leaves a copy holds. `Honest` runs also respect FREEZE-ORDER: no relay for the chain
executes on the gateway while its gateway copy is frozen.

* The L1 copy during the move to the gateway (`InProgressIffInFlight`, `L1SnapshotFrozen`,
  `FailureRestoresL1`).
* **Mirror** (`MirrorPrefix`): in honest runs, from the gateway copy's creation until the L1
  mint, the gateway tree's leaves followed by the pending relays are exactly the L1 tree's
  leaves, and both trees' storage is the result of pushing those leaves from the setup state.
* **No operation lost or repeated** (`ExecutedIsL1Prefix`, headline): in honest runs, the
  operations processed by either copy, in processing order, are a prefix of the L1 tree's
  leaves; whenever the L1 copy settles they are exactly the leaves below its unprocessed index.
  `ReturnMintChecksPass`: the L1 mint's modelled checks pass once L1 deposits are paused.
* **Without FREEZE-ORDER** (`DroppedRelayCountermodel`): a relay executed while the gateway copy
  is frozen is dropped, the next operation takes its index on the gateway, the processed
  sequence stops being a prefix of the L1 leaves (`ExecutedDivergencePermanent`: for good), and
  the L1 mint reverts on its historical-root check. In every consistent run the check passes in
  that situation only through a root collision between two named leaf lists
  (`ReturnRootCheckIffRootMatch`, `BrokenReturnNeedsRootCollision`).
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
`isMigrationInProgress` is set, so `depositsPaused()` is true and every L1 request reverts; `pre`
settled with deposits paused; the L1 copy no longer settles; its priority tree, batch counters
and stored batch hashes, and pause timestamp are those of `pre`; no relay is queued. While the
gateway transaction is in flight it carries `prepareChainCommitment` of `pre`. -/
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
message is in flight, with migrations enabled and L1 deposits paused: the commitment has a root,
that root is historical in the L1 tree, `l1Reinit` and the batch checks pass, and the L1 mint
succeeds. It sets the L1 unprocessed index to the number of processed operations, which are then
the L1 leaves below it. -/
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
`[11, 1, 3]` is not a prefix of the L1 leaves `[11, 1, 2, 3]`. With L1 deposits paused, `l1Reinit`
and the batch checks would pass, but the commitment's root is not historical in the L1 tree and
the L1 mint reverts. -/
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
`3`), op `4` was requested during the return window, and all five L1 operations are processed. -/
def Properties.ExecutedIsL1PrefixWitness : Prop :=
  ∃ (s : St) (d : ChainDiamond), Reach wParams Honest s ∧ s.phase = .back
    ∧ s.d1.settling = true ∧ s.d2 = some d ∧ d.tree.unprocessedIndex = 3
    ∧ s.executed = [11, 1, 2, 3, 4] ∧ s.log1 = [11, 1, 2, 3, 4]
    ∧ s.d1.tree.unprocessedIndex = 5

/-- **WITNESS FOR `ReturnMintChecksPass`.** With `wParams` (migrations enabled), an honest state
with the gateway burn's message in flight and L1 deposits paused again after being unpaused in
the window: the commitment carries three processed operations, the L1 copy's unprocessed index is
`1`, and the L1 tree holds five leaves. -/
def Properties.ReturnMintChecksPassWitness : Prop :=
  ∃ (s : St) (c : ChainCommitment), Reach wParams Honest s ∧ s.phase = .toL1 c
    ∧ wParams.migrationsEnabled = true ∧ s.d1.pausedTs ≠ 0
    ∧ c.priorityTree.unprocessedIndex = 3 ∧ s.d1.tree.unprocessedIndex = 1
    ∧ s.log1.length = 5

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
prefix of the L1 leaves, the root check passes, and the L1 mint succeeds with the L1 unprocessed
index at `3`, where the L1 leaf is op `3`, already processed on the gateway, while op `2` was
never processed. -/
def Properties.BrokenReturnNeedsRootCollisionWitness : Prop :=
  ∃ (s s' : St) (c : ChainCommitment), Reach cParams ConsistentProcessing s ∧ s.phase = .toL1 c
    ∧ ¬ s.executed <+: s.log1
    ∧ s.d1.tree.isHistoricalRoot (lastSide c.priorityTree) = true
    ∧ s.executed = [11, 1, 3] ∧ s.log1 = [11, 1, 2, 3]
    ∧ step cParams s .l1Mint = some s' ∧ s'.d1.tree.unprocessedIndex = 3
    ∧ s'.log1.drop s'.d1.tree.unprocessedIndex = [3]

/-- **WITNESS FOR `ExecutedDivergencePermanent`.** With `wParams`, a consistent state where the
processed sequence `[11, 1, 3]` is not a prefix of the L1 leaves, and a later state, after the
gateway burn and further L1 requests, with more L1 leaves. -/
def Properties.ExecutedDivergencePermanentWitness : Prop :=
  ∃ s s' : St, Reach wParams ConsistentProcessing s ∧ Steps wParams ConsistentProcessing s s'
    ∧ ¬ s.executed <+: s.log1 ∧ s.executed = [11, 1, 3]
    ∧ s.log1.length = 4 ∧ s'.log1.length = 5 ∧ s'.phase ≠ s.phase

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
