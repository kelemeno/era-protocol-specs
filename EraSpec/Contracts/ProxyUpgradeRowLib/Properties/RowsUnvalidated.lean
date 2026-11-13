import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsUnvalidated

/-!
# Properties: rows that `validateRows` never checked (`e561b9cc2`)

Statements about `EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsUnvalidated`, which is the
`RowsCurrent` model plus `Transition.Genuine` and witness data. Proofs are in
`EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsUnvalidated`.

`applyTransition` applies whatever `rows()` the object it is handed returns
(`ProxyUpgradeRowLib.sol:102-113`). Only a genuine `ProxyUpgradeTransition` ran
`validateRows` on them (`objects/ProxyUpgradeTransition.sol:36`). `OnlyNamedEdgesAcrossCall`
and `ValidSourceIsNotApplied` (`Properties/RowsCurrent.lean`) take distinct proxies or
`ValidRows`, so they cover only genuine objects. This file states what holds for any row
list.

## Replay safety needs no validation

* `OnlyNamedEdgesAcrossCallAnyRows`: under `ReinitFrames` alone, a successful `applyRows`
  over any rows moves each proxy only from some row's `expectedOldImpl` to that row's
  `implNew`. The distinct-proxies premise of `OnlyNamedEdgesAcrossCall` is dropped.
* The row is the first one naming the proxy (`FirstRowCarriesTheEdge`). The verification
  pass (`:142-147`) requires `p`'s final implementation to be the target of every row naming
  `p`, so all of them have one target. Rows naming other proxies leave `p` alone, so the
  first row naming `p` finds it where the call started: at that target (no net move) or at
  the row's own source (a move along its edge). Later events, such as a reinitializer moving
  `p` or a later duplicate row moving it again, do not change where `p` ends.
* A later duplicate row need not start where the call started
  (`LaterDuplicateRowIsNotAnEdgeFromStart`). The proof of `OnlyNamedEdgesAcrossCall` used
  that per-row fact, which is why it needed distinct proxies.
* `OnlyNamedEdgesAcrossTransitionAnyRows` is the same for `applyTransition` on any object,
  which is the entry point of both domain executors (`CTMUpgradeExecutor.sol:64-67`,
  `CoreUpgradeExecutor.sol:33-36`).
* Of `validateRows`' checks, `ValidSourceIsNotApplied` needs only the row's own self-edge
  check (`SourceIsNotAppliedAnyRows`). `SelfEdgeAppliesWithoutMoving` shows that one is
  needed.

## What the duplicate check still buys

* The source's reason for a separate verification pass (`:119-120`): "a reinitializer that
  moves any proxy of the row set is caught too". For rows naming distinct proxies, and
  reinitializers that move at most their own proxy, it holds: in a successful call every
  row's iteration leaves the mapping exactly as a plain swap would, so no reinitializer
  moved anything (`ReinitMovesAreCaughtOnDistinctRows`). In any row list it holds for the
  last row naming each proxy (`ReinitMovesAreCaughtOnLastRow`).
* With a duplicate row it fails (`DuplicateRowHidesReinitMove`). `rowB`'s reinitializer moves
  its own proxy `6` from `12` on to `11`. On its own `rowB` reverts. Followed by a second row
  `6: 11 → 12`, the call succeeds. The net effect is still `rowB`'s edge, by the headline.
* A later duplicate row whose target is where the reinitializer left the proxy is skipped,
  so the first loop passes, and `applyRows` still reverts: the verification also checks the
  first row (`DetourThenSkipIsCaught`, an instance of `TwoTargetsForOneProxyRevert`).
* Executability can depend on the row order (`DuplicateRowsBreakOrder` in
  `Properties/RowsCurrent.lean`). The duplicate check does not remove that dependence on its
  own: on valid rows, a reinitializer that reads another row's proxy can still make one order
  revert (`ReinitReadBreaksOrder` in `Properties/RowsOrder.lean`).

## `ReinitFrames` stays

* `ReinitLeakMovesNamedProxyOffEdge`: the rows are valid, and `rowB`'s reinitializer moves
  proxy `5` to the source of `5`'s own later row. Proxy `5` goes `10 → 12`, although its only
  row is `11 → 12`, and the verification passes. `ReinitLeakIsNotCaught` showed this only for
  a proxy no row names. The same run refutes the source's sentence above once reinitializers
  may move other proxies.
-/

namespace Contracts.ProxyUpgradeCurrent

/-! ## Replay safety for any rows -/

/-- **ACROSS A CALL, A PROXY MOVES ONLY ALONG A ROW'S EDGE, FOR ANY ROWS.** For any row list,
including the `rows()` of an object that is not a genuine `ProxyUpgradeTransition` (rows on the
same proxy, self-edges, zero fields), and reinitializers that move at most their own proxy:
after a successful `applyRows`, every proxy is either where it was, or was at some row's
`expectedOldImpl` and is now at that row's `implNew`. This is `OnlyNamedEdgesAcrossCall`
without its distinct-proxies premise. -/
def Properties.OnlyNamedEdgesAcrossCallAnyRows : Prop :=
  ∀ (C : Config) (I J : Impl) (rows : List Row), ReinitFrames C → ApplyRows C I rows J →
    ∀ p, J p = I p ∨ ∃ r ∈ rows, r.proxy = p ∧ I p = r.expectedOldImpl ∧ J p = r.implNew

/-- **THE FIRST ROW NAMING A PROXY CARRIES ITS EDGE.** Split the rows as `pre ++ r :: post`
with no row of `pre` naming `r`'s proxy, so `r` is the first row naming it. Under
`ReinitFrames`, after a successful `applyRows` the proxy started at `r`'s target or at `r`'s
source, and ends at `r`'s target. Later rows on the same proxy need not start where the call
started (`LaterDuplicateRowIsNotAnEdgeFromStart`). -/
def Properties.FirstRowCarriesTheEdge : Prop :=
  ∀ (C : Config) (I J : Impl) (pre post : List Row) (r : Row), ReinitFrames C →
    ApplyRows C I (pre ++ r :: post) J → (∀ x ∈ pre, x.proxy ≠ r.proxy) →
    (I r.proxy = r.implNew ∨ I r.proxy = r.expectedOldImpl) ∧ J r.proxy = r.implNew

/-- **THE SAME FOR `applyTransition` ON ANY OBJECT.** A successful `applyTransition` of either
domain, on any object that is code and reports the domain, genuine or not, moves each proxy
only along an edge of one of the object's rows, provided reinitializers move at most their own
proxy. -/
def Properties.OnlyNamedEdgesAcrossTransitionAnyRows : Prop :=
  ∀ (C : Config) (d : Domain) (T : Transition) (I J : Impl), ReinitFrames C →
    ApplyTransition C d T I J →
    ∀ p, J p = I p ∨ ∃ r ∈ T.rows, r.proxy = p ∧ I p = r.expectedOldImpl ∧ J p = r.implNew

/-- **A ROW'S SOURCE STATE IS NOT ALREADY APPLIED, FOR ANY ROWS.** `ValidSourceIsNotApplied`
with `ValidRows` replaced by the one check it uses: the row itself is not a self-edge. If a
row's proxy is at that row's `expectedOldImpl`, the verification does not already hold, and
any successful `applyRows` moves that proxy. No premise on the other rows and no
`ReinitFrames`. -/
def Properties.SourceIsNotAppliedAnyRows : Prop :=
  ∀ (C : Config) (I J : Impl) (rows : List Row) (r : Row), r ∈ rows →
    r.expectedOldImpl ≠ r.implNew → I r.proxy = r.expectedOldImpl →
    ¬ RowsApplied I rows ∧ (ApplyRows C I rows J → J r.proxy ≠ I r.proxy)

/-! ## The source's reason for the separate verification pass -/

/-- **ON THE LAST ROW FOR ITS PROXY, A REINITIALIZER THAT MOVES ANYTHING IS CAUGHT.** In a
successful `applyRows`, take a row `r` such that no later row names `r`'s proxy, and the
state `K` the loop reached before `r`. Under `ReinitFrames`, the state `L` right after `r`'s
iteration is exactly `K` with `r`'s proxy at `r.implNew`, which is what a skip or a plain
`upgrade` leaves. So `r`'s reinitializer, if it ran, moved nothing. The premise on the later
rows is needed (`DuplicateRowHidesReinitMove`). -/
def Properties.ReinitMovesAreCaughtOnLastRow : Prop :=
  ∀ (C : Config) (I J K L : Impl) (pre post : List Row) (r : Row), ReinitFrames C →
    ApplyRows C I (pre ++ r :: post) J → ApplyLoop C I pre K → ApplyRow C K r L →
    (∀ x ∈ post, x.proxy ≠ r.proxy) → L = upd K r.proxy r.implNew

/-- **ON DISTINCT ROWS, A REINITIALIZER THAT MOVES ANYTHING IS CAUGHT.** The source says the
verification is a separate pass "so a reinitializer that moves any proxy of the row set is
caught too" (`ProxyUpgradeRowLib.sol:119-120`). For rows naming distinct proxies, as a genuine
object's rows do, and reinitializers that move at most their own proxy, this holds: every row
is the last for its proxy, so by `ReinitMovesAreCaughtOnLastRow` no reinitializer of a
successful call moved anything. -/
def Properties.ReinitMovesAreCaughtOnDistinctRows : Prop :=
  ∀ (C : Config) (I J K L : Impl) (pre post : List Row) (r : Row),
    (pre ++ r :: post).Pairwise (fun a b => a.proxy ≠ b.proxy) → ReinitFrames C →
    ApplyRows C I (pre ++ r :: post) J → ApplyLoop C I pre K → ApplyRow C K r L →
    L = upd K r.proxy r.implNew

/-! ## Countermodels -/

/-- **A LATER DUPLICATE ROW NEED NOT START WHERE THE CALL STARTED.** Rows `5: 10 → 11` then
`5: 12 → 11` name one proxy twice, with one target, so no genuine object carries them, and the
reinitializers are inert. `applyRows` succeeds from the state with every proxy at `10`. The
second row's proxy started at neither that row's source nor its target. So the per-row fact
"every row finds its proxy at its source or its target", which the proof of
`OnlyNamedEdgesAcrossCall` used, needs distinct proxies, and `FirstRowCarriesTheEdge` is about
the first row only. -/
def Properties.LaterDuplicateRowIsNotAnEdgeFromStart : Prop :=
  ReinitFrames wConfig ∧ ¬ [rowA, rowA3].Pairwise (fun a b => a.proxy ≠ b.proxy) ∧
    (∃ J, ApplyRows wConfig wImpl [rowA, rowA3] J) ∧
    ¬ ∀ r ∈ [rowA, rowA3], wImpl r.proxy = r.implNew ∨ wImpl r.proxy = r.expectedOldImpl

/-- **A DUPLICATE ROW HIDES A REINITIALIZER'S MOVE.** `rowB` is `6: 10 → 12` with a
reinitializer that moves its own proxy `6` on to `11`, so `ReinitFrames` holds. On its own
`rowB` is valid, and `applyRows` over it reverts: the move is caught. Followed by `rowB2`
(`6: 11 → 12`, valid on its own), the call succeeds; only a non-genuine object can carry the
pair. Yet `rowB`'s iteration did not leave proxy `6` at `rowB`'s target. So, with `pre = []`
and `post = [rowB2]`, the conclusion of `ReinitMovesAreCaughtOnLastRow` fails without its
premise on the later rows, and that of `ReinitMovesAreCaughtOnDistinctRows` without distinct
proxies. -/
def Properties.DuplicateRowHidesReinitMove : Prop :=
  ReinitFrames wDetour ∧ ValidRows [rowB] ∧ ValidRows [rowB2] ∧
    ¬ [rowB, rowB2].Pairwise (fun a b => a.proxy ≠ b.proxy) ∧
    (¬ ∃ J, ApplyRows wDetour wImpl [rowB] J) ∧
    (∃ J, ApplyRows wDetour wImpl [rowB, rowB2] J) ∧
    ∃ L, ApplyRow wDetour wImpl rowB L ∧ L rowB.proxy ≠ rowB.implNew

/-- **A DUPLICATE ROW THAT ACCEPTS THE MOVED PROXY IS CAUGHT.** The same reinitializer, now
followed by `rowB3` (`6: 10 → 11`, valid on its own), whose target is where the reinitializer
left proxy `6`. The first loop succeeds, because `rowB3` is skipped, and ends with proxy `6`
at `rowB3`'s target. `applyRows` reverts, because the verification also checks `rowB`
(`TwoTargetsForOneProxyRevert`). -/
def Properties.DetourThenSkipIsCaught : Prop :=
  ReinitFrames wDetour ∧ ValidRows [rowB3] ∧
    (∃ K, ApplyLoop wDetour wImpl [rowB, rowB3] K ∧ K rowB3.proxy = rowB3.implNew) ∧
    ¬ ∃ J, ApplyRows wDetour wImpl [rowB, rowB3] J

/-- **WITHOUT `ReinitFrames`, A NAMED PROXY CAN MOVE OFF EVERY EDGE.** Rows `6: 10 → 12`
(`rowB`, with a reinitializer) and `5: 11 → 12` (`rowA2`) are valid: in particular they name
distinct proxies. `rowB`'s reinitializer moves proxy `5` to `11`, so `ReinitFrames` fails.
From the state with every proxy at `10`, `applyRows` succeeds. Proxy `5`, which a row names,
went from `10` to `12` along no row's edge, so the conclusion of `OnlyNamedEdgesAcrossCall`
(and of its `AnyRows` form) fails at `5`. `rowB`'s iteration moved proxy `5`, a proxy of the
row set, and was not caught. `ReinitLeakIsNotCaught` shows the same only for a proxy no row
names. -/
def Properties.ReinitLeakMovesNamedProxyOffEdge : Prop :=
  ¬ ReinitFrames wLeakNamed ∧ ValidRows [rowB, rowA2] ∧
    (∃ L, ApplyRow wLeakNamed wImpl rowB L ∧ L rowA2.proxy ≠ wImpl rowA2.proxy) ∧
    ∃ J, ApplyRows wLeakNamed wImpl [rowB, rowA2] J ∧ rowA2 ∈ [rowB, rowA2] ∧
      rowA2.proxy = 5 ∧
      ¬ (J 5 = wImpl 5 ∨
        ∃ r ∈ [rowB, rowA2], r.proxy = 5 ∧ wImpl 5 = r.expectedOldImpl ∧ J 5 = r.implNew)

/-! ## Witnesses -/

/-- **THE PREMISES ARE MET BY A NON-GENUINE OBJECT.** `wDupTransition` is a CTM-domain object
whose rows name proxy `6` twice: `rowB` (`6: 10 → 12`, with a reinitializer), then `rowB2`
(`6: 11 → 12`). It is not a genuine `ProxyUpgradeTransition`, and `OnlyNamedEdgesAcrossCall`
does not apply to it. Under `wDetour`, whose reinitializers move at most their own proxy,
`applyTransition` on it succeeds from the state with every proxy at `10`. Proxy `6` really
moves, from `rowB`'s source to its target, which is the first row's edge, and every other
proxy stays. `rowB` is not a self-edge and its proxy starts at its source. So the premises
of `OnlyNamedEdgesAcrossCallAnyRows`, `OnlyNamedEdgesAcrossTransitionAnyRows`,
`SourceIsNotAppliedAnyRows` and `FirstRowCarriesTheEdge` (with `pre = []`, `r = rowB`,
`post = [rowB2]`) hold together, and the moving disjunct is the one that fires. -/
def Properties.AnyRowsWitness : Prop :=
  ReinitFrames wDetour ∧ ¬ wDupTransition.Genuine ∧
    ¬ wDupTransition.rows.Pairwise (fun a b => a.proxy ≠ b.proxy) ∧
    rowB ∈ wDupTransition.rows ∧ rowB.expectedOldImpl ≠ rowB.implNew ∧
    wImpl rowB.proxy = rowB.expectedOldImpl ∧
    ∃ J, ApplyTransition wDetour .ctm wDupTransition wImpl J ∧
      ApplyRows wDetour wImpl ([] ++ rowB :: [rowB2]) J ∧
      J rowB.proxy = rowB.implNew ∧ J rowB.proxy ≠ wImpl rowB.proxy ∧
      ∀ q, q ≠ rowB.proxy → J q = wImpl q

/-- **THE PREMISES OF `ReinitMovesAreCaughtOnDistinctRows` AND `ReinitMovesAreCaughtOnLastRow`
ARE MET.** Rows `5: 10 → 11` then `6: 10 → 12` (the latter with a reinitializer) name distinct
proxies, and the witness configuration's reinitializers move at most their own proxy.
`applyRows` succeeds, and the second row's iteration is a real swap: its proxy is not at the
target when the row runs, and its reinitializer runs. The last-row form also covers rows no
genuine object carries: in the duplicate pair `rowB`, `rowB2` under `wDetour`, `rowB2` is the
last row for proxy `6`, the call succeeds, and `rowB2`'s iteration is a real swap. -/
def Properties.ReinitMovesCaughtWitness : Prop :=
  ReinitFrames wConfig ∧ ([rowA] ++ rowB :: []).Pairwise (fun a b => a.proxy ≠ b.proxy) ∧
    rowB.callInitializeUpgrade = true ∧
    (∃ J K L, ApplyRows wConfig wImpl ([rowA] ++ rowB :: []) J ∧
      ApplyLoop wConfig wImpl [rowA] K ∧ ApplyRow wConfig K rowB L ∧ K rowB.proxy ≠ rowB.implNew) ∧
    ReinitFrames wDetour ∧ ¬ ([rowB] ++ rowB2 :: []).Pairwise (fun a b => a.proxy ≠ b.proxy) ∧
    ∃ J K L, ApplyRows wDetour wImpl ([rowB] ++ rowB2 :: []) J ∧
      ApplyLoop wDetour wImpl [rowB] K ∧ ApplyRow wDetour K rowB2 L ∧ K rowB2.proxy ≠ rowB2.implNew

end Contracts.ProxyUpgradeCurrent
