import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsAdminSlot
import EraSpec.Core.Headline

/-!
# Properties: the rows at `b17415d20`, read through the proxies' admin dispatch

Statements about `EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsAdminSlot`, which models
each proxy's ERC-1967 implementation and admin slots, the OpenZeppelin v4.9.6 transparent
proxy's admin dispatch, and a reinitializer that can write both slots of its proxy. Proofs are
in `EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsAdminSlot`.

`Specs/RowsCurrent.lean` reads `_admin.getProxyImplementation(proxy)` as the implementation the
proxy runs. In this model the read is the implementation slot while the proxy's admin slot
holds `_admin`, and a reinitializer, which runs in its proxy's storage, can change the admin
slot.

## `RowsCurrent` is a fragment of this model

* `LiftedCallIsRowsCurrentCall`: lifted with `_admin` administering every proxy, every
  `RowsCurrent` configuration has exactly its `RowsCurrent` calls, on the implementation slots,
  with every admin slot kept. No premise. `RowsCurrentIsTheKeepsAdminFragment` relates the
  premises of the two models.
* `ApplyRowsCorrespond`: under `SelfOnly`, `KeepsAdmin` and `Administered`, a call of this
  model is exactly a `RowsCurrent` call of its projection on the implementation slots, with
  every admin slot kept.
* The `RowsCurrent` headlines restated on the slots under these three premises:
  `ApplyRowsPostconditionOnSlots`, `OnlyNamedEdgesAcrossCallOnSlots`,
  `OnlyNamedEdgesAcrossTransitionOnSlots`, `ReinitMovesAreCaughtOnLastRowOnSlots`,
  `ReinitMovesAreCaughtOnDistinctRowsOnSlots`, `OrderIndependentOnSlots`. Witness:
  `AdminSlotWitness`.

## Each of the three premises is needed

* `KeepsAdmin`: `AdminRewritePassesVerification`. On valid rows, a reinitializer that writes
  only its own proxy's two slots (`SelfOnly`) points the admin slot away from `_admin` and the
  implementation slot at code whose forwarded `implementation()` returns the row's target. The
  `RowsCurrent` projection of the call reverts. In this model the call succeeds, and the
  proxy's implementation slot ends on no row's edge. `AdminRewriteMakesOrderMatter` and
  `MoveBackWithAdminRewriteIsNotCaught` are two more runs of this kind.
* `Administered`: `UnadministeredRowSkippedWhileOffTarget`, with inert reinitializers.
* `SelfOnly`: `SelfOnlyIsNeededOnSlots`, which is `ReinitLeakIsNotCaught` run on the slots.

## What holds without `KeepsAdmin`

* `AdministeredRowRunsItsTarget`: with no premise, a row's proxy whose admin slot holds `_admin`
  when the call returns has its implementation slot at the row's target.
* `AdminLostOnlyByOwnReinitializer`: under `SelfOnly`, a proxy's admin slot stops holding
  `_admin` during a call only if a row naming that proxy calls `initializeUpgrade()`.
* `OnlyNamedEdgesOrAdminLost` and `ReinitMovesAreCaughtOrAdminLost`: the `RowsCurrent`
  conclusions on the slots, or the proxy's admin slot no longer holds `_admin`.
* `SourceIsNotAppliedOnSlots`: from a row's source, a successful call changes that proxy's
  slots.
* `AdminSlotCasesWitness`: one run that meets the premises of these statements, in which every
  case of their conclusions occurs.
-/

namespace Contracts.ProxyUpgradeCurrent.AdminSlot

/-! ## Each premise is needed -/

/-- **A REINITIALIZER THAT REWRITES ITS OWN PROXY'S ADMIN SLOT PASSES THE VERIFICATION OFF
EVERY EDGE.** The rows are `5: 10 → 11` and `6: 10 → 12` (`rowA`, `rowB`), and they are valid.
`_admin` administers every proxy, and every proxy's implementation slot holds `10`. `rowB`'s
reinitializer writes only its own proxy `6` (`SelfOnly`), so its projection to the
implementation slots meets `RowsCurrent`'s `ReinitFrames`, and it does not keep the admin slot
(`KeepsAdmin` fails). It points proxy `6`'s admin slot at `66` and its implementation slot at
`99`, and a proxy running `99` answers a forwarded `implementation()` with `12`.

The `RowsCurrent` call of the projection on the implementation slots reverts. In this model the
call succeeds, directly and as a CTM-domain `ApplyTransition` (the leg's object checks followed
by the default engine's `applyRows`), because the verification read of
proxy `6` is the forwarded answer. Afterwards proxy `6`'s implementation slot holds `99`: not its
row's target, and `10 → 99` is on no row's edge. Its admin slot no longer holds `_admin`, and
`rowB`'s iteration did not leave the implementation slots as a plain swap would.

So, on the implementation slots of this model, the conclusions of `ApplyRowsPostcondition`,
`OnlyNamedEdgesAcrossCall` (and its `AnyRows` and transition forms), `FirstRowCarriesTheEdge`,
`ReinitMovesAreCaughtOnLastRow` and `ReinitMovesAreCaughtOnDistinctRows` fail for a successful
call whose configuration projects to one meeting `ReinitFrames`. The `RowsCurrent` theorems are
not contradicted: in `RowsCurrent` this call reverts. The `...OnSlots` forms add `KeepsAdmin`.
Proxy `6` is in the third case of `OnlyNamedEdgesOrAdminLost`. -/
@[countermodel] def Properties.AdminRewritePassesVerification : Prop :=
  SelfOnly wAdminRewrite ∧ ProxyUpgradeCurrent.ReinitFrames (wAdminRewrite.project wSlots.admin) ∧
    ¬ KeepsAdmin wAdminRewrite ∧ ValidRows [rowA, rowB] ∧
    Administered wAdminRewrite wSlots [rowA, rowB] ∧
    (¬ ∃ I, ProxyUpgradeCurrent.ApplyRows (wAdminRewrite.project wSlots.admin) wSlots.impl
      [rowA, rowB] I) ∧
    ∃ J, ApplyRows wAdminRewrite wSlots [rowA, rowB] J ∧
      ApplyTransition wAdminRewrite .ctm ⟨3, .ctm, [rowA, rowB]⟩ wSlots J ∧
      read wAdminRewrite J rowB.proxy = some rowB.implNew ∧
      J.impl rowB.proxy ≠ rowB.implNew ∧ J.admin rowB.proxy ≠ wAdminRewrite.proxyAdmin ∧
      ¬ (J.impl 6 = wSlots.impl 6 ∨
        ∃ r ∈ [rowA, rowB], r.proxy = 6 ∧ wSlots.impl 6 = r.expectedOldImpl ∧ J.impl 6 = r.implNew) ∧
      ∃ K L, ApplyLoop wAdminRewrite wSlots [rowA] K ∧ ApplyRow wAdminRewrite K rowB L ∧
        L.impl ≠ upd K.impl rowB.proxy rowB.implNew

/-- **SUCH A REINITIALIZER CAN MAKE THE ORDER DECIDE A ROW PROXY'S IMPLEMENTATION.** `rowB`'s
reinitializer writes only proxy `6`. It points the admin slot at `66` and the implementation
slot at `98` if proxy `5`'s implementation slot holds `11` when it runs, and at `99` otherwise.
A proxy running `98` or `99` answers a forwarded `implementation()` with `12`. The projection
meets `ReinitFrames`, and the rows are valid. In `RowsCurrent` both orders of the projected call
revert. In this model both orders succeed, and proxy `6`, which a row names, ends with
different implementation slots. So, on the implementation slots of this model, the conclusions
of `OrderIndependent` (premise `ReinitFrames`) and `OrderIndependentOnRowProxies` (no premise
beyond two successful calls) fail. `OrderIndependentOnSlots` adds `KeepsAdmin`. -/
def Properties.AdminRewriteMakesOrderMatter : Prop :=
  SelfOnly wAdminRewriteOrder ∧
    ProxyUpgradeCurrent.ReinitFrames (wAdminRewriteOrder.project wSlots.admin) ∧
    ValidRows [rowA, rowB] ∧ Administered wAdminRewriteOrder wSlots [rowA, rowB] ∧
    (¬ ∃ I, ProxyUpgradeCurrent.ApplyRows (wAdminRewriteOrder.project wSlots.admin) wSlots.impl
      [rowA, rowB] I) ∧
    (¬ ∃ I, ProxyUpgradeCurrent.ApplyRows (wAdminRewriteOrder.project wSlots.admin) wSlots.impl
      [rowB, rowA] I) ∧
    ∃ J K, ApplyRows wAdminRewriteOrder wSlots [rowA, rowB] J ∧
      ApplyRows wAdminRewriteOrder wSlots [rowB, rowA] K ∧ rowB ∈ [rowA, rowB] ∧
      J.impl rowB.proxy ≠ K.impl rowB.proxy

/-- **A REINITIALIZER THAT MOVES ITS PROXY BACK AND REWRITES THE ADMIN SLOT IS NOT CAUGHT.** On
the implementation slots, `wAdminRewriteBack` projects to `wSelfMoving`: `rowB`'s reinitializer
moves its own proxy `6` back to `10`, and in `RowsCurrent` the call reverts
(`ReinitMovingOwnProxyIsCaught`). This reinitializer also points proxy `6`'s admin slot at `66`,
and a proxy running `10` answers a forwarded `implementation()` with `12`. In this model
`applyRows` over the same valid rows succeeds. Proxy `6` started at `rowB`'s source, and its
implementation slot ends there; only its admin slot moved. So, on the implementation slot, a
successful call from a row's source need not move the proxy (compare `ValidSourceIsNotApplied`
and `SourceIsNotAppliedOnSlots`). -/
def Properties.MoveBackWithAdminRewriteIsNotCaught : Prop :=
  SelfOnly wAdminRewriteBack ∧ wAdminRewriteBack.project wSlots.admin = wSelfMoving ∧
    ValidRows [rowA, rowB] ∧ Administered wAdminRewriteBack wSlots [rowA, rowB] ∧
    (¬ ∃ I, ProxyUpgradeCurrent.ApplyRows wSelfMoving wSlots.impl [rowA, rowB] I) ∧
    wSlots.impl rowB.proxy = rowB.expectedOldImpl ∧
    ∃ J, ApplyRows wAdminRewriteBack wSlots [rowA, rowB] J ∧
      J.impl rowB.proxy = wSlots.impl rowB.proxy ∧ J.admin rowB.proxy ≠ wSlots.admin rowB.proxy

/-- **`Administered` IS NEEDED: A ROW WHOSE PROXY `_admin` DOES NOT ADMINISTER IS SKIPPED WHILE
OFF ITS TARGET.** The reinitializers are inert, so `SelfOnly` and `KeepsAdmin` hold. Proxy `6`
is administered by `66`, not `_admin`, and its implementation slot holds `99`; a proxy running
`99` answers a forwarded `implementation()` with `12`. `applyRows [rowB]` reads `12`, takes the
skip, passes the verification and changes nothing, and proxy `6`'s implementation slot is not
`rowB`'s target. `Specs/RowsCurrent.lean:66-69` leaves this configuration out of that model. -/
@[countermodel] def Properties.UnadministeredRowSkippedWhileOffTarget : Prop :=
  SelfOnly wForeignAnswers ∧ KeepsAdmin wForeignAnswers ∧ ValidRows [rowB] ∧
    ¬ Administered wForeignAnswers wSlotsForeign6 [rowB] ∧
    ApplyRows wForeignAnswers wSlotsForeign6 [rowB] wSlotsForeign6 ∧
    wSlotsForeign6.impl rowB.proxy ≠ rowB.implNew

/-- **`SelfOnly` IS NEEDED.** `wKeepAdminLeaky` (`wLeaky` lifted) keeps every admin slot, so
`KeepsAdmin` holds, and `_admin` administers every proxy of `wSlots`. `rowB`'s reinitializer
also sets proxy `7`'s implementation slot to `99`, so `SelfOnly` fails. The valid rows `rowA`,
`rowB` apply, no admin slot changes, and proxy `7`, which no row names, ends with its
implementation slot moved, so the conclusion of `OnlyNamedEdgesAcrossCallOnSlots` fails at `7`.
This is `ReinitLeakIsNotCaught` (`Properties/RowsCurrent.lean`) run on the slots. -/
def Properties.SelfOnlyIsNeededOnSlots : Prop :=
  ¬ SelfOnly wKeepAdminLeaky ∧ KeepsAdmin wKeepAdminLeaky ∧ ValidRows [rowA, rowB] ∧
    Administered wKeepAdminLeaky wSlots [rowA, rowB] ∧
    ∃ J, ApplyRows wKeepAdminLeaky wSlots [rowA, rowB] J ∧ J.admin = wSlots.admin ∧
      (∀ r ∈ [rowA, rowB], r.proxy ≠ 7) ∧ J.impl 7 ≠ wSlots.impl 7

/-! ## What holds without `KeepsAdmin` -/

/-- **WHAT THE VERIFICATION ESTABLISHES ON THE SLOTS.** After a successful `applyRows`, a row's
proxy whose admin slot holds `_admin` when the call returns has its implementation slot at that
row's `implNew`. No premise. For a proxy whose admin slot does not hold `_admin`, the
verification read was the forwarded answer, and the implementation slot can be elsewhere
(`AdminRewritePassesVerification`). -/
def Properties.AdministeredRowRunsItsTarget : Prop :=
  ∀ (C : Config) (S J : Slots) (rows : List Row), ApplyRows C S rows J →
    ∀ r ∈ rows, J.admin r.proxy = C.proxyAdmin → J.impl r.proxy = r.implNew

/-- **ONLY THE REINITIALIZER OF A ROW NAMING A PROXY CAN TAKE IT FROM `_admin`.** Under
`SelfOnly`: if `p`'s admin slot holds `_admin` when the call starts and does not when it
returns, some row naming `p` calls `initializeUpgrade()`. A skip and a plain swap leave the
admin slot alone, a forwarded swap needs the admin slot to have stopped holding `_admin`
already, and under `SelfOnly` nothing else writes `p`'s slots. -/
def Properties.AdminLostOnlyByOwnReinitializer : Prop :=
  ∀ (C : Config) (S J : Slots) (rows : List Row) (p : Address), SelfOnly C →
    ApplyRows C S rows J → S.admin p = C.proxyAdmin → J.admin p ≠ C.proxyAdmin →
    ∃ r ∈ rows, r.proxy = p ∧ r.callInitializeUpgrade = true

/-- **A PROXY MOVES ONLY ALONG A ROW'S EDGE, OR `_admin` HAS LOST IT.** For any rows, under
`SelfOnly` and `Administered`, after a successful `applyRows` each proxy is in one of three
cases. Both of its slots are as they were. Or its implementation slot was at some row's
`expectedOldImpl` and is now at that row's `implNew`, and its admin slot is as it was. Or its
admin slot no longer holds `_admin`, and some row naming it calls `initializeUpgrade()`. This
is `OnlyNamedEdgesAcrossCallAnyRows` on the slots with the third case added. All three cases
occur in one run (`AdminSlotCasesWitness`); with `KeepsAdmin` the third does not
(`OnlyNamedEdgesAcrossCallOnSlots`). -/
def Properties.OnlyNamedEdgesOrAdminLost : Prop :=
  ∀ (C : Config) (S J : Slots) (rows : List Row), SelfOnly C → Administered C S rows →
    ApplyRows C S rows J → ∀ p,
      (J.impl p = S.impl p ∧ J.admin p = S.admin p) ∨
      (∃ r ∈ rows, r.proxy = p ∧ S.impl p = r.expectedOldImpl ∧ J.impl p = r.implNew ∧
        J.admin p = S.admin p) ∨
      (J.admin p ≠ C.proxyAdmin ∧ ∃ r ∈ rows, r.proxy = p ∧ r.callInitializeUpgrade = true)

/-- **ON DISTINCT ROWS, A ROW'S ITERATION IS A PLAIN SWAP, OR `_admin` HAS LOST ITS PROXY.**
Take rows naming distinct proxies, as a genuine object's are, with `SelfOnly` and
`Administered`. Take a successful `applyRows`, a row `r`, the state `K` before `r`'s iteration
and the state `L` after it. Then `L` is `K` with `r`'s proxy's implementation slot at
`r.implNew`, which is what a skip or a plain `upgrade` leaves, or `r`'s proxy's admin slot does
not hold `_admin` when the call returns. This is `ReinitMovesAreCaughtOnDistinctRows` on the
slots with the second case added. Both cases occur (`AdminSlotCasesWitness`,
`AdminRewritePassesVerification`). -/
def Properties.ReinitMovesAreCaughtOrAdminLost : Prop :=
  ∀ (C : Config) (S J K L : Slots) (pre post : List Row) (r : Row),
    (pre ++ r :: post).Pairwise (fun a b => a.proxy ≠ b.proxy) → SelfOnly C →
    Administered C S (pre ++ r :: post) → ApplyRows C S (pre ++ r :: post) J →
    ApplyLoop C S pre K → ApplyRow C K r L →
    L = K.setImpl r.proxy r.implNew ∨ J.admin r.proxy ≠ C.proxyAdmin

/-- **FROM A ROW'S SOURCE, A SUCCESSFUL CALL CHANGES THAT PROXY'S SLOTS.**
`SourceIsNotAppliedAnyRows` on the slots. The row is not a self-edge, its proxy's admin slot
holds `_admin`, and its implementation slot holds the row's `expectedOldImpl`. Then the
verification does not already hold. After any successful `applyRows`, either the admin slot
still holds `_admin` and the implementation slot moved, or the admin slot no longer holds
`_admin`. No premise on the other rows and no `SelfOnly`. Both cases occur
(`AdminSlotCasesWitness`). The implementation slot alone need not move
(`MoveBackWithAdminRewriteIsNotCaught`). -/
def Properties.SourceIsNotAppliedOnSlots : Prop :=
  ∀ (C : Config) (S J : Slots) (rows : List Row) (r : Row), r ∈ rows →
    r.expectedOldImpl ≠ r.implNew → S.admin r.proxy = C.proxyAdmin →
    S.impl r.proxy = r.expectedOldImpl →
    ¬ RowsRead C S rows ∧
      (ApplyRows C S rows J →
        (J.admin r.proxy = C.proxyAdmin ∧ J.impl r.proxy ≠ S.impl r.proxy) ∨
          J.admin r.proxy ≠ C.proxyAdmin)

/-! ## `RowsCurrent` as a fragment, and the transfer under `KeepsAdmin` -/

/-- **`SelfOnly` IS THE SLOT READING OF `ReinitFrames`.** Every projection of a `SelfOnly`
configuration to a fixed admin mapping meets `RowsCurrent`'s `ReinitFrames`. -/
def Properties.SelfOnlyProjectsToReinitFrames : Prop :=
  ∀ (C : Config) (A : Address → Address), SelfOnly C → ProxyUpgradeCurrent.ReinitFrames (C.project A)

/-- **THE LIFT MEETS `KeepsAdmin`, AND `SelfOnly` EXACTLY UNDER `ReinitFrames`.** Every
`RowsCurrent` configuration `C0`, lifted with `_admin` at any `a`, meets `KeepsAdmin`. It meets
`SelfOnly` exactly when `C0` meets `ReinitFrames`, and it projects back to `C0` at every admin
mapping. `LiftedCallIsRowsCurrentCall` relates their calls. -/
def Properties.RowsCurrentIsTheKeepsAdminFragment : Prop :=
  ∀ (C0 : ProxyUpgradeCurrent.Config) (a : Address) (A : Address → Address),
    KeepsAdmin (lift C0 a) ∧ (SelfOnly (lift C0 a) ↔ ProxyUpgradeCurrent.ReinitFrames C0) ∧
      (lift C0 a).project A = C0

/-- **EVERY `RowsCurrent` CALL IS A CALL OF ITS LIFT, AND CONVERSELY.** For any `RowsCurrent`
configuration `C0`, whether or not it meets `ReinitFrames`, and any address `a` for `_admin`:
from the slots whose implementation slots are `I` and whose admin slots all hold `a`,
`applyRows` of `lift C0 a` ends in `J` exactly when `RowsCurrent`'s `applyRows` of `C0` from `I`
ends in `J`'s implementation slots and `J`'s admin slots all still hold `a`. -/
def Properties.LiftedCallIsRowsCurrentCall : Prop :=
  ∀ (C0 : ProxyUpgradeCurrent.Config) (a : Address) (I : Impl) (rows : List Row) (J : Slots),
    ApplyRows (lift C0 a) ⟨I, fun _ => a⟩ rows J ↔
      ProxyUpgradeCurrent.ApplyRows C0 I rows J.impl ∧ J.admin = fun _ => a

/-- **UNDER `KeepsAdmin` THE CALL IS THE `RowsCurrent` CALL.** Take a configuration meeting
`SelfOnly` and `KeepsAdmin`, and a starting state in which `_admin` administers every row's
proxy. Then a successful `applyRows` ending in `J` is exactly a successful `RowsCurrent`
`applyRows` of the projection at the starting admin slots, from the starting implementation
slots, ending in `J`'s implementation slots, with every admin slot of `J` as it was. So a
`RowsCurrent` statement about the calls of that projection is a statement about the
implementation slots under these premises. -/
def Properties.ApplyRowsCorrespond : Prop :=
  ∀ (C : Config) (S J : Slots) (rows : List Row), SelfOnly C → KeepsAdmin C →
    Administered C S rows →
    (ApplyRows C S rows J ↔
      ProxyUpgradeCurrent.ApplyRows (C.project S.admin) S.impl rows J.impl ∧ J.admin = S.admin)

/-- **`ApplyRowsPostcondition` ON THE SLOTS.** Under `SelfOnly`, `KeepsAdmin` and
`Administered`, after a successful `applyRows` every row's proxy runs its `implNew` and is
still administered by `_admin`. Without `KeepsAdmin` this fails
(`AdminRewritePassesVerification`), and without `Administered` too
(`UnadministeredRowSkippedWhileOffTarget`). -/
def Properties.ApplyRowsPostconditionOnSlots : Prop :=
  ∀ (C : Config) (S J : Slots) (rows : List Row), SelfOnly C → KeepsAdmin C →
    Administered C S rows → ApplyRows C S rows J →
    ∀ r ∈ rows, J.impl r.proxy = r.implNew ∧ J.admin r.proxy = C.proxyAdmin

/-- **`OnlyNamedEdgesAcrossCallAnyRows` ON THE SLOTS.** For any rows, under `SelfOnly`,
`KeepsAdmin` and `Administered`: after a successful `applyRows` no admin slot has changed, and
every proxy's implementation slot is where it was, or was at some row's `expectedOldImpl` and
is now at that row's `implNew`. Without `SelfOnly` this fails (`SelfOnlyIsNeededOnSlots`). -/
@[headline] def Properties.OnlyNamedEdgesAcrossCallOnSlots : Prop :=
  ∀ (C : Config) (S J : Slots) (rows : List Row), SelfOnly C → KeepsAdmin C →
    Administered C S rows → ApplyRows C S rows J → J.admin = S.admin ∧
      ∀ p, J.impl p = S.impl p ∨
        ∃ r ∈ rows, r.proxy = p ∧ S.impl p = r.expectedOldImpl ∧ J.impl p = r.implNew

/-- **`OnlyNamedEdgesAcrossTransitionAnyRows` ON THE SLOTS.** The same for `ApplyTransition`
(the leg's object checks and the default engine's `applyRows`) on any object that is code,
reports the domain and whose manifest pins `DefaultProxyUpgradeEngine` (empty hooks at
`b17415d20`, `engines/DefaultProxyUpgradeEngine.sol:51-65`). A leg with any other engine runs
arbitrary code, bounded only by the executor's post-checks (`../ProxyUpgradeExecutorBase/`:
`DomainHoldersV35`, `EngineLegV35`). `Administered` is about the object's rows. -/
def Properties.OnlyNamedEdgesAcrossTransitionOnSlots : Prop :=
  ∀ (C : Config) (d : Domain) (T : Transition) (S J : Slots), SelfOnly C → KeepsAdmin C →
    Administered C S T.rows → ApplyTransition C d T S J → J.admin = S.admin ∧
      ∀ p, J.impl p = S.impl p ∨
        ∃ r ∈ T.rows, r.proxy = p ∧ S.impl p = r.expectedOldImpl ∧ J.impl p = r.implNew

/-- **`ReinitMovesAreCaughtOnLastRow` ON THE SLOTS.** Under `SelfOnly`, `KeepsAdmin` and
`Administered`, in a successful `applyRows`, take a row `r` that no later row's proxy
repeats. The state `L` right after `r`'s iteration is the state `K` before it, with `r`'s
proxy's implementation slot at `r.implNew`. So `r`'s reinitializer, if it ran, changed no
slot. -/
def Properties.ReinitMovesAreCaughtOnLastRowOnSlots : Prop :=
  ∀ (C : Config) (S J K L : Slots) (pre post : List Row) (r : Row), SelfOnly C →
    KeepsAdmin C → Administered C S (pre ++ r :: post) → ApplyRows C S (pre ++ r :: post) J →
    ApplyLoop C S pre K → ApplyRow C K r L → (∀ x ∈ post, x.proxy ≠ r.proxy) →
    L = K.setImpl r.proxy r.implNew

/-- **`ReinitMovesAreCaughtOnDistinctRows` ON THE SLOTS.** For rows naming distinct proxies,
reinitializers that write only their own proxy's slots and leave its admin slot alone, and
proxies `_admin` administers when the call starts: in a successful `applyRows`, every row's
iteration leaves the slots as a skip or a plain `upgrade` would, so no reinitializer changed a
slot. -/
def Properties.ReinitMovesAreCaughtOnDistinctRowsOnSlots : Prop :=
  ∀ (C : Config) (S J K L : Slots) (pre post : List Row) (r : Row),
    (pre ++ r :: post).Pairwise (fun a b => a.proxy ≠ b.proxy) → SelfOnly C → KeepsAdmin C →
    Administered C S (pre ++ r :: post) → ApplyRows C S (pre ++ r :: post) J →
    ApplyLoop C S pre K → ApplyRow C K r L → L = K.setImpl r.proxy r.implNew

/-- **`OrderIndependent` ON THE SLOTS.** Under `SelfOnly`, `KeepsAdmin` and `Administered`,
two successful calls over permutations of the same rows reach the same slots. Without
`KeepsAdmin` this fails (`AdminRewriteMakesOrderMatter`). -/
def Properties.OrderIndependentOnSlots : Prop :=
  ∀ (C : Config) (S J K : Slots) (rows rows' : List Row), rows.Perm rows' → SelfOnly C →
    KeepsAdmin C → Administered C S rows → ApplyRows C S rows J → ApplyRows C S rows' K → J = K

/-! ## Witnesses -/

/-- **THE TRANSFER PREMISES ARE MET, AND NOT ONLY VACUOUSLY.** In `wCfg` (`RowsCurrent`'s
witness configuration, lifted), `SelfOnly` and `KeepsAdmin` hold, and `Administered` holds for
the valid rows `rowA`, `rowB` from `wSlots`. `applyRows` succeeds in both orders and as a
CTM-domain `ApplyTransition`, reaching one state that moves proxies `5` and `6` to their
targets and leaves every admin slot alone. In it `rowB`, the last row, is a real swap with
`callInitializeUpgrade` set: its proxy is not at the target before its iteration. `wCfg`'s
reinitializer is inert (the identity), so `SelfOnly` and `KeepsAdmin` hold there trivially. So the
premises of `ApplyRowsCorrespond`, the six `...OnSlots` results and
`SelfOnlyProjectsToReinitFrames` hold together, with the moving disjuncts firing for proxies `5`
and `6`; no successful call here has a reinitializer that changes the slots.

`wKeepAdminSelfMoving` (`wSelfMoving` lifted) meets `SelfOnly` and `KeepsAdmin` too. Its
reinitializer moves proxy `6` back to `10` and leaves the admin slot alone. The first loop
succeeds and `applyRows` reverts: the move is caught, as
`ReinitMovesAreCaughtOnDistinctRowsOnSlots` requires. -/
@[witness] def Properties.AdminSlotWitness : Prop :=
  SelfOnly wCfg ∧ KeepsAdmin wCfg ∧ Administered wCfg wSlots [rowA, rowB] ∧
    ValidRows [rowA, rowB] ∧
    (∃ J, ApplyRows wCfg wSlots [rowA, rowB] J ∧ ApplyRows wCfg wSlots [rowB, rowA] J ∧
      ApplyTransition wCfg .ctm ⟨3, .ctm, [rowA, rowB]⟩ wSlots J ∧
      J.impl 5 = 11 ∧ J.impl 6 = 12 ∧ J.admin = wSlots.admin ∧
      ∃ K L, ApplyLoop wCfg wSlots [rowA] K ∧ ApplyRow wCfg K rowB L ∧
        K.impl rowB.proxy ≠ rowB.implNew ∧ rowB.callInitializeUpgrade = true) ∧
    SelfOnly wKeepAdminSelfMoving ∧ KeepsAdmin wKeepAdminSelfMoving ∧
    Administered wKeepAdminSelfMoving wSlots [rowA, rowB] ∧
    (∃ K, ApplyLoop wKeepAdminSelfMoving wSlots [rowA, rowB] K) ∧
    ¬ ∃ J, ApplyRows wKeepAdminSelfMoving wSlots [rowA, rowB] J

/-- **WITHOUT `KeepsAdmin`, EVERY CASE OCCURS IN ONE RUN.** The run of
`AdminRewritePassesVerification`: `wAdminRewrite` meets `SelfOnly`, `_admin` administers every
proxy of `wSlots`, and the valid rows `rowA`, `rowB` name distinct proxies. In the successful
call:

* proxy `7`, which no row names, keeps both slots (the first case of
  `OnlyNamedEdgesOrAdminLost`);
* proxy `5` moves along `rowA`'s edge and stays administered by `_admin` (the second case, not
  the first), so `AdministeredRowRunsItsTarget` and the first case of
  `SourceIsNotAppliedOnSlots` apply to `rowA`;
* proxy `6` starts administered by `_admin` and ends not, and `rowB` calls
  `initializeUpgrade()` (the third case; `AdminRewritePassesVerification` shows it is in
  neither of the others), so `AdminLostOnlyByOwnReinitializer` applies to it and
  `SourceIsNotAppliedOnSlots` takes its second case for `rowB`;
* `rowA`'s iteration, with `pre = []` and `post = [rowB]`, is a plain swap (the first case of
  `ReinitMovesAreCaughtOrAdminLost`; `rowB`'s iteration takes the second). -/
def Properties.AdminSlotCasesWitness : Prop :=
  SelfOnly wAdminRewrite ∧ Administered wAdminRewrite wSlots [rowA, rowB] ∧
    [rowA, rowB].Pairwise (fun a b => a.proxy ≠ b.proxy) ∧
    ∃ J, ApplyRows wAdminRewrite wSlots [rowA, rowB] J ∧
      ((∀ r ∈ [rowA, rowB], r.proxy ≠ 7) ∧ J.impl 7 = wSlots.impl 7 ∧
        J.admin 7 = wSlots.admin 7) ∧
      (wSlots.impl rowA.proxy = rowA.expectedOldImpl ∧ J.impl rowA.proxy = rowA.implNew ∧
        J.impl rowA.proxy ≠ wSlots.impl rowA.proxy ∧
        J.admin rowA.proxy = wSlots.admin rowA.proxy ∧
        J.admin rowA.proxy = wAdminRewrite.proxyAdmin) ∧
      (wSlots.admin rowB.proxy = wAdminRewrite.proxyAdmin ∧
        J.admin rowB.proxy ≠ wAdminRewrite.proxyAdmin ∧ rowB.callInitializeUpgrade = true) ∧
      ∃ L, ApplyLoop wAdminRewrite wSlots [] wSlots ∧ ApplyRow wAdminRewrite wSlots rowA L ∧
        L = wSlots.setImpl rowA.proxy rowA.implNew

end Contracts.ProxyUpgradeCurrent.AdminSlot
