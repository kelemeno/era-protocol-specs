import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsAdminSlot

/-!
# Properties: the rows at `e561b9cc2`, read through the proxies' admin dispatch

Statements about `EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsAdminSlot`, which models
each proxy's ERC-1967 implementation and admin slots, the transparent proxy's admin
dispatch, and a reinitializer that can write both slots. Proofs are in
`EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsAdminSlot`.

`Specs/RowsCurrent.lean` reads `_admin.getProxyImplementation(proxy)` as the implementation the
proxy runs. That is true only while `_admin` is the proxy's admin. A reinitializer runs in its
own proxy's storage, so it can change that.

## The countermodel

* `AdminRewriteDefeatsVerification`: valid rows `5: 10 → 11`, `6: 10 → 12`. `rowB`'s
  reinitializer writes only its own proxy (`SelfOnly`; its projection meets `ReinitFrames`).
  It points the admin slot away from `_admin` and the implementation slot at code whose
  `implementation()` returns `12`. `RowsCurrent` says the call reverts. In the contract it
  succeeds, and proxy `6` runs code that is on no row's edge. This refutes the contract
  reading of `ApplyRowsPostcondition`, `OnlyNamedEdgesAcrossCall` and its `AnyRows` and
  transition forms, `FirstRowCarriesTheEdge`, `ReinitMovesAreCaughtOnLastRow` and
  `ReinitMovesAreCaughtOnDistinctRows`. It also refutes the source's `@dev`
  (`ProxyUpgradeRowLib.sol:119-120`) for a reinitializer that moves only its own proxy.
* `AdminRewriteMakesOrderMatter`: the same kind of reinitializer makes the final
  implementation of a row's proxy depend on the order of the rows. This refutes the contract
  reading of `OrderIndependent` and `OrderIndependentOnRowProxies`.
* `MoveBackWithAdminRewriteIsNotCaught`: `ReinitMovingOwnProxyIsCaught`'s move, made together
  with an admin-slot rewrite, is not caught. The proxy ends at its row's source, which refutes
  the implementation-slot reading of `ValidSourceIsNotApplied`.
* `UnadministeredProxyFoolsTheSkip`: `Administered` is needed even with inert
  reinitializers.

## What holds without `KeepsAdmin`

* `AdministeredRowRunsItsTarget`: with no premise, a row's proxy that `_admin` still
  administers runs the row's target.
* `AdminLostOnlyByOwnReinitializer`: under `SelfOnly`, `_admin` loses a proxy only through
  the reinitializer of a row naming that proxy.
* `OnlyNamedEdgesOrAdminLost` (replay safety on the slots) and
  `ReinitMovesAreCaughtOrAdminLost` (the `@dev`). Each holds as in `RowsCurrent`, or
  `_admin` has lost the proxy.
* `SourceIsNotAppliedOnSlots`: from a row's source, a successful call changes that proxy's
  slots.

## The transfer under `KeepsAdmin`

* `RowsCurrentIsTheKeepsAdminFragment` and `ApplyRowsCorrespond`: under `SelfOnly`,
  `KeepsAdmin` and `Administered`, a refined call is exactly a `RowsCurrent` call on the
  implementation slots, and it leaves every admin slot as it was.
* The `RowsCurrent` headlines, restated on the slots: `ApplyRowsPostconditionOnSlots`,
  `OnlyNamedEdgesAcrossCallOnSlots`, `OnlyNamedEdgesAcrossTransitionOnSlots`,
  `ReinitMovesAreCaughtOnLastRowOnSlots`, `ReinitMovesAreCaughtOnDistinctRowsOnSlots`,
  `OrderIndependentOnSlots`.
* `AdminSlotWitness`: the premises hold together with real moves.
-/

namespace Contracts.ProxyUpgradeCurrent.AdminSlot

/-! ## The countermodels -/

/-- **A REINITIALIZER THAT REWRITES ITS OWN PROXY'S ADMIN SLOT DEFEATS THE VERIFICATION.**
The rows are `5: 10 → 11` and `6: 10 → 12` (`rowA`, `rowB`), and they are valid. `_admin`
administers every proxy, and every proxy runs `10`. `rowB`'s reinitializer writes only its
own proxy `6` (`SelfOnly`), and its projection to the implementation mapping meets
`RowsCurrent`'s `ReinitFrames`. It points proxy `6`'s admin slot at `66` and its
implementation slot at `99`, and `99`'s `implementation()` returns `12`. `RowsCurrent` says
`applyRows` reverts. In the contract it succeeds, both directly and as a CTM-domain
transition, because the verification read of proxy `6` is delegated to `99`.

Afterwards proxy `6` runs `99`. That is not its row's target, and the move `10 → 99` is on no
row's edge. `_admin` no longer administers proxy `6`, and `rowB`'s iteration did not leave the
slots as a plain swap would. So, read as statements about the contract, these are false under
the trust model `ReinitFrames` stands for: "every row's proxy runs its `implNew`"
(`ApplyRowsPostcondition`); "a proxy moves only along a row's edge"
(`OnlyNamedEdgesAcrossCall`, `OnlyNamedEdgesAcrossCallAnyRows`,
`OnlyNamedEdgesAcrossTransitionAnyRows`, `FirstRowCarriesTheEdge`); and "a reinitializer
that moves its proxy is caught" (`ReinitMovesAreCaughtOnLastRow`,
`ReinitMovesAreCaughtOnDistinctRows`, and the source's `@dev`, `:119-120`). `KeepsAdmin`
fails, and it is the premise the transfer results add. Proxy `6` lands in the third case of
`OnlyNamedEdgesOrAdminLost`. -/
def Properties.AdminRewriteDefeatsVerification : Prop :=
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
        L ≠ K.setImpl rowB.proxy rowB.implNew

/-- **SUCH A REINITIALIZER CAN MAKE THE ORDER MATTER ON A ROW'S PROXY.** `rowB`'s
reinitializer writes only proxy `6`. It points the admin slot at `66` and installs `98` if
proxy `5` is at `11` when it runs, and `99` otherwise. Both answer `implementation()` with
`12`. Its projection meets `ReinitFrames`, and the rows are valid. Both orders of the rows
succeed, and proxy `6`, which a row names, ends at different implementations. So the contract
reading of `OrderIndependent` (premise `ReinitFrames`) and of `OrderIndependentOnRowProxies`
(no premise) is false. -/
def Properties.AdminRewriteMakesOrderMatter : Prop :=
  SelfOnly wAdminRewriteOrder ∧
    ProxyUpgradeCurrent.ReinitFrames (wAdminRewriteOrder.project wSlots.admin) ∧
    ValidRows [rowA, rowB] ∧ Administered wAdminRewriteOrder wSlots [rowA, rowB] ∧
    ∃ J K, ApplyRows wAdminRewriteOrder wSlots [rowA, rowB] J ∧
      ApplyRows wAdminRewriteOrder wSlots [rowB, rowA] K ∧ rowB ∈ [rowA, rowB] ∧
      J.impl rowB.proxy ≠ K.impl rowB.proxy

/-- **MOVING ITS PROXY BACK IS NOT CAUGHT IF THE ADMIN SLOT IS REWRITTEN TOO.** On the
implementation mapping, `wAdminRewriteBack` is `wSelfMoving`: `rowB`'s reinitializer moves its
own proxy `6` back to `10`, and `RowsCurrent` catches it (`ReinitMovingOwnProxyIsCaught`).
This reinitializer also points proxy `6`'s admin slot at `66`, and the source implementation
`10` answers `implementation()` with `12`. Then `applyRows` over the same valid rows succeeds.
Proxy `6` started at `rowB`'s source and ends there, and only its admin slot moved. So the
contract reading of `ReinitMovingOwnProxyIsCaught`, as evidence for the `@dev`, does not
survive an admin-slot rewrite. Neither does that of `ValidSourceIsNotApplied`'s "any
successful call from it moves that proxy", read on the implementation slot. -/
def Properties.MoveBackWithAdminRewriteIsNotCaught : Prop :=
  SelfOnly wAdminRewriteBack ∧ wAdminRewriteBack.project wSlots.admin = wSelfMoving ∧
    ValidRows [rowA, rowB] ∧ Administered wAdminRewriteBack wSlots [rowA, rowB] ∧
    (¬ ∃ I, ProxyUpgradeCurrent.ApplyRows wSelfMoving wSlots.impl [rowA, rowB] I) ∧
    wSlots.impl rowB.proxy = rowB.expectedOldImpl ∧
    ∃ J, ApplyRows wAdminRewriteBack wSlots [rowA, rowB] J ∧
      J.impl rowB.proxy = wSlots.impl rowB.proxy ∧ J.admin rowB.proxy ≠ wSlots.admin rowB.proxy

/-- **`Administered` IS NEEDED: A PROXY `_admin` DOES NOT ADMINISTER FOOLS THE SKIP.** The
reinitializers are inert, so `SelfOnly` and `KeepsAdmin` hold. Proxy `6` is administered by
`66` and runs `99`, whose `implementation()` returns `12`. `applyRows [rowB]` reads `12`,
takes the skip, passes the verification and changes nothing. Proxy `6` still runs `99`, not
`rowB`'s target. `Specs/RowsCurrent.lean:66-69` leaves this case out of the model. -/
def Properties.UnadministeredProxyFoolsTheSkip : Prop :=
  SelfOnly wForeignAnswers ∧ KeepsAdmin wForeignAnswers ∧ ValidRows [rowB] ∧
    ¬ Administered wForeignAnswers wSlotsForeign6 [rowB] ∧
    ApplyRows wForeignAnswers wSlotsForeign6 [rowB] wSlotsForeign6 ∧
    wSlotsForeign6.impl rowB.proxy ≠ rowB.implNew

/-! ## What holds without `KeepsAdmin` -/

/-- **WHAT THE VERIFICATION ESTABLISHES ON THE SLOTS.** After a successful `applyRows`, a
row's proxy that `_admin` still administers runs that row's `implNew`. No premise. For a proxy
`_admin` no longer administers, the read was answered by the proxy's own implementation, and
nothing follows (`AdminRewriteDefeatsVerification`). -/
def Properties.AdministeredRowRunsItsTarget : Prop :=
  ∀ (C : Config) (S J : Slots) (rows : List Row), ApplyRows C S rows J →
    ∀ r ∈ rows, J.admin r.proxy = C.proxyAdmin → J.impl r.proxy = r.implNew

/-- **ONLY THE REINITIALIZER OF A ROW NAMING A PROXY CAN TAKE IT FROM `_admin`.** Under
`SelfOnly`: if `_admin` administered `p` when the call started and does not when it returns,
some row naming `p` calls `initializeUpgrade()`. A plain swap and a skip leave the admin slot
alone, and a forwarded swap needs `_admin` to have lost the proxy already. -/
def Properties.AdminLostOnlyByOwnReinitializer : Prop :=
  ∀ (C : Config) (S J : Slots) (rows : List Row) (p : Address), SelfOnly C →
    ApplyRows C S rows J → S.admin p = C.proxyAdmin → J.admin p ≠ C.proxyAdmin →
    ∃ r ∈ rows, r.proxy = p ∧ r.callInitializeUpgrade = true

/-- **REPLAY SAFETY ON THE SLOTS, WITHOUT `KeepsAdmin`.** This is the strongest form of
`OnlyNamedEdgesAcrossCallAnyRows` that holds for reinitializers that write only their own
proxy. For any rows, under `SelfOnly` and `Administered`, after a successful `applyRows` each
proxy is in one of three cases. It kept both slots. Or it was at some row's `expectedOldImpl`,
is now at that row's `implNew`, and is still administered by `_admin`. Or `_admin` has lost
it, and some row naming it calls `initializeUpgrade()`. The third case happens
(`AdminRewriteDefeatsVerification`). The proof takes the first row naming the proxy as the
row of the second case, as `FirstRowCarriesTheEdge` does. -/
def Properties.OnlyNamedEdgesOrAdminLost : Prop :=
  ∀ (C : Config) (S J : Slots) (rows : List Row), SelfOnly C → Administered C S rows →
    ApplyRows C S rows J → ∀ p,
      (J.impl p = S.impl p ∧ J.admin p = S.admin p) ∨
      (∃ r ∈ rows, r.proxy = p ∧ S.impl p = r.expectedOldImpl ∧ J.impl p = r.implNew ∧
        J.admin p = S.admin p) ∨
      (J.admin p ≠ C.proxyAdmin ∧ ∃ r ∈ rows, r.proxy = p ∧ r.callInitializeUpgrade = true)

/-- **ON DISTINCT ROWS, A REINITIALIZER THAT MOVES ANYTHING IS CAUGHT OR TOOK ITS PROXY FROM
`_admin`.** This is the source's `@dev` (`ProxyUpgradeRowLib.sol:119-120`) without
`KeepsAdmin`. Take rows naming distinct proxies, as a genuine object's are, with `SelfOnly`
and `Administered`. Take a successful `applyRows`, a row `r`, the state `K` before `r`'s
iteration and the state `L` after it. Then `L` is `K` with `r`'s proxy's implementation slot
at `r.implNew`, which is what a skip or a plain `upgrade` leaves, unless `_admin` no longer
administers `r`'s proxy when the call returns. The second case happens
(`AdminRewriteDefeatsVerification`), and no read through `_admin` can detect it. Once the
admin slot is rewritten, `getProxyImplementation` and `getProxyAdmin`
(`transparent/ProxyAdmin.sol:21-42`) are both answered by the proxy's own implementation. -/
def Properties.ReinitMovesAreCaughtOrAdminLost : Prop :=
  ∀ (C : Config) (S J K L : Slots) (pre post : List Row) (r : Row),
    (pre ++ r :: post).Pairwise (fun a b => a.proxy ≠ b.proxy) → SelfOnly C →
    Administered C S (pre ++ r :: post) → ApplyRows C S (pre ++ r :: post) J →
    ApplyLoop C S pre K → ApplyRow C K r L →
    L = K.setImpl r.proxy r.implNew ∨ J.admin r.proxy ≠ C.proxyAdmin

/-- **FROM A ROW'S SOURCE, A SUCCESSFUL CALL CHANGES THAT PROXY'S SLOTS.**
`SourceIsNotAppliedAnyRows` on the slots. The row is not a self-edge, and its proxy is
administered by `_admin` and at the row's `expectedOldImpl`. Then the verification does not
already hold. After any successful `applyRows`, either `_admin` still administers the proxy
and its implementation slot moved, or `_admin` has lost it. No premise on the other rows and
no `SelfOnly`. The implementation slot alone need not move
(`MoveBackWithAdminRewriteIsNotCaught`). -/
def Properties.SourceIsNotAppliedOnSlots : Prop :=
  ∀ (C : Config) (S J : Slots) (rows : List Row) (r : Row), r ∈ rows →
    r.expectedOldImpl ≠ r.implNew → S.admin r.proxy = C.proxyAdmin →
    S.impl r.proxy = r.expectedOldImpl →
    ¬ RowsRead C S rows ∧
      (ApplyRows C S rows J →
        (J.admin r.proxy = C.proxyAdmin ∧ J.impl r.proxy ≠ S.impl r.proxy) ∨
          J.admin r.proxy ≠ C.proxyAdmin)

/-! ## The transfer under `KeepsAdmin` -/

/-- **`SelfOnly` IS THE SLOT READING OF `ReinitFrames`.** Every projection of a `SelfOnly`
configuration to a fixed admin mapping meets `RowsCurrent`'s `ReinitFrames`. -/
def Properties.SelfOnlyProjectsToReinitFrames : Prop :=
  ∀ (C : Config) (A : Address → Address), SelfOnly C → ProxyUpgradeCurrent.ReinitFrames (C.project A)

/-- **`RowsCurrent` IS THE `KeepsAdmin` FRAGMENT.** Every `RowsCurrent` configuration `C0`,
lifted with `_admin` at any `a`, meets `KeepsAdmin`. It meets `SelfOnly` exactly when `C0`
meets `ReinitFrames`, and it projects back to `C0` at every admin mapping. So, by
`ApplyRowsCorrespond`, when `C0` meets `ReinitFrames` its runs from `I` are exactly the runs of
`lift C0 a` from the state with implementation slots `I` and `_admin` administering every
proxy, read on the implementation slots. -/
def Properties.RowsCurrentIsTheKeepsAdminFragment : Prop :=
  ∀ (C0 : ProxyUpgradeCurrent.Config) (a : Address) (A : Address → Address),
    KeepsAdmin (lift C0 a) ∧ (SelfOnly (lift C0 a) ↔ ProxyUpgradeCurrent.ReinitFrames C0) ∧
      (lift C0 a).project A = C0

/-- **UNDER `KeepsAdmin` THE CALL IS THE `RowsCurrent` CALL.** Take reinitializers that write
only their own proxy's slots and never its admin slot, and a starting state in which `_admin`
administers every row's proxy. Then a successful refined `applyRows` is exactly a successful
`RowsCurrent` `applyRows` on the implementation slots that leaves every admin slot as it was.
So every `RowsCurrent` result is a result about the implementation slots under these
premises. -/
def Properties.ApplyRowsCorrespond : Prop :=
  ∀ (C : Config) (S J : Slots) (rows : List Row), SelfOnly C → KeepsAdmin C →
    Administered C S rows →
    (ApplyRows C S rows J ↔
      ProxyUpgradeCurrent.ApplyRows (C.project S.admin) S.impl rows J.impl ∧ J.admin = S.admin)

/-- **`ApplyRowsPostcondition` ON THE SLOTS.** Under `SelfOnly`, `KeepsAdmin` and
`Administered`, after a successful `applyRows` every row's proxy runs its `implNew` and is
still administered by `_admin`. Without `KeepsAdmin` this fails
(`AdminRewriteDefeatsVerification`), and without `Administered` too
(`UnadministeredProxyFoolsTheSkip`). -/
def Properties.ApplyRowsPostconditionOnSlots : Prop :=
  ∀ (C : Config) (S J : Slots) (rows : List Row), SelfOnly C → KeepsAdmin C →
    Administered C S rows → ApplyRows C S rows J →
    ∀ r ∈ rows, J.impl r.proxy = r.implNew ∧ J.admin r.proxy = C.proxyAdmin

/-- **`OnlyNamedEdgesAcrossCallAnyRows` ON THE SLOTS.** For any rows, under `SelfOnly`,
`KeepsAdmin` and `Administered`: after a successful `applyRows` no admin slot has changed, and
every proxy's implementation slot is where it was, or was at some row's `expectedOldImpl` and
is now at that row's `implNew`. -/
def Properties.OnlyNamedEdgesAcrossCallOnSlots : Prop :=
  ∀ (C : Config) (S J : Slots) (rows : List Row), SelfOnly C → KeepsAdmin C →
    Administered C S rows → ApplyRows C S rows J → J.admin = S.admin ∧
      ∀ p, J.impl p = S.impl p ∨
        ∃ r ∈ rows, r.proxy = p ∧ S.impl p = r.expectedOldImpl ∧ J.impl p = r.implNew

/-- **`OnlyNamedEdgesAcrossTransitionAnyRows` ON THE SLOTS.** The same for `applyTransition`
on any object that is code and reports the domain. `Administered` is about the object's rows:
the executors' bound admin administers their proxies. -/
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

/-- **`ReinitMovesAreCaughtOnDistinctRows` ON THE SLOTS.** The source's `@dev`
(`ProxyUpgradeRowLib.sol:119-120`), "a reinitializer that moves any proxy of the row set is
caught too", holds for rows naming distinct proxies, reinitializers that write only their own
proxy's slots and leave its admin slot alone, and proxies `_admin` administers. -/
def Properties.ReinitMovesAreCaughtOnDistinctRowsOnSlots : Prop :=
  ∀ (C : Config) (S J K L : Slots) (pre post : List Row) (r : Row),
    (pre ++ r :: post).Pairwise (fun a b => a.proxy ≠ b.proxy) → SelfOnly C → KeepsAdmin C →
    Administered C S (pre ++ r :: post) → ApplyRows C S (pre ++ r :: post) J →
    ApplyLoop C S pre K → ApplyRow C K r L → L = K.setImpl r.proxy r.implNew

/-- **`OrderIndependent` ON THE SLOTS.** Under `SelfOnly`, `KeepsAdmin` and `Administered`,
two successful calls over permutations of the same rows reach the same slots. -/
def Properties.OrderIndependentOnSlots : Prop :=
  ∀ (C : Config) (S J K : Slots) (rows rows' : List Row), rows.Perm rows' → SelfOnly C →
    KeepsAdmin C → Administered C S rows → ApplyRows C S rows J → ApplyRows C S rows' K → J = K

/-! ## Witness -/

/-- **THE TRANSFER PREMISES ARE MET, AND NOT ONLY VACUOUSLY.** In `wCfg` (`RowsCurrent`'s
witness configuration, lifted), `SelfOnly` and `KeepsAdmin` hold, and `Administered` holds for
the valid rows `rowA`, `rowB` from `wSlots`. `applyRows` succeeds, moves proxies `5` and `6`
to their targets, and leaves every admin slot alone. `wKeepAdminSelfMoving` (`wSelfMoving`
lifted) meets `SelfOnly` and `KeepsAdmin` too. Its reinitializer moves proxy `6` back to `10`
and leaves the admin slot alone. The first loop succeeds and `applyRows` reverts: the move is
caught, as `ReinitMovesAreCaughtOnDistinctRowsOnSlots` requires. -/
def Properties.AdminSlotWitness : Prop :=
  SelfOnly wCfg ∧ KeepsAdmin wCfg ∧ Administered wCfg wSlots [rowA, rowB] ∧
    ValidRows [rowA, rowB] ∧
    (∃ J, ApplyRows wCfg wSlots [rowA, rowB] J ∧ J.impl 5 = 11 ∧ J.impl 6 = 12 ∧
      J.admin = wSlots.admin) ∧
    SelfOnly wKeepAdminSelfMoving ∧ KeepsAdmin wKeepAdminSelfMoving ∧
    Administered wKeepAdminSelfMoving wSlots [rowA, rowB] ∧
    (∃ K, ApplyLoop wKeepAdminSelfMoving wSlots [rowA, rowB] K) ∧
    ¬ ∃ J, ApplyRows wKeepAdminSelfMoving wSlots [rowA, rowB] J

end Contracts.ProxyUpgradeCurrent.AdminSlot
