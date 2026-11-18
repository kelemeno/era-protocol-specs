import EraSpec.Contracts.L2AssetTracker.Specs.RecoveryNeutrality

/-!
# Properties: atomic recovery and the `L2AssetTracker` at v35

Statements about `EraSpec.Contracts.L2AssetTracker.Specs.RecoveryNeutrality` (v35 head `b17415d20`;
the same code at `main` `70096e2ea` on the modelled paths).  Proofs are in
`EraSpec.Contracts.L2AssetTracker.Proofs.RecoveryNeutrality`.  `TRK`, `L2NTV`, `BTH`, `L2AR`, `AFM`
are the source files listed in the specification's header.

"Recovery" is the vault's `bridgeRecoverFailedTransfer` reached from `claimRefund` through the
router's `recoverAtomicCall` (a router call) or `bridgehubRecoverBaseToken` (a valued direct call),
including the base-token holder's `recoverBaseToken`.  The asset view of a state at `a` is
`Sys.AgreeAt`: every tracker entry indexed by `a`, the vault's registry entries for `a`, the router's
handler for `a`, and, when `a` is the base asset, the holder's balance.

## (i) A recovery whose original destination is L1 reverts

* `RecoveryToL1RevertsAtV35`: with the v35 checks, `claimRefund` of a bundle toward L1, the router's
  two recovery entry points toward L1, the vault's recovery toward L1, and the holder's recovery of a
  nonzero amount toward L1 all revert.
* `EachL1CheckSufficesOnItsPath`: each of the four L1 checks rejects, on its own, every recovery that
  reaches it: the flow manager's (`AFM:299`) every bundle toward L1, the router's (`L2AR:275`, `:320`)
  both entry points and every bundle toward L1 with a call that reaches the router, the vault's call
  of the tracker check (`L2NTV:213`) every vault recovery, the holder's (`BTH:84`) every nonzero
  base-token recovery.  `L1RecoveryRejectionWitness` exhibits a valued bundle call whose recovery
  passes all four checks, so that each single-check configuration rejects it toward L1, while it
  succeeds toward another chain, and with no checks at all toward L1.
* `L1ChecksLoadBearing` (countermodel): with the four checks removed, a model run bridges `x` out
  toward L1 while settling on L1 and then claims a bundle toward L1 that recovers `x`; the claim
  succeeds, `totalWithdrawalsToL1` keeps counting the bridge-out, and the recovery raises
  `totalSuccessfulDepositsFromL1`.  The model lets a claim name any bundle; the source's interop
  center never appends a bundle toward L1 (`IC:552-553`, `:733-742`), which the model leaves out, so
  this run shows what the recovery-side checks do on their own.

## (ii) A bridge-out followed by its recovery

* `BurnThenRecoveriesRestoreAsset`: the vault's bridge-out of `x` of `a` toward `d`, then any run of
  steps none of which is on `a`, then v35 vault recoveries of `a` toward `d` whose amounts total `x`.
  Every tracker entry of `a` ends as the first-touch registration of `a` left it, the registry and
  handler entries of `a` are unchanged, every other asset is as the intermediate run left it, and
  the holder's balance is restored (base asset) or untouched by both (other assets).
* `InteropValueBurnThenRecoveriesRestoreBase`: the same for the interop center's same-base-token value
  burn (`IC:432-440`) and recoveries of the base asset.
* `RecoveriesAfterBurnSucceed`: in the same setting, the recoveries succeed whenever the destination
  is not L1 and, for the base asset, the vault does not record it as native here (the release of
  funds, which can revert in the source, is not modelled).
* `ClaimRefundIsVaultRecoveries`: a claim whose calls are all valued direct calls is the vault's
  recoveries of the bundle's destination base token, one per call; a claim whose calls are all
  router calls for one asset whose handler is the vault is the vault's recoveries of that asset.
* `BurnThenClaimRestores`: the two round trips stated with the `claimRefund` entry point.
* `BurnThenInterleavedRecoveriesRestoreAsset`: the same restoration of the asset when the recoveries
  are interleaved in any order with operations not on the asset, as when a refund's release runs code
  between the calls of a claim (`InterleavedRecoveryWitness`).
* `BalancedFlowsRestoreAsset`: the general form for an asset the tracker has already registered.  In
  a nested run (other steps, and the calls of other claims, may fall between the calls of a claim)
  whose steps on the asset are bridge-outs toward chains other than L1 and calls of claims, with
  bridged-out and recovered totals equal, the asset's view ends as it started, whatever the order
  and however many bridge-outs and claims there are (`BalancedFlowsWitness`).
* `StepNotOnAssetLeavesItAlone`: a step that is not on asset `a` leaves the asset view at `a`
  unchanged (any checks).
* Witnesses: `RecoveryRoundTripWitness`, `BaseRecoveryRoundTripWitness`, `StepNotOnAssetWitness`.

## (iii) What one recovery writes

* `VaultRecoveryEffectAtV35`: a successful v35 vault recovery has a destination other than L1, leaves
  `interopInfo` unchanged, and: for the base asset, writes no tracker entry at all, needs the vault to
  record the base asset as not native here, and lowers the holder's balance by the amount; for any
  other asset, makes the first-touch registration and then adds exactly the amount to
  `chainBalance[block.chainid][a]` if the vault records `a` as native here, writes no other tracker
  entry, and changes `a`'s registry entries only when it deploys a bridged token for `a`.
* `ClaimRefundNeverWritesInteropInfo`: a successful v35 `claimRefund` has a destination other than L1,
  leaves `interopInfo` unchanged, never lowers a chain balance, changes none on another chain, and
  never raises the holder's balance.  `RecoveryEffectWitness` makes both effects nonzero.

## (iv) `totalWithdrawalsToL1`

* `WithdrawalsToL1Ledger`: along any run, under any checks, `totalWithdrawalsToL1[a]` grows by exactly
  the amounts of the logged bridge-outs of `a` toward L1 made while the chain settled on L1; with the
  flow manager's check (so at v35), no logged recovery has L1 as its destination, so the counter
  never decreases.  That a counted L1 bridge-out
  is never refunded through a claim toward another chain depends on the claim naming its own
  appended bundle, which is not modelled (see the specification's header).
  `WithdrawalsLedgerWitness` is a run with counted and uncounted bridge-outs and a recovery.
* `WithdrawalsToL1LedgerNested`: the same ledger for nested runs, in which other steps fall between
  the calls of a claim, as a release inside the claim can make them; every run is a nested run.
  `NestedLedgerWitness` has a counted bridge-out between the two calls of one claim.

## Boundary: the checked re-credit (`TRK:220`)

* `RecoveryCreditFitsIff`: for a registered asset other than the base asset that the vault records as
  native here, a v35 recovery toward a non-L1 chain succeeds (as modelled) exactly when
  `chainBalance + amount` fits in a word.  For the base asset it succeeds exactly when the amount is
  zero or the holder can pay, if the vault records it as not native here, and never if native here.
* `InflowBeforeRecoveryBlocksClaim`: for an asset native here whose chain balance is
  `MAX_TOKEN_BALANCE`, a bridge-out, then an inbound transfer of the same amount of it, then the claim
  of the bridge-out: the claim reverts as a whole.  Without the inbound transfer the same claim
  succeeds and restores the chain balance.

## The base-token origin check (`TRK:182-184`)

* `BaseOriginCheckLoadBearing` (countermodel): with the base asset recorded as native here (a
  configuration the source's comments say does not occur, `TRK:180-181`), the vault's bridge-out of it
  lowers its chain balance and leaves the holder alone.  With both origin checks removed, its
  recovery succeeds, pays out of the holder, and leaves the chain balance lowered.  With the v35
  checks the same recovery reverts.
-/

namespace Contracts.L2AssetTracker.RecoveryNeutrality

/-! ## (i) A recovery whose original destination is L1 reverts -/

/-- **NO RECOVERY TOWARD L1 AT V35.**  With every check present: `claimRefund` of a bundle whose
destination is `L1_CHAIN_ID` reverts; so do the router's `recoverAtomicCall` and
`bridgehubRecoverBaseToken` with destination L1 (any call data, asset, receiver, amount), the vault's
`bridgeRecoverFailedTransfer` with destination L1 (any asset and mint data), and the holder's
`recoverBaseToken` of a nonzero amount with destination L1. -/
def Properties.RecoveryToL1RevertsAtV35 : Prop :=
  ∀ (cfg : Config) (sys : Sys) (reads : AssetId → TokenReads),
    (∀ b : Bundle, b.dest = cfg.l1 → exec cfg Guards.v35 sys (.claimRefund reads b) = none) ∧
    (∀ data : CallData, routerRecoverAtomicCall cfg Guards.v35 sys reads cfg.l1 data = none) ∧
    (∀ (a : AssetId) (r : Address) (x : UInt256),
      routerRecoverBase cfg Guards.v35 sys reads cfg.l1 a r x = none) ∧
    (∀ (a : AssetId) (m : Option MintData), vaultRecover cfg Guards.v35 sys reads cfg.l1 a m = none) ∧
    (∀ x : UInt256, x ≠ 0 → holderRecover cfg Guards.v35 sys x cfg.l1 = none)

/-- **EACH L1 CHECK ALONE SUFFICES ON ITS PATH.**  For any combination of checks:
* with the flow manager's check (`AFM:299`), every bundle toward L1 reverts;
* with the router's (`L2AR:275`, `:320`), both router entry points toward L1 revert, and so does
  every bundle toward L1 with a call that reaches the router (a router call, or a valued call);
* with the vault's call of the tracker check (`L2NTV:213`), every vault recovery toward L1 reverts;
* with the holder's (`BTH:84`), every holder recovery of a nonzero amount toward L1 reverts.
The vault's check is not on the path of a router call whose handler is not the vault, and the
holder's only on the base asset's path. -/
def Properties.EachL1CheckSufficesOnItsPath : Prop :=
  ∀ (cfg : Config) (g : Guards) (sys : Sys) (reads : AssetId → TokenReads),
    (g.managerL1 = true → ∀ b : Bundle, b.dest = cfg.l1 → recoverBundle cfg g sys reads b = none) ∧
    (g.routerL1 = true →
      (∀ data : CallData, routerRecoverAtomicCall cfg g sys reads cfg.l1 data = none) ∧
      (∀ (a : AssetId) (r : Address) (x : UInt256),
        routerRecoverBase cfg g sys reads cfg.l1 a r x = none) ∧
      ∀ b : Bundle, b.dest = cfg.l1 → (∃ c ∈ b.calls, c.sender = cfg.router ∨ c.value ≠ 0) →
        recoverBundle cfg g sys reads b = none) ∧
    (g.vaultL1 = true → ∀ (a : AssetId) (m : Option MintData),
      vaultRecover cfg g sys reads cfg.l1 a m = none) ∧
    (g.holderL1 = true → ∀ x : UInt256, x ≠ 0 → holderRecover cfg g sys x cfg.l1 = none)

/-- **THE L1 CHECKS ARE NOT VACUOUS.**  A state and a valued direct call `c` (amount nonzero, sender not
the router, the bundle's destination base token the base asset) such that:
* the claim of `⟨L1, base, [c]⟩` reverts at v35 and under each of the four single-check
  configurations;
* with no checks at all it succeeds and lowers the holder's balance;
* with the v35 checks, the claim of the same call in a bundle toward another chain succeeds and
  lowers the holder's balance. -/
def Properties.L1RecoveryRejectionWitness : Prop :=
  ∃ (cfg : Config) (sys : Sys) (reads : AssetId → TokenReads) (c : Call) (d : ChainId),
    c.sender ≠ cfg.router ∧ c.value ≠ 0 ∧ d ≠ cfg.l1 ∧
    exec cfg Guards.v35 sys (.claimRefund reads ⟨cfg.l1, cfg.base, [c]⟩) = none ∧
    exec cfg { Guards.none with managerL1 := true } sys (.claimRefund reads ⟨cfg.l1, cfg.base, [c]⟩)
      = none ∧
    exec cfg { Guards.none with routerL1 := true } sys (.claimRefund reads ⟨cfg.l1, cfg.base, [c]⟩)
      = none ∧
    exec cfg { Guards.none with vaultL1 := true } sys (.claimRefund reads ⟨cfg.l1, cfg.base, [c]⟩)
      = none ∧
    exec cfg { Guards.none with holderL1 := true } sys (.claimRefund reads ⟨cfg.l1, cfg.base, [c]⟩)
      = none ∧
    (∃ s, exec cfg Guards.none sys (.claimRefund reads ⟨cfg.l1, cfg.base, [c]⟩) = some s ∧
      s.holder < sys.holder) ∧
    (∃ s, exec cfg Guards.v35 sys (.claimRefund reads ⟨d, cfg.base, [c]⟩) = some s ∧
      s.holder < sys.holder)

/-- **COUNTERMODEL: WITHOUT THE RECOVERY CHECKS, A RECOVERY TOWARD L1 GOES THROUGH.**  With every
recovery check removed (`Guards.none`: the four L1 checks, and the two base-origin checks, which are
off this path), a run (from a state where both of asset `a`'s counters are
zero) whose log has a bridge-out of `x ≠ 0` of `a` toward L1 made while settling on L1 and a recovery
of `x` of `a` whose original destination is L1.  At its end `totalWithdrawalsToL1[a]` is `x` (it
still counts the bridge-out) and `totalSuccessfulDepositsFromL1[a]` is also `x` (the recovery is
counted as a deposit from L1).  With the v35 checks the same operations revert.  The run's claim
names a bundle toward L1, which the model admits and the source's interop center never appends (see
the specification's header): the statement is about the recovery-side checks alone. -/
def Properties.L1ChecksLoadBearing : Prop :=
  ∃ (cfg : Config) (sys₀ sys : Sys) (ops : List Op) (a : AssetId) (x : UInt256),
    x ≠ 0 ∧ (sys₀.trk.interopInfo a) = ⟨0, 0⟩ ∧
    run cfg Guards.none sys₀ ops = some sys ∧
    Event.burned a cfg.l1 x cfg.l1 ∈ sys.log ∧ Event.recovered a cfg.l1 x ∈ sys.log ∧
    (sys.trk.interopInfo a).totalWithdrawalsToL1 = x ∧
    (sys.trk.interopInfo a).totalSuccessfulDepositsFromL1 = x ∧
    run cfg Guards.v35 sys₀ ops = none

/-! ## (ii) A bridge-out followed by its recovery -/

/-- **A STEP NOT ON `a` LEAVES `a` ALONE.**  Under any checks, a successful operation that is not a
step on `a` (`Op.Touches`) leaves the asset view at `a` (`Sys.AgreeAt`) unchanged. -/
def Properties.StepNotOnAssetLeavesItAlone : Prop :=
  ∀ (cfg : Config) (g : Guards) (sys sys' : Sys) (op : Op) (a : AssetId),
    exec cfg g sys op = some sys' → ¬ op.Touches cfg a → sys'.AgreeAt cfg sys a

/-- **THE STEP FRAME IS NOT VACUOUS.**  A step on one asset `b` that changes `b`'s chain balance here,
and is not a step on another asset `a`. -/
def Properties.StepNotOnAssetWitness : Prop :=
  ∃ (cfg : Config) (sys sys' : Sys) (op : Op) (a b : AssetId),
    exec cfg Guards.v35 sys op = some sys' ∧ ¬ op.Touches cfg a ∧ op.Touches cfg b ∧
    sys'.trk.chainBalance cfg.thisChain b ≠ sys.trk.chainBalance cfg.thisChain b

/-- **THE VAULT'S BRIDGE-OUT AND ITS RECOVERIES RESTORE THE ASSET (headline (ii)).**  Premises: the
vault's bridge-out of `x` of `a` toward `d` from `sys₀` succeeds with `sys₁`; a run `mid` of
operations, none of which is a step on `a`, takes `sys₁` to `sys₂`; v35 vault recoveries of `a`
toward `d`, one per mint data in `mds`, whose amounts total `x`, take `sys₂` to `sys₃`.  Then, with
`t₀` the first-touch registration of `a` on `sys₀`'s tracker (which exists):
* every tracker entry of `a` in `sys₃` is `t₀`'s;
* `a`'s registry and handler entries are `sys₀`'s;
* every other asset's view is `sys₂`'s;
* the holder's balance is `sys₀`'s if `a` is the base asset; otherwise neither the bridge-out nor the
  recoveries change it. -/
def Properties.BurnThenRecoveriesRestoreAsset : Prop :=
  ∀ (cfg : Config) (sys₀ sys₁ sys₂ sys₃ : Sys) (reads₀ : TokenReads) (reads : AssetId → TokenReads)
    (d : ChainId) (a : AssetId) (x : UInt256) (mid : List Op) (mds : List MintData),
    exec cfg Guards.v35 sys₀ (.vaultBurn reads₀ d a x) = some sys₁ →
    run cfg Guards.v35 sys₁ mid = some sys₂ → (∀ op ∈ mid, ¬ op.Touches cfg a) →
    (mds.map fun m => m.amount.val).sum = x.val →
    vaultRecoverAll cfg Guards.v35 sys₂ reads d a mds = some sys₃ →
    ∃ t₀, registerIfNeeded cfg sys₀ reads₀ sys₀.trk a (sys₀.token a) = some t₀ ∧
      sys₃.trk.AgreeAt t₀ a ∧ sys₃.origin a = sys₀.origin a ∧ sys₃.token a = sys₀.token a ∧
      sys₃.handler a = sys₀.handler a ∧ (∀ b, b ≠ a → sys₃.AgreeAt cfg sys₂ b) ∧
      (a = cfg.base → sys₃.holder = sys₀.holder) ∧
      (a ≠ cfg.base → sys₁.holder = sys₀.holder ∧ sys₃.holder = sys₂.holder)

/-- **THE INTEROP CENTER'S VALUE BURN AND ITS RECOVERIES RESTORE THE BASE ASSET.**  As
`BurnThenRecoveriesRestoreAsset`, for the interop center's same-base-token value burn of `v` toward
`d` and v35 vault recoveries of the base asset whose amounts total `v`, with no step on the base asset
in between: the base asset's tracker entries end as its first-touch registration left them, its
registry and handler entries are `sys₀`'s, every other asset's view is `sys₂`'s, and the holder's
balance is `sys₀`'s. -/
def Properties.InteropValueBurnThenRecoveriesRestoreBase : Prop :=
  ∀ (cfg : Config) (sys₀ sys₁ sys₂ sys₃ : Sys) (reads₀ : TokenReads) (reads : AssetId → TokenReads)
    (d : ChainId) (v : UInt256) (mid : List Op) (mds : List MintData),
    exec cfg Guards.v35 sys₀ (.icBurnBase reads₀ d v) = some sys₁ →
    run cfg Guards.v35 sys₁ mid = some sys₂ → (∀ op ∈ mid, ¬ op.Touches cfg cfg.base) →
    (mds.map fun m => m.amount.val).sum = v.val →
    vaultRecoverAll cfg Guards.v35 sys₂ reads d cfg.base mds = some sys₃ →
    ∃ t₀, registerIfNeeded cfg sys₀ reads₀ sys₀.trk cfg.base (sys₀.token cfg.base) = some t₀ ∧
      sys₃.trk.AgreeAt t₀ cfg.base ∧ sys₃.origin cfg.base = sys₀.origin cfg.base ∧
      sys₃.token cfg.base = sys₀.token cfg.base ∧ sys₃.handler cfg.base = sys₀.handler cfg.base ∧
      (∀ b, b ≠ cfg.base → sys₃.AgreeAt cfg sys₂ b) ∧ sys₃.holder = sys₀.holder

/-- **THE RECOVERIES OF A BRIDGE-OUT SUCCEED (AS MODELLED).**  In the settings of
`BurnThenRecoveriesRestoreAsset` and `InteropValueBurnThenRecoveriesRestoreBase` (before the
recoveries), if the destination is not L1 and, for the base asset, the vault does not record it as
native here on `sys₀`, then the v35 vault recoveries whose amounts total the bridged-out amount
succeed.  The release of funds, which the model does not represent, can still revert in the
source. -/
def Properties.RecoveriesAfterBurnSucceed : Prop :=
  (∀ (cfg : Config) (sys₀ sys₁ sys₂ : Sys) (reads₀ : TokenReads) (reads : AssetId → TokenReads)
    (d : ChainId) (a : AssetId) (x : UInt256) (mid : List Op) (mds : List MintData),
    exec cfg Guards.v35 sys₀ (.vaultBurn reads₀ d a x) = some sys₁ →
    run cfg Guards.v35 sys₁ mid = some sys₂ → (∀ op ∈ mid, ¬ op.Touches cfg a) →
    d ≠ cfg.l1 → (a = cfg.base → sys₀.origin a ≠ cfg.thisChain) →
    (mds.map fun m => m.amount.val).sum = x.val →
    ∃ sys₃, vaultRecoverAll cfg Guards.v35 sys₂ reads d a mds = some sys₃) ∧
  (∀ (cfg : Config) (sys₀ sys₁ sys₂ : Sys) (reads₀ : TokenReads) (reads : AssetId → TokenReads)
    (d : ChainId) (v : UInt256) (mid : List Op) (mds : List MintData),
    exec cfg Guards.v35 sys₀ (.icBurnBase reads₀ d v) = some sys₁ →
    run cfg Guards.v35 sys₁ mid = some sys₂ → (∀ op ∈ mid, ¬ op.Touches cfg cfg.base) →
    d ≠ cfg.l1 → sys₀.origin cfg.base ≠ cfg.thisChain →
    (mds.map fun m => m.amount.val).sum = v.val →
    ∃ sys₃, vaultRecoverAll cfg Guards.v35 sys₂ reads d cfg.base mds = some sys₃)

/-- **A CLAIM IS THE VAULT'S RECOVERIES.**  At v35:
* if every call of the bundle is a valued direct call (sender not the router, nonzero value), the
  claim reverts toward L1 and otherwise is the vault's recoveries of the bundle's destination base
  token, one per call, of the call's value, refunded to its sender (`L2AR:326`);
* if the vault's address is nonzero, the router's handler for `a` is the vault, and the bundle's calls
  are router calls `finalizeDeposit(a, md)` for the mint data `mds` in order, the claim reverts toward
  L1 and otherwise is the vault's recoveries of `a` with `mds`. -/
def Properties.ClaimRefundIsVaultRecoveries : Prop :=
  ∀ (cfg : Config) (sys : Sys) (reads : AssetId → TokenReads) (b : Bundle),
    ((∀ c ∈ b.calls, c.sender ≠ cfg.router ∧ c.value ≠ 0) →
      exec cfg Guards.v35 sys (.claimRefund reads b) =
        if b.dest = cfg.l1 then none
        else vaultRecoverAll cfg Guards.v35 sys reads b.dest b.destBase
          (b.calls.map fun c => ⟨c.sender, c.sender, 0, c.value, []⟩)) ∧
    (∀ (a : AssetId) (mds : List MintData), cfg.ntv ≠ 0 → sys.handler a = cfg.ntv →
      b.calls = mds.map (fun md => ⟨cfg.router, .finalizeDeposit a (some md), 0⟩) →
      exec cfg Guards.v35 sys (.claimRefund reads b) =
        if b.dest = cfg.l1 then none else vaultRecoverAll cfg Guards.v35 sys reads b.dest a mds)

/-- **A BRIDGE-OUT AND THE CLAIM OF ITS LEG RESTORE THE ASSET (entry-point form of (ii)).**  At v35,
with the vault's address nonzero:
* the vault's bridge-out of `x` of `a` toward `d`, with the vault as `a`'s handler at that time; a run
  with no step on `a`; then a successful `claimRefund` of a bundle toward `d` whose calls are router
  calls `finalizeDeposit(a, md)` for mint data totalling `x`: the conclusion of
  `BurnThenRecoveriesRestoreAsset` holds;
* the interop center's value burn of `v` toward `d`; a run with no step on the base asset; then a
  successful `claimRefund` of a bundle toward `d` with the base asset as destination base token and
  only valued direct calls, totalling `v`: the conclusion of
  `InteropValueBurnThenRecoveriesRestoreBase` holds. -/
def Properties.BurnThenClaimRestores : Prop :=
  (∀ (cfg : Config) (sys₀ sys₁ sys₂ sys₃ : Sys) (reads₀ : TokenReads)
    (reads : AssetId → TokenReads) (d : ChainId) (destBase a : AssetId) (x : UInt256)
    (mid : List Op) (mds : List MintData),
    cfg.ntv ≠ 0 → sys₀.handler a = cfg.ntv →
    exec cfg Guards.v35 sys₀ (.vaultBurn reads₀ d a x) = some sys₁ →
    run cfg Guards.v35 sys₁ mid = some sys₂ → (∀ op ∈ mid, ¬ op.Touches cfg a) →
    (mds.map fun m => m.amount.val).sum = x.val →
    exec cfg Guards.v35 sys₂ (.claimRefund reads
      ⟨d, destBase, mds.map (fun md => ⟨cfg.router, .finalizeDeposit a (some md), 0⟩)⟩) = some sys₃ →
    ∃ t₀, registerIfNeeded cfg sys₀ reads₀ sys₀.trk a (sys₀.token a) = some t₀ ∧
      sys₃.trk.AgreeAt t₀ a ∧ sys₃.origin a = sys₀.origin a ∧ sys₃.token a = sys₀.token a ∧
      sys₃.handler a = sys₀.handler a ∧ (∀ b, b ≠ a → sys₃.AgreeAt cfg sys₂ b) ∧
      (a = cfg.base → sys₃.holder = sys₀.holder) ∧
      (a ≠ cfg.base → sys₁.holder = sys₀.holder ∧ sys₃.holder = sys₂.holder)) ∧
  (∀ (cfg : Config) (sys₀ sys₁ sys₂ sys₃ : Sys) (reads₀ : TokenReads)
    (reads : AssetId → TokenReads) (d : ChainId) (v : UInt256) (mid : List Op) (calls : List Call),
    exec cfg Guards.v35 sys₀ (.icBurnBase reads₀ d v) = some sys₁ →
    run cfg Guards.v35 sys₁ mid = some sys₂ → (∀ op ∈ mid, ¬ op.Touches cfg cfg.base) →
    (∀ c ∈ calls, c.sender ≠ cfg.router ∧ c.value ≠ 0) →
    (calls.map fun c => c.value.val).sum = v.val →
    exec cfg Guards.v35 sys₂ (.claimRefund reads ⟨d, cfg.base, calls⟩) = some sys₃ →
    ∃ t₀, registerIfNeeded cfg sys₀ reads₀ sys₀.trk cfg.base (sys₀.token cfg.base) = some t₀ ∧
      sys₃.trk.AgreeAt t₀ cfg.base ∧ sys₃.origin cfg.base = sys₀.origin cfg.base ∧
      sys₃.token cfg.base = sys₀.token cfg.base ∧ sys₃.handler cfg.base = sys₀.handler cfg.base ∧
      (∀ b, b ≠ cfg.base → sys₃.AgreeAt cfg sys₂ b) ∧ sys₃.holder = sys₀.holder)

/-- **(ii) UNDER ARBITRARY INTERLEAVING.**  The vault's bridge-out of `x` of `a` toward `d` from `sys₀`
(resp. the interop center's value burn of `v` of the base asset), then a schedule of v35 vault
recoveries of the asset toward `d` whose amounts total the bridged-out amount, interleaved in any
order with operations none of which is a step on the asset (`runSchedule`).  Then, with `t₀` the
first-touch registration of the asset on `sys₀`'s tracker (which exists), every tracker entry of the
asset ends as `t₀`'s, its registry and handler entries are `sys₀`'s, and for the base asset so is the
holder's balance. -/
def Properties.BurnThenInterleavedRecoveriesRestoreAsset : Prop :=
  (∀ (cfg : Config) (sys₀ sys₁ sys₃ : Sys) (reads₀ : TokenReads) (reads : AssetId → TokenReads)
    (d : ChainId) (a : AssetId) (x : UInt256) (sched : List SchedItem),
    exec cfg Guards.v35 sys₀ (.vaultBurn reads₀ d a x) = some sys₁ →
    (∀ op, SchedItem.other op ∈ sched → ¬ op.Touches cfg a) →
    ((scheduleRecoveries sched).map fun m => m.amount.val).sum = x.val →
    runSchedule cfg Guards.v35 reads d a sys₁ sched = some sys₃ →
    ∃ t₀, registerIfNeeded cfg sys₀ reads₀ sys₀.trk a (sys₀.token a) = some t₀ ∧
      sys₃.trk.AgreeAt t₀ a ∧ sys₃.origin a = sys₀.origin a ∧ sys₃.token a = sys₀.token a ∧
      sys₃.handler a = sys₀.handler a ∧ (a = cfg.base → sys₃.holder = sys₀.holder)) ∧
  (∀ (cfg : Config) (sys₀ sys₁ sys₃ : Sys) (reads₀ : TokenReads) (reads : AssetId → TokenReads)
    (d : ChainId) (v : UInt256) (sched : List SchedItem),
    exec cfg Guards.v35 sys₀ (.icBurnBase reads₀ d v) = some sys₁ →
    (∀ op, SchedItem.other op ∈ sched → ¬ op.Touches cfg cfg.base) →
    ((scheduleRecoveries sched).map fun m => m.amount.val).sum = v.val →
    runSchedule cfg Guards.v35 reads d cfg.base sys₁ sched = some sys₃ →
    ∃ t₀, registerIfNeeded cfg sys₀ reads₀ sys₀.trk cfg.base (sys₀.token cfg.base) = some t₀ ∧
      sys₃.trk.AgreeAt t₀ cfg.base ∧ sys₃.origin cfg.base = sys₀.origin cfg.base ∧
      sys₃.token cfg.base = sys₀.token cfg.base ∧ sys₃.handler cfg.base = sys₀.handler cfg.base ∧
      sys₃.holder = sys₀.holder)

/-- **THE INTERLEAVED PREMISES, NONTRIVIALLY.**  (1) A bridge-out of `x ≠ 0` of an asset `a` other than
the base asset toward `d ≠ L1`, then a schedule with two recoveries and, between them, a step on another
asset; it succeeds and moves `a`'s chain balance off its post-bridge-out value.  (2) The interop
center's value burn of `v ≠ 0`, then a schedule with two recoveries of the base asset and steps not
on it between and before them; it succeeds and restores the holder's balance. -/
def Properties.InterleavedRecoveryWitness : Prop :=
  ∃ (cfg : Config) (sys₀ sys₁ sys₃ s₁ s₃ : Sys) (reads₀ : TokenReads)
    (reads : AssetId → TokenReads) (d : ChainId) (a : AssetId) (x v : UInt256)
    (sched sched' : List SchedItem),
    a ≠ cfg.base ∧ x ≠ 0 ∧ v ≠ 0 ∧ d ≠ cfg.l1 ∧
    exec cfg Guards.v35 sys₀ (.vaultBurn reads₀ d a x) = some sys₁ ∧
    (∀ op, SchedItem.other op ∈ sched → ¬ op.Touches cfg a) ∧ (∃ op, SchedItem.other op ∈ sched) ∧
    (scheduleRecoveries sched).length = 2 ∧
    ((scheduleRecoveries sched).map fun m => m.amount.val).sum = x.val ∧
    runSchedule cfg Guards.v35 reads d a sys₁ sched = some sys₃ ∧
    sys₃.trk.chainBalance cfg.thisChain a ≠ sys₁.trk.chainBalance cfg.thisChain a ∧
    exec cfg Guards.v35 sys₀ (.icBurnBase reads₀ d v) = some s₁ ∧
    (∀ op, SchedItem.other op ∈ sched' → ¬ op.Touches cfg cfg.base) ∧
    (∃ op, SchedItem.other op ∈ sched') ∧ (scheduleRecoveries sched').length = 2 ∧
    ((scheduleRecoveries sched').map fun m => m.amount.val).sum = v.val ∧
    runSchedule cfg Guards.v35 reads d cfg.base s₁ sched' = some s₃ ∧ s₃.holder = sys₀.holder

/-- **BALANCED FLOWS LEAVE A REGISTERED ASSET AS IT WAS ((ii), general form).**  At v35, a nested run
(`runNested`) from `sys₀` to `sys` in which:
* every step on asset `a` (`NestedItem.Touches`) is a bridge-out of `a` toward a chain other than L1
  (the vault's, or for the base asset the interop center's value burn) or a call of a claim;
* the bridged-out total of `a` equals the total that the calls ask the vault to recover
  (`NestedItem.burnedOf`, `NestedItem.recoveredOf`);
* if some call is a router call naming `a`, the router's handler for `a` on `sys₀` is the vault.
Premises on `sys₀`: the tracker has registered `a`, the vault has a nonzero token address for `a`,
and if `a` is the base asset the vault does not record it as native here.  Then the asset view at `a`
on `sys` is the one on `sys₀` (`Sys.AgreeAt`): every tracker entry of `a`, its registry and handler
entries, and for the base asset the holder's balance.  Bridge-outs, calls of any number of claims
(of bundles that may also name other assets), and other steps may come in any order. -/
def Properties.BalancedFlowsRestoreAsset : Prop :=
  ∀ (cfg : Config) (sys₀ sys : Sys) (items : List NestedItem) (a : AssetId),
    runNested cfg Guards.v35 sys₀ items = some sys →
    sys₀.trk.isAssetRegistered a = true → sys₀.token a ≠ 0 →
    (a = cfg.base → sys₀.origin a ≠ cfg.thisChain) →
    (∀ it ∈ items, it.Touches cfg a → it.IsFlowOf cfg a) →
    (∀ it ∈ items, it.IsRouterCallOn cfg a → sys₀.handler a = cfg.ntv) →
    (items.map (NestedItem.burnedOf cfg a)).sum = (items.map (NestedItem.recoveredOf cfg a)).sum →
    sys.AgreeAt cfg sys₀ a

/-- **BALANCED FLOWS, NONTRIVIALLY.**  (1) An asset `a` other than the base asset, native here and
registered, with a token and with the vault as its handler, and a v35 nested run from that state
that succeeds and contains the vault's bridge-outs of `x₁ ≠ 0` and `x₂ ≠ 0` of `a` toward two
different chains other than L1, a router call naming `a`, and a step on another asset `b`.  Its steps
on `a` are bridge-outs toward chains other than L1 or calls of claims, and its bridged-out and
recovered totals of `a` are both `x₁ + x₂`.  A prefix of it moves `a`'s chain balance here off its
start value.  (2) The base asset, registered, with a token and recorded as not native here, and a
v35 nested run from that state that succeeds and contains the interop center's value burn of
`v₁ ≠ 0`, the vault's bridge-out of `v₂ ≠ 0` of the base asset, and a settlement-layer change, and
no router call naming the base asset.  Its steps on the base asset are bridge-outs toward chains
other than L1 or calls of claims, and its bridged-out and recovered totals are both `v₁ + v₂`.  A
prefix of it moves the holder's balance off its start value. -/
def Properties.BalancedFlowsWitness : Prop :=
  ∃ (cfg : Config) (sys₀ sys s₀ s : Sys) (items items' pre pre' : List NestedItem) (a b : AssetId)
    (d₁ d₂ e₁ e₂ c : ChainId) (x₁ x₂ v₁ v₂ : UInt256) (r₁ r₂ r₃ r₄ : TokenReads),
    a ≠ cfg.base ∧ b ≠ a ∧ d₁ ≠ d₂ ∧ d₁ ≠ cfg.l1 ∧ d₂ ≠ cfg.l1 ∧
    x₁ ≠ 0 ∧ x₂ ≠ 0 ∧ v₁ ≠ 0 ∧ v₂ ≠ 0 ∧
    sys₀.origin a = cfg.thisChain ∧ sys₀.trk.isAssetRegistered a = true ∧ sys₀.token a ≠ 0 ∧
    sys₀.handler a = cfg.ntv ∧
    runNested cfg Guards.v35 sys₀ items = some sys ∧
    NestedItem.op (.vaultBurn r₁ d₁ a x₁) ∈ items ∧ NestedItem.op (.vaultBurn r₂ d₂ a x₂) ∈ items ∧
    (∃ it ∈ items, it.IsRouterCallOn cfg a) ∧ (∃ it ∈ items, it.Touches cfg b) ∧
    (∀ it ∈ items, it.Touches cfg a → it.IsFlowOf cfg a) ∧
    (items.map (NestedItem.burnedOf cfg a)).sum = x₁.val + x₂.val ∧
    (items.map (NestedItem.recoveredOf cfg a)).sum = x₁.val + x₂.val ∧
    pre <+: items ∧ (∃ sp, runNested cfg Guards.v35 sys₀ pre = some sp ∧
      sp.trk.chainBalance cfg.thisChain a ≠ sys₀.trk.chainBalance cfg.thisChain a) ∧
    s₀.origin cfg.base ≠ cfg.thisChain ∧ s₀.trk.isAssetRegistered cfg.base = true ∧
    s₀.token cfg.base ≠ 0 ∧
    runNested cfg Guards.v35 s₀ items' = some s ∧
    NestedItem.op (.icBurnBase r₃ e₁ v₁) ∈ items' ∧
    NestedItem.op (.vaultBurn r₄ e₂ cfg.base v₂) ∈ items' ∧
    NestedItem.op (.setSettlementLayer c) ∈ items' ∧
    (∀ it ∈ items', ¬ it.IsRouterCallOn cfg cfg.base) ∧
    (∀ it ∈ items', it.Touches cfg cfg.base → it.IsFlowOf cfg cfg.base) ∧
    (items'.map (NestedItem.burnedOf cfg cfg.base)).sum = v₁.val + v₂.val ∧
    (items'.map (NestedItem.recoveredOf cfg cfg.base)).sum = v₁.val + v₂.val ∧
    pre' <+: items' ∧ (∃ sp, runNested cfg Guards.v35 s₀ pre' = some sp ∧ sp.holder ≠ s₀.holder)

/-- **THE ROUND-TRIP PREMISES, NONTRIVIALLY.**  An asset `a` other than the base asset, native here and
not yet registered, and a nonempty run `mid` of steps none of which is on `a` (one of them changes
another asset's chain balance).  The vault's bridge-out of `x ≠ 0` of `a` toward `d ≠ L1` succeeds;
its first-touch registration changes the chain balance; two recoveries of nonzero amounts totalling
`x`, made by one `claimRefund` of two router calls, succeed and bring the chain balance back to the
registration's value, which differs from the value before the bridge-out. -/
def Properties.RecoveryRoundTripWitness : Prop :=
  ∃ (cfg : Config) (sys₀ sys₁ sys₂ sys₃ : Sys) (reads₀ : TokenReads)
    (reads : AssetId → TokenReads) (d : ChainId) (a b : AssetId) (x : UInt256) (mid : List Op)
    (mds : List MintData) (t₀ : Tracker),
    a ≠ cfg.base ∧ b ≠ a ∧ d ≠ cfg.l1 ∧ x ≠ 0 ∧ mds.length = 2 ∧ (∀ m ∈ mds, m.amount ≠ 0) ∧
    sys₀.trk.isAssetRegistered a = false ∧ sys₀.origin a = cfg.thisChain ∧ mid ≠ [] ∧
    exec cfg Guards.v35 sys₀ (.vaultBurn reads₀ d a x) = some sys₁ ∧
    run cfg Guards.v35 sys₁ mid = some sys₂ ∧ (∀ op ∈ mid, ¬ op.Touches cfg a) ∧
    sys₂.trk.chainBalance cfg.thisChain b ≠ sys₁.trk.chainBalance cfg.thisChain b ∧
    (mds.map fun m => m.amount.val).sum = x.val ∧
    vaultRecoverAll cfg Guards.v35 sys₂ reads d a mds = some sys₃ ∧
    cfg.ntv ≠ 0 ∧ sys₀.handler a = cfg.ntv ∧ sys₂.handler a = cfg.ntv ∧
    exec cfg Guards.v35 sys₂ (.claimRefund reads
      ⟨d, cfg.base, mds.map (fun md => ⟨cfg.router, .finalizeDeposit a (some md), 0⟩)⟩) = some sys₃ ∧
    registerIfNeeded cfg sys₀ reads₀ sys₀.trk a (sys₀.token a) = some t₀ ∧
    t₀.chainBalance cfg.thisChain a ≠ sys₀.trk.chainBalance cfg.thisChain a ∧
    sys₁.trk.chainBalance cfg.thisChain a ≠ t₀.chainBalance cfg.thisChain a ∧
    sys₃.trk.chainBalance cfg.thisChain a = t₀.chainBalance cfg.thisChain a

/-- **THE BASE-ASSET ROUND-TRIP PREMISES, NONTRIVIALLY.**  The base asset recorded as not native here.
(1) The vault's bridge-out of `x ≠ 0` of the base asset toward `d ≠ L1` raises the holder's balance,
and a recovery of `x` brings it back.  (2) The interop center's value burn of `v ≠ 0` toward `d`,
then a nonempty run of steps none of which is on the base asset, then one `claimRefund` of two valued
calls whose values total `v`: the claim succeeds, is the vault's two recoveries of the base asset,
and brings the holder's balance back. -/
def Properties.BaseRecoveryRoundTripWitness : Prop :=
  ∃ (cfg : Config) (sys₀ sys₁ sys₂ sys₃ s₁ s₂ : Sys) (reads₀ : TokenReads)
    (reads : AssetId → TokenReads) (d : ChainId) (x v : UInt256) (mid : List Op) (md : MintData)
    (calls : List Call),
    sys₀.origin cfg.base ≠ cfg.thisChain ∧ d ≠ cfg.l1 ∧ x ≠ 0 ∧ v ≠ 0 ∧ md.amount = x ∧
    exec cfg Guards.v35 sys₀ (.vaultBurn reads₀ d cfg.base x) = some s₁ ∧
    s₁.holder = sys₀.holder + x.val ∧
    vaultRecoverAll cfg Guards.v35 s₁ reads d cfg.base [md] = some s₂ ∧ s₂.holder = sys₀.holder ∧
    exec cfg Guards.v35 sys₀ (.icBurnBase reads₀ d v) = some sys₁ ∧ mid ≠ [] ∧
    run cfg Guards.v35 sys₁ mid = some sys₂ ∧ (∀ op ∈ mid, ¬ op.Touches cfg cfg.base) ∧
    calls.length = 2 ∧ (∀ c ∈ calls, c.sender ≠ cfg.router ∧ c.value ≠ 0) ∧
    (calls.map fun c => c.value.val).sum = v.val ∧
    exec cfg Guards.v35 sys₂ (.claimRefund reads ⟨d, cfg.base, calls⟩) = some sys₃ ∧
    vaultRecoverAll cfg Guards.v35 sys₂ reads d cfg.base
      (calls.map fun c => ⟨c.sender, c.sender, 0, c.value, []⟩) = some sys₃ ∧
    sys₂.holder = sys₀.holder + v.val ∧ sys₃.holder = sys₀.holder

/-! ## (iii) What one recovery writes -/

/-- **WHAT A VAULT RECOVERY WRITES AT V35.**  A successful v35 vault recovery of `md.amount` of `a`
with original destination `d`:
* `d` is not L1; `interopInfo` is unchanged for every asset; the router's handlers and the settlement
  layer are unchanged; the log gains one `recovered a d amount` event;
* for the base asset: the vault records it as not native here, the tracker is unchanged, the registry
  is unchanged, and the holder's balance drops by the amount;
* for any other asset: the holder's balance is unchanged; registry entries of other assets are
  unchanged, and `a`'s too when the vault records `a` as native here or has a token for it; and with
  `t₀` the first-touch registration of `a` (which exists), the new tracker is `t₀` with
  `chainBalance[block.chainid][a]` raised by exactly the amount (checked) if the vault records `a` as
  native here, and `t₀` otherwise. -/
def Properties.VaultRecoveryEffectAtV35 : Prop :=
  ∀ (cfg : Config) (sys sys' : Sys) (reads : AssetId → TokenReads) (d : ChainId) (a : AssetId)
    (md : MintData),
    vaultRecover cfg Guards.v35 sys reads d a (some md) = some sys' →
    d ≠ cfg.l1 ∧ sys'.trk.interopInfo = sys.trk.interopInfo ∧ sys'.handler = sys.handler ∧
      sys'.sl = sys.sl ∧ sys'.log = sys.log ++ [.recovered a d md.amount] ∧
      (a = cfg.base → sys.origin a ≠ cfg.thisChain ∧ sys'.trk = sys.trk ∧
        sys'.holder + md.amount.val = sys.holder ∧ sys'.origin = sys.origin ∧
        sys'.token = sys.token) ∧
      (a ≠ cfg.base → sys'.holder = sys.holder ∧
        (∀ b, b ≠ a → sys'.origin b = sys.origin b ∧ sys'.token b = sys.token b) ∧
        ((sys.origin a = cfg.thisChain ∨ sys.token a ≠ 0) →
          sys'.origin = sys.origin ∧ sys'.token = sys.token) ∧
        ∃ t₀, registerIfNeeded cfg sys (reads a) sys.trk a (sys.token a) = some t₀ ∧
          (if sys.origin a = cfg.thisChain then increaseChainBalance t₀ cfg.thisChain a md.amount
            else some t₀) = some sys'.trk)

/-- **A CLAIM NEVER WRITES `interopInfo` (headline (iii)).**  A successful v35 `claimRefund` in any
state: the bundle's destination is not L1; `interopInfo` is unchanged for every asset; no chain
balance decreases; chain balances on chains other than this one are unchanged; the holder's balance
does not increase; handlers and the settlement layer are unchanged. -/
def Properties.ClaimRefundNeverWritesInteropInfo : Prop :=
  ∀ (cfg : Config) (sys sys' : Sys) (reads : AssetId → TokenReads) (b : Bundle),
    exec cfg Guards.v35 sys (.claimRefund reads b) = some sys' →
    b.dest ≠ cfg.l1 ∧ sys'.trk.interopInfo = sys.trk.interopInfo ∧
      (∀ c a, (sys.trk.chainBalance c a).val ≤ (sys'.trk.chainBalance c a).val) ∧
      (∀ c a, c ≠ cfg.thisChain → sys'.trk.chainBalance c a = sys.trk.chainBalance c a) ∧
      sys'.holder ≤ sys.holder ∧ sys'.handler = sys.handler ∧ sys'.sl = sys.sl

/-- **THE RECOVERY EFFECTS, NONZERO.**  (1) A v35 vault recovery of a nonzero amount of a registered
asset other than the base asset, native here, raises its chain balance here by the amount.  (2) A v35
vault recovery of a nonzero amount of the base asset lowers the holder's balance by it.  (3) A v35
`claimRefund` changes a chain balance (by `ClaimRefundNeverWritesInteropInfo`, it can only raise
one). -/
def Properties.RecoveryEffectWitness : Prop :=
  ∃ (cfg : Config) (sys s₁ s₂ s₃ : Sys) (reads : AssetId → TokenReads) (d : ChainId) (a : AssetId)
    (md₁ md₂ : MintData) (b : Bundle),
    a ≠ cfg.base ∧ md₁.amount ≠ 0 ∧ md₂.amount ≠ 0 ∧ sys.trk.isAssetRegistered a = true ∧
    sys.origin a = cfg.thisChain ∧
    vaultRecover cfg Guards.v35 sys reads d a (some md₁) = some s₁ ∧
    (s₁.trk.chainBalance cfg.thisChain a).val =
      (sys.trk.chainBalance cfg.thisChain a).val + md₁.amount.val ∧
    vaultRecover cfg Guards.v35 sys reads d cfg.base (some md₂) = some s₂ ∧
    s₂.holder + md₂.amount.val = sys.holder ∧
    exec cfg Guards.v35 sys (.claimRefund reads b) = some s₃ ∧
    sys.trk.chainBalance cfg.thisChain a ≠ s₃.trk.chainBalance cfg.thisChain a

/-! ## (iv) `totalWithdrawalsToL1` -/

/-- **WHAT `totalWithdrawalsToL1` COUNTS (headline (iv)).**  Along any run under any checks, the log
grows by some events `new`, and for every asset `a`, `totalWithdrawalsToL1[a]` grows by exactly the
total of the `burned a L1 x L1` events in `new` (`l1BurnTotal`): the bridge-outs of `a` toward L1
made while the chain settled on L1.  It never decreases.  If the flow manager's check is present (so
at v35), no `recovered` event in `new` has L1 as its destination. -/
def Properties.WithdrawalsToL1Ledger : Prop :=
  ∀ (cfg : Config) (g : Guards) (sys₀ sys : Sys) (ops : List Op),
    run cfg g sys₀ ops = some sys →
    ∃ new, sys.log = sys₀.log ++ new ∧
      (∀ a, (sys.trk.interopInfo a).totalWithdrawalsToL1.val =
        (sys₀.trk.interopInfo a).totalWithdrawalsToL1.val + l1BurnTotal cfg a new) ∧
      (∀ a, (sys₀.trk.interopInfo a).totalWithdrawalsToL1.val ≤
        (sys.trk.interopInfo a).totalWithdrawalsToL1.val) ∧
      (g.managerL1 = true → ∀ A d x, Event.recovered A d x ∈ new → d ≠ cfg.l1)

/-- **THE LEDGER, NONTRIVIALLY.**  A v35 run from a state where `totalWithdrawalsToL1[a]` is zero, in
which asset `a` is bridged out by `x₁ ≠ 0` toward L1 while settling on L1 (counted), by `x₂ ≠ 0` toward
L1 while settling on another chain (not counted), and by `x₃ ≠ 0` toward another chain, which is then
recovered: `totalWithdrawalsToL1[a]` ends at exactly `x₁`, and the log has the three bridge-outs and
the recovery. -/
def Properties.WithdrawalsLedgerWitness : Prop :=
  ∃ (cfg : Config) (sys₀ sys : Sys) (ops : List Op) (a : AssetId) (x₁ x₂ x₃ : UInt256)
    (s : ChainId) (d : ChainId),
    x₁ ≠ 0 ∧ x₂ ≠ 0 ∧ x₃ ≠ 0 ∧ s ≠ cfg.l1 ∧ d ≠ cfg.l1 ∧
    (sys₀.trk.interopInfo a).totalWithdrawalsToL1 = 0 ∧
    run cfg Guards.v35 sys₀ ops = some sys ∧
    Event.burned a cfg.l1 x₁ cfg.l1 ∈ sys.log ∧ Event.burned a cfg.l1 x₂ s ∈ sys.log ∧
    Event.burned a d x₃ cfg.l1 ∈ sys.log ∧ Event.recovered a d x₃ ∈ sys.log ∧
    (sys.trk.interopInfo a).totalWithdrawalsToL1 = x₁

/-- **THE LEDGER WITH STEPS BETWEEN THE CALLS OF A CLAIM.**  `WithdrawalsToL1Ledger` for nested runs
(`runNested`), in which other operations, and the calls of other claims, may fall between the calls
of a claim: along any nested run under any checks, the log grows by some events `new`, and for every
asset `a`, `totalWithdrawalsToL1[a]` grows by exactly `l1BurnTotal cfg a new` and so never decreases;
if the flow manager's check is present, no `recovered` event in `new` has L1 as its destination.  And
every run is a nested run with the same result, each claim taken as its calls in order
(`NestedItem.ofOp`). -/
def Properties.WithdrawalsToL1LedgerNested : Prop :=
  (∀ (cfg : Config) (g : Guards) (sys₀ sys : Sys) (items : List NestedItem),
    runNested cfg g sys₀ items = some sys →
    ∃ new, sys.log = sys₀.log ++ new ∧
      (∀ a, (sys.trk.interopInfo a).totalWithdrawalsToL1.val =
        (sys₀.trk.interopInfo a).totalWithdrawalsToL1.val + l1BurnTotal cfg a new) ∧
      (∀ a, (sys₀.trk.interopInfo a).totalWithdrawalsToL1.val ≤
        (sys.trk.interopInfo a).totalWithdrawalsToL1.val) ∧
      (g.managerL1 = true → ∀ A d x, Event.recovered A d x ∈ new → d ≠ cfg.l1)) ∧
  (∀ (cfg : Config) (g : Guards) (sys₀ sys : Sys) (ops : List Op),
    run cfg g sys₀ ops = some sys → runNested cfg g sys₀ (ops.flatMap NestedItem.ofOp) = some sys)

/-- **THE NESTED LEDGER, NONTRIVIALLY.**  A v35 nested run, from a state settling on L1 where
`totalWithdrawalsToL1[a]` is zero: a bridge-out of `x ≠ 0` of `a` toward `d ≠ L1`; the first call of
a claim of a two-call bundle toward `d`; a bridge-out of `y ≠ 0` of `a` toward L1 (counted); the
bundle's second call.  The two calls recover nonzero amounts of `a` totalling `x`.  The nested run
succeeds, its log is exactly these four events in this order, and `totalWithdrawalsToL1[a]` ends at
`y`. -/
def Properties.NestedLedgerWitness : Prop :=
  ∃ (cfg : Config) (sys₀ sys : Sys) (reads₀ : TokenReads) (reads : AssetId → TokenReads)
    (d : ChainId) (a : AssetId) (x y x₁ x₂ : UInt256) (c₁ c₂ : Call),
    x ≠ 0 ∧ y ≠ 0 ∧ x₁ ≠ 0 ∧ x₂ ≠ 0 ∧ x₁.val + x₂.val = x.val ∧ d ≠ cfg.l1 ∧
    sys₀.sl = cfg.l1 ∧ (sys₀.trk.interopInfo a).totalWithdrawalsToL1 = 0 ∧
    runNested cfg Guards.v35 sys₀
      [.op (.vaultBurn reads₀ d a x), .call reads ⟨d, cfg.base, [c₁, c₂]⟩ c₁,
        .op (.vaultBurn reads₀ cfg.l1 a y), .call reads ⟨d, cfg.base, [c₁, c₂]⟩ c₂] = some sys ∧
    sys.log = sys₀.log ++
      [.burned a d x cfg.l1, .recovered a d x₁, .burned a cfg.l1 y cfg.l1, .recovered a d x₂] ∧
    (sys.trk.interopInfo a).totalWithdrawalsToL1 = y

/-! ## Boundary: the checked re-credit -/

/-- **WHEN A RECOVERY SUCCEEDS AT V35 (AS MODELLED).**  For a destination other than L1, with the release
of funds not modelled:
* for a registered asset other than the base asset that the vault records as native here, the vault
  recovery succeeds exactly when `chainBalance[block.chainid][a] + amount < 2^256` (`TRK:220`);
* for the base asset recorded as not native here, exactly when the amount is zero or at most the
  holder's balance;
* for the base asset recorded as native here, never (`TRK:182-184`). -/
def Properties.RecoveryCreditFitsIff : Prop :=
  ∀ (cfg : Config) (sys : Sys) (reads : AssetId → TokenReads) (d : ChainId) (a : AssetId)
    (md : MintData), d ≠ cfg.l1 →
    (a ≠ cfg.base → sys.trk.isAssetRegistered a = true → sys.origin a = cfg.thisChain →
      ((∃ s', vaultRecover cfg Guards.v35 sys reads d a (some md) = some s') ↔
        (sys.trk.chainBalance cfg.thisChain a).val + md.amount.val < UInt256.size)) ∧
    (sys.origin cfg.base ≠ cfg.thisChain →
      ((∃ s', vaultRecover cfg Guards.v35 sys reads d cfg.base (some md) = some s') ↔
        (md.amount = 0 ∨ md.amount.val ≤ sys.holder))) ∧
    (sys.origin cfg.base = cfg.thisChain →
      vaultRecover cfg Guards.v35 sys reads d cfg.base (some md) = none)

/-- **AN INBOUND TRANSFER BETWEEN A BRIDGE-OUT AND ITS CLAIM CAN BLOCK THE CLAIM.**  An asset `a` other
than the base asset, native here and registered with chain balance `MAX_TOKEN_BALANCE`.  The vault's
bridge-out of `x ≠ 0` toward `d ≠ L1` succeeds; an inbound transfer of `x` of `a` from a chain `c`
other than L1 succeeds; then `claimRefund` of the bridge-out's router call reverts as a whole.
Without the inbound transfer the same claim succeeds and restores the chain balance. -/
def Properties.InflowBeforeRecoveryBlocksClaim : Prop :=
  ∃ (cfg : Config) (sys₀ sys₁ sys₂ sys₃ : Sys) (reads₀ : TokenReads)
    (reads : AssetId → TokenReads) (d c : ChainId) (a : AssetId) (x : UInt256) (md : MintData),
    a ≠ cfg.base ∧ d ≠ cfg.l1 ∧ c ≠ cfg.l1 ∧ x ≠ 0 ∧ md.amount = x ∧
    sys₀.trk.isAssetRegistered a = true ∧ sys₀.origin a = cfg.thisChain ∧
    sys₀.trk.chainBalance cfg.thisChain a = MAX_TOKEN_BALANCE ∧ sys₀.handler a = cfg.ntv ∧
    exec cfg Guards.v35 sys₀ (.vaultBurn reads₀ d a x) = some sys₁ ∧
    exec cfg Guards.v35 sys₁ (.vaultMint reads₀ c a x) = some sys₂ ∧
    exec cfg Guards.v35 sys₂
      (.claimRefund reads ⟨d, cfg.base, [⟨cfg.router, .finalizeDeposit a (some md), 0⟩]⟩) = none ∧
    exec cfg Guards.v35 sys₁
      (.claimRefund reads ⟨d, cfg.base, [⟨cfg.router, .finalizeDeposit a (some md), 0⟩]⟩) =
        some sys₃ ∧
    sys₃.trk.chainBalance cfg.thisChain a = MAX_TOKEN_BALANCE

/-! ## The base-token origin check -/

/-- **COUNTERMODEL: WITHOUT THE ORIGIN CHECKS, A NATIVE BASE TOKEN'S RECOVERY IS NOT NEUTRAL.**  The base
asset recorded as native here and registered with chain balance `MAX_TOKEN_BALANCE`; the vault's
bridge-out of `x ≠ 0` of it toward `d ≠ L1` lowers its chain balance by `x` and leaves the holder's
balance alone (the native branch, `NTV:442-445`).  With the vault's and the holder's origin checks
removed (all L1 checks kept) its recovery succeeds: the holder pays `x`, and the chain balance stays
lowered by `x`.  With the v35 checks the same recovery reverts.  The source's comments say the base
token never originates on this chain (`TRK:180-181`, `NTV:443`); the model's registry can record it so
(`vaultUpdateBase` writes any origin), and this is the configuration the origin checks reject. -/
def Properties.BaseOriginCheckLoadBearing : Prop :=
  ∃ (cfg : Config) (sys₀ sys₁ sys₂ : Sys) (reads₀ : TokenReads) (reads : AssetId → TokenReads)
    (d : ChainId) (x : UInt256) (md : MintData),
    sys₀.origin cfg.base = cfg.thisChain ∧ d ≠ cfg.l1 ∧ x ≠ 0 ∧ md.amount = x ∧
    sys₀.trk.chainBalance cfg.thisChain cfg.base = MAX_TOKEN_BALANCE ∧
    exec cfg Guards.v35 sys₀ (.vaultBurn reads₀ d cfg.base x) = some sys₁ ∧
    sys₁.holder = sys₀.holder ∧
    (sys₁.trk.chainBalance cfg.thisChain cfg.base).val + x.val = MAX_TOKEN_BALANCE.val ∧
    vaultRecover cfg Guards.v35 sys₁ reads d cfg.base (some md) = none ∧
    vaultRecover cfg { Guards.v35 with vaultBase := false, holderBase := false } sys₁ reads d
      cfg.base (some md) = some sys₂ ∧
    sys₂.holder + x.val = sys₀.holder ∧
    sys₂.trk.chainBalance cfg.thisChain cfg.base = sys₁.trk.chainBalance cfg.thisChain cfg.base

end Contracts.L2AssetTracker.RecoveryNeutrality
