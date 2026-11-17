import EraSpec.Contracts.NativeTokenVaultBase.Specs.TrackerHooks

/-!
# Properties: the deployed chain-balance hooks discharge (or fail) the round-trip premise

Statements about `EraSpec.Contracts.NativeTokenVaultBase.Specs.TrackerHooks`.  Proofs are in
`EraSpec.Contracts.NativeTokenVaultBase.Proofs.TrackerHooks`.  Source pin `c67894b9`,
`L1NTV` = `bridge/ntv/L1NativeTokenVault.sol`, `TRK` = `bridge/asset-tracker/L2AssetTracker.sol`.

## L1: `HooksCancel` holds

* `L1HooksCancel`: the L1 vault's two hooks (`L1NTV:259-277`) satisfy `HooksCancel`, for every
  `block.chainid` and every metadata dependency, native assets included: a checked
  `bridgedOut += amount` is undone by the checked `bridgedOut -= amount` of the same amount.
* `L1NativeHooksMoveBridgedOut`: for a native asset, the outbound hook succeeds iff
  `bridgedOut + amount < 2^256` and adds the amount; the inbound hook succeeds iff
  `amount ≤ bridgedOut` and subtracts it.
* `L1BridgedBranchHooksAreIdentity`: for an asset not native on L1, both hooks are the identity.
* `L1PrepareThenRecoverRoundTrip`: `Properties.PrepareThenRecoverRoundTrip` with the L1 hooks and
  NO hook premise: prepare-then-recover returns the original state exactly.
* `L1BridgedResolutionLeavesLedger`: on the bridged branch the resolution model covers, with the
  ledger agreeing with the configuration, preparation, destination mint and recovery leave the
  ledger unchanged.

## L2: `HooksCancel` fails, and what holds instead

* `HooksCancelIsModuloNothing`: `HooksCancel` is `HooksCancelModulo` with no side condition and
  the identity registration, so the generalization is conservative.
* `PrepareThenRecoverRoundTripModulo`: B2's round trip under the weaker law: the router's
  recovery of a preparation's data succeeds and returns the original state with the accounting
  replaced by the registration `reg`, through the commit interfaces as well.
* `L2HooksCancelModuloRegistration`: the L2 hooks satisfy `HooksCancelModulo` with side condition
  `L2OffL1` (the chain is not L1, or the chain does not settle on L1) and the tracker's
  first-touch registration.
* `AtomicRecoveryRestoresVaultAndTrackerL2` (headline): for a burn whose destination is not L1 (or
  while the chain settles off L1), the atomic-recovery refund restores the vault's whole state
  (token ledger, registry, pause flag, configuration) and the tracker's whole storage, up to the
  first-touch registration of the asset, which reads the PRE-burn token; for an asset the
  tracker had registered, it restores everything exactly.
* Countermodels, all on a well-formed vault state with a successful preparation and a successful
  recovery that restores the token ledger:
  - `L2L1DestinationCountersDiverge`: destination L1 while settling on L1: both L1 counters end
    one unit higher, so `HooksCancel` fails for the L2 hooks;
  - `L2SlSwitchBetweenPrepareAndRecover`: destination L1, settling on L1 at the burn and on
    another layer at the recovery: only `totalWithdrawalsToL1` moves;
  - `L2FirstLegacyBridgeLeavesRegistration`: destination not L1, asset not yet registered in the
    tracker: the recovery leaves the asset registered with the PRE-burn supply as snapshot.
* `L2FirstBridgeRegistersAsNew`: on the first-bridge branch, the L2 registration hook registers
  the token as new (snapshot `(true, 0)`) before the inbound hook runs, so a first bridge never
  takes the first-touch path.

## Non-vacuity

`L1TrackerHooksSatisfiable` meets the premises of `L1PrepareThenRecoverRoundTrip` and
`L1BridgedResolutionLeavesLedger` with a nonzero amount, and shows the native branch of
`L1HooksCancel` is not trivial (the outbound hook changes the ledger, an inbound amount above
`bridgedOut` fails).  `AtomicRecoveryL2Satisfiable` meets the premises of
`AtomicRecoveryRestoresVaultAndTrackerL2` with a registered asset and a nonzero amount, off L1;
`L2FirstLegacyBridgeLeavesRegistration` meets them with an unregistered one.
`L2FirstBridgeSatisfiable` meets the premises of `L2FirstBridgeRegistersAsNew` with a nonzero
amount.
-/

namespace Contracts.NativeTokenVaultBase

/-! ## L1 -/

/-- **THE L1 HOOKS CANCEL.**  For every `block.chainid` and metadata dependency, the L1 vault's
preparation and resolution hooks satisfy `HooksCancel`. -/
def Properties.L1HooksCancel : Prop :=
  ∀ (thisChain : UInt256) (metadata : BridgedStandardERC20.State → UInt256 → Option Bytes),
    HooksCancel (l1Hooks thisChain metadata) (l1ResolutionHooks thisChain)

/-- **WHAT THE L1 HOOKS DO TO A NATIVE ASSET.**  For an asset whose origin chain is `block.chainid`:
the outbound hook succeeds iff `bridgedOut + amount < 2^256` and then holds `bridgedOut + amount`
at the asset and the same values elsewhere; the inbound hook succeeds iff
`amount ≤ bridgedOut` and then holds `bridgedOut - amount` there.  Neither reads the chain or the
token. -/
def Properties.L1NativeHooksMoveBridgedOut : Prop :=
  ∀ (thisChain : UInt256) (acc : L1Ledger) (asset amount : UInt256),
    acc.originChainId asset = thisChain →
      ((∃ acc', l1ToChain thisChain acc asset amount = some acc') ↔
          (acc.bridgedOut asset).val + amount.val < UInt256.size) ∧
      (∀ acc', l1ToChain thisChain acc asset amount = some acc' →
          acc'.originChainId = acc.originChainId ∧
          (acc'.bridgedOut asset).val = (acc.bridgedOut asset).val + amount.val ∧
          ∀ b, b ≠ asset → acc'.bridgedOut b = acc.bridgedOut b) ∧
      ((∃ acc', l1FromChain thisChain acc asset amount = some acc') ↔
          amount.val ≤ (acc.bridgedOut asset).val) ∧
      (∀ acc', l1FromChain thisChain acc asset amount = some acc' →
          acc'.originChainId = acc.originChainId ∧
          (acc'.bridgedOut asset).val = (acc.bridgedOut asset).val - amount.val ∧
          ∀ b, b ≠ asset → acc'.bridgedOut b = acc.bridgedOut b)

/-- **ON THE BRIDGED BRANCH THE L1 HOOKS ARE THE IDENTITY** (`L1NTV:260-264, 270-277` touch only
native assets).  This is the branch `Codegen.VaultPreparationSlice` transcribes; its
`HooksAgree` premise is then about this identity. -/
def Properties.L1BridgedBranchHooksAreIdentity : Prop :=
  ∀ (thisChain : UInt256) (metadata : BridgedStandardERC20.State → UInt256 → Option Bytes)
    (acc : L1Ledger) (before after : BridgedStandardERC20.State) (chain asset amount : UInt256),
    acc.originChainId asset ≠ thisChain →
      (l1Hooks thisChain metadata).account acc before chain asset amount = some acc ∧
      (l1ResolutionHooks thisChain).fromChain acc after chain asset amount = some acc

/-- **THE L1 ROUND TRIP, WITH NO HOOK PREMISE.**  With the L1 hooks, on a `WellFormed` state, the
router's recovery of a successful preparation's returned data returns exactly the state before
the preparation, and through the commit interfaces the recovery reports success. -/
def Properties.L1PrepareThenRecoverRoundTrip : Prop :=
  ∀ (thisChain : UInt256) (metadata : BridgedStandardERC20.State → UInt256 → Option Bytes)
    (s : State L1Ledger) (r : Request) (out : Result L1Ledger),
    WellFormed s → prepare (l1Hooks thisChain metadata) s r = some out →
      bridgeRecoverFailedTransfer (l1ResolutionHooks thisChain) out.state
          (recoveryCall s.config.router r out.data) = some s ∧
      recoverTransact (l1ResolutionHooks thisChain) (transact (l1Hooks thisChain metadata) s r).1
          (recoveryCall s.config.router r out.data) = (s, true)

/-- **ON THE BRIDGED BRANCH THE L1 LEDGER DOES NOT MOVE.**  When the ledger agrees with the vault
configuration (`L1LedgerAgrees`): a successful preparation on a `WellFormed` state, a successful
destination `bridgeMint`, and a successful recovery all leave the ledger as it was. -/
def Properties.L1BridgedResolutionLeavesLedger : Prop :=
  ∀ (thisChain : UInt256) (metadata : BridgedStandardERC20.State → UInt256 → Option Bytes)
    (s : State L1Ledger),
    L1LedgerAgrees thisChain s →
      (∀ (r : Request) (out : Result L1Ledger), WellFormed s →
        prepare (l1Hooks thisChain metadata) s r = some out → out.state.accounting = s.accounting) ∧
      (∀ (c : ResolutionCall) (t : State L1Ledger),
        bridgeMint (l1ResolutionHooks thisChain) s c = some t → t.accounting = s.accounting) ∧
      (∀ (c : ResolutionCall) (t : State L1Ledger),
        bridgeRecoverFailedTransfer (l1ResolutionHooks thisChain) s c = some t →
          t.accounting = s.accounting)

/-! ## The generalized law -/

/-- **`HooksCancel` IS THE TRIVIAL CASE OF `HooksCancelModulo`.** -/
def Properties.HooksCancelIsModuloNothing : Prop :=
  ∀ (Accounting : Type) (hooks : Hooks Accounting) (rh : ResolutionHooks Accounting),
    HooksCancel hooks rh ↔ HooksCancelModulo hooks rh (fun _ _ => True) (fun a _ _ => some a)

/-- **THE ROUND TRIP UP TO A REGISTRATION.**  Under `HooksCancelModulo hooks rh Off reg`, on a
`WellFormed` state, for a successful preparation whose starting accounting and destination chain
satisfy `Off`: the registration of the starting accounting and the PRE-burn token is defined,
with result `a₀`, and the router's recovery of the returned data succeeds with exactly the
original state but accounting `a₀`, also through the commit interfaces. -/
def Properties.PrepareThenRecoverRoundTripModulo : Prop :=
  ∀ (Accounting : Type) (hooks : Hooks Accounting) (rh : ResolutionHooks Accounting)
    (Off : Accounting → UInt256 → Prop)
    (reg : Accounting → BridgedStandardERC20.State → UInt256 → Option Accounting)
    (s : State Accounting) (r : Request) (out : Result Accounting),
    HooksCancelModulo hooks rh Off reg → WellFormed s → prepare hooks s r = some out →
    Off s.accounting r.destinationChain →
      ∃ a₀, reg s.accounting s.token r.assetId = some a₀ ∧
        bridgeRecoverFailedTransfer rh out.state (recoveryCall s.config.router r out.data) =
          some { s with accounting := a₀ } ∧
        recoverTransact rh (transact hooks s r).1 (recoveryCall s.config.router r out.data) =
          ({ s with accounting := a₀ }, true)

/-! ## L2 -/

/-- **THE L2 HOOKS CANCEL UP TO REGISTRATION, OFF L1.** -/
def Properties.L2HooksCancelModuloRegistration : Prop :=
  ∀ (cfg : L2AssetTracker.Config) (metadata : BridgedStandardERC20.State → UInt256 → Option Bytes),
    HooksCancelModulo (l2Hooks cfg metadata) (l2ResolutionHooks cfg) L2OffL1 (l2Registration cfg)

/-- **ATOMIC RECOVERY ON L2 RESTORES THE VAULT AND THE TRACKER** (headline).  With the L2 hooks,
on a `WellFormed` vault state, after a successful preparation whose destination is not L1 (or
while the chain does not settle on L1): the tracker's first-touch registration of the asset from
the starting tracker storage and the PRE-burn token is defined, with result `st₀`; the router's
recovery of the returned data succeeds and yields the original vault state with tracker storage
`st₀` (settlement layer unchanged), also through the commit interfaces; and if the tracker had
already registered the asset, `st₀` is the original storage, so the recovery yields exactly the
original state. -/
def Properties.AtomicRecoveryRestoresVaultAndTrackerL2 : Prop :=
  ∀ (cfg : L2AssetTracker.Config) (metadata : BridgedStandardERC20.State → UInt256 → Option Bytes)
    (s : State L2Accounting) (r : Request) (out : Result L2Accounting),
    WellFormed s → prepare (l2Hooks cfg metadata) s r = some out →
    L2OffL1 s.accounting r.destinationChain →
      ∃ st₀, L2AssetTracker.registerLegacyTokenIfNeeded cfg s.accounting.st
          (L2AssetTracker.tokenReads cfg s.token) r.assetId (cfg.ntvTokenAddress r.assetId) =
          some st₀ ∧
        bridgeRecoverFailedTransfer (l2ResolutionHooks cfg) out.state
            (recoveryCall s.config.router r out.data) =
          some { s with accounting := { s.accounting with st := st₀ } } ∧
        recoverTransact (l2ResolutionHooks cfg) (transact (l2Hooks cfg metadata) s r).1
            (recoveryCall s.config.router r out.data) =
          ({ s with accounting := { s.accounting with st := st₀ } }, true) ∧
        (s.accounting.st.isAssetRegistered r.assetId = true →
          st₀ = s.accounting.st ∧
          bridgeRecoverFailedTransfer (l2ResolutionHooks cfg) out.state
            (recoveryCall s.config.router r out.data) = some s)

/-- **COUNTERMODEL: TO L1 WHILE SETTLING ON L1, THE L1 COUNTERS DIVERGE.**  A `WellFormed` state
whose tracker has the asset registered, a successful preparation to L1 while the chain settles on
L1, and a successful recovery: the token ledger is restored, and both of the asset's L1 counters
are one unit higher, so the state is not; the L2 hooks violate `HooksCancel`. -/
def Properties.L2L1DestinationCountersDiverge : Prop :=
  ∃ (cfg : L2AssetTracker.Config) (metadata : BridgedStandardERC20.State → UInt256 → Option Bytes)
    (s : State L2Accounting) (r : Request) (out : Result L2Accounting) (t : State L2Accounting),
    WellFormed s ∧ s.accounting.st.isAssetRegistered r.assetId = true ∧
    r.destinationChain = s.accounting.st.l1ChainId ∧ s.accounting.sl = s.accounting.st.l1ChainId ∧
    prepare (l2Hooks cfg metadata) s r = some out ∧ r.data.amount ≠ 0 ∧
    bridgeRecoverFailedTransfer (l2ResolutionHooks cfg) out.state
      (recoveryCall s.config.router r out.data) = some t ∧
    t.token = s.token ∧
    (t.accounting.st.interopInfo r.assetId).totalWithdrawalsToL1.val =
      (s.accounting.st.interopInfo r.assetId).totalWithdrawalsToL1.val + r.data.amount.val ∧
    (t.accounting.st.interopInfo r.assetId).totalSuccessfulDepositsFromL1.val =
      (s.accounting.st.interopInfo r.assetId).totalSuccessfulDepositsFromL1.val +
        r.data.amount.val ∧
    t ≠ s ∧ ¬ HooksCancel (l2Hooks cfg metadata) (l2ResolutionHooks cfg)

/-- **COUNTERMODEL: A SETTLEMENT-LAYER SWITCH BETWEEN BURN AND RECOVERY.**  As above, but the chain
moves to another settlement layer `gw` between the preparation and the recovery: the recovery
succeeds and restores the token ledger, `totalWithdrawalsToL1` is one unit higher and
`totalSuccessfulDepositsFromL1` is unchanged, so the tracker storage is not restored. -/
def Properties.L2SlSwitchBetweenPrepareAndRecover : Prop :=
  ∃ (cfg : L2AssetTracker.Config) (metadata : BridgedStandardERC20.State → UInt256 → Option Bytes)
    (s : State L2Accounting) (r : Request) (out : Result L2Accounting) (gw : UInt256)
    (t : State L2Accounting),
    WellFormed s ∧ s.accounting.st.isAssetRegistered r.assetId = true ∧
    r.destinationChain = s.accounting.st.l1ChainId ∧ s.accounting.sl = s.accounting.st.l1ChainId ∧
    gw ≠ s.accounting.st.l1ChainId ∧
    prepare (l2Hooks cfg metadata) s r = some out ∧ r.data.amount ≠ 0 ∧
    bridgeRecoverFailedTransfer (l2ResolutionHooks cfg)
        { out.state with accounting := { out.state.accounting with sl := gw } }
        (recoveryCall s.config.router r out.data) = some t ∧
    t.token = s.token ∧
    (t.accounting.st.interopInfo r.assetId).totalWithdrawalsToL1.val =
      (s.accounting.st.interopInfo r.assetId).totalWithdrawalsToL1.val + r.data.amount.val ∧
    (t.accounting.st.interopInfo r.assetId).totalSuccessfulDepositsFromL1 =
      (s.accounting.st.interopInfo r.assetId).totalSuccessfulDepositsFromL1 ∧
    t.accounting.st ≠ s.accounting.st

/-- **COUNTERMODEL: THE FIRST LEGACY BRIDGE LEAVES A REGISTRATION.**  A `WellFormed` state whose
tracker has not registered the asset, a successful preparation to a chain that is not L1, and a
successful recovery: the token ledger, configuration, registry and pause flag are restored, the
tracker now has the asset registered, with the PRE-burn supply (not the post-burn one) as its
snapshot, and the state is not restored. -/
def Properties.L2FirstLegacyBridgeLeavesRegistration : Prop :=
  ∃ (cfg : L2AssetTracker.Config) (metadata : BridgedStandardERC20.State → UInt256 → Option Bytes)
    (s : State L2Accounting) (r : Request) (out : Result L2Accounting) (t : State L2Accounting),
    WellFormed s ∧ s.accounting.st.isAssetRegistered r.assetId = false ∧
    L2OffL1 s.accounting r.destinationChain ∧
    prepare (l2Hooks cfg metadata) s r = some out ∧ r.data.amount ≠ 0 ∧
    bridgeRecoverFailedTransfer (l2ResolutionHooks cfg) out.state
      (recoveryCall s.config.router r out.data) = some t ∧
    t.token = s.token ∧ t.config = s.config ∧ t.registry = s.registry ∧ t.paused = s.paused ∧
    t.accounting.st.isAssetRegistered r.assetId = true ∧
    (t.accounting.st.totalPreV31TotalSupply r.assetId).amount.val = s.token.totalSupply ∧
    (t.accounting.st.totalPreV31TotalSupply r.assetId).amount.val ≠ out.state.token.totalSupply ∧
    t ≠ s

/-- **ON L2 A FIRST BRIDGE REGISTERS THE TOKEN AS NEW, BEFORE THE INBOUND HOOK.**  With the L2
registration hook (`_setNewTokenStorage` → `registerNewTokenIfNeeded`) and the L2 resolution
hook: a successful first-bridge `bridgeMint` of an asset the tracker had not registered, whose
origin chain is not this chain, leaves the asset registered with snapshot `(true, 0)`
(`L2AssetTracker.sol:168-174`: never bridged before v31), so the inbound hook did not take the
first-touch path and read nothing from the token. -/
def Properties.L2FirstBridgeRegistersAsNew : Prop :=
  ∀ (cfg : L2AssetTracker.Config) (reg : RegistrationHooks L2Accounting)
    (s : RegistrationState L2Accounting) (c : ResolutionCall) (t : State L2Accounting),
    reg.registerTracker = l2RegistrationHook cfg →
    s.accounting.st.isAssetRegistered s.config.assetId = false →
    s.config.originChainId ≠ cfg.thisChain →
    bridgeMintFirst reg (l2ResolutionHooks cfg) s c = some t →
      t.accounting.st.isAssetRegistered s.config.assetId = true ∧
      t.accounting.st.totalPreV31TotalSupply s.config.assetId = ⟨true, 0⟩

/-! ## Non-vacuity -/

/-- **THE FIRST-BRIDGE PREMISES ARE SATISFIABLE**: an unregistered asset from another chain, the L2
registration hook, and a successful first bridge of a nonzero amount. -/
def Properties.L2FirstBridgeSatisfiable : Prop :=
  ∃ (cfg : L2AssetTracker.Config) (reg : RegistrationHooks L2Accounting)
    (s : RegistrationState L2Accounting) (c : ResolutionCall) (t : State L2Accounting),
    reg.registerTracker = l2RegistrationHook cfg ∧
    s.accounting.st.isAssetRegistered s.config.assetId = false ∧
    s.config.originChainId ≠ cfg.thisChain ∧ c.data.amount ≠ 0 ∧
    bridgeMintFirst reg (l2ResolutionHooks cfg) s c = some t

/-- **THE L1 PREMISES ARE SATISFIABLE, AND THE NATIVE BRANCH IS NOT TRIVIAL.**  A `WellFormed`
state whose ledger agrees with its configuration and a successful preparation of a nonzero
amount; and a native asset whose outbound hook changes the ledger and whose inbound hook rejects
more than `bridgedOut`. -/
def Properties.L1TrackerHooksSatisfiable : Prop :=
  ∃ (thisChain : UInt256) (metadata : BridgedStandardERC20.State → UInt256 → Option Bytes)
    (s : State L1Ledger) (r : Request) (out : Result L1Ledger) (acc acc' : L1Ledger)
    (asset amount big : UInt256),
    WellFormed s ∧ L1LedgerAgrees thisChain s ∧ prepare (l1Hooks thisChain metadata) s r = some out ∧
    r.data.amount ≠ 0 ∧
    acc.originChainId asset = thisChain ∧ l1ToChain thisChain acc asset amount = some acc' ∧
    acc' ≠ acc ∧ (acc.bridgedOut asset).val < big.val ∧
    l1FromChain thisChain acc asset big = none

/-- **THE L2 HEADLINE'S PREMISES ARE SATISFIABLE, WITH A REGISTERED ASSET.**  A `WellFormed` state
whose tracker has the asset registered and a successful preparation of a nonzero amount to a
chain that is not L1. -/
def Properties.AtomicRecoveryL2Satisfiable : Prop :=
  ∃ (cfg : L2AssetTracker.Config) (metadata : BridgedStandardERC20.State → UInt256 → Option Bytes)
    (s : State L2Accounting) (r : Request) (out : Result L2Accounting),
    WellFormed s ∧ s.accounting.st.isAssetRegistered r.assetId = true ∧
    r.destinationChain ≠ s.accounting.st.l1ChainId ∧
    prepare (l2Hooks cfg metadata) s r = some out ∧ r.data.amount ≠ 0

end Contracts.NativeTokenVaultBase
