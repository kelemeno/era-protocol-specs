import EraSpec.Contracts.NativeTokenVaultBase.Specs.Resolution

/-!
# Properties: destination mint and failed-transfer recovery

Statements about `EraSpec.Contracts.NativeTokenVaultBase.Specs.Resolution`. Proofs are in
`EraSpec.Contracts.NativeTokenVaultBase.Proofs.Resolution`.

## Destination `bridgeMint` (registered bridged branch)

* `BridgeMintExact`: a successful mint passed the three entry checks, called the hook with
  the call's chain, asset and amount on the pre-mint token, and credited exactly `amount` to
  the data's `remoteReceiver` and to total supply, changing nothing else.
* `BridgeMintAssetBinding`: under `RepresentationConsistent`, the credited token is the
  registry's token for the call's asset id and records that asset id.
* `BridgeMintIgnoresUnreadFields`: the result does not depend on the data's
  `originalCaller`, `originToken` or metadata. On this branch the data's origin token is not
  checked; only the first bridge checks it (`FirstBridgeChecksOriginToken`).
* `BridgeMintPreservesWellFormed`, `BridgeMintEnabled`.

## Source `bridgeRecoverFailedTransfer` (registered bridged branch)

* `RecoverExact`: as `BridgeMintExact`, crediting the data's `originalCaller`.
* `RecoverIgnoresReceiver`: the result does not depend on the data's `remoteReceiver`,
  `originToken` or metadata.
* `RecoverPreservesWellFormed`, `RecoverEnabled`.

## Round trip

* `PrepareThenRecoverRestoresToken`: with no premise on the hooks, a recovery of a
  preparation's returned data restores the token ledger exactly (every balance, supply,
  identity).
* `PrepareThenRecoverEnabled`: that recovery is on the registered branch, passes its entry
  checks, and succeeds whenever the hook does.
* `PrepareThenRecoverRoundTrip`: under `HooksCancel`, prepare-then-recover returns the original
  state exactly, including accounting.
* `RoundTripNeedsCancellingHooks` (countermodel): with counting hooks the token is restored and
  the state is not.
* `RecoverAfterSpending`: ordinary transfers between preparation and recovery cannot block the
  refund or change its amount, and total supply returns to its starting value.
* `PrepareThenDeliverConserves`: for one transfer across two chains, the destination credits
  exactly what the source debited, and the sum of the two supplies is unchanged.
* `VaultHasNoReplayGuard` (limit): the same recovery, and the same destination mint, succeed
  twice; one-time resolution is the callers' job.

## Guards, rollback and limits

* `ResolutionWrongRouterRejected`, `ResolutionPausedRejected`, `ResolutionValueRejected`: the
  three modifiers, on both entry points.
* `ResolutionFailureAtomic`, `ResolutionHookFailureAtomic`, `MintRejectionRollsBackHook`: a
  failure commits nothing, including a hook update made before a rejected mint.
* `ZeroReceiverMintRejected`, `MintSupplyOverflowRejected`: the token-level conditions that can
  block a delivery.
* `ZeroReceiverOnlyRecoverable` (limit): preparation accepts a zero receiver, after which no
  modelled destination branch can mint the data, while recovery restores the source state.

## First bridge

* `FirstBridgeMintExact`: the asset id is checked against the data's origin token, and the
  fresh token holds exactly `amount` at the receiver.
* `FirstBridgeChecksOriginToken`, `FirstBridgeRejected`, `FirstBridgeEnabled`.
* `FirstBridgeEstablishesRegistered`: afterwards the asset is on the registered branch.

## Anti-vacuity

`ResolutionSatisfiable` meets, in one instance, the premises of the destination, source and
round-trip results (`BridgeMint…`, `Recover…` except `RecoverAfterSpending`,
`PrepareThenRecover…`), with hooks that satisfy `HooksCancel` without being the identity, a
nonzero amount, and a destination receiver different from the depositor.
`SpendingAndDeliverySatisfiable` meets those of `RecoverAfterSpending`, with a real transfer that
empties the depositor, and those of `PrepareThenDeliverConserves`.
`ResolutionRejectionsSatisfiable` meets every rejection premise with a call or state that differs
from a succeeding one in that single input, including a rejected mint whose hook would have
changed the accounting. `FirstBridgeSatisfiable` meets the premises of the first-bridge results,
with a mismatched origin token one input away. `RoundTripNeedsCancellingHooks`,
`ZeroReceiverOnlyRecoverable` and `VaultHasNoReplayGuard` are existence statements and are their
own witnesses.
-/

namespace Contracts.NativeTokenVaultBase

/-! ## Destination `bridgeMint` -/

/-- **EXACT DESTINATION CREDIT.** A successful `bridgeMint` passed its three entry checks and is
on the registered bridged branch. It called the chain-balance hook with the call's chain, asset
and amount on the PRE-mint token snapshot, and that call's result is the new accounting. The
mint is a genuine operation of the token model, with the vault as caller. The data's
`remoteReceiver` gains exactly `amount`, total supply rises by exactly `amount`, and every other
balance, the token's identity (vault, origin token, asset id), the vault's configuration, its
registry and its pause flag are unchanged. No invariant is assumed. -/
def Properties.BridgeMintExact : Prop :=
  ∀ (Accounting : Type) (rh : ResolutionHooks Accounting) (s t : State Accounting)
    (c : ResolutionCall),
    bridgeMint rh s c = some t →
      ResolveEntryAllowed s c ∧ RegisteredBridged s c ∧
      rh.fromChain s.accounting s.token c.chain c.assetId c.data.amount = some t.accounting ∧
      BridgedStandardERC20.mint s.token s.config.vault c.data.remoteReceiver c.data.amount =
        some t.token ∧
      t.token.balances c.data.remoteReceiver =
        s.token.balances c.data.remoteReceiver + c.data.amount.val ∧
      t.token.totalSupply = s.token.totalSupply + c.data.amount.val ∧
      (∀ a, a ≠ c.data.remoteReceiver → t.token.balances a = s.token.balances a) ∧
      t.token.config = s.token.config ∧
      t.config = s.config ∧ t.registry = s.registry ∧ t.paused = s.paused

/-- **THE CREDITED TOKEN IS THE CALL'S ASSET.** Under `RepresentationConsistent`, the token a
successful `bridgeMint` credits is the one the registry holds for the call's asset id, and it
records that asset id and this vault. The asset is fixed by the outer `_assetId`, not by the
data's `originToken`. -/
def Properties.BridgeMintAssetBinding : Prop :=
  ∀ (Accounting : Type) (rh : ResolutionHooks Accounting) (s t : State Accounting)
    (c : ResolutionCall),
    RepresentationConsistent s → bridgeMint rh s c = some t →
      s.registry.tokenForAsset c.assetId = s.config.tokenAddress ∧
      t.token.config.assetId = c.assetId ∧ t.token.config.vault = s.config.vault

/-- **`bridgeMint` READS ONLY THE RECEIVER AND THE AMOUNT FROM THE DATA.** For every input,
replacing the data's `originalCaller`, `originToken` and metadata leaves the result unchanged.
The data's origin token is decoded (`NTV:251`) but only the deploy branch (`NTV:253-255`) uses
it; on the registered branch nothing compares it with the token's own `originToken`. -/
def Properties.BridgeMintIgnoresUnreadFields : Prop :=
  ∀ (Accounting : Type) (rh : ResolutionHooks Accounting) (s : State Accounting)
    (c : ResolutionCall) (caller origin : Address) (metadata : Bytes),
    bridgeMint rh s
        { c with data := { c.data with originalCaller := caller, originToken := origin,
                                       metadata := metadata } } =
      bridgeMint rh s c

/-- **A DESTINATION MINT KEEPS THE VAULT WELL-FORMED.** Both the token ledger invariant (sum of
balances is supply, supply below `2^256`, zero address empty) and representation consistency. -/
def Properties.BridgeMintPreservesWellFormed : Prop :=
  ∀ (Accounting : Type) (rh : ResolutionHooks Accounting) (s t : State Accounting)
    (c : ResolutionCall),
    WellFormed s → bridgeMint rh s c = some t → WellFormed t

/-- **WHEN `bridgeMint` SUCCEEDS.** On a `RepresentationConsistent` state (so the token records
this vault as its minter), a call that passes the entry checks, is on the registered bridged
branch, names a nonzero receiver, keeps total supply below `2^256`, and whose hook succeeds,
succeeds. Nothing else is checked: no nonzero amount, no origin token, no metadata. -/
def Properties.BridgeMintEnabled : Prop :=
  ∀ (Accounting : Type) (rh : ResolutionHooks Accounting) (s : State Accounting)
    (c : ResolutionCall) (accounted : Accounting),
    RepresentationConsistent s → ResolveEntryAllowed s c → RegisteredBridged s c →
    c.data.remoteReceiver ≠ 0 →
    s.token.totalSupply + c.data.amount.val < UInt256.size →
    rh.fromChain s.accounting s.token c.chain c.assetId c.data.amount = some accounted →
      ∃ t, bridgeMint rh s c = some t

/-! ## Source `bridgeRecoverFailedTransfer` -/

/-- **EXACT REFUND TO THE DEPOSITOR.** As `BridgeMintExact`, but the credited account is the
data's `originalCaller`: it gains exactly `amount`, supply rises by exactly `amount`, and every
other account, in particular a `remoteReceiver` different from it, is unchanged. -/
def Properties.RecoverExact : Prop :=
  ∀ (Accounting : Type) (rh : ResolutionHooks Accounting) (s t : State Accounting)
    (c : ResolutionCall),
    bridgeRecoverFailedTransfer rh s c = some t →
      ResolveEntryAllowed s c ∧ RegisteredBridged s c ∧
      rh.fromChain s.accounting s.token c.chain c.assetId c.data.amount = some t.accounting ∧
      BridgedStandardERC20.mint s.token s.config.vault c.data.originalCaller c.data.amount =
        some t.token ∧
      t.token.balances c.data.originalCaller =
        s.token.balances c.data.originalCaller + c.data.amount.val ∧
      t.token.totalSupply = s.token.totalSupply + c.data.amount.val ∧
      (∀ a, a ≠ c.data.originalCaller → t.token.balances a = s.token.balances a) ∧
      t.token.config = s.token.config ∧
      t.config = s.config ∧ t.registry = s.registry ∧ t.paused = s.paused

/-- **RECOVERY IGNORES THE REMOTE RECEIVER.** For every input, replacing the data's
`remoteReceiver`, `originToken` and metadata leaves the result unchanged (`NTV:219-220` decodes
the receiver into an unnamed slot). -/
def Properties.RecoverIgnoresReceiver : Prop :=
  ∀ (Accounting : Type) (rh : ResolutionHooks Accounting) (s : State Accounting)
    (c : ResolutionCall) (receiver origin : Address) (metadata : Bytes),
    bridgeRecoverFailedTransfer rh s
        { c with data := { c.data with remoteReceiver := receiver, originToken := origin,
                                       metadata := metadata } } =
      bridgeRecoverFailedTransfer rh s c

def Properties.RecoverPreservesWellFormed : Prop :=
  ∀ (Accounting : Type) (rh : ResolutionHooks Accounting) (s t : State Accounting)
    (c : ResolutionCall),
    WellFormed s → bridgeRecoverFailedTransfer rh s c = some t → WellFormed t

/-- **WHEN `bridgeRecoverFailedTransfer` SUCCEEDS.** As `BridgeMintEnabled`, with the data's
`originalCaller` as the recipient. -/
def Properties.RecoverEnabled : Prop :=
  ∀ (Accounting : Type) (rh : ResolutionHooks Accounting) (s : State Accounting)
    (c : ResolutionCall) (accounted : Accounting),
    RepresentationConsistent s → ResolveEntryAllowed s c → RegisteredBridged s c →
    c.data.originalCaller ≠ 0 →
    s.token.totalSupply + c.data.amount.val < UInt256.size →
    rh.fromChain s.accounting s.token c.chain c.assetId c.data.amount = some accounted →
      ∃ t, bridgeRecoverFailedTransfer rh s c = some t

/-! ## Round trip: preparation, then recovery of its returned data -/

/-- **RECOVERY UNDOES THE BURN EXACTLY, WHATEVER THE HOOKS DO.** After a successful preparation
`prepare hooks s r = some out` on a state satisfying the ledger invariant, a successful router
recovery of the returned data leaves the token exactly as it was before the preparation: every
balance, the total supply and the token's identity. Configuration, registry and pause flag are
those of `s` as well. The accounting is the resolution hook applied to the preparation hook's
result, both with the burn's destination chain, asset and amount. -/
def Properties.PrepareThenRecoverRestoresToken : Prop :=
  ∀ (Accounting : Type) (hooks : Hooks Accounting) (rh : ResolutionHooks Accounting)
    (s : State Accounting) (r : Request) (out : Result Accounting) (router : Address)
    (t : State Accounting),
    LedgerInvariant s → prepare hooks s r = some out →
    bridgeRecoverFailedTransfer rh out.state (recoveryCall router r out.data) = some t →
      t.token = s.token ∧ t.config = s.config ∧ t.registry = s.registry ∧
      t.paused = s.paused ∧
      hooks.account s.accounting s.token r.destinationChain r.assetId r.data.amount =
        some out.state.accounting ∧
      rh.fromChain out.state.accounting out.state.token r.destinationChain r.assetId
        r.data.amount = some t.accounting

/-- **NOTHING BUT THE HOOK CAN BLOCK THAT RECOVERY.** After a successful preparation on a
`WellFormed` state, the router's recovery call for the returned data passes all three entry
checks (the preparation left the vault unpaused), is on the registered bridged branch (so
recovery's deploy branch, `NTV:301-303`, is not taken), and succeeds whenever the resolution hook
does: the depositor is nonzero, the vault is the token's minter, and the re-mint fits under the
supply bound because the burn freed that much. -/
def Properties.PrepareThenRecoverEnabled : Prop :=
  ∀ (Accounting : Type) (hooks : Hooks Accounting) (rh : ResolutionHooks Accounting)
    (s : State Accounting) (r : Request) (out : Result Accounting) (accounted : Accounting),
    WellFormed s → prepare hooks s r = some out →
    rh.fromChain out.state.accounting out.state.token r.destinationChain r.assetId
      r.data.amount = some accounted →
      ResolveEntryAllowed out.state (recoveryCall s.config.router r out.data) ∧
      RegisteredBridged out.state (recoveryCall s.config.router r out.data) ∧
      ∃ t, bridgeRecoverFailedTransfer rh out.state (recoveryCall s.config.router r out.data) =
        some t

/-- **ROUND TRIP.** Under `HooksCancel`, the router's recovery of a preparation's returned data
succeeds and returns exactly the state before the preparation: the depositor's balance, total
supply, every other balance, the token's identity, the registry, the pause flag and the
accounting. Through the commit interfaces: committing the preparation and then the recovery
yields the original state, and the recovery reports success. -/
def Properties.PrepareThenRecoverRoundTrip : Prop :=
  ∀ (Accounting : Type) (hooks : Hooks Accounting) (rh : ResolutionHooks Accounting)
    (s : State Accounting) (r : Request) (out : Result Accounting),
    HooksCancel hooks rh → WellFormed s → prepare hooks s r = some out →
      bridgeRecoverFailedTransfer rh out.state (recoveryCall s.config.router r out.data) =
        some s ∧
      recoverTransact rh (transact hooks s r).1 (recoveryCall s.config.router r out.data) =
        (s, true)

/-- **SPENDING CANNOT BLOCK OR SHRINK THE REFUND.** After a successful preparation on a
`WellFormed` state and any sequence of ordinary transfers (`SpendReach`), the router's recovery of
the returned data is still on the registered branch and passes its entry checks; given the hook,
it succeeds; the depositor gains exactly `amount` over whatever it holds at that moment; total
supply is back to its value before the preparation; and the result is `WellFormed`. -/
def Properties.RecoverAfterSpending : Prop :=
  ∀ (Accounting : Type) (hooks : Hooks Accounting) (rh : ResolutionHooks Accounting)
    (s : State Accounting) (r : Request) (out : Result Accounting) (u : State Accounting)
    (accounted : Accounting),
    WellFormed s → prepare hooks s r = some out → SpendReach out.state u →
    rh.fromChain u.accounting u.token r.destinationChain r.assetId r.data.amount =
      some accounted →
      ResolveEntryAllowed u (recoveryCall s.config.router r out.data) ∧
      RegisteredBridged u (recoveryCall s.config.router r out.data) ∧
      ∃ t, bridgeRecoverFailedTransfer rh u (recoveryCall s.config.router r out.data) = some t ∧
        t.token.balances r.depositor = u.token.balances r.depositor + r.data.amount.val ∧
        t.token.totalSupply = s.token.totalSupply ∧ WellFormed t

/-- **ONE TRANSFER, TWO CHAINS: WHAT THE SOURCE BURNS, THE DESTINATION MINTS.** A successful
preparation on a source state satisfying the ledger invariant, and a successful destination
`bridgeMint` of the returned data (any destination state, chain and asset id): the destination
credits the request's receiver with exactly the amount the source debited from the depositor,
and the sum of the two total supplies is unchanged. Which destination and asset the data is
delivered to is the router's and the interop layer's binding, not the vault's. -/
def Properties.PrepareThenDeliverConserves : Prop :=
  ∀ (A B : Type) (hooks : Hooks A) (rh : ResolutionHooks B) (s : State A) (r : Request)
    (out : Result A) (d d' : State B) (c : ResolutionCall),
    LedgerInvariant s → prepare hooks s r = some out → c.data = out.data →
    bridgeMint rh d c = some d' →
      d'.token.balances r.data.receiver = d.token.balances r.data.receiver + r.data.amount.val ∧
      out.state.token.balances r.depositor + r.data.amount.val = s.token.balances r.depositor ∧
      out.state.token.totalSupply + d'.token.totalSupply =
        s.token.totalSupply + d.token.totalSupply

/-- **LIMIT: THE VAULT IS NOT A REPLAY GUARD.** The vault keeps no record of resolved data. On a
`WellFormed` state, with hooks satisfying `HooksCancel`, a preparation is followed by two
successful router recoveries of the same returned data: the depositor ends with `amount` MORE
than before the preparation, and total supply exceeds its starting value by `amount`. The same
destination `bridgeMint` call also succeeds twice in a row. One-time resolution has to come from
the callers (the interop handler's bundle status, the atomic flow manager's leg state). -/
def Properties.VaultHasNoReplayGuard : Prop :=
  ∃ (hooks : Hooks ℕ) (rh : ResolutionHooks ℕ) (s : State ℕ) (r : Request) (out : Result ℕ)
    (t t' : State ℕ),
    WellFormed s ∧ HooksCancel hooks rh ∧ prepare hooks s r = some out ∧ r.data.amount ≠ 0 ∧
    bridgeRecoverFailedTransfer rh out.state (recoveryCall s.config.router r out.data) = some t ∧
    bridgeRecoverFailedTransfer rh t (recoveryCall s.config.router r out.data) = some t' ∧
    t'.token.balances r.depositor = s.token.balances r.depositor + r.data.amount.val ∧
    t'.token.totalSupply = s.token.totalSupply + r.data.amount.val ∧
    ∃ (c : ResolutionCall) (d d' : State ℕ),
      bridgeMint rh s c = some d ∧ bridgeMint rh d c = some d' ∧ c.data.amount ≠ 0 ∧
      d'.token.balances c.data.remoteReceiver =
        s.token.balances c.data.remoteReceiver + 2 * c.data.amount.val

/-- **COUNTERMODEL: WITHOUT CANCELLING HOOKS THE ROUND TRIP DOES NOT RESTORE THE VAULT.** Hooks
that record outflow and inflow in two separate counters (the pattern of the L2 asset tracker's
`totalWithdrawalsToL1` and `totalSuccessfulDepositsFromL1`, `L2AssetTracker.sol:244-249,
299-304`, for an L1 destination while settling on L1) violate `HooksCancel`. On a `WellFormed`
state a preparation and the router's recovery of its data both succeed; the token ledger is
restored exactly, and the state is not. -/
def Properties.RoundTripNeedsCancellingHooks : Prop :=
  ∃ (hooks : Hooks (ℕ × ℕ)) (rh : ResolutionHooks (ℕ × ℕ)) (s : State (ℕ × ℕ)) (r : Request)
    (out : Result (ℕ × ℕ)) (t : State (ℕ × ℕ)),
    ¬ HooksCancel hooks rh ∧ WellFormed s ∧ prepare hooks s r = some out ∧
    bridgeRecoverFailedTransfer rh out.state (recoveryCall s.config.router r out.data) = some t ∧
    t.token = s.token ∧ t ≠ s

/-! ## Guards and rollback -/

/-- **ONLY THE ROUTER RESOLVES** (`onlyAssetRouter`, `NTV:107-110`). -/
def Properties.ResolutionWrongRouterRejected : Prop :=
  ∀ (Accounting : Type) (rh : ResolutionHooks Accounting) (s : State Accounting)
    (c : ResolutionCall),
    c.caller ≠ s.config.router →
      bridgeMint rh s c = none ∧ bridgeRecoverFailedTransfer rh s c = none

/-- **NOTHING RESOLVES WHILE PAUSED** (`whenNotPaused`). -/
def Properties.ResolutionPausedRejected : Prop :=
  ∀ (Accounting : Type) (rh : ResolutionHooks Accounting) (s : State Accounting)
    (c : ResolutionCall),
    s.paused = true →
      bridgeMint rh s c = none ∧ bridgeRecoverFailedTransfer rh s c = none

/-- **NO NATIVE VALUE** (`requireZeroValue(msg.value)`; the router forwards its `msg.value`,
`AssetRouterBase.sol:284, 290`). -/
def Properties.ResolutionValueRejected : Prop :=
  ∀ (Accounting : Type) (rh : ResolutionHooks Accounting) (s : State Accounting)
    (c : ResolutionCall),
    c.msgValue ≠ 0 →
      bridgeMint rh s c = none ∧ bridgeRecoverFailedTransfer rh s c = none

/-- **A FAILED RESOLUTION COMMITS NOTHING.** -/
def Properties.ResolutionFailureAtomic : Prop :=
  ∀ (Accounting : Type) (rh : ResolutionHooks Accounting) (s : State Accounting)
    (c : ResolutionCall),
    (bridgeMint rh s c = none → mintTransact rh s c = (s, false)) ∧
    (bridgeRecoverFailedTransfer rh s c = none → recoverTransact rh s c = (s, false))

/-- **A FAILED HOOK MINTS NOTHING.** The hook runs before the mint, and its failure fails the
call with no effect on the token or the accounting. -/
def Properties.ResolutionHookFailureAtomic : Prop :=
  ∀ (Accounting : Type) (rh : ResolutionHooks Accounting) (s : State Accounting)
    (c : ResolutionCall),
    rh.fromChain s.accounting s.token c.chain c.assetId c.data.amount = none →
      mintTransact rh s c = (s, false) ∧ recoverTransact rh s c = (s, false)

/-- **A REJECTED MINT ROLLS BACK THE HOOK.** If the token rejects the mint (zero recipient,
supply overflow, caller not its vault), the call commits nothing, even when the hook had already
produced a new accounting state. -/
def Properties.MintRejectionRollsBackHook : Prop :=
  ∀ (Accounting : Type) (rh : ResolutionHooks Accounting) (s : State Accounting)
    (c : ResolutionCall),
    (BridgedStandardERC20.mint s.token s.config.vault c.data.remoteReceiver c.data.amount = none →
      mintTransact rh s c = (s, false)) ∧
    (BridgedStandardERC20.mint s.token s.config.vault c.data.originalCaller c.data.amount = none →
      recoverTransact rh s c = (s, false))

/-- **THE ZERO RECEIVER IS NEVER PAID.** On the registered bridged branch, `bridgeMint` with
`remoteReceiver = 0` fails for every state and hook: the token rejects minting to the zero
address. -/
def Properties.ZeroReceiverMintRejected : Prop :=
  ∀ (Accounting : Type) (rh : ResolutionHooks Accounting) (s : State Accounting)
    (c : ResolutionCall),
    RegisteredBridged s c → c.data.remoteReceiver = 0 → bridgeMint rh s c = none

/-- **SUPPLY OVERFLOW BLOCKS RESOLUTION.** On the registered bridged branch, a mint or refund that
would take total supply to `2^256` or beyond fails. -/
def Properties.MintSupplyOverflowRejected : Prop :=
  ∀ (Accounting : Type) (rh : ResolutionHooks Accounting) (s : State Accounting)
    (c : ResolutionCall),
    RegisteredBridged s c → UInt256.size ≤ s.token.totalSupply + c.data.amount.val →
      bridgeMint rh s c = none ∧ bridgeRecoverFailedTransfer rh s c = none

/-- **LIMIT: A PREPARED TRANSFER TO THE ZERO RECEIVER CAN ONLY BE RECOVERED.** Preparation never
checks the receiver; it only copies it into the returned data (`NTV:330, 336, 415-421`; the
router's `_burn`, `AssetRouterBase.sol:313-346`, does not check it either). There is a
`WellFormed` state and a successful
preparation whose returned data names receiver `0`. No destination on the registered bridged
branch, whatever its state and hooks, can mint that data, and neither can a first bridge. The
router's recovery of the same data succeeds and restores the source state exactly. -/
def Properties.ZeroReceiverOnlyRecoverable : Prop :=
  ∃ (hooks : Hooks ℕ) (rh : ResolutionHooks ℕ) (s : State ℕ) (r : Request) (out : Result ℕ),
    WellFormed s ∧ prepare hooks s r = some out ∧ out.data.remoteReceiver = 0 ∧
    (∀ (A : Type) (rh' : ResolutionHooks A) (d : State A) (c : ResolutionCall),
      c.data = out.data → RegisteredBridged d c → bridgeMint rh' d c = none) ∧
    (∀ (A : Type) (reg : RegistrationHooks A) (rh' : ResolutionHooks A)
      (d : RegistrationState A) (c : ResolutionCall),
      c.data = out.data → bridgeMintFirst reg rh' d c = none) ∧
    bridgeRecoverFailedTransfer rh out.state (recoveryCall s.config.router r out.data) = some s

/-! ## First bridge -/

/-- **FIRST BRIDGE: THE DATA'S ORIGIN TOKEN IS CHECKED, AND THE NEW TOKEN HOLDS EXACTLY THE
AMOUNT.** A successful first-bridge `bridgeMint` passed the entry checks, started at an unset
`tokenAddress` slot, and checked the call's asset id against the encoding of the resolved origin
chain and the DATA's origin token (`assetIdCheck`, `NTV:580`). Its result is `WellFormed`; its
token is the fresh representation of that origin token for the call's asset id, minted by this
vault, holding exactly `amount` at the receiver and nothing elsewhere; the registry is installed
for the asset. The hook ran after registration, on the freshly initialized token. -/
def Properties.FirstBridgeMintExact : Prop :=
  ∀ (Accounting : Type) (reg : RegistrationHooks Accounting) (rh : ResolutionHooks Accounting)
    (s : RegistrationState Accounting) (c : ResolutionCall) (t : State Accounting),
    bridgeMintFirst reg rh s c = some t →
      FirstEntryAllowed s c ∧ FirstBridge s c ∧
      s.registry.tokenForAsset s.config.assetId = 0 ∧
      c.assetId = reg.assetIdFor s.config.originChainId c.data.originToken ∧
      t.token.config = ⟨s.config.vault, c.data.originToken, c.assetId⟩ ∧
      t.token.balances c.data.remoteReceiver = c.data.amount.val ∧
      t.token.totalSupply = c.data.amount.val ∧
      (∀ a, a ≠ c.data.remoteReceiver → t.token.balances a = 0) ∧
      t.config = s.config ∧ t.paused = s.paused ∧
      t.registry = installRegistry s.registry s.config.assetId s.config.tokenAddress ∧
      WellFormed t ∧
      ∃ registered : Registered Accounting,
        registerFreshBranch reg s c.data.originToken = some registered ∧
        registered.state.token = registeredToken s.config c.data.originToken ∧
        rh.fromChain registered.state.accounting registered.state.token c.chain c.assetId
          c.data.amount = some t.accounting

/-- **ON THE FIRST BRIDGE A MISMATCHED ORIGIN TOKEN IS REJECTED.** If the call's asset id is not
the encoding of the resolved origin chain and the data's origin token, the first bridge fails.
Compare `BridgeMintIgnoresUnreadFields`: once the token is registered the data's origin token is
not read at all. -/
def Properties.FirstBridgeChecksOriginToken : Prop :=
  ∀ (Accounting : Type) (reg : RegistrationHooks Accounting) (rh : ResolutionHooks Accounting)
    (s : RegistrationState Accounting) (c : ResolutionCall),
    c.assetId ≠ reg.assetIdFor s.config.originChainId c.data.originToken →
      bridgeMintFirst reg rh s c = none

/-- **THE FIRST BRIDGE'S GUARDS.** A wrong caller, a paused vault, nonzero value, or a zero
receiver (the deploy happens, then the mint to `0` fails and the whole call with it) each make
the first bridge fail. -/
def Properties.FirstBridgeRejected : Prop :=
  ∀ (Accounting : Type) (reg : RegistrationHooks Accounting) (rh : ResolutionHooks Accounting)
    (s : RegistrationState Accounting) (c : ResolutionCall),
    c.caller ≠ s.config.router ∨ s.paused = true ∨ c.msgValue ≠ 0 ∨ c.data.remoteReceiver = 0 →
      bridgeMintFirst reg rh s c = none

/-- **WHEN THE FIRST BRIDGE SUCCEEDS.** Entry checks, the unset slot, a matching asset id, a
foreign resolved origin chain, a nonzero origin token, successful metadata setup, a deployment at
the expected address, successful tracker registration and hook, and a nonzero receiver. -/
def Properties.FirstBridgeEnabled : Prop :=
  ∀ (Accounting : Type) (reg : RegistrationHooks Accounting) (rh : ResolutionHooks Accounting)
    (s : RegistrationState Accounting) (c : ResolutionCall) (tracked accounted : Accounting),
    FirstEntryAllowed s c → FirstBridge s c →
    s.registry.tokenForAsset s.config.assetId = 0 →
    s.config.assetId = reg.assetIdFor s.config.originChainId c.data.originToken →
    s.config.originChainId ≠ s.config.chainId → c.data.originToken ≠ 0 →
    reg.metadataDecoded = true →
    reg.deploy s.config.originChainId c.data.originToken = some s.config.tokenAddress →
    reg.registerTracker s.accounting
        (installRegistry s.registry s.config.assetId s.config.tokenAddress)
        (registeredToken s.config c.data.originToken) s.config.assetId s.config.originChainId =
      some tracked →
    c.data.remoteReceiver ≠ 0 →
    rh.fromChain tracked (registeredToken s.config c.data.originToken) c.chain c.assetId
      c.data.amount = some accounted →
      ∃ t, bridgeMintFirst reg rh s c = some t

/-- **AFTER THE FIRST BRIDGE THE ASSET IS ON THE REGISTERED BRANCH.** With a nonzero deployed
address (CREATE2 never yields `0`; `VM-DEPLOY`), the state a first bridge produces is
`WellFormed`, and every later call naming the same asset is on the registered bridged branch, so
`bridgeMint` and `bridgeRecoverFailedTransfer` above describe it. -/
def Properties.FirstBridgeEstablishesRegistered : Prop :=
  ∀ (Accounting : Type) (reg : RegistrationHooks Accounting) (rh : ResolutionHooks Accounting)
    (s : RegistrationState Accounting) (c c' : ResolutionCall) (t : State Accounting),
    s.config.tokenAddress ≠ 0 → bridgeMintFirst reg rh s c = some t → c'.assetId = c.assetId →
      WellFormed t ∧ RegisteredBridged t c'

/-! ## Anti-vacuity -/

/-- **THE RESOLUTION PREMISES ARE JOINTLY SATISFIABLE, NONTRIVIALLY.** One `WellFormed` state,
hooks that satisfy `HooksCancel` and are not the identity, a successful preparation of a nonzero
amount whose hook changes the accounting, the router's recovery of its data returning exactly
the original state, and a successful `bridgeMint` of a nonzero amount to a receiver other than
the depositor whose hook also changes the accounting. -/
def Properties.ResolutionSatisfiable : Prop :=
  ∃ (hooks : Hooks ℕ) (rh : ResolutionHooks ℕ) (s : State ℕ) (r : Request) (out : Result ℕ)
    (c : ResolutionCall) (t : State ℕ),
    HooksCancel hooks rh ∧ WellFormed s ∧ prepare hooks s r = some out ∧
    r.data.amount ≠ 0 ∧ out.state.accounting ≠ s.accounting ∧
    bridgeRecoverFailedTransfer rh out.state (recoveryCall s.config.router r out.data) =
      some s ∧
    bridgeMint rh s c = some t ∧ c.data.amount ≠ 0 ∧ c.data.remoteReceiver ≠ r.depositor ∧
    t.accounting ≠ s.accounting

/-- **THE SPENDING AND TWO-CHAIN PREMISES ARE SATISFIABLE, NONTRIVIALLY.** After a successful
preparation on a `WellFormed` state, the depositor transfers its whole remaining balance away
(`SpendReach` by a transfer that changes the token), and the recovery hook succeeds there; and a
destination `bridgeMint` of the returned data succeeds. -/
def Properties.SpendingAndDeliverySatisfiable : Prop :=
  ∃ (hooks : Hooks ℕ) (rh : ResolutionHooks ℕ) (s : State ℕ) (r : Request) (out : Result ℕ)
    (u : State ℕ) (accounted : ℕ) (c : ResolutionCall) (d d' : State ℕ),
    WellFormed s ∧ prepare hooks s r = some out ∧ r.data.amount ≠ 0 ∧ SpendReach out.state u ∧
    u.token ≠ out.state.token ∧ u.token.balances r.depositor = 0 ∧
    rh.fromChain u.accounting u.token r.destinationChain r.assetId r.data.amount =
      some accounted ∧
    c.data = out.data ∧ bridgeMint rh d c = some d'

/-- **EACH REJECTION PREMISE IS MET ONE INPUT AWAY FROM A SUCCESS.** On a `WellFormed` state with
a call that `bridgeMint` and `bridgeRecoverFailedTransfer` both accept: changing only the caller,
only the pause flag, or only the value makes both fail; changing only the receiver to `0` keeps
the call on the registered branch and makes `bridgeMint` fail, although its hook would have moved
the accounting, which the commit then discards; changing only the accounting to `0` makes the
hook fail and the call commit nothing; and on a `WellFormed` state whose supply is `2^256 - 1`
the same branch overflows. -/
def Properties.ResolutionRejectionsSatisfiable : Prop :=
  ∃ (rh : ResolutionHooks ℕ) (s : State ℕ) (c : ResolutionCall) (t : State ℕ) (x : Address),
    WellFormed s ∧ bridgeMint rh s c = some t ∧ bridgeRecoverFailedTransfer rh s c ≠ none ∧
    x ≠ s.config.router ∧
    bridgeMint rh s { c with caller := x } = none ∧
    bridgeRecoverFailedTransfer rh s { c with caller := x } = none ∧
    bridgeMint rh { s with paused := true } c = none ∧
    bridgeRecoverFailedTransfer rh { s with paused := true } c = none ∧
    bridgeMint rh s { c with msgValue := 1 } = none ∧
    bridgeRecoverFailedTransfer rh s { c with msgValue := 1 } = none ∧
    RegisteredBridged s { c with data := { c.data with remoteReceiver := 0 } } ∧
    bridgeMint rh s { c with data := { c.data with remoteReceiver := 0 } } = none ∧
    rh.fromChain s.accounting s.token c.chain c.assetId c.data.amount ≠ some s.accounting ∧
    rh.fromChain s.accounting s.token c.chain c.assetId c.data.amount ≠ none ∧
    mintTransact rh s { c with data := { c.data with remoteReceiver := 0 } } = (s, false) ∧
    rh.fromChain 0 s.token c.chain c.assetId c.data.amount = none ∧
    mintTransact rh { s with accounting := 0 } c = ({ s with accounting := 0 }, false) ∧
    ∃ s' : State ℕ, WellFormed s' ∧ RegisteredBridged s' c ∧ ResolveEntryAllowed s' c ∧
      UInt256.size ≤ s'.token.totalSupply + c.data.amount.val

/-- **THE FIRST-BRIDGE PREMISES ARE SATISFIABLE.** A registration state with a nonzero expected
address and a call on which the first bridge succeeds with a nonzero amount; and, one input
away each, an origin token whose encoding does not match the call's asset id, and the zero
receiver, on which the same first bridge fails. -/
def Properties.FirstBridgeSatisfiable : Prop :=
  ∃ (reg : RegistrationHooks ℕ) (rh : ResolutionHooks ℕ) (s : RegistrationState ℕ)
    (c : ResolutionCall) (t : State ℕ) (o : Address),
    s.config.tokenAddress ≠ 0 ∧ bridgeMintFirst reg rh s c = some t ∧ c.data.amount ≠ 0 ∧
    c.assetId ≠ reg.assetIdFor s.config.originChainId o ∧
    bridgeMintFirst reg rh s { c with data := { c.data with originToken := o } } = none ∧
    bridgeMintFirst reg rh s { c with data := { c.data with remoteReceiver := 0 } } = none

end Contracts.NativeTokenVaultBase
