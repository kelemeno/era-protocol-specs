import EraSpec.Contracts.NativeTokenVaultBase.Specs.Initialization

/-!
# Resolution: destination `bridgeMint` and source `bridgeRecoverFailedTransfer`

Local specification of the two `NativeTokenVaultBase` entry points that resolve a
prepared transfer, at source pin `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`
(`l1-contracts/contracts/bridge/ntv/NativeTokenVaultBase.sol`, cited below as `NTV`).
It is built on the representation model's `State` (`Specs/RepresentationPreparation.lean`)
and the token ledger (`BridgedStandardERC20/Specs/Model.lean`); the first-bridge branch
is built on the registration projection (`Specs/Initialization.lean`).

## What the source does

* `bridgeMint(_chainId, _assetId, _data)` (`NTV:193-205`) carries the modifiers
  `requireZeroValue(msg.value) onlyAssetRouter whenNotPaused` (`NTV:197`;
  `bridge/interfaces/AssetHandlerModifiers.sol:11-16`, `NTV:107-110`) and calls
  `_bridgeMintToken` (`NTV:240-267`). That reads `_isBridgedToken =
  originChainId[_assetId] != block.chainid` (`:245`) and `token = tokenAddress[_assetId]`
  (`:247`), decodes `(_, receiver, originToken, amount, erc20Data)` (`:251`), deploys the
  token if it is bridged and `token == 0` (`:253-255`), calls the chain-balance hook
  `_handleBridgeFromChain(_chainId, _assetId, amount)` (`:260`), and then, for a bridged
  token, `IBridgedStandardToken(token).bridgeMint(receiver, amount)` (`:262-263`).
* `bridgeRecoverFailedTransfer(_chainId, _assetId, _data)` (`NTV:213-233`) carries the
  same three modifiers (`:217`), decodes `(originalCaller, _, originToken, amount,
  erc20Data)` (`:219-220`), and calls `_disburseFailedTransfer` with
  `_receiver: originalCaller` (`:222-230`). That calls the same hook first (`:296`) and
  then, for a bridged asset, re-mints to the receiver (`:300-304`), deploying the token
  first if `tokenAddress[_assetId] == 0` (`:301-303`).
* `L2AssetRouter.recoverAtomicCall` (`bridge/asset-router/L2AssetRouter.sol:281-296`)
  forwards the bundle's mint data verbatim and passes the burn-time destination chain as
  `_chainId`. `recoveryCall` below is that call.

## The modelled branches

* **Registered bridged representation** (`RegisteredBridged`): the call names the
  tracked asset, which is not native to this chain, whose `tokenAddress` entry is set and
  is the tracked token, with a nonzero vault (the token's nonlegacy `onlyNTV` branch,
  `bridge/BridgedStandardERC20.sol:52-64`). On this branch both entry points are: entry
  checks, hook, mint (`hookThenMint`). `RegisteredBridged` SELECTS the branch the model
  represents; it is not a production guard, and a `none` for a call outside it is not a
  claim that the source reverts (native assets release escrow via `_withdrawFunds`,
  `NTV:264-266, 297-298`, which is not modelled here).
* **First bridge** (`bridgeMintFirst`): `bridgeMint` when `tokenAddress[_assetId]` is
  unset. `_ensureAndSaveTokenDeployed` (`NTV:538-552`) checks
  `assetIdCheck(tokenOriginChainId, _assetId, originToken)` (`:580`), deploys and
  initializes the representation (`:582`, `:620-633`), checks the address (`:583`) and
  installs the registry (`:585`, `:588-598`) — exactly the registration projection
  `registerFreshBranch`, applied with the DATA's origin token. The origin chain and
  expected address that `_calculateExpectedTokenAddress` derives from `erc20Data`
  (`NTV:555-571`) are the registration state's `config.originChainId` and
  `config.tokenAddress`; that decoding is not modelled. Recovery's own deploy branch
  (`NTV:301-303`) is not modelled: after a preparation of the same asset the token is
  registered, so it is not taken (`Properties.PrepareThenRecoverEnabled`).

## Dependencies and boundaries

* The chain-balance hook `_handleBridgeFromChain` (`NTV:532`; L2 implementation
  `bridge/ntv/L2NativeTokenVault.sol:304-315`, L1 `bridge/ntv/L1NativeTokenVault.sol:270-277`)
  is a parameter, `ResolutionHooks.fromChain`, as the preparation hook is. It sees the
  PRE-mint token snapshot, which is how "before the mint" is represented, and it may
  fail. Its interface confines writes to `Accounting` (`DEP-FRAME`).
* `HooksCancel` is the law under which a recovery undoes a preparation's hook. It is a
  premise, not a fact about the deployed trackers: the L2 asset tracker counts
  `totalWithdrawalsToL1` on the way out and `totalSuccessfulDepositsFromL1` on the way
  in when the other chain is L1 and the settlement layer is L1
  (`bridge/asset-tracker/L2AssetTracker.sol:244-249, 299-304`): a round trip moves both
  counters by the same amount, so their difference is kept but neither is restored. Its
  first-touch legacy registration (`:292`, `:342-353`) also persists. Whether an atomic
  recovery can name L1 as the burn's destination is not examined here.
  `Properties.RoundTripNeedsCancellingHooks` is that counter pattern as a countermodel. For a
  bridged (non-native) asset on L1 both hooks are no-ops (`L1NativeTokenVault.sol:260-277` only
  touch native assets), so they cancel.
* `_data` is the typed `MintData` tuple; `DataEncoding.decodeBridgeMintData`
  (`common/libraries/DataEncoding.sol:102-118`) and its decoding failures are not
  modelled (`SOL-ABI`). Events (`NTV:204, 232`) are not modelled.
* Each operation returns `Option`; `commitResolution` keeps only a successful result,
  which models atomic rollback (`MODEL-COMMIT`), not EVM semantics (`VM-REVERT`).
* The vault calls the token with its own address `config.vault` as `msg.sender`
  (`VM-CALL`). The token's guards are those of `BridgedStandardERC20.mint`: caller is
  the token's configured vault, nonzero recipient, supply stays below `2^256`
  (OpenZeppelin v4 `ERC20Upgradeable._mint`).
-/

namespace Contracts.NativeTokenVaultBase

/-- The inputs of `bridgeMint(_chainId, _assetId, _data)` and
`bridgeRecoverFailedTransfer(_chainId, _assetId, _data)` (`NTV:193-197, 213-217`), with
`_data` already decoded into the typed mint-data tuple. -/
structure ResolutionCall where
  /-- `msg.sender`; `onlyAssetRouter` requires the router. -/
  caller : Address
  /-- `msg.value`; `requireZeroValue(msg.value)` requires zero. -/
  msgValue : UInt256
  /-- `_chainId`: for `bridgeMint` the chain the message came from; for recovery the
  destination chain the burn was prepared for. -/
  chain : UInt256
  /-- `_assetId`. -/
  assetId : UInt256
  /-- `_data`, decoded: `(originalCaller, remoteReceiver, originToken, amount, erc20Data)`. -/
  data : MintData

structure ResolutionHooks (Accounting : Type) where
  /-- `_handleBridgeFromChain(_chainId, _assetId, _amount)`: the accounting successor, or
  failure, computed on the PRE-mint token snapshot. -/
  fromChain : Accounting → BridgedStandardERC20.State → UInt256 → UInt256 → UInt256 →
    Option Accounting

variable {Accounting : Type}

/-- The three modifiers both entry points carry: `requireZeroValue(msg.value)`,
`onlyAssetRouter`, `whenNotPaused` (`NTV:197, 217`). -/
def ResolveEntryAllowed (s : State Accounting) (c : ResolutionCall) : Prop :=
  c.msgValue = 0 ∧ c.caller = s.config.router ∧ s.paused = false

/-- Branch selection, not a guard: the call names the tracked asset; it is not native here
(`originChainId[_assetId] != block.chainid`, `NTV:245`, `:221`); its `tokenAddress` entry
(`NTV:247`, `:300`) is the tracked token and is set; the vault address is nonzero. -/
def RegisteredBridged (s : State Accounting) (c : ResolutionCall) : Prop :=
  s.config.vault ≠ 0 ∧ c.assetId = s.config.assetId ∧
  s.config.originChainId ≠ s.config.chainId ∧
  s.registry.tokenForAsset c.assetId = s.config.tokenAddress ∧ s.config.tokenAddress ≠ 0

instance (s : State Accounting) (c : ResolutionCall) : Decidable (ResolveEntryAllowed s c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (s : State Accounting) (c : ResolutionCall) : Decidable (RegisteredBridged s c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The common tail of `_bridgeMintToken` (`NTV:260-263`) and `_disburseFailedTransfer`
(`NTV:296, 300-304`) on the registered bridged branch: the chain-balance hook on the
pre-mint snapshot, then `IBridgedStandardToken(token).bridgeMint(recipient, amount)` with the
vault as caller. A failure of either step fails the whole call. -/
def hookThenMint (rh : ResolutionHooks Accounting) (s : State Accounting)
    (chain asset : UInt256) (recipient : Address) (amount : UInt256) : Option (State Accounting) :=
  match rh.fromChain s.accounting s.token chain asset amount with
  | none => none
  | some accounted =>
    match BridgedStandardERC20.mint s.token s.config.vault recipient amount with
    | none => none
    | some minted => some { s with token := minted, accounting := accounted }

/-- `bridgeMint` on the registered bridged branch: mint `amount` to the data's
`remoteReceiver`. The data's `originalCaller`, `originToken` and metadata are not read. -/
def bridgeMint (rh : ResolutionHooks Accounting) (s : State Accounting) (c : ResolutionCall) :
    Option (State Accounting) :=
  if ResolveEntryAllowed s c ∧ RegisteredBridged s c then
    hookThenMint rh s c.chain c.assetId c.data.remoteReceiver c.data.amount
  else none

/-- `bridgeRecoverFailedTransfer` on the registered bridged branch: re-mint `amount` to the
data's `originalCaller`. The data's `remoteReceiver`, `originToken` and metadata are not
read. -/
def bridgeRecoverFailedTransfer (rh : ResolutionHooks Accounting) (s : State Accounting)
    (c : ResolutionCall) : Option (State Accounting) :=
  if ResolveEntryAllowed s c ∧ RegisteredBridged s c then
    hookThenMint rh s c.chain c.assetId c.data.originalCaller c.data.amount
  else none

/-- The atomic commit interface, as `transact` is for preparation: a failed call leaves the
whole modelled state unchanged, including an accounting update the hook had already made. The
flag records success. -/
def commitResolution (s : State Accounting) : Option (State Accounting) → State Accounting × Bool
  | none => (s, false)
  | some t => (t, true)

def mintTransact (rh : ResolutionHooks Accounting) (s : State Accounting) (c : ResolutionCall) :
    State Accounting × Bool :=
  commitResolution s (bridgeMint rh s c)

def recoverTransact (rh : ResolutionHooks Accounting) (s : State Accounting)
    (c : ResolutionCall) : State Accounting × Bool :=
  commitResolution s (bridgeRecoverFailedTransfer rh s c)

/-- The call `L2AssetRouter.recoverAtomicCall` makes for a bundle call carrying preparation
request `r`'s asset and the returned mint data `data` (`L2AssetRouter.sol:281-296`): the
router is the caller, it sends no value (`recoverAtomicCall` is not payable), the chain is
the burn's destination, and the data is forwarded verbatim. -/
def recoveryCall (router : Address) (r : Request) (data : MintData) : ResolutionCall :=
  ⟨router, 0, r.destinationChain, r.assetId, data⟩

/-- Ordinary token transfers on the vault's token, by anyone, between a preparation and its
recovery: the interference the preparation trace allows (`AssetBridgePreparation.Step.spend`).
Pause changes, other preparations and other resolutions are not included. -/
inductive SpendReach : State Accounting → State Accounting → Prop
  | refl {s : State Accounting} : SpendReach s s
  | tail {s u : State Accounting} {owner recipient : Address} {amount : UInt256}
      {token : BridgedStandardERC20.State} :
      SpendReach s u → BridgedStandardERC20.transfer u.token owner recipient amount = some token →
      SpendReach s { u with token := token }

/-- The tracker-hook law a round trip needs: whenever the preparation hook
`_handleBridgeToChain(chain, asset, amount)` takes accounting `a` to `a'`, the resolution hook
`_handleBridgeFromChain(chain, asset, amount)` succeeds from `a'` and gives back exactly `a`,
whatever token snapshot each sees. A premise, not a property of the deployed trackers. -/
def HooksCancel (hooks : Hooks Accounting) (rh : ResolutionHooks Accounting) : Prop :=
  ∀ (a a' : Accounting) (before after : BridgedStandardERC20.State) (chain asset amount : UInt256),
    hooks.account a before chain asset amount = some a' →
    rh.fromChain a' after chain asset amount = some a

/-! ## First bridge: `bridgeMint` with `tokenAddress[_assetId]` unset -/

/-- The three modifiers, read on a state with no tracked token yet. -/
def FirstEntryAllowed (s : RegistrationState Accounting) (c : ResolutionCall) : Prop :=
  c.msgValue = 0 ∧ c.caller = s.config.router ∧ s.paused = false

/-- Branch selection: the call names the asset being deployed, and the vault address is
nonzero. That the asset is not native here (`NTV:245`; an unregistered asset's stored origin
chain is `0`) is part of the selection; the deploy itself requires the resolved origin chain
to differ from this chain (`NTV:626`), which `registerRepresentation` checks. -/
def FirstBridge (s : RegistrationState Accounting) (c : ResolutionCall) : Prop :=
  s.config.vault ≠ 0 ∧ c.assetId = s.config.assetId

instance (s : RegistrationState Accounting) (c : ResolutionCall) :
    Decidable (FirstEntryAllowed s c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (s : RegistrationState Accounting) (c : ResolutionCall) : Decidable (FirstBridge s c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `bridgeMint` on the first-bridge branch (`NTV:253-255`, then `:260-263`): deploy, initialize
and register the representation for the data's origin token (`registerFreshBranch`, which
starts at the unset `tokenAddress` slot and runs the asset-id check), then the hook, then the
mint to the data's `remoteReceiver`. -/
def bridgeMintFirst (reg : RegistrationHooks Accounting) (rh : ResolutionHooks Accounting)
    (s : RegistrationState Accounting) (c : ResolutionCall) : Option (State Accounting) :=
  if FirstEntryAllowed s c ∧ FirstBridge s c then
    match registerFreshBranch reg s c.data.originToken with
    | none => none
    | some registered =>
      hookThenMint rh registered.state c.chain c.assetId c.data.remoteReceiver c.data.amount
  else none

end Contracts.NativeTokenVaultBase
