import EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecovery
import EraSpec.Protocol.AssetBridgePreparation.Specs.Model

/-!
# Model: full recovery of an atomic bundle of asset-router deposits

Source: era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af` (`contracts/` below is
`l1-contracts/contracts/`).

**This file is definitions only.**  The statements are in
`EraSpec.Protocol.AssetBridgePreparation.Properties.FullRecovery` and are proved in
`EraSpec.Protocol.AssetBridgePreparation.Proofs.FullRecovery`.

## The question

`AtomicFlowManager._recoverBundle` (`atomic-interop/AtomicFlowManager.sol:219-230`) is
best-effort.  A claim succeeds as soon as one call recovers (`recovered != 0`, `:229`), and
`claimRefund` has already set the leg `Reverted` (`:175`), which no later claim can reopen.  So a
terminal leg does not by itself mean that every call was restored (`AttackVectors.RecoveryLimits`,
limit 1), and one reverting call blocks the whole claim (limit 2).  The source leaves full
refundability to the flow author (`:215-217`):

    A flow author must make any fund-moving leg a recoverable (asset-router) call to have it
    returned on timeout

This topic is the positive side of that sentence.  For a bundle all of whose calls are
asset-router deposits on assets the native token vault has registered: when is the claim
enabled, and what exactly does it restore?

## The stack, unchanged

The manager's loop (`claimRefund`, `recoverBundle`), the router's `recoverAtomicCall`
(`bridge/asset-router/L2AssetRouter.sol:281-296`) and the vault's `bridgeRecoverFailedTransfer`
guard chain (`bridge/ntv/NativeTokenVaultBase.sol:213-233, 284-306`) are the model of
`Contracts.AssetRouter.AtomicRecovery` (`Contracts/AssetRouterBase/Specs/AtomicRecovery.lean`),
used as it is.  That model keeps the vault's external effects as hooks on an abstract rest of
the world `X`.  Here `X` is fixed to the local token model.

* `Ledgers.token tok` is the ERC20 ledger of the token contract at address `tok` — the address
  the vault's registry stores in `tokenAddress[assetId]` — as a
  `Contracts.BridgedStandardERC20.State`: balances, total supply and configured vault
  (`MODEL-LEDGER`).
* `Ledgers.tracker` is the asset tracker's state, opaque.

`localHooks` fills in the four hooks.

* `_handleBridgeFromChain(chainId, assetId, amount)` is the tracker hook `tr`, a parameter that
  may revert (`bridge/ntv/L2NativeTokenVault.sol:304-315`, which calls
  `L2AssetTracker.handleFinalizeBridgingOnL2`, `bridge/asset-tracker/L2AssetTracker.sol:269-307`).
* `IBridgedStandardToken(token).bridgeMint(receiver, amount)` (`NativeTokenVaultBase.sol:304`) is
  the token model's `mint` with the vault as caller.  At the source this is `onlyNTV` followed
  by OpenZeppelin v4 `_mint` (`bridge/BridgedStandardERC20.sol:170-173`), which rejects the zero
  address and a supply overflow.
* `_withdrawFunds(assetId, to, token, amount)` (`L2NativeTokenVault.sol:238-241`) is
  `require(assetId != BASE_TOKEN_ASSET_ID)` followed by `IERC20(token).safeTransfer(to, amount)`
  from the vault: the token model's `transfer` with the vault as owner.  This reads the native
  token as a standard ERC20 with no fee and no rebasing (`MODEL-ESCROW`).
* `_ensureAndSaveTokenDeployed` (the first-bridge deploy, `NativeTokenVaultBase.sol:301-303`) is a
  parameter `dep`.  The vault reaches it only for an asset its registry has no token for, which
  the statements exclude; nothing is assumed about it.

`vault` is the vault's own address as the token sees it (`msg.sender` of the token call), and
`base` is `BASE_TOKEN_ASSET_ID`.  The hooks' types confine their writes to the ledgers and the
tracker (`DEP-FRAME`).

## Deposit bundles

A deposit is the pair `(assetId, mintData)` that a `finalizeDeposit` call carries.
`DepositBundle cfg calls ds` says that call `i` targets the router with data
`finalizeDeposit(_, ds[i].1, ds[i].2)` whose mint data decodes.  That is the shape
`AssetRouterBase.getDepositCalldata` (`bridge/asset-router/AssetRouterBase.sol:378-384`) gives every
router-produced bundle call.  The call's sender and value are left free, because the refund reads
neither (`Contracts.AssetRouter.AtomicRecovery.Properties.RefundIgnoresCallSender`).

## The credits

`creditStep` is what the vault's refund of one deposit on a registered asset does to the ledgers
(`NativeTokenVaultBase.sol:221, 296-304`):

* a bridged asset (`originChainId[assetId] != block.chainid`) is re-minted to the mint data's
  `originalCaller`;
* a native asset is released from the vault's escrow to the same account.

`creditRun` applies the steps in bundle order, and `trackerRun` runs the tracker hook in bundle
order, with the bundle's destination chain as `_chainId` (`AtomicFlowManager.sol:220, 225`).

The sums `mintedOn`, `releasedOn` and `creditedTo` total the deposits per token and per account.
`CreditsCovered` is the token-level condition under which every credit succeeds, and
`ExactCredits` is the closed form of the result.

The vault keeps no record of resolved data (`Contracts.NativeTokenVaultBase.Properties.VaultHasNoReplayGuard`),
so at-most-once refund rests on the leg state alone (`AtomicFlowManager.sol:169-175`); that is
not re-proved here.
-/

namespace AssetBridgePreparation.FullRecovery

open Contracts
open Contracts.AssetRouter (Chain AssetId Address AssetIdOf)
open Contracts.AssetRouter.AtomicRecovery (Config Call CallData World Hooks MintData Addr160)

/-! ## The rest of the world in the local token model -/

/-- The rest of the world a refund touches, in the local token model. -/
structure Ledgers (A : Type) where
  /-- The ERC20 ledger of the token contract at each address, keyed by the 256-bit word the
  vault's registry stores in `tokenAddress[assetId]`. -/
  token : Address → BridgedStandardERC20.State
  /-- The asset tracker's state (`L2AssetTracker`), opaque. -/
  tracker : A

/-- `_handleBridgeFromChain(chainId, assetId, amount)` on the tracker state; `none` is a revert. -/
abbrev TrackerHook (A : Type) := A → Chain → AssetId → UInt256 → Option A

/-- `_ensureAndSaveTokenDeployed(assetId, originToken, erc20Data)`, from the origin chain the
metadata decodes to: the new world and the deployed token, or a revert. -/
abbrev DeployHook (A : Type) := Ledgers A → AssetId → Addr160 → Chain → Option (Ledgers A × Address)

/-- What a bundle call to a target other than the router does, from the manager: an arbitrary
function of the world, as in `Contracts.AssetRouter.AtomicRecovery.recoverCall`. -/
abbrev OtherTargets (X : Type) := Address → World X → Chain → CallData → Option (World X × Bool)

variable {A : Type}

/-- The vault's external effects when tokens behave as the local token model (see the module
header): the tracker hook `tr`; a native release is `require(assetId != base)` and then the token
model's `transfer` from `vault`; a re-mint is the token model's `mint` with `vault` as caller; the
first-bridge deploy is `dep`. -/
def localHooks (vault : Addr160) (base : AssetId) (tr : TrackerHook A) (dep : DeployHook A) :
    Hooks (Ledgers A) where
  fromChain x c a amt := (tr x.tracker c a amt).map fun t => { x with tracker := t }
  withdraw x a rcv tok amt :=
    if a = base then none
    else (BridgedStandardERC20.transfer (x.token tok) vault rcv amt).map fun l =>
      { x with token := Function.update x.token tok l }
  deploy := dep
  mint x tok rcv amt :=
    (BridgedStandardERC20.mint (x.token tok) vault rcv amt).map fun l =>
      { x with token := Function.update x.token tok l }

/-! ## Deposit bundles -/

/-- A deposit: the asset id and the decoded bridge-mint data
`(originalCaller, remoteReceiver, originToken, amount, erc20Metadata)` of one `finalizeDeposit`
call. -/
abbrev Deposit := AssetId × MintData

/-- Call `c` is a `finalizeDeposit` call to the router carrying deposit `d`: the shape every
router-produced bundle call has (`AssetRouterBase.sol:378-384`), with mint data that decodes. -/
def DepositCall (cfg : Config) (c : Call) (d : Deposit) : Prop :=
  c.target = cfg.router ∧ ∃ src, c.data = .finalizeDeposit src d.1 (some d.2)

/-- The bundle's calls are, in order, deposit calls carrying the deposits `ds`. -/
def DepositBundle (cfg : Config) (calls : List Call) (ds : List Deposit) : Prop :=
  List.Forall₂ (DepositCall cfg) calls ds

/-- Call `c` targets the router with `finalizeDeposit` data of any kind (any asset, mint data
that may not decode). -/
def RouterDepositShaped (cfg : Config) (c : Call) : Prop :=
  c.target = cfg.router ∧ ∃ src a m, c.data = .finalizeDeposit src a m

/-! ## The credits -/

/-- The token-model credit the vault's refund of deposit `d` makes on the ledgers `L`, for an asset
the registry `V` has a token for.  Native (`originChainId[assetId] == block.chainid`): the base
token is rejected, otherwise `transfer` from the vault to `originalCaller`.  Bridged: `mint` to
`originalCaller` with the vault as caller.  Either way the amount is the data's `amount`, on the
ledger of `V.token assetId`. -/
def creditStep (vault : Addr160) (base : AssetId) (thisChain : Chain) (V : NativeTokenVault.Vault)
    (L : Address → BridgedStandardERC20.State) (d : Deposit) :
    Option (Address → BridgedStandardERC20.State) :=
  if V.originChain d.1 = thisChain then
    if d.1 = base then none
    else (BridgedStandardERC20.transfer (L (V.token d.1)) vault d.2.originalCaller d.2.amount).map
      (Function.update L (V.token d.1))
  else (BridgedStandardERC20.mint (L (V.token d.1)) vault d.2.originalCaller d.2.amount).map
    (Function.update L (V.token d.1))

/-- The credits of the deposits `ds`, in order, each on the ledgers the previous one left;
`none` if any fails. -/
def creditRun (vault : Addr160) (base : AssetId) (thisChain : Chain) (V : NativeTokenVault.Vault) :
    (Address → BridgedStandardERC20.State) → List Deposit → Option (Address → BridgedStandardERC20.State)
  | L, [] => some L
  | L, d :: ds => (creditStep vault base thisChain V L d).bind fun L' =>
      creditRun vault base thisChain V L' ds

/-- The tracker hook on the deposits `ds`, in order, with the bundle's destination chain `dest`;
`none` if any call reverts. -/
def trackerRun (tr : TrackerHook A) (dest : Chain) : A → List Deposit → Option A
  | t, [] => some t
  | t, d :: ds => (tr t dest d.1 d.2.amount).bind fun t' => trackerRun tr dest t' ds

/-! ## Totals -/

/-- `Σ amount` over the deposits that `p` selects. -/
def amountSum (p : Deposit → Bool) (ds : List Deposit) : ℕ :=
  ((ds.filter p).map fun d => d.2.amount.val).sum

/-- What the refund of `ds` re-mints on token `tok`: the bridged deposits whose asset's token is
`tok`. -/
def mintedOn (thisChain : Chain) (V : NativeTokenVault.Vault) (tok : Address) (ds : List Deposit) :
    ℕ :=
  amountSum (fun d => decide (V.originChain d.1 ≠ thisChain ∧ V.token d.1 = tok)) ds

/-- What the refund of `ds` releases from the vault's escrow of token `tok`: the native deposits
whose asset's token is `tok`. -/
def releasedOn (thisChain : Chain) (V : NativeTokenVault.Vault) (tok : Address) (ds : List Deposit) :
    ℕ :=
  amountSum (fun d => decide (V.originChain d.1 = thisChain ∧ V.token d.1 = tok)) ds

/-- What the refund of `ds` credits to account `u` on token `tok`: the deposits on `tok` whose
mint data names `u` as `originalCaller`. -/
def creditedTo (V : NativeTokenVault.Vault) (tok : Address) (u : Addr160) (ds : List Deposit) : ℕ :=
  amountSum (fun d => decide (V.token d.1 = tok ∧ d.2.originalCaller = u)) ds

/-! ## When every credit succeeds, and what it gives -/

/-- The token-level conditions under which every credit of `ds` succeeds in bundle order.  These
are the guards of OpenZeppelin v4 `_mint` / `_transfer` and of `onlyNTV`, totalled over the
bundle. -/
structure CreditsCovered (vault : Addr160) (base : AssetId) (thisChain : Chain)
    (V : NativeTokenVault.Vault) (L : Address → BridgedStandardERC20.State) (ds : List Deposit) :
    Prop where
  /-- The vault is a real account: the token model rejects a zero minter and a zero owner. -/
  vaultNonzero : vault ≠ 0
  /-- Every `originalCaller` is nonzero: `_mint` and `_transfer` reject the zero address. -/
  receiverNonzero : ∀ d ∈ ds, d.2.originalCaller ≠ 0
  /-- A native deposit is not the base token (`_withdrawFunds`), and the vault's balance of its
  token covers all the native releases of the bundle on that token. -/
  native : ∀ d ∈ ds, V.originChain d.1 = thisChain →
    d.1 ≠ base ∧ releasedOn thisChain V (V.token d.1) ds ≤ (L (V.token d.1)).balances vault
  /-- A bridged deposit's token names the vault as its minter (`onlyNTV`), and its total supply
  plus all the re-mints of the bundle on that token stays below `2^256` (`_mint`). -/
  bridged : ∀ d ∈ ds, V.originChain d.1 ≠ thisChain →
    (L (V.token d.1)).config.vault = vault ∧
    (L (V.token d.1)).totalSupply + mintedOn thisChain V (V.token d.1) ds < UInt256.size

/-- The ledgers `L'` are exactly `L` with the credits of `ds`.  A token no deposit names is
untouched.  On every token the configuration is unchanged, the supply rose by exactly what was
re-minted on it, and each account `u` gained exactly what the bundle credits it on that token —
less, for the vault itself, what was released from its escrow. -/
def ExactCredits (vault : Addr160) (thisChain : Chain) (V : NativeTokenVault.Vault)
    (L L' : Address → BridgedStandardERC20.State) (ds : List Deposit) : Prop :=
  (∀ tok, (∀ d ∈ ds, V.token d.1 ≠ tok) → L' tok = L tok) ∧
  ∀ tok, (L' tok).config = (L tok).config ∧
    (L' tok).totalSupply = (L tok).totalSupply + mintedOn thisChain V tok ds ∧
    ∀ u, (L' tok).balances u + (if u = vault then releasedOn thisChain V tok ds else 0) =
      (L tok).balances u + creditedTo V tok u ds

/-! ## Pending obligations as deposits -/

/-- The deposit a pending obligation's router call carries: its asset id and its mint data
(`AssetRouterBase.sol:378-384` wraps the vault's returned data unchanged). -/
def obligationDeposit (o : Obligation) : Deposit := (o.assetId, o.data)

/-- The total pending amount owed back to account `u`: the obligations whose mint data names `u`
as `originalCaller`.  The refund-side counterpart of `pendingAmountTo`. -/
def pendingAmountFor (u : Addr160) (pending : List Obligation) : ℕ :=
  ((pending.filter fun o => decide (o.data.originalCaller = u)).map fun o => o.data.amount.val).sum

/-- What the preparation trace keeps true of every pending obligation: it is for the vault's
tracked asset, it names a nonzero depositor as `originalCaller`, and the vault's configuration
was in scope for preparation (nonzero vault and token, origin chain not this chain). -/
def PendingSound {Accounting : Type} (l : Ledger Accounting) : Prop :=
  ∀ o ∈ l.pending, o.assetId = l.vault.config.assetId ∧ o.data.originalCaller ≠ 0 ∧
    l.vault.config.vault ≠ 0 ∧ l.vault.config.tokenAddress ≠ 0 ∧
    l.vault.config.originChainId ≠ l.vault.config.chainId

end AssetBridgePreparation.FullRecovery
