import EraSpec.Contracts.AssetRouterBase.Specs.HandlerRegistration
import EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryLimits
import EraSpec.Contracts.NativeTokenVaultBase.Specs.ModelCorrespondence

/-!
# Model: `L2AssetRouter.recoverAtomicCall` — an atomic refund always goes to the vault

Source: era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`
(`contracts/` below is `l1-contracts/contracts/`).

**This file is definitions only.**  The results are in
`EraSpec.Contracts.AssetRouterBase.Properties.AtomicRecovery` and proved in
`EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecovery`.

## The two halves of one atomic transfer

An atomic interop leg burns at the source when it is sent, and is refunded at the source
if its flow times out.  The router picks the asset handler differently on the two sides.

*Send.*  `AssetRouterBase._burn` (`bridge/asset-router/AssetRouterBase.sol:313-346`)
reads the routing table:

    address assetHandler = assetHandlerAddress[_assetId];
    if (assetHandler == address(0)) { ... tryRegisterTokenFromBurnData ...; assetHandler = _nativeTokenVault; }
    bridgeMintCalldata = IAssetHandler(assetHandler).bridgeBurn{...}(...);

so an asset with a custom handler is burned by that handler, which also writes the
bridge-mint data.  `getDepositCalldata` (`AssetRouterBase.sol:378-384`) wraps it as
`finalizeDeposit(block.chainid, assetId, bridgeMintCalldata)`, and that is the bundle call.

*Refund.*  `AtomicFlowManager._recoverBundle` (`atomic-interop/AtomicFlowManager.sol:219-230`)
passes each call's `(destinationChainId, data)` to `IAtomicRecoverable(c.to).recoverAtomicCall`,
with no `try/catch`.  The router's implementation (`bridge/asset-router/L2AssetRouter.sol:281-296`):

    function recoverAtomicCall(uint256 _destChainId, bytes calldata _callData)
        external onlyAtomicFlowManager nonReentrant returns (bool recovered) {
        if (_callData.length < 4 || bytes4(_callData[:4]) != AssetRouterBase.finalizeDeposit.selector) {
            return false;
        }
        (, bytes32 assetId, bytes memory mintData) = abi.decode(_callData[4:], (uint256, bytes32, bytes));
        IL2NativeTokenVault(_nativeTokenVaultAddr()).bridgeRecoverFailedTransfer(_destChainId, assetId, mintData);
        return true;
    }

It never reads `assetHandlerAddress`: every `finalizeDeposit` call goes to the native token
vault.  (Compare `L1AssetRouter.bridgeConfirmTransferResult`, `L1AssetRouter.sol:309`,
which calls `assetHandlerAddress[_assetId]` for the L1 failed-deposit refund.)

## The vault's guard chain, as far as `assetIdCheck`

`NativeTokenVaultBase.bridgeRecoverFailedTransfer` (`bridge/ntv/NativeTokenVaultBase.sol:213-233`)
and `_disburseFailedTransfer` (`:284-306`), with the L2 overrides of
`bridge/ntv/L2NativeTokenVault.sol`:

1. `requireZeroValue(msg.value) onlyAssetRouter whenNotPaused` (`:217`);
2. `DataEncoding.decodeBridgeMintData(_data)` (`:219-220`, `common/libraries/DataEncoding.sol:102-119`);
3. `isNative = originChainId[_assetId] == block.chainid` (`:221`);
4. `_handleBridgeFromChain(...)`, the asset-tracker hook (`:296`, `L2NativeTokenVault.sol:304-315`);
5. native: `_withdrawFunds(_assetId, _receiver, tokenAddress[_assetId], _amount)` (`:298`,
   `L2NativeTokenVault.sol:238-241`);
6. otherwise, with `token = tokenAddress[_assetId]`: if `token == 0`,
   `_ensureAndSaveTokenDeployed` (`L2NativeTokenVault.sol:195-209`), which decodes the metadata's
   origin chain (`tokenDataOriginChainId`, `NativeTokenVaultBase.sol:565-571`) and runs
   `DataEncoding.assetIdCheck(originChain, _assetId, originToken)` (`:580`), which reverts unless
   `_assetId == encodeNTVAssetId(originChain, originToken)` (`DataEncoding.sol:208-214`); then
   `_deployBridgedToken` (`:620-633`, rejecting `originChain == block.chainid` at `:626`) and
   `_setNewTokenStorage` (`:585`, `:588-598`);
7. `IBridgedStandardToken(token).bridgeMint(_receiver, _amount)` (`:304`).

The receiver is the mint data's `originalCaller`; `remoteReceiver` is decoded and dropped.

So an asset the vault has never registered — every custom-handler asset whose id is not an
NTV id — reaches step 6 and reverts there (on L2 it already reverts at step 4, in
`L2AssetTracker._registerLegacyToken`, `bridge/asset-tracker/L2AssetTracker.sol:311-312`; the
model keeps the tracker hook abstract and does not rely on that).  The router does not catch
it, so `recoverAtomicCall` reverts instead of returning `false` — against
`IAtomicRecoverable.sol:13-15` ("MUST return `false` (rather than revert) for call data they do
not recognise as recoverable") and `AtomicFlowManager.sol:205-206`.  The manager does not catch
it either, so the whole refund reverts (`AttackVectors.RecoveryLimits`, limit 2).

## What is modelled, and what is not

* Bundle call data is typed: `CallData` stands for the bytes `recoverAtomicCall` parses, with
  decoding failures as their own cases (`SOL-ABI` boundary).  The mint data is the
  `Contracts.NativeTokenVaultBase.MintData` tuple the vault's preparation returns, so a burn's
  returned data can be placed in a call unchanged.
* The vault's registry is the registry model's `Contracts.NativeTokenVault.Vault`; the deploy
  branch writes it through that model's `registerBridged`.  The vault's external effects (asset
  tracker, token transfer, CREATE2 deployment, token mint) are hooks on an abstract rest of the
  world `X`.  Their types confine their writes to `X` (`DEP-FRAME`): no hook can write the vault
  registry, the router's maps, or the pause flag.
* `nonReentrant` and events are not modelled.  `msg.value` is zero on the router-to-vault call
  (`L2AssetRouter.sol:294` forwards none).
* Targets other than the router are an arbitrary function of the world.
* The leg state machine and the acceptance rule are `AttackVectors.RecoveryLimits`'s.
-/

namespace Contracts.AssetRouter.AtomicRecovery

open AttackVectors.RecoveryLimits (Outcome LegState)

/-- A 160-bit address, as the vault-preparation model and its mint data use it. -/
abbrev Addr160 := Contracts.NativeTokenVaultBase.Address

/-- Decoded `bridgeMintData`: `(originalCaller, remoteReceiver, originToken, amount, erc20Metadata)`
(`DataEncoding.encodeBridgeMintData` / `decodeBridgeMintData`, `DataEncoding.sol:84-119`).  The
same tuple the vault's `bridgeBurn` returns (`Contracts.NativeTokenVaultBase.mintData`). -/
abbrev MintData := Contracts.NativeTokenVaultBase.MintData

/-- Opaque bytes. -/
abbrev Bytes := List UInt8

/-! ## Configuration -/

/-- The fixed addresses and decoders on the source chain, where a refund runs. -/
structure Config where
  /-- `block.chainid`. -/
  thisChain : Chain
  /-- `L2_ASSET_ROUTER_ADDR`: the target of every router-produced bundle call (the router has
  the same address on every chain, `L2AssetRouter.sol:233-234`). -/
  router : Address
  /-- `_nativeTokenVaultAddr()` = `L2_NATIVE_TOKEN_VAULT_ADDR` (`L2AssetRouter.sol:72-74`).  On
  an L2 the vault's address is also the address hashed into every NTV asset id
  (`DataEncoding.sol:151-153`), so one field serves for both. -/
  ntv : Address
  /-- `_atomicFlowManagerAddr()` = `L2_ATOMIC_FLOW_MANAGER_ADDR` (`L2AssetRouter.sol:86-88`). -/
  manager : Address
  /-- `tokenDataOriginChainId(erc20Data)` (`NativeTokenVaultBase.sol:565-571`): the origin chain
  decoded from the token metadata, with `0` replaced by the L1 chain id; `none` when
  `DataEncoding.decodeTokenData` reverts (`DataEncoding.sol:174-186`). -/
  tokenOrigin : Bytes → Option Chain

/-- `DataEncoding.encodeNTVAssetId(chainId, token)` = `keccak256(abi.encode(chainId,
L2_NATIVE_TOKEN_VAULT_ADDR, token))` (`DataEncoding.sol:151-153`), which is the router's
`encodeAssetId(chainId, bytes32(token), L2_NATIVE_TOKEN_VAULT_ADDR)` (`:126-128`): the router
encoding with the vault as the sender.  Tokens are 256-bit words here (as in the registry
model); a 160-bit address enters as its zero extension `widen`. -/
def ntvId (enc : AssetIdOf) (cfg : Config) : NativeTokenVault.NtvAssetId :=
  fun c t => enc c cfg.ntv t

/-! ## Bundle calls -/

/-- The `data` of one bundle call, as `recoverAtomicCall` parses it
(`L2AssetRouter.sol:285-293`). -/
inductive CallData where
  /-- Starts with the `finalizeDeposit` selector, and `abi.decode(_callData[4:], (uint256,
  bytes32, bytes))` succeeds.  `mint` is the inner bytes decoded as bridge-mint data, `none` if
  that decoding reverts (it happens inside the vault, `NativeTokenVaultBase.sol:219-220`). -/
  | finalizeDeposit (sourceChain : Chain) (assetId : AssetId) (mint : Option MintData)
  /-- Starts with the `finalizeDeposit` selector, but the outer `abi.decode` reverts. -/
  | malformedFinalizeDeposit
  /-- Shorter than four bytes, or any other selector. -/
  | other

/-- One `InteropCall` (`common/Messaging.sol:257-264`).  The manager passes only `target`'s
`recoverAtomicCall(destinationChainId, data)`; `sender` (`InteropCall.from`) and `value` are not
passed on. -/
structure Call where
  /-- `InteropCall.to`. -/
  target : Address
  /-- `InteropCall.from`: the router for an indirect call through it, the sending account for
  a direct call (`InteropCenter.sol:733-750`). -/
  sender : Address
  /-- `InteropCall.value`. -/
  value : UInt256
  /-- `InteropCall.data`. -/
  data : CallData

/-- The bundle call a router-routed indirect starter produces: `target` the router, `from` the
router (`InteropCenter.sol:733-740`; `L2AssetRouter.sol:336-341`), value zero for a non-base
asset, data `finalizeDeposit(block.chainid, assetId, bridgeMintCalldata)`. -/
def routerCall (cfg : Config) (assetId : AssetId) (md : MintData) : Call :=
  ⟨cfg.router, cfg.router, 0, .finalizeDeposit cfg.thisChain assetId (some md)⟩

/-- The bundle call a DIRECT starter produces (`InteropCenter.sol:741-750`): `to` and `data`
exactly as the sender supplied them, `from` the sender.  Nothing is burned for it; its value is
zero in an atomic bundle (`_validateAtomicBundle`). -/
def directCall (target sender : Address) (data : CallData) : Call := ⟨target, sender, 0, data⟩

/-- `InteropCenter._validateAtomicBundle` (`interop/InteropCenter.sol:670-677`), called at
`:649` before the leg is committed: the one send-time check specific to atomic bundles rejects
calls that carry native `value`, and nothing else.  In particular it does not look at the
asset, its handler, or whether the call is direct. -/
def AtomicBundleValid (calls : List Call) : Prop := ∀ c ∈ calls, c.value = 0

/-! ## State and dependencies -/

/-- The vault's external effects during a refund, on the rest of the world `X`.  Each may
revert (`none`).  Their types confine writes to `X`. -/
structure Hooks (X : Type) where
  /-- `_handleBridgeFromChain(chainId, assetId, amount)`: `L2AssetTracker.handleFinalizeBridgingOnL2`
  (`L2NativeTokenVault.sol:304-315`). -/
  fromChain : X → Chain → AssetId → UInt256 → Option X
  /-- `_withdrawFunds(assetId, to, token, amount)`: `require(assetId != BASE_TOKEN_ASSET_ID)`,
  then `safeTransfer` (`L2NativeTokenVault.sol:238-241`). -/
  withdraw : X → AssetId → Addr160 → Address → UInt256 → Option X
  /-- `_deployBridgedToken(originChain, assetId, originToken, erc20Data)` and the address check
  (`NativeTokenVaultBase.sol:582-583, 620-633`), plus `_registerTokenInAssetTracker`: returns the
  deployed local token.  Runs only after `assetIdCheck` passed. -/
  deploy : X → AssetId → Addr160 → Chain → Option (X × Address)
  /-- `IBridgedStandardToken(token).bridgeMint(receiver, amount)` (`NativeTokenVaultBase.sol:304`). -/
  mint : X → Address → Addr160 → UInt256 → Option X

/-- What a refund reads and writes on the source chain. -/
structure World (X : Type) where
  /-- The router's `assetHandlerAddress` / `assetDeploymentTracker` maps. -/
  router : Router
  /-- The vault's registry (`originChainId`, `tokenAddress`, `assetId`, …), as the registry
  model has it. -/
  vault : NativeTokenVault.Vault
  /-- The vault's `paused()` flag. -/
  paused : Bool
  /-- Everything else: asset tracker, token ledgers, other contracts. -/
  rest : X

variable {X : Type}

/-! ## The vault's refund -/

/-- `NativeTokenVaultBase.bridgeRecoverFailedTransfer(chainId, assetId, data)` called by
`caller` with `msgValue`, steps 1–7 of the header, on the vault's registry `V`, its pause flag and
the rest of the world `x`.  It returns the new registry and rest; `none` is a revert. -/
def vaultRefund (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (V : NativeTokenVault.Vault)
    (paused : Bool) (x : X) (caller : Address) (msgValue : UInt256) (chainId : Chain)
    (a : AssetId) (m : Option MintData) : Option (NativeTokenVault.Vault × X) :=
  -- 1. requireZeroValue(msg.value) onlyAssetRouter whenNotPaused
  if msgValue ≠ 0 ∨ caller ≠ cfg.router ∨ paused = true then none else
  -- 2. decodeBridgeMintData
  match m with
  | none => none
  | some md =>
    -- 4. _handleBridgeFromChain
    match hk.fromChain x chainId a md.amount with
    | none => none
    | some x₁ =>
      -- 3./5. native: unlock the escrow to `originalCaller`
      if V.originChain a = cfg.thisChain then
        (hk.withdraw x₁ a md.originalCaller (V.token a) md.amount).map fun x₂ => (V, x₂)
      -- 6./7. bridged and known: mint to `originalCaller`
      else if V.token a ≠ 0 then
        (hk.mint x₁ (V.token a) md.originalCaller md.amount).map fun x₂ => (V, x₂)
      -- 6. bridged and unknown: decode the origin chain, `assetIdCheck`, deploy, save, mint
      else
        match cfg.tokenOrigin md.metadata with
        | none => none
        | some c =>
          if a ≠ ntvId enc cfg c (NativeTokenVaultBase.widen md.originToken) then none
          else if c = cfg.thisChain then none
          else
            match hk.deploy x₁ a md.originToken c with
            | none => none
            | some (x₂, tok) =>
              (hk.mint x₂ tok md.originalCaller md.amount).map fun x₃ =>
                (NativeTokenVault.registerBridged V a tok (NativeTokenVaultBase.widen md.originToken) c,
                  x₃)

/-- The vault's refund on a world: it reads the registry, the pause flag and the rest of the
world, and writes only the registry and the rest.  The router's maps are neither read nor
written. -/
def ntvRecover (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (caller : Address) (msgValue : UInt256) (chainId : Chain) (a : AssetId)
    (m : Option MintData) : Option (World X) :=
  (vaultRefund enc cfg hk w.vault w.paused w.rest caller msgValue chainId a m).map
    fun p => { w with vault := p.1, rest := p.2 }

/-! ## The router's refund -/

/-- `L2AssetRouter.recoverAtomicCall(destChainId, callData)` called by `caller`
(`L2AssetRouter.sol:281-296`): `none` is a revert, `some (w', b)` returns `b`.  It takes the
world, router maps included, and never reads `w.router`. -/
def recoverAtomicCall (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (caller : Address) (destChainId : Chain) (d : CallData) : Option (World X × Bool) :=
  -- onlyAtomicFlowManager (`:137-140`)
  if caller ≠ cfg.manager then none else
  match d with
  -- not a `finalizeDeposit`: `return false` (`:285-287`)
  | .other => some (w, false)
  -- the outer `abi.decode` reverts (`:293`)
  | .malformedFinalizeDeposit => none
  -- the vault, with the call's own `(destChainId, assetId, mintData)`; then `return true`
  | .finalizeDeposit _ a m =>
    (ntvRecover enc cfg hk w cfg.router 0 destChainId a m).map fun w' => (w', true)

/-- `_burn`'s choice of handler for asset `a` (`AssetRouterBase.sol:322-336`): the registered
handler, or the vault when none is registered. -/
def burnHandler (cfg : Config) (R : Router) (a : AssetId) : Address :=
  if R.handler a = 0 then cfg.ntv else R.handler a

/-- The outcome class `AttackVectors.RecoveryLimits` reasons about. -/
def outcomeOf {W : Type} : Option (W × Bool) → Outcome
  | none => Outcome.reverts
  | some (_, true) => Outcome.recovered
  | some (_, false) => Outcome.declined

/-! ## The manager's refund loop -/

/-- One iteration of `_recoverBundle` (`AtomicFlowManager.sol:224-227`): the router's
`recoverAtomicCall` if the call targets the router, otherwise whatever the target `other c.target`
does, from the manager. -/
def recoverCall (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (destChainId : Chain) (w : World X) (c : Call) : Option (World X × Bool) :=
  if c.target = cfg.router then recoverAtomicCall enc cfg hk w cfg.manager destChainId c.data
  else other c.target w destChainId c.data

/-- `_recoverBundle`'s loop (`AtomicFlowManager.sol:219-230`): the calls in order, each on the
state the previous one left, no `try/catch`; `some (w, n)` counts the calls that returned
`true`. -/
def recoverBundle (step : World X → Call → Option (World X × Bool)) :
    World X → List Call → Option (World X × ℕ)
  | w, [] => some (w, 0)
  | w, c :: cs =>
    match step w c with
    | none => none
    | some (w', b) =>
      match recoverBundle step w' cs with
      | none => none
      | some (w'', n) => some (w'', (if b then 1 else 0) + n)

/-- `AtomicFlowManager.claimRefund` for one leg (`AtomicFlowManager.sol:165-180`): enabled only
on a `Revertable` leg (`:169-170`); the leg is set `Reverted` before the loop (`:175`), and the
loop must recover at least one call (`:229`).  `none` is a revert of the whole transaction, so
the leg stays `Revertable` and nothing the loop did persists. -/
def claimRefund (step : World X → Call → Option (World X × Bool)) (s : LegState)
    (w : World X) (calls : List Call) : Option (LegState × World X) :=
  if s ≠ LegState.Revertable then none else
  match recoverBundle step w calls with
  | none => none
  | some (w', n) => if n = 0 then none else some (LegState.Reverted, w')

/-- The outcomes the loop produces, on the threaded state: it stops at the first revert. -/
def outcomes (step : World X → Call → Option (World X × Bool)) :
    World X → List Call → List Outcome
  | _, [] => []
  | w, c :: cs =>
    match step w c with
    | none => [Outcome.reverts]
    | some (w', b) => (if b then Outcome.recovered else Outcome.declined) :: outcomes step w' cs

/-! ## Predicates used by the statements -/

/-- The vault does not know asset `a`: no local token, and not native to this chain.  The state
of every asset the vault never registered (`originChainId` and `tokenAddress` unset). -/
def VaultUnaware (cfg : Config) (V : NativeTokenVault.Vault) (a : AssetId) : Prop :=
  V.token a = 0 ∧ V.originChain a ≠ cfg.thisChain

/-- `assetIdCheck` cannot pass for asset `a` on the pair decoded from `m`: for the decoded
origin token and every origin chain the metadata decodes to, `a` is not their NTV id. -/
def FailsAssetIdCheck (enc : AssetIdOf) (cfg : Config) (a : AssetId) (m : Option MintData) :
    Prop :=
  ∀ md, m = some md → ∀ c, cfg.tokenOrigin md.metadata = some c →
    a ≠ ntvId enc cfg c (NativeTokenVaultBase.widen md.originToken)

/-- Asset `a`'s registry entry is the same in `V` and `V'`: a write elsewhere, or none. -/
def LeavesAlone (a : AssetId) (V V' : NativeTokenVault.Vault) : Prop :=
  V'.token a = V.token a ∧ V'.originChain a = V.originChain a

/-- Every router call on asset `a` in the bundle carries data that fails `assetIdCheck` for `a`. -/
def RouterCallsOnFail (enc : AssetIdOf) (cfg : Config) (a : AssetId) (calls : List Call) : Prop :=
  ∀ c ∈ calls, c.target = cfg.router →
    ∀ src m, c.data = .finalizeDeposit src a m → FailsAssetIdCheck enc cfg a m

/-- The bundle contains a router call on asset `a`. -/
def HasRouterCallOn (cfg : Config) (a : AssetId) (calls : List Call) : Prop :=
  ∃ c ∈ calls, c.target = cfg.router ∧ ∃ src m, c.data = .finalizeDeposit src a m

/-- Every other target, when it returns, has left asset `a`'s vault entry alone. -/
def OthersLeaveAlone (a : AssetId)
    (other : Address → World X → Chain → CallData → Option (World X × Bool)) : Prop :=
  ∀ target w dest d w' b, other target w dest d = some (w', b) → LeavesAlone a w.vault w'.vault

end Contracts.AssetRouter.AtomicRecovery
