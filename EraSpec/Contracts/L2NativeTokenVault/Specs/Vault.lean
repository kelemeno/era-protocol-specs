import EraSpec.Contracts.L2AssetRouter.Specs.Basics

/-!
# Model: `L2NativeTokenVault` — registry, bridged-token deployment, mint and burn

Source: era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`.
Paths are relative to `l1-contracts/contracts/`; `NTV/` is `bridge/ntv/`, so
`NTV/L2NativeTokenVault.sol` and `NTV/NativeTokenVaultBase.sol`.

**This file is definitions only.**  Statements are in
`EraSpec.Contracts.L2NativeTokenVault.Properties.Vault`, proofs in
`EraSpec.Contracts.L2NativeTokenVault.Proofs.Vault`.

## What is modelled

Every state-changing entry point of the deployed contract except
`addLegacyTokenToBridgedTokensList` and `registerBaseTokenIfNeeded` (below), each with
its guards in source order.  A revert is `none`.

| `Op` | Source | Who can call |
|---|---|---|
| `initL2` | `NTV/L2NativeTokenVault.sol:99-115` | the complex upgrader, once (`reentrancyGuardInitializer`) |
| `updateL2` | `NTV/L2NativeTokenVault.sol:134-174` | the complex upgrader |
| `registerToken` | `NTV/NativeTokenVaultBase.sol:127-140, 492-499` | anyone |
| `tryRegisterTokenFromBurnData` | `NTV/NativeTokenVaultBase.sol:321-335` | anyone |
| `bridgeMint` | `NTV/NativeTokenVaultBase.sol:180-189, 220-247` | the asset router |
| `bridgeRecoverFailedTransfer` | `NTV/NativeTokenVaultBase.sol:195-214`, `NTV/L2NativeTokenVault.sol:204-227` | the asset router |
| `bridgeBurn` | `NTV/NativeTokenVaultBase.sol:294-318, 337-457` | the asset router |
| `owner` | `pause`/`unpause` (`NTV/NativeTokenVaultBase.sol:636-643`) and `Ownable2Step` | the owner / pending owner |
| `envDeploy` | not a vault function: some other account deploys code at an address | — |

`ensureTokenIsRegistered` (`NTV/NativeTokenVaultBase.sol:143-150`) is `registerToken`
when the token is unregistered and writes nothing otherwise, so it adds no transition.

## Abstractions (model boundaries)

* **Typed data.**  Bridge-mint data is `MintData`, bridge-burn data is `BurnData`
  (`common/libraries/DataEncoding.sol:51-60, 84-118`).  Of the ERC-20 metadata only the
  origin-chain field is kept (`metaChain`); `none` is metadata that `decodeTokenData`
  rejects (`DataEncoding.sol:173-185`).  Byte layouts are not modelled (`SOL-ABI`).
* **Hashes and CREATE2 are functions of `Cfg`.**  `encNTV` is
  `DataEncoding.encodeNTVAssetId` (`DataEncoding.sol:150-152`); `create2 salt beacon` is
  `Create2.computeAddress(salt, keccak256(BeaconProxy.creationCode ++ abi.encode(beacon, "")))`
  (`NTV/L2NativeTokenVault.sol:255-265`); `saltHash` is the non-L1 salt
  `keccak256(abi.encode(originChainId, token))` (:270-277).  No injectivity is assumed
  anywhere in this file.
* **Deployment (`VM-DEPLOY`).**  `Create2.deploy` succeeds exactly when the address has
  no code, and puts a proxy there (`code`, `proxy`).  A deployment landing on address
  zero is excluded by a guard of `ensureAndSaveTokenDeployed`; the event it excludes is
  the single hash equation `create2 … = 0`.  `require(deployedToken == _expectedToken)`
  (`NTV/NativeTokenVaultBase.sol:560`) is then true by construction.
* **Token ledgers.**  For a proxy the vault deployed, `supply` is the token's
  `totalSupply`, changed only by the vault's `bridgeMint`/`bridgeBurn` calls
  (`bridge/BridgedStandardERC20.sol:158-167`, `onlyNTV`).  Holder balances are not
  modelled: the burn's balance check is weakened to `amount ≤ totalSupply`, which only
  adds runs.  The supply is a natural number (no overflow revert), which also only adds
  runs.
* **Hooks.**  Calls to `L2_ASSET_TRACKER`, `L2_BASE_TOKEN_HOLDER`, a native token's
  `transfer`/`transferFrom`, and any token the vault did not deploy succeed with no
  effect on the modelled state.  A hook that reverts in the deployment removes a run of
  the model, never adds one.  `hookOrigin` is what such a token's `originToken()` getter
  returns.
* **The router callback.**  `_unsafeRegisterNativeToken` calls
  `setAssetHandlerAddressThisChain` on the router (`NTV/NativeTokenVaultBase.sol:495-498`).
  The vault-only model omits it (it cannot revert for the vault as caller);
  `Contracts.L2AssetRouter` composes it.
* **Not modelled:** `bridgedTokens`/`tokenIndex`/`bridgedTokensCount`
  (`addLegacyTokenToBridgedTokensList`), `registerBaseTokenIfNeeded` (writes no vault
  storage), `BASE_TOKEN_NAME/SYMBOL/DECIMALS`, events, and upgrades of the vault itself.
-/

namespace Contracts.L2NativeTokenVault

open Contracts.L2AssetRouter (Chain AssetId Address upd Own OwnerOp)

/-! ## Configuration and data -/

/-- Constants and hash functions the vault uses. -/
structure Cfg where
  /-- `block.chainid`. -/
  thisChain : Chain
  /-- `DataEncoding.encodeNTVAssetId(chainId, tokenAddress)`. -/
  encNTV : Chain → Address → AssetId
  /-- `Create2.computeAddress(salt, keccak256(BeaconProxy.creationCode ++ abi.encode(beacon, "")))`. -/
  create2 : UInt256 → Address → Address
  /-- `keccak256(abi.encode(originChainId, token))`, the salt of a non-L1 token. -/
  saltHash : Chain → Address → UInt256
  /-- `L2_ASSET_ROUTER_ADDR` (`_getAssetRouter`, `NTV/L2NativeTokenVault.sol:234-236`). -/
  router : Address
  /-- `L2_COMPLEX_UPGRADER_ADDR` (`onlyUpgrader`, `NTV/L2NativeTokenVault.sol:84-89`). -/
  upgrader : Address
  /-- `L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR`. -/
  baseTokenAddr : Address

/-- Decoded bridge-mint data (`DataEncoding.decodeBridgeMintData`). -/
structure MintData where
  originalCaller : Address
  receiver : Address
  originToken : Address
  amount : UInt256
  /-- The origin-chain field of the ERC-20 metadata; `none` if the metadata does not
  decode. -/
  metaChain : Option Chain

/-- Decoded bridge-burn data (`DataEncoding.decodeBridgeBurnData`): amount, receiver,
maybe-token. -/
structure BurnData where
  amount : UInt256
  receiver : Address
  token : Address

/-- `TokenBridgingData` of the base token, as `updateL2` receives it. -/
structure BaseTokenData where
  assetId : AssetId
  originToken : Address
  originChainId : Chain

/-- Ghost record of one bridged-token deployment, with the configuration it used. -/
structure DeployRec where
  assetId : AssetId
  /-- The deployed proxy. -/
  token : Address
  /-- The resolved origin chain (`tokenDataOriginChainId`). -/
  origin : Chain
  originToken : Address
  /-- `bridgedTokenBeacon` at the deployment. -/
  beacon : Address
  /-- `L1_CHAIN_ID` at the deployment. -/
  l1ChainId : Chain

/-- The vault's storage, plus the code and token state it reads, plus the ghost log. -/
structure Vault where
  /-- `WETH_TOKEN`. -/
  weth : Address
  /-- `BASE_TOKEN_ASSET_ID`. -/
  baseAssetId : AssetId
  /-- `L1_CHAIN_ID`. -/
  l1ChainId : Chain
  /-- `BASE_TOKEN_ORIGIN_TOKEN`. -/
  baseOriginToken : Address
  /-- `bridgedTokenBeacon`. -/
  beacon : Address
  /-- The reentrancy-guard slot is set (`reentrancyGuardInitializer`). -/
  initialized : Bool
  own : Own
  /-- `originChainId[assetId]`. -/
  originChainId : AssetId → Chain
  /-- `tokenAddress[assetId]`. -/
  tokenAddress : AssetId → Address
  /-- `assetId[tokenAddress]`. -/
  assetId : Address → AssetId
  /-- The address has code. -/
  code : Address → Bool
  /-- Ghost: the address is a beacon proxy this vault deployed. -/
  proxy : Address → Bool
  /-- A deployed proxy's stored `originToken`. -/
  tokOrigin : Address → Address
  /-- A deployed proxy's `totalSupply`. -/
  supply : Address → Nat
  /-- Ghost: every deployment, oldest first. -/
  deploys : List DeployRec

/-- Fresh storage, no code anywhere. -/
def Vault.init : Vault :=
  { weth := 0, baseAssetId := 0, l1ChainId := 0, baseOriginToken := 0, beacon := 0,
    initialized := false, own := Own.init, originChainId := fun _ => 0,
    tokenAddress := fun _ => 0, assetId := fun _ => 0, code := fun _ => false,
    proxy := fun _ => false, tokOrigin := fun _ => 0, supply := fun _ => 0, deploys := [] }

/-! ## Internal functions -/

/-- `_setNewTokenStorage` (`NTV/NativeTokenVaultBase.sol:565-575`): the three registry
maps, written together. -/
def setNewTokenStorage (V : Vault) (a : AssetId) (t : Address) (c : Chain) : Vault :=
  { V with tokenAddress := upd V.tokenAddress a t, assetId := upd V.assetId t a,
           originChainId := upd V.originChainId a c }

/-- `_getCreate2Salt` (`NTV/L2NativeTokenVault.sol:270-277`) for a given `L1_CHAIN_ID`:
the plain token address for an L1 token, a hash otherwise. -/
def saltOf (K : Cfg) (l1 origin : Chain) (tok : Address) : UInt256 :=
  if origin = l1 then tok else K.saltHash origin tok

/-- `calculateCreate2TokenAddress` (`NTV/L2NativeTokenVault.sol:255-265`), a public view. -/
def calculateCreate2TokenAddress (K : Cfg) (V : Vault) (origin : Chain) (tok : Address) : Address :=
  K.create2 (saltOf K V.l1ChainId origin tok) V.beacon

/-- `tokenDataOriginChainId` (`NTV/NativeTokenVaultBase.sol:542-548`): zero means L1;
undecodable metadata reverts. -/
def tokenDataOriginChainId (V : Vault) : Option Chain → Option Chain
  | none => none
  | some c => some (if c = 0 then V.l1ChainId else c)

/-- `_registerToken` (`NTV/NativeTokenVaultBase.sol:131-140`) and the storage write of
`_unsafeRegisterNativeToken` (:492-494).  Guards: the WETH rule (:133-136), code present
(:137), token not yet registered (:138).  Returns the new asset id. -/
def registerToken (K : Cfg) (V : Vault) (t : Address) : Option (Vault × AssetId) :=
  if (t ≠ V.weth ∨ K.thisChain = V.l1ChainId) ∧ V.code t = true ∧ V.assetId t = 0 then
    some (setNewTokenStorage V (K.encNTV K.thisChain t) t K.thisChain, K.encNTV K.thisChain t)
  else none

/-- The state after a successful bridged-token deployment for asset `a` with resolved
origin `(origin, originToken)`: code and proxy flag at the CREATE2 address,
`bridgeInitialize`'s `originToken`, the ghost record, then `_setNewTokenStorage`. -/
def deployedAt (K : Cfg) (V : Vault) (a : AssetId) (origin : Chain) (originToken : Address) : Vault :=
  setNewTokenStorage
    { V with
        code := upd V.code (calculateCreate2TokenAddress K V origin originToken) true
        proxy := upd V.proxy (calculateCreate2TokenAddress K V origin originToken) true
        tokOrigin := upd V.tokOrigin (calculateCreate2TokenAddress K V origin originToken) originToken
        deploys := V.deploys ++ [⟨a, calculateCreate2TokenAddress K V origin originToken, origin,
          originToken, V.beacon, V.l1ChainId⟩] }
    a (calculateCreate2TokenAddress K V origin originToken) origin

/-- `_ensureAndSaveTokenDeployed` (`NTV/NativeTokenVaultBase.sol:515-563, 597-610`).
Guards in source order: metadata decodes (:537), `assetIdCheck` (:557), not this chain's
own token (:603), `Create2.deploy` (:606; no code at the address, and the address-zero
exclusion of the header), `bridgeInitialize`'s nonzero origin token
(`bridge/BridgedStandardERC20.sol:83`).  Returns the deployed proxy. -/
def ensureAndSaveTokenDeployed (K : Cfg) (V : Vault) (a : AssetId) (originToken : Address)
    (mc : Option Chain) : Option (Vault × Address) :=
  match tokenDataOriginChainId V mc with
  | none => none
  | some origin =>
    if a = K.encNTV origin originToken ∧ origin ≠ K.thisChain
        ∧ V.code (calculateCreate2TokenAddress K V origin originToken) = false
        ∧ calculateCreate2TokenAddress K V origin originToken ≠ 0 ∧ originToken ≠ 0 then
      some (deployedAt K V a origin originToken, calculateCreate2TokenAddress K V origin originToken)
    else none

/-- `IBridgedStandardToken(t).bridgeMint(r, n)`.  On a proxy the vault deployed: OZ
`_mint` rejects the zero receiver and raises the supply.  On any other address: a hook.
Returns the proxy credited, if any. -/
def tokenMint (V : Vault) (t r : Address) (n : Nat) : Option (Vault × Option Address) :=
  if V.proxy t = true then
    if r ≠ 0 then some ({ V with supply := upd V.supply t (V.supply t + n) }, some t) else none
  else some (V, none)

/-- `IBridgedStandardToken(t).bridgeBurn(f, n)`.  On a proxy the vault deployed: OZ
`_burn` rejects the zero account and an amount above the balance (weakened here to the
supply) and lowers the supply.  On any other address: a hook.  Returns the proxy
debited, if any. -/
def tokenBurn (V : Vault) (t f : Address) (n : Nat) : Option (Vault × Option Address) :=
  if V.proxy t = true then
    if f ≠ 0 ∧ n ≤ V.supply t then
      some ({ V with supply := upd V.supply t (V.supply t - n) }, some t)
    else none
  else some (V, none)

/-- `_getOriginTokenFromAddress` (`NTV/L2NativeTokenVault.sol:307-312`,
`NTV/NativeTokenVaultBase.sol:122-124`): the base token's stored origin, a deployed
proxy's `originToken`, or whatever another token's getter returns. -/
def originOf (K : Cfg) (V : Vault) (t hookOrigin : Address) : Address :=
  if t = K.baseTokenAddr then V.baseOriginToken
  else if V.proxy t = true then V.tokOrigin t else hookOrigin

/-! ## Entry points -/

/-- `bridgeMint` (`NTV/NativeTokenVaultBase.sol:180-189`) with `_bridgeMintToken`
(:220-247).  Modifiers: zero value, router only, not paused.  A bridged asset
(`originChainId ≠ block.chainid`) with no token yet is deployed first (:233-235), then
minted (:243); a native asset is released by `_withdrawFunds`, which rejects the base
token (`NTV/L2NativeTokenVault.sol:196-199`).  Returns the proxy credited, if any. -/
def bridgeMint (K : Cfg) (V : Vault) (caller : Address) (value : UInt256) (a : AssetId)
    (md : MintData) : Option (Vault × Option Address) :=
  if value = 0 ∧ caller = K.router ∧ V.own.paused = false then
    if V.originChainId a ≠ K.thisChain then
      if V.tokenAddress a = 0 then
        match ensureAndSaveTokenDeployed K V a md.originToken md.metaChain with
        | none => none
        | some (V1, t) => tokenMint V1 t md.receiver md.amount.val
      else tokenMint V (V.tokenAddress a) md.receiver md.amount.val
    else if a ≠ V.baseAssetId then some (V, none) else none
  else none

/-- `bridgeRecoverFailedTransfer` (`NTV/NativeTokenVaultBase.sol:195-214`) with the L2
`_disburseFailedTransfer` (`NTV/L2NativeTokenVault.sol:204-227`,
`NTV/NativeTokenVaultBase.sol:264-286`).  The base token goes to the base-token holder
(a hook); a native asset is released; a bridged asset is minted to the data's
`originalCaller`, after a deployment if it has no token yet.  Returns the proxy
credited, if any. -/
def bridgeRecoverFailedTransfer (K : Cfg) (V : Vault) (caller : Address) (value : UInt256)
    (a : AssetId) (md : MintData) : Option (Vault × Option Address) :=
  if value = 0 ∧ caller = K.router ∧ V.own.paused = false then
    if a = V.baseAssetId then some (V, none)
    else if V.originChainId a = K.thisChain then some (V, none)
    else if V.tokenAddress a = 0 then
      match ensureAndSaveTokenDeployed K V a md.originToken md.metaChain with
      | none => none
      | some (V1, t) => tokenMint V1 t md.originalCaller md.amount.val
    else tokenMint V (V.tokenAddress a) md.originalCaller md.amount.val
  else none

/-- `_decodeBurnAndCheckAssetId`'s resolved token (`NTV/NativeTokenVaultBase.sol:337-347`):
the data's token, or the registered one when the data leaves it zero. -/
def parsedToken (V : Vault) (a : AssetId) (bd : BurnData) : Address :=
  if bd.token = 0 then V.tokenAddress a else bd.token

/-- `_getTokenAndBridgeToChain` (`NTV/NativeTokenVaultBase.sol:425-457`).  The base token
needs `amount == msg.value` and moves through hooks.  Any other asset needs zero value;
a bridged one is burned from `originalCaller`, a native one is pulled by a hook.
Returns the proxy debited, if any. -/
def getTokenAndBridgeToChain (K : Cfg) (V : Vault) (value : UInt256) (a : AssetId)
    (t originalCaller : Address) (amount : UInt256) : Option (Vault × Option Address) :=
  if a = V.baseAssetId then
    if amount = value then some (V, none) else none
  else if value = 0 then
    if V.originChainId a ≠ K.thisChain then tokenBurn V t originalCaller amount.val
    else some (V, none)
  else none

/-- `bridgeBurn` (`NTV/NativeTokenVaultBase.sol:294-318`) with
`_decodeBurnAndCheckAssetId` (:337-354) and `_bridgeBurnToken` (:361-410).  Guards in
source order: zero `_l2MsgValue`, router only, not paused, a resolved nonzero token whose
recorded asset id is the supplied one (:350-353), nonzero amount (:370), no native WETH
(:375); then the funds move; then, for a bridged asset, a nonzero origin token (:392) and
a nonzero recorded origin chain (:420).  Returns the bridge-mint data and the proxy
debited, if any. -/
def bridgeBurn (K : Cfg) (V : Vault) (caller : Address) (value l2MsgValue : UInt256)
    (a : AssetId) (originalCaller : Address) (bd : BurnData) (hookOrigin : Address) :
    Option (Vault × MintData × Option Address) :=
  if l2MsgValue = 0 ∧ caller = K.router ∧ V.own.paused = false
      ∧ parsedToken V a bd ≠ 0 ∧ V.assetId (parsedToken V a bd) = a ∧ bd.amount ≠ 0
      ∧ (V.originChainId a ≠ K.thisChain ∨ parsedToken V a bd ≠ V.weth) then
    match getTokenAndBridgeToChain K V value a (parsedToken V a bd) originalCaller bd.amount with
    | none => none
    | some (V1, tok) =>
      if V.originChainId a ≠ K.thisChain then
        if originOf K V (parsedToken V a bd) hookOrigin ≠ 0 ∧ V.originChainId a ≠ 0 then
          some (V1, ⟨originalCaller, bd.receiver, originOf K V (parsedToken V a bd) hookOrigin,
            bd.amount, some (V.originChainId a)⟩, tok)
        else none
      else
        some (V1, ⟨originalCaller, bd.receiver, parsedToken V a bd, bd.amount,
          some (V.originChainId a)⟩, tok)
  else none

/-- `tryRegisterTokenFromBurnData` (`NTV/NativeTokenVaultBase.sol:321-335`), without the
router callback: nonzero token (:325), unregistered (:328), `_registerToken`, and the new
id is the expected one (:334). -/
def tryRegisterTokenFromBurnData (K : Cfg) (V : Vault) (bd : BurnData) (expected : AssetId) :
    Option Vault :=
  if bd.token ≠ 0 ∧ V.assetId bd.token = 0 then
    match registerToken K V bd.token with
    | none => none
    | some (V1, newId) => if newId = expected then some V1 else none
  else none

/-- `updateL2` (`NTV/L2NativeTokenVault.sol:134-174`).  Guards in source order: upgrader
only, nonzero WETH (:142), WETH frozen once set (:145), `L1_CHAIN_ID` frozen once set
(:148), `BASE_TOKEN_ASSET_ID` frozen once set (:152-155), and a nonzero owner when the
owner changes (:171).  It writes the base token's registry entry unconditionally
(:165-167). -/
def updateL2 (K : Cfg) (V : Vault) (caller : Address) (l1 : Chain) (newOwner weth : Address)
    (b : BaseTokenData) : Option Vault :=
  if caller = K.upgrader ∧ weth ≠ 0 ∧ (V.weth = 0 ∨ V.weth = weth)
      ∧ (V.l1ChainId = 0 ∨ V.l1ChainId = l1)
      ∧ (V.baseAssetId = 0 ∨ V.baseAssetId = b.assetId)
      ∧ (V.own.owner = newOwner ∨ newOwner ≠ 0) then
    some { V with
      weth := weth, baseAssetId := b.assetId, l1ChainId := l1, baseOriginToken := b.originToken
      tokenAddress := upd V.tokenAddress b.assetId K.baseTokenAddr
      assetId := upd V.assetId K.baseTokenAddr b.assetId
      originChainId := upd V.originChainId b.assetId b.originChainId
      own := if V.own.owner = newOwner then V.own else V.own.setOwner newOwner }
  else none

/-- `initL2` (`NTV/L2NativeTokenVault.sol:99-115`): once only
(`reentrancyGuardInitializer`), then `updateL2`, then a nonzero beacon is stored
(:110-113). -/
def initL2 (K : Cfg) (V : Vault) (caller : Address) (l1 : Chain) (newOwner beacon weth : Address)
    (b : BaseTokenData) : Option Vault :=
  if V.initialized = false then
    match updateL2 K { V with initialized := true } caller l1 newOwner weth b with
    | none => none
    | some V1 => if beacon ≠ 0 then some { V1 with beacon := beacon } else none
  else none

/-- One call, with its arguments. -/
inductive Op where
  | initL2 (l1 : Chain) (newOwner beacon weth : Address) (b : BaseTokenData)
  | updateL2 (l1 : Chain) (newOwner weth : Address) (b : BaseTokenData)
  | registerToken (t : Address)
  | tryRegisterTokenFromBurnData (bd : BurnData) (expected : AssetId)
  | bridgeMint (value : UInt256) (a : AssetId) (md : MintData)
  | bridgeRecoverFailedTransfer (value : UInt256) (a : AssetId) (md : MintData)
  | bridgeBurn (value l2MsgValue : UInt256) (a : AssetId) (originalCaller : Address)
      (bd : BurnData) (hookOrigin : Address)
  | owner (o : OwnerOp)
  /-- Environment: another account deploys code at a nonzero address that has none. -/
  | envDeploy (t : Address)

/-- One call by `caller`.  `none` is a revert. -/
def exec (K : Cfg) (caller : Address) (V : Vault) : Op → Option Vault
  | .initL2 l1 o beacon weth b => initL2 K V caller l1 o beacon weth b
  | .updateL2 l1 o weth b => updateL2 K V caller l1 o weth b
  | .registerToken t => (registerToken K V t).map Prod.fst
  | .tryRegisterTokenFromBurnData bd expected => tryRegisterTokenFromBurnData K V bd expected
  | .bridgeMint value a md => (bridgeMint K V caller value a md).map Prod.fst
  | .bridgeRecoverFailedTransfer value a md =>
      (bridgeRecoverFailedTransfer K V caller value a md).map Prod.fst
  | .bridgeBurn value l2MsgValue a originalCaller bd hookOrigin =>
      (bridgeBurn K V caller value l2MsgValue a originalCaller bd hookOrigin).map Prod.fst
  | .owner o => (V.own.exec caller o).map fun own => { V with own := own }
  | .envDeploy t =>
      if V.code t = false ∧ t ≠ 0 then some { V with code := upd V.code t true } else none

/-- One successful call by any caller. -/
def Step (K : Cfg) (V V' : Vault) : Prop := ∃ caller op, exec K caller V op = some V'

/-- Any number of calls, in any order. -/
def Reach (K : Cfg) : Vault → Vault → Prop := Relation.ReflTransGen (Step K)

/-! ## A variant without `assetIdCheck`, for the countermodel -/

/-- `_ensureAndSaveTokenDeployed` with the `assetIdCheck` of
`NTV/NativeTokenVaultBase.sol:557` removed.  Not the deployed code. -/
def ensureAndSaveTokenDeployedNoIdCheck (K : Cfg) (V : Vault) (a : AssetId) (originToken : Address)
    (mc : Option Chain) : Option (Vault × Address) :=
  match tokenDataOriginChainId V mc with
  | none => none
  | some origin =>
    if origin ≠ K.thisChain
        ∧ V.code (calculateCreate2TokenAddress K V origin originToken) = false
        ∧ calculateCreate2TokenAddress K V origin originToken ≠ 0 ∧ originToken ≠ 0 then
      some (deployedAt K V a origin originToken, calculateCreate2TokenAddress K V origin originToken)
    else none

end Contracts.L2NativeTokenVault
