import EraSpec.Contracts.L2ComplexUpgrader.Specs.SystemProxy

/-!
# Model: the L2 upgrade path

**This file is definitions only.** Statements are in the `Properties/` modules of this folder
(`ForceDeployments`, `Authority`, `GenesisOnce`, `Witness`), proofs in `Proofs/`.

Source: era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`, under
`l1-contracts/contracts/`:

* `l2-upgrades/L2ComplexUpgrader.sol`, `L2GenesisForceDeploymentsHelper.sol`,
  `L2GenesisUpgrade.sol`, `L2DefaultUpgrade.sol`, `SystemContractProxy.sol`,
  `SystemContractProxyAdmin.sol`;
* `l2-system/zksync-os/ContractDeployer.sol` (the one function the helper calls);
* OpenZeppelin v4.9.6 `proxy/transparent/ProxyAdmin.sol`, `access/Ownable.sol`.

## The contracts and who may call what

    FORCE_DEPLOYER ──▶ L2ComplexUpgrader.forceDeployAndUpgradeUniversal / upgrade   (onlyForceDeployer, :22-27)
        for each row: L2GenesisForceDeploymentsHelper.conductContractUpgrade        (:41-47; helper :162-175)
            unsafe row  ──▶ ContractDeployer.setBytecodeDetailsEVM                  (onlyComplexUpgrader, ContractDeployer.sol:16-29)
            proxy row   ──▶ … setBytecodeDetailsEVM, proxy.forceInitAdmin,
                            SystemContractProxyAdmin.upgrade ──▶ proxy.upgradeTo    (helper :113-154)
        then delegatecall `_delegateTo`                                             (:58-69)
            L2GenesisUpgrade.genesisUpgrade / L2DefaultUpgrade.upgrade
                ──▶ helper.performForceDeployedContractsInit                        (helper :187-235)

The helper is a library of `internal` functions, so its code runs inside the complex upgrader:
`address(this)` and the `msg.sender` its callees see are `L2_COMPLEX_UPGRADER_ADDR`. The
delegatecalled upgrade contract runs the same way.

## State

`World` holds what these contracts decide on and write:

* `code a`: the bytecode details the `SET_BYTECODE_ON_ADDRESS_HOOK` recorded for `a`. The model
  reads `a.code.length` and `extcodehash(a)` from it (`MODEL-L2UP-HOOK`).
* `admin a`, `impl a`: the two ERC-1967 slots in the storage of `a`.
* `owner`: `Ownable._owner` of the `SystemContractProxyAdmin` at
  `L2_SYSTEM_CONTRACT_PROXY_ADMIN_ADDR`.
* `inited b`: the storage word that `initL2` of built-in `b` tests before it runs
  (`BuiltIn`).

## Model boundary

* `MODEL-L2UP-HOOK`. The hook is a ZKsync OS system hook, not Solidity. The model takes
  `setBytecodeDetailsEVM(a, hash, len, observableHash)` to make `a.code.length = len` and
  `extcodehash(a) = observableHash`, and to change nothing else. Whether the hook accepts a call
  is `Env.hookAccepts`. Code created by `CREATE`/`CREATE2` is not modelled: `code` changes only
  through the hook.
* `MODEL-L2UP-PROXYCODE`. Which bytecode is the `SystemContractProxy` is `Env.isProxyCode`. A
  call through the proxy interface to an address whose code is not that (or that has no code) has
  no transition in this model. The source never checks it: `upgradeSystemContractProxy` deploys
  whatever proxy bytecode the row names and calls it.
* `MODEL-L2UP-IMPL`. A call that a proxy forwards to its implementation is not followed. When an
  outside caller makes it, the model takes an idle step (the implementation is assumed not to
  write the two ERC-1967 slots, the proxy admin's owner, or the `inited` words; the entry points
  that do write `inited` are the `initL2` calls, modelled separately). When the proxy admin makes
  it, the model has a transition only if the implementation slot points at an address with no
  code, where the delegatecall succeeds and does nothing; otherwise there is none.
* `MODEL-L2UP-DELEGATE`. `L2ComplexUpgrader.upgrade` delegatecalls whatever `_delegateTo` holds.
  The label says which program that is: `genesisUpgrade`, `defaultUpgrade`, or `custom w'`, any
  other code, which may leave the world in any state `w'`. The model does not tie the label to
  the bytecode at `_delegateTo`; it keeps the source's one check, `code.length != 0`.
* `MODEL-L2UP-INIT`. Of `performForceDeployedContractsInit` the model keeps the writes to the
  state above and the checks on it: `_setupProxyAdmin`, the governance zero check, and for genesis
  the one-shot guard of each `initL2`, in source order. Every other step (decoding, the WETH proxy,
  `updateL2`, `setAddresses`, the remaining `initL2` checks) is the label's `restOk`. The built-ins
  are assumed to run the implementations of this commit.
* Byte strings are opaque: `Env.decodeInfo`, `Env.decodePair` and `Env.randomAddress` stand for
  `abi.decode`, the canonical-encoding check, and `keccak256`. Nothing is assumed about them
  (`SOL-ABI`); in particular no injectivity.
* A revert is `none`. Events, gas, `msg.value` of the upgrader's payable functions, and return
  data are not modelled.
* Top-level transactions are atomic and do not re-enter the modelled contracts. The modelled
  contracts make calls only from the code transcribed here, so a transaction whose sender is the
  upgrader or the proxy admin does not occur (`Tx.External`).
-/

namespace Contracts.L2ComplexUpgrader

/-! ## Roles and oracles -/

/-- The three addresses the contracts compare against. -/
structure Roles where
  /-- `L2_FORCE_DEPLOYER_ADDR`, checked by `onlyForceDeployer` (`L2ComplexUpgrader.sol:22-27`). The
  L1 side makes it the sender of every upgrade transaction
  (`L2CanonicalTransactionLib.sol:56`). -/
  forceDeployer : Address
  /-- `L2_COMPLEX_UPGRADER_ADDR`: the address the upgrader's code runs at, checked by
  `SystemContractProxy.sol:51`, `SystemContractProxyAdmin.sol:10-15`, `ContractDeployer.sol:16-21`
  and every `initL2`. -/
  upgrader : Address
  /-- `L2_SYSTEM_CONTRACT_PROXY_ADMIN_ADDR`: where the `SystemContractProxyAdmin` lives. -/
  proxyAdmin : Address

/-- The deployed values (`L2ContractAddresses.sol:53, 65, 115`): `0x8000 + 0x07`,
`0x8000 + 0x0f`, `0x10000 + 0x0c`. -/
def deployedRoles : Roles := ⟨0x8007, 0x800f, 0x1000c⟩

/-- A `bytes` value. The model never looks inside one, except for its length. -/
abbrev Bytes := List UInt8

/-- What `setBytecodeDetailsEVM` records for an address
(`ContractDeployer.sol:24-29`, `ZKSyncOSBytecodeInfo.sol:34-40`). -/
structure BytecodeInfo where
  /-- The Blake2b hash of the bytecode. -/
  blakeHash : UInt256
  /-- The bytecode length (`uint32` in the source); `a.code.length`. -/
  length : UInt256
  /-- The observable (Keccak) hash; `extcodehash(a)`. -/
  observableHash : UInt256
deriving DecidableEq

/-- Everything the model does not compute. -/
structure Env where
  /-- `abi.decode(b, (bytes32, uint32, bytes32))` (`ZKSyncOSBytecodeInfo.sol:47-54`); `none` when
  it reverts. -/
  decodeInfo : Bytes → Option BytecodeInfo
  /-- The first three statements of `upgradeSystemContractProxy`
  (`L2GenesisForceDeploymentsHelper.sol:115-122`): the length check, `abi.decode(b, (bytes, bytes))`
  and the canonical-encoding check. `none` when any of them reverts; otherwise the implementation's
  bytecode info and the proxy's. -/
  decodePair : Bytes → Option (Bytes × Bytes)
  /-- `generateRandomAddress` (`:109-111`): the low 160 bits of `keccak256(bytes32(0) ++ b)`. -/
  randomAddress : Bytes → Address
  /-- Whether `SET_BYTECODE_ON_ADDRESS_HOOK` accepts these details for this address
  (`ContractDeployer.sol:30-36`). -/
  hookAccepts : Address → BytecodeInfo → Bool
  /-- Whether these details are those of the `SystemContractProxy` bytecode. -/
  isProxyCode : BytecodeInfo → Bool

/-! ## State -/

/-- The built-in contracts whose `initL2` the genesis upgrade calls, in call order
(`L2GenesisForceDeploymentsHelper.sol:253-291, 356-374`). Each `initL2` is `onlyUpgrader` and
reverts when its own flag is already set:

* `reentrancyGuardInitializer` (`ReentrancyGuard.sol:43-63`, the lock slot must be zero):
  `L2MessageRoot.sol:67`, `L2Bridgehub.sol:60-64`, `L2AssetRouter.sol:154-159`,
  `L2NativeTokenVault.sol:99-106`, `L2ChainAssetHandler.sol:89`, `L2AssetTracker.sol:96`,
  `L2InteropHandler.sol:34`, `InteropCenter.sol:170-174`;
* `baseTokenHolderBalanceInitialized` (`L2BaseToken.sol:64-68`);
* `IMT.setup`'s `_leafNumber != 0` (`L2InteropCommitmentTree.sol:45-48`);
* `L1_CHAIN_ID != 0` (`AtomicFlowManager.sol:76-79`). -/
inductive BuiltIn where
  | messageRoot | bridgehub | assetRouter | nativeTokenVault | chainAssetHandler
  | assetTracker | interopHandler | interopCenter | baseToken | commitmentTree
  | atomicFlowManager
deriving DecidableEq

/-- The state the L2 upgrade path reads and writes. -/
structure World where
  /-- The bytecode details recorded for each address; all zero where nothing was set. -/
  code : Address → BytecodeInfo
  /-- The ERC-1967 admin slot of each address. -/
  admin : Address → Address
  /-- The ERC-1967 implementation slot of each address. -/
  impl : Address → Address
  /-- The owner of the `SystemContractProxyAdmin`. -/
  owner : Address
  /-- Whether the one-shot flag of each built-in's `initL2` is set. -/
  inited : BuiltIn → Bool

/-- `a.code.length != 0`. -/
def World.hasCode (w : World) (a : Address) : Bool := decide ((w.code a).length ≠ 0)

/-- The address holds `SystemContractProxy` code. -/
def IsProxy (E : Env) (w : World) (a : Address) : Bool := w.hasCode a && E.isProxyCode (w.code a)

/-- The two ERC-1967 slots of `a`, as a proxy state. -/
def World.proxyState (w : World) (a : Address) : ProxyState := ⟨w.admin a, w.impl a⟩

/-- Write both ERC-1967 slots of `a`. -/
def World.setProxy (w : World) (a : Address) (s : ProxyState) : World :=
  { w with admin := Function.update w.admin a s.admin, impl := Function.update w.impl a s.impl }

/-- The hook's write: record details for `a`. -/
def World.setCode (w : World) (a : Address) (i : BytecodeInfo) : World :=
  { w with code := Function.update w.code a i }

/-! ## Calls to a proxy -/

/-- A call to `p` through the proxy interface made by a modelled contract (the upgrader or the
proxy admin). `p` must hold proxy code (`MODEL-L2UP-PROXYCODE`). If the proxy forwards the call,
the model follows it only into an implementation address with no code, where the delegatecall
succeeds and changes nothing (`MODEL-L2UP-IMPL`). -/
def callProxyFromContract (K : Roles) (E : Env) (w : World) (sender p : Address)
    (value : UInt256) (c : ProxyCall) : Option World :=
  if IsProxy E w p then
    match fallback K.upgrader w.hasCode sender value (w.proxyState p) c with
    | .handled s' => some (w.setProxy p s')
    | .delegated => if w.hasCode (w.impl p) then none else some w
    | .reverted => none
  else none

/-- A call to `p` through the proxy interface made by an outside caller. A forwarded call is an
idle step (`MODEL-L2UP-IMPL`). -/
def callProxyFromOutside (K : Roles) (E : Env) (w : World) (sender p : Address)
    (value : UInt256) (c : ProxyCall) : Option World :=
  if IsProxy E w p then
    match fallback K.upgrader w.hasCode sender value (w.proxyState p) c with
    | .handled s' => some (w.setProxy p s')
    | .delegated => some w
    | .reverted => none
  else none

/-- The three `onlyOwner` functions of `ProxyAdmin` that call a proxy (`ProxyAdmin.sol:51-80`):
the owner check (`Ownable.sol:50-52`), then the call, whose `msg.sender` is the proxy admin. -/
def proxyAdminCall (K : Roles) (E : Env) (w : World) (sender p : Address) (value : UInt256)
    (c : ProxyCall) : Option World :=
  if sender ≠ w.owner then none else callProxyFromContract K E w K.proxyAdmin p value c

/-! ## Force deployments (`L2GenesisForceDeploymentsHelper.sol:74-175`) -/

/-- `unsafeForceDeploy` (`:74-94`), running inside the upgrader: the length check, the decode,
then `ContractDeployer.setBytecodeDetailsEVM`, whose `onlyComplexUpgrader` passes because the
caller is the upgrader, and which reverts when the hook refuses. -/
def unsafeForceDeploy (E : Env) (w : World) (b : Bytes) (a : Address) : Option World :=
  if b.length ≠ 96 then none                                    -- :76
  else match E.decodeInfo b with                                -- :79-80
    | none => none
    | some i => if E.hookAccepts a i then some (w.setCode a i) else none  -- :90-93

/-- `forceDeployOnAddress` (`:96-104`): the address must have no code and lie above the
precompile range. -/
def forceDeployOnAddress (E : Env) (w : World) (b : Bytes) (a : Address) : Option World :=
  if w.hasCode a then none                                      -- :97
  else if (0xFF : UInt256) < a then unsafeForceDeploy E w b a   -- :100-103
  else none

/-- The implementation half of `upgradeSystemContractProxy` (`:124-142`): deploy the
implementation at its derived address if nothing is there, otherwise require the code hash there
to be the listed one. -/
def ensureImplementation (E : Env) (w : World) (ib : Bytes) : Option World :=
  if w.hasCode (E.randomAddress ib) then
    match E.decodeInfo ib with                                  -- :137
    | none => none
    | some i =>
        if (w.code (E.randomAddress ib)).observableHash = i.observableHash then some w
        else none                                               -- :139-141
  else forceDeployOnAddress E w ib (E.randomAddress ib)         -- :126-127

/-- The proxy half of `upgradeSystemContractProxy` (`:144-148`): if `a` has no code, deploy the
proxy there and have the upgrader call `forceInitAdmin(L2_SYSTEM_CONTRACT_PROXY_ADMIN_ADDR)`. -/
def ensureProxy (K : Roles) (E : Env) (w : World) (pb : Bytes) (a : Address) : Option World :=
  if w.hasCode a then some w
  else (forceDeployOnAddress E w pb a).bind fun w' =>
    callProxyFromContract K E w' K.upgrader a 0 (.forceInitAdmin K.proxyAdmin)

/-- `upgradeSystemContractProxy` (`:113-154`), running inside the upgrader: decode, ensure the
implementation, ensure the proxy, then `SystemContractProxyAdmin.upgrade(a, implAddress)` with the
upgrader as its caller. -/
def upgradeSystemContractProxy (K : Roles) (E : Env) (w : World) (b : Bytes) (a : Address) :
    Option World :=
  match E.decodePair b with                                     -- :115-122
  | none => none
  | some (ib, pb) =>
      (ensureImplementation E w ib).bind fun w1 =>
      (ensureProxy K E w1 pb a).bind fun w2 =>
      proxyAdminCall K E w2 K.upgrader a 0 (.upgradeTo (E.randomAddress ib))  -- :150-153

/-- `IComplexUpgrader.ContractUpgradeType` (`IComplexUpgrader.sol:19-23`). -/
inductive UpgradeType where
  /-- Ordinal 0, retired. -/
  | deprecatedEraForceDeployment
  | systemProxyUpgrade
  | unsafeForceDeployment
deriving DecidableEq

/-- `IComplexUpgrader.UniversalContractUpgradeInfo` (`IComplexUpgrader.sol:29-33`). -/
structure Row where
  upgradeType : UpgradeType
  deployedBytecodeInfo : Bytes
  newAddress : Address

/-- `conductContractUpgrade` (`:162-175`). -/
def conductContractUpgrade (K : Roles) (E : Env) (w : World) (r : Row) : Option World :=
  match r.upgradeType with
  | .unsafeForceDeployment => unsafeForceDeploy E w r.deployedBytecodeInfo r.newAddress
  | .systemProxyUpgrade => upgradeSystemContractProxy K E w r.deployedBytecodeInfo r.newAddress
  | .deprecatedEraForceDeployment => none                       -- :172

/-- The loop of `forceDeployAndUpgradeUniversal` (`L2ComplexUpgrader.sol:41-47`). -/
def conductAll (K : Roles) (E : Env) : World → List Row → Option World
  | w, [] => some w
  | w, r :: rs => (conductContractUpgrade K E w r).bind fun w' => conductAll K E w' rs

/-- The implementation the rows name for `a`, starting from `cur`: the derived address of the
last system-proxy row whose `newAddress` is `a`, or `cur` if there is none. -/
def plannedImpl (E : Env) : List Row → Address → Address → Address
  | [], _, cur => cur
  | r :: rs, a, cur =>
      plannedImpl E rs a
        (if r.upgradeType = .systemProxyUpgrade ∧ r.newAddress = a then
          match E.decodePair r.deployedBytecodeInfo with
          | some (ib, _) => E.randomAddress ib
          | none => cur
        else cur)

/-! ## The delegatecalled upgrade (`L2GenesisUpgrade.sol`, `L2DefaultUpgrade.sol`) -/

/-- `initL2` of built-in `b`, called by `sender`: `onlyUpgrader` and the one-shot guard (see
`BuiltIn`). Both revert, so their order does not show. -/
def initL2 (K : Roles) (sender : Address) (w : World) (b : BuiltIn) : Option World :=
  if sender ≠ K.upgrader then none
  else if w.inited b then none
  else some { w with inited := Function.update w.inited b true }

/-- The `initL2` calls of the genesis upgrade, in source order
(`L2GenesisForceDeploymentsHelper.sol:253, 255, 262, 279, 288, 356, 361, 363, 371, 373, 374`). -/
def genesisInitOrder : List BuiltIn :=
  [.messageRoot, .bridgehub, .assetRouter, .nativeTokenVault, .chainAssetHandler,
   .assetTracker, .interopHandler, .interopCenter, .baseToken, .commitmentTree,
   .atomicFlowManager]

/-- The upgrader calling `initL2` on each built-in of a list, in order. -/
def initAll (K : Roles) : World → List BuiltIn → Option World
  | w, [] => some w
  | w, b :: bs => (initL2 K K.upgrader w b).bind fun w' => initAll K w' bs

/-- `performForceDeployedContractsInit` (`L2GenesisForceDeploymentsHelper.sol:187-235`), running
inside the upgrader, cut down to the modelled state (`MODEL-L2UP-INIT`): `_setupProxyAdmin`
(`:202, 237-244`) makes the upgrader the proxy admin's owner, the governance address must be
nonzero (`:206`), and the genesis branch calls every `initL2` (`:219-224, 230-232`). -/
def performInit (K : Roles) (w : World) (governance : Address) (isGenesis restOk : Bool) :
    Option World :=
  if governance = 0 then none
  else if restOk then
    if isGenesis then initAll K { w with owner := K.upgrader } genesisInitOrder
    else some { w with owner := K.upgrader }
  else none

/-- What the code at `_delegateTo` does (`MODEL-L2UP-DELEGATE`). -/
inductive UpgradeAction where
  /-- `L2GenesisUpgrade.genesisUpgrade(chainId, …)` (`L2GenesisUpgrade.sol:22-40`), with the
  `aliasedL1Governance` field of its fixed data. -/
  | genesisUpgrade (chainId : UInt256) (governance : Address) (restOk : Bool)
  /-- `L2DefaultUpgrade.upgrade(…)` (`L2DefaultUpgrade.sol:16-27`). -/
  | defaultUpgrade (governance : Address) (restOk : Bool)
  /-- Any other code, leaving the world as `w'`. -/
  | custom (w' : World)

/-- The delegatecall of `L2ComplexUpgrader.upgrade` (`L2ComplexUpgrader.sol:63-68`). -/
def runAction (K : Roles) (w : World) : UpgradeAction → Option World
  | .genesisUpgrade chainId governance restOk =>
      if chainId = 0 then none                                  -- L2GenesisUpgrade.sol:28-30
      else performInit K w governance true restOk               -- :32-37
  | .defaultUpgrade governance restOk => performInit K w governance false restOk
  | .custom w' => some w'

/-! ## The complex upgrader (`L2ComplexUpgrader.sol`) -/

/-- `upgrade` (`:58-69`): `onlyForceDeployer`, the target must have code, then the
delegatecall. -/
def upgrade (K : Roles) (w : World) (sender delegateTo : Address) (act : UpgradeAction) :
    Option World :=
  if sender ≠ K.forceDeployer then none                         -- :23-25
  else if w.hasCode delegateTo then runAction K w act           -- :59-61, :63
  else none

/-- `forceDeployAndUpgradeUniversal` (`:35-50`): `onlyForceDeployer`, the rows in order, then
`upgrade` (an internal call, so the same `msg.sender`). -/
def forceDeployAndUpgradeUniversal (K : Roles) (E : Env) (w : World) (sender : Address)
    (rows : List Row) (delegateTo : Address) (act : UpgradeAction) : Option World :=
  if sender ≠ K.forceDeployer then none                         -- :23-25
  else (conductAll K E w rows).bind fun w' => upgrade K w' sender delegateTo act  -- :41-49

/-! ## Every entry point -/

/-- The state-changing entry points of the modelled contracts. -/
inductive Call where
  /-- `L2ComplexUpgrader.forceDeployAndUpgradeUniversal`. -/
  | forceDeployAndUpgradeUniversal (rows : List Row) (delegateTo : Address) (act : UpgradeAction)
  /-- `L2ComplexUpgrader.upgrade`. -/
  | upgrade (delegateTo : Address) (act : UpgradeAction)
  /-- `SystemContractProxyAdmin.forceSetOwner` (`SystemContractProxyAdmin.sol:23-25`). -/
  | forceSetOwner (newOwner : Address)
  /-- `Ownable.transferOwnership` on the proxy admin (`Ownable.sol:69-72`). -/
  | transferOwnership (newOwner : Address)
  /-- `Ownable.renounceOwnership` on the proxy admin (`Ownable.sol:61-63`). -/
  | renounceOwnership
  /-- `ProxyAdmin.upgrade(proxy, impl)` (`ProxyAdmin.sol:62-64`). -/
  | adminUpgrade (proxy newImpl : Address)
  /-- `ProxyAdmin.upgradeAndCall(proxy, impl, data)` (`ProxyAdmin.sol:74-80`); `initOk` as in
  `ProxyCall.upgradeToAndCall`. -/
  | adminUpgradeAndCall (proxy newImpl : Address) (value : UInt256) (initOk : Bool)
  /-- `ProxyAdmin.changeProxyAdmin(proxy, newAdmin)` (`ProxyAdmin.sol:51-53`). -/
  | changeProxyAdmin (proxy newAdmin : Address)
  /-- Any call to the address `p`, through the proxy code there. -/
  | proxy (p : Address) (value : UInt256) (c : ProxyCall)
  /-- `ContractDeployer.setBytecodeDetailsEVM` (`ContractDeployer.sol:24-37`). -/
  | setBytecodeDetailsEVM (a : Address) (i : BytecodeInfo)
  /-- `initL2` of a built-in. -/
  | initL2 (b : BuiltIn)

/-- One call by `sender`. `none` is a revert. -/
def exec (K : Roles) (E : Env) (sender : Address) (w : World) : Call → Option World
  | .forceDeployAndUpgradeUniversal rows delegateTo act =>
      forceDeployAndUpgradeUniversal K E w sender rows delegateTo act
  | .upgrade delegateTo act => upgrade K w sender delegateTo act
  | .forceSetOwner o =>
      if sender ≠ K.upgrader then none                          -- SystemContractProxyAdmin.sol:11-13
      else some { w with owner := o }                           -- :24, no zero check
  | .transferOwnership o =>
      if sender ≠ w.owner then none                             -- Ownable.sol:51
      else if o = 0 then none                                   -- Ownable.sol:70
      else some { w with owner := o }
  | .renounceOwnership =>
      if sender ≠ w.owner then none else some { w with owner := 0 }
  | .adminUpgrade p n => proxyAdminCall K E w sender p 0 (.upgradeTo n)
  | .adminUpgradeAndCall p n value initOk =>
      proxyAdminCall K E w sender p value (.upgradeToAndCall n initOk)
  | .changeProxyAdmin p n => proxyAdminCall K E w sender p 0 (.changeAdmin n)
  | .proxy p value c => callProxyFromOutside K E w sender p value c
  | .setBytecodeDetailsEVM a i =>
      if sender ≠ K.upgrader then none                          -- ContractDeployer.sol:17-19
      else if E.hookAccepts a i then some (w.setCode a i) else none  -- :30-36
  | .initL2 b => initL2 K sender w b

/-! ## Transactions and runs -/

/-- A top-level transaction. -/
structure Tx where
  sender : Address
  call : Call

/-- The transactions succeed one after another from `w`; `none` if any reverts. -/
def runTxs (K : Roles) (E : Env) : World → List Tx → Option World
  | w, [] => some w
  | w, t :: ts => (exec K E t.sender w t.call).bind fun w' => runTxs K E w' ts

/-- `txs` is a sequence of successful transactions taking `w` to `w'`. -/
def Run (K : Roles) (E : Env) (w : World) (txs : List Tx) (w' : World) : Prop :=
  runTxs K E w txs = some w'

/-- The sender is neither of the two modelled contracts. Those call only from their own code,
which `exec` already contains, so they never send a top-level transaction. -/
def Tx.External (K : Roles) (t : Tx) : Prop :=
  t.sender ≠ K.upgrader ∧ t.sender ≠ K.proxyAdmin

/-- The delegatecalled program of a call, if it is a call to the complex upgrader. -/
def Call.action? : Call → Option UpgradeAction
  | .forceDeployAndUpgradeUniversal _ _ act => some act
  | .upgrade _ act => some act
  | _ => none

/-- The call delegatecalls code other than the genesis or the default upgrade. -/
def Call.IsCustom (c : Call) : Prop := ∃ w', c.action? = some (.custom w')

/-- The call delegatecalls `L2GenesisUpgrade.genesisUpgrade`. -/
def Call.IsGenesis (c : Call) : Prop :=
  ∃ chainId governance restOk, c.action? = some (.genesisUpgrade chainId governance restOk)

/-- The call is to the complex upgrader. -/
def Call.IsUpgraderCall (c : Call) : Prop := c.action?.isSome = true

end Contracts.L2ComplexUpgrader
