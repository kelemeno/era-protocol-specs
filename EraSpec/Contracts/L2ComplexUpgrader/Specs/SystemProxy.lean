import EraSpec.Core.Word

/-!
# Model: `SystemContractProxy`, one proxy

**This file is definitions only.** Statements are in
`EraSpec.Contracts.L2ComplexUpgrader.Properties.SystemProxy`, proofs in
`EraSpec.Contracts.L2ComplexUpgrader.Proofs.SystemProxy`.

Source: era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`,
`l1-contracts/contracts/l2-upgrades/SystemContractProxy.sol`, and OpenZeppelin v4.9.6
(`lib/openzeppelin-contracts-v4` at `dc44c9f1`): `proxy/transparent/TransparentUpgradeableProxy.sol`,
`proxy/ERC1967/ERC1967Upgrade.sol`, `proxy/Proxy.sol`.

## What the source does

The proxy has no external function of its own. Every call lands in `_fallback`
(`SystemContractProxy.sol:39-68`), which branches on the selector:

    if (selector == upgradeTo || upgradeToAndCall || changeAdmin || admin || implementation) {
        super._fallback();                                                    // :42-49
    } else if (selector == ISystemContractProxy.forceInitAdmin.selector) {    // :50
        if (msg.sender != L2_COMPLEX_UPGRADER_ADDR) { Proxy._fallback(); }    // :51-55, never returns
        require(_getAdmin() == address(0), SystemContractProxyInitialized()); // :61
        _dispatchForceInitAdmin();                                            // :63
    } else {
        Proxy._fallback();                                                    // :66
    }

`_dispatchForceInitAdmin` (`:31-35`) requires `msg.value == 0`, decodes one address and calls
`_changeAdmin`, whose `_setAdmin` requires the new admin to be nonzero
(`ERC1967Upgrade.sol:104-106`).

`super._fallback()` is `TransparentUpgradeableProxy._fallback`
(`TransparentUpgradeableProxy.sol:84-107`): if `msg.sender == _getAdmin()` it dispatches the
five admin selectors itself and reverts on any other selector; otherwise it calls
`Proxy._fallback()`, which delegatecalls the implementation (`Proxy.sol:58-61`). The
dispatchers (`:116-173`):

* `upgradeTo`: `msg.value == 0`, then `_upgradeToAndCall(impl, "", false)`, which only sets the
  implementation, and that requires `Address.isContract(impl)` (`ERC1967Upgrade.sol:39-41, 59-64`);
* `upgradeToAndCall`: no value check; sets the implementation the same way and then
  delegatecalls it with the supplied data (`forceCall = true`);
* `changeAdmin`: `msg.value == 0`, then `_changeAdmin` (nonzero admin required);
* `admin`, `implementation`: `msg.value == 0`, then return the slot.

## Model boundary

* The state is the proxy's two ERC-1967 slots. Events and return data are not modelled.
* Calls are typed: a selector with its decoded arguments. Calldata whose `abi.decode` reverts is
  not a `ProxyCall` (`SOL-ABI`).
* `ProxyResult.delegated` says the call was forwarded to the implementation. What the
  implementation then does is outside this file; `Specs/UpgradePath.lean` says how the wider
  model treats it (`MODEL-L2UP-IMPL`).
* `upgradeToAndCall` carries a Boolean: whether the delegatecall into the new implementation
  succeeds. The model assumes that call does not write the two ERC-1967 slots
  (`MODEL-L2UP-IMPL`).
* `hasCode` is `Address.isContract`, supplied by the caller of these functions.
-/

namespace Contracts.L2ComplexUpgrader

/-- An address, as a word. Only equality, and one comparison with `0xFF`, are used. -/
abbrev Address := UInt256

/-- The two ERC-1967 slots of a proxy: `_ADMIN_SLOT` and `_IMPLEMENTATION_SLOT`
(`ERC1967Upgrade.sol:28, 96`). -/
structure ProxyState where
  /-- `_getAdmin()`. -/
  admin : Address
  /-- `_implementation()`. -/
  impl : Address
deriving DecidableEq

/-- A call to the proxy, by selector. `other` is every selector not named here. -/
inductive ProxyCall where
  /-- `upgradeTo(newImpl)`. -/
  | upgradeTo (newImpl : Address)
  /-- `upgradeToAndCall(newImpl, data)`; `initOk` says whether the delegatecall of `data` into
  `newImpl` succeeds. -/
  | upgradeToAndCall (newImpl : Address) (initOk : Bool)
  /-- `changeAdmin(newAdmin)`. -/
  | changeAdmin (newAdmin : Address)
  /-- `admin()`. -/
  | admin
  /-- `implementation()`. -/
  | implementation
  /-- `forceInitAdmin(newAdmin)` (`ISystemContractProxy.sol:12`). -/
  | forceInitAdmin (newAdmin : Address)
  /-- Any other selector. -/
  | other
deriving DecidableEq

/-- What the proxy does with a call. -/
inductive ProxyResult where
  /-- The proxy ran the call itself and left its slots as `s'`. -/
  | handled (s' : ProxyState)
  /-- The proxy forwarded the call to its implementation (`Proxy._fallback`). -/
  | delegated
  /-- The proxy reverted. -/
  | reverted
deriving DecidableEq

/-- The admin branch of `TransparentUpgradeableProxy._fallback`
(`TransparentUpgradeableProxy.sol:85-103`): the dispatchers at `:116-173`, and the revert
`"admin cannot fallback to proxy target"` (`:99`) for every other selector. -/
def adminDispatch (hasCode : Address → Bool) (value : UInt256) (s : ProxyState) :
    ProxyCall → ProxyResult
  | .upgradeTo n =>
      if value ≠ 0 then .reverted
      else if hasCode n then .handled { s with impl := n }
      else .reverted
  | .upgradeToAndCall n initOk =>
      if hasCode n && initOk then .handled { s with impl := n } else .reverted
  | .changeAdmin n =>
      if value ≠ 0 then .reverted
      else if n = 0 then .reverted
      else .handled { s with admin := n }
  | .admin => if value ≠ 0 then .reverted else .handled s
  | .implementation => if value ≠ 0 then .reverted else .handled s
  | .forceInitAdmin _ => .reverted
  | .other => .reverted

/-- `TransparentUpgradeableProxy._fallback` (`TransparentUpgradeableProxy.sol:84-107`): the admin
is dispatched or refused, everyone else is forwarded to the implementation. -/
def transparentFallback (hasCode : Address → Bool) (sender : Address) (value : UInt256)
    (s : ProxyState) (c : ProxyCall) : ProxyResult :=
  if sender = s.admin then adminDispatch hasCode value s c else .delegated

/-- `SystemContractProxy._fallback` (`SystemContractProxy.sol:39-68`). `upgrader` is
`L2_COMPLEX_UPGRADER_ADDR`. Guards are in source order. -/
def fallback (upgrader : Address) (hasCode : Address → Bool) (sender : Address) (value : UInt256)
    (s : ProxyState) : ProxyCall → ProxyResult
  | .upgradeTo n => transparentFallback hasCode sender value s (.upgradeTo n)
  | .upgradeToAndCall n initOk =>
      transparentFallback hasCode sender value s (.upgradeToAndCall n initOk)
  | .changeAdmin n => transparentFallback hasCode sender value s (.changeAdmin n)
  | .admin => transparentFallback hasCode sender value s .admin
  | .implementation => transparentFallback hasCode sender value s .implementation
  | .forceInitAdmin n =>
      if sender ≠ upgrader then .delegated          -- :51-55
      else if s.admin ≠ 0 then .reverted            -- :61
      else if value ≠ 0 then .reverted              -- :32
      else if n = 0 then .reverted                  -- ERC1967Upgrade.sol:105
      else .handled { s with admin := n }           -- :34
  | .other => .delegated                            -- :66

end Contracts.L2ComplexUpgrader
