import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: `ChainAdmin` and its restrictions (`d9f678900e`)

Source: era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`. Paths are
under `l1-contracts/contracts/`:

* `governance/ChainAdmin.sol` — the restriction-driven chain admin;
* `governance/restriction/{IRestriction,Restriction,RestrictionValidator}.sol`;
* `governance/AccessControlRestriction.sol`, on OpenZeppelin v4.9
  `AccessControlDefaultAdminRules` (`lib/openzeppelin-contracts-v4` at `dc44c9f1`);
* `governance/PermanentRestriction.sol`, on `Ownable2StepUpgradeable`;
* the two `Admin` facet functions that move a chain's admin
  (`state-transition/chain-deps/facets/Admin.sol:131-153`).

`governance/ChainAdminOwnable.sol` is in `Specs/Ownable.lean`.

**This file is definitions only.** Statements are in
`EraSpec.Contracts.ChainAdmin.Properties.Model`, proofs in `EraSpec.Contracts.ChainAdmin.Proofs.*`.

## The system

One `State` holds every `ChainAdmin`, every `AccessControlRestriction`, every
`PermanentRestriction`, and every ZK chain's `admin`/`pendingAdmin` pair. `Config.kind` says
which code sits at an address; it is fixed (no redeployment, no proxy upgrade of a
`PermanentRestriction`). Everything else other contracts hold is `Ext`, which any actor may
rewrite at any time.

Execution is one inductive relation `Sem cfg j S L S'` with three judgements `j`. `L` is the
list of events the derivation emits (`Entry`), oldest first:

* `.call s c ok` — `s` calls `c.target` with `c.value` and `c.data`; `ok` is the low-level
  success flag. **Any** call may fail with no effect (`callFails`): out of gas, a reverting
  callee, or a failed transfer. A call that succeeds runs the target's entry point.
* `.loop a i rs cs` — the body of `ChainAdmin(a).multicall(cs, rs)` invoked by `i`
  (`ChainAdmin.sol:83-100`): for each call, every active restriction validates it against the
  current state (`:88`, `:107-115`), then `a` makes the call (`:91`); with `rs` a failed call
  reverts the whole multicall (`:92-97`). A revert is the absence of a derivation.
* `.acts` — what an arbitrary external contract does while it holds control: any sequence of
  calls by senders that are not `ChainAdmin`s, and arbitrary rewrites of `Ext`.

A `ChainAdmin` makes calls only from its multicall loop, so a call with a `ChainAdmin` as
`msg.sender` appears nowhere else. Reentrancy is the `locked` flag (`nonReentrant`, `:83`).

The emitted events are every call a multicall made (`CallExecuted`, `:98`), each with the state
the restrictions validated it in, and every `setAllowedAdminImplementation(h, true)`. A reverted
multicall emits nothing, because it has no derivation.

`Step` is one top-level transaction, an environment rewrite, or a clock tick; `Reach` is any
finite sequence of steps, with the events it emitted.

## Model boundaries (see the README and `ASSUMPTIONS.md`, `MODEL-CHAIN-ADMIN`)

* ABI decoding is `Config.abi`: one function per argument tuple type, shared by every contract
  that decodes that type. The selectors are the real constants.
* `validateCall` and `getSupportsRestrictionMagic` are `view`, so they are `STATICCALL`s and
  change nothing: a validation is a `Bool` function of the state. A revert inside one is
  `false`. Third-party restrictions answer through `Ext.accepts`/`Ext.magic`. A static call the
  restriction makes into code outside the model (`getAdmin`, `assetRouter`, ...) is a total
  function of `Ext`: a revert there is over-approximated by some answer.
* ETH balances are not modelled; a value transfer that fails is a failed call.
* A chain's `admin`/`pendingAdmin` are written only by `setPendingAdmin`/`acceptAdmin`; its
  other functions are modelled as an arbitrary external computation (`chainOther`).
* `getChainId()` answers and the bridgehub's chain registry are configuration.
-/

namespace Contracts.ChainAdmin

/-! ## Words, bytes and maps -/

/-- Addresses, `bytes32` and `uint256` values are 256-bit words; `0` is the zero address. -/
abbrev Address := UInt256

/-- Raw calldata. -/
abbrev Bytes := List UInt8

/-- Point update of a mapping. -/
def upd {κ α : Type} [DecidableEq κ] (f : κ → α) (k : κ) (v : α) : κ → α :=
  fun x => if x = k then v else f x

/-- `Call` (`governance/Common.sol:9-13`). -/
structure Call where
  target : Address
  value : UInt256
  data : Bytes
deriving DecidableEq

/-! ## Selectors (`cast sig` of each signature) -/

/-- `ChainAdmin.addRestriction(address)`. -/
def SEL_ADD_RESTRICTION : Bytes := [0x33, 0x16, 0x39, 0x87]
/-- `ChainAdmin.removeRestriction(address)`. -/
def SEL_REMOVE_RESTRICTION : Bytes := [0x69, 0xa5, 0xb9, 0x50]
/-- `ChainAdmin.multicall((address,uint256,bytes)[],bool)`. -/
def SEL_MULTICALL : Bytes := [0x69, 0x34, 0x0b, 0xeb]
/-- `ChainAdmin.getRestrictions()`. -/
def SEL_GET_RESTRICTIONS : Bytes := [0xc4, 0x19, 0x5c, 0xb8]
/-- `ChainAdmin.isRestrictionActive(address)`. -/
def SEL_IS_RESTRICTION_ACTIVE : Bytes := [0x02, 0xf0, 0x27, 0x7d]
/-- `IAdmin.setPendingAdmin(address)`. -/
def SEL_SET_PENDING_ADMIN : Bytes := [0x4d, 0xd1, 0x8b, 0xf5]
/-- `IAdmin.acceptAdmin()`. -/
def SEL_ACCEPT_ADMIN : Bytes := [0x0e, 0x18, 0xb6, 0x81]
/-- `IL1Bridgehub.requestL2TransactionTwoBridges(L2TransactionRequestTwoBridgesOuter)`. -/
def SEL_TWO_BRIDGES : Bytes := [0x24, 0xfd, 0x57, 0xfb]
/-- `AccessControlRestriction.setRequiredRoleForCall(address,bytes4,bytes32)`. -/
def SEL_SET_ROLE_FOR_CALL : Bytes := [0xb9, 0x15, 0xe4, 0x05]
/-- `AccessControlRestriction.setRequiredRoleForFallback(address,bytes32)`. -/
def SEL_SET_ROLE_FOR_FALLBACK : Bytes := [0x2d, 0xe3, 0x41, 0x86]
/-- `grantRole(bytes32,address)`. -/
def SEL_GRANT_ROLE : Bytes := [0x2f, 0x2f, 0xf1, 0x5d]
/-- `revokeRole(bytes32,address)`. -/
def SEL_REVOKE_ROLE : Bytes := [0xd5, 0x47, 0x74, 0x1f]
/-- `renounceRole(bytes32,address)`. -/
def SEL_RENOUNCE_ROLE : Bytes := [0x36, 0x56, 0x8a, 0xbe]
/-- `beginDefaultAdminTransfer(address)`. -/
def SEL_BEGIN_ADMIN_TRANSFER : Bytes := [0x63, 0x4e, 0x93, 0xda]
/-- `cancelDefaultAdminTransfer()`. -/
def SEL_CANCEL_ADMIN_TRANSFER : Bytes := [0xd6, 0x02, 0xb9, 0xfd]
/-- `acceptDefaultAdminTransfer()`. -/
def SEL_ACCEPT_ADMIN_TRANSFER : Bytes := [0xce, 0xfc, 0x14, 0x29]
/-- `changeDefaultAdminDelay(uint48)`. -/
def SEL_CHANGE_DELAY : Bytes := [0x64, 0x9a, 0x5e, 0xc7]
/-- `rollbackDefaultAdminDelay()`. -/
def SEL_ROLLBACK_DELAY : Bytes := [0x0a, 0xa6, 0x22, 0x0b]
/-- `PermanentRestriction.initialize(address)`. -/
def SEL_INITIALIZE : Bytes := [0xc4, 0xd6, 0x6d, 0xe8]
/-- `setAllowedAdminImplementation(bytes32,bool)`. -/
def SEL_SET_ALLOWED_IMPL : Bytes := [0xa1, 0xe3, 0x41, 0xd4]
/-- `setAllowedData(bytes,bool)`. -/
def SEL_SET_ALLOWED_DATA : Bytes := [0xdb, 0xaa, 0xbc, 0xfd]
/-- `setSelectorShouldBeValidated(bytes4,bool)`. -/
def SEL_SET_SELECTOR_VALIDATED : Bytes := [0xc6, 0x76, 0x41, 0xa4]
/-- `allowL2Admin(uint256)`. -/
def SEL_ALLOW_L2_ADMIN : Bytes := [0x76, 0x2c, 0xad, 0xe4]
/-- `transferOwnership(address)`. -/
def SEL_TRANSFER_OWNERSHIP : Bytes := [0xf2, 0xfd, 0xe3, 0x8b]
/-- `acceptOwnership()`. -/
def SEL_ACCEPT_OWNERSHIP : Bytes := [0x79, 0xba, 0x50, 0x97]
/-- `renounceOwnership()`. -/
def SEL_RENOUNCE_OWNERSHIP : Bytes := [0x71, 0x50, 0x18, 0xa6]

/-- The state-changing selectors of `AccessControlRestriction`. -/
def ACR_ENTRY_SELECTORS : List Bytes :=
  [SEL_SET_ROLE_FOR_CALL, SEL_SET_ROLE_FOR_FALLBACK, SEL_GRANT_ROLE, SEL_REVOKE_ROLE,
    SEL_RENOUNCE_ROLE, SEL_BEGIN_ADMIN_TRANSFER, SEL_CANCEL_ADMIN_TRANSFER,
    SEL_ACCEPT_ADMIN_TRANSFER, SEL_CHANGE_DELAY, SEL_ROLLBACK_DELAY]

/-- The state-changing selectors of `PermanentRestriction`. -/
def PERM_ENTRY_SELECTORS : List Bytes :=
  [SEL_INITIALIZE, SEL_SET_ALLOWED_IMPL, SEL_SET_ALLOWED_DATA, SEL_SET_SELECTOR_VALIDATED,
    SEL_ALLOW_L2_ADMIN, SEL_TRANSFER_OWNERSHIP, SEL_ACCEPT_OWNERSHIP, SEL_RENOUNCE_OWNERSHIP]

/-- `NEW_ENCODING_VERSION` (`bridge/asset-router/IAssetRouterBase.sol:6`). -/
def NEW_ENCODING_VERSION : UInt8 := 0x01

/-- `MAX_ALLOWED_NONCE = 1 << 48` (`PermanentRestriction.sol:34`). -/
def MAX_ALLOWED_NONCE : Nat := 2 ^ 48

/-- `uint48` bound, for the OpenZeppelin schedules and delays. -/
def UINT48_BOUND : Nat := 2 ^ 48

/-- `defaultAdminDelayIncreaseWait()` = 5 days. -/
def DELAY_INCREASE_WAIT : Nat := 432000

/-! ## Code, ABI and the environment -/

/-- The code at an address. Fixed for the whole run. -/
inductive Kind where
  /-- No code: an EOA or an empty account. -/
  | none
  /-- `ChainAdmin.sol`. -/
  | chainAdmin
  /-- `AccessControlRestriction.sol`. -/
  | acr
  /-- A `PermanentRestriction` proxy, with its immutables `BRIDGE_HUB` and `L2_ADMIN_FACTORY`. -/
  | perm (bridgehub l2AdminFactory : Address)
  /-- A ZK chain diamond. -/
  | zkChain
  /-- Any other code. -/
  | other
deriving DecidableEq

/-- ABI decoding, one function per argument tuple. `none` is a decoding revert. Every contract
decoding the same tuple type uses the same function. -/
structure Abi where
  /-- `(address)`. -/
  addr : Bytes → Option Address
  /-- `(Call[], bool)`. -/
  calls : Bytes → Option (List Call × Bool)
  /-- `(address, bytes4, bytes32)`; the `bytes4` is four bytes. -/
  addrSelWord : Bytes → Option (Address × Bytes × UInt256)
  /-- `(address, bytes32)`. -/
  addrWord : Bytes → Option (Address × UInt256)
  /-- `(bytes32, address)`. -/
  wordAddr : Bytes → Option (UInt256 × Address)
  /-- `(uint256)`. -/
  word : Bytes → Option UInt256
  /-- `(uint48)`. -/
  uint48 : Bytes → Option Nat
  /-- `(bytes32, bool)`. -/
  wordBool : Bytes → Option (UInt256 × Bool)
  /-- `(bytes, bool)`. -/
  bytesBool : Bytes → Option (Bytes × Bool)
  /-- `(bytes4, bool)`. -/
  selBool : Bytes → Option (Bytes × Bool)
  /-- `(L2TransactionRequestTwoBridgesOuter)`, projected to `(secondBridgeAddress,
  secondBridgeCalldata)`. -/
  twoBridges : Bytes → Option (Address × Bytes)
  /-- `(bytes32, bytes)`: the `NEW_ENCODING_VERSION` payload `(chainAssetId, bridgehubData)`. -/
  newEncoding : Bytes → Option (UInt256 × Bytes)
  /-- `bridgehubData` as `BridgehubBurnCTMAssetData`, then its `ctmData` as `(address, bytes)`
  (`PermanentRestriction.sol:361-362`), projected to the address. -/
  burnAdmin : Bytes → Option Address

/-- Fixed configuration: code, ABI, code hashes, and the chain registry. -/
structure Config where
  kind : Address → Kind
  abi : Abi
  /-- `EXTCODEHASH`. -/
  codehash : Address → UInt256
  /-- `_getChainIdUnffallibleCall(t)` (`PermanentRestriction.sol:272-290`): `none` when the
  `getChainId()` static call fails or returns other than 32 bytes. -/
  chainIdOf : Address → Option UInt256
  /-- `IL1Bridgehub(bh).getZKChain(chainId)` (`core/bridgehub/BridgehubBase.sol:344-347`). -/
  zkChainOf : Address → UInt256 → Address
  /-- `L2ContractHelper.computeCreateAddress(sender, nonce)`. -/
  createAddress : Address → UInt256 → Address

/-- The zero address has no code. Message senders are therefore never zero. -/
def Config.WF (cfg : Config) : Prop := cfg.kind 0 = .none

/-- State held by contracts outside the model. Any actor may rewrite it. -/
structure Ext where
  /-- A third-party restriction `r`'s `validateCall(call, invoker)` called by `admin`. -/
  accepts : Address → Address → Call → Address → Bool
  /-- A third-party contract's `getSupportsRestrictionMagic() == RESTRICTION_MAGIC`. -/
  magic : Address → Bool
  /-- A third-party contract's `isRestrictionActive(r)`. -/
  reportsActive : Address → Address → Bool
  /-- `IZKChain(t).getAdmin()` for code other than a modelled chain. -/
  getAdmin : Address → Address
  /-- `IL1Bridgehub(bh).assetRouter()`. -/
  assetRouter : Address → Address
  /-- `IL1Bridgehub(bh).ctmAssetIdToAddress(assetId)`. -/
  ctmAssetIdToAddress : Address → UInt256 → Address
  /-- `IAssetRouterBase(router).assetHandlerAddress(assetId)`. -/
  assetHandlerAddress : Address → UInt256 → Address

/-! ## Contract state -/

/-- `ChainAdmin` storage: `activeRestrictions.values()` in `EnumerableSet` order, and the
reentrancy guard. -/
structure CAState where
  restrictions : List Address
  locked : Bool

/-- `AccessControlRestriction` storage, with `AccessControlDefaultAdminRules`'. Times are
`uint48` values held as naturals. -/
structure AcrState where
  /-- `_roles[role].members[account]`. -/
  roles : UInt256 → Address → Bool
  /-- `_currentDefaultAdmin`. -/
  defaultAdmin : Address
  /-- `_pendingDefaultAdmin`. -/
  pendingAdmin : Address
  /-- `_pendingDefaultAdminSchedule` (`0` = unset). -/
  pendingAdminSchedule : Nat
  /-- `_currentDelay`. -/
  currentDelay : Nat
  /-- `_pendingDelay`. -/
  pendingDelay : Nat
  /-- `_pendingDelaySchedule`. -/
  pendingDelaySchedule : Nat
  /-- `requiredRoles[target][selector]` (`AccessControlRestriction.sol:23`). -/
  requiredRoles : Address → Bytes → UInt256
  /-- `requiredRolesForFallback[target]` (`:26`). -/
  requiredRolesForFallback : Address → UInt256

/-- `PermanentRestriction` storage (`PermanentRestriction.sol:54-63`), with the proxy's
initializer flag and `Ownable2Step`'s owners. -/
structure PermState where
  initialized : Bool
  owner : Address
  pendingOwner : Address
  allowedAdminImplementations : UInt256 → Bool
  allowedCalls : Bytes → Bool
  selectorsToValidate : Bytes → Bool
  allowedL2Admins : Address → Bool

/-- A ZK chain's `s.admin` and `s.pendingAdmin`. -/
structure ChainState where
  admin : Address
  pendingAdmin : Address

/-- All modelled storage, and `block.timestamp`. -/
structure State where
  ca : Address → CAState
  acr : Address → AcrState
  perm : Address → PermState
  chain : Address → ChainState
  ext : Ext
  now : Nat

/-- An emitted event. -/
inductive Entry where
  /-- `CallExecuted` (`ChainAdmin.sol:98`): `admin`'s multicall, invoked by `invoker`, made
  `call` with low-level result `success`; the restrictions validated it against `pre`. -/
  | exec (admin invoker : Address) (call : Call) (success : Bool) (pre : State)
  /-- `AdminImplementationAllowed(codeHash, true)` (`PermanentRestriction.sol:88`) by
  `restriction`. -/
  | allowImpl (restriction : Address) (codeHash : UInt256)

/-- Write one `ChainAdmin`'s storage. -/
def State.setCA (S : State) (a : Address) (s : CAState) : State := { S with ca := upd S.ca a s }

/-- Write one `AccessControlRestriction`'s storage. -/
def State.setAcr (S : State) (r : Address) (s : AcrState) : State :=
  { S with acr := upd S.acr r s }

/-- Write one `PermanentRestriction`'s storage. -/
def State.setPerm (S : State) (p : Address) (s : PermState) : State :=
  { S with perm := upd S.perm p s }

/-- Write one chain's admin pair. -/
def State.setChain (S : State) (c : Address) (s : ChainState) : State :=
  { S with chain := upd S.chain c s }

/-- Replace the environment. -/
def State.setExt (S : State) (e : Ext) : State := { S with ext := e }

/-- Advance `block.timestamp` by one. -/
def State.tick (S : State) : State := { S with now := S.now + 1 }

/-- `a`'s list of active restrictions. -/
def State.restrictions (S : State) (a : Address) : List Address := (S.ca a).restrictions

/-- Append a restriction to `a`'s set (`EnumerableSet.add` of an absent value). -/
def State.addRestriction (S : State) (a x : Address) : State :=
  S.setCA a { S.ca a with restrictions := (S.ca a).restrictions ++ [x] }

/-- `EnumerableSet.remove` (OpenZeppelin v4.9 `_remove`): the last value moves into the removed
slot, then the array is popped. Applied only when `x` is present. -/
def enumRemove (l : List Address) (x : Address) : List Address :=
  (l.set (l.idxOf x) (l.getLast?.getD 0)).dropLast

/-- Remove a present restriction from `a`'s set. -/
def State.removeRestriction (S : State) (a x : Address) : State :=
  S.setCA a { S.ca a with restrictions := enumRemove (S.ca a).restrictions x }

/-- Set `a`'s reentrancy guard. -/
def State.setLocked (S : State) (a : Address) (b : Bool) : State :=
  S.setCA a { S.ca a with locked := b }

/-! ## `ChainAdmin` helpers -/

/-- `RestrictionValidator.validateRestriction` (`restriction/RestrictionValidator.sol:17-21`):
`getSupportsRestrictionMagic()` returns `RESTRICTION_MAGIC`. Both restriction contracts inherit
`Restriction.getSupportsRestrictionMagic` (`restriction/Restriction.sol:14-16`). A `ChainAdmin`,
a chain or an empty account reverts. -/
def supportsMagic (cfg : Config) (S : State) (x : Address) : Bool :=
  match cfg.kind x with
  | .acr => true
  | .perm _ _ => true
  | .other => S.ext.magic x
  | _ => false

/-! ## `AccessControlRestriction.validateCall` (`AccessControlRestriction.sol:63-79`) -/

/-- The role `validateCall` requires for a call: `requiredRolesForFallback[target]` for calldata
shorter than four bytes (`:67-72`), else `requiredRoles[target][selector]` (`:73-77`). -/
def requiredRoleFor (A : AcrState) (c : Call) : UInt256 :=
  if c.data.length < 4 then A.requiredRolesForFallback c.target
  else A.requiredRoles c.target (c.data.take 4)

/-- `validateCall(_call, _invoker)` does not revert. -/
def acrValidates (A : AcrState) (c : Call) (invoker : Address) : Bool :=
  A.roles (requiredRoleFor A c) invoker

/-! ## `PermanentRestriction.validateCall` (`PermanentRestriction.sol:136-143`) -/

/-- `IZKChain(t).getAdmin()`. -/
def adminOf (cfg : Config) (S : State) (t : Address) : Address :=
  if cfg.kind t = .zkChain then (S.chain t).admin else S.ext.getAdmin t

/-- `_isAdminOfAChain(t)` with `msg.sender = sender` (`:233-263`). -/
def isAdminOfAChain (cfg : Config) (bh : Address) (S : State) (sender t : Address) : Bool :=
  if t = 0 then false
  else
    match cfg.chainIdOf t with
    | none => false
    | some id => if cfg.zkChainOf bh id ≠ t then false else decide (adminOf cfg S t = sender)

/-- `IChainAdmin(n).isRestrictionActive(r)` answers `true` (`ChainAdmin.sol:59-61`). -/
def reportsActive (cfg : Config) (S : State) (n r : Address) : Bool :=
  match cfg.kind n with
  | .chainAdmin => decide (r ∈ (S.ca n).restrictions)
  | .other => S.ext.reportsActive n r
  | _ => false

/-- `_validateAsChainAdmin` (`:160-187`) with `_validateNewAdmin` (`:192-206`) inlined; `p` is
`address(this)`. -/
def validateAsChainAdmin (cfg : Config) (bh p : Address) (P : PermState) (S : State)
    (sender : Address) (c : Call) : Bool :=
  if isAdminOfAChain cfg bh S sender c.target = false then true
  else if c.data.length < 4 then true
  else if c.data.take 4 = SEL_SET_PENDING_ADMIN then
    match cfg.abi.addr (c.data.drop 4) with
    | none => false
    | some n => P.allowedAdminImplementations (cfg.codehash n) && reportsActive cfg S n p
  else if P.selectorsToValidate (c.data.take 4) = false then true
  else P.allowedCalls c.data

/-- The outcome of `_getNewAdminFromMigration`. -/
inductive MigrationCheck where
  /-- A decoding revert. -/
  | reverts
  /-- `(address(0), false)`. -/
  | notMigration
  /-- `(l2Admin, true)`. -/
  | migration (l2Admin : Address)
deriving DecidableEq

/-- `_getNewAdminFromMigration` (`:298-365`), the checks in source order. -/
def newAdminFromMigration (cfg : Config) (bh : Address) (S : State) (c : Call) : MigrationCheck :=
  if c.target ≠ bh then .notMigration                                        -- `:299-301`
  else if c.data.length < 4 then .notMigration                               -- `:303-305`
  else if c.data.take 4 ≠ SEL_TWO_BRIDGES then .notMigration                 -- `:307-309`
  else
    match cfg.abi.twoBridges (c.data.drop 4) with                            -- `:315-318`
    | none => .reverts
    | some (second, sbData) =>
      if second ≠ S.ext.assetRouter bh then .notMigration                    -- `:320-322`
      else
        match sbData with
        | [] => .notMigration                                                -- `:325-327`
        | v :: rest =>
          if v ≠ NEW_ENCODING_VERSION then .notMigration                     -- `:329-331`
          else
            match cfg.abi.newEncoding rest with                              -- `:343`
            | none => .reverts
            | some (assetId, bhData) =>
              if S.ext.ctmAssetIdToAddress bh assetId = 0 then .notMigration -- `:348-351`
              else if S.ext.assetHandlerAddress (S.ext.assetRouter bh) assetId ≠ bh
              then .notMigration                                             -- `:355-358`
              else
                match cfg.abi.burnAdmin bhData with                          -- `:361-362`
                | none => .reverts
                | some l2Admin => .migration l2Admin

/-- `_validateMigrationToL2` (`:149-156`). -/
def validateMigrationToL2 (cfg : Config) (bh : Address) (P : PermState) (S : State) (c : Call) :
    Bool :=
  match newAdminFromMigration cfg bh S c with
  | .reverts => false
  | .notMigration => true
  | .migration a => P.allowedL2Admins a

/-- `_validateRemoveRestriction` (`:211-229`) with `msg.sender = sender`. -/
def validateRemoveRestriction (cfg : Config) (p sender : Address) (c : Call) : Bool :=
  if c.target ≠ sender then true
  else if c.data.length < 4 then true
  else if c.data.take 4 ≠ SEL_REMOVE_RESTRICTION then true
  else
    match cfg.abi.addr (c.data.drop 4) with
    | none => false
    | some x => decide (x ≠ p)

/-- `validateCall` (`:136-143`), the three checks in source order. -/
def permValidates (cfg : Config) (bh p : Address) (P : PermState) (S : State) (sender : Address)
    (c : Call) : Bool :=
  validateAsChainAdmin cfg bh p P S sender c && validateMigrationToL2 cfg bh P S c &&
    validateRemoveRestriction cfg p sender c

/-! ## One restriction, and `_validateCall` -/

/-- `Restriction(r).validateCall(c, invoker)`, called by `admin`, does not revert. -/
def validates (cfg : Config) (S : State) (admin r : Address) (c : Call) (invoker : Address) :
    Bool :=
  match cfg.kind r with
  | .acr => acrValidates (S.acr r) c invoker
  | .perm bh _ => permValidates cfg bh r (S.perm r) S admin c
  | .other => S.ext.accepts r admin c invoker
  | _ => false

/-- `_validateCall` (`ChainAdmin.sol:107-115`): every restriction in `getRestrictions()` accepts. -/
def AllAccept (cfg : Config) (S : State) (admin : Address) (c : Call) (invoker : Address) : Prop :=
  ∀ r ∈ (S.ca admin).restrictions, validates cfg S admin r c invoker = true

instance (cfg : Config) (S : State) (admin : Address) (c : Call) (invoker : Address) :
    Decidable (AllAccept cfg S admin c invoker) := by
  unfold AllAccept; infer_instance

/-! ## `AccessControlRestriction` entry points -/

/-- A decoded call of a state-changing `AccessControlRestriction` function. -/
inductive AcrMsg where
  | setRequiredRoleForCall (target : Address) (selector : Bytes) (role : UInt256)
  | setRequiredRoleForFallback (target : Address) (role : UInt256)
  | grantRole (role : UInt256) (account : Address)
  | revokeRole (role : UInt256) (account : Address)
  | renounceRole (role : UInt256) (account : Address)
  | beginDefaultAdminTransfer (newAdmin : Address)
  | cancelDefaultAdminTransfer
  | acceptDefaultAdminTransfer
  | changeDefaultAdminDelay (newDelay : Nat)
  | rollbackDefaultAdminDelay

/-- Selector dispatch and argument decoding. `none` is a revert (no such function, or a
decoding failure). -/
def acrDecode (abi : Abi) (d : Bytes) : Option AcrMsg :=
  if d.length < 4 then none
  else if d.take 4 = SEL_SET_ROLE_FOR_CALL then
    (abi.addrSelWord (d.drop 4)).map fun x => .setRequiredRoleForCall x.1 x.2.1 x.2.2
  else if d.take 4 = SEL_SET_ROLE_FOR_FALLBACK then
    (abi.addrWord (d.drop 4)).map fun x => .setRequiredRoleForFallback x.1 x.2
  else if d.take 4 = SEL_GRANT_ROLE then
    (abi.wordAddr (d.drop 4)).map fun x => .grantRole x.1 x.2
  else if d.take 4 = SEL_REVOKE_ROLE then
    (abi.wordAddr (d.drop 4)).map fun x => .revokeRole x.1 x.2
  else if d.take 4 = SEL_RENOUNCE_ROLE then
    (abi.wordAddr (d.drop 4)).map fun x => .renounceRole x.1 x.2
  else if d.take 4 = SEL_BEGIN_ADMIN_TRANSFER then
    (abi.addr (d.drop 4)).map .beginDefaultAdminTransfer
  else if d.take 4 = SEL_CANCEL_ADMIN_TRANSFER then some .cancelDefaultAdminTransfer
  else if d.take 4 = SEL_ACCEPT_ADMIN_TRANSFER then some .acceptDefaultAdminTransfer
  else if d.take 4 = SEL_CHANGE_DELAY then (abi.uint48 (d.drop 4)).map .changeDefaultAdminDelay
  else if d.take 4 = SEL_ROLLBACK_DELAY then some .rollbackDefaultAdminDelay
  else none

/-- `defaultAdminDelay()`. -/
def acrDelay (A : AcrState) (now : Nat) : Nat :=
  if A.pendingDelaySchedule ≠ 0 ∧ A.pendingDelaySchedule < now then A.pendingDelay
  else A.currentDelay

/-- `_revokeRole` (OZ `AccessControlDefaultAdminRules.sol:140-145`, `AccessControl.sol:242-247`). -/
def acrRevoke (A : AcrState) (role : UInt256) (acc : Address) : AcrState :=
  let A1 := if role = 0 ∧ acc = A.defaultAdmin then { A with defaultAdmin := 0 } else A
  { A1 with roles := upd A1.roles role (upd (A1.roles role) acc false) }

/-- `_grantRole` (`:129-135`, `AccessControl.sol:228-233`): the default admin role only when
there is none. -/
def acrGrant (A : AcrState) (role : UInt256) (acc : Address) : Option AcrState :=
  if role = 0 then
    if A.defaultAdmin ≠ 0 then none
    else some { A with defaultAdmin := acc, roles := upd A.roles 0 (upd (A.roles 0) acc true) }
  else some { A with roles := upd A.roles role (upd (A.roles role) acc true) }

/-- `_setPendingDelay` (`:349-363`). -/
def acrSetPendingDelay (A : AcrState) (now newDelay newSchedule : Nat) : AcrState :=
  let A1 := if A.pendingDelaySchedule ≠ 0 ∧ A.pendingDelaySchedule < now
    then { A with currentDelay := A.pendingDelay } else A
  { A1 with pendingDelay := newDelay, pendingDelaySchedule := newSchedule }

/-- A state-changing entry point of `AccessControlRestriction` called by `sender` (value zero).
`none` is a revert. `onlyRole(getRoleAdmin(role))` is `onlyRole(0)`: the contract never calls
`_setRoleAdmin`. -/
def acrRun (sender : Address) (now : Nat) (A : AcrState) : AcrMsg → Option AcrState
  -- `AccessControlRestriction.sol:37-48`
  | .setRequiredRoleForCall t s role =>
    if A.roles 0 sender = false then none
    else if t = 0 then none
    else some { A with requiredRoles := upd A.requiredRoles t (upd (A.requiredRoles t) s role) }
  -- `:53-60`
  | .setRequiredRoleForFallback t role =>
    if A.roles 0 sender = false then none
    else if t = 0 then none
    else some { A with requiredRolesForFallback := upd A.requiredRolesForFallback t role }
  -- OZ `AccessControlDefaultAdminRules.sol:82-85`, `AccessControl.sol:145-147`
  | .grantRole role acc =>
    if role = 0 then none
    else if A.roles 0 sender = false then none
    else acrGrant A role acc
  -- `:90-93`, `AccessControl.sol:160-162`
  | .revokeRole role acc =>
    if role = 0 then none
    else if A.roles 0 sender = false then none
    else some (acrRevoke A role acc)
  -- `:108-117`, `AccessControl.sol:180-184`
  | .renounceRole role acc =>
    if role = 0 ∧ acc = A.defaultAdmin then
      if A.pendingAdmin = 0 ∧ A.pendingAdminSchedule ≠ 0 ∧ A.pendingAdminSchedule < now then
        if acc ≠ sender then none
        else some (acrRevoke { A with pendingAdminSchedule := 0 } role acc)
      else none
    else if acc ≠ sender then none
    else some (acrRevoke A role acc)
  -- `:203-216`
  | .beginDefaultAdminTransfer n =>
    if A.roles 0 sender = false then none
    else if UINT48_BOUND ≤ now then none
    else if UINT48_BOUND ≤ now + acrDelay A now then none
    else some { A with pendingAdmin := n, pendingAdminSchedule := now + acrDelay A now }
  -- `:221-232`
  | .cancelDefaultAdminTransfer =>
    if A.roles 0 sender = false then none
    else some { A with pendingAdmin := 0, pendingAdminSchedule := 0 }
  -- `:237-255`
  | .acceptDefaultAdminTransfer =>
    if sender ≠ A.pendingAdmin then none
    else if ¬ (A.pendingAdminSchedule ≠ 0 ∧ A.pendingAdminSchedule < now) then none
    else
      match acrGrant (acrRevoke A 0 A.defaultAdmin) 0 A.pendingAdmin with
      | none => none
      | some A2 => some { A2 with pendingAdmin := 0, pendingAdminSchedule := 0 }
  -- `:264-276`, `_delayChangeWait` `:304-320`
  | .changeDefaultAdminDelay nd =>
    if A.roles 0 sender = false then none
    else if UINT48_BOUND ≤ now then none
    else
      let wait := if acrDelay A now < nd then min nd DELAY_INCREASE_WAIT else acrDelay A now - nd
      if UINT48_BOUND ≤ now + wait then none
      else some (acrSetPendingDelay A now nd (now + wait))
  -- `:282-293`
  | .rollbackDefaultAdminDelay =>
    if A.roles 0 sender = false then none
    else some (acrSetPendingDelay A now 0 0)

/-! ## `PermanentRestriction` entry points -/

/-- A decoded call of a state-changing `PermanentRestriction` function. -/
inductive PermMsg where
  | initialize (owner : Address)
  | setAllowedAdminImplementation (codeHash : UInt256) (allowed : Bool)
  | setAllowedData (data : Bytes) (allowed : Bool)
  | setSelectorShouldBeValidated (selector : Bytes) (validated : Bool)
  | allowL2Admin (nonce : UInt256)
  | transferOwnership (newOwner : Address)
  | acceptOwnership
  | renounceOwnership

/-- Selector dispatch and argument decoding. -/
def permDecode (abi : Abi) (d : Bytes) : Option PermMsg :=
  if d.length < 4 then none
  else if d.take 4 = SEL_INITIALIZE then (abi.addr (d.drop 4)).map .initialize
  else if d.take 4 = SEL_SET_ALLOWED_IMPL then
    (abi.wordBool (d.drop 4)).map fun x => .setAllowedAdminImplementation x.1 x.2
  else if d.take 4 = SEL_SET_ALLOWED_DATA then
    (abi.bytesBool (d.drop 4)).map fun x => .setAllowedData x.1 x.2
  else if d.take 4 = SEL_SET_SELECTOR_VALIDATED then
    (abi.selBool (d.drop 4)).map fun x => .setSelectorShouldBeValidated x.1 x.2
  else if d.take 4 = SEL_ALLOW_L2_ADMIN then (abi.word (d.drop 4)).map .allowL2Admin
  else if d.take 4 = SEL_TRANSFER_OWNERSHIP then (abi.addr (d.drop 4)).map .transferOwnership
  else if d.take 4 = SEL_ACCEPT_OWNERSHIP then some .acceptOwnership
  else if d.take 4 = SEL_RENOUNCE_OWNERSHIP then some .renounceOwnership
  else none

/-- A state-changing entry point of the `PermanentRestriction` proxy at `p` with factory `fac`,
called by `sender` (value zero). Returns the new storage and the events it emits. -/
def permRun (cfg : Config) (fac p sender : Address) (P : PermState) :
    PermMsg → Option (PermState × List Entry)
  -- `PermanentRestriction.sol:75-80`, under the proxy's `initializer`
  | .initialize o =>
    if P.initialized then none
    else if o = 0 then none
    else some ({ P with initialized := true, owner := o, pendingOwner := 0 }, [])
  -- `:85-89`
  | .setAllowedAdminImplementation h b =>
    if P.owner ≠ sender then none
    else some ({ P with allowedAdminImplementations := upd P.allowedAdminImplementations h b },
      if b then [Entry.allowImpl p h] else [])
  -- `:94-98`
  | .setAllowedData data b =>
    if P.owner ≠ sender then none
    else some ({ P with allowedCalls := upd P.allowedCalls data b }, [])
  -- `:103-107`
  | .setSelectorShouldBeValidated s b =>
    if P.owner ≠ sender then none
    else some ({ P with selectorsToValidate := upd P.selectorsToValidate s b }, [])
  -- `:115-133`; permissionless
  | .allowL2Admin n =>
    if n = 0 then none
    else if MAX_ALLOWED_NONCE < n.val then none
    else if P.allowedL2Admins (cfg.createAddress fac n) then none
    else some ({ P with allowedL2Admins := upd P.allowedL2Admins (cfg.createAddress fac n) true },
      [])
  -- `Ownable2StepUpgradeable.transferOwnership`
  | .transferOwnership n =>
    if P.owner ≠ sender then none
    else some ({ P with pendingOwner := n }, [])
  -- `Ownable2StepUpgradeable.acceptOwnership`
  | .acceptOwnership =>
    if P.pendingOwner ≠ sender then none
    else some ({ P with owner := sender, pendingOwner := 0 }, [])
  -- `OwnableUpgradeable.renounceOwnership`, through `Ownable2Step._transferOwnership`
  | .renounceOwnership =>
    if P.owner ≠ sender then none
    else some ({ P with owner := 0, pendingOwner := 0 }, [])

/-! ## The chain's admin pair (`facets/Admin.sol:131-153`) -/

/-- The calldata selects `setPendingAdmin` or `acceptAdmin`. -/
def IsAdminSelector (d : Bytes) : Prop :=
  4 ≤ d.length ∧ (d.take 4 = SEL_SET_PENDING_ADMIN ∨ d.take 4 = SEL_ACCEPT_ADMIN)

/-- `setPendingAdmin` (`onlyAdmin`) and `acceptAdmin` (by the pending admin), value zero. -/
def chainExec (cfg : Config) (sender : Address) (C : ChainState) (d : Bytes) : Option ChainState :=
  if d.length < 4 then none
  else if d.take 4 = SEL_SET_PENDING_ADMIN then
    match cfg.abi.addr (d.drop 4) with
    | none => none
    | some n => if sender ≠ C.admin then none else some { C with pendingAdmin := n }
  else if d.take 4 = SEL_ACCEPT_ADMIN then
    if sender ≠ C.pendingAdmin then none else some { admin := C.pendingAdmin, pendingAdmin := 0 }
  else none

/-! ## Execution -/

/-- What a `Sem` derivation describes. -/
inductive Judgement where
  /-- `sender` calls `c`; `ok` is the low-level success flag. -/
  | call (sender : Address) (c : Call) (ok : Bool)
  /-- The remaining iterations of `admin`'s multicall loop, invoked by `invoker`. -/
  | loop (admin invoker : Address) (requireSuccess : Bool) (calls : List Call)
  /-- An external contract holding control. -/
  | acts

/-- The execution relation: `Sem cfg j S L S'` — judgement `j` takes `S` to `S'` and emits `L`.
A revert is the absence of a derivation; a failed inner call is `callFails`, which changes
nothing. -/
inductive Sem (cfg : Config) : Judgement → State → List Entry → State → Prop
  /-- Any call may fail, with no effect. -/
  | callFails {s : Address} {c : Call} {S : State} : Sem cfg (.call s c false) S [] S
  /-- `receive()` (`ChainAdmin.sol:103`): empty calldata, any value. -/
  | caReceive {s : Address} {c : Call} {S : State} :
      cfg.kind c.target = .chainAdmin → c.data = [] → Sem cfg (.call s c true) S [] S
  /-- `addRestriction` (`:64-66`, `_addRestriction` `:119-126`): non-payable, `onlySelf`, the
  magic check, then `EnumerableSet.add` (reverts if present). -/
  | caAdd {s : Address} {c : Call} {S : State} {x : Address} :
      cfg.kind c.target = .chainAdmin → c.value = 0 → 4 ≤ c.data.length →
      c.data.take 4 = SEL_ADD_RESTRICTION → cfg.abi.addr (c.data.drop 4) = some x →
      s = c.target → supportsMagic cfg S x = true → x ∉ S.restrictions c.target →
      Sem cfg (.call s c true) S [] (S.addRestriction c.target x)
  /-- `removeRestriction` (`:69-74`): non-payable, `onlySelf`, `EnumerableSet.remove` (reverts if
  absent). -/
  | caRemove {s : Address} {c : Call} {S : State} {x : Address} :
      cfg.kind c.target = .chainAdmin → c.value = 0 → 4 ≤ c.data.length →
      c.data.take 4 = SEL_REMOVE_RESTRICTION → cfg.abi.addr (c.data.drop 4) = some x →
      s = c.target → x ∈ S.restrictions c.target →
      Sem cfg (.call s c true) S [] (S.removeRestriction c.target x)
  /-- `multicall` (`:83-100`): payable, `nonReentrant`, at least one call; the loop runs with the
  guard set and the guard is released at the end. -/
  | caMulticall {s : Address} {c : Call} {S S' : State} {L : List Entry} {cs : List Call}
      {rs : Bool} :
      cfg.kind c.target = .chainAdmin → 4 ≤ c.data.length → c.data.take 4 = SEL_MULTICALL →
      cfg.abi.calls (c.data.drop 4) = some (cs, rs) → (S.ca c.target).locked = false →
      cs ≠ [] →
      Sem cfg (.loop c.target s rs cs) (S.setLocked c.target true) L S' →
      Sem cfg (.call s c true) S L (S'.setLocked c.target false)
  /-- `getRestrictions` and `isRestrictionActive` (`:54-61`): non-payable views. -/
  | caView {s : Address} {c : Call} {S : State} :
      cfg.kind c.target = .chainAdmin → c.value = 0 → 4 ≤ c.data.length →
      (c.data.take 4 = SEL_GET_RESTRICTIONS ∨
        (c.data.take 4 = SEL_IS_RESTRICTION_ACTIVE ∧ (cfg.abi.addr (c.data.drop 4)).isSome)) →
      Sem cfg (.call s c true) S [] S
  /-- A state-changing `AccessControlRestriction` entry point. -/
  | acrCall {s : Address} {c : Call} {S : State} {m : AcrMsg} {A' : AcrState} :
      cfg.kind c.target = .acr → c.value = 0 → acrDecode cfg.abi c.data = some m →
      acrRun s S.now (S.acr c.target) m = some A' →
      Sem cfg (.call s c true) S [] (S.setAcr c.target A')
  /-- Any other selector of an `AccessControlRestriction` (its views; an unknown selector in
  fact reverts): no effect. -/
  | acrView {s : Address} {c : Call} {S : State} :
      cfg.kind c.target = .acr → c.value = 0 → 4 ≤ c.data.length →
      c.data.take 4 ∉ ACR_ENTRY_SELECTORS → Sem cfg (.call s c true) S [] S
  /-- A state-changing `PermanentRestriction` entry point. -/
  | permCall {s : Address} {c : Call} {S : State} {bh fac : Address} {m : PermMsg}
      {P' : PermState} {L : List Entry} :
      cfg.kind c.target = .perm bh fac → c.value = 0 → permDecode cfg.abi c.data = some m →
      permRun cfg fac c.target s (S.perm c.target) m = some (P', L) →
      Sem cfg (.call s c true) S L (S.setPerm c.target P')
  /-- Any other selector of a `PermanentRestriction` (its views; an unknown selector in fact
  reverts): no effect. -/
  | permView {s : Address} {c : Call} {S : State} {bh fac : Address} :
      cfg.kind c.target = .perm bh fac → c.value = 0 → 4 ≤ c.data.length →
      c.data.take 4 ∉ PERM_ENTRY_SELECTORS → Sem cfg (.call s c true) S [] S
  /-- A chain's `setPendingAdmin`/`acceptAdmin`. -/
  | chainAdminCall {s : Address} {c : Call} {S : State} {C' : ChainState} :
      cfg.kind c.target = .zkChain → c.value = 0 →
      chainExec cfg s (S.chain c.target) c.data = some C' →
      Sem cfg (.call s c true) S [] (S.setChain c.target C')
  /-- Any other function of a chain: an external computation that leaves the admin pair of the
  called chain to the two functions above. -/
  | chainOther {s : Address} {c : Call} {S S' : State} {L : List Entry} :
      cfg.kind c.target = .zkChain → ¬ IsAdminSelector c.data → Sem cfg .acts S L S' →
      Sem cfg (.call s c true) S L S'
  /-- A call into other code, or to an account with none. -/
  | external {s : Address} {c : Call} {S S' : State} {L : List Entry} :
      (cfg.kind c.target = .other ∨ cfg.kind c.target = .none) → Sem cfg .acts S L S' →
      Sem cfg (.call s c true) S L S'
  /-- The loop is done. -/
  | loopNil {a i : Address} {rs : Bool} {S : State} : Sem cfg (.loop a i rs []) S [] S
  /-- One iteration (`:87-99`): validate against the current state, call, check success, emit. -/
  | loopCons {a i : Address} {rs ok : Bool} {c : Call} {cs : List Call} {S S1 S2 : State}
      {L1 L2 : List Entry} :
      AllAccept cfg S a c i → Sem cfg (.call a c ok) S L1 S1 → (rs = true → ok = true) →
      Sem cfg (.loop a i rs cs) S1 L2 S2 →
      Sem cfg (.loop a i rs (c :: cs)) S (L1 ++ Entry.exec a i c ok S :: L2) S2
  /-- An external computation that does nothing more. -/
  | actsRefl {S : State} : Sem cfg .acts S [] S
  /-- It makes a call as some address that is not a `ChainAdmin`. -/
  | actsCall {s : Address} {c : Call} {ok : Bool} {S S1 S2 : State} {L1 L2 : List Entry} :
      cfg.kind s ≠ .chainAdmin → s ≠ 0 → Sem cfg (.call s c ok) S L1 S1 →
      Sem cfg .acts S1 L2 S2 → Sem cfg .acts S (L1 ++ L2) S2
  /-- It rewrites state outside the model. -/
  | actsExt {e : Ext} {S S2 : State} {L : List Entry} :
      Sem cfg .acts (S.setExt e) L S2 → Sem cfg .acts S L S2

/-- One transaction, an environment change, or the clock advancing. -/
inductive Step (cfg : Config) : State → List Entry → State → Prop
  /-- A transaction from an address that is not a `ChainAdmin`. -/
  | tx {s : Address} {c : Call} {ok : Bool} {S S' : State} {L : List Entry} :
      cfg.kind s ≠ .chainAdmin → s ≠ 0 → Sem cfg (.call s c ok) S L S' → Step cfg S L S'
  /-- Other contracts change. -/
  | ext {S : State} (e : Ext) : Step cfg S [] (S.setExt e)
  /-- `block.timestamp` advances. -/
  | tick {S : State} : Step cfg S [] S.tick

/-- Reachability: any interleaving of any steps, with the events emitted, oldest first. -/
inductive Reach (cfg : Config) : State → List Entry → State → Prop
  | refl {S : State} : Reach cfg S [] S
  | tail {S S1 S2 : State} {L L1 : List Entry} :
      Reach cfg S L S1 → Step cfg S1 L1 S2 → Reach cfg S (L ++ L1) S2

/-! ## Predicates used by the properties -/

/-- A self-call of `admin` that adds or removes a restriction. -/
def IsRestrictionSetCall (admin : Address) (c : Call) : Prop :=
  c.target = admin ∧ 4 ≤ c.data.length ∧
    (c.data.take 4 = SEL_ADD_RESTRICTION ∨ c.data.take 4 = SEL_REMOVE_RESTRICTION)

/-- Code that answers `getSupportsRestrictionMagic`. -/
def IsRestrictionCode (k : Kind) : Prop :=
  k = .acr ∨ (∃ bh fac, k = .perm bh fac) ∨ k = .other

/-- The chain `c` is registered in bridgehub `bh` and answers `getChainId()`. -/
def Registered (cfg : Config) (bh c : Address) : Prop :=
  ∃ id, cfg.chainIdOf c = some id ∧ cfg.zkChainOf bh id = c

/-- `a` is a `ChainAdmin` with `p` active. -/
def UnderRestriction (cfg : Config) (S : State) (p a : Address) : Prop :=
  cfg.kind a = .chainAdmin ∧ p ∈ S.restrictions a

/-- The chain's admin is a `ChainAdmin` with `p` active, and so is its pending admin, if any. -/
def GoodChain (cfg : Config) (p c : Address) (S : State) : Prop :=
  UnderRestriction cfg S p (S.chain c).admin ∧
    ((S.chain c).pendingAdmin = 0 ∨ UnderRestriction cfg S p (S.chain c).pendingAdmin)

/-- Only `ChainAdmin` code has code hash `h` (a statement about one hash, not injectivity). -/
def GenuineHash (cfg : Config) (h : UInt256) : Prop :=
  ∀ a, cfg.codehash a = h → cfg.kind a = .chainAdmin

/-- Every implementation hash `p` allows is genuine. -/
def AllowedGenuine (cfg : Config) (p : Address) (S : State) : Prop :=
  ∀ h, (S.perm p).allowedAdminImplementations h = true → GenuineHash cfg h

/-- Every allowance by `p` among the events `L` is of a genuine hash. -/
def LoggedAllowancesGenuine (cfg : Config) (p : Address) (L : List Entry) : Prop :=
  ∀ h, Entry.allowImpl p h ∈ L → GenuineHash cfg h

/-- `x` is `computeCreateAddress(fac, n)` for a nonce `allowL2Admin` accepts. -/
def FactoryAddress (cfg : Config) (fac x : Address) : Prop :=
  ∃ n : UInt256, n ≠ 0 ∧ n.val ≤ MAX_ALLOWED_NONCE ∧ x = cfg.createAddress fac n

/-- Every whitelisted L2 admin is a factory address. -/
def L2AdminsFromFactory (cfg : Config) (fac : Address) (P : PermState) : Prop :=
  ∀ x, P.allowedL2Admins x = true → FactoryAddress cfg fac x

/-- `AccessControlDefaultAdminRules`' bookkeeping: `DEFAULT_ADMIN_ROLE` is held by exactly
`_currentDefaultAdmin`, and by nobody once it is zero. -/
def AcrAdminConsistent (A : AcrState) : Prop :=
  ∀ x, A.roles 0 x = true ↔ (x = A.defaultAdmin ∧ x ≠ 0)

/-- What the asset router does with the call, independently of `PermanentRestriction`: `c` is
`BRIDGE_HUB.requestL2TransactionTwoBridges` through the bridgehub's asset router with a
`NEW_ENCODING_VERSION` payload for a registered CTM asset; the router hands the burn to
`handler = assetHandlerAddress[assetId]` (`bridge/asset-router/AssetRouterBase.sol:103`), and
the burn data names `l2Admin` as the chain's admin on the settlement layer. This is
`_getNewAdminFromMigration` (`PermanentRestriction.sol:298-365`) without the comparison of the
handler with `BRIDGE_HUB` at `:355-358`. -/
def MigrationVia (cfg : Config) (bh : Address) (S : State) (c : Call) (handler l2Admin : Address) :
    Prop :=
  c.target = bh ∧ 4 ≤ c.data.length ∧ c.data.take 4 = SEL_TWO_BRIDGES ∧
    ∃ rest assetId bhData,
      cfg.abi.twoBridges (c.data.drop 4) =
        some (S.ext.assetRouter bh, NEW_ENCODING_VERSION :: rest) ∧
      cfg.abi.newEncoding rest = some (assetId, bhData) ∧
      S.ext.ctmAssetIdToAddress bh assetId ≠ 0 ∧
      S.ext.assetHandlerAddress (S.ext.assetRouter bh) assetId = handler ∧
      cfg.abi.burnAdmin bhData = some l2Admin

end Contracts.ChainAdmin
