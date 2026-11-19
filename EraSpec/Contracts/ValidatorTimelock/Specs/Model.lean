import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: `ValidatorTimelock`

**Source commit.** era-contracts `draft/v0.35.0` at **`b17415d20`**
(`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`). Paths are relative to `l1-contracts/contracts/`.

* `state-transition/validators/ValidatorTimelock.sol` (`VT`)
* `state-transition/AccessControlEnumerablePerChainAddressUpgradeable.sol` (`AC`)
* `common/Config.sol:334` (`MAX_VALIDATOR_TIMELOCK_EXECUTION_DELAY`)
* the packed timestamp map `state-transition/libraries/LibMap.sol`, transcribed bit for bit in
  `Specs/LibMap.lean`
* OpenZeppelin `contracts-upgradeable` v4.9.6, the submodule `lib/openzeppelin-contracts-upgradeable-v4`
  at `2d081f24` that `b17415d20` pins: `access/Ownable2StepUpgradeable.sol` (`O2`),
  `access/OwnableUpgradeable.sol` (`OW`), `proxy/utils/Initializable.sol` (`IN`).

Every line cited below is at `b17415d20`. `main` (`70096e2ea`) and the interop pin `c67894b9` carry an older
`ValidatorTimelock.sol` (one ecosystem-wide delay with no upper bound, no per-chain delay, a
`precommitSharedBridge` entry point). That version is not modelled.

**This file is definitions only.** The statements are in
`EraSpec.Contracts.ValidatorTimelock.Properties.*` and are proved in
`EraSpec.Contracts.ValidatorTimelock.Proofs.*`.

## What is modelled

Every state-changing external entry point of the timelock proxy, each as a function
`State → Option State` with the checks of the source. **A revert is `none`**: no step. Since a
revert undoes the whole call, the order of the checks does not matter for the result.

* the owner (`initialize`, `transferOwnership`, `acceptOwnership`, `renounceOwnership`);
* the three delay setters and the enforced delay `max(executionDelay, chainExecutionDelay)`;
* the per-chain role registry (`grantRole`, `revokeRole`, `renounceRole`, `setRoleAdmin`) and
  the six validator-rotation wrappers, which are sequences of `grantRole`/`revokeRole` calls in
  the order of the source (`changeMany`);
* the five forwarding entry points (`commitBatchesSharedBridge`, `revertBatchesSharedBridge`,
  `proveBatchesSharedBridge`, `executeBatchesSharedBridge`, both `upgradeChainFromVersion`
  overloads), with the commit-timestamp write and the delay check.

## The environment of one call (`Env`)

Everything a call reads from outside the timelock's storage is a field of `Env`, and each call
of a run has its own `Env`. Nothing relates one call's `Env` to the next: the chain's admin, the
bridgehub's registry and the clock may change arbitrarily between calls. Within one call the
answers are taken as fixed, also across the repeated lookups of a rotation wrapper: the lookups
below are `view` (`STATICCALL`) calls, the timelock makes no other external call before the
forwarded call, which is its last action, and a chain diamond's `getChainId()`/`getAdmin()` and
`BridgehubBase.getZKChain` read only their own storage.

* `now` is `block.timestamp`.
* `chainIdOf c` is `IZKChain(c).getChainId()` (`VT:399`); `none` is a reverting call.
* `zkChain id` is `BRIDGE_HUB.getZKChain(id)` (`VT:223`, `:270`, `:400`). It is total:
  `BridgehubBase.getZKChain` (`core/bridgehub/BridgehubBase.sol:344-347`) is a `tryGet` that
  returns `address(0)` for an unknown id.
* `adminOf c` is `IZKChain(c).getAdmin()` (`VT:405`); `none` is a reverting call.
* `forwardOk` says whether the forwarded call of `_propagateToAddress` succeeds
  (`VT:368-389`). When it does not, the whole call reverts, the timestamp writes included.

## Modelling choices

* **Addresses and `bytes32` roles are 256-bit words**; only equality matters. The role
  constants are the literal values of the `keccak256` expressions at `VT:46-61` and `:67`
  (computed with `cast keccak`). No hash property is assumed.
* **Batch numbers and times are natural numbers.** `validRange` restricts the batch arguments
  to what a `uint256` pair can carry and for which the `unchecked` loops terminate (`VT:300`,
  `:333`): with `_processBatchTo == type(uint256).max` the loop condition never fails and the
  call runs out of gas. Gas is not modelled otherwise, so a commit or execute over any other
  range may succeed. This only adds successful calls.
* **`committedAt c i` is `committedBatchTimestamp[c].get(i)`** (`VT:88`, `:172-174`, `:334`).
  `Specs/LibMap.lean` transcribes the packed `LibMap.Uint32Map` and its `get`/`set`, and shows
  that the commit loop writes exactly the update `recordCommit` makes here. The stored value is
  `uint32(block.timestamp)` (`VT:299`), that is `now % 2^32`.
* **Delays are natural numbers.** Every write is behind `_checkExecutionDelayWithinBounds`
  (`VT:165-169`), so a value above `MAX_EXECUTION_DELAY` never reaches storage; the delay
  arguments are `uint32`, and `MAX_EXECUTION_DELAY < 2^32`.
* **`hasRole` can revert.** For `DEFAULT_ADMIN_ROLE` it calls the chain and the bridgehub
  (`AC:73-78`, `VT:392-406`); `hasRole … = none` is that revert.
* **`msg.sender` is any word**, `0` included. On a real chain no call has sender `0`; results
  that need this take it as a premise.
* **Re-entrant calls.** The forwarded call is the last thing a forwarding entry point does and
  ends the call frame (`return` or `revert` in assembly, `VT:379-387`); nothing is read or
  written after it. A call the chain makes back into the timelock during the forwarded call
  runs on the state the outer call has left, and its writes stand only if the outer call
  succeeds. The model takes it as a later call of the run, with its own `Env`.
* **`initialize`** is OpenZeppelin's `initializer` (`IN:84-99`) for a proxy that has code: it
  succeeds once, while `_initialized` is `0`. The constructor-time disjunct of `IN:87`, a nested
  initializer and the `_initializing` flag are not modelled.

## What is not modelled

`MultisigCommitter` and `PermissionlessValidator` (the other files of `validators/`), events,
the views (`hasRoleForChainId`, `getRoleMember`, `getRoleMemberCount`, the getters, `getName`),
the proxy and its admin (upgrades of the timelock's code), and the chain diamond: whether the
diamond accepts a forwarded call is `forwardOk`. That the batches a forwarded commit or execute
acts on are exactly `_processBatchFrom … _processBatchTo` is checked by the diamond
(`BatchDecoder.decodeAndCheck*Data`), not here.
-/

namespace Contracts.ValidatorTimelock

open Clear

/-! ## Words and constants -/

/-- An EVM address, as a 256-bit word. Only equality and `address(0)` matter. -/
abbrev Address := UInt256

/-- A `bytes32` role identifier. -/
abbrev Role := UInt256

/-- Point update of a mapping. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

/-- `DEFAULT_ADMIN_ROLE = 0x00` (`AC:59`). -/
def DEFAULT_ADMIN_ROLE : Role := 0

/-- `keccak256("PRECOMMITTER_ROLE")` (`VT:46`). Retired: no forwarding entry point checks it. -/
def PRECOMMITTER_ROLE : Role :=
  0x3353dfbbf9a3ed2a5be49cd3bd3a51ee03c3751d409cccac7723c4907332afee

/-- `keccak256("COMMITTER_ROLE")` (`VT:49`). -/
def COMMITTER_ROLE : Role :=
  0x0b60b5d7f7e737e4561eecda7c6a01e19e626c495c26e6f45e5b255f76a20106

/-- `keccak256("REVERTER_ROLE")` (`VT:52`). -/
def REVERTER_ROLE : Role :=
  0x30085792330f3f9ee2ee216aea0321c55a0909b87c51ee9ab49d05ca4a4c2ecb

/-- `keccak256("PROVER_ROLE")` (`VT:55`). -/
def PROVER_ROLE : Role :=
  0x60044782a422109ac08a415e44260ad5d3bad63d96ebe1fac0363399642ee3f2

/-- `keccak256("EXECUTOR_ROLE")` (`VT:58`). -/
def EXECUTOR_ROLE : Role :=
  0xd8aa0f3194971a2a116679f7c2090f6939c8d4e01a2a8d7e41d55e5351469e63

/-- `keccak256("UPGRADER_ROLE")` (`VT:61`). -/
def UPGRADER_ROLE : Role :=
  0x189ab7a9244df0848122154315af71fe140f3db0fe014031783b0946b8c9d2e3

/-- `keccak256("OPTIONAL_COMMITTER_ADMIN_ROLE")` (`VT:67`). The contract never installs it; a
chain admin may make it the admin role of `COMMITTER_ROLE` with `setRoleAdmin`. -/
def OPTIONAL_COMMITTER_ADMIN_ROLE : Role :=
  0x764da40dc482d3b385909d7a072df3207fef1d443f7a2633f4e7f1c0bb574ee0

/-- `MAX_VALIDATOR_TIMELOCK_EXECUTION_DELAY = 30 days` in seconds (`common/Config.sol:334`,
`VT:82`). -/
def MAX_EXECUTION_DELAY : ℕ := 2592000

/-- `2^32`: the range of the stored `uint32` commit timestamp. -/
def UINT32 : ℕ := 4294967296

/-! ## Storage -/

/-- The timelock proxy's storage. -/
@[ext] structure State where
  /-- `Initializable._initialized ≠ 0` (`IN:63`). -/
  initialized : Bool
  /-- `OwnableUpgradeable._owner` (`OW:22`). -/
  owner : Address
  /-- `Ownable2StepUpgradeable._pendingOwner` (`O2:21`). -/
  pendingOwner : Address
  /-- `_executionDelay` (`VT:91`). -/
  executionDelay : ℕ
  /-- `_chainExecutionDelay[chain]` (`VT:94`). -/
  chainDelay : Address → ℕ
  /-- `_roles[chain][role].members.contains(account)` (`AC:54`, `:77`). -/
  members : Address → Role → Address → Bool
  /-- `_roles[chain][role].adminRole` (`AC:50`, `:54`); `0` is `DEFAULT_ADMIN_ROLE`. -/
  adminRole : Address → Role → Role
  /-- `committedBatchTimestamp[chain].get(batch)` (`VT:88`, `:172-174`). -/
  committedAt : Address → ℕ → ℕ

/-- Fresh proxy storage: everything zero. -/
def init : State where
  initialized := false
  owner := 0
  pendingOwner := 0
  executionDelay := 0
  chainDelay := fun _ => 0
  members := fun _ _ _ => false
  adminRole := fun _ _ => 0
  committedAt := fun _ _ => 0

/-- `getExecutionDelay` (`VT:158-162`): the delay enforced for a chain. -/
def enforcedDelay (s : State) (c : Address) : ℕ :=
  if s.chainDelay c > s.executionDelay then s.chainDelay c else s.executionDelay

/-- `_roles[c][r].members` gets (`b = true`) or loses (`b = false`) `a`. -/
def setMember (s : State) (c : Address) (r : Role) (a : Address) (b : Bool) : State :=
  { s with members := fun c' r' a' => if c' = c ∧ r' = r ∧ a' = a then b else s.members c' r' a' }

/-- `v` gets (`b = true`) or loses (`b = false`) every role of `rs` on chain `c`. -/
def setMembers (s : State) (c v : Address) (rs : List Role) (b : Bool) : State :=
  { s with members := fun c' r' a' =>
      if c' = c ∧ r' ∈ rs ∧ a' = v then b else s.members c' r' a' }

/-- Chain `c` has no role member and no role with a non-default admin role. Fresh storage has
this for every chain. -/
def ChainRolesEmpty (s : State) (c : Address) : Prop :=
  (∀ r a, s.members c r a = false) ∧ ∀ r, s.adminRole c r = DEFAULT_ADMIN_ROLE

/-- `_recordBatchCommitment(c, lo, hi)` (`VT:291-304`): the timestamp of every batch
`lo ≤ i ≤ hi` of chain `c` becomes `uint32(now)`. -/
def recordCommit (s : State) (c : Address) (lo hi now : ℕ) : State :=
  { s with committedAt := fun c' i =>
      if c' = c ∧ lo ≤ i ∧ i ≤ hi then now % UINT32 else s.committedAt c' i }

/-! ## The environment of one call -/

/-- What one call reads from outside the timelock's storage. -/
structure Env where
  /-- `block.timestamp`. -/
  now : ℕ
  /-- `IZKChain(c).getChainId()`; `none` is a reverting call. -/
  chainIdOf : Address → Option UInt256
  /-- `BRIDGE_HUB.getZKChain(chainId)`. -/
  zkChain : UInt256 → Address
  /-- `IZKChain(c).getAdmin()`; `none` is a reverting call. -/
  adminOf : Address → Option Address
  /-- The forwarded call of `_propagateToAddress` succeeds. -/
  forwardOk : Bool

/-- `_getChainAdmin` (`VT:392-406`): the chain's admin, provided the bridgehub maps the chain's
own id to this address. `none` is a revert (`NotAZKChain`, or a failed call). -/
def chainAdmin (e : Env) (c : Address) : Option Address :=
  match e.chainIdOf c with
  | none => none
  | some id => if e.zkChain id = c then e.adminOf c else none

/-- `hasRole` (`AC:73-78`). `none` is a revert of the chain-admin lookup. -/
def hasRole (e : Env) (s : State) (c : Address) (r : Role) (a : Address) : Option Bool :=
  if r = DEFAULT_ADMIN_ROLE then (chainAdmin e c).map (fun adm => decide (a = adm))
  else some (s.members c r a)

/-- `getRoleAdmin` (`AC:82-87`). -/
def getRoleAdmin (s : State) (c : Address) (r : Role) : Role :=
  if r = DEFAULT_ADMIN_ROLE then DEFAULT_ADMIN_ROLE else s.adminRole c r

/-- The caller `x` holds role `r`'s admin role on chain `c`: if that admin role
(`getRoleAdmin`) is `DEFAULT_ADMIN_ROLE`, `x` is the chain's verified admin (`chainAdmin`);
otherwise `x` is a member of the admin role. This is `hasRole(c, getRoleAdmin(c, r), x)`
returning `true` without a revert. -/
def HoldsAdminOf (e : Env) (s : State) (c : Address) (r : Role) (x : Address) : Prop :=
  if getRoleAdmin s c r = DEFAULT_ADMIN_ROLE then chainAdmin e c = some x
  else s.members c (getRoleAdmin s c r) x = true

/-! ## The owner -/

/-- `initialize` (`VT:106-114`): the `initializer` modifier (`IN:84-99`), then
`_transferOwnership` (`O2:51-54`, which also clears the pending owner), the bound check and the
delay write. Anyone may call it. -/
def initializeTimelock (o : Address) (d : ℕ) (s : State) : Option State :=
  if s.initialized then none
  else if MAX_EXECUTION_DELAY < d then none
  else some { s with initialized := true, owner := o, pendingOwner := 0, executionDelay := d }

/-- `transferOwnership` (`O2:42-45`): `onlyOwner` (`OW:40-57`), then the pending owner is set.
There is no zero-address check, so `n = 0` cancels a pending transfer. -/
def transferOwnership (x n : Address) (s : State) : Option State :=
  if x ≠ s.owner then none else some { s with pendingOwner := n }

/-- `acceptOwnership` (`O2:59-63`): the caller must be the pending owner; it becomes the owner
and the pending owner is cleared. -/
def acceptOwnership (x : Address) (s : State) : Option State :=
  if s.pendingOwner ≠ x then none else some { s with owner := x, pendingOwner := 0 }

/-- `renounceOwnership` (`OW:66-68`, not overridden by the timelock): `onlyOwner`, then
`_transferOwnership(address(0))`, which dispatches to `O2:51-54` and also clears the pending
owner. -/
def renounceOwnership (x : Address) (s : State) : Option State :=
  if x ≠ s.owner then none else some { s with owner := 0, pendingOwner := 0 }

/-! ## Delays -/

/-- `setExecutionDelay` (`VT:127-131`). -/
def setExecutionDelay (x : Address) (d : ℕ) (s : State) : Option State :=
  if x ≠ s.owner then none
  else if MAX_EXECUTION_DELAY < d then none
  else some { s with executionDelay := d }

/-- `increaseChainExecutionDelay` (`VT:134-148`): the caller needs `DEFAULT_ADMIN_ROLE` on the
chain, the bound check, and the new delay must exceed the enforced one. -/
def increaseChainExecutionDelay (e : Env) (x c : Address) (d : ℕ) (s : State) : Option State :=
  if hasRole e s c DEFAULT_ADMIN_ROLE x ≠ some true then none
  else if MAX_EXECUTION_DELAY < d then none
  else if d ≤ enforcedDelay s c then none
  else some { s with chainDelay := upd s.chainDelay c d }

/-- `setChainExecutionDelay` (`VT:151-155`). -/
def setChainExecutionDelay (x c : Address) (d : ℕ) (s : State) : Option State :=
  if x ≠ s.owner then none
  else if MAX_EXECUTION_DELAY < d then none
  else some { s with chainDelay := upd s.chainDelay c d }

/-! ## The role registry -/

/-- `grantRole` (`AC:115-130`) for `b = true` and `revokeRole` (`AC:136-142` with `_revokeRole`,
`AC:177-188`) for `b = false`. The two have the same checks: the caller needs the role's admin
role (the modifier), and `DEFAULT_ADMIN_ROLE` cannot be granted or revoked. Then the member is
added or removed (the `hasRole` test of `AC:124`/`:182` only skips a write that would change
nothing). -/
def changeRole (b : Bool) (e : Env) (x c : Address) (r : Role) (a : Address) (s : State) :
    Option State :=
  if hasRole e s c (getRoleAdmin s c r) x ≠ some true then none
  else if r = DEFAULT_ADMIN_ROLE then none
  else some (setMember s c r a b)

/-- `renounceRole` (`AC:147-149`): the caller needs the role itself, and `_revokeRole` refuses
`DEFAULT_ADMIN_ROLE`. -/
def renounceRole (e : Env) (x c : Address) (r : Role) (s : State) : Option State :=
  if hasRole e s c r x ≠ some true then none
  else if r = DEFAULT_ADMIN_ROLE then none
  else some (setMember s c r x false)

/-- `setRoleAdmin` (`AC:155-167`). -/
def setRoleAdmin (e : Env) (x c : Address) (r ar : Role) (s : State) : Option State :=
  if hasRole e s c (getRoleAdmin s c r) x ≠ some true then none
  else if r = DEFAULT_ADMIN_ROLE then none
  else some { s with adminRole := fun c' r' => if c' = c ∧ r' = r then ar else s.adminRole c' r' }

/-- Consecutive internal `grantRole(c, r, v)` (`b = true`) or `revokeRole(c, r, v)`
(`b = false`) calls of one transaction, in list order, all with the transaction's
`msg.sender`. Each check sees the state the earlier ones left. -/
def changeMany (b : Bool) (e : Env) (x c v : Address) : List Role → State → Option State
  | [], s => some s
  | r :: rs, s => (changeRole b e x c r v s).bind (changeMany b e x c v rs)

/-- `IValidatorTimelock.ValidatorRotationParams`. -/
structure RotationParams where
  precommitter : Bool
  committer : Bool
  reverter : Bool
  prover : Bool
  executor : Bool
  upgrader : Bool

/-- The roles a rotation touches, in the order of `VT:182-201` and `:232-249`. -/
def RotationParams.roles (p : RotationParams) : List Role :=
  (if p.precommitter then [PRECOMMITTER_ROLE] else []) ++
  (if p.committer then [COMMITTER_ROLE] else []) ++
  (if p.reverter then [REVERTER_ROLE] else []) ++
  (if p.prover then [PROVER_ROLE] else []) ++
  (if p.executor then [EXECUTOR_ROLE] else []) ++
  (if p.upgrader then [UPGRADER_ROLE] else [])

/-- The parameters of `addValidator` (`VT:257-264`): every role but the retired one. -/
def addValidatorParams : RotationParams := ⟨false, true, true, true, true, true⟩

/-- The parameters of `removeValidator` (`VT:209-217`): all six roles. -/
def removeValidatorParams : RotationParams := ⟨true, true, true, true, true, true⟩

/-! ## The forwarding entry points -/

/-- The batch arguments fit a `uint256` pair and the `unchecked` loops over them terminate. -/
def validRange (lo hi : ℕ) : Prop := lo < UInt256.size ∧ hi + 1 < UInt256.size

instance (lo hi : ℕ) : Decidable (validRange lo hi) :=
  inferInstanceAs (Decidable (lo < UInt256.size ∧ hi + 1 < UInt256.size))

/-- The check of `VT:333-344` passes for every batch of the range: none has
`block.timestamp < commitBatchTimestamp + delay`. -/
def delayPassed (s : State) (c : Address) (lo hi now : ℕ) : Prop :=
  ∀ i, i ≤ hi → lo ≤ i → s.committedAt c i + enforcedDelay s c ≤ now

instance (s : State) (c : Address) (lo hi now : ℕ) : Decidable (delayPassed s c lo hi now) :=
  inferInstanceAs (Decidable (∀ i, i ≤ hi → lo ≤ i → s.committedAt c i + enforcedDelay s c ≤ now))

/-- `commitBatchesSharedBridge` (`VT:279-304`): the role check, the timestamp of every batch
of the range becomes `uint32(block.timestamp)`, and the call is forwarded. -/
def commitBatches (e : Env) (x c : Address) (lo hi : ℕ) (s : State) : Option State :=
  if hasRole e s c COMMITTER_ROLE x ≠ some true then none
  else if ¬ validRange lo hi then none
  else if e.forwardOk = false then none
  else some (recordCommit s c lo hi e.now)

/-- `executeBatchesSharedBridge` (`VT:325-347`): the role check, the delay check for every
batch of the range, and the call is forwarded. Storage is not written. -/
def executeBatches (e : Env) (x c : Address) (lo hi : ℕ) (s : State) : Option State :=
  if hasRole e s c EXECUTOR_ROLE x ≠ some true then none
  else if ¬ validRange lo hi then none
  else if ¬ delayPassed s c lo hi e.now then none
  else if e.forwardOk = false then none
  else some s

/-- `revertBatchesSharedBridge` (`VT:307-312`), `proveBatchesSharedBridge` (`:315-322`) and both
`upgradeChainFromVersion` overloads (`:350-364`): a role check and the forwarded call. -/
def forwardOnly (e : Env) (x c : Address) (r : Role) (s : State) : Option State :=
  if hasRole e s c r x ≠ some true then none
  else if e.forwardOk = false then none
  else some s

/-! ## Calls and steps -/

/-- The state-changing external entry points. -/
inductive Action
  | initializeTimelock (initialOwner : Address) (delay : ℕ)
  | transferOwnership (newOwner : Address)
  | acceptOwnership
  | renounceOwnership
  | setExecutionDelay (delay : ℕ)
  | increaseChainExecutionDelay (chain : Address) (delay : ℕ)
  | setChainExecutionDelay (chain : Address) (delay : ℕ)
  | grantRole (chain : Address) (role : Role) (account : Address)
  | revokeRole (chain : Address) (role : Role) (account : Address)
  | renounceRole (chain : Address) (role : Role)
  | setRoleAdmin (chain : Address) (role adminRole : Role)
  | addValidatorRoles (chain validator : Address) (params : RotationParams)
  | removeValidatorRoles (chain validator : Address) (params : RotationParams)
  | addValidator (chain validator : Address)
  | removeValidator (chain validator : Address)
  | addValidatorForChainId (chainId : UInt256) (validator : Address)
  | removeValidatorForChainId (chainId : UInt256) (validator : Address)
  | commitBatches (chain : Address) (lo hi : ℕ)
  | revertBatches (chain : Address)
  | proveBatches (chain : Address)
  | executeBatches (chain : Address) (lo hi : ℕ)
  /-- Either overload of `upgradeChainFromVersion`; `withCut` is the three-argument one. -/
  | upgradeChainFromVersion (chain : Address) (withCut : Bool)

/-- One external call: its environment, `msg.sender`, and the entry point with its arguments. -/
structure Call where
  env : Env
  sender : Address
  action : Action

/-- One call. `none` is a revert. -/
def step (k : Call) (s : State) : Option State :=
  match k.action with
  | .initializeTimelock o d => initializeTimelock o d s
  | .transferOwnership n => transferOwnership k.sender n s
  | .acceptOwnership => acceptOwnership k.sender s
  | .renounceOwnership => renounceOwnership k.sender s
  | .setExecutionDelay d => setExecutionDelay k.sender d s
  | .increaseChainExecutionDelay c d => increaseChainExecutionDelay k.env k.sender c d s
  | .setChainExecutionDelay c d => setChainExecutionDelay k.sender c d s
  | .grantRole c r a => changeRole true k.env k.sender c r a s
  | .revokeRole c r a => changeRole false k.env k.sender c r a s
  | .renounceRole c r => renounceRole k.env k.sender c r s
  | .setRoleAdmin c r ar => setRoleAdmin k.env k.sender c r ar s
  | .addValidatorRoles c v p => changeMany true k.env k.sender c v p.roles s
  | .removeValidatorRoles c v p => changeMany false k.env k.sender c v p.roles s
  | .addValidator c v => changeMany true k.env k.sender c v addValidatorParams.roles s
  | .removeValidator c v => changeMany false k.env k.sender c v removeValidatorParams.roles s
  | .addValidatorForChainId id v =>
      changeMany true k.env k.sender (k.env.zkChain id) v addValidatorParams.roles s
  | .removeValidatorForChainId id v =>
      changeMany false k.env k.sender (k.env.zkChain id) v removeValidatorParams.roles s
  | .commitBatches c lo hi => commitBatches k.env k.sender c lo hi s
  | .revertBatches c => forwardOnly k.env k.sender c REVERTER_ROLE s
  | .proveBatches c => forwardOnly k.env k.sender c PROVER_ROLE s
  | .executeBatches c lo hi => executeBatches k.env k.sender c lo hi s
  | .upgradeChainFromVersion c _ => forwardOnly k.env k.sender c UPGRADER_ROLE s

/-- The chain a call addresses: the `_chainAddress` argument, or the bridgehub's answer for a
`…ForChainId` wrapper. `none` for the entry points that name no chain. -/
def Action.chain (e : Env) : Action → Option Address
  | .increaseChainExecutionDelay c _ | .setChainExecutionDelay c _ => some c
  | .grantRole c _ _ | .revokeRole c _ _ | .renounceRole c _ | .setRoleAdmin c _ _ => some c
  | .addValidatorRoles c _ _ | .removeValidatorRoles c _ _ => some c
  | .addValidator c _ | .removeValidator c _ => some c
  | .addValidatorForChainId id _ | .removeValidatorForChainId id _ => some (e.zkChain id)
  | .commitBatches c _ _ | .revertBatches c | .proveBatches c => some c
  | .executeBatches c _ _ | .upgradeChainFromVersion c _ => some c
  | _ => none

/-- The call a successful entry point forwards: the target of `_propagateToAddress` and the role
its `onlyRole` modifier names. `none` for an entry point that forwards nothing. -/
def Action.forward : Action → Option (Address × Role)
  | .commitBatches c _ _ => some (c, COMMITTER_ROLE)
  | .revertBatches c => some (c, REVERTER_ROLE)
  | .proveBatches c => some (c, PROVER_ROLE)
  | .executeBatches c _ _ => some (c, EXECUTOR_ROLE)
  | .upgradeChainFromVersion c _ => some (c, UPGRADER_ROLE)
  | _ => none

/-- A commit through the timelock of a range containing batch `i` of chain `c`. -/
def Action.commits (c : Address) (i : ℕ) : Action → Prop
  | .commitBatches c' lo hi => c = c' ∧ lo ≤ i ∧ i ≤ hi
  | _ => False

/-- `initialize`, `setExecutionDelay` and `setChainExecutionDelay`: the entry points that write a
delay without requiring it to grow. The only other delay writer is
`increaseChainExecutionDelay`. -/
def Action.mayLowerDelay : Action → Prop
  | .initializeTimelock _ _ | .setExecutionDelay _ | .setChainExecutionDelay _ _ => True
  | _ => False

/-- The call writes chain `c`'s role registry: a grant, revoke, renounce, role-admin change or
rotation wrapper whose chain (resolved with `e` for the `…ForChainId` wrappers) is `c`. -/
def Action.writesRolesOf (e : Env) (c : Address) : Action → Prop
  | .grantRole c' _ _ | .revokeRole c' _ _ | .renounceRole c' _ | .setRoleAdmin c' _ _ => c' = c
  | .addValidatorRoles c' _ _ | .removeValidatorRoles c' _ _ => c' = c
  | .addValidator c' _ | .removeValidator c' _ => c' = c
  | .addValidatorForChainId id _ | .removeValidatorForChainId id _ => e.zkChain id = c
  | _ => False

/-- The call is `initialize`. -/
def Action.isInitialize : Action → Bool
  | .initializeTimelock _ _ => true
  | _ => false

/-! ## Runs -/

/-- A sequence of successful calls, any entry points in any order, each with its own
environment and caller. -/
inductive Run : State → List Call → State → Prop
  | nil (s : State) : Run s [] s
  | cons {s s₁ s₂ : State} {k : Call} {ks : List Call} :
      step k s = some s₁ → Run s₁ ks s₂ → Run s (k :: ks) s₂

/-- The same run as a function: `none` when some call reverts. -/
def exec : List Call → State → Option State
  | [], s => some s
  | k :: ks, s => (step k s).bind (exec ks)

/-- The bound the delay setters keep and the commit loop keeps: both delays at most
`MAX_EXECUTION_DELAY`, and every stored timestamp below `2^32`. -/
def Bounded (s : State) : Prop :=
  s.executionDelay ≤ MAX_EXECUTION_DELAY ∧ (∀ c, s.chainDelay c ≤ MAX_EXECUTION_DELAY) ∧
    ∀ c i, s.committedAt c i < UINT32

/-! ## Variants for the countermodels -/

/-- `increaseChainExecutionDelay` **without** the comparison of `VT:141-144`. -/
def increaseChainExecutionDelayUnchecked (e : Env) (x c : Address) (d : ℕ) (s : State) :
    Option State :=
  if hasRole e s c DEFAULT_ADMIN_ROLE x ≠ some true then none
  else if MAX_EXECUTION_DELAY < d then none
  else some { s with chainDelay := upd s.chainDelay c d }

/-- `increaseChainExecutionDelay` comparing against the **stored** chain delay instead of the
enforced one (the alternative the comment at `VT:140` names). -/
def increaseChainExecutionDelayStored (e : Env) (x c : Address) (d : ℕ) (s : State) :
    Option State :=
  if hasRole e s c DEFAULT_ADMIN_ROLE x ≠ some true then none
  else if MAX_EXECUTION_DELAY < d then none
  else if d ≤ s.chainDelay c then none
  else some { s with chainDelay := upd s.chainDelay c d }

/-- `executeBatchesSharedBridge` **without** the `TimeNotReached` check of `VT:341-343`. -/
def executeBatchesUnchecked (e : Env) (x c : Address) (lo hi : ℕ) (s : State) : Option State :=
  if hasRole e s c EXECUTOR_ROLE x ≠ some true then none
  else if ¬ validRange lo hi then none
  else if e.forwardOk = false then none
  else some s

/-- `hasRole` with `_getChainAdmin` **without** the bridgehub check of `VT:399-402`: the
default admin is whatever `getAdmin()` returns. -/
def hasRoleUnchecked (e : Env) (s : State) (c : Address) (r : Role) (a : Address) : Option Bool :=
  if r = DEFAULT_ADMIN_ROLE then (e.adminOf c).map (fun adm => decide (a = adm))
  else some (s.members c r a)

/-- `grantRole` with the role check of `hasRoleUnchecked`. -/
def grantRoleUnchecked (e : Env) (x c : Address) (r : Role) (a : Address) (s : State) :
    Option State :=
  if hasRoleUnchecked e s c (getRoleAdmin s c r) x ≠ some true then none
  else if r = DEFAULT_ADMIN_ROLE then none
  else some (setMember s c r a true)

/-! ## Witness data

The timelock's owner is `1`. Chain `100` reports chain id `270`, which the bridgehub maps to
`100`, and admin `2`. Address `200` also reports chain id `270` and admin `5`, but the bridgehub
maps `270` to `100`, so `200` is not a registered chain. Validator `3`, delegated committer
admin `4`, delegated committer `6`. Every forwarded call succeeds. -/

/-- The owner of the witness timelock. -/
def vtOwner : Address := 1
/-- The registered chain. -/
def vtChain : Address := 100
/-- Its chain admin. -/
def vtAdmin : Address := 2
/-- The validator. -/
def vtValidator : Address := 3
/-- The account the chain admin makes the admin of `COMMITTER_ROLE`. -/
def vtManager : Address := 4
/-- The committer that account appoints. -/
def vtDelegate : Address := 6
/-- An unregistered contract claiming chain id `270`. -/
def vtFake : Address := 200
/-- The admin it reports. -/
def vtFakeAdmin : Address := 5

/-- The environment at time `t`. -/
def vtEnv (t : ℕ) : Env where
  now := t
  chainIdOf := fun c => if c = vtChain then some 270 else if c = vtFake then some 270 else none
  zkChain := fun id => if id = 270 then vtChain else 0
  adminOf := fun c => if c = vtChain then some vtAdmin else if c = vtFake then some vtFakeAdmin
    else none
  forwardOk := true

/-- A call at time `t`. -/
def vtCall (t : ℕ) (x : Address) (a : Action) : Call := ⟨vtEnv t, x, a⟩

/-- The setup run from fresh storage at time `0`: `initialize(1, 100)` by anyone, then the
chain admin's `addValidator(100, 3)`. -/
def vtSetupCalls : List Call :=
  [vtCall 0 9 (.initializeTimelock vtOwner 100), vtCall 0 vtAdmin (.addValidator vtChain vtValidator)]

/-- The commit of the delay witness: batches `1 … 3` of chain `100` at time `1000`. -/
def vtDelayCommit : Call := vtCall 1000 vtValidator (.commitBatches vtChain 1 3)

/-- The calls between commit and execute in the delay witness: a commit of batches `4 … 5` at
`1050`, then the chain admin raises the chain's delay to `200` at `1100`. -/
def vtDelayMid : List Call :=
  [vtCall 1050 vtValidator (.commitBatches vtChain 4 5),
   vtCall 1100 vtAdmin (.increaseChainExecutionDelay vtChain 200)]

/-- The execute of the delay witness: batches `1 … 3` of chain `100` at time `1200`. -/
def vtDelayExecute : Call := vtCall 1200 vtValidator (.executeBatches vtChain 1 3)

end Contracts.ValidatorTimelock
