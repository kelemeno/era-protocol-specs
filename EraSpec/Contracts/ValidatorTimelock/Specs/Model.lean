import EraSpec.Core.Word

/-!
# Model: `ValidatorTimelock`

Source: era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`. Paths are
relative to `l1-contracts/contracts/`.

* `state-transition/validators/ValidatorTimelock.sol` (`VT`)
* `state-transition/AccessControlEnumerablePerChainAddressUpgradeable.sol` (`AC`)
* `lib/openzeppelin-contracts-upgradeable-v4` `access/Ownable2StepUpgradeable.sol`,
  `access/OwnableUpgradeable.sol` (the owner)

**This file is definitions only.** The statements are in
`EraSpec.Contracts.ValidatorTimelock.Properties.*` and are proved in
`EraSpec.Contracts.ValidatorTimelock.Proofs.*`.

## What is modelled

Every state-changing external entry point of the timelock proxy, each as a function
`State → Option State` with the guards in source order. **A revert is `none`**: no step.

* the owner (`initialize`, `transferOwnership`, `acceptOwnership`, `renounceOwnership`);
* the three delay setters and the enforced delay `max(executionDelay, chainExecutionDelay)`;
* the per-chain role registry (`grantRole`, `revokeRole`, `renounceRole`, `setRoleAdmin`) and
  the six validator-rotation wrappers, which are sequences of `grantRole`/`revokeRole` in the
  order the source makes them (`changeMany`);
* the five forwarding entry points (`commitBatchesSharedBridge`, `revertBatchesSharedBridge`,
  `proveBatchesSharedBridge`, `executeBatchesSharedBridge`, both `upgradeChainFromVersion`
  overloads), with the commit-timestamp write and the delay check.

## The environment of one call (`Env`)

Everything a call reads from outside the timelock's storage is a field of `Env`, and each call
of a run has its own `Env`. Nothing relates one call's `Env` to the next: the chain's admin, the
bridgehub's registry and the clock may change arbitrarily between calls.

* `now` is `block.timestamp`.
* `chainIdOf c` is `IZKChain(c).getChainId()` (`VT:399`); `none` is a reverting call.
* `zkChain id` is `BRIDGE_HUB.getZKChain(id)` (`VT:223`, `:270`, `:400`), taken as total.
* `adminOf c` is `IZKChain(c).getAdmin()` (`VT:405`); `none` is a reverting call.
* `forwardOk` says whether the forwarded call of `_propagateToAddress` returns successfully
  (`VT:373-388`). When it does not, the whole transaction reverts, the timestamp writes included.

## Modelling choices

* **Addresses and `bytes32` roles are words**; only equality matters. The role constants are
  the literal values of the `keccak256` expressions at `VT:46-67` (computed with
  `cast keccak`); no hash property is assumed, their distinctness is checked by evaluation.
* **Batch numbers and times are natural numbers.** `validRange` restricts the batch arguments
  to what a `uint256` pair can carry and for which the `unchecked` loops terminate (`VT:300`,
  `:333`): with `_processBatchTo == type(uint256).max` the loop condition never fails and the
  call runs out of gas.
* **`committedAt c i` is `committedBatchTimestamp[c].get(i)`.** The packed `LibMap.Uint32Map`
  is modelled bit for bit in `Specs.LibMap`, where the commit loop is shown to write exactly
  the function update used here. The stored value is `uint32(block.timestamp)` (`VT:299`),
  that is `now % 2^32`.
* **Delays are natural numbers.** Every write is behind `_checkExecutionDelayWithinBounds`
  (`VT:165-169`), so a value that does not fit a `uint32` never reaches storage.
* **`hasRole` can revert.** For `DEFAULT_ADMIN_ROLE` it calls the chain and the bridgehub
  (`AC:74-76`, `VT:392-406`); `hasRole … = none` is that revert.
* **No reentrancy step.** The forwarded call is the last thing a forwarding entry point does,
  and the chain-admin lookups are `view` calls. A call the callee makes back into the timelock
  is another call of the run. Gas is not modelled.

## What is not modelled

`MultisigCommitter` and `PermissionlessValidator` (the other files of `validators/`), events,
the enumeration views (`getRoleMember`, `getRoleMemberCount`), `getName`, the proxy and its
admin, and the chain diamond: whether the diamond accepts a forwarded call is `forwardOk`.
That the batches a forwarded commit or execute acts on are exactly `_processBatchFrom …
_processBatchTo` is checked by the diamond (`BatchDecoder.decodeAndCheck*Data`), not here.
-/

namespace Contracts.ValidatorTimelock

open Clear

/-! ## Words and constants -/

/-- An EVM address. Only equality and `address(0)` matter. -/
abbrev Address := UInt256

/-- A `bytes32` role identifier. -/
abbrev Role := UInt256

/-- Function update. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

/-- `DEFAULT_ADMIN_ROLE = 0x00` (`AC:59`). -/
def DEFAULT_ADMIN_ROLE : Role := 0

/-- `keccak256("PRECOMMITTER_ROLE")` (`VT:46`). Retired: it gates nothing. -/
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

/-- `keccak256("OPTIONAL_COMMITTER_ADMIN_ROLE")` (`VT:67`). The contract never installs it;
a chain admin may make it the admin role of `COMMITTER_ROLE` with `setRoleAdmin`. -/
def OPTIONAL_COMMITTER_ADMIN_ROLE : Role :=
  0x764da40dc482d3b385909d7a072df3207fef1d443f7a2633f4e7f1c0bb574ee0

/-- `MAX_VALIDATOR_TIMELOCK_EXECUTION_DELAY = 30 days` (`common/Config.sol:334`, `VT:82`). -/
def MAX_EXECUTION_DELAY : ℕ := 2592000

/-- `2^32`: the range of the stored `uint32` commit timestamp. -/
def UINT32 : ℕ := 4294967296

/-! ## Storage -/

/-- The timelock proxy's storage. -/
@[ext] structure State where
  /-- OpenZeppelin `Initializable`: `initialize` has run. -/
  initialized : Bool
  /-- `OwnableUpgradeable._owner`. -/
  owner : Address
  /-- `Ownable2StepUpgradeable._pendingOwner`. -/
  pendingOwner : Address
  /-- `_executionDelay` (`VT:91`). -/
  executionDelay : ℕ
  /-- `_chainExecutionDelay[chain]` (`VT:94`). -/
  chainDelay : Address → ℕ
  /-- `_roles[chain][role].members.contains(account)` (`AC:54`). -/
  members : Address → Role → Address → Bool
  /-- `_roles[chain][role].adminRole` (`AC:50`, `:54`); `0` is `DEFAULT_ADMIN_ROLE`. -/
  adminRole : Address → Role → Role
  /-- `committedBatchTimestamp[chain].get(batch)` (`VT:88`, `:172-174`). -/
  committedAt : Address → ℕ → ℕ

/-- Fresh proxy storage. -/
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

/-- `_roles[c][r].members` gets or loses `a`. -/
def setMember (s : State) (c : Address) (r : Role) (a : Address) (b : Bool) : State :=
  { s with members := fun c' r' a' => if c' = c ∧ r' = r ∧ a' = a then b else s.members c' r' a' }

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
  /-- The forwarded call of `_propagateToAddress` returns successfully. -/
  forwardOk : Bool

/-- `_getChainAdmin` (`VT:392-406`): the chain's admin, provided the bridgehub registers the
chain's own id to this address. `none` is a revert (`NotAZKChain` or a failed call). -/
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

/-! ## The owner -/

/-- `initialize` (`VT:106-114`): the `initializer` modifier, `_transferOwnership`, the bound
check, the delay write. -/
def initializeTimelock (o : Address) (d : ℕ) (s : State) : Option State :=
  if s.initialized then none
  else if MAX_EXECUTION_DELAY < d then none
  else some { s with initialized := true, owner := o, pendingOwner := 0, executionDelay := d }

/-- `Ownable2StepUpgradeable.transferOwnership`: `onlyOwner`, then the pending owner is set. -/
def transferOwnership (x n : Address) (s : State) : Option State :=
  if x ≠ s.owner then none else some { s with pendingOwner := n }

/-- `Ownable2StepUpgradeable.acceptOwnership`. -/
def acceptOwnership (x : Address) (s : State) : Option State :=
  if s.pendingOwner ≠ x then none else some { s with owner := x, pendingOwner := 0 }

/-- `OwnableUpgradeable.renounceOwnership`, not overridden by the timelock. -/
def renounceOwnership (x : Address) (s : State) : Option State :=
  if x ≠ s.owner then none else some { s with owner := 0, pendingOwner := 0 }

/-! ## Delays -/

/-- `setExecutionDelay` (`VT:127-131`). -/
def setExecutionDelay (x : Address) (d : ℕ) (s : State) : Option State :=
  if x ≠ s.owner then none
  else if MAX_EXECUTION_DELAY < d then none
  else some { s with executionDelay := d }

/-- `increaseChainExecutionDelay` (`VT:134-148`). -/
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
role (the modifier), and the default admin role cannot be granted or revoked. Then the member is
added or removed. -/
def changeRole (b : Bool) (e : Env) (x c : Address) (r : Role) (a : Address) (s : State) :
    Option State :=
  if hasRole e s c (getRoleAdmin s c r) x ≠ some true then none
  else if r = DEFAULT_ADMIN_ROLE then none
  else some (setMember s c r a b)

/-- `grantRole` (`AC:115-130`). -/
abbrev grantRole := changeRole true

/-- `revokeRole` (`AC:136-142`). -/
abbrev revokeRole := changeRole false

/-- `renounceRole` (`AC:147-149`): the caller needs the role itself. -/
def renounceRole (e : Env) (x c : Address) (r : Role) (s : State) : Option State :=
  if hasRole e s c r x ≠ some true then none
  else if r = DEFAULT_ADMIN_ROLE then none
  else some (setMember s c r x false)

/-- `setRoleAdmin` (`AC:155-167`). -/
def setRoleAdmin (e : Env) (x c : Address) (r ar : Role) (s : State) : Option State :=
  if hasRole e s c (getRoleAdmin s c r) x ≠ some true then none
  else if r = DEFAULT_ADMIN_ROLE then none
  else some { s with adminRole := fun c' r' => if c' = c ∧ r' = r then ar else s.adminRole c' r' }

/-- Consecutive `grantRole(c, r, v)` (`b = true`) or `revokeRole(c, r, v)` (`b = false`) calls
of one transaction, in list order. Each check sees the state the earlier ones left. -/
def changeMany (b : Bool) (e : Env) (x c v : Address) : List Role → State → Option State
  | [], s => some s
  | r :: rs, s => (changeRole b e x c r v s).bind (changeMany b e x c v rs)

/-- `v` gets (`b = true`) or loses (`b = false`) every role of `rs` on chain `c`. -/
def setMembers (s : State) (c v : Address) (rs : List Role) (b : Bool) : State :=
  { s with members := fun c' r' a' =>
      if c' = c ∧ r' ∈ rs ∧ a' = v then b else s.members c' r' a' }

/-- Chain `c` has no role member and no role with a non-default admin role. -/
def ChainRolesEmpty (s : State) (c : Address) : Prop :=
  (∀ r a, s.members c r a = false) ∧ ∀ r, s.adminRole c r = DEFAULT_ADMIN_ROLE

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
of the range is overwritten with `uint32(block.timestamp)`, and the call is forwarded. -/
def commitBatches (e : Env) (x c : Address) (lo hi : ℕ) (s : State) : Option State :=
  if hasRole e s c COMMITTER_ROLE x ≠ some true then none
  else if ¬ validRange lo hi then none
  else if e.forwardOk = false then none
  else some { s with committedAt := fun c' i =>
      if c' = c ∧ lo ≤ i ∧ i ≤ hi then e.now % UINT32 else s.committedAt c' i }

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

/-- One successful call. `none` is a revert. -/
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
its `onlyRole` modifier named. `none` for an entry point that forwards nothing. -/
def Action.forward : Action → Option (Address × Role)
  | .commitBatches c _ _ => some (c, COMMITTER_ROLE)
  | .revertBatches c => some (c, REVERTER_ROLE)
  | .proveBatches c => some (c, PROVER_ROLE)
  | .executeBatches c _ _ => some (c, EXECUTOR_ROLE)
  | .upgradeChainFromVersion c _ => some (c, UPGRADER_ROLE)
  | _ => none

/-- A commit of batch `i` of chain `c`. -/
def Action.commits (c : Address) (i : ℕ) : Action → Prop
  | .commitBatches c' lo hi => c = c' ∧ lo ≤ i ∧ i ≤ hi
  | _ => False

/-- One of the owner's two delay setters, the only entry points that can lower a delay. -/
def Action.isOwnerDelaySetter : Action → Prop
  | .setExecutionDelay _ | .setChainExecutionDelay _ _ => True
  | _ => False

/-! ## Runs -/

/-- A sequence of successful calls, any entry points in any order, each with its own
environment and caller. `P` is a condition on each call and the state it starts from. -/
inductive RunP (P : State → Call → Prop) : State → List Call → State → Prop
  | nil (s : State) : RunP P s [] s
  | cons {s s₁ s₂ : State} {k : Call} {ks : List Call} :
      P s k → step k s = some s₁ → RunP P s₁ ks s₂ → RunP P s (k :: ks) s₂

/-- An unconstrained run. -/
abbrev Run : State → List Call → State → Prop := RunP (fun _ _ => True)

/-- The same run as a function: `none` when some call reverts. -/
def exec : List Call → State → Option State
  | [], s => some s
  | k :: ks, s => (step k s).bind (exec ks)

/-- The clocks of a run never go back and stay below `2^32` (before the year 2106). -/
def ClocksOk (ks : List Call) : Prop :=
  ks.Pairwise (fun k k' => k.env.now ≤ k'.env.now) ∧ ∀ k ∈ ks, k.env.now < UINT32

/-! ## Variants for the countermodels -/

/-- `increaseChainExecutionDelay` **without** the comparison of `VT:141-144`. -/
def increaseChainExecutionDelayUnchecked (e : Env) (x c : Address) (d : ℕ) (s : State) :
    Option State :=
  if hasRole e s c DEFAULT_ADMIN_ROLE x ≠ some true then none
  else if MAX_EXECUTION_DELAY < d then none
  else some { s with chainDelay := upd s.chainDelay c d }

/-- `increaseChainExecutionDelay` comparing against the **stored** chain delay instead of the
enforced one, the alternative the comment at `VT:140` rejects. -/
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

/-- `_getChainAdmin` **without** the bridgehub check of `VT:399-402`. -/
def chainAdminUnchecked (e : Env) (c : Address) : Option Address := e.adminOf c

/-- `grantRole` with the chain admin read by `chainAdminUnchecked`. -/
def grantRoleUnchecked (e : Env) (x c : Address) (r : Role) (a : Address) (s : State) :
    Option State :=
  if (if getRoleAdmin s c r = DEFAULT_ADMIN_ROLE
        then (chainAdminUnchecked e c).map (fun adm => decide (x = adm))
        else some (s.members c (getRoleAdmin s c r) x)) ≠ some true then none
  else if r = DEFAULT_ADMIN_ROLE then none
  else some (setMember s c r a true)

end Contracts.ValidatorTimelock
