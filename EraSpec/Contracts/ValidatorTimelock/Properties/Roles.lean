import EraSpec.Contracts.ValidatorTimelock.Specs.Model
import EraSpec.Core.Headline

/-!
# Properties: the per-chain role registry and where the timelock forwards

Statements about `EraSpec.Contracts.ValidatorTimelock.Specs.Model` (source `b17415d20`).
Proofs are in `EraSpec.Contracts.ValidatorTimelock.Proofs.Roles`.

## What holds

* **Every forwarded call needs its role** (`ForwardNeedsTheRole`): a successful commit, revert,
  prove, execute or upgrade on chain `c` was sent by a member of the matching role of `c`.
* **Only registry writes on `c` change `c`'s registry** (`RegistryWriters`).
* **Every role traces back to a verified chain admin** (`RolesTraceToAVerifiedChainAdmin`,
  headline). Fresh storage has no member and no non-default admin role on any chain. Along any
  run, once chain `c`'s registry is not empty, some call of the run wrote `c`'s registry and was
  sent by `c`'s verified admin: `c` reported a chain id the bridgehub mapped to `c`, and `c`'s
  `getAdmin()` returned the sender. Later grants can come from delegated admins
  (`RoleDelegationWitness`), so the call found may be an earlier one.
* **The timelock forwards only to addresses the bridgehub once registered**
  (`ForwardsOnlyToOnceRegisteredChains`, headline). Along any run from fresh storage, a
  successful forwarding call to `c` comes after a registry write on `c` by `c`'s verified admin
  in that earlier call's environment. Only that earlier call is constrained: `c` may have been
  deregistered, or changed its admin, since, and its roles persist.

## The check is load-bearing

`UncheckedLookupGrantsOnUnregisteredChain`: with `_getChainAdmin` reading `getAdmin()` without
the bridgehub check of `VT:399-402`, the self-reported admin of an unregistered contract grants
itself `COMMITTER_ROLE` from fresh storage, after which the deployed commit forwards to that
contract. The deployed grant reverts.
-/

namespace Contracts.ValidatorTimelock

/-- **EVERY FORWARDED CALL NEEDS ITS ROLE.** If a call that forwards to chain `c` with role `r`
(`Action.forward`: commit, revert, prove, execute, upgrade) succeeds, its sender was a member of
`r` on `c` in the state it ran on, and the forwarded call succeeded. -/
def Properties.ForwardNeedsTheRole : Prop :=
  ∀ (k : Call) (s s' : State) (c : Address) (r : Role), step k s = some s' →
    k.action.forward = some (c, r) → s.members c r k.sender = true ∧ k.env.forwardOk = true

/-- **ONLY REGISTRY WRITES ON `c` CHANGE `c`'S REGISTRY.** If a successful call changes a role
membership or a role's admin role on chain `c`, it is a grant, revoke, renounce, role-admin
change or rotation wrapper on `c` (`Action.writesRolesOf`). -/
def Properties.RegistryWriters : Prop :=
  ∀ (k : Call) (s s' : State) (c : Address), step k s = some s' →
    (s'.members c ≠ s.members c ∨ s'.adminRole c ≠ s.adminRole c) →
    k.action.writesRolesOf k.env c

/-- **HEADLINE: EVERY ROLE TRACES BACK TO A VERIFIED CHAIN ADMIN.** Fresh storage has an empty
registry on every chain (`ChainRolesEmpty`). Along any run of successful calls from a state
where chain `c`'s registry is empty to one where it is not, some call of the run writes `c`'s
registry and is sent by `c`'s verified admin in its own environment
(`chainAdmin k.env c = some k.sender`). -/
@[headline] def Properties.RolesTraceToAVerifiedChainAdmin : Prop :=
  (∀ c, ChainRolesEmpty init c) ∧
  ∀ (s₀ s : State) (ks : List Call) (c : Address), ChainRolesEmpty s₀ c → Run s₀ ks s →
    ¬ ChainRolesEmpty s c →
    ∃ k ∈ ks, k.action.writesRolesOf k.env c ∧ chainAdmin k.env c = some k.sender

/-- **HEADLINE: THE TIMELOCK FORWARDS ONLY TO ADDRESSES THE BRIDGEHUB ONCE REGISTERED.** Take
any run of successful calls from fresh storage, followed by a successful call that forwards to
`c`. Then some call `k₀` of the run wrote `c`'s registry, and in `k₀`'s environment `c` reported
a chain id `id` with `BRIDGE_HUB.getZKChain(id) = c`, and `c`'s `getAdmin()` returned `k₀`'s
sender. -/
@[headline] def Properties.ForwardsOnlyToOnceRegisteredChains : Prop :=
  ∀ (ks : List Call) (s s' : State) (k : Call) (c : Address) (r : Role),
    Run init ks s → step k s = some s' → k.action.forward = some (c, r) →
    ∃ k₀ ∈ ks, k₀.action.writesRolesOf k₀.env c ∧
      ∃ id, k₀.env.chainIdOf c = some id ∧ k₀.env.zkChain id = c ∧
        k₀.env.adminOf c = some k₀.sender

/-! ## The check is load-bearing -/

/-- **WITHOUT THE BRIDGEHUB CHECK, AN UNREGISTERED CONTRACT GETS ROLES.** Address `200` reports
chain id `270` and admin `5`, but the bridgehub maps `270` to `100`, so `200` has no verified
admin. With the lookup of `hasRoleUnchecked`, `5` grants itself `COMMITTER_ROLE` on `200` from
fresh storage, and then the deployed `commitBatchesSharedBridge` by `5` succeeds and forwards
to `200`. The deployed `grantRole` of the same call reverts. -/
@[countermodel] def Properties.UncheckedLookupGrantsOnUnregisteredChain : Prop :=
  chainAdmin (vtEnv 0) vtFake = none ∧ (vtEnv 0).adminOf vtFake = some vtFakeAdmin ∧
  (∃ s s' : State,
    grantRoleUnchecked (vtEnv 0) vtFakeAdmin vtFake COMMITTER_ROLE vtFakeAdmin init = some s ∧
    s.members vtFake COMMITTER_ROLE vtFakeAdmin = true ∧
    step (vtCall 0 vtFakeAdmin (.commitBatches vtFake 1 1)) s = some s') ∧
  step (vtCall 0 vtFakeAdmin (.grantRole vtFake COMMITTER_ROLE vtFakeAdmin)) init = none

/-! ## Witness -/

/-- **ROLES CAN BE DELEGATED, SO THE TRACE IS TO AN EARLIER CALL.** After the witness setup,
the chain admin `2` makes `OPTIONAL_COMMITTER_ADMIN_ROLE` the admin role of `COMMITTER_ROLE` on
chain `100` and grants it to `4`; then `4`, which is not the chain's admin, grants
`COMMITTER_ROLE` to `6`, and `6`'s commit succeeds. The chain admin's own grant of
`COMMITTER_ROLE` now reverts, since it does not hold the new admin role. The run's last grant is
not by the verified admin; `RolesTraceToAVerifiedChainAdmin` finds the admin's earlier calls. -/
@[witness] def Properties.RoleDelegationWitness : Prop :=
  ∃ s₀ s s' : State,
    Run init vtSetupCalls s₀ ∧
    Run s₀ [vtCall 1 vtAdmin (.setRoleAdmin vtChain COMMITTER_ROLE OPTIONAL_COMMITTER_ADMIN_ROLE),
            vtCall 1 vtAdmin (.grantRole vtChain OPTIONAL_COMMITTER_ADMIN_ROLE vtManager),
            vtCall 2 vtManager (.grantRole vtChain COMMITTER_ROLE vtDelegate)] s ∧
    chainAdmin (vtEnv 2) vtChain = some vtAdmin ∧ vtManager ≠ vtAdmin ∧
    s.members vtChain COMMITTER_ROLE vtDelegate = true ∧
    step (vtCall 3 vtDelegate (.commitBatches vtChain 1 1)) s = some s' ∧
    step (vtCall 3 vtAdmin (.grantRole vtChain COMMITTER_ROLE vtDelegate)) s = none

end Contracts.ValidatorTimelock
