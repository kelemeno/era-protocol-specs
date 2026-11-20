import EraSpec.Contracts.ValidatorTimelock.Specs.Model
import EraSpec.Core.Headline

/-!
# Properties: what each `ValidatorTimelock` entry point checks and writes

Statements about `EraSpec.Contracts.ValidatorTimelock.Specs.Model` (source `b17415d20`).
Proofs are in `EraSpec.Contracts.ValidatorTimelock.Proofs.Model`. These are statements about
one call (with one witness run); the run-level results are in `Properties.Delay`,
`Properties.Roles`, `Properties.Isolation` and `Properties.Ownership`.

* **The forwarding entry points check exactly their role** (`ForwardingGuardsExact`). They
  read only the registry's membership bit, never the chain's admin or the bridgehub, because
  the five role constants are nonzero. Only `commitBatches` writes storage: the timestamps of
  its range.
* **The owner entry points** (`OwnerCallsExact`): OpenZeppelin's `initialize`, two-step
  handover and renounce, exactly.
* **The delay setters** (`DelaySettersExact`): the owner's two setters need the owner and the
  30-day bound; `increaseChainExecutionDelay` needs the chain's verified admin, the bound, and
  a value above the enforced delay.
* **The role registry** (`RegistryWritesExact`): a grant, revoke or role-admin change of `r`
  needs `r ≠ DEFAULT_ADMIN_ROLE` and the caller to hold `r`'s admin role (`HoldsAdminOf`);
  a renounce needs the caller's own membership and removes only it.
  `DEFAULT_ADMIN_ROLE` itself can be neither granted, revoked, renounced nor re-administered
  (`DefaultAdminRoleIsNotTransferable`).
* **The rotation wrappers** are their grants or revokes (`RotationIsItsGrants`), with the role
  lists of the source: `addValidator` does not grant the retired `PRECOMMITTER_ROLE`,
  `removeValidator` revokes it.
* **Each call touches only its own chain's per-chain storage** (`CallsTouchOnlyTheirChain`).
-/

namespace Contracts.ValidatorTimelock

/-- **THE FORWARDING ENTRY POINTS CHECK EXACTLY THEIR ROLE.** A call of
`commitBatchesSharedBridge`, `executeBatchesSharedBridge`, `revertBatchesSharedBridge`,
`proveBatchesSharedBridge` or either `upgradeChainFromVersion` on chain `c` succeeds exactly
when the caller is a member of `COMMITTER_ROLE`, `EXECUTOR_ROLE`, `REVERTER_ROLE`,
`PROVER_ROLE` or `UPGRADER_ROLE` of `c` respectively, the forwarded call succeeds, and, for
commit and execute, the range is valid and (execute only) every batch of it has waited the
enforced delay. The chain's admin and the bridgehub are not consulted. A commit writes the
range's timestamps (`recordCommit`); the other four leave storage unchanged. -/
@[headline] def Properties.ForwardingGuardsExact : Prop :=
  ∀ (e : Env) (x c : Address) (s s' : State),
    (∀ lo hi, step ⟨e, x, .commitBatches c lo hi⟩ s = some s' ↔
      s.members c COMMITTER_ROLE x = true ∧ validRange lo hi ∧ e.forwardOk = true ∧
        s' = recordCommit s c lo hi e.now) ∧
    (∀ lo hi, step ⟨e, x, .executeBatches c lo hi⟩ s = some s' ↔
      s.members c EXECUTOR_ROLE x = true ∧ validRange lo hi ∧ delayPassed s c lo hi e.now ∧
        e.forwardOk = true ∧ s' = s) ∧
    (step ⟨e, x, .revertBatches c⟩ s = some s' ↔
      s.members c REVERTER_ROLE x = true ∧ e.forwardOk = true ∧ s' = s) ∧
    (step ⟨e, x, .proveBatches c⟩ s = some s' ↔
      s.members c PROVER_ROLE x = true ∧ e.forwardOk = true ∧ s' = s) ∧
    (∀ w, step ⟨e, x, .upgradeChainFromVersion c w⟩ s = some s' ↔
      s.members c UPGRADER_ROLE x = true ∧ e.forwardOk = true ∧ s' = s)

/-- **THE OWNER ENTRY POINTS.** `initialize(o, d)` succeeds exactly on uninitialized storage
with `d ≤ MAX_EXECUTION_DELAY`, whoever sends it, and sets the owner to `o`, clears the
pending owner and sets the ecosystem delay to `d`. `transferOwnership(n)` succeeds exactly for
the owner and only sets the pending owner (`n = 0` included). `acceptOwnership()` succeeds
exactly for the pending owner, who becomes the owner, with the pending owner cleared.
`renounceOwnership()` succeeds exactly for the owner and clears both. -/
def Properties.OwnerCallsExact : Prop :=
  ∀ (e : Env) (x o n : Address) (d : ℕ) (s s' : State),
    (step ⟨e, x, .initializeTimelock o d⟩ s = some s' ↔
      s.initialized = false ∧ d ≤ MAX_EXECUTION_DELAY ∧
        s' = { s with initialized := true, owner := o, pendingOwner := 0, executionDelay := d }) ∧
    (step ⟨e, x, .transferOwnership n⟩ s = some s' ↔
      x = s.owner ∧ s' = { s with pendingOwner := n }) ∧
    (step ⟨e, x, .acceptOwnership⟩ s = some s' ↔
      x = s.pendingOwner ∧ s' = { s with owner := x, pendingOwner := 0 }) ∧
    (step ⟨e, x, .renounceOwnership⟩ s = some s' ↔
      x = s.owner ∧ s' = { s with owner := 0, pendingOwner := 0 })

/-- **THE DELAY SETTERS.** `setExecutionDelay(d)` and `setChainExecutionDelay(c, d)` succeed
exactly when the caller is the owner and `d ≤ MAX_EXECUTION_DELAY` (30 days), and write only
that delay. `increaseChainExecutionDelay(c, d)` succeeds exactly when the caller is `c`'s
verified admin (`chainAdmin`: `c` reports a chain id the bridgehub maps to `c`, and `c`'s
`getAdmin()` is the caller), `d ≤ MAX_EXECUTION_DELAY`, and `d` exceeds the delay enforced for
`c`; it writes only `c`'s chain delay. -/
def Properties.DelaySettersExact : Prop :=
  ∀ (e : Env) (x c : Address) (d : ℕ) (s s' : State),
    (step ⟨e, x, .setExecutionDelay d⟩ s = some s' ↔
      x = s.owner ∧ d ≤ MAX_EXECUTION_DELAY ∧ s' = { s with executionDelay := d }) ∧
    (step ⟨e, x, .setChainExecutionDelay c d⟩ s = some s' ↔
      x = s.owner ∧ d ≤ MAX_EXECUTION_DELAY ∧ s' = { s with chainDelay := upd s.chainDelay c d }) ∧
    (step ⟨e, x, .increaseChainExecutionDelay c d⟩ s = some s' ↔
      chainAdmin e c = some x ∧ d ≤ MAX_EXECUTION_DELAY ∧ enforcedDelay s c < d ∧
        s' = { s with chainDelay := upd s.chainDelay c d })

/-- **THE ROLE REGISTRY.** On chain `c`: `grantRole(c, r, a)` and `revokeRole(c, r, a)` succeed
exactly when `r ≠ DEFAULT_ADMIN_ROLE` and the caller holds `r`'s admin role
(`HoldsAdminOf`), and then set or clear `a`'s membership of `r` and nothing else.
`renounceRole(c, r)` succeeds exactly when `r ≠ DEFAULT_ADMIN_ROLE` and the caller is a member
of `r`, and clears only the caller's membership. `setRoleAdmin(c, r, ar)` succeeds exactly when
`r ≠ DEFAULT_ADMIN_ROLE` and the caller holds `r`'s admin role, and sets only `r`'s admin role
on `c` to `ar`. -/
def Properties.RegistryWritesExact : Prop :=
  ∀ (e : Env) (x c : Address) (r ar : Role) (a : Address) (s s' : State),
    (step ⟨e, x, .grantRole c r a⟩ s = some s' ↔
      r ≠ DEFAULT_ADMIN_ROLE ∧ HoldsAdminOf e s c r x ∧ s' = setMember s c r a true) ∧
    (step ⟨e, x, .revokeRole c r a⟩ s = some s' ↔
      r ≠ DEFAULT_ADMIN_ROLE ∧ HoldsAdminOf e s c r x ∧ s' = setMember s c r a false) ∧
    (step ⟨e, x, .renounceRole c r⟩ s = some s' ↔
      r ≠ DEFAULT_ADMIN_ROLE ∧ s.members c r x = true ∧ s' = setMember s c r x false) ∧
    (step ⟨e, x, .setRoleAdmin c r ar⟩ s = some s' ↔
      r ≠ DEFAULT_ADMIN_ROLE ∧ HoldsAdminOf e s c r x ∧
        s' = { s with adminRole := fun c' r' => if c' = c ∧ r' = r then ar else s.adminRole c' r' })

/-- **`DEFAULT_ADMIN_ROLE` IS NOT TRANSFERABLE.** For every caller, environment and state,
`grantRole`, `revokeRole`, `renounceRole` and `setRoleAdmin` of `DEFAULT_ADMIN_ROLE` revert
(`DefaultAdminTransferNotAllowed`, `AC:120-122`, `:160-162`, `:178-180`). The role is held
only through `chainAdmin`. -/
def Properties.DefaultAdminRoleIsNotTransferable : Prop :=
  ∀ (e : Env) (x c a : Address) (ar : Role) (s : State),
    step ⟨e, x, .grantRole c DEFAULT_ADMIN_ROLE a⟩ s = none ∧
    step ⟨e, x, .revokeRole c DEFAULT_ADMIN_ROLE a⟩ s = none ∧
    step ⟨e, x, .renounceRole c DEFAULT_ADMIN_ROLE⟩ s = none ∧
    step ⟨e, x, .setRoleAdmin c DEFAULT_ADMIN_ROLE ar⟩ s = none

/-- **THE ROTATION WRAPPERS ARE THEIR GRANTS.** A successful `addValidatorRoles(c, v, p)` gives
`v` every role `p` flags on `c` and changes nothing else; `removeValidatorRoles` takes them
away. `addValidator` and `addValidatorForChainId` grant `COMMITTER_ROLE`, `REVERTER_ROLE`,
`PROVER_ROLE`, `EXECUTOR_ROLE` and `UPGRADER_ROLE` (not `PRECOMMITTER_ROLE`);
`removeValidator` and `removeValidatorForChainId` revoke those and `PRECOMMITTER_ROLE`. The
`…ForChainId` forms act on the bridgehub's answer `e.zkChain id`. Whether a wrapper succeeds is
the success of its grants or revokes one after the other (`changeMany`). -/
def Properties.RotationIsItsGrants : Prop :=
  addValidatorParams.roles = [COMMITTER_ROLE, REVERTER_ROLE, PROVER_ROLE, EXECUTOR_ROLE,
      UPGRADER_ROLE] ∧
  removeValidatorParams.roles = [PRECOMMITTER_ROLE, COMMITTER_ROLE, REVERTER_ROLE, PROVER_ROLE,
      EXECUTOR_ROLE, UPGRADER_ROLE] ∧
  ∀ (e : Env) (x c v : Address) (id : UInt256) (p : RotationParams) (s s' : State),
    (step ⟨e, x, .addValidatorRoles c v p⟩ s = some s' → s' = setMembers s c v p.roles true) ∧
    (step ⟨e, x, .removeValidatorRoles c v p⟩ s = some s' →
      s' = setMembers s c v p.roles false) ∧
    (step ⟨e, x, .addValidator c v⟩ s = some s' →
      s' = setMembers s c v addValidatorParams.roles true) ∧
    (step ⟨e, x, .removeValidator c v⟩ s = some s' →
      s' = setMembers s c v removeValidatorParams.roles false) ∧
    (step ⟨e, x, .addValidatorForChainId id v⟩ s = some s' →
      s' = setMembers s (e.zkChain id) v addValidatorParams.roles true) ∧
    (step ⟨e, x, .removeValidatorForChainId id v⟩ s = some s' →
      s' = setMembers s (e.zkChain id) v removeValidatorParams.roles false)

/-- **EACH CALL TOUCHES ONLY ITS OWN CHAIN.** A successful call leaves the role members, the
role admins, the chain delay and the commit timestamps of every chain other than the one it
addresses (`Action.chain`) unchanged; a call that addresses no chain leaves them unchanged for
every chain. The ecosystem-wide delay is not per-chain and is not covered. -/
def Properties.CallsTouchOnlyTheirChain : Prop :=
  ∀ (k : Call) (s s' : State) (c : Address), step k s = some s' →
    k.action.chain k.env ≠ some c →
    s'.members c = s.members c ∧ s'.adminRole c = s.adminRole c ∧
      s'.chainDelay c = s.chainDelay c ∧ s'.committedAt c = s.committedAt c

/-! ## Witnesses -/

/-- **EVERY ROTATION WRAPPER RUNS.** From fresh storage, the witness setup (`initialize`, then
the chain admin's `addValidator(100, 3)`), followed by the chain admin's
`removeValidatorRoles(100, 3, committer only)`, `addValidatorRoles(100, 3, committer only)`,
`removeValidator(100, 3)`, `addValidatorForChainId(270, 3)` and
`removeValidatorForChainId(270, 3)`, all succeed. Validator `3` holds `COMMITTER_ROLE` after the
setup and none of the six validator roles at the end. -/
@[witness] def Properties.RotationWrappersRun : Prop :=
  ∃ s₀ s : State,
    Run init vtSetupCalls s₀ ∧ s₀.members vtChain COMMITTER_ROLE vtValidator = true ∧
    Run s₀ [vtCall 1 vtAdmin (.removeValidatorRoles vtChain vtValidator
              ⟨false, true, false, false, false, false⟩),
            vtCall 1 vtAdmin (.addValidatorRoles vtChain vtValidator
              ⟨false, true, false, false, false, false⟩),
            vtCall 1 vtAdmin (.removeValidator vtChain vtValidator),
            vtCall 1 vtAdmin (.addValidatorForChainId 270 vtValidator),
            vtCall 1 vtAdmin (.removeValidatorForChainId 270 vtValidator)] s ∧
    ∀ r ∈ removeValidatorParams.roles, s.members vtChain r vtValidator = false

end Contracts.ValidatorTimelock
