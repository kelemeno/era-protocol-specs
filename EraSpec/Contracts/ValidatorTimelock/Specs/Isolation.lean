import EraSpec.Contracts.ValidatorTimelock.Specs.Model

/-!
# Model: what one chain's calls depend on

Definitions for the isolation statements about `EraSpec.Contracts.ValidatorTimelock.Specs.Model`
(source `b17415d20`). The statements are in
`EraSpec.Contracts.ValidatorTimelock.Properties.Isolation` and are proved in
`EraSpec.Contracts.ValidatorTimelock.Proofs.Isolation`.

The timelock keeps one storage for all chains: the owner fields and the ecosystem-wide delay
are shared, and the role registry, the chain delay and the commit timestamps are kept per chain
address. `AgreeOn c s t` says two states have the same shared fields and the same storage for
chain `c`. A call `concerns` chain `c` if it addresses `c` (`Action.chain`) or no chain at all.
-/

namespace Contracts.ValidatorTimelock

/-- `s` and `t` agree on the shared fields (initialization, owner, pending owner, ecosystem
delay) and on chain `c`'s storage (role members, role admins, chain delay, commit
timestamps). -/
def AgreeOn (c : Address) (s t : State) : Prop :=
  s.initialized = t.initialized ∧ s.owner = t.owner ∧ s.pendingOwner = t.pendingOwner ∧
  s.executionDelay = t.executionDelay ∧ s.members c = t.members c ∧
  s.adminRole c = t.adminRole c ∧ s.chainDelay c = t.chainDelay c ∧
  s.committedAt c = t.committedAt c

/-- The call addresses chain `c` (for a `…ForChainId` wrapper, the bridgehub answers `c` in the
call's environment) or addresses no chain. -/
def Call.concerns (k : Call) (c : Address) : Prop :=
  k.action.chain k.env = some c ∨ k.action.chain k.env = none

instance (k : Call) (c : Address) : Decidable (k.concerns c) :=
  inferInstanceAs (Decidable (k.action.chain k.env = some c ∨ k.action.chain k.env = none))

/-- An owner call on another chain, for the isolation witness: the owner sets the chain delay
of address `200` to `50`. -/
def vtOtherChainCall : Call := vtCall 1 vtOwner (.setChainExecutionDelay vtFake 50)

end Contracts.ValidatorTimelock
