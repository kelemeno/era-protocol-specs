import EraSpec.Contracts.ServerNotifier.Specs.Model

/-!
# Properties: who can set a chain's upgrade timestamp

Statements about `EraSpec.Contracts.ServerNotifier.Specs.Model`; proofs in
`EraSpec.Contracts.ServerNotifier.Proofs.Model`.

* `TimestampWritesAuthorized` (run-level): every write in the log was made by the chain's
  admin as reported by the CTM read, for the chain's current version with an upgrade
  scheduled from it; every schedule entry that differs from the start is the value of such a
  write.
* `TimestampNeverResetToZero` (run-level): once an entry is nonzero it stays nonzero.
* `OnlyOwnerConfigures`: `chainTypeManager` and the checker table change only by the owner's
  calls, and `chainTypeManager` never becomes zero.
* `InitializeOnce` (run-level): after `initialize`, no further `initialize` succeeds.
* `MigrationEventsAuthorized` (run-level): every migration event was emitted by the chain's
  admin with the asset handler's migration number plus one, and to the gateway only for a
  chain that was ready.
* `OwnerRedirectsTimestampAuthority` (observation): the chain-admin check is only as strong
  as the `chainTypeManager` pointer, which the owner sets. The owner, not a chain admin per
  the original CTM, can write a chain's schedule after repointing it.
* `ZeroCheckLoadBearing` (countermodel): without the zero check, a scheduled entry can be
  reset to zero.
* `ScheduleWitness`: from a fresh proxy, initialize, set the CTM, and schedule.
-/

namespace Contracts.ServerNotifier

/-- **EVERY TIMESTAMP WRITE IS AUTHORIZED, AND EVERY CHANGE IS A WRITE.** Along any
interleaving of transactions in any environments, from a state with an empty write log:
every logged write is `Authorized` (made by `getChainAdmin(chain)` of the CTM it read, for
that CTM's `getProtocolVersion(chain)`, with an upgrade scheduled from it, a nonzero value and
a nonzero CTM); and every entry `ts c v` that differs from its starting value equals the
value of a logged write for `(c, v)`. -/
def Properties.TimestampWritesAuthorized : Prop :=
  ∀ (s₀ s : State), s₀.writes = [] → Reach s₀ s →
    (∀ w ∈ s.writes, w.Authorized) ∧
    ∀ c v, s.ts c v ≠ s₀.ts c v →
      ∃ w ∈ s.writes, w.chain = c ∧ w.version = v ∧ w.value = s.ts c v

/-- **A SET TIMESTAMP IS NEVER CLEARED.** Along any run, an entry that is nonzero stays
nonzero. -/
def Properties.TimestampNeverResetToZero : Prop :=
  ∀ (s s' : State) (c v : UInt256), Reach s s' → s.ts c v ≠ 0 → s'.ts c v ≠ 0

/-- **ONLY THE OWNER CONFIGURES.** In one transaction, if `chainTypeManager` changes, the
transaction is `setChainTypeManager(new)` by the owner with `new ≠ 0`; if the checker table
changes, it is `setUpgradePreconditionChecker` by the owner. Every step keeps a nonzero
`chainTypeManager` nonzero. -/
def Properties.OnlyOwnerConfigures : Prop :=
  ∀ (E : Env) (s s' : State) (l : Label), Step E s l s' →
    (s'.ctm ≠ s.ctm → l = .setCTM s.owner s'.ctm ∧ s'.ctm ≠ 0) ∧
    (s'.checker ≠ s.checker → ∃ v a, l = .setChecker s.owner v a) ∧
    (s.ctm ≠ 0 → s'.ctm ≠ 0)

/-- **`initialize` RUNS AT MOST ONCE.** After a successful `initialize`, along any run, no
`initialize` succeeds. -/
def Properties.InitializeOnce : Prop :=
  ∀ (E E' : Env) (s s' s'' s''' : State) (c o c' o' : Address),
    Step E s (.init c o) s' → Reach s' s'' → ¬ Step E' s'' (.init c' o') s'''

/-- **MIGRATION EVENTS ARE AUTHORIZED.** Along any run from a state with no logged events,
every `MigrateToGateway`/`MigrateFromGateway` was emitted by the chain's admin as reported by
the CTM read, carries the chain asset handler's migration number plus one, and (to the
gateway) only for a chain ready for migration. -/
def Properties.MigrationEventsAuthorized : Prop :=
  ∀ (s₀ s : State), s₀.events = [] → Reach s₀ s → ∀ e ∈ s.events, e.Authorized

/-- **OBSERVATION: THE OWNER CAN REDIRECT TIMESTAMP AUTHORITY.** There are environments and a
two-transaction run in which the CTM at `chainTypeManager` names `10` as chain `1`'s admin,
the owner `20 ≠ 10` repoints `chainTypeManager` to a contract naming itself admin, and then
writes chain `1`'s schedule. `ChainTypeManager/Specs/UpgradeTiming.lean` assumes the
notifier's `chainTypeManager` is the CTM; this is what that assumption excludes. -/
def Properties.OwnerRedirectsTimestampAuthority : Prop :=
  ∃ (E₁ E₂ : Env) (s₀ s₁ s₂ : State) (V₀ : CtmView) (t : UInt256),
    E₁.ctm s₀.ctm = some V₀ ∧ V₀.chainAdmin 1 = 10 ∧ s₀.owner = 20 ∧
    Step E₁ s₀ (.setCTM 20 77) s₁ ∧ Step E₂ s₁ (.setTs 20 1 t) s₂ ∧
    ∃ v, s₂.ts 1 v ≠ s₀.ts 1 v

/-- **COUNTERMODEL: THE ZERO CHECK IS LOAD-BEARING.** Without `_upgradeTimestamp == 0`
(:114-116), a write clears a nonzero entry, which `TimestampNeverResetToZero` excludes. -/
def Properties.ZeroCheckLoadBearing : Prop :=
  ∃ (E : Env) (s s' : State) (l : Label) (c v : UInt256),
    SetTsNoZeroCheck E s l s' ∧ s.ts c v ≠ 0 ∧ s'.ts c v = 0

/-- **WITNESS.** From a fresh proxy: `initialize(5)`, the owner sets the CTM to `9`, and
chain `1`'s admin `7` (per the CTM, at version `3` with a transition scheduled) sets
timestamp `1000`; the entry for `(1, 3)` is `1000`. -/
def Properties.ScheduleWitness : Prop :=
  ∃ s : State, Reach fresh s ∧ s.ts 1 3 = 1000 ∧ s.owner = 5 ∧ s.ctm = 9

end Contracts.ServerNotifier
