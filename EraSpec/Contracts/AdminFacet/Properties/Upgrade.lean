import EraSpec.Contracts.AdminFacet.Specs.Mutants

/-!
# Properties: chain upgrades through the facet

Statements about `EraSpec.Contracts.AdminFacet.Specs.AdminFacet`; proofs in
`EraSpec.Contracts.AdminFacet.Proofs.Upgrade`.

* `UpgradeRunsExactlyTheCommittedCut`: `upgradeChainFromVersion(_, v)` succeeds exactly when the
  chain is at `v`, the caller is admin/CTM/validator (validators gated by the notifier), the CTM
  has a cut committed for `v`, and running **that** cut raises the version above `v`. The result
  is that cut's result; the caller supplies no cut.
* `VersionRisesAlongRuns` (run): with genuine genesis code, along any run without
  `executeUpgrade`, the protocol version never decreases and each `upgradeChainFromVersion` raises
  it by at least one.
* `GenesisRunsOnce` (run): with genuine genesis code, after a genesis upgrade no further genesis
  upgrade can succeed while its L2 transaction is pending, whatever else happens (other than the
  two other cut entries).
* `UpgradeWitness`: a concrete run with genesis, finalization, a validator added by the CTM, and
  that validator's scheduled upgrade.
* Countermodels: `ExecuteUpgradeCanLowerVersion` (the run premise is needed),
  `UpgradePostCheckIsLoadBearing` (the `ProtocolIdNotGreater` check is what makes upgrades raise
  the version), `GenesisRerunsAfterFinalization` (the facet alone does not make genesis
  once-only: after finalization the CTM can run it again; once-only rests on the CTM calling it
  only from `createNewChain`).
-/

namespace Contracts.AdminFacet

/-- **AN UPGRADE RUNS EXACTLY THE CUT THE CTM COMMITTED.** For any caller `a`, time `τ`, version
`v`: `upgradeChainFromVersion(_, v)` succeeds with result `s'` iff

* the diamond does not block the selector;
* `a` is the admin, the CTM, or a validator;
* `IChainTypeManager(s.chainTypeManager).upgradeCutForVersion(v)` returns a cut `cut`;
* the chain is at version `v`;
* a caller other than admin and CTM finds the notifier's timestamp for `v` set and reached;
* running `cut` on the storage yields `s'` (`Diamond.diamondCut`, including its initializer);
* if `s'` requires the second proof system, its verifier's `getProofMode(0)` is multi-proof;
* `s'` has version strictly above `v`. -/
def Properties.UpgradeRunsExactlyTheCommittedCut : Prop :=
  ∀ (K : Config) (e : Env) (s s' : State) (a : Address) (τ : ℕ) (ch : Address) (v : ℕ),
    call K e s ⟨a, τ, .upgradeChainFromVersion ch v⟩ = some s' ↔
      (¬ (s.frozen = true ∧ s.freezable (Entry.upgradeChainFromVersion 0 0).sel = true) ∧
       (a = s.admin ∨ a = s.chainTypeManager ∨ s.validators a = true) ∧
       ∃ cut, e.upgradeCutForVersion s.chainTypeManager v = some cut ∧
         s.protocolVersion = v ∧
         (a ≠ s.admin ∧ a ≠ s.chainTypeManager →
           e.upgradeTimestamp s.chainTypeManager v ≠ 0 ∧
           e.upgradeTimestamp s.chainTypeManager v ≤ τ) ∧
         K.runCut e cut s = some s' ∧
         (s'.secondProofSystemRequired = true →
           e.getProofMode s'.verifier 0 = ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE) ∧
         v < s'.protocolVersion)

/-- **THE VERSION RISES ALONG RUNS.** Assume the CTM's genesis address holds the genuine
`L1GenesisUpgrade` (`GenuineGenesis`: a successful genesis cut does what `genesisEffect` does). Along any run — calls by anyone, environment changes,
foreign writes, `genesisUpgrade` and `upgradeChainFromVersion` included — that contains no
`executeUpgrade`, the final version is at least the initial version plus the number of
`upgradeChainFromVersion` calls. Cuts run by those calls may do anything else. -/
def Properties.VersionRisesAlongRuns : Prop :=
  ∀ (K : Config) (w w' : World) (ls : List Label),
    GenuineGenesis K → Run K w ls w' → (∀ l ∈ ls, l.isExecuteUpgrade = false) →
    w.st.protocolVersion + ls.countP Label.isUpgrade ≤ w'.st.protocolVersion

/-- **THE GENESIS UPGRADE RUNS ONCE WHILE ITS TRANSACTION IS PENDING.** Assume `GenuineGenesis`. If
a `genesisUpgrade` call succeeds in a world whose CTM composes a genesis transaction with nonzero
hash, then along any later run whose foreign writes never clear the L2 upgrade transaction hash
and which calls neither `upgradeChainFromVersion` nor `executeUpgrade`, no `genesisUpgrade` call
succeeds. -/
def Properties.GenesisRunsOnce : Prop :=
  ∀ (K : Config) (w w₁ w₂ : World) (a : Address) (τ : ℕ) (ls : List Label),
    GenuineGenesis K →
    Step K w (.call ⟨a, τ, .genesisUpgrade⟩) w₁ →
    w.env.genesisTxHash w.st.chainTypeManager w.st.protocolVersion ≠ 0 →
    Run K w₁ ls w₂ →
    (∀ l ∈ ls, l.isUpgrade = false ∧ l.isExecuteUpgrade = false) →
    (∀ s', Label.foreign s' ∈ ls → s'.upgradeTxHash ≠ 0) →
    ∀ l ∈ ls, l.isGenesis = false

/-- **WITNESS: GENESIS, THEN A VALIDATOR'S SCHEDULED UPGRADE.** With genuine genesis code, a run
from a fresh chain — the CTM's genesis upgrade, the Executor finalizing its transaction, the CTM
adding a validator, and that validator (neither admin nor CTM) upgrading once the notifier's time
is reached — raises the version by one and contains exactly one genesis upgrade. -/
def Properties.UpgradeWitness : Prop :=
  ∃ (K : Config) (w w' : World) (ls : List Label) (a : Address) (τ : ℕ),
    GenuineGenesis K ∧ Run K w ls w' ∧
    Label.call ⟨a, τ, .upgradeChainFromVersion 0 w.st.protocolVersion⟩ ∈ ls ∧
    a ≠ w.st.admin ∧ a ≠ w.st.chainTypeManager ∧
    w'.st.protocolVersion = w.st.protocolVersion + 1 ∧ ls.countP Label.isGenesis = 1

/-- **COUNTERMODEL: `executeUpgrade` CAN LOWER THE VERSION.** The CTM's `executeUpgrade` runs any
cut it is handed, with no version check; a cut that lowers the version succeeds. So
`VersionRisesAlongRuns` needs its no-`executeUpgrade` premise. -/
def Properties.ExecuteUpgradeCanLowerVersion : Prop :=
  ∃ (K : Config) (e : Env) (s s' : State) (τ : ℕ) (cut : Cut),
    call K e s ⟨s.chainTypeManager, τ, .executeUpgrade cut⟩ = some s' ∧
    s'.protocolVersion < s.protocolVersion

/-- **COUNTERMODEL: THE `ProtocolIdNotGreater` CHECK IS LOAD-BEARING.** Without
`Admin.sol:587-589`, the admin's `upgradeChainFromVersion` with a committed cut that leaves the
version unchanged succeeds; the real entry reverts on it. -/
def Properties.UpgradePostCheckIsLoadBearing : Prop :=
  ∃ (K : Config) (e : Env) (s s' : State) (τ v : ℕ),
    upgradeWithoutPostCheck K e s ⟨s.admin, τ, .upgradeChainFromVersion 0 v⟩ v = some s' ∧
    s'.protocolVersion ≤ s.protocolVersion ∧
    call K e s ⟨s.admin, τ, .upgradeChainFromVersion 0 v⟩ = none

/-- **SCOPE: GENESIS CAN RUN AGAIN AFTER FINALIZATION.** With genuine genesis code, a run in which
the CTM calls `genesisUpgrade`, the Executor finalizes the genesis transaction (clearing its hash,
`Executor.sol:209-210`), and the CTM calls `genesisUpgrade` again, succeeds. The facet makes
genesis once-only only while the transaction is pending (`GenesisRunsOnce`); beyond that it rests
on the CTM, whose only call is in `createNewChain` (`ChainTypeManager.sol:703-707`). -/
def Properties.GenesisRerunsAfterFinalization : Prop :=
  ∃ (K : Config) (w w' : World) (ls : List Label),
    GenuineGenesis K ∧ Run K w ls w' ∧ ls.countP Label.isGenesis = 2

end Contracts.AdminFacet
