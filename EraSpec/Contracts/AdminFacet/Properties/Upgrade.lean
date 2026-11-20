import EraSpec.Contracts.AdminFacet.Specs.Mutants
import EraSpec.Core.Headline

/-!
# Properties: chain upgrades through the facet

Statements about `EraSpec.Contracts.AdminFacet.Specs.AdminFacet`; proofs in
`EraSpec.Contracts.AdminFacet.Proofs.Upgrade`.

* `UpgradeRunsExactlyTheCommittedCut`: `upgradeChainFromVersion(_, v)` succeeds exactly when the
  diamond does not block it, the caller is admin/CTM/validator (validators gated by the notifier),
  the CTM has a cut committed for `v`, the chain is at `v`, and running **that** cut passes the
  second-proof-system recheck and raises the version above `v`. The result is that cut's result;
  the caller supplies no cut.
* `VersionRisesAlongRuns` (run): with genuine genesis code, along any run without
  `executeUpgrade`, the protocol version never decreases and each `upgradeChainFromVersion` raises
  it by at least one.
* `GenesisRunsOnce` (run): with genuine genesis code, after a genesis upgrade with a nonzero
  transaction hash, no further genesis upgrade succeeds along a later run in which no foreign
  write zeroes the hash, whatever else happens (other than the two other cut entries).
* Witnesses: `UpgradeWitness` (a genesis upgrade and a scheduled upgrade, by a caller that is
  initially neither the admin, the CTM nor a validator, in one run), `GenesisRunsOnceWitness`.
* Countermodels: `ExecuteUpgradeCanLowerVersion` (the no-`executeUpgrade` premise is needed),
  `UpgradePostCheckIsLoadBearing` (the `ProtocolIdNotGreater` check is what makes upgrades raise
  the version), `GenesisRerunsAfterFinalization` (the premise that no foreign write clears the
  pending hash is needed: after finalization the CTM can run genesis again; once-only rests on the
  CTM calling it only from `createNewChain`).
-/

namespace Contracts.AdminFacet

/-- **AN UPGRADE RUNS EXACTLY THE CUT THE CTM COMMITTED.** "The committed cut" is the cut the CTM's
`upgradeCutForVersion` returns, an oracle here (`Env.upgradeCutForVersion`); that the CTM derives
it from the committed transition is not modelled (README, *Open*). For any caller `a`, time `τ`,
version `v`: `upgradeChainFromVersion(_, v)` succeeds with result `s'` iff

* the diamond does not block the selector;
* `a` is the admin, the CTM, or a validator;
* `IChainTypeManager(s.chainTypeManager).upgradeCutForVersion(v)` returns a cut `cut`;
* the chain is at version `v`;
* a caller other than admin and CTM finds the notifier's timestamp for `v` set and reached;
* running `cut` at time `τ` on the storage yields `s'` (`Diamond.diamondCut`, including its
  initializer);
* if `s'` requires the second proof system, its verifier's `getProofMode(0)` is multi-proof;
* `s'` has version strictly above `v`. -/
@[headline] def Properties.UpgradeRunsExactlyTheCommittedCut : Prop :=
  ∀ (K : Config) (e : Env) (s s' : State) (a : Address) (τ : ℕ) (ch : Address) (v : ℕ),
    call K e s ⟨a, τ, .upgradeChainFromVersion ch v⟩ = some s' ↔
      (¬ (s.frozen = true ∧ s.freezable (Entry.upgradeChainFromVersion 0 0).sel = true) ∧
       (a = s.admin ∨ a = s.chainTypeManager ∨ s.validators a = true) ∧
       ∃ cut, e.upgradeCutForVersion s.chainTypeManager v = some cut ∧
         s.protocolVersion = v ∧
         (a ≠ s.admin ∧ a ≠ s.chainTypeManager →
           e.upgradeTimestamp s.chainTypeManager v ≠ 0 ∧
           e.upgradeTimestamp s.chainTypeManager v ≤ τ) ∧
         K.runCut e τ cut s = some s' ∧
         (s'.secondProofSystemRequired = true →
           e.getProofMode s'.verifier 0 = ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE) ∧
         v < s'.protocolVersion)

/-- **THE VERSION RISES ALONG RUNS.** Assume the CTM's genesis address holds the genuine
`L1GenesisUpgrade` (`GenuineGenesis`: a successful genesis cut does what `genesisEffect` does).
Along any run — calls by anyone, environment changes, foreign writes, `genesisUpgrade` and
`upgradeChainFromVersion` included — that contains no `executeUpgrade`, the final version is at
least the initial version plus the number of `upgradeChainFromVersion` calls. Cuts run by those
calls may do anything else. -/
@[headline] def Properties.VersionRisesAlongRuns : Prop :=
  ∀ (K : Config) (w w' : World) (ls : List Label),
    GenuineGenesis K → Run K w ls w' → (∀ l ∈ ls, l.isExecuteUpgrade = false) →
    w.st.protocolVersion + ls.countP Label.isUpgrade ≤ w'.st.protocolVersion

/-- **THE GENESIS UPGRADE RUNS ONCE WHILE ITS TRANSACTION IS PENDING.** Assume `GenuineGenesis`. If
a `genesisUpgrade` call succeeds in a world whose CTM composes a genesis transaction with nonzero
hash (a keccak output; zero only for a preimage of `bytes32(0)`), then along any later run whose
foreign writes never clear the L2 upgrade transaction hash and which calls neither
`upgradeChainFromVersion` nor `executeUpgrade`, no `genesisUpgrade` call succeeds. -/
@[headline] def Properties.GenesisRunsOnce : Prop :=
  ∀ (K : Config) (w w₁ w₂ : World) (a : Address) (τ : ℕ) (ls : List Label),
    GenuineGenesis K →
    Step K w (.call ⟨a, τ, .genesisUpgrade⟩) w₁ →
    w.env.genesisTxHash w.st.chainTypeManager w.st.protocolVersion ≠ 0 →
    Run K w₁ ls w₂ →
    (∀ l ∈ ls, l.isUpgrade = false ∧ l.isExecuteUpgrade = false) →
    (∀ s', Label.foreign s' ∈ ls → s'.upgradeTxHash ≠ 0) →
    ∀ l ∈ ls, l.isGenesis = false

/-! ## Witnesses -/

/-- **WITNESS: A GENESIS UPGRADE AND A VALIDATOR'S UPGRADE IN ONE RUN.** With genuine genesis code,
there is a run without `executeUpgrade` that contains exactly one `genesisUpgrade` and exactly one
`upgradeChainFromVersion`, the latter from the initial version by a caller that is initially
neither the admin, the CTM nor a validator, and that ends exactly one version higher (the premises
of `VersionRisesAlongRuns`, its bound met with equality). -/
@[witness] def Properties.UpgradeWitness : Prop :=
  ∃ (K : Config) (w w' : World) (ls : List Label) (a : Address) (τ : ℕ),
    GenuineGenesis K ∧ Run K w ls w' ∧ (∀ l ∈ ls, l.isExecuteUpgrade = false) ∧
    Label.call ⟨a, τ, .upgradeChainFromVersion 0 w.st.protocolVersion⟩ ∈ ls ∧
    a ≠ w.st.admin ∧ a ≠ w.st.chainTypeManager ∧ w.st.validators a = false ∧
    w'.st.protocolVersion = w.st.protocolVersion + 1 ∧
    ls.countP Label.isUpgrade = 1 ∧ ls.countP Label.isGenesis = 1

/-- **WITNESS: THE PREMISES OF `GenesisRunsOnce` HOLD TOGETHER.** With genuine genesis code, a
`genesisUpgrade` step whose CTM composes a transaction with nonzero hash is followed by a run
without `upgradeChainFromVersion` and `executeUpgrade` that contains a call, an environment change
and a foreign write, all of whose foreign writes leave the hash nonzero. -/
@[witness] def Properties.GenesisRunsOnceWitness : Prop :=
  ∃ (K : Config) (w w₁ w₂ : World) (a : Address) (τ : ℕ) (ls : List Label),
    GenuineGenesis K ∧ Step K w (.call ⟨a, τ, .genesisUpgrade⟩) w₁ ∧
    w.env.genesisTxHash w.st.chainTypeManager w.st.protocolVersion ≠ 0 ∧
    Run K w₁ ls w₂ ∧ (∀ l ∈ ls, l.isUpgrade = false ∧ l.isExecuteUpgrade = false) ∧
    (∀ s', Label.foreign s' ∈ ls → s'.upgradeTxHash ≠ 0) ∧
    (∃ c, Label.call c ∈ ls) ∧ (∃ e, Label.env e ∈ ls) ∧ (∃ s', Label.foreign s' ∈ ls)

/-! ## Countermodels -/

/-- **COUNTERMODEL: `executeUpgrade` CAN LOWER THE VERSION.** The CTM's `executeUpgrade` runs any
cut it is handed, with no version check (`Admin.sol:593-595`). With genuine genesis code, a run
containing exactly one `executeUpgrade` ends below the initial version. So `VersionRisesAlongRuns`
needs its no-`executeUpgrade` premise. -/
@[countermodel] def Properties.ExecuteUpgradeCanLowerVersion : Prop :=
  ∃ (K : Config) (w w' : World) (ls : List Label),
    GenuineGenesis K ∧ Run K w ls w' ∧ ls.countP Label.isExecuteUpgrade = 1 ∧
    w'.st.protocolVersion < w.st.protocolVersion

/-- **COUNTERMODEL: THE `ProtocolIdNotGreater` CHECK IS LOAD-BEARING.** Without
`Admin.sol:587-589`, the admin's `upgradeChainFromVersion` with a committed cut that does not raise
the version succeeds; the transcribed entry reverts on the same call. -/
@[countermodel] def Properties.UpgradePostCheckIsLoadBearing : Prop :=
  ∃ (K : Config) (e : Env) (s s' : State) (τ v : ℕ),
    upgradeWithoutPostCheck K e s ⟨s.admin, τ, .upgradeChainFromVersion 0 v⟩ v = some s' ∧
    s'.protocolVersion ≤ s.protocolVersion ∧
    call K e s ⟨s.admin, τ, .upgradeChainFromVersion 0 v⟩ = none

/-- **COUNTERMODEL: GENESIS CAN RUN AGAIN ONCE ITS TRANSACTION IS FINALIZED.** `GenesisRunsOnce`
needs its premise that no foreign write clears the L2 upgrade transaction hash. With genuine
genesis code, a successful `genesisUpgrade` whose CTM composes a transaction with nonzero hash is
followed by a run without `upgradeChainFromVersion` and `executeUpgrade` that contains a foreign
write leaving the hash zero (as the Executor's finalization does, `Executor.sol:209-210`) and a
further successful `genesisUpgrade`. The facet makes genesis once-only only while the transaction
is pending; beyond that it rests on the CTM, whose only call is in `createNewChain`
(`ChainTypeManager.sol:703-707`). -/
@[countermodel] def Properties.GenesisRerunsAfterFinalization : Prop :=
  ∃ (K : Config) (w w₁ w₂ : World) (a : Address) (τ : ℕ) (ls : List Label),
    GenuineGenesis K ∧ Step K w (.call ⟨a, τ, .genesisUpgrade⟩) w₁ ∧
    w.env.genesisTxHash w.st.chainTypeManager w.st.protocolVersion ≠ 0 ∧
    Run K w₁ ls w₂ ∧ (∀ l ∈ ls, l.isUpgrade = false ∧ l.isExecuteUpgrade = false) ∧
    (∃ s', Label.foreign s' ∈ ls ∧ s'.upgradeTxHash = 0) ∧
    ∃ l ∈ ls, l.isGenesis = true

end Contracts.AdminFacet
