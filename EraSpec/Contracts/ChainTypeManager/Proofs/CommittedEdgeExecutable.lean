import EraSpec.Contracts.ChainTypeManager.Properties.CommittedEdgeExecutable
import EraSpec.Contracts.ChainTypeManager.Proofs.VersionRegistry

/-!
# Proofs: the commit-time edge checks imply the chain-side upgrade checks

Checked derivations of the statements in
`EraSpec.Contracts.ChainTypeManager.Properties.CommittedEdgeExecutable`.
-/

namespace Contracts.ChainTypeManager.EdgeChecks

/-! ## Packed versions -/

theorem majorOf_eq (v : ℕ) : majorOf v = v / 2 ^ 64 % 2 ^ 32 := by
  simp [majorOf, edgeUnpackSemVer, edgeToUint32, Nat.shiftRight_eq_div_pow]

theorem minorOf_eq (v : ℕ) : minorOf v = v / 2 ^ 32 % 2 ^ 32 := by
  simp [minorOf, edgeUnpackSemVer, edgeToUint32, Nat.shiftRight_eq_div_pow]

theorem unpackChecked_of_lt {v : ℕ} (h : v < 2 ^ 96) :
    unpackChecked v = some (majorOf v, minorOf v, edgeToUint32 v) := by
  rw [unpackChecked, ite_eq_left h]; rfl

theorem unpackChecked_of_not_lt {v : ℕ} (h : ¬ v < 2 ^ 96) : unpackChecked v = none := by
  rw [unpackChecked, ite_eq_right h]

/-- A well-formed version is one below `2^64`. -/
theorem versionWf_iff (v : ℕ) : VersionWf v ↔ v < 2 ^ 64 := by
  unfold VersionWf
  rw [majorOf_eq]
  constructor
  · rintro ⟨h1, h2⟩; omega
  · intro h; constructor <;> omega

theorem minorOf_of_wf {v : ℕ} (h : VersionWf v) : minorOf v = v / 2 ^ 32 := by
  rw [versionWf_iff] at h
  rw [minorOf_eq]; omega

/-- `L2CanonicalTransactionLib.sol:67-69`: the upgrade nonce is the minor version when the major
is zero. -/
theorem nonce_of_wf {v : ℕ} (h : VersionWf v) : protocolUpgradeNonce v = minorOf v := by
  rw [minorOf_of_wf h]; simp [protocolUpgradeNonce, Nat.shiftRight_eq_div_pow]

/-- The minor is monotone on well-formed versions (`BaseZkSyncUpgrade.sol:241-242`,
`VersionEdgeLib.sol:78-79`). -/
theorem minor_mono {v w : ℕ} (hv : VersionWf v) (hw : VersionWf w) (h : v ≤ w) :
    minorOf v ≤ minorOf w := by
  rw [minorOf_of_wf hv, minorOf_of_wf hw]; exact Nat.div_le_div_right h

/-- A version below a well-formed one is well formed. -/
theorem versionWf_of_le {v w : ℕ} (hw : VersionWf w) (h : v ≤ w) : VersionWf v := by
  rw [versionWf_iff] at hw ⊢; omega

/-- `_setNewProtocolVersion` in closed form. -/
theorem setNewProtocolVersion_eq (c : ChainUpgradeState) (newV : ℕ) (onSL : Bool) :
    setNewProtocolVersion c newV onSL =
      if EdgeVersionShape c.pv newV ∧
          ¬ (minorOf newV ≠ minorOf c.pv ∧ onSL = true ∧ (c.h ≠ 0 ∨ c.b ≠ 0)) then
        some (minorOf newV, decide (minorOf newV = minorOf c.pv), { c with pv := newV })
      else none := by
  unfold setNewProtocolVersion
  by_cases h1 : newV ≤ c.pv
  · rw [ite_eq_left h1, ite_eq_right (by rintro ⟨⟨h, _⟩, _⟩; omega)]
  rw [ite_eq_right h1]
  have hlt : c.pv < newV := by omega
  by_cases h2 : c.pv < 2 ^ 96
  swap
  · rw [unpackChecked_of_not_lt h2, ite_eq_right (by rintro ⟨⟨_, ⟨h, _⟩, _⟩, _⟩; exact h2 h)]
  by_cases h3 : newV < 2 ^ 96
  swap
  · rw [unpackChecked_of_lt h2, unpackChecked_of_not_lt h3,
      ite_eq_right (by rintro ⟨⟨_, _, ⟨h, _⟩, _⟩, _⟩; exact h3 h)]
  rw [unpackChecked_of_lt h2, unpackChecked_of_lt h3]
  simp only
  by_cases hA : majorOf c.pv = 0
  swap
  · rw [ite_eq_left hA, ite_eq_right (by rintro ⟨⟨_, ⟨_, h⟩, _⟩, _⟩; exact hA h)]
  by_cases hB : majorOf newV = 0
  swap
  · rw [ite_eq_right (not_not.mpr hA), ite_eq_left hB,
      ite_eq_right (by rintro ⟨⟨_, _, ⟨_, h⟩, _⟩, _⟩; exact hB h)]
  have hmono := minor_mono ⟨h2, hA⟩ ⟨h3, hB⟩ (Nat.le_of_lt hlt)
  have hC : ¬ minorOf newV < minorOf c.pv := by omega
  rw [ite_eq_right (not_not.mpr hA), ite_eq_right (not_not.mpr hB), ite_eq_right hC]
  by_cases hD : MAX_ALLOWED_MINOR_VERSION_DELTA < minorOf newV - minorOf c.pv
  · rw [ite_eq_left hD, ite_eq_right (by rintro ⟨⟨_, _, _, h⟩, _⟩; omega)]
  rw [ite_eq_right hD]
  have hS : EdgeVersionShape c.pv newV := ⟨hlt, ⟨h2, hA⟩, ⟨h3, hB⟩, by omega⟩
  have hsub : (minorOf newV - minorOf c.pv = 0) ↔ (minorOf newV = minorOf c.pv) := by omega
  simp only [hS, true_and, ne_eq, hsub]
  by_cases hP : ¬minorOf newV = minorOf c.pv ∧ onSL = true ∧ (¬c.h = 0 ∨ ¬c.b = 0)
  · rw [ite_eq_left hP, ite_eq_right (not_not.mpr hP)]
  · rw [ite_eq_right hP, ite_eq_left hP]

/-- `requireValidEdge` in closed form. -/
theorem requireValidEdge_eq (old new deadline ts : ℕ) (l2 : Bool) :
    requireValidEdge old new deadline ts l2 =
      if EdgeVersionShape old new ∧ deadline ≠ 0 ∧ ts ≤ deadline ∧
          ¬ (minorOf old = minorOf new ∧ l2 = true) then some () else none := by
  unfold requireValidEdge
  by_cases h1 : new ≤ old
  · rw [ite_eq_left h1, ite_eq_right (by rintro ⟨⟨h, _⟩, _⟩; omega)]
  rw [ite_eq_right h1]
  have hlt : old < new := by omega
  by_cases hd : deadline = 0
  · rw [ite_eq_left hd, ite_eq_right (by rintro ⟨_, h, _⟩; exact h hd)]
  rw [ite_eq_right hd]
  by_cases ht : deadline < ts
  · rw [ite_eq_left ht, ite_eq_right (by rintro ⟨_, _, h, _⟩; omega)]
  rw [ite_eq_right ht]
  by_cases h2 : old < 2 ^ 96
  swap
  · rw [unpackChecked_of_not_lt h2, ite_eq_right (by rintro ⟨⟨_, ⟨h, _⟩, _⟩, _⟩; exact h2 h)]
  by_cases h3 : new < 2 ^ 96
  swap
  · rw [unpackChecked_of_lt h2, unpackChecked_of_not_lt h3,
      ite_eq_right (by rintro ⟨⟨_, _, ⟨h, _⟩, _⟩, _⟩; exact h3 h)]
  rw [unpackChecked_of_lt h2, unpackChecked_of_lt h3]
  simp only
  by_cases hA : majorOf old = 0
  swap
  · rw [ite_eq_left hA, ite_eq_right (by rintro ⟨⟨_, ⟨_, h⟩, _⟩, _⟩; exact hA h)]
  by_cases hB : majorOf new = 0
  swap
  · rw [ite_eq_right (not_not.mpr hA), ite_eq_left hB,
      ite_eq_right (by rintro ⟨⟨_, _, ⟨_, h⟩, _⟩, _⟩; exact hB h)]
  have hmono := minor_mono ⟨h2, hA⟩ ⟨h3, hB⟩ (Nat.le_of_lt hlt)
  have hC : ¬ minorOf new < minorOf old := by omega
  rw [ite_eq_right (not_not.mpr hA), ite_eq_right (not_not.mpr hB), ite_eq_right hC]
  by_cases hD : MAX_ALLOWED_MINOR_VERSION_DELTA < minorOf new - minorOf old
  · rw [ite_eq_left hD, ite_eq_right (by rintro ⟨⟨_, _, _, h⟩, _⟩; omega)]
  rw [ite_eq_right hD]
  have hS : EdgeVersionShape old new := ⟨hlt, ⟨h2, hA⟩, ⟨h3, hB⟩, by omega⟩
  by_cases hP : minorOf old = minorOf new ∧ l2 = true
  · rw [ite_eq_left hP, ite_eq_right (by rintro ⟨_, _, _, h⟩; exact h hP)]
  · rw [ite_eq_right hP, ite_eq_left ⟨hS, hd, by omega, hP⟩]

theorem requireValidEdge_some_iff (old new deadline ts : ℕ) (l2 : Bool) :
    requireValidEdge old new deadline ts l2 = some () ↔
      EdgeVersionShape old new ∧ deadline ≠ 0 ∧ ts ≤ deadline ∧
        ¬ (minorOf old = minorOf new ∧ l2 = true) := by
  rw [requireValidEdge_eq]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun e => absurd e (by simp), fun e => absurd e h⟩

theorem setNewProtocolVersion_some_iff (c : ChainUpgradeState) (newV : ℕ) (onSL : Bool)
    (r : ℕ × Bool × ChainUpgradeState) :
    setNewProtocolVersion c newV onSL = some r ↔
      EdgeVersionShape c.pv newV ∧
        (minorOf newV ≠ minorOf c.pv → onSL = true → c.h = 0 ∧ c.b = 0) ∧
        r = (minorOf newV, decide (minorOf newV = minorOf c.pv), { c with pv := newV }) := by
  rw [setNewProtocolVersion_eq]
  split_ifs with h
  · obtain ⟨hS, hn⟩ := h
    constructor
    · intro e
      refine ⟨hS, ?_, (Option.some.inj e).symm⟩
      intro hne hSL
      by_contra hc
      exact hn ⟨hne, hSL, by omega⟩
    · rintro ⟨_, _, rfl⟩; rfl
  · constructor
    · intro e; exact absurd e (by simp)
    · rintro ⟨hS, himp, _⟩
      refine absurd ⟨hS, ?_⟩ h
      rintro ⟨hne, hSL, hhb⟩
      have := himp hne hSL
      omega

/-! ## The L2 plan and the composer -/

/-- What a successful `build` guarantees about its plan: at most `MAX_NEW_FACTORY_DEPS`
factory dependencies, no delegate when nothing is deployed, and the factory-dependency list of
its own deployments. -/
theorem planBuild_facts {E : PlanEnv} {derived : List Deployment} {a : AuthoredL2Plan}
    {plan : L2UpgradePlan} (h : planBuild E derived a = some plan) :
    plan.factoryDepHashes.length ≤ MAX_NEW_FACTORY_DEPS ∧
      (plan.deployments = [] → plan.delegateTo = 0) ∧
      E.factoryDepHashes plan.deployments = some plan.factoryDepHashes := by
  unfold planBuild at h
  simp only at h
  split at h
  · rename_i del extras hdel hextras
    split at h
    · rename_i fdh hfdh
      split_ifs at h with h1 h2 h3 h4
      · -- with a delegate
        cases h
        simp only at hdel h3 hfdh ⊢
        refine ⟨by omega, ?_, hfdh⟩
        intro hnil
        exfalso
        simp only [h4, ↓reduceIte] at hdel
        cases hu : unsafeDeployment E a.delegateBytecodeInfo with
        | none => rw [hu] at hdel; simp at hdel
        | some d =>
          rw [hu] at hdel
          simp only [Option.map_some, Option.some.injEq] at hdel
          subst hdel
          simp at hnil
      · -- without a delegate
        cases h
        simp only at h3 hfdh ⊢
        exact ⟨by omega, fun _ => trivial, hfdh⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The composer's emptiness test is `deployments = []` on built plans. -/
theorem composed_empty_iff {E : PlanEnv} {derived : List Deployment} {a : AuthoredL2Plan}
    {plan : L2UpgradePlan} (h : planBuild E derived a = some plan) (v : ℕ) (dc : Bytes) :
    (buildL2UpgradeTxFromPlan E plan v dc = emptyL2CanonicalTransaction ↔ plan.deployments = []) ∧
    ((buildL2UpgradeTxFromPlan E plan v dc).txType = 0 ↔ plan.deployments = []) := by
  obtain ⟨_, hdel, _⟩ := planBuild_facts h
  unfold buildL2UpgradeTxFromPlan
  by_cases hd : plan.deployments = []
  · have h0 := hdel hd
    simp [hd, h0, emptyL2CanonicalTransaction]
  · have hlen : plan.deployments.length ≠ 0 := by simpa using hd
    simp only [hlen, false_and, ↓reduceIte, hd, iff_false]
    constructor
    · intro he
      have := congrArg L2Tx.txType he
      simp [upgradeTransaction, emptyL2CanonicalTransaction, ZKSYNC_OS_SYSTEM_UPGRADE_L2_TX_TYPE] at this
    · simp [upgradeTransaction, ZKSYNC_OS_SYSTEM_UPGRADE_L2_TX_TYPE]

/-- The composed transaction of a plan that deploys something. -/
theorem composed_of_ne_nil (E : PlanEnv) (plan : L2UpgradePlan) (v : ℕ) (dc : Bytes)
    (hd : plan.deployments ≠ []) :
    buildL2UpgradeTxFromPlan E plan v dc =
      { upgradeTransaction v (E.encodeUpgradeCall plan.deployments plan.delegateTo
          (if plan.delegateComposer = 0 then [] else dc)) with
        factoryDeps := plan.factoryDepHashes } := by
  have hlen : plan.deployments.length ≠ 0 := by simpa using hd
  simp only [buildL2UpgradeTxFromPlan, hlen, false_and, ↓reduceIte]

/-- The composed transaction of a plan that deploys nothing and has no delegate. -/
theorem composed_of_nil (E : PlanEnv) (plan : L2UpgradePlan) (v : ℕ) (dc : Bytes)
    (hd : plan.deployments = []) (h0 : plan.delegateTo = 0) :
    buildL2UpgradeTxFromPlan E plan v dc = emptyL2CanonicalTransaction := by
  simp [buildL2UpgradeTxFromPlan, hd, h0]

/-- The upgrade envelope with any calldata and factory dependencies passes
`validateUpgradeTransaction`. -/
theorem validateUpgrade_upgradeTransaction (v : ℕ) (calldata : Bytes) (fdh : List ℕ) :
    validateUpgradeTransaction { upgradeTransaction v calldata with factoryDeps := fdh } = true := by
  simp [validateUpgradeTransaction, upgradeTransaction, emptyL2CanonicalTransaction,
    L2_FORCE_DEPLOYER_ADDR, L2_COMPLEX_UPGRADER_ADDR]

/-- `getMinimalPriorityTransactionGasLimit` at `REQUIRED_L2_GAS_PRICE_PER_PUBDATA`: the native
part is `351 * 800 + ceilDiv(2^35, 10^8) = 281_144`. -/
theorem minimalGas_upgrade (len : ℕ) :
    minimalPriorityTxGasLimit len REQUIRED_L2_GAS_PRICE_PER_PUBDATA =
      if 2 ^ 256 ≤ L1_TX_INTRINSIC_L2_GAS_ZKSYNC_OS + L1_TX_CALLDATA_FLOOR_PRICE_L2_GAS_ZKSYNC_OS * len
      then none
      else some (max (L1_TX_INTRINSIC_L2_GAS_ZKSYNC_OS + L1_TX_CALLDATA_FLOOR_PRICE_L2_GAS_ZKSYNC_OS * len)
        281144) := by
  unfold minimalPriorityTxGasLimit
  have e1 : L1_TX_INTRINSIC_L2_GAS_ZKSYNC_OS = 21000 := rfl
  have e2 : L1_TX_CALLDATA_FLOOR_PRICE_L2_GAS_ZKSYNC_OS = 40 := rfl
  have e3 : L1_TX_INTRINSIC_PUBDATA_ZKSYNC_OS * REQUIRED_L2_GAS_PRICE_PER_PUBDATA = 280800 := rfl
  have e4 : ceilDiv MAX_NATIVE_COMPUTATIONAL_ZKSYNC_OS L1_TX_NATIVE_PER_GAS = 344 := by decide
  simp only [e3, e4]
  by_cases h : 2 ^ 256 ≤ L1_TX_INTRINSIC_L2_GAS_ZKSYNC_OS + L1_TX_CALLDATA_FLOOR_PRICE_L2_GAS_ZKSYNC_OS * len
  · rw [ite_eq_left (Or.inr (Or.inl h)), ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right (by rintro (h1|h1|h1|h1) <;> omega)]

/-- The upgrade envelope passes `validateL1ToL2Transaction` exactly under the two premises. -/
theorem validateL1ToL2_upgradeTransaction (maxPubdata v : ℕ) (calldata : Bytes) (fdh : List ℕ) :
    validateL1ToL2Transaction { upgradeTransaction v calldata with factoryDeps := fdh }
        UPGRADE_TX_MAX_GAS_LIMIT maxPubdata = true ↔
      UPGRADE_TX_MAX_GAS_LIMIT / REQUIRED_L2_GAS_PRICE_PER_PUBDATA ≤ maxPubdata ∧
      L1_TX_INTRINSIC_L2_GAS_ZKSYNC_OS + L1_TX_CALLDATA_FLOOR_PRICE_L2_GAS_ZKSYNC_OS * calldata.length ≤
        UPGRADE_TX_MAX_GAS_LIMIT := by
  have e1 : L1_TX_INTRINSIC_L2_GAS_ZKSYNC_OS = 21000 := rfl
  have e2 : L1_TX_CALLDATA_FLOOR_PRICE_L2_GAS_ZKSYNC_OS = 40 := rfl
  have e5 : UPGRADE_TX_MAX_GAS_LIMIT = 72000000 := rfl
  have e6 : REQUIRED_L2_GAS_PRICE_PER_PUBDATA = 800 := rfl
  unfold validateL1ToL2Transaction
  simp only [upgradeTransaction]
  rw [minimalGas_upgrade]
  by_cases hl : L1_TX_INTRINSIC_L2_GAS_ZKSYNC_OS + L1_TX_CALLDATA_FLOOR_PRICE_L2_GAS_ZKSYNC_OS * calldata.length ≤
      UPGRADE_TX_MAX_GAS_LIMIT
  · have hnb : ¬ (2 ^ 256 ≤ L1_TX_INTRINSIC_L2_GAS_ZKSYNC_OS +
        L1_TX_CALLDATA_FLOOR_PRICE_L2_GAS_ZKSYNC_OS * calldata.length) := by omega
    rw [ite_eq_right hnb]
    have hm : max (L1_TX_INTRINSIC_L2_GAS_ZKSYNC_OS +
        L1_TX_CALLDATA_FLOOR_PRICE_L2_GAS_ZKSYNC_OS * calldata.length) 281144 ≤ UPGRADE_TX_MAX_GAS_LIMIT := by
      rw [e5]; omega
    have hg : REQUIRED_L2_GAS_PRICE_PER_PUBDATA ≠ 0 := by rw [e6]; decide
    simp only [le_refl, decide_true, hg, ne_eq, not_false_eq_true, Bool.true_and, hm, hl, and_true,
      Bool.and_true]
    exact decide_eq_true_iff
  · simp only [hl, and_false, iff_false]
    split_ifs with hb
    · simp
    · intro h
      simp only [Bool.and_eq_true] at h
      exact hl (le_trans (le_max_left _ _) (of_decide_eq_true h.2))

/-- The composed transaction passes `_setL2SystemContractUpgrade` on a non-patch edge. -/
theorem setL2_upgradeTransaction (H : L2Tx → ℕ) (c : ChainUpgradeState) (maxPubdata v : ℕ)
    (calldata : Bytes) (fdh : List ℕ) (hwf : VersionWf v)
    (hpub : UPGRADE_TX_MAX_GAS_LIMIT / REQUIRED_L2_GAS_PRICE_PER_PUBDATA ≤ maxPubdata)
    (hlen : L1_TX_INTRINSIC_L2_GAS_ZKSYNC_OS + L1_TX_CALLDATA_FLOOR_PRICE_L2_GAS_ZKSYNC_OS * calldata.length ≤
      UPGRADE_TX_MAX_GAS_LIMIT)
    (hfd : fdh.length ≤ MAX_NEW_FACTORY_DEPS) :
    setL2SystemContractUpgrade H c maxPubdata { upgradeTransaction v calldata with factoryDeps := fdh }
        (minorOf v) false =
      some (H { upgradeTransaction v calldata with factoryDeps := fdh },
        { c with h := H { upgradeTransaction v calldata with factoryDeps := fdh } }) := by
  have hnonce := nonce_of_wf hwf
  have hval := (validateL1ToL2_upgradeTransaction maxPubdata v calldata fdh).mpr ⟨hpub, hlen⟩
  have hvu := validateUpgrade_upgradeTransaction v calldata fdh
  unfold setL2SystemContractUpgrade
  rw [hval, hvu]
  simp only [upgradeTransaction, ZKSYNC_OS_SYSTEM_UPGRADE_L2_TX_TYPE, hnonce] at *
  have hfd' : ¬ MAX_NEW_FACTORY_DEPS < fdh.length := by omega
  simp only [hfd', ↓reduceIte, ne_eq, not_true_eq_false, Bool.false_eq_true, OfNat.ofNat_ne_zero]
  rfl

/-- The storage part on the settlement layer is the version step followed by the L2 step. -/
theorem upgradeStoragePart_onSL (H : L2Tx → ℕ) (c : ChainUpgradeState) (maxPubdata newV : ℕ)
    (tx : L2Tx) :
    upgradeStoragePart H c maxPubdata newV tx true =
      (setNewProtocolVersion c newV true).bind
        (fun r => setL2SystemContractUpgrade H r.2.2 maxPubdata tx r.1 r.2.1) := by
  unfold upgradeStoragePart
  cases setNewProtocolVersion c newV true <;> rfl

/-- An upgrade-type transaction that `validateL1ToL2Transaction` refuses reverts the L2 step. -/
theorem setL2_of_invalid (H : L2Tx → ℕ) (c : ChainUpgradeState) (maxPubdata : ℕ) (tx : L2Tx)
    (m : ℕ) (hty : tx.txType = ZKSYNC_OS_SYSTEM_UPGRADE_L2_TX_TYPE)
    (hv : validateL1ToL2Transaction tx UPGRADE_TX_MAX_GAS_LIMIT maxPubdata = false) :
    setL2SystemContractUpgrade H c maxPubdata tx m false = none := by
  unfold setL2SystemContractUpgrade
  rw [hty, hv]
  simp only [ZKSYNC_OS_SYSTEM_UPGRADE_L2_TX_TYPE, OfNat.ofNat_ne_zero, ↓reduceIte, ne_eq,
    not_true_eq_false, Bool.false_eq_true]

/-! ## The two copies agree -/

theorem EdgeShapeIsTheChainVersionCheck : Properties.EdgeShapeIsTheChainVersionCheck :=
  ⟨requireValidEdge_some_iff, setNewProtocolVersion_some_iff⟩

theorem ComposerEmptinessIsHasL2Side : Properties.ComposerEmptinessIsHasL2Side := by
  intro E derived a plan v composed h
  obtain ⟨h1, h2⟩ := composed_empty_iff h v composed
  exact ⟨h1, h2, (planBuild_facts h).2.1⟩

theorem ConstructedEdgeChainFacts : Properties.ConstructedEdgeChainFacts := by
  intro E o plan composed ⟨hb, he⟩
  obtain ⟨hS, _, _, hpatch⟩ := (requireValidEdge_some_iff _ _ _ _ _).mp he
  obtain ⟨hfd, _, _⟩ := planBuild_facts hb
  obtain ⟨hE1, hE2⟩ := composed_empty_iff hb o.new composed
  refine ⟨hS, hE2, hE1, fun hd => ?_⟩
  have hlen : plan.deployments.length ≠ 0 := by simpa using hd
  have hne : minorOf o.new ≠ minorOf o.old := by
    intro heq; exact hpatch ⟨heq.symm, by simp [hlen]⟩
  unfold composedTx
  rw [composed_of_ne_nil E plan o.new composed hd]
  refine ⟨hne, rfl, nonce_of_wf hS.2.2.1, rfl, hfd,
    validateUpgrade_upgradeTransaction _ _ _, rfl, rfl⟩

/-! ## Headline -/

theorem ConstructedEdgePassesChainChecks : Properties.ConstructedEdgePassesChainChecks := by
  intro E o plan c maxPubdata composed ⟨hb, he⟩ hpv hclean hpub hfit
  obtain ⟨hS, _, _, hpatch⟩ := (requireValidEdge_some_iff _ _ _ _ _).mp he
  obtain ⟨hfd, hdel, _⟩ := planBuild_facts hb
  have hV : setNewProtocolVersion c o.new true =
      some (minorOf o.new, decide (minorOf o.new = minorOf o.old), { c with pv := o.new }) := by
    rw [setNewProtocolVersion_some_iff]
    rw [hpv]
    exact ⟨hS, fun hne _ => hclean hne, rfl⟩
  have hL : setL2SystemContractUpgrade E.txHash { c with pv := o.new } maxPubdata
      (composedTx E o plan composed) (minorOf o.new) (decide (minorOf o.new = minorOf o.old)) =
      some (if plan.deployments = [] then (0, { c with pv := o.new })
            else (E.txHash (composedTx E o plan composed),
              { c with pv := o.new, h := E.txHash (composedTx E o plan composed) })) := by
    by_cases hd : plan.deployments = []
    · rw [ite_eq_left hd]
      unfold composedTx
      rw [composed_of_nil E plan o.new composed hd (hdel hd)]
      simp [setL2SystemContractUpgrade, emptyL2CanonicalTransaction]
    · rw [ite_eq_right hd]
      have hlen : plan.deployments.length ≠ 0 := by simpa using hd
      have hne : minorOf o.new ≠ minorOf o.old := by
        intro heq; exact hpatch ⟨heq.symm, by simp [hlen]⟩
      have hdec : decide (minorOf o.new = minorOf o.old) = false := by simp [hne]
      rw [hdec]
      unfold composedTx at hfit ⊢
      rw [composed_of_ne_nil E plan o.new composed hd] at hfit ⊢
      exact setL2_upgradeTransaction E.txHash _ maxPubdata o.new _ _ hS.2.2.1 hpub hfit hfd
  refine ⟨hV, hL, ?_⟩
  unfold upgradeStoragePart
  rw [hV]
  exact hL

theorem ConstructedEdgePassesOffLayerVersionStep :
    Properties.ConstructedEdgePassesOffLayerVersionStep := by
  intro E o plan c maxPubdata tx ⟨_, he⟩ hpv
  obtain ⟨hS, _, _, _⟩ := (requireValidEdge_some_iff _ _ _ _ _).mp he
  have hV : setNewProtocolVersion c o.new false =
      some (minorOf o.new, decide (minorOf o.new = minorOf o.old), { c with pv := o.new }) := by
    rw [setNewProtocolVersion_some_iff, hpv]
    exact ⟨hS, fun _ h => absurd h (by simp), rfl⟩
  refine ⟨hV, ?_⟩
  unfold upgradeStoragePart
  rw [hV]
  rfl

theorem CommittedSlotEdgePassesChainChecks : Properties.CommittedSlotEdgePassesChainChecks := by
  intro W E EW s s' ops hI hold hgen hrun v hv hC hrep c maxPubdata composed hpv hclean hpub hfit
  have hslot := SlotsDepartFromTheirVersion W s s' ops hI hold hgen hrun v hv
  obtain ⟨hrold, hrnew⟩ := hrep
  have hpv' : c.pv = (EW.obj (s'.ut v)).old := by rw [hpv, ← hrold, hslot]
  have hclean' : minorOf (EW.obj (s'.ut v)).new ≠ minorOf (EW.obj (s'.ut v)).old →
      c.h = 0 ∧ c.b = 0 := by
    rw [← hrnew, ← hrold, hslot]; exact hclean
  obtain ⟨_, _, hU⟩ :=
    ConstructedEdgePassesChainChecks E _ _ c maxPubdata composed hC hpv' hclean' hpub hfit
  rw [hrnew]
  split_ifs at hU with hd
  · exact ⟨_, _, hU, rfl⟩
  · exact ⟨_, _, hU, rfl⟩

theorem PublishedFactoryDepsStayPublished : Properties.PublishedFactoryDepsStayPublished := by
  intro s s' ops hashes hpub hrun hops
  induction hrun with
  | nil => exact hpub
  | @cons s s1 s2 op ops hs _ ih =>
    apply ih _ (fun op' hm => hops op' (List.mem_cons_of_mem _ hm))
    cases hs with
    | @publish hash blk hblk hfresh =>
      intro x hx
      by_cases hxe : x = hash
      · subst hxe; simp [upd, hblk]
      · simp only [upd, hxe, ↓reduceIte]; exact hpub x hx
    | implementationSwap => exact absurd (hops _ List.mem_cons_self) (by simp [SupplierOp.IsPublish])

/-! ## The premises are needed -/

theorem PubdataLimitThresholdIsExact : Properties.PubdataLimitThresholdIsExact := by
  refine ⟨by unfold Constructed; decide, by unfold UpgradeCalldataFits; decide, by decide,
    ⟨(31, ⟨v30, 31, 0⟩), by decide⟩⟩

/-- `wEdge` passes on the clean chain at `0.29.0` for any composer answer that fits. -/
theorem wEdge_passes (maxPubdata : ℕ) (composed : Bytes) (hpub : 90000 ≤ maxPubdata)
    (hfit : UpgradeCalldataFits (composedTx wEnv wEdge wPlan composed)) :
    ∃ r, upgradeStoragePart wEnv.txHash ⟨v29, 0, 0⟩ maxPubdata v30
      (composedTx wEnv wEdge wPlan composed) true = some r :=
  ⟨_, (ConstructedEdgePassesChainChecks wEnv wEdge wPlan ⟨v29, 0, 0⟩ maxPubdata composed
    (by unfold Constructed; decide) rfl (fun _ => ⟨rfl, rfl⟩) hpub hfit).2.2⟩

/-- The composed calldata of `wEdge` is 100 bytes plus the composer's answer. -/
theorem wEdge_data (composed : Bytes) :
    (composedTx wEnv wEdge wPlan composed).data = List.replicate 100 0 ++ composed := by
  show (buildL2UpgradeTxFromPlan wEnv wPlan v30 composed).data = _
  rw [composed_of_ne_nil wEnv wPlan v30 composed (by decide)]
  simp [upgradeTransaction, wEnv, wPlan]

/-- The composed transaction of `wEdge` has the upgrade type. -/
theorem wEdge_txType (composed : Bytes) :
    (composedTx wEnv wEdge wPlan composed).txType = ZKSYNC_OS_SYSTEM_UPGRADE_L2_TX_TYPE := by
  show (buildL2UpgradeTxFromPlan wEnv wPlan v30 composed).txType = _
  rw [composed_of_ne_nil wEnv wPlan v30 composed (by decide)]
  rfl

/-- `wEdge`'s composed transaction fits exactly when the composer's answer has at most
`1_799_375` bytes. -/
theorem wEdge_fits_iff (composed : Bytes) :
    UpgradeCalldataFits (composedTx wEnv wEdge wPlan composed) ↔ composed.length ≤ 1799375 := by
  unfold UpgradeCalldataFits
  rw [wEdge_data]
  have e1 : L1_TX_INTRINSIC_L2_GAS_ZKSYNC_OS = 21000 := rfl
  have e2 : L1_TX_CALLDATA_FLOOR_PRICE_L2_GAS_ZKSYNC_OS = 40 := rfl
  have e5 : UPGRADE_TX_MAX_GAS_LIMIT = 72000000 := rfl
  rw [List.length_append, List.length_replicate, e1, e2, e5]
  omega

/-- On the clean chain at `0.29.0`, `wEdge` reverts for a composer answer that does not fit. -/
theorem wEdge_reverts_of_not_fits (composed : Bytes)
    (h : ¬ UpgradeCalldataFits (composedTx wEnv wEdge wPlan composed)) :
    upgradeStoragePart wEnv.txHash ⟨v29, 0, 0⟩ 99000 v30 (composedTx wEnv wEdge wPlan composed) true =
      none := by
  have hV : setNewProtocolVersion ⟨v29, 0, 0⟩ v30 true = some (30, false, ⟨v30, 0, 0⟩) := by decide
  have hval : validateL1ToL2Transaction (composedTx wEnv wEdge wPlan composed)
      UPGRADE_TX_MAX_GAS_LIMIT 99000 = false := by
    rw [Bool.eq_false_iff]
    intro hv
    apply h
    revert hv
    show validateL1ToL2Transaction (buildL2UpgradeTxFromPlan wEnv wPlan v30 composed)
        UPGRADE_TX_MAX_GAS_LIMIT 99000 = true →
      UpgradeCalldataFits (buildL2UpgradeTxFromPlan wEnv wPlan v30 composed)
    rw [composed_of_ne_nil wEnv wPlan v30 _ (by decide)]
    intro hv
    exact ((validateL1ToL2_upgradeTransaction 99000 v30 _ _).mp hv).2
  rw [upgradeStoragePart_onSL, hV, Option.bind_some]
  exact setL2_of_invalid _ _ _ _ _ (wEdge_txType _) hval

theorem CalldataBoundIsExact : Properties.CalldataBoundIsExact := by
  have hfit : UpgradeCalldataFits (composedTx wEnv wEdge wPlan (List.replicate 1799375 0)) := by
    rw [wEdge_fits_iff, List.length_replicate]
  have hnofit : ¬ UpgradeCalldataFits (composedTx wEnv wEdge wPlan (List.replicate 1799376 0)) := by
    rw [wEdge_fits_iff, List.length_replicate]
    omega
  exact ⟨by unfold Constructed; decide, hfit, wEdge_passes 99000 _ (by norm_num) hfit, hnofit,
    wEdge_reverts_of_not_fits _ hnofit⟩

/-- On any chain at `0.29.0`, the storage part of `_upgrade` towards `0.130.0` reverts. -/
theorem farEdge_reverts (c : ChainUpgradeState) (maxPubdata : ℕ) (tx : L2Tx) (onSL : Bool)
    (hpv : c.pv = v29) : upgradeStoragePart wEnv.txHash c maxPubdata v130 tx onSL = none := by
  have hshape : ¬ EdgeVersionShape v29 v130 := by decide
  have hV : setNewProtocolVersion c v130 onSL = none := by
    rw [setNewProtocolVersion_eq, hpv]
    exact ite_eq_right (fun h => hshape h.1)
  unfold upgradeStoragePart
  rw [hV]

theorem NonGenuineSlotEdgeRevertsOnChain : Properties.NonGenuineSlotEdgeRevertsOnChain := by
  refine ⟨_, CRun.cons (CStep.commit ?_ ?_ ?_ ?_ ?_ ?_)
    (CRun.cons (CStep.commit ?_ ?_ ?_ ?_ ?_ ?_)
      (CRun.cons (CStep.replace ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) CRun.nil)),
    by decide, by unfold Constructed; decide, ⟨by decide, by decide⟩, by decide,
    fun c maxPubdata tx onSL hpv => farEdge_reverts c maxPubdata tx onSL hpv⟩
  all_goals decide

theorem UnbuiltPlanBreaksEmptinessAgreement : Properties.UnbuiltPlanBreaksEmptinessAgreement := by
  refine ⟨fun E derived a h => ?_, by decide, by decide, by decide⟩
  have := (planBuild_facts h).2.1 rfl
  exact absurd this (by decide)

theorem SupplierSwapClearsPublication : Properties.SupplierSwapClearsPublication := by
  refine ⟨⟨fun _ => 1⟩, ⟨fun _ => 0⟩, ?_, by decide,
    SupplierRun.cons SupplierStep.implementationSwap SupplierRun.nil, ?_⟩
  · intro x _; simp
  · intro h; exact h 7 (by decide) rfl

/-! ## Witnesses -/

theorem ConstructedEdgeWitness : Properties.ConstructedEdgeWitness := by
  refine ⟨by unfold Constructed; decide, by decide, by decide, by unfold UpgradeCalldataFits; decide,
    by decide, by decide, by decide, by unfold Constructed; decide, by decide, by decide⟩

theorem CommittedSlotWitness : Properties.CommittedSlotWitness := by
  refine ⟨_, CRun.cons (CStep.commit ?_ ?_ ?_ ?_ ?_ ?_)
      (CRun.cons (CStep.replace ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) CRun.nil),
    InitSatisfiesInvariant _ _ (by decide), by decide, by decide, by unfold Constructed; decide,
    ⟨by decide, by decide⟩, by unfold UpgradeCalldataFits; decide, 31, ⟨v30, 31, 0⟩, by decide, rfl⟩
  all_goals decide

theorem CommittedSlotWitnessMeetsHeadline : Properties.CommittedSlotWitnessMeetsHeadline := by
  obtain ⟨s', hrun, hinv, hgen, hslot, hcon, hrep, hfit, -⟩ := CommittedSlotWitness
  have hpre : ∀ v, (initState wEdgeWorld 100).ut v ≠ 0 →
      (wEdgeWorld.tr ((initState wEdgeWorld 100).ut v)).old = v :=
    fun _ h => absurd rfl h
  have hops : ∀ e r, Op.replace e r ∈ ([.commit 300, .replace 300 400] : List Op) →
      (wEdgeWorld.tr r).old = wEdgeWorld.relVersion (wEdgeWorld.tr r).fromRel := by
    intro e r hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h
    · cases h
    · cases h
      exact hgen
  refine ⟨hpre, hops, s', hrun, hslot, ?_⟩
  have h := CommittedSlotEdgePassesChainChecks wEdgeWorld wEnv wEdgeObjs _ s' _ hinv hpre hops
    hrun v29 (by rw [hslot]; decide) (by rw [hslot]; exact hcon) (by rw [hslot]; exact hrep)
    ⟨v29, 0, 0⟩ 99000 [1, 2, 3] rfl (fun _ => ⟨rfl, rfl⟩) (by decide) (by rw [hslot]; exact hfit)
  rw [hslot] at h
  exact h

theorem SupplierWitness : Properties.SupplierWitness := by
  refine ⟨⟨fun x => if x = 7 ∨ x = 8 then 3 else 0⟩, _, ?_,
    SupplierRun.cons (SupplierStep.publish (by decide) (by decide))
      (SupplierRun.cons (SupplierStep.publish (by decide) (by decide)) SupplierRun.nil),
    fun op hop => ?_, ?_, ?_⟩
  · intro x hx
    simp only [wPlan, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl <;> trivial
  · intro x hx
    simp only [wPlan, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> decide
  · decide

theorem RequireValidEdgeIsL2TablesValidEdge : Properties.RequireValidEdgeIsL2TablesValidEdge := by
  intro old new deadline upgradeTs hasL2Side
  rw [EdgeShapeIsTheChainVersionCheck.1]
  simp only [EdgeVersionShape, VersionWf, majorOf, minorOf, edgeUnpackSemVer, edgeToUint32,
    L2Tables.ValidEdge, L2Tables.majorOf, L2Tables.minorOf, Nat.shiftRight_eq_div_pow,
    MAX_ALLOWED_MINOR_VERSION_DELTA]
  tauto

end Contracts.ChainTypeManager.EdgeChecks
