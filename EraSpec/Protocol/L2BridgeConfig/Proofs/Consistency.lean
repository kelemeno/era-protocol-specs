import EraSpec.Protocol.L2BridgeConfig.Properties.Consistency

/-!
# Proofs: the L2 bridge configuration words stay consistent

Each entry point gets a characterization: it succeeds exactly under its checks, and then the
state is an explicit update of the old one (`…_eq_some`).  The two upgrade programs are chained
from those: from all-zero storage a successful genesis leaves `genesisPost`
(`genesis_fresh_eq_some`), and from a state with a nonzero WETH a successful default upgrade
leaves `defaultPost` (`defaultUpgrade_with_eq_some`).  The invariant proofs are then case
splits on the call.  The one place the vault's freezes enter is `default_ids`: the stored
`L1_CHAIN_ID` and `BASE_TOKEN_ASSET_ID` are nonzero, so the freezes force the upgrade's ids to
equal them.

The witnesses use the deployed addresses and a toy asset-id encoding (chain plus sender plus
data); the run of `ConfigRunWitness` is built with `ConfigRun.snoc` and each step is checked by
evaluation (`rfl`).
-/

namespace Contracts.L2BridgeConfig

open Contracts.AssetRouter (Chain AssetId Address AssetData upd setHandler writtenId senderOf)

/-! ## Map updates -/

lemma cfg_upd_self (f : UInt256 → UInt256) (a v : UInt256) : upd f a v a = v := by
  simp [upd]

lemma cfg_upd_of_ne (f : UInt256 → UInt256) {x a : UInt256} (v : UInt256) (h : x ≠ a) :
    upd f a v x = f x := by
  simp [upd, h]

/-! ## One entry point at a time -/

lemma messageRootUpdateL2_eq_some {E : ConfigEnv} {s : Address} {l1 : Chain}
    {w w' : ConfigWorld} :
    messageRootUpdateL2 E s l1 w = some w' ↔
      s = E.upgrader ∧ w' = { w with messageRoot := { w.messageRoot with l1 := l1 } } := by
  unfold messageRootUpdateL2
  by_cases h : s = E.upgrader <;> simp [h, eq_comm]

lemma messageRootInitL2_eq_some {E : ConfigEnv} {s : Address} {l1 : Chain}
    {w w' : ConfigWorld} :
    messageRootInitL2 E s l1 w = some w' ↔
      w.messageRoot.locked = false ∧ s = E.upgrader ∧
        w' = { w with messageRoot := ⟨l1, true⟩ } := by
  unfold messageRootInitL2 messageRootUpdateL2
  by_cases h1 : w.messageRoot.locked = true <;> by_cases h2 : s = E.upgrader <;>
    simp [h1, h2, eq_comm]

lemma bridgehubUpdateL2_eq_some {E : ConfigEnv} {s : Address} {l1 : Chain}
    {w w' : ConfigWorld} :
    bridgehubUpdateL2 E s l1 w = some w' ↔
      s = E.upgrader ∧ w' = { w with bridgehub :=
        { w.bridgehub with l1 := l1, eth := E.encNTV l1 E.ethToken } } := by
  unfold bridgehubUpdateL2
  by_cases h : s = E.upgrader <;> simp [h, eq_comm]

lemma bridgehubInitL2_eq_some {E : ConfigEnv} {s : Address} {l1 : Chain}
    {w w' : ConfigWorld} :
    bridgehubInitL2 E s l1 w = some w' ↔
      w.bridgehub.locked = false ∧ s = E.upgrader ∧
        w' = { w with bridgehub := ⟨l1, E.encNTV l1 E.ethToken, true⟩ } := by
  unfold bridgehubInitL2 bridgehubUpdateL2
  by_cases h1 : w.bridgehub.locked = true <;> by_cases h2 : s = E.upgrader <;>
    simp [h1, h2, eq_comm]

lemma routerUpdateL2_eq_some {E : ConfigEnv} {s : Address} {l1 : Chain} {r : Address}
    {a : AssetId} {w w' : ConfigWorld} :
    routerUpdateL2 E s l1 r a w = some w' ↔
      s = E.upgrader ∧ r ≠ 0 ∧
        w' = { w with router := { w.router with l1 := l1, l1AssetRouter := r, base := a } } := by
  unfold routerUpdateL2
  by_cases h : s = E.upgrader <;> by_cases h2 : r = 0 <;> simp [h, h2, eq_comm]

lemma routerInitL2_eq_some {E : ConfigEnv} {s : Address} {l1 : Chain} {r : Address}
    {a : AssetId} {w w' : ConfigWorld} :
    routerInitL2 E s l1 r a w = some w' ↔
      w.router.locked = false ∧ s = E.upgrader ∧ r ≠ 0 ∧
        w' = { w with router := ⟨l1, r, a,
          { w.router.routes with handler := upd w.router.routes.handler a E.ntvAddr }, true⟩ } := by
  unfold routerInitL2 routerUpdateL2 ConfigWorld.pointRoute
  by_cases h1 : w.router.locked = true <;> by_cases h2 : s = E.upgrader <;> by_cases h3 : r = 0 <;>
    simp [h1, h2, h3, eq_comm]

lemma vaultUpdateL2With_eq_some {F : VaultFreezes} {E : ConfigEnv} {s : Address} {l1 : Chain}
    {weth : Address} {b : BaseTokenData} {w w' : ConfigWorld} :
    vaultUpdateL2With F E s l1 weth b w = some w' ↔
      (s = E.upgrader ∧ weth ≠ 0 ∧ (w.vault.weth = 0 ∨ w.vault.weth = weth)
        ∧ (F.l1 = true → w.vault.l1 = 0 ∨ w.vault.l1 = l1)
        ∧ (F.base = true → w.vault.base = 0 ∨ w.vault.base = b.assetId)) ∧
      w' = { w with vault := { w.vault with
        weth := weth, base := b.assetId, l1 := l1, baseOriginToken := b.originToken
        tokenAddress := upd w.vault.tokenAddress b.assetId E.baseTokenAddr
        assetIdOf := upd w.vault.assetIdOf E.baseTokenAddr b.assetId
        originChainId := upd w.vault.originChainId b.assetId b.originChainId } } := by
  unfold vaultUpdateL2With
  split_ifs with h
  · simp only [Option.some.injEq]
    exact ⟨fun h' => ⟨h, h'.symm⟩, fun h' => h'.2.symm⟩
  · simp only [false_iff]
    exact fun h' => h h'.1

lemma vaultInitL2_eq_some {E : ConfigEnv} {s : Address} {l1 : Chain} {beacon weth : Address}
    {b : BaseTokenData} {w w' : ConfigWorld} :
    vaultInitL2 E s l1 beacon weth b w = some w' ↔
      w.vault.locked = false ∧ s = E.upgrader ∧ weth ≠ 0 ∧ (w.vault.weth = 0 ∨ w.vault.weth = weth)
        ∧ (w.vault.l1 = 0 ∨ w.vault.l1 = l1)
        ∧ (w.vault.base = 0 ∨ w.vault.base = b.assetId) ∧ beacon ≠ 0 ∧
      w' = { w with vault := { w.vault with
        weth := weth, base := b.assetId, l1 := l1, baseOriginToken := b.originToken
        beacon := beacon
        tokenAddress := upd w.vault.tokenAddress b.assetId E.baseTokenAddr
        assetIdOf := upd w.vault.assetIdOf E.baseTokenAddr b.assetId
        originChainId := upd w.vault.originChainId b.assetId b.originChainId
        locked := true } } := by
  unfold vaultInitL2 vaultUpdateL2
  cases hlk : w.vault.locked
  · simp only [Bool.false_eq_true, ite_false, Option.bind_eq_some_iff,
      vaultUpdateL2With_eq_some, deployedFreezes, true_and]
    constructor
    · rintro ⟨w1, ⟨⟨hs, hw, hww, hl, hb⟩, rfl⟩, h⟩
      by_cases hbe : beacon = 0
      · simp [hbe] at h
      · simp only [hbe, ne_eq, not_false_eq_true, ite_true, Option.some.injEq] at h
        exact ⟨hs, hw, hww, by simpa using hl, by simpa using hb, hbe, h.symm⟩
    · rintro ⟨hs, hw, hww, hl, hb, hbe, rfl⟩
      refine ⟨_, ⟨⟨hs, hw, hww, fun _ => hl, fun _ => hb⟩, rfl⟩, ?_⟩
      simp [hbe]
  · simp

lemma chainAssetHandlerUpdateL2_eq_some {E : ConfigEnv} {s : Address} {l1 : Chain}
    {w w' : ConfigWorld} :
    chainAssetHandlerUpdateL2 E s l1 w = some w' ↔
      s = E.upgrader ∧ w' = { w with chainAssetHandler :=
        { w.chainAssetHandler with l1 := l1, eth := E.encNTV l1 E.ethToken } } := by
  unfold chainAssetHandlerUpdateL2
  by_cases h : s = E.upgrader <;> simp [h, eq_comm]

lemma chainAssetHandlerInitL2_eq_some {E : ConfigEnv} {s : Address} {l1 : Chain}
    {w w' : ConfigWorld} :
    chainAssetHandlerInitL2 E s l1 w = some w' ↔
      w.chainAssetHandler.locked = false ∧ s = E.upgrader ∧
        w' = { w with chainAssetHandler := ⟨l1, E.encNTV l1 E.ethToken, true⟩ } := by
  unfold chainAssetHandlerInitL2 chainAssetHandlerUpdateL2
  by_cases h1 : w.chainAssetHandler.locked = true <;> by_cases h2 : s = E.upgrader <;>
    simp [h1, h2, eq_comm]

lemma trackerInitL2_eq_some {E : ConfigEnv} {s : Address} {l1 : Chain} {a : AssetId}
    {w w' : ConfigWorld} :
    trackerInitL2 E s l1 a w = some w' ↔
      w.tracker.locked = false ∧ s = E.upgrader ∧ w' = { w with tracker := ⟨l1, a, true⟩ } := by
  unfold trackerInitL2
  by_cases h1 : w.tracker.locked = true <;> by_cases h2 : s = E.upgrader <;>
    simp [h1, h2, eq_comm]

lemma centerInitL2_eq_some {E : ConfigEnv} {s : Address} {l1 : Chain} {zk : AssetId}
    {w w' : ConfigWorld} :
    centerInitL2 E s l1 zk w = some w' ↔
      w.center.locked = false ∧ s = E.upgrader ∧ zk ≠ 0 ∧
        w' = { w with center := ⟨l1, true⟩ } := by
  unfold centerInitL2
  by_cases h1 : w.center.locked = true <;> by_cases h2 : s = E.upgrader <;>
    by_cases h3 : zk = 0 <;> simp [h1, h2, h3, eq_comm]

lemma baseTokenInitL2_eq_some {E : ConfigEnv} {s : Address} {l1 : Chain} {w w' : ConfigWorld} :
    baseTokenInitL2 E s l1 w = some w' ↔
      s = E.upgrader ∧ w.baseToken.initialized = false ∧
        w' = { w with baseToken := ⟨l1, true⟩ } := by
  unfold baseTokenInitL2
  by_cases h1 : w.baseToken.initialized = true <;> by_cases h2 : s = E.upgrader <;>
    simp [h1, h2, eq_comm]

lemma flowManagerInitL2_eq_some {E : ConfigEnv} {s : Address} {l1 : Chain} {w w' : ConfigWorld} :
    flowManagerInitL2 E s l1 w = some w' ↔
      s = E.upgrader ∧ w.flowManager.l1 = 0 ∧ l1 ≠ 0 ∧ w' = { w with flowManager := ⟨l1⟩ } := by
  unfold flowManagerInitL2
  split_ifs with h
  · simp only [Option.some.injEq]
    exact ⟨fun h' => ⟨h.1, h.2.1, h.2.2, h'.symm⟩, fun h' => h'.2.2.2.symm⟩
  · simp only [false_iff]
    exact fun h' => h ⟨h'.1, h'.2.1, h'.2.2.1⟩

lemma ensureWeth_of_ne {E : ConfigEnv} {u : UpgradeInput} {w : ConfigWorld}
    (h : w.vault.weth ≠ 0) : ensureWeth E u w = some (w, w.vault.weth) := by
  simp [ensureWeth, h]

lemma ensureWeth_of_eq_eq_some {E : ConfigEnv} {u : UpgradeInput} {w : ConfigWorld}
    {p : ConfigWorld × Address} (h : w.vault.weth = 0) :
    ensureWeth E u w = some p ↔
      (E.routerAddr ≠ 0 ∧ u.baseTokenL1Address ≠ 0 ∧ u.base.assetId ≠ 0) ∧
      p = ({ w with weth := ⟨u.base.assetId, u.baseTokenL1Address, true⟩ }, E.wethProxy u) := by
  unfold ensureWeth
  simp only [h, ne_eq, not_true_eq_false, ite_false]
  split_ifs with h2
  · simp only [Option.some.injEq]
    exact ⟨fun h' => ⟨h2, h'.symm⟩, fun h' => h'.2.symm⟩
  · simp only [false_iff]
    exact fun h' => h2 h'.1

/-! ## The two upgrade programs -/

/-- The state a successful genesis leaves, from all-zero storage. -/
def genesisPost (E : ConfigEnv) (u : UpgradeInput) : ConfigWorld where
  messageRoot := ⟨u.l1ChainId, true⟩
  bridgehub := ⟨u.l1ChainId, E.encNTV u.l1ChainId E.ethToken, true⟩
  router := ⟨u.l1ChainId, u.l1AssetRouter, u.base.assetId,
    ⟨upd (fun _ => 0) u.base.assetId E.ntvAddr, fun _ => 0⟩, true⟩
  vault := ⟨E.wethProxy u, u.base.assetId, u.l1ChainId, u.base.originToken, E.beaconOf u,
    upd (fun _ => 0) u.base.assetId E.baseTokenAddr, upd (fun _ => 0) E.baseTokenAddr u.base.assetId,
    upd (fun _ => 0) u.base.assetId u.base.originChainId, true⟩
  chainAssetHandler := ⟨u.l1ChainId, E.encNTV u.l1ChainId E.ethToken, true⟩
  tracker := ⟨u.l1ChainId, u.base.assetId, true⟩
  center := ⟨u.l1ChainId, true⟩
  baseToken := ⟨u.l1ChainId, true⟩
  flowManager := ⟨u.l1ChainId⟩
  weth := ⟨u.base.assetId, u.baseTokenL1Address, true⟩

/-- The checks a genesis from all-zero storage makes. -/
def GenesisInputOk (E : ConfigEnv) (c : Chain) (u : UpgradeInput) : Prop :=
  c ≠ 0 ∧ u.governance ≠ 0 ∧ E.routerAddr ≠ 0 ∧ u.baseTokenL1Address ≠ 0 ∧ u.base.assetId ≠ 0 ∧
    u.l1AssetRouter ≠ 0 ∧ E.wethProxy u ≠ 0 ∧ E.beaconOf u ≠ 0 ∧ u.zkTokenAssetId ≠ 0 ∧
    u.l1ChainId ≠ 0

/-- Genesis from all-zero storage succeeds exactly under its checks, and leaves `genesisPost`. -/
theorem genesis_fresh_eq_some {E : ConfigEnv} {c : Chain} {u : UpgradeInput} {w : ConfigWorld} :
    genesisUpgrade E c u ConfigWorld.fresh = some w ↔
      GenesisInputOk E c u ∧ w = genesisPost E u := by
  unfold genesisUpgrade
  by_cases h0 : c = 0 ∨ u.governance = 0
  · simp only [h0, ite_true, reduceCtorEq, false_iff]
    rintro ⟨⟨hc, hg, -⟩, -⟩
    rcases h0 with h0 | h0
    · exact hc h0
    · exact hg h0
  · simp only [h0, ite_false]
    rw [not_or] at h0
    simp only [Option.bind_eq_some_iff,
      ensureWeth_of_eq_eq_some (rfl : ConfigWorld.fresh.vault.weth = 0),
      messageRootInitL2_eq_some, bridgehubInitL2_eq_some, routerInitL2_eq_some, vaultInitL2_eq_some,
      chainAssetHandlerInitL2_eq_some, trackerInitL2_eq_some, centerInitL2_eq_some,
      baseTokenInitL2_eq_some, flowManagerInitL2_eq_some]
    constructor
    · rintro ⟨p, ⟨⟨hr, hl, ha⟩, rfl⟩, w1, ⟨-, -, rfl⟩, w2, ⟨-, -, rfl⟩, w3, ⟨-, -, hr0, rfl⟩,
        w4, ⟨-, -, hw, -, -, -, hbe, rfl⟩, w5, ⟨-, -, rfl⟩, w6, ⟨-, -, rfl⟩, w7, ⟨-, -, hzk, rfl⟩,
        w8, ⟨-, -, rfl⟩, -, -, hl1, rfl⟩
      exact ⟨⟨h0.1, h0.2, hr, hl, ha, hr0, hw, hbe, hzk, hl1⟩, rfl⟩
    · rintro ⟨⟨hc, hg, hr, hl, ha, hr0, hw, hbe, hzk, hl1⟩, rfl⟩
      refine ⟨_, ⟨⟨hr, hl, ha⟩, rfl⟩, _, ⟨?_, ?_, rfl⟩, _, ⟨?_, ?_, rfl⟩, _,
        ⟨?_, ?_, hr0, rfl⟩, _, ⟨?_, ?_, hw, ?_, ?_, ?_, hbe, rfl⟩,
        _, ⟨?_, ?_, rfl⟩, _, ⟨?_, ?_, rfl⟩, _, ⟨?_, ?_, hzk, rfl⟩, _, ⟨?_, ?_, rfl⟩,
        ?_, ?_, hl1, rfl⟩
      all_goals first | trivial | exact Or.inl rfl

/-- The state a successful default upgrade leaves. -/
def defaultPost (E : ConfigEnv) (u : UpgradeInput) (w : ConfigWorld) : ConfigWorld :=
  { w with
    messageRoot := { w.messageRoot with l1 := u.l1ChainId }
    bridgehub := { w.bridgehub with l1 := u.l1ChainId, eth := E.encNTV u.l1ChainId E.ethToken }
    router := { w.router with
      l1 := u.l1ChainId, l1AssetRouter := u.l1AssetRouter, base := u.base.assetId }
    vault := { w.vault with
      base := u.base.assetId, l1 := u.l1ChainId, baseOriginToken := u.base.originToken
      tokenAddress := upd w.vault.tokenAddress u.base.assetId E.baseTokenAddr
      assetIdOf := upd w.vault.assetIdOf E.baseTokenAddr u.base.assetId
      originChainId := upd w.vault.originChainId u.base.assetId u.base.originChainId }
    chainAssetHandler := { w.chainAssetHandler with
      l1 := u.l1ChainId, eth := E.encNTV u.l1ChainId E.ethToken } }

/-- The checks a default upgrade makes on a state with a nonzero WETH. -/
def DefaultInputOk (F : VaultFreezes) (u : UpgradeInput) (w : ConfigWorld) : Prop :=
  u.governance ≠ 0 ∧ u.l1AssetRouter ≠ 0 ∧
    (F.l1 = true → w.vault.l1 = 0 ∨ w.vault.l1 = u.l1ChainId) ∧
    (F.base = true → w.vault.base = 0 ∨ w.vault.base = u.base.assetId)

/-- On a state with a nonzero WETH, a default upgrade (with any freezes) succeeds exactly under
its checks, and leaves `defaultPost`. -/
theorem defaultUpgrade_with_eq_some {F : VaultFreezes} {E : ConfigEnv} {u : UpgradeInput}
    {w w' : ConfigWorld} (hw : w.vault.weth ≠ 0) :
    defaultUpgradeWith F E u w = some w' ↔ DefaultInputOk F u w ∧ w' = defaultPost E u w := by
  unfold defaultUpgradeWith
  by_cases hg : u.governance = 0
  · simp only [hg, ite_true, reduceCtorEq, false_iff]
    rintro ⟨⟨hg', -⟩, -⟩
    exact hg' hg
  · simp only [hg, ite_false, ensureWeth_of_ne hw, Option.bind_some, Option.bind_eq_some_iff,
      messageRootUpdateL2_eq_some, bridgehubUpdateL2_eq_some, routerUpdateL2_eq_some,
      vaultUpdateL2With_eq_some, chainAssetHandlerUpdateL2_eq_some]
    constructor
    · rintro ⟨w1, ⟨-, rfl⟩, w2, ⟨-, rfl⟩, w3, ⟨-, hr, rfl⟩, w4, ⟨⟨-, -, -, hl, hb⟩, rfl⟩, -, rfl⟩
      exact ⟨⟨hg, hr, hl, hb⟩, rfl⟩
    · rintro ⟨⟨-, hr, hl, hb⟩, rfl⟩
      refine ⟨_, ⟨?_, rfl⟩, _, ⟨?_, rfl⟩, _, ⟨?_, hr, rfl⟩, _, ⟨⟨?_, hw, ?_, hl, hb⟩, rfl⟩, ?_, rfl⟩
      all_goals first | trivial | exact Or.inr rfl

/-! ## Facts about the callers and the other writers -/

lemma genesis_unlocked {E : ConfigEnv} {c : Chain} {u : UpgradeInput} {w w' : ConfigWorld}
    (h : genesisUpgrade E c u w = some w') : w.messageRoot.locked = false := by
  unfold genesisUpgrade at h
  split_ifs at h
  obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨w1, h1, -⟩ := Option.bind_eq_some_iff.1 h
  rw [messageRootInitL2_eq_some] at h1
  unfold ensureWeth at hp
  split_ifs at hp
  · simp only [Option.some.injEq] at hp
    subst hp
    exact h1.1
  · simp only [Option.some.injEq] at hp
    subst hp
    exact h1.1

lemma directExec_sender {E : ConfigEnv} {s : Address} {w w' : ConfigWorld} {d : DirectCall}
    (h : directExec E s w d = some w') : s = E.upgrader := by
  cases d <;> simp only [directExec] at h
  · exact (messageRootInitL2_eq_some.1 h).2.1
  · exact (messageRootUpdateL2_eq_some.1 h).1
  · exact (bridgehubInitL2_eq_some.1 h).2.1
  · exact (bridgehubUpdateL2_eq_some.1 h).1
  · exact (routerInitL2_eq_some.1 h).2.1
  · exact (routerUpdateL2_eq_some.1 h).1
  · exact (vaultInitL2_eq_some.1 h).2.1
  · exact (vaultUpdateL2With_eq_some.1 h).1.1
  · exact (chainAssetHandlerInitL2_eq_some.1 h).2.1
  · exact (chainAssetHandlerUpdateL2_eq_some.1 h).1
  · exact (trackerInitL2_eq_some.1 h).2.1
  · exact (centerInitL2_eq_some.1 h).2.1
  · exact (baseTokenInitL2_eq_some.1 h).1
  · exact (flowManagerInitL2_eq_some.1 h).1

lemma upgrade_eq_some {E : ConfigEnv} {s : Address} {w w' : ConfigWorld} {p : UpgradeProgram} :
    configExec E s w (.upgrade p) = some w' ↔ s = E.forceDeployer ∧ runProgram E w p = some w' := by
  simp only [configExec]
  split_ifs with hs
  · exact ⟨fun h => ⟨hs, h⟩, fun h => h.2⟩
  · simp only [false_iff]
    exact fun h => hs h.1

lemma upgrade_sender {E : ConfigEnv} {s : Address} {w w' : ConfigWorld} {p : UpgradeProgram}
    (h : configExec E s w (.upgrade p) = some w') : s = E.forceDeployer :=
  (upgrade_eq_some.1 h).1

/-- No router call by an account other than the vault passes the tracker check while every
recorded tracker is zero or the vault. -/
lemma routerRegister_none {E : ConfigEnv} {s : Address} {w : ConfigWorld} {d : AssetData}
    {h : Address}
    (ht : ∀ x, w.router.routes.tracker x = 0 ∨ w.router.routes.tracker x = E.ntvAddr) :
    configExec E s w (.routerRegister d h) = none := by
  simp only [configExec]
  split_ifs with hg
  · obtain ⟨hs0, hsn, htr⟩ := hg
    rcases ht (writtenId E.enc E.thisChain E.ntvAddr E.ntvAddr s d) with h0 | h0
    · exact absurd (htr.symm.trans h0) hs0
    · exact absurd (htr.symm.trans h0) hsn
  · rfl

lemma genesis_none_of_consistent {E : ConfigEnv} {l1 : Chain} {a : AssetId} {weth : Address}
    {w : ConfigWorld} (hC : ConfigConsistent E l1 a weth w) (c : Chain) (u : UpgradeInput) :
    genesisUpgrade E c u w = none := by
  cases hg : genesisUpgrade E c u w with
  | none => rfl
  | some w' =>
    have := genesis_unlocked hg
    rw [hC.messageRootLocked] at this
    exact absurd this (by decide)

/-! ## The invariant under each kind of step -/

lemma consistent_defaultPost {E : ConfigEnv} {l1 : Chain} {a : AssetId} {weth : Address}
    {w : ConfigWorld} {u : UpgradeInput} (hC : ConfigConsistent E l1 a weth w)
    (hl : u.l1ChainId = l1) (ha : u.base.assetId = a) :
    ConfigConsistent E l1 a weth (defaultPost E u w) := by
  subst hl ha
  exact { hC with
    messageRootL1 := rfl, bridgehubL1 := rfl, routerL1 := rfl, vaultL1 := rfl,
    chainAssetHandlerL1 := rfl, routerBase := rfl, vaultBase := rfl, bridgehubEth := rfl,
    chainAssetHandlerEth := rfl
    baseTokenAddress := cfg_upd_self _ _ _
    baseAssetIdOf := cfg_upd_self _ _ _ }

/-- **Where the freezes act.**  From a consistent state, a successful default upgrade carries the
stored ids, made its checks, and leaves `defaultPost`. -/
lemma default_ids {E : ConfigEnv} {l1 : Chain} {a : AssetId} {weth : Address}
    {w w' : ConfigWorld} {u : UpgradeInput} (hC : ConfigConsistent E l1 a weth w)
    (h : defaultUpgrade E u w = some w') :
    u.l1ChainId = l1 ∧ u.base.assetId = a ∧ DefaultInputOk deployedFreezes u w ∧
      w' = defaultPost E u w := by
  have hw : w.vault.weth ≠ 0 := hC.vaultWeth ▸ hC.weth_ne
  obtain ⟨⟨hg, hr, hl, hb⟩, rfl⟩ := (defaultUpgrade_with_eq_some hw).1 h
  have hl' := hl rfl
  have hb' := hb rfl
  rw [hC.vaultL1] at hl'
  rw [hC.vaultBase] at hb'
  refine ⟨?_, ?_, ⟨hg, hr, hl, hb⟩, rfl⟩
  · rcases hl' with h0 | h0
    · exact absurd h0 hC.l1_ne
    · exact h0.symm
  · rcases hb' with h0 | h0
    · exact absurd h0 hC.base_ne
    · exact h0.symm

lemma consistent_pointRoute {E : ConfigEnv} {l1 : Chain} {a : AssetId} {weth : Address}
    {w : ConfigWorld} (hC : ConfigConsistent E l1 a weth w) (id : AssetId) (h : Address) :
    ConfigConsistent E l1 a weth (w.pointRoute id h) :=
  { hC with }

lemma consistent_registerNative {E : ConfigEnv} {l1 : Chain} {a : AssetId} {weth : Address}
    {w : ConfigWorld} {t : Address} (hC : ConfigConsistent E l1 a weth w)
    (hfresh : w.vault.assetIdOf t = 0) (hmiss : E.encNTV E.thisChain t ≠ a) :
    ConfigConsistent E l1 a weth (registerNative E w t) := by
  have hbt : t ≠ E.baseTokenAddr := by
    rintro rfl
    exact hC.base_ne (hC.baseAssetIdOf.symm.trans hfresh)
  refine { hC with baseTokenAddress := ?_, baseAssetIdOf := ?_, trackersVaultOnly := ?_ }
  · simp only [registerNative, ConfigWorld.setRoutes, ConfigWorld.setNewTokenStorage]
    rw [cfg_upd_of_ne _ _ (Ne.symm hmiss)]
    exact hC.baseTokenAddress
  · simp only [registerNative, ConfigWorld.setRoutes, ConfigWorld.setNewTokenStorage]
    rw [cfg_upd_of_ne _ _ (Ne.symm hbt)]
    exact hC.baseAssetIdOf
  · intro x
    simp only [registerNative, ConfigWorld.setRoutes, setHandler]
    by_cases hx : x = writtenId E.enc E.thisChain E.ntvAddr E.ntvAddr E.ntvAddr t
    · subst hx
      exact Or.inr (cfg_upd_self _ _ _)
    · rw [cfg_upd_of_ne _ _ hx]
      exact hC.trackersVaultOnly x

lemma consistent_setNewTokenStorage {E : ConfigEnv} {l1 : Chain} {a : AssetId} {weth : Address}
    {w : ConfigWorld} {id : AssetId} {tok : Address} {o : Chain}
    (hC : ConfigConsistent E l1 a weth w) (hid : w.vault.tokenAddress id = 0)
    (htok : tok ≠ E.baseTokenAddr) :
    ConfigConsistent E l1 a weth (w.setNewTokenStorage id tok o) := by
  have hida : a ≠ id := by
    rintro rfl
    exact hC.baseTokenAddr_ne (hC.baseTokenAddress.symm.trans hid)
  refine { hC with baseTokenAddress := ?_, baseAssetIdOf := ?_ }
  · simp only [ConfigWorld.setNewTokenStorage]
    rw [cfg_upd_of_ne _ _ hida]
    exact hC.baseTokenAddress
  · simp only [ConfigWorld.setNewTokenStorage]
    rw [cfg_upd_of_ne _ _ (Ne.symm htok)]
    exact hC.baseAssetIdOf

theorem step_preserves {E : ConfigEnv} {l1 : Chain} {a : AssetId} {weth : Address}
    {w w' : ConfigWorld} {c : ConfigCall} (hC : ConfigConsistent E l1 a weth w)
    (hadm : c.Admissible E a) (h : configExec E c.sender w c.op = some w') :
    ConfigConsistent E l1 a weth w' := by
  obtain ⟨s, op⟩ := c
  cases op with
  | upgrade p =>
    obtain ⟨-, h⟩ := upgrade_eq_some.1 h
    cases p with
    | genesis ch u =>
      simp only [runProgram, genesis_none_of_consistent hC] at h
      exact absurd h (by simp)
    | default u =>
      obtain ⟨hl, ha, -, rfl⟩ := default_ids hC h
      exact consistent_defaultPost hC hl ha
  | direct d =>
    exact absurd (directExec_sender h) (hadm.notUpgraderDirect d rfl)
  | counterpartSet src id hh =>
    simp only [configExec] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    exact consistent_pointRoute hC id hh
  | routerRegister d hh =>
    rw [routerRegister_none hC.trackersVaultOnly] at h
    exact absurd h (by simp)
  | finalizeFallback id =>
    simp only [configExec] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    exact consistent_pointRoute hC id E.ntvAddr
  | vaultRegister t =>
    simp only [configExec] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h
    subst h
    exact consistent_registerNative hC hg.2 (hadm.registrationMissesBase t rfl)
  | vaultDeploy id o ot tok =>
    simp only [configExec] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h
    subst h
    exact consistent_setNewTokenStorage hC hg.1 hg.2.2.2.2.2.2

/-! ## Genesis, and the default upgrade from a consistent state -/

theorem genesis_establishes {E : ConfigEnv} {s : Address} {c : Chain} {u : UpgradeInput}
    {w : ConfigWorld} (hbt : E.baseTokenAddr ≠ 0)
    (h : configExec E s ConfigWorld.fresh (.upgrade (.genesis c u)) = some w) :
    s = E.forceDeployer ∧
    ConfigConsistent E u.l1ChainId u.base.assetId (E.wethProxy u) w ∧
    BaseRoutedToVault E u.base.assetId w ∧
    BaseOriginIs u.base.originChainId u.base.originToken u.base.assetId w := by
  obtain ⟨hs, h⟩ := upgrade_eq_some.1 h
  simp only [runProgram] at h
  obtain ⟨⟨-, -, -, -, ha, -, hw, -, -, hl1⟩, rfl⟩ := genesis_fresh_eq_some.1 h
  refine ⟨hs, ?_, ?_, ?_⟩
  · exact
      { l1_ne := hl1, base_ne := ha, weth_ne := hw, baseTokenAddr_ne := hbt
        messageRootL1 := rfl, bridgehubL1 := rfl, routerL1 := rfl, vaultL1 := rfl
        chainAssetHandlerL1 := rfl, trackerL1 := rfl, centerL1 := rfl, baseTokenL1 := rfl
        flowManagerL1 := rfl, routerBase := rfl, vaultBase := rfl, trackerBase := rfl
        wethBase := rfl, bridgehubEth := rfl, chainAssetHandlerEth := rfl, vaultWeth := rfl
        baseTokenAddress := cfg_upd_self (fun _ => 0) u.base.assetId E.baseTokenAddr
        baseAssetIdOf := cfg_upd_self (fun _ => 0) E.baseTokenAddr u.base.assetId
        messageRootLocked := rfl, bridgehubLocked := rfl, routerLocked := rfl, vaultLocked := rfl
        chainAssetHandlerLocked := rfl, trackerLocked := rfl, centerLocked := rfl
        baseTokenInitialized := rfl, trackersVaultOnly := fun _ => Or.inl rfl }
  · exact cfg_upd_self (fun _ => 0) u.base.assetId E.ntvAddr
  · exact ⟨cfg_upd_self (fun _ => 0) u.base.assetId u.base.originChainId, rfl⟩

theorem default_adopts {E : ConfigEnv} {l1 : Chain} {a : AssetId} {weth : Address}
    {w : ConfigWorld} {u : UpgradeInput} (hC : ConfigConsistent E l1 a weth w)
    (hl : u.l1ChainId = l1) (ha : u.base.assetId = a) (hg : u.governance ≠ 0)
    (hr : u.l1AssetRouter ≠ 0) :
    configExec E E.forceDeployer w (.upgrade (.default u)) = some (defaultPost E u w) := by
  have hw : w.vault.weth ≠ 0 := hC.vaultWeth ▸ hC.weth_ne
  rw [upgrade_eq_some]
  refine ⟨rfl, (defaultUpgrade_with_eq_some hw).2
    ⟨⟨hg, hr, fun _ => Or.inr ?_, fun _ => Or.inr ?_⟩, rfl⟩⟩
  · rw [hC.vaultL1, hl]
  · rw [hC.vaultBase, ha]

/-! ## The base id's route -/

lemma directExec_routes {E : ConfigEnv} {l1 : Chain} {a : AssetId} {weth : Address}
    {s : Address} {w w' : ConfigWorld} {d : DirectCall} (hC : ConfigConsistent E l1 a weth w)
    (h : directExec E s w d = some w') : w'.router.routes = w.router.routes := by
  cases d <;> simp only [directExec] at h
  · obtain ⟨-, -, rfl⟩ := messageRootInitL2_eq_some.1 h; rfl
  · obtain ⟨-, rfl⟩ := messageRootUpdateL2_eq_some.1 h; rfl
  · obtain ⟨-, -, rfl⟩ := bridgehubInitL2_eq_some.1 h; rfl
  · obtain ⟨-, rfl⟩ := bridgehubUpdateL2_eq_some.1 h; rfl
  · have := (routerInitL2_eq_some.1 h).1
    rw [hC.routerLocked] at this
    exact absurd this (by decide)
  · obtain ⟨-, -, rfl⟩ := routerUpdateL2_eq_some.1 h; rfl
  · obtain ⟨-, -, -, -, -, -, -, rfl⟩ := vaultInitL2_eq_some.1 h; rfl
  · obtain ⟨-, rfl⟩ := vaultUpdateL2With_eq_some.1 h; rfl
  · obtain ⟨-, -, rfl⟩ := chainAssetHandlerInitL2_eq_some.1 h; rfl
  · obtain ⟨-, rfl⟩ := chainAssetHandlerUpdateL2_eq_some.1 h; rfl
  · obtain ⟨-, -, rfl⟩ := trackerInitL2_eq_some.1 h; rfl
  · obtain ⟨-, -, -, rfl⟩ := centerInitL2_eq_some.1 h; rfl
  · obtain ⟨-, -, rfl⟩ := baseTokenInitL2_eq_some.1 h; rfl
  · obtain ⟨-, -, -, rfl⟩ := flowManagerInitL2_eq_some.1 h; rfl

theorem base_route_stays {E : ConfigEnv} {l1 : Chain} {a : AssetId} {weth : Address}
    {w w' : ConfigWorld} {c : ConfigCall} (hC : ConfigConsistent E l1 a weth w)
    (hR : BaseRoutedToVault E a w) (h : configExec E c.sender w c.op = some w')
    (hnc : ¬ c.op.IsCounterpartAt a) : BaseRoutedToVault E a w' := by
  obtain ⟨s, op⟩ := c
  unfold BaseRoutedToVault at hR ⊢
  cases op with
  | upgrade p =>
    obtain ⟨-, h⟩ := upgrade_eq_some.1 h
    cases p with
    | genesis ch u =>
      simp only [runProgram, genesis_none_of_consistent hC] at h
      exact absurd h (by simp)
    | default u =>
      simp only [runProgram] at h
      obtain ⟨-, -, -, rfl⟩ := default_ids hC h
      exact hR
  | direct d =>
    simp only [configExec] at h
    rw [directExec_routes hC h]
    exact hR
  | counterpartSet src id hh =>
    simp only [configExec] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    have hid : a ≠ id := fun he => hnc (by simp [ConfigOp.IsCounterpartAt, he])
    simp only [ConfigWorld.pointRoute]
    rw [cfg_upd_of_ne _ _ hid]
    exact hR
  | routerRegister d hh =>
    rw [routerRegister_none hC.trackersVaultOnly] at h
    exact absurd h (by simp)
  | finalizeFallback id =>
    simp only [configExec] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h
    subst h
    have hid : a ≠ id := fun he => hg.1 (he ▸ hC.routerBase.symm)
    simp only [ConfigWorld.pointRoute]
    rw [cfg_upd_of_ne _ _ hid]
    exact hR
  | vaultRegister t =>
    simp only [configExec] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    simp only [registerNative, ConfigWorld.setRoutes, setHandler, ConfigWorld.setNewTokenStorage]
    by_cases hx : a = writtenId E.enc E.thisChain E.ntvAddr E.ntvAddr E.ntvAddr t
    · rw [hx, cfg_upd_self]
    · rw [cfg_upd_of_ne _ _ hx]
      exact hR
  | vaultDeploy id o ot tok =>
    simp only [configExec] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    exact hR

/-! ## Writers -/

theorem only_upgrader_writes_scalars {E : ConfigEnv} {s : Address} {w w' : ConfigWorld}
    {op : ConfigOp} (h : configExec E s w op = some w') (hne : w'.scalars ≠ w.scalars) :
    ((∃ p, op = .upgrade p) ∧ s = E.forceDeployer) ∨
      ((∃ d, op = .direct d) ∧ s = E.upgrader) := by
  cases op with
  | upgrade p => exact Or.inl ⟨⟨p, rfl⟩, upgrade_sender h⟩
  | direct d => exact Or.inr ⟨⟨d, rfl⟩, directExec_sender h⟩
  | counterpartSet src id hh =>
    simp only [configExec] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    exact absurd rfl hne
  | routerRegister d hh =>
    simp only [configExec] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    exact absurd rfl hne
  | finalizeFallback id =>
    simp only [configExec] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    exact absurd rfl hne
  | vaultRegister t =>
    simp only [configExec] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    exact absurd rfl hne
  | vaultDeploy id o ot tok =>
    simp only [configExec] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    exact absurd rfl hne

lemma directExec_baseEntries {E : ConfigEnv} {l1 : Chain} {a : AssetId} {weth : Address}
    {s : Address} {w w' : ConfigWorld} {d : DirectCall} (hC : ConfigConsistent E l1 a weth w)
    (h : directExec E s w d = some w') (hne : w'.baseEntries E a ≠ w.baseEntries E a) :
    ∃ l1' weth' b, d = .vaultUpdate l1' weth' b := by
  cases d with
  | vaultUpdate l1' weth' b => exact ⟨l1', weth', b, rfl⟩
  | _ =>
    simp only [directExec] at h
    first
    | (obtain ⟨-, -, rfl⟩ := messageRootInitL2_eq_some.1 h; exact absurd rfl hne)
    | (obtain ⟨-, rfl⟩ := messageRootUpdateL2_eq_some.1 h; exact absurd rfl hne)
    | (obtain ⟨-, -, rfl⟩ := bridgehubInitL2_eq_some.1 h; exact absurd rfl hne)
    | (obtain ⟨-, rfl⟩ := bridgehubUpdateL2_eq_some.1 h; exact absurd rfl hne)
    | (have := (routerInitL2_eq_some.1 h).1
       rw [hC.routerLocked] at this
       exact absurd this (by decide))
    | (obtain ⟨-, -, rfl⟩ := routerUpdateL2_eq_some.1 h; exact absurd rfl hne)
    | (have := (vaultInitL2_eq_some.1 h).1
       rw [hC.vaultLocked] at this
       exact absurd this (by decide))
    | (obtain ⟨-, -, rfl⟩ := chainAssetHandlerInitL2_eq_some.1 h; exact absurd rfl hne)
    | (obtain ⟨-, rfl⟩ := chainAssetHandlerUpdateL2_eq_some.1 h; exact absurd rfl hne)
    | (obtain ⟨-, -, rfl⟩ := trackerInitL2_eq_some.1 h; exact absurd rfl hne)
    | (obtain ⟨-, -, -, rfl⟩ := centerInitL2_eq_some.1 h; exact absurd rfl hne)
    | (obtain ⟨-, -, rfl⟩ := baseTokenInitL2_eq_some.1 h; exact absurd rfl hne)
    | (obtain ⟨-, -, -, rfl⟩ := flowManagerInitL2_eq_some.1 h; exact absurd rfl hne)

theorem base_entries_writers {E : ConfigEnv} {l1 : Chain} {a : AssetId} {weth : Address}
    {w w' : ConfigWorld} {s : Address} {op : ConfigOp} (hC : ConfigConsistent E l1 a weth w)
    (h : configExec E s w op = some w') (hne : w'.baseEntries E a ≠ w.baseEntries E a) :
    ((∃ u, op = .upgrade (.default u)) ∧ s = E.forceDeployer) ∨
    ((∃ l1' weth' b, op = .direct (.vaultUpdate l1' weth' b)) ∧ s = E.upgrader) ∨
    (∃ t, op = .vaultRegister t ∧ E.encNTV E.thisChain t = a) ∨
    (∃ h, op = .counterpartSet l1 a h ∧ E.undoAlias s = w.router.l1AssetRouter) := by
  cases op with
  | upgrade p =>
    obtain ⟨hs, h⟩ := upgrade_eq_some.1 h
    cases p with
    | genesis ch u =>
      simp only [runProgram, genesis_none_of_consistent hC] at h
      exact absurd h (by simp)
    | default u => exact Or.inl ⟨⟨u, rfl⟩, hs⟩
  | direct d =>
    have hs := directExec_sender h
    simp only [configExec] at h
    obtain ⟨l1', weth', b, rfl⟩ := directExec_baseEntries hC h hne
    exact Or.inr (Or.inl ⟨⟨l1', weth', b, rfl⟩, hs⟩)
  | counterpartSet src id hh =>
    simp only [configExec] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h
    subst h
    by_cases hid : a = id
    · subst hid
      refine Or.inr (Or.inr (Or.inr ⟨hh, ?_, hg.2⟩))
      rw [hg.1, hC.routerL1]
    · refine absurd ?_ hne
      simp only [ConfigWorld.baseEntries, ConfigWorld.pointRoute]
      rw [cfg_upd_of_ne _ _ hid]
  | routerRegister d hh =>
    rw [routerRegister_none hC.trackersVaultOnly] at h
    exact absurd h (by simp)
  | finalizeFallback id =>
    simp only [configExec] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h
    subst h
    have hid : a ≠ id := fun he => hg.1 (he ▸ hC.routerBase.symm)
    refine absurd ?_ hne
    simp only [ConfigWorld.baseEntries, ConfigWorld.pointRoute]
    rw [cfg_upd_of_ne _ _ hid]
  | vaultRegister t =>
    simp only [configExec] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h
    subst h
    by_cases hx : E.encNTV E.thisChain t = a
    · exact Or.inr (Or.inr (Or.inl ⟨t, rfl, hx⟩))
    · have hbt : t ≠ E.baseTokenAddr := by
        rintro rfl
        exact hC.base_ne (hC.baseAssetIdOf.symm.trans hg.2)
      have hx' : a ≠ E.encNTV E.thisChain t := Ne.symm hx
      refine absurd ?_ hne
      simp only [ConfigWorld.baseEntries, registerNative, ConfigWorld.setRoutes,
        ConfigWorld.setNewTokenStorage, setHandler]
      have hw : a ≠ writtenId E.enc E.thisChain E.ntvAddr E.ntvAddr E.ntvAddr t := by
        simpa [writtenId, senderOf, ConfigEnv.encNTV] using hx'
      rw [cfg_upd_of_ne _ _ hx', cfg_upd_of_ne _ _ (Ne.symm hbt), cfg_upd_of_ne _ _ hx',
        cfg_upd_of_ne _ _ hw]
  | vaultDeploy id o ot tok =>
    simp only [configExec] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h
    subst h
    have hida : a ≠ id := by
      rintro rfl
      exact hC.baseTokenAddr_ne (hC.baseTokenAddress.symm.trans hg.1)
    refine absurd ?_ hne
    simp only [ConfigWorld.baseEntries, ConfigWorld.setNewTokenStorage]
    rw [cfg_upd_of_ne _ _ hida, cfg_upd_of_ne _ _ (Ne.symm hg.2.2.2.2.2.2), cfg_upd_of_ne _ _ hida]

/-! ## Runs -/

theorem run_invariant {E : ConfigEnv} {l1 : Chain} {a : AssetId} {weth : Address}
    {w0 w : ConfigWorld} {cs : List ConfigCall}
    (h0 : ConfigConsistent E l1 a weth w0) (hrun : ConfigRun E w0 cs w) :
    (∀ c ∈ cs, c.Admissible E a) →
    ConfigConsistent E l1 a weth w ∧
    (∀ c ∈ cs, ∀ u', c.op = .upgrade (.default u') → u'.l1ChainId = l1 ∧ u'.base.assetId = a) ∧
    (BaseRoutedToVault E a w0 → (∀ c ∈ cs, ¬ c.op.IsCounterpartAt a) →
      BaseRoutedToVault E a w) := by
  induction hrun with
  | nil => exact fun _ => ⟨h0, fun c hc => (by cases hc), fun hR _ => hR⟩
  | snoc hprev hstep ih =>
    intro hadm
    obtain ⟨hv, hids, hroute⟩ := ih (fun c hc => hadm c (List.mem_append_left _ hc))
    have hlast := hadm _ (List.mem_append_right _ (List.mem_singleton_self _))
    refine ⟨step_preserves hv hlast hstep, ?_, ?_⟩
    · intro c' hc' u' hu'
      rcases List.mem_append.1 hc' with hc' | hc'
      · exact hids c' hc' u' hu'
      · rw [List.mem_singleton] at hc'
        subst hc'
        rw [hu'] at hstep
        obtain ⟨-, hstep⟩ := upgrade_eq_some.1 hstep
        obtain ⟨hl, ha, -⟩ := default_ids hv hstep
        exact ⟨hl, ha⟩
    · intro hR hnc
      exact base_route_stays hv (hroute hR (fun c hc => hnc c (List.mem_append_left _ hc))) hstep
        (hnc _ (List.mem_append_right _ (List.mem_singleton_self _)))

theorem step_keeps_origin {E : ConfigEnv} {l1 : Chain} {a : AssetId} {weth : Address}
    {o : Chain} {t : Address} {w w' : ConfigWorld} {c : ConfigCall}
    (hC : ConfigConsistent E l1 a weth w) (hO : BaseOriginIs o t a w) (hadm : c.Admissible E a)
    (hk : c.KeepsBaseOrigin o t) (h : configExec E c.sender w c.op = some w') :
    BaseOriginIs o t a w' := by
  obtain ⟨s, op⟩ := c
  obtain ⟨hO1, hO2⟩ := hO
  cases op with
  | upgrade p =>
    obtain ⟨-, h⟩ := upgrade_eq_some.1 h
    cases p with
    | genesis ch u =>
      simp only [runProgram, genesis_none_of_consistent hC] at h
      exact absurd h (by simp)
    | default u =>
      simp only [runProgram] at h
      obtain ⟨-, ha, -, rfl⟩ := default_ids hC h
      obtain ⟨ho, ht⟩ := hk u rfl
      subst ha
      refine ⟨?_, ht⟩
      show upd w.vault.originChainId u.base.assetId u.base.originChainId u.base.assetId = o
      rw [cfg_upd_self, ho]
  | direct d => exact absurd (directExec_sender h) (hadm.notUpgraderDirect d rfl)
  | counterpartSet src id hh =>
    simp only [configExec] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨hO1, hO2⟩
  | routerRegister d hh =>
    rw [routerRegister_none hC.trackersVaultOnly] at h
    exact absurd h (by simp)
  | finalizeFallback id =>
    simp only [configExec] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨hO1, hO2⟩
  | vaultRegister t' =>
    simp only [configExec] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    have hx : a ≠ E.encNTV E.thisChain t' := Ne.symm (hadm.registrationMissesBase t' rfl)
    refine ⟨?_, hO2⟩
    simp only [registerNative, ConfigWorld.setRoutes, ConfigWorld.setNewTokenStorage]
    rw [cfg_upd_of_ne _ _ hx]
    exact hO1
  | vaultDeploy id o' ot tok =>
    simp only [configExec] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h
    subst h
    have hida : a ≠ id := by
      rintro rfl
      exact hC.baseTokenAddr_ne (hC.baseTokenAddress.symm.trans hg.1)
    refine ⟨?_, hO2⟩
    simp only [ConfigWorld.setNewTokenStorage]
    rw [cfg_upd_of_ne _ _ hida]
    exact hO1

theorem run_origin {E : ConfigEnv} {l1 : Chain} {a : AssetId} {weth : Address}
    {o : Chain} {t : Address} {w0 w : ConfigWorld} {cs : List ConfigCall}
    (h0 : ConfigConsistent E l1 a weth w0) (hO : BaseOriginIs o t a w0)
    (hrun : ConfigRun E w0 cs w) :
    (∀ c ∈ cs, c.Admissible E a) → (∀ c ∈ cs, c.KeepsBaseOrigin o t) →
    ConfigConsistent E l1 a weth w ∧ BaseOriginIs o t a w := by
  induction hrun with
  | nil => exact fun _ _ => ⟨h0, hO⟩
  | snoc hprev hstep ih =>
    intro hadm hk
    obtain ⟨hv, hvO⟩ := ih (fun c hc => hadm c (List.mem_append_left _ hc))
      (fun c hc => hk c (List.mem_append_left _ hc))
    have hlast := hadm _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hklast := hk _ (List.mem_append_right _ (List.mem_singleton_self _))
    exact ⟨step_preserves hv hlast hstep, step_keeps_origin hv hvO hlast hklast hstep⟩

/-! ## Countermodels -/

lemma not_consistent_of_ne {E : ConfigEnv} {w : ConfigWorld}
    (hne : w.router.base ≠ w.tracker.base) :
    ∀ l1' a' weth', ¬ ConfigConsistent E l1' a' weth' w := by
  intro l1' a' weth' hC
  exact hne (hC.routerBase.trans hC.trackerBase.symm)

theorem no_base_freeze {E : ConfigEnv} {l1 : Chain} {a : AssetId} {weth : Address}
    {w : ConfigWorld} {u : UpgradeInput} (hC : ConfigConsistent E l1 a weth w)
    (hl : u.l1ChainId = l1) (ha : u.base.assetId ≠ a) (hg : u.governance ≠ 0)
    (hr : u.l1AssetRouter ≠ 0) :
    defaultUpgrade E u w = none ∧
    ∃ w', defaultUpgradeWith ⟨true, false⟩ E u w = some w' ∧
      w'.router.base = u.base.assetId ∧ w'.vault.base = u.base.assetId ∧
      w'.tracker.base = a ∧ w'.weth.base = a ∧
      ∀ l1' a' weth', ¬ ConfigConsistent E l1' a' weth' w' := by
  have hw : w.vault.weth ≠ 0 := hC.vaultWeth ▸ hC.weth_ne
  refine ⟨?_, defaultPost E u w, (defaultUpgrade_with_eq_some hw).2
    ⟨⟨hg, hr, fun _ => Or.inr (by rw [hC.vaultL1, hl]), fun h => absurd h (by decide)⟩, rfl⟩,
    rfl, rfl, hC.trackerBase, hC.wethBase, not_consistent_of_ne ?_⟩
  · cases hd : defaultUpgrade E u w with
    | none => rfl
    | some w' => exact absurd (default_ids hC hd).2.1 ha
  · show u.base.assetId ≠ w.tracker.base
    rw [hC.trackerBase]
    exact ha

theorem no_l1_freeze {E : ConfigEnv} {l1 : Chain} {a : AssetId} {weth : Address}
    {w : ConfigWorld} {u : UpgradeInput} (hC : ConfigConsistent E l1 a weth w)
    (hl : u.l1ChainId ≠ l1) (ha : u.base.assetId = a) (hg : u.governance ≠ 0)
    (hr : u.l1AssetRouter ≠ 0) :
    defaultUpgrade E u w = none ∧
    ∃ w', defaultUpgradeWith ⟨false, true⟩ E u w = some w' ∧
      w'.messageRoot.l1 = u.l1ChainId ∧ w'.bridgehub.l1 = u.l1ChainId ∧
      w'.router.l1 = u.l1ChainId ∧ w'.vault.l1 = u.l1ChainId ∧
      w'.chainAssetHandler.l1 = u.l1ChainId ∧
      w'.tracker.l1 = l1 ∧ w'.center.l1 = l1 ∧ w'.baseToken.l1 = l1 ∧ w'.flowManager.l1 = l1 ∧
      ∀ l1' a' weth', ¬ ConfigConsistent E l1' a' weth' w' := by
  have hw : w.vault.weth ≠ 0 := hC.vaultWeth ▸ hC.weth_ne
  refine ⟨?_, defaultPost E u w, (defaultUpgrade_with_eq_some hw).2
    ⟨⟨hg, hr, fun h => absurd h (by decide), fun _ => Or.inr (by rw [hC.vaultBase, ha])⟩, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, hC.trackerL1, hC.centerL1, hC.baseTokenL1, hC.flowManagerL1, ?_⟩
  · cases hd : defaultUpgrade E u w with
    | none => rfl
    | some w' => exact absurd (default_ids hC hd).1 hl
  · intro l1' a' weth' hC'
    have h1 : (defaultPost E u w).vault.l1 = l1' := hC'.vaultL1
    have h2 : (defaultPost E u w).tracker.l1 = l1' := hC'.trackerL1
    have h3 : u.l1ChainId = l1 := by
      rw [← hC.trackerL1]
      exact h1.trans h2.symm
    exact hl h3

theorem origin_flip {E : ConfigEnv} {l1 : Chain} {a : AssetId} {weth : Address}
    {w : ConfigWorld} {u : UpgradeInput} (hC : ConfigConsistent E l1 a weth w)
    (hl : u.l1ChainId = l1) (ha : u.base.assetId = a) (ho : u.base.originChainId = E.thisChain)
    (hg : u.governance ≠ 0) (hr : u.l1AssetRouter ≠ 0) :
    configExec E E.forceDeployer w (.upgrade (.default u)) = some (defaultPost E u w) ∧
      ConfigConsistent E l1 a weth (defaultPost E u w) ∧ BaseNativeHere E (defaultPost E u w) := by
  refine ⟨default_adopts hC hl ha hg hr, consistent_defaultPost hC hl ha, ?_⟩
  show upd w.vault.originChainId u.base.assetId u.base.originChainId u.base.assetId = E.thisChain
  rw [cfg_upd_self, ho]

theorem router_outside_helper {E : ConfigEnv} {l1 : Chain} {a : AssetId} {weth : Address}
    {w : ConfigWorld} {r : Address} {a' : AssetId} (hC : ConfigConsistent E l1 a weth w)
    (hr : r ≠ 0) (ha : a' ≠ a) :
    ∃ w', configExec E E.upgrader w (.direct (.routerUpdate l1 r a')) = some w' ∧
      w'.router.base = a' ∧ w'.vault.base = a ∧ w'.tracker.base = a ∧
      ∀ l1' a'' weth', ¬ ConfigConsistent E l1' a'' weth' w' := by
  refine ⟨{ w with router := { w.router with l1 := l1, l1AssetRouter := r, base := a' } },
    routerUpdateL2_eq_some.2 ⟨rfl, hr, rfl⟩, rfl, hC.vaultBase, hC.trackerBase,
    not_consistent_of_ne ?_⟩
  show a' ≠ w.tracker.base
  rw [hC.trackerBase]
  exact ha

/-! ## Witnesses

The deployed addresses (`0x8007`, `0x800f`, `0x10004`, `0x10003`, `0x800a`, `address(1)`), this
chain `270`, L1 `1`, and a toy asset-id encoding: chain plus sender plus data.  No property of
the encoding is used by the results; it only has to separate the ids below. -/

/-- The witness environment. -/
def wConfigEnv : ConfigEnv where
  thisChain := 270
  forceDeployer := 0x8007
  upgrader := 0x800f
  ntvAddr := 0x10004
  routerAddr := 0x10003
  baseTokenAddr := 0x800a
  ethToken := 1
  enc := fun c s d => c + s + d
  wethProxy := fun _ => 0x20000
  deployedBeacon := 0x20001
  undoAlias := fun x => x

/-- The genesis input: L1 is chain `1`, the base token is the L1 token `0x5000`, with asset id
`encodeNTVAssetId(1, 0x5000)`. -/
def wGenesisInput : UpgradeInput where
  l1ChainId := 1
  l1AssetRouter := 0x4000
  governance := 0x4444
  zkTokenAssetId := 0x5555
  forcedBeacon := 0
  baseTokenL1Address := 0x5000
  base := ⟨wConfigEnv.encNTV 1 0x5000, 1, 0x5000⟩

/-- A default upgrade with the genesis data except the L1 asset router, now `0x4001`. -/
def wRotateInput : UpgradeInput := { wGenesisInput with l1AssetRouter := 0x4001 }

/-- A default upgrade with the genesis ids and origin chain `270`. -/
def wFlipInput : UpgradeInput :=
  { wGenesisInput with base := ⟨wGenesisInput.base.assetId, 270, 0x5000⟩ }

/-- The run's five calls: the default upgrade, a registration of the native token `0x6000`, the
deployment of chain `324`'s token `0x7000` at `0x30000`, a counterpart write at `0x9999` and a
fallback write at `0x8888`. -/
def wConfigCalls : List ConfigCall :=
  [⟨0x8007, .upgrade (.default wRotateInput)⟩,
   ⟨0x7777, .vaultRegister 0x6000⟩,
   ⟨0x10003, .vaultDeploy (wConfigEnv.encNTV 324 0x7000) 324 0x7000 0x30000⟩,
   ⟨0x4001, .counterpartSet 1 0x9999 0x1234⟩,
   ⟨0x2222, .finalizeFallback 0x8888⟩]

lemma wGenesis_ok : configExec wConfigEnv wConfigEnv.forceDeployer ConfigWorld.fresh
    (.upgrade (.genesis 270 wGenesisInput)) = some (genesisPost wConfigEnv wGenesisInput) :=
  upgrade_eq_some.2 ⟨rfl, genesis_fresh_eq_some.2 ⟨by unfold GenesisInputOk; decide, rfl⟩⟩

lemma wGenesis_consistent :
    ConfigConsistent wConfigEnv 1 wGenesisInput.base.assetId 0x20000
      (genesisPost wConfigEnv wGenesisInput) :=
  (genesis_establishes (by decide) wGenesis_ok).2.1

/-- The final state of the run. -/
def wConfigFinal : ConfigWorld :=
  (((registerNative wConfigEnv (defaultPost wConfigEnv wRotateInput
        (genesisPost wConfigEnv wGenesisInput)) 0x6000).setNewTokenStorage
      (wConfigEnv.encNTV 324 0x7000) 0x30000 324).pointRoute 0x9999 0x1234).pointRoute
    0x8888 wConfigEnv.ntvAddr

lemma wConfig_run :
    ConfigRun wConfigEnv (genesisPost wConfigEnv wGenesisInput) wConfigCalls wConfigFinal := by
  have h1 := default_adopts (u := wRotateInput) wGenesis_consistent rfl rfl (by decide) (by decide)
  exact (((((ConfigRun.nil).snoc h1).snoc rfl).snoc rfl).snoc rfl).snoc rfl

/-! ## The named properties -/

theorem GenesisEstablishesConfigConsistent : Properties.GenesisEstablishesConfigConsistent :=
  fun _ _ _ _ _ hbt h => genesis_establishes hbt h

theorem GenesisEstablishesConfigConsistentWitness :
    Properties.GenesisEstablishesConfigConsistentWitness :=
  ⟨wConfigEnv, 270, wGenesisInput, _, by decide, wGenesis_ok, by decide, by decide, rfl⟩

theorem StepPreservesConfigConsistent : Properties.StepPreservesConfigConsistent :=
  fun _ _ _ _ _ _ _ hC hadm h => step_preserves hC hadm h

theorem DefaultUpgradeKeepsL1AndBaseIds : Properties.DefaultUpgradeKeepsL1AndBaseIds := by
  intro E l1 a weth w s u w' hC h
  obtain ⟨-, h⟩ := upgrade_eq_some.1 h
  obtain ⟨hl, ha, -⟩ := default_ids hC h
  exact ⟨hl, ha⟩

theorem DefaultUpgradeAdoptsAnyBaseOrigin : Properties.DefaultUpgradeAdoptsAnyBaseOrigin := by
  intro E l1 a weth w u hC hl ha hg hr
  refine ⟨defaultPost E u w, default_adopts hC hl ha hg hr, consistent_defaultPost hC hl ha,
    ⟨?_, rfl⟩, rfl⟩
  show upd w.vault.originChainId u.base.assetId u.base.originChainId a = u.base.originChainId
  rw [← ha, cfg_upd_self]

theorem GenesisRevertsOnConsistentState : Properties.GenesisRevertsOnConsistentState := by
  intro E l1 a weth w s c u hC
  simp only [configExec, runProgram, genesis_none_of_consistent hC, ite_self]

theorem BaseRouteMovesOnlyByCounterpart : Properties.BaseRouteMovesOnlyByCounterpart :=
  fun _ _ _ _ _ _ _ hC hR h hnc => base_route_stays hC hR h hnc

theorem OnlyUpgraderWritesScalarConfig : Properties.OnlyUpgraderWritesScalarConfig :=
  fun _ _ _ _ _ h hne => only_upgrader_writes_scalars h hne

theorem BaseEntriesWritersFromConsistent : Properties.BaseEntriesWritersFromConsistent :=
  fun _ _ _ _ _ _ _ _ hC h hne => base_entries_writers hC h hne

theorem ConfigConsistentAlongRuns : Properties.ConfigConsistentAlongRuns := by
  intro E s c u w0 cs w hbt h0 hrun hadm
  obtain ⟨-, hC0, hR0, -⟩ := genesis_establishes hbt h0
  obtain ⟨hC, hids, hroute⟩ := run_invariant hC0 hrun hadm
  exact ⟨hC, hids, hroute hR0⟩

theorem BaseOriginPinnedAlongRuns : Properties.BaseOriginPinnedAlongRuns := by
  intro E s c u w0 cs w hbt h0 hrun hadm hk
  obtain ⟨-, hC0, -, hO0⟩ := genesis_establishes hbt h0
  obtain ⟨hC, hO⟩ := run_origin hC0 hO0 hrun hadm hk
  refine ⟨hO, ?_⟩
  unfold BaseNativeHere
  rw [hC.vaultBase, hO.1]

theorem ConfigRunWitness : Properties.ConfigRunWitness := by
  refine ⟨wConfigEnv, 270, wGenesisInput, genesisPost wConfigEnv wGenesisInput, wConfigCalls,
    wConfigFinal, by decide, wGenesis_ok, wConfig_run, ?_, ?_, ?_,
    ⟨wRotateInput, List.Mem.head _, by decide⟩,
    ⟨0x7777, 0x6000, List.Mem.tail _ (List.Mem.head _)⟩,
    ⟨0x10003, wConfigEnv.encNTV 324 0x7000, 324, 0x7000, 0x30000,
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))⟩,
    ⟨0x4001, 1, 0x9999, 0x1234,
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))⟩,
    ⟨0x2222, 0x8888,
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))⟩,
    ?_⟩
  · intro c hc
    simp only [wConfigCalls, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun d hd => (by cases hd), fun t ht => (by cases ht)⟩
    · exact ⟨fun d hd => (by cases hd), fun t ht => (by cases ht; decide)⟩
    · exact ⟨fun d hd => (by cases hd), fun t ht => (by cases ht)⟩
    · exact ⟨fun d hd => (by cases hd), fun t ht => (by cases ht)⟩
    · exact ⟨fun d hd => (by cases hd), fun t ht => (by cases ht)⟩
  · intro c hc u hu
    simp only [wConfigCalls, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> cases hu
    exact ⟨rfl, rfl⟩
  · intro c hc
    simp only [wConfigCalls, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact id
    · exact id
    · exact id
    · show ¬ ((0x9999 : AssetId) = wGenesisInput.base.assetId)
      decide
    · exact id
  · intro h
    have := congrArg ScalarConfig.routerL1AssetRouter h
    revert this
    decide

theorem NoBaseFreezeLeavesTrackerOnOldBase : Properties.NoBaseFreezeLeavesTrackerOnOldBase :=
  fun _ _ _ _ _ _ hC hl ha hg hr => no_base_freeze hC hl ha hg hr

theorem NoL1FreezeLeavesTrackerOnOldL1 : Properties.NoL1FreezeLeavesTrackerOnOldL1 :=
  fun _ _ _ _ _ _ hC hl ha hg hr => no_l1_freeze hC hl ha hg hr

theorem SameBaseOriginRewriteFlipsNativeTest : Properties.SameBaseOriginRewriteFlipsNativeTest := by
  intro E l1 a weth w u hC _ hl ha ho hg hr
  obtain ⟨h1, h2, h3⟩ := origin_flip hC hl ha ho hg hr
  exact ⟨_, h1, h2, h3⟩

theorem RouterUpdateOutsideHelperDivergesBase :
    Properties.RouterUpdateOutsideHelperDivergesBase :=
  fun _ _ _ _ _ _ _ hC hr ha => router_outside_helper hC hr ha

theorem ConfigCountermodelWitness : Properties.ConfigCountermodelWitness := by
  refine ⟨wConfigEnv, 270, wGenesisInput, genesisPost wConfigEnv wGenesisInput, wGenesis_ok,
    wGenesis_consistent, ?_, ?_, ?_⟩
  · show ¬ (upd (fun _ => 0) wGenesisInput.base.assetId 1 wGenesisInput.base.assetId = 270)
    rw [cfg_upd_self]
    decide
  · obtain ⟨h1, -, h3⟩ := origin_flip (u := wFlipInput) wGenesis_consistent rfl rfl rfl
      (by decide) (by decide)
    refine ⟨wFlipInput, _, rfl, rfl, rfl, h1, ?_, h3⟩
    intro h
    have := congrArg (fun p => p.2.2.1) h
    simp only [ConfigWorld.baseEntries, defaultPost, genesisPost, cfg_upd_self] at this
    revert this
    decide
  · obtain ⟨w', h, hb, hv, -, -⟩ := router_outside_helper (r := 0x4000) (a' := 0x1111)
      wGenesis_consistent (by decide) (by decide)
    refine ⟨0x4000, 0x1111, w', h, ?_⟩
    rw [hb, hv]
    decide

end Contracts.L2BridgeConfig
