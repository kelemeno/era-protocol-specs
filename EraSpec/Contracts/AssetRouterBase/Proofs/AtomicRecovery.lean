import EraSpec.Contracts.AssetRouterBase.Properties.AtomicRecovery
import EraSpec.Contracts.AssetRouterBase.Proofs.HandlerRegistration
import EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryLimits
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.RegistryAndEscrow
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.RepresentationPreparation
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.ModelCorrespondence

/-!
# Proofs: what an atomic refund does with a bundle's asset-router calls

The vault's refund is one decision tree, and every statement is a walk down it.  An asset the
vault does not know falls through the two registered branches into the deploy branch, where
`assetIdCheck` is the only exit that does not revert (`vaultRefund_unaware`).  Every successful
branch writes the registry at most at the refunded asset (`vaultRefund_frame`), which is the
frame fact behind the bundle and run-level results.  The bundle results are one induction over
the call list (`recoverBundle_eq_none_of_blocking`), with "the vault does not know `a`" as the
invariant.
-/

namespace Contracts.AssetRouter.AtomicRecovery

open AttackVectors.RecoveryLimits (Outcome LegState LoopCompletes recoveredCount ClaimAccepted)

variable {X : Type}

/-! ## The vault's refund, branch by branch -/

/-- Step 1 rejects a nonzero value, any caller but the router, and a paused vault. -/
theorem vaultRefund_guard {enc : AssetIdOf} {cfg : Config} {hk : Hooks X}
    {V : NativeTokenVault.Vault} {paused : Bool} {x : X} {caller : Address} {v : UInt256}
    {chainId : Chain} {a : AssetId} {m : Option MintData}
    (h : v ≠ 0 ∨ caller ≠ cfg.router ∨ paused = true) :
    vaultRefund enc cfg hk V paused x caller v chainId a m = none := by
  unfold vaultRefund
  rw [ite_eq_left h]

/-- Past step 1, with decoded data and a tracker hook that returns. -/
theorem vaultRefund_some (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (V : NativeTokenVault.Vault) (paused : Bool) (x : X) (chainId : Chain) (a : AssetId)
    (md : MintData) (x₁ : X) (hp : paused = false)
    (hf : hk.fromChain x chainId a md.amount = some x₁) :
    vaultRefund enc cfg hk V paused x cfg.router 0 chainId a (some md) =
      if V.originChain a = cfg.thisChain then
        (hk.withdraw x₁ a md.originalCaller (V.token a) md.amount).map fun x₂ => (V, x₂)
      else if V.token a ≠ 0 then
        (hk.mint x₁ (V.token a) md.originalCaller md.amount).map fun x₂ => (V, x₂)
      else
        match cfg.tokenOrigin md.metadata with
        | none => none
        | some c =>
          if a ≠ ntvId enc cfg c (NativeTokenVaultBase.widen md.originToken) then none
          else if c = cfg.thisChain then none
          else
            match hk.deploy x₁ a md.originToken c with
            | none => none
            | some (x₂, tok) =>
              (hk.mint x₂ tok md.originalCaller md.amount).map fun x₃ =>
                (NativeTokenVault.registerBridged V a tok (NativeTokenVaultBase.widen md.originToken) c,
                  x₃) := by
  subst hp
  unfold vaultRefund
  rw [ite_eq_right (by simp)]
  dsimp only
  rw [hf]
  rfl

/-- **The vault rejects an asset it does not know.** -/
theorem vaultRefund_unaware {enc : AssetIdOf} {cfg : Config} {hk : Hooks X}
    {V : NativeTokenVault.Vault} {paused : Bool} {x : X} {caller : Address} {v : UInt256}
    {chainId : Chain} {a : AssetId} {m : Option MintData}
    (hU : VaultUnaware cfg V a) (hF : FailsAssetIdCheck enc cfg a m) :
    vaultRefund enc cfg hk V paused x caller v chainId a m = none := by
  obtain ⟨htok, hnat⟩ := hU
  unfold vaultRefund
  by_cases hg : v ≠ 0 ∨ caller ≠ cfg.router ∨ paused = true
  · rw [ite_eq_left hg]
  rw [ite_eq_right hg]
  rcases m with _ | md
  · rfl
  dsimp only
  rcases hk.fromChain x chainId a md.amount with _ | x₁
  · rfl
  dsimp only
  rw [ite_eq_right hnat, ite_eq_right (by simpa using htok)]
  rcases hc : cfg.tokenOrigin md.metadata with _ | c
  · rfl
  dsimp only
  rw [ite_eq_left (hF md rfl c hc)]

/-- **A successful refund writes the registry at most at the refunded asset.** -/
theorem vaultRefund_frame {enc : AssetIdOf} {cfg : Config} {hk : Hooks X}
    {V V' : NativeTokenVault.Vault} {paused : Bool} {x x' : X} {caller : Address} {v : UInt256}
    {chainId : Chain} {b : AssetId} {m : Option MintData} {a : AssetId} (hab : b ≠ a)
    (h : vaultRefund enc cfg hk V paused x caller v chainId b m = some (V', x')) :
    LeavesAlone a V V' := by
  unfold vaultRefund at h
  by_cases hg : v ≠ 0 ∨ caller ≠ cfg.router ∨ paused = true
  · rw [ite_eq_left hg] at h; cases h
  rw [ite_eq_right hg] at h
  rcases m with _ | md
  · cases h
  dsimp only at h
  rcases hf : hk.fromChain x chainId b md.amount with _ | x₁ <;> rw [hf] at h
  · cases h
  dsimp only at h
  by_cases hn : V.originChain b = cfg.thisChain
  · rw [ite_eq_left hn] at h
    rcases hw : hk.withdraw x₁ b md.originalCaller (V.token b) md.amount with _ | x₂ <;>
      rw [hw] at h
    · cases h
    · cases h; exact ⟨rfl, rfl⟩
  rw [ite_eq_right hn] at h
  by_cases ht : V.token b ≠ 0
  · rw [ite_eq_left ht] at h
    rcases hm : hk.mint x₁ (V.token b) md.originalCaller md.amount with _ | x₂ <;> rw [hm] at h
    · cases h
    · cases h; exact ⟨rfl, rfl⟩
  rw [ite_eq_right ht] at h
  rcases ho : cfg.tokenOrigin md.metadata with _ | c <;> rw [ho] at h
  · cases h
  dsimp only at h
  by_cases hid : b ≠ ntvId enc cfg c (NativeTokenVaultBase.widen md.originToken)
  · rw [ite_eq_left hid] at h; cases h
  rw [ite_eq_right hid] at h
  by_cases hc : c = cfg.thisChain
  · rw [ite_eq_left hc] at h; cases h
  rw [ite_eq_right hc] at h
  rcases hd : hk.deploy x₁ b md.originToken c with _ | ⟨x₂, tok⟩ <;> rw [hd] at h
  · cases h
  dsimp only at h
  rcases hm : hk.mint x₂ tok md.originalCaller md.amount with _ | x₃ <;> rw [hm] at h
  · cases h
  cases h
  exact ⟨NativeTokenVault.sn_token_of_ne _ _ _ _ _ (Ne.symm hab),
    NativeTokenVault.sn_originChain_of_ne _ _ _ _ _ (Ne.symm hab)⟩

/-! ## The vault's and the router's refund on a world -/

theorem ntvRecover_unaware {enc : AssetIdOf} {cfg : Config} {hk : Hooks X} {w : World X}
    {caller : Address} {v : UInt256} {chainId : Chain} {a : AssetId} {m : Option MintData}
    (hU : VaultUnaware cfg w.vault a) (hF : FailsAssetIdCheck enc cfg a m) :
    ntvRecover enc cfg hk w caller v chainId a m = none := by
  unfold ntvRecover
  rw [vaultRefund_unaware hU hF]
  rfl

theorem ntvRecover_frame {enc : AssetIdOf} {cfg : Config} {hk : Hooks X} {w w' : World X}
    {caller : Address} {v : UInt256} {chainId : Chain} {b : AssetId} {m : Option MintData}
    {a : AssetId} (hab : b ≠ a) (h : ntvRecover enc cfg hk w caller v chainId b m = some w') :
    LeavesAlone a w.vault w'.vault := by
  unfold ntvRecover at h
  obtain ⟨⟨V', x'⟩, hv, rfl⟩ := Option.map_eq_some_iff.mp h
  exact vaultRefund_frame hab hv

theorem ntvRecover_router (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (R : Router) (caller : Address) (v : UInt256) (chainId : Chain) (a : AssetId)
    (m : Option MintData) :
    ntvRecover enc cfg hk { w with router := R } caller v chainId a m
      = (ntvRecover enc cfg hk w caller v chainId a m).map (fun w' => { w' with router := R }) := by
  unfold ntvRecover
  rw [Option.map_map]
  rfl

/-- The manager's call of `recoverAtomicCall` on a `finalizeDeposit` is the vault's refund. -/
theorem recoverAtomicCall_finalize (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (dest src : Chain) (a : AssetId) (m : Option MintData) :
    recoverAtomicCall enc cfg hk w cfg.manager dest (.finalizeDeposit src a m)
      = (ntvRecover enc cfg hk w cfg.router 0 dest a m).map (fun w' => (w', true)) := by
  unfold recoverAtomicCall
  rw [ite_eq_right (by simp)]

theorem recoverAtomicCall_router (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (R : Router) (caller : Address) (dest : Chain) (d : CallData) :
    recoverAtomicCall enc cfg hk { w with router := R } caller dest d
      = (recoverAtomicCall enc cfg hk w caller dest d).map
          (fun p => ({ p.1 with router := R }, p.2)) := by
  unfold recoverAtomicCall
  by_cases hc : caller ≠ cfg.manager
  · rw [ite_eq_left hc, ite_eq_left hc]; rfl
  rw [ite_eq_right hc, ite_eq_right hc]
  rcases d with ⟨src, a, m⟩ | _ | _
  · dsimp only
    rw [ntvRecover_router, Option.map_map, Option.map_map]
    rfl
  · rfl
  · rfl

theorem recoverAtomicCall_unaware {enc : AssetIdOf} {cfg : Config} {hk : Hooks X} {w : World X}
    {dest src : Chain} {a : AssetId} {m : Option MintData}
    (hU : VaultUnaware cfg w.vault a) (hF : FailsAssetIdCheck enc cfg a m) :
    recoverAtomicCall enc cfg hk w cfg.manager dest (.finalizeDeposit src a m) = none := by
  rw [recoverAtomicCall_finalize, ntvRecover_unaware hU hF]
  rfl

/-- A `recoverAtomicCall` that returns, on data that is not a `finalizeDeposit` on `a`, leaves
`a` alone. -/
theorem recoverAtomicCall_frame {enc : AssetIdOf} {cfg : Config} {hk : Hooks X} {w w' : World X}
    {caller : Address} {dest : Chain} {d : CallData} {b : Bool} {a : AssetId}
    (hd : ∀ src m, d ≠ .finalizeDeposit src a m)
    (h : recoverAtomicCall enc cfg hk w caller dest d = some (w', b)) :
    LeavesAlone a w.vault w'.vault := by
  unfold recoverAtomicCall at h
  by_cases hc : caller ≠ cfg.manager
  · rw [ite_eq_left hc] at h; cases h
  rw [ite_eq_right hc] at h
  rcases d with ⟨src, a', m⟩ | _ | _
  · have hne : a' ≠ a := fun he => hd src m (by rw [he])
    obtain ⟨w'', hn, hp⟩ := Option.map_eq_some_iff.mp h
    cases hp
    exact ntvRecover_frame hne hn
  · cases h
  · cases h; exact ⟨rfl, rfl⟩

/-- The branch for a bridged asset the vault knows. -/
theorem recoverAtomicCall_known {enc : AssetIdOf} {cfg : Config} {hk : Hooks X} {w : World X}
    {dest src : Chain} {a : AssetId} {md : MintData} {x₁ : X}
    (hp : w.paused = false) (hn : w.vault.originChain a ≠ cfg.thisChain) (ht : w.vault.token a ≠ 0)
    (hf : hk.fromChain w.rest dest a md.amount = some x₁) :
    recoverAtomicCall enc cfg hk w cfg.manager dest (.finalizeDeposit src a (some md))
      = (hk.mint x₁ (w.vault.token a) md.originalCaller md.amount).map
          (fun x₂ => ({ w with rest := x₂ }, true)) := by
  rw [recoverAtomicCall_finalize]
  unfold ntvRecover
  rw [vaultRefund_some enc cfg hk w.vault w.paused w.rest dest a md x₁ hp hf, ite_eq_right hn,
    ite_eq_left ht]
  cases hk.mint x₁ (w.vault.token a) md.originalCaller md.amount <;> rfl

/-- The branch for an asset native to this chain. -/
theorem recoverAtomicCall_native {enc : AssetIdOf} {cfg : Config} {hk : Hooks X} {w : World X}
    {dest src : Chain} {a : AssetId} {md : MintData} {x₁ : X}
    (hp : w.paused = false) (hn : w.vault.originChain a = cfg.thisChain)
    (hf : hk.fromChain w.rest dest a md.amount = some x₁) :
    recoverAtomicCall enc cfg hk w cfg.manager dest (.finalizeDeposit src a (some md))
      = (hk.withdraw x₁ a md.originalCaller (w.vault.token a) md.amount).map
          (fun x₂ => ({ w with rest := x₂ }, true)) := by
  rw [recoverAtomicCall_finalize]
  unfold ntvRecover
  rw [vaultRefund_some enc cfg hk w.vault w.paused w.rest dest a md x₁ hp hf, ite_eq_left hn]
  cases hk.withdraw x₁ a md.originalCaller (w.vault.token a) md.amount <;> rfl

/-! ## Registry runs -/

theorem leavesAlone_unaware {cfg : Config} {V V' : NativeTokenVault.Vault} {a : AssetId}
    (hU : VaultUnaware cfg V a) (h : LeavesAlone a V V') : VaultUnaware cfg V' a :=
  ⟨h.1.trans hU.1, h.2 ▸ hU.2⟩

theorem leavesAlone_refl (a : AssetId) (V : NativeTokenVault.Vault) : LeavesAlone a V V :=
  ⟨rfl, rfl⟩

theorem leavesAlone_trans {a : AssetId} {V₁ V₂ V₃ : NativeTokenVault.Vault}
    (h₁ : LeavesAlone a V₁ V₂) (h₂ : LeavesAlone a V₂ V₃) : LeavesAlone a V₁ V₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

theorem vaultStep_leavesAlone {enc : AssetIdOf} {cfg : Config} {o : NativeTokenVault.Op}
    {W W' : NativeTokenVault.World} {a : AssetId}
    (hs : NativeTokenVault.StepOp (ntvId enc cfg) cfg.thisChain o W W')
    (hp : ∀ p, o.pair cfg.thisChain = some p → ntvId enc cfg p.1 p.2 ≠ a) :
    LeavesAlone a W.vault W'.vault := by
  cases hs with
  | @registerNative W t _ =>
    have hne : a ≠ ntvId enc cfg cfg.thisChain t := fun he => hp _ rfl he.symm
    exact ⟨NativeTokenVault.sn_token_of_ne _ _ _ _ _ hne,
      NativeTokenVault.sn_originChain_of_ne _ _ _ _ _ hne⟩
  | @registerBridged W a' t ot origin hg =>
    have hne : a ≠ a' := by
      rw [hg.idChecked]
      exact fun he => hp _ rfl he.symm
    exact ⟨NativeTokenVault.sn_token_of_ne _ _ _ _ _ hne,
      NativeTokenVault.sn_originChain_of_ne _ _ _ _ _ hne⟩
  | @bridgeOut W c b amt _ =>
    exact ⟨congrFun (NativeTokenVault.bridgeOut_token cfg.thisChain W c b amt) a,
      congrFun (NativeTokenVault.bridgeOut_originChain cfg.thisChain W c b amt) a⟩
  | @bridgeIn W c b amt _ =>
    exact ⟨congrFun (NativeTokenVault.bridgeIn_token cfg.thisChain W c b amt) a,
      congrFun (NativeTokenVault.bridgeIn_originChain cfg.thisChain W c b amt) a⟩
  | @donate W b amt => exact ⟨rfl, rfl⟩

/-- Injectivity on the custom triple and an NTV triple separates the two ids. -/
theorem custom_ne_ntv {enc : AssetIdOf} {cfg : Config} {c₀ : Chain} {s : Address}
    {d : AssetData} {c : Chain} {t : Address} (hs : s ≠ cfg.ntv)
    (hinj : IdInjOn enc {(c₀, s, d), (c, cfg.ntv, t)}) :
    enc c₀ s d ≠ ntvId enc cfg c t := by
  intro he
  have := hinj _ (Set.mem_insert _ _) _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)) he
  exact hs (congrArg (fun p => p.2.1) this)

theorem customId_unknown_along {enc : AssetIdOf} {cfg : Config} {c₀ : Chain} {s : Address}
    {d : AssetData} (hc : cfg.thisChain ≠ 0) (hs : s ≠ cfg.ntv) :
    ∀ {W : NativeTokenVault.World} {log : List NativeTokenVault.Op},
      NativeTokenVault.ReachLog (ntvId enc cfg) cfg.thisChain NativeTokenVault.empty W log →
      (∀ p ∈ NativeTokenVault.registeredPairs cfg.thisChain log,
        IdInjOn enc {(c₀, s, d), (p.1, cfg.ntv, p.2)}) →
      VaultUnaware cfg W.vault (enc c₀ s d) := by
  intro W log hr
  induction hr with
  | refl => intro _; exact ⟨rfl, fun h => hc h.symm⟩
  | @tail X' Y log' o _ hstep ih =>
    intro hinj
    have hsub : ∀ p ∈ NativeTokenVault.registeredPairs cfg.thisChain log',
        p ∈ NativeTokenVault.registeredPairs cfg.thisChain (log' ++ [o]) := by
      intro p hp
      obtain ⟨o', ho', hpo⟩ := (NativeTokenVault.MemRegisteredPairs cfg.thisChain log' p).mp hp
      exact (NativeTokenVault.MemRegisteredPairs cfg.thisChain _ p).mpr
        ⟨o', List.mem_append_left _ ho', hpo⟩
    have hU := ih (fun p hp => hinj p (hsub p hp))
    refine leavesAlone_unaware hU (vaultStep_leavesAlone hstep ?_)
    intro p hp he
    have hmem : p ∈ NativeTokenVault.registeredPairs cfg.thisChain (log' ++ [o]) :=
      (NativeTokenVault.MemRegisteredPairs cfg.thisChain _ p).mpr
        ⟨o, List.mem_append_right _ List.mem_cons_self, hp⟩
    exact custom_ne_ntv hs (hinj p hmem) he.symm

/-! ## The refund loop -/

/-- **The loop with a blocking call reverts.**  If an invariant is kept by every successful call
of the bundle, and some call of the bundle reverts in every state satisfying it, the loop
reverts. -/
theorem recoverBundle_eq_none_of_blocking {step : World X → Call → Option (World X × Bool)}
    (Inv : World X → Prop) (Blocks : Call → Prop) :
    ∀ (calls : List Call) (w : World X),
      (∀ c ∈ calls, ∀ u u' b, Inv u → step u c = some (u', b) → Inv u') →
      (∀ c ∈ calls, Blocks c → ∀ u, Inv u → step u c = none) →
      (∃ c ∈ calls, Blocks c) → Inv w → recoverBundle step w calls = none
  | [], _, _, _, ⟨_, hc, _⟩, _ => absurd hc List.not_mem_nil
  | c :: cs, w, hpres, hblock, ⟨c', hc', hb'⟩, hw => by
    unfold recoverBundle
    by_cases hcb : Blocks c
    · rw [hblock c List.mem_cons_self hcb w hw]
    rcases hs : step w c with _ | ⟨w', b⟩
    · rfl
    dsimp only
    have hw' := hpres c List.mem_cons_self w w' b hw hs
    have hex : ∃ c ∈ cs, Blocks c := by
      rcases List.mem_cons.mp hc' with rfl | h
      · exact absurd hb' hcb
      · exact ⟨c', h, hb'⟩
    rw [recoverBundle_eq_none_of_blocking Inv Blocks cs w'
      (fun c hc => hpres c (List.mem_cons_of_mem _ hc))
      (fun c hc => hblock c (List.mem_cons_of_mem _ hc)) hex hw']

/-- **A loop whose every call leaves `a` alone leaves `a` alone.** -/
theorem recoverBundle_leavesAlone {step : World X → Call → Option (World X × Bool)}
    {a : AssetId} :
    ∀ (calls : List Call) (w w' : World X) (n : ℕ),
      (∀ c ∈ calls, ∀ u u' b, step u c = some (u', b) → LeavesAlone a u.vault u'.vault) →
      recoverBundle step w calls = some (w', n) → LeavesAlone a w.vault w'.vault
  | [], w, w', n, _, h => by
    unfold recoverBundle at h
    cases h
    exact leavesAlone_refl _ _
  | c :: cs, w, w', n, hstep, h => by
    unfold recoverBundle at h
    rcases hs : step w c with _ | ⟨w₁, b⟩ <;> rw [hs] at h
    · cases h
    dsimp only at h
    rcases hr : recoverBundle step w₁ cs with _ | ⟨w₂, k⟩ <;> rw [hr] at h
    · cases h
    dsimp only at h
    have hw : w₂ = w' := (Prod.mk.inj (Option.some.inj h)).1
    rw [← hw]
    exact leavesAlone_trans (hstep c List.mem_cons_self w w₁ b hs)
      (recoverBundle_leavesAlone cs w₁ w₂ k (fun c hc => hstep c (List.mem_cons_of_mem _ hc)) hr)

/-- One router call: a call on `a` reverts, any other successful call leaves `a` alone. -/
theorem recoverCall_frame {enc : AssetIdOf} {cfg : Config} {hk : Hooks X}
    {other : Address → World X → Chain → CallData → Option (World X × Bool)} {dest : Chain}
    {a : AssetId} (ho : OthersLeaveAlone a other) {c : Call}
    (hc : c.target = cfg.router → ∀ src m, c.data ≠ .finalizeDeposit src a m)
    {u u' : World X} {b : Bool} (h : recoverCall enc cfg hk other dest u c = some (u', b)) :
    LeavesAlone a u.vault u'.vault := by
  unfold recoverCall at h
  by_cases ht : c.target = cfg.router
  · rw [ite_eq_left ht] at h
    exact recoverAtomicCall_frame (hc ht) h
  · rw [ite_eq_right ht] at h
    exact ho _ _ _ _ _ _ h

theorem claimRefund_eq_none {step : World X → Call → Option (World X × Bool)} {st : LegState}
    {w : World X} {calls : List Call} (h : recoverBundle step w calls = none) :
    claimRefund step st w calls = none := by
  unfold claimRefund
  split_ifs
  · rfl
  · rw [h]

theorem claimRevertsWithUnknownAssetCall {enc : AssetIdOf} {cfg : Config} {hk : Hooks X}
    {other : Address → World X → Chain → CallData → Option (World X × Bool)} {dest : Chain}
    {w : World X} {st : LegState} {calls : List Call} {a : AssetId}
    (hU : VaultUnaware cfg w.vault a) (ho : OthersLeaveAlone a other)
    (hhas : HasRouterCallOn cfg a calls) (hfail : RouterCallsOnFail enc cfg a calls) :
    claimRefund (recoverCall enc cfg hk other dest) st w calls = none := by
  apply claimRefund_eq_none
  refine recoverBundle_eq_none_of_blocking (fun u => VaultUnaware cfg u.vault a)
    (fun c => c.target = cfg.router ∧ ∃ src m, c.data = .finalizeDeposit src a m)
    calls w ?_ ?_ ?_ hU
  · intro c hc u u' b hu hs
    by_cases hon : c.target = cfg.router ∧ ∃ src m, c.data = .finalizeDeposit src a m
    · obtain ⟨ht, src, m, hd⟩ := hon
      have hnone : recoverCall enc cfg hk other dest u c = none := by
        unfold recoverCall
        rw [ite_eq_left ht, hd]
        exact recoverAtomicCall_unaware hu (hfail c hc ht src m hd)
      rw [hnone] at hs
      cases hs
    · refine leavesAlone_unaware hu (recoverCall_frame ho ?_ hs)
      intro ht src m hd
      exact hon ⟨ht, src, m, hd⟩
  · rintro c hc ⟨ht, src, m, hd⟩ u hu
    unfold recoverCall
    rw [ite_eq_left ht, hd]
    exact recoverAtomicCall_unaware hu (hfail c hc ht src m hd)
  · obtain ⟨c, hc, ht, src, m, hd⟩ := hhas
    exact ⟨c, hc, ht, src, m, hd⟩

/-! ## The loop is `RecoveryLimits`' acceptance rule -/

theorem recoverBundle_some_outcomes {step : World X → Call → Option (World X × Bool)} :
    ∀ (calls : List Call) (w w' : World X) (n : ℕ), recoverBundle step w calls = some (w', n) →
      LoopCompletes (outcomes step w calls) ∧ recoveredCount (outcomes step w calls) = n
  | [], w, w', n, h => by
    unfold recoverBundle at h
    cases h
    exact ⟨List.not_mem_nil, rfl⟩
  | c :: cs, w, w', n, h => by
    unfold recoverBundle at h
    rcases hs : step w c with _ | ⟨w₁, b⟩ <;> rw [hs] at h
    · cases h
    dsimp only at h
    rcases hr : recoverBundle step w₁ cs with _ | ⟨w₂, k⟩ <;> rw [hr] at h
    · cases h
    dsimp only at h
    have hn : (if b then 1 else 0) + k = n := (Prod.mk.inj (Option.some.inj h)).2
    subst hn
    obtain ⟨hl, hk⟩ := recoverBundle_some_outcomes cs w₁ w₂ k hr
    unfold outcomes
    rw [hs]
    dsimp only
    refine ⟨?_, ?_⟩
    · intro hm
      rcases List.mem_cons.mp hm with he | hm
      · cases b <;> simp at he
      · exact hl hm
    · cases b <;> simp [recoveredCount] at hk ⊢ <;> omega

theorem recoverBundle_none_outcomes {step : World X → Call → Option (World X × Bool)} :
    ∀ (calls : List Call) (w : World X), recoverBundle step w calls = none →
      ¬ LoopCompletes (outcomes step w calls)
  | [], w, h => by unfold recoverBundle at h; cases h
  | c :: cs, w, h => by
    unfold recoverBundle at h
    unfold outcomes
    rcases hs : step w c with _ | ⟨w₁, b⟩ <;> rw [hs] at h
    · dsimp only
      exact fun hl => hl List.mem_cons_self
    dsimp only at h ⊢
    rcases hr : recoverBundle step w₁ cs with _ | ⟨w₂, k⟩ <;> rw [hr] at h
    · intro hl
      exact recoverBundle_none_outcomes cs w₁ hr (fun hm => hl (List.mem_cons_of_mem _ hm))
    · cases h

theorem claimSucceedsIffAccepted (step : World X → Call → Option (World X × Bool)) (w : World X)
    (calls : List Call) :
    (claimRefund step LegState.Revertable w calls).isSome = true ↔
      ClaimAccepted (outcomes step w calls) := by
  unfold claimRefund
  rw [ite_eq_right (by simp)]
  rcases hr : recoverBundle step w calls with _ | ⟨w', n⟩
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact fun hacc => recoverBundle_none_outcomes calls w hr hacc.1
  · obtain ⟨hl, hc⟩ := recoverBundle_some_outcomes calls w w' n hr
    dsimp only
    constructor
    · intro hs
      refine ⟨hl, ?_⟩
      rw [hc]
      intro h0
      rw [ite_eq_left h0] at hs
      cases hs
    · rintro ⟨-, hn⟩
      rw [hc] at hn
      rw [ite_eq_right hn]
      rfl

/-! ## Certificates -/

theorem BurnUsesRegisteredHandler : Properties.BurnUsesRegisteredHandler := by
  intro cfg R a h
  unfold burnHandler
  rw [ite_eq_right h]

theorem VaultRejectsUnknownAsset : Properties.VaultRejectsUnknownAsset :=
  fun _ _ _ _ _ _ _ _ _ _ hU hF => ntvRecover_unaware hU hF

theorem CustomIdFailsAssetIdCheckOn : Properties.CustomIdFailsAssetIdCheckOn := by
  intro enc cfg c₀ s d m hs hinj md hm c hc
  exact custom_ne_ntv hs (hinj md hm c hc)

theorem VaultStepLeavesAlone : Properties.VaultStepLeavesAlone :=
  fun _ _ _ _ _ _ hs hp => vaultStep_leavesAlone hs hp

theorem CustomIdUnknownAlongLoggedRunsOn : Properties.CustomIdUnknownAlongLoggedRunsOn :=
  fun _ _ _ _ _ _ _ hc hs hr hinj => customId_unknown_along hc hs hr hinj

theorem VaultRefundOnlyByRouter : Properties.VaultRefundOnlyByRouter := by
  intro X enc cfg hk w caller v chainId a m h
  unfold ntvRecover
  rw [vaultRefund_guard (Or.inr (Or.inl h))]
  rfl

theorem VaultRefundRefinesResolution : Properties.VaultRefundRefinesResolution := by
  intro Accounting enc cfg rh s V c hR hC hO hT hReg
  obtain ⟨_, _, hne, _, htok⟩ := hReg
  have hguard : (c.msgValue ≠ 0 ∨ NativeTokenVaultBase.widen c.caller ≠ cfg.router ∨
      s.paused = true) ↔ ¬ NativeTokenVaultBase.ResolveEntryAllowed s c := by
    unfold NativeTokenVaultBase.ResolveEntryAllowed
    rw [hR]
    have hw : NativeTokenVaultBase.widen c.caller ≠ NativeTokenVaultBase.widen s.config.router ↔
        c.caller ≠ s.config.router := by rw [Ne, NativeTokenVaultBase.widen_inj]
    rw [hw]
    cases s.paused <;> simp
    tauto
  unfold vaultRefund NativeTokenVaultBase.bridgeRecoverFailedTransfer
  by_cases hE : NativeTokenVaultBase.ResolveEntryAllowed s c
  · have hng : ¬ (c.msgValue ≠ 0 ∨ NativeTokenVaultBase.widen c.caller ≠ cfg.router ∨
        s.paused = true) := fun h => (hguard.mp h) hE
    have hnat : ¬ V.originChain c.assetId = cfg.thisChain := by rw [hO, hC]; exact hne
    have htk : V.token c.assetId ≠ 0 := by
      rw [hT, Ne, NativeTokenVaultBase.widen_eq_zero]; exact htok
    rw [ite_eq_right hng, ite_eq_left ⟨hE, ⟨‹_›, ‹_›, hne, ‹_›, htok⟩⟩]
    simp only [resolutionHooks, NativeTokenVaultBase.hookThenMint]
    rcases h1 : rh.fromChain s.accounting s.token c.chain c.assetId c.data.amount with _ | acc
    · simp
    · simp only [Option.map_some, ite_eq_right hnat, ite_eq_left htk]
      rcases h2 : BridgedStandardERC20.mint s.token s.config.vault c.data.originalCaller
          c.data.amount with _ | t
      · simp
      · simp
  · rw [ite_eq_left (hguard.mpr hE), ite_eq_right (fun h => hE h.1)]
    rfl

/-! ## Concrete instances

Chain `7`; router `3`, vault `4`, manager `5`; every metadata decodes to origin chain `1`.
Under `wEnc` every id hashed from the vault is `1` and every other id is `2`, so `wEnc` is
injective on any pair of one vault triple and one other triple.  The vault has registered one
bridged asset, `1` (origin chain `1`, origin token `9`, local token `6`); asset `2` has the
custom handler `11`. -/

def wCfg : Config := ⟨7, 3, 4, 5, fun _ => some 1⟩

def wEnc : AssetIdOf := fun _ s _ => if s = 4 then 1 else 2

/-- Hooks that always return; the deploy hook returns token `6`. -/
def okHooks : Hooks Unit :=
  ⟨fun x _ _ _ => some x, fun x _ _ _ _ => some x, fun x _ _ _ => some (x, 6), fun x _ _ _ => some x⟩

/-- Original caller `11`, remote receiver `12`, origin token `9`, amount `1`. -/
def wMd : MintData := ⟨11, 12, 9, 1, []⟩

def wOp : NativeTokenVault.Op := .registerBridged 1 6 9 1

def wVault : NativeTokenVault.Vault :=
  NativeTokenVault.registerBridged NativeTokenVault.empty.vault 1 6 9 1

/-- The custom handler `11` for asset `2`, the vault for asset `1`. -/
def wRouter : Router := ⟨fun a => if a = 2 then 11 else if a = 1 then 4 else 0, fun _ => 0⟩

def wWorld : World Unit := ⟨wRouter, wVault, false, ()⟩

/-- Targets other than the router return `false` and change nothing. -/
def declineOther {X : Type} : Address → World X → Chain → CallData → Option (World X × Bool) :=
  fun _ w _ _ => some (w, false)

theorem wEnc_custom_ne_vault (c₀ c : Chain) (d t : AssetData) : wEnc c₀ 9 d ≠ wEnc c 4 t := by
  unfold wEnc; decide

theorem wEnc_injOn (c₀ c : Chain) (d t : AssetData) :
    IdInjOn wEnc {(c₀, (9 : Address), d), (c, (4 : Address), t)} :=
  idInjOn_pair (wEnc_custom_ne_vault c₀ c d t)

theorem wVault_token_one : wVault.token 1 = 6 := NativeTokenVault.sn_token_self _ _ _ _ _

theorem wVault_origin_one : wVault.originChain 1 = 1 := NativeTokenVault.sn_originChain_self _ _ _ _ _

theorem wVault_origin_two : wVault.originChain 2 = 0 :=
  NativeTokenVault.sn_originChain_of_ne NativeTokenVault.empty.vault 1 6 9 1 (by decide)

theorem wVault_unaware_two : VaultUnaware wCfg wVault 2 :=
  ⟨NativeTokenVault.sn_token_of_ne _ _ _ _ _ (by decide),
    by rw [wVault_origin_two]; decide⟩

theorem wVault_known_one : wVault.originChain 1 ≠ wCfg.thisChain ∧ wVault.token 1 ≠ 0 := by
  rw [wVault_origin_one, wVault_token_one]; decide

theorem wFails (m : Option MintData) : FailsAssetIdCheck wEnc wCfg 2 m := by
  intro md _ c _
  show (2 : AssetId) ≠ wEnc c 4 _
  unfold wEnc; decide

theorem wReach : NativeTokenVault.ReachLog (ntvId wEnc wCfg) wCfg.thisChain NativeTokenVault.empty
    ⟨wVault, NativeTokenVault.empty.audit⟩ [wOp] := by
  have hg : NativeTokenVault.RegisterBridgedGuard (ntvId wEnc wCfg) wCfg.thisChain
      NativeTokenVault.empty.vault 1 6 9 1 :=
    ⟨by decide, by decide, by unfold ntvId wEnc; decide, by decide, rfl, fun h => h rfl⟩
  exact NativeTokenVault.ReachLog.tail NativeTokenVault.ReachLog.refl
    (NativeTokenVault.StepOp.registerBridged hg)

theorem wBundleFails : RouterCallsOnFail wEnc wCfg 2 [routerCall wCfg 2 wMd, routerCall wCfg 1 wMd] := by
  intro c hc _ src m hd
  exact wFails m

theorem wBundleHas : HasRouterCallOn wCfg 2 [routerCall wCfg 2 wMd, routerCall wCfg 1 wMd] :=
  ⟨routerCall wCfg 2 wMd, List.mem_cons_self, rfl, 7, some wMd, rfl⟩

theorem declineOther_leaves (a : AssetId) {X : Type} :
    OthersLeaveAlone a (declineOther (X := X)) := by
  intro _ _ _ _ _ _ h; cases h; exact ⟨rfl, rfl⟩

theorem wEnc_custom : wEnc 0 9 0 = 2 := by unfold wEnc; decide

/-- An encoding under which every id is `2`. -/
def cEnc : AssetIdOf := fun _ _ _ => 2

/-- The vault with token `6` registered as native. -/
def nVault : NativeTokenVault.Vault :=
  NativeTokenVault.registerNative (ntvId wEnc wCfg) 7 NativeTokenVault.empty.vault 6

/-- The vault with asset `2 + 1` bridged (local token `6`, origin token `9`, origin chain `1`). -/
def pVault : NativeTokenVault.Vault :=
  NativeTokenVault.setNewTokenStorage NativeTokenVault.empty.vault (2 + 1) 6 9 1

/-- The bridged token's ledger: the mint hook credits the receiver. -/
def ledgerHooks : Hooks (Addr160 → ℕ) :=
  ⟨fun x _ _ _ => some x, fun x _ _ _ _ => some x, fun x _ _ _ => some (x, 6),
    fun bal _ rcv amt => some (Function.update bal rcv (bal rcv + amt.val))⟩

def ledgerWorld : World (Addr160 → ℕ) := ⟨wRouter, wVault, false, fun _ => 0⟩

end Contracts.AssetRouter.AtomicRecovery
