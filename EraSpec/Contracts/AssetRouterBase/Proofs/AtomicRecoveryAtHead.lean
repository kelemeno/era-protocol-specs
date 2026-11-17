import EraSpec.Contracts.AssetRouterBase.Properties.AtomicRecoveryAtHead
import EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecovery
import EraSpec.Contracts.AssetRouterBase.Proofs.AllWriters

/-!
# Proofs: atomic recovery at head

The head loop is the pin's loop with a different dispatch key and no acceptance threshold, so the
proofs are walks down `recoverCallAtHead` (sender, then value), `recoverAtomicCallAtHead` (manager, L1,
selector, handler) and `handlerRecover` (vault or code), plus one induction over the call list for
the bundle results.  The routing headline is an induction over the writers' run, one case per writer
(`astep_keeps_handler`).  The concrete instances reuse the pin model's witness setting.
-/

namespace Contracts.AssetRouter.AtomicRecoveryAtHead

open AttackVectors.RecoveryLimits (Outcome LegState LoopCompletes claimEnabled)

variable {X : Type}

/-! ## The vault's refund, as the head code calls it -/

/-- The vault's refund never writes the router's maps. -/
theorem ntvRecover_router {enc : AssetIdOf} {cfg : AtomicRecovery.Config}
    {hk : AtomicRecovery.Hooks X} {w w' : World X} {caller : Address} {v : UInt256}
    {chainId : Chain} {a : AssetId} {m : Option MintData}
    (h : AtomicRecovery.ntvRecover enc cfg hk w caller v chainId a m = some w') :
    w'.router = w.router := by
  unfold AtomicRecovery.ntvRecover at h
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.mp h
  rfl

/-- The vault's refund of a bridged asset it knows: the token's `bridgeMint` to `originalCaller`. -/
theorem ntvRecover_known {enc : AssetIdOf} {cfg : AtomicRecovery.Config}
    {hk : AtomicRecovery.Hooks X} {w : World X} {dest : Chain} {a : AssetId} {md : MintData}
    {x₁ : X} (hp : w.paused = false) (hn : w.vault.originChain a ≠ cfg.thisChain)
    (ht : w.vault.token a ≠ 0) (hf : hk.fromChain w.rest dest a md.amount = some x₁) :
    AtomicRecovery.ntvRecover enc cfg hk w cfg.router 0 dest a (some md)
      = (hk.mint x₁ (w.vault.token a) md.originalCaller md.amount).map
          (fun x₂ => { w with rest := x₂ }) := by
  unfold AtomicRecovery.ntvRecover
  rw [AtomicRecovery.vaultRefund_some enc cfg hk w.vault w.paused w.rest dest a md x₁ hp hf,
    ite_eq_right hn, ite_eq_left ht]
  cases hk.mint x₁ (w.vault.token a) md.originalCaller md.amount <;> rfl

/-- Off the chain's own base token and off L1, the head vault refund is the pin's. -/
theorem vaultRecoverAtHead_offBase {enc : AssetIdOf} {cfg : HeadConfig} {hk : HeadHooks X}
    {w : World X} {caller : Address} {v : UInt256} {chainId : Chain} {a : AssetId}
    {m : Option MintData} (hd : chainId ≠ cfg.l1Chain) (ha : a ≠ cfg.baseAsset) :
    vaultRecoverAtHead enc cfg hk w caller v chainId a m
      = AtomicRecovery.ntvRecover enc cfg.toConfig hk.toHooks w caller v chainId a m := by
  unfold vaultRecoverAtHead
  by_cases hg : v ≠ 0 ∨ caller ≠ cfg.router ∨ w.paused = true
  · rw [ite_eq_left hg]
    unfold AtomicRecovery.ntvRecover AtomicRecovery.vaultRefund
    rw [ite_eq_left hg]
    rfl
  · rw [ite_eq_right hg]
    cases m with
    | none =>
      unfold AtomicRecovery.ntvRecover AtomicRecovery.vaultRefund
      rw [ite_eq_right hg]
      rfl
    | some md =>
      dsimp only
      rw [ite_eq_right hd, ite_eq_right ha]

/-- On the chain's own base token, called by the router with no value, unpaused, off L1. -/
theorem vaultRecoverAtHead_base {enc : AssetIdOf} {cfg : HeadConfig} {hk : HeadHooks X}
    {w : World X} {chainId : Chain} {md : MintData} (hd : chainId ≠ cfg.l1Chain)
    (hp : w.paused = false) :
    vaultRecoverAtHead enc cfg hk w cfg.router 0 chainId cfg.baseAsset (some md)
      = if w.vault.originChain cfg.baseAsset = cfg.thisChain then none
        else (hk.recoverBase w.rest md.originalCaller md.amount chainId).map
          (fun x => { w with rest := x }) := by
  unfold vaultRecoverAtHead
  rw [ite_eq_right (by simp [hp])]
  dsimp only
  rw [ite_eq_right hd, ite_eq_left rfl]

/-- The head vault refund never writes the router's maps. -/
theorem vaultRecoverAtHead_router {enc : AssetIdOf} {cfg : HeadConfig} {hk : HeadHooks X}
    {w w' : World X} {caller : Address} {v : UInt256} {chainId : Chain} {a : AssetId}
    {m : Option MintData} (h : vaultRecoverAtHead enc cfg hk w caller v chainId a m = some w') :
    w'.router = w.router := by
  unfold vaultRecoverAtHead at h
  by_cases hg : v ≠ 0 ∨ caller ≠ cfg.router ∨ w.paused = true
  · rw [ite_eq_left hg] at h
    cases h
  rw [ite_eq_right hg] at h
  cases m with
  | none =>
    dsimp only at h
    cases h
  | some md =>
    dsimp only at h
    by_cases hd : chainId = cfg.l1Chain
    · rw [ite_eq_left hd] at h
      cases h
    rw [ite_eq_right hd] at h
    by_cases ha : a = cfg.baseAsset
    · rw [ite_eq_left ha] at h
      by_cases hn : w.vault.originChain a = cfg.thisChain
      · rw [ite_eq_left hn] at h
        cases h
      rw [ite_eq_right hn] at h
      obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.mp h
      rfl
    · rw [ite_eq_right ha] at h
      exact ntvRecover_router h

theorem handlerRecover_ntv (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (w : World X) (chainId : Chain) (a : AssetId) (data : Bytes) :
    handlerRecover enc cfg hk code cfg.ntv w chainId a data
      = vaultRecoverAtHead enc cfg hk w cfg.router 0 chainId a (cfg.decodeMint data) := by
  unfold handlerRecover
  rw [ite_eq_left rfl]

theorem handlerRecover_other {enc : AssetIdOf} {cfg : HeadConfig} {hk : HeadHooks X}
    {code : HandlerCode X} {h : Address} {w : World X} {chainId : Chain} {a : AssetId}
    {data : Bytes} (hh : h ≠ cfg.ntv) :
    handlerRecover enc cfg hk code h w chainId a data = code h w chainId a data := by
  unfold handlerRecover
  rw [ite_eq_right hh]

/-! ## The router's refund -/

theorem recoverAtomicCallAtHead_finalize {enc : AssetIdOf} {cfg : HeadConfig}
    {hk : HeadHooks X} {code : HandlerCode X} {w : World X} {dest src : Chain}
    {a : AssetId} {data : Bytes} (hd : dest ≠ cfg.l1Chain) :
    recoverAtomicCallAtHead enc cfg hk code w cfg.manager dest (.finalizeDeposit src a data)
      = if w.router.handler a = 0 then none
        else (handlerRecover enc cfg hk code (w.router.handler a) w dest a data).map
          (fun w' => (w', true)) := by
  unfold recoverAtomicCallAtHead
  rw [ite_eq_right (by simp), ite_eq_right hd]

theorem recoverAtomicCallAtHead_other {enc : AssetIdOf} {cfg : HeadConfig}
    {hk : HeadHooks X} {code : HandlerCode X} {w : World X} {dest : Chain}
    (hd : dest ≠ cfg.l1Chain) :
    recoverAtomicCallAtHead enc cfg hk code w cfg.manager dest .other = some (w, false) := by
  unfold recoverAtomicCallAtHead
  rw [ite_eq_right (by simp), ite_eq_right hd]

theorem bridgehubRecoverBaseTokenAtHead_manager {enc : AssetIdOf} {cfg : HeadConfig}
    {hk : HeadHooks X} {w : World X} {chainId : Chain} {a : AssetId}
    {receiver : Address} {amount : UInt256} (hd : chainId ≠ cfg.l1Chain) :
    bridgehubRecoverBaseTokenAtHead enc cfg hk w cfg.manager chainId a receiver amount
      = vaultRecoverAtHead enc cfg hk w cfg.router 0 chainId a
          (some (baseRefundMint receiver amount)) := by
  unfold bridgehubRecoverBaseTokenAtHead
  rw [ite_eq_right (by simp), ite_eq_right hd]

/-! ## One iteration of the manager's loop -/

theorem recoverCallAtHead_routerCall (enc : AssetIdOf) (cfg : HeadConfig)
    (hk : HeadHooks X) (code : HandlerCode X) (dest : Chain) (base : AssetId)
    (w : World X) (a : AssetId) (mintBytes : Bytes) :
    recoverCallAtHead enc cfg hk code dest base w (routerCallAtHead cfg a mintBytes)
      = recoverAtomicCallAtHead enc cfg hk code w cfg.manager dest
          (.finalizeDeposit cfg.thisChain a mintBytes) := by
  unfold recoverCallAtHead routerCallAtHead
  rw [ite_eq_left rfl]

theorem recoverCallAtHead_fromRouter {enc : AssetIdOf} {cfg : HeadConfig}
    {hk : HeadHooks X} {code : HandlerCode X} {dest : Chain} {base : AssetId}
    {w : World X} {c : HeadCall} (hs : c.sender = cfg.router) :
    recoverCallAtHead enc cfg hk code dest base w c
      = recoverAtomicCallAtHead enc cfg hk code w cfg.manager dest c.data := by
  unfold recoverCallAtHead
  rw [ite_eq_left hs]

theorem recoverCallAtHead_direct {enc : AssetIdOf} {cfg : HeadConfig}
    {hk : HeadHooks X} {code : HandlerCode X} {dest : Chain} {base : AssetId}
    {w : World X} {c : HeadCall} (hs : c.sender ≠ cfg.router) :
    recoverCallAtHead enc cfg hk code dest base w c
      = if c.value = 0 then some (w, false)
        else (bridgehubRecoverBaseTokenAtHead enc cfg hk w cfg.manager dest base c.sender
          c.value).map (fun w' => (w', true)) := by
  unfold recoverCallAtHead
  rw [ite_eq_right hs]
  by_cases hv : c.value = 0
  · rw [ite_eq_right (not_not.mpr hv), ite_eq_left hv]
  · rw [ite_eq_left hv, ite_eq_right hv]

/-- A router call on an asset the vault handles and knows: the vault re-mints to the decoded
`originalCaller`. -/
theorem recoverCallAtHead_router_known {enc : AssetIdOf} {cfg : HeadConfig}
    {hk : HeadHooks X} {code : HandlerCode X} {dest : Chain} {base : AssetId}
    {w : World X} {a : AssetId} {data : Bytes} {md : MintData} {x₁ : X}
    (hd : dest ≠ cfg.l1Chain) (hh : w.router.handler a = cfg.ntv) (hn0 : cfg.ntv ≠ 0)
    (hb : a ≠ cfg.baseAsset) (hdec : cfg.decodeMint data = some md) (hp : w.paused = false)
    (hn : w.vault.originChain a ≠ cfg.thisChain) (ht : w.vault.token a ≠ 0)
    (hf : hk.fromChain w.rest dest a md.amount = some x₁) :
    recoverCallAtHead enc cfg hk code dest base w (routerCallAtHead cfg a data)
      = (hk.mint x₁ (w.vault.token a) md.originalCaller md.amount).map
          (fun x₂ => ({ w with rest := x₂ }, true)) := by
  rw [recoverCallAtHead_routerCall, recoverAtomicCallAtHead_finalize hd, hh, ite_eq_right hn0,
    handlerRecover_ntv, hdec, vaultRecoverAtHead_offBase hd hb]
  rw [ntvRecover_known (cfg := cfg.toConfig) hp hn ht hf, Option.map_map]
  rfl

/-- A router call on an asset with a custom handler: that handler's code, then `true`. -/
theorem recoverCallAtHead_router_custom {enc : AssetIdOf} {cfg : HeadConfig}
    {hk : HeadHooks X} {code : HandlerCode X} {dest : Chain} {base : AssetId}
    {w : World X} {a : AssetId} {data : Bytes} (hd : dest ≠ cfg.l1Chain)
    (h0 : w.router.handler a ≠ 0) (hn : w.router.handler a ≠ cfg.ntv) :
    recoverCallAtHead enc cfg hk code dest base w (routerCallAtHead cfg a data)
      = (code (w.router.handler a) w dest a data).map (fun w' => (w', true)) := by
  rw [recoverCallAtHead_routerCall, recoverAtomicCallAtHead_finalize hd, ite_eq_right h0,
    handlerRecover_other hn]

/-- Every iteration that returns keeps the handler at `a`, provided the handlers' code does: the
vault's refunds never write the router's maps. -/
theorem recoverCallAtHead_keeps_handler {enc : AssetIdOf} {cfg : HeadConfig}
    {hk : HeadHooks X} {code : HandlerCode X} {dest : Chain} {base : AssetId}
    {a : AssetId} (hcode : CodeKeepsHandlerAt a code) {u u' : World X} {c : HeadCall} {x : Bool}
    (h : recoverCallAtHead enc cfg hk code dest base u c = some (u', x)) :
    u'.router.handler a = u.router.handler a := by
  unfold recoverCallAtHead at h
  by_cases hs : c.sender = cfg.router
  · rw [ite_eq_left hs] at h
    unfold recoverAtomicCallAtHead at h
    rw [ite_eq_right (by simp)] at h
    by_cases hd : dest = cfg.l1Chain
    · rw [ite_eq_left hd] at h
      cases h
    rw [ite_eq_right hd] at h
    rcases hdata : c.data with ⟨src, a', data⟩ | _ | _ <;> rw [hdata] at h
    · dsimp only at h
      by_cases h0 : u.router.handler a' = 0
      · rw [ite_eq_left h0] at h
        cases h
      rw [ite_eq_right h0] at h
      obtain ⟨w'', hrec, hp⟩ := Option.map_eq_some_iff.mp h
      cases hp
      unfold handlerRecover at hrec
      split_ifs at hrec with hn
      · rw [vaultRecoverAtHead_router hrec]
      · exact hcode _ _ _ _ _ _ hrec
    · cases h
    · cases h
      rfl
  · rw [ite_eq_right hs] at h
    by_cases hv : c.value ≠ 0
    · rw [ite_eq_left hv] at h
      obtain ⟨w'', hrec, hp⟩ := Option.map_eq_some_iff.mp h
      cases hp
      unfold bridgehubRecoverBaseTokenAtHead at hrec
      split_ifs at hrec
      rw [vaultRecoverAtHead_router hrec]
    · rw [ite_eq_right hv] at h
      cases h
      rfl

/-! ## The loop -/

theorem recoverBundleAtHead_cons_some {step : World X → HeadCall → Option (World X × Bool)}
    {w w' : World X} {c : HeadCall} {cs : List HeadCall} {x : Bool} (h : step w c = some (w', x)) :
    recoverBundleAtHead step w (c :: cs)
      = (recoverBundleAtHead step w' cs).map (fun q => (q.1, (if x then 1 else 0) + q.2)) := by
  simp only [recoverBundleAtHead, h]
  cases recoverBundleAtHead step w' cs <;> rfl

theorem recoverBundleAtHead_cons_none {step : World X → HeadCall → Option (World X × Bool)}
    {w : World X} {c : HeadCall} {cs : List HeadCall} (h : step w c = none) :
    recoverBundleAtHead step w (c :: cs) = none := by
  simp only [recoverBundleAtHead, h]

/-- A loop whose every call's iteration declines and changes nothing returns the world unchanged. -/
theorem recoverBundleAtHead_noop {step : World X → HeadCall → Option (World X × Bool)} :
    ∀ (calls : List HeadCall) (w : World X), (∀ c ∈ calls, ∀ u, step u c = some (u, false)) →
      recoverBundleAtHead step w calls = some (w, 0)
  | [], _, _ => rfl
  | c :: cs, w, h => by
    rw [recoverBundleAtHead_cons_some (h c List.mem_cons_self w),
      recoverBundleAtHead_noop cs w (fun c hc => h c (List.mem_cons_of_mem _ hc))]
    rfl

theorem claimRefundAtHead_revertable {cfg : HeadConfig}
    {step : Chain → AssetId → World X → HeadCall → Option (World X × Bool)} {w : World X}
    {b : HeadBundle} (hd : b.destChain ≠ cfg.l1Chain) :
    claimRefundAtHead cfg step LegState.Revertable w b
      = (recoverBundleAtHead (step b.destChain b.destBaseTokenAssetId) w b.calls).map
          (fun p => (LegState.Reverted, p.1)) := by
  unfold claimRefundAtHead
  rw [ite_eq_right (by simp), ite_eq_right hd]

/-- A claim whose first call returns: the rest of the loop, from the world it left. -/
theorem claimRefundAtHead_cons_some {cfg : HeadConfig}
    {step : Chain → AssetId → World X → HeadCall → Option (World X × Bool)} {w w' : World X}
    {dest : Chain} {base : AssetId} {c : HeadCall} {cs : List HeadCall} {x : Bool}
    (hd : dest ≠ cfg.l1Chain) (h : step dest base w c = some (w', x)) :
    claimRefundAtHead cfg step LegState.Revertable w ⟨dest, base, c :: cs⟩
      = (recoverBundleAtHead (step dest base) w' cs).map (fun q => (LegState.Reverted, q.1)) := by
  unfold claimRefundAtHead
  dsimp only
  rw [ite_eq_right (by simp), ite_eq_right hd, recoverBundleAtHead_cons_some h, Option.map_map]
  rfl

theorem claimRefundAtHead_eq_none {cfg : HeadConfig}
    {step : Chain → AssetId → World X → HeadCall → Option (World X × Bool)} {st : LegState}
    {w : World X} {b : HeadBundle}
    (h : recoverBundleAtHead (step b.destChain b.destBaseTokenAssetId) w b.calls = none) :
    claimRefundAtHead cfg step st w b = none := by
  unfold claimRefundAtHead
  split_ifs
  · rfl
  · rfl
  · rw [h]
    rfl

/-- A claim whose first call reverts. -/
theorem claimRefundAtHead_cons_none {cfg : HeadConfig}
    {step : Chain → AssetId → World X → HeadCall → Option (World X × Bool)} {w : World X}
    {st : LegState} {dest : Chain} {base : AssetId} {c : HeadCall} {cs : List HeadCall}
    (h : step dest base w c = none) :
    claimRefundAtHead cfg step st w ⟨dest, base, c :: cs⟩ = none :=
  claimRefundAtHead_eq_none (recoverBundleAtHead_cons_none h)

theorem recoverBundleAtHead_some_loopCompletes
    {step : World X → HeadCall → Option (World X × Bool)} :
    ∀ (calls : List HeadCall) (w w' : World X) (n : ℕ),
      recoverBundleAtHead step w calls = some (w', n) → LoopCompletes (outcomesAtHead step w calls)
  | [], _, _, _, _ => List.not_mem_nil
  | c :: cs, w, w', n, h => by
    rcases hs : step w c with _ | ⟨w₁, x⟩
    · rw [recoverBundleAtHead_cons_none hs] at h
      cases h
    rw [recoverBundleAtHead_cons_some hs] at h
    obtain ⟨⟨w₂, k⟩, hr, -⟩ := Option.map_eq_some_iff.mp h
    have ih := recoverBundleAtHead_some_loopCompletes cs w₁ w₂ k hr
    simp only [outcomesAtHead, hs]
    intro hm
    rcases List.mem_cons.mp hm with he | hm
    · cases x <;> simp at he
    · exact ih hm

theorem recoverBundleAtHead_none_not_loopCompletes
    {step : World X → HeadCall → Option (World X × Bool)} :
    ∀ (calls : List HeadCall) (w : World X),
      recoverBundleAtHead step w calls = none → ¬ LoopCompletes (outcomesAtHead step w calls)
  | [], _, h => by simp [recoverBundleAtHead] at h
  | c :: cs, w, h => by
    rcases hs : step w c with _ | ⟨w₁, x⟩
    · simp [outcomesAtHead, hs]
    rw [recoverBundleAtHead_cons_some hs] at h
    have hr : recoverBundleAtHead step w₁ cs = none := by
      rcases hr' : recoverBundleAtHead step w₁ cs with _ | q
      · rfl
      · rw [hr'] at h
        cases h
    simp only [outcomesAtHead, hs]
    intro hl
    exact recoverBundleAtHead_none_not_loopCompletes cs w₁ hr
      (fun hm => hl (List.mem_cons_of_mem _ hm))

/-- **The loop with a blocking call reverts.** -/
theorem recoverBundleAtHead_eq_none_of_blocking
    {step : World X → HeadCall → Option (World X × Bool)}
    (Inv : World X → Prop) (Blocks : HeadCall → Prop) :
    ∀ (calls : List HeadCall) (w : World X),
      (∀ c ∈ calls, ∀ u u' x, Inv u → step u c = some (u', x) → Inv u') →
      (∀ c ∈ calls, Blocks c → ∀ u, Inv u → step u c = none) →
      (∃ c ∈ calls, Blocks c) → Inv w → recoverBundleAtHead step w calls = none
  | [], _, _, _, ⟨_, hc, _⟩, _ => absurd hc List.not_mem_nil
  | c :: cs, w, hpres, hblock, ⟨c', hc', hb'⟩, hw => by
    by_cases hcb : Blocks c
    · exact recoverBundleAtHead_cons_none (hblock c List.mem_cons_self hcb w hw)
    rcases hs : step w c with _ | ⟨w', x⟩
    · exact recoverBundleAtHead_cons_none hs
    rw [recoverBundleAtHead_cons_some hs]
    have hw' := hpres c List.mem_cons_self w w' x hw hs
    have hex : ∃ c ∈ cs, Blocks c := by
      rcases List.mem_cons.mp hc' with rfl | h
      · exact absurd hb' hcb
      · exact ⟨c', h, hb'⟩
    rw [recoverBundleAtHead_eq_none_of_blocking Inv Blocks cs w'
      (fun c hc => hpres c (List.mem_cons_of_mem _ hc))
      (fun c hc => hblock c (List.mem_cons_of_mem _ hc)) hex hw']
    rfl

/-! ## Rotation along the writers' runs -/

/-- **One writer call keeps a handler it does not rotate.** -/
theorem astep_keeps_handler {K : AllWriters.Cfg} {op : AllWriters.Op} {S T : Router}
    {a : AssetId} {h₀ : Address} (hs : AllWriters.AStep K op S T) (hS : S.handler a = h₀)
    (h0 : h₀ ≠ 0) (hrot : ¬ Rotates K a h₀ op) : T.handler a = h₀ := by
  cases hs with
  | @register _ caller d h _ =>
    by_cases hw : a = writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d
    · have hh : h = h₀ := by
        by_contra hne
        exact hrot ⟨hw.symm, hne⟩
      rw [hw]
      show upd S.handler (writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d) h
        (writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d) = h₀
      rw [upd_same]
      exact hh
    · rw [handler_frame _ _ _ _ _ _ _ _ _ hw]
      exact hS
  | @finalize _ a' h0' _ _ =>
    by_cases ha : a = a'
    · subst ha
      rw [hS] at h0'
      exact absurd h0' h0
    · rw [AllWriters.pointAt_handler_ne _ _ ha]
      exact hS
  | seed =>
    by_cases ha : a = K.seedId
    · have hh : K.ntv = h₀ := by
        by_contra hne
        exact hrot ⟨ha.symm, hne⟩
      rw [ha, AllWriters.pointAt_handler_self]
      exact hh
    · rw [AllWriters.pointAt_handler_ne _ _ ha]
      exact hS
  | @counterpartSet _ a' h _ =>
    by_cases ha : a = a'
    · have hh : h = h₀ := by
        by_contra hne
        exact hrot ⟨ha.symm, hne⟩
      rw [ha, AllWriters.pointAt_handler_self]
      exact hh
    · rw [AllWriters.pointAt_handler_ne _ _ ha]
      exact hS
  | setTracker _ => exact hS

theorem noRotation_keeps {K : AllWriters.Cfg} {a : AssetId} {h₀ : Address} (h0 : h₀ ≠ 0) :
    ∀ {R₁ R₂ : Router} {ops : List AllWriters.Op}, AllWriters.ARun K R₁ ops R₂ →
      R₁.handler a = h₀ → NoRotation K a h₀ ops → R₂.handler a = h₀ := by
  intro R₁ R₂ ops hr
  induction hr with
  | nil => exact fun h _ => h
  | @snoc S T ops' op _ hstep ih =>
    intro h1 hnr
    have hS : S.handler a = h₀ := ih h1 (fun o ho => hnr o (List.mem_append_left _ ho))
    exact astep_keeps_handler hstep hS h0 (hnr op (List.mem_append_right _ List.mem_cons_self))

/-- The logged premises rule out every rotation. -/
theorem noRotation_of_logged {K : AllWriters.Cfg} {ops : List AllWriters.Op} {c₀ : Chain}
    {s₀ : Address} {d₀ : AssetData} {h₀ : Address}
    (hinj : ∀ op ∈ ops, ∀ p, op.triple K = some p → IdInjOn K.enc {(c₀, s₀, d₀), p})
    (hreg : ∀ caller d h, AllWriters.Op.register caller d h ∈ ops →
      (K.thisChain, senderOf K.ntv K.ntvAddr caller, d) = (c₀, s₀, d₀) → h = h₀)
    (hcp : ∀ a' h, AllWriters.Op.counterpartSet a' h ∈ ops → a' = K.enc c₀ s₀ d₀ → h = h₀)
    (hseed : AllWriters.Op.seed ∈ ops → K.seedId = K.enc c₀ s₀ d₀ → K.ntv = h₀) :
    NoRotation K (K.enc c₀ s₀ d₀) h₀ ops := by
  intro op hop hrot
  cases op with
  | register caller d h =>
    obtain ⟨hw, hne⟩ := hrot
    have hp := hinj _ hop (K.thisChain, senderOf K.ntv K.ntvAddr caller, d) rfl
    have heq : (K.thisChain, senderOf K.ntv K.ntvAddr caller, d) = (c₀, s₀, d₀) :=
      hp _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)) _ (Set.mem_insert _ _) hw
    exact hne (hreg caller d h hop heq)
  | finalize _ => exact hrot
  | seed => exact hrot.2 (hseed hop hrot.1)
  | counterpartSet a' h => exact hrot.2 (hcp a' h hop hrot.1)
  | setTracker _ _ => exact hrot

/-! ## Certificates: (a) direct calls -/

theorem DirectCallSkipsRouterRecovery : Properties.DirectCallSkipsRouterRecovery :=
  fun _ _ _ _ _ _ _ _ _ hs => recoverCallAtHead_direct hs

theorem DirectCallDataIgnoredAtHead : Properties.DirectCallDataIgnoredAtHead := by
  intro X enc cfg hk code code' dest base w c target d hs
  have hs' : ({ c with target := target, data := d } : HeadCall).sender ≠ cfg.router := hs
  rw [recoverCallAtHead_direct hs', recoverCallAtHead_direct hs]

theorem DirectValueLegRefundsItsSenderAtHead :
    Properties.DirectValueLegRefundsItsSenderAtHead := by
  intro X enc cfg hk code dest base w c hs hv hd
  rw [recoverCallAtHead_direct hs, ite_eq_right hv, bridgehubRecoverBaseTokenAtHead_manager hd]

theorem CrossBaseValueLegRefundAtHead : Properties.CrossBaseValueLegRefundAtHead := by
  intro X enc cfg hk code dest base w c hs hv hd hb
  rw [recoverCallAtHead_direct hs, ite_eq_right hv, bridgehubRecoverBaseTokenAtHead_manager hd,
    vaultRecoverAtHead_offBase hd hb]

theorem SameBaseValueLegRefundAtHead : Properties.SameBaseValueLegRefundAtHead := by
  intro X enc cfg hk code dest w c hs hv hd hp hn
  rw [recoverCallAtHead_direct hs, ite_eq_right hv, bridgehubRecoverBaseTokenAtHead_manager hd,
    vaultRecoverAtHead_base hd hp, ite_eq_right hn, Option.map_map]
  rfl

theorem CallTargetIgnoredAtHead : Properties.CallTargetIgnoredAtHead := by
  intro X enc cfg hk code dest base w c target
  rfl

theorem DirectBundleClaimIsNoOpAtHead : Properties.DirectBundleClaimIsNoOpAtHead := by
  intro X enc cfg hk code w b hd hcalls
  have hnoop : ∀ c ∈ b.calls, ∀ u,
      recoverCallAtHead enc cfg hk code b.destChain b.destBaseTokenAssetId u c = some (u, false) := by
    intro c hc u
    obtain ⟨hs, hv⟩ := hcalls c hc
    rw [recoverCallAtHead_direct hs, ite_eq_left hv]
  rw [claimRefundAtHead_revertable hd, recoverBundleAtHead_noop b.calls w hnoop]
  rfl

theorem RouterSenderIffIndirectAtHead : Properties.RouterSenderIffIndirectAtHead := by
  intro cfg msgSender st hs
  cases st with
  | direct recipient d v =>
    constructor
    · intro h
      exact absurd h hs
    · rintro ⟨a, mb, h, -⟩
      cases h
  | indirect a mb =>
    exact ⟨fun _ => ⟨a, mb, rfl, rfl⟩, fun _ => rfl⟩

theorem SentDirectCallNeverRecoveredAtHead : Properties.SentDirectCallNeverRecoveredAtHead := by
  intro X enc cfg hk code dest base w msgSender recipient d v hs
  exact recoverCallAtHead_direct (c := directCallAtHead recipient msgSender v d) hs

/-! ## Certificates: (b) routing -/

theorem VaultRecoverAtHeadIsPinRefundOffBaseToken :
    Properties.VaultRecoverAtHeadIsPinRefundOffBaseToken :=
  fun _ _ _ _ _ _ _ _ _ _ hd ha => vaultRecoverAtHead_offBase hd ha

theorem VaultRecoverAtHeadOnBaseToken : Properties.VaultRecoverAtHeadOnBaseToken :=
  fun _ _ _ _ _ _ _ hd hp => vaultRecoverAtHead_base hd hp

theorem RecoveryReadsClaimTimeHandler : Properties.RecoveryReadsClaimTimeHandler :=
  fun _ _ _ _ _ _ _ _ _ _ hd => recoverAtomicCallAtHead_finalize hd

theorem BurnLeavesBurnHandler : Properties.BurnLeavesBurnHandler := by
  intro cfg R a
  unfold burnRouter AtomicRecovery.burnHandler
  split_ifs with h
  · exact upd_same _ _ _
  · rfl

theorem BurnHandlerNonzero : Properties.BurnHandlerNonzero := by
  intro cfg R a hn
  unfold AtomicRecovery.burnHandler
  split_ifs with h
  · exact hn
  · exact h

theorem NoRotationKeepsHandler : Properties.NoRotationKeepsHandler :=
  fun _ _ _ _ _ _ hr h1 h0 hnr => noRotation_keeps h0 hr h1 hnr

theorem HandlerMovesOnlyByRotation : Properties.HandlerMovesOnlyByRotation := by
  intro K op R R' a hs hmove h0
  by_contra hrot
  exact hmove (astep_keeps_handler hs rfl h0 hrot)

theorem NoRotationKeepsHandlerLoggedOn : Properties.NoRotationKeepsHandlerLoggedOn := by
  intro K R₁ R₂ ops c₀ s₀ d₀ h₀ hr h1 h0 hinj hreg hcp hseed
  exact noRotation_keeps h0 hr h1 (noRotation_of_logged hinj hreg hcp hseed)

theorem RouterLegReachesBurnHandler : Properties.RouterLegReachesBurnHandler := by
  intro X enc cfg hk code K R ops w dest base a mintBytes hd hn hrun hnr
  have h0 : AtomicRecovery.burnHandler cfg.toConfig R a ≠ 0 := BurnHandlerNonzero cfg.toConfig R a hn
  have hkeep : w.router.handler a = AtomicRecovery.burnHandler cfg.toConfig R a :=
    noRotation_keeps h0 hrun (BurnLeavesBurnHandler cfg.toConfig R a) hnr
  rw [recoverCallAtHead_routerCall, recoverAtomicCallAtHead_finalize hd, hkeep, ite_eq_right h0]

theorem RouterLegReachesBurnHandlerLoggedOn : Properties.RouterLegReachesBurnHandlerLoggedOn := by
  intro X enc cfg hk code K R ops w dest base c₀ s₀ d₀ mintBytes hd hn hrun hinj hreg hcp hseed
  exact RouterLegReachesBurnHandler X enc cfg hk code K R ops w dest base (K.enc c₀ s₀ d₀) mintBytes
    hd hn hrun (noRotation_of_logged hinj hreg hcp hseed)

theorem CustomHandlerRecoveredByItsHandler : Properties.CustomHandlerRecoveredByItsHandler := by
  intro X enc cfg hk code w w' dest src a data hd h0 hn hc
  rw [recoverAtomicCallAtHead_finalize hd, ite_eq_right h0, handlerRecover_other hn, hc]
  rfl

theorem PreparedBurnRefundsDepositorAtHead : Properties.PreparedBurnRefundsDepositorAtHead := by
  intro Acc prepHooks s r out hw hprep X enc cfg hk code dest base w mintBytes x₁ hd hdec hh hn0
    hb hp hn ht hf
  obtain ⟨hoc, -, -, hamt, -, -⟩ := NativeTokenVaultBase.preparation_payload hw hprep
  rw [← hamt] at hf
  rw [recoverCallAtHead_router_known hd hh hn0 hb hdec hp hn ht hf, hoc, hamt]

/-! ## Certificates: (c) rotation -/

theorem ZeroedHandlerRecoveryReverts : Properties.ZeroedHandlerRecoveryReverts := by
  intro X enc cfg hk code w dest base a mintBytes h0
  rw [recoverCallAtHead_routerCall]
  by_cases hd : dest = cfg.l1Chain
  · unfold recoverAtomicCallAtHead
    rw [ite_eq_right (by simp), ite_eq_left hd]
  · rw [recoverAtomicCallAtHead_finalize hd, ite_eq_left h0]

/-! ## Certificates: (d) blocking -/

theorem ClaimSucceedsIffLoopCompletesAtHead : Properties.ClaimSucceedsIffLoopCompletesAtHead := by
  intro X cfg step w b
  by_cases hd : b.destChain = cfg.l1Chain
  · have hnone : claimRefundAtHead cfg step LegState.Revertable w b = none := by
      unfold claimRefundAtHead
      rw [ite_eq_right (by simp), ite_eq_left hd]
    rw [hnone]
    simp [hd]
  · rw [claimRefundAtHead_revertable hd]
    rcases hr : recoverBundleAtHead (step b.destChain b.destBaseTokenAssetId) w b.calls with
      _ | ⟨w', n⟩
    · simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
      exact fun _ => recoverBundleAtHead_none_not_loopCompletes _ _ hr
    · simp only [Option.map_some, Option.isSome_some, true_iff]
      exact ⟨hd, recoverBundleAtHead_some_loopCompletes _ _ _ _ hr⟩

theorem RevertingCallBlocksClaimAtHead : Properties.RevertingCallBlocksClaimAtHead := by
  intro X cfg step st w b Inv Blocks hpres hblock hex hw
  exact claimRefundAtHead_eq_none
    (recoverBundleAtHead_eq_none_of_blocking Inv Blocks b.calls w hpres hblock hex hw)

/-- A router call on `a` reverts in every world whose table points `a` at an unrecoverable `h`. -/
theorem routerCallOn_blocks {enc : AssetIdOf} {cfg : HeadConfig} {hk : HeadHooks X}
    {code : HandlerCode X} {dest : Chain} {base : AssetId} {a : AssetId} {h : Address}
    (hrev : h ≠ 0 → RecoveryRevertsAt enc cfg hk code h a) {c : HeadCall}
    (hc : c.sender = cfg.router ∧ ∃ src data, c.data = .finalizeDeposit src a data)
    {u : World X} (hu : u.router.handler a = h) :
    recoverCallAtHead enc cfg hk code dest base u c = none := by
  obtain ⟨hs, src, data, hdata⟩ := hc
  rw [recoverCallAtHead_fromRouter hs, hdata]
  by_cases hd : dest = cfg.l1Chain
  · unfold recoverAtomicCallAtHead
    rw [ite_eq_right (by simp), ite_eq_left hd]
  rw [recoverAtomicCallAtHead_finalize hd]
  by_cases h0 : u.router.handler a = 0
  · rw [ite_eq_left h0]
  · rw [ite_eq_right h0, hu, hrev (hu ▸ h0) u dest data hu]
    rfl

theorem UnrecoverableHandlerBlocksBundleAtHead :
    Properties.UnrecoverableHandlerBlocksBundleAtHead := by
  intro X enc cfg hk code st w b a h hw hrev hcode hhas
  refine claimRefundAtHead_eq_none
    (recoverBundleAtHead_eq_none_of_blocking (fun u : World X => u.router.handler a = h)
      (fun c => c.sender = cfg.router ∧ ∃ src data, c.data = .finalizeDeposit src a data)
      b.calls w ?_ ?_ hhas hw)
  · intro c _ u u' x hu hs
    rw [recoverCallAtHead_keeps_handler hcode hs]
    exact hu
  · intro c _ hc u hu
    exact routerCallOn_blocks hrev hc hu

theorem NothingRecoveredStillConsumesLegAtHead :
    Properties.NothingRecoveredStillConsumesLegAtHead := by
  intro X cfg step w w' b hd hr
  refine ⟨?_, by decide⟩
  rw [claimRefundAtHead_revertable hd, hr]
  rfl

theorem UnrecognisedRouterCallConsumedAtHead :
    Properties.UnrecognisedRouterCallConsumedAtHead := by
  intro X enc cfg hk code w b hd hcalls
  have hnoop : ∀ c ∈ b.calls, ∀ u,
      recoverCallAtHead enc cfg hk code b.destChain b.destBaseTokenAssetId u c = some (u, false) := by
    intro c hc u
    rcases hcalls c hc with ⟨hs, hdata⟩ | ⟨hs, hv⟩
    · rw [recoverCallAtHead_fromRouter hs, hdata, recoverAtomicCallAtHead_other hd]
    · rw [recoverCallAtHead_direct hs, ite_eq_left hv]
  rw [claimRefundAtHead_revertable hd, recoverBundleAtHead_noop b.calls w hnoop]
  rfl

/-! ## Concrete instances

The pin model's witness setting: `AtomicRecovery.wCfg` (chain `7`, router `3`, vault `4`, manager
`5`), `AtomicRecovery.wEnc` (every vault-hashed id is `1`, every other id `2`), `AtomicRecovery.wVault`
(bridged asset `1`, local token `6`) and `AtomicRecovery.wRouter` (asset `2` → custom handler `11`,
asset `1` → the vault).  The head adds L1 chain `99` and a vault decoder that reads every byte string
as `AtomicRecovery.wMd` (original caller `11`, amount `1`), and this chain's base token is asset
`77`, which the witness vault does not hold.  Bundles go to chain `8`. -/

/-- The head configuration of the witness setting. -/
def headCfg : HeadConfig :=
  { toConfig := AtomicRecovery.wCfg, l1Chain := 99, baseAsset := 77,
    decodeMint := fun _ => some AtomicRecovery.wMd }

/-- The pin's always-returning hooks, with a base-token holder that always returns. -/
def headOkHooks : HeadHooks Unit :=
  { toHooks := AtomicRecovery.okHooks, recoverBase := fun x _ _ _ => some x }

/-- The pin's ledger hooks, with a base-token holder that credits the receiver on the same ledger. -/
def headLedgerHooks : HeadHooks (Addr160 → ℕ) :=
  { toHooks := AtomicRecovery.ledgerHooks,
    recoverBase := fun bal rcv amt _ => some (Function.update bal rcv (bal rcv + amt.val)) }

/-- The L2 router's writers in the witness setting. -/
def headK : AllWriters.Cfg := ⟨AtomicRecovery.wEnc, 7, 4, 4, .l2, 0, fun _ => False⟩

/-- Every address other than the vault answers `bridgeRecoverFailedTransfer` by returning without
moving anything. -/
def headNoOpCode {X : Type} : HandlerCode X := fun _ w _ _ _ => some w

/-- No address other than the vault implements `bridgeRecoverFailedTransfer`. -/
def headRevertCode {X : Type} : HandlerCode X := fun _ _ _ _ _ => none

/-- The ledger after the vault re-mints `AtomicRecovery.wMd` to its original caller. -/
def headCredited (w : World (Addr160 → ℕ)) : World (Addr160 → ℕ) :=
  { w with
    rest := Function.update w.rest AtomicRecovery.wMd.originalCaller
      (w.rest AtomicRecovery.wMd.originalCaller + AtomicRecovery.wMd.amount.val) }

theorem headCredited_rest (w : World (Addr160 → ℕ)) :
    (headCredited w).rest AtomicRecovery.wMd.originalCaller
      = w.rest AtomicRecovery.wMd.originalCaller + AtomicRecovery.wMd.amount.val := by
  unfold headCredited
  dsimp only
  exact Function.update_self _ _ _

theorem head_wRouter_one : AtomicRecovery.wRouter.handler 1 = 4 := by
  unfold AtomicRecovery.wRouter; decide

theorem head_wRouter_two : AtomicRecovery.wRouter.handler 2 = 11 := by
  unfold AtomicRecovery.wRouter; decide

theorem head_dest : (8 : Chain) ≠ headCfg.l1Chain := by decide

theorem head_ntv_ne_zero : headCfg.ntv ≠ 0 := by decide

/-- The vault-asset router call, on a ledger world whose table points asset `1` at the vault. -/
theorem head_vault_step (code : HandlerCode (Addr160 → ℕ)) (w : World (Addr160 → ℕ))
    (hh : w.router.handler 1 = 4) (hv : w.vault = AtomicRecovery.wVault) (hp : w.paused = false) :
    recoverCallAtHead AtomicRecovery.wEnc headCfg headLedgerHooks code 8 1 w
      (routerCallAtHead headCfg 1 []) = some (headCredited w, true) := by
  have hn : w.vault.originChain 1 ≠ headCfg.thisChain := by
    rw [hv]; exact AtomicRecovery.wVault_known_one.1
  have ht : w.vault.token 1 ≠ 0 := by
    rw [hv]; exact AtomicRecovery.wVault_known_one.2
  rw [recoverCallAtHead_router_known (enc := AtomicRecovery.wEnc) (cfg := headCfg)
    (hk := headLedgerHooks) (code := code) (dest := 8) (base := 1) (w := w) (a := 1)
    (data := []) (md := AtomicRecovery.wMd) (x₁ := w.rest) head_dest hh head_ntv_ne_zero (by decide)
    rfl hp hn ht
    rfl]
  rfl

/-- The same on a `Unit` world with hooks that always return. -/
theorem head_vault_step_unit (code : HandlerCode Unit) (w : World Unit)
    (hh : w.router.handler 1 = 4) (hv : w.vault = AtomicRecovery.wVault) (hp : w.paused = false) :
    recoverCallAtHead AtomicRecovery.wEnc headCfg headOkHooks code 8 1 w
      (routerCallAtHead headCfg 1 []) = some ({ w with rest := () }, true) := by
  have hn : w.vault.originChain 1 ≠ headCfg.thisChain := by
    rw [hv]; exact AtomicRecovery.wVault_known_one.1
  have ht : w.vault.token 1 ≠ 0 := by
    rw [hv]; exact AtomicRecovery.wVault_known_one.2
  rw [recoverCallAtHead_router_known (enc := AtomicRecovery.wEnc) (cfg := headCfg)
    (hk := headOkHooks) (code := code) (dest := 8) (base := 1) (w := w) (a := 1)
    (data := []) (md := AtomicRecovery.wMd) (x₁ := ()) head_dest hh head_ntv_ne_zero (by decide)
    rfl hp hn ht
    rfl]
  rfl

/-- A router call on an asset with a custom handler, under `headNoOpCode`. -/
theorem head_custom_noop_step {X : Type} (hk : HeadHooks X) (w : World X) (a : AssetId)
    (data : Bytes) (base : AssetId) (h0 : w.router.handler a ≠ 0)
    (hn : w.router.handler a ≠ headCfg.ntv) :
    recoverCallAtHead AtomicRecovery.wEnc headCfg hk headNoOpCode 8 base w
      (routerCallAtHead headCfg a data) = some (w, true) := by
  rw [recoverCallAtHead_router_custom (enc := AtomicRecovery.wEnc) (cfg := headCfg) (hk := hk)
    (code := headNoOpCode) (dest := 8) (base := base) (w := w) (a := a) (data := data) head_dest h0 hn]
  rfl

/-- A router call on an asset with a custom handler, under `headRevertCode`. -/
theorem head_custom_revert_step {X : Type} (hk : HeadHooks X) (w : World X)
    (a : AssetId) (data : Bytes) (base : AssetId) (h0 : w.router.handler a ≠ 0)
    (hn : w.router.handler a ≠ headCfg.ntv) :
    recoverCallAtHead AtomicRecovery.wEnc headCfg hk headRevertCode 8 base w
      (routerCallAtHead headCfg a data) = none := by
  rw [recoverCallAtHead_router_custom (enc := AtomicRecovery.wEnc) (cfg := headCfg) (hk := hk)
    (code := headRevertCode) (dest := 8) (base := base) (w := w) (a := a) (data := data) head_dest h0
    hn]
  rfl

theorem head_revertCode_keeps {X : Type} (a : AssetId) :
    CodeKeepsHandlerAt a (headRevertCode (X := X)) := by
  intro _ _ _ _ _ _ h
  cases h

theorem head_revert_recoveryRevertsAt {X : Type} (hk : HeadHooks X) :
    RecoveryRevertsAt AtomicRecovery.wEnc headCfg hk headRevertCode 11 2 := by
  intro u chainId data _
  rw [handlerRecover_other (show (11 : Address) ≠ headCfg.ntv by decide)]
  rfl

theorem head_burnRouter_two : burnRouter AtomicRecovery.wCfg AtomicRecovery.wRouter 2
    = AtomicRecovery.wRouter := by
  unfold burnRouter
  rw [ite_eq_right (by rw [head_wRouter_two]; decide)]

theorem head_burnHandler_two : AtomicRecovery.burnHandler AtomicRecovery.wCfg AtomicRecovery.wRouter 2
    = 11 := by
  unfold AtomicRecovery.burnHandler
  rw [head_wRouter_two]
  decide

theorem head_burnHandler_one : AtomicRecovery.burnHandler AtomicRecovery.wCfg AtomicRecovery.wRouter 1
    = 4 := by
  unfold AtomicRecovery.burnHandler
  rw [head_wRouter_one]
  decide

/-- The pin's stranded two-call bundle of the witness setting (custom asset `2`, vault asset `1`). -/
def headStrandedBundle : HeadBundle :=
  ⟨8, 1, [routerCallAtHead headCfg 2 [], routerCallAtHead headCfg 1 []]⟩

theorem head_stranded_has : HasRouterCallOnAtHead headCfg 2 headStrandedBundle.calls :=
  ⟨routerCallAtHead headCfg 2 [], List.mem_cons_self, rfl, headCfg.thisChain, [], rfl⟩

/-- The vault-asset call of that bundle, alone: refunded. -/
theorem head_vault_alone (code : HandlerCode Unit) :
    (claimRefundAtHead headCfg (recoverCallAtHead AtomicRecovery.wEnc headCfg headOkHooks code)
      LegState.Revertable AtomicRecovery.wWorld ⟨8, 1, [routerCallAtHead headCfg 1 []]⟩).isSome := by
  rw [claimRefundAtHead_cons_some head_dest
    (head_vault_step_unit code AtomicRecovery.wWorld head_wRouter_one rfl rfl)]
  rfl

/-! ## Certificates: concrete instances and countermodels -/

theorem PinUnbackedMintRejectedAtHead : Properties.PinUnbackedMintRejectedAtHead := by
  obtain ⟨-, hclaim⟩ := AtomicRecovery.DirectCallIsRefunded (Addr160 → ℕ) AtomicRecovery.wEnc
    AtomicRecovery.wCfg AtomicRecovery.ledgerHooks AtomicRecovery.declineOther 8 0
    AtomicRecovery.ledgerWorld 13 1 AtomicRecovery.wMd (fun _ => 0)
    (Function.update (fun _ => 0) AtomicRecovery.wMd.originalCaller
      (0 + AtomicRecovery.wMd.amount.val))
    rfl AtomicRecovery.wVault_known_one.1 AtomicRecovery.wVault_known_one.2 rfl rfl
  refine ⟨AtomicRecovery.wEnc, headCfg, headLedgerHooks, AtomicRecovery.declineOther,
    headNoOpCode, 8, 0, 1, AtomicRecovery.ledgerWorld, _, 13, 1, AtomicRecovery.wMd, [],
    by decide, rfl, head_dest, hclaim, rfl, ?_, ?_⟩
  · show 0 < Function.update (fun _ => 0) AtomicRecovery.wMd.originalCaller
      (0 + AtomicRecovery.wMd.amount.val) AtomicRecovery.wMd.originalCaller
    rw [Function.update_self]
    decide
  · refine DirectBundleClaimIsNoOpAtHead _ _ _ _ _ _ _ head_dest ?_
    intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    exact ⟨by decide, rfl⟩

theorem DirectCallIsRefundedFailsAtHead : Properties.DirectCallIsRefundedFailsAtHead := by
  intro hall
  have h := hall (Addr160 → ℕ) AtomicRecovery.wEnc headCfg headLedgerHooks headNoOpCode
    8 0 1 AtomicRecovery.ledgerWorld 13 1 [] AtomicRecovery.wMd (fun _ => 0)
    (Function.update (fun _ => 0) AtomicRecovery.wMd.originalCaller
      (0 + AtomicRecovery.wMd.amount.val))
    (by decide) head_dest rfl rfl AtomicRecovery.wVault_known_one.1
    AtomicRecovery.wVault_known_one.2 rfl rfl
  have hnoop : claimRefundAtHead headCfg
      (recoverCallAtHead AtomicRecovery.wEnc headCfg headLedgerHooks headNoOpCode)
      LegState.Revertable AtomicRecovery.ledgerWorld
      ⟨8, 1, [directCallAtHead headCfg.router 13 0 (.finalizeDeposit 0 1 [])]⟩
      = some (LegState.Reverted, AtomicRecovery.ledgerWorld) := by
    refine DirectBundleClaimIsNoOpAtHead _ _ _ _ _ _ _ head_dest ?_
    intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    exact ⟨by decide, rfl⟩
  rw [hnoop] at h
  have hrest := congrArg (fun o : Option (LegState × World (Addr160 → ℕ)) =>
    o.map (fun p => p.2.rest AtomicRecovery.wMd.originalCaller)) h
  revert hrest
  decide

theorem PinStrandedBundleRefundedAtHead : Properties.PinStrandedBundleRefundedAtHead := by
  refine ⟨Unit, AtomicRecovery.wEnc, headCfg, headOkHooks, AtomicRecovery.declineOther,
    headNoOpCode, 8, 1, AtomicRecovery.wWorld, 2, 1, AtomicRecovery.wMd, AtomicRecovery.wMd, [], [],
    rfl, rfl, ?_, head_burnHandler_one, ?_, ?_⟩
  · show AtomicRecovery.burnHandler AtomicRecovery.wCfg AtomicRecovery.wRouter 2 ≠ 4
    rw [head_burnHandler_two]
    decide
  · exact AtomicRecovery.LegNeverRefunded Unit AtomicRecovery.wEnc AtomicRecovery.wCfg
      AtomicRecovery.okHooks AtomicRecovery.declineOther 8 AtomicRecovery.wWorld AtomicRecovery.wWorld
      _ 2 AtomicRecovery.wVault_unaware_two (AtomicRecovery.declineOther_leaves 2)
      AtomicRecovery.wBundleHas AtomicRecovery.wBundleFails Relation.ReflTransGen.refl
  · rw [claimRefundAtHead_cons_some head_dest
      (head_custom_noop_step headOkHooks AtomicRecovery.wWorld 2 [] 1
        (by rw [show AtomicRecovery.wWorld.router.handler 2 = 11 from head_wRouter_two]; decide)
        (by rw [show AtomicRecovery.wWorld.router.handler 2 = 11 from head_wRouter_two]; decide)),
      recoverBundleAtHead_cons_some
        (head_vault_step_unit headNoOpCode AtomicRecovery.wWorld head_wRouter_one rfl rfl)]
    rfl

theorem RecoveryCallsTheVaultFailsAtHead : Properties.RecoveryCallsTheVaultFailsAtHead := by
  intro hall
  have h := hall Unit AtomicRecovery.wEnc headCfg headOkHooks headNoOpCode
    AtomicRecovery.wWorld 8 7 2 [] head_dest
  have hl : recoverAtomicCallAtHead AtomicRecovery.wEnc headCfg headOkHooks headNoOpCode
      AtomicRecovery.wWorld headCfg.manager 8 (.finalizeDeposit 7 2 [])
      = some (AtomicRecovery.wWorld, true) :=
    CustomHandlerRecoveredByItsHandler _ _ _ _ _ _ _ _ _ _ _ head_dest
      (by rw [show AtomicRecovery.wWorld.router.handler 2 = 11 from head_wRouter_two]; decide)
      (by rw [show AtomicRecovery.wWorld.router.handler 2 = 11 from head_wRouter_two]; decide) rfl
  have hn : vaultRecoverAtHead AtomicRecovery.wEnc headCfg headOkHooks
      AtomicRecovery.wWorld headCfg.router 0 8 2 (headCfg.decodeMint []) = none := by
    rw [vaultRecoverAtHead_offBase head_dest (by decide)]
    exact AtomicRecovery.ntvRecover_unaware AtomicRecovery.wVault_unaware_two (AtomicRecovery.wFails _)
  rw [hl, hn] at h
  cases h

theorem RecoveryIgnoresHandlerFailsAtHead : Properties.RecoveryIgnoresHandlerFailsAtHead := by
  intro hall
  have h := hall Unit AtomicRecovery.wEnc headCfg headOkHooks headNoOpCode
    AtomicRecovery.wWorld Contracts.AssetRouter.empty 8 (.finalizeDeposit 7 2 [])
  have hl : recoverAtomicCallAtHead AtomicRecovery.wEnc headCfg headOkHooks headNoOpCode
      { AtomicRecovery.wWorld with router := Contracts.AssetRouter.empty } headCfg.manager 8
      (.finalizeDeposit 7 2 []) = none := by
    rw [recoverAtomicCallAtHead_finalize head_dest]
    exact ite_eq_left rfl
  have hr : recoverAtomicCallAtHead AtomicRecovery.wEnc headCfg headOkHooks headNoOpCode
      AtomicRecovery.wWorld headCfg.manager 8 (.finalizeDeposit 7 2 [])
      = some (AtomicRecovery.wWorld, true) :=
    CustomHandlerRecoveredByItsHandler _ _ _ _ _ _ _ _ _ _ _ head_dest
      (by rw [show AtomicRecovery.wWorld.router.handler 2 = 11 from head_wRouter_two]; decide)
      (by rw [show AtomicRecovery.wWorld.router.handler 2 = 11 from head_wRouter_two]; decide) rfl
  rw [hl, hr] at h
  cases h

theorem RotationToNoOpHandlerStrandsBurn : Properties.RotationToNoOpHandlerStrandsBurn := by
  refine ⟨AtomicRecovery.wEnc, headCfg, headLedgerHooks, headNoOpCode, headK,
    AtomicRecovery.ledgerWorld, AllWriters.pointAt AtomicRecovery.wRouter 1 13, 8, 1, 1, [],
    AtomicRecovery.wMd, 13, headCredited AtomicRecovery.ledgerWorld,
    rfl, rfl, head_burnHandler_one, by decide, ?_, headCredited_rest _, by decide,
    AllWriters.AStep.counterpartSet rfl, AllWriters.pointAt_handler_self _ _ _, ?_, by decide⟩
  · rw [claimRefundAtHead_cons_some head_dest
      (head_vault_step headNoOpCode AtomicRecovery.ledgerWorld head_wRouter_one rfl rfl)]
    rfl
  · have h13 : ({ AtomicRecovery.ledgerWorld with
        router := AllWriters.pointAt AtomicRecovery.wRouter 1 13 } : World (Addr160 → ℕ)).router.handler 1
        = 13 := AllWriters.pointAt_handler_self _ _ _
    rw [claimRefundAtHead_cons_some head_dest
      (head_custom_noop_step headLedgerHooks _ 1 [] 1 (by rw [h13]; decide)
        (by rw [h13]; decide))]
    rfl

theorem RotationToRevertingHandlerBlocksClaim : Properties.RotationToRevertingHandlerBlocksClaim := by
  have h13 : ({ AtomicRecovery.ledgerWorld with
      router := AllWriters.pointAt AtomicRecovery.wRouter 1 13 } : World (Addr160 → ℕ)).router.handler 1
      = 13 := AllWriters.pointAt_handler_self _ _ _
  have h4 : ({ AtomicRecovery.ledgerWorld with
      router := AllWriters.pointAt (AllWriters.pointAt AtomicRecovery.wRouter 1 13) 1 headCfg.ntv } :
        World (Addr160 → ℕ)).router.handler 1 = 4 := AllWriters.pointAt_handler_self _ _ _
  refine ⟨AtomicRecovery.wEnc, headCfg, headLedgerHooks, headRevertCode, headK,
    AtomicRecovery.ledgerWorld, AllWriters.pointAt AtomicRecovery.wRouter 1 13,
    AllWriters.pointAt (AllWriters.pointAt AtomicRecovery.wRouter 1 13) 1 headCfg.ntv, 8, 1, 1, [],
    AtomicRecovery.wMd, 13,
    headCredited { AtomicRecovery.ledgerWorld with
      router := AllWriters.pointAt (AllWriters.pointAt AtomicRecovery.wRouter 1 13) 1 headCfg.ntv },
    rfl, rfl, head_burnHandler_one, by decide, AllWriters.AStep.counterpartSet rfl, ?_,
    AllWriters.AStep.counterpartSet rfl, ?_, headCredited_rest _, by decide⟩
  · exact claimRefundAtHead_cons_none
      (head_custom_revert_step headLedgerHooks _ 1 [] 1 (by rw [h13]; decide)
        (by rw [h13]; decide))
  · rw [claimRefundAtHead_cons_some head_dest (head_vault_step headRevertCode _ h4 rfl rfl)]
    rfl

theorem L2RotationOnlyByCounterpartSeedOrVault :
    Properties.L2RotationOnlyByCounterpartSeedOrVault := by
  intro K hK ops R R' op a hrun hstep h0 hmove
  have hrot : Rotates K a (R.handler a) op := by
    by_contra hrot
    exact hmove (astep_keeps_handler hstep rfl h0 hrot)
  cases op with
  | register caller d h =>
    have hc : caller = K.ntv :=
      (AllWriters.L2OnlyVaultRegisters K hK _ _ (AllWriters.ARun.snoc hrun hstep)).2 caller d h
        (List.mem_append_right _ List.mem_cons_self)
    exact Or.inr (Or.inr ⟨d, h, by rw [hc]⟩)
  | finalize _ => exact absurd hrot id
  | seed => exact Or.inr (Or.inl ⟨rfl, hrot.1⟩)
  | counterpartSet a' h => exact Or.inl ⟨h, by rw [hrot.1]⟩
  | setTracker _ _ => exact absurd hrot id

theorem HandlerWithoutRecoveryStrandsBundleAtHead :
    Properties.HandlerWithoutRecoveryStrandsBundleAtHead := by
  refine ⟨Unit, AtomicRecovery.wEnc, headCfg, headOkHooks, headRevertCode, 8, 1,
    AtomicRecovery.wWorld, 2, 1, [], [], ?_, ?_, head_wRouter_one, head_vault_alone _, ?_⟩
  · show AtomicRecovery.wRouter.handler 2 ≠ 0
    rw [head_wRouter_two]; decide
  · show AtomicRecovery.wRouter.handler 2 ≠ 4
    rw [head_wRouter_two]; decide
  · intro w' hr
    have hh : w'.router.handler 2 = 11 := by
      induction hr with
      | refl => exact head_wRouter_two
      | tail _ hstep ih => rw [hstep]; exact ih
    exact UnrecoverableHandlerBlocksBundleAtHead Unit AtomicRecovery.wEnc headCfg
      headOkHooks headRevertCode LegState.Revertable w' headStrandedBundle 2 11 hh
      (fun _ => head_revert_recoveryRevertsAt _) (head_revertCode_keeps 2) head_stranded_has

theorem PinRejectsNothingRecoverableHeadAccepts :
    Properties.PinRejectsNothingRecoverableHeadAccepts := by
  refine ⟨Unit, AtomicRecovery.wEnc, headCfg, headOkHooks, AtomicRecovery.declineOther,
    headNoOpCode, 8, 1, AtomicRecovery.wWorld, 13, by decide, head_dest, rfl, ?_⟩
  refine DirectBundleClaimIsNoOpAtHead _ _ _ _ _ _ _ head_dest ?_
  intro c hc
  rw [List.mem_singleton] at hc
  subst hc
  exact ⟨by decide, rfl⟩

/-! ## Certificates: witnesses -/

theorem DirectCallPremisesSatisfiable : Properties.DirectCallPremisesSatisfiable := by
  refine ⟨Unit, AtomicRecovery.wEnc, headCfg, headOkHooks, headNoOpCode, 8, 1,
    AtomicRecovery.wWorld, 13, 7, 1, [], by decide, head_dest, ?_,
    ⟨{ AtomicRecovery.wWorld with rest := () }, ?_⟩, ?_⟩
  · show AtomicRecovery.wRouter.handler 1 ≠ 0
    rw [head_wRouter_one]; decide
  · have h := head_vault_step_unit headNoOpCode AtomicRecovery.wWorld head_wRouter_one rfl rfl
    rw [recoverCallAtHead_routerCall] at h
    exact h
  · rw [recoverCallAtHead_direct (show (13 : Address) ≠ headCfg.router by decide)]
    rfl

theorem DirectValueLegRefundSatisfiable : Properties.DirectValueLegRefundSatisfiable := by
  refine ⟨AtomicRecovery.wEnc, headCfg, headLedgerHooks, headNoOpCode, 8, 1,
    AtomicRecovery.ledgerWorld,
    { AtomicRecovery.ledgerWorld with
      rest := Function.update AtomicRecovery.ledgerWorld.rest (narrow 13)
        (AtomicRecovery.ledgerWorld.rest (narrow 13) + (5 : UInt256).val) },
    ⟨headCfg.router, 13, 5, .other⟩, by decide, by decide, head_dest, by decide, ?_,
    by dsimp only; exact Function.update_self _ _ _⟩
  rw [CrossBaseValueLegRefundAtHead _ _ _ _ _ _ _ _ _ (by decide) (by decide) head_dest (by decide),
    ntvRecover_known (md := baseRefundMint 13 5) (x₁ := AtomicRecovery.ledgerWorld.rest) rfl
      AtomicRecovery.wVault_known_one.1 AtomicRecovery.wVault_known_one.2 rfl]
  rfl

theorem head_wVault_origin_base : AtomicRecovery.wVault.originChain 77 = 0 :=
  NativeTokenVault.sn_originChain_of_ne NativeTokenVault.empty.vault 1 6 9 1 (by decide)

theorem head_wVault_unaware_base : AtomicRecovery.VaultUnaware AtomicRecovery.wCfg AtomicRecovery.wVault 77 :=
  ⟨NativeTokenVault.sn_token_of_ne _ _ _ _ _ (by decide), by rw [head_wVault_origin_base]; decide⟩

theorem head_wFails_base (m : Option MintData) :
    AtomicRecovery.FailsAssetIdCheck AtomicRecovery.wEnc AtomicRecovery.wCfg 77 m := by
  intro md _ c _
  show (77 : AssetId) ≠ AtomicRecovery.wEnc c 4 _
  unfold AtomicRecovery.wEnc; decide

theorem SameBaseValueLegRefundSatisfiable : Properties.SameBaseValueLegRefundSatisfiable := by
  have hn : AtomicRecovery.ledgerWorld.vault.originChain headCfg.baseAsset ≠ headCfg.thisChain := by
    show AtomicRecovery.wVault.originChain 77 ≠ 7
    rw [head_wVault_origin_base]; decide
  refine ⟨AtomicRecovery.wEnc, headCfg, headLedgerHooks, headNoOpCode, 8,
    AtomicRecovery.ledgerWorld,
    { AtomicRecovery.ledgerWorld with
      rest := Function.update AtomicRecovery.ledgerWorld.rest (narrow 13)
        (AtomicRecovery.ledgerWorld.rest (narrow 13) + (5 : UInt256).val) },
    ⟨headCfg.router, 13, 5, .other⟩, by decide, by decide, head_dest, rfl, hn, ?_,
    by dsimp only; exact Function.update_self _ _ _, ?_⟩
  · rw [SameBaseValueLegRefundAtHead _ _ _ _ _ _ _ _ (by decide) (by decide) head_dest rfl hn]
    rfl
  · exact AtomicRecovery.ntvRecover_unaware head_wVault_unaware_base (head_wFails_base _)

theorem VaultRecoverAtHeadOffBaseSatisfiable : Properties.VaultRecoverAtHeadOffBaseSatisfiable := by
  refine ⟨Unit, AtomicRecovery.wEnc, headCfg, headOkHooks, AtomicRecovery.wWorld, headCfg.router, 0, 8,
    1, some AtomicRecovery.wMd, head_dest, by decide, ?_⟩
  rw [vaultRecoverAtHead_offBase head_dest (by decide),
    ntvRecover_known (md := AtomicRecovery.wMd) (x₁ := ()) rfl AtomicRecovery.wVault_known_one.1
      AtomicRecovery.wVault_known_one.2 rfl]
  rfl

theorem DirectBundleClaimIsNoOpSatisfiable : Properties.DirectBundleClaimIsNoOpSatisfiable := by
  refine ⟨headCfg, ⟨8, 1, [directCallAtHead headCfg.router 13 0 (.finalizeDeposit 7 1 [])]⟩, 7, 1, [],
    13, head_dest, ?_, List.mem_singleton.mpr rfl⟩
  intro c hc
  rw [List.mem_singleton] at hc
  subst hc
  exact ⟨by decide, rfl⟩

theorem RouterSenderIffIndirectSatisfiable : Properties.RouterSenderIffIndirectSatisfiable :=
  ⟨headCfg, 13, 1, [], .other, by decide, rfl, by decide⟩

theorem RoutingPremisesSatisfiable : Properties.RoutingPremisesSatisfiable := by
  have h2 : AtomicRecovery.wWorld.router.handler 2 = 11 := head_wRouter_two
  exact ⟨Unit, AtomicRecovery.wEnc, headCfg, headOkHooks, headNoOpCode,
    AtomicRecovery.wWorld, AtomicRecovery.wWorld, 8, 7, 2, [], head_dest, head_ntv_ne_zero,
    by rw [h2]; decide, by rw [h2]; decide, rfl,
    CustomHandlerRecoveredByItsHandler _ _ _ _ _ _ _ _ _ _ _ head_dest (by rw [h2]; decide)
      (by rw [h2]; decide) rfl⟩

theorem NoRotationKeepsHandlerSatisfiable : Properties.NoRotationKeepsHandlerSatisfiable := by
  refine ⟨headK, AtomicRecovery.wRouter, AllWriters.pointAt AtomicRecovery.wRouter 1 11,
    [.counterpartSet 1 11], 2, 11,
    AllWriters.ARun.snoc AllWriters.ARun.nil (AllWriters.AStep.counterpartSet rfl), head_wRouter_two,
    by decide, ?_, 1, ?_⟩
  · intro op hop
    rw [List.mem_singleton] at hop
    subst hop
    exact fun h => absurd h.1 (by decide)
  · rw [AllWriters.pointAt_handler_self, head_wRouter_one]
    decide

theorem HandlerMovesOnlyByRotationSatisfiable : Properties.HandlerMovesOnlyByRotationSatisfiable :=
  ⟨headK, .counterpartSet 1 11, AtomicRecovery.wRouter, AllWriters.pointAt AtomicRecovery.wRouter 1 11,
    1, AllWriters.AStep.counterpartSet rfl,
    by rw [AllWriters.pointAt_handler_self, head_wRouter_one]; decide,
    by rw [head_wRouter_one]; decide⟩

theorem LoggedRoutingPremisesSatisfiable : Properties.LoggedRoutingPremisesSatisfiable := by
  have hid : headK.enc 7 9 0 = 2 := by
    show AtomicRecovery.wEnc 7 9 0 = 2
    unfold AtomicRecovery.wEnc; decide
  have hguard : SetGuard AtomicRecovery.wEnc 7 4 4 AtomicRecovery.wRouter 4 0 :=
    ⟨Or.inl rfl, by decide⟩
  have hrun : AllWriters.ARun headK AtomicRecovery.wRouter [.register 4 0 4]
      (setHandler AtomicRecovery.wEnc 7 4 4 AtomicRecovery.wRouter 4 0 4) :=
    AllWriters.ARun.snoc AllWriters.ARun.nil (AllWriters.AStep.register hguard)
  have hwritten : writtenId AtomicRecovery.wEnc 7 4 4 4 0 = 1 := by
    unfold writtenId senderOf AtomicRecovery.wEnc; decide
  have hR₂ : (setHandler AtomicRecovery.wEnc 7 4 4 AtomicRecovery.wRouter 4 0 4).handler 2 = 11 := by
    rw [handler_frame _ _ _ _ _ _ _ _ _ (by rw [hwritten]; decide), head_wRouter_two]
  have hsend : senderOf headK.ntv headK.ntvAddr 4 = 4 := senderOf_self _ _
  refine ⟨Unit, AtomicRecovery.wEnc, headCfg, headOkHooks, headNoOpCode, headK,
    AtomicRecovery.wRouter, [.register 4 0 4],
    ⟨setHandler AtomicRecovery.wEnc 7 4 4 AtomicRecovery.wRouter 4 0 4, AtomicRecovery.wVault, false, ()⟩,
    8, 1, 7, 9, 0, [], head_dest, head_ntv_ne_zero, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hid]
    show AllWriters.ARun headK (burnRouter AtomicRecovery.wCfg AtomicRecovery.wRouter 2) _ _
    rw [head_burnRouter_two]
    exact hrun
  · refine ⟨_, List.mem_singleton.mpr rfl, (7, 4, 0), ?_, by decide⟩
    show some (headK.thisChain, senderOf headK.ntv headK.ntvAddr 4, (0 : AssetData)) = some (7, 4, 0)
    rw [hsend]
    rfl
  · intro op hop p hp
    rw [List.mem_singleton] at hop
    subst hop
    have hp' : some ((7 : Chain), (4 : Address), (0 : AssetData)) = some p := by
      rw [← hp]
      show some ((7 : Chain), (4 : Address), (0 : AssetData))
        = some (headK.thisChain, senderOf headK.ntv headK.ntvAddr 4, (0 : AssetData))
      rw [hsend]
      rfl
    cases hp'
    exact AtomicRecovery.wEnc_injOn 7 7 0 0
  · intro caller d h hmem heq
    rw [List.mem_singleton] at hmem
    cases hmem
    rw [hsend] at heq
    exact absurd heq (by decide)
  · intro a' h hmem
    rw [List.mem_singleton] at hmem
    cases hmem
  · intro hmem
    rw [List.mem_singleton] at hmem
    cases hmem
  · rw [hid]
    show AtomicRecovery.burnHandler AtomicRecovery.wCfg AtomicRecovery.wRouter 2 ≠ 4
    rw [head_burnHandler_two]
    decide
  · rw [hid, head_custom_noop_step _ _ 2 [] 1 (by rw [show
        (⟨setHandler AtomicRecovery.wEnc 7 4 4 AtomicRecovery.wRouter 4 0 4, AtomicRecovery.wVault,
          false, ()⟩ : World Unit).router.handler 2 = 11 from hR₂]; decide)
      (by rw [show
        (⟨setHandler AtomicRecovery.wEnc 7 4 4 AtomicRecovery.wRouter 4 0 4, AtomicRecovery.wVault,
          false, ()⟩ : World Unit).router.handler 2 = 11 from hR₂]; decide)]
    rfl

theorem RouterLegReachesBurnHandlerSatisfiable :
    Properties.RouterLegReachesBurnHandlerSatisfiable := by
  have h2 : (⟨AllWriters.pointAt AtomicRecovery.wRouter 1 11, AtomicRecovery.wVault, false, ()⟩ :
      World Unit).router.handler 2 = 11 := by
    show (AllWriters.pointAt AtomicRecovery.wRouter 1 11).handler 2 = 11
    rw [AllWriters.pointAt_handler_ne _ _ (by decide), head_wRouter_two]
  refine ⟨Unit, AtomicRecovery.wEnc, headCfg, headOkHooks, headNoOpCode, headK,
    AtomicRecovery.wRouter, [.counterpartSet 1 11],
    ⟨AllWriters.pointAt AtomicRecovery.wRouter 1 11, AtomicRecovery.wVault, false, ()⟩, 8, 1, 2, [],
    head_dest, head_ntv_ne_zero, ?_, List.cons_ne_nil _ _, ?_, ?_, ?_⟩
  · show AllWriters.ARun headK (burnRouter AtomicRecovery.wCfg AtomicRecovery.wRouter 2) _ _
    rw [head_burnRouter_two]
    exact AllWriters.ARun.snoc AllWriters.ARun.nil (AllWriters.AStep.counterpartSet rfl)
  · intro op hop
    rw [List.mem_singleton] at hop
    subst hop
    exact fun h => absurd h.1 (by decide)
  · show AtomicRecovery.burnHandler AtomicRecovery.wCfg AtomicRecovery.wRouter 2 ≠ 4
    rw [head_burnHandler_two]
    decide
  · rw [head_custom_noop_step _ _ 2 [] 1 (by rw [h2]; decide) (by rw [h2]; decide)]
    rfl

theorem PreparedBurnRefundAtHeadSatisfiable : Properties.PreparedBurnRefundAtHeadSatisfiable := by
  open NativeTokenVaultBase in
  have hw : WellFormed witnessPrepState := ⟨witnessToken_ledger, witnessPrep_rc⟩
  have htok : witnessPrepState.registry.tokenForAsset (2 + 1) = 5 := witnessPrep_token
  have hs : InScope witnessPrepState witnessRequest := by
    refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    show (if (0 : NativeTokenVaultBase.Address) = 0 then
      witnessPrepState.registry.tokenForAsset (2 + 1) else 0) = 5
    rw [ite_eq_left rfl, htok]
  have hsel : selectedToken witnessPrepState witnessRequest = 5 := hs.2.2.2.2
  have he : EntryAllowed witnessPrepState witnessRequest := by
    refine ⟨rfl, rfl, rfl, ?_, ?_, by decide⟩
    · rw [hsel]; decide
    · rw [hsel]; exact witnessPrep_asset
  have hb : witnessRequest.data.amount.val ≤ witnessPrepState.token.balances 11 := by
    show (1 : UInt256).val ≤ Function.update (fun _ => 0) (11 : NativeTokenVaultBase.Address)
      (0 + (1 : UInt256).val) 11
    rw [Function.update_self]
    decide
  obtain ⟨out, hout⟩ := preparation_enabled (hooks := witnessPrepHooks) (accounted := ())
    (metadata := []) hw hs he rfl (by decide) hb (by decide) (by decide) rfl rfl
  have ho : AtomicRecovery.pVault.originChain (2 + 1) = 1 :=
    NativeTokenVault.sn_originChain_self _ _ _ _ _
  have htk : AtomicRecovery.pVault.token (2 + 1) = 6 := NativeTokenVault.sn_token_self _ _ _ _ _
  have hn : AtomicRecovery.pVault.originChain (2 + 1) ≠ AtomicRecovery.wCfg.thisChain := by
    rw [ho]; decide
  have ht : AtomicRecovery.pVault.token (2 + 1) ≠ 0 := by rw [htk]; decide
  have hd : (8 : Chain) ≠ 99 := by decide
  have hn0 : AtomicRecovery.wCfg.ntv ≠ 0 := by decide
  have hb : witnessRequest.assetId ≠ 77 := by decide
  refine ⟨Unit, witnessPrepHooks, witnessPrepState, witnessRequest, out, Unit, AtomicRecovery.wEnc,
    { toConfig := AtomicRecovery.wCfg, l1Chain := 99, baseAsset := 77,
      decodeMint := fun _ => some out.data },
    headOkHooks, headNoOpCode, 8, 1,
    ⟨⟨fun _ => 4, fun _ => 0⟩, AtomicRecovery.pVault, false, ()⟩, [], (), hw, hout, by decide, hd,
    rfl, rfl, hn0, hb, rfl, hn, ht, rfl, ?_⟩
  rw [PreparedBurnRefundsDepositorAtHead Unit witnessPrepHooks witnessPrepState witnessRequest out hw
    hout Unit AtomicRecovery.wEnc
    { toConfig := AtomicRecovery.wCfg, l1Chain := 99, baseAsset := 77,
      decodeMint := fun _ => some out.data }
    headOkHooks headNoOpCode 8 1 ⟨⟨fun _ => 4, fun _ => 0⟩, AtomicRecovery.pVault, false, ()⟩
    [] () hd rfl rfl hn0 hb rfl hn ht rfl]
  rfl

theorem L2RotationSatisfiable : Properties.L2RotationSatisfiable := by
  refine ⟨headK, [.seed], AllWriters.pointAt empty 0 4,
    AllWriters.pointAt (AllWriters.pointAt empty 0 4) 0 13, .counterpartSet 0 13, 0, rfl,
    AllWriters.ARun.snoc AllWriters.ARun.nil AllWriters.AStep.seed,
    AllWriters.AStep.counterpartSet rfl, ?_, ?_⟩
  · rw [AllWriters.pointAt_handler_self]; decide
  · rw [AllWriters.pointAt_handler_self, AllWriters.pointAt_handler_self]; decide

theorem ZeroedHandlerReachableByCounterpart : Properties.ZeroedHandlerReachableByCounterpart :=
  ⟨headK, AtomicRecovery.wRouter, AllWriters.pointAt AtomicRecovery.wRouter 1 0, 1, rfl,
    by rw [head_wRouter_one]; decide, AllWriters.AStep.counterpartSet rfl,
    AllWriters.pointAt_handler_self _ _ _⟩

theorem RevertingCallBlocksClaimSatisfiable : Properties.RevertingCallBlocksClaimSatisfiable := by
  refine ⟨Unit, headCfg,
    recoverCallAtHead AtomicRecovery.wEnc headCfg headOkHooks headRevertCode,
    AtomicRecovery.wWorld, headStrandedBundle, fun u => u.router.handler 2 = 11,
    fun c => c.sender = headCfg.router ∧ ∃ src data, c.data = .finalizeDeposit src 2 data,
    ?_, ?_, head_stranded_has, head_wRouter_two,
    ⟨routerCallAtHead headCfg 1 [], List.mem_cons_of_mem _ List.mem_cons_self, ?_, head_vault_alone _⟩⟩
  · intro c _ u u' x hu hs
    rw [recoverCallAtHead_keeps_handler (head_revertCode_keeps 2) hs]
    exact hu
  · intro c _ hc u hu
    exact routerCallOn_blocks (fun _ => head_revert_recoveryRevertsAt _) hc hu
  · rintro ⟨-, src, data, hd⟩
    injection hd with _ h2
    exact absurd h2 (by decide)

theorem UnrecoverableHandlerBlocksBundleSatisfiable :
    Properties.UnrecoverableHandlerBlocksBundleSatisfiable :=
  ⟨Unit, AtomicRecovery.wEnc, headCfg, headOkHooks, headRevertCode, AtomicRecovery.wWorld,
    headStrandedBundle, 2, 11, head_wRouter_two, by decide, by decide,
    head_revert_recoveryRevertsAt _, head_revertCode_keeps 2, head_stranded_has,
    ⟨routerCallAtHead headCfg 1 [], List.mem_cons_of_mem _ List.mem_cons_self, head_vault_alone _⟩⟩

theorem NothingRecoveredSatisfiable : Properties.NothingRecoveredSatisfiable := by
  refine ⟨Unit, AtomicRecovery.wEnc, headCfg, headOkHooks, headNoOpCode,
    AtomicRecovery.wWorld,
    ⟨8, 1, [⟨headCfg.router, headCfg.router, 0, .other⟩, directCallAtHead headCfg.router 13 0 .other]⟩,
    head_dest, List.cons_ne_nil _ _, ?_, ⟨_, List.mem_cons_self, rfl⟩, ?_⟩
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inl ⟨rfl, rfl⟩
    · rw [List.mem_singleton] at hc
      subst hc
      exact Or.inr ⟨by decide, rfl⟩
  · apply recoverBundleAtHead_noop
    intro c hc u
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [recoverCallAtHead_fromRouter rfl, recoverAtomicCallAtHead_other head_dest]
    · rw [List.mem_singleton] at hc
      subst hc
      rw [recoverCallAtHead_direct (show (13 : Address) ≠ headCfg.router by decide)]
      rfl

end Contracts.AssetRouter.AtomicRecoveryAtHead
