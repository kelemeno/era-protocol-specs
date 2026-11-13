import EraSpec.Protocol.AssetBridgePreparation.Properties.FullRecovery
import EraSpec.Protocol.AssetBridgePreparation.Proofs.Model
import EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecovery
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.ModelCorrespondence

/-!
# Proofs: when an atomic refund restores a bundle in full

The proofs use `Contracts.AssetRouter.AtomicRecovery`'s branch lemmas for the vault's refund
(`recoverAtomicCall_known`, `recoverAtomicCall_native`).

* **One deposit call.** In the local token model a router deposit call on a registered asset is
  one tracker step followed by one token-model credit (`depositRefund_step`).
* **The loop.** An induction over the bundle (`depositRefund_loop`) turns that into the
  tracker run and the credit run side by side.
* **The closed form.** A second induction carries the "covered for the rest of the bundle"
  invariant: each step spends exactly its own share of the escrow or of the supply headroom
  (`creditRun_exact`).
* **The trace.** At trace level, the headroom comes from the preparation trace's conservation, and
  the token and branch from the registry correspondence.
-/

namespace AssetBridgePreparation.FullRecovery

open Contracts
open Contracts.AssetRouter (Chain AssetId Address AssetIdOf)
open Contracts.AssetRouter.AtomicRecovery (Config Call CallData World Hooks MintData Addr160
  recoverCall recoverAtomicCall recoverBundle claimRefund outcomes ntvRecover vaultRefund
  routerCall AtomicBundleValid)
open AttackVectors.RecoveryLimits (Outcome LegState ClaimAccepted recoveredCount LoopCompletes)

variable {A : Type}

/-! ## One deposit call -/

/-- A tracker hook that reverts makes the router's refund revert. -/
theorem depositRefund_hook_none {X : Type} {enc : AssetIdOf} {cfg : Config} {hk : Hooks X}
    {w : World X} {dest src : Chain} {a : AssetId} {md : MintData}
    (hp : w.paused = false) (hf : hk.fromChain w.rest dest a md.amount = none) :
    recoverAtomicCall enc cfg hk w cfg.manager dest (.finalizeDeposit src a (some md)) = none := by
  rw [AssetRouter.AtomicRecovery.recoverAtomicCall_finalize]
  unfold ntvRecover vaultRefund
  rw [ite_eq_right (by simp [hp])]
  simp only [hf]
  rfl

/-- **One router deposit call, in the local token model, on a registered asset**: the tracker
step, then the token-model credit, returning `true`. -/
theorem depositRefund_step (enc : AssetIdOf) (cfg : Config) (vault : Addr160) (base : AssetId)
    (tr : TrackerHook A) (dep : DeployHook A) (other : OtherTargets (Ledgers A)) (dest : Chain)
    (w : World (Ledgers A)) (c : Call) (d : Deposit)
    (hp : w.paused = false) (hc : DepositCall cfg c d) (hreg : w.vault.token d.1 ≠ 0) :
    recoverCall enc cfg (localHooks vault base tr dep) other dest w c =
      (tr w.rest.tracker dest d.1 d.2.amount).bind fun t =>
        (creditStep vault base cfg.thisChain w.vault w.rest.token d).map fun L =>
          ({ w with rest := ⟨L, t⟩ }, true) := by
  obtain ⟨ht, src, hd⟩ := hc
  unfold recoverCall
  rw [ite_eq_left ht, hd]
  rcases htr : tr w.rest.tracker dest d.1 d.2.amount with _ | t
  · rw [depositRefund_hook_none hp (by simp [localHooks, htr])]
    rfl
  · have hf : (localHooks vault base tr dep).fromChain w.rest dest d.1 d.2.amount =
        some { w.rest with tracker := t } := by simp [localHooks, htr]
    by_cases hn : w.vault.originChain d.1 = cfg.thisChain
    · rw [AssetRouter.AtomicRecovery.recoverAtomicCall_native hp hn hf]
      simp only [Option.bind_some, creditStep, ite_eq_left hn]
      by_cases hb : d.1 = base
      · simp [localHooks, hb]
      · simp only [localHooks, ite_eq_right hb, Option.map_map]
        rfl
    · rw [AssetRouter.AtomicRecovery.recoverAtomicCall_known hp hn hreg hf]
      simp only [Option.bind_some, creditStep, ite_eq_right hn, localHooks, Option.map_map]
      rfl

/-! ## The loop and the claim -/

/-- **The loop over a deposit bundle is the tracker run and the credit run.** -/
theorem depositRefund_loop (enc : AssetIdOf) (cfg : Config) (vault : Addr160) (base : AssetId)
    (tr : TrackerHook A) (dep : DeployHook A) (other : OtherTargets (Ledgers A)) (dest : Chain) :
    ∀ (w : World (Ledgers A)) (calls : List Call) (ds : List Deposit),
      w.paused = false → DepositBundle cfg calls ds → (∀ d ∈ ds, w.vault.token d.1 ≠ 0) →
      recoverBundle (recoverCall enc cfg (localHooks vault base tr dep) other dest) w calls =
        (trackerRun tr dest w.rest.tracker ds).bind fun t =>
          (creditRun vault base cfg.thisChain w.vault w.rest.token ds).map fun L =>
            ({ w with rest := ⟨L, t⟩ }, ds.length) := by
  intro w calls ds hp hb hreg
  induction hb generalizing w with
  | nil => rfl
  | @cons c d calls ds hcd _ ih =>
    unfold recoverBundle
    rw [depositRefund_step enc cfg vault base tr dep other dest w c d hp hcd
      (hreg d List.mem_cons_self)]
    rcases htr : tr w.rest.tracker dest d.1 d.2.amount with _ | t
    · simp [trackerRun, htr]
    · rcases hcs : creditStep vault base cfg.thisChain w.vault w.rest.token d with _ | L₁
      · simp [trackerRun, creditRun, htr, hcs]
      · have ih' := ih { w with rest := ⟨L₁, t⟩ } hp
          (fun d' hd' => hreg d' (List.mem_cons_of_mem _ hd'))
        simp only [Option.bind_some, Option.map_some]
        rw [ih']
        simp only [trackerRun, creditRun, htr, hcs, Option.bind_some]
        rcases trackerRun tr dest t ds with _ | t'
        · rfl
        · rcases creditRun vault base cfg.thisChain w.vault L₁ ds with _ | L'
          · rfl
          · simp only [Option.bind_some, Option.map_some, ite_true, List.length_cons]
            congr 2
            omega

/-- **The claim over a deposit bundle.** -/
theorem depositRefund_claim (enc : AssetIdOf) (cfg : Config) (vault : Addr160) (base : AssetId)
    (tr : TrackerHook A) (dep : DeployHook A) (other : OtherTargets (Ledgers A)) (dest : Chain)
    (w : World (Ledgers A)) (calls : List Call) (ds : List Deposit)
    (hp : w.paused = false) (hb : DepositBundle cfg calls ds)
    (hreg : ∀ d ∈ ds, w.vault.token d.1 ≠ 0) :
    claimRefund (recoverCall enc cfg (localHooks vault base tr dep) other dest)
        LegState.Revertable w calls =
      if ds = [] then none else
        (trackerRun tr dest w.rest.tracker ds).bind fun t =>
          (creditRun vault base cfg.thisChain w.vault w.rest.token ds).map fun L =>
            (LegState.Reverted, { w with rest := ⟨L, t⟩ }) := by
  unfold claimRefund
  rw [ite_eq_right (by simp), depositRefund_loop enc cfg vault base tr dep other dest w calls ds
    hp hb hreg]
  rcases trackerRun tr dest w.rest.tracker ds with _ | t
  · simp
  · rcases creditRun vault base cfg.thisChain w.vault w.rest.token ds with _ | L
    · simp
    · by_cases hds : ds = []
      · subst hds; simp
      · simp [hds]

/-! ## Counting: terminality against full restoration -/

theorem loopCount_le_length {X : Type} {step : World X → Call → Option (World X × Bool)} :
    ∀ (calls : List Call) (w w' : World X) (n : ℕ),
      recoverBundle step w calls = some (w', n) → n ≤ calls.length
  | [], w, w', n, h => by unfold recoverBundle at h; cases h; rfl
  | c :: cs, w, w', n, h => by
    unfold recoverBundle at h
    rcases hs : step w c with _ | ⟨w₁, b⟩ <;> rw [hs] at h
    · cases h
    · dsimp only at h
      rcases hr : recoverBundle step w₁ cs with _ | ⟨w₂, k⟩ <;> rw [hr] at h
      · cases h
      · dsimp only at h
        have hn : (if b then 1 else 0) + k = n := (Prod.mk.inj (Option.some.inj h)).2
        have := loopCount_le_length cs w₁ w₂ k hr
        simp only [List.length_cons]
        cases b <;> simp at hn <;> omega

/-- A completed loop counted every call exactly when no call declined. -/
theorem loopCount_eq_length_iff {X : Type} {step : World X → Call → Option (World X × Bool)} :
    ∀ (calls : List Call) (w w' : World X) (n : ℕ),
      recoverBundle step w calls = some (w', n) →
        (n = calls.length ↔ Outcome.declined ∉ outcomes step w calls)
  | [], w, w', n, h => by
    unfold recoverBundle at h; cases h; simp [outcomes]
  | c :: cs, w, w', n, h => by
    unfold recoverBundle at h
    rcases hs : step w c with _ | ⟨w₁, b⟩ <;> rw [hs] at h
    · cases h
    · dsimp only at h
      rcases hr : recoverBundle step w₁ cs with _ | ⟨w₂, k⟩ <;> rw [hr] at h
      · cases h
      · dsimp only at h
        have hn : (if b then 1 else 0) + k = n := (Prod.mk.inj (Option.some.inj h)).2
        have ih := loopCount_eq_length_iff cs w₁ w₂ k hr
        have hk := loopCount_le_length cs w₁ w₂ k hr
        unfold outcomes
        rw [hs]
        dsimp only
        subst hn
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, List.mem_cons, true_or,
            not_true_eq_false, iff_false]
          omega
        · simp only [↓reduceIte, List.length_cons, List.mem_cons, reduceCtorEq, false_or]
          rw [← ih]
          omega

theorem terminal_full_iff_no_decline {X : Type} (step : World X → Call → Option (World X × Bool))
    (w w' : World X) (calls : List Call)
    (h : claimRefund step LegState.Revertable w calls = some (LegState.Reverted, w')) :
    recoverBundle step w calls = some (w', calls.length) ↔
      Outcome.declined ∉ outcomes step w calls := by
  unfold claimRefund at h
  rw [ite_eq_right (by simp)] at h
  rcases hr : recoverBundle step w calls with _ | ⟨w₁, n⟩ <;> rw [hr] at h
  · cases h
  · dsimp only at h
    by_cases hn : n = 0
    · rw [ite_eq_left hn] at h; cases h
    · rw [ite_eq_right hn] at h
      have hw : w₁ = w' := (Prod.mk.inj (Option.some.inj h)).2
      subst hw
      rw [← loopCount_eq_length_iff calls w w₁ n hr]
      constructor
      · intro h'; exact (Prod.mk.inj (Option.some.inj h')).2
      · intro h'; rw [h']

/-- A router call on `finalizeDeposit` data is the vault's refund followed by `return true`. -/
theorem routerDeposit_step {X : Type} {enc : AssetIdOf} {cfg : Config} {hk : Hooks X}
    {other : OtherTargets X} {dest : Chain} {w : World X} {c : Call} {src : Chain} {a : AssetId}
    {m : Option MintData} (ht : c.target = cfg.router) (hd : c.data = .finalizeDeposit src a m) :
    recoverCall enc cfg hk other dest w c =
      (ntvRecover enc cfg hk w cfg.router 0 dest a m).map (fun w' => (w', true)) := by
  unfold recoverCall
  rw [ite_eq_left ht, hd, AssetRouter.AtomicRecovery.recoverAtomicCall_finalize]

theorem routerDeposits_never_decline {X : Type} {enc : AssetIdOf} {cfg : Config} {hk : Hooks X}
    {other : OtherTargets X} {dest : Chain} :
    ∀ (calls : List Call) (w : World X), (∀ c ∈ calls, RouterDepositShaped cfg c) →
      Outcome.declined ∉ outcomes (recoverCall enc cfg hk other dest) w calls
  | [], w, _ => by simp [outcomes]
  | c :: cs, w, hs => by
    obtain ⟨ht, src, a, m, hd⟩ := hs c List.mem_cons_self
    unfold outcomes
    rw [routerDeposit_step ht hd]
    rcases ntvRecover enc cfg hk w cfg.router 0 dest a m with _ | w₁
    · simp
    · simp only [Option.map_some, ↓reduceIte, List.mem_cons, reduceCtorEq, false_or]
      exact routerDeposits_never_decline cs w₁ (fun c hc => hs c (List.mem_cons_of_mem _ hc))

/-! ## Covered credits succeed, exactly -/

theorem amountSum_cons (p : Deposit → Bool) (d : Deposit) (ds : List Deposit) :
    amountSum p (d :: ds) = (if p d then d.2.amount.val else 0) + amountSum p ds := by
  unfold amountSum
  by_cases h : p d <;> simp [h]

theorem mintedOn_cons (thisChain : Chain) (V : NativeTokenVault.Vault) (tok : Address)
    (d : Deposit) (ds : List Deposit) :
    mintedOn thisChain V tok (d :: ds) =
      (if V.originChain d.1 ≠ thisChain ∧ V.token d.1 = tok then d.2.amount.val else 0) +
        mintedOn thisChain V tok ds := by
  unfold mintedOn
  rw [amountSum_cons]
  simp only [decide_eq_true_eq]

theorem releasedOn_cons (thisChain : Chain) (V : NativeTokenVault.Vault) (tok : Address)
    (d : Deposit) (ds : List Deposit) :
    releasedOn thisChain V tok (d :: ds) =
      (if V.originChain d.1 = thisChain ∧ V.token d.1 = tok then d.2.amount.val else 0) +
        releasedOn thisChain V tok ds := by
  unfold releasedOn
  rw [amountSum_cons]
  simp only [decide_eq_true_eq]

theorem creditedTo_cons (V : NativeTokenVault.Vault) (tok : Address) (u : Addr160) (d : Deposit)
    (ds : List Deposit) :
    creditedTo V tok u (d :: ds) =
      (if V.token d.1 = tok ∧ d.2.originalCaller = u then d.2.amount.val else 0) +
        creditedTo V tok u ds := by
  unfold creditedTo
  rw [amountSum_cons]
  simp only [decide_eq_true_eq]

theorem credit_mint_balances (s : BridgedStandardERC20.State) (rcv u : Addr160) (amt : UInt256) :
    (BridgedStandardERC20.mintEffect s rcv amt).balances u =
      s.balances u + (if rcv = u then amt.val else 0) := by
  unfold BridgedStandardERC20.mintEffect
  by_cases h : rcv = u
  · subst h; simp
  · simp [Function.update_of_ne (Ne.symm h), h]

/-- The token model's transfer, as one balance law: what the owner sends, the recipient gets. -/
theorem credit_transfer_balances (s : BridgedStandardERC20.State) (owner rcv u : Addr160)
    (amt : UInt256) (hb : amt.val ≤ s.balances owner) :
    (BridgedStandardERC20.transferEffect s owner rcv amt).balances u +
        (if u = owner then amt.val else 0) =
      s.balances u + (if rcv = u then amt.val else 0) := by
  unfold BridgedStandardERC20.transferEffect
  simp only
  by_cases hr : u = rcv
  · subst hr
    rw [Function.update_self]
    by_cases ho : u = owner
    · subst ho
      simp only [Function.update_self, ite_true]
      omega
    · simp [ho]
  · rw [Function.update_of_ne hr]
    by_cases ho : u = owner
    · subst ho
      simp only [Function.update_self, ite_true, Ne.symm hr, ite_false]
      omega
    · simp [ho, Ne.symm hr]

/-- One credit on the head deposit, followed by exact credits of the rest, is the exact credits
of the whole list. -/
theorem exactCredits_cons {vault : Addr160} {thisChain : Chain} {V : NativeTokenVault.Vault}
    {L L' : Address → BridgedStandardERC20.State} {S₁ : BridgedStandardERC20.State}
    {d : Deposit} {ds : List Deposit}
    (hcfg : S₁.config = (L (V.token d.1)).config)
    (hsup : S₁.totalSupply = (L (V.token d.1)).totalSupply +
      (if V.originChain d.1 ≠ thisChain then d.2.amount.val else 0))
    (hbal : ∀ u, S₁.balances u +
        (if u = vault ∧ V.originChain d.1 = thisChain then d.2.amount.val else 0) =
      (L (V.token d.1)).balances u + (if d.2.originalCaller = u then d.2.amount.val else 0))
    (ih : ExactCredits vault thisChain V (Function.update L (V.token d.1) S₁) L' ds) :
    ExactCredits vault thisChain V L L' (d :: ds) := by
  obtain ⟨ihf, ihe⟩ := ih
  refine ⟨?_, ?_⟩
  · intro tok htok
    have hne : V.token d.1 ≠ tok := htok d List.mem_cons_self
    rw [ihf tok (fun d' hd' => htok d' (List.mem_cons_of_mem _ hd')),
      Function.update_of_ne (Ne.symm hne)]
  · intro tok
    obtain ⟨hc, hs, hb⟩ := ihe tok
    by_cases htok : V.token d.1 = tok
    · subst htok
      rw [Function.update_self] at hc hs hb
      refine ⟨hc.trans hcfg, ?_, ?_⟩
      · rw [hs, hsup, mintedOn_cons]
        by_cases hn : V.originChain d.1 = thisChain
        · simp [hn]
        · simp [hn]; omega
      · intro u
        have h1 := hb u
        have h2 := hbal u
        rw [releasedOn_cons, creditedTo_cons]
        by_cases hu : u = vault <;> by_cases hn : V.originChain d.1 = thisChain <;>
          by_cases hr : d.2.originalCaller = u <;>
          simp only [hu, hn, hr, and_true, true_and, and_false, ↓reduceIte,
            Nat.add_zero, Nat.zero_add] at h1 h2 ⊢ <;> omega
    · rw [Function.update_of_ne (Ne.symm htok)] at hc hs hb
      refine ⟨hc, ?_, ?_⟩
      · rw [hs, mintedOn_cons]
        simp [htok]
      · intro u
        rw [releasedOn_cons, creditedTo_cons]
        simpa [htok] using hb u

theorem exactCredits_nil (vault : Addr160) (thisChain : Chain) (V : NativeTokenVault.Vault)
    (L : Address → BridgedStandardERC20.State) : ExactCredits vault thisChain V L L [] :=
  ⟨fun _ _ => rfl, fun _ => ⟨rfl, by simp [mintedOn, amountSum],
    fun _ => by simp [releasedOn, creditedTo, amountSum]⟩⟩

/-- **Every covered credit succeeds, and the result is exact.**  The invariant is "covered for the
rest of the bundle": each step spends exactly its own share of the escrow (native) or of the
supply headroom (bridged). -/
theorem creditRun_exact (vault : Addr160) (base : AssetId) (thisChain : Chain)
    (V : NativeTokenVault.Vault) :
    ∀ (ds : List Deposit) (L : Address → BridgedStandardERC20.State),
      CreditsCovered vault base thisChain V L ds →
      ∃ L', creditRun vault base thisChain V L ds = some L' ∧ ExactCredits vault thisChain V L L' ds
  | [], L, _ => ⟨L, rfl, exactCredits_nil vault thisChain V L⟩
  | d :: ds, L, hc => by
    obtain ⟨hv, hr, hnat, hbr⟩ := hc
    have hr₀ : d.2.originalCaller ≠ 0 := hr d List.mem_cons_self
    by_cases hn : V.originChain d.1 = thisChain
    · -- native: release from the vault's escrow
      obtain ⟨hbase, hcov⟩ := hnat d List.mem_cons_self hn
      have hrel : releasedOn thisChain V (V.token d.1) (d :: ds) =
          d.2.amount.val + releasedOn thisChain V (V.token d.1) ds := by
        rw [releasedOn_cons]; simp [hn]
      have hamt : d.2.amount.val ≤ (L (V.token d.1)).balances vault := by omega
      obtain ⟨S₁, hS₁⟩ : ∃ S₁, BridgedStandardERC20.transferEffect (L (V.token d.1)) vault
          d.2.originalCaller d.2.amount = S₁ := ⟨_, rfl⟩
      have hstep : creditStep vault base thisChain V L d =
          some (Function.update L (V.token d.1) S₁) := by
        unfold creditStep BridgedStandardERC20.transfer
        rw [ite_eq_left hn, ite_eq_right hbase, ite_eq_left ⟨hv, hr₀, hamt⟩, hS₁]
        rfl
      have hlaw : ∀ u, S₁.balances u + (if u = vault then d.2.amount.val else 0) =
          (L (V.token d.1)).balances u + (if d.2.originalCaller = u then d.2.amount.val else 0) :=
        fun u => hS₁ ▸ credit_transfer_balances _ _ _ u _ hamt
      have hcfg : S₁.config = (L (V.token d.1)).config := by rw [← hS₁]; rfl
      have hsup₁ : S₁.totalSupply = (L (V.token d.1)).totalSupply := by rw [← hS₁]; rfl
      have hc₁ : CreditsCovered vault base thisChain V (Function.update L (V.token d.1) S₁) ds := by
        refine ⟨hv, fun d' hd' => hr d' (List.mem_cons_of_mem _ hd'), ?_, ?_⟩
        · intro d' hd' hn'
          obtain ⟨hb', hcov'⟩ := hnat d' (List.mem_cons_of_mem _ hd') hn'
          refine ⟨hb', ?_⟩
          by_cases htok : V.token d'.1 = V.token d.1
          · rw [htok, Function.update_self]
            rw [htok, hrel] at hcov'
            have h := hlaw vault
            rw [ite_eq_left (rfl : vault = vault)] at h
            by_cases hrv : d.2.originalCaller = vault
            · rw [ite_eq_left hrv] at h; omega
            · rw [ite_eq_right hrv] at h; omega
          · rw [Function.update_of_ne htok]
            rw [releasedOn_cons] at hcov'
            simpa [Ne.symm htok] using hcov'
        · intro d' hd' hn'
          obtain ⟨hcv, hsup⟩ := hbr d' (List.mem_cons_of_mem _ hd') hn'
          have hm : mintedOn thisChain V (V.token d'.1) (d :: ds) =
              mintedOn thisChain V (V.token d'.1) ds := by
            rw [mintedOn_cons]; simp [hn]
          rw [hm] at hsup
          by_cases htok : V.token d'.1 = V.token d.1
          · rw [htok, Function.update_self, hcfg, hsup₁]
            rw [htok] at hcv hsup
            exact ⟨hcv, hsup⟩
          · rw [Function.update_of_ne htok]
            exact ⟨hcv, hsup⟩
      obtain ⟨L', hrun, hex⟩ := creditRun_exact vault base thisChain V ds _ hc₁
      refine ⟨L', ?_, exactCredits_cons hcfg ?_ ?_ hex⟩
      · simp only [creditRun, hstep, Option.bind_some, hrun]
      · simp [hsup₁, hn]
      · intro u
        simpa [hn] using hlaw u
    · -- bridged: re-mint
      obtain ⟨hcv, hsup⟩ := hbr d List.mem_cons_self hn
      have hmint : mintedOn thisChain V (V.token d.1) (d :: ds) =
          d.2.amount.val + mintedOn thisChain V (V.token d.1) ds := by
        rw [mintedOn_cons]; simp [hn]
      obtain ⟨S₁, hS₁⟩ : ∃ S₁, BridgedStandardERC20.mintEffect (L (V.token d.1))
          d.2.originalCaller d.2.amount = S₁ := ⟨_, rfl⟩
      have hstep : creditStep vault base thisChain V L d =
          some (Function.update L (V.token d.1) S₁) := by
        unfold creditStep BridgedStandardERC20.mint
        rw [ite_eq_right hn, ite_eq_left ⟨by rw [hcv]; exact hv, hcv.symm, hr₀, by omega⟩, hS₁]
        rfl
      have hlaw : ∀ u, S₁.balances u =
          (L (V.token d.1)).balances u + (if d.2.originalCaller = u then d.2.amount.val else 0) :=
        fun u => hS₁ ▸ credit_mint_balances _ _ u _
      have hcfg : S₁.config = (L (V.token d.1)).config := by rw [← hS₁]; rfl
      have hsup₁ : S₁.totalSupply = (L (V.token d.1)).totalSupply + d.2.amount.val := by
        rw [← hS₁]; rfl
      have hc₁ : CreditsCovered vault base thisChain V (Function.update L (V.token d.1) S₁) ds := by
        refine ⟨hv, fun d' hd' => hr d' (List.mem_cons_of_mem _ hd'), ?_, ?_⟩
        · intro d' hd' hn'
          obtain ⟨hb', hcov'⟩ := hnat d' (List.mem_cons_of_mem _ hd') hn'
          refine ⟨hb', ?_⟩
          have hrel : releasedOn thisChain V (V.token d'.1) (d :: ds) =
              releasedOn thisChain V (V.token d'.1) ds := by
            rw [releasedOn_cons]; simp [hn]
          rw [hrel] at hcov'
          by_cases htok : V.token d'.1 = V.token d.1
          · rw [htok, Function.update_self, hlaw]
            rw [htok] at hcov'
            omega
          · rw [Function.update_of_ne htok]
            exact hcov'
        · intro d' hd' hn'
          obtain ⟨hcv', hsup'⟩ := hbr d' (List.mem_cons_of_mem _ hd') hn'
          by_cases htok : V.token d'.1 = V.token d.1
          · rw [htok, Function.update_self, hcfg, hsup₁]
            rw [htok, hmint] at hsup'
            rw [htok] at hcv'
            exact ⟨hcv', by omega⟩
          · rw [Function.update_of_ne htok]
            rw [mintedOn_cons] at hsup'
            exact ⟨hcv', by simpa [Ne.symm htok] using hsup'⟩
      obtain ⟨L', hrun, hex⟩ := creditRun_exact vault base thisChain V ds _ hc₁
      refine ⟨L', ?_, exactCredits_cons hcfg ?_ ?_ hex⟩
      · simp only [creditRun, hstep, Option.bind_some, hrun]
      · simp [hsup₁, hn]
      · intro u
        rw [hlaw]
        simp [hn]

theorem creditStep_wellFormed {vault : Addr160} {base : AssetId} {thisChain : Chain}
    {V : NativeTokenVault.Vault} {L L₁ : Address → BridgedStandardERC20.State} {d : Deposit}
    (h : creditStep vault base thisChain V L d = some L₁) (tok : Address)
    (hw : BridgedStandardERC20.WellFormed (L tok)) : BridgedStandardERC20.WellFormed (L₁ tok) := by
  unfold creditStep at h
  by_cases hn : V.originChain d.1 = thisChain
  · rw [ite_eq_left hn] at h
    by_cases hb : d.1 = base
    · rw [ite_eq_left hb] at h; cases h
    · rw [ite_eq_right hb] at h
      obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp h
      by_cases htok : tok = V.token d.1
      · subst htok
        rw [Function.update_self]
        exact (BridgedStandardERC20.transfer_preserves_ledger hw hl).1
      · rw [Function.update_of_ne htok]; exact hw
  · rw [ite_eq_right hn] at h
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp h
    by_cases htok : tok = V.token d.1
    · subst htok
      rw [Function.update_self]
      exact BridgedStandardERC20.mint_preserves_ledger hw hl
    · rw [Function.update_of_ne htok]; exact hw

theorem creditRun_wellFormed {vault : Addr160} {base : AssetId} {thisChain : Chain}
    {V : NativeTokenVault.Vault} :
    ∀ {ds : List Deposit} {L L' : Address → BridgedStandardERC20.State},
      creditRun vault base thisChain V L ds = some L' → ∀ tok,
        BridgedStandardERC20.WellFormed (L tok) → BridgedStandardERC20.WellFormed (L' tok)
  | [], L, L', h => by
    cases h
    exact fun _ hw => hw
  | d :: ds, L, L', h => by
    simp only [creditRun] at h
    obtain ⟨L₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    exact fun tok hw => creditRun_wellFormed h₂ tok (creditStep_wellFormed h₁ tok hw)

theorem trackerRun_isSome {tr : TrackerHook A} {dest : Chain} :
    ∀ (ds : List Deposit) (t : A), (∀ d ∈ ds, ∀ t', (tr t' dest d.1 d.2.amount).isSome) →
      (trackerRun tr dest t ds).isSome
  | [], _, _ => rfl
  | d :: ds, t, h => by
    obtain ⟨t₁, ht₁⟩ := Option.isSome_iff_exists.mp (h d List.mem_cons_self t)
    simp only [trackerRun, ht₁, Option.bind_some]
    exact trackerRun_isSome ds t₁ (fun d' hd' => h d' (List.mem_cons_of_mem _ hd'))

/-! ## The world-level headline -/

theorem registeredDepositBundleFullyRecovered (enc : AssetIdOf) (cfg : Config) (vault : Addr160)
    (base : AssetId) (tr : TrackerHook A) (dep : DeployHook A) (other : OtherTargets (Ledgers A))
    (dest : Chain) (w : World (Ledgers A)) (calls : List Call) (ds : List Deposit)
    (hp : w.paused = false) (hb : DepositBundle cfg calls ds) (hne : ds ≠ [])
    (hreg : ∀ d ∈ ds, w.vault.token d.1 ≠ 0) (htr : (trackerRun tr dest w.rest.tracker ds).isSome)
    (hcov : CreditsCovered vault base cfg.thisChain w.vault w.rest.token ds) :
    ∃ w', claimRefund (recoverCall enc cfg (localHooks vault base tr dep) other dest)
        LegState.Revertable w calls = some (LegState.Reverted, w')
      ∧ recoverBundle (recoverCall enc cfg (localHooks vault base tr dep) other dest) w calls
          = some (w', calls.length)
      ∧ w'.router = w.router ∧ w'.vault = w.vault ∧ w'.paused = w.paused
      ∧ ExactCredits vault cfg.thisChain w.vault w.rest.token w'.rest.token ds
      ∧ ∀ tok, BridgedStandardERC20.WellFormed (w.rest.token tok) →
          BridgedStandardERC20.WellFormed (w'.rest.token tok) := by
  obtain ⟨L', hrun, hex⟩ := creditRun_exact vault base cfg.thisChain w.vault ds w.rest.token hcov
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp htr
  have hrb := depositRefund_loop enc cfg vault base tr dep other dest w calls ds hp hb hreg
  rw [ht', hrun] at hrb
  refine ⟨{ w with rest := ⟨L', t'⟩ }, ?_, ?_, rfl, rfl, rfl, hex, creditRun_wellFormed hrun⟩
  · rw [depositRefund_claim enc cfg vault base tr dep other dest w calls ds hp hb hreg,
      ite_eq_right hne, ht', hrun]
    rfl
  · rw [hrb, hb.length_eq]
    rfl

/-! ## The preparation trace -/

theorem prepared_inScope {Acc : Type} {hooks : NativeTokenVaultBase.Hooks Acc}
    {s : NativeTokenVaultBase.State Acc} {r : NativeTokenVaultBase.Request}
    {out : NativeTokenVaultBase.Result Acc} (h : NativeTokenVaultBase.prepare hooks s r = some out) :
    NativeTokenVaultBase.InScope s r := by
  unfold NativeTokenVaultBase.prepare at h
  by_cases hg : NativeTokenVaultBase.InScope s r ∧ NativeTokenVaultBase.EntryAllowed s r
  · exact hg.1
  · rw [ite_eq_right hg] at h; cases h

theorem burned_owner_ne_zero {s t : BridgedStandardERC20.State}
    {caller owner : BridgedStandardERC20.Address} {amount : UInt256}
    (h : BridgedStandardERC20.burn s caller owner amount = some t) : owner ≠ 0 := by
  unfold BridgedStandardERC20.burn at h
  by_cases hg : BridgedStandardERC20.BurnAllowed s caller owner amount
  · exact hg.2.2.1
  · rw [ite_eq_right hg] at h; cases h

theorem pendingSound_step {Acc : Type} {hooks : NativeTokenVaultBase.Hooks Acc}
    {s t : Ledger Acc} (hw : NativeTokenVaultBase.WellFormed s.vault) (hs : PendingSound s)
    (h : Step hooks s t) : PendingSound t := by
  cases h with
  | @prepare r out hp =>
    have hcfg := (NativeTokenVaultBase.preparation_preserves_ledger hw hp).2.1
    have hbind := (NativeTokenVaultBase.preparation_asset_binding hw hp).1
    have hcaller := (NativeTokenVaultBase.preparation_payload hw hp).1
    have hburn := (NativeTokenVaultBase.preparation_backed hw hp).1
    have hscope := prepared_inScope hp
    have hdep : out.data.originalCaller ≠ 0 := by
      rw [hcaller]; exact burned_owner_ne_zero hburn
    intro o ho
    simp only [hcfg]
    rcases List.mem_append.mp ho with ho | ho
    · exact hs o ho
    · rw [List.mem_singleton] at ho
      subst ho
      exact ⟨hbind, hdep, hscope.1, hscope.2.1, hscope.2.2.2.1⟩
  | spend ht => exact hs

theorem pendingSound_reach {Acc : Type} {hooks : NativeTokenVaultBase.Hooks Acc}
    {s t : Ledger Acc} (hw : NativeTokenVaultBase.WellFormed s.vault) (hs : PendingSound s)
    (h : Reach hooks s t) : PendingSound t := by
  induction h with
  | refl => exact hs
  | @tail u v hr hstep ih =>
    exact pendingSound_step (reachable_conservation hw hr).1 ih hstep

theorem fullRecovery_pending_append (l₁ l₂ : List Obligation) :
    pendingAmount (l₁ ++ l₂) = pendingAmount l₁ + pendingAmount l₂ := by
  simp [pendingAmount, List.map_append, List.sum_append]

theorem fullRecovery_pending_subperm {l₁ l₂ : List Obligation} (h : l₁.Subperm l₂) :
    pendingAmount l₁ ≤ pendingAmount l₂ := by
  obtain ⟨l, hp, hs⟩ := h
  unfold pendingAmount
  rw [← (hp.map fun o => o.data.amount.val).sum_eq]
  exact (hs.map _).sum_le_sum (fun _ _ => Nat.zero_le _)

/-- On deposits of one asset `a` that is bridged, with token `T`: the totals are the
obligation-level totals. -/
theorem trackedDeposit_sums {thisChain : Chain} {V : NativeTokenVault.Vault} {a : AssetId}
    {T : Address} (hT : V.token a = T) (hn : V.originChain a ≠ thisChain) :
    ∀ (obs : List Obligation), (∀ o ∈ obs, o.assetId = a) →
      mintedOn thisChain V T (obs.map obligationDeposit) = pendingAmount obs ∧
      releasedOn thisChain V T (obs.map obligationDeposit) = 0 ∧
      ∀ u, creditedTo V T u (obs.map obligationDeposit) = pendingAmountFor u obs
  | [], _ => ⟨rfl, rfl, fun _ => rfl⟩
  | o :: obs, h => by
    have ho : o.assetId = a := h o List.mem_cons_self
    obtain ⟨ih1, ih2, ih3⟩ := trackedDeposit_sums hT hn obs (fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))
    have hoT : V.token o.assetId = T := by rw [ho, hT]
    have hon : V.originChain o.assetId ≠ thisChain := by rw [ho]; exact hn
    refine ⟨?_, ?_, ?_⟩
    · rw [List.map_cons, mintedOn_cons, ih1]
      simp only [obligationDeposit, hoT, hon, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
      simp [pendingAmount]
    · rw [List.map_cons, releasedOn_cons, ih2]
      simp [obligationDeposit, hon]
    · intro u
      rw [List.map_cons, creditedTo_cons, ih3]
      by_cases hu : o.data.originalCaller = u
      · simp [obligationDeposit, hoT, hu, pendingAmountFor]
      · simp [obligationDeposit, hu, pendingAmountFor]

theorem preparedBundleFullyRecovered {Acc : Type} (hooks : NativeTokenVaultBase.Hooks Acc)
    (s t : Ledger Acc) (hw : NativeTokenVaultBase.WellFormed s.vault) (hs0 : s.pending = [])
    (hr : Reach hooks s t) (enc : AssetIdOf) (cfg : Config) (base : AssetId) (tr : TrackerHook A)
    (dep : DeployHook A) (other : OtherTargets (Ledgers A)) (dest : Chain)
    (w : World (Ledgers A)) (calls : List Call) (obs : List Obligation) (hne : obs ≠ [])
    (hsub : obs.Subperm t.pending) (hb : DepositBundle cfg calls (obs.map obligationDeposit))
    (hp : w.paused = false) (hcorr : NativeTokenVaultBase.Corr t.vault cfg.thisChain w.vault)
    (hled : w.rest.token (NativeTokenVaultBase.widen t.vault.config.tokenAddress) = t.vault.token)
    (htr : (trackerRun tr dest w.rest.tracker (obs.map obligationDeposit)).isSome) :
    ∃ w', claimRefund (recoverCall enc cfg (localHooks t.vault.config.vault base tr dep) other dest)
        LegState.Revertable w calls = some (LegState.Reverted, w')
      ∧ recoverBundle (recoverCall enc cfg (localHooks t.vault.config.vault base tr dep) other
          dest) w calls = some (w', calls.length)
      ∧ w'.router = w.router ∧ w'.vault = w.vault ∧ w'.paused = w.paused
      ∧ (∀ tok, tok ≠ NativeTokenVaultBase.widen t.vault.config.tokenAddress →
          w'.rest.token tok = w.rest.token tok)
      ∧ (w'.rest.token (NativeTokenVaultBase.widen t.vault.config.tokenAddress)).config =
          t.vault.token.config
      ∧ (∀ u, (w'.rest.token (NativeTokenVaultBase.widen t.vault.config.tokenAddress)).balances u
          = t.vault.token.balances u + pendingAmountFor u obs)
      ∧ (w'.rest.token (NativeTokenVaultBase.widen t.vault.config.tokenAddress)).totalSupply
          = t.vault.token.totalSupply + pendingAmount obs
      ∧ BridgedStandardERC20.WellFormed
          (w'.rest.token (NativeTokenVaultBase.widen t.vault.config.tokenAddress))
      ∧ ∀ rest : List Obligation, (obs ++ rest).Perm t.pending →
          (w'.rest.token (NativeTokenVaultBase.widen t.vault.config.tokenAddress)).totalSupply
            + pendingAmount rest = s.vault.token.totalSupply := by
  obtain ⟨hwt, hcons, -⟩ := reachable_conservation hw hr
  have hps : PendingSound t := pendingSound_reach hw (by intro o ho; rw [hs0] at ho; cases ho) hr
  obtain ⟨o₀, ho₀⟩ := List.exists_mem_of_ne_nil obs hne
  obtain ⟨-, -, hvault, htokaddr, horigin⟩ := hps o₀ (hsub.subset ho₀)
  -- the tracked asset, its token and its branch in the world's registry
  have hTok : w.vault.token t.vault.config.assetId =
      NativeTokenVaultBase.widen t.vault.config.tokenAddress := by
    rw [hcorr.registry.token, hwt.2.2.2.1]
  have hReg : w.vault.token t.vault.config.assetId ≠ 0 := by
    rw [hTok]; exact fun h => htokaddr (NativeTokenVaultBase.widen_eq_zero.mp h)
  have hOrig : w.vault.originChain t.vault.config.assetId ≠ cfg.thisChain := by
    rw [(hcorr.tracked hReg).1, hcorr.chain]; exact horigin
  have hassets : ∀ o ∈ obs, o.assetId = t.vault.config.assetId :=
    fun o ho => (hps o (hsub.subset ho)).1
  obtain ⟨hmint, hrel, hcred⟩ := trackedDeposit_sums hTok hOrig obs hassets
  have hnil : pendingAmount ([] : List Obligation) = 0 := rfl
  rw [hs0, hnil, Nat.add_zero] at hcons
  have hsupply : t.vault.token.totalSupply + pendingAmount obs < UInt256.size := by
    have h1 := fullRecovery_pending_subperm hsub
    have h2 := hw.1.2.1
    omega
  -- every deposit is on the tracked asset
  have hds : ∀ d ∈ obs.map obligationDeposit, d.1 = t.vault.config.assetId ∧
      d.2.originalCaller ≠ 0 := by
    intro d hd
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hd
    exact ⟨(hps o (hsub.subset ho)).1, (hps o (hsub.subset ho)).2.1⟩
  have hcov : CreditsCovered t.vault.config.vault base cfg.thisChain w.vault w.rest.token
      (obs.map obligationDeposit) := by
    refine ⟨hvault, fun d hd => (hds d hd).2, ?_, ?_⟩
    · intro d hd hn
      rw [(hds d hd).1] at hn
      exact absurd hn hOrig
    · intro d hd _
      rw [(hds d hd).1, hTok, hled, hmint]
      exact ⟨hwt.2.1, hsupply⟩
  have hreg' : ∀ d ∈ obs.map obligationDeposit, w.vault.token d.1 ≠ 0 := by
    intro d hd; rw [(hds d hd).1]; exact hReg
  obtain ⟨w', hclaim, hfull, hrouter, hv, hpz, ⟨hframe, hex⟩, hwf⟩ :=
    registeredDepositBundleFullyRecovered enc cfg t.vault.config.vault base tr dep other dest w
      calls (obs.map obligationDeposit) hp hb (by simpa using hne) hreg' htr hcov
  obtain ⟨hcfgT, hsupT, hbalT⟩ := hex (NativeTokenVaultBase.widen t.vault.config.tokenAddress)
  refine ⟨w', hclaim, hfull, hrouter, hv, hpz, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tok htok
    refine hframe tok (fun d hd => ?_)
    rw [(hds d hd).1, hTok]
    exact Ne.symm htok
  · rw [hcfgT, hled]
  · intro u
    have := hbalT u
    rw [hrel, hcred u, hled] at this
    simpa using this
  · rw [hsupT, hmint, hled]
  · exact hwf _ (by rw [hled]; exact hwt.1)
  · intro rest hperm
    have hpa : pendingAmount (obs ++ rest) = pendingAmount t.pending := by
      unfold pendingAmount
      exact (hperm.map _).sum_eq
    rw [hsupT, hmint, hled]
    have happ := fullRecovery_pending_append obs rest
    omega

theorem depositBundle_shaped {cfg : Config} {calls : List Call} {ds : List Deposit}
    (hb : DepositBundle cfg calls ds) : ∀ c ∈ calls, RouterDepositShaped cfg c := by
  induction hb with
  | nil => intro c hc; cases hc
  | @cons c' d' cs ds' hcd _ ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨ht, src, hd⟩ := hcd
      exact ⟨ht, src, _, _, hd⟩
    · exact ih c hc

/-! ## Concrete instances

This chain `7`; router `3`, vault `4`, manager `5`; the base asset is `99`.  Asset `1` is native
here with token `20`; asset `2` is bridged (origin chain `9`) with token `21`.  The vault holds `5`
of token `20` in escrow; token `21` is minted by the vault and has no supply yet. -/

def frCfg : Config := ⟨7, 3, 4, 5, fun _ => some 1⟩

def frVault : NativeTokenVault.Vault :=
  ⟨fun a => if a = 1 then 7 else if a = 2 then 9 else 0,
    fun a => if a = 1 then 20 else if a = 2 then 21 else 0,
    fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

def frLedger : Address → BridgedStandardERC20.State := fun tok =>
  if tok = 20 then BridgedStandardERC20.mintEffect (BridgedStandardERC20.empty ⟨4, 0, 1⟩) 4 5
  else if tok = 21 then BridgedStandardERC20.empty ⟨4, 8, 2⟩
  else BridgedStandardERC20.empty ⟨4, 0, 0⟩

/-- A tracker that adds up the amounts it is told about. -/
def frTracker : TrackerHook ℕ := fun n _ _ amt => some (n + amt.val)

def frDep : DeployHook ℕ := fun _ _ _ _ => none

/-- Every other target declines and changes nothing. -/
def frOther : OtherTargets (Ledgers ℕ) := fun _ w _ _ => some (w, false)

/-- Native deposit: original caller `11`, remote receiver `13`, amount `2`. -/
def frMdNative : MintData := ⟨11, 13, 0, 2, []⟩

/-- Bridged deposit: original caller `12`, remote receiver `14`, origin token `8`, amount `3`. -/
def frMdBridged : MintData := ⟨12, 14, 8, 3, []⟩

def frDeposits : List Deposit := [(1, frMdNative), (2, frMdBridged)]

def frCalls : List Call := [routerCall frCfg 1 frMdNative, routerCall frCfg 2 frMdBridged]

def frWorld : World (Ledgers ℕ) := ⟨AssetRouter.empty, frVault, false, ⟨frLedger, 0⟩⟩

theorem frBundle : DepositBundle frCfg frCalls frDeposits :=
  List.Forall₂.cons ⟨rfl, 7, rfl⟩ (List.Forall₂.cons ⟨rfl, 7, rfl⟩ List.Forall₂.nil)

theorem frRegistered : ∀ d ∈ frDeposits, frVault.token d.1 ≠ 0 := by decide

theorem frCovered : CreditsCovered 4 99 7 frVault frLedger frDeposits :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem frEmpty_wf (c : BridgedStandardERC20.Config) :
    BridgedStandardERC20.WellFormed (BridgedStandardERC20.empty c) :=
  ⟨Finset.sum_const_zero, by norm_num [BridgedStandardERC20.empty, UInt256.size], rfl⟩

theorem frMintEffect_wf (c : BridgedStandardERC20.Config) (holder : Addr160) (amt : UInt256)
    (hv : c.vault ≠ 0) (hh : holder ≠ 0) :
    BridgedStandardERC20.WellFormed
      (BridgedStandardERC20.mintEffect (BridgedStandardERC20.empty c) holder amt) := by
  have hmint : BridgedStandardERC20.mint (BridgedStandardERC20.empty c) c.vault holder amt =
      some (BridgedStandardERC20.mintEffect (BridgedStandardERC20.empty c) holder amt) := by
    unfold BridgedStandardERC20.mint
    rw [ite_eq_left]
    refine ⟨hv, rfl, hh, ?_⟩
    show 0 + amt.val < UInt256.size
    have := amt.isLt
    omega
  exact BridgedStandardERC20.mint_preserves_ledger (frEmpty_wf c) hmint

theorem frLedger_wf (tok : Address) : BridgedStandardERC20.WellFormed (frLedger tok) := by
  unfold frLedger
  split_ifs
  · exact frMintEffect_wf _ _ _ (by decide) (by decide)
  · exact frEmpty_wf _
  · exact frEmpty_wf _

theorem frTracker_returns : ∀ d ∈ frDeposits, ∀ t, (frTracker t 8 d.1 d.2.amount).isSome := by
  intro d _ t; rfl

theorem frTrackerRun : trackerRun frTracker 8 0 frDeposits = some 5 := rfl

theorem FullRecoverySatisfiable : Properties.FullRecoverySatisfiable := by
  obtain ⟨w', hclaim, -⟩ := registeredDepositBundleFullyRecovered (A := ℕ) (fun _ _ _ => 0) frCfg
    4 99 frTracker frDep frOther 8 frWorld frCalls frDeposits rfl frBundle (by decide)
    frRegistered (by rw [show frWorld.rest.tracker = 0 from rfl, frTrackerRun]; rfl) frCovered
  obtain ⟨L', hrun, -⟩ := creditRun_exact 4 99 7 frVault frDeposits frLedger frCovered
  refine ⟨ℕ, fun _ _ _ => 0, frCfg, 4, 99, frTracker, frDep, frOther, 8, frWorld, w', frCalls,
    frDeposits, rfl, frBundle, by decide, frRegistered,
    by rw [show frWorld.rest.tracker = 0 from rfl, frTrackerRun]; rfl, frTracker_returns,
    frCovered, frLedger_wf, ?_, rfl, ⟨(1, frMdNative), List.mem_cons_self, by decide⟩,
    ⟨(2, frMdBridged), List.mem_cons_of_mem _ List.mem_cons_self, by decide⟩, by decide,
    by rw [show frWorld.rest.tracker = 0 from rfl, frTrackerRun]; decide,
    depositBundle_shaped frBundle,
    by show (creditRun 4 99 7 frVault frLedger frDeposits).isSome = true; rw [hrun]; rfl,
    hclaim, by decide⟩
  intro c hc
  simp only [frCalls, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> rfl

/-! ### Countermodels -/

/-- The bridged deposit's credit on its own. -/
theorem frBridgedCredit : ∃ L₁, creditStep 4 99 7 frVault frLedger (2, frMdBridged) = some L₁ := by
  obtain ⟨L₁, hrun, -⟩ := creditRun_exact 4 99 7 frVault [(2, frMdBridged)] frLedger
    ⟨by decide, by decide, by decide, by decide⟩
  exact ⟨L₁, by simpa [creditRun] using hrun⟩

/-- A call to target `77`, which is not the router. -/
def frDeclining : Call := ⟨77, 13, 0, .other⟩

theorem DecliningCallMakesTerminalPartial : Properties.DecliningCallMakesTerminalPartial := by
  obtain ⟨L₁, hL₁⟩ := frBridgedCredit
  have h1 : recoverCall (fun _ _ _ => 0) frCfg (localHooks 4 99 frTracker frDep) frOther 8 frWorld
      (routerCall frCfg 2 frMdBridged) = some ({ frWorld with rest := ⟨L₁, 0 + 3⟩ }, true) := by
    rw [depositRefund_step (fun _ _ _ => 0) frCfg 4 99 frTracker frDep frOther 8 frWorld _
      (2, frMdBridged) rfl ⟨rfl, 7, rfl⟩ (by decide)]
    show (some (0 + (3 : UInt256).val)).bind _ = _
    rw [Option.bind_some]
    show (creditStep 4 99 7 frVault frLedger (2, frMdBridged)).map _ = _
    rw [hL₁]
    rfl
  have h2 : ∀ u : World (Ledgers ℕ), recoverCall (fun _ _ _ => 0) frCfg
      (localHooks 4 99 frTracker frDep) frOther 8 u frDeclining = some (u, false) := by
    intro u
    unfold recoverCall
    rw [ite_eq_right (by decide)]
    rfl
  refine ⟨ℕ, fun _ _ _ => 0, frCfg, 4, 99, frTracker, frDep, frOther, 8, frWorld,
    { frWorld with rest := ⟨L₁, 0 + 3⟩ }, [routerCall frCfg 2 frMdBridged, frDeclining], ?_, rfl,
    ?_, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> rfl
  · simp only [claimRefund, recoverBundle, h1, h2]
    rfl
  · simp only [recoverBundle, h1, h2]
    rfl
  · simp only [outcomes, h1, h2]
    rfl

/-- Unit tracker; the token's `bridgeMint` returns without crediting anyone. -/
def frNonStandardHooks : Hooks (Ledgers Unit) :=
  { localHooks (A := Unit) 4 99 (fun t _ _ _ => some t) (fun _ _ _ _ => none) with
    mint := fun x _ _ _ => some x }

def frUnitWorld : World (Ledgers Unit) := ⟨AssetRouter.empty, frVault, false, ⟨frLedger, ()⟩⟩

theorem NonStandardTokenCountedButNotCredited :
    Properties.NonStandardTokenCountedButNotCredited := by
  have hstep : recoverCall (fun _ _ _ => 0) frCfg frNonStandardHooks (fun _ w _ _ => some (w, false))
      8 frUnitWorld (routerCall frCfg 2 frMdBridged) = some (frUnitWorld, true) := by
    unfold recoverCall
    rw [ite_eq_left (show (routerCall frCfg 2 frMdBridged).target = frCfg.router from rfl)]
    show recoverAtomicCall (fun _ _ _ => 0) frCfg frNonStandardHooks frUnitWorld frCfg.manager 8
      (.finalizeDeposit frCfg.thisChain 2 (some frMdBridged)) = _
    rw [AssetRouter.AtomicRecovery.recoverAtomicCall_known (x₁ := frUnitWorld.rest) rfl
      (by decide) (by decide) rfl]
    rfl
  refine ⟨fun _ _ _ => 0, frCfg, frNonStandardHooks, fun _ w _ _ => some (w, false), 8, frUnitWorld,
    frUnitWorld, [routerCall frCfg 2 frMdBridged], (2, frMdBridged), rfl,
    List.Forall₂.cons ⟨rfl, 7, rfl⟩ List.Forall₂.nil, by decide, by decide, by decide, by decide,
    ?_, ?_, rfl⟩
  · simp only [claimRefund, recoverBundle, hstep]
    rfl
  · simp only [recoverBundle, hstep]
    rfl

/-- `2^256 - 2`. -/
def frBigWord : UInt256 := ⟨UInt256.size - 2, by decide⟩

/-- Token `21` with supply `2^256 - 2`, all held by account `15`. -/
def frBigLedger : Address → BridgedStandardERC20.State := fun tok =>
  if tok = 21 then
    BridgedStandardERC20.mintEffect (BridgedStandardERC20.empty ⟨4, 8, 2⟩) 15 frBigWord
  else BridgedStandardERC20.empty ⟨4, 0, 0⟩

def frBigWorld : World (Ledgers ℕ) := ⟨AssetRouter.empty, frVault, false, ⟨frBigLedger, 0⟩⟩

/-- One unit of the bridged asset back to `12`. -/
def frMdOne : MintData := ⟨12, 14, 8, 1, []⟩

def frBigDeposits : List Deposit := [(2, frMdOne), (2, frMdOne)]

def frBigCalls : List Call := [routerCall frCfg 2 frMdOne, routerCall frCfg 2 frMdOne]

theorem frBigCredits_fail :
    (creditRun 4 99 7 frVault frBigLedger frBigDeposits).isNone = true := by
  decide

theorem JointHeadroomNeeded : Properties.JointHeadroomNeeded := by
  have hb : DepositBundle frCfg frBigCalls frBigDeposits :=
    List.Forall₂.cons ⟨rfl, 7, rfl⟩ (List.Forall₂.cons ⟨rfl, 7, rfl⟩ List.Forall₂.nil)
  refine ⟨ℕ, fun _ _ _ => 0, frCfg, 4, 99, frTracker, frDep, frOther, 8, frBigWorld, frBigCalls,
    frBigDeposits, rfl, hb, rfl, by decide, rfl, ?_, ?_⟩
  · intro d hd
    simp only [frBigDeposits, List.mem_cons, List.not_mem_nil, or_false, or_self] at hd
    subst hd
    refine ⟨by decide, by decide, by decide, by decide, ?_, by decide⟩
    exact frMintEffect_wf _ _ _ (by decide) (by decide)
  · rw [depositRefund_claim (fun _ _ _ => 0) frCfg 4 99 frTracker frDep frOther 8 frBigWorld
      frBigCalls frBigDeposits rfl hb (by decide), ite_eq_right (by decide)]
    have hnone : creditRun 4 99 7 frVault frBigLedger frBigDeposits = none :=
      Option.isNone_iff_eq_none.mp frBigCredits_fail
    show (trackerRun frTracker 8 0 frBigDeposits).bind
      (fun t => (creditRun 4 99 7 frVault frBigLedger frBigDeposits).map _) = none
    rw [hnone]
    rfl

/-! ### A preparation trace with two depositors

On the representation model's witness configuration (`NativeTokenVaultBase.toyConfig 5 (2 + 1) 1 2`:
vault and router `1`, token `5`, asset `2 + 1`, this chain `1`, origin chain `2`), the token holds
one unit for each of `11` and `13`.  Both burn it towards chain `4`. -/

def frPrepToken : BridgedStandardERC20.State :=
  BridgedStandardERC20.mintEffect
    (BridgedStandardERC20.mintEffect (BridgedStandardERC20.empty ⟨1, 7, 2 + 1⟩) 11 1) 13 1

def frPrepState : NativeTokenVaultBase.State Unit :=
  ⟨NativeTokenVaultBase.toyConfig 5 (2 + 1) 1 2,
    NativeTokenVaultBase.installRegistry (NativeTokenVaultBase.nativeRegistry 9) (2 + 1) 5, false,
    frPrepToken, ()⟩

/-- Burn one unit of `dep`'s balance towards chain `4` for `rcv`, the token resolved from the
registry (zero hint). -/
def frRequest (dep rcv : NativeTokenVaultBase.Address) : NativeTokenVaultBase.Request :=
  ⟨1, 4, 2 + 1, dep, 0, 0, ⟨1, rcv, 0⟩⟩

theorem frPrepToken_wf : BridgedStandardERC20.WellFormed frPrepToken := by
  have h1 := frMintEffect_wf ⟨1, 7, 2 + 1⟩ 11 1 (by decide) (by decide)
  have hmint : BridgedStandardERC20.mint
      (BridgedStandardERC20.mintEffect (BridgedStandardERC20.empty ⟨1, 7, 2 + 1⟩) 11 1) 1 13 1
      = some frPrepToken := by
    unfold BridgedStandardERC20.mint
    rw [ite_eq_left]
    · rfl
    · exact ⟨by decide, rfl, by decide, by decide⟩
  exact BridgedStandardERC20.mint_preserves_ledger h1 hmint

theorem frPrepState_wf : NativeTokenVaultBase.WellFormed frPrepState :=
  ⟨frPrepToken_wf, rfl, rfl, NativeTokenVaultBase.witnessPrep_token,
    NativeTokenVaultBase.witnessPrep_asset⟩

/-- A preparation of one unit is enabled on any well-formed state of this shape whose depositor
holds a unit. -/
theorem frPrep_enabled (s : NativeTokenVaultBase.State Unit) (hw : NativeTokenVaultBase.WellFormed s)
    (hcfg : s.config = NativeTokenVaultBase.toyConfig 5 (2 + 1) 1 2)
    (hreg : s.registry =
      NativeTokenVaultBase.installRegistry (NativeTokenVaultBase.nativeRegistry 9) (2 + 1) 5)
    (hpz : s.paused = false) (horig : s.token.config.originToken = 7)
    {dep rcv : NativeTokenVaultBase.Address} (hd : dep ≠ 0) (hb : 1 ≤ s.token.balances dep) :
    ∃ out, NativeTokenVaultBase.prepare NativeTokenVaultBase.witnessPrepHooks s (frRequest dep rcv)
      = some out := by
  have htok : s.registry.tokenForAsset (2 + 1) = 5 := by
    rw [hreg]; exact NativeTokenVaultBase.witnessPrep_token
  have hasset : s.registry.assetForToken 5 = 2 + 1 := by
    rw [hreg]; exact NativeTokenVaultBase.witnessPrep_asset
  have hsel : NativeTokenVaultBase.selectedToken s (frRequest dep rcv) = 5 := by
    show (if (0 : NativeTokenVaultBase.Address) = 0 then s.registry.tokenForAsset (2 + 1) else 0) = 5
    rw [ite_eq_left rfl, htok]
  have hs : NativeTokenVaultBase.InScope s (frRequest dep rcv) := by
    unfold NativeTokenVaultBase.InScope
    rw [hcfg, hsel]
    exact ⟨by decide, by decide, by decide, by decide, rfl⟩
  have he : NativeTokenVaultBase.EntryAllowed s (frRequest dep rcv) := by
    unfold NativeTokenVaultBase.EntryAllowed
    rw [hcfg, hsel, hpz, hasset]
    exact ⟨rfl, rfl, rfl, by decide, rfl, show (1 : UInt256) ≠ 0 by decide⟩
  exact NativeTokenVaultBase.preparation_enabled (hooks := NativeTokenVaultBase.witnessPrepHooks)
    (accounted := ()) (metadata := []) hw hs he rfl hd hb (by rw [horig]; decide)
    (by rw [hcfg]; decide) rfl rfl

/-- What a successful preparation keeps. -/
theorem frPrep_keeps {s : NativeTokenVaultBase.State Unit} {r : NativeTokenVaultBase.Request}
    {out : NativeTokenVaultBase.Result Unit} (hw : NativeTokenVaultBase.WellFormed s)
    (h : NativeTokenVaultBase.prepare NativeTokenVaultBase.witnessPrepHooks s r = some out) :
    NativeTokenVaultBase.WellFormed out.state ∧ out.state.config = s.config ∧
      out.state.registry = s.registry ∧ out.state.paused = s.paused ∧
      out.state.token.config = s.token.config ∧
      (∀ a, a ≠ r.depositor → out.state.token.balances a = s.token.balances a) := by
  obtain ⟨hw', hc, hr, hp, hbal⟩ := NativeTokenVaultBase.preparation_preserves_ledger hw h
  have hburn := (NativeTokenVaultBase.preparation_backed hw h).1
  exact ⟨hw', hc, hr, hp, (BridgedStandardERC20.burn_exact hw.1 hburn).2.2.2.2.2, hbal⟩

theorem frPrep_corr : NativeTokenVaultBase.Corr frPrepState 1 NativeTokenVaultBase.witnessVault := by
  refine ⟨rfl, NativeTokenVaultBase.registryCorr_install (NativeTokenVaultBase.nativeRegistry_corr 9)
    _ _ _ _, ?_⟩
  intro _
  exact ⟨NativeTokenVault.sn_originChain_self _ _ _ _ _,
    NativeTokenVault.sn_originToken_self _ _ _ _ _⟩

theorem PreparedBundleFullyRecoveredSatisfiable :
    Properties.PreparedBundleFullyRecoveredSatisfiable := by
  -- the first preparation: `11` burns its unit
  obtain ⟨out₁, h₁⟩ := frPrep_enabled frPrepState frPrepState_wf rfl rfl rfl rfl
    (dep := 11) (rcv := 12) (by decide) (by decide)
  obtain ⟨hw₁, hc₁, hr₁, hp₁, ht₁, hb₁⟩ := frPrep_keeps frPrepState_wf h₁
  -- the second preparation: `13` burns its unit
  obtain ⟨out₂, h₂⟩ := frPrep_enabled out₁.state hw₁ hc₁ hr₁ hp₁
    (by rw [ht₁]; rfl) (dep := 13) (rcv := 14) (by decide)
    (by rw [hb₁ 13 (by decide)]; decide)
  obtain ⟨hw₂, hc₂, -, -, -, -⟩ := frPrep_keeps hw₁ h₂
  have hpay₁ := NativeTokenVaultBase.preparation_payload frPrepState_wf h₁
  have hpay₂ := NativeTokenVaultBase.preparation_payload hw₁ h₂
  -- the trace and its correspondence with the registry vault
  let s : Ledger Unit := ⟨frPrepState, []⟩
  let t : Ledger Unit := ⟨out₂.state,
    ([] ++ [obligation (frRequest 11 12) out₁.data]) ++ [obligation (frRequest 13 14) out₂.data]⟩
  have hreach : Reach NativeTokenVaultBase.witnessPrepHooks s t :=
    Reach.tail (Reach.tail Reach.refl (Step.prepare h₁)) (Step.prepare h₂)
  let W : NativeTokenVault.World := ⟨NativeTokenVaultBase.witnessVault, NativeTokenVault.empty.audit⟩
  have hcorr₁ := (NativeTokenVaultBase.preparationIsForeignBridgeOut NativeTokenVaultBase.toyId
    (W := W) frPrep_corr frPrepState_wf.2 h₁).2.2.2
  have hcorr₂ := (NativeTokenVaultBase.preparationIsForeignBridgeOut NativeTokenVaultBase.toyId
    (W := W) hcorr₁ hw₁.2 h₂).2.2.2
  -- the manager's world: this chain `1`, router `3`; the tracked token's ledger is the trace's
  let cfg : Config := ⟨1, 3, 4, 5, fun _ => some 2⟩
  let w : World (Ledgers ℕ) := ⟨AssetRouter.empty, NativeTokenVaultBase.witnessVault, false,
    ⟨Function.update (fun _ => BridgedStandardERC20.empty ⟨0, 0, 0⟩)
      (NativeTokenVaultBase.widen 5) out₂.state.token, 0⟩⟩
  have hcfg₂ : out₂.state.config.tokenAddress = 5 := by rw [hc₂, hc₁]; rfl
  have hled : w.rest.token (NativeTokenVaultBase.widen t.vault.config.tokenAddress) = t.vault.token := by
    show Function.update (fun _ : Address => BridgedStandardERC20.empty ⟨0, 0, 0⟩)
      (NativeTokenVaultBase.widen 5) out₂.state.token
      (NativeTokenVaultBase.widen out₂.state.config.tokenAddress) = out₂.state.token
    rw [hcfg₂, Function.update_self]
  have hb : DepositBundle cfg [routerCall cfg (2 + 1) out₁.data, routerCall cfg (2 + 1) out₂.data]
      (t.pending.map obligationDeposit) :=
    List.Forall₂.cons ⟨rfl, 1, rfl⟩ (List.Forall₂.cons ⟨rfl, 1, rfl⟩ List.Forall₂.nil)
  have hamt₁ : out₁.data.amount = 1 := hpay₁.2.2.2.1
  have hamt₂ : out₂.data.amount = 1 := hpay₂.2.2.2.1
  have htr : trackerRun frTracker 4 0 (t.pending.map obligationDeposit) = some 2 := by
    show (some (0 + out₁.data.amount.val)).bind _ = _
    rw [Option.bind_some]
    show (some (0 + out₁.data.amount.val + out₂.data.amount.val)).bind _ = _
    rw [Option.bind_some, hamt₁, hamt₂]
    rfl
  refine ⟨Unit, NativeTokenVaultBase.witnessPrepHooks, s, t, ℕ, cfg, frTracker, 4, w,
    [routerCall cfg (2 + 1) out₁.data, routerCall cfg (2 + 1) out₂.data], t.pending,
    frPrepState_wf, rfl, hreach, by simp [t], List.Subperm.refl _, hb, rfl, hcorr₂, hled,
    by rw [show w.rest.tracker = 0 from rfl, htr]; rfl, rfl, ?_,
    by rw [show w.rest.tracker = 0 from rfl, htr]; decide⟩
  refine ⟨obligation (frRequest 11 12) out₁.data, by simp [t],
    obligation (frRequest 13 14) out₂.data, by simp [t], ?_⟩
  show out₁.data.originalCaller ≠ out₂.data.originalCaller
  rw [hpay₁.1, hpay₂.1]
  decide

/-! ## Certificates -/

theorem TerminalIsFullIffNoDecline : Properties.TerminalIsFullIffNoDecline :=
  fun _ step w w' calls h => terminal_full_iff_no_decline step w w' calls h

theorem FullAcceptanceIffAllRecovered : Properties.FullAcceptanceIffAllRecovered := by
  intro os
  unfold ClaimAccepted AttackVectors.RecoveryLimits.LoopCompletes recoveredCount
  rw [List.length_filter_eq_length_iff]
  constructor
  · rintro ⟨⟨-, hne⟩, hall⟩
    refine ⟨?_, fun o ho => by simpa using hall o ho⟩
    rintro rfl
    simp at hne
  · rintro ⟨hne, hall⟩
    have hall' : ∀ o ∈ os, decide (o = Outcome.recovered) = true :=
      fun o ho => by simpa using hall o ho
    refine ⟨⟨fun hm => by simpa using hall _ hm, ?_⟩, hall'⟩
    rw [List.length_filter_eq_length_iff.mpr hall']
    exact fun h0 => hne (List.length_eq_zero_iff.mp h0)

theorem DepositBundleNeverDeclines : Properties.DepositBundleNeverDeclines :=
  fun _ _ _ _ _ _ w calls hs => routerDeposits_never_decline calls w hs

theorem DepositBundleClaimIsFull : Properties.DepositBundleClaimIsFull := by
  intro X enc cfg hk other dest w w' calls hs h
  exact (terminal_full_iff_no_decline _ w w' calls h).mpr (routerDeposits_never_decline calls w hs)

theorem DepositRefundIsCredits : Properties.DepositRefundIsCredits :=
  fun _ enc cfg vault base tr dep other dest w calls ds hp hb hreg =>
    depositRefund_loop enc cfg vault base tr dep other dest w calls ds hp hb hreg

theorem DepositClaimIffCredits : Properties.DepositClaimIffCredits := by
  intro A enc cfg vault base tr dep other dest w w' calls ds hp hb hreg
  rw [depositRefund_claim enc cfg vault base tr dep other dest w calls ds hp hb hreg]
  by_cases hds : ds = []
  · rw [ite_eq_left hds]
    simp [hds]
  · rw [ite_eq_right hds]
    constructor
    · intro h
      obtain ⟨t, ht, h'⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨L, hL, h''⟩ := Option.map_eq_some_iff.mp h'
      exact ⟨hds, t, L, ht, hL, ((Prod.mk.inj h'').2).symm⟩
    · rintro ⟨-, t, L, ht, hL, rfl⟩
      rw [ht, hL]
      rfl

theorem CreditsCoveredSucceedExactly : Properties.CreditsCoveredSucceedExactly :=
  fun vault base thisChain V L ds hc => creditRun_exact vault base thisChain V ds L hc

theorem CreditsPreserveLedgers : Properties.CreditsPreserveLedgers :=
  fun _ _ _ _ _ _ _ h => creditRun_wellFormed h

theorem TrackerAlwaysReturnsRuns : Properties.TrackerAlwaysReturnsRuns :=
  fun _ _ _ t ds h => trackerRun_isSome ds t h

theorem RegisteredDepositBundleFullyRecovered : Properties.RegisteredDepositBundleFullyRecovered :=
  fun _ enc cfg vault base tr dep other dest w calls ds hp hb hne hreg htr hcov =>
    registeredDepositBundleFullyRecovered enc cfg vault base tr dep other dest w calls ds hp hb hne
      hreg htr hcov

theorem PausedVaultBlocksDepositClaim : Properties.PausedVaultBlocksDepositClaim := by
  intro X enc cfg hk other dest w calls hp hne hs
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨ht, src, a, m, hd⟩ := hs c List.mem_cons_self
  apply AssetRouter.AtomicRecovery.claimRefund_eq_none
  unfold recoverBundle
  rw [routerDeposit_step ht hd]
  have hnone : ntvRecover enc cfg hk w cfg.router 0 dest a m = none := by
    unfold ntvRecover
    rw [AssetRouter.AtomicRecovery.vaultRefund_guard (Or.inr (Or.inr hp))]
    rfl
  rw [hnone]
  rfl

theorem PauseOnlyDelaysFullRecovery : Properties.PauseOnlyDelaysFullRecovery := by
  intro A enc cfg vault base tr dep other dest w calls ds hp hb hne hreg htr hcov
  refine ⟨?_, ?_⟩
  · refine PausedVaultBlocksDepositClaim _ enc cfg _ other dest { w with paused := true } calls rfl
      ?_ ?_
    · rintro rfl
      cases hb
      exact hne rfl
    · exact depositBundle_shaped hb
  · obtain ⟨w', h1, h2, -⟩ :=
      registeredDepositBundleFullyRecovered enc cfg vault base tr dep other dest w calls ds hp hb
        hne hreg htr hcov
    exact ⟨w', h1, h2⟩

theorem PendingObligationsSound : Properties.PendingObligationsSound := by
  intro Acc hooks s t hw hs0 hr
  exact pendingSound_reach hw (by intro o ho; rw [hs0] at ho; cases ho) hr

theorem PreparedBundleFullyRecovered : Properties.PreparedBundleFullyRecovered :=
  fun _ hooks s t hw hs0 hr _ enc cfg base tr dep other dest w calls obs hne hsub hb hp hcorr hled
    htr =>
    preparedBundleFullyRecovered hooks s t hw hs0 hr enc cfg base tr dep other dest w calls obs hne
      hsub hb hp hcorr hled htr

end AssetBridgePreparation.FullRecovery
