import EraSpec.Protocol.NativeValueLegs.Properties.LegConservation

/-!
# Proofs: a native-value atomic leg returns exactly what it collected

The ledger moves (`moveNative`, `moveToken`, `burnToken`, `mintToken`) change the touched accounts
by `±v` (`moveNative_native`, `moveToken_bal_self`, `burnToken_bal_self`, `mintToken_bal_self`).  On
an asset already registered, the tracker calls reduce to their `chainBalance` update
(`trackerInitiate_registered`, `trackerFinalize_registered`).  From these, one base-token refund
shifts the leg's footprint by `+v` (`routerRecoverBase_shifted`) and the collection by `-v`
(`collect_shifted`).  `Shifted` composes additively (`Shifted.trans`), a framed router-call
recovery is a zero shift (`Shifted.of_frames`), and the loop's shift is the sum of the refunds it
requests (`recoverBundle_shifted`).  The send-side lemma `shape` supplies the loop's hypotheses and
identifies that sum with `totalBurnedCallsValue` (`valueRefunds_sum`).  Without the registration
premise, a refund of a token that does not originate here registers it and mints
(`registerIfNeeded_not_native`, `routerRecoverBase_shifted_unregistered`), which gives the same
shift (`recoverBundle_shifted_gen`, `claim_shifted_gen`).
-/

namespace Contracts.NativeValueLegs

/-! ## Ledger moves -/

theorem update_move (f : Address → ℕ) (src dst : Address) (v : ℕ) (hv : v ≤ f src) (x : Address) :
    ((Function.update (Function.update f src (f src - v)) dst
        (Function.update f src (f src - v) dst + v) x : ℕ) : ℤ) =
      f x + v * ((if x = dst then 1 else 0) - (if x = src then 1 else 0)) := by
  simp only [Function.update_apply]
  split_ifs <;> subst_vars <;> first | omega | (exfalso; simp_all)

theorem moveNative_native (w : World) (src dst : Address) (v : ℕ) (hv : v ≤ w.native src)
    (x : Address) :
    ((moveNative w src dst v).native x : ℤ) =
      w.native x + v * ((if x = dst then 1 else 0) - (if x = src then 1 else 0)) :=
  update_move w.native src dst v hv x

theorem moveToken_bal_self (w : World) (a : AssetId) (src dst : Address) (v : ℕ)
    (hv : v ≤ w.bal a src) (x : Address) :
    ((moveToken w a src dst v).bal a x : ℤ) =
      w.bal a x + v * ((if x = dst then 1 else 0) - (if x = src then 1 else 0)) := by
  unfold moveToken
  simp only [Function.update_self]
  exact update_move (w.bal a) src dst v hv x

theorem burnToken_bal_self (w : World) (a : AssetId) (src : Address) (v : ℕ)
    (hv : v ≤ w.bal a src) (x : Address) :
    ((burnToken w a src v).bal a x : ℤ) = w.bal a x - v * (if x = src then 1 else 0) := by
  unfold burnToken
  simp only [Function.update_self, Function.update_apply]
  split_ifs <;> subst_vars <;> omega

theorem mintToken_bal_self (w : World) (a : AssetId) (dst : Address) (v : ℕ) (x : Address) :
    ((mintToken w a dst v).bal a x : ℤ) = w.bal a x + v * (if x = dst then 1 else 0) := by
  unfold mintToken
  simp only [Function.update_self, Function.update_apply]
  split_ifs <;> subst_vars <;> omega

theorem sink_base {cfg : Config} {A : AssetId} (h : A = cfg.baseAsset) :
    sink cfg A = some cfg.holder := by
  simp [sink, h]

theorem sink_native {cfg : Config} {A : AssetId} (h : A ≠ cfg.baseAsset)
    (hn : cfg.originOf A = cfg.thisChain) : sink cfg A = some cfg.ntv := by
  simp [sink, h, hn]

theorem sink_bridged {cfg : Config} {A : AssetId} (h : A ≠ cfg.baseAsset)
    (hn : cfg.originOf A ≠ cfg.thisChain) : sink cfg A = none := by
  simp [sink, h, hn]

theorem dir_of_sink_some {cfg : Config} {A : AssetId} {s : Address} (h : sink cfg A = some s)
    (u x : Address) :
    dir cfg A u x = (if x = u then 1 else 0) - (if x = s then 1 else 0) := by
  simp only [dir, h, Option.some.injEq]
  by_cases hx : x = s
  · simp [hx]
  · simp [hx, Ne.symm hx]

theorem dir_of_sink_none {cfg : Config} {A : AssetId} (h : sink cfg A = none) (u x : Address) :
    dir cfg A u x = if x = u then 1 else 0 := by
  simp [dir, h]

theorem ledger_base {cfg : Config} {A : AssetId} (h : A = cfg.baseAsset) (w : World) :
    ledger cfg A w = w.native := by
  simp [ledger, h]

theorem ledger_token {cfg : Config} {A : AssetId} (h : A ≠ cfg.baseAsset) (w : World) :
    ledger cfg A w = w.bal A := by
  simp [ledger, h]

theorem Shifted.refl (cfg : Config) (A : AssetId) (u : Address) (w : World) :
    Shifted cfg A u 0 w w :=
  ⟨fun _ => by ring, by ring, by ring, rfl, rfl⟩

theorem Shifted.trans {cfg : Config} {A : AssetId} {u : Address} {c₁ c₂ : ℤ} {w w₁ w₂ : World}
    (h₁ : Shifted cfg A u c₁ w w₁) (h₂ : Shifted cfg A u c₂ w₁ w₂) :
    Shifted cfg A u (c₁ + c₂) w w₂ :=
  ⟨fun x => by rw [h₂.ledger x, h₁.ledger x]; ring, by rw [h₂.supply, h₁.supply]; ring,
    by rw [h₂.chainBalance, h₁.chainBalance]; ring, h₂.toL1.trans h₁.toL1,
    h₂.fromL1.trans h₁.fromL1⟩

theorem Shifted.congr {cfg : Config} {A : AssetId} {u : Address} {c c' : ℤ} {w w' : World}
    (h : Shifted cfg A u c w w') (hc : c = c') : Shifted cfg A u c' w w' := hc ▸ h

theorem Shifted.of_frames {cfg : Config} {A : AssetId} {u : Address} {w w' : World}
    (h : Frames cfg A w w') : Shifted cfg A u 0 w w' := by
  obtain ⟨hl, hs, hc, ht, hf, -⟩ := h
  exact ⟨fun x => by rw [hl]; ring, by rw [hs]; ring, by rw [hc]; ring, ht, hf⟩

theorem registerIfNeeded_of_registered {cfg : Config} {w : World} {a : AssetId}
    (h : w.registered a = true) : registerIfNeeded cfg w a = some w := by
  simp [registerIfNeeded, h]

theorem trackerFinalize_registered {cfg : Config} {w : World} {fromChain : Chain} {a : AssetId}
    {amount : ℕ} (hreg : w.registered a = true) (hd : fromChain ≠ cfg.l1Chain) :
    trackerFinalize cfg w fromChain a amount =
      some (if cfg.originOf a = cfg.thisChain then
        { w with chainBalance := Function.update w.chainBalance a (w.chainBalance a + amount) }
       else w) := by
  unfold trackerFinalize
  rw [registerIfNeeded_of_registered hreg]
  split_ifs <;> simp_all


/-! ## One base-token refund -/

theorem moveToken_bal_record (w : World) (cb : AssetId → ℕ) (a : AssetId) (s d : Address) (v : ℕ) :
    (moveToken { w with chainBalance := cb } a s d v).bal = (moveToken w a s d v).bal := rfl

theorem routerRecoverBase_shifted {cfg : Config} {w w' : World} {d : Chain} {A : AssetId}
    {u : Address} {v : ℕ} (hreg : A = cfg.baseAsset ∨ w.registered A = true)
    (h : routerRecoverBase cfg w d A u v = some w') :
    Shifted cfg A u v w w' ∧ w'.registered A = w.registered A := by
  unfold routerRecoverBase vaultRefund at h
  by_cases hd : d = cfg.l1Chain
  · simp [hd] at h
  by_cases hp : w.ntvPaused = true
  · simp [hd, hp] at h
  by_cases hn : RecoveryNeutral cfg A d
  swap
  · simp [hd, hp, hn] at h
  rw [ite_eq_right hd, ite_eq_right hp, ite_eq_right (not_not.mpr hn)] at h
  by_cases hA : A = cfg.baseAsset
  · -- the base token, through the holder
    rw [ite_eq_left hA] at h
    have hnh : ¬ NativeHere cfg A := hn.2 hA
    have hbs : ¬ BurnsSupply cfg A := fun hb => hb.1 hA
    unfold holderRecover at h
    by_cases hv : v = 0
    · rw [ite_eq_left hv] at h
      cases h
      subst hv
      exact ⟨by simpa using Shifted.refl cfg A u w, rfl⟩
    rw [ite_eq_right hv, ite_eq_right (by rw [← hA]; exact not_not.mpr hn)] at h
    unfold sendValue at h
    by_cases hbal : w.native cfg.holder < v
    · simp [hbal] at h
    by_cases hrej : cfg.rejectsValue u = true
    · simp [hbal, hrej] at h
    rw [ite_eq_right hbal, ite_eq_right hrej] at h
    cases h
    refine ⟨⟨fun x => ?_, ?_, ?_, rfl, rfl⟩, rfl⟩
    · rw [ledger_base hA, ledger_base hA, moveNative_native w cfg.holder u v (not_lt.mp hbal) x,
        dir_of_sink_some (sink_base hA)]
    · simp [hbs, moveNative]
    · simp [hnh, moveNative]
  · -- a token, through the vault
    rw [ite_eq_right hA] at h
    have hreg' : w.registered A = true := hreg.resolve_left hA
    rw [trackerFinalize_registered hreg' hn.1, Option.bind_some] at h
    by_cases hnat : cfg.originOf A = cfg.thisChain
    · -- native here: the escrow pays, `chainBalance` is credited
      simp only [hnat, ↓reduceIte] at h
      by_cases htok : cfg.tokenOf A = 0
      · simp [htok] at h
      by_cases hlt : w.bal A cfg.ntv < v
      · simp [htok, hlt] at h
      simp only [htok, hlt, ↓reduceIte, Option.some.injEq] at h
      subst h
      have hnh : NativeHere cfg A := hnat
      have hbs : ¬ BurnsSupply cfg A := fun hb => hb.2 hnat
      refine ⟨⟨fun x => ?_, ?_, ?_, rfl, rfl⟩, rfl⟩
      · rw [ledger_token hA, ledger_token hA, moveToken_bal_record,
          moveToken_bal_self w A cfg.ntv u v (not_lt.mp hlt) x,
          dir_of_sink_some (sink_native hA hnat)]
      · simp [hbs, moveToken]
      · simp [hnh, moveToken]
    · -- bridged: minted
      simp only [hnat, ↓reduceIte] at h
      by_cases htok : cfg.tokenOf A = 0
      · simp [htok] at h
      simp only [htok, ↓reduceIte, Option.some.injEq] at h
      subst h
      have hnh : ¬ NativeHere cfg A := hnat
      have hbs : BurnsSupply cfg A := ⟨hA, hnat⟩
      refine ⟨⟨fun x => ?_, ?_, ?_, rfl, rfl⟩, rfl⟩
      · rw [ledger_token hA, ledger_token hA, mintToken_bal_self w A u v x,
          dir_of_sink_none (sink_bridged hA hnat)]
      · simp [hbs, mintToken]
      · simp [hnh, mintToken]


/-! ## Registration in the tracker -/

theorem registerIfNeeded_registers {cfg : Config} {w w' : World} {a : AssetId}
    (h : registerIfNeeded cfg w a = some w') : w'.registered a = true := by
  unfold registerIfNeeded at h
  split_ifs at h <;> simp_all <;> (try (cases h; simp))

theorem trackerInitiate_registers {cfg : Config} {w w' : World} {d : Chain} {a : AssetId}
    {amount : ℕ} (h : trackerInitiate cfg w d a amount = some w') : w'.registered a = true := by
  unfold trackerInitiate at h
  by_cases htok : cfg.tokenOf a = 0
  · simp [htok] at h
  rw [ite_eq_right htok] at h
  cases hr : registerIfNeeded cfg w a with
  | none => rw [hr] at h; simp at h
  | some w₁ =>
    have h₁ := registerIfNeeded_registers hr
    rw [hr, Option.bind_some] at h
    split_ifs at h <;> simp at h <;> subst h <;> simpa using h₁

theorem trackerInitiate_registered {cfg : Config} {w : World} {toChain : Chain} {a : AssetId}
    {amount : ℕ} (htok : cfg.tokenOf a ≠ 0) (hreg : w.registered a = true)
    (hd : toChain ≠ cfg.l1Chain) :
    trackerInitiate cfg w toChain a amount =
      if cfg.originOf a = cfg.thisChain then
        (if w.chainBalance a < amount then none
         else some { w with chainBalance := Function.update w.chainBalance a (w.chainBalance a - amount) })
      else some w := by
  unfold trackerInitiate
  rw [registerIfNeeded_of_registered hreg]
  split_ifs <;> simp_all

/-! ## The collection -/

theorem collect_shifted {P : Params} {w w' : World} {u : Address} {d : Chain} {A : AssetId}
    {v : ℕ} (hd : d ≠ P.cfg.l1Chain) (hroute : A = P.cfg.baseAsset ∨ w.handler A = P.cfg.ntv)
    (hreg : w.registered A = true) (hsup : SupplyCovers w A)
    (h : collect P w u d A v = some w') :
    Shifted P.cfg A u (-(v : ℤ)) w w' := by
  unfold collect at h
  by_cases hv : v = 0
  · subst hv
    have : w' = w := by
      by_cases hA : A = P.cfg.baseAsset <;> simp [hA] at h <;> exact h.symm
    rw [this]
    simpa using Shifted.refl P.cfg A u w
  by_cases hA : A = P.cfg.baseAsset
  · -- the base token, into the holder
    rw [ite_eq_left hA, ite_eq_right hv] at h
    unfold holderBurn at h
    by_cases hbal : w.native u < v
    · simp [hbal] at h
    rw [ite_eq_right hbal, ← hA] at h
    by_cases htok : P.cfg.tokenOf A = 0
    · simp [trackerInitiate, htok] at h
    rw [trackerInitiate_registered (w := moveNative w u P.cfg.holder v) htok hreg hd] at h
    have hbs : ¬ BurnsSupply P.cfg A := fun hb => hb.1 hA
    have hledger : ∀ x, (ledger P.cfg A (moveNative w u P.cfg.holder v) x : ℤ) =
        ledger P.cfg A w x + -(v : ℤ) * dir P.cfg A u x := by
      intro x
      rw [ledger_base hA, ledger_base hA, moveNative_native w u P.cfg.holder v (not_lt.mp hbal) x,
        dir_of_sink_some (sink_base hA)]
      ring
    by_cases hnat : P.cfg.originOf A = P.cfg.thisChain
    · simp only [hnat, ↓reduceIte] at h
      by_cases hlt : (moveNative w u P.cfg.holder v).chainBalance A < v
      · simp [hlt] at h
      simp only [hlt, ↓reduceIte, Option.some.injEq] at h
      subst h
      have hnh : NativeHere P.cfg A := hnat
      have hle : v ≤ w.chainBalance A := not_lt.mp hlt
      refine ⟨fun x => hledger x, ?_, ?_, rfl, rfl⟩
      · simp [hbs, moveNative]
      · simp only [hnh, ↓reduceIte, moveNative, Function.update_self]
        omega
    · simp only [hnat, ↓reduceIte, Option.some.injEq] at h
      subst h
      have hnh : ¬ NativeHere P.cfg A := hnat
      exact ⟨hledger, by simp [hbs, moveNative], by simp [hnh, moveNative], rfl, rfl⟩
  · -- a token, through the vault
    rw [ite_eq_right hA, ite_eq_right hv] at h
    have hntv : w.handler A = P.cfg.ntv := hroute.resolve_left hA
    unfold routerDepositBase at h
    have hh0 : w.handler A ≠ 0 := by
      intro h0
      simp [h0] at h
    rw [ite_eq_right hh0, ite_eq_left hntv] at h
    unfold vaultBurn at h
    by_cases hp : w.ntvPaused = true
    · simp [hp] at h
    by_cases htok : P.cfg.tokenOf A = 0
    · simp [hp, htok] at h
    by_cases has : P.cfg.assetOf (P.cfg.tokenOf A) ≠ A
    · simp [hp, htok, has] at h
    by_cases hweth : P.cfg.originOf A = P.cfg.thisChain ∧ P.cfg.tokenOf A = P.cfg.weth
    · simp [hp, hv, hweth] at h
    rw [ite_eq_right hp, ite_eq_right htok, ite_eq_right has, ite_eq_right hv,
      ite_eq_right hweth, ite_eq_right hA, trackerInitiate_registered htok hreg hd] at h
    by_cases hnat : P.cfg.originOf A = P.cfg.thisChain
    · -- native here: into the escrow
      simp only [hnat, ↓reduceIte] at h
      by_cases hlt : w.chainBalance A < v
      · simp [hlt] at h
      simp only [hlt, ↓reduceIte, Option.bind_some, ne_eq, not_true_eq_false] at h
      by_cases hun : u = P.cfg.ntv
      · simp [hun] at h
      by_cases hb : w.bal A u < v
      · simp [hun, hb] at h
      simp only [hun, hb, ↓reduceIte, Option.some.injEq] at h
      subst h
      have hnh : NativeHere P.cfg A := hnat
      have hbs : ¬ BurnsSupply P.cfg A := fun hb' => hb'.2 hnat
      refine ⟨fun x => ?_, ?_, ?_, rfl, rfl⟩
      · rw [ledger_token hA, ledger_token hA, moveToken_bal_record,
          moveToken_bal_self w A u P.cfg.ntv v (not_lt.mp hb) x,
          dir_of_sink_some (sink_native hA hnat)]
        ring
      · simp [hbs, moveToken]
      · simp only [hnh, ↓reduceIte, moveToken, Function.update_self]
        omega
    · -- bridged: burned
      simp only [hnat, ↓reduceIte, Option.bind_some, ne_eq, not_false_eq_true] at h
      by_cases hb : w.bal A u < v
      · simp [hb] at h
      simp only [hb, ↓reduceIte, Option.some.injEq] at h
      subst h
      have hnh : ¬ NativeHere P.cfg A := hnat
      have hbs : BurnsSupply P.cfg A := ⟨hA, hnat⟩
      have hsv : v ≤ w.supply A := le_trans (not_lt.mp hb) (hsup u)
      refine ⟨fun x => ?_, ?_, ?_, rfl, rfl⟩
      · rw [ledger_token hA, ledger_token hA, burnToken_bal_self w A u v (not_lt.mp hb) x,
          dir_of_sink_none (sink_bridged hA hnat)]
        ring
      · simp only [hbs, ↓reduceIte, burnToken, Function.update_self]
        omega
      · simp [hnh, burnToken]

theorem vaultBurn_registers {cfg : Config} {w w' : World} {d : Chain} {a : AssetId} {u : Address}
    {v : ℕ} (h : vaultBurn cfg w d a u v = some w') : w'.registered a = true := by
  unfold vaultBurn at h
  split_ifs at h
  all_goals
    obtain ⟨w₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    have hr₁ := trackerInitiate_registers h₁
    first
    | simp only [reduceCtorEq] at h₂
    | split_ifs at h₂
      simp only [Option.some.injEq] at h₂
      subst h₂
      exact hr₁

theorem collect_registers {P : Params} {w w' : World} {u : Address} {d : Chain} {A : AssetId}
    {v : ℕ} (hv : 0 < v) (hroute : A = P.cfg.baseAsset ∨ w.handler A = P.cfg.ntv)
    (h : collect P w u d A v = some w') : w'.registered A = true := by
  unfold collect at h
  have hv0 : v ≠ 0 := Nat.pos_iff_ne_zero.mp hv
  by_cases hA : A = P.cfg.baseAsset
  · rw [ite_eq_left hA, ite_eq_right hv0] at h
    unfold holderBurn at h
    by_cases hbal : w.native u < v
    · simp [hbal] at h
    rw [ite_eq_right hbal, ← hA] at h
    exact trackerInitiate_registers h
  · rw [ite_eq_right hA, ite_eq_right hv0] at h
    have hntv : w.handler A = P.cfg.ntv := hroute.resolve_left hA
    unfold routerDepositBase at h
    have hh0 : w.handler A ≠ 0 := by
      intro h0
      simp [h0] at h
    rw [ite_eq_right hh0, ite_eq_left hntv] at h
    exact vaultBurn_registers h


/-! ## The refund loop -/

theorem valueRefunds_sum_cons (cfg : Config) (c : Call) (cs : List Call) :
    ((valueRefunds cfg (c :: cs)).map Prod.snd).sum =
      (if c.fromAddr ≠ cfg.router ∧ c.value ≠ 0 then c.value else 0) +
        ((valueRefunds cfg cs).map Prod.snd).sum := by
  unfold valueRefunds
  by_cases h : c.fromAddr ≠ cfg.router ∧ c.value ≠ 0
  · simp [h]
  · rw [ite_eq_right h]
    simp only [List.filter_cons, decide_eq_true_eq]
    rw [ite_eq_right h]
    simp

/-- The loop moves the sum of the requested refunds to `u`, when every call sent from the router
names another asset in its data and every other call is `u`'s. -/
theorem recoverBundle_shifted {P : Params} {d : Chain} {A : AssetId} {u : Address}
    (hframe : RecoveryFramesOthers P A) :
    ∀ (calls : List Call) (w w' : World),
      (∀ c ∈ calls, c.fromAddr = P.cfg.router →
        ∀ src a m, c.data = .finalizeDeposit src a m → a ≠ A) →
      (∀ c ∈ calls, c.fromAddr ≠ P.cfg.router → c.fromAddr = u) →
      ((∃ c ∈ calls, c.fromAddr ≠ P.cfg.router ∧ c.value ≠ 0) →
        A = P.cfg.baseAsset ∨ w.registered A = true) →
      recoverBundle P d A w calls = some w' →
      Shifted P.cfg A u (((valueRefunds P.cfg calls).map Prod.snd).sum : ℕ) w w' ∧
        w'.registered A = w.registered A
  | [], w, w', _, _, _, h => by
    simp only [recoverBundle, Option.some.injEq] at h
    subst h
    exact ⟨by simpa [valueRefunds] using Shifted.refl P.cfg A u w, rfl⟩
  | c :: cs, w, w', hr, hf, hreg, h => by
    simp only [recoverBundle] at h
    obtain ⟨w₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    have step : Shifted P.cfg A u
        ((if c.fromAddr ≠ P.cfg.router ∧ c.value ≠ 0 then c.value else 0 : ℕ) : ℤ) w w₁ ∧
        w₁.registered A = w.registered A := by
      unfold recoverCall at h₁
      by_cases hc : c.fromAddr = P.cfg.router
      · rw [ite_eq_left hc] at h₁
        have hfr := hframe w d c.data w₁ (hr c List.mem_cons_self hc) h₁
        exact ⟨(Shifted.of_frames hfr).congr (by simp [hc]), hfr.2.2.2.2.2⟩
      · rw [ite_eq_right hc] at h₁
        by_cases hv : c.value ≠ 0
        · rw [ite_eq_left hv] at h₁
          have hu : c.fromAddr = u := hf c List.mem_cons_self hc
          rw [hu] at h₁
          obtain ⟨hs, hrg⟩ := routerRecoverBase_shifted (hreg ⟨c, List.mem_cons_self, hc, hv⟩) h₁
          exact ⟨hs.congr (by simp [hc, hv]), hrg⟩
        · rw [ite_eq_right hv] at h₁
          cases h₁
          exact ⟨(Shifted.refl P.cfg A u w).congr (by simp [hv]), rfl⟩
    have hreg₁ : (∃ c' ∈ cs, c'.fromAddr ≠ P.cfg.router ∧ c'.value ≠ 0) →
        A = P.cfg.baseAsset ∨ w₁.registered A = true := by
      rintro ⟨c', hc', h'⟩
      rw [step.2]
      exact hreg ⟨c', List.mem_cons_of_mem _ hc', h'⟩
    obtain ⟨ih, ihr⟩ := recoverBundle_shifted hframe cs w₁ w'
      (fun c' hc' => hr c' (List.mem_cons_of_mem _ hc'))
      (fun c' hc' => hf c' (List.mem_cons_of_mem _ hc')) hreg₁ h₂
    refine ⟨(step.1.trans ih).congr ?_, ihr.trans step.2⟩
    rw [valueRefunds_sum_cons]
    push_cast
    ring

/-! ## The send side -/

/-- What a formed bundle's calls satisfy, call by call, under the deployed checks. -/
theorem shape {cfg : Config} {A : AssetId} {u : Address} (hu : u ≠ cfg.router) :
    ∀ {starters : List Starter} {calls : List Call},
      (∀ s ∈ starters, StarterPasses deployed cfg s) →
      List.Forall₂ (FormsCall cfg A u) starters calls →
      (∀ c ∈ calls, c.fromAddr = cfg.router →
          c.value = 0 ∧ ∃ a m, c.data = .finalizeDeposit cfg.thisChain a m ∧ a ≠ A) ∧
        (∀ c ∈ calls, c.fromAddr ≠ cfg.router → c.fromAddr = u) ∧
        (calls.map Call.value).sum = collected starters
  | [], [], _, .nil => by simp [collected]
  | s :: ss, c :: cs, hp, .cons hsc hrest => by
    obtain ⟨ih1, ih2, ih3⟩ := shape hu (fun s' hs' => hp s' (List.mem_cons_of_mem _ hs')) hrest
    have hps := hp s List.mem_cons_self
    have hc : (c.fromAddr = cfg.router →
          c.value = 0 ∧ ∃ a m, c.data = .finalizeDeposit cfg.thisChain a m ∧ a ≠ A) ∧
        (c.fromAddr ≠ cfg.router → c.fromAddr = u) := by
      cases hind : s.indirectCall
      · obtain ⟨-, -, hfrom⟩ := hsc.direct hind
        exact ⟨fun h => absurd (hfrom ▸ h) hu, fun _ => hfrom⟩
      · obtain ⟨hto, hval⟩ := hps hind
        have hto' := hto rfl
        have hval' := hval rfl
        have hfrom : c.fromAddr = cfg.router := (hsc.indirect hind).trans hto'
        exact ⟨fun _ => ⟨hsc.value.trans hval', hsc.routerData hind hto'⟩, fun h => absurd hfrom h⟩
    refine ⟨?_, ?_, ?_⟩
    · intro c' hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hc.1
      · exact ih1 c' hc'
    · intro c' hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hc.2
      · exact ih2 c' hc'
    · simp only [List.map_cons, List.sum_cons, collected] at ih3 ⊢
      rw [ih3, hsc.value]

theorem valueRefunds_sum {cfg : Config} : ∀ {calls : List Call},
    (∀ c ∈ calls, c.fromAddr = cfg.router → c.value = 0) →
    ((valueRefunds cfg calls).map Prod.snd).sum = (calls.map Call.value).sum
  | [], _ => rfl
  | c :: cs, h => by
    rw [valueRefunds_sum_cons, valueRefunds_sum (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
    simp only [List.map_cons, List.sum_cons]
    by_cases hc : c.fromAddr = cfg.router
    · rw [h c List.mem_cons_self hc]
      simp
    · by_cases hv : c.value = 0 <;> simp [hc, hv]

theorem valueRefunds_from {cfg : Config} {u : Address} {calls : List Call}
    (h : ∀ c ∈ calls, c.fromAddr ≠ cfg.router → c.fromAddr = u) :
    ∀ p ∈ valueRefunds cfg calls, p.1 = u := by
  intro p hp
  simp only [valueRefunds, List.mem_map, List.mem_filter, decide_eq_true_eq] at hp
  obtain ⟨c, ⟨hc, hdec⟩, rfl⟩ := hp
  exact h c hc hdec.1

/-- The router-call hypothesis of `recoverBundle_shifted`, from the shape. -/
theorem routerCalls_name_others {cfg : Config} {A : AssetId} {calls : List Call}
    (h : ∀ c ∈ calls, c.fromAddr = cfg.router →
      c.value = 0 ∧ ∃ a m, c.data = .finalizeDeposit cfg.thisChain a m ∧ a ≠ A) :
    ∀ c ∈ calls, c.fromAddr = cfg.router →
      ∀ src a m, c.data = .finalizeDeposit src a m → a ≠ A := by
  intro c hc hcr src a m hdata
  obtain ⟨-, a', m', hd', hne⟩ := h c hc hcr
  rw [hdata] at hd'
  cases hd'
  exact hne

/-- The refund of a formed bundle: the shift, and the registration kept. -/
theorem claim_shifted {P : Params} {u : Address} {starters : List Starter} {B : Bundle}
    {w w' : World} (hu : u ≠ P.cfg.router) (hp : ∀ s ∈ starters, StarterPasses deployed P.cfg s)
    (hf : List.Forall₂ (FormsCall P.cfg B.destBaseAsset u) starters B.calls)
    (hframe : RecoveryFramesOthers P B.destBaseAsset)
    (hreg : 0 < collected starters →
      B.destBaseAsset = P.cfg.baseAsset ∨ w.registered B.destBaseAsset = true)
    (h : claimRefund P w B = some w') :
    Shifted P.cfg B.destBaseAsset u (collected starters) w w' ∧
      w'.registered B.destBaseAsset = w.registered B.destBaseAsset := by
  obtain ⟨h1, h2, h3⟩ := shape hu hp hf
  unfold claimRefund at h
  by_cases hd : B.destChain = P.cfg.l1Chain
  · simp [hd] at h
  rw [ite_eq_right hd] at h
  have hreg' : (∃ c ∈ B.calls, c.fromAddr ≠ P.cfg.router ∧ c.value ≠ 0) →
      B.destBaseAsset = P.cfg.baseAsset ∨ w.registered B.destBaseAsset = true := by
    rintro ⟨c, hc, -, hv⟩
    apply hreg
    rw [← h3]
    exact lt_of_lt_of_le (Nat.pos_of_ne_zero hv) (List.le_sum_of_mem (List.mem_map_of_mem hc))
  obtain ⟨hs, hr⟩ :=
    recoverBundle_shifted hframe B.calls w w' (routerCalls_name_others h1) h2 hreg' h
  refine ⟨hs.congr ?_, hr⟩
  rw [valueRefunds_sum (fun c hc hr' => (h1 c hc hr').1), h3]

/-! ## The registration premise, for a token that does not originate here -/

/-- For an asset that does not originate here, `registerIfNeeded` writes only the registration. -/
theorem registerIfNeeded_not_native {cfg : Config} {w w' : World} {a : AssetId}
    (hnat : cfg.originOf a ≠ cfg.thisChain) (h : registerIfNeeded cfg w a = some w') :
    w'.native = w.native ∧ w'.bal = w.bal ∧ w'.supply = w.supply ∧
      w'.chainBalance = w.chainBalance ∧ w'.toL1 = w.toL1 ∧ w'.fromL1 = w.fromL1 ∧
      w'.registered a = true := by
  have hreg := registerIfNeeded_registers h
  unfold registerIfNeeded at h
  -- `split_ifs` discharges the native branch with `hnat`
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hreg⟩

/-- The refund of a token that does not originate here, registered in the tracker or not: the
tracker registers it if needed and the vault mints. -/
theorem routerRecoverBase_shifted_unregistered {cfg : Config} {w w' : World} {d : Chain}
    {A : AssetId} {u : Address} {v : ℕ} (hA : A ≠ cfg.baseAsset) (hnat : ¬ NativeHere cfg A)
    (h : routerRecoverBase cfg w d A u v = some w') :
    Shifted cfg A u v w w' ∧ w'.registered A = true := by
  have hnat' : cfg.originOf A ≠ cfg.thisChain := hnat
  unfold routerRecoverBase vaultRefund at h
  by_cases hd : d = cfg.l1Chain
  · simp [hd] at h
  by_cases hp : w.ntvPaused = true
  · simp [hd, hp] at h
  by_cases hn : RecoveryNeutral cfg A d
  swap
  · simp [hd, hp, hn] at h
  rw [ite_eq_right hd, ite_eq_right hp, ite_eq_right (not_not.mpr hn), ite_eq_right hA] at h
  obtain ⟨w₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
  unfold trackerFinalize at h₁
  obtain ⟨w₀, h₀, h₀₁⟩ := Option.map_eq_some_iff.mp h₁
  obtain ⟨-, hb0, hs0, hc0, ht0, hf0, hr0⟩ := registerIfNeeded_not_native hnat' h₀
  have hl : ¬ (d = cfg.l1Chain ∧ cfg.slIsL1 = true) := fun h' => hd h'.1
  simp only [hnat', hl, ↓reduceIte] at h₀₁
  subst h₀₁
  simp only [hnat', ↓reduceIte] at h₂
  by_cases htok : cfg.tokenOf A = 0
  · simp [htok] at h₂
  simp only [htok, ↓reduceIte, Option.some.injEq] at h₂
  subst h₂
  have hbs : BurnsSupply cfg A := ⟨hA, hnat'⟩
  refine ⟨⟨fun x => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [ledger_token hA, ledger_token hA, mintToken_bal_self, hb0,
      dir_of_sink_none (sink_bridged hA hnat')]
  · simp [hbs, mintToken, hs0]
  · simp [hnat, mintToken, hc0]
  · simp [mintToken, ht0]
  · simp [mintToken, hf0]
  · simp [mintToken, hr0]

/-- One base-token refund under the weaker registration premise: the shift, and a registration kept. -/
theorem routerRecoverBase_shifted_gen {cfg : Config} {w w' : World} {d : Chain} {A : AssetId}
    {u : Address} {v : ℕ}
    (hreg : A = cfg.baseAsset ∨ w.registered A = true ∨ ¬ NativeHere cfg A)
    (h : routerRecoverBase cfg w d A u v = some w') :
    Shifted cfg A u v w w' ∧ (w.registered A = true → w'.registered A = true) := by
  by_cases hr : A = cfg.baseAsset ∨ w.registered A = true
  · obtain ⟨hs, hrg⟩ := routerRecoverBase_shifted hr h
    exact ⟨hs, fun h' => hrg.trans h'⟩
  · have hA : A ≠ cfg.baseAsset := fun h' => hr (Or.inl h')
    have hnat : ¬ NativeHere cfg A := by
      rcases hreg with h' | h' | h'
      · exact absurd h' hA
      · exact absurd (Or.inr h') hr
      · exact h'
    obtain ⟨hs, hrg⟩ := routerRecoverBase_shifted_unregistered hA hnat h
    exact ⟨hs, fun _ => hrg⟩

/-- `recoverBundle_shifted` under the weaker registration premise. -/
theorem recoverBundle_shifted_gen {P : Params} {d : Chain} {A : AssetId} {u : Address}
    (hframe : RecoveryFramesOthers P A) :
    ∀ (calls : List Call) (w w' : World),
      (∀ c ∈ calls, c.fromAddr = P.cfg.router →
        ∀ src a m, c.data = .finalizeDeposit src a m → a ≠ A) →
      (∀ c ∈ calls, c.fromAddr ≠ P.cfg.router → c.fromAddr = u) →
      ((∃ c ∈ calls, c.fromAddr ≠ P.cfg.router ∧ c.value ≠ 0) →
        A = P.cfg.baseAsset ∨ w.registered A = true ∨ ¬ NativeHere P.cfg A) →
      recoverBundle P d A w calls = some w' →
      Shifted P.cfg A u (((valueRefunds P.cfg calls).map Prod.snd).sum : ℕ) w w' ∧
        (w.registered A = true → w'.registered A = true)
  | [], w, w', _, _, _, h => by
    simp only [recoverBundle, Option.some.injEq] at h
    subst h
    exact ⟨by simpa [valueRefunds] using Shifted.refl P.cfg A u w, id⟩
  | c :: cs, w, w', hr, hf, hreg, h => by
    simp only [recoverBundle] at h
    obtain ⟨w₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    have step : Shifted P.cfg A u
        ((if c.fromAddr ≠ P.cfg.router ∧ c.value ≠ 0 then c.value else 0 : ℕ) : ℤ) w w₁ ∧
        (w.registered A = true → w₁.registered A = true) := by
      unfold recoverCall at h₁
      by_cases hc : c.fromAddr = P.cfg.router
      · rw [ite_eq_left hc] at h₁
        have hfr := hframe w d c.data w₁ (hr c List.mem_cons_self hc) h₁
        exact ⟨(Shifted.of_frames hfr).congr (by simp [hc]), fun h' => hfr.2.2.2.2.2.trans h'⟩
      · rw [ite_eq_right hc] at h₁
        by_cases hv : c.value ≠ 0
        · rw [ite_eq_left hv] at h₁
          have hu : c.fromAddr = u := hf c List.mem_cons_self hc
          rw [hu] at h₁
          obtain ⟨hs, hrg⟩ :=
            routerRecoverBase_shifted_gen (hreg ⟨c, List.mem_cons_self, hc, hv⟩) h₁
          exact ⟨hs.congr (by simp [hc, hv]), hrg⟩
        · rw [ite_eq_right hv] at h₁
          cases h₁
          exact ⟨(Shifted.refl P.cfg A u w).congr (by simp [hv]), id⟩
    have hreg₁ : (∃ c' ∈ cs, c'.fromAddr ≠ P.cfg.router ∧ c'.value ≠ 0) →
        A = P.cfg.baseAsset ∨ w₁.registered A = true ∨ ¬ NativeHere P.cfg A := by
      rintro ⟨c', hc', h'⟩
      rcases hreg ⟨c', List.mem_cons_of_mem _ hc', h'⟩ with h'' | h'' | h''
      · exact Or.inl h''
      · exact Or.inr (Or.inl (step.2 h''))
      · exact Or.inr (Or.inr h'')
    obtain ⟨ih, ihr⟩ := recoverBundle_shifted_gen hframe cs w₁ w'
      (fun c' hc' => hr c' (List.mem_cons_of_mem _ hc'))
      (fun c' hc' => hf c' (List.mem_cons_of_mem _ hc')) hreg₁ h₂
    refine ⟨(step.1.trans ih).congr ?_, fun h' => ihr (step.2 h')⟩
    rw [valueRefunds_sum_cons]
    push_cast
    ring

/-- `claim_shifted` under the weaker registration premise. -/
theorem claim_shifted_gen {P : Params} {u : Address} {starters : List Starter} {B : Bundle}
    {w w' : World} (hu : u ≠ P.cfg.router) (hp : ∀ s ∈ starters, StarterPasses deployed P.cfg s)
    (hf : List.Forall₂ (FormsCall P.cfg B.destBaseAsset u) starters B.calls)
    (hframe : RecoveryFramesOthers P B.destBaseAsset)
    (hreg : 0 < collected starters →
      B.destBaseAsset = P.cfg.baseAsset ∨ w.registered B.destBaseAsset = true ∨
        ¬ NativeHere P.cfg B.destBaseAsset)
    (h : claimRefund P w B = some w') :
    Shifted P.cfg B.destBaseAsset u (collected starters) w w' := by
  obtain ⟨h1, h2, h3⟩ := shape hu hp hf
  unfold claimRefund at h
  by_cases hd : B.destChain = P.cfg.l1Chain
  · simp [hd] at h
  rw [ite_eq_right hd] at h
  have hreg' : (∃ c ∈ B.calls, c.fromAddr ≠ P.cfg.router ∧ c.value ≠ 0) →
      B.destBaseAsset = P.cfg.baseAsset ∨ w.registered B.destBaseAsset = true ∨
        ¬ NativeHere P.cfg B.destBaseAsset := by
    rintro ⟨c, hc, -, hv⟩
    apply hreg
    rw [← h3]
    exact lt_of_lt_of_le (Nat.pos_of_ne_zero hv) (List.le_sum_of_mem (List.mem_map_of_mem hc))
  obtain ⟨hs, -⟩ :=
    recoverBundle_shifted_gen hframe B.calls w w' (routerCalls_name_others h1) h2 hreg' h
  refine hs.congr ?_
  rw [valueRefunds_sum (fun c hc hr' => (h1 c hc hr').1), h3]

/-! ## Headlines -/

theorem ValueCallsComeFromTheSender : Properties.ValueCallsComeFromTheSender := by
  intro cfg A u starters calls hu hp hf
  obtain ⟨h1, h2, h3⟩ := shape hu hp hf
  refine ⟨h1, h2, valueRefunds_from h2, ?_⟩
  rw [valueRefunds_sum (fun c hc hr => (h1 c hc hr).1), h3]

theorem ClaimReturnsCollected : Properties.ClaimReturnsCollected := by
  intro P u starters B w w' hu hp hf hframe hreg h
  exact (claim_shifted hu hp hf hframe hreg h).1

theorem ClaimReturnsCollectedIfNativeRegistered :
    Properties.ClaimReturnsCollectedIfNativeRegistered := by
  intro P u starters B w w' hu hp hf hframe hreg h
  exact claim_shifted_gen hu hp hf hframe hreg h

theorem CollectionTakesCollected : Properties.CollectionTakesCollected := by
  intro P u d A v w w' hd hroute hreg hsup h
  exact collect_shifted hd hroute hreg hsup h

theorem CollectionRegistersAsset : Properties.CollectionRegistersAsset := by
  intro P u d A v w w' hv hroute h
  exact collect_registers hv hroute h

theorem RefundIsCollectionInverse : Properties.RefundIsCollectionInverse := by
  intro P u starters B w₀ w₁ w₂ w₃ hu hp hf hframe hroute hreg₀ hsup hcol hreg₂ hclaim
  have hd : B.destChain ≠ P.cfg.l1Chain := by
    intro hd
    simp [claimRefund, hd] at hclaim
  have hc := collect_shifted hd hroute hreg₀ hsup hcol
  have hr := (claim_shifted hu hp hf hframe hreg₂ hclaim).1
  refine ⟨fun x => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr.ledger x, hc.ledger x]
    ring
  · rw [hr.supply, hc.supply]
    ring
  · rw [hr.chainBalance, hc.chainBalance]
    ring
  · rw [hr.toL1, hc.toL1]
    ring
  · rw [hr.fromL1, hc.fromL1]
    ring

theorem RefundRestoresFootprint : Properties.RefundRestoresFootprint := by
  intro P u starters B w₀ w₁ w₂ hu hp hf hframe hroute hreg₀ hsup hcol hclaim
  have hd : B.destChain ≠ P.cfg.l1Chain := by
    intro hd
    simp [claimRefund, hd] at hclaim
  have hreg₁ : w₁.registered B.destBaseAsset = true := by
    by_cases hv : collected starters = 0
    · have : w₁ = w₀ := by
        rw [hv] at hcol
        by_cases hA : B.destBaseAsset = P.cfg.baseAsset <;> simp [collect, hA] at hcol <;>
          exact hcol.symm
      rw [this]
      exact hreg₀
    · exact collect_registers (Nat.pos_of_ne_zero hv) hroute hcol
  have hc := collect_shifted hd hroute hreg₀ hsup hcol
  obtain ⟨hr, hrr⟩ := claim_shifted hu hp hf hframe (fun _ => Or.inr hreg₁) hclaim
  refine ⟨funext fun x => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := hr.ledger x
    have h2 := hc.ledger x
    have : (ledger P.cfg B.destBaseAsset w₂ x : ℤ) = ledger P.cfg B.destBaseAsset w₀ x := by
      rw [h1, h2]; ring
    exact_mod_cast this
  · have h1 := hr.supply
    have h2 := hc.supply
    have : (w₂.supply B.destBaseAsset : ℤ) = w₀.supply B.destBaseAsset := by
      rw [h1, h2]; ring
    exact_mod_cast this
  · have h1 := hr.chainBalance
    have h2 := hc.chainBalance
    have : (w₂.chainBalance B.destBaseAsset : ℤ) = w₀.chainBalance B.destBaseAsset := by
      rw [h1, h2]; ring
    exact_mod_cast this
  · rw [hr.toL1, hc.toL1]
  · rw [hr.fromL1, hc.fromL1]
  · rw [hrr, hreg₁, hreg₀]

/-! ## Witnesses -/

theorem mintToken_frames {cfg : Config} {A a : AssetId} (h : a ≠ A) (w : World) (dst : Address)
    (v : ℕ) : Frames cfg A w (mintToken w a dst v) := by
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · by_cases hA : A = cfg.baseAsset
    · simp [ledger, hA, mintToken]
    · simp [ledger, hA, mintToken, Function.update_of_ne (Ne.symm h)]
  · simp [mintToken, Function.update_of_ne (Ne.symm h)]

theorem wRecover_frames (A : AssetId) : RecoveryFramesOthers wParams A := by
  intro w d cd w' hcd h
  cases cd with
  | finalizeDeposit src a m =>
    simp only [wParams, wRecover, Option.some.injEq] at h
    subst h
    exact mintToken_frames (hcd src a m rfl) w 8 1
  | other raw =>
    simp only [wParams, wRecover, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wDirect_passes (K : Checks) (v : ℕ) : StarterPasses K wCfg (wDirect v) := by
  intro h
  simp [wDirect] at h

theorem wIndirect_passes (v : ℕ) : StarterPasses deployed wCfg (wIndirect 0) ∧
    StarterPasses withoutIndirectValueBan wCfg (wIndirect v) := by
  refine ⟨fun _ => ⟨fun _ => rfl, fun _ => rfl⟩, fun _ => ⟨fun _ => rfl, fun h => ?_⟩⟩
  simp [withoutIndirectValueBan] at h

theorem wDirect_forms (A : AssetId) (u : Address) (v : ℕ) :
    FormsCall wCfg A u (wDirect v) (wDirectCall u v) :=
  ⟨rfl, fun _ => ⟨rfl, rfl, rfl⟩, fun h => by simp [wDirect] at h,
    fun h => by simp [wDirect] at h⟩

theorem wIndirect_forms (A a : AssetId) (u : Address) (v : ℕ) (ha : a ≠ A) :
    FormsCall wCfg A u (wIndirect v) (wRouterCall a v) :=
  ⟨rfl, fun h => by simp [wIndirect] at h, fun _ => rfl, fun _ _ => ⟨a, [], rfl, ha⟩⟩

theorem ValueCallsWitness : Properties.ValueCallsWitness := by
  refine ⟨wCfg, 200, 5, [wDirect 6, wIndirect 0], [wDirectCall 5 6, wRouterCall 300 0],
    by decide, ?_, ?_, ⟨wRouterCall 300 0, by simp, rfl⟩, by decide, by decide⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact wDirect_passes _ 6
    · exact (wIndirect_passes 0).1
  · exact .cons (wDirect_forms 200 5 6) (.cons (wIndirect_forms 200 300 5 0 (by decide)) .nil)

/-- The deployed checks pass on the two-starter list. -/
theorem wPair_passes : ∀ s ∈ [wDirect 6, wIndirect 0], StarterPasses deployed wCfg s := by
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact wDirect_passes _ 6
  · exact (wIndirect_passes 0).1

theorem ClaimWitnessNativeToken : Properties.ClaimWitnessNativeToken := by
  refine ⟨wParams, 5, [wDirect 6, wIndirect 0], wBundle 200 [wDirectCall 5 6, wRouterCall 300 0],
    wWorld, by decide, wPair_passes, ?_, wRecover_frames 200, by decide, by decide, by decide,
    ⟨wRouterCall 300 0, by simp [wBundle], rfl⟩, by decide, by decide⟩
  exact .cons (wDirect_forms 200 5 6) (.cons (wIndirect_forms 200 300 5 0 (by decide)) .nil)

theorem ClaimWitnessBaseToken : Properties.ClaimWitnessBaseToken := by
  refine ⟨wParams, 5, [wDirect 6, wIndirect 0], wBundle 100 [wDirectCall 5 6, wRouterCall 300 0],
    wWorld, by decide, wPair_passes, ?_, wRecover_frames 100, rfl,
    ⟨wRouterCall 300 0, by simp [wBundle], rfl⟩, by decide, by decide⟩
  exact .cons (wDirect_forms 100 5 6) (.cons (wIndirect_forms 100 300 5 0 (by decide)) .nil)

theorem wWorld_supplyCovers (A : AssetId) : SupplyCovers wWorld A := by
  intro x
  simp only [wWorld]
  split_ifs <;> simp_all

theorem CollectionWitness : Properties.CollectionWitness :=
  ⟨wParams, 5, 20, 300, 6, wWorld, by decide, by decide, by decide, by decide,
    wWorld_supplyCovers 300, by decide, by decide⟩

theorem CollectionRegistersWitness : Properties.CollectionRegistersWitness :=
  ⟨wParams, 5, 20, 300, 6, wWorldUnregistered, by decide, by decide, by decide, by decide,
    by decide⟩

theorem RoundTripWitness : Properties.RoundTripWitness := by
  have hcol : collect wParams wWorld 5 20 300 6 = some (burnToken wWorld 300 5 6) := rfl
  refine ⟨wParams, 5, [wDirect 6, wIndirect 0], wBundle 300 [wDirectCall 5 6, wRouterCall 200 0],
    wWorld, burnToken wWorld 300 5 6, by decide, wPair_passes, ?_,
    wRecover_frames 300, Or.inr (by decide), by decide, wWorld_supplyCovers 300, by decide,
    ⟨wRouterCall 200 0, by simp [wBundle], rfl⟩, hcol, by decide⟩
  exact .cons (wDirect_forms 300 5 6) (.cons (wIndirect_forms 300 200 5 0 (by decide)) .nil)

theorem WithoutIndirectValueBanValueIsNotRefunded :
    Properties.WithoutIndirectValueBanValueIsNotRefunded := by
  have hcol : (collect wParams wWorld 5 20 100 7).isSome := by decide
  set w₁ := (collect wParams wWorld 5 20 100 7).get hcol with hw₁
  have hcol' : collect wParams wWorld 5 20 100 7 = some w₁ := (Option.some_get hcol).symm
  refine ⟨wParams, 5, [wIndirect 7], wBundle 100 [wRouterCall 300 7], wWorld, w₁,
    mintToken w₁ 300 8 1, by decide, ?_, ?_, wRecover_frames 100, by decide, hcol', ?_, ?_,
    mintToken_frames (by decide) w₁ 8 1⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs
    exact (wIndirect_passes 7).2
  · exact .cons (wIndirect_forms 100 300 5 7 (by decide)) .nil
  · exact collect_shifted (P := wParams) (by decide) (Or.inl rfl) (by decide)
      (wWorld_supplyCovers 100) hcol'
  · rfl

theorem RouterSenderValueIsNotRefunded : Properties.RouterSenderValueIsNotRefunded := by
  have hcol : (collect wParams wWorld 3 20 100 6).isSome := by decide
  set w₁ := (collect wParams wWorld 3 20 100 6).get hcol with hw₁
  have hcol' : collect wParams wWorld 3 20 100 6 = some w₁ := (Option.some_get hcol).symm
  refine ⟨wParams, 3, [wDirect 6], wBundle 100 [wDirectCall 3 6], wWorld, w₁, w₁, rfl, ?_,
    .cons (wDirect_forms 100 3 6) .nil, wRecover_frames 100, by decide, hcol', ?_, rfl,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs
    exact wDirect_passes _ 6
  · exact collect_shifted (P := wParams) (by decide) (Or.inl rfl) (by decide)
      (wWorld_supplyCovers 100) hcol'

theorem ClaimWitnessUnregisteredBridged : Properties.ClaimWitnessUnregisteredBridged := by
  refine ⟨wParams, 5, [wDirect 6, wIndirect 0], wBundle 300 [wDirectCall 5 6, wRouterCall 200 0],
    wWorldUnregistered, by decide, wPair_passes, ?_, wRecover_frames 300, by decide, by decide,
    by decide, ⟨wRouterCall 200 0, by simp [wBundle], rfl⟩, by decide, by decide⟩
  exact .cons (wDirect_forms 300 5 6) (.cons (wIndirect_forms 300 200 5 0 (by decide)) .nil)

/-- The world after the refund of a value call of `6` in asset `200` from
`wWorldNativeUnregistered`. -/
def wNativeRefundAfter : World :=
  (claimRefund wParams wWorldNativeUnregistered (wBundle 200 [wDirectCall 5 6])).get (by decide)

theorem UnregisteredNativeRefundSetsChainBalance :
    Properties.UnregisteredNativeRefundSetsChainBalance := by
  have hclaim : claimRefund wParams wWorldNativeUnregistered (wBundle 200 [wDirectCall 5 6]) =
      some wNativeRefundAfter := (Option.some_get _).symm
  have hcb : wNativeRefundAfter.chainBalance 200 = maxTokenBalance - 30 + 6 := by decide
  refine ⟨wParams, 5, [wDirect 6], wBundle 200 [wDirectCall 5 6], wWorldNativeUnregistered,
    wNativeRefundAfter, by decide, ?_, .cons (wDirect_forms 200 5 6) .nil, wRecover_frames 200,
    by decide, by decide, by decide, by decide, hclaim, by decide, fun hS => ?_⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs
    exact wDirect_passes _ 6
  · have h := hS.chainBalance
    have hn : NativeHere wParams.cfg 200 := by decide
    have h0 : wWorldNativeUnregistered.chainBalance 200 = 0 := rfl
    have hc : collected [wDirect 6] = 6 := rfl
    simp only [wBundle, hcb, h0, hn, hc, ↓reduceIte] at h
    norm_num [maxTokenBalance, UInt256.size] at h

end Contracts.NativeValueLegs
