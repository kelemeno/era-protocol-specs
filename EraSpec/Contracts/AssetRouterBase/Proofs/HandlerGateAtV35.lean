import EraSpec.Contracts.AssetRouterBase.Properties.HandlerGateAtV35
import EraSpec.Contracts.AssetRouterBase.Proofs.AllWriters

/-!
# Proofs: the L1 asset router's handler gate at `draft/v0.35.0`

The gate passes exactly when `(c, a)` is not stranded (`allowed_iff_not_stranded`).  The
run-level results are inductions over `RunV35`, with one case split on the step.  A step writes
`a`'s handler only if it is a call that `Ev.RewritesHandler` lists, or the fallback at `a`,
which needs an unset handler.  It changes the environment only by `enableInterop`, which only
sets a flag, or by `setAddresses`.  The projection onto `AllWriters` maps each router-writing
event to the `AStep` with the same guard.
-/

namespace Contracts.AssetRouter.HandlerGateAtV35

open Contracts.AssetRouter.AllWriters (Cfg Op ARun AStep MintsOnlyNtvIds IsNtvId WeakValid
  pointAt recordTracker pointAt_handler_self pointAt_handler_ne recordTracker_handler)

/-! ## The gate -/

lemma allowed_iff_not_stranded (K : Cfg) (S : St) (c : Chain) (a : AssetId) :
    Allowed K S.env S.router c a ↔ ¬ Stranded K S c a := by
  unfold Allowed Stranded Custom
  cases S.env.ie c
  · simp only [Bool.false_eq_true, or_false, and_true, not_and, not_not]
    tauto
  · simp

lemma enable_ie_self (E : Env) (c : Chain) : (enable E c).ie c = true := by
  simp [enable]

lemma enable_ie_ne (E : Env) {c x : Chain} (h : x ≠ c) : (enable E c).ie x = E.ie x := by
  simp [enable, h]

@[simp] lemma enable_cah (E : Env) (c : Chain) : (enable E c).cah = E.cah := rfl

lemma enable_ie_of_true (E : Env) (c : Chain) {x : Chain} (h : E.ie x = true) :
    (enable E c).ie x = true := by
  by_cases hx : x = c
  · subst hx
    exact enable_ie_self E x
  · rw [enable_ie_ne E hx]
    exact h

/-! ## Runs -/

lemma run_nil_eq {K : Cfg} {S T : St} {evs : List Ev} (h : RunV35 K S evs T) (he : evs = []) :
    T = S := by
  cases h with
  | nil => rfl
  | snoc _ _ => exact absurd he (by simp)

lemma run_snoc_inv {K : Cfg} {S T : St} {evs evs' : List Ev} {e : Ev} (h : RunV35 K S evs T)
    (he : evs = evs' ++ [e]) : ∃ U, RunV35 K S evs' U ∧ StepV35 K e U T := by
  cases h with
  | nil => exact absurd he.symm (by simp)
  | @snoc U _ evs₀ e₀ hr hs =>
    obtain ⟨h1, h2⟩ := List.append_inj' he rfl
    simp only [List.cons.injEq, and_true] at h2
    subst h1
    subst h2
    exact ⟨U, hr, hs⟩

lemma run_single {K : Cfg} {S T : St} {e : Ev} (h : RunV35 K S [e] T) : StepV35 K e S T := by
  obtain ⟨U, hU, hs⟩ := run_snoc_inv (evs' := []) h rfl
  rw [run_nil_eq hU rfl] at hs
  exact hs

theorem run_append {K : Cfg} {S U T : St} {evs₁ evs₂ : List Ev} (h₁ : RunV35 K S evs₁ U)
    (h₂ : RunV35 K U evs₂ T) : RunV35 K S (evs₁ ++ evs₂) T := by
  induction h₂ with
  | nil => simpa using h₁
  | @snoc V W evs e _ hs ih =>
    rw [← List.append_assoc]
    exact ih.snoc hs

theorem run_split {K : Cfg} {S T : St} {evs : List Ev} (hr : RunV35 K S evs T) :
    ∀ evs₁ evs₂ : List Ev, evs = evs₁ ++ evs₂ → ∃ U, RunV35 K S evs₁ U ∧ RunV35 K U evs₂ T := by
  induction hr with
  | nil =>
    intro evs₁ evs₂ h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h.symm
    exact ⟨_, .nil, .nil⟩
  | @snoc V W evs e hr hs ih =>
    intro evs₁ evs₂ h
    rcases List.eq_nil_or_concat' evs₂ with rfl | ⟨L, b, rfl⟩
    · rw [List.append_nil] at h
      subst h
      exact ⟨W, hr.snoc hs, .nil⟩
    · rw [← List.append_assoc] at h
      obtain ⟨h1, h2⟩ := List.append_inj' h rfl
      simp only [List.cons.injEq, and_true] at h2
      subst h2
      obtain ⟨U, hU1, hU2⟩ := ih evs₁ L h1
      exact ⟨U, hU1, hU2.snoc hs⟩

/-! ## (a) What the gate lets through -/

theorem movement_enabled_iff (K : Cfg) (S : St) (c : Chain) (a : AssetId) :
    (∀ g : Gated,
      ((∃ T, StepV35 K (.gated g c a) S T) ↔ S.router.handler a ≠ 0 ∧ ¬ Stranded K S c a) ∧
      ∀ T, StepV35 K (.gated g c a) S T → T = S) ∧
    ((∃ T, StepV35 K (.finalize c a) S T) ↔ S.router.handler a = 0 ∧ K.ntvMints a) := by
  refine ⟨fun g => ⟨⟨?_, ?_⟩, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨T, hs⟩
    cases hs with
    | gated hA h0 => exact ⟨h0, (allowed_iff_not_stranded K S c a).1 hA⟩
  · rintro ⟨h0, hn⟩
    exact ⟨S, .gated ((allowed_iff_not_stranded K S c a).2 hn) h0⟩
  · intro T hs
    cases hs with
    | gated _ _ => rfl
  · rintro ⟨T, hs⟩
    cases hs with
    | finalize _ h0 hm => exact ⟨h0, hm⟩
  · rintro ⟨h0, hm⟩
    exact ⟨_, .finalize (Or.inl h0) h0 hm⟩

/-- One step of an asset-moving event: what it moved the asset through. -/
lemma step_through {K : Cfg} {U V : St} {e : Ev} {c : Chain} {a : AssetId}
    (hs : StepV35 K e U V) (he : e.gatedAt = some (c, a)) :
    ∃ h, e.through K U = some h ∧ (h = K.ntv ∨ h = U.env.cah ∨ U.env.ie c = true) := by
  cases hs with
  | finalize _ _ _ => exact ⟨K.ntv, rfl, Or.inl rfl⟩
  | @gated _ g c' a' hA h0 =>
    simp only [Ev.gatedAt, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨U.router.handler a', rfl, ?_⟩
    rcases hA with h | h | h | h
    · exact absurd h h0
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  | register _ => simp [Ev.gatedAt] at he
  | seed => simp [Ev.gatedAt] at he
  | setTracker => simp [Ev.gatedAt] at he
  | counterpartMsg => simp [Ev.gatedAt] at he
  | enableInterop _ => simp [Ev.gatedAt] at he
  | setAddresses => simp [Ev.gatedAt] at he

theorem movements_use_exempt_handler_or_enabled_chain {K : Cfg} {S T : St}
    {evs₁ evs₂ : List Ev} {e : Ev} (hr : RunV35 K S (evs₁ ++ e :: evs₂) T) {c : Chain}
    {a : AssetId} (he : e.gatedAt = some (c, a)) :
    ∃ U V : St, RunV35 K S evs₁ U ∧ StepV35 K e U V ∧ RunV35 K V evs₂ T ∧
      ∃ h, e.through K U = some h ∧ (h = K.ntv ∨ h = U.env.cah ∨ U.env.ie c = true) := by
  obtain ⟨U, hU, hrest⟩ := run_split hr evs₁ (e :: evs₂) rfl
  obtain ⟨V, hV, hV2⟩ := run_split hrest [e] evs₂ rfl
  exact ⟨U, V, hU, run_single hV, hV2, step_through (run_single hV) he⟩

/-! ## (b) What did not change -/

theorem run_projects_to_allWriters {K : Cfg} (hK : K.side = .l1) {S T : St} {evs : List Ev}
    (hr : RunV35 K S evs T) : ARun K S.router (ops evs) T.router := by
  induction hr with
  | nil => exact .nil
  | @snoc V W evs e _ hs ih =>
    unfold ops at ih ⊢
    rw [List.filterMap_append]
    cases hs with
    | @register _ caller d h hg =>
      exact ih.snoc (op := .register caller d h) (AStep.register hg)
    | seed => exact ih.snoc (op := .seed) AStep.seed
    | @setTracker _ d t => exact ih.snoc (op := .setTracker d t) (AStep.setTracker hK)
    | @finalize _ c a _ h0 hm =>
      have hside : K.side = .l2 → a ≠ K.seedId := by
        intro h2
        rw [hK] at h2
        cases h2
      exact ih.snoc (op := .finalize a) (AStep.finalize h0 hm hside)
    | gated _ _ =>
      show ARun K S.router (List.filterMap Ev.op evs ++ []) _
      rw [List.append_nil]
      exact ih
    | counterpartMsg =>
      show ARun K S.router (List.filterMap Ev.op evs ++ []) _
      rw [List.append_nil]
      exact ih
    | enableInterop _ =>
      show ARun K S.router (List.filterMap Ev.op evs ++ []) _
      rw [List.append_nil]
      exact ih
    | setAddresses =>
      show ARun K S.router (List.filterMap Ev.op evs ++ []) _
      rw [List.append_nil]
      exact ih

theorem gated_run_weakValid_on {K : Cfg} (hK : K.side = .l1) (hN : K.ntvAddr ≠ 0)
    (hmint : MintsOnlyNtvIds K) (hseed : IsNtvId K.enc K.ntvAddr K.seedId) {E : Env}
    {evs : List Ev} {T : St} (hr : RunV35 K ⟨empty, E⟩ evs T)
    (hinj : IdInjOn K.enc ↑(AllWriters.loggedTriples K (ops evs))) : WeakValid K T.router :=
  AllWriters.l1_run_weakValid_on hK hN hmint hseed (run_projects_to_allWriters hK hr) hinj

/-- One step that is not `setAddresses`: the chain asset handler stays, enabled chains stay
enabled, and only `enableInterop` changes a flag. -/
lemma step_env {K : Cfg} {S T : St} {e : Ev} (hs : StepV35 K e S T) (hn : ¬ e.IsSetAddresses) :
    T.env.cah = S.env.cah ∧ ∀ c, (S.env.ie c = true → T.env.ie c = true) ∧
      (e ≠ .enableInterop c → T.env.ie c = S.env.ie c) := by
  cases hs with
  | enableInterop _ =>
    refine ⟨rfl, fun x => ⟨enable_ie_of_true _ _, fun hx => ?_⟩⟩
    apply enable_ie_ne
    rintro rfl
    exact hx rfl
  | setAddresses => exact absurd trivial hn
  | register _ => exact ⟨rfl, fun _ => ⟨id, fun _ => rfl⟩⟩
  | seed => exact ⟨rfl, fun _ => ⟨id, fun _ => rfl⟩⟩
  | setTracker => exact ⟨rfl, fun _ => ⟨id, fun _ => rfl⟩⟩
  | finalize _ _ _ => exact ⟨rfl, fun _ => ⟨id, fun _ => rfl⟩⟩
  | gated _ _ => exact ⟨rfl, fun _ => ⟨id, fun _ => rfl⟩⟩
  | counterpartMsg => exact ⟨rfl, fun _ => ⟨id, fun _ => rfl⟩⟩

theorem interop_flags_one_way {K : Cfg} {S T : St} {evs : List Ev} (hr : RunV35 K S evs T)
    (hn : ∀ e ∈ evs, ¬ e.IsSetAddresses) :
    T.env.cah = S.env.cah ∧ ∀ c, (S.env.ie c = true → T.env.ie c = true) ∧
      (Ev.enableInterop c ∉ evs → T.env.ie c = S.env.ie c) := by
  induction hr with
  | nil => exact ⟨rfl, fun _ => ⟨id, fun _ => rfl⟩⟩
  | @snoc V W evs e _ hs ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun x hx => hn x (List.mem_append_left _ hx))
    obtain ⟨h1, h2⟩ := step_env hs (hn e (List.mem_append_right _ (List.mem_singleton_self _)))
    refine ⟨h1.trans ih1, fun c => ⟨fun hc => (h2 c).1 ((ih2 c).1 hc), fun hc => ?_⟩⟩
    have hne : e ≠ .enableInterop c := by
      rintro rfl
      exact hc (List.mem_append_right _ (List.mem_singleton_self _))
    rw [(h2 c).2 hne]
    exact (ih2 c).2 (fun hm => hc (List.mem_append_left _ hm))

theorem movements_at_disabled_chain {K : Cfg} {S T : St} {evs : List Ev}
    (hr : RunV35 K S evs T) (hn : ∀ e ∈ evs, ¬ e.IsSetAddresses) {c : Chain}
    (hc : T.env.ie c = false) {evs₁ evs₂ : List Ev} {e : Ev} (he : evs = evs₁ ++ e :: evs₂)
    {a : AssetId} (hg : e.gatedAt = some (c, a)) :
    ∃ U : St, RunV35 K S evs₁ U ∧ ∃ h, e.through K U = some h ∧ (h = K.ntv ∨ h = S.env.cah) := by
  subst he
  obtain ⟨U, V, hU, hs, hV, h, hth, hdis⟩ := movements_use_exempt_handler_or_enabled_chain hr hg
  have hUT : RunV35 K U (e :: evs₂) T := run_append (RunV35.nil.snoc hs) hV
  obtain ⟨-, hieUT⟩ := interop_flags_one_way hUT
    (fun x hx => hn x (List.mem_append_right _ hx))
  obtain ⟨hcahSU, -⟩ := interop_flags_one_way hU
    (fun x hx => hn x (List.mem_append_left _ hx))
  refine ⟨U, hU, h, hth, ?_⟩
  rcases hdis with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (h1.trans hcahSU)
  · have h2 := (hieUT c).1 h1
    rw [hc] at h2
    exact absurd h2 (by simp)

/-! ## (c) Stranding, and what ends it -/

/-- One step with no listed call keeps a stranding, and does not move `a` at `c`. -/
lemma step_keeps_stranded {K : Cfg} {S T : St} {e : Ev} {c : Chain} {a : AssetId}
    (hS : Stranded K S c a) (hs : StepV35 K e S T) (hm : ¬ e.MayUnstrand K c a) :
    Stranded K T c a ∧ e.gatedAt ≠ some (c, a) := by
  obtain ⟨⟨h0, hn, hc⟩, hie⟩ := hS
  cases hs with
  | @register _ caller d h hg =>
    have hw : a ≠ writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d :=
      fun h' => hm (Or.inl h'.symm)
    refine ⟨⟨?_, hie⟩, by simp [Ev.gatedAt]⟩
    show Custom K S.env ((setHandler K.enc K.thisChain K.ntv K.ntvAddr S.router caller d h).handler a)
    rw [handler_frame _ _ _ _ _ _ _ _ _ hw]
    exact ⟨h0, hn, hc⟩
  | seed =>
    have hw : a ≠ K.seedId := fun h' => hm (Or.inl h'.symm)
    refine ⟨⟨?_, hie⟩, by simp [Ev.gatedAt]⟩
    show Custom K S.env ((pointAt S.router K.seedId K.ntv).handler a)
    rw [pointAt_handler_ne _ _ hw]
    exact ⟨h0, hn, hc⟩
  | setTracker => exact ⟨⟨⟨h0, hn, hc⟩, hie⟩, by simp [Ev.gatedAt]⟩
  | @finalize _ c' a' _ h0' _ =>
    have hw : a ≠ a' := by
      rintro rfl
      exact h0 h0'
    refine ⟨⟨?_, hie⟩, ?_⟩
    · show Custom K S.env ((pointAt S.router a' K.ntv).handler a)
      rw [pointAt_handler_ne _ _ hw]
      exact ⟨h0, hn, hc⟩
    · simp only [Ev.gatedAt, ne_eq, Option.some.injEq, Prod.mk.injEq, not_and]
      exact fun _ h => hw h.symm
  | @gated _ g c' a' hA _ =>
    refine ⟨⟨⟨h0, hn, hc⟩, hie⟩, ?_⟩
    simp only [Ev.gatedAt, ne_eq, Option.some.injEq, Prod.mk.injEq, not_and]
    rintro rfl rfl
    exact (allowed_iff_not_stranded K S c' a').1 hA ⟨⟨h0, hn, hc⟩, hie⟩
  | counterpartMsg => exact ⟨⟨⟨h0, hn, hc⟩, hie⟩, by simp [Ev.gatedAt]⟩
  | @enableInterop _ c' _ =>
    have hw : c ≠ c' := by
      rintro rfl
      exact hm (Or.inr (Or.inl rfl))
    refine ⟨⟨⟨h0, hn, hc⟩, ?_⟩, by simp [Ev.gatedAt]⟩
    show (enable S.env c').ie c = false
    rw [enable_ie_ne _ hw]
    exact hie
  | setAddresses => exact absurd (Or.inr (Or.inr trivial)) hm

theorem stranded_until_listed_call {K : Cfg} {S T : St} {evs : List Ev} {c : Chain}
    {a : AssetId} (hS : Stranded K S c a) (hr : RunV35 K S evs T)
    (hm : ∀ e ∈ evs, ¬ e.MayUnstrand K c a) :
    Stranded K T c a ∧ ∀ e ∈ evs, e.gatedAt ≠ some (c, a) := by
  induction hr with
  | nil => exact ⟨hS, fun _ h => absurd h (List.not_mem_nil)⟩
  | @snoc V W evs e _ hs ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun x hx => hm x (List.mem_append_left _ hx))
    obtain ⟨h1, h2⟩ := step_keeps_stranded ih1 hs
      (hm e (List.mem_append_right _ (List.mem_singleton_self _)))
    refine ⟨h1, fun x hx => ?_⟩
    rcases List.mem_append.1 hx with hx | hx
    · exact ih2 x hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact h2

theorem unstranding_call_is_listed {K : Cfg} {S T : St} {e : Ev} {c : Chain} {a : AssetId}
    (hS : Stranded K S c a) (hs : StepV35 K e S T) (hT : ¬ Stranded K T c a) :
    e = .enableInterop c ∨ e.IsSetAddresses ∨ (e = .seed ∧ K.seedId = a) ∨
      ∃ caller d h, e = .register caller d h ∧
        writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d = a ∧
        (caller = K.ntv ∨ caller = S.router.tracker a) := by
  by_cases hm : e.MayUnstrand K c a
  · rcases hm with hw | he | hsa
    · cases hs with
      | @register _ caller d h hg =>
        refine Or.inr (Or.inr (Or.inr ⟨caller, d, h, rfl, hw, ?_⟩))
        have := hg.authorized
        rw [hw] at this
        exact this
      | seed => exact Or.inr (Or.inr (Or.inl ⟨rfl, hw⟩))
      | setTracker => exact absurd hw id
      | finalize _ _ _ => exact absurd hw id
      | gated _ _ => exact absurd hw id
      | counterpartMsg => exact absurd hw id
      | enableInterop _ => exact absurd hw id
      | setAddresses => exact absurd hw id
    · exact Or.inl he
    · exact Or.inr (Or.inl hsa)
  · exact absurd (step_keeps_stranded hS hs hm).1 hT

theorem open_gate_stays_open {K : Cfg} {S T : St} {evs : List Ev} {g : Gated} {c : Chain}
    {a : AssetId} (h0 : StepV35 K (.gated g c a) S S) (hr : RunV35 K S evs T)
    (hn : ∀ e ∈ evs, ¬ e.RewritesHandler K a ∧ ¬ e.IsSetAddresses) :
    T.router.handler a = S.router.handler a ∧ ∀ g' : Gated, StepV35 K (.gated g' c a) T T := by
  have hstart : S.router.handler a ≠ 0 ∧ Allowed K S.env S.router c a := by
    cases h0 with
    | gated hA hne => exact ⟨hne, hA⟩
  -- The invariant: `a`'s handler is the starting one, and the gate passes at `(c, a)`.
  suffices key : T.router.handler a = S.router.handler a ∧ Allowed K T.env T.router c a by
    refine ⟨key.1, fun g' => .gated key.2 ?_⟩
    rw [key.1]
    exact hstart.1
  induction hr with
  | nil => exact ⟨rfl, hstart.2⟩
  | @snoc V W evs e _ hs ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun x hx => hn x (List.mem_append_left _ hx))
    obtain ⟨hw, hsa⟩ := hn e (List.mem_append_right _ (List.mem_singleton_self _))
    have hV0 : V.router.handler a ≠ 0 := by
      rw [ih1]
      exact hstart.1
    -- If the step keeps `a`'s handler and the environment, the gate still passes.
    have keep : ∀ W' : St, W'.router.handler a = V.router.handler a → W'.env = V.env →
        W'.router.handler a = S.router.handler a ∧ Allowed K W'.env W'.router c a := by
      intro W' hh he
      refine ⟨hh.trans ih1, ?_⟩
      unfold Allowed
      rw [hh, he]
      exact ih2
    cases hs with
    | @register _ caller d h hg =>
      have hne : a ≠ writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d :=
        fun h' => hw h'.symm
      exact keep _ (handler_frame _ _ _ _ _ _ _ _ _ hne) rfl
    | seed =>
      have hne : a ≠ K.seedId := fun h' => hw h'.symm
      exact keep _ (pointAt_handler_ne _ _ hne) rfl
    | setTracker => exact keep _ rfl rfl
    | @finalize _ c' a' _ hz _ =>
      have hne : a ≠ a' := by
        rintro rfl
        exact hV0 hz
      exact keep _ (pointAt_handler_ne _ _ hne) rfl
    | gated _ _ => exact ⟨ih1, ih2⟩
    | counterpartMsg => exact ⟨ih1, ih2⟩
    | @enableInterop _ c' _ =>
      refine ⟨ih1, ?_⟩
      rcases ih2 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (enable_ie_of_true _ _ h)))
    | setAddresses => exact absurd trivial hsa

/-! ## A concrete L1 run for the witnesses

The configuration is `AllWriters.wK1`: chain `1`, vault `9`, `L2_NATIVE_TOKEN_VAULT_ADDR = 8`,
seeded id `ETH_TOKEN_ASSET_ID = 101`, the encoding `wEnc` (a triple hashed from `8` gets id
`100`, `101` or `102` by data `0`, `1` or other; any other triple gets its sender as id), and a
vault that mints exactly the vault ids.  The chain asset handler is `11`, and chains `270` and
`300` start without interop. -/

open Contracts.AssetRouter.AllWriters (wK1 wEnc wK1_mints isNtv_101 isNtv_102
  mem_loggedTriples idInjOn_mono)

/-- Chain asset handler `11`, no chain interop-enabled. -/
def gateE0 : Env := ⟨11, fun _ => false⟩
/-- After `enableInterop(300)`. -/
def gateE1 : Env := enable gateE0 300

/-- `setNativeTokenVault`: `ETH` (id `101`) → vault `9`. -/
def gateR1 : Router := pointAt empty 101 9
/-- The owner records tracker `5` for data `3`, at id `wEnc 1 5 3 = 5`. -/
def gateR2 : Router := recordTracker wK1 gateR1 3 5
/-- Tracker `5` registers its asset (id `5`) with the custom handler `7`. -/
def gateR3 : Router := setHandler wEnc 1 9 8 gateR2 5 3 7
/-- The vault registers its token `0` (id `100`), with itself as handler. -/
def gateR4 : Router := setHandler wEnc 1 9 8 gateR3 9 0 9
/-- A withdrawal of the vault id `102`, unseen so far, from chain `270` takes the fallback. -/
def gateR5 : Router := pointAt gateR4 102 9
/-- The owner records tracker `6` for data `4`, at id `6`. -/
def gateR6 : Router := recordTracker wK1 gateR5 4 6
/-- Tracker `6` registers its asset (id `6`) with the chain asset handler `11`. -/
def gateR7 : Router := setHandler wEnc 1 9 8 gateR6 6 4 11

/-- Seed, tracker write, custom registration, vault registration. -/
def gateSetup : List Ev := [.seed, .setTracker 3 5, .register 5 3 7, .register 9 0 9]
/-- A vault-asset deposit to `270`, a fallback withdrawal from `270`, a counterpart message,
and `enableInterop(300)`. -/
def gateBusyA : List Ev :=
  [.gated .deposit 270 100, .finalize 270 102, .counterpartMsg 270 5 7, .enableInterop 300]
/-- The custom asset's deposit to `300` and its confirmation. -/
def gateBusyB : List Ev := [.gated .deposit 300 5, .gated .confirm 300 5]
/-- A second tracker routes its asset to the chain asset handler. -/
def gateCtm : List Ev := [.setTracker 4 6, .register 6 4 11]

lemma gate_run_setup : RunV35 wK1 ⟨empty, gateE0⟩ gateSetup ⟨gateR4, gateE0⟩ := by
  have g3 : SetGuard wEnc 1 9 8 gateR2 5 3 := ⟨Or.inr (by decide), by decide⟩
  have g4 : SetGuard wEnc 1 9 8 gateR3 9 0 := ⟨Or.inl rfl, by decide⟩
  exact (((RunV35.nil.snoc StepV35.seed).snoc (StepV35.setTracker (d := 3) (t := 5))).snoc
    (StepV35.register (h := 7) g3)).snoc (StepV35.register (h := 9) g4)

lemma gate_run_busyA : RunV35 wK1 ⟨gateR4, gateE0⟩ gateBusyA ⟨gateR5, gateE1⟩ := by
  have s1 : StepV35 wK1 (.gated .deposit 270 100) ⟨gateR4, gateE0⟩ ⟨gateR4, gateE0⟩ :=
    .gated (by decide) (by decide)
  have s2 : StepV35 wK1 (.finalize 270 102) ⟨gateR4, gateE0⟩ ⟨gateR5, gateE0⟩ :=
    .finalize (Or.inl (by decide)) (by decide) isNtv_102
  have s4 : StepV35 wK1 (.enableInterop 300) ⟨gateR5, gateE0⟩ ⟨gateR5, gateE1⟩ :=
    .enableInterop rfl
  exact (((RunV35.nil.snoc s1).snoc s2).snoc (StepV35.counterpartMsg (c := 270) (a := 5)
    (h := 7))).snoc s4

lemma gate_step_custom_deposit (g : Gated) :
    StepV35 wK1 (.gated g 300 5) ⟨gateR5, gateE1⟩ ⟨gateR5, gateE1⟩ :=
  .gated (by decide) (by decide)

lemma gate_run_busyB : RunV35 wK1 ⟨gateR5, gateE1⟩ gateBusyB ⟨gateR5, gateE1⟩ :=
  (RunV35.nil.snoc (gate_step_custom_deposit .deposit)).snoc
    (gate_step_custom_deposit .confirm)

lemma gate_run_ctm : RunV35 wK1 ⟨gateR5, gateE1⟩ gateCtm ⟨gateR7, gateE1⟩ := by
  have g : SetGuard wEnc 1 9 8 gateR6 6 4 := ⟨Or.inr (by decide), by decide⟩
  exact (RunV35.nil.snoc (StepV35.setTracker (d := 4) (t := 6))).snoc
    (StepV35.register (h := 11) g)

/-- The setup leaves the custom asset `5` stranded at `270`. -/
lemma gate_stranded : Stranded wK1 ⟨gateR4, gateE0⟩ 270 5 := by decide

lemma not_mayUnstrand_of {K : Cfg} {c : Chain} {a : AssetId} {e : Ev}
    (h1 : ¬ e.RewritesHandler K a) (h2 : e ≠ .enableInterop c) (h3 : ¬ e.IsSetAddresses) :
    ¬ e.MayUnstrand K c a := by
  rintro (h | h | h)
  exacts [h1 h, h2 h, h3 h]

/-! ### Witnesses -/

theorem custom_movement_at_enabled_chain_witness :
    ∃ (K : Cfg) (E : Env) (T U : St) (evs₁ evs₂ : List Ev) (e : Ev) (c : Chain) (a : AssetId),
      K.side = .l1 ∧ RunV35 K ⟨empty, E⟩ (evs₁ ++ e :: evs₂) T ∧ evs₂ ≠ [] ∧
      e.gatedAt = some (c, a) ∧ RunV35 K ⟨empty, E⟩ evs₁ U ∧
      Custom K U.env (U.router.handler a) ∧ E.ie c = false ∧ Ev.enableInterop c ∈ evs₁ := by
  have hpre := run_append gate_run_setup gate_run_busyA
  refine ⟨wK1, gateE0, ⟨gateR5, gateE1⟩, ⟨gateR5, gateE1⟩, gateSetup ++ gateBusyA,
    [.gated .confirm 300 5], .gated .deposit 300 5, 300, 5, rfl,
    run_append hpre gate_run_busyB, by simp, rfl, hpre, by decide, rfl, ?_⟩
  simp [gateSetup, gateBusyA]

theorem run_projects_to_allWriters_witness :
    ∃ (K : Cfg) (E : Env) (T : St) (evs : List Ev),
      K.side = .l1 ∧ RunV35 K ⟨empty, E⟩ evs T ∧
      (∃ caller d h, Ev.register caller d h ∈ evs) ∧ Ev.seed ∈ evs ∧
      (∃ d t, Ev.setTracker d t ∈ evs) ∧ (∃ c a, Ev.finalize c a ∈ evs) ∧
      (∃ g c a, Ev.gated g c a ∈ evs) ∧ (∃ c a h, Ev.counterpartMsg c a h ∈ evs) ∧
      (∃ c, Ev.enableInterop c ∈ evs) ∧ (∃ cah ie, Ev.setAddresses cah ie ∈ evs) := by
  have hr := run_append (run_append gate_run_setup gate_run_busyA)
    (RunV35.nil.snoc (StepV35.setAddresses (cah := 12) (ie := fun _ => false)))
  refine ⟨wK1, gateE0, _, _, rfl, hr, ⟨5, 3, 7, ?_⟩, ?_, ⟨3, 5, ?_⟩, ⟨270, 102, ?_⟩,
    ⟨.deposit, 270, 100, ?_⟩, ⟨270, 5, 7, ?_⟩, ⟨300, ?_⟩, ⟨12, fun _ => false, ?_⟩⟩ <;>
    simp [gateSetup, gateBusyA]

/-- The router writes of `gateSetup ++ gateBusyA`. -/
lemma gate_ops : ops (gateSetup ++ gateBusyA) =
    [.seed, .setTracker 3 5, .register 5 3 7, .register 9 0 9, .finalize 102] := rfl

lemma gate_loggedTriples_sub :
    (↑(AllWriters.loggedTriples wK1 (ops (gateSetup ++ gateBusyA))) :
      Set (Chain × Address × AssetData)) ⊆
      {((1 : Chain), (5 : Address), (3 : AssetData)), (1, 8, 0)} := by
  intro p hp
  rw [Finset.mem_coe, mem_loggedTriples, gate_ops] at hp
  obtain ⟨op, hop, hpop⟩ := hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl
  · simp [Op.triple] at hpop
  · simp only [Op.triple, Option.some.injEq] at hpop
    subst hpop
    exact Set.mem_insert _ _
  · simp only [Op.triple, Option.some.injEq] at hpop
    subst hpop
    rw [show senderOf wK1.ntv wK1.ntvAddr 5 = 5 from senderOf_ne (by decide)]
    exact Set.mem_insert _ _
  · simp only [Op.triple, Option.some.injEq] at hpop
    subst hpop
    rw [show senderOf wK1.ntv wK1.ntvAddr 9 = 8 from senderOf_self _ _]
    exact Set.mem_insert_of_mem _ rfl
  · simp [Op.triple] at hpop

theorem gated_run_weakValid_on_witness :
    ∃ (K : Cfg) (E : Env) (evs : List Ev) (T : St),
      K.side = .l1 ∧ K.ntvAddr ≠ 0 ∧ MintsOnlyNtvIds K ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧
      RunV35 K ⟨empty, E⟩ evs T ∧ IdInjOn K.enc ↑(AllWriters.loggedTriples K (ops evs)) ∧
      (∃ g c a, Ev.gated g c a ∈ evs) ∧ (∃ c a, Ev.finalize c a ∈ evs) ∧
      (∃ c, Ev.enableInterop c ∈ evs) ∧ ¬ Valid T.router := by
  refine ⟨wK1, gateE0, gateSetup ++ gateBusyA, ⟨gateR5, gateE1⟩, rfl, by decide, wK1_mints,
    isNtv_101, run_append gate_run_setup gate_run_busyA,
    idInjOn_mono gate_loggedTriples_sub (idInjOn_pair (by decide)),
    ⟨.deposit, 270, 100, by simp [gateSetup, gateBusyA]⟩,
    ⟨270, 102, by simp [gateSetup, gateBusyA]⟩, ⟨300, by simp [gateSetup, gateBusyA]⟩, ?_⟩
  exact fun hV => hV 102 (by decide) (by decide)

theorem interop_flags_one_way_witness :
    ∃ (K : Cfg) (E : Env) (evs₀ evs : List Ev) (S T : St) (c c' : Chain),
      K.side = .l1 ∧ RunV35 K ⟨empty, E⟩ evs₀ S ∧ RunV35 K S evs T ∧
      (∀ e ∈ evs, ¬ e.IsSetAddresses) ∧ S.env.ie c = true ∧ S.env.ie c' = false ∧
      Ev.enableInterop c' ∈ evs ∧ ∃ g a, Ev.gated g c a ∈ evs := by
  have s1 : StepV35 wK1 (.enableInterop 270) ⟨gateR5, gateE1⟩ ⟨gateR5, enable gateE1 270⟩ :=
    .enableInterop (by decide)
  have s2 : StepV35 wK1 (.gated .deposit 300 5) ⟨gateR5, enable gateE1 270⟩
      ⟨gateR5, enable gateE1 270⟩ := .gated (by decide) (by decide)
  refine ⟨wK1, gateE0, gateSetup ++ gateBusyA, [.enableInterop 270, .gated .deposit 300 5],
    ⟨gateR5, gateE1⟩, _, 300, 270, rfl, run_append gate_run_setup gate_run_busyA,
    (RunV35.nil.snoc s1).snoc s2, ?_, by decide, by decide, by simp, .deposit, 5, by simp⟩
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> exact fun h => h

theorem movements_at_disabled_chain_witness :
    ∃ (K : Cfg) (E : Env) (evs : List Ev) (T : St) (c : Chain),
      K.side = .l1 ∧ RunV35 K ⟨empty, E⟩ evs T ∧ (∀ e ∈ evs, ¬ e.IsSetAddresses) ∧
      T.env.ie c = false ∧ (∃ g a, Ev.gated g c a ∈ evs) ∧ (∃ b, Ev.finalize c b ∈ evs) ∧
      ∃ (evs₁ evs₂ : List Ev) (g : Gated) (c' : Chain) (a : AssetId) (U : St),
        evs = evs₁ ++ Ev.gated g c' a :: evs₂ ∧ c' ≠ c ∧ RunV35 K ⟨empty, E⟩ evs₁ U ∧
        Custom K U.env (U.router.handler a) := by
  have hpre := run_append gate_run_setup gate_run_busyA
  refine ⟨wK1, gateE0, gateSetup ++ gateBusyA ++ gateBusyB, ⟨gateR5, gateE1⟩, 270, rfl,
    run_append hpre gate_run_busyB, ?_, by decide, ⟨.deposit, 100, by simp [gateBusyA]⟩,
    ⟨102, by simp [gateBusyA]⟩, gateSetup ++ gateBusyA, [.gated .confirm 300 5], .deposit, 300,
    5, ⟨gateR5, gateE1⟩, rfl, by decide, hpre, by decide⟩
  intro e he
  simp only [gateSetup, gateBusyA, gateBusyB, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact fun h => h

theorem stranded_until_listed_call_witness :
    ∃ (K : Cfg) (E : Env) (evs₀ evs : List Ev) (S T : St) (c c' : Chain) (a : AssetId),
      K.side = .l1 ∧ RunV35 K ⟨empty, E⟩ evs₀ S ∧ Stranded K S c a ∧ RunV35 K S evs T ∧
      (∀ e ∈ evs, ¬ e.MayUnstrand K c a) ∧ c' ≠ c ∧ Ev.enableInterop c' ∈ evs ∧
      (∃ g, Ev.gated g c' a ∈ evs) ∧ (∃ g b, b ≠ a ∧ Ev.gated g c b ∈ evs) ∧
      ∃ b, Ev.finalize c b ∈ evs := by
  refine ⟨wK1, gateE0, gateSetup, gateBusyA ++ gateBusyB, ⟨gateR4, gateE0⟩, ⟨gateR5, gateE1⟩,
    270, 300, 5, rfl, gate_run_setup, gate_stranded, run_append gate_run_busyA gate_run_busyB,
    ?_, by decide, by simp [gateBusyA], ⟨.deposit, by simp [gateBusyB]⟩,
    ⟨.deposit, 100, by decide, by simp [gateBusyA]⟩, ⟨102, by simp [gateBusyA]⟩⟩
  intro e he
  simp only [gateBusyA, gateBusyB, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_mayUnstrand_of (fun h => h) (by intro h; cases h) (fun h => h)
  · exact not_mayUnstrand_of (fun h => h) (by intro h; cases h) (fun h => h)
  · exact not_mayUnstrand_of (fun h => h) (by intro h; cases h) (fun h => h)
  · refine not_mayUnstrand_of (fun h => h) ?_ (fun h => h)
    intro h
    injection h with h'
    exact absurd h' (by decide)
  · exact not_mayUnstrand_of (fun h => h) (by intro h; cases h) (fun h => h)
  · exact not_mayUnstrand_of (fun h => h) (by intro h; cases h) (fun h => h)

theorem unstranding_call_is_listed_witness :
    ∃ (K : Cfg) (E : Env) (evs₀ : List Ev) (S T₁ T₂ : St) (e : Ev) (c : Chain) (a : AssetId),
      K.side = .l1 ∧ RunV35 K ⟨empty, E⟩ evs₀ S ∧ Stranded K S c a ∧
      StepV35 K (.enableInterop c) S T₁ ∧ ¬ Stranded K T₁ c a ∧
      StepV35 K e S T₂ ∧ ¬ Stranded K T₂ c a ∧
      ∃ d h, e = .register (S.router.tracker a) d h := by
  have g : SetGuard wEnc 1 9 8 gateR4 5 3 := ⟨Or.inr (by decide), by decide⟩
  have ht : gateR4.tracker 5 = 5 := by decide
  refine ⟨wK1, gateE0, gateSetup, ⟨gateR4, gateE0⟩, ⟨gateR4, enable gateE0 270⟩,
    ⟨setHandler wEnc 1 9 8 gateR4 5 3 9, gateE0⟩, .register 5 3 9, 270, 5, rfl,
    gate_run_setup, gate_stranded, .enableInterop rfl, by decide, StepV35.register g,
    by decide, 3, 9, ?_⟩
  show Ev.register 5 3 9 = Ev.register (gateR4.tracker 5) 3 9
  rw [ht]

theorem open_gate_stays_open_witness :
    ∃ (K : Cfg) (E : Env) (evs₀ evs : List Ev) (S T : St) (c : Chain) (a : AssetId),
      K.side = .l1 ∧ RunV35 K ⟨empty, E⟩ evs₀ S ∧ StepV35 K (.gated .deposit c a) S S ∧
      Custom K S.env (S.router.handler a) ∧ RunV35 K S evs T ∧
      (∀ e ∈ evs, ¬ e.RewritesHandler K a ∧ ¬ e.IsSetAddresses) ∧
      (∃ d t, Ev.setTracker d t ∈ evs) ∧ (∃ caller d h, Ev.register caller d h ∈ evs) ∧
      ∃ c', Ev.enableInterop c' ∈ evs := by
  have s3 : StepV35 wK1 (.enableInterop 270) ⟨gateR7, gateE1⟩ ⟨gateR7, enable gateE1 270⟩ :=
    .enableInterop (by decide)
  have s4 : StepV35 wK1 (.gated .depositBase 270 100) ⟨gateR7, enable gateE1 270⟩
      ⟨gateR7, enable gateE1 270⟩ := .gated (by decide) (by decide)
  have hrest : RunV35 wK1 ⟨gateR7, gateE1⟩ [.enableInterop 270, .gated .depositBase 270 100]
      ⟨gateR7, enable gateE1 270⟩ := (RunV35.nil.snoc s3).snoc s4
  refine ⟨wK1, gateE0, gateSetup ++ gateBusyA, gateCtm ++ [.enableInterop 270,
    .gated .depositBase 270 100], ⟨gateR5, gateE1⟩, _, 300, 5, rfl,
    run_append gate_run_setup gate_run_busyA, gate_step_custom_deposit .deposit, by decide,
    run_append gate_run_ctm hrest, ?_, ⟨4, 6, by simp [gateCtm]⟩,
    ⟨6, 4, 11, by simp [gateCtm]⟩, ⟨270, by simp⟩⟩
  intro e he
  simp only [gateCtm, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨fun h => h, fun h => h⟩
  · refine ⟨?_, fun h => h⟩
    show ¬ writtenId wEnc 1 9 8 6 4 = 5
    decide
  · exact ⟨fun h => h, fun h => h⟩
  · exact ⟨fun h => h, fun h => h⟩

theorem set_addresses_closes_open_gate :
    ∃ (K : Cfg) (E : Env) (evs₀ : List Ev) (S T : St) (c : Chain) (a : AssetId)
      (cah : Address) (ie : Chain → Bool),
      K.side = .l1 ∧ RunV35 K ⟨empty, E⟩ evs₀ S ∧ StepV35 K (.gated .deposit c a) S S ∧
      Custom K S.env (S.router.handler a) ∧ S.env.ie c = true ∧
      StepV35 K (.setAddresses cah ie) S T ∧ T.env.ie c = false ∧
      ¬ ∃ T', StepV35 K (.gated .confirm c a) T T' := by
  refine ⟨wK1, gateE0, gateSetup ++ gateBusyA, ⟨gateR5, gateE1⟩,
    ⟨gateR5, ⟨11, fun _ => false⟩⟩, 300, 5, 11, fun _ => false, rfl,
    run_append gate_run_setup gate_run_busyA, gate_step_custom_deposit .deposit, by decide,
    by decide, .setAddresses, rfl, ?_⟩
  rintro ⟨T', hs⟩
  cases hs with
  | gated hA _ => exact absurd hA (by decide)

theorem repointing_closes_open_gate :
    ∃ (K : Cfg) (E : Env) (evs₀ : List Ev) (S T : St) (c : Chain) (a : AssetId) (e : Ev),
      K.side = .l1 ∧ RunV35 K ⟨empty, E⟩ evs₀ S ∧ StepV35 K (.gated .deposit c a) S S ∧
      S.router.handler a = S.env.cah ∧ S.env.ie c = false ∧
      StepV35 K e S T ∧ e.RewritesHandler K a ∧ ¬ e.IsSetAddresses ∧
      (∃ d h, e = .register (S.router.tracker a) d h) ∧ Custom K T.env (T.router.handler a) ∧
      ¬ ∃ T', StepV35 K (.gated .confirm c a) T T' := by
  have g : SetGuard wEnc 1 9 8 gateR7 6 4 := ⟨Or.inr (by decide), by decide⟩
  have ht : gateR7.tracker 6 = 6 := by decide
  refine ⟨wK1, gateE0, gateSetup ++ gateBusyA ++ gateCtm, ⟨gateR7, gateE1⟩,
    ⟨setHandler wEnc 1 9 8 gateR7 6 4 7, gateE1⟩, 270, 6, .register 6 4 7, rfl,
    run_append (run_append gate_run_setup gate_run_busyA) gate_run_ctm,
    .gated (by decide) (by decide), by decide, by decide, StepV35.register g, ?_,
    fun h => h, ⟨4, 7, ?_⟩, by decide, ?_⟩
  · show writtenId wEnc 1 9 8 6 4 = 6
    decide
  · show Ev.register 6 4 7 = Ev.register (gateR7.tracker 6) 4 7
    rw [ht]
  · rintro ⟨T', hs⟩
    cases hs with
    | gated hA _ => exact absurd hA (by decide)

/-! ## Certificates -/

theorem MovementEnabledIff : Properties.MovementEnabledIff := movement_enabled_iff

theorem MovementsUseExemptHandlerOrEnabledChain :
    Properties.MovementsUseExemptHandlerOrEnabledChain :=
  fun _ _ _ _ _ _ hr _ _ he => movements_use_exempt_handler_or_enabled_chain hr he

theorem CustomMovementAtEnabledChainWitness : Properties.CustomMovementAtEnabledChainWitness :=
  custom_movement_at_enabled_chain_witness

theorem RunProjectsToAllWriters : Properties.RunProjectsToAllWriters :=
  fun _ hK _ _ _ hr => run_projects_to_allWriters hK hr

theorem RunProjectsToAllWritersWitness : Properties.RunProjectsToAllWritersWitness :=
  run_projects_to_allWriters_witness

theorem GatedRunWeakValidOn : Properties.GatedRunWeakValidOn :=
  fun _ hK hN hmint hseed _ _ _ hr hinj => gated_run_weakValid_on hK hN hmint hseed hr hinj

theorem GatedRunWeakValidOnWitness : Properties.GatedRunWeakValidOnWitness :=
  gated_run_weakValid_on_witness

theorem InteropFlagsOneWayWithoutSetAddresses :
    Properties.InteropFlagsOneWayWithoutSetAddresses :=
  fun _ _ _ _ hr hn => interop_flags_one_way hr hn

theorem InteropFlagsOneWayWitness : Properties.InteropFlagsOneWayWitness :=
  interop_flags_one_way_witness

theorem MovementsAtDisabledChainUseExemptHandler :
    Properties.MovementsAtDisabledChainUseExemptHandler :=
  fun _ _ _ _ hr hn _ hc _ _ _ he _ hg => movements_at_disabled_chain hr hn hc he hg

theorem MovementsAtDisabledChainWitness : Properties.MovementsAtDisabledChainWitness :=
  movements_at_disabled_chain_witness

theorem StrandedUntilListedCall : Properties.StrandedUntilListedCall :=
  fun _ _ _ _ _ _ hS hr hm => stranded_until_listed_call hS hr hm

theorem StrandedAlongRun : Properties.StrandedAlongRun := by
  intro K S T evs₁ evs₂ c a hS hr hm
  obtain ⟨U, hU, hUT⟩ := run_split hr evs₁ evs₂ rfl
  have hstr := (stranded_until_listed_call hS hU
    (fun e he => hm e (List.mem_append_left _ he))).1
  refine ⟨U, hU, hUT, hstr, fun g hstep => ?_⟩
  exact ((movement_enabled_iff K U c a).1 g).1.1 hstep |>.2 hstr

theorem StrandedUntilListedCallWitness : Properties.StrandedUntilListedCallWitness :=
  stranded_until_listed_call_witness

theorem UnstrandingCallIsListed : Properties.UnstrandingCallIsListed :=
  fun _ _ _ _ _ _ hS hs hT => unstranding_call_is_listed hS hs hT

theorem UnstrandingCallIsListedWitness : Properties.UnstrandingCallIsListedWitness :=
  unstranding_call_is_listed_witness

theorem OpenGateStaysOpen : Properties.OpenGateStaysOpen :=
  fun _ _ _ _ _ _ _ h0 hr hn => open_gate_stays_open h0 hr hn

theorem OpenGateStaysOpenWitness : Properties.OpenGateStaysOpenWitness :=
  open_gate_stays_open_witness

theorem SetAddressesClosesOpenGate : Properties.SetAddressesClosesOpenGate :=
  set_addresses_closes_open_gate

theorem RepointingClosesOpenGate : Properties.RepointingClosesOpenGate :=
  repointing_closes_open_gate

end Contracts.AssetRouter.HandlerGateAtV35
