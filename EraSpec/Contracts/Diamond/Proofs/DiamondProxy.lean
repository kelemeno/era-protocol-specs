import EraSpec.Contracts.Diamond.Properties.DiamondProxy
import EraSpec.Contracts.ChainTypeManager.Proofs.DiamondStorage

/-!
# Proofs: the diamond proxy's routing, freezing and init call

The storage invariant `DiamondOk` and its preservation by every cut are
`Contracts.ChainTypeManager.Proofs.DiamondStorage` (`diamondCut_ok`, `fresh_ok`), used as they
are. New here:

* `FreezeUniform` is preserved by each action. The only interesting case is
  `_addOneFunction`: on consistent storage, every selector already routed to the facet is in
  its selector list, so the list is nonempty and the check compares against a selector that
  routes to the facet (`addOne_save_uniform`).
* The return-data check pins the bytes: on 32-byte strings the big-endian value is injective
  and below `2^256` (`decode_eq_magic`), so accepting means returning exactly `magicBytes`.
  This is a restricted injectivity on 32-byte strings, proved, not assumed.
* Runs: `step_inv` / `run_inv` carry the invariant; freezing results go by cases on `Step`.
-/

namespace Contracts.Diamond

open Clear
open Contracts.ChainTypeManager

/-! ## Routing helpers -/

lemma routing_eq_some {ds : DiamondStorage} {x : Selector} {f : Address} {b : Bool} :
    ds.routing x = some (f, b) ↔
      (ds.selectorToFacet x).facetAddress = f ∧ f ≠ 0 ∧ (ds.selectorToFacet x).isFreezable = b := by
  unfold DiamondStorage.routing
  split_ifs with h0
  · simp only [false_iff]
    rintro ⟨h1, h2, -⟩
    exact h2 (h1 ▸ h0)
  · simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h1 ▸ h0, h2⟩
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩

lemma saveFacetIfNew_sels (ds : DiamondStorage) (f g : Address) :
    ((saveFacetIfNew ds f).facetToSelectors g).selectors = (ds.facetToSelectors g).selectors := by
  unfold saveFacetIfNew
  split_ifs
  · by_cases hg : g = f
    · subst hg; simp
    · simp [upd_ne _ _ hg]
  · rfl

/-- On consistent storage, the first selector of `f`'s list routes to `f`, and every selector
routed to `f` has that selector's freezability (given uniformity). -/
lemma first_sel_routes {ds : DiamondStorage} (hI : DiamondOk ds) {f : Address} {y₀ : Selector}
    {rest : List Selector} (hs : (ds.facetToSelectors f).selectors = y₀ :: rest) :
    ds.routing y₀ = some (f, (ds.selectorToFacet y₀).isFreezable) := by
  have hy : y₀ ∈ (ds.facetToSelectors f).selectors := by rw [hs]; exact List.mem_cons_self
  obtain ⟨h1, h2⟩ := hI.mem_sels.mp hy
  exact routing_eq_some.mpr ⟨h1, h2, rfl⟩

/-! ## `FreezeUniform` under each writer -/

lemma FreezeUniform.of_routing {ds d : DiamondStorage} (h : d.routing = ds.routing)
    (hU : FreezeUniform ds) : FreezeUniform d := by
  intro x y f b c hx hy
  rw [h] at hx hy
  exact hU x y f b c hx hy

lemma FreezeUniform.upd_none {ds d : DiamondStorage} {z : Selector}
    (h : d.routing = upd ds.routing z none) (hU : FreezeUniform ds) : FreezeUniform d := by
  intro x y f b c hx hy
  rw [h] at hx hy
  by_cases hxz : x = z
  · subst hxz; simp at hx
  by_cases hyz : y = z
  · subst hyz; simp at hy
  rw [upd_ne _ _ hxz] at hx
  rw [upd_ne _ _ hyz] at hy
  exact hU x y f b c hx hy

/-- **What the freezability check enforces**: if `_addOneFunction` (after `_saveFacetIfNew`)
succeeds on consistent, freeze-uniform storage, every selector already routed to the facet has
the new selector's freezability. -/
lemma addOne_save_key {ds d : DiamondStorage} {f : Address} {x : Selector} {b : Bool}
    (hI : DiamondOk ds) (hU : FreezeUniform ds)
    (h : addOneFunction (saveFacetIfNew ds f) f x b = some d) :
    ∀ z c, ds.routing z = some (f, c) → c = b := by
    intro z c hz
    have hmem : z ∈ (ds.facetToSelectors f).selectors := hI.mem_routing.mpr ⟨c, hz⟩
    obtain ⟨y₀, rest, hs⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
    have hb : b = (ds.selectorToFacet y₀).isFreezable := by
      by_contra hne
      unfold addOneFunction at h
      simp only [saveFacetIfNew_sels, saveFacetIfNew_s2f, hs] at h
      simp [hne] at h
    have h0 := first_sel_routes hI hs
    rw [hU z y₀ f c _ hz h0, hb]

/-- **`_addOneFunction` keeps freeze-uniformity** (after `_saveFacetIfNew`), on consistent
storage. -/
lemma addOne_save_uniform {ds d : DiamondStorage} {f : Address} {x : Selector} {b : Bool}
    (hI : DiamondOk ds) (hU : FreezeUniform ds) (hf : f ≠ 0)
    (h : addOneFunction (saveFacetIfNew ds f) f x b = some d) : FreezeUniform d := by
  have hkey := addOne_save_key hI hU h
  have hr : d.routing = upd ds.routing x (some (f, b)) := by
    rw [addOne_routing hf h, saveFacetIfNew_routing]
  intro y z g c c' hy hz
  rw [hr] at hy hz
  by_cases hyx : y = x
  · subst hyx
    rw [upd_same] at hy
    simp only [Option.some.injEq, Prod.mk.injEq] at hy
    obtain ⟨rfl, rfl⟩ := hy
    by_cases hzx : z = y
    · subst hzx
      rw [upd_same] at hz
      simp only [Option.some.injEq, Prod.mk.injEq] at hz
      exact hz.2
    · rw [upd_ne _ _ hzx] at hz
      exact (hkey z c' hz).symm
  · rw [upd_ne _ _ hyx] at hy
    by_cases hzx : z = x
    · subst hzx
      rw [upd_same] at hz
      simp only [Option.some.injEq, Prod.mk.injEq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      exact hkey y c hy
    · rw [upd_ne _ _ hzx] at hz
      exact hU y z g c c' hy hz

lemma addLoop_uniform {f : Address} {b : Bool} (hf : f ≠ 0) :
    ∀ (xs : List Selector) (d d' : DiamondStorage), DiamondOk d →
      (d.facetToSelectors f).selectors ≠ [] → FreezeUniform d → addLoop d f xs b = some d' →
      FreezeUniform d' := by
  intro xs
  induction xs with
  | nil => intro d d' _ _ hU h; simp [addLoop] at h; subst h; exact hU
  | cons x xs ih =>
    intro d d' hI hne hU h
    simp only [addLoop] at h
    split_ifs at h with hx
    cases h1 : addOneFunction d f x b with
    | none => rw [h1] at h; simp at h
    | some d1 =>
      rw [h1, Option.bind_some] at h
      rw [← saveFacetIfNew_of_ne hne] at h1
      obtain ⟨hI1, hne1⟩ := addOne_save_ok hI hf (not_not.mp hx) h1
      exact ih d1 d' hI1 hne1 (addOne_save_uniform hI hU hf h1) h

lemma addFunctions_uniform {ds d : DiamondStorage} {f : Address} {xs : List Selector}
    {b : Bool} (hI : DiamondOk ds) (hU : FreezeUniform ds)
    (h : addFunctions ds f xs b = some d) : FreezeUniform d := by
  unfold addFunctions at h
  split_ifs at h with hf
  cases xs with
  | nil =>
    simp only [addLoop, Option.some.injEq] at h
    subst h
    exact FreezeUniform.of_routing (saveFacetIfNew_routing ds f) hU
  | cons x xs =>
    simp only [addLoop, saveFacetIfNew_s2f] at h
    split_ifs at h with hx
    cases h1 : addOneFunction (saveFacetIfNew ds f) f x b with
    | none => rw [h1] at h; simp at h
    | some d1 =>
      rw [h1, Option.bind_some] at h
      obtain ⟨hI1, hne1⟩ := addOne_save_ok hI hf (not_not.mp hx) h1
      exact addLoop_uniform hf xs d1 d hI1 hne1 (addOne_save_uniform hI hU hf h1) h

lemma removeLoop_uniform : ∀ (xs : List Selector) (d d' : DiamondStorage),
    FreezeUniform d → removeLoop d xs = some d' → FreezeUniform d' := by
  intro xs
  induction xs with
  | nil => intro d d' hU h; simp [removeLoop] at h; subst h; exact hU
  | cons x xs ih =>
    intro d d' hU h
    simp only [removeLoop] at h
    split_ifs at h with hx
    cases h1 : removeOneFunction d (d.selectorToFacet x).facetAddress x with
    | none => rw [h1] at h; simp at h
    | some d1 =>
      rw [h1, Option.bind_some] at h
      exact ih d1 d' (FreezeUniform.upd_none (removeOne_routing h1) hU) h

lemma replaceLoop_uniform {f : Address} {b : Bool} (hf : f ≠ 0) :
    ∀ (xs : List Selector) (d d' : DiamondStorage), DiamondOk d → FreezeUniform d →
      replaceLoop d f xs b = some d' → FreezeUniform d' := by
  intro xs
  induction xs with
  | nil => intro d d' _ hU h; simp [replaceLoop] at h; subst h; exact hU
  | cons x xs ih =>
    intro d d' hI hU h
    simp only [replaceLoop] at h
    split_ifs at h with hx
    cases h1 : removeOneFunction d (d.selectorToFacet x).facetAddress x with
    | none => rw [h1] at h; simp at h
    | some d1 =>
      rw [h1, Option.bind_some] at h
      have hI1 := removeOne_ok hI hx rfl h1
      have hU1 := FreezeUniform.upd_none (removeOne_routing h1) hU
      have hx1 : (d1.selectorToFacet x).facetAddress = 0 := removeOne_s2f_self h1
      cases h2 : addOneFunction (saveFacetIfNew d1 f) f x b with
      | none => rw [h2] at h; simp at h
      | some d2 =>
        rw [h2, Option.bind_some] at h
        exact ih d2 d' (addOne_save_ok hI1 hf hx1 h2).1 (addOne_save_uniform hI1 hU1 hf h2) h

lemma facetCut_uniform {ds d : DiamondStorage} {c : FacetCut} (hI : DiamondOk ds)
    (hU : FreezeUniform ds) (h : facetCut ds c = some d) : FreezeUniform d := by
  unfold facetCut at h
  split_ifs at h with hne
  cases hc : c.action with
  | add => rw [hc] at h; exact addFunctions_uniform hI hU h
  | replace =>
    rw [hc] at h
    unfold replaceFunctions at h
    split_ifs at h with hf
    exact replaceLoop_uniform hf _ _ _ hI hU h
  | remove =>
    rw [hc] at h
    unfold removeFunctions at h
    split_ifs at h with hf
    exact removeLoop_uniform _ _ _ hU h

lemma diamondCut_inv : ∀ (cs : List FacetCut) (ds d : DiamondStorage), DiamondOk ds →
    FreezeUniform ds → diamondCut ds cs = some d → DiamondOk d ∧ FreezeUniform d := by
  intro cs
  induction cs with
  | nil => intro ds d hI hU h; simp [diamondCut] at h; subst h; exact ⟨hI, hU⟩
  | cons c cs ih =>
    intro ds d hI hU h
    simp only [diamondCut] at h
    cases h1 : facetCut ds c with
    | none => rw [h1] at h; simp at h
    | some d1 =>
      rw [h1, Option.bind_some] at h
      exact ih d1 d (facetCut_ok hI h1) (facetCut_uniform hI hU h1) h

/-! ## The magic value pins the return data -/

lemma bytesToNat_acc : ∀ (l : Bytes) (acc : ℕ), bytesToNat l acc = acc * 256 ^ l.length + bytesToNat l 0
  | [], acc => by simp [bytesToNat]
  | b :: bs, acc => by
    simp only [bytesToNat]
    rw [bytesToNat_acc bs (acc * 256 + b.toNat), bytesToNat_acc bs (0 * 256 + b.toNat)]
    simp only [List.length_cons, pow_succ]
    ring

lemma bytesToNat_lt : ∀ l : Bytes, bytesToNat l 0 < 256 ^ l.length
  | [] => by simp [bytesToNat]
  | b :: bs => by
    simp only [bytesToNat, zero_mul, zero_add]
    rw [bytesToNat_acc]
    have h1 := bytesToNat_lt bs
    have hb : b.toNat < 256 := UInt8.toNat_lt b
    simp only [List.length_cons, pow_succ]
    nlinarith

lemma bytesToNat_inj : ∀ (l₁ l₂ : Bytes), l₁.length = l₂.length →
    bytesToNat l₁ 0 = bytesToNat l₂ 0 → l₁ = l₂
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | b₁ :: t₁, b₂ :: t₂, hl, h => by
    have hl' : t₁.length = t₂.length := by simpa using hl
    simp only [bytesToNat, zero_mul, zero_add] at h
    rw [bytesToNat_acc t₁, bytesToNat_acc t₂, hl'] at h
    have h1 := bytesToNat_lt t₁
    have h2 := bytesToNat_lt t₂
    rw [hl'] at h1
    have hP : 0 < 256 ^ t₂.length := by positivity
    have hd : b₁.toNat = b₂.toNat := by
      have this : (b₁.toNat * 256 ^ t₂.length + bytesToNat t₁ 0) / 256 ^ t₂.length =
          (b₂.toNat * 256 ^ t₂.length + bytesToNat t₂ 0) / 256 ^ t₂.length := by rw [h]
      rw [add_comm (b₁.toNat * _), add_comm (b₂.toNat * _), Nat.add_mul_div_right _ _ hP,
        Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt h1, Nat.div_eq_of_lt h2] at this
      simpa using this
    have hr : bytesToNat t₁ 0 = bytesToNat t₂ 0 := by
      rw [hd] at h
      omega
    rw [UInt8.toNat_inj.mp hd, bytesToNat_inj t₁ t₂ hl' hr]

lemma size_eq : UInt256.size = 256 ^ 32 := by
  simp [UInt256.size]

lemma magic_decode : decodeBytes32 magicBytes = MAGIC := by decide

/-- **On 32-byte strings, decoding to the magic value means being the magic bytes.** -/
lemma decode_eq_magic {data : Bytes} (hl : data.length = 32) (h : decodeBytes32 data = MAGIC) :
    data = magicBytes := by
  rw [← magic_decode] at h
  unfold decodeBytes32 at h
  have h1 := bytesToNat_lt data
  have h2 := bytesToNat_lt magicBytes
  rw [hl] at h1
  have hm : magicBytes.length = 32 := rfl
  rw [hm] at h2
  have := congrArg Fin.val h
  simp only [Fin.val_ofNat] at this
  rw [Nat.mod_eq_of_lt (size_eq ▸ h1), Nat.mod_eq_of_lt (size_eq ▸ h2)] at this
  exact bytesToNat_inj _ _ (by rw [hl, hm]) this

/-! ## The init call and the whole cut -/

lemma initialize_spec {s s' : ProxyState} {init : Address} {cd : Bytes} {r : InitRun}
    (h : initializeDiamondCut s init cd r = some s') :
    s'.isFrozen = s.isFrozen ∧
      ((init = 0 ∧ cd = [] ∧ s'.ds = s.ds) ∨
       (init ≠ 0 ∧ r.outcome = .returned magicBytes ∧ diamondCut s.ds r.nested = some s'.ds)) := by
  unfold initializeDiamondCut at h
  split_ifs at h with h0 hcd
  · cases h
    exact ⟨rfl, Or.inl ⟨h0, List.eq_nil_of_length_eq_zero (not_not.mp hcd), rfl⟩⟩
  · cases ho : r.outcome with
    | reverted data => rw [ho] at h; simp at h
    | returned data =>
      rw [ho] at h
      simp only at h
      cases hn : diamondCut s.ds r.nested with
      | none => rw [hn] at h; simp at h
      | some d' =>
        rw [hn, Option.bind_some] at h
        split_ifs at h with hlen hdec
        cases h
        have hdata := decode_eq_magic (not_not.mp hlen) (not_not.mp hdec)
        exact ⟨rfl, Or.inr ⟨h0, by rw [hdata], rfl⟩⟩

lemma cutFull_spec {s s' : ProxyState} {c : CutData} {r : InitRun}
    (h : diamondCutFull s c r = some s') :
    s'.isFrozen = s.isFrozen ∧
    ∃ d₁, diamondCut s.ds c.facetCuts = some d₁ ∧
      ((c.initAddress = 0 ∧ c.initCalldata = [] ∧ s'.ds = d₁) ∨
       (c.initAddress ≠ 0 ∧ r.outcome = .returned magicBytes ∧
         diamondCut d₁ r.nested = some s'.ds)) := by
  unfold diamondCutFull at h
  cases h1 : diamondCut s.ds c.facetCuts with
  | none => rw [h1] at h; simp at h
  | some d₁ =>
    rw [h1, Option.bind_some] at h
    obtain ⟨hz, hc⟩ := initialize_spec h
    exact ⟨hz, d₁, rfl, hc⟩

lemma cutFull_inv {s s' : ProxyState} {c : CutData} {r : InitRun} (hI : DiamondOk s.ds)
    (hU : FreezeUniform s.ds) (h : diamondCutFull s c r = some s') :
    DiamondOk s'.ds ∧ FreezeUniform s'.ds := by
  obtain ⟨-, d₁, h1, hc⟩ := cutFull_spec h
  obtain ⟨hI1, hU1⟩ := diamondCut_inv _ _ _ hI hU h1
  rcases hc with ⟨-, -, he⟩ | ⟨-, -, hn⟩
  · rw [he]; exact ⟨hI1, hU1⟩
  · exact diamondCut_inv _ _ _ hI1 hU1 hn

/-! ## Runs -/

lemma fresh_uniform : FreezeUniform DiamondStorage.fresh := by
  intro x y f b c hx _
  simp [DiamondStorage.routing, DiamondStorage.fresh, SelectorToFacet.zero] at hx

lemma step_inv {E : Env} {c : Address} {s s' : ProxyState} (hs : Step E c s s')
    (hI : DiamondOk s.ds) (hU : FreezeUniform s.ds) : DiamondOk s'.ds ∧ FreezeUniform s'.ds := by
  cases hs with
  | cut c r _ _ h => exact cutFull_inv hI hU h
  | freeze => exact ⟨hI, hU⟩
  | unfreeze => exact ⟨hI, hU⟩
  | other => exact ⟨hI, hU⟩

lemma run_inv {E : Env} {cs : List Address} {s s' : ProxyState} (hr : Run E cs s s') :
    DiamondOk s.ds → FreezeUniform s.ds → DiamondOk s'.ds ∧ FreezeUniform s'.ds := by
  induction hr with
  | nil => exact fun hI hU => ⟨hI, hU⟩
  | cons hs _ ih =>
    intro hI hU
    obtain ⟨hI1, hU1⟩ := step_inv hs hI hU
    exact ih hI1 hU1

lemma reach_inv {E : Env} {s : ProxyState} (h : Reach E s) : DiamondOk s.ds ∧ FreezeUniform s.ds := by
  obtain ⟨cid, cut, r, s₀, cs, hc, hr⟩ := h
  have hc' : diamondCutFull ProxyState.fresh cut r = some s₀ := by simpa [construct] using hc
  obtain ⟨hI0, hU0⟩ := cutFull_inv (s := ProxyState.fresh) fresh_ok fresh_uniform hc'
  exact run_inv hr hI0 hU0

/-! ## Dispatch -/

theorem DispatchExact : Properties.DispatchExact := by
  intro s cd f
  unfold fallbackTarget
  simp only [routing_eq_some]
  obtain ⟨a, p, fz⟩ := s.ds.selectorToFacet cd.sig
  cases hfr : s.isFrozen <;> cases fz <;> by_cases hl : (4 ≤ cd.len ∨ cd.len = 0) <;>
    by_cases ha : a = 0 <;> simp [hl, ha] <;> aesop

lemma dispatch_spec {s : ProxyState} {cd : Calldata} {f : Address}
    (h : fallbackTarget s cd = some f) :
    (4 ≤ cd.len ∨ cd.len = 0) ∧
      ∃ b, s.ds.routing cd.sig = some (f, b) ∧ (s.isFrozen = false ∨ b = false) :=
  (DispatchExact s cd f).mp h

theorem FreezeBlocksExactlyFreezable : Properties.FreezeBlocksExactlyFreezable := by
  intro ds cd
  refine ⟨fun hnot => ?_, fun f hf => ?_⟩
  · unfold fallbackTarget
    split_ifs <;> try rfl
    all_goals simp_all [routing_eq_some]
  · have hf' := routing_eq_some.mp hf
    refine ⟨?_, fun hl => ?_⟩
    · unfold fallbackTarget
      split_ifs <;> try rfl
      simp_all
    · unfold fallbackTarget
      simp [hl, hf'.1, hf'.2.1]

/-! ## The properties -/

theorem ReachableInvariant : Properties.ReachableInvariant := fun _ _ h => reach_inv h

theorem ReachableGettersMatchDispatch : Properties.ReachableGettersMatchDispatch := by
  intro E s hR x f b hx
  obtain ⟨hI, hU⟩ := reach_inv hR
  have hmem : x ∈ (s.ds.facetToSelectors f).selectors := hI.mem_routing.mpr ⟨b, hx⟩
  obtain ⟨y₀, rest, hs⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  have hfacet : isFacetFreezable s.ds f = b := by
    unfold isFacetFreezable
    rw [hs]
    exact (hU x y₀ f b _ hx (first_sel_routes hI hs)).symm
  have hx' := routing_eq_some.mp hx
  refine ⟨hfacet, ?_, hI.mem_facets.mpr (List.ne_nil_of_mem hmem), hmem, ?_⟩
  · unfold isFunctionFreezable
    simp [hx'.1, hx'.2.1, hx'.2.2]
  · intro cd hsig hl
    rw [DispatchExact, hfacet, hsig]
    constructor
    · rintro ⟨-, b', hb', hor⟩
      rw [hx] at hb'
      simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hb'
      rw [hb']
      exact hor
    · intro hor
      exact ⟨hl, b, hx, hor⟩

theorem OnlyCtmTogglesFreeze : Properties.OnlyCtmTogglesFreeze := by
  intro E c s s' hs hne
  cases hs with
  | cut c r _ _ h => exact absurd (cutFull_spec h).1 hne
  | freeze _ _ hc _ => exact ⟨hc, rfl⟩
  | unfreeze _ _ hc _ => exact ⟨hc, rfl⟩
  | other => exact absurd rfl hne

theorem RunsWithoutCtmKeepFreeze : Properties.RunsWithoutCtmKeepFreeze := by
  intro E cs s s' hr
  induction hr with
  | nil => intro _; rfl
  | @cons c cs s s₁ s₂ hs _ ih =>
    intro hnot
    have hc : c ≠ E.ctm := fun h => hnot (h ▸ List.mem_cons_self)
    have h1 : s₁.isFrozen = s.isFrozen := by
      by_contra hne
      exact hc (OnlyCtmTogglesFreeze E c s s₁ hs hne).1
    rw [ih (fun h => hnot (List.mem_cons_of_mem _ h)), h1]

lemma step_stuck {E : Env} {c : Address} {s s₁ : ProxyState} (hs : Step E c s s₁)
    (hfz : s.isFrozen = true)
    (hprem : ∀ (x : Selector) (f : Address) (b : Bool), s.ds.routing x = some (f, b) →
      (E.fn f x = .executeCut ∨ E.fn f x = .unfreeze) → b = true) : s₁ = s := by
  cases hs with
  | cut c r hd hfn _ =>
    obtain ⟨-, b, hb, hor⟩ := dispatch_spec hd
    have := hprem _ _ _ hb (Or.inl hfn)
    rw [hfz, this] at hor
    simp at hor
  | freeze _ _ _ hnf => rw [hfz] at hnf; cases hnf
  | unfreeze hd hfn _ _ =>
    obtain ⟨-, b, hb, hor⟩ := dispatch_spec hd
    have := hprem _ _ _ hb (Or.inr hfn)
    rw [hfz, this] at hor
    simp at hor
  | other => rfl

theorem FreezableEntrypointsMakeFreezePermanent :
    Properties.FreezableEntrypointsMakeFreezePermanent := by
  intro E cs s s' hfz hprem hr
  induction hr with
  | nil => rfl
  | cons hs _ ih =>
    have h1 := step_stuck hs hfz hprem
    subst h1
    exact ih hfz hprem

/-! ## The cut -/

lemma addAll_map_spec (r : Route) : ∀ (xs : List Selector) (ρ ρ' : Routing),
    addAll ρ (xs.map fun x => (x, r)) = some ρ' →
    xs.Nodup ∧ (∀ x ∈ xs, ρ x = none) ∧ ∀ y, ρ' y = if y ∈ xs then some r else ρ y
  | [], ρ, ρ', h => by simp [addAll] at h; subst h; simp
  | x :: xs, ρ, ρ', h => by
    simp only [List.map_cons, addAll, addSel] at h
    by_cases hx : ρ x = none
    swap
    · simp [hx] at h
    simp only [hx, ite_true, Option.bind_some] at h
    obtain ⟨hnd, hfree, hpt⟩ := addAll_map_spec r xs _ _ h
    refine ⟨List.nodup_cons.mpr ⟨fun hmem => ?_, hnd⟩, ?_, ?_⟩
    · have := hfree x hmem
      simp at this
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · have := hfree y hy
        by_cases hyx : y = x
        · subst hyx; exact hx
        · rwa [upd_ne _ _ hyx] at this
    · intro y
      rw [hpt y]
      by_cases hyx : y = x
      · subst hyx; simp
      · by_cases hy : y ∈ xs <;> simp [hy, hyx, upd_ne _ _ hyx]

lemma removeAll_spec : ∀ (xs : List Selector) (ρ ρ' : Routing), removeAll ρ xs = some ρ' →
    xs.Nodup ∧ (∀ x ∈ xs, ρ x ≠ none) ∧ ∀ y, ρ' y = if y ∈ xs then none else ρ y
  | [], ρ, ρ', h => by simp [removeAll] at h; subst h; simp
  | x :: xs, ρ, ρ', h => by
    simp only [removeAll, removeSel] at h
    by_cases hx : ρ x = none
    · simp [hx] at h
    simp only [hx, ite_false, Option.bind_some] at h
    obtain ⟨hnd, hrt, hpt⟩ := removeAll_spec xs _ _ h
    refine ⟨List.nodup_cons.mpr ⟨fun hmem => ?_, hnd⟩, ?_, ?_⟩
    · have := hrt x hmem
      simp at this
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · have := hrt y hy
        by_cases hyx : y = x
        · subst hyx; exact hx
        · rwa [upd_ne _ _ hyx] at this
    · intro y
      rw [hpt y]
      by_cases hyx : y = x
      · subst hyx; simp
      · by_cases hy : y ∈ xs <;> simp [hy, hyx, upd_ne _ _ hyx]

theorem FacetCutGuards : Properties.FacetCutGuards := by
  intro ds d c h
  unfold facetCut at h
  split_ifs at h with hne
  refine ⟨hne, fun ha => ?_, fun ha => ?_, fun ha => ?_⟩
  · rw [ha] at h
    simp only at h
    have hf : c.facet ≠ 0 := by
      intro h0; unfold addFunctions at h; simp [h0] at h
    obtain ⟨hnd, hfree, hpt⟩ := addAll_map_spec _ _ _ _ (addFunctions_routing h)
    exact ⟨hf, hnd, hfree, hpt⟩
  · rw [ha] at h
    simp only at h
    exact replaceFunctions_routing h
  · rw [ha] at h
    simp only at h
    have hf : c.facet = 0 := by
      by_contra h0; unfold removeFunctions at h; simp [h0] at h
    obtain ⟨hnd, hrt, hpt⟩ := removeAll_spec _ _ _ (removeFunctions_routing h)
    exact ⟨hf, hnd, hrt, hpt⟩

theorem DiamondCutKeepsFreezeUniform : Properties.DiamondCutKeepsFreezeUniform :=
  fun ds d cuts hI hU h => (diamondCut_inv cuts ds d hI hU h).2

/-- The same-facet replacement witness: facet `11` with selector `1`, not freezable. -/
def wR₀ : DiamondStorage :=
  (facetCut DiamondStorage.fresh ⟨11, .add, false, [1]⟩).getD DiamondStorage.fresh

/-- After replacing `1` by facet `11`, freezable. -/
def wR₁ : DiamondStorage := (facetCut wR₀ ⟨11, .replace, true, [1]⟩).getD wR₀

/-- After doing it again. -/
def wR₂ : DiamondStorage := (facetCut wR₁ ⟨11, .replace, true, [1]⟩).getD wR₁

theorem ReplaceWithSameFacetAccepted : Properties.ReplaceWithSameFacetAccepted := by
  have h₀ : facetCut DiamondStorage.fresh ⟨11, .add, false, [1]⟩ = some wR₀ := rfl
  have h₁ : facetCut wR₀ ⟨11, .replace, true, [1]⟩ = some wR₁ := rfl
  have h₂ : facetCut wR₁ ⟨11, .replace, true, [1]⟩ = some wR₂ := rfl
  have hI₂ := facetCut_ok (facetCut_ok (facetCut_ok fresh_ok h₀) h₁) h₂
  refine ⟨_, _, _, h₀, h₁, rfl, rfl, h₂, ?_, hI₂⟩
  funext y
  have hr : replaceFunctions wR₁ 11 [1] true = some wR₂ := h₂
  rw [(replaceFunctions_routing hr).2.2 y]
  by_cases hy : y = 1
  · subst hy; rfl
  · simp [hy]

/-! ## The init call -/

theorem InitReturnChecked : Properties.InitReturnChecked :=
  fun _ _ _ _ h => cutFull_spec h

theorem ReturnDataCheckLoadBearing : Properties.ReturnDataCheckLoadBearing := by
  intro s init cd h0
  refine ⟨?_, ?_, fun data hl hne => ?_⟩
  · simp [initializeDiamondCut, h0, codelessInit, diamondCut]
  · simp [initializeNoReturnCheck, h0, codelessInit, diamondCut]
  · unfold initializeDiamondCut
    simp only [h0, ite_false, diamondCut, Option.bind_some, hl, ne_eq, not_true_eq_false]
    have hd : decodeBytes32 data ≠ MAGIC := fun hd => hne (decode_eq_magic hl hd)
    simp [hd]

/-! ## Countermodels and witnesses -/

theorem FreezabilityCheckLoadBearing : Properties.FreezabilityCheckLoadBearing := by
  refine ⟨_, _, rfl, rfl, rfl, ?_, by decide, by decide, by decide, by decide⟩
  intro hU
  exact absurd (hU 1 2 11 false true (by decide) (by decide)) (by decide)

theorem FacetExistsCheckLoadBearing : Properties.FacetExistsCheckLoadBearing := by
  refine ⟨_, _, rfl, rfl, rfl, by decide, by decide, ?_⟩
  intro hI
  have := (hI.selsBack 11 0 1 (by decide)).1
  exact absurd this (by decide)

/-- The witness proxy's routing storage after construction (`wInit adminFreezable`). -/
def wD₀ (adminFreezable : Bool) : DiamondStorage :=
  (diamondCut DiamondStorage.fresh (wInit adminFreezable).nested).getD DiamondStorage.fresh

/-- The witness proxy's routing storage after the cut made while frozen. -/
def wD₂ : DiamondStorage := (diamondCut (wD₀ false) wFrozenCut.facetCuts).getD (wD₀ false)

theorem ProxyRunWitness : Properties.ProxyRunWitness := by
  have h1 : Step wEnv 99 ⟨wD₀ false, false⟩ ⟨wD₀ false, true⟩ :=
    Step.freeze (cd := ⟨4, 2⟩) (f := 21) rfl rfl rfl rfl
  have h2 : Step wEnv 99 ⟨wD₀ false, true⟩ ⟨wD₂, true⟩ :=
    Step.cut (cd := ⟨4, 1⟩) (f := 21) wFrozenCut ⟨[], .reverted []⟩ rfl rfl rfl
  have h3 : Step wEnv 99 ⟨wD₂, true⟩ ⟨wD₂, false⟩ :=
    Step.unfreeze (cd := ⟨4, 3⟩) (f := 21) rfl rfl rfl rfl
  have hR : Reach wEnv ⟨wD₂, false⟩ :=
    ⟨1, wCtorCut, wInit false, _, [99, 99, 99], rfl, Run.cons h1 (Run.cons h2 (Run.cons h3 (Run.nil _)))⟩
  exact ⟨_, _, _, _, rfl, h1, h2, h3, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hR,
    rfl, rfl⟩

theorem FreezePermanentWitness : Properties.FreezePermanentWitness := by
  have h1 : Step wEnv 99 ⟨wD₀ true, false⟩ ⟨wD₀ true, true⟩ :=
    Step.freeze (cd := ⟨4, 2⟩) (f := 21) rfl rfl rfl rfl
  have hR : Reach wEnv ⟨wD₀ true, true⟩ :=
    ⟨1, wCtorCut, wInit true, _, [99], rfl, Run.cons h1 (Run.nil _)⟩
  refine ⟨_, _, rfl, h1, rfl, hR, fun cs s' hr =>
    FreezableEntrypointsMakeFreezePermanent wEnv cs _ s' rfl ?_ hr⟩
  intro x f b hx hfn
  have hf : (f = 21 ∧ x = 1) ∨ (f = 21 ∧ x = 3) := by
    simp only [wEnv] at hfn
    split_ifs at hfn with ha hb hc <;> simp_all
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have : (wD₀ true).routing 1 = some (21, true) := rfl
    rw [this] at hx
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    exact hx.2.symm
  · have : (wD₀ true).routing 3 = some (21, true) := rfl
    rw [this] at hx
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    exact hx.2.symm

/-! ## `Add` is enabled exactly under its guards -/

/-- The shape `_addOneFunction`'s check accepts: the facet has no selector yet, or its first
selector has the new freezability. -/
def FirstSelOk (d : DiamondStorage) (f : Address) (b : Bool) : Prop :=
  (d.facetToSelectors f).selectors = [] ∨
    ∃ y₀ rest, (d.facetToSelectors f).selectors = y₀ :: rest ∧ (d.selectorToFacet y₀).isFreezable = b

lemma addOne_some {d : DiamondStorage} {f : Address} {x : Selector} {b : Bool}
    (hP : FirstSelOk d f b) :
    addOneFunction d f x b = some { d with
      selectorToFacet := upd d.selectorToFacet x ⟨f, (d.facetToSelectors f).selectors.length, b⟩,
      facetToSelectors := upd d.facetToSelectors f
        { d.facetToSelectors f with selectors := (d.facetToSelectors f).selectors ++ [x] } } := by
  unfold addOneFunction
  rcases hP with h | ⟨y₀, rest, h, hb⟩
  · simp [h]
  · simp [h, hb]

lemma addLoop_succeeds {f : Address} {b : Bool} : ∀ (xs : List Selector) (d : DiamondStorage),
    xs.Nodup → (∀ x ∈ xs, (d.selectorToFacet x).facetAddress = 0) → FirstSelOk d f b →
    ∃ d', addLoop d f xs b = some d' := by
  intro xs
  induction xs with
  | nil => intro d _ _ _; exact ⟨d, rfl⟩
  | cons x xs ih =>
    intro d hnd hfree hP
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [addLoop, hfree x List.mem_cons_self, ne_eq, not_true_eq_false, ite_false,
      addOne_some hP, Option.bind_some]
    apply ih _ hnd'
    · intro y hy
      have hyx : y ≠ x := fun h => hx (h ▸ hy)
      simp only [upd_ne _ _ hyx]
      exact hfree y (List.mem_cons_of_mem _ hy)
    · right
      rcases hP with h | ⟨y₀, rest, h, hb⟩
      · refine ⟨x, [], by simp [h], by simp⟩
      · refine ⟨y₀, rest ++ [x], by simp [h], ?_⟩
        by_cases hyx : y₀ = x
        · subst hyx; simp
        · simp only [upd_ne _ _ hyx]; exact hb

theorem AddEnabledIff : Properties.AddEnabledIff := by
  intro ds f b xs hI hU
  constructor
  · rintro ⟨d, h⟩
    obtain ⟨hne, hadd, -, -⟩ := FacetCutGuards ds d _ h
    obtain ⟨hf, hnd, hfree, -⟩ := hadd rfl
    refine ⟨hne, hf, hnd, hfree, ?_⟩
    obtain ⟨x, xs', rfl⟩ := List.exists_cons_of_ne_nil hne
    have h' : addFunctions ds f (x :: xs') b = some d := by
      simpa [facetCut] using h
    unfold addFunctions at h'
    simp only [hf, ite_false, addLoop, saveFacetIfNew_s2f] at h'
    split_ifs at h' with hx
    cases h1 : addOneFunction (saveFacetIfNew ds f) f x b with
    | none => rw [h1] at h'; simp at h'
    | some d1 => exact addOne_save_key hI hU h1
  · rintro ⟨hne, hf, hnd, hfree, hfrz⟩
    have hP : FirstSelOk (saveFacetIfNew ds f) f b := by
      unfold FirstSelOk
      rw [saveFacetIfNew_sels, saveFacetIfNew_s2f]
      cases hs : (ds.facetToSelectors f).selectors with
      | nil => exact Or.inl rfl
      | cons y₀ rest => exact Or.inr ⟨y₀, rest, rfl, hfrz _ _ (first_sel_routes hI hs)⟩
    have hfree' : ∀ x ∈ xs, ((saveFacetIfNew ds f).selectorToFacet x).facetAddress = 0 := by
      intro x hx
      rw [saveFacetIfNew_s2f]
      exact routing_eq_none.mp (hfree x hx)
    obtain ⟨d', h⟩ := addLoop_succeeds xs _ hnd hfree' hP
    refine ⟨d', ?_⟩
    simp [facetCut, hne, addFunctions, hf, h]

theorem ChainAdminCannotFreeze : Properties.ChainAdminCannotFreeze := by
  intro E a ha s s' hs
  by_contra hne
  exact ha (OnlyCtmTogglesFreeze E a s s' hs hne).1

theorem ConstructedProxyIsUnfrozen : Properties.ConstructedProxyIsUnfrozen := by
  intro cid bcid cut r s h
  unfold construct at h
  split_ifs at h with hc
  exact ⟨not_not.mp hc, (cutFull_spec h).1⟩

end Contracts.Diamond
