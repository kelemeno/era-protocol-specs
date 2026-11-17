import EraSpec.Contracts.InteropCenter.Properties.SendAtHead
import EraSpec.Contracts.InteropCenter.Proofs.Dispatch
import EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryLimits

/-!
# Proofs: the head send path

Three facts carry everything. `parseAtomicSend` is atomic exactly on lists carrying `atomicBundle`
and is the zero struct otherwise (`parseAtomicSend_isAtomic_iff`, `parseAtomicSend_of_not_has`); a
non-atomic send cannot take the L2 branch, because the zero struct's flow has no leg
(`nonatomic_toL1`); and the gate plus `_ensureL2ToL2` then pin every `sendMessage` to the atomic L2
branch. Two run invariants, `Inv` (each field under the check it needs) and `LegInv` (no check),
carry the restated pin results; the proofs follow `Proofs/Dispatch.lean`, with the head's bundle
hash `keccak(abi.encode(bundle))` and the head's `CallsChecked` in place of `Validated`.
-/

namespace Contracts.InteropCenter.SendAtHead

open AttackVectors.BundleHashEncoding
open Contracts.AtomicFlowManager (Manager LegState AuthorizeGuard ClaimGuard)

/-! ## The attribute parser -/

theorem not_mem_atomicBundle_cons {a : Attribute} (ha : a.isAtomicBundle = false)
    (rest : List Attribute) :
    HasAtomicBundle (a :: rest) ↔ HasAtomicBundle rest := by
  constructor
  · rintro ⟨pre, lni, h⟩
    rcases List.mem_cons.mp h with h | h
    · subst h; simp [Attribute.isAtomicBundle] at ha
    · exact ⟨pre, lni, h⟩
  · rintro ⟨pre, lni, h⟩
    exact ⟨pre, lni, List.mem_cons_of_mem _ h⟩

theorem parseAtomicSend_cons_of_not {a : Attribute} (ha : a.isAtomicBundle = false)
    (rest : List Attribute) : parseAtomicSend (a :: rest) = parseAtomicSend rest := by
  cases a <;> simp_all [parseAtomicSend, Attribute.isAtomicBundle]

theorem parseAtomicSend_isAtomic_iff (attrs : List Attribute) :
    (parseAtomicSend attrs).isAtomic = true ↔ HasAtomicBundle attrs := by
  induction attrs with
  | nil =>
    simp only [parseAtomicSend, AtomicSend.empty, Bool.false_eq_true, false_iff]
    rintro ⟨_, _, h⟩; simp at h
  | cons a rest ih =>
    by_cases ha : a.isAtomicBundle = true
    · cases a <;> simp [Attribute.isAtomicBundle] at ha
      simp only [parseAtomicSend, true_iff]
      exact ⟨_, _, List.mem_cons_self⟩
    · simp only [Bool.not_eq_true] at ha
      rw [parseAtomicSend_cons_of_not ha, not_mem_atomicBundle_cons ha, ih]

theorem parseAtomicSend_of_has (attrs : List Attribute) (h : HasAtomicBundle attrs) :
    ∃ pre lni, Attribute.atomicBundle pre lni ∈ attrs ∧
      parseAtomicSend attrs = ⟨pre, lni, true⟩ := by
  induction attrs with
  | nil => obtain ⟨_, _, h⟩ := h; simp at h
  | cons a rest ih =>
    by_cases ha : a.isAtomicBundle = true
    · cases a <;> simp [Attribute.isAtomicBundle] at ha
      exact ⟨_, _, List.mem_cons_self, rfl⟩
    · simp only [Bool.not_eq_true] at ha
      obtain ⟨pre, lni, hm, he⟩ := ih ((not_mem_atomicBundle_cons ha rest).mp h)
      exact ⟨pre, lni, List.mem_cons_of_mem _ hm, by rw [parseAtomicSend_cons_of_not ha, he]⟩

theorem parseAtomicSend_of_not_has (attrs : List Attribute) (h : ¬ HasAtomicBundle attrs) :
    parseAtomicSend attrs = AtomicSend.empty := by
  induction attrs with
  | nil => rfl
  | cons a rest ih =>
    by_cases ha : a.isAtomicBundle = true
    · cases a <;> simp [Attribute.isAtomicBundle] at ha
      exact absurd ⟨_, _, List.mem_cons_self⟩ h
    · simp only [Bool.not_eq_true] at ha
      rw [parseAtomicSend_cons_of_not ha]
      exact ih (fun h' => h ((not_mem_atomicBundle_cons ha rest).mpr h'))

theorem parseAtomicSend_empty_of_not_atomic (attrs : List Attribute)
    (h : (parseAtomicSend attrs).isAtomic = false) : parseAtomicSend attrs = AtomicSend.empty := by
  apply parseAtomicSend_of_not_has
  intro hh
  rw [(parseAtomicSend_isAtomic_iff attrs).mpr hh] at h
  exact Bool.noConfusion h

theorem ParseAtomicSendIsTheAttribute : Properties.ParseAtomicSendIsTheAttribute := fun attrs =>
  ⟨parseAtomicSend_isAtomic_iff attrs, parseAtomicSend_of_has attrs,
    parseAtomicSend_of_not_has attrs⟩

/-- Every attribute of an accepted list is a supported one that the restriction allows. -/
theorem parseFrom_allowed {r : Restriction} :
    ∀ (attrs : List Attribute) (used : List ℕ) (x : CallAttributes × BundleAttributes)
      (y : CallAttributes × BundleAttributes), parseFrom r used x attrs = some y →
      ∀ a ∈ attrs, ∃ i, a.index = some i ∧ allowedUnder i r = true := by
  intro attrs
  induction attrs with
  | nil => intro _ _ _ _ a ha; simp at ha
  | cons a rest ih =>
    intro used x y h b hb
    simp only [parseFrom] at h
    cases hi : a.index with
    | none => rw [hi] at h; exact absurd h (by simp)
    | some i =>
      rw [hi] at h
      simp only at h
      by_cases hu : i ∈ used
      · rw [ite_eq_left hu] at h; exact absurd h (by simp)
      · rw [ite_eq_right hu] at h
        by_cases hal : allowedUnder i r = true
        · rw [ite_eq_left hal] at h
          rcases List.mem_cons.mp hb with rfl | hb
          · exact ⟨i, hi, hal⟩
          · exact ih _ _ _ h b hb
        · rw [ite_eq_right hal] at h; exact absurd h (by simp)

theorem parseAttributes_allowed {attrs : List Attribute} {r : Restriction} {y}
    (h : parseAttributes attrs r = some y) :
    ∀ a ∈ attrs, ∃ i, a.index = some i ∧ allowedUnder i r = true :=
  parseFrom_allowed attrs [] _ y h

theorem parseAttributes_none_of_atomic {attrs : List Attribute} {r : Restriction}
    (hr : allowedUnder 5 r = false) (h : HasAtomicBundle attrs) : parseAttributes attrs r = none := by
  cases hp : parseAttributes attrs r with
  | none => rfl
  | some y =>
    obtain ⟨pre, lni, hm⟩ := h
    obtain ⟨i, hi, hal⟩ := parseAttributes_allowed hp _ hm
    simp only [Attribute.index, Option.some.injEq] at hi
    subst hi
    rw [hr] at hal
    exact absurd hal (by simp)

theorem parseAttributes_single_atomic (pre : FlowPreimage) (lni : ℕ) (r : Restriction)
    (hr : allowedUnder 5 r = true) :
    parseAttributes [.atomicBundle pre lni] r = some (noCallAttributes, noBundleAttributes) := by
  simp [parseAttributes, parseFrom, Attribute.index, hr, Attribute.apply]

theorem AtomicBundleIsABundleAttribute : Properties.AtomicBundleIsABundleAttribute := by
  refine ⟨fun attrs h => ⟨parseAttributes_none_of_atomic (by decide) h,
    parseAttributes_none_of_atomic (by decide) h⟩, fun pre lni => ⟨?_, ?_⟩⟩
  · exact parseAttributes_single_atomic pre lni _ (by decide)
  · exact parseAttributes_single_atomic pre lni _ (by decide)

theorem MaskTableIsPinTable : Properties.MaskTableIsPinTable := by
  intro i hi r
  interval_cases i <;> cases r <;> rfl

/-! ## One step that logs a dispatch is that dispatch's send -/

theorem step_logs {K : Checks} {P : Params} {S S' : State} {d : Dispatch}
    (hs : Step K P S S') (hlog : S'.log = S.log ++ [d]) :
    S' = S.afterSend P d ∧ SendShape K P d ∧
      (K.saltCheck = true → S.saltUsed d.sender d.salt = false) ∧
      (d.appends P →
        S.manager.legState (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle) = .Unset) := by
  cases hs with
  | send d' hshape hsalt hfresh =>
    have hdd : d' = d := by simpa [State.afterSend] using hlog
    subst hdd
    exact ⟨rfl, hshape, hsalt, hfresh⟩
  | authorize =>
    have := congrArg List.length hlog
    simp at this
  | claim =>
    have := congrArg List.length hlog
    simp at this
  | foreignAppend =>
    have := congrArg List.length hlog
    simp at this

/-! ## What a send's shape gives -/

theorem atomicSend_eq_parse {K : Checks} {P : Params} {d : Dispatch}
    (hK : K.sendMessageParsesAtomic = true) (hshape : SendShape K P d) :
    d.atomicSend = parseAtomicSend d.attrs := by
  cases he : d.entry
  · have h := (hshape.message he).atomic
    rw [hK, ite_eq_left rfl] at h
    exact h
  · exact (hshape.bundleEntry he).atomic

/-- A non-atomic send has the zero `AtomicSend`, whatever the checks. -/
theorem nonatomic_empty {K : Checks} {P : Params} {d : Dispatch} (hshape : SendShape K P d)
    (h : d.atomicSend.isAtomic = false) : d.atomicSend = AtomicSend.empty := by
  cases he : d.entry
  · have ha := (hshape.message he).atomic
    by_cases hK : K.sendMessageParsesAtomic = true
    · rw [hK, ite_eq_left rfl] at ha
      rw [ha] at h ⊢
      exact parseAtomicSend_empty_of_not_atomic _ h
    · rw [ite_eq_right hK] at ha
      exact ha
  · have ha := (hshape.bundleEntry he).atomic
    rw [ha] at h ⊢
    exact parseAtomicSend_empty_of_not_atomic _ h

/-- A non-atomic send goes to L1, whatever the checks: the zero flow has no leg. -/
theorem nonatomic_toL1 {K : Checks} {P : Params} {d : Dispatch} (hshape : SendShape K P d)
    (h : d.atomicSend.isAtomic = false) : d.bundle.destinationChainId = P.l1ChainId := by
  by_contra hne
  have hf := (hshape.flow hne).isLeg
  rw [nonatomic_empty hshape h] at hf
  simp [AtomicSend.empty] at hf

/-- An appended send is atomic, whatever the checks. -/
theorem appends_atomic {K : Checks} {P : Params} {d : Dispatch} (hshape : SendShape K P d)
    (h : d.appends P) : d.atomicSend.isAtomic = true := by
  by_contra hne
  exact h (nonatomic_toL1 hshape (by simpa using hne))

theorem appends_iff_atomic {K : Checks} {P : Params} {d : Dispatch}
    (hK : K.atomicityGate = true) (hshape : SendShape K P d) :
    d.appends P ↔ d.atomicSend.isAtomic = true :=
  ⟨appends_atomic hshape, hshape.atomicNotToL1 hK⟩

theorem atomic_iff_has {K : Checks} {P : Params} {d : Dispatch}
    (hK : K.sendMessageParsesAtomic = true) (hshape : SendShape K P d) :
    d.atomicSend.isAtomic = true ↔ HasAtomicBundle d.attrs := by
  rw [atomicSend_eq_parse hK hshape]
  exact parseAtomicSend_isAtomic_iff _

theorem sendMessage_appends {K : Checks} {P : Params} {d : Dispatch}
    (hK : K.l2ToL2Check = true) (hshape : SendShape K P d) (he : d.entry = .sendMessage) :
    d.appends P :=
  ((hshape.message he).l2ToL2 hK).2.1

/-- `Forall₂` puts every right element next to some left one. -/
theorem forall₂_exists_left {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, _, .nil => fun _ hb => by simp at hb
  | _, _, .cons hab hrest => fun b hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, hr⟩ := forall₂_exists_left hrest b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

/-- The head's call checks follow from the starter checks and `_processCallStarter`. -/
theorem callsChecked {K : Checks} {P : Params} {d : Dispatch}
    (hK : K.indirectRestriction = true) (hshape : SendShape K P d) : CallsChecked P d := by
  have hcalls := hshape.formed.calls
  refine ⟨fun c hc hv => ?_, fun c hc hfrom => ?_⟩
  · obtain ⟨cs, hcs, hf⟩ := forall₂_exists_left hcalls c hc
    cases hind : cs.callAttributes.indirectCall
    · exact (hf.direct hind).2.2
    · have := ((hshape.starterChecks cs hcs).indirect hK hind).2
      rw [hf.value, this] at hv
      exact absurd rfl hv
  · obtain ⟨cs, hcs, hf⟩ := forall₂_exists_left hcalls c hc
    cases hind : cs.callAttributes.indirectCall
    · exact absurd (hf.direct hind).2.2 hfrom
    · have hr := (hshape.starterChecks cs hcs).indirect hK hind
      exact ⟨(hf.indirect hind).trans hr.1, hf.value.trans hr.2⟩

/-! ## The state after a send -/

theorem mem_afterSend {P : Params} {S : State} {d d' : Dispatch} :
    d' ∈ (S.afterSend P d).log ↔ d' ∈ S.log ∨ d' = d := by
  simp [State.afterSend]

theorem afterSend_legState (P : Params) (S : State) (d : Dispatch) (f h : Word) :
    (S.afterSend P d).manager.legState f h =
      if d.appends P ∧ f = flowIdOf P d.atomicSend.flowPreimage ∧ h = bundleHash P d.bundle then
        .Committed
      else S.manager.legState f h := by
  unfold Dispatch.appends
  by_cases hd : d.bundle.destinationChainId = P.l1ChainId
  · simp [State.afterSend, hd]
  · simp only [State.afterSend, hd, ite_false, Contracts.InteropCenter.legState_set, ne_eq,
      not_false_eq_true, true_and]

theorem afterSend_manager_of_appends {P : Params} {S : State} {d : Dispatch} (h : d.appends P) :
    (S.afterSend P d).manager =
      S.manager.set (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle) .Committed := by
  simp [State.afterSend, ite_eq_right h]

theorem afterSend_manager_of_toL1 {P : Params} {S : State} {d : Dispatch}
    (h : d.bundle.destinationChainId = P.l1ChainId) : (S.afterSend P d).manager = S.manager := by
  simp [State.afterSend, h]

theorem afterSend_l1_of_appends {P : Params} {S : State} {d : Dispatch} (h : d.appends P) :
    (S.afterSend P d).l1Messages = S.l1Messages := by
  simp [State.afterSend, ite_eq_right h]

theorem afterSend_l1_of_toL1 {P : Params} {S : State} {d : Dispatch}
    (h : d.bundle.destinationChainId = P.l1ChainId) :
    (S.afterSend P d).l1Messages = S.l1Messages ++ [l1Message P d.bundle] := by
  simp [State.afterSend, h]

/-! ## The run invariant -/

/-- The L1 dispatches of a log, as messages. -/
def publishedOf (P : Params) (log : List Dispatch) : List (List UInt8) :=
  (log.filter fun d => decide (d.bundle.destinationChainId = P.l1ChainId)).map
    fun d => l1Message P d.bundle

/-- What every reachable state satisfies, each field under the check it needs. -/
structure Inv (K : Checks) (P : Params) (S : State) : Prop where
  salt : ∀ a s, S.saltUsed a s = true ↔ ∃ d ∈ S.log, d.sender = a ∧ d.salt = s
  shape : ∀ d ∈ S.log, SendShape K P d
  keys : K.saltCheck = true → (S.log.map Dispatch.key).Nodup
  published : S.l1Messages = publishedOf P S.log
  legs : K.onlyInteropCenter = true → ∀ f h, S.manager.legState f h ≠ .Unset →
    ∃ d ∈ S.log, d.appends P ∧ flowIdOf P d.atomicSend.flowPreimage = f ∧ bundleHash P d.bundle = h

theorem inv_init (K : Checks) (P : Params) : Inv K P init where
  salt := by intro a s; simp [init]
  shape := by simp [init]
  keys := by simp [init]
  published := by simp [init, publishedOf]
  legs := by intro _ f h hne; exact absurd rfl hne

theorem inv_step {K : Checks} {P : Params} {S S' : State} (hs : Step K P S S')
    (hI : Inv K P S) : Inv K P S' := by
  cases hs with
  | send d hshape hsalt hfresh =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a s
      simp only [State.afterSend, markSalt]
      by_cases hk : a = d.sender ∧ s = d.salt
      · rw [ite_eq_left hk]
        simp only [true_iff]
        exact ⟨d, by simp, hk.1.symm, hk.2.symm⟩
      · rw [ite_eq_right hk, hI.salt a s]
        constructor
        · rintro ⟨d', hd', h1, h2⟩; exact ⟨d', by simp [hd'], h1, h2⟩
        · rintro ⟨d', hd', h1, h2⟩
          simp only [List.mem_append, List.mem_singleton] at hd'
          rcases hd' with hd' | rfl
          · exact ⟨d', hd', h1, h2⟩
          · exact absurd ⟨h1.symm, h2.symm⟩ hk
    · intro d' hd'
      rcases mem_afterSend.mp hd' with hd' | rfl
      · exact hI.shape d' hd'
      · exact hshape
    · intro hK
      simp only [State.afterSend, List.map_append, List.map_singleton]
      refine List.Nodup.append (hI.keys hK) (List.nodup_singleton _) ?_
      intro x hx hx'
      simp only [List.mem_singleton] at hx'
      subst hx'
      obtain ⟨d', hd', hkey⟩ := List.mem_map.mp hx
      have hused : S.saltUsed d.sender d.salt = true := by
        rw [hI.salt]
        exact ⟨d', hd', congrArg Prod.fst hkey, congrArg Prod.snd hkey⟩
      rw [hsalt hK] at hused
      exact Bool.false_ne_true hused
    · by_cases hd : d.bundle.destinationChainId = P.l1ChainId
      · rw [afterSend_l1_of_toL1 hd, hI.published]
        simp [publishedOf, State.afterSend, List.filter_append, hd]
      · rw [afterSend_l1_of_appends hd, hI.published]
        simp [publishedOf, State.afterSend, List.filter_append, hd]
    · intro hK f h hne
      rw [afterSend_legState] at hne
      by_cases hc : d.appends P ∧ f = flowIdOf P d.atomicSend.flowPreimage ∧
          h = bundleHash P d.bundle
      · exact ⟨d, by simp [State.afterSend], hc.1, hc.2.1.symm, hc.2.2.symm⟩
      · rw [ite_eq_right hc] at hne
        obtain ⟨d', hd', h1, h2, h3⟩ := hI.legs hK f h hne
        exact ⟨d', by simp [State.afterSend, hd'], h1, h2, h3⟩
  | authorize f h hg =>
    refine ⟨hI.salt, hI.shape, hI.keys, hI.published, ?_⟩
    intro hK f' h' hne
    simp only [Contracts.InteropCenter.legState_set] at hne
    by_cases hfh : f' = f ∧ h' = h
    · obtain ⟨rfl, rfl⟩ := hfh
      refine hI.legs hK f' h' ?_
      rw [hg]; exact LegState.noConfusion
    · rw [ite_eq_right hfh] at hne; exact hI.legs hK f' h' hne
  | claim f h hg =>
    refine ⟨hI.salt, hI.shape, hI.keys, hI.published, ?_⟩
    intro hK f' h' hne
    simp only [Contracts.InteropCenter.legState_set] at hne
    by_cases hfh : f' = f ∧ h' = h
    · obtain ⟨rfl, rfl⟩ := hfh
      refine hI.legs hK f' h' ?_
      rw [hg]; exact LegState.noConfusion
    · rw [ite_eq_right hfh] at hne; exact hI.legs hK f' h' hne
  | foreignAppend caller a h hne hmod _ _ =>
    exact ⟨hI.salt, hI.shape, hI.keys, hI.published, fun hK => absurd (hmod hK) hne⟩

theorem inv_reach {K : Checks} {P : Params} {S : State} (hr : Reach K P init S) : Inv K P S := by
  induction hr with
  | refl => exact inv_init K P
  | tail _ hs ih => exact inv_step hs ih

/-! ### The leg facts that need no check -/

/-- What every reachable state satisfies whichever checks are in place. -/
structure LegInv (P : Params) (S : State) : Prop where
  stay : ∀ d ∈ S.log, d.appends P →
    S.manager.legState (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle) ≠ .Unset
  once : ((S.log.filter fun d => decide (d.appends P)).map (legOf P)).Nodup

/-- No step writes `Unset`. -/
theorem step_keeps_set {K : Checks} {P : Params} {S S' : State} (hs : Step K P S S') (f h : Word)
    (hne : S.manager.legState f h ≠ .Unset) : S'.manager.legState f h ≠ .Unset := by
  cases hs with
  | send d _ _ _ =>
    rw [afterSend_legState]
    split_ifs
    · exact LegState.noConfusion
    · exact hne
  | authorize f' h' _ =>
    simp only [Contracts.InteropCenter.legState_set]
    split_ifs
    · exact LegState.noConfusion
    · exact hne
  | claim f' h' _ =>
    simp only [Contracts.InteropCenter.legState_set]
    split_ifs
    · exact LegState.noConfusion
    · exact hne
  | foreignAppend _ a h' _ _ _ _ =>
    simp only [Contracts.InteropCenter.legState_set]
    split_ifs
    · exact LegState.noConfusion
    · exact hne

theorem legInv_step {K : Checks} {P : Params} {S S' : State} (hs : Step K P S S')
    (hI : LegInv P S) : LegInv P S' := by
  have hstay : ∀ d ∈ S.log, d.appends P →
      S'.manager.legState (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle) ≠ .Unset :=
    fun d hd hat => step_keeps_set hs _ _ (hI.stay d hd hat)
  cases hs with
  | send d hshape hsalt hfresh =>
    refine ⟨?_, ?_⟩
    · intro d' hd' hat
      rcases mem_afterSend.mp hd' with hd' | rfl
      · exact hstay d' hd' hat
      · rw [afterSend_legState, ite_eq_left ⟨hat, rfl, rfl⟩]
        exact LegState.noConfusion
    · by_cases hat : d.appends P
      · have hf : (S.log ++ [d]).filter (fun d => decide (d.appends P)) =
            S.log.filter (fun d => decide (d.appends P)) ++ [d] := by
          simp [List.filter_append, hat]
        show (((S.log ++ [d]).filter fun d => decide (d.appends P)).map (legOf P)).Nodup
        rw [hf, List.map_append, List.map_singleton]
        refine List.Nodup.append hI.once (List.nodup_singleton _) ?_
        intro x hx hx'
        simp only [List.mem_singleton] at hx'
        subst hx'
        obtain ⟨d', hd', hkey⟩ := List.mem_map.mp hx
        obtain ⟨hd'log, hat'⟩ := List.mem_filter.mp hd'
        have hset := hI.stay d' hd'log (of_decide_eq_true hat')
        have hk1 : flowIdOf P d'.atomicSend.flowPreimage = flowIdOf P d.atomicSend.flowPreimage :=
          congrArg Prod.fst hkey
        have hk2 : bundleHash P d'.bundle = bundleHash P d.bundle := congrArg Prod.snd hkey
        rw [hk1, hk2] at hset
        exact hset (hfresh hat)
      · have hf : (S.log ++ [d]).filter (fun d => decide (d.appends P)) =
            S.log.filter (fun d => decide (d.appends P)) := by
          simp [List.filter_append, hat]
        show (((S.log ++ [d]).filter fun d => decide (d.appends P)).map (legOf P)).Nodup
        rw [hf]
        exact hI.once
  | authorize f h _ => exact ⟨hstay, hI.once⟩
  | claim f h _ => exact ⟨hstay, hI.once⟩
  | foreignAppend _ a h _ _ _ _ => exact ⟨hstay, hI.once⟩

theorem legInv_reach {K : Checks} {P : Params} {S : State} (hr : Reach K P init S) :
    LegInv P S := by
  induction hr with
  | refl => exact ⟨by simp [init], by simp [init]⟩
  | tail _ hs ih => exact legInv_step hs ih

/-- `Forall₂` puts every left element next to some right one. -/
theorem forall₂_exists_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, R a b
  | _, _, .nil => fun _ ha => by simp at ha
  | _, _, .cons hab hrest => fun a ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, hr⟩ := forall₂_exists_right hrest a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

/-! ## 2. `sendMessage` is always atomic -/

theorem SendMessageAlwaysAtomic : Properties.SendMessageAlwaysAtomic := by
  intro P S S' d hs hlog he
  obtain ⟨rfl, hshape, -, hfresh⟩ := step_logs hs hlog
  have happ : d.appends P := sendMessage_appends rfl hshape he
  have hatom : d.atomicSend.isAtomic = true := appends_atomic hshape happ
  refine ⟨(atomic_iff_has rfl hshape).mp hatom, atomicSend_eq_parse rfl hshape, hatom, happ,
    hfresh happ, ?_, afterSend_l1_of_appends happ⟩
  rw [afterSend_legState, ite_eq_left ⟨happ, rfl, rfl⟩]

theorem SendMessageWithoutAttributeReverts : Properties.SendMessageWithoutAttributeReverts := by
  intro P S S' d he hno hs hlog
  exact hno (SendMessageAlwaysAtomic P S S' d hs hlog he).1

theorem SendMessagesAreAtomicAlongRuns : Properties.SendMessagesAreAtomicAlongRuns := by
  intro P S hr d hd he
  have hshape := (inv_reach hr).shape d hd
  have happ := sendMessage_appends rfl hshape he
  have hatom := appends_atomic hshape happ
  exact ⟨(atomic_iff_has rfl hshape).mp hatom, hatom, happ, (legInv_reach hr).stay d hd happ⟩

theorem PinConstantMakesSendMessageUnusable : Properties.PinConstantMakesSendMessageUnusable := by
  intro P S S' d hs hlog he
  obtain ⟨-, hshape, -, -⟩ := step_logs hs hlog
  have happ : d.appends P := sendMessage_appends rfl hshape he
  have ha := (hshape.message he).atomic
  have hna : d.atomicSend.isAtomic = false := by rw [ha]; rfl
  exact happ (hshape.nonAtomicToL1 rfl hna)

/-! ## 1. O1-1, pin and head -/

theorem PinSendMessageDroppedAtomicBundle : Properties.PinSendMessageDroppedAtomicBundle := by
  refine ⟨⟨[.atomicBundle ⟨1, 0, 1, [], []⟩ 0], ⟨_, _, List.mem_singleton_self _⟩, ?_⟩, ?_⟩
  · rw [parseAttributes_single_atomic _ _ _ (by decide)]
    exact Option.some_ne_none _
  · intro attrs _ _
    refine ⟨rfl, fun P S d hd => ?_⟩
    simp [Contracts.InteropCenter.State.afterSend, Contracts.InteropCenter.Dispatch.isAtomic, hd,
      pinSendMessageAtomicSend]

theorem PinFindingRejectedAtHead : Properties.PinFindingRejectedAtHead := by
  intro attrs hhas _
  refine ⟨(parseAtomicSend_isAtomic_iff attrs).mpr hhas, fun P S S' d hs hlog he hattrs => ?_⟩
  obtain ⟨-, h2, -, -, -, h6, h7⟩ := SendMessageAlwaysAtomic P S S' d hs hlog he
  exact ⟨hattrs ▸ h2, h6, h7⟩

/-! ## 3. The `atomicBundle` NatSpec -/

theorem AtomicBundleAttributeMeansAppended : Properties.AtomicBundleAttributeMeansAppended := by
  intro P S S' d hs hlog
  obtain ⟨rfl, hshape, -, hfresh⟩ := step_logs hs hlog
  refine ⟨fun hhas => ?_, fun hno => ?_⟩
  · have hatom : d.atomicSend.isAtomic = true := (atomic_iff_has rfl hshape).mpr hhas
    have happ : d.appends P := hshape.atomicNotToL1 rfl hatom
    exact ⟨atomicSend_eq_parse rfl hshape, hatom, happ, hshape.flow happ, hfresh happ,
      afterSend_manager_of_appends happ, afterSend_l1_of_appends happ⟩
  · have hna : d.atomicSend.isAtomic = false := by
      cases h : d.atomicSend.isAtomic
      · rfl
      · exact absurd ((atomic_iff_has rfl hshape).mp h) hno
    have hL1 := nonatomic_toL1 hshape hna
    exact ⟨nonatomic_empty hshape hna, hL1, afterSend_manager_of_toL1 hL1,
      afterSend_l1_of_toL1 hL1⟩

theorem CallLevelAtomicBundleReverts : Properties.CallLevelAtomicBundleReverts := by
  intro K P S S' d hs hlog he l hl hhas
  obtain ⟨-, hshape, -, -⟩ := step_logs hs hlog
  obtain ⟨cs, -, -, ba, hp⟩ := forall₂_exists_right (hshape.bundleEntry he).calls l hl
  rw [parseAttributes_none_of_atomic (by decide) hhas] at hp
  simp at hp

theorem EveryL2SendIsAtomic : Properties.EveryL2SendIsAtomic := by
  intro P S hr d hd
  have hshape := (inv_reach hr).shape d hd
  exact ⟨appends_iff_atomic rfl hshape, atomic_iff_has rfl hshape⟩

theorem NonAtomicL2SendRevertsInAppend : Properties.NonAtomicL2SendRevertsInAppend := by
  intro K P S S' d hs hlog hna
  obtain ⟨-, hshape, -, -⟩ := step_logs hs hlog
  exact nonatomic_toL1 hshape hna

theorem PublishedMessagesAreL1Dispatches : Properties.PublishedMessagesAreL1Dispatches := by
  intro K P S hr
  exact (inv_reach hr).published

theorem PublishedMessagesAreWithdrawals : Properties.PublishedMessagesAreWithdrawals := by
  intro P S hr d hd hL1
  have hshape := (inv_reach hr).shape d hd
  have hentry : d.entry = .sendBundle := by
    cases he : d.entry
    · exact absurd hL1 (sendMessage_appends rfl hshape he)
    · rfl
  have hna : d.atomicSend.isAtomic = false := by
    cases h : d.atomicSend.isAtomic
    · rfl
    · exact absurd hL1 (hshape.atomicNotToL1 rfl h)
  have hno : ¬ HasAtomicBundle d.attrs := fun hh => by
    rw [(atomic_iff_has rfl hshape).mpr hh] at hna
    exact Bool.noConfusion hna
  have hcalls := hshape.formed.calls
  have hlen : d.bundle.calls.length = 1 := by
    rw [← hcalls.length_eq]
    exact (hshape.bundleEntry hentry).toL1Single hL1
  refine ⟨hentry, hno, nonatomic_empty hshape hna, hlen, fun c hc => ?_, ?_⟩
  · obtain ⟨cs, hcs, hf⟩ := forall₂_exists_left hcalls c hc
    obtain ⟨hind, hto, hv⟩ := (hshape.starterChecks cs hcs).toL1 hL1
    exact ⟨(hf.indirect hind).trans hto, hf.value.trans hv⟩
  · unfold totalBurnedCallsValue
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hx
    exact ((hshape.starterChecks cs hcs).toL1 hL1).2.2

/-! ## 4(a). Sender salts -/

theorem SaltFlagRecordsDispatches : Properties.SaltFlagRecordsDispatches := by
  intro K P S hr a s
  exact (inv_reach hr).salt a s

theorem SaltFlagsNeverCleared : Properties.SaltFlagsNeverCleared := by
  intro K P S S' hs a s h
  cases hs with
  | send d _ _ _ =>
    simp only [State.afterSend, markSalt]
    split_ifs
    · rfl
    · exact h
  | authorize => exact h
  | claim => exact h
  | foreignAppend => exact h

theorem UsedSaltHasNoDispatch : Properties.UsedSaltHasNoDispatch := by
  intro P S S' d hused hs hlog
  obtain ⟨-, -, hsalt, -⟩ := step_logs hs hlog
  rw [hsalt rfl] at hused
  exact Bool.false_ne_true hused

theorem EachSaltDispatchesOnce : Properties.EachSaltDispatchesOnce := by
  intro P S hr
  exact (inv_reach hr).keys rfl

/-! ## 4(b). Validation at head -/

theorem CommittedLegsAreCheckedDispatches : Properties.CommittedLegsAreCheckedDispatches := by
  intro P S hr f h hne
  have hI := inv_reach hr
  obtain ⟨d, hd, happ, hf, hh⟩ := hI.legs rfl f h hne
  have hshape := hI.shape d hd
  have hatom := appends_atomic hshape happ
  refine ⟨d, hd, hatom, (atomic_iff_has rfl hshape).mp hatom, happ, hf, hh, ?_,
    hshape.formed.source, callsChecked rfl hshape⟩
  rw [← hh]
  exact hshape.flow happ

theorem OnlyADispatchCommitsALeg : Properties.OnlyADispatchCommitsALeg := by
  intro P S S' hs f h hU hne
  cases hs with
  | send d hshape hsalt hfresh =>
    rw [afterSend_legState] at hne
    by_cases hc : d.appends P ∧ f = flowIdOf P d.atomicSend.flowPreimage ∧
        h = bundleHash P d.bundle
    · exact ⟨d, rfl, appends_atomic hshape hc.1, hc.1, hc.2.1.symm, hc.2.2.symm,
        callsChecked rfl hshape⟩
    · rw [ite_eq_right hc] at hne; exact absurd hU hne
  | authorize f' h' hg =>
    simp only [Contracts.InteropCenter.legState_set] at hne
    by_cases hfh : f = f' ∧ h = h'
    · obtain ⟨rfl, rfl⟩ := hfh
      have hg' : S.manager.legState f h = .Committed := hg
      rw [hU] at hg'; exact absurd hg' LegState.noConfusion
    · rw [ite_eq_right hfh] at hne; exact absurd hU hne
  | claim f' h' hg =>
    simp only [Contracts.InteropCenter.legState_set] at hne
    by_cases hfh : f = f' ∧ h = h'
    · obtain ⟨rfl, rfl⟩ := hfh
      have hg' : S.manager.legState f h = .Revertable := hg
      rw [hU] at hg'; exact absurd hg' LegState.noConfusion
    · rw [ite_eq_right hfh] at hne; exact absurd hU hne
  | foreignAppend caller a h' hne' hmod _ _ => exact absurd (hmod rfl) hne'

theorem BurnedTotalIsCallValues : Properties.BurnedTotalIsCallValues := by
  intro K P S hr d hd
  unfold totalBurnedCallsValue
  rw [Contracts.InteropCenter.map_value_of_forall₂ ((inv_reach hr).shape d hd).formed.calls]

/-- If every value-carrying call is from `a`, not the router, `_recoverBundle`'s base-token branch
refunds the whole call value. -/
theorem refund_sum (P : Params) (a : Address) (ha : a ≠ P.assetRouter) :
    ∀ (calls : List InteropCall), (∀ c ∈ calls, c.value ≠ 0 → c.fromAddr = a) →
      ((calls.filter fun c => decide (c.fromAddr ≠ P.assetRouter) && decide (c.value ≠ 0)).map
        InteropCall.value).sum = (calls.map InteropCall.value).sum
  | [], _ => rfl
  | c :: rest, h => by
    have ih := refund_sum P a ha rest (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    by_cases hv : c.value = 0
    · rw [List.filter_cons_of_neg (by simp [hv]), ih, List.map_cons, List.sum_cons, hv, zero_add]
    · have hfrom : c.fromAddr = a := h c List.mem_cons_self hv
      have hr : c.fromAddr ≠ P.assetRouter := hfrom ▸ ha
      rw [List.filter_cons_of_pos (by simp [hv, hr]), List.map_cons, List.sum_cons, ih,
        List.map_cons, List.sum_cons]

theorem AtomicValueIsRefundedToPayer : Properties.AtomicValueIsRefundedToPayer := by
  intro P S hr d hd hsender
  have hshape := (inv_reach hr).shape d hd
  have hcc := callsChecked rfl hshape
  refine ⟨fun r hr' => ?_, ?_⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr'
    obtain ⟨hcm, hcp⟩ := List.mem_filter.mp hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcp
    exact hcc.valueFromSender c hcm hcp.2
  · rw [BurnedTotalIsCallValues deployed P S hr d hd, baseTokenRefunds, List.map_map]
    exact refund_sum P d.sender hsender d.bundle.calls hcc.valueFromSender

theorem SolePath : Properties.SolePath := by
  rintro P S hr d ⟨hd, -⟩
  exact callsChecked rfl ((inv_reach hr).shape d hd)

theorem ValidationUnbypassableDischarged : Properties.ValidationUnbypassableDischarged := by
  intro P S hr
  refine ⟨SolePath P S hr, fun d h => ?_⟩
  exact AttackVectors.RecoveryLimits.validation_unbypassable (CallsChecked P)
    (fun d => d ∈ S.log ∧ d.appends P) (SolePath P S hr) h

theorem ClaimedBundleIsDispatchedOrCollision :
    Properties.ClaimedBundleIsDispatchedOrCollision := by
  intro P dec S hr hdec f x hne
  have hI := inv_reach hr
  obtain ⟨d, hd, happ, hf, hh⟩ := hI.legs rfl f _ hne
  have hshape := hI.shape d hd
  refine ⟨d, hd, appends_atomic hshape happ, happ, callsChecked rfl hshape, hf, ?_⟩
  by_cases hx : x = P.enc d.bundle
  · left
    exact ⟨hx, by rw [hx, hdec d hd]⟩
  · right
    exact ⟨hx, hh.symm⟩

theorem PresentedBundleIsDispatchedOrClash : Properties.PresentedBundleIsDispatchedOrClash := by
  intro P S hr f b hne
  have hI := inv_reach hr
  obtain ⟨d, hd, happ, hf, hh⟩ := hI.legs rfl f _ hne
  have hshape := hI.shape d hd
  refine ⟨d, hd, appends_atomic hshape happ, happ, callsChecked rfl hshape, hf, ?_⟩
  by_cases hb : b = d.bundle
  · left; exact hb
  · right; exact ⟨hb, hh.symm⟩

theorem AppendedLegsStayCommitted : Properties.AppendedLegsStayCommitted := by
  intro K P S hr
  exact (legInv_reach hr).stay

theorem EachLegAppendedOnce : Properties.EachLegAppendedOnce := by
  intro K P S hr
  exact (legInv_reach hr).once

/-! ## 4(c). Distinct dispatches -/

theorem DistinctDispatchesDistinctBundles : Properties.DistinctDispatchesDistinctBundles := by
  intro P S hr i j hi hj hij
  have hI := inv_reach hr
  have hkeys : (S.log.map Dispatch.key).Nodup := hI.keys rfl
  have hk : S.log[i].key ≠ S.log[j].key := by
    intro heq
    have hi' : i < (S.log.map Dispatch.key).length := by simpa using hi
    have hj' : j < (S.log.map Dispatch.key).length := by simpa using hj
    have heq' : (S.log.map Dispatch.key)[i] = (S.log.map Dispatch.key)[j] := by
      simpa [List.getElem_map] using heq
    exact hij ((List.Nodup.getElem_inj_iff hkeys).mp heq')
  by_cases hb : S.log[i].bundle = S.log[j].bundle
  · right
    have hsalt : S.log[i].salt = S.log[j].salt := by simp [Dispatch.salt, hb]
    have hsender : S.log[i].sender ≠ S.log[j].sender := by
      intro hs; exact hk (by simp [Dispatch.key, hs, hsalt])
    refine ⟨hsalt, hsender, ?_, ?_⟩
    · intro hpre; exact hsender (Contracts.InteropCenter.saltPreimage_inj hpre).1
    · have h1 := (hI.shape _ (List.getElem_mem hi)).formed.salt
      have h2 := (hI.shape _ (List.getElem_mem hj)).formed.salt
      rw [← h1, ← h2, hb]
  · left; exact hb

theorem DistinctDispatchesDistinctBundleHashes :
    Properties.DistinctDispatchesDistinctBundleHashes := by
  intro P S hr henc i j hi hj hij
  rcases DistinctDispatchesDistinctBundles P S hr i j hi hj hij with hb | hc
  · by_cases hh : bundleHash P S.log[i].bundle = bundleHash P S.log[j].bundle
    · right; right
      refine ⟨fun he => hb ?_, hh⟩
      exact henc _ (List.mem_map_of_mem (List.getElem_mem hi)) _
        (List.mem_map_of_mem (List.getElem_mem hj)) he
    · left; exact hh
  · right; left; exact hc

theorem LoggedRunBundleHashesUnique : Properties.LoggedRunBundleHashesUnique := by
  intro P S hr henc hsaltInj hencInj
  rw [List.nodup_iff_injective_get]
  rintro ⟨i, hi⟩ ⟨j, hj⟩ heq
  simp only [List.get_eq_getElem, List.getElem_map] at heq
  simp only [List.length_map] at hi hj
  by_contra hne
  have hij : i ≠ j := fun h => hne (Fin.ext h)
  rcases DistinctDispatchesDistinctBundleHashes P S hr henc i j hi hj hij with
    h | ⟨-, -, hs1, hs2⟩ | ⟨hb1, hb2⟩
  · exact h heq
  · exact hs1 (hsaltInj _ (List.mem_map_of_mem (List.getElem_mem hi)) _
      (List.mem_map_of_mem (List.getElem_mem hj)) hs2)
  · exact hb1 (hencInj _ (List.mem_map_of_mem (List.getElem_mem hi)) _
      (List.mem_map_of_mem (List.getElem_mem hj)) hb2)

theorem AtomicBytesNeverPublished : Properties.AtomicBytesNeverPublished := by
  intro K P S hr henc d hd happ hmem
  rw [(inv_reach hr).published] at hmem
  obtain ⟨d', hd', heq⟩ := List.mem_map.mp hmem
  obtain ⟨hd'log, hL1⟩ := List.mem_filter.mp hd'
  have henc' : P.enc d'.bundle = P.enc d.bundle := by
    simpa [l1Message] using heq
  have hb := henc _ (List.mem_map_of_mem hd'log) _ (List.mem_map_of_mem hd) henc'
  have hL1' : d'.bundle.destinationChainId = P.l1ChainId := of_decide_eq_true hL1
  rw [hb] at hL1'
  exact happ hL1'

/-! ## Witnesses and countermodels -/

/-- On the witness chain a bundle's hash is its user salt. -/
theorem bundleHash_headParams (b : Bundle) : bundleHash headParams b = b.bundleAttributes.salt := by
  show lastWord (toBytesBE 32 b.interopBundleSalt.val ++ toBytesBE 32 b.bundleAttributes.salt.val) = _
  rw [Contracts.InteropCenter.lastWord_append_word, Contracts.InteropCenter.ofNat_val]

/-- On the witness chain a flow id is its deadline. -/
theorem flowIdOf_headParams (pre : FlowPreimage) :
    flowIdOf headParams pre = Fin.ofNat UInt256.size pre.deadline := by
  show lastWord (toBytesBE 32 pre.deadline) = _
  have h := Contracts.InteropCenter.lastWord_append_word [] pre.deadline
  rwa [List.nil_append] at h

theorem headMsg_hash : bundleHash headParams headMsg.bundle = 1 := bundleHash_headParams _
theorem headMsg_flow : flowIdOf headParams headMsg.atomicSend.flowPreimage = 7 :=
  flowIdOf_headParams _
theorem headValueLeg_hash : bundleHash headParams headValueLeg.bundle = 2 := bundleHash_headParams _
theorem headValueLeg_flow : flowIdOf headParams headValueLeg.atomicSend.flowPreimage = 8 :=
  flowIdOf_headParams _

/-- The encoder determines the user salt. -/
theorem saltWordsEncoder_salt {b b' : Bundle} (h : saltWordsEncoder b = saltWordsEncoder b') :
    b.bundleAttributes.salt = b'.bundleAttributes.salt := by
  have h1 := congrArg (List.drop 32) h
  simp only [saltWordsEncoder, List.drop_left' (length_toBytesBE 32 _)] at h1
  have hm := Contracts.InteropCenter.toBytesBE_eq_mod h1
  rw [Contracts.InteropCenter.size_eq, Nat.mod_eq_of_lt b.bundleAttributes.salt.isLt,
    Nat.mod_eq_of_lt b'.bundleAttributes.salt.isLt] at hm
  exact Fin.ext hm

/-- A list whose user salts are distinct is separated by the witness encoder. -/
theorem encInjOn_of_salts {L : List Bundle} (h : (L.map fun b => b.bundleAttributes.salt).Nodup) :
    EncInjOn saltWordsEncoder L := by
  intro b hb b' hb' he
  exact List.inj_on_of_nodup_map h hb hb' (saltWordsEncoder_salt he)

/-- A list whose images are distinct is one on which keccak is injective. -/
theorem keccakInjOn_of_nodup_map {k : List UInt8 → Word} {L : List (List UInt8)}
    (h : (L.map k).Nodup) : KeccakInjOn k L := by
  intro x hx y hy hxy
  exact List.inj_on_of_nodup_map h hx hy hxy

/-- The witness withdrawal is a well-shaped send for any checks. -/
theorem headWithdrawal_shape (K : Checks) : SendShape K headParams headWithdrawal where
  message := fun h => absurd h (by decide)
  bundleEntry := fun _ =>
    { notOnL1 := by decide
      notToSelf := by decide
      toL1Single := fun _ => rfl
      calls := List.Forall₂.cons ⟨by decide, noBundleAttributes, by rfl⟩ List.Forall₂.nil
      bundleAttrs := ⟨noCallAttributes, ⟨[], [], false, 3⟩, by rfl, by rfl⟩
      atomic := rfl }
  atomicNotToL1 := fun _ h => absurd h (by decide)
  nonAtomicToL1 := fun _ _ => rfl
  formed := ⟨rfl, rfl, List.Forall₂.cons (Contracts.InteropCenter.formsCall_indirect 3)
    List.Forall₂.nil⟩
  starterChecks := by
    intro cs hcs
    simp only [headWithdrawal, List.mem_singleton] at hcs
    subst hcs
    exact ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩⟩
  flow := fun h => absurd rfl h

theorem headMsg_shape : SendShape deployed headParams headMsg where
  message := fun _ =>
    { l2ToL2 := fun _ => by decide
      parsed := ⟨5, [], noCallAttributes, ⟨[], [], false, 1⟩, by decide, by rfl, rfl, by rfl⟩
      callAttrs := rfl
      atomic := by rfl }
  bundleEntry := fun h => absurd h (by decide)
  atomicNotToL1 := fun _ _ => by decide
  nonAtomicToL1 := fun _ h => absurd h (by decide)
  formed := ⟨rfl, rfl, List.Forall₂.cons (Contracts.InteropCenter.formsCall_direct 1 0)
    List.Forall₂.nil⟩
  starterChecks := by
    intro cs hcs
    simp only [headMsg, List.mem_singleton] at hcs
    subst hcs
    exact ⟨fun h => absurd h (by decide), fun _ h => absurd h (by decide)⟩
  flow := fun _ => ⟨by rw [headMsg_hash]; decide, by rw [headMsg_hash]; decide⟩

theorem headValueLeg_shape : SendShape deployed headParams headValueLeg where
  message := fun h => absurd h (by decide)
  bundleEntry := fun _ =>
    { notOnL1 := by decide
      notToSelf := by decide
      toL1Single := fun h => absurd h (by decide)
      calls := List.Forall₂.cons ⟨by decide, noBundleAttributes, by rfl⟩ List.Forall₂.nil
      bundleAttrs := ⟨noCallAttributes, ⟨[], [], false, 2⟩, by rfl, by rfl⟩
      atomic := rfl }
  atomicNotToL1 := fun _ _ => by decide
  nonAtomicToL1 := fun _ h => absurd h (by decide)
  formed := ⟨rfl, rfl, List.Forall₂.cons (Contracts.InteropCenter.formsCall_direct 2 9)
    List.Forall₂.nil⟩
  starterChecks := by
    intro cs hcs
    simp only [headValueLeg, List.mem_singleton] at hcs
    subst hcs
    exact ⟨fun h => absurd h (by decide), fun _ h => absurd h (by decide)⟩
  flow := fun _ => ⟨by rw [headValueLeg_hash]; decide, by rw [headValueLeg_hash]; decide⟩

theorem headS1_legState (f h : Word) :
    headS1.manager.legState f h = if f = 7 ∧ h = 1 then .Committed else .Unset := by
  rw [headS1, afterSend_legState, headMsg_flow, headMsg_hash]
  by_cases hc : f = 7 ∧ h = 1
  · rw [ite_eq_left ⟨by decide, hc.1, hc.2⟩, ite_eq_left hc]
  · rw [ite_eq_right (fun h' => hc ⟨h'.2.1, h'.2.2⟩), ite_eq_right hc]
    rfl

theorem headS3_legState (f h : Word) :
    headS3.manager.legState f h =
      if f = 8 ∧ h = 2 then .Committed else if f = 7 ∧ h = 1 then .Committed else .Unset := by
  rw [headS3, afterSend_manager_of_toL1 rfl, headS2, afterSend_legState, headValueLeg_flow,
    headValueLeg_hash, headS1_legState]
  by_cases hc : f = 8 ∧ h = 2
  · rw [ite_eq_left ⟨by decide, hc.1, hc.2⟩, ite_eq_left hc]
  · rw [ite_eq_right (fun h' => hc ⟨h'.2.1, h'.2.2⟩), ite_eq_right hc]

theorem headStep1 : Step deployed headParams init headS1 :=
  Step.send headMsg headMsg_shape (fun _ => rfl) (fun _ => rfl)

theorem headStep2 : Step deployed headParams headS1 headS2 := by
  refine Step.send headValueLeg headValueLeg_shape (fun _ => by rfl) (fun _ => ?_)
  rw [headValueLeg_flow, headValueLeg_hash, headS1_legState]
  rfl

theorem headStep3 (K : Checks) (hK : K.saltCheck = true → headS2.saltUsed 3 3 = false) :
    Step K headParams headS2 headS3 :=
  Step.send headWithdrawal (headWithdrawal_shape K) hK (fun h => absurd rfl h)

theorem headStep4 : Step deployed headParams headS3 headS4 := by
  refine Step.authorize 7 1 ?_
  show headS3.manager.legState 7 1 = .Committed
  rw [headS3_legState]
  rfl

theorem headReach : Reach deployed headParams init headS4 :=
  .tail (.tail (.tail (.tail .refl headStep1) headStep2) (headStep3 _ (fun _ => by rfl))) headStep4

theorem headS4_legState (f h : Word) :
    headS4.manager.legState f h =
      if f = 7 ∧ h = 1 then .Revertable else headS3.manager.legState f h := by
  simp [headS4]

theorem headS4_log : headS4.log = [headMsg, headValueLeg, headWithdrawal] := rfl

theorem not_has_salt_only (s : Word) : ¬ HasAtomicBundle [Attribute.interopBundleSalt s] := by
  rintro ⟨_, _, h⟩
  simp at h

theorem SendAtHeadWitness : Properties.SendAtHeadWitness := by
  have h12 : (1 : Word) ≠ 2 := by decide
  refine ⟨headReach, headS4_log, ?_, ?_, ?_, rfl, ⟨_, _, List.mem_cons_self⟩, ?_, rfl, ?_, ?_,
    by decide, not_has_salt_only 3, rfl, ?_, ?_⟩
  · rw [headS4_log]
    exact encInjOn_of_salts (by decide)
  · rw [headS4_log]
    apply keccakInjOn_of_nodup_map
    simp only [saltPreimages, List.map_cons, List.map_nil]
    show [lastWord (saltPreimage 1 1), lastWord (saltPreimage 2 2), lastWord (saltPreimage 3 3)].Nodup
    rw [Contracts.InteropCenter.lastWord_saltPreimage, Contracts.InteropCenter.lastWord_saltPreimage,
      Contracts.InteropCenter.lastWord_saltPreimage]
    decide
  · rw [headS4_log]
    apply keccakInjOn_of_nodup_map
    simp only [bundleEncodings, List.map_cons, List.map_nil]
    show [bundleHash headParams headMsg.bundle, bundleHash headParams headValueLeg.bundle,
      bundleHash headParams headWithdrawal.bundle].Nodup
    rw [bundleHash_headParams, bundleHash_headParams, bundleHash_headParams]
    decide
  · rw [headMsg_flow, headMsg_hash, headS4_legState]
    rfl
  · intro h
    exact absurd (h _ (List.mem_singleton_self _)) (by decide)
  · rw [headValueLeg_flow, headValueLeg_hash, headS4_legState, headS3_legState]
    rfl
  · rintro ⟨-, hk⟩
    have hk' : lastWord (saltPreimage 1 1) = lastWord (saltPreimage 2 2) := hk
    rw [Contracts.InteropCenter.lastWord_saltPreimage,
      Contracts.InteropCenter.lastWord_saltPreimage] at hk'
    exact h12 hk'
  · rintro ⟨-, hk⟩
    have hk' : bundleHash headParams headMsg.bundle = bundleHash headParams headValueLeg.bundle := hk
    rw [headMsg_hash, headValueLeg_hash] at hk'
    exact h12 hk'

theorem SendAtHeadStepWitness : Properties.SendAtHeadStepWitness := by
  refine ⟨headStep1, rfl, rfl, ⟨_, _, List.mem_cons_self⟩, ?_, rfl, ?_, by rfl, headStep2,
    headStep3 _ (fun _ => by rfl), rfl, rfl, not_has_salt_only 3, rfl,
    headStep3 _ (fun _ => by rfl), ⟨{ headMsg with attrs := [] }, rfl, ?_⟩⟩
  · show parseAttributes headMsgAttrs .callAndBundleAttributes ≠ none
    rw [show parseAttributes headMsgAttrs .callAndBundleAttributes
      = some (noCallAttributes, ⟨[], [], false, 1⟩) by rfl]
    exact Option.some_ne_none _
  · rw [headS1_legState]
    exact LegState.noConfusion
  · rintro ⟨_, _, h⟩
    simp at h

theorem headEnc_ne_12 : saltWordsEncoder headMsg.bundle ≠ saltWordsEncoder headValueLeg.bundle :=
  fun h => absurd (saltWordsEncoder_salt h) (by decide)

theorem headEnc_ne_13 : saltWordsEncoder headMsg.bundle ≠ saltWordsEncoder headWithdrawal.bundle :=
  fun h => absurd (saltWordsEncoder_salt h) (by decide)

theorem headEnc_ne_32 :
    saltWordsEncoder headWithdrawal.bundle ≠ saltWordsEncoder headValueLeg.bundle :=
  fun h => absurd (saltWordsEncoder_salt h) (by decide)

theorem headDec_msg : headDec (headParams.enc headMsg.bundle) = headMsg.bundle := by
  show (if saltWordsEncoder headMsg.bundle = saltWordsEncoder headValueLeg.bundle then _
    else if saltWordsEncoder headMsg.bundle = saltWordsEncoder headWithdrawal.bundle then _
    else headMsg.bundle) = headMsg.bundle
  rw [ite_eq_right headEnc_ne_12, ite_eq_right headEnc_ne_13]

theorem SendAtHeadClaimWitness : Properties.SendAtHeadClaimWitness := by
  refine ⟨?_, ?_, headDec_msg⟩
  · intro d hd
    rw [headS4_log] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact headDec_msg
    · show (if saltWordsEncoder headValueLeg.bundle = saltWordsEncoder headValueLeg.bundle then
        headValueLeg.bundle else _) = headValueLeg.bundle
      rw [ite_eq_left rfl]
    · show (if saltWordsEncoder headWithdrawal.bundle = saltWordsEncoder headValueLeg.bundle then _
        else if saltWordsEncoder headWithdrawal.bundle = saltWordsEncoder headWithdrawal.bundle then
          headWithdrawal.bundle else _) = headWithdrawal.bundle
      rw [ite_eq_right headEnc_ne_32, ite_eq_left rfl]
  · show headS4.manager.legState 7 (bundleHash headParams headMsg.bundle) = .Revertable
    rw [headMsg_hash, headS4_legState]
    rfl

theorem ValueLegCommitsAtHead : Properties.ValueLegCommitsAtHead := by
  obtain ⟨hr, hlog, -, -, -, -, -, -, hat, hnv, hc, -⟩ := SendAtHeadWitness
  exact ⟨headParams, headS4, hr, headValueLeg, by rw [hlog]; simp, hat, hnv, by decide, hc⟩

/-! ### Countermodels to the checks -/

/-- Sender `4`'s `sendMessage` to L1: an indirect zero-value call to the asset router, no
`atomicBundle`. -/
def l1MsgAttrs : List Attribute := [.indirectCall 0, .interopBundleSalt 4]

def l1SendMessage : Dispatch :=
  ⟨.sendMessage, 4, l1MsgAttrs, [l1MsgAttrs], [⟨9, [], ⟨0, 0, true⟩⟩],
    ⟨324, 1, 1, lastWord (saltPreimage 4 4), [⟨5, 9, 0, []⟩], wAttrs 4⟩, AtomicSend.empty⟩

theorem l1SendMessage_shape : SendShape withoutL2ToL2Check headParams l1SendMessage where
  message := fun _ =>
    { l2ToL2 := fun h => absurd h (by decide)
      parsed := ⟨9, [], ⟨0, 0, true⟩, ⟨[], [], false, 4⟩, by decide, by rfl, rfl, by rfl⟩
      callAttrs := rfl
      atomic := by rfl }
  bundleEntry := fun h => absurd h (by decide)
  atomicNotToL1 := fun _ h => absurd h (by decide)
  nonAtomicToL1 := fun _ _ => rfl
  formed := ⟨rfl, rfl, List.Forall₂.cons (Contracts.InteropCenter.formsCall_indirect 4)
    List.Forall₂.nil⟩
  starterChecks := by
    intro cs hcs
    simp only [l1SendMessage, List.mem_singleton] at hcs
    subst hcs
    exact ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩⟩
  flow := fun h => absurd rfl h

theorem WithoutL2ToL2CheckSendMessagePublishes :
    Properties.WithoutL2ToL2CheckSendMessagePublishes := by
  refine ⟨headParams, init.afterSend headParams l1SendMessage,
    .tail .refl (Step.send l1SendMessage l1SendMessage_shape (fun _ => rfl) (fun h => absurd rfl h)),
    l1SendMessage, by simp [State.afterSend], rfl, ?_, rfl, rfl⟩
  rintro ⟨_, _, h⟩
  simp [l1SendMessage, l1MsgAttrs] at h

/-- Sender `5`'s `sendBundle` to L1 carrying `atomicBundle`: one indirect zero-value router call. -/
def gateAttrs : List Attribute := [.atomicBundle (oneLegFlow 9 5) 0, .interopBundleSalt 5]

def atomicToL1 : Dispatch :=
  ⟨.sendBundle, 5, gateAttrs, [[.indirectCall 0]], [⟨9, [], ⟨0, 0, true⟩⟩],
    ⟨324, 1, 1, lastWord (saltPreimage 5 5), [⟨5, 9, 0, []⟩], wAttrs 5⟩, ⟨oneLegFlow 9 5, 0, true⟩⟩

theorem atomicToL1_shape : SendShape withoutAtomicityGate headParams atomicToL1 where
  message := fun h => absurd h (by decide)
  bundleEntry := fun _ =>
    { notOnL1 := by decide
      notToSelf := by decide
      toL1Single := fun _ => rfl
      calls := List.Forall₂.cons ⟨by decide, noBundleAttributes, by rfl⟩ List.Forall₂.nil
      bundleAttrs := ⟨noCallAttributes, ⟨[], [], false, 5⟩, by rfl, by rfl⟩
      atomic := rfl }
  atomicNotToL1 := fun h _ => absurd h (by decide)
  nonAtomicToL1 := fun h _ => absurd h (by decide)
  formed := ⟨rfl, rfl, List.Forall₂.cons (Contracts.InteropCenter.formsCall_indirect 5)
    List.Forall₂.nil⟩
  starterChecks := by
    intro cs hcs
    simp only [atomicToL1, List.mem_singleton] at hcs
    subst hcs
    exact ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩⟩
  flow := fun h => absurd rfl h

theorem WithoutAtomicityGateAttributeBundleIsPublished :
    Properties.WithoutAtomicityGateAttributeBundleIsPublished := by
  refine ⟨headParams, init.afterSend headParams atomicToL1,
    .tail .refl (Step.send atomicToL1 atomicToL1_shape (fun _ => rfl) (fun h => absurd rfl h)),
    atomicToL1, by simp [State.afterSend], ⟨_, _, List.mem_cons_self⟩, rfl, rfl, ?_⟩
  intro f h
  rw [afterSend_manager_of_toL1 rfl]
  rfl

theorem WithoutSaltCheckABundleRepeats : Properties.WithoutSaltCheckABundleRepeats := by
  have s : ∀ S : State, Step withoutSaltCheck headParams S (S.afterSend headParams headWithdrawal) :=
    fun _ => Step.send headWithdrawal (headWithdrawal_shape _) (fun h => absurd h (by decide))
      (fun h => absurd rfl h)
  exact ⟨headParams, (init.afterSend headParams headWithdrawal).afterSend headParams headWithdrawal,
    .tail (.tail .refl (s init)) (s _), 0, 1, by decide, by decide, by decide, rfl, rfl⟩

theorem WithoutOnlyInteropCenterUnbackedLegCommits :
    Properties.WithoutOnlyInteropCenterUnbackedLegCommits := by
  refine ⟨headParams,
    { init with manager := init.manager.set (flowIdOf headParams (oneLegFlow 7 1)) 1 .Committed },
    flowIdOf headParams (oneLegFlow 7 1), 1, ?_, rfl, by simp⟩
  refine .tail .refl (Step.foreignAppend 1 ⟨oneLegFlow 7 1, 0, true⟩ 1 (by decide)
    (fun h => absurd h (by decide)) ⟨by decide, by decide⟩ rfl)

/-- The asset router's own atomic `sendBundle`, with a direct call carrying value `4`. -/
def routerAttrs : List Attribute := [.atomicBundle (oneLegFlow 10 6) 0, .interopBundleSalt 6]

def routerValueLeg : Dispatch :=
  ⟨.sendBundle, 9, routerAttrs, [[.interopCallValue 4]], [⟨5, [], ⟨4, 0, false⟩⟩],
    ⟨324, 325, 1, lastWord (saltPreimage 9 6), [⟨5, 9, 4, []⟩], wAttrs 6⟩,
    ⟨oneLegFlow 10 6, 0, true⟩⟩

theorem routerValueLeg_shape : SendShape deployed headParams routerValueLeg where
  message := fun h => absurd h (by decide)
  bundleEntry := fun _ =>
    { notOnL1 := by decide
      notToSelf := by decide
      toL1Single := fun h => absurd h (by decide)
      calls := List.Forall₂.cons ⟨by decide, noBundleAttributes, by rfl⟩ List.Forall₂.nil
      bundleAttrs := ⟨noCallAttributes, ⟨[], [], false, 6⟩, by rfl, by rfl⟩
      atomic := rfl }
  atomicNotToL1 := fun _ _ => by decide
  nonAtomicToL1 := fun _ h => absurd h (by decide)
  formed := ⟨rfl, rfl, List.Forall₂.cons (Contracts.InteropCenter.formsCall_direct 9 4)
    List.Forall₂.nil⟩
  starterChecks := by
    intro cs hcs
    simp only [routerValueLeg, List.mem_singleton] at hcs
    subst hcs
    exact ⟨fun h => absurd h (by decide), fun _ h => absurd h (by decide)⟩
  flow := fun _ => ⟨by rw [bundleHash_headParams]; decide, by rw [bundleHash_headParams]; decide⟩

theorem RouterSenderValueIsNotRefunded : Properties.RouterSenderValueIsNotRefunded :=
  ⟨headParams, init.afterSend headParams routerValueLeg,
    .tail .refl (Step.send routerValueLeg routerValueLeg_shape (fun _ => rfl) (fun _ => rfl)),
    routerValueLeg, by simp [State.afterSend], rfl, rfl, by decide, by decide⟩

/-- Sender `2`'s atomic `sendBundle` with an indirect call through contract `8` (not the router)
carrying value `5`: allowed only without :658-677. -/
def foreignIndirectAttrs : List Attribute := [.atomicBundle (oneLegFlow 11 7) 0, .interopBundleSalt 7]

def foreignIndirectLeg : Dispatch :=
  ⟨.sendBundle, 2, foreignIndirectAttrs, [[.indirectCall 0, .interopCallValue 5]],
    [⟨8, [], ⟨5, 0, true⟩⟩],
    ⟨324, 325, 1, lastWord (saltPreimage 2 7), [⟨5, 8, 5, []⟩], wAttrs 7⟩,
    ⟨oneLegFlow 11 7, 0, true⟩⟩

theorem foreignIndirectLeg_shape :
    SendShape withoutIndirectRestriction headParams foreignIndirectLeg where
  message := fun h => absurd h (by decide)
  bundleEntry := fun _ =>
    { notOnL1 := by decide
      notToSelf := by decide
      toL1Single := fun h => absurd h (by decide)
      calls := List.Forall₂.cons ⟨by decide, noBundleAttributes, by rfl⟩ List.Forall₂.nil
      bundleAttrs := ⟨noCallAttributes, ⟨[], [], false, 7⟩, by rfl, by rfl⟩
      atomic := rfl }
  atomicNotToL1 := fun _ _ => by decide
  nonAtomicToL1 := fun _ h => absurd h (by decide)
  formed := ⟨rfl, rfl, List.Forall₂.cons
    ⟨rfl, fun _ => rfl, fun h => absurd h (by decide)⟩ List.Forall₂.nil⟩
  starterChecks := by
    intro cs hcs
    simp only [foreignIndirectLeg, List.mem_singleton] at hcs
    subst hcs
    exact ⟨fun h => absurd h (by decide), fun h _ => absurd h (by decide)⟩
  flow := fun _ => ⟨by rw [bundleHash_headParams]; decide, by rw [bundleHash_headParams]; decide⟩

theorem WithoutIndirectRestrictionRefundMissesPayer :
    Properties.WithoutIndirectRestrictionRefundMissesPayer :=
  ⟨headParams, init.afterSend headParams foreignIndirectLeg,
    .tail .refl (Step.send foreignIndirectLeg foreignIndirectLeg_shape (fun _ => rfl)
      (fun _ => rfl)),
    foreignIndirectLeg, by simp [State.afterSend], rfl, by decide, (8, 5), by decide, by decide⟩

/-! ### The collision disjuncts fire -/

/-- The colliding witness chain: as `headParams`, but keccak is constant. -/
def collidingHeadParams : Params :=
  ⟨324, 1, 0x8010, 9, saltWordsEncoder, deadlineEncoder, fun _ => 0, fun _ _ => [1]⟩

/-- Under the constant keccak, a withdrawal with salt `3`, whoever sends it. -/
def sharedWithdrawal : Bundle := ⟨324, 1, 1, 0, [⟨5, 9, 0, []⟩], wAttrs 3⟩

def sharer (a : Address) : Dispatch :=
  ⟨.sendBundle, a, [.interopBundleSalt 3], [[.indirectCall 0]], [⟨9, [], ⟨0, 0, true⟩⟩],
    sharedWithdrawal, AtomicSend.empty⟩

theorem sharer_shape (a : Address) : SendShape deployed collidingHeadParams (sharer a) where
  message := fun h => by cases h
  bundleEntry := fun _ =>
    { notOnL1 := by decide
      notToSelf := show (1 : Word) ≠ 324 by decide
      toL1Single := fun _ => rfl
      calls := List.Forall₂.cons ⟨by decide, noBundleAttributes, by rfl⟩ List.Forall₂.nil
      bundleAttrs := ⟨noCallAttributes, ⟨[], [], false, 3⟩, by rfl, by rfl⟩
      atomic := rfl }
  atomicNotToL1 := fun _ h => by cases h
  nonAtomicToL1 := fun _ _ => rfl
  formed := ⟨rfl, rfl, List.Forall₂.cons (Contracts.InteropCenter.formsCall_indirect a)
    List.Forall₂.nil⟩
  starterChecks := by
    intro cs hcs
    simp only [sharer, List.mem_singleton] at hcs
    subst hcs
    exact ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩⟩
  flow := fun h => absurd rfl h

/-- Both senders have dispatched the shared withdrawal. -/
def sharedState : State :=
  (init.afterSend collidingHeadParams (sharer 1)).afterSend collidingHeadParams (sharer 2)

theorem sharedState_log : sharedState.log = [sharer 1, sharer 2] := rfl

theorem SaltClashLetsTwoSendersShareABundle :
    Properties.SaltClashLetsTwoSendersShareABundle := by
  have s1 : Step deployed collidingHeadParams init (init.afterSend collidingHeadParams (sharer 1)) :=
    Step.send (sharer 1) (sharer_shape 1) (fun _ => rfl) (fun h => absurd rfl h)
  have s2 : Step deployed collidingHeadParams (init.afterSend collidingHeadParams (sharer 1))
      sharedState :=
    Step.send (sharer 2) (sharer_shape 2) (fun _ => by rfl) (fun h => absurd rfl h)
  refine ⟨collidingHeadParams, sharedState, .tail (.tail .refl s1) s2, 0, 1,
    by rw [sharedState_log]; decide, by rw [sharedState_log]; decide, by decide, ?_⟩
  simp only [sharedState_log, List.getElem_cons_zero, List.getElem_cons_succ]
  refine ⟨rfl, rfl, show (1 : Address) ≠ 2 by decide, ?_, rfl⟩
  intro hpre
  exact absurd (Contracts.InteropCenter.saltPreimage_inj hpre).1 (by decide)

/-- Under the constant keccak, an atomic leg whose bundle hash is `0`. -/
def headCollidingLeg : Dispatch :=
  ⟨.sendBundle, 1, [.atomicBundle ⟨1, 0, 1, [0], [324]⟩ 0, .interopBundleSalt 1], [[]],
    [⟨5, [], noCallAttributes⟩], ⟨324, 325, 1, 0, [⟨5, 1, 0, []⟩], wAttrs 1⟩,
    ⟨⟨1, 0, 1, [0], [324]⟩, 0, true⟩⟩

theorem headCollidingLeg_shape : SendShape deployed collidingHeadParams headCollidingLeg where
  message := fun h => absurd h (by decide)
  bundleEntry := fun _ =>
    { notOnL1 := by decide
      notToSelf := by decide
      toL1Single := fun h => absurd h (by decide)
      calls := List.Forall₂.cons ⟨by decide, noBundleAttributes, by rfl⟩ List.Forall₂.nil
      bundleAttrs := ⟨noCallAttributes, ⟨[], [], false, 1⟩, by rfl, by rfl⟩
      atomic := rfl }
  atomicNotToL1 := fun _ _ => by decide
  nonAtomicToL1 := fun _ h => absurd h (by decide)
  formed := ⟨rfl, rfl, List.Forall₂.cons (Contracts.InteropCenter.formsCall_direct 1 0)
    List.Forall₂.nil⟩
  starterChecks := by
    intro cs hcs
    simp only [headCollidingLeg, List.mem_singleton] at hcs
    subst hcs
    exact ⟨fun h => absurd h (by decide), fun _ h => absurd h (by decide)⟩
  flow := fun _ => ⟨by decide, by decide⟩

theorem CollisionLetsForeignBytesMatchACommittedLeg :
    Properties.CollisionLetsForeignBytesMatchACommittedLeg := by
  refine ⟨collidingHeadParams, init.afterSend collidingHeadParams headCollidingLeg, 0, [],
    .tail .refl (Step.send headCollidingLeg headCollidingLeg_shape (fun _ => rfl) (fun _ => rfl)),
    ?_, ?_⟩
  · rw [afterSend_legState, ite_eq_left ⟨by decide, rfl, rfl⟩]
    exact LegState.noConfusion
  · intro d hd h
    have hl := congrArg List.length h
    simp [collidingHeadParams, saltWordsEncoder, length_toBytesBE] at hl

end Contracts.InteropCenter.SendAtHead
