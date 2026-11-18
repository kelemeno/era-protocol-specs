import EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.EngineLegV35
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashPinned
import EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsCurrent

/-!
# Proofs: what a successful engine leg pins, and each check is load-bearing

The general results read the checks off the leg: (a), (c) and the checks before the engine are
fields. (b) is a case split on the hashed preimages. If the before and after preimages differ,
their equal hashes are a collision on those named inputs. If they are equal, the encoding is
injective (`AbiEncodeInjective`, from `word_val_inj` and the fixed 32-byte word length), so
the words are equal; a CTM preimage (six words) never equals a notifier preimage (five). With
a ServerNotifier on both sides the split runs twice, once per level. The CTM-proxy result
combines (b) with the check at `:75-77` and `AdminFallsThrough`.

The witnesses and countermodels run in the concrete world. Two helpers carry them:
`oneRow_delegate` builds a one-row engine's delegatecall when its follow-up calls run from
the state after the row, and `oneRow_delegate_inv` shows that every successful delegatecall
of such an engine has that shape. `DefaultEngineLegIsApplyTransition` rests on
`rowCalls_run` and `rowCalls_run_inv`: with inert reinitializers, the calls the loop sends
reach exactly the implementations `ApplyLoop` computes.
-/

namespace Contracts.EngineLegV35

open Clear
open Contracts.ProxyUpgradeCurrent (Address Row Impl upd RowsApplied toRows Domain)

/-! ## Encoding -/

theorem abiWord_length (w : UInt256) : (abiWord w).length = 32 :=
  AttackVectors.BundleHashEncoding.word_length _

theorem abiWord_inj {x y : UInt256} (h : abiWord x = abiWord y) : x = y :=
  AttackVectors.BundleHashEncoding.word_val_inj h

theorem abiEncode_cons (w : UInt256) (ws : List UInt256) :
    abiEncode (w :: ws) = abiWord w ++ abiEncode ws := by
  simp [abiEncode, List.flatMap_cons]

theorem abiEncode_length (ws : List UInt256) : (abiEncode ws).length = 32 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => rw [abiEncode_cons, List.length_append, abiWord_length, ih]; simp; ring

theorem AbiEncodeInjective : Properties.AbiEncodeInjective := by
  intro ws
  induction ws with
  | nil =>
      intro ws' h
      have := congrArg List.length h
      rw [abiEncode_length, abiEncode_length] at this
      cases ws' with
      | nil => rfl
      | cons _ _ => simp at this
  | cons a as ih =>
      intro ws' h
      cases ws' with
      | nil =>
          have := congrArg List.length h
          rw [abiEncode_length, abiEncode_length] at this
          simp at this
      | cons b bs =>
          rw [abiEncode_cons, abiEncode_cons] at h
          obtain ⟨h1, h2⟩ := List.append_inj h (by rw [abiWord_length, abiWord_length])
          rw [abiWord_inj h1, ih bs h2]

theorem abiEncode_eq_iff {ws ws' : List UInt256} : abiEncode ws = abiEncode ws' ↔ ws = ws' :=
  ⟨AbiEncodeInjective ws ws', fun h => h ▸ rfl⟩

/-! ## The holder preimages -/

variable {σ κ : Type}

theorem ctmPre_eq_iff {E : Env σ κ} {s s' : σ} :
    ctmPre E s = ctmPre E s' ↔ ctmWords E s = ctmWords E s' :=
  abiEncode_eq_iff

theorem notifierPre_eq_iff {E : Env σ κ} {s s' : σ} :
    notifierPre E s = notifierPre E s' ↔
      E.keccak (ctmPre E s) = E.keccak (ctmPre E s') ∧ notifierWords E s = notifierWords E s' := by
  unfold notifierPre
  rw [abiEncode_eq_iff, List.cons.injEq]

/-- A CTM preimage (six words) is never a notifier preimage (five words). -/
theorem ctmPre_ne_notifierPre {E : Env σ κ} {s s' : σ} : ctmPre E s ≠ notifierPre E s' := by
  intro h
  have := congrArg List.length h
  simp [ctmPre, notifierPre, abiEncode_length, ctmWords, notifierWords] at this

/-- What an unchanged holder tuple says, component by component. -/
theorem holderTuple_eq_parts {E : Env σ κ} {s s' : σ}
    (ht : holderTuple E s' = holderTuple E s) :
    E.paOwner s' = E.paOwner s ∧
      (E.chainTypeManager ≠ 0 → ctmWords E s' = ctmWords E s ∧
        (E.serverNotifierAddress s ≠ 0 → notifierWords E s' = notifierWords E s)) := by
  by_cases hc : E.chainTypeManager = 0
  · simp only [holderTuple, ite_eq_left hc, List.cons.injEq] at ht
    exact ⟨ht.1, fun h => absurd hc h⟩
  · have hw : ctmWords E s' = ctmWords E s ∧
        (E.serverNotifierAddress s ≠ 0 → notifierWords E s' = notifierWords E s) := by
      by_cases hn : E.serverNotifierAddress s = 0 <;>
        by_cases hn' : E.serverNotifierAddress s' = 0
      · simp only [holderTuple, ite_eq_right hc, ite_eq_left hn, ite_eq_left hn'] at ht
        exact ⟨ht, fun h => absurd hn h⟩
      · simp only [holderTuple, ite_eq_right hc, ite_eq_left hn, ite_eq_right hn'] at ht
        have := congrArg List.length ht
        simp [ctmWords, notifierWords] at this
      · simp only [holderTuple, ite_eq_right hc, ite_eq_right hn, ite_eq_left hn'] at ht
        have := congrArg List.length ht
        simp [ctmWords, notifierWords] at this
      · simp only [holderTuple, ite_eq_right hc, ite_eq_right hn, ite_eq_right hn'] at ht
        obtain ⟨h1, h2⟩ := List.append_inj ht (by simp [ctmWords])
        exact ⟨h1, fun _ => h2⟩
    refine ⟨?_, fun _ => hw⟩
    have h := hw.1
    simp only [ctmWords, List.cons.injEq] at h
    exact h.1

/-! ## What a successful leg pins -/

theorem leg_engine {E : Env σ κ} {eng : Engine σ κ} {T : Address} {M : Manifest} {d : Domain}
    {st : Store} {s : σ} {st' : Store} {s' : σ} (h : Leg E eng T M d st s st' s') :
    ∃ calls, eng (context E T M d) M.proxyUpgrades st s st' calls ∧ CallRun E s calls s' := by
  rcases h.1.2 with ⟨_, hrun⟩ | ⟨hnc, _, _⟩
  · exact hrun
  · exact absurd (h.2 .engineCode) hnc

theorem LegRunsThePinnedEngine : Properties.LegRunsThePinnedEngine :=
  fun _ _ _ _ _ _ _ _ _ _ _ h =>
    ⟨h.1.1.transitionCode, h.2 .domain, h.2 .engineCode, h.2 .ctmAdmin, leg_engine h⟩

theorem LegKeepsExecutorOwnership : Properties.LegKeepsExecutorOwnership :=
  fun _ _ _ _ _ _ _ _ _ _ _ h => h.2 .ownership

theorem LegChangesOnlyUndeclaredExecutorStorage :
    Properties.LegChangesOnlyUndeclaredExecutorStorage := by
  intro _ _ _ _ _ _ _ st _ st' _ h
  obtain ⟨h1, h2⟩ := h.2 .ownership
  obtain ⟨o, p, x⟩ := st
  obtain ⟨o', p', x'⟩ := st'
  simp only at h1 h2
  subst h1 h2
  rfl

theorem LegKeepsDomainHoldersOrCollides : Properties.LegKeepsDomainHoldersOrCollides := by
  intro _ _ E _ _ _ _ _ s _ s' h
  have hh : E.keccak (holdersPre E s') = E.keccak (holdersPre E s) := h.2 .holders
  by_cases hp : holdersPre E s = holdersPre E s'
  · by_cases hc : E.chainTypeManager = 0
    · left
      simp only [holdersPre, ite_eq_left hc, corePre] at hp
      simp only [holderTuple, ite_eq_left hc]
      exact (abiEncode_eq_iff.mp hp).symm
    · by_cases hn : E.serverNotifierAddress s = 0 <;>
        by_cases hn' : E.serverNotifierAddress s' = 0
      · left
        simp only [holdersPre, ite_eq_right hc, ite_eq_left hn, ite_eq_left hn'] at hp
        simp only [holderTuple, ite_eq_right hc, ite_eq_left hn, ite_eq_left hn']
        exact (ctmPre_eq_iff.mp hp).symm
      · simp only [holdersPre, ite_eq_right hc, ite_eq_left hn, ite_eq_right hn'] at hp
        exact absurd hp ctmPre_ne_notifierPre
      · simp only [holdersPre, ite_eq_right hc, ite_eq_right hn, ite_eq_left hn'] at hp
        exact absurd hp.symm ctmPre_ne_notifierPre
      · simp only [holdersPre, ite_eq_right hc, ite_eq_right hn, ite_eq_right hn'] at hp
        obtain ⟨hk, hw⟩ := notifierPre_eq_iff.mp hp
        by_cases hq : ctmPre E s = ctmPre E s'
        · left
          simp only [holderTuple, ite_eq_right hc, ite_eq_right hn, ite_eq_right hn']
          rw [ctmPre_eq_iff.mp hq, hw]
        · exact Or.inr (Or.inr ⟨hc, hn, hn', hq, hk⟩)
  · exact Or.inr (Or.inl ⟨hp, hh.symm⟩)

theorem LegKeepsNamedHoldersUnlessCollision :
    Properties.LegKeepsNamedHoldersUnlessCollision := by
  intro _ _ E eng T M d st s st' s' h hb
  have ht : holderTuple E s' = holderTuple E s :=
    (LegKeepsDomainHoldersOrCollides _ _ E eng T M d st s st' s' h).resolve_right hb
  obtain ⟨hpa, hrest⟩ := holderTuple_eq_parts ht
  refine ⟨hpa, fun hc => ?_, fun hc hn => ?_⟩
  · have hw := (hrest hc).1
    simp only [ctmWords, List.cons.injEq] at hw
    exact ⟨hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1⟩
  · obtain ⟨hw, hnw⟩ := hrest hc
    have hn' : E.serverNotifierAddress s' = E.serverNotifierAddress s := by
      simp only [ctmWords, List.cons.injEq] at hw
      exact hw.2.2.2.2.2.1
    have h2 := hnw hn
    simp only [notifierWords, hn', List.cons.injEq] at h2
    exact ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1⟩

theorem UnchangedHoldersPassTheCheck : Properties.UnchangedHoldersPassTheCheck := by
  intro _ _ E s s' ht
  refine congrArg E.keccak ?_
  obtain ⟨hpa, hrest⟩ := holderTuple_eq_parts ht
  by_cases hc : E.chainTypeManager = 0
  · simp only [holdersPre, ite_eq_left hc, corePre, hpa]
  · obtain ⟨hw, hnw⟩ := hrest hc
    have hn' : E.serverNotifierAddress s' = E.serverNotifierAddress s := by
      have h := hw
      simp only [ctmWords, List.cons.injEq] at h
      exact h.2.2.2.2.2.1
    by_cases hn : E.serverNotifierAddress s = 0
    · have hn0 : E.serverNotifierAddress s' = 0 := hn'.trans hn
      simp only [holdersPre, ite_eq_right hc, ite_eq_left hn, ite_eq_left hn0, ctmPre, hw]
    · have hn0 : E.serverNotifierAddress s' ≠ 0 := fun h => hn (hn'.symm.trans h)
      simp only [holdersPre, ite_eq_right hc, ite_eq_right hn, ite_eq_right hn0, notifierPre, ctmPre, hw, hnw hn]

theorem LegKeepsCtmProxyAdministeredUnlessCollision :
    Properties.LegKeepsCtmProxyAdministeredUnlessCollision := by
  intro _ _ E eng T M d st s st' s' h hb hc hfall hslot
  obtain ⟨-, hrest, -⟩ := LegKeepsNamedHoldersUnlessCollision _ _ E eng T M d st s st' s' h hb
  obtain ⟨-, -, hadm, hgpa, -⟩ := hrest hc
  have hpre : E.ctmAdmin s ≠ E.proxyAdmin := h.2 .ctmAdmin hc
  have h0 : E.getProxyAdmin s E.chainTypeManager = E.proxyAdmin := by
    rw [hfall s, ite_eq_left hslot]
  refine ⟨?_, by rw [hadm]; exact hpre⟩
  by_contra hne
  have h1 := hfall s'
  rw [ite_eq_right hne, hgpa, h0, hadm] at h1
  exact hpre h1.symm

theorem LegLandsEveryRow : Properties.LegLandsEveryRow :=
  fun _ _ _ _ _ _ _ _ _ _ _ h => ⟨h.1.1.inventoryLength, h.2 .rows⟩

theorem LegLandsEveryActiveSlot : Properties.LegLandsEveryActiveSlot :=
  fun _ _ _ _ _ _ _ _ _ _ _ h r hr hne =>
    h.2 .rows r (ProxyUpgradeCurrent.mem_toRows.mpr ⟨hr, hne⟩)

/-! ## The code check and the domain check -/

theorem CodelessEngineLegIff : Properties.CodelessEngineLegIff := by
  intro _ _ E eng T M d st s st' s' hnc
  refine ⟨⟨?_, ?_⟩, fun h => hnc (h.2 .engineCode)⟩
  · rintro ⟨⟨hpre, hdel⟩, hc⟩
    rcases hdel with ⟨hcode, _⟩ | ⟨_, rfl, rfl⟩
    · exact absurd hcode hnc
    · exact ⟨hpre, hc .domain (by decide), hc .ctmAdmin (by decide), rfl, rfl,
        hc .rows (by decide)⟩
  · rintro ⟨hpre, hdom, hadm, rfl, rfl, hrows⟩
    refine ⟨⟨hpre, Or.inr ⟨hnc, rfl, rfl⟩⟩, ?_⟩
    intro c hc
    cases c with
    | domain => exact hdom
    | engineCode => exact absurd rfl hc
    | ctmAdmin => exact hadm
    | ownership => exact ⟨rfl, rfl⟩
    | holders => rfl
    | rows => exact hrows

theorem CodelessEngineMovesNothing : Properties.CodelessEngineMovesNothing := by
  rintro _ _ E eng T M d st s hnc ⟨r, hr, hne⟩ ⟨st', s', h⟩
  obtain ⟨_, _, _, _, rfl, hrows⟩ :=
    ((CodelessEngineLegIff _ _ E eng T M d st s st' s' hnc).1).1 h
  exact hne (hrows r hr)

theorem DomainCheckRedundantAtConstructorLength :
    Properties.DomainCheckRedundantAtConstructorLength := by
  intro _ _ E eng T M d st s st' s' hlen
  refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, fun c _ => h.2 c⟩⟩
  intro c
  by_cases hc : c = .domain
  · subst hc
    show M.domain = d
    have h2 : M.proxyUpgrades.length = inventoryLength d := h.1.1.inventoryLength
    rw [hlen] at h2
    cases hM : M.domain <;> cases d <;> simp_all [inventoryLength]
  · exact h.2 c hc

/-- A leg with check `c₀` deleted is the leg once `c₀` holds too. -/
theorem leg_of_without {c₀ : Check} {E : Env σ κ} {eng : Engine σ κ} {T : Address}
    {M : Manifest} {d : Domain} {st : Store} {s : σ} {st' : Store} {s' : σ}
    (h : LegWithout c₀ E eng T M d st s st' s') (h0 : Check.Holds E M d st s st' s' c₀) :
    Leg E eng T M d st s st' s' :=
  ⟨h.1, fun c => if hc : c = c₀ then hc ▸ h0 else h.2 c hc⟩

/-- With a CTM and a ServerNotifier, the holders preimage is the notifier preimage. -/
theorem holdersPre_of_notifier {E : Env σ κ} {s : σ} (hc : E.chainTypeManager ≠ 0)
    (hn : E.serverNotifierAddress s ≠ 0) :
    holdersPre E s = abiEncode (E.keccak (ctmPre E s) :: notifierWords E s) := by
  unfold holdersPre
  rw [ite_eq_right hc, ite_eq_right hn]
  rfl

/-! ## The concrete world: rows, calls and the default engine -/

theorem toRows_wInv : toRows wInv = [wRow] := by decide

theorem toRows_wInvEmpty : toRows wInvEmpty = [] := by decide

theorem toRows_wInvCore : toRows wInvCore = [wRow] := by decide

theorem rowCalls_oneRow {I : Impl} (h5 : I 5 = 10) : rowCalls I [wRow] = [.upgrade 5 11] := by
  simp [rowCalls, wRow, h5]

/-- Reinitializers are inert in `rowConfig`, so a swap is a point update. -/
theorem swap_rowConfig (code : Address → Prop) (s : WState) (r : Row) (I : Impl) :
    ProxyUpgradeCurrent.swap (rowConfig code s) r I = upd I r.proxy r.implNew :=
  ProxyUpgradeCurrent.swap_inert (Or.inr fun _ => rfl) I

theorem rowsApplied_oneRow {J : Impl} (h : J 5 = 11) : RowsApplied J [wRow] := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h

/-- `applyRows` of the one row `5: 10 → 11`, from a state with proxy `5` at `10`. -/
theorem applyRows_oneRow {s : WState} (hpa : s.paOwner = 1) (h5 : s.impl 5 = 10) :
    ProxyUpgradeCurrent.ApplyRows (rowConfig allCode s) s.impl [wRow] (upd s.impl 5 11) := by
  refine ⟨fun _ _ => trivial, ?_, rowsApplied_oneRow (by simp [upd])⟩
  have hstep : ProxyUpgradeCurrent.ApplyRow (rowConfig allCode s) s.impl wRow
      (ProxyUpgradeCurrent.swap (rowConfig allCode s) wRow s.impl) :=
    ProxyUpgradeCurrent.ApplyRow.upgrade hpa (by show s.impl 5 ≠ 11; rw [h5]; decide) h5
  rw [swap_rowConfig] at hstep
  exact ProxyUpgradeCurrent.ApplyLoop.cons hstep ProxyUpgradeCurrent.ApplyLoop.nil

/-- The delegatecall of a one-row `engineWith allCode write after` engine from a state with the
row's proxy at its source, when `after` runs from the state after the row. -/
theorem oneRow_delegate {c : Address} {k : List UInt8 → UInt256} {write : Store → Store}
    {after : List WCall} {T : Address} {M : Manifest} {d : Domain} {st : Store} {s s' : WState}
    (hrows : toRows M.proxyUpgrades = [wRow]) (hlen : M.proxyUpgrades.length = inventoryLength d)
    (hpa : s.paOwner = 1) (h5 : s.impl 5 = 10) (hslot : s.adminSlot 5 = 2)
    (hafter : CallRun (wEnvWith c allCode k) { s with impl := upd s.impl 5 11 } after s') :
    Delegate (wEnvWith c allCode k) (engineWith allCode write after) M.proxyUpgradeEngine
      (context (wEnvWith c allCode k) T M d) M.proxyUpgrades st s (write st) s' := by
  refine Or.inl ⟨trivial, .upgrade 5 11 :: after, ⟨hpa, hlen, ⟨upd s.impl 5 11, ?_⟩, rfl, ?_⟩,
    CallRun.cons (WStep.upgrade hpa hslot trivial) hafter⟩
  · rw [hrows]; exact applyRows_oneRow hpa h5
  · rw [hrows, rowCalls_oneRow h5]; rfl

/-- Every successful delegatecall of a one-row `engineWith allCode write after` engine from a
state with the row's proxy at its source runs the row, then `after`. -/
theorem oneRow_delegate_inv {c : Address} {k : List UInt8 → UInt256} {write : Store → Store}
    {after : List WCall} {e : Address} {ctx : Context} {inv : List Row} {st st' : Store}
    {s s' : WState}
    (h : Delegate (wEnvWith c allCode k) (engineWith allCode write after) e ctx inv st s st' s')
    (hinv : toRows inv = [wRow]) (h5 : s.impl 5 = 10) :
    st' = write st ∧
      CallRun (wEnvWith c allCode k) { s with impl := upd s.impl 5 11 } after s' := by
  rcases h with ⟨_, calls, ⟨_, _, _, hst, hcalls⟩, hrun⟩ | ⟨hnc, _, _⟩
  · refine ⟨hst, ?_⟩
    rw [hcalls, hinv, rowCalls_oneRow h5] at hrun
    cases hrun with
    | cons hstep hrest =>
        change WStep allCode s (.upgrade 5 11) _ at hstep
        cases hstep
        exact hrest
  · exact absurd trivial hnc

/-- A run of one call is one step. -/
theorem callRun_single {c : Address} {k : List UInt8 → UInt256} {s s' : WState} {x : WCall}
    (h : CallRun (wEnvWith c allCode k) s [x] s') : WStep allCode s x s' := by
  cases h with
  | cons hstep hrest =>
      cases hrest with
      | nil => exact hstep

/-- The leg with check `c₀` deleted, for a one-row engine of the concrete world from a state
with the row's proxy at its source: each other check as a premise. -/
theorem legWithout_oneRow {c₀ : Check} {c : Address} {k : List UInt8 → UInt256}
    {write : Store → Store} {after : List WCall} {M : Manifest} {d : Domain} {s s' : WState}
    (hrows : toRows M.proxyUpgrades = [wRow]) (hlen : M.proxyUpgrades.length = inventoryLength d)
    (hpa : s.paOwner = 1) (h5 : s.impl 5 = 10) (hslot : s.adminSlot 5 = 2)
    (hafter : CallRun (wEnvWith c allCode k) { s with impl := upd s.impl 5 11 } after s')
    (hdom : c₀ ≠ .domain → M.domain = d)
    (hadm : c₀ ≠ .ctmAdmin → c ≠ 0 → s.roleAdmin c ≠ 2)
    (hown : c₀ ≠ .ownership →
      (write wStore).owner = wStore.owner ∧ (write wStore).pendingOwner = wStore.pendingOwner)
    (hh : c₀ ≠ .holders →
      domainHolders (wEnvWith c allCode k) s' = domainHolders (wEnvWith c allCode k) s)
    (hr : c₀ ≠ .rows → s'.impl 5 = 11) :
    LegWithout c₀ (wEnvWith c allCode k) (engineWith allCode write after) wT M d wStore s
      (write wStore) s' := by
  refine ⟨⟨⟨trivial, hlen⟩, oneRow_delegate hrows hlen hpa h5 hslot hafter⟩, ?_⟩
  intro x hx
  cases x with
  | domain => exact hdom (Ne.symm hx)
  | engineCode => trivial
  | ctmAdmin => exact hadm (Ne.symm hx)
  | ownership => exact hown (Ne.symm hx)
  | holders => exact hh (Ne.symm hx)
  | rows =>
      show RowsApplied s'.impl (toRows M.proxyUpgrades)
      rw [hrows]
      exact rowsApplied_oneRow (hr (Ne.symm hx))

/-- With inert reinitializers, the calls `rowCalls` sends for a successful loop succeed from a
state whose `ProxyAdmin` the executor owns and administers every proxy, and reach the loop's
implementations. -/
theorem rowCalls_run {c : Address} {code : Address → Prop} {k : List UInt8 → UInt256}
    {s₀ : WState} {rows : List Row} {I J : Impl}
    (h : ProxyUpgradeCurrent.ApplyLoop (rowConfig code s₀) I rows J) :
    ∀ s : WState, s.impl = I → s.paOwner = 1 → (∀ p, s.adminSlot p = 2) →
      (∀ r ∈ rows, code r.implNew) →
      CallRun (wEnvWith c code k) s (rowCalls I rows) { s with impl := J } := by
  induction h with
  | nil =>
      intro s hI _ _ _
      subst hI
      exact CallRun.nil
  | @cons I J K r rs hstep _ ih =>
      intro s hI hpa hslot hcode
      cases hstep with
      | alreadyAtTarget he =>
          have hc : rowCalls I (r :: rs) = rowCalls I rs := by simp [rowCalls, he]
          rw [hc]
          exact ih s hI hpa hslot (fun t ht => hcode t (List.mem_cons_of_mem _ ht))
      | upgrade _ hne _ =>
          have hc : rowCalls I (r :: rs) =
              .upgrade r.proxy r.implNew :: rowCalls (upd I r.proxy r.implNew) rs := by
            simp [rowCalls, hne]
          rw [hc]
          rw [swap_rowConfig] at ih
          subst hI
          exact CallRun.cons (WStep.upgrade hpa (hslot _) (hcode r List.mem_cons_self))
            (ih { s with impl := upd s.impl r.proxy r.implNew } rfl hpa hslot
              (fun t ht => hcode t (List.mem_cons_of_mem _ ht)))

/-- Conversely, wherever the calls `rowCalls` sends for a successful loop end, the world is
the start world with the loop's implementations. -/
theorem rowCalls_run_inv {c : Address} {code : Address → Prop} {k : List UInt8 → UInt256}
    {s₀ : WState} {rows : List Row} {I J : Impl}
    (h : ProxyUpgradeCurrent.ApplyLoop (rowConfig code s₀) I rows J) :
    ∀ s s' : WState, s.impl = I → CallRun (wEnvWith c code k) s (rowCalls I rows) s' →
      s' = { s with impl := J } := by
  induction h with
  | nil =>
      intro s s' hI hrun
      change CallRun _ s [] s' at hrun
      cases hrun
      subst hI
      rfl
  | @cons I J K r rs hstep _ ih =>
      intro s s' hI hrun
      cases hstep with
      | alreadyAtTarget he =>
          have hc : rowCalls I (r :: rs) = rowCalls I rs := by simp [rowCalls, he]
          rw [hc] at hrun
          exact ih s s' hI hrun
      | upgrade _ hne _ =>
          have hc : rowCalls I (r :: rs) =
              .upgrade r.proxy r.implNew :: rowCalls (upd I r.proxy r.implNew) rs := by
            simp [rowCalls, hne]
          rw [hc] at hrun
          rw [swap_rowConfig] at ih
          subst hI
          cases hrun with
          | cons hstep' hrest =>
              change WStep code s (.upgrade r.proxy r.implNew) _ at hstep'
              cases hstep'
              exact ih { s with impl := upd s.impl r.proxy r.implNew } s' rfl hrest

theorem DefaultEngineLegIsApplyTransition : Properties.DefaultEngineLegIsApplyTransition := by
  intro c code k T M d st s st' s' hslot
  constructor
  · rintro ⟨⟨hpre, hdel⟩, hchk⟩
    rcases hdel with ⟨_, calls, ⟨hpa, _, ⟨J, hJ⟩, hst, hcalls⟩, hrun⟩ | ⟨hnc, _, _⟩
    · rw [hcalls, List.append_nil] at hrun
      have hs' : s' = { s with impl := J } := rowCalls_run_inv hJ.loop s s' rfl hrun
      subst hs'
      exact ⟨hchk .engineCode, hpa, hpre.inventoryLength, hchk .ctmAdmin,
        ⟨hpre.transitionCode, hchk .domain, hJ⟩, hst, rfl⟩
    · exact absurd (hchk .engineCode) hnc
  · rintro ⟨hcode, hpa, hlen, hadm, ⟨hT, hdom, hJ⟩, rfl, hs'⟩
    obtain ⟨J, rfl⟩ : ∃ J, s' = { s with impl := J } := ⟨s'.impl, hs'⟩
    refine ⟨⟨⟨hT, hlen⟩, Or.inl ⟨hcode, _, ⟨hpa, hlen, ⟨J, hJ⟩, rfl, rfl⟩, ?_⟩⟩, ?_⟩
    · rw [List.append_nil]
      exact rowCalls_run hJ.loop s rfl hpa hslot hJ.code
    · intro x
      cases x with
      | domain => exact hdom
      | engineCode => exact hcode
      | ctmAdmin => exact hadm
      | ownership => exact ⟨rfl, rfl⟩
      | holders => rfl
      | rows => exact hJ.verified

/-! ## Hash computations in the concrete world -/

/-- The holder tuple does not read the hash. -/
theorem holderTuple_wEnvWith (c : Address) (k : List UInt8 → UInt256) (s : WState) :
    holderTuple (wEnvWith c allCode k) s = holderTuple (wEnvWith c allCode wKeccak) s := rfl

theorem wEnv_keccak : wEnv.keccak = wKeccak := rfl

theorem wKeccak_abiEncode (ws : List UInt256) :
    wKeccak (abiEncode ws) =
      if ws = ctmWords0 then 100 else if ws = notifierWords0 then 200 else 0 := by
  simp only [wKeccak, abiEncode_eq_iff]

theorem ctmWords_ne_notifierWords0 {E : Env σ κ} {s : σ} : ctmWords E s ≠ notifierWords0 := by
  intro h
  have := congrArg List.length h
  simp [ctmWords, notifierWords0] at this

theorem wKeccak_ctmPre_w0 : wKeccak (ctmPre wEnv w0) = 100 := by
  rw [ctmPre, wKeccak_abiEncode]
  decide

theorem wKeccak_holdersPre_w0 : wKeccak (holdersPre wEnv w0) = 200 := by
  rw [holdersPre_of_notifier (by decide) (by decide)]
  rw [wEnv_keccak]
  rw [wKeccak_ctmPre_w0, wKeccak_abiEncode]
  decide

theorem wKeccak_ctmPre_of_ne {s : WState} (h : ctmWords wEnv s ≠ ctmWords0) :
    wKeccak (ctmPre wEnv s) = 0 := by
  rw [ctmPre, wKeccak_abiEncode, ite_eq_right h, ite_eq_right ctmWords_ne_notifierWords0]

theorem wKeccak_holdersPre_of_ne {s : WState} (hn : s.notifier 8 ≠ 0)
    (h : ctmWords wEnv s ≠ ctmWords0) : wKeccak (holdersPre wEnv s) = 0 := by
  rw [holdersPre_of_notifier (by decide) hn]
  rw [wEnv_keccak]
  rw [wKeccak_ctmPre_of_ne h, wKeccak_abiEncode]
  have h1 : (0 : UInt256) :: notifierWords wEnv s ≠ ctmWords0 := by
    intro h'
    have := congrArg List.length h'
    simp [notifierWords, ctmWords0] at this
  have h2 : (0 : UInt256) :: notifierWords wEnv s ≠ notifierWords0 := by
    intro h'
    simp only [notifierWords0, List.cons.injEq] at h'
    exact absurd h'.1 (by decide)
  rw [ite_eq_right h1, ite_eq_right h2]

/-- Under `wKeccak`, a world whose CTM names a nonzero ServerNotifier and whose CTM words differ
from `w0`'s collides with `w0` on no compared preimage. -/
theorem noBreak_from_w0 {s : WState} (hn : s.notifier 8 ≠ 0) (h : ctmWords wEnv s ≠ ctmWords0) :
    ¬ HoldersBreak wEnv w0 s := by
  rintro (⟨_, hk⟩ | ⟨_, _, _, _, hk⟩)
  · rw [wEnv_keccak] at hk
    rw [wKeccak_holdersPre_w0, wKeccak_holdersPre_of_ne hn h] at hk
    exact absurd hk (by decide)
  · rw [wEnv_keccak] at hk
    rw [wKeccak_ctmPre_w0, wKeccak_ctmPre_of_ne h] at hk
    exact absurd hk (by decide)

/-! ## Satisfiability -/

theorem w1_impl5 : w1.impl 5 = 11 := by decide

theorem DefaultEngineLegWitness : Properties.DefaultEngineLegWitness := by
  refine ⟨fun k => ⟨?_, ?_, fun _ => rfl⟩, toRows_wInv, rfl, w1_impl5, rfl, fun _ => rfl, rfl,
    rfl, rfl, by decide⟩
  · exact leg_of_without (c₀ := .engineCode)
      (legWithout_oneRow (write := id) (after := []) toRows_wInv rfl rfl rfl rfl CallRun.nil
        (fun _ => rfl) (fun _ _ => by decide) (fun _ => ⟨rfl, rfl⟩) (fun _ => rfl)
        (fun _ => w1_impl5)) trivial
  · rintro (⟨hne, _⟩ | ⟨_, _, _, hne, _⟩) <;> exact hne rfl

theorem DefaultEngineCoreLegWitness : Properties.DefaultEngineCoreLegWitness := by
  refine ⟨fun k => ⟨?_, ?_⟩, toRows_wInvCore, by decide⟩
  · exact leg_of_without (c₀ := .engineCode)
      (legWithout_oneRow (write := id) (after := []) toRows_wInvCore rfl rfl rfl rfl CallRun.nil
        (fun _ => rfl) (fun _ h => absurd rfl h) (fun _ => ⟨rfl, rfl⟩) (fun _ => rfl)
        (fun _ => w1_impl5)) trivial
  · rintro (⟨hne, _⟩ | ⟨hc, _⟩)
    · exact hne rfl
    · exact hc rfl

theorem UnownedAdminReplayNowReverts : Properties.UnownedAdminReplayNowReverts := by
  have hrows : RowsApplied wUnowned.impl (toRows wInv) := by
    rw [toRows_wInv]
    exact rowsApplied_oneRow (by decide)
  refine ⟨⟨trivial, rfl, ⟨fun _ _ => trivial, ProxyUpgradeCurrent.applyLoop_skip hrows, hrows⟩⟩,
    by decide, ?_⟩
  rintro k ⟨st', s', h⟩
  rcases h.1.2 with ⟨_, _, ⟨hpa, _⟩, _⟩ | ⟨hnc, _, _⟩
  · exact absurd hpa (by decide)
  · exact hnc trivial

/-! ## Each check is load-bearing -/

theorem OwnerSlotWriteIsCaught : Properties.OwnerSlotWriteIsCaught := by
  refine ⟨fun k => ?_, fun k => ?_, rfl⟩
  · rintro ⟨st', s', h⟩
    obtain ⟨hst, _⟩ := oneRow_delegate_inv h.1.2 toRows_wInv rfl
    have hown := (h.2 .ownership).1
    rw [hst] at hown
    exact absurd hown (by decide)
  · exact legWithout_oneRow (write := fun st => { st with owner := 6 }) (after := []) toRows_wInv
      rfl rfl rfl rfl CallRun.nil (fun _ => rfl) (fun _ _ => by decide) (fun h => absurd rfl h)
      (fun _ => rfl) (fun _ => w1_impl5)

/-- Accepting a one-call engine from `w0` ends where the call ends, or collides. -/
theorem accepts_breaks_of_tuple_ne {k : List UInt8 → UInt256} {x : WCall} {s₁ : WState}
    (hstep : ∀ s', WStep allCode w1 x s' → s' = s₁)
    (hne : holderTuple wEnv s₁ ≠ holderTuple wEnv w0)
    (h : Accepts (wEnvWith 8 allCode k) (engineWith allCode id [x]) wT wManifest .ctm wStore w0) :
    HoldersBreak (wEnvWith 8 allCode k) w0 s₁ := by
  obtain ⟨st', s', h⟩ := h
  obtain ⟨_, hr⟩ := oneRow_delegate_inv h.1.2 toRows_wInv rfl
  have hs : s' = s₁ := hstep s' (callRun_single hr)
  subst hs
  rcases LegKeepsDomainHoldersOrCollides _ _ _ _ _ _ _ _ _ _ _ h with ht | hb
  · rw [holderTuple_wEnvWith 8 k, holderTuple_wEnvWith 8 k w0] at ht
    exact absurd ht hne
  · exact hb

theorem CtmNominationIsCaught : Properties.CtmNominationIsCaught := by
  have hacc : ∀ k : List UInt8 → UInt256,
      Accepts (wEnvWith 8 allCode k) ctmNominateEngine wT wManifest .ctm wStore w0 →
        HoldersBreak (wEnvWith 8 allCode k) w0 wNominated := fun k =>
    accepts_breaks_of_tuple_ne (fun s' hs => by cases hs; rfl) (by decide)
  have hnb : ¬ HoldersBreak wEnv w0 wNominated := noBreak_from_w0 (by decide) (by decide)
  refine ⟨hacc, hnb, fun h => hnb (hacc wKeccak h), fun k => ?_, by decide⟩
  exact legWithout_oneRow (write := id) (after := [.transferOwnership 8 7]) toRows_wInv rfl rfl
    rfl rfl (CallRun.cons (WStep.transferOwnership (by decide)) CallRun.nil) (fun _ => rfl)
    (fun _ _ => by decide) (fun _ => ⟨rfl, rfl⟩) (fun h => absurd rfl h) (fun _ => w1_impl5)

theorem NotifierRepointIsCaught : Properties.NotifierRepointIsCaught := by
  have hacc : ∀ k : List UInt8 → UInt256,
      Accepts (wEnvWith 8 allCode k) notifierRepointEngine wT wManifest .ctm wStore w0 →
        HoldersBreak (wEnvWith 8 allCode k) w0 wRepointed := fun k =>
    accepts_breaks_of_tuple_ne (fun s' hs => by cases hs; rfl) (by decide)
  have hnb : ¬ HoldersBreak wEnv w0 wRepointed := noBreak_from_w0 (by decide) (by decide)
  refine ⟨hacc, hnb, fun h => hnb (hacc wKeccak h), fun k => ?_, rfl, by decide, by decide⟩
  exact legWithout_oneRow (write := id) (after := [.setServerNotifier 8 13]) toRows_wInv rfl rfl
    rfl rfl (CallRun.cons (WStep.setServerNotifier (by decide)) CallRun.nil) (fun _ => rfl)
    (fun _ _ => by decide) (fun _ => ⟨rfl, rfl⟩) (fun h => absurd rfl h) (fun _ => w1_impl5)

theorem RowMovedBackIsCaught : Properties.RowMovedBackIsCaught := by
  refine ⟨fun k => ?_, fun k => ?_, by decide⟩
  · rintro ⟨st', s', h⟩
    obtain ⟨_, hr⟩ := oneRow_delegate_inv h.1.2 toRows_wInv rfl
    have hs : s' = wMovedBack := by
      have hstep := callRun_single hr
      cases hstep
      rfl
    subst hs
    have h5 := h.2 .rows wRow (by
      show wRow ∈ toRows wInv
      rw [toRows_wInv]
      exact List.mem_singleton_self _)
    change wMovedBack.impl 5 = 11 at h5
    exact absurd h5 (by decide)
  · exact legWithout_oneRow (write := id) (after := [.upgrade 5 10]) toRows_wInv rfl rfl rfl rfl
      (CallRun.cons (WStep.upgrade rfl rfl trivial) CallRun.nil) (fun _ => rfl)
      (fun _ _ => by decide) (fun _ => ⟨rfl, rfl⟩) (fun _ => rfl) (fun h => absurd rfl h)

/-- `ProxyAdmin.changeProxyAdmin(ctm, 13)` from `w1` makes `13` the CTM proxy's admin. -/
theorem ctmMove_from_w1 (s : WState) (h : WStep allCode w1 (.changeProxyAdmin 8 13) s) :
    s.adminSlot 8 = 13 := by
  cases h
  decide

theorem tuple_ctmMoved (k : List UInt8 → UInt256) :
    holderTuple (wEnvWith 8 allCode k) wCtmMoved = holderTuple (wEnvWith 8 allCode k) wAliased := by
  rw [holderTuple_wEnvWith 8 k wCtmMoved, holderTuple_wEnvWith 8 k wAliased]
  decide

theorem AliasedCtmMoveIsCaughtByTheAdminCheck :
    Properties.AliasedCtmMoveIsCaughtByTheAdminCheck := by
  refine ⟨fun k => ?_, fun k => ⟨?_, tuple_ctmMoved k, fun _ => rfl⟩, rfl, rfl, by decide, ?_⟩
  · rintro ⟨st', s', h⟩
    exact h.2 .ctmAdmin (show (8 : UInt256) ≠ 0 by decide) rfl
  · exact legWithout_oneRow (write := id) (after := [.changeProxyAdmin 8 13]) toRows_wInv rfl rfl
      rfl rfl (CallRun.cons (WStep.changeProxyAdmin rfl rfl (by decide)) CallRun.nil)
      (fun _ => rfl) (fun h => absurd rfl h) (fun _ => ⟨rfl, rfl⟩)
      (fun _ => UnchangedHoldersPassTheCheck _ _ _ _ _ (tuple_ctmMoved k)) (fun _ => by decide)
  · intro k st' s' h
    by_contra hb
    obtain ⟨hslot, -⟩ := LegKeepsCtmProxyAdministeredUnlessCollision _ _ _ _ _ _ _ _ _ _ _ h hb
      (show (8 : UInt256) ≠ 0 by decide) (fun _ => rfl) rfl
    obtain ⟨_, hr⟩ := oneRow_delegate_inv h.1.2 toRows_wInv rfl
    have h13 : s'.adminSlot 8 = 13 := ctmMove_from_w1 s' (callRun_single hr)
    have h2 : s'.adminSlot 8 = 2 := hslot
    rw [h13] at h2
    exact absurd h2 (by decide)

theorem CodelessEngineFreshStateIsRefused : Properties.CodelessEngineFreshStateIsRefused := by
  have hnc : ¬ wEnvCodeless.hasCode w0 wManifest.proxyUpgradeEngine := fun h => h rfl
  have hrow : ∃ r ∈ toRows wManifest.proxyUpgrades, wEnvCodeless.impl w0 r.proxy ≠ r.implNew :=
    ⟨wRow, by
      show wRow ∈ toRows wInv
      rw [toRows_wInv]
      exact List.mem_singleton_self _, by decide⟩
  exact ⟨hnc, hrow, CodelessEngineMovesNothing _ _ _ _ _ _ _ _ _ hnc hrow⟩

theorem CodelessEngineReplayIsCaught : Properties.CodelessEngineReplayIsCaught := by
  have hnc : ¬ wEnvCodeless.hasCode w1 wManifest.proxyUpgradeEngine := fun h => h rfl
  have hpre : LegPre wEnvCodeless wT wManifest .ctm w1 := ⟨show (3 : UInt256) ≠ 4 by decide, rfl⟩
  have hrows : RowsApplied (wEnvCodeless.impl w1) (toRows wManifest.proxyUpgrades) := by
    show RowsApplied w1.impl (toRows wInv)
    rw [toRows_wInv]
    exact rowsApplied_oneRow w1_impl5
  refine ⟨((CodelessEngineLegIff _ _ _ defaultEngine wT wManifest .ctm wStore w1 wStore w1
    hnc).1).2 ⟨hpre, rfl, fun _ => by decide, rfl, rfl, hrows⟩, ?_⟩
  rintro ⟨st', s', h⟩
  exact (CodelessEngineLegIff _ _ _ _ _ _ _ _ _ _ _ hnc).2 h

theorem CodelessEngineEmptyTransitionIsCaught :
    Properties.CodelessEngineEmptyTransitionIsCaught := by
  have hnc : ¬ wEnvCodeless.hasCode w0 wManifestEmpty.proxyUpgradeEngine := fun h => h rfl
  have hpre : LegPre wEnvCodeless wT wManifestEmpty .ctm w0 := ⟨show (3 : UInt256) ≠ 4 by decide, rfl⟩
  have hrows : RowsApplied (wEnvCodeless.impl w0) (toRows wManifestEmpty.proxyUpgrades) := by
    show RowsApplied _ (toRows wInvEmpty)
    rw [toRows_wInvEmpty]
    intro r hr
    exact absurd hr List.not_mem_nil
  refine ⟨((CodelessEngineLegIff _ _ _ defaultEngine wT wManifestEmpty .ctm wStore w0 wStore w0
    hnc).1).2 ⟨hpre, rfl, fun _ => by decide, rfl, rfl, hrows⟩, ?_⟩
  rintro ⟨st', s', h⟩
  exact (CodelessEngineLegIff _ _ _ _ _ _ _ _ _ _ _ hnc).2 h

theorem ForeignDomainManifestIsCaught : Properties.ForeignDomainManifestIsCaught := by
  refine ⟨?_, ?_, by decide⟩
  · rintro ⟨st', s', h⟩
    have hd : wManifestForeign.domain = .ctm := h.2 .domain
    exact absurd hd (by decide)
  · exact legWithout_oneRow (write := id) (after := []) toRows_wInv rfl rfl rfl rfl CallRun.nil
      (fun h => absurd rfl h) (fun _ _ => by decide) (fun _ => ⟨rfl, rfl⟩) (fun _ => rfl)
      (fun _ => w1_impl5)

/-! ## Boundaries -/

theorem HoldersCollisionIsNeeded : Properties.HoldersCollisionIsNeeded := by
  refine ⟨leg_of_without (c₀ := .engineCode)
      (legWithout_oneRow (write := id) (after := [.transferOwnership 8 7]) toRows_wInv rfl rfl
        rfl rfl (CallRun.cons (WStep.transferOwnership (by decide)) CallRun.nil) (fun _ => rfl)
        (fun _ _ => by decide) (fun _ => ⟨rfl, rfl⟩) (fun _ => rfl) (fun _ => w1_impl5)) trivial,
    by decide, Or.inr ⟨by decide, by decide, by decide, fun h => ?_, rfl⟩⟩
  exact absurd (ctmPre_eq_iff.mp h) (by decide)

theorem UnlistedProxyMovePassesEveryCheck : Properties.UnlistedProxyMovePassesEveryCheck := by
  refine ⟨fun k => leg_of_without (c₀ := .engineCode)
      (legWithout_oneRow (write := id) (after := [.upgrade 6 12]) toRows_wInv rfl rfl rfl rfl
        (CallRun.cons (WStep.upgrade rfl rfl trivial) CallRun.nil) (fun _ => rfl)
        (fun _ _ => by decide) (fun _ => ⟨rfl, rfl⟩) (fun _ => rfl) (fun _ => by decide)) trivial,
    ?_, rfl, by decide⟩
  intro r hr
  change r ∈ toRows wInv at hr
  rw [toRows_wInv] at hr
  simp only [List.mem_singleton] at hr
  subst hr
  decide

theorem UndeclaredSlotWritePassesEveryCheck : Properties.UndeclaredSlotWritePassesEveryCheck :=
  ⟨{ wStore with other := upd wStore.other 7 1 }, fun _ => leg_of_without (c₀ := .engineCode)
    (legWithout_oneRow (write := fun st => { st with other := upd st.other 7 1 }) (after := [])
      toRows_wInv rfl rfl rfl rfl CallRun.nil (fun _ => rfl) (fun _ _ => by decide)
      (fun _ => ⟨rfl, rfl⟩) (fun _ => rfl) (fun _ => w1_impl5)) trivial, rfl, by decide⟩

end Contracts.EngineLegV35
