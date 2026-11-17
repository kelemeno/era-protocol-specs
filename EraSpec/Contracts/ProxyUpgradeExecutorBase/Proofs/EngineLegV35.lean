import EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.EngineLegV35
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashPinned

/-!
# Proofs: what a successful engine leg pins, and each check is load-bearing

The general results read the post-checks off the leg: (a) and (c) are fields. (b) is a case
split on the hashed preimages. If the before and after preimages differ, their equal hashes
are a collision on those named inputs; if they are equal, the encoding is injective
(`AbiEncodeInjective`, from `word_val_inj` and the fixed 32-byte word length), so the tuples
are equal. With a ServerNotifier the split runs twice, once per level.

The witnesses and countermodels run in the witness world. Two helpers carry them:
`core_of_after` builds the engine's delegatecall from `w0` when its follow-up calls run from
`w1`, and `core_inv` shows that every successful delegatecall of such an engine from `w0` has
that shape. The rest is computation on small lists.
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

theorem abiEncode_nil : abiEncode [] = [] := rfl

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

/-! ## The leg -/

variable {σ κ : Type}

theorem leg_engine {E : Env σ κ} {eng : Engine σ κ} {T : Address} {M : Manifest} {d : Domain}
    {st : Store} {s : σ} {st' : Store} {s' : σ} (h : Leg E eng T M d st s st' s') :
    ∃ calls, eng (context E T M d) M.proxyUpgrades st s st' calls ∧ CallRun E s calls s' := by
  rcases h.1.2 with ⟨_, hrun⟩ | ⟨hnc, _, _⟩
  · exact hrun
  · exact absurd (h.2 .engineCode) hnc

theorem LegKeepsExecutorOwnership : Properties.LegKeepsExecutorOwnership :=
  fun _ _ _ _ _ _ _ _ _ _ _ h => h.2 .ownership

theorem LegChangesNoExecutorStorage : Properties.LegChangesNoExecutorStorage := by
  intro _ _ _ _ _ _ _ st _ st' _ h
  obtain ⟨h1, h2⟩ := h.2 .ownership
  cases st; cases st'
  simp_all

theorem LegKeepsDomainHoldersOrCollides : Properties.LegKeepsDomainHoldersOrCollides := by
  intro _ _ E _ _ _ _ _ s _ s' h
  have hh := h.2 .holders
  simp only [Check.Holds] at hh
  generalize notifierAt E s = n at hh ⊢
  unfold domainHolders at hh
  unfold holderTuple HoldersBreak
  split_ifs at hh ⊢ with hc hn
  · by_cases hp : corePre E s = corePre E s'
    · left
      have := AbiEncodeInjective _ _ hp
      simp only [List.cons.injEq] at this
      rw [this.1]
    · exact Or.inr ⟨hp, hh.symm⟩
  · by_cases hp : ctmPre E s = ctmPre E s'
    · left
      have := AbiEncodeInjective _ _ hp
      simp only [List.cons.injEq] at this
      obtain ⟨h1, h2, h3, h4, -⟩ := this
      rw [h1, h2, h3, h4]
    · exact Or.inr ⟨hp, hh.symm⟩
  · by_cases hq : notifierPre E n s = notifierPre E n s'
    · have := AbiEncodeInjective _ _ hq
      simp only [List.cons.injEq] at this
      obtain ⟨hk, h5, h6, h7, -⟩ := this
      by_cases hp : ctmPre E s = ctmPre E s'
      · left
        have := AbiEncodeInjective _ _ hp
        simp only [List.cons.injEq] at this
        obtain ⟨h1, h2, h3, h4, -⟩ := this
        rw [h1, h2, h3, h4, h5, h6, h7]
      · exact Or.inr (Or.inr ⟨hp, hk⟩)
    · exact Or.inr (Or.inl ⟨hq, hh.symm⟩)

theorem LegLandsEveryRow : Properties.LegLandsEveryRow :=
  fun _ _ _ _ _ _ _ _ _ _ _ h => ⟨h.1.1.inventoryLength, h.2 .rows⟩

theorem CodelessEngineLegIff : Properties.CodelessEngineLegIff := by
  intro _ _ E eng T M d st s st' s' hnc
  refine ⟨⟨?_, ?_⟩, fun h => hnc (h.2 .engineCode)⟩
  · rintro ⟨⟨hpre, hdel⟩, hc⟩
    rcases hdel with ⟨hcode, _⟩ | ⟨_, rfl, rfl⟩
    · exact absurd hcode hnc
    · exact ⟨hpre, rfl, rfl, hc .rows (by decide)⟩
  · rintro ⟨hpre, rfl, rfl, hrows⟩
    refine ⟨⟨hpre, Or.inr ⟨hnc, rfl, rfl⟩⟩, ?_⟩
    intro c hc
    cases c with
    | engineCode => exact absurd rfl hc
    | ownership => exact ⟨rfl, rfl⟩
    | holders => rfl
    | rows => exact hrows

theorem CodelessEngineMovesNothing : Properties.CodelessEngineMovesNothing := by
  rintro _ _ E eng T M d st s hnc ⟨r, hr, hne⟩ ⟨st', s', h⟩
  obtain ⟨_, _, _, hrows⟩ := ((CodelessEngineLegIff _ _ E eng T M d st s st' s' hnc).1).1 h
  exact hne (hrows r hr)

/-! ## Witness-world computations -/

theorem h80 : (8 : UInt256) ≠ 0 := by decide
theorem h90 : (9 : UInt256) ≠ 0 := by decide

theorem toRows_wInv : toRows wInv = [wRow] := by decide

theorem toRows_wInvEmpty : toRows wInvEmpty = [] := by decide

theorem wInv_length : wInv.length = 21 := rfl

theorem wInvEmpty_length : wInvEmpty.length = 21 := rfl

theorem rowCalls_w0 : rowCalls w0.impl [wRow] = [.upgrade 5 11] := by
  simp [rowCalls, w0, wRow]

theorem applyRows_w0 (code : Address → Prop) (hc : code 11) :
    ProxyUpgradeCurrent.ApplyRows (rowConfig code w0) w0.impl [wRow] w1.impl := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact hc
  · refine ProxyUpgradeCurrent.ApplyLoop.cons (J := ProxyUpgradeCurrent.swap (rowConfig code w0) wRow w0.impl)
      (ProxyUpgradeCurrent.ApplyRow.upgrade rfl (by simp [w0, wRow]) rfl) ?_
    have : ProxyUpgradeCurrent.swap (rowConfig code w0) wRow w0.impl = w1.impl := by
      simp [ProxyUpgradeCurrent.swap, wRow, w1]
    rw [this]
    exact ProxyUpgradeCurrent.ApplyLoop.nil
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    simp [w1, wRow, upd]

theorem notifierAt_w (code : Address → Prop) (k : List UInt8 → UInt256) (s : WState) :
    notifierAt (wEnvWith code k) s = s.notifier := by
  simp [notifierAt, wEnvWith, h80]

/-- The holders hash reads only the owners, nominees and admins. -/
theorem domainHolders_congr (E : Env σ κ) (n : Address) {s s' : σ}
    (h1 : E.paOwner s' = E.paOwner s) (h2 : E.ownerOf s' = E.ownerOf s)
    (h3 : E.pendingOwnerOf s' = E.pendingOwnerOf s) (h4 : E.getProxyAdmin s' = E.getProxyAdmin s) :
    domainHolders E n s' = domainHolders E n s := by
  simp [domainHolders, corePre, ctmPre, notifierPre, h1, h2, h3, h4]

/-- Every successful delegatecall of an `engineWith allCode write after` engine from `w0` on
the witness manifest runs the row and then `after`. -/
theorem core_inv {k : List UInt8 → UInt256} {write : Store → Store} {after : List WCall}
    {st' : Store} {s' : WState}
    (h : Leg (wEnvWith allCode k) (engineWith allCode write after) wT wManifest .ctm wStore w0
      st' s') :
    st' = write wStore ∧ CallRun (wEnvWith allCode k) w1 after s' := by
  obtain ⟨calls, ⟨_, _, _, hst, hcalls⟩, hrun⟩ := leg_engine h
  refine ⟨hst, ?_⟩
  have hc : calls = .upgrade 5 11 :: after := by
    rw [hcalls]
    show rowCalls w0.impl (toRows wInv) ++ after = _
    rw [toRows_wInv, rowCalls_w0]
    rfl
  subst hc
  cases hrun with
  | cons hstep hrest =>
      change WStep allCode w0 (.upgrade 5 11) _ at hstep
      cases hstep with
      | upgrade _ _ => exact hrest

/-- The delegatecall of an `engineWith allCode write after` engine from `w0` on the witness
manifest, when `after` runs from `w1`. -/
theorem core_of_after {k : List UInt8 → UInt256} {write : Store → Store} {after : List WCall}
    {s' : WState} (h : CallRun (wEnvWith allCode k) w1 after s') :
    LegCore (wEnvWith allCode k) (engineWith allCode write after) wT wManifest .ctm wStore w0
      (write wStore) s' := by
  refine ⟨⟨trivial, rfl, wInv_length⟩, Or.inl ⟨trivial, .upgrade 5 11 :: after, ?_, ?_⟩⟩
  · refine ⟨rfl, wInv_length, ⟨w1.impl, ?_⟩, rfl, ?_⟩
    · show ProxyUpgradeCurrent.ApplyRows (rowConfig allCode w0) w0.impl (toRows wInv) w1.impl
      rw [toRows_wInv]
      exact applyRows_w0 allCode trivial
    · show _ = rowCalls w0.impl (toRows wInv) ++ after
      rw [toRows_wInv, rowCalls_w0]
      rfl
  · exact CallRun.cons (WStep.upgrade rfl trivial) h

theorem rows_w1 : RowsApplied w1.impl (toRows wInv) := by
  rw [toRows_wInv]
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  simp [w1, wRow, upd]

/-- The checks other than the code check, for a state that agrees with `w1` on rows and on
holders. -/
theorem legOf {k : List UInt8 → UInt256} {write : Store → Store} {after : List WCall}
    {s' : WState} (h : CallRun (wEnvWith allCode k) w1 after s')
    (hw : (write wStore).owner = wStore.owner ∧ (write wStore).pendingOwner = wStore.pendingOwner)
    (hh : domainHolders (wEnvWith allCode k) 9 s' = domainHolders (wEnvWith allCode k) 9 w0)
    (hr : RowsApplied s'.impl (toRows wInv)) :
    Leg (wEnvWith allCode k) (engineWith allCode write after) wT wManifest .ctm wStore w0
      (write wStore) s' := by
  refine ⟨core_of_after h, ?_⟩
  intro c
  cases c with
  | engineCode => trivial
  | ownership => exact hw
  | holders =>
      show domainHolders _ (notifierAt _ w0) _ = domainHolders _ (notifierAt _ w0) _
      rw [notifierAt_w]; exact hh
  | rows => exact hr

theorem legWithoutOf {k : List UInt8 → UInt256} {write : Store → Store} {after : List WCall}
    {s' : WState} (c₀ : Check) (h : CallRun (wEnvWith allCode k) w1 after s')
    (hw : c₀ ≠ .ownership →
      (write wStore).owner = wStore.owner ∧ (write wStore).pendingOwner = wStore.pendingOwner)
    (hh : c₀ ≠ .holders →
      domainHolders (wEnvWith allCode k) 9 s' = domainHolders (wEnvWith allCode k) 9 w0)
    (hr : c₀ ≠ .rows → RowsApplied s'.impl (toRows wInv)) :
    LegWithout c₀ (wEnvWith allCode k) (engineWith allCode write after) wT wManifest .ctm wStore
      w0 (write wStore) s' := by
  refine ⟨core_of_after h, ?_⟩
  intro c hc
  cases c with
  | engineCode => trivial
  | ownership => exact hw (fun e => hc e.symm)
  | holders =>
      show domainHolders _ (notifierAt _ w0) _ = domainHolders _ (notifierAt _ w0) _
      rw [notifierAt_w]; exact hh (fun e => hc e.symm)
  | rows => exact hr (fun e => hc e.symm)

theorem holders_w1 (k : List UInt8 → UInt256) :
    domainHolders (wEnvWith allCode k) 9 w1 = domainHolders (wEnvWith allCode k) 9 w0 :=
  domainHolders_congr _ _ rfl rfl rfl rfl

/-! ## Satisfiability -/

theorem DefaultEngineLegWitness : Properties.DefaultEngineLegWitness := by
  refine ⟨legOf CallRun.nil ⟨rfl, rfl⟩ (holders_w1 _) rows_w1, notifierAt_w _ _ _, toRows_wInv,
    rfl, by simp [w1, upd], ?_, ?_⟩
  · simp [holderTuple, wEnv, wEnvWith, h80, h90]
  · have e1 : notifierPre wEnv 9 w1 = notifierPre wEnv 9 w0 := rfl
    have e2 : ctmPre wEnv w1 = ctmPre wEnv w0 := rfl
    have hc : wEnv.chainTypeManager ≠ 0 := h80
    simp [HoldersBreak, Collides, e1, e2, hc, h90]

/-! ## Each check is load-bearing -/

theorem OwnerSlotWriteIsCaught : Properties.OwnerSlotWriteIsCaught := by
  refine ⟨?_, ⟨_, _, legWithoutOf .ownership CallRun.nil (fun h => absurd rfl h)
    (fun _ => holders_w1 _) (fun _ => rows_w1)⟩⟩
  rintro ⟨st', s', h⟩
  obtain ⟨hst, _⟩ := core_inv h
  have := (h.2 .ownership).1
  rw [hst] at this
  exact absurd this (by decide)

/-- The state after the CTM nomination. -/
def wNominated : WState := { w1 with pending := upd w1.pending 8 7 }

theorem run_nominate (k : List UInt8 → UInt256) :
    CallRun (wEnvWith allCode k) w1 [.transferOwnership 8 7] wNominated :=
  CallRun.cons (WStep.transferOwnership rfl) CallRun.nil

theorem run_nominate_inv {k : List UInt8 → UInt256} {s' : WState}
    (h : CallRun (wEnvWith allCode k) w1 [.transferOwnership 8 7] s') : s' = wNominated := by
  cases h with
  | cons hstep hrest =>
      change WStep allCode w1 (.transferOwnership 8 7) _ at hstep
      cases hstep with
      | transferOwnership _ =>
          cases hrest with
          | nil => rfl

theorem ctmPre_nominated (k : List UInt8 → UInt256) :
    ctmPre (wEnvWith allCode k) wNominated = abiEncode [1, 1, 7, 2] := by
  simp [ctmPre, wEnvWith, wNominated, w1, w0, upd]

theorem ctmPre_w0 (k : List UInt8 → UInt256) :
    ctmPre (wEnvWith allCode k) w0 = abiEncode [1, 1, 0, 2] := rfl

theorem notifierPre_nominated (k : List UInt8 → UInt256) :
    notifierPre (wEnvWith allCode k) 9 wNominated =
      abiEncode [k (abiEncode [1, 1, 7, 2]), 1, 0, 2] := by
  rw [notifierPre, ctmPre_nominated]
  simp [wEnvWith, wNominated, w1, w0, upd]

theorem notifierPre_w0 (k : List UInt8 → UInt256) :
    notifierPre (wEnvWith allCode k) 9 w0 = abiEncode [k (abiEncode [1, 1, 0, 2]), 1, 0, 2] := rfl

theorem holders_nominated_ne :
    domainHolders wEnv 9 wNominated ≠ domainHolders wEnv 9 w0 := by
  have hv : (9 : UInt256) ≠ 0 := h90
  have hc : wEnv.chainTypeManager ≠ 0 := h80
  unfold domainHolders
  simp only [hc, hv, if_false]
  show wKeccak (notifierPre wEnv 9 wNominated) ≠ wKeccak (notifierPre wEnv 9 w0)
  rw [show wEnv = wEnvWith allCode wKeccak from rfl, notifierPre_nominated, notifierPre_w0]
  simp [wKeccak, ctmPre0, notifierPre0, abiEncode_eq_iff]

theorem CtmNominationIsCaught : Properties.CtmNominationIsCaught := by
  refine ⟨?_, ⟨_, _, legWithoutOf .holders (run_nominate _) (fun _ => ⟨rfl, rfl⟩)
    (fun h => absurd rfl h) (fun _ => rows_w1)⟩⟩
  rintro ⟨st', s', h⟩
  obtain ⟨_, hrun⟩ := core_inv h
  have hs := run_nominate_inv hrun
  subst hs
  have := h.2 .holders
  simp only [Check.Holds] at this
  rw [show notifierAt wEnv w0 = 9 from notifierAt_w _ _ _] at this
  exact holders_nominated_ne this

/-- The state after the row and the move back. -/
def wMovedBack : WState := { w1 with impl := upd w1.impl 5 10 }

theorem RowMovedBackIsCaught : Properties.RowMovedBackIsCaught := by
  have hrun : CallRun wEnv w1 [.upgrade 5 10] wMovedBack :=
    CallRun.cons (WStep.upgrade rfl trivial) CallRun.nil
  refine ⟨?_, ⟨_, _, legWithoutOf .rows hrun (fun _ => ⟨rfl, rfl⟩)
    (fun _ => domainHolders_congr _ _ rfl rfl rfl rfl) (fun h => absurd rfl h)⟩⟩
  rintro ⟨st', s', h⟩
  obtain ⟨_, hrun'⟩ := core_inv h
  have hs : s' = wMovedBack := by
    cases hrun' with
    | cons hstep hrest =>
        change WStep allCode w1 (.upgrade 5 10) _ at hstep
        cases hstep with
        | upgrade _ _ => cases hrest with | nil => rfl
  subst hs
  have := h.2 .rows
  simp only [Check.Holds] at this
  have h5 := this wRow (by show wRow ∈ toRows wInv; rw [toRows_wInv]; simp)
  revert h5
  simp [wEnv, wEnvWith, wMovedBack, w1, wRow, upd]

theorem CodelessEngineReplayIsCaught : Properties.CodelessEngineReplayIsCaught := by
  have hnc : ¬ wEnvCodeless.hasCode w1 wManifest.proxyUpgradeEngine := by
    simp [wEnvCodeless, wEnvWith, noEngineCode, wManifest]
  have hpre : LegPre wEnvCodeless wT wManifest .ctm w1 :=
    ⟨by simp [wEnvCodeless, wEnvWith, noEngineCode, wT], rfl, wInv_length⟩
  refine ⟨((CodelessEngineLegIff _ _ _ defaultEngine wT wManifest .ctm wStore w1 wStore w1
    hnc).1).2 ⟨hpre, rfl, rfl, rows_w1⟩, ?_⟩
  rintro ⟨st', s', h⟩
  exact (CodelessEngineLegIff _ _ _ _ _ _ _ _ _ _ _ hnc).2 h

theorem CodelessEngineEmptyTransitionIsCaught :
    Properties.CodelessEngineEmptyTransitionIsCaught := by
  have hnc : ¬ wEnvCodeless.hasCode w0 wManifestEmpty.proxyUpgradeEngine := by
    simp [wEnvCodeless, wEnvWith, noEngineCode, wManifestEmpty]
  have hpre : LegPre wEnvCodeless wT wManifestEmpty .ctm w0 :=
    ⟨by simp [wEnvCodeless, wEnvWith, noEngineCode, wT], rfl, wInvEmpty_length⟩
  have hrows : RowsApplied (wEnvCodeless.impl w0) (toRows wManifestEmpty.proxyUpgrades) := by
    show RowsApplied _ (toRows wInvEmpty)
    rw [toRows_wInvEmpty]
    intro r hr
    simp at hr
  refine ⟨((CodelessEngineLegIff _ _ _ defaultEngine wT wManifestEmpty .ctm wStore w0 wStore w0
    hnc).1).2 ⟨hpre, rfl, rfl, hrows⟩, ?_⟩
  rintro ⟨st', s', h⟩
  exact (CodelessEngineLegIff _ _ _ _ _ _ _ _ _ _ _ hnc).2 h

/-! ## Boundaries -/

theorem HoldersCollisionIsNeeded : Properties.HoldersCollisionIsNeeded := by
  refine ⟨_, _, legOf (run_nominate _) ⟨rfl, rfl⟩ rfl rows_w1, ?_, ?_⟩
  · intro h
    have hc : (wEnvWith allCode constKeccak).chainTypeManager ≠ 0 := h80
    simp only [holderTuple, hc, h90, if_false, List.cons.injEq] at h
    revert h
    simp [wEnvWith, wNominated, w1, w0, upd]
    decide
  · have hc : (wEnvWith allCode constKeccak).chainTypeManager ≠ 0 := h80
    unfold HoldersBreak
    simp only [hc, h90, if_false]
    refine Or.inr ⟨?_, rfl⟩
    rw [ctmPre_w0, ctmPre_nominated, Ne, abiEncode_eq_iff]
    decide

/-- The state after the row and the unlisted move. -/
def wUnlisted : WState := { w1 with impl := upd w1.impl 6 12 }

theorem UnlistedProxyMovePassesEveryCheck : Properties.UnlistedProxyMovePassesEveryCheck := by
  have hrun : CallRun wEnv w1 [.upgrade 6 12] wUnlisted :=
    CallRun.cons (WStep.upgrade rfl trivial) CallRun.nil
  refine ⟨_, _, legOf hrun ⟨rfl, rfl⟩ (domainHolders_congr _ _ rfl rfl rfl rfl) ?_, ?_, ?_⟩
  · rw [toRows_wInv]
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    simp [wUnlisted, w1, wRow, upd]
  · intro r hr
    have hr' : r ∈ toRows wInv := hr
    rw [toRows_wInv] at hr'
    simp only [List.mem_singleton] at hr'
    subst hr'
    decide
  · simp [wUnlisted, w1, w0, upd]

end Contracts.EngineLegV35
