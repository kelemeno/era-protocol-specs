import EraSpec.Contracts.AssetRouterBase.Properties.CounterpartGate
import EraSpec.Contracts.AssetRouterBase.Proofs.AllWriters

/-!
# Proofs: the counterpart exception, narrowed by the L1 side

The L1 half rests on one hash-free invariant of every run (`run_trackerSource`).  A
nonzero tracker sits at the id of a triple the run logged, and that triple's sender is
the tracker or its normalised form.  At a vault triple's id, either that logged triple
is the vault triple, so the tracker is the vault or `L2_NATIVE_TOKEN_VAULT_ADDR`, or it
is a different logged triple with the same id: the clash.
-/

namespace Contracts.AssetRouter.AllWriters

/-! ## Where a tracker comes from -/

/-- Every nonzero tracker sits at the id of a logged triple whose sender is that tracker,
or the tracker's normalised form. -/
def TrackerSource (K : Cfg) (ops : List Op) (R : Router) : Prop :=
  ∀ a, R.tracker a ≠ 0 → ∃ p ∈ loggedTriples K ops, K.enc p.1 p.2.1 p.2.2 = a ∧
    (p.2.1 = R.tracker a ∨ p.2.1 = senderOf K.ntv K.ntvAddr (R.tracker a))

lemma trackerSource_frame {K : Cfg} {ops : List Op} {op : Op} {S T : Router}
    (hP : TrackerSource K ops S) (ht : T.tracker = S.tracker) :
    TrackerSource K (ops ++ [op]) T := by
  intro a ha
  rw [ht] at ha ⊢
  obtain ⟨p, hp, h1, h2⟩ := hP a ha
  exact ⟨p, loggedTriples_mono hp, h1, h2⟩

theorem run_trackerSource {K : Cfg} {ops : List Op} {R : Router} (hr : ARun K empty ops R) :
    TrackerSource K ops R := by
  induction hr with
  | nil => intro a ha; exact absurd rfl ha
  | @snoc S T ops op _ hs ih =>
    cases hs with
    | @register _ caller d h _ =>
      intro x hx
      by_cases hxw : x = writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d
      · subst hxw
        refine ⟨(K.thisChain, senderOf K.ntv K.ntvAddr caller, d), mem_loggedTriples_snoc rfl,
          rfl, Or.inr ?_⟩
        rw [tracker_records_caller]
      · rw [setHandler_tracker_ne _ _ _ _ _ _ _ _ hxw] at hx ⊢
        obtain ⟨p, hp, h1, h2⟩ := ih x hx
        exact ⟨p, loggedTriples_mono hp, h1, h2⟩
    | finalize _ _ _ => exact trackerSource_frame ih rfl
    | seed => exact trackerSource_frame ih rfl
    | counterpartSet _ => exact trackerSource_frame ih rfl
    | @setTracker _ d t _ =>
      intro x hx
      by_cases hxt : x = K.enc K.thisChain t d
      · subst hxt
        rw [recordTracker_tracker_self] at hx ⊢
        exact ⟨(K.thisChain, t, d), mem_loggedTriples_snoc rfl, rfl, Or.inl rfl⟩
      · rw [recordTracker_tracker_ne _ _ hxt] at hx ⊢
        obtain ⟨p, hp, h1, h2⟩ := ih x hx
        exact ⟨p, loggedTriples_mono hp, h1, h2⟩

/-! ## The L1 half -/

theorem l1_counterpart_at_vault_id_or_logged_clash {K1 : Cfg} {approves : Approvals}
    (hA : VaultApprovals K1 approves) {ops1 : List Op} {R1 : Router}
    (hr : ARun K1 empty ops1 R1) {q : Chain × Address × AssetData} (hq : q.2.1 = K1.ntvAddr)
    {h : Address} (he : L1Emits approves R1 (K1.enc q.1 q.2.1 q.2.2) h) :
    h = K1.ntvAddr ∨
      ∃ p ∈ loggedTriples K1 ops1, p ≠ q ∧ K1.enc p.1 p.2.1 p.2.2 = K1.enc q.1 q.2.1 q.2.2 := by
  unfold L1Emits at he
  have ht : R1.tracker (K1.enc q.1 q.2.1 q.2.2) ≠ 0 := fun h0 => hA.zero _ h (h0 ▸ he)
  obtain ⟨p, hp, hpa, hps⟩ := run_trackerSource hr _ ht
  by_cases hpq : p = q
  · left
    have hp1 : p.2.1 = K1.ntvAddr := by rw [hpq]; exact hq
    have key : R1.tracker (K1.enc q.1 q.2.1 q.2.2) = K1.ntv ∨
        R1.tracker (K1.enc q.1 q.2.1 q.2.2) = K1.ntvAddr := by
      rcases hps with h1 | h1
      · exact Or.inr (h1.symm.trans hp1)
      · by_cases htn : R1.tracker (K1.enc q.1 q.2.1 q.2.2) = K1.ntv
        · exact Or.inl htn
        · rw [senderOf_ne htn] at h1
          exact Or.inr (h1.symm.trans hp1)
    rcases key with h2 | h2
    · exact hA.vault _ h (h2 ▸ he)
    · exact hA.vaultAddr _ h (h2 ▸ he)
  · exact Or.inr ⟨p, hp, hpq, hpa⟩

theorem l1_counterpart_at_vault_id_on {K1 : Cfg} {approves : Approvals}
    (hA : VaultApprovals K1 approves) {ops1 : List Op} {R1 : Router}
    (hr : ARun K1 empty ops1 R1) {q : Chain × Address × AssetData} (hq : q.2.1 = K1.ntvAddr)
    (hinj : IdInjOn K1.enc (↑(loggedTriples K1 ops1) ∪ {q})) {h : Address}
    (he : L1Emits approves R1 (K1.enc q.1 q.2.1 q.2.2) h) : h = K1.ntvAddr := by
  rcases l1_counterpart_at_vault_id_or_logged_clash hA hr hq he with h1 | ⟨p, hp, hpq, hpe⟩
  · exact h1
  · exact absurd (hinj p (Set.mem_union_left _ (Finset.mem_coe.2 hp)) q
      (Set.mem_union_right _ (Set.mem_singleton q)) hpe) hpq

/-! ## The L2 half -/

lemma acct_congr {K : Cfg} {R R' : Router} {x : AssetId}
    (hw : R.handler x ≠ 0 → R.tracker x ≠ 0 ∨ R.handler x = K.ntv)
    (hh : R'.handler x = R.handler x) (ht : R'.tracker x = R.tracker x) :
    R'.handler x ≠ 0 → R'.tracker x ≠ 0 ∨ R'.handler x = K.ntv := by
  intro hx
  rw [hh] at hx ⊢
  rw [ht]
  exact hw hx

theorem l2_route_accountable {K : Cfg} (hK : K.side = .l2) (x : AssetId) {ops : List Op}
    {R : Router} (hr : ARun K empty ops R) (hc : ∀ h, Op.counterpartSet x h ∈ ops → h = K.ntv) :
    R.handler x ≠ 0 → R.tracker x ≠ 0 ∨ R.handler x = K.ntv := by
  induction hr with
  | nil => intro h; exact absurd rfl h
  | @snoc S T ops op _ hs ih =>
    have ih' := ih fun h hm => hc h (List.mem_append_left _ hm)
    cases hs with
    | @register _ caller d h hg =>
      by_cases hxw : x = writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d
      · subst hxw
        intro _
        left
        rw [tracker_records_caller]
        exact hg.callerNonzero
      · exact acct_congr ih' (handler_frame _ _ _ _ _ _ _ _ _ hxw)
          (setHandler_tracker_ne _ _ _ _ _ _ _ _ hxw)
    | @finalize _ a _ _ _ =>
      by_cases hxa : x = a
      · subst hxa
        exact fun _ => Or.inr (pointAt_handler_self _ _ _)
      · exact acct_congr ih' (pointAt_handler_ne _ _ hxa) rfl
    | seed =>
      by_cases hxa : x = K.seedId
      · subst hxa
        exact fun _ => Or.inr (pointAt_handler_self _ _ _)
      · exact acct_congr ih' (pointAt_handler_ne _ _ hxa) rfl
    | @counterpartSet _ a h _ =>
      by_cases hxa : x = a
      · subst hxa
        intro _
        right
        rw [pointAt_handler_self]
        exact hc h (List.mem_append_right _ (List.mem_singleton_self _))
      · exact acct_congr ih' (pointAt_handler_ne _ _ hxa) rfl
    | setTracker hside => rw [hK] at hside; cases hside

theorem counterpart_cannot_misroute_vault_triple {K1 K2 : Cfg} {approves : Approvals}
    (hK2 : K2.side = .l2) (hnA : K2.ntvAddr = K1.ntvAddr) (hnv : K2.ntv = K2.ntvAddr)
    (hA : VaultApprovals K1 approves) {q : Chain × Address × AssetData}
    (hq : q.2.1 = K1.ntvAddr) {ops : List Op} {R : Router} (hr : ARun K2 empty ops R)
    (hmsg : ∀ h, Op.counterpartSet (K2.enc q.1 q.2.1 q.2.2) h ∈ ops →
      ∃ (ops1 : List Op) (R1 : Router), ARun K1 empty ops1 R1 ∧
        L1Emits approves R1 (K1.enc q.1 q.2.1 q.2.2) h ∧
        IdInjOn K1.enc (↑(loggedTriples K1 ops1) ∪ {q})) :
    TripleAccountable K2 R q := by
  refine l2_route_accountable hK2 _ hr (fun h hm => ?_)
  obtain ⟨ops1, R1, hr1, he, hinj⟩ := hmsg h hm
  rw [hnv, hnA]
  exact l1_counterpart_at_vault_id_on hA hr1 hq hinj he

/-! ## Witnesses and countermodels -/

/-- Only the L1 vault `9` lets anything through, and only the L2 vault `8`. -/
def wApp : Approvals := fun t _ h => t = 9 ∧ h = 8

/-- As `wApp`, plus a custom tracker `5` that lets every handler through. -/
def wApp5 : Approvals := fun t _ h => (t = 9 ∧ h = 8) ∨ t = 5

lemma wApp_ok : VaultApprovals wK1 wApp :=
  ⟨fun _ _ hh => absurd hh.1 (by decide), fun _ _ hh => hh.2,
    fun _ _ hh => absurd hh.1 (by decide)⟩

lemma wApp5_ok (K : Cfg) (hv : K.ntv = 9) (ha : K.ntvAddr = 8) : VaultApprovals K wApp5 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ _ (⟨h1, _⟩ | h1) <;> exact absurd h1 (by decide)
  · rw [hv, ha]
    rintro _ _ (⟨_, h2⟩ | h1)
    · exact h2
    · exact absurd h1 (by decide)
  · rw [ha]
    rintro _ _ (⟨h1, _⟩ | h1) <;> exact absurd h1 (by decide)

/-- The L1 vault registers token `0`: id `wEnc 1 8 0 = 100`, tracker the vault. -/
def g1 : Router := setHandler wEnc 1 9 8 empty 9 0 9

lemma runG1 : ARun wK1 empty [.register 9 0 9] g1 :=
  (ARun.nil).snoc (AStep.register (⟨Or.inl rfl, by decide⟩ : SetGuard wEnc 1 9 8 empty 9 0))

lemma idInjOn_singleton {enc : AssetIdOf} {S : Set (Chain × Address × AssetData)}
    {x : Chain × Address × AssetData} (hS : S ⊆ {x}) : IdInjOn enc S :=
  fun _ hp _ hq _ => (hS hp).trans (hS hq).symm

lemma g1_inj :
    IdInjOn wEnc (↑(loggedTriples wK1 [.register 9 0 9]) ∪ {((1 : Chain), (8 : Address),
      (0 : AssetData))}) := by
  refine idInjOn_singleton (x := ((1 : Chain), (8 : Address), (0 : AssetData))) ?_
  intro p hp
  rcases hp with hp | hp
  · rw [Finset.mem_coe, mem_loggedTriples] at hp
    obtain ⟨op, hop, hpop⟩ := hp
    rw [List.mem_singleton] at hop
    subst hop
    simp only [Op.triple, Option.some.injEq] at hpop
    rw [← hpop]
    show ((1 : Chain), senderOf 9 8 9, (0 : AssetData)) = (1, 8, 0)
    rw [senderOf_self]
  · exact hp

lemma g1_emits : L1Emits wApp g1 (wK1.enc 1 8 0) 8 := ⟨by decide, rfl⟩

theorem l1_counterpart_at_vault_id_witness :
    ∃ (K1 : Cfg) (approves : Approvals) (ops1 : List Op) (R1 : Router)
      (q : Chain × Address × AssetData) (h : Address),
      K1.side = .l1 ∧ VaultApprovals K1 approves ∧ ARun K1 empty ops1 R1 ∧
      q.2.1 = K1.ntvAddr ∧ IdInjOn K1.enc (↑(loggedTriples K1 ops1) ∪ {q}) ∧
      L1Emits approves R1 (K1.enc q.1 q.2.1 q.2.2) h :=
  ⟨wK1, wApp, [.register 9 0 9], g1, (1, 8, 0), 8, rfl, wApp_ok, runG1, rfl, g1_inj, g1_emits⟩

theorem custom_tracker_names_any_handler :
    ∃ (K1 : Cfg) (approves : Approvals) (ops1 : List Op) (R1 : Router) (a : AssetId)
      (h : Address),
      K1.side = .l1 ∧ VaultApprovals K1 approves ∧ ARun K1 empty ops1 R1 ∧
      ¬ IsNtvId K1.enc K1.ntvAddr a ∧ L1Emits approves R1 a h ∧ h ≠ K1.ntvAddr ∧ h ≠ 0 :=
  ⟨wK1, wApp5, [.setTracker 3 5], recordTracker wK1 empty 3 5, 5, 7, rfl,
    wApp5_ok wK1 rfl rfl, (ARun.nil).snoc (AStep.setTracker rfl), not_isNtv_5,
    Or.inr (by decide), by decide, by decide⟩

theorem counterpart_gate_clash_fires :
    ∃ (K1 : Cfg) (approves : Approvals) (ops1 : List Op) (R1 : Router)
      (q : Chain × Address × AssetData) (h : Address),
      K1.side = .l1 ∧ VaultApprovals K1 approves ∧ ARun K1 empty ops1 R1 ∧
      q.2.1 = K1.ntvAddr ∧ L1Emits approves R1 (K1.enc q.1 q.2.1 q.2.2) h ∧
      h ≠ K1.ntvAddr ∧ ¬ IdInjOn K1.enc (↑(loggedTriples K1 ops1) ∪ {q}) := by
  refine ⟨cK, wApp5, [.setTracker 3 5], recordTracker cK empty 3 5, (1, 8, 0), 7, rfl,
    wApp5_ok cK rfl rfl, (ARun.nil).snoc (AStep.setTracker rfl), rfl, Or.inr (by decide),
    by decide, ?_⟩
  intro hinj
  have hmem : ((1 : Chain), (5 : Address), (3 : AssetData)) ∈ loggedTriples cK [.setTracker 3 5] :=
    mem_loggedTriples.2 ⟨.setTracker 3 5, List.mem_singleton_self _, rfl⟩
  exact absurd (hinj _ (Set.mem_union_left _ (Finset.mem_coe.2 hmem)) _
    (Set.mem_union_right _ (Set.mem_singleton _)) rfl) (by decide)

theorem counterpart_cannot_misroute_vault_triple_witness :
    ∃ (K1 K2 : Cfg) (approves : Approvals) (q : Chain × Address × AssetData) (ops : List Op)
      (R : Router),
      K1.side = .l1 ∧ K2.side = .l2 ∧ K2.enc = K1.enc ∧ K2.ntvAddr = K1.ntvAddr ∧
      K2.ntv = K2.ntvAddr ∧ VaultApprovals K1 approves ∧ q.2.1 = K1.ntvAddr ∧
      ARun K2 empty ops R ∧
      (∀ h, Op.counterpartSet (K2.enc q.1 q.2.1 q.2.2) h ∈ ops →
        ∃ (ops1 : List Op) (R1 : Router), ARun K1 empty ops1 R1 ∧
          L1Emits approves R1 (K1.enc q.1 q.2.1 q.2.2) h ∧
          IdInjOn K1.enc (↑(loggedTriples K1 ops1) ∪ {q})) ∧
      (∃ h, Op.counterpartSet (K2.enc q.1 q.2.1 q.2.2) h ∈ ops) ∧
      R.handler (K2.enc q.1 q.2.1 q.2.2) ≠ 0 := by
  refine ⟨wK1, wK2, wApp, (1, 8, 0), [.counterpartSet (wEnc 1 8 0) 8],
    pointAt empty (wEnc 1 8 0) 8, rfl, rfl, rfl, rfl, rfl, wApp_ok, rfl,
    (ARun.nil).snoc (AStep.counterpartSet rfl), ?_, ⟨8, List.mem_singleton_self _⟩, ?_⟩
  · intro h hm
    rw [List.mem_singleton] at hm
    cases hm
    exact ⟨[.register 9 0 9], g1, runG1, g1_emits, g1_inj⟩
  · rw [show wK2.enc 1 8 0 = wEnc 1 8 0 from rfl, pointAt_handler_self]
    decide

end Contracts.AssetRouter.AllWriters

/-! ## Certificates -/

namespace Contracts.AssetRouter.AllWriters

theorem L1CounterpartAtVaultIdOrLoggedClash : Properties.L1CounterpartAtVaultIdOrLoggedClash :=
  fun _ _ _ hA _ _ hr _ hq _ he => l1_counterpart_at_vault_id_or_logged_clash hA hr hq he

theorem L1CounterpartAtVaultIdOn : Properties.L1CounterpartAtVaultIdOn :=
  fun _ _ _ hA _ _ hr _ hq hinj _ he => l1_counterpart_at_vault_id_on hA hr hq hinj he

theorem L1CounterpartAtVaultIdWitness : Properties.L1CounterpartAtVaultIdWitness :=
  l1_counterpart_at_vault_id_witness

theorem CustomTrackerNamesAnyHandler : Properties.CustomTrackerNamesAnyHandler :=
  custom_tracker_names_any_handler

theorem CounterpartGateClashFires : Properties.CounterpartGateClashFires :=
  counterpart_gate_clash_fires

theorem L2RouteAccountable : Properties.L2RouteAccountable :=
  fun _ hK x _ _ hr hc => l2_route_accountable hK x hr hc

theorem CounterpartCannotMisrouteVaultTriple : Properties.CounterpartCannotMisrouteVaultTriple :=
  fun _ _ _ _ hK2 _ hnA hnv hA _ hq _ _ hr hmsg =>
    counterpart_cannot_misroute_vault_triple hK2 hnA hnv hA hq hr hmsg

theorem CounterpartCannotMisrouteVaultTripleWitness :
    Properties.CounterpartCannotMisrouteVaultTripleWitness :=
  counterpart_cannot_misroute_vault_triple_witness

end Contracts.AssetRouter.AllWriters
