import EraSpec.Contracts.ChainTypeManager.Properties.L2Derivation

/-!
# Proofs: the L2 side a registry transition derives from its two releases

The loops are transcribed by their revert conditions and their outputs, so each property reduces
to reading those off: `changedL2Rows_some`, `derive_some` and `buildPlan_some` say exactly what a
successful call returns, and `ctmTransitionL2_some` takes a successful construction apart. The
hash appears only as `kec x = kec y`; where a property needs `x = y`, it splits on `x = y` and
the other case is the named clash. The witnesses are concrete and checked by `decide`, except
where a statement quantifies over every hash (`AppendedEmptyRowKeepsAnL1OnlyEdge`), which is
proved through `derivedPlan_of_rows_agree`.
-/

namespace Contracts.ChainTypeManager.L2Tables

/-! ## Rows and fixed addresses -/

lemma fixedAddress_lt {i : ℕ} (h : fixedAddress i ≠ none) : i < memberCount := by
  unfold fixedAddress at h
  unfold memberCount
  split at h <;> first | omega | exact absurd rfl h

/-- `L2InventoryLib.fixedAddress` never sends two members to one address. -/
lemma fixedAddress_inj {i j : ℕ} {a : L2Addr} (hi : fixedAddress i = some a)
    (hj : fixedAddress j = some a) : i = j := by
  have hi' : i < 27 := fixedAddress_lt (by rw [hi]; simp)
  have hj' : j < 27 := fixedAddress_lt (by rw [hj]; simp)
  have key : ∀ i < 27, ∀ j < 27, fixedAddress i ≠ none → fixedAddress i = fixedAddress j → i = j := by
    decide
  exact key i hi' j hj' (by rw [hi]; simp) (by rw [hi, hj])

lemma rowAt_of_le {t : List Bytes} {i : ℕ} (h : t.length ≤ i) : rowAt t i = [] := by
  simp [rowAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma rowAt_ne_nil_lt {t : List Bytes} {i : ℕ} (h : rowAt t i ≠ []) : i < t.length := by
  by_contra hc
  exact h (rowAt_of_le (by omega))

lemma rowAt_map_range {n : ℕ} {f : ℕ → Bytes} {i : ℕ} :
    rowAt ((List.range n).map f) i = if i < n then f i else [] := by
  split_ifs with h
  · simp [rowAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  · exact rowAt_of_le (by simp; omega)

lemma rowAt_append_nil {t : List Bytes} (i : ℕ) : rowAt (t ++ [[]]) i = rowAt t i := by
  by_cases h : i < t.length
  · simp [rowAt, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [rowAt_of_le (t := t) (by omega)]
    by_cases h' : i = t.length
    · subst h'; simp [rowAt]
    · exact rowAt_of_le (by simp; omega)

/-- Hashes equal: the values are equal or a named clash. -/
lemma eq_or_clash {H : Type} {kec : Bytes → H} {x y : Bytes} (h : kec x = kec y) :
    x = y ∨ KeccakClash kec x y := by
  by_cases hxy : x = y
  · exact Or.inl hxy
  · exact Or.inr ⟨hxy, h⟩

/-- `_l2TableChanged` hashes a row past the end as the empty row, which is `rowAt`'s reading. -/
lemma tableRowHash_eq {H : Type} (kec : Bytes → H) (t : List Bytes) (i : ℕ) :
    tableRowHash kec t i = kec (rowAt t i) := by
  unfold tableRowHash
  split_ifs with h
  · rfl
  · rw [rowAt_of_le (by omega)]

lemma l2TableChanged_false {H : Type} [DecidableEq H] {kec : Bytes → H} {fromT newT : List Bytes} :
    l2TableChanged kec fromT newT = false ↔
      ∀ i, i < max fromT.length newT.length → kec (rowAt fromT i) = kec (rowAt newT i) := by
  unfold l2TableChanged
  simp only [List.any_eq_false, List.mem_range, decide_eq_true_eq, tableRowHash_eq, ne_eq,
    not_not]

/-! ## `changedL2Rows` -/

lemma changedL2RowsReverts_false {fromT newT : List Bytes} :
    changedL2RowsReverts fromT newT = false ↔
      fromT.length ≤ newT.length ∧
        ∀ i, rowAt newT i = [] → i < fromT.length → rowAt fromT i = [] := by
  unfold changedL2RowsReverts
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt, List.any_eq_false,
    List.mem_range, decide_eq_true_eq, not_and, not_not]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i hi hlt => ?_⟩
    exact h2 i (by omega) hi hlt
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i _ hi hlt => h2 i hi hlt⟩

/-- What `changedL2Rows` returns, exactly. -/
lemma changedL2Rows_some {H : Type} [DecidableEq H] {kec : Bytes → H}
    {fromT newT changed : List Bytes} :
    changedL2Rows kec fromT newT = some changed ↔
      (fromT.length ≤ newT.length ∧
        ∀ i, rowAt newT i = [] → i < fromT.length → rowAt fromT i = []) ∧
      changed = (List.range newT.length).map
        (fun i => if RowChanged kec fromT newT i then rowAt newT i else []) := by
  unfold changedL2Rows
  rw [← changedL2RowsReverts_false]
  cases changedL2RowsReverts fromT newT <;> simp [eq_comm]

lemma rowAt_changed {H : Type} [DecidableEq H] {kec : Bytes → H} {fromT newT changed : List Bytes}
    (h : changedL2Rows kec fromT newT = some changed) (i : ℕ) :
    rowAt changed i = if RowChanged kec fromT newT i then rowAt newT i else [] := by
  rw [(changedL2Rows_some.1 h).2, rowAt_map_range]
  split_ifs with h1 h2 h2
  · rfl
  · rfl
  · exact absurd (rowAt_ne_nil_lt h2.1) h1
  · rfl

lemma rowAt_changed_ne_nil {H : Type} [DecidableEq H] {kec : Bytes → H}
    {fromT newT changed : List Bytes} (h : changedL2Rows kec fromT newT = some changed) (i : ℕ) :
    rowAt changed i ≠ [] ↔ RowChanged kec fromT newT i := by
  rw [rowAt_changed h]
  split_ifs with hc
  · exact ⟨fun _ => hc, fun _ => hc.1⟩
  · simp [hc]

lemma mem_changed_ne_nil {H : Type} [DecidableEq H] {kec : Bytes → H}
    {fromT newT changed : List Bytes} (h : changedL2Rows kec fromT newT = some changed) :
    (∃ x ∈ changed, x ≠ []) ↔ ∃ i, RowChanged kec fromT newT i := by
  rw [(changedL2Rows_some.1 h).2]
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨x, ⟨i, _, rfl⟩, hx⟩
    split_ifs at hx with hc
    · exact ⟨i, hc⟩
    · exact absurd rfl hx
  · rintro ⟨i, hc⟩
    exact ⟨_, ⟨i, rowAt_ne_nil_lt hc.1, rfl⟩, by simp [hc]⟩

/-! ## `deriveL2DeploymentsFromTable` -/

lemma deriveReverts_false {rows : List Bytes} :
    deriveReverts rows = false ↔ ∀ i, rowAt rows i ≠ [] → fixedAddress i ≠ none := by
  unfold deriveReverts
  simp only [List.any_eq_false, List.mem_range, decide_eq_true_eq, not_and, ne_eq]
  constructor
  · intro h i hi
    exact h i (rowAt_ne_nil_lt hi) hi
  · intro h i _ hi
    exact h i hi

lemma derive_some {rows : List Bytes} {sh : Bytes} {ds : List ProxyDeployment} :
    deriveL2DeploymentsFromTable rows sh = some ds ↔
      (∀ i, rowAt rows i ≠ [] → fixedAddress i ≠ none) ∧ ds = deriveOut rows sh := by
  unfold deriveL2DeploymentsFromTable
  rw [← deriveReverts_false]
  cases deriveReverts rows <;> simp [eq_comm]

lemma mem_deriveOut {rows : List Bytes} {sh : Bytes} {d : ProxyDeployment} :
    d ∈ deriveOut rows sh ↔
      ∃ i a, rowAt rows i ≠ [] ∧ fixedAddress i = some a ∧ d = ⟨a, rowAt rows i, sh⟩ := by
  unfold deriveOut
  simp only [List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨i, _, hi⟩
    split_ifs at hi with he
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hi
    exact ⟨i, a, he, ha, rfl⟩
  · rintro ⟨i, a, he, ha, rfl⟩
    exact ⟨i, rowAt_ne_nil_lt he, by simp [he, ha]⟩

lemma deriveOut_addrs_nodup {rows : List Bytes} {sh : Bytes} :
    ((deriveOut rows sh).map ProxyDeployment.addr).Nodup := by
  unfold deriveOut
  rw [List.map_filterMap]
  refine List.Nodup.filterMap ?_ List.nodup_range
  intro i j a hi hj
  simp only [Option.mem_def] at hi hj
  split_ifs at hi hj with h1 h2 h2
  · simp at hi
  · simp at hi
  · simp at hj
  · simp only [Option.map_map, Function.comp_def, Option.map_id'] at hi hj
    exact fixedAddress_inj hi hj

lemma deriveOut_eq_nil {rows : List Bytes} {sh : Bytes} :
    deriveOut rows sh = [] ↔ ∀ i a, rowAt rows i ≠ [] → fixedAddress i ≠ some a := by
  constructor
  · intro h i a he ha
    have : (⟨a, rowAt rows i, sh⟩ : ProxyDeployment) ∈ deriveOut rows sh :=
      mem_deriveOut.2 ⟨i, a, he, ha, rfl⟩
    rw [h] at this
    simp at this
  · intro h
    apply List.eq_nil_iff_forall_not_mem.2
    intro d hd
    obtain ⟨i, a, he, ha, _⟩ := mem_deriveOut.1 hd
    exact h i a he ha

/-! ## `L2PlanLib.build` -/

lemma buildPlan_some {rnd : Bytes → L2Addr} {derived : List ProxyDeployment} {a : AuthoredL2}
    {p : L2Plan} (h : buildPlan rnd derived a = some p) :
    p.deployments = derived.map Deployment.proxy ++
        (if a.delegate ≠ [] then [Deployment.unsafeForce (rnd a.delegate) a.delegate] else []) ++
        a.extras.map (fun x => Deployment.unsafeForce (rnd x) x) ∧
      p.delegateTo = (if a.delegate ≠ [] then rnd a.delegate else 0) ∧ p.composer = a.composer ∧
      (a.delegate = [] → derived = [] ∧ a.extras = [] ∧ a.composer = 0) ∧
      (a.delegate ≠ [] → a.composer ≠ 0) := by
  unfold buildPlan at h
  by_cases hd : a.delegate = []
  · simp [hd] at h
    obtain ⟨_, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ := h
    simp [hd, h1, h2, h3]
  · simp [hd] at h
    obtain ⟨_, _, h3, rfl⟩ := h
    simp [hd, h3]

lemma filterMap_proxyPart_build {rnd : Bytes → L2Addr} {derived : List ProxyDeployment}
    {a : AuthoredL2} {p : L2Plan} (h : buildPlan rnd derived a = some p) :
    p.deployments.filterMap Deployment.proxyPart = derived := by
  rw [(buildPlan_some h).1]
  simp only [List.filterMap_append]
  have h1 : (derived.map Deployment.proxy).filterMap Deployment.proxyPart = derived := by
    rw [List.filterMap_map]
    simp [Function.comp_def, Deployment.proxyPart]
  have h2 : (a.extras.map (fun x => Deployment.unsafeForce (rnd x) x)).filterMap
      Deployment.proxyPart = [] := by
    rw [List.filterMap_map]
    simp [Function.comp_def, Deployment.proxyPart]
  rw [h1, h2]
  split_ifs <;> simp [Deployment.proxyPart]

lemma proxy_mem_build {rnd : Bytes → L2Addr} {derived : List ProxyDeployment} {a : AuthoredL2}
    {p : L2Plan} (h : buildPlan rnd derived a = some p) (d : ProxyDeployment) :
    Deployment.proxy d ∈ p.deployments ↔ d ∈ derived := by
  rw [← filterMap_proxyPart_build h, List.mem_filterMap]
  constructor
  · intro hd
    exact ⟨_, hd, rfl⟩
  · rintro ⟨x, hx, hpx⟩
    cases x with
    | proxy d' =>
        simp only [Deployment.proxyPart, Option.some.injEq] at hpx
        subst hpx
        exact hx
    | unsafeForce _ _ => simp [Deployment.proxyPart] at hpx

lemma hasL2Side_build {rnd : Bytes → L2Addr} {derived : List ProxyDeployment} {a : AuthoredL2}
    {p : L2Plan} (h : buildPlan rnd derived a = some p) :
    hasL2Side p = true ↔ a.delegate ≠ [] := by
  obtain ⟨hdep, _, _, hnone, _⟩ := buildPlan_some h
  unfold hasL2Side
  rw [hdep]
  by_cases hd : a.delegate = []
  · obtain ⟨h1, h2, _⟩ := hnone hd
    simp [hd, h1, h2]
  · simp [hd]

/-! ## The constructor -/

lemma ctmTransitionL2_some {H : Type} [DecidableEq H] {kec : Bytes → H} {rnd : Bytes → L2Addr}
    {vFrom vNew : ℕ} {Rf Rn : ReleaseL2} {e : EdgeInput} {p : L2Plan}
    (h : ctmTransitionL2 kec rnd vFrom vNew Rf Rn e = some p) :
    ∃ changed derived, changedL2Rows kec Rf.table Rn.table = some changed ∧
      deriveL2DeploymentsFromTable changed Rn.shell = some derived ∧
      buildPlan rnd derived e.authored = some p ∧
      ValidEdge vFrom vNew e.deadline e.timestamp (hasL2Side p) ∧
      (hasL2Side p = true ∨ L2StateKept kec Rf Rn) := by
  unfold ctmTransitionL2 derivedPlan at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨p', ⟨changed, hc, derived, hd, hb⟩, hif⟩ := h
  split_ifs at hif with hcond
  cases hif
  exact ⟨changed, derived, hc, hd, hb, hcond.1, hcond.2⟩

/-- The derived system-proxy deployments of a successful construction. -/
lemma ctm_derived {H : Type} [DecidableEq H] {kec : Bytes → H} {rnd : Bytes → L2Addr}
    {vFrom vNew : ℕ} {Rf Rn : ReleaseL2} {e : EdgeInput} {p : L2Plan}
    (h : ctmTransitionL2 kec rnd vFrom vNew Rf Rn e = some p) :
    (∀ d, Deployment.proxy d ∈ p.deployments ↔
      ∃ i a, fixedAddress i = some a ∧ RowChanged kec Rf.table Rn.table i ∧
        d = ⟨a, rowAt Rn.table i, Rn.shell⟩) ∧
    ((p.deployments.filterMap Deployment.proxyPart).map ProxyDeployment.addr).Nodup ∧
    (∀ i, RowChanged kec Rf.table Rn.table i → fixedAddress i ≠ none) := by
  obtain ⟨changed, derived, hc, hd, hb, _, _⟩ := ctmTransitionL2_some h
  obtain ⟨hfix, rfl⟩ := derive_some.1 hd
  refine ⟨fun d => ?_, ?_, fun i hi => hfix i ((rowAt_changed_ne_nil hc i).2 hi)⟩
  · rw [proxy_mem_build hb, mem_deriveOut]
    constructor
    · rintro ⟨i, a, he, ha, rfl⟩
      have hrc := (rowAt_changed_ne_nil hc i).1 he
      refine ⟨i, a, ha, hrc, ?_⟩
      rw [rowAt_changed hc i, ite_eq_left hrc]
    · rintro ⟨i, a, ha, hrc, rfl⟩
      refine ⟨i, a, (rowAt_changed_ne_nil hc i).2 hrc, ha, ?_⟩
      rw [rowAt_changed hc i, ite_eq_left hrc]
  · rw [filterMap_proxyPart_build hb]
    exact deriveOut_addrs_nodup

/-- A new or changed row puts a deployment into the plan, so it needs a delegate. -/
lemma ctm_changed_needs_delegate {H : Type} [DecidableEq H] {kec : Bytes → H}
    {rnd : Bytes → L2Addr} {vFrom vNew : ℕ} {Rf Rn : ReleaseL2} {e : EdgeInput} {p : L2Plan}
    (h : ctmTransitionL2 kec rnd vFrom vNew Rf Rn e = some p) {i : ℕ}
    (hi : RowChanged kec Rf.table Rn.table i) : e.authored.delegate ≠ [] := by
  obtain ⟨changed, derived, hc, hd, hb, _, _⟩ := ctmTransitionL2_some h
  obtain ⟨hfix, rfl⟩ := derive_some.1 hd
  intro hdel
  have hnil := ((buildPlan_some hb).2.2.2.1 hdel).1
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (hfix i ((rowAt_changed_ne_nil hc i).2 hi))
  exact deriveOut_eq_nil.1 hnil i a ((rowAt_changed_ne_nil hc i).2 hi) ha

/-! ## What a successful construction deploys -/

theorem TransitionDeploysExactlyTheChangedRows :
    Properties.TransitionDeploysExactlyTheChangedRows := by
  intro H _ kec rnd vFrom vNew Rf Rn e p h
  exact ctm_derived h

theorem HasL2SideIffDelegate : Properties.HasL2SideIffDelegate := by
  intro H _ kec rnd vFrom vNew Rf Rn e p h
  obtain ⟨changed, derived, hc, hd, hb, _, _⟩ := ctmTransitionL2_some h
  have hside := hasL2Side_build hb
  obtain ⟨_, _, _, hnone, hsome⟩ := buildPlan_some hb
  have hch : (∃ i, RowChanged kec Rf.table Rn.table i) → e.authored.delegate ≠ [] :=
    fun ⟨i, hi⟩ => ctm_changed_needs_delegate h hi
  refine ⟨hside, ?_, hch, ?_, ?_⟩
  · rw [hside]
    constructor
    · exact Or.inr
    · rintro (hi | hi)
      · exact hch hi
      · exact hi
  · intro hx hdel
    exact hx (hnone hdel).2.1
  · constructor
    · intro hc0 hdel
      exact hc0 (hnone hdel).2.2
    · exact hsome

theorem L1OnlyEdgeKeepsTheL2Description : Properties.L1OnlyEdgeKeepsTheL2Description := by
  intro H _ kec rnd vFrom vNew Rf Rn e p h hside
  obtain ⟨changed, derived, hc, hd, hb, _, hkept⟩ := ctmTransitionL2_some h
  have hdel : e.authored.delegate = [] := by
    by_contra hne
    rw [(hasL2Side_build hb).2 hne] at hside
    exact Bool.noConfusion hside
  obtain ⟨hdep, hto, hcomp, hnone, _⟩ := buildPlan_some hb
  obtain ⟨hder, hext, hc0⟩ := hnone hdel
  have hkept' : L2StateKept kec Rf Rn := by
    rcases hkept with hk | hk
    · rw [hside] at hk; exact absurd hk (by decide)
    · exact hk
  obtain ⟨htab, hsh, hbl, hgen⟩ := hkept'
  obtain ⟨⟨hlen, hrem⟩, _⟩ := changedL2Rows_some.1 hc
  have hnochange : ∀ i, ¬ RowChanged kec Rf.table Rn.table i :=
    fun i hi => ctm_changed_needs_delegate h hi hdel
  refine ⟨?_, htab, hlen, fun i => ?_, eq_or_clash hsh, eq_or_clash hbl, hgen⟩
  · cases p with
    | mk deps dto comp =>
      simp only at hdep hto hcomp
      subst hdep hto hcomp
      simp [hder, hext, hdel, hc0]
  · by_cases hn : rowAt Rn.table i = []
    · left
      rw [hn]
      by_cases hl : i < Rf.table.length
      · exact hrem i hn hl
      · exact rowAt_of_le (by omega)
    · have hi := hnochange i
      simp only [RowChanged, not_and, not_or, ne_eq, not_not] at hi
      obtain ⟨_, heq⟩ := hi hn
      exact eq_or_clash heq

theorem PatchEdgeHasNoL2Side : Properties.PatchEdgeHasNoL2Side := by
  intro H _ kec rnd vFrom vNew Rf Rn e p h hminor
  obtain ⟨changed, derived, hc, hd, hb, hvalid, _⟩ := ctmTransitionL2_some h
  have hside : hasL2Side p = false := by
    cases hs : hasL2Side p
    · rfl
    · exact absurd ⟨hminor, hs⟩ hvalid.2.2.2.2.2.2.2.2
  have hdel : e.authored.delegate = [] := by
    by_contra hne
    rw [(hasL2Side_build hb).2 hne] at hside
    exact Bool.noConfusion hside
  exact ⟨hside, hdel, fun ⟨i, hi⟩ => ctm_changed_needs_delegate h hi hdel⟩

/-! ## The two table comparisons -/

theorem TableComparisonsAgree : Properties.TableComparisonsAgree := by
  intro H _ kec fromT newT changed hc
  obtain ⟨⟨hlen, hrem⟩, _⟩ := changedL2Rows_some.1 hc
  have hmax : max fromT.length newT.length = newT.length := max_eq_right hlen
  constructor
  · intro hall
    have hno : ∀ i, ¬ RowChanged kec fromT newT i := by
      intro i hi
      obtain ⟨x, hx, hne⟩ := (mem_changed_ne_nil hc).2 ⟨i, hi⟩
      exact hne (hall x hx)
    rw [l2TableChanged_false]
    intro i _
    by_cases hn : rowAt newT i = []
    · rw [hn]
      by_cases hl : i < fromT.length
      · rw [hrem i hn hl]
      · rw [rowAt_of_le (t := fromT) (by omega)]
    · have hi := hno i
      simp only [RowChanged, not_and, not_or, ne_eq, not_not] at hi
      exact (hi hn).2
  · intro hfalse
    rw [l2TableChanged_false, hmax] at hfalse
    by_cases hall : ∀ x ∈ changed, x = []
    · exact Or.inl hall
    · right
      push Not at hall
      obtain ⟨i, hi⟩ := (mem_changed_ne_nil hc).1 hall
      have hlt : i < newT.length := rowAt_ne_nil_lt hi.1
      have heq := hfalse i hlt
      rcases hi.2 with hge | hne
      · refine ⟨i, hge, hlt, hi.1, ?_⟩
        rw [← heq, rowAt_of_le hge]
      · exact absurd heq hne

/-- A departing table that agrees with the target member by member, with no authored input:
the derived plan is empty, for every hash. -/
lemma derivedPlan_of_rows_agree {H : Type} [DecidableEq H] (kec : Bytes → H)
    (rnd : Bytes → L2Addr) {Rf Rn : ReleaseL2} {a : AuthoredL2}
    (hlen : Rf.table.length ≤ Rn.table.length) (hrows : ∀ i, rowAt Rf.table i = rowAt Rn.table i)
    (hd : a.delegate = []) (hx : a.extras = []) (hc : a.composer = 0) :
    derivedPlan kec rnd Rf Rn a = some ⟨[], 0, 0⟩ := by
  have hno : ∀ i, ¬ RowChanged kec Rf.table Rn.table i := by
    intro i hi
    rcases hi.2 with hge | hne
    · exact hi.1 (by rw [← hrows i]; exact rowAt_of_le hge)
    · exact hne (by rw [hrows i])
  have hch : changedL2Rows kec Rf.table Rn.table =
      some ((List.range Rn.table.length).map (fun _ => [])) := by
    rw [changedL2Rows_some]
    refine ⟨⟨hlen, fun i hn _ => by rw [hrows i]; exact hn⟩, ?_⟩
    congr 1
    funext i
    rw [ite_eq_right (hno i)]
  have hder : deriveL2DeploymentsFromTable ((List.range Rn.table.length).map (fun _ => []))
      Rn.shell = some [] := by
    rw [derive_some]
    have hz : ∀ i, rowAt ((List.range Rn.table.length).map (fun _ => ([] : Bytes))) i = [] := by
      intro i; rw [rowAt_map_range]; split_ifs <;> rfl
    refine ⟨fun i hi => absurd (hz i) hi, ?_⟩
    symm
    exact deriveOut_eq_nil.2 (fun i a hi => absurd (hz i) hi)
  unfold derivedPlan
  rw [hch, Option.bind_some, hder, Option.bind_some]
  unfold buildPlan
  simp [hd, hx, hc]

/-! ## Boundaries -/

theorem NonemptyRowStaysNonempty : Properties.NonemptyRowStaysNonempty := by
  intro H _ kec rnd vFrom vNew Rf Rn e p h i hi hn
  obtain ⟨changed, derived, hc, _, _, _, _⟩ := ctmTransitionL2_some h
  obtain ⟨⟨_, hrem⟩, _⟩ := changedL2Rows_some.1 hc
  exact hi (hrem i hn (rowAt_ne_nil_lt hi))

theorem NoFixedAddressRowCannotChange : Properties.NoFixedAddressRowCannotChange := by
  intro H _ kec rnd vFrom vNew Rf Rn e i hfix hch
  cases h : ctmTransitionL2 kec rnd vFrom vNew Rf Rn e with
  | none => rfl
  | some p => exact absurd hfix ((ctm_derived h).2.2 i hch)

theorem NoFixedAddressRowIsFrozen : Properties.NoFixedAddressRowIsFrozen := by
  intro H _ kec rnd vFrom vNew Rf Rn e p h i hfix hi
  have hn := NonemptyRowStaysNonempty kec rnd vFrom vNew Rf Rn e p h i hi
  have hno : ¬ RowChanged kec Rf.table Rn.table i := fun hch => (ctm_derived h).2.2 i hch hfix
  simp only [RowChanged, not_and, not_or, ne_eq, not_not] at hno
  obtain ⟨_, heq⟩ := hno hn
  refine ⟨hn, ?_⟩
  rcases eq_or_clash heq with h' | h'
  · exact Or.inl h'.symm
  · exact Or.inr h'

theorem BootstrapOntoNoFixedAddressRowReverts :
    Properties.BootstrapOntoNoFixedAddressRowReverts := by
  intro rnd R a i hfix hi
  have hrev : deriveReverts R.table = true := by
    cases hr : deriveReverts R.table
    · exact absurd hfix (deriveReverts_false.1 hr i hi)
    · rfl
  unfold bootstrapPlanL2 deriveL2DeploymentsFromTable
  rw [hrev]
  rfl

/-! ## Witnesses -/

theorem EmptyRowClashSplitsTheComparisons : Properties.EmptyRowClashSplitsTheComparisons :=
  ⟨wClashKec, wRnd, 2 ^ 32, 2 * 2 ^ 32, wRel [wDesc 1], wRel [wDesc 1, wDesc 7], wMinorEdge,
    ⟨[.proxy ⟨0x10003, wDesc 7, wDesc 50⟩, .unsafeForce 0x1234 (wDesc 90)], 0x1234, 77⟩,
    by decide, by decide, ⟨⟨0x10003, wDesc 7, wDesc 50⟩, by decide⟩, ⟨1, by decide, by decide, by decide⟩⟩

theorem AppendedEmptyRowKeepsAnL1OnlyEdge : Properties.AppendedEmptyRowKeepsAnL1OnlyEdge := by
  have hrows : ∀ i, rowAt (wRel [wDesc 1]).table i = rowAt (wRel ([wDesc 1] ++ [[]])).table i :=
    fun i => (rowAt_append_nil i).symm
  have hplan : ∀ {H : Type} [DecidableEq H] (kec : Bytes → H),
      derivedPlan kec wRnd (wRel [wDesc 1]) (wRel ([wDesc 1] ++ [[]])) wL1OnlyEdge.authored =
        some ⟨[], 0, 0⟩ :=
    fun kec => derivedPlan_of_rows_agree kec wRnd (by decide) hrows rfl rfl rfl
  refine ⟨wRnd, 2 ^ 32, 2 ^ 32 + 1, wRel [wDesc 1], wRel ([wDesc 1] ++ [[]]), wL1OnlyEdge,
    ⟨[], 0, 0⟩, by decide, rfl, by decide, rfl, ?_, ?_⟩
  · intro H _ kec
    unfold ctmTransitionL2
    rw [hplan kec, Option.bind_some]
    have hkept : L2StateKept kec (wRel [wDesc 1]) (wRel ([wDesc 1] ++ [[]])) :=
      ⟨l2TableChanged_false.2 (fun i _ => by rw [hrows i]), rfl, rfl, rfl⟩
    exact ite_eq_left ⟨by decide, Or.inr hkept⟩
  · intro H _ kec encT hinj
    unfold ctmTransitionL2PreFix
    rw [hplan kec, Option.bind_some]
    apply ite_eq_right
    rintro ⟨_, hk | hk⟩
    · exact absurd hk (by decide)
    · exact absurd (hinj hk.1) (by decide)

theorem FrozenRowWitness : Properties.FrozenRowWitness := by
  refine ⟨wEnc, wRnd, wRel27 (wDesc 1) (wDesc 14), wRel27 (wDesc 2) (wDesc 14),
    wRel27 (wDesc 1) (wDesc 15), wMinorEdge,
    ⟨[.proxy ⟨0x10002, wDesc 2, wDesc 50⟩, .unsafeForce 0x1234 (wDesc 90)], 0x1234, 77⟩,
    ?_, ?_, ?_, rfl, by decide, by decide, rfl, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · unfold ReleaseL2Accepted; decide
  · unfold ReleaseL2Accepted; decide
  · unfold ReleaseL2Accepted; decide
  · intro i hi
    simp only [wRel27, wTable27, rowAt, List.getD_eq_getElem?_getD,
      List.getElem?_set_ne (Ne.symm hi)]
  · intro vFrom vNew e'
    exact NoFixedAddressRowCannotChange _ _ vFrom vNew _ _ e' 14 rfl (by decide)
  · intro a
    exact BootstrapOntoNoFixedAddressRowReverts _ _ a 14 rfl (by decide)

theorem L2DerivationWitness : Properties.L2DerivationWitness :=
  ⟨wRnd, wRel [wDesc 1, wDesc 2], wRel [wDesc 3, wDesc 2, wDesc 4], wRel [wDesc 3, wDesc 2, wDesc 4],
    wMinorEdge, wL1OnlyEdge,
    ⟨[.proxy ⟨0x10002, wDesc 3, wDesc 50⟩, .proxy ⟨0x10004, wDesc 4, wDesc 50⟩,
      .unsafeForce 0x1234 (wDesc 90)], 0x1234, 77⟩,
    ⟨[], 0, 0⟩, [wDesc 3, [], wDesc 4], [[], [], []],
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, ⟨wDesc 3, by decide, by decide⟩, by decide, by decide⟩

end Contracts.ChainTypeManager.L2Tables
