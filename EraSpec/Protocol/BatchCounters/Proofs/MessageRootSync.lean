import EraSpec.Protocol.BatchCounters.Properties.MessageRootSync

/-!
# Proofs: the message root's counter tracks each diamond's executed count

The append loop is analysed once (`appendAll_*`): it keeps registration, advances the counter
by the number of batches, writes the batches' roots in order at consecutive numbers after the
old counter, and succeeds whenever those numbers follow the counter, the slots are empty and
the roots are nonzero. Everything else is a case analysis over `HubStep`.
-/

namespace Contracts.BatchCounters

/-! ## Point updates -/

@[simp] lemma upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (v : β) :
    upd f a v a = v := by simp [upd]

lemma upd_ne {α β : Type} [DecidableEq α] (f : α → β) {a x : α} (v : β) (h : x ≠ a) :
    upd f a v x = f x := by simp [upd, h]

lemma upd_self {α β : Type} [DecidableEq α] (f : α → β) (a : α) : upd f a (f a) = f := by
  funext x; by_cases h : x = a <;> simp [upd, h]

/-! ## `writeRoots` -/

lemma writeRoots_of_not_mem (f : ℕ → Word) (infos : List BatchInfo) (n : ℕ)
    (h : ∀ b ∈ infos, b.batchNumber ≠ n) : writeRoots f infos n = f n := by
  induction infos generalizing f with
  | nil => rfl
  | cons b bs ih =>
    simp only [writeRoots]
    rw [ih _ (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))]
    exact upd_ne _ _ (Ne.symm (h b (List.mem_cons_self ..)))

/-- Two maps written by the same list agree at `n`, or both are unchanged at `n`. -/
lemma writeRoots_agree (f g : ℕ → Word) (infos : List BatchInfo) (n : ℕ) :
    (writeRoots f infos n = f n ∧ writeRoots g infos n = g n) ∨
      writeRoots f infos n = writeRoots g infos n := by
  induction infos generalizing f g with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons b bs ih =>
    simp only [writeRoots]
    rcases ih (upd f b.batchNumber b.logsRoot) (upd g b.batchNumber b.logsRoot) with
      ⟨h1, h2⟩ | h
    · by_cases hn : n = b.batchNumber
      · right; rw [h1, h2, hn, upd_same, upd_same]
      · left; rw [h1, h2, upd_ne _ _ hn, upd_ne _ _ hn]; exact ⟨rfl, rfl⟩
    · exact Or.inr h

/-- With distinct batch numbers, the written map holds each batch's own root. -/
lemma writeRoots_mem (f : ℕ → Word) (infos : List BatchInfo)
    (hnd : (infos.map BatchInfo.batchNumber).Nodup) (b : BatchInfo) (hb : b ∈ infos) :
    writeRoots f infos b.batchNumber = b.logsRoot := by
  induction infos generalizing f with
  | nil => simp at hb
  | cons b' bs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [writeRoots]
    rcases List.mem_cons.1 hb with rfl | hb
    · rw [writeRoots_of_not_mem]
      · exact upd_same _ _ _
      · intro x hx hxn; exact hnd.1 ⟨x, hx, hxn⟩
    · exact ih _ hnd.2 hb

/-! ## `appendAll` -/

lemma recordRoot_some {m m' : MsgRoot} {c n : ℕ} {r : Word} (h : recordRoot m c n r = some m') :
    m.reg c = true ∧ r ≠ 0 ∧ m.roots c n = 0 ∧ n = m.cur c + 1 ∧
      m' = { m with roots := upd m.roots c (upd (m.roots c) n r), cur := upd m.cur c n } := by
  unfold recordRoot at h
  split_ifs at h with hg
  · exact ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2, (Option.some.inj h).symm⟩

lemma appendAll_cons {m m' : MsgRoot} {c : ChainId} {b : BatchInfo} {bs : List BatchInfo}
    (h : appendAll m c (b :: bs) = some m') :
    ∃ m₁, recordRoot m c b.batchNumber b.logsRoot = some m₁ ∧ appendAll m₁ c bs = some m' := by
  simp only [appendAll] at h
  split at h
  · exact absurd h (by simp)
  · exact ⟨_, by assumption, h⟩

/-- What a successful append loop does. -/
lemma appendAll_spec {m m' : MsgRoot} {c : ChainId} {infos : List BatchInfo}
    (h : appendAll m c infos = some m') :
    m'.reg = m.reg ∧
      m'.cur = upd m.cur c (m.cur c + infos.length) ∧
      (∀ c', c' ≠ c → m'.roots c' = m.roots c') ∧
      m'.roots c = writeRoots (m.roots c) infos ∧
      infos.map BatchInfo.batchNumber = List.range' (m.cur c + 1) infos.length ∧
      (∀ b ∈ infos, b.logsRoot ≠ 0) ∧
      (infos ≠ [] → m.reg c = true) ∧
      (∀ n, m.roots c n ≠ 0 → m'.roots c n = m.roots c n) := by
  induction infos generalizing m with
  | nil =>
    simp only [appendAll, Option.some.injEq] at h
    subst h
    refine ⟨rfl, ?_, fun _ _ => rfl, rfl, rfl, by simp, by simp, fun _ _ => rfl⟩
    simp [upd_self]
  | cons b bs ih =>
    obtain ⟨m₁, h1, h2⟩ := appendAll_cons h
    obtain ⟨hreg, hr, hz, hn, rfl⟩ := recordRoot_some h1
    obtain ⟨ireg, icur, iother, iroots, inums, inz, _, iwo⟩ := ih h2
    refine ⟨ireg, ?_, ?_, ?_, ?_, ?_, fun _ => hreg, ?_⟩
    · rw [icur]; funext x
      by_cases hx : x = c
      · subst hx; simp [upd, hn]; omega
      · simp [upd, hx]
    · intro c' hc'; rw [iother c' hc']; exact upd_ne _ _ hc'
    · rw [iroots]; simp [writeRoots, hn]
    · simp only [List.map_cons, List.length_cons]
      rw [inums, List.range'_succ]
      simp [upd, hn]
    · intro b' hb'
      rcases List.mem_cons.1 hb' with rfl | hb'
      · exact hr
      · exact inz b' hb'
    · intro n hne
      have hnb : n ≠ b.batchNumber := fun he => hne (he ▸ hz)
      have hne' : (upd m.roots c (upd (m.roots c) b.batchNumber b.logsRoot)) c n ≠ 0 := by
        simp only [upd_same]; rw [upd_ne _ _ hnb]; exact hne
      rw [iwo n hne']; simp only [upd_same]; exact upd_ne _ _ hnb

/-- The append loop succeeds when the batch numbers follow the counter, the slots after the
counter are empty, and every root is nonzero. -/
lemma appendAll_some (m : MsgRoot) (c : ChainId) (infos : List BatchInfo)
    (hreg : m.reg c = true) (hfr : ∀ n, m.cur c < n → m.roots c n = 0)
    (hnums : infos.map BatchInfo.batchNumber = List.range' (m.cur c + 1) infos.length)
    (hnz : ∀ b ∈ infos, b.logsRoot ≠ 0) : ∃ m', appendAll m c infos = some m' := by
  induction infos generalizing m with
  | nil => exact ⟨m, rfl⟩
  | cons b bs ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hnums
    have hrec : recordRoot m c b.batchNumber b.logsRoot =
        some { m with roots := upd m.roots c (upd (m.roots c) b.batchNumber b.logsRoot),
                      cur := upd m.cur c b.batchNumber } := by
      have hcond : m.reg c = true ∧ b.logsRoot ≠ 0 ∧ m.roots c b.batchNumber = 0 ∧
          b.batchNumber = m.cur c + 1 :=
        ⟨hreg, hnz b (List.mem_cons_self ..), hfr _ (by omega), hnums.1⟩
      unfold recordRoot
      exact ite_eq_left_of_eq_true _ _ (eq_true hcond)
    obtain ⟨m', hm'⟩ := ih { m with roots := upd m.roots c (upd (m.roots c) b.batchNumber b.logsRoot),
                                      cur := upd m.cur c b.batchNumber }
      hreg
      (by
        intro n hn
        simp only [upd_same] at hn ⊢
        rw [upd_ne _ _ (by omega)]
        exact hfr n (by omega))
      (by simp only [upd_same]; rw [hnums.1]; exact hnums.2)
      (fun b' hb' => hnz b' (List.mem_cons_of_mem _ hb'))
    refine ⟨m', ?_⟩
    simp only [appendAll, hrec]
    exact hm'

lemma appendAll_zero_root (m : MsgRoot) (c : ChainId) (infos : List BatchInfo)
    (h : ∃ b ∈ infos, b.logsRoot = 0) : appendAll m c infos = none := by
  cases hA : appendAll m c infos with
  | none => rfl
  | some m' =>
    obtain ⟨b, hb, hz⟩ := h
    exact absurd hz ((appendAll_spec hA).2.2.2.2.2.1 b hb)

lemma mem_range'_bound {s k n : ℕ} (h : n ∈ List.range' s k) : s ≤ n ∧ n < s + k := by
  rw [List.mem_range'_1] at h; exact h

/-! ## The layer invariant -/

lemma HubInv.reg_of_chain {h : Hub} (hI : HubInv h) {c : ChainId} {d : Diamond}
    (hc : h.chains c = some d) : h.mr.reg c = true :=
  (hI.regIff c).2 (by simp [hc])

/-- A step that rewrites one registered diamond without touching its logs roots or the message
root keeps the invariant. -/
lemma inv_update_diamond {h : Hub} {c : ChainId} {d d' : Diamond} (hI : HubInv h)
    (hc : h.chains c = some d) (hl : d'.logsRoot = d.logsRoot) :
    HubInv { h with chains := upd h.chains c (some d') } := by
  refine ⟨fun x => ?_, hI.unregZero, hI.frontier, fun x e n he hne => ?_⟩
  · by_cases hx : x = c
    · subst hx; simp [hI.reg_of_chain hc]
    · simp only [upd_ne _ _ hx]; exact hI.regIff x
  · by_cases hx : x = c
    · subst hx; simp only [upd_same, Option.some.injEq] at he; subst he
      rw [hl]; exact hI.rootsAgree x d n hc hne
    · simp only [upd_ne _ _ hx] at he; exact hI.rootsAgree x e n he hne

theorem HubStepPreservesInv : Properties.HubStepPreservesInv := by
  intro cfg h h' l hI hs
  cases hs with
  | @createChain c gh gr g _ hnone hreg _ _ _ =>
    refine ⟨fun x => ?_, fun x n hx => ?_, fun x n hn => ?_, fun x e n he hne => ?_⟩
    · by_cases hx : x = c
      · subst hx; simp
      · simp only [upd_ne _ _ hx]; exact hI.regIff x
    · have hxc : x ≠ c := by rintro rfl; simp at hx
      simp only [upd_ne _ _ hxc] at hx ⊢; exact hI.unregZero x n hx
    · by_cases hx : x = c
      · subst hx; simp only [upd_same] at hn ⊢
        rw [upd_ne _ _ (by omega)]; exact hI.unregZero x n hreg
      · simp only [upd_ne _ _ hx] at hn ⊢; exact hI.frontier x n hn
    · by_cases hx : x = c
      · subst hx; simp only [upd_same, Option.some.injEq] at he hne ⊢; subst he
        by_cases hn : n = 0
        · subst hn; simp [initDiamond]
        · rw [upd_ne _ _ hn] at hne; exact absurd (hI.unregZero x n hreg) hne
      · simp only [upd_ne _ _ hx] at he hne ⊢; exact hI.rootsAgree x e n he hne
  | @registerDeployed c d _ hnone hreg =>
    refine ⟨fun x => ?_, fun x n hx => ?_, fun x n hn => ?_, fun x e n he hne => ?_⟩
    · by_cases hx : x = c
      · subst hx; simp
      · simp only [upd_ne _ _ hx]; exact hI.regIff x
    · have hxc : x ≠ c := by rintro rfl; simp at hx
      simp only [upd_ne _ _ hxc] at hx; exact hI.unregZero x n hx
    · by_cases hx : x = c
      · subst hx; exact hI.unregZero x n hreg
      · simp only [upd_ne _ _ hx] at hn; exact hI.frontier x n hn
    · by_cases hx : x = c
      · subst hx; exact absurd (hI.unregZero x n hreg) hne
      · simp only [upd_ne _ _ hx] at he; exact hI.rootsAgree x e n he hne
  | commit hc _ _ _ => exact inv_update_diamond hI hc rfl
  | prove hc _ _ _ => exact inv_update_diamond hI hc rfl
  | @execute c d infos m' hc hg hA =>
    obtain ⟨sreg, scur, sother, sroots, snums, _, _, _⟩ := appendAll_spec hA
    have hregc := hI.reg_of_chain hc
    refine ⟨fun x => ?_, fun x n hx => ?_, fun x n hn => ?_, fun x e n he hne => ?_⟩
    · rw [sreg]
      by_cases hx : x = c
      · subst hx; simp [hregc]
      · simp only [upd_ne _ _ hx]; exact hI.regIff x
    · rw [sreg] at hx
      have hxc : x ≠ c := by rintro rfl; rw [hregc] at hx; simp at hx
      rw [sother x hxc]; exact hI.unregZero x n hx
    · by_cases hx : x = c
      · subst hx
        rw [scur, upd_same] at hn
        rw [sroots, writeRoots_of_not_mem]
        · exact hI.frontier x n (by omega)
        · intro b hb hbn
          have hmem : b.batchNumber ∈ infos.map BatchInfo.batchNumber := List.mem_map.2 ⟨b, hb, rfl⟩
          rw [snums] at hmem
          have := mem_range'_bound hmem
          omega
      · rw [scur, upd_ne _ _ hx] at hn; rw [sother x hx]; exact hI.frontier x n hn
    · by_cases hx : x = c
      · subst hx
        simp only [upd_same, Option.some.injEq] at he; subst he
        rw [sroots] at hne ⊢
        simp only [executeEffect]
        rcases writeRoots_agree (h.mr.roots x) d.logsRoot infos n with ⟨h1, h2⟩ | h1
        · rw [h1, h2]; rw [h1] at hne; exact hI.rootsAgree x d n hc hne
        · exact h1
      · simp only [upd_ne _ _ hx] at he; rw [sother x hx] at hne ⊢
        exact hI.rootsAgree x e n he hne
  | revert hc _ _ _ => exact inv_update_diamond hI hc rfl
  | @upgrade c d t hc =>
    refine inv_update_diamond hI hc ?_
    unfold upgradeEffect; split <;> rfl
  | burn _ hc _ _ _ _ => exact inv_update_diamond hI hc rfl
  | @mintExisting c d bn com _ hc hle _ _ =>
    refine ⟨fun x => ?_, hI.unregZero, fun x n hn => ?_, fun x e n he hne => ?_⟩
    · by_cases hx : x = c
      · subst hx; simp [hI.reg_of_chain hc]
      · simp only [upd_ne _ _ hx]; exact hI.regIff x
    · by_cases hx : x = c
      · subst hx; simp only [upd_same] at hn; exact hI.frontier x n (by omega)
      · simp only [upd_ne _ _ hx] at hn; exact hI.frontier x n hn
    · by_cases hx : x = c
      · subst hx; simp only [upd_same, Option.some.injEq] at he; subst he
        exact hI.rootsAgree x d n hc hne
      · simp only [upd_ne _ _ hx] at he; exact hI.rootsAgree x e n he hne
  | @mintNew c bn com gh gr _ _ hnone hreg _ _ =>
    refine ⟨fun x => ?_, fun x n hx => ?_, fun x n hn => ?_, fun x e n he hne => ?_⟩
    · by_cases hx : x = c
      · subst hx; simp
      · simp only [upd_ne _ _ hx]; exact hI.regIff x
    · have hxc : x ≠ c := by rintro rfl; simp at hx
      simp only [upd_ne _ _ hxc] at hx; exact hI.unregZero x n hx
    · by_cases hx : x = c
      · subst hx; exact hI.unregZero x n hreg
      · simp only [upd_ne _ _ hx] at hn; exact hI.frontier x n hn
    · by_cases hx : x = c
      · subst hx; exact absurd (hI.unregZero x n hreg) hne
      · simp only [upd_ne _ _ hx] at he; exact hI.rootsAgree x e n he hne
  | confirmFailure _ hc _ => exact inv_update_diamond hI hc rfl

theorem EmptyHubInv : Properties.EmptyHubInv :=
  ⟨fun _ => by simp [emptyHub], fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ h _ => by
    simp [emptyHub] at h⟩

lemma hubRun_inv {cfg : HubConfig} {h h' : Hub} {ls : List HubLabel} (hI : HubInv h)
    (hr : HubRun cfg h ls h') : HubInv h' := by
  induction hr with
  | nil => exact hI
  | cons hs _ ih => exact ih (HubStepPreservesInv _ _ _ _ hI hs)

/-- Two runs, one after the other. -/
lemma HubRun.append {cfg : HubConfig} {h h' h'' : Hub} {ls ls' : List HubLabel}
    (r : HubRun cfg h ls h') (r' : HubRun cfg h' ls' h'') : HubRun cfg h (ls ++ ls') h'' := by
  induction r with
  | nil => exact r'
  | cons hs _ ih => exact HubRun.cons hs (ih r')

theorem ReachableHubsSatisfyInv : Properties.ReachableHubsSatisfyInv := by
  intro cfg ls h hr
  have hI := hubRun_inv EmptyHubInv hr
  exact ⟨hI, hI.frontier⟩

theorem BatchRootsWriteOnce : Properties.BatchRootsWriteOnce := by
  intro cfg h h' l c n hs hne
  cases hs with
  | @createChain c₀ gh gr g _ _ _ _ _ hz =>
    show upd h.mr.roots c₀ (upd (h.mr.roots c₀) 0 gr) c n = h.mr.roots c n
    by_cases hx : c = c₀
    · subst hx; simp only [upd_same]
      by_cases hn : n = 0
      · subst hn; exact absurd hz hne
      · exact upd_ne _ _ hn
    · exact congrFun (upd_ne _ _ hx) n
  | @execute c₀ d infos m' _ _ hA =>
    obtain ⟨_, _, sother, _, _, _, _, swo⟩ := appendAll_spec hA
    by_cases hx : c = c₀
    · subst hx; exact swo n hne
    · exact congrFun (sother c hx) n
  | _ => rfl

lemma hubRun_roots_persist {cfg : HubConfig} {h h' : Hub} {ls : List HubLabel}
    (hr : HubRun cfg h ls h') (c n : ℕ) (hne : h.mr.roots c n ≠ 0) :
    h'.mr.roots c n = h.mr.roots c n := by
  induction hr with
  | nil => rfl
  | cons hs _ ih =>
    have e := BatchRootsWriteOnce _ _ _ _ c n hs hne
    rw [ih (by rw [e]; exact hne), e]

/-- Right after an execute step, every executed batch's root is in the message root. -/
lemma execute_step_roots {cfg : HubConfig} {h h' : Hub} {c : ChainId} {infos : List BatchInfo}
    (hs : HubStep cfg h (.execute c infos) h') (b : BatchInfo) (hb : b ∈ infos) :
    h'.mr.roots c b.batchNumber = b.logsRoot ∧ b.logsRoot ≠ 0 := by
  cases hs with
  | @execute _ d _ m' _ _ hA =>
    obtain ⟨_, _, _, sroots, snums, snz, _, _⟩ := appendAll_spec hA
    refine ⟨?_, snz b hb⟩
    show m'.roots c b.batchNumber = b.logsRoot
    rw [sroots]
    exact writeRoots_mem _ _ (by rw [snums]; exact List.nodup_range') b hb

theorem ExecutedRootsRecorded : Properties.ExecutedRootsRecorded := by
  intro cfg h h' ls c infos b hI hr hmem hb
  have hroot : h'.mr.roots c b.batchNumber = b.logsRoot ∧ b.logsRoot ≠ 0 := by
    induction hr with
    | nil => simp at hmem
    | @cons h₀ h₁ h₂ l ls' hs hr' ih =>
      rcases List.mem_cons.1 hmem with rfl | hmem'
      · obtain ⟨e, hnz⟩ := execute_step_roots hs b hb
        refine ⟨?_, hnz⟩
        rw [hubRun_roots_persist hr' c _ (by rw [e]; exact hnz), e]
      · exact ih (HubStepPreservesInv _ _ _ _ hI hs) hmem'
  have hI' := hubRun_inv hI hr
  refine ⟨hroot.1, hroot.2, ?_⟩
  have hne : h'.mr.roots c b.batchNumber ≠ 0 := by rw [hroot.1]; exact hroot.2
  have hreg : h'.mr.reg c = true := by
    by_contra hf
    exact hne (hI'.unregZero c _ (by simpa using hf))
  obtain ⟨d', hd'⟩ := Option.ne_none_iff_exists'.1 ((hI'.regIff c).1 hreg)
  exact ⟨d', hd', by rw [← hI'.rootsAgree c d' _ hd' hne, hroot.1]⟩

/-! ## Sync -/

/-- Rewriting one diamond without changing its executed count, the message root untouched,
keeps every chain's sync. -/
lemma synced_update_diamond {h : Hub} {c₀ c : ChainId} {d d' : Diamond}
    (hc : h.chains c₀ = some d) (he : d'.executed = d.executed) (hs : Synced h c) :
    Synced { h with chains := upd h.chains c₀ (some d') } c := by
  intro e hce
  by_cases hx : c = c₀
  · subst hx; simp only [upd_same, Option.some.injEq] at hce; subst hce
    rw [he]; exact hs d hc
  · simp only [upd_ne _ _ hx] at hce; exact hs e hce

theorem SyncedStaysSynced : Properties.SyncedStaysSynced := by
  intro cfg h h' l c hs hcons hsync
  cases hs with
  | @createChain c₀ gh gr g _ _ _ _ _ _ =>
    intro e hce
    by_cases hx : c = c₀
    · subst hx; simp only [upd_same, Option.some.injEq] at hce ⊢; subst hce; rfl
    · simp only [upd_ne _ _ hx] at hce ⊢; exact hsync e hce
  | @registerDeployed c₀ d _ _ _ =>
    intro e hce
    by_cases hx : c = c₀
    · subst hx; simp only [upd_same, Option.some.injEq] at hce ⊢; subst hce; rfl
    · simp only [upd_ne _ _ hx] at hce ⊢; exact hsync e hce
  | commit hc _ _ _ => exact synced_update_diamond hc rfl hsync
  | prove hc _ _ _ => exact synced_update_diamond hc rfl hsync
  | @execute c₀ d infos m' hc _ hA =>
    obtain ⟨_, scur, _, _, _, _, _, _⟩ := appendAll_spec hA
    intro e hce
    show m'.cur c = e.executed
    rw [scur]
    by_cases hx : c = c₀
    · subst hx; simp only [upd_same, Option.some.injEq] at hce ⊢; subst hce
      simp only [executeEffect]; rw [hsync d hc]
    · simp only [upd_ne _ _ hx] at hce ⊢; exact hsync e hce
  | revert hc _ _ _ => exact synced_update_diamond hc rfl hsync
  | @upgrade c₀ d t hc =>
    refine synced_update_diamond hc ?_ hsync
    unfold upgradeEffect; split <;> rfl
  | burn _ hc _ _ _ _ => exact synced_update_diamond hc rfl hsync
  | @mintExisting c₀ d bn com _ hc _ _ _ =>
    intro e hce
    by_cases hx : c = c₀
    · subst hx; simp only [upd_same, Option.some.injEq] at hce ⊢; subst hce
      exact hcons
    · simp only [upd_ne _ _ hx] at hce ⊢; exact hsync e hce
  | @mintNew c₀ bn com gh gr _ _ _ _ _ _ =>
    intro e hce
    by_cases hx : c = c₀
    · subst hx; simp only [upd_same, Option.some.injEq] at hce ⊢; subst hce
      exact hcons
    · simp only [upd_ne _ _ hx] at hce ⊢; exact hsync e hce
  | confirmFailure _ hc _ => exact synced_update_diamond hc rfl hsync

theorem SyncedAlongRuns : Properties.SyncedAlongRuns := by
  intro cfg h h' ls c hr hcons hs
  induction hr with
  | nil => exact hs
  | cons hstep _ ih =>
    exact ih (fun l hl => hcons l (List.mem_cons_of_mem _ hl))
      (SyncedStaysSynced _ _ _ _ c hstep (hcons _ (List.mem_cons_self ..)) hs)

/-- With migrations disabled, no mint step exists, so every label of a run is consistent. -/
lemma head_step_consistent {cfg : HubConfig} {h h' : Hub} {l : HubLabel}
    (hm : cfg.migrationsEnabled = false) (hs : HubStep cfg h l h') : l.MintConsistent := by
  cases hs with
  | mintExisting hme _ _ _ _ => rw [hm] at hme; cases hme
  | mintNew hme _ _ _ _ _ => rw [hm] at hme; cases hme
  | _ => trivial

lemma head_run_consistent {cfg : HubConfig} {h h' : Hub} {ls : List HubLabel}
    (hm : cfg.migrationsEnabled = false) (hr : HubRun cfg h ls h') :
    ∀ l ∈ ls, HubLabel.MintConsistent l := by
  induction hr with
  | nil => simp
  | cons hs _ ih =>
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact head_step_consistent hm hs
    · exact ih l hl

theorem HeadRunsKeepSync : Properties.HeadRunsKeepSync := by
  intro cfg h h' ls c hm hr hs
  exact SyncedAlongRuns _ _ _ _ c hr (head_run_consistent hm hr) hs

theorem ReachableHeadHubsSynced : Properties.ReachableHeadHubsSynced := by
  intro cfg ls h hm hr
  refine ⟨(ReachableHubsSatisfyInv _ _ _ hr).1, fun c => ?_⟩
  exact HeadRunsKeepSync _ _ _ _ c hm hr (fun d hd => by simp [emptyHub] at hd)

/-! ## Liveness and drift -/

theorem ExecuteNeverRevertsInMessageRoot : Properties.ExecuteNeverRevertsInMessageRoot := by
  intro cfg h c d infos hI hs hc hg hnz
  have hcur := hs d hc
  obtain ⟨m', hA⟩ := appendAll_some h.mr c infos (hI.reg_of_chain hc) (hI.frontier c)
    (by rw [hcur]; exact hg.2.2.1) hnz
  refine ⟨⟨m', hA, ?_⟩, ⟨_, HubStep.execute hc hg hA⟩⟩
  obtain ⟨_, scur, _, _, _, _, _, _⟩ := appendAll_spec hA
  rw [scur, upd_same, hcur]; rfl

theorem DriftBlocksExecute : Properties.DriftBlocksExecute := by
  intro cfg h c d hc hdrift infos h' hs
  cases hs with
  | @execute _ d' _ m' hc' hg hA =>
    rw [hc] at hc'; cases hc'
    obtain ⟨_, _, _, _, snums, _, _, _⟩ := appendAll_spec hA
    obtain ⟨hne, _, hnums, _, _⟩ := hg
    obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at snums hnums
    exact hdrift (by omega)

theorem ZeroLogsRootRefused : Properties.ZeroLogsRootRefused := by
  intro cfg h c infos hz
  refine ⟨appendAll_zero_root _ _ _ hz, fun h' hs => ?_⟩
  cases hs with
  | execute _ _ hA => rw [appendAll_zero_root _ _ _ hz] at hA; cases hA

theorem ExecuteEnabledIffSynced : Properties.ExecuteEnabledIffSynced := by
  intro cfg h c d infos hI hc hg hnz
  constructor
  · rintro ⟨h', hs⟩
    by_contra hne
    exact DriftBlocksExecute _ _ _ _ hc hne _ _ hs
  · intro hcur
    have hs : Synced h c := fun d' hd' => by rw [hc] at hd'; cases hd'; exact hcur
    exact (ExecuteNeverRevertsInMessageRoot _ _ _ _ _ hI hs hc hg hnz).2

/-- One step at `b17415d20` keeps a drifted chain's two counters, and is not its execute. -/
lemma drift_step {cfg : HubConfig} {h h' : Hub} {l : HubLabel} {c : ChainId} {d : Diamond}
    (hm : cfg.migrationsEnabled = false) (hs : HubStep cfg h l h') (hc : h.chains c = some d)
    (hdrift : h.mr.cur c ≠ d.executed) :
    (∃ d', h'.chains c = some d' ∧ d'.executed = d.executed) ∧ h'.mr.cur c = h.mr.cur c ∧
      execNumbers c [l] = [] := by
  have keep : ∀ (c₀ : ChainId) (e e' : Diamond), h.chains c₀ = some e → e'.executed = e.executed →
      ∃ d', upd h.chains c₀ (some e') c = some d' ∧ d'.executed = d.executed := by
    intro c₀ e e' he hee
    by_cases hx : c = c₀
    · subst hx; rw [hc] at he; cases he; exact ⟨e', by simp, hee⟩
    · exact ⟨d, by rw [upd_ne _ _ hx]; exact hc, rfl⟩
  cases hs with
  | @createChain c₀ gh gr g _ hnone _ _ _ _ =>
    have hx : c ≠ c₀ := by rintro rfl; rw [hc] at hnone; cases hnone
    exact ⟨⟨d, by simp only [upd_ne _ _ hx]; exact hc, rfl⟩, upd_ne _ _ hx, by simp [execNumbers]⟩
  | @registerDeployed c₀ d₀ _ hnone _ =>
    have hx : c ≠ c₀ := by rintro rfl; rw [hc] at hnone; cases hnone
    exact ⟨⟨d, by simp only [upd_ne _ _ hx]; exact hc, rfl⟩, upd_ne _ _ hx, by simp [execNumbers]⟩
  | commit hc₀ _ _ _ => exact ⟨keep _ _ _ hc₀ rfl, rfl, by simp [execNumbers]⟩
  | prove hc₀ _ _ _ => exact ⟨keep _ _ _ hc₀ rfl, rfl, by simp [execNumbers]⟩
  | @execute c₀ d₀ infos m' hc₀ hg hA =>
    have hx : c ≠ c₀ := by
      rintro rfl
      exact DriftBlocksExecute _ _ _ _ hc hdrift _ _ (HubStep.execute hc₀ hg hA)
    obtain ⟨_, scur, _, _, _, _, _, _⟩ := appendAll_spec hA
    refine ⟨⟨d, by simp only [upd_ne _ _ hx]; exact hc, rfl⟩, ?_, by simp [execNumbers, Ne.symm hx]⟩
    show m'.cur c = h.mr.cur c
    rw [scur, upd_ne _ _ hx]
  | revert hc₀ _ _ _ => exact ⟨keep _ _ _ hc₀ rfl, rfl, by simp [execNumbers]⟩
  | @upgrade c₀ d₀ t hc₀ =>
    refine ⟨keep _ _ _ hc₀ ?_, rfl, by simp [execNumbers]⟩
    unfold upgradeEffect; split <;> rfl
  | burn hme _ _ _ _ _ => rw [hm] at hme; cases hme
  | mintExisting hme _ _ _ _ => rw [hm] at hme; cases hme
  | mintNew hme _ _ _ _ _ => rw [hm] at hme; cases hme
  | confirmFailure _ hc₀ _ => exact ⟨keep _ _ _ hc₀ rfl, rfl, by simp [execNumbers]⟩

lemma execNumbers_cons (c : ChainId) (l : HubLabel) (ls : List HubLabel) :
    execNumbers c (l :: ls) = execNumbers c [l] ++ execNumbers c ls := by
  cases l <;> simp [execNumbers]

theorem DriftPersistsAtHead : Properties.DriftPersistsAtHead := by
  intro cfg h h' ls c d hm hr hc hdrift
  induction hr generalizing d with
  | nil => exact ⟨⟨d, hc, rfl, rfl⟩, rfl⟩
  | cons hs _ ih =>
    obtain ⟨⟨d₁, hd₁, he⟩, hcur, hnum⟩ := drift_step hm hs hc hdrift
    obtain ⟨⟨d₂, hd₂, he₂, hcur₂⟩, hnum₂⟩ := ih d₁ hd₁ (by rw [hcur, he]; exact hdrift)
    refine ⟨⟨d₂, hd₂, he₂.trans he, hcur₂.trans hcur⟩, ?_⟩
    rw [execNumbers_cons, hnum, hnum₂]; rfl

/-! ## Legacy chains and the witness run -/

/-- The executor's modelled checks for a call executing one batch. -/
lemma execGuard_single {H : BatchInfo → Word} {d : Diamond} {b : BatchInfo} (ha : d.away = false)
    (hn : b.batchNumber = d.executed + 1) (hh : H b = d.batchHash b.batchNumber)
    (hv : d.executed + 1 ≤ d.verified) : ExecGuard H d [b] :=
  ⟨by simp, ha, by simp [hn], fun b' hb' => by
    simp only [List.mem_singleton] at hb'; subst hb'; exact hh, hv⟩

lemma wLegacyHub_chain : wLegacyHub.chains 7 = some wLegacyDiamond := by simp [wLegacyHub]

lemma wLegacy_guard : ExecGuard headL1.hash wLegacyDiamond [wInfo 6] := by
  refine ⟨by simp, rfl, rfl, ?_, by decide⟩
  intro b hb
  simp only [List.mem_singleton] at hb
  subst hb; rfl

lemma wLegacy_inv (cur : ChainId → ℕ) :
    HubInv { wLegacyHub with mr := { wLegacyHub.mr with cur := cur } } := by
  refine ⟨fun x => ?_, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ h => absurd rfl h⟩
  by_cases hx : x = 7
  · subst hx; simp [wLegacyHub]
  · simp [wLegacyHub, upd, hx]

theorem LegacyUnsavedChainIsWedged : Properties.LegacyUnsavedChainIsWedged := by
  have hdrift : wLegacyHub.mr.cur 7 ≠ wLegacyDiamond.executed := by
    simp [wLegacyHub, wLegacyDiamond]
  refine ⟨wLegacy_inv _, wLegacy_guard, by simp [wInfo],
    fun h' => DriftBlocksExecute _ _ _ _ wLegacyHub_chain hdrift _ _, fun ls h' hr => ?_⟩
  exact (DriftPersistsAtHead _ _ _ _ _ _ rfl hr wLegacyHub_chain hdrift).2

theorem LegacySavedChainExecutes : Properties.LegacySavedChainExecutes := by
  unfold Properties.LegacySavedChainExecutes
  intro h
  have hI : HubInv h := wLegacy_inv _
  have hc : h.chains 7 = some wLegacyDiamond := wLegacyHub_chain
  have hS : Synced h 7 := by
    intro d hd; rw [hc] at hd; cases hd; simp [h, wLegacyDiamond]
  obtain ⟨⟨m', hA, _⟩, _⟩ :=
    ExecuteNeverRevertsInMessageRoot headL1 h 7 wLegacyDiamond [wInfo 6] hI hS hc wLegacy_guard
      (by simp [wInfo])
  obtain ⟨_, scur, _, sroots, _, _, _, _⟩ := appendAll_spec hA
  refine ⟨hI, hS, _, HubStep.execute hc wLegacy_guard hA, ?_, ?_,
    executeEffect wLegacyDiamond [wInfo 6], by simp, rfl, ?_⟩
  · show m'.cur 7 = 6
    rw [scur]; simp [h]
  · show m'.roots 7 6 = 26
    rw [sroots]
    exact writeRoots_mem _ [wInfo 6] (by simp [wInfo]) (wInfo 6) (by simp)
  · exact writeRoots_mem wLegacyDiamond.logsRoot [wInfo 6] (by simp [wInfo]) (wInfo 6) (by simp)

theorem HubSyncWitness : Properties.HubSyncWitness := by
  have hr := HubRun.cons (cfg := headL1) (h := emptyHub)
    (HubStep.createChain (c := 1) (gh := 13) (gr := 12) (g := 0) rfl rfl rfl (by decide)
      (by decide) rfl)
    (HubRun.cons (HubStep.commit (c := 1) (prev := wInfo0) (new := wInfo 1) rfl rfl rfl rfl)
    (HubRun.cons (HubStep.commit (c := 1) (prev := wInfo 1) (new := wInfo 2) rfl rfl rfl rfl)
    (HubRun.cons (HubStep.prove (c := 1) (v := 2) rfl rfl (by decide) (by decide))
    (HubRun.cons (HubStep.execute (c := 1) (infos := [wInfo 1, wInfo 2]) rfl
        ⟨by simp, rfl, rfl, fun b hb => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl <;> rfl, by decide⟩ rfl)
    (HubRun.cons (HubStep.registerDeployed (c := 2) (d := wDeployed) rfl rfl rfl)
    (HubRun.cons (HubStep.execute (c := 2) (infos := [wInfo 8]) rfl
        ⟨by simp, rfl, rfl, fun b hb => by
          simp only [List.mem_singleton] at hb
          subst hb; rfl, by decide⟩ rfl)
    HubRun.nil))))))
  have hS := ReachableHeadHubsSynced _ _ _ rfl hr
  exact ⟨_, _, hr, rfl, rfl, hS.1, hS.2 1, hS.2 2, rfl, rfl, rfl, rfl, rfl,
    ⟨_, rfl, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩⟩

theorem ZeroLogsRootRefusedOnSyncedChain : Properties.ZeroLogsRootRefusedOnSyncedChain := by
  unfold Properties.ZeroLogsRootRefusedOnSyncedChain
  intro b d h
  have hc : h.chains 7 = some d := rfl
  refine ⟨⟨fun x => ?_, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ hne => absurd rfl hne⟩,
    fun e he => ?_, execGuard_single rfl rfl rfl (by decide), fun h' hs => ?_⟩
  · by_cases hx : x = 7
    · subst hx; simp [h, wLegacyHub]
    · simp [h, wLegacyHub, upd, hx]
  · rw [hc] at he; cases he; rfl
  · exact (ZeroLogsRootRefused headL1 h 7 [b] ⟨b, by simp, rfl⟩).2 h' hs

/-! The diamonds of chain `1` along `HubUpgradeRevertWitness`'s run. -/

/-- Created, with genesis upgrade transaction hash `77`. -/
def wUpgD0 : Diamond := initDiamond 13 12 77
/-- `wInfoReverted` committed: batch 1 is the upgrade batch. -/
def wUpgD1 : Diamond := commitEffect wHash wUpgD0 wInfoReverted
/-- Reverted to `0` batches. -/
def wUpgD2 : Diamond := revertEffect wUpgD1 0
/-- `wInfo 1` committed. -/
def wUpgD3 : Diamond := commitEffect wHash wUpgD2 (wInfo 1)
/-- Batch 1 proved and executed. -/
def wUpgD4 : Diamond := executeEffect { wUpgD3 with verified := 1 } [wInfo 1]
/-- The in-tree upgrade with transaction hash `88`. -/
def wUpgD5 : Diamond := upgradeEffect wUpgD4 88

/-- `HubUpgradeRevertWitness`'s run, on an L1 layer with either migration flag. -/
lemma wUpg_l1Run (m : Bool) : ∃ h₁ h₂ h₃ h : Hub,
    HubRun ⟨true, m, wHash⟩ emptyHub [.createChain 1 13 12 77, .commit 1 wInfo0 wInfoReverted] h₁ ∧
    h₁.chains 1 = some wUpgD1 ∧
    HubStep ⟨true, m, wHash⟩ h₁ (.revert 1 0) h₂ ∧ h₂.chains 1 = some wUpgD2 ∧
    HubRun ⟨true, m, wHash⟩ h₂ [.commit 1 wInfo0 (wInfo 1), .prove 1 1, .execute 1 [wInfo 1]] h₃ ∧
    h₃.chains 1 = some wUpgD4 ∧
    HubStep ⟨true, m, wHash⟩ h₃ (.upgrade 1 88) h ∧ h.chains 1 = some wUpgD5 ∧
    h.mr.cur 1 = 1 ∧ h.mr.roots 1 1 = 21 :=
  ⟨_, _, _, _,
    HubRun.cons (HubStep.createChain (c := 1) (gh := 13) (gr := 12) (g := 77) rfl rfl rfl
        (by decide) (by decide) rfl)
      (HubRun.cons (HubStep.commit (c := 1) (prev := wInfo0) (new := wInfoReverted) rfl rfl rfl rfl)
      HubRun.nil),
    rfl,
    HubStep.revert (c := 1) (n := 0) rfl rfl (Nat.le_refl 0) (Nat.zero_le 1), rfl,
    HubRun.cons (HubStep.commit (c := 1) (prev := wInfo0) (new := wInfo 1) rfl rfl rfl rfl)
      (HubRun.cons (HubStep.prove (c := 1) (v := 1) rfl rfl Nat.zero_lt_one (Nat.le_refl 1))
      (HubRun.cons (HubStep.execute (c := 1) (infos := [wInfo 1]) rfl
          ⟨by simp, rfl, rfl, fun b hb => by
            simp only [List.mem_singleton] at hb
            subst hb; rfl, Nat.le_refl 1⟩ rfl)
      HubRun.nil)),
    rfl, HubStep.upgrade (c := 1) (t := 88) rfl, rfl, rfl, rfl⟩

theorem HubUpgradeRevertWitness : Properties.HubUpgradeRevertWitness := by
  obtain ⟨h₁, h₂, h₃, h, hr₁, hc₁, st₂, hc₂, hr₃, hc₃, st₄, hc, hcur, hroot⟩ := wUpg_l1Run false
  have hI₂ := HubStepPreservesInv _ _ _ _ (hubRun_inv EmptyHubInv hr₁) st₂
  have hI := HubStepPreservesInv _ _ _ _ (hubRun_inv hI₂ hr₃) st₄
  refine ⟨h₁, h₂, h₃, h, hr₁, ⟨_, hc₁, by decide, by decide, by decide⟩, st₂,
    ⟨_, hc₂, by decide, by decide, by decide⟩, hr₃, ⟨_, hc₃, by decide, by decide, by decide⟩, st₄,
    hI, fun d hd => ?_, hcur, hroot, _, hc, by decide, by decide, by decide, by decide, by decide,
    by decide⟩
  rw [hc] at hd; cases hd; rw [hcur]; decide

end Contracts.BatchCounters
