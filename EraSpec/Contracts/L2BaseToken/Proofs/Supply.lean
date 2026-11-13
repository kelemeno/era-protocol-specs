import EraSpec.Contracts.L2BaseToken.Properties.Supply

/-!
# Proofs: base-token supply on ZKsync OS

Proofs of `EraSpec.Contracts.L2BaseToken.Properties.Supply`. The ledger lemmas say how `credit`,
`debit` and `xfer` move the sum of balances and one account. `step_inv` shows one combined
invariant (`Inv`) is preserved by every call; every run-level property is read off it.
-/

namespace Contracts.L2BaseToken

/-! ## Ledger arithmetic -/

theorem sum_update_add (f : Address → ℕ) (i : Address) (v : ℕ) :
    (∑ a : Address, Function.update f i v a) + f i = (∑ a : Address, f a) + v := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i) f v, Finset.sdiff_singleton_eq_erase]
  have he := Finset.sum_erase_add (Finset.univ : Finset Address) f (Finset.mem_univ i)
  omega

theorem sum_credit (b : Address → ℕ) (x : Address) (amt : ℕ) :
    ∑ a, credit b x amt a = (∑ a, b a) + amt := by
  have := sum_update_add b x (b x + amt)
  unfold credit; omega

theorem sum_debit {b : Address → ℕ} {x : Address} {amt : ℕ} (h : amt ≤ b x) :
    (∑ a, debit b x amt a) + amt = ∑ a, b a := by
  have := sum_update_add b x (b x - amt)
  unfold debit; omega

theorem sum_xfer {b : Address → ℕ} {f : Address} (t : Address) {amt : ℕ} (h : amt ≤ b f) :
    ∑ a, xfer b f t amt a = ∑ a, b a := by
  unfold xfer; rw [sum_credit]; exact sum_debit h

theorem xfer_apply (b : Address → ℕ) (f t : Address) (amt : ℕ) (a : Address) :
    xfer b f t amt a = (if a = f then b f - amt else b a) + (if a = t then amt else 0) := by
  unfold xfer credit debit
  by_cases hat : a = t
  · subst hat; simp [Function.update_apply]
  · simp [Function.update_apply, hat]

theorem le_supply {T : Type} (s : State T) (a : Address) : s.bal a ≤ supply s :=
  Finset.single_le_sum (f := s.bal) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem circulating_add {T : Type} (s : State T) :
    circulating s + s.bal holderAddr = supply s := by
  have := le_supply s holderAddr
  unfold circulating; omega

/-- Distinctness of the role addresses, by evaluation. -/
theorem addr_facts :
    holderAddr ≠ baseTokenAddr ∧ interopCenterAddr ≠ holderAddr ∧ ntvAddr ≠ holderAddr
    ∧ interopHandlerAddr ≠ holderAddr ∧ baseTokenAddr ≠ complexUpgraderAddr := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Characterizations of successful calls -/

section chars
variable {T : Type} {tr : Tracker T} {s s' : State T}

theorem sendValue_some {b b' : Address → ℕ} {src dst : Address} {amt : ℕ}
    (h : sendValue b src dst amt = some b') :
    amt ≤ b src ∧ dst ≠ holderAddr ∧ dst ≠ baseTokenAddr ∧ b' = xfer b src dst amt := by
  unfold sendValue at h
  split_ifs at h with hc
  · exact ⟨hc.1, hc.2.1, hc.2.2, (Option.some.inj h).symm⟩

theorem execInitL2_some {caller : Address} {l1 : UInt256}
    (h : execInitL2 s caller l1 = some s') :
    caller = complexUpgraderAddr ∧ s.initialized = false ∧ s' = initL2Effect s l1 := by
  unfold execInitL2 at h
  split_ifs at h with h1 h2
  · refine ⟨not_not.mp h1, by simpa using h2, (Option.some.inj h).symm⟩

theorem execGive_some {caller dst : Address} {amt : ℕ} {ch : UInt256}
    (h : execGive tr s caller dst amt ch = some s') :
    caller = interopHandlerAddr ∧
      ((amt = 0 ∧ s' = s) ∨
       (amt ≠ 0 ∧ ∃ t', tr.finalize s.trk ch amt = some t' ∧ amt ≤ s.bal holderAddr
          ∧ dst ≠ holderAddr ∧ dst ≠ baseTokenAddr
          ∧ s' = { s with bal := xfer s.bal holderAddr dst amt, trk := t',
                          calls := s.calls ++ [.finalize ch amt], given := s.given + amt })) := by
  unfold execGive at h
  split_ifs at h with h1 h2
  · exact ⟨not_not.mp h1, Or.inl ⟨h2, (Option.some.inj h).symm⟩⟩
  · refine ⟨not_not.mp h1, Or.inr ⟨h2, ?_⟩⟩
    cases hf : tr.finalize s.trk ch amt with
    | none => rw [hf] at h; cases h
    | some t' =>
      rw [hf] at h
      cases hv : sendValue s.bal holderAddr dst amt with
      | none => rw [hv] at h; cases h
      | some b' =>
        rw [hv] at h
        obtain ⟨hle, hd1, hd2, rfl⟩ := sendValue_some hv
        exact ⟨t', rfl, hle, hd1, hd2, (Option.some.inj h).symm⟩

theorem execRecover_some {caller dst : Address} {amt : ℕ} {ch : UInt256}
    (h : execRecover tr s caller dst amt ch = some s') :
    caller = ntvAddr ∧
      ((amt = 0 ∧ s' = s) ∨
       (amt ≠ 0 ∧ tr.recoveryNeutral s.trk ch = true ∧ amt ≤ s.bal holderAddr
          ∧ dst ≠ holderAddr ∧ dst ≠ baseTokenAddr
          ∧ s' = { s with bal := xfer s.bal holderAddr dst amt,
                          recovered := s.recovered + amt })) := by
  unfold execRecover at h
  split_ifs at h with h1 h2 h3
  · exact ⟨not_not.mp h1, Or.inl ⟨h2, (Option.some.inj h).symm⟩⟩
  · refine ⟨not_not.mp h1, Or.inr ⟨h2, by simpa using h3, ?_⟩⟩
    cases hv : sendValue s.bal holderAddr dst amt with
    | none => rw [hv] at h; cases h
    | some b' =>
      rw [hv] at h
      obtain ⟨hle, hd1, hd2, rfl⟩ := sendValue_some hv
      exact ⟨hle, hd1, hd2, (Option.some.inj h).symm⟩

theorem execBurn_some {caller : Address} {v : ℕ} {ch : UInt256}
    (h : execBurn tr s caller v ch = some s') :
    v ≤ s.bal caller ∧ (caller = interopCenterAddr ∨ caller = ntvAddr) ∧
      ∃ t', tr.initiate s.trk ch v = some t'
        ∧ s' = { s with bal := xfer s.bal caller holderAddr v, trk := t',
                        calls := s.calls ++ [.initiate ch v], burnt := s.burnt + v } := by
  unfold execBurn at h
  split_ifs at h with h1 h2
  refine ⟨not_lt.mp h1, ?_, ?_⟩
  · by_cases hc : caller = interopCenterAddr
    · exact Or.inl hc
    · exact Or.inr (by by_contra hn; exact h2 ⟨hc, hn⟩)
  · cases hf : tr.initiate s.trk ch v with
    | none => rw [hf] at h; cases h
    | some t' => rw [hf] at h; exact ⟨t', rfl, (Option.some.inj h).symm⟩

theorem exec_transfer_some {f t : Address} {amt : ℕ}
    (h : exec tr s (.transfer f t amt) = some s') :
    f ≠ holderAddr ∧ f ≠ baseTokenAddr ∧ t ≠ holderAddr ∧ amt ≤ s.bal f
      ∧ s' = { s with bal := xfer s.bal f t amt } := by
  simp only [exec] at h
  split_ifs at h with h1
  push Not at h1
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, (Option.some.inj h).symm⟩

theorem exec_force_some {f : Address} {amt : ℕ}
    (h : exec tr s (.forceToHolder f amt) = some s') :
    f ≠ holderAddr ∧ f ≠ baseTokenAddr ∧ amt ≤ s.bal f
      ∧ s' = { s with bal := xfer s.bal f holderAddr amt, forced := s.forced + amt } := by
  simp only [exec] at h
  split_ifs at h with h1
  push Not at h1
  exact ⟨h1.1, h1.2.1, h1.2.2, (Option.some.inj h).symm⟩

theorem exec_release_some {t : Address} {amt : ℕ}
    (h : exec tr s (.vmRelease t amt) = some s') :
    t ≠ holderAddr ∧ amt ≤ s.bal holderAddr
      ∧ s' = { s with bal := xfer s.bal holderAddr t amt, released := s.released + amt } := by
  simp only [exec] at h
  split_ifs at h with h1
  push Not at h1
  exact ⟨h1.1, h1.2, (Option.some.inj h).symm⟩

end chars

/-! ## Balance of the holder and the sum, per ledger move -/

theorem xfer_holder_in {b : Address → ℕ} {f : Address} (amt : ℕ) (hf : f ≠ holderAddr) :
    xfer b f holderAddr amt holderAddr = b holderAddr + amt := by
  rw [xfer_apply]; simp [Ne.symm hf]

theorem xfer_holder_out {b : Address → ℕ} {t : Address} (amt : ℕ) (ht : t ≠ holderAddr) :
    xfer b holderAddr t amt holderAddr = b holderAddr - amt := by
  rw [xfer_apply]; simp [Ne.symm ht]

theorem xfer_holder_other {b : Address → ℕ} {f t : Address} (amt : ℕ) (hf : f ≠ holderAddr)
    (ht : t ≠ holderAddr) : xfer b f t amt holderAddr = b holderAddr := by
  rw [xfer_apply]; simp [Ne.symm hf, Ne.symm ht]

theorem supply_initL2Effect {T : Type} (s : State T) (l1 : UInt256) :
    supply (initL2Effect s l1) = supply s + INITIAL := by
  show ∑ a, xfer (credit s.bal baseTokenAddr INITIAL) baseTokenAddr holderAddr INITIAL a = _
  rw [sum_xfer holderAddr (by unfold credit; simp), sum_credit]
  simp only [supply]

theorem holder_initL2Effect {T : Type} (s : State T) (l1 : UInt256) :
    (initL2Effect s l1).bal holderAddr = s.bal holderAddr + INITIAL := by
  show xfer (credit s.bal baseTokenAddr INITIAL) baseTokenAddr holderAddr INITIAL holderAddr = _
  rw [xfer_holder_in INITIAL addr_facts.1.symm]
  unfold credit
  rw [Function.update_of_ne addr_facts.1]

/-! ## What one successful call does -/

/-- The amount a call pays out of the holder into circulation. -/
def Call.out : Call → ℕ
  | .give _ _ amt _ => amt
  | .recover _ _ amt _ => amt
  | .vmRelease _ amt => amt
  | _ => 0

/-- The amount a call pays from circulation into the holder. -/
def Call.inn : Call → ℕ
  | .burn _ v _ => v
  | .forceToHolder _ amt => amt
  | _ => 0

/-- The effect of one successful call on every quantity the invariants mention. -/
structure StepFacts {T : Type} (tr : Tracker T) (s s' : State T) (c : Call) : Prop where
  supply_eq : supply s' + s.minted = supply s + s'.minted
  holder_eq : s'.bal holderAddr + s'.given + s'.recovered + s'.released
        + s.minted + s.burnt + s.forced
      = s.bal holderAddr + s.given + s.recovered + s.released
        + s'.minted + s'.burnt + s'.forced
  out_eq : s'.given + s'.recovered + s'.released = s.given + s.recovered + s.released + c.out
  in_eq : s'.burnt + s'.forced = s.burnt + s.forced + c.inn
  pre_eq : s'.preV31 = s.preV31
  calls_eq : s'.calls = s.calls ++ c.trackerCall.toList
  replay_eq : replay tr s.trk c.trackerCall.toList = some s'.trk
  given_eq : s'.given = s.given + finalizedTotal c.trackerCall.toList
  burnt_eq : s'.burnt = s.burnt + initiatedTotal c.trackerCall.toList
  init : c.isInitL2 = true → ∃ l1, c = .initL2 complexUpgraderAddr l1 ∧ s.initialized = false
      ∧ s'.initialized = true ∧ s'.l1ChainId = l1 ∧ s'.minted = s.minted + INITIAL
  noinit : c.isInitL2 = false →
      s'.initialized = s.initialized ∧ s'.l1ChainId = s.l1ChainId ∧ s'.minted = s.minted

theorem stepFacts_refl {T : Type} (tr : Tracker T) (s : State T) (c : Call)
    (ht : c.trackerCall = none) (hi : c.isInitL2 = false) (ho : c.out = 0) (hn : c.inn = 0) :
    StepFacts tr s s c where
  supply_eq := rfl
  holder_eq := rfl
  out_eq := by rw [ho]; rfl
  in_eq := by rw [hn]; rfl
  pre_eq := rfl
  calls_eq := by rw [ht]; simp
  replay_eq := by rw [ht]; rfl
  given_eq := by rw [ht]; rfl
  burnt_eq := by rw [ht]; rfl
  init := by intro h; rw [hi] at h; cases h
  noinit := fun _ => ⟨rfl, rfl, rfl⟩

theorem step_facts {T : Type} {tr : Tracker T} {s s' : State T} {c : Call}
    (h : exec tr s c = some s') : StepFacts tr s s' c := by
  cases c with
  | transfer f t amt =>
    obtain ⟨hf, _, ht, hle, rfl⟩ := exec_transfer_some h
    exact
      { supply_eq := by
          show (∑ a, xfer s.bal f t amt a) + s.minted = supply s + s.minted
          rw [sum_xfer t hle]; simp only [supply]
        holder_eq := by
          show xfer s.bal f t amt holderAddr + _ + _ + _ + _ + _ + _ = _
          rw [xfer_holder_other amt hf ht]
        out_eq := by dsimp only [Call.out]; omega
        in_eq := by dsimp only [Call.inn]; omega
        pre_eq := rfl
        calls_eq := by simp [Call.trackerCall]
        replay_eq := rfl
        given_eq := rfl
        burnt_eq := rfl
        init := by intro h; cases h
        noinit := fun _ => ⟨rfl, rfl, rfl⟩ }
  | forceToHolder f amt =>
    obtain ⟨hf, _, hle, rfl⟩ := exec_force_some h
    exact
      { supply_eq := by
          show (∑ a, xfer s.bal f holderAddr amt a) + s.minted = supply s + s.minted
          rw [sum_xfer holderAddr hle]; simp only [supply]
        holder_eq := by
          show xfer s.bal f holderAddr amt holderAddr + s.given + s.recovered + s.released
              + s.minted + s.burnt + s.forced
            = s.bal holderAddr + s.given + s.recovered + s.released
              + s.minted + s.burnt + (s.forced + amt)
          rw [xfer_holder_in amt hf]; omega
        out_eq := by dsimp only [Call.out]; omega
        in_eq := by dsimp only [Call.inn]; omega
        pre_eq := rfl
        calls_eq := by simp [Call.trackerCall]
        replay_eq := rfl
        given_eq := rfl
        burnt_eq := rfl
        init := by intro h; cases h
        noinit := fun _ => ⟨rfl, rfl, rfl⟩ }
  | holderReceive caller amt => simp [exec] at h
  | initL2 caller l1 =>
    obtain ⟨rfl, hni, rfl⟩ := execInitL2_some (show execInitL2 s caller l1 = some s' from h)
    exact
      { supply_eq := by
          rw [supply_initL2Effect]
          show supply s + INITIAL + s.minted = supply s + (s.minted + INITIAL)
          omega
        holder_eq := by
          rw [holder_initL2Effect]
          show s.bal holderAddr + INITIAL + s.given + s.recovered + s.released
              + s.minted + s.burnt + s.forced
            = s.bal holderAddr + s.given + s.recovered + s.released
              + (s.minted + INITIAL) + s.burnt + s.forced
          omega
        out_eq := rfl
        in_eq := rfl
        pre_eq := rfl
        calls_eq := by simp [Call.trackerCall, initL2Effect]
        replay_eq := rfl
        given_eq := rfl
        burnt_eq := rfl
        init := fun _ => ⟨l1, rfl, hni, rfl, rfl, rfl⟩
        noinit := by intro h; cases h }
  | give caller dst amt ch =>
    obtain ⟨rfl, hcase⟩ := execGive_some (show execGive tr s caller dst amt ch = some s' from h)
    rcases hcase with ⟨h0, rfl⟩ | ⟨h0, t', hfin, hle, hd, _, rfl⟩
    · exact stepFacts_refl tr _ (Call.give interopHandlerAddr dst amt ch)
        (by simp [Call.trackerCall, h0]) rfl (by simp [Call.out, h0]) rfl
    · have htc : (Call.give interopHandlerAddr dst amt ch).trackerCall.toList
          = [TrackerCall.finalize ch amt] := by simp [Call.trackerCall, h0]
      exact
        { supply_eq := by
            show (∑ a, xfer s.bal holderAddr dst amt a) + s.minted = supply s + s.minted
            rw [sum_xfer dst hle]; simp only [supply]
          holder_eq := by
            show xfer s.bal holderAddr dst amt holderAddr + (s.given + amt) + s.recovered
                + s.released + s.minted + s.burnt + s.forced
              = s.bal holderAddr + s.given + s.recovered + s.released
                + s.minted + s.burnt + s.forced
            rw [xfer_holder_out amt hd]; omega
          out_eq := by dsimp only [Call.out]; omega
          in_eq := by dsimp only [Call.inn]; omega
          pre_eq := rfl
          calls_eq := by rw [htc]
          replay_eq := by rw [htc]; simp [replay, hfin]
          given_eq := by rw [htc]; simp [finalizedTotal]
          burnt_eq := by rw [htc]; simp [initiatedTotal]
          init := by intro h; cases h
          noinit := fun _ => ⟨rfl, rfl, rfl⟩ }
  | recover caller dst amt ch =>
    obtain ⟨rfl, hcase⟩ :=
      execRecover_some (show execRecover tr s caller dst amt ch = some s' from h)
    rcases hcase with ⟨h0, rfl⟩ | ⟨_, _, hle, hd, _, rfl⟩
    · exact stepFacts_refl tr _ (Call.recover ntvAddr dst amt ch) rfl rfl
        (by simp [Call.out, h0]) rfl
    · exact
        { supply_eq := by
            show (∑ a, xfer s.bal holderAddr dst amt a) + s.minted = supply s + s.minted
            rw [sum_xfer dst hle]; simp only [supply]
          holder_eq := by
            show xfer s.bal holderAddr dst amt holderAddr + s.given + (s.recovered + amt)
                + s.released + s.minted + s.burnt + s.forced
              = s.bal holderAddr + s.given + s.recovered + s.released
                + s.minted + s.burnt + s.forced
            rw [xfer_holder_out amt hd]; omega
          out_eq := by dsimp only [Call.out]; omega
          in_eq := by dsimp only [Call.inn]; omega
          pre_eq := rfl
          calls_eq := by simp [Call.trackerCall]
          replay_eq := rfl
          given_eq := rfl
          burnt_eq := rfl
          init := by intro h; cases h
          noinit := fun _ => ⟨rfl, rfl, rfl⟩ }
  | burn caller v ch =>
    obtain ⟨hle, hcaller, t', hini, rfl⟩ :=
      execBurn_some (show execBurn tr s caller v ch = some s' from h)
    have hc : caller ≠ holderAddr := by
      rcases hcaller with rfl | rfl
      · exact addr_facts.2.1
      · exact addr_facts.2.2.1
    exact
      { supply_eq := by
          show (∑ a, xfer s.bal caller holderAddr v a) + s.minted = supply s + s.minted
          rw [sum_xfer holderAddr hle]; simp only [supply]
        holder_eq := by
          show xfer s.bal caller holderAddr v holderAddr + s.given + s.recovered + s.released
              + s.minted + s.burnt + s.forced
            = s.bal holderAddr + s.given + s.recovered + s.released
              + s.minted + (s.burnt + v) + s.forced
          rw [xfer_holder_in v hc]; omega
        out_eq := by dsimp only [Call.out]; omega
        in_eq := by dsimp only [Call.inn]; omega
        pre_eq := rfl
        calls_eq := rfl
        replay_eq := by simp [Call.trackerCall, replay, hini]
        given_eq := by simp [Call.trackerCall, finalizedTotal]
        burnt_eq := by simp [Call.trackerCall, initiatedTotal]
        init := by intro h; cases h
        noinit := fun _ => ⟨rfl, rfl, rfl⟩ }
  | vmRelease dst amt =>
    obtain ⟨hd, hle, rfl⟩ := exec_release_some h
    exact
      { supply_eq := by
          show (∑ a, xfer s.bal holderAddr dst amt a) + s.minted = supply s + s.minted
          rw [sum_xfer dst hle]; simp only [supply]
        holder_eq := by
          show xfer s.bal holderAddr dst amt holderAddr + s.given + s.recovered
              + (s.released + amt) + s.minted + s.burnt + s.forced
            = s.bal holderAddr + s.given + s.recovered + s.released
              + s.minted + s.burnt + s.forced
          rw [xfer_holder_out amt hd]; omega
        out_eq := by dsimp only [Call.out]; omega
        in_eq := by dsimp only [Call.inn]; omega
        pre_eq := rfl
        calls_eq := by simp [Call.trackerCall]
        replay_eq := rfl
        given_eq := rfl
        burnt_eq := rfl
        init := by intro h; cases h
        noinit := fun _ => ⟨rfl, rfl, rfl⟩ }

/-! ## The combined invariant -/

/-- Everything the run-level properties need, relative to the start `s₀` and the labels. -/
structure Inv {T : Type} (tr : Tracker T) (s₀ s : State T) (cs : List Call) : Prop where
  supply_eq : supply s = supply s₀ + s.minted
  minted_eq : s.minted = (if s.initialized then INITIAL else 0)
  count_eq : cs.countP Call.isInitL2 = (if s.initialized then 1 else 0)
  holder_eq : s.bal holderAddr + s.given + s.recovered + s.released
      = s₀.bal holderAddr + s.minted + s.burnt + s.forced
  calls_eq : s.calls = cs.filterMap Call.trackerCall
  replay_eq : replay tr s₀.trk s.calls = some s.trk
  fin_eq : finalizedTotal s.calls = s.given
  init_eq : initiatedTotal s.calls = s.burnt
  pre_eq : s.preV31 = s₀.preV31
  callers : ∀ caller l1, Call.initL2 caller l1 ∈ cs → caller = complexUpgraderAddr
  l1_eq : s.initialized = true → ∃ l1, Call.initL2 complexUpgraderAddr l1 ∈ cs ∧ s.l1ChainId = l1

theorem replay_append {T : Type} (tr : Tracker T) (L M : List TrackerCall) (t₀ : T) :
    replay tr t₀ (L ++ M) = (replay tr t₀ L).bind (fun t => replay tr t M) := by
  induction L generalizing t₀ with
  | nil => rfl
  | cons y L ih =>
    cases y with
    | finalize c a =>
      simp only [replay, List.cons_append]
      cases tr.finalize t₀ c a with
      | none => rfl
      | some t₁ => simpa using ih t₁
    | initiate c a =>
      simp only [replay, List.cons_append]
      cases tr.initiate t₀ c a with
      | none => rfl
      | some t₁ => simpa using ih t₁

theorem finalizedTotal_append (L M : List TrackerCall) :
    finalizedTotal (L ++ M) = finalizedTotal L + finalizedTotal M := by
  induction L with
  | nil => simp [finalizedTotal]
  | cons y L ih => cases y <;> simp [finalizedTotal, ih]; omega

theorem initiatedTotal_append (L M : List TrackerCall) :
    initiatedTotal (L ++ M) = initiatedTotal L + initiatedTotal M := by
  induction L with
  | nil => simp [initiatedTotal]
  | cons y L ih => cases y <;> simp [initiatedTotal, ih]; omega

theorem inv_genesis {T : Type} (tr : Tracker T) {s₀ : State T} (g : Genesis s₀) :
    Inv tr s₀ s₀ [] where
  supply_eq := by rw [g.minted, Nat.add_zero]
  minted_eq := by rw [g.minted, g.notInit]; simp
  count_eq := by rw [g.notInit]; simp
  holder_eq := by rw [g.given, g.recovered, g.released, g.minted, g.burnt, g.forced]
  calls_eq := by rw [g.noCalls]; simp
  replay_eq := by rw [g.noCalls]; simp [replay]
  fin_eq := by rw [g.noCalls, g.given]; simp [finalizedTotal]
  init_eq := by rw [g.noCalls, g.burnt]; simp [initiatedTotal]
  pre_eq := rfl
  callers := by intro _ _ h; cases h
  l1_eq := by intro h; rw [g.notInit] at h; cases h

theorem filterMap_singleton (c : Call) :
    [c].filterMap Call.trackerCall = c.trackerCall.toList := by
  cases h : c.trackerCall <;> simp [List.filterMap_cons, h]

theorem inv_step {T : Type} {tr : Tracker T} {s₀ s s' : State T} {cs : List Call} {c : Call}
    (I : Inv tr s₀ s cs) (h : exec tr s c = some s') : Inv tr s₀ s' (cs ++ [c]) := by
  have F := step_facts h
  have hsup := I.supply_eq
  have hmint := I.minted_eq
  have hcount := I.count_eq
  have hholder := I.holder_eq
  have hFs := F.supply_eq
  have hFh := F.holder_eq
  cases hi : c.isInitL2 with
  | false =>
    obtain ⟨e1, e2, e3⟩ := F.noinit hi
    exact
      { supply_eq := by omega
        minted_eq := by rw [e1, e3]; exact hmint
        count_eq := by
          rw [List.countP_append, e1, hcount]; simp [hi]
        holder_eq := by omega
        calls_eq := by
          rw [F.calls_eq, I.calls_eq, List.filterMap_append, filterMap_singleton]
        replay_eq := by
          rw [F.calls_eq, replay_append, I.replay_eq]; exact F.replay_eq
        fin_eq := by rw [F.calls_eq, finalizedTotal_append, I.fin_eq, F.given_eq]
        init_eq := by rw [F.calls_eq, initiatedTotal_append, I.init_eq, F.burnt_eq]
        pre_eq := by rw [F.pre_eq, I.pre_eq]
        callers := by
          intro caller l1 hm
          rcases List.mem_append.mp hm with hm | hm
          · exact I.callers caller l1 hm
          · rw [List.mem_singleton] at hm; subst hm; cases hi
        l1_eq := by
          intro hinit
          rw [e1] at hinit
          obtain ⟨l1, hm, hl⟩ := I.l1_eq hinit
          exact ⟨l1, List.mem_append_left _ hm, by rw [e2]; exact hl⟩ }
  | true =>
    obtain ⟨l1, rfl, hni, hinit', hl1, hm'⟩ := F.init hi
    rw [hni] at hmint hcount
    simp only [Bool.false_eq_true, ite_false] at hmint hcount
    exact
      { supply_eq := by omega
        minted_eq := by rw [hinit', hm', hmint]; simp
        count_eq := by
          rw [List.countP_append, hinit', hcount]; simp [List.countP_cons, Call.isInitL2]
        holder_eq := by omega
        calls_eq := by
          rw [F.calls_eq, I.calls_eq, List.filterMap_append]
          simp [Call.trackerCall]
        replay_eq := by
          rw [F.calls_eq, replay_append, I.replay_eq]; exact F.replay_eq
        fin_eq := by rw [F.calls_eq, finalizedTotal_append, I.fin_eq, F.given_eq]
        init_eq := by rw [F.calls_eq, initiatedTotal_append, I.init_eq, F.burnt_eq]
        pre_eq := by rw [F.pre_eq, I.pre_eq]
        callers := by
          intro caller l1' hm
          rcases List.mem_append.mp hm with hm | hm
          · exact I.callers caller l1' hm
          · rw [List.mem_singleton] at hm; cases hm; rfl
        l1_eq := fun _ => ⟨l1, List.mem_append_right _ (List.mem_singleton.mpr rfl), hl1⟩ }

theorem inv_run {T : Type} {tr : Tracker T} {s₀ s : State T} {cs : List Call}
    (g : Genesis s₀) (r : Run tr s₀ cs s) : Inv tr s₀ s cs := by
  induction r with
  | nil => exact inv_genesis tr g
  | snoc _ h ih => exact inv_step ih h

/-! ## Run-level properties -/

/-- **HEADLINE: NATIVE SUPPLY IS MINTED ONLY BY THE ONE `initL2`.** -/
theorem SupplyOnlyMintedByInitL2 : Properties.SupplyOnlyMintedByInitL2 := by
  intro T tr s₀ s cs g r
  have I := inv_run g r
  exact ⟨I.supply_eq, I.minted_eq, I.count_eq⟩

/-- **`initL2` IS THE UPGRADER'S, ONCE.** -/
theorem InitL2OnlyByUpgraderOnce : Properties.InitL2OnlyByUpgraderOnce := by
  intro T tr s₀ s cs g r
  have I := inv_run g r
  exact ⟨I.callers, I.l1_eq, I.pre_eq⟩

/-- **HEADLINE: THE HOLDER AND CIRCULATING LEDGERS.** -/
theorem HolderAndCirculatingLedger : Properties.HolderAndCirculatingLedger := by
  intro T tr s₀ s cs g r
  have I := inv_run g r
  refine ⟨I.holder_eq, ?_⟩
  have h1 := circulating_add s
  have h2 := circulating_add s₀
  have h3 := I.supply_eq
  have h4 := I.holder_eq
  omega

/-- **THE TRACKER SEES EVERY BRIDGE MOVEMENT OF THE HOLDER.** -/
theorem TrackerSeesEveryBridgeMovement : Properties.TrackerSeesEveryBridgeMovement := by
  intro T tr s₀ s cs g r
  have I := inv_run g r
  exact ⟨I.calls_eq, I.replay_eq, I.fin_eq, I.init_eq⟩

/-! ## Per-call movement of the circulating supply -/

/-- One successful call moves the circulating supply by exactly its out-flow minus its in-flow. -/
theorem circ_step {T : Type} {tr : Tracker T} {s s' : State T} {c : Call}
    (h : exec tr s c = some s') : circulating s' + c.inn = circulating s + c.out := by
  have F := step_facts h
  have h1 := F.supply_eq
  have h2 := F.holder_eq
  have h3 := F.out_eq
  have h4 := F.in_eq
  have h5 := circulating_add s
  have h6 := circulating_add s'
  omega

/-- **CIRCULATING SUPPLY RISES ONLY THROUGH THE INBOUND PATHS.** -/
theorem CirculatingRisesOnlyByInboundPaths : Properties.CirculatingRisesOnlyByInboundPaths := by
  intro T tr s s' c h hlt
  have hc := circ_step h
  cases c with
  | transfer f t amt => simp only [Call.inn, Call.out] at hc; omega
  | forceToHolder f amt => simp only [Call.inn, Call.out] at hc; omega
  | holderReceive caller amt => simp only [Call.inn, Call.out] at hc; omega
  | initL2 caller l1 => simp only [Call.inn, Call.out] at hc; omega
  | burn caller v ch => simp only [Call.inn, Call.out] at hc; omega
  | give caller dst amt ch =>
    simp only [Call.inn, Call.out] at hc
    obtain ⟨rfl, hcase⟩ := execGive_some (show execGive tr s caller dst amt ch = some s' from h)
    rcases hcase with ⟨h0, _⟩ | ⟨_, t', hfin, _⟩
    · omega
    · exact Or.inl ⟨dst, amt, ch, rfl, by rw [hfin]; simp, by omega⟩
  | recover caller dst amt ch =>
    simp only [Call.inn, Call.out] at hc
    obtain ⟨rfl, hcase⟩ :=
      execRecover_some (show execRecover tr s caller dst amt ch = some s' from h)
    rcases hcase with ⟨h0, _⟩ | ⟨_, hneutral, _⟩
    · omega
    · exact Or.inr (Or.inl ⟨dst, amt, ch, rfl, hneutral, by omega⟩)
  | vmRelease dst amt =>
    simp only [Call.inn, Call.out] at hc
    exact Or.inr (Or.inr ⟨dst, amt, rfl, by omega⟩)

/-- **CIRCULATING SUPPLY FALLS ONLY THROUGH THE OUTBOUND PATHS.** -/
theorem CirculatingFallsOnlyByOutboundPaths : Properties.CirculatingFallsOnlyByOutboundPaths := by
  intro T tr s s' c h hlt
  have hc := circ_step h
  cases c with
  | transfer f t amt => simp only [Call.inn, Call.out] at hc; omega
  | holderReceive caller amt => simp only [Call.inn, Call.out] at hc; omega
  | initL2 caller l1 => simp only [Call.inn, Call.out] at hc; omega
  | give caller dst amt ch => simp only [Call.inn, Call.out] at hc; omega
  | recover caller dst amt ch => simp only [Call.inn, Call.out] at hc; omega
  | vmRelease dst amt => simp only [Call.inn, Call.out] at hc; omega
  | burn caller v ch =>
    simp only [Call.inn, Call.out] at hc
    obtain ⟨_, hcaller, t', hini, _⟩ :=
      execBurn_some (show execBurn tr s caller v ch = some s' from h)
    exact Or.inl ⟨caller, v, ch, rfl, hcaller, by rw [hini]; simp, by omega⟩
  | forceToHolder f amt =>
    simp only [Call.inn, Call.out] at hc
    exact Or.inr ⟨f, amt, rfl, by omega⟩

/-! ## `totalSupply()` -/

theorem INITIAL_pos : 0 < INITIAL := by unfold INITIAL; norm_num

theorem INITIAL_lt : INITIAL < 2 ^ 256 := by unfold INITIAL; norm_num

/-- **AFTER `initL2`, `totalSupply()` IS THE CIRCULATING SUPPLY.** -/
theorem TotalSupplyIsCirculating : Properties.TotalSupplyIsCirculating := by
  intro T tr s₀ s cs g r hpre hbound hinit
  have I := inv_run g r
  have hm := I.minted_eq
  rw [hinit] at hm
  simp only [if_true] at hm
  have hs := I.supply_eq
  have hp := I.pre_eq
  have hle := le_supply s holderAddr
  have hc := circulating_add s
  unfold totalSupplyView
  rw [if_neg (by omega), if_neg (by omega)]
  exact congrArg some (by omega)

/-- **…AND WITHOUT THE BACKFILL PREMISE, OFF BY A CONSTANT.** -/
theorem TotalSupplyErrorIsConstant : Properties.TotalSupplyErrorIsConstant := by
  intro T tr s₀ s cs g r hinit
  have I := inv_run g r
  have hm := I.minted_eq
  rw [hinit] at hm
  simp only [if_true] at hm
  have hs := I.supply_eq
  have hp := I.pre_eq
  have hc := circulating_add s
  omega

/-- **SOURCE NATSPEC REFUTED: `totalSupply()` OVERSTATES BY `2^127 - 1` BEFORE `initL2`.** -/
theorem TotalSupplyOverstatedBeforeInitL2 : Properties.TotalSupplyOverstatedBeforeInitL2 := by
  intro T tr s₀ s cs g r hpre hbound hinit
  have I := inv_run g r
  have hm := I.minted_eq
  rw [hinit] at hm
  simp only [Bool.false_eq_true, if_false] at hm
  have hs := I.supply_eq
  have hp := I.pre_eq
  have hle := le_supply s holderAddr
  have hc := circulating_add s
  unfold totalSupplyView
  rw [if_neg (by omega), if_neg (by omega)]
  exact congrArg some (by omega)

/-- **SOURCE NATSPEC CONFIRMED: NO BALANCE OVERFLOWS.** -/
theorem NoBalanceOverflows : Properties.NoBalanceOverflows := by
  intro T tr s₀ s cs g r hbound
  have I := inv_run g r
  have hm := I.minted_eq
  have hs := I.supply_eq
  have hlt : supply s < 2 ^ 256 := by
    cases hi : s.initialized <;> rw [hi] at hm <;> simp at hm <;> omega
  exact ⟨hlt, fun a => lt_of_le_of_lt (le_supply s a) hlt⟩

/-! ## Countermodels and witness -/

theorem genesis_empty : Genesis emptyGenesis :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem supply_empty : supply emptyGenesis = 0 := by
  show ∑ _a : Address, (0 : ℕ) = 0
  simp

theorem execGive_ok {T : Type} {tr : Tracker T} {s : State T} {dst : Address} {amt : ℕ}
    {ch : UInt256} {t' : T} (h0 : amt ≠ 0) (hf : tr.finalize s.trk ch amt = some t')
    (hle : amt ≤ s.bal holderAddr) (hd : dst ≠ holderAddr) (hb : dst ≠ baseTokenAddr) :
    execGive tr s interopHandlerAddr dst amt ch
      = some { s with bal := xfer s.bal holderAddr dst amt, trk := t',
                      calls := s.calls ++ [.finalize ch amt], given := s.given + amt } := by
  unfold execGive sendValue
  simp [h0, hf, hle, hd, hb]

/-- **COUNTERMODEL: THE `initL2` FLAG CHECK IS LOAD-BEARING.** -/
theorem InitL2FlagIsLoadBearing : Properties.InitL2FlagIsLoadBearing := by
  have hb : (initL2Effect (initL2Effect emptyGenesis 1) 1).bal holderAddr = INITIAL + INITIAL := by
    rw [holder_initL2Effect, holder_initL2Effect]
    show 0 + INITIAL + INITIAL = _
    omega
  have hp : (initL2Effect (initL2Effect emptyGenesis 1) 1).preV31 = 0 := rfl
  refine ⟨emptyGenesis, initL2Effect emptyGenesis 1, initL2Effect (initL2Effect emptyGenesis 1) 1,
    genesis_empty, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [supply_empty]; rfl
  · simp [execInitL2NoFlag]
  · simp [execInitL2NoFlag]
  · rw [supply_initL2Effect, supply_initL2Effect]; omega
  · unfold totalSupplyView
    have h1 := INITIAL_pos
    have h2 := INITIAL_lt
    rw [if_neg (by rw [hp]; omega), if_pos (by rw [hp, hb]; omega)]
    exact fun h => by cases h
  · simp [execInitL2, emptyGenesis]
  · simp [execInitL2, initL2Effect]

/-- **COUNTERMODEL: `give`'S CALLER CHECK IS LOAD-BEARING.** -/
theorem GiveGuardIsLoadBearing : Properties.GiveGuardIsLoadBearing := by
  have hne : userAddr ≠ interopHandlerAddr := by decide
  have hh : userAddr ≠ holderAddr := by decide
  have hbt : userAddr ≠ baseTokenAddr := by decide
  have hbal : (1 : ℕ) ≤ witness₁.bal holderAddr := by
    show 1 ≤ (initL2Effect emptyGenesis 1).bal holderAddr
    rw [holder_initL2Effect]
    have := INITIAL_pos
    omega
  have hok := execGive_ok (tr := acceptAll) (s := witness₁) (dst := userAddr) (amt := 1)
    (ch := 0) (t' := ()) (by norm_num) rfl hbal hh hbt
  refine ⟨acceptAll, witness₁, _, userAddr, 1, hne, by norm_num, hok, ?_, ?_, ?_⟩
  · show xfer witness₁.bal holderAddr userAddr 1 userAddr = witness₁.bal userAddr + 1
    rw [xfer_apply]; simp [hh]
  · have := circ_step (tr := acceptAll) (s := witness₁)
      (c := Call.give interopHandlerAddr userAddr 1 0) hok
    simpa [Call.inn, Call.out] using this
  · show execGive acceptAll witness₁ userAddr userAddr 1 0 = none
    unfold execGive
    rw [if_pos hne]

/-- **THE PREMISES ARE SATISFIABLE, NONTRIVIALLY.** -/
theorem SupplyWitness : Properties.SupplyWitness := by
  have hbound : supply emptyGenesis + INITIAL < 2 ^ 256 := by
    rw [supply_empty]; have := INITIAL_lt; omega
  have hpre : emptyGenesis.preV31 = supply emptyGenesis := by rw [supply_empty]; rfl
  have h1 : exec acceptAll emptyGenesis (.initL2 complexUpgraderAddr 1) = some witness₁ := by
    simp [exec, execInitL2, emptyGenesis, witness₁]
  have hbal1 : (100 : ℕ) ≤ witness₁.bal holderAddr := by
    show 100 ≤ (initL2Effect emptyGenesis 1).bal holderAddr
    rw [holder_initL2Effect]
    show 100 ≤ 0 + INITIAL
    unfold INITIAL; norm_num
  have h2 : exec acceptAll witness₁ (.give interopHandlerAddr interopCenterAddr 100 5)
      = some witness₂ :=
    execGive_ok (tr := acceptAll) (s := witness₁) (dst := interopCenterAddr) (amt := 100)
      (ch := 5) (t' := ()) (by norm_num) rfl hbal1 (by decide) (by decide)
  have hbal2 : (40 : ℕ) ≤ witness₂.bal interopCenterAddr := by
    show 40 ≤ xfer witness₁.bal holderAddr interopCenterAddr 100 interopCenterAddr
    rw [xfer_apply]; simp
  have h3 : exec acceptAll witness₂ (.burn interopCenterAddr 40 9) = some witness₃ := by
    show execBurn acceptAll witness₂ interopCenterAddr 40 9 = some witness₃
    unfold execBurn
    rw [if_neg (by omega), if_neg (by simp)]
    rfl
  have hbal3 : (7 : ℕ) ≤ witness₃.bal holderAddr := by
    show 7 ≤ xfer witness₂.bal interopCenterAddr holderAddr 40 holderAddr
    rw [xfer_holder_in 40 (by decide)]; omega
  have h4 : exec acceptAll witness₃ (.vmRelease userAddr 7) = some witness₄ := by
    have hu : userAddr ≠ holderAddr := by decide
    simp only [exec]
    rw [if_neg (by push Not; exact ⟨hu, by omega⟩)]
    rfl
  have hrun : Run acceptAll emptyGenesis
      [.initL2 complexUpgraderAddr 1, .give interopHandlerAddr interopCenterAddr 100 5,
        .burn interopCenterAddr 40 9, .vmRelease userAddr 7] witness₄ :=
    Run.snoc (Run.snoc (Run.snoc (Run.snoc Run.nil h1) h2) h3) h4
  have hgiven : witness₄.given = 100 := rfl
  have hburnt : witness₄.burnt = 40 := rfl
  have hrel : witness₄.released = 7 := rfl
  have hrec : witness₄.recovered = 0 := rfl
  have hforced : witness₄.forced = 0 := rfl
  have hinit : witness₄.initialized = true := rfl
  have hledger := (HolderAndCirculatingLedger Unit acceptAll _ _ _ genesis_empty hrun).2
  refine ⟨acceptAll, emptyGenesis, witness₄, _, genesis_empty, hpre, hbound, hrun, hinit,
    by omega, by omega, by omega, by omega, ?_⟩
  exact TotalSupplyIsCirculating Unit acceptAll _ _ _ genesis_empty hrun hpre hbound hinit

end Contracts.L2BaseToken
