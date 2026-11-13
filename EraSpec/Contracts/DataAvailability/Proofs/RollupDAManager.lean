import EraSpec.Contracts.DataAvailability.Properties.RollupDAManager

/-!
# Proofs: `RollupDAManager` — the allowed DA pairs change only by the owner

Proofs of `EraSpec.Contracts.DataAvailability.Properties.RollupDAManager`. Each entry point is
inverted once (`exec_*_some`); the run-level results are inductions over `ReachLog`.
-/

namespace Contracts.DataAvailability

/-! ## One call -/

theorem exec_updateDAPair_some {M M' : Manager} {c v : Address} {s : L2DACommitmentScheme}
    {st : Bool} (h : exec M (.updateDAPair c v s st) = some M') :
    c = M.owner ∧ v ≠ 0 ∧ s ≠ .NONE ∧ M' = setPair M v s st := by
  simp only [exec] at h
  split_ifs at h with h1 h2 h3
  exact ⟨not_not.mp h1, h2, h3, (Option.some.inj h).symm⟩

theorem exec_transferOwnership_some {M M' : Manager} {c n : Address}
    (h : exec M (.transferOwnership c n) = some M') :
    c = M.owner ∧ M' = { M with pendingOwner := n } := by
  simp only [exec] at h
  split_ifs at h with h1
  exact ⟨not_not.mp h1, (Option.some.inj h).symm⟩

theorem exec_acceptOwnership_some {M M' : Manager} {c : Address}
    (h : exec M (.acceptOwnership c) = some M') :
    M.pendingOwner = c ∧ M' = { M with owner := c, pendingOwner := 0 } := by
  simp only [exec] at h
  split_ifs at h with h1
  exact ⟨not_not.mp h1, (Option.some.inj h).symm⟩

theorem exec_renounceOwnership_some {M M' : Manager} {c : Address}
    (h : exec M (.renounceOwnership c) = some M') :
    c = M.owner ∧ M' = { M with owner := 0, pendingOwner := 0 } := by
  simp only [exec] at h
  split_ifs at h with h1
  exact ⟨not_not.mp h1, (Option.some.inj h).symm⟩

/-- Every successful call is made by the owner or by the pending owner. -/
theorem exec_some_caller {M M' : Manager} {c : MCall} (h : exec M c = some M') :
    c.caller = M.owner ∨ c.caller = M.pendingOwner := by
  cases c with
  | updateDAPair c v s st => exact Or.inl (exec_updateDAPair_some h).1
  | transferOwnership c n => exact Or.inl (exec_transferOwnership_some h).1
  | acceptOwnership c => exact Or.inr (exec_acceptOwnership_some h).1.symm
  | renounceOwnership c => exact Or.inl (exec_renounceOwnership_some h).1

theorem lastStatus_snoc (log : List (Manager × MCall)) (pre : Manager) (c : MCall) (v : Address)
    (s : L2DACommitmentScheme) :
    lastStatus (log ++ [(pre, c)]) v s
      = match c with
        | .updateDAPair _ v' s' st => if v' = v ∧ s' = s then some st else lastStatus log v s
        | _ => lastStatus log v s := by
  unfold lastStatus
  rw [List.foldl_append]
  cases c <;> rfl

theorem Nominated.mono {M₀ : Manager} {log : List (Manager × MCall)} {a : Address}
    (e : Manager × MCall) (h : Nominated M₀ log a) : Nominated M₀ (log ++ [e]) a := by
  rcases h with h | ⟨pre, hp⟩
  · exact Or.inl h
  · exact Or.inr ⟨pre, List.mem_append_left _ hp⟩

/-! ## Runs -/

theorem pairs_follow_owner_updates {M₀ M : Manager} {log : List (Manager × MCall)}
    (h : ReachLog M₀ M log) :
    (∀ v s, M.allowed v s = (lastStatus log v s).getD (M₀.allowed v s))
    ∧ ∀ pre c v s st, (pre, MCall.updateDAPair c v s st) ∈ log →
        c = pre.owner ∧ v ≠ 0 ∧ s ≠ L2DACommitmentScheme.NONE := by
  induction h with
  | refl => exact ⟨fun v s => rfl, fun _ _ _ _ _ hm => by simp at hm⟩
  | tail hr hex ih =>
    rename_i M M' log c
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun v s => ?_, fun pre c' v s st hm => ?_⟩
    · rw [lastStatus_snoc]
      cases c with
      | updateDAPair c v' s' st =>
        obtain ⟨-, -, -, rfl⟩ := exec_updateDAPair_some hex
        show (if v = v' ∧ s = s' then st else M.allowed v s) = _
        by_cases hvs : v' = v ∧ s' = s
        · rw [ite_eq_left ⟨hvs.1.symm, hvs.2.symm⟩]
          simp only [ite_eq_left hvs, Option.getD_some]
        · rw [ite_eq_right (fun hc => hvs ⟨hc.1.symm, hc.2.symm⟩)]
          simp only [ite_eq_right hvs]
          exact ih1 v s
      | transferOwnership c n =>
        obtain ⟨-, rfl⟩ := exec_transferOwnership_some hex
        exact ih1 v s
      | acceptOwnership c =>
        obtain ⟨-, rfl⟩ := exec_acceptOwnership_some hex
        exact ih1 v s
      | renounceOwnership c =>
        obtain ⟨-, rfl⟩ := exec_renounceOwnership_some hex
        exact ih1 v s
    · rcases List.mem_append.mp hm with hm | hm
      · exact ih2 pre c' v s st hm
      · rw [List.mem_singleton] at hm
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hm
        obtain ⟨h1, h2, h3, -⟩ := exec_updateDAPair_some hex
        exact ⟨h1, h2, h3⟩

theorem exec_preserves_noInvalidPairs {M M' : Manager} {c : MCall} (h : exec M c = some M')
    (hM : NoInvalidPairs M) : NoInvalidPairs M' := by
  cases c with
  | updateDAPair c v s st =>
    obtain ⟨-, hv, hs, rfl⟩ := exec_updateDAPair_some h
    refine ⟨fun s' => ?_, fun v' => ?_⟩
    · show (if (0 : Address) = v ∧ s' = s then st else M.allowed 0 s') = false
      rw [ite_eq_right (fun hc => hv hc.1.symm)]
      exact hM.1 s'
    · show (if v' = v ∧ L2DACommitmentScheme.NONE = s then st else M.allowed v' .NONE) = false
      rw [ite_eq_right (fun hc => hs hc.2.symm)]
      exact hM.2 v'
  | transferOwnership c n =>
    obtain ⟨-, rfl⟩ := exec_transferOwnership_some h
    exact hM
  | acceptOwnership c =>
    obtain ⟨-, rfl⟩ := exec_acceptOwnership_some h
    exact hM
  | renounceOwnership c =>
    obtain ⟨-, rfl⟩ := exec_renounceOwnership_some h
    exact hM

theorem reachLog_preserves_noInvalidPairs {M₀ M : Manager} {log : List (Manager × MCall)}
    (h : ReachLog M₀ M log) (h0 : NoInvalidPairs M₀) : NoInvalidPairs M := by
  induction h with
  | refl => exact h0
  | tail _ hex ih => exact exec_preserves_noInvalidPairs hex (ih h0)

theorem noInvalidPairs_deploy (d : Address) : NoInvalidPairs (deploy d) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem owner_changes_only_by_handover {M₀ M : Manager} {log : List (Manager × MCall)}
    (h : ReachLog M₀ M log) :
    (M.pendingOwner = 0 ∨ Nominated M₀ log M.pendingOwner)
    ∧ (M.owner = M₀.owner ∨ M.owner = 0
        ∨ (Nominated M₀ log M.owner
            ∧ ∃ pre, (pre, MCall.acceptOwnership M.owner) ∈ log ∧ pre.pendingOwner = M.owner)) := by
  induction h with
  | refl => exact ⟨Or.inr (Or.inl rfl), Or.inl rfl⟩
  | tail hr hex ih =>
    rename_i M M' log c
    obtain ⟨ihp, iho⟩ := ih
    -- both facts survive a call that keeps the owner and the pending owner
    have keep : M'.owner = M.owner → M'.pendingOwner = M.pendingOwner →
        (M'.pendingOwner = 0 ∨ Nominated M₀ (log ++ [(M, c)]) M'.pendingOwner)
        ∧ (M'.owner = M₀.owner ∨ M'.owner = 0
          ∨ (Nominated M₀ (log ++ [(M, c)]) M'.owner
            ∧ ∃ pre, (pre, MCall.acceptOwnership M'.owner) ∈ log ++ [(M, c)]
                ∧ pre.pendingOwner = M'.owner)) := by
      intro ho hp
      rw [ho, hp]
      refine ⟨ihp.imp id (Nominated.mono _), ?_⟩
      rcases iho with h1 | h1 | ⟨hn, pre, hm, hpre⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr ⟨hn.mono _, pre, List.mem_append_left _ hm, hpre⟩)
    cases c with
    | updateDAPair c v s st =>
      obtain ⟨-, -, -, rfl⟩ := exec_updateDAPair_some hex
      exact keep rfl rfl
    | transferOwnership c n =>
      obtain ⟨hc, rfl⟩ := exec_transferOwnership_some hex
      subst hc
      refine ⟨Or.inr (Or.inr ⟨M, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩), ?_⟩
      show M.owner = M₀.owner ∨ M.owner = 0 ∨ _
      rcases iho with h1 | h1 | ⟨hn, pre, hm, hpre⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr ⟨hn.mono _, pre, List.mem_append_left _ hm, hpre⟩)
    | acceptOwnership c =>
      obtain ⟨hc, rfl⟩ := exec_acceptOwnership_some hex
      refine ⟨Or.inl rfl, ?_⟩
      show c = M₀.owner ∨ c = 0 ∨ _
      rcases ihp with h0 | hn
      · exact Or.inr (Or.inl (hc.symm.trans h0))
      · rw [hc] at hn
        exact Or.inr (Or.inr ⟨hn.mono _, M,
          List.mem_append_right _ (List.mem_singleton.mpr rfl), hc⟩)
    | renounceOwnership c =>
      obtain ⟨-, rfl⟩ := exec_renounceOwnership_some hex
      exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩

theorem outsiders_cannot_act {M₀ M : Manager} {log : List (Manager × MCall)}
    (h : ReachLog M₀ M log)
    (hall : ∀ e ∈ log, e.2.caller ≠ M₀.owner ∧ e.2.caller ≠ M₀.pendingOwner) :
    log = [] ∧ M = M₀ := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail hr hex ih =>
    rename_i M M' log c
    obtain ⟨-, hM⟩ := ih (fun e he => hall e (List.mem_append_left _ he))
    subst hM
    have hc := hall (M, c) (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    rcases exec_some_caller hex with h1 | h1
    · exact absurd h1 hc.1
    · exact absurd h1 hc.2

/-! ## The named properties -/

/-- **HEADLINE: THE ALLOW-LIST IS EXACTLY WHAT THE OWNERS WROTE.** -/
theorem PairsFollowOwnerUpdates : Properties.PairsFollowOwnerUpdates :=
  fun _ _ _ h => pairs_follow_owner_updates h

/-- **THE ZERO VALIDATOR AND THE `NONE` SCHEME ARE NEVER ALLOWED.** -/
theorem InvalidPairsNeverAllowed : Properties.InvalidPairsNeverAllowed :=
  ⟨fun _ _ h0 ⟨_, h⟩ => reachLog_preserves_noInvalidPairs h h0,
   fun d _ ⟨_, h⟩ => reachLog_preserves_noInvalidPairs h (noInvalidPairs_deploy d)⟩

/-- **THE OWNER CHANGES ONLY BY RENOUNCING OR BY A TWO-STEP HANDOVER.** -/
theorem OwnerChangesOnlyByHandover : Properties.OwnerChangesOnlyByHandover :=
  fun _ _ _ h => owner_changes_only_by_handover h

/-- **OUTSIDERS CANNOT ACT.** -/
theorem OutsidersCannotAct : Properties.OutsidersCannotAct :=
  fun _ _ _ h hall => outsiders_cannot_act h hall

/-- **A RENOUNCED MANAGER IS FROZEN FOR GOOD.** -/
theorem RenouncedManagerFrozen : Properties.RenouncedManagerFrozen := by
  refine ⟨fun M M' c h => ?_, fun M₀ M log ho hp h hall => ?_⟩
  · obtain ⟨hc, rfl⟩ := exec_renounceOwnership_some h
    exact ⟨hc, rfl, rfl, rfl⟩
  · exact outsiders_cannot_act h (fun e he => by
      rw [ho, hp]; exact ⟨hall e he, hall e he⟩)

/-- **COUNTERMODEL: `onlyOwner` IS LOAD-BEARING.** -/
theorem OwnerCheckLoadBearing : Properties.OwnerCheckLoadBearing := by
  refine ⟨deploy 1, setPair (deploy 1) 5 .BLOBS_AND_PUBDATA_KECCAK256 true, 2, 5,
    .BLOBS_AND_PUBDATA_KECCAK256, by decide, by decide, rfl, ?_, ?_, ?_⟩
  · simp [exec, deploy]
  · simp [updateDAPairNoOwner]
  · simp [setPair]

/-- **COUNTERMODEL: `validDAConfiguration` IS LOAD-BEARING.** -/
theorem ValidConfigurationCheckLoadBearing : Properties.ValidConfigurationCheckLoadBearing := by
  refine ⟨1, 5, .BLOBS_AND_PUBDATA_KECCAK256,
    setPair (deploy 1) 0 .BLOBS_AND_PUBDATA_KECCAK256 true, setPair (deploy 1) 5 .NONE true,
    by decide, by decide, noInvalidPairs_deploy 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [exec, deploy]
  · simp [exec, deploy]
  · simp [updateDAPairUnchecked, deploy]
  · intro h
    have := h.1 .BLOBS_AND_PUBDATA_KECCAK256
    simp [setPair] at this
  · simp [updateDAPairUnchecked, deploy]
  · intro h
    have := h.2 5
    simp [setPair] at this

/-- **WITNESS: A RUN WITH AN UPDATE, A REVOCATION AND A HANDOVER.** -/
theorem ManagerRunWitness : Properties.ManagerRunWitness := by
  let M0 : Manager := deploy 1
  let M1 : Manager := setPair M0 5 .BLOBS_AND_PUBDATA_KECCAK256 true
  let M2 : Manager := setPair M1 6 .PUBDATA_KECCAK256 true
  let M3 : Manager := { M2 with pendingOwner := 2 }
  let M4 : Manager := { M3 with owner := 2, pendingOwner := 0 }
  let M5 : Manager := setPair M4 6 .PUBDATA_KECCAK256 false
  have r1 : ReachLog M0 M1 ([] ++ [(M0, MCall.updateDAPair 1 5 .BLOBS_AND_PUBDATA_KECCAK256 true)]) :=
    ReachLog.tail ReachLog.refl (by simp [exec, M0, M1, deploy])
  have r2 := ReachLog.tail (c := MCall.updateDAPair 1 6 .PUBDATA_KECCAK256 true) (M' := M2) r1
    (by simp [exec, M0, M1, M2, deploy, setPair])
  have r3 := ReachLog.tail (c := MCall.transferOwnership 1 2) (M' := M3) r2
    (by simp [exec, M0, M1, M2, M3, deploy, setPair])
  have r4 := ReachLog.tail (c := MCall.acceptOwnership 2) (M' := M4) r3
    (by simp [exec, M3, M4])
  have r5 := ReachLog.tail (c := MCall.updateDAPair 2 6 .PUBDATA_KECCAK256 false) (M' := M5) r4
    (by simp [exec, M4, M5])
  refine ⟨M5, setPair M5 7 .EMPTY_NO_DA true, _, r5, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [M5, M4, M3, M2, M1, M0, setPair, deploy]
  · simp [M5, setPair]
  · simp [lastStatus]
  · simp [exec, M5, M4, setPair]
  · simp [exec, M5, M4, setPair]
  · simp [setPair]

end Contracts.DataAvailability
