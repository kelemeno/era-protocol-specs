import EraSpec.Contracts.L2AdminFactory.Properties.Model

/-!
# Proofs: every admin the factory deploys carries the required restrictions

The run-level results follow from one invariant (`inv`): every logged admin sits at the
`CREATE` address of its nonce, the nonces used are distinct and lie in `[n₀, nonce)`, and every
logged restriction list extends `required` without duplicates.
-/

namespace Contracts.L2AdminFactory

/-- The run invariant. -/
private def Inv (K : Config) (n₀ : ℕ) (s : State) : Prop :=
  n₀ ≤ s.nonce ∧ (s.admins.map AdminRec.nonce).Nodup ∧
    ∀ a ∈ s.admins, K.required <+: a.restrictions ∧ a.restrictions.Nodup ∧
      a.addr = K.createAddr a.nonce ∧ n₀ ≤ a.nonce ∧ a.nonce < s.nonce

private lemma inv_of_reach {K : Config} {n₀ : ℕ} {s : State} (h : Reach K ⟨n₀, []⟩ s) :
    Inv K n₀ s := by
  induction h with
  | refl => exact ⟨le_rfl, by simp, by simp⟩
  | step _ hs ih =>
    obtain ⟨hn, hnd, hall⟩ := ih
    cases hs with
    | deploy _ hok =>
      refine ⟨by simp [deployed]; omega, ?_, ?_⟩
      · simp only [deployed, List.map_append, List.map_cons, List.map_nil]
        rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton _, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
        subst hb
        exact Nat.ne_of_lt (hall x hx).2.2.2.2
      · intro a ha
        simp only [deployed, List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · obtain ⟨h1, h2, h3, h4, h5⟩ := hall a ha
          exact ⟨h1, h2, h3, h4, by simp [deployed]; omega⟩
        · exact ⟨List.prefix_append _ _, hok.2, rfl, hn, by simp [deployed]⟩

theorem DeploySucceedsIff : Properties.DeploySucceedsIff := by
  intro K s v add
  constructor
  · rintro ⟨s', h⟩
    cases h with
    | deploy _ hok => exact hok
  · intro h
    exact ⟨_, .deploy (fun r hr => h.1 r (List.mem_append_right _ hr)) h⟩

theorem EveryAdminHasRequired : Properties.EveryAdminHasRequired := by
  intro K n₀ s h a ha
  exact (inv_of_reach h).2.2 a ha

theorem AdminsDistinctOrCreateCollision : Properties.AdminsDistinctOrCreateCollision := by
  intro K n₀ s h
  obtain ⟨_, hnd, hall⟩ := inv_of_reach h
  by_cases hN : (s.admins.map AdminRec.addr).Nodup
  · exact Or.inl hN
  · right
    have hadm : s.admins.Nodup := List.Nodup.of_map _ hnd
    have : ¬ ∀ x ∈ s.admins, ∀ y ∈ s.admins, x.addr = y.addr → x = y :=
      fun hinj => hN (List.Nodup.map_on hinj hadm)
    simp only [not_forall] at this
    obtain ⟨x, hx, y, hy, hxy, hne⟩ := this
    have hnon : x.nonce ≠ y.nonce := fun he =>
      hne (List.inj_on_of_nodup_map hnd hx hy he)
    obtain ⟨_, _, hx3, hx4, hx5⟩ := hall x hx
    obtain ⟨_, _, hy3, hy4, hy5⟩ := hall y hy
    rcases Nat.lt_or_gt_of_ne hnon with hlt | hlt
    · exact ⟨x.nonce, y.nonce, hx4, hlt, hy5, by rw [← hx3, ← hy3, hxy]⟩
    · exact ⟨y.nonce, x.nonce, hy4, hlt, hx5, by rw [← hx3, ← hy3, hxy]⟩

theorem DeployedRestrictionsValid : Properties.DeployedRestrictionsValid := by
  intro K s s' v add h
  cases h with
  | deploy _ hok => exact hok.1

theorem DuplicateRequiredBricksFactory : Properties.DuplicateRequiredBricksFactory := by
  intro K s s' l hdup h
  cases h with
  | deploy _ hok => exact hdup (List.Nodup.of_append_left hok.2)

theorem FactoryCheckRedundant : Properties.FactoryCheckRedundant := by
  intro K s s' l
  constructor
  · intro h
    cases h with
    | deploy _ hok => exact .deploy hok
  · intro h
    cases h with
    | deploy hok => exact .deploy (fun r hr => hok.1 r (List.mem_append_right _ hr)) hok

theorem UnvalidatedAdminAdmitsAnything : Properties.UnvalidatedAdminAdmitsAnything := by
  refine ⟨⟨[7], fun _ => 0⟩, ⟨0, []⟩, _, ⟨fun _ => false, []⟩, .deploy (by decide),
    ⟨7, by simp, rfl⟩, ?_⟩
  intro h
  cases h with
  | deploy _ hok => exact absurd (hok.1 7 (by simp)) (by decide)

theorem DeployWitness : Properties.DeployWitness :=
  ⟨_, .step .refl (.deploy (v := fun _ => true) (add := [8]) (by simp) ⟨by simp, by decide⟩),
    by simp [deployed], rfl⟩

end Contracts.L2AdminFactory
