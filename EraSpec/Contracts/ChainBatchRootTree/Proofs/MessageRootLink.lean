import EraSpec.Contracts.ChainBatchRootTree.Properties.MessageRootLink
import EraSpec.Contracts.MessageRoot.Proofs.Model

/-!
# Proofs: the canonical `MessageRoot` model refines the genesis-seed slice

Each entry point of the canonical model writes chain `c`'s three slice fields only when its chain
argument is `c`, and then exactly as `seedExec` does: the shared-tree, chain-tree, timestamp and
log-id writes of `_pushChainBatchRoot` and `_emitRoot` are outside the slice.  A new chain gets
index `chainCount ≥ 1` (`Inv.count_pos`), so it is registered afterwards.
-/

namespace Contracts.ChainBatchRootTree

open Contracts.MessageRoot (Hashes Config Env State Call exec Inv chainRegistered upd2 upd2_apply
  addNewChainInternal_some recordChainBatchRoot_some pushChainBatchRoot_some)

theorem seedSlice_eq_of {cfg : Config} {s t : State} {c : ℕ}
    (h1 : t.chainIndex c = s.chainIndex c)
    (h2 : t.currentChainBatchNumber c = s.currentChainBatchNumber c)
    (h3 : t.chainBatchRoots c = s.chainBatchRoots c) : seedSlice cfg t c = seedSlice cfg s c := by
  simp [seedSlice, chainRegistered, h1, h2, h3]

theorem upd2_other {β : Type} (f : ℕ → ℕ → β) {a c : ℕ} (b : ℕ) (v : β) (h : c ≠ a) :
    upd2 f a b v c = f c := by
  funext y
  rw [upd2_apply]
  simp [h]

theorem upd2_self {β : Type} (f : ℕ → ℕ → β) (a b : ℕ) (v : β) :
    upd2 f a b v a = Function.update (f a) b v := by
  simp [upd2]

theorem message_root_call_is_seed_call {H : Hashes} {cfg : Config} {env : Env} {s t : State}
    {call : Call} {c : ℕ} (hI : Inv H cfg s) (hc : c ≠ cfg.selfChainId)
    (h : exec H cfg env s call = some t) :
    seedSlice cfg t c = seedSlice cfg s c
      ∨ ∃ sc, seedExec (seedSlice cfg s c) (some (env.l2LogsRootHash c 0)) sc
          = some (seedSlice cfg t c) := by
  cases call with
  | «initialize» =>
    have := hI.initialized
    simp only [exec] at h
    simp [show ¬ s.initialized < 2 by omega] at h
  | addNewChain c' start =>
    simp only [exec] at h
    split_ifs at h with h1 h2
    obtain ⟨S', R, k, -, -, -, -, rfl⟩ := addNewChainInternal_some h
    by_cases hcc : c' = c
    · subst hcc
      refine Or.inr ⟨.addNewChain start, ?_⟩
      have hreg : chainRegistered cfg s c' = false := by simpa using h2
      have hpos := hI.count_pos
      simp only [seedExec, seedSlice, hreg, Bool.false_eq_true, ite_false, Option.some.injEq]
      simp only [chainRegistered, Function.update_self]
      simp [show s.chainCount ≠ 0 by omega]
    · exact Or.inl (seedSlice_eq_of (by simp [Function.update_of_ne (Ne.symm hcc)])
        (by simp [Function.update_of_ne (Ne.symm hcc)]) rfl)
  | setMigratingChainBatchNumber c' n =>
    simp only [exec] at h
    split_ifs at h with h1 h2
    cases h
    by_cases hcc : c' = c
    · subst hcc
      refine Or.inr ⟨.setMigratingChainBatchNumber n, ?_⟩
      simp [seedExec, seedSlice, h2, chainRegistered]
    · exact Or.inl (seedSlice_eq_of rfl (by simp [Function.update_of_ne (Ne.symm hcc)]) rfl)
  | addChainBatchRoot c' n r =>
    simp only [exec] at h
    split_ifs at h with h1
    obtain ⟨hreg, hr, hz, hov, hn, rfl⟩ := recordChainBatchRoot_some h
    by_cases hcc : c' = c
    · subst hcc
      refine Or.inr ⟨.addChainBatchRoot n r, ?_⟩
      simp only [seedExec, seedSlice, hreg, hr, ne_eq, not_true_eq_false, ite_false,
        Bool.true_eq_false, not_le.mpr hov, hn]
      simp [chainRegistered, upd2_self]
      exact ⟨by rw [← hn]; exact hz, Contracts.MessageRoot.chainRegistered_iff.mp hreg⟩
    · exact Or.inl (seedSlice_eq_of rfl (by simp [Function.update_of_ne (Ne.symm hcc)])
        (upd2_other _ _ _ (Ne.symm hcc)))
  | addChainBatchRootV32 c' n r =>
    simp only [exec] at h
    split_ifs at h with h1
    obtain ⟨t₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hreg, hr, hz, hov, hn, rfl⟩ := recordChainBatchRoot_some h₁
    obtain ⟨S', R, k, -, -, -, rfl⟩ := pushChainBatchRoot_some h₂
    by_cases hcc : c' = c
    · subst hcc
      refine Or.inr ⟨.addChainBatchRoot n r, ?_⟩
      simp only [seedExec, seedSlice, hreg, hr, ne_eq, not_true_eq_false, ite_false,
        Bool.true_eq_false, not_le.mpr hov, hn]
      simp [chainRegistered, upd2_self]
      exact ⟨by rw [← hn]; exact hz, Contracts.MessageRoot.chainRegistered_iff.mp hreg⟩
    · exact Or.inl (seedSlice_eq_of rfl (by simp [Function.update_of_ne (Ne.symm hcc)])
        (upd2_other _ _ _ (Ne.symm hcc)))
  | seedGenesisRoot c' =>
    simp only [exec] at h
    split_ifs at h with h1 h2 h3 h4 h5
    obtain ⟨S', R, k, -, -, -, rfl⟩ := pushChainBatchRoot_some h
    by_cases hcc : c' = c
    · subst hcc
      refine Or.inr ⟨.seedGenesisRoot, ?_⟩
      have hreg : chainRegistered cfg s c' = true := by simpa using h3
      simp only [seedExec, seedSlice, h2, hreg, h4, h5, ite_false, Bool.true_eq_false]
      simp [chainRegistered, upd2_self]
      exact Contracts.MessageRoot.chainRegistered_iff.mp hreg
    · exact Or.inl (seedSlice_eq_of rfl rfl (upd2_other _ _ _ (Ne.symm hcc)))
  | enableInterop c' req =>
    simp only [exec] at h
    split_ifs at h
    cases h
    exact Or.inl rfl

theorem initialized_slice_is_fresh {H : Hashes} {cfg : Config} {env : Env} {s : State} {c : ℕ}
    (h : exec H cfg env Contracts.MessageRoot.fresh .initialize = some s) (hc : c ≠ cfg.selfChainId) :
    seedSlice cfg s c = seedFresh.mr := by
  simp only [exec, Contracts.MessageRoot.fresh, show (0 : ℕ) < 2 by decide, ite_true,
    Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨s₂, h₂, h₃⟩ := h
  split_ifs at h₃
  cases h₃
  obtain ⟨S', R, k, -, -, -, -, rfl⟩ := addNewChainInternal_some h₂
  simp [seedSlice, seedFresh, chainRegistered, hc]

theorem reachable_slice_is_seed_run {H : Hashes} {cfg : Config} {s : State} {c : ℕ}
    (h : Contracts.MessageRoot.Reachable H cfg s) (hc : c ≠ cfg.selfChainId) :
    SeedCallsReach seedFresh.mr (seedSlice cfg s c) := by
  induction h with
  | init hi =>
    rw [initialized_slice_is_fresh hi hc]
    exact SeedCallsReach.refl
  | @step s t e call hs hexec ih =>
    rcases message_root_call_is_seed_call (Contracts.MessageRoot.inv_reachable hs) hc hexec with
      heq | ⟨sc, hsc⟩
    · rw [heq]; exact ih
    · exact SeedCallsReach.tail _ sc ih hsc

theorem MessageRootCallIsSeedCall : Properties.MessageRootCallIsSeedCall :=
  fun _ _ _ _ _ _ _ hI hc h => message_root_call_is_seed_call hI hc h
theorem InitializedSliceIsFresh : Properties.InitializedSliceIsFresh :=
  fun _ _ _ _ _ h hc => initialized_slice_is_fresh h hc
theorem ReachableSliceIsSeedRun : Properties.ReachableSliceIsSeedRun :=
  fun _ _ _ _ h hc => reachable_slice_is_seed_run h hc

end Contracts.ChainBatchRootTree
