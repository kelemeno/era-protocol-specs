import EraSpec.Contracts.L2InteropRootStorage.Properties.Refinement
import EraSpec.Contracts.L2InteropRootStorage.Proofs.Model
import EraSpec.Contracts.L2InteropRootStorage.Proofs.Storage

/-!
# Proofs: the canonical storage model refines the `ok`-admitted model

One successful `_addInteropRoot` of the canonical model passes the model's `AddGuard` on the
projected state and writes what the model's `write` writes (`addRoot_refines`); a batch is a list
of these (`addRoots_refines`), so a call is a `Step` and a logged run a `Reach`.
-/

namespace Contracts.L2InteropRootStorage

open Contracts.InteropRootStorage (addRoot addRoots addRoot_iff addRoots_cons_eq_some exec_eq_some
  writeRoot)

theorem toModel_entries_val (S : Contracts.InteropRootStorage.State) (c b : UInt256) :
    (toModel S).entries c b.val =
      ⟨(S.storedInteropRoots c b).root, (S.storedInteropRoots c b).timestamp.val⟩ := by
  simp only [toModel]
  rw [dif_pos b.isLt]

theorem toModel_empty : toModel Contracts.InteropRootStorage.empty = empty := by
  simp only [toModel, Contracts.InteropRootStorage.empty, empty]
  congr
  funext c n
  split_ifs <;> rfl

theorem toModel_writeRoot (S : Contracts.InteropRootStorage.State) (c b ts root : UInt256) :
    toModel (writeRoot S c b ts root) =
      (toModel S).write ⟨c, b.val, ts.val, [root]⟩ root := by
  have : ∀ c' n, (toModel (writeRoot S c b ts root)).entries c' n =
      ((toModel S).write ⟨c, b.val, ts.val, [root]⟩ root).entries c' n := by
    intro c' n
    rw [write_entries]
    simp only [toModel, writeRoot]
    by_cases hn : n < UInt256.size
    · rw [dif_pos hn, dif_pos hn]
      by_cases hc : c' = c
      · subst hc
        by_cases hb : n = b.val
        · subst hb
          rw [if_pos ⟨rfl, rfl⟩]
          simp
        · have hb' : (⟨n, hn⟩ : UInt256) ≠ b := fun h => hb (by rw [← h])
          rw [if_neg (fun h => hb' h.2)]
          simp [hb]
      · simp [hc]
    · rw [dif_neg hn, dif_neg hn]
      have hb : ¬ n = b.val := fun h => hn (h ▸ b.isLt)
      simp [hb]
  cases h₁ : toModel (writeRoot S c b ts root)
  cases h₂ : (toModel S).write ⟨c, b.val, ts.val, [root]⟩ root
  congr
  funext c' n
  have := this c' n
  rw [h₁, h₂] at this
  exact this

theorem addRoot_refines {S S' : Contracts.InteropRootStorage.State}
    {r : Contracts.InteropRootStorage.InteropRoot} (h : addRoot S r = some S') :
    ∃ w, AddGuard (toModel S) (ofInteropRoot r) w ∧
      toModel S' = (toModel S).write (ofInteropRoot r) w := by
  obtain ⟨root, hs, hr, ht, hfresh, rfl⟩ := addRoot_iff.mp h
  refine ⟨root, ⟨hs, hr, ?_, ?_⟩, ?_⟩
  · intro h0
    apply ht
    exact Fin.ext (by simpa [ofInteropRoot] using h0)
  · show ((toModel S).entries r.chainId r.blockOrBatchNumber.val).root = 0
    rw [toModel_entries_val]
    exact hfresh
  · rw [toModel_writeRoot]
    simp only [ofInteropRoot, hs]

theorem addRoots_refines (ok : RootIn → Prop) :
    ∀ (rs : List Contracts.InteropRootStorage.InteropRoot) (S S' : Contracts.InteropRootStorage.State),
      addRoots S rs = some S' → (∀ r ∈ rs, ok (ofInteropRoot r)) →
        AddsAll ok (toModel S) (rs.map ofInteropRoot) (toModel S')
  | [], S, S', h, _ => by
      simp only [addRoots, Option.some.injEq] at h
      subst h
      exact AddsAll.nil
  | r :: rs, S, S', h, hok => by
      obtain ⟨S₁, h1, h2⟩ := addRoots_cons_eq_some.mp h
      obtain ⟨w, hg, hw⟩ := addRoot_refines h1
      have ih := addRoots_refines ok rs S₁ S' h2 (fun r' hr' => hok r' (List.mem_cons_of_mem _ hr'))
      rw [hw] at ih
      exact AddsAll.cons w (hok r List.mem_cons_self) hg ih

theorem canonical_call_is_model_step (ok : RootIn → Prop) {S S' : Contracts.InteropRootStorage.State}
    {caller : Contracts.InteropRootStorage.Address} {c : Contracts.InteropRootStorage.Call}
    (h : Contracts.InteropRootStorage.exec S caller c = some S')
    (hok : ∀ r ∈ c.roots, ok (ofInteropRoot r)) : Step ok (toModel S) (toModel S') :=
  Step.batch _ (addRoots_refines ok c.roots S S' (exec_eq_some.mp h).2 hok)

theorem reach_trans' {ok : RootIn → Prop} {a b c : State} (h1 : Reach ok a b) (h2 : Reach ok b c) :
    Reach ok a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hs ih => exact Reach.tail ih hs

theorem canonical_run_is_model_run (ok : RootIn → Prop) {S S' : Contracts.InteropRootStorage.State}
    {log : List (Contracts.InteropRootStorage.Address × Contracts.InteropRootStorage.Call)}
    (h : Contracts.InteropRootStorage.ReachLog S S' log)
    (hok : ∀ r ∈ Contracts.InteropRootStorage.imports log, ok (ofInteropRoot r)) :
    Reach ok (toModel S) (toModel S') := by
  induction h with
  | refl => exact Reach.refl
  | @tail T U log' caller c _ hexec ih =>
    have hok' : ∀ r ∈ Contracts.InteropRootStorage.imports log', ok (ofInteropRoot r) := by
      intro r hr
      apply hok
      rw [Contracts.InteropRootStorage.imports_snoc]
      exact List.mem_append_left _ hr
    have hokc : ∀ r ∈ c.roots, ok (ofInteropRoot r) := by
      intro r hr
      apply hok
      rw [Contracts.InteropRootStorage.imports_snoc]
      exact List.mem_append_right _ hr
    exact Reach.tail (ih hok') (canonical_call_is_model_step ok hexec hokc)

theorem ToModelReadsTheStorage : Properties.ToModelReadsTheStorage := toModel_entries_val
theorem ToModelEmpty : Properties.ToModelEmpty := toModel_empty
theorem CanonicalCallIsModelStep : Properties.CanonicalCallIsModelStep :=
  fun ok _ _ _ _ h hok => canonical_call_is_model_step ok h hok
theorem CanonicalRunIsModelRun : Properties.CanonicalRunIsModelRun :=
  fun ok _ _ _ h hok => canonical_run_is_model_run ok h hok

end Contracts.L2InteropRootStorage
