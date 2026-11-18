import EraSpec.Contracts.L1Messenger.Properties.SenderKeying
import Mathlib.Tactic

/-!
# Proofs: how an L2→L1 message is keyed by its sender

By induction on the run: each step appends at most one log, and under `HooksAsDocumented` only a
`withdrawal` appends a center-keyed one. A `message` from another account is keyed by that account
(`padAddr` is injective on addresses); a direct hook call by anyone but the messenger records nothing;
a leaf log is not center-keyed; a bootloader log has sender 0x8001. The witnesses are evaluated by
`decide`.
-/

namespace Contracts.L1MessengerKeying

open Contracts.L1WithdrawalGate

lemma padAddr_injective : Function.Injective padAddr := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa [padAddr] using this

lemma messageLog_centerKeyed_iff (C : Codec) (t : ℕ) (a : Address) (m : Bytes) :
    CenterKeyed (messageLog C t a m) ↔ a = l2InteropCenterAddr := by
  constructor
  · rintro ⟨_, hk⟩
    exact padAddr_injective hk
  · rintro rfl
    exact ⟨rfl, rfl⟩

lemma filter_append_one (L : L2Log) (out : List L2Log) (h : CenterKeyed L) :
    (out ++ [L]).filter (fun L => decide (CenterKeyed L)) =
      out.filter (fun L => decide (CenterKeyed L)) ++ [L] := by
  simp [List.filter_append, h]

lemma filter_append_none (L : L2Log) (out : List L2Log) (h : ¬ CenterKeyed L) :
    (out ++ [L]).filter (fun L => decide (CenterKeyed L)) =
      out.filter (fun L => decide (CenterKeyed L)) := by
  simp [List.filter_append, h]

lemma filter_append_opt (o : Option L2Log) (out : List L2Log) (h : ∀ L, o = some L → ¬ CenterKeyed L) :
    (out ++ o.toList).filter (fun L => decide (CenterKeyed L)) =
      out.filter (fun L => decide (CenterKeyed L)) := by
  rcases o with _ | L
  · simp
  · exact filter_append_none L out (h L rfl)

theorem CenterKeyedLogsAreItsWithdrawals : Properties.CenterKeyedLogsAreItsWithdrawals := by
  intro C Q H S hH hR
  induction hR with
  | refl => exact ⟨rfl, fun _ h => by simp [L2State.init] at h⟩
  | tail _ hs ih =>
    obtain ⟨ihf, ihs⟩ := ih
    cases hs with
    | withdrawal b t hshape =>
      refine ⟨?_, ?_⟩
      · simp only [hH.messengerRecords, Option.toList_some]
        rw [filter_append_one _ _ ((messageLog_centerKeyed_iff _ _ _ _).2 rfl), ihf]
        simp [dispatchLog]
      · intro d hd
        rcases List.mem_append.1 hd with hd | hd
        · exact ihs d hd
        · simp only [List.mem_singleton] at hd
          subst hd
          exact hshape
    | message a m t ha =>
      refine ⟨?_, ihs⟩
      simp only [hH.messengerRecords, Option.toList_some]
      rw [filter_append_none _ _ (fun h => ha ((messageLog_centerKeyed_iff _ _ _ _).1 h)), ihf]
    | hookCall c x t hc =>
      refine ⟨?_, ihs⟩
      rw [hH.messengerCallerGated c t x hc]
      simpa using ihf
    | leafCall c v t =>
      refine ⟨?_, ihs⟩
      rw [filter_append_opt _ _ ?_, ihf]
      intro L hL
      by_cases hc : c = l2CommitmentTreeAddr
      · subst hc
        exact hH.leafNotCenterKeyed t v L hL
      · rw [hH.leafCallerGated c t v hc] at hL
        cases hL
    | bootloaderLog L hL =>
      refine ⟨?_, ihs⟩
      rw [filter_append_none _ _ ?_, ihf]
      rintro ⟨hs, _⟩
      rw [hL] at hs
      exact absurd hs (by decide)

lemma wGatedHooks_documented : HooksAsDocumented wCodec wGatedHooks where
  messengerCallerGated c t x hc := by simp [wGatedHooks, hc]
  messengerRecords t a m := by simp [wGatedHooks]
  leafCallerGated c t v hc := by simp [wGatedHooks, hc]
  leafNotCenterKeyed t v L hL := by
    simp only [wGatedHooks, ↓reduceIte, Option.some.injEq] at hL
    subst hL
    rintro ⟨hs, _⟩
    change l2CommitmentTreeAddr = l2ToL1MessengerAddr at hs
    exact absurd hs (by decide)

lemma wS₄_reach (H : HookSem) (h₁ : wForger ≠ l2InteropCenterAddr)
    (h₂ : wForger ≠ l2ToL1MessengerAddr) :
    Reach wCodec wChain H L2State.init (wS₄ H) := by
  have hshape : WithdrawalShape wCodec wChain wOne := by
    refine ⟨rfl, rfl, rfl, rfl, wCall 7, rfl, rfl, rfl, rfl, rfl, by decide⟩
  exact .tail (.tail (.tail (.tail (.refl _) (.withdrawal _ wOne 0 hshape))
    (.message _ wForger [0x42] 1 h₁)) (.hookCall _ wForger _ 2 h₂)) (.leafCall _ _ 7 3)

theorem SenderKeyingWitness : Properties.SenderKeyingWitness :=
  ⟨wGatedHooks_documented, wS₄_reach _ (by decide) (by decide), by decide, by decide⟩

theorem UngatedHookForgesACenterKeyedLog : Properties.UngatedHookForgesACenterKeyedLog := by
  refine ⟨?_, ?_, ?_, ?_, wS₄_reach _ (by decide) (by decide), by decide, by decide, by decide⟩
  · intro h
    have := h wForger 0 (l2InteropCenterAddr, []) (by decide)
    simp [wUngatedHooks] at this
  · intro t a m; rfl
  · exact wGatedHooks_documented.leafCallerGated
  · exact wGatedHooks_documented.leafNotCenterKeyed

end Contracts.L1MessengerKeying
