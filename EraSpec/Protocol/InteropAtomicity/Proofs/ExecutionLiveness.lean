import EraSpec.Protocol.InteropAtomicity.Properties.ExecutionLiveness
import EraSpec.Contracts.InteropHandlerBase.Proofs.Reentrancy
import EraSpec.Contracts.InteropCenter.Proofs.Dispatch
import EraSpec.Protocol.InteropAtomicity.Proofs.Refund

/-!
# Proofs: an atomic leg has one route, and what that costs

**(d), (e)** Two inductions on the budget, over every frame kind, in the style of
`Contracts.InteropHandler.exec_good`. A frame whose entry calls are all backed by `Pub` keeps an
unpublished hash in `{Unreceived, FullyExecuted}` (`exec_keeps_closed`): reaching `Verified` needs a
backed `true` verdict on that very hash, and `unbundleBundle` needs `Verified` or `Unbundled` to
start with. If moreover every atomic attempt on the hash meets a reverting target, the hash stays
`Unreceived` and no frame commits an effect of it (`exec_keeps_stuck`): the one route left reverts
by `Contracts.InteropHandler.RevertingCallRevertsTheExecution`, at every depth. The source half is
`abiEncode` injectivity in both arguments plus `Contracts.InteropCenter.AtomicBytesNeverPublished`.

**(h)** `unbundleBundle`'s first loop on an accepted request computes `applyRequest`
(`markCalls_accepts`, by induction on the request), and a loop whose targets accept delivers every
listed call (`Contracts.InteropHandler.exec_calls_returns`).
-/

namespace Contracts.ExecutionLiveness

open Contracts.InteropHandler (State Entry Callee Frame Tx Bundle BundleHash Effect exec submit
  submitAll toExecute markCalls commit init Variant beforeCalls afterCalls afterUnbundle
  writesCallsFirst)
open AttackVectors.BundleStatusMachine (Status CallStatus)
open AttackVectors.BundleHashEncoding (abiEncode word pad32 toBytesBE length_toBytesBE)
open Contracts.InteropCenter (Params Dispatch CrossSenderSaltClash EncInjOn bundleHash
  bundlePreimage)
open MerkleSpec (Hash)
open Contracts.InteropCommitmentTree (LeafHash)
open Contracts.Atomicity (CommitValue FlowHash System Wf Flow FlowLeg GateEvidence ExecutedViaBy)
open Contracts.Refund (Managers AuthCall ReachLog emptyManagers Refunded RefundBreak obligationOf)

/-! ## Every entry of a frame -/

/-- Every entry-point call of a frame, including the frame's own entry, satisfies `Q`. -/
def FrameEvery (Q : Entry → List Callee → Prop) : Frame → Prop
  | .entry e cs => Q e cs ∧ ∀ c ∈ cs, EveryEntry Q c
  | .calls _ _ cs => ∀ c ∈ cs, EveryEntry Q c
  | .target c => EveryEntry Q c

lemma headD_every {Q : Entry → List Callee → Prop} {cs : List Callee}
    (h : ∀ c ∈ cs, EveryEntry Q c) : EveryEntry Q (cs.headD .returns) := by
  cases cs with
  | nil => exact .returns
  | cons c cs => exact h c List.mem_cons_self

lemma tail_every {Q : Entry → List Callee → Prop} {cs : List Callee}
    (h : ∀ c ∈ cs, EveryEntry Q c) : ∀ c ∈ cs.tail, EveryEntry Q c :=
  fun c hc => h c (List.mem_of_mem_tail hc)

/-- The deployed first loop of `unbundleBundle` leaves the bundle statuses alone. -/
lemma markCalls_bundle {h : BundleHash} {req : List CallStatus} {u s₁ : State}
    (hm : markCalls true h 0 req u = some s₁) : s₁.bundle = u.bundle :=
  (Contracts.InteropHandler.markCalls_spec req 0 u s₁ hm).1

/-- The two statuses an unpublished hash keeps. -/
def Closed (s : State) (h : BundleHash) : Prop :=
  s.bundle h = .Unreceived ∨ s.bundle h = .FullyExecuted

lemma Closed.not_verified {s : State} {h : BundleHash} (hc : Closed s h) :
    s.bundle h ≠ .Verified := by
  rcases hc with h1 | h1 <;> rw [h1] <;> decide

lemma Closed.not_unbundled {s : State} {h : BundleHash} (hc : Closed s h) :
    s.bundle h ≠ .Unbundled := by
  rcases hc with h1 | h1 <;> rw [h1] <;> decide

/-- The writes before a whole-bundle execution's calls touch only that bundle's status. -/
lemma beforeCalls_bundle_other {b : Bundle} {s : State} {h : BundleHash} (hne : h ≠ b.hash) :
    (beforeCalls .deployed b s).bundle h = s.bundle h := by
  simp [hne]

lemma verifyIfUnreceived_bundle_other {s : State} {h h' : BundleHash} (hne : h ≠ h') :
    (s.verifyIfUnreceived h').bundle h = s.bundle h := by
  unfold State.verifyIfUnreceived
  split_ifs <;> simp [hne]

/-! ## (d) An unpublished hash keeps only the atomic route -/

/-- **THE FRAME INVARIANT FOR (d).** -/
theorem exec_keeps_closed {Pub : BundleHash → Prop} {h : BundleHash} (hpub : ¬ Pub h) :
    ∀ (n : ℕ) (f : Frame) (s s' : State) (l : List Effect),
      exec .deployed n f s = some (s', l) → FrameEvery (ProofBacked Pub) f → Closed s h →
        Closed s' h := by
  intro n
  induction n with
  | zero => intro f s s' l hx _; simp [exec] at hx
  | succ n ih =>
    intro f s s' l hx hf hc
    match f, hf with
    | .entry (.executeBundle b ok) cs, ⟨hq, hcs⟩ =>
      simp only [exec] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₂ l₂ heq
        simp only [Contracts.InteropHandler.afterCalls_deployed, Option.some.injEq,
          Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        have hne : b.hash ≠ h := by
          rintro rfl
          rcases hG with hv | ⟨_, hok⟩
          · exact hc.not_verified hv
          · exact hpub (hq hok)
        refine ih _ _ _ _ heq hcs ?_
        unfold Closed
        rw [beforeCalls_bundle_other (Ne.symm hne), verifyIfUnreceived_bundle_other (Ne.symm hne)]
        exact hc
      · simp at hx
    | .entry (.executeAtomicBundle b ok) cs, ⟨_, hcs⟩ =>
      simp only [exec] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₂ l₂ heq
        simp only [Contracts.InteropHandler.afterCalls_deployed, Option.some.injEq,
          Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        refine ih _ _ _ _ heq hcs ?_
        unfold Closed
        by_cases hb : h = b.hash
        · subst hb; simp
        · rw [beforeCalls_bundle_other hb]; exact hc
      · simp at hx
    | .entry (.verifyBundle b ok) cs, ⟨hq, _⟩ =>
      simp only [exec] at hx
      split_ifs at hx with hG
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      have hne : b.hash ≠ h := by
        rintro rfl
        exact hpub (hq hG.2)
      unfold Closed
      rw [Contracts.InteropHandler.setBundle_bundle, ite_eq_right (Ne.symm hne)]
      exact hc
    | .entry (.unbundleBundle b req) cs, ⟨_, hcs⟩ =>
      simp only [exec, Contracts.InteropHandler.writesCallsFirst_deployed] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₁ hm
        split at hx
        · rename_i s₂ l₂ heq
          simp only [Contracts.InteropHandler.afterUnbundle_deployed, Option.some.injEq,
            Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          have hne : b.hash ≠ h := by
            rintro rfl
            rcases hG.2 with hv | hv
            · exact hc.not_verified hv
            · exact hc.not_unbundled hv
          refine ih _ _ _ _ heq hcs ?_
          unfold Closed
          rw [markCalls_bundle hm, Contracts.InteropHandler.setBundle_bundle,
            ite_eq_right (Ne.symm hne)]
          exact hc
        · simp at hx
      · simp at hx
    | .calls hb [] cs, _ =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact hc
    | .calls hb (i :: is) cs, hcs =>
      simp only [exec] at hx
      split at hx
      · rename_i s₁ l₁ heq₁
        split at hx
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact ih _ _ _ _ heq₂ (tail_every hcs) (ih _ _ _ _ heq₁ (headD_every hcs) hc)
        · simp at hx
      · simp at hx
    | .target .returns, _ =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact hc
    | .target .reverts, _ => simp [exec] at hx
    | .target (.calls e inner caught next), hcall =>
      cases hcall with
      | calls hq hinner hnext =>
        simp only [exec] at hx
        split at hx
        · rename_i s₁ l₁ heq₁
          split at hx
          · rename_i s₂ l₂ heq₂
            simp only [Option.some.injEq, Prod.mk.injEq] at hx
            obtain ⟨rfl, rfl⟩ := hx
            exact ih _ _ _ _ heq₂ hnext (ih _ _ _ _ heq₁ ⟨hq, hinner⟩ hc)
          · simp at hx
        · split_ifs at hx
          exact ih _ _ _ _ hx hnext hc

/-- One transaction keeps an unpublished hash closed. -/
lemma submit_keeps_closed {Pub : BundleHash → Prop} {h : BundleHash} (hpub : ¬ Pub h)
    {s : State} {t : Tx} (ht : TxEvery (ProofBacked Pub) t) (hc : Closed s h) :
    Closed (submit .deployed s t).1 h := by
  unfold submit
  cases hx : exec .deployed t.fuel (.entry t.entry t.callees) s with
  | none => exact hc
  | some r =>
    obtain ⟨s', l⟩ := r
    exact exec_keeps_closed hpub _ _ _ _ _ hx ht hc

lemma submitAll_keeps_closed {Pub : BundleHash → Prop} {h : BundleHash} (hpub : ¬ Pub h) :
    ∀ (s : State) (txs : List Tx), (∀ t ∈ txs, TxEvery (ProofBacked Pub) t) → Closed s h →
      Closed (submitAll .deployed s txs).1 h
  | _, [], _, hc => hc
  | _, t :: ts, hts, hc =>
    submitAll_keeps_closed hpub _ ts (fun t' ht' => hts t' (List.mem_cons_of_mem _ ht'))
      (submit_keeps_closed hpub (hts t List.mem_cons_self) hc)

theorem UnpublishedHashKeepsOnlyTheAtomicRoute :
    Properties.UnpublishedHashKeepsOnlyTheAtomicRoute :=
  fun _ _ hpub s txs hc hts => submitAll_keeps_closed hpub s txs hts hc

theorem PublicRoutesRevertOutsideVerified : Properties.PublicRoutesRevertOutsideVerified := by
  intro s b hc n cs
  have hv : s.bundle b.hash ≠ .Verified := Closed.not_verified hc
  have hu : s.bundle b.hash ≠ .Unbundled := Closed.not_unbundled hc
  refine ⟨?_, ?_, fun req => ?_⟩
  · cases n with
    | zero => simp [exec]
    | succ n => simp [exec, hv]
  · cases n with
    | zero => simp [exec]
    | succ n => simp [exec]
  · cases n with
    | zero => simp [exec]
    | succ n => simp [exec, hv, hu]

/-! ## (e) A reverting call strands the atomic route -/

/-- A loop frame is not one of `h`'s own: the hash whose calls it delivers differs from `h`. -/
def NotLoopOf (h : BundleHash) : Frame → Prop
  | .calls h' _ _ => h' ≠ h
  | _ => True

/-- **THE FRAME INVARIANT FOR (e).** With every verdict backed, `h` unpublished and every atomic
attempt on `h` meeting a reverting target, a committed frame started with `h` `Unreceived` ends with
`h` `Unreceived` and commits no effect of `h`. -/
theorem exec_keeps_stuck {Pub : BundleHash → Prop} {h : BundleHash} (hpub : ¬ Pub h) :
    ∀ (n : ℕ) (f : Frame) (s s' : State) (l : List Effect),
      exec .deployed n f s = some (s', l) → FrameEvery (ProofBacked Pub) f →
      FrameEvery (AtomicAttemptReverts h) f → NotLoopOf h f → s.bundle h = .Unreceived →
        s'.bundle h = .Unreceived ∧ ∀ e ∈ l, e.bundleHash ≠ h := by
  intro n
  induction n with
  | zero => intro f s s' l hx; simp [exec] at hx
  | succ n ih =>
    intro f s s' l hx hf hr hloop hu
    match f, hf, hr with
    | .entry (.executeBundle b ok) cs, ⟨hq, hcs⟩, ⟨_, hrs⟩ =>
      simp only [exec] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₂ l₂ heq
        simp only [Contracts.InteropHandler.afterCalls_deployed, Option.some.injEq,
          Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        have hne : b.hash ≠ h := by
          rintro rfl
          rcases hG with hv | ⟨_, hok⟩
          · rw [hu] at hv; exact absurd hv (by decide)
          · exact hpub (hq hok)
        have hu' : (beforeCalls .deployed b (s.verifyIfUnreceived b.hash)).bundle h = .Unreceived := by
          rw [beforeCalls_bundle_other (Ne.symm hne), verifyIfUnreceived_bundle_other (Ne.symm hne)]
          exact hu
        obtain ⟨h1, h2⟩ := ih _ _ _ _ heq hcs hrs hne hu'
        refine ⟨h1, fun e he => ?_⟩
        rcases List.mem_append.mp he with he | he
        · exact h2 e he
        · rw [List.mem_singleton] at he; subst he; exact hne
      · simp at hx
    | .entry (.executeAtomicBundle b ok) cs, ⟨_, hcs⟩, ⟨hra, hrs⟩ =>
      have hne : b.hash ≠ h := by
        intro hb
        have hnone := (Contracts.InteropHandler.RevertingCallRevertsTheExecution .deployed (n + 1)
          b ok cs s (hra hb)).1
        rw [hnone] at hx
        simp at hx
      simp only [exec] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₂ l₂ heq
        simp only [Contracts.InteropHandler.afterCalls_deployed, Option.some.injEq,
          Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        have hu' : (beforeCalls .deployed b s).bundle h = .Unreceived := by
          rw [beforeCalls_bundle_other (Ne.symm hne)]; exact hu
        obtain ⟨h1, h2⟩ := ih _ _ _ _ heq hcs hrs hne hu'
        refine ⟨h1, fun e he => ?_⟩
        rcases List.mem_append.mp he with he | he
        · exact h2 e he
        · rw [List.mem_singleton] at he; subst he; exact hne
      · simp at hx
    | .entry (.verifyBundle b ok) cs, ⟨hq, _⟩, _ =>
      simp only [exec] at hx
      split_ifs at hx with hG
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      have hne : b.hash ≠ h := by
        rintro rfl
        exact hpub (hq hG.2)
      refine ⟨?_, by simp⟩
      rw [Contracts.InteropHandler.setBundle_bundle, ite_eq_right (Ne.symm hne)]
      exact hu
    | .entry (.unbundleBundle b req) cs, ⟨_, hcs⟩, ⟨_, hrs⟩ =>
      simp only [exec, Contracts.InteropHandler.writesCallsFirst_deployed] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₁ hm
        split at hx
        · rename_i s₂ l₂ heq
          simp only [Contracts.InteropHandler.afterUnbundle_deployed, Option.some.injEq,
            Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          have hne : b.hash ≠ h := by
            rintro rfl
            rcases hG.2 with hv | hv <;> rw [hu] at hv <;> exact absurd hv (by decide)
          have hu' : s₁.bundle h = .Unreceived := by
            rw [markCalls_bundle hm, Contracts.InteropHandler.setBundle_bundle,
              ite_eq_right (Ne.symm hne)]
            exact hu
          exact ih _ _ _ _ heq hcs hrs hne hu'
        · simp at hx
      · simp at hx
    | .calls hb [] cs, _, _ =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨hu, by simp⟩
    | .calls hb (i :: is) cs, hcs, hrs =>
      simp only [exec] at hx
      split at hx
      · rename_i s₁ l₁ heq₁
        split at hx
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          have hne : hb ≠ h := hloop
          obtain ⟨h1, h2⟩ := ih _ _ _ _ heq₁ (headD_every hcs) (headD_every hrs) trivial hu
          obtain ⟨h3, h4⟩ := ih _ _ _ _ heq₂ (tail_every hcs) (tail_every hrs) hne h1
          refine ⟨h3, fun e he => ?_⟩
          rcases List.mem_cons.mp he with rfl | he
          · exact hne
          · rcases List.mem_append.mp he with he | he
            · exact h2 e he
            · exact h4 e he
        · simp at hx
      · simp at hx
    | .target .returns, _, _ =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨hu, by simp⟩
    | .target .reverts, _, _ => simp [exec] at hx
    | .target (.calls e inner caught next), hcall, hrcall =>
      cases hcall with
      | calls hq hinner hnext =>
        cases hrcall with
        | calls hrq hrinner hrnext =>
          simp only [exec] at hx
          split at hx
          · rename_i s₁ l₁ heq₁
            split at hx
            · rename_i s₂ l₂ heq₂
              simp only [Option.some.injEq, Prod.mk.injEq] at hx
              obtain ⟨rfl, rfl⟩ := hx
              obtain ⟨h1, h2⟩ := ih _ _ _ _ heq₁ ⟨hq, hinner⟩ ⟨hrq, hrinner⟩ trivial hu
              obtain ⟨h3, h4⟩ := ih _ _ _ _ heq₂ hnext hrnext trivial h1
              refine ⟨h3, fun e he => ?_⟩
              rcases List.mem_append.mp he with he | he
              · exact h2 e he
              · exact h4 e he
            · simp at hx
          · split_ifs at hx
            exact ih _ _ _ _ hx hnext hrnext trivial hu

lemma submit_keeps_stuck {Pub : BundleHash → Prop} {h : BundleHash} (hpub : ¬ Pub h)
    {s : State} {t : Tx} (ht : TxEvery (ProofBacked Pub) t) (hr : TxEvery (AtomicAttemptReverts h) t)
    (hu : s.bundle h = .Unreceived) :
    (submit .deployed s t).1.bundle h = .Unreceived ∧ ∀ e ∈ (submit .deployed s t).2, e.bundleHash ≠ h := by
  unfold submit
  cases hx : exec .deployed t.fuel (.entry t.entry t.callees) s with
  | none => exact ⟨hu, by simp [commit]⟩
  | some r =>
    obtain ⟨s', l⟩ := r
    exact exec_keeps_stuck hpub _ _ _ _ _ hx ht hr trivial hu

lemma submitAll_keeps_stuck {Pub : BundleHash → Prop} {h : BundleHash} (hpub : ¬ Pub h) :
    ∀ (s : State) (txs : List Tx), (∀ t ∈ txs, TxEvery (ProofBacked Pub) t) →
      (∀ t ∈ txs, TxEvery (AtomicAttemptReverts h) t) → s.bundle h = .Unreceived →
      (submitAll .deployed s txs).1.bundle h = .Unreceived ∧
        ∀ e ∈ (submitAll .deployed s txs).2, e.bundleHash ≠ h
  | _, [], _, _, hu => ⟨hu, by simp [submitAll]⟩
  | s, t :: ts, hts, hrs, hu => by
    obtain ⟨h1, h2⟩ := submit_keeps_stuck hpub (hts t List.mem_cons_self) (hrs t List.mem_cons_self) hu
    obtain ⟨h3, h4⟩ := submitAll_keeps_stuck hpub _ ts
      (fun t' ht' => hts t' (List.mem_cons_of_mem _ ht'))
      (fun t' ht' => hrs t' (List.mem_cons_of_mem _ ht')) h1
    refine ⟨h3, fun e he => ?_⟩
    simp only [submitAll, List.mem_append] at he
    rcases he with he | he
    · exact h2 e he
    · exact h4 e he

theorem AtomicLegWithRevertingCallNeverExecutes :
    Properties.AtomicLegWithRevertingCallNeverExecutes :=
  fun _ _ hpub s txs hu hts hrs => submitAll_keeps_stuck hpub s txs hts hrs hu

/-! ## (d) The source half, and the composite -/

/-- **`abi.encode(uint256, bytes)` DETERMINES ITS WORD**, modulo `2^256`: the head word. -/
lemma abiEncode_left {c c' : ℕ} {x y : List UInt8} (h : abiEncode c x = abiEncode c' y) :
    c % 256 ^ 32 = c' % 256 ^ 32 := by
  have h1 := congrArg (List.take 32) h
  simp only [abiEncode] at h1
  rw [List.take_left' (length_toBytesBE 32 _), List.take_left' (length_toBytesBE 32 _)] at h1
  exact Contracts.InteropCenter.toBytesBE_eq_mod h1

/-- Equal preimages name the same chain and the same bytes. -/
lemma abiEncode_inj_word {c c' : Contracts.InteropCenter.Word} {x y : List UInt8}
    (h : abiEncode c.val x = abiEncode c'.val y) : c = c' ∧ x = y := by
  refine ⟨Fin.ext ?_, Contracts.InteropCenter.abiEncode_right_inj h⟩
  have := abiEncode_left h
  rwa [Contracts.InteropCenter.size_eq, Nat.mod_eq_of_lt c.isLt, Nat.mod_eq_of_lt c'.isLt] at this

theorem AtomicLegHashUnpublishedOrClash : Properties.AtomicLegHashUnpublishedOrClash := by
  intro P S hr henc pub hpub d hd hat p hp
  by_cases hh : publishedHash P.keccak p = bundleHash P d.bundle
  · by_cases hpre : abiEncode p.1.val p.2 = bundlePreimage P d.bundle
    · right; left
      obtain ⟨hc, hx⟩ := abiEncode_inj_word (c := p.1) (c' := P.chainId) hpre
      have hmem : (P.chainId, P.enc d.bundle) ∈ pub := by
        rw [← hc, ← hx]; exact hp
      obtain ⟨d', hd', hat', hx'⟩ := hpub _ hmem
      refine ⟨d', hd', hat', ?_⟩
      rcases Contracts.InteropCenter.AtomicBytesNeverPublished P S hr henc d hd hat d' hd' hat'
        with hne | hcl
      · exact absurd hx' hne
      · exact hcl
    · right; right; exact ⟨hpre, hh⟩
  · left; exact hh

theorem AtomicHasNoUnbundleRoute : Properties.AtomicHasNoUnbundleRoute := by
  intro P S hr henc pub hpub txs hts d hd hat
  by_cases hin : PubHashes P.keccak pub (bundleHash P d.bundle)
  · obtain ⟨p, hp, hph⟩ := hin
    rcases AtomicLegHashUnpublishedOrClash P S hr henc pub hpub d hd hat p hp with hne | hcl | hcol
    · exact absurd hph hne
    · exact Or.inr (Or.inl hcl)
    · exact Or.inr (Or.inr ⟨p, hp, hcol⟩)
  · exact Or.inl (submitAll_keeps_closed hin _ txs hts (Or.inl rfl))

/-! ## (e) The composite -/

theorem FinalizedLegStrandedByRevertingCall : Properties.FinalizedLegStrandedByRevertingCall := by
  intro hh z0 hl cv fh S hS F ev leg hex other hother Pub hpub txs hts hrs
  refine ⟨submitAll_keeps_stuck hpub _ txs hts hrs rfl, fun Ms log hrun => ?_⟩
  exact Contracts.Refund.OneExecutionFreezesTheFlowOrBreak hh z0 hl cv fh S hS F ev leg hex Ms log
    hrun other hother

/-! ## (h) The unbundled route is enabled -/

/-- What the deployed first loop leaves, from call `i` on, on a request it accepts. -/
def markedState (u : State) (h : BundleHash) (i : ℕ) (req : List CallStatus) : State where
  bundle := u.bundle
  call := fun h' j =>
    if h' = h ∧ i ≤ j then requestedStatus (u.call h j) req[j - i]? else u.call h' j

/-- Processing one more requested call: `markedState` shifts by one. -/
lemma markedState_cons {u u' : State} {h : BundleHash} {i : ℕ} {x : CallStatus}
    {req : List CallStatus} (hb : u'.bundle = u.bundle)
    (hi : u'.call h i = requestedStatus (u.call h i) (some x))
    (hother : ∀ h' j, ¬ (h' = h ∧ j = i) → u'.call h' j = u.call h' j) :
    markedState u' h (i + 1) req = markedState u h i (x :: req) := by
  unfold markedState
  rw [hb]
  congr 1
  funext h' j
  by_cases hh : h' = h
  · subst hh
    rcases lt_trichotomy j i with hj | rfl | hj
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), hother _ _ (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_left ⟨rfl, le_rfl⟩, hi, Nat.sub_self,
        List.getElem?_cons_zero]
    · rw [ite_eq_left ⟨rfl, by omega⟩, ite_eq_left ⟨rfl, by omega⟩, hother _ _ (by omega)]
      obtain ⟨k, rfl⟩ : ∃ k, j = i + 1 + k := ⟨j - (i + 1), by omega⟩
      rw [show i + 1 + k - i = k + 1 by omega, show i + 1 + k - (i + 1) = k by omega,
        List.getElem?_cons_succ]
  · rw [ite_eq_right (fun h => hh h.1), ite_eq_right (fun h => hh h.1),
      hother _ _ (fun h => hh h.1)]

/-- **THE FIRST LOOP ON AN ACCEPTED REQUEST.** -/
lemma markCalls_accepts (h : BundleHash) : ∀ (req : List CallStatus) (i : ℕ) (u : State),
    (∀ (k : ℕ) (hk : k < req.length),
      (req[k] = .Executed → u.call h (i + k) = .Unprocessed) ∧
      (req[k] = .Cancelled → u.call h (i + k) ≠ .Executed)) →
    markCalls true h i req u = some (markedState u h i req)
  | [], i, u, _ => by
    simp only [markCalls, Option.some.injEq]
    cases u with
    | mk bnd call =>
      simp only [markedState, List.getElem?_nil, requestedStatus, State.mk.injEq, true_and]
      funext h' j
      split_ifs with hc
      · rw [hc.1]
      · rfl
  | .Executed :: req, i, u, hv => by
    have h0 : u.call h i = .Unprocessed := by simpa using (hv 0 (by simp)).1 rfl
    simp only [markCalls, h0, ↓reduceIte]
    rw [markCalls_accepts h req (i + 1) _ ?_]
    · congr 1
      refine markedState_cons (by simp) (by simp [requestedStatus]) ?_
      intro h' j hne
      simp only [Contracts.InteropHandler.setCall_call]
      rw [ite_eq_right hne]
    · intro k hk
      have := hv (k + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      have hne : ¬ (h = h ∧ i + 1 + k = i) := by omega
      rw [Contracts.InteropHandler.setCall_call, ite_eq_right hne,
        show i + 1 + k = i + (k + 1) by omega]
      exact this
  | .Cancelled :: req, i, u, hv => by
    have h0 : u.call h i ≠ .Executed := by simpa using (hv 0 (by simp)).2 rfl
    simp only [markCalls, h0, ↓reduceIte]
    rw [markCalls_accepts h req (i + 1) _ ?_]
    · congr 1
      refine markedState_cons ?_ ?_ ?_
      · split_ifs <;> simp
      · show (if u.call h i = .Unprocessed then u.setCall h i .Cancelled else u).call h i = _
        simp only [requestedStatus]
        split_ifs with hu
        · simp
        · cases hc : u.call h i
          · exact absurd hc hu
          · exact absurd hc h0
          · rfl
      · intro h' j hne
        split_ifs
        · simp only [Contracts.InteropHandler.setCall_call]; rw [ite_eq_right hne]
        · rfl
    · intro k hk
      have := hv (k + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      have hne : ¬ (h = h ∧ i + 1 + k = i) := by omega
      rw [show i + (k + 1) = i + 1 + k by omega] at this
      split_ifs
      · rw [Contracts.InteropHandler.setCall_call, ite_eq_right hne]; exact this
      · exact this
  | .Unprocessed :: req, i, u, hv => by
    simp only [markCalls]
    rw [markCalls_accepts h req (i + 1) u ?_]
    · congr 1
      exact markedState_cons rfl (by simp [requestedStatus]) (fun _ _ _ => rfl)
    · intro k hk
      have := hv (k + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [show i + 1 + k = i + (k + 1) by omega]
      exact this

lemma toExecute_length_le : ∀ (i : ℕ) (req : List CallStatus), (toExecute i req).length ≤ req.length
  | _, [] => by simp [toExecute]
  | i, .Executed :: req => by
    have := toExecute_length_le (i + 1) req
    simp [toExecute]; omega
  | i, .Cancelled :: req => by
    have := toExecute_length_le (i + 1) req
    simp [toExecute]; omega
  | i, .Unprocessed :: req => by
    have := toExecute_length_le (i + 1) req
    simp [toExecute]; omega

/-- `unbundleBundle` with an accepted request and accepting targets. -/
theorem exec_unbundle_valid {s : State} {b : Bundle} {req : List CallStatus} {cs : List Callee}
    (hlen : req.length = b.calls) (hst : s.bundle b.hash = .Verified ∨ s.bundle b.hash = .Unbundled)
    (hvalid : RequestValid s b.hash req) (hcs : ∀ c ∈ cs, c = .returns) :
    exec .deployed (b.calls + 2) (.entry (.unbundleBundle b req) cs) s =
      some (applyRequest s b.hash req, (toExecute 0 req).map (Effect.delivered b.hash)) := by
  have hm : markCalls true b.hash 0 req (s.setBundle b.hash .Unbundled)
      = some (markedState (s.setBundle b.hash .Unbundled) b.hash 0 req) := by
    apply markCalls_accepts
    intro k hk
    simpa using hvalid k hk
  have hloop := Contracts.InteropHandler.exec_calls_returns .deployed b.hash (toExecute 0 req) cs
    (b.calls + 1) (markedState (s.setBundle b.hash .Unbundled) b.hash 0 req) hcs
    (by have := toExecute_length_le 0 req; omega)
  have hres : markedState (s.setBundle b.hash .Unbundled) b.hash 0 req = applyRequest s b.hash req := by
    unfold markedState applyRequest
    congr 1
    funext h' j
    by_cases hh : h' = b.hash
    · subst hh; simp
    · simp [hh]
  show exec .deployed (b.calls + 1 + 1) _ s = _
  simp only [exec, Contracts.InteropHandler.writesCallsFirst_deployed]
  rw [ite_eq_left ⟨hlen, hst⟩, hm]
  simp only [hloop, Contracts.InteropHandler.afterUnbundle_deployed]
  rw [hres]

theorem UnbundleEnabled : Properties.UnbundleEnabled := by
  intro s b req cs hlen hst hvalid hcs
  simp only [submit, exec_unbundle_valid hlen hst hvalid hcs, commit]

/-! ## (e) The public contrast -/

lemma toExecute_map_range' (g : ℕ → CallStatus) : ∀ (m k : ℕ),
    toExecute k ((List.range' k m).map g) = (List.range' k m).filter (fun j => g j = .Executed)
  | 0, k => by simp [toExecute]
  | m + 1, k => by
    rw [List.range'_succ, List.map_cons, List.filter_cons]
    have ih := toExecute_map_range' g m (k + 1)
    cases g k <;> simp [toExecute, ih]

lemma toExecute_escape (n i : ℕ) :
    toExecute 0 (escapeRequest n i) = (List.range n).filter (· ≠ i) := by
  unfold escapeRequest
  rw [List.range_eq_range', toExecute_map_range']
  apply List.filter_congr
  intro j _
  by_cases hj : j = i <;> simp [hj]

lemma escapeRequest_get (n i j : ℕ) (hj : j < n) :
    (escapeRequest n i)[j]? = some (if j = i then .Cancelled else .Executed) := by
  simp [escapeRequest, List.getElem?_map, List.getElem?_range hj]

lemma escapeRequest_length (n i : ℕ) : (escapeRequest n i).length = n := by
  simp [escapeRequest]

/-- The verify-then-unbundle run, computed. -/
lemma escape_run (b : Bundle) (i : ℕ) :
    submitAll .deployed init
        [⟨1, .verifyBundle b true, []⟩, ⟨b.calls + 2, .unbundleBundle b (escapeRequest b.calls i), []⟩]
      = (applyRequest (init.setBundle b.hash .Verified) b.hash (escapeRequest b.calls i),
          (toExecute 0 (escapeRequest b.calls i)).map (Effect.delivered b.hash)) := by
  have h1 : submit .deployed init ⟨1, .verifyBundle b true, []⟩ = (init.setBundle b.hash .Verified, []) := by
    simp [submit, exec, commit, init]
  have hvalid : RequestValid (init.setBundle b.hash .Verified) b.hash (escapeRequest b.calls i) := by
    intro j hj
    exact ⟨fun _ => rfl, fun _ => by simp [init]⟩
  have h2 := UnbundleEnabled (init.setBundle b.hash .Verified) b (escapeRequest b.calls i) []
    (escapeRequest_length _ _) (Or.inl (by simp)) hvalid (by simp)
  simp [submitAll, h1, h2]

theorem PublicBundleEscapesViaUnbundle : Properties.PublicBundleEscapesViaUnbundle := by
  intro b i hi
  refine ⟨fun n ok cs s hr => (Contracts.InteropHandler.RevertingCallRevertsTheExecution .deployed
    n b ok cs s hr).2, ?_⟩
  rw [escape_run]
  refine ⟨by simp [applyRequest], ?_, fun j hj hji => ?_, by rw [toExecute_escape]⟩
  · simp [applyRequest, escapeRequest_get _ _ _ hi, requestedStatus]
  · simp [applyRequest, escapeRequest_get _ _ _ hj, hji, requestedStatus]

/-! ## (f) Who may execute -/

theorem ExecutorGatedLegNeedsExecutor : Properties.ExecutorGatedLegNeedsExecutor := by
  intro thisChain ch a r hr
  cases r with
  | direct caller =>
    simp only [ExecutionPermitted] at hr
    rcases hr with h | ⟨ch', a', heq, hch, ha⟩
    · exact absurd h (by simp)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq)
      exact ⟨by rw [ha], hch⟩
  | rescue sc sa => exact hr.elim

theorem ForeignExecutorStrandsAtomicLeg : Properties.ForeignExecutorStrandsAtomicLeg := by
  intro thisChain ch a h1 h2
  refine ⟨fun r hr => ?_, Or.inr ⟨ch, a, rfl, Or.inl rfl, rfl⟩⟩
  rcases (ExecutorGatedLegNeedsExecutor thisChain ch a r hr).2 with h | h
  · exact h1 h
  · exact h2 h

/-! ## (g) A `Verified` hash -/

lemma reach_not_unreceived {a c : Status} (h : AttackVectors.BundleStatusMachine.Reach a c)
    (ha : a ≠ .Unreceived) : c ≠ .Unreceived := by
  induction h with
  | refl => exact ha
  | tail _ hs _ => cases hs <;> decide

lemma exec_atomic_of_not_unreceived {s : State} {b : Bundle} (hne : s.bundle b.hash ≠ .Unreceived)
    (n : ℕ) (ok : Bool) (cs : List Callee) :
    exec .deployed n (.entry (.executeAtomicBundle b ok) cs) s = none := by
  cases n with
  | zero => simp [exec]
  | succ n => simp [exec, hne]

/-- `executeBundle` of a `Verified` bundle with no proof and accepting targets. -/
lemma exec_public_verified {s : State} {b : Bundle} (hv : s.bundle b.hash = .Verified)
    {cs : List Callee} (hcs : ∀ c ∈ cs, c = .returns) :
    exec .deployed (b.calls + 2) (.entry (.executeBundle b false) cs) s =
      some (beforeCalls .deployed b s,
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash]) := by
  have hvi : s.verifyIfUnreceived b.hash = s := by
    simp [State.verifyIfUnreceived, hv]
  show exec .deployed (b.calls + 1 + 1) _ s = _
  simp only [exec, hv, true_or, ↓reduceIte, hvi]
  rw [Contracts.InteropHandler.exec_calls_returns .deployed b.hash _ _ _ _ hcs (by simp)]
  rfl

theorem GriefVerifiedBlocksAtomic : Properties.GriefVerifiedBlocksAtomic := by
  intro s b hv
  have hnot : ∀ txs : List Tx, (submitAll .deployed s txs).1.bundle b.hash ≠ .Unreceived := by
    intro txs
    have hr := (Contracts.InteropHandler.submitAll_good s txs).reach b.hash
    exact reach_not_unreceived hr (by rw [hv]; decide)
  refine ⟨hnot, fun txs n ok cs => exec_atomic_of_not_unreceived (hnot txs) n ok cs,
    fun cs hcs => ?_⟩
  simp only [submit, exec_public_verified hv hcs, commit,
    Contracts.InteropHandler.beforeCalls_deployed]

/-! ## (h) The atomic route is enabled -/

/-- `executeAtomicBundle` of an `Unreceived` bundle with the gate passing and accepting targets. -/
lemma exec_atomic_accepting {s : State} {b : Bundle} (hu : s.bundle b.hash = .Unreceived)
    {cs : List Callee} (hcs : ∀ c ∈ cs, c = .returns) :
    exec .deployed (b.calls + 2) (.entry (.executeAtomicBundle b true) cs) s =
      some (beforeCalls .deployed b s,
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash]) := by
  show exec .deployed (b.calls + 1 + 1) _ s = _
  simp only [exec, hu, and_self, ↓reduceIte]
  rw [Contracts.InteropHandler.exec_calls_returns .deployed b.hash _ _ _ _ hcs (by simp)]
  rfl

theorem FinalizedLegExecutableUnderEnabledness :
    Properties.FinalizedLegExecutableUnderEnabledness := by
  intro Pub b hpub txs hts
  rcases submitAll_keeps_closed hpub init txs hts (Or.inl rfl) with hu | hfe
  · right
    refine ⟨hu, fun cs hcs => ?_⟩
    simp only [submit, exec_atomic_accepting hu hcs, commit,
      Contracts.InteropHandler.beforeCalls_deployed]
  · exact Or.inl hfe

/-! ## Witnesses -/

theorem NoUnbundleRouteWitness : Properties.NoUnbundleRouteWitness := by
  have hh1 : bundleHash Contracts.InteropCenter.wParams Contracts.InteropCenter.wD1.bundle = 1 :=
    Contracts.InteropCenter.wHash1
  have hh2 : bundleHash Contracts.InteropCenter.wParams Contracts.InteropCenter.wD2.bundle = 2 :=
    Contracts.InteropCenter.wHash2
  have hlog : Contracts.InteropCenter.wS3.log = [Contracts.InteropCenter.wD1,
    Contracts.InteropCenter.wD2] := rfl
  have hp2 : publishedHash Contracts.InteropCenter.wParams.keccak
      (Contracts.InteropCenter.wParams.chainId,
        Contracts.InteropCenter.wParams.enc Contracts.InteropCenter.wD2.bundle) = 2 := hh2
  refine ⟨Contracts.InteropCenter.wReach, ?_, ?_, ?_, by rw [hlog]; simp, rfl, hh1,
    by decide, by decide, ?_, ?_⟩
  · rw [hlog]
    exact Contracts.InteropCenter.encInjOn_pair Contracts.InteropCenter.wEnc_ne
  · intro x hx
    simp only [wPub, List.mem_singleton, Prod.mk.injEq, true_and] at hx
    exact ⟨Contracts.InteropCenter.wD2, by rw [hlog]; simp, rfl, hx⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨fun _ => ⟨_, List.mem_singleton_self _, hp2⟩, by simp [wVerifyPublic]⟩
    · exact ⟨trivial, by simp [wExecAtomic]⟩
  · rintro ⟨d', hd', hat', hcl⟩
    rw [hlog] at hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with rfl | rfl
    · exact absurd hat' (by decide)
    · exact absurd hcl.1 (by decide)
  · rintro ⟨p, hp, -, hph⟩
    simp only [wPub, List.mem_singleton] at hp
    subst hp
    rw [hp2, hh1] at hph
    exact absurd hph (by decide)

theorem StrandedLegWitness : Properties.StrandedLegWitness := by
  intro hh z0 hl
  have h1 : (0 : UInt256) < 1 := by decide
  refine ⟨fun _ _ => 1, Contracts.Refund.lengthFlowHash, Contracts.Atomicity.mixedSystem 1,
    Contracts.Atomicity.subsetFlow 0 1,
    fun _ => (0, Contracts.Atomicity.honestProof hh z0 hl (Contracts.Atomicity.mixedSystem 1) 0 0 1),
    ⟨0, 1⟩, ⟨0, 1⟩, [wRevertingAttempt 1, wNestedRevertingAttempt 1],
    Contracts.Atomicity.mixedSystem_wf h1,
    (Contracts.Refund.subsetFlow_executes hh z0 hl _ Contracts.Refund.lengthFlowHash_checks_subset).1,
    List.mem_singleton_self _, rfl, ?_, by decide, ?_, by decide⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · refine ⟨trivial, fun c hc => ?_⟩
      simp only [wRevertingAttempt, List.mem_singleton] at hc
      subst hc; exact .reverts
    · refine ⟨trivial, fun c hc => ?_⟩
      simp only [wNestedRevertingAttempt, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact .calls (fun _ => rfl) (by simp) .returns
      · exact .reverts
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · refine ⟨fun _ => by simp [wRevertingAttempt], fun c hc => ?_⟩
      simp only [wRevertingAttempt, List.mem_singleton] at hc
      subst hc; exact .reverts
    · refine ⟨fun _ => by simp [wNestedRevertingAttempt], fun c hc => ?_⟩
      simp only [wNestedRevertingAttempt, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact .calls trivial (by simp) .returns
      · exact .reverts

theorem GriefWitness : Properties.GriefWitness := by
  unfold Properties.GriefWitness; decide

theorem EnablednessWitness : Properties.EnablednessWitness := by
  refine ⟨⟨by decide, ?_, by decide⟩, ⟨?_, by decide, by decide⟩⟩
  · intro j hj
    have hj' : j < 2 := by simpa using hj
    interval_cases j <;> simp [submit, exec, commit, wVerify, init]
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨fun _ => rfl, by simp [wVerify]⟩

theorem ExecutorGateWitness : Properties.ExecutorGateWitness :=
  ⟨Or.inr ⟨324, 7, rfl, Or.inl rfl, rfl⟩, Or.inr ⟨325, 7, rfl, Or.inl rfl, rfl⟩⟩

end Contracts.ExecutionLiveness
