import EraSpec.Protocol.InteropAtomicity.Properties.ExecutionLiveness
import EraSpec.Contracts.InteropHandlerBase.Proofs.BundleStatusMachineStrong
import EraSpec.Contracts.InteropHandlerBase.Proofs.ReentrancyStrong
import EraSpec.Contracts.InteropHandlerBase.Proofs.SelfCallAuthorityFaithful
import EraSpec.Contracts.InteropCenter.Proofs.Dispatch
import EraSpec.Protocol.InteropAtomicity.Proofs.Refund
import EraSpec.Protocol.InteropAtomicity.Proofs.RootImport

/-!
# Proofs: what an atomic leg can still do on its destination

**(d)** Each public entry point's guard reads the bundle status first; outside `Verified` and
`Unbundled`, and with the proof bit `false`, every guard fails.

**(e)** One induction on the budget, over every frame kind, in the style of
`Contracts.InteropHandler.exec_atomicPart` (topic `BundleStatusMachineStrong`), with two
hypotheses carried down: no entry-point call of the frame presents a valid proof for `h`
(`Frame.Mentions`), and every atomic attempt on `h` in it meets an always-reverting target
(`FrameEvery`). A committed frame started with `h` `Unreceived` then ends with `h` `Unreceived` and
commits no effect of `h` (`exec_keeps_unreceived`): an atomic attempt on `h` would revert
(`Contracts.InteropHandler.AlwaysRevertingTargetRevertsTheExecution`), so a committed one is on
another hash, and every other route to `h` needs a valid proof or a status `h` does not have. The
source-run form discharges the no-proof premise with
`Contracts.InteropHandler.published_atomic_hash_clashes`, as
`AtomicLegStaysAtomicAtDestinationOrClash` does.

**(f)** A call reaching `executeAtomicBundle` at the pin is direct
(`AttackVectors.SelfCallAuthority.Faithful.AtomicSelfDisjunctDeadAtPin`), and for a direct caller
the gate's self disjunct is false, which leaves the attribute comparison. The relayed
`executeBundle` is the first arm of the pin's dispatch table, computed.

**(h)** `unbundleBundle`'s first loop on an accepted request computes `applyRequest`
(`markCalls_accepts`, by induction on the request), and a loop whose targets accept delivers every
listed call (`Contracts.InteropHandler.exec_calls_returns`). The atomic route stays open because
a no-proof run keeps the hash in the atomic sub-machine
(`Contracts.InteropHandler.submitAll_atomicPart`).
-/

namespace Contracts.ExecutionLiveness

open Contracts.InteropHandler (State Entry Callee Frame Tx Bundle BundleHash Effect exec submit
  submitAll toExecute markCalls commit init Variant beforeCalls afterCalls afterUnbundle
  writesCallsFirst NoProofRun SoundProofRun PublishedHash PublishesOnlyPublicDispatches
  AlwaysReverts mentions_headD mentions_tail)
open AttackVectors.BundleStatusMachine (Status CallStatus)
open AttackVectors.BundleHashEncoding (abiEncode HashCollision)
open Contracts.InteropCenter (Params Dispatch CrossSenderSaltClash EncInjOn bundleHash
  bundlePreimage)
open MerkleSpec (Hash)
open Contracts.InteropCommitmentTree (LeafHash)
open Contracts.Atomicity (CommitValue FlowHash System Wf Flow FlowLeg GateEvidence ExecutedViaBy)
open Contracts.Refund (Managers AuthCall ReachLog emptyManagers Refunded RefundBreak obligationOf)
open AttackVectors.SelfCallAuthority.Faithful (GateCall GateAttrs Reaches pinnedTable InnerGate
  dispatch)

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

/-- The writes before a whole-bundle execution's calls touch only that bundle's status. -/
lemma beforeCalls_bundle_other {b : Bundle} {s : State} {h : BundleHash} (hne : h ≠ b.hash) :
    (beforeCalls .deployed b s).bundle h = s.bundle h := by
  simp [hne]

lemma verifyIfUnreceived_bundle_other {s : State} {h h' : BundleHash} (hne : h ≠ h') :
    (s.verifyIfUnreceived h').bundle h = s.bundle h := by
  unfold State.verifyIfUnreceived
  split_ifs <;> simp [hne]

/-! ## (d) Outside `Verified`, the other routes revert -/

theorem PublicRoutesRevertOutsideVerified : Properties.PublicRoutesRevertOutsideVerified := by
  intro s b hc n cs
  have hv : s.bundle b.hash ≠ .Verified := by rcases hc with h1 | h1 <;> rw [h1] <;> decide
  have hu : s.bundle b.hash ≠ .Unbundled := by rcases hc with h1 | h1 <;> rw [h1] <;> decide
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

/-! ## (e) A call that always reverts -/

/-- A loop frame is not one of `h`'s own: the hash whose calls it delivers differs from `h`. -/
def NotLoopOf (h : BundleHash) : Frame → Prop
  | .calls h' _ _ => h' ≠ h
  | _ => True

/-- **THE FRAME INVARIANT FOR (e).** With no valid proof for `h` presented and every atomic attempt
on `h` meeting an always-reverting target, a committed frame started with `h` `Unreceived` ends
with `h` `Unreceived` and commits no effect of `h`. -/
theorem exec_keeps_unreceived {h : BundleHash} :
    ∀ (n : ℕ) (f : Frame) (s s' : State) (l : List Effect),
      exec .deployed n f s = some (s', l) → (∀ e, f.Mentions e → e.NoProofFor h) →
      FrameEvery (AtomicAttemptReverts h) f → NotLoopOf h f → s.bundle h = .Unreceived →
        s'.bundle h = .Unreceived ∧ ∀ e ∈ l, e.bundleHash ≠ h := by
  intro n
  induction n with
  | zero => intro f s s' l hx; simp [exec] at hx
  | succ n ih =>
    intro f s s' l hx hnp hr hloop hu
    match f, hr with
    | .entry (.executeBundle b ok) cs, ⟨_, hrs⟩ =>
      simp only [exec] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₂ l₂ heq
        simp only [Contracts.InteropHandler.afterCalls_deployed, Option.some.injEq,
          Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        have hne : b.hash ≠ h := by
          intro hb
          rcases hG with hv | ⟨_, hok⟩
          · rw [hb, hu] at hv; exact absurd hv (by decide)
          · have hf : ok = false := hnp (.executeBundle b ok) (Or.inl rfl) hb
            rw [hf] at hok; exact absurd hok (by decide)
        have hu' : (beforeCalls .deployed b (s.verifyIfUnreceived b.hash)).bundle h
            = .Unreceived := by
          rw [beforeCalls_bundle_other (Ne.symm hne), verifyIfUnreceived_bundle_other (Ne.symm hne)]
          exact hu
        obtain ⟨h1, h2⟩ := ih _ _ _ _ heq (fun e he => hnp e (Or.inr he)) hrs hne hu'
        refine ⟨h1, fun e he => ?_⟩
        rcases List.mem_append.mp he with he | he
        · exact h2 e he
        · rw [List.mem_singleton] at he; subst he; exact hne
      · simp at hx
    | .entry (.executeAtomicBundle b ok) cs, ⟨hra, hrs⟩ =>
      have hne : b.hash ≠ h := by
        intro hb
        have hnone :=
          (Contracts.InteropHandler.AlwaysRevertingTargetRevertsTheExecution .deployed (n + 1)
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
        obtain ⟨h1, h2⟩ := ih _ _ _ _ heq (fun e he => hnp e (Or.inr he)) hrs hne hu'
        refine ⟨h1, fun e he => ?_⟩
        rcases List.mem_append.mp he with he | he
        · exact h2 e he
        · rw [List.mem_singleton] at he; subst he; exact hne
      · simp at hx
    | .entry (.verifyBundle b ok) cs, _ =>
      simp only [exec] at hx
      split_ifs at hx with hG
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      have hne : b.hash ≠ h := by
        intro hb
        have hf : ok = false := hnp (.verifyBundle b ok) (Or.inl rfl) hb
        rw [hf] at hG; exact absurd hG.2 (by decide)
      refine ⟨?_, by simp⟩
      rw [Contracts.InteropHandler.setBundle_bundle, ite_eq_right (Ne.symm hne)]
      exact hu
    | .entry (.unbundleBundle b req) cs, ⟨_, hrs⟩ =>
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
          exact ih _ _ _ _ heq (fun e he => hnp e (Or.inr he)) hrs hne hu'
        · simp at hx
      · simp at hx
    | .calls hb [] cs, _ =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨hu, by simp⟩
    | .calls hb (i :: is) cs, hrs =>
      simp only [exec] at hx
      split at hx
      · rename_i s₁ l₁ heq₁
        split at hx
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          have hne : hb ≠ h := hloop
          obtain ⟨h1, h2⟩ := ih _ _ _ _ heq₁ (fun e he => hnp e (mentions_headD he))
            (headD_every hrs) trivial hu
          obtain ⟨h3, h4⟩ := ih _ _ _ _ heq₂ (fun e he => hnp e (mentions_tail he))
            (tail_every hrs) hne h1
          refine ⟨h3, fun e he => ?_⟩
          rcases List.mem_cons.mp he with rfl | he
          · exact hne
          · rcases List.mem_append.mp he with he | he
            · exact h2 e he
            · exact h4 e he
        · simp at hx
      · simp at hx
    | .target .returns, _ =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨hu, by simp⟩
    | .target .reverts, _ => simp [exec] at hx
    | .target (.calls e inner caught next), hrcall =>
      cases hrcall with
      | calls hrq hrinner hrnext =>
        have hnp₁ : ∀ e', Frame.Mentions (.entry e inner) e' → e'.NoProofFor h := by
          intro e' he'
          apply hnp e'
          rcases he' with rfl | ⟨c, hc, hm⟩
          · exact Contracts.InteropHandler.Callee.Mentions.here
          · exact Contracts.InteropHandler.Callee.Mentions.nested hc hm
        have hnp₂ : ∀ e', Frame.Mentions (.target next) e' → e'.NoProofFor h :=
          fun e' he' => hnp e' (Contracts.InteropHandler.Callee.Mentions.cont he')
        simp only [exec] at hx
        split at hx
        · rename_i s₁ l₁ heq₁
          split at hx
          · rename_i s₂ l₂ heq₂
            simp only [Option.some.injEq, Prod.mk.injEq] at hx
            obtain ⟨rfl, rfl⟩ := hx
            obtain ⟨h1, h2⟩ := ih _ _ _ _ heq₁ hnp₁ ⟨hrq, hrinner⟩ trivial hu
            obtain ⟨h3, h4⟩ := ih _ _ _ _ heq₂ hnp₂ hrnext trivial h1
            refine ⟨h3, fun e he => ?_⟩
            rcases List.mem_append.mp he with he | he
            · exact h2 e he
            · exact h4 e he
          · simp at hx
        · split_ifs at hx
          exact ih _ _ _ _ hx hnp₂ hrnext trivial hu

lemma submit_keeps_unreceived {h : BundleHash} {s : State} {t : Tx}
    (hnp : ∀ e, t.Mentions e → e.NoProofFor h) (hr : TxEvery (AtomicAttemptReverts h) t)
    (hu : s.bundle h = .Unreceived) :
    (submit .deployed s t).1.bundle h = .Unreceived ∧
      ∀ e ∈ (submit .deployed s t).2, e.bundleHash ≠ h := by
  unfold submit
  cases hx : exec .deployed t.fuel (.entry t.entry t.callees) s with
  | none => exact ⟨hu, by simp [commit]⟩
  | some r =>
    obtain ⟨s', l⟩ := r
    exact exec_keeps_unreceived _ _ _ _ _ hx hnp hr trivial hu

lemma submitAll_keeps_unreceived {h : BundleHash} :
    ∀ (s : State) (txs : List Tx), NoProofRun h txs →
      (∀ t ∈ txs, TxEvery (AtomicAttemptReverts h) t) → s.bundle h = .Unreceived →
      (submitAll .deployed s txs).1.bundle h = .Unreceived ∧
        ∀ e ∈ (submitAll .deployed s txs).2, e.bundleHash ≠ h
  | _, [], _, _, hu => ⟨hu, by simp [submitAll]⟩
  | s, t :: ts, hnp, hrs, hu => by
    obtain ⟨h1, h2⟩ := submit_keeps_unreceived (hnp t List.mem_cons_self)
      (hrs t List.mem_cons_self) hu
    obtain ⟨h3, h4⟩ := submitAll_keeps_unreceived _ ts
      (fun t' ht' => hnp t' (List.mem_cons_of_mem _ ht'))
      (fun t' ht' => hrs t' (List.mem_cons_of_mem _ ht')) h1
    refine ⟨h3, fun e he => ?_⟩
    simp only [submitAll, List.mem_append] at he
    rcases he with he | he
    · exact h2 e he
    · exact h4 e he

theorem AtomicLegWithRevertingCallNeverExecutes :
    Properties.AtomicLegWithRevertingCallNeverExecutes :=
  fun _ s txs hu hnp hrs => submitAll_keeps_unreceived s txs hnp hrs hu

/-- A run whose valid proofs are all for published hashes presents none for an atomic leg's hash,
unless one of the two named clashes. -/
lemma noProofRun_of_sound {P : Params} {S : Contracts.InteropCenter.State}
    (hreach : Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed P
      Contracts.InteropCenter.init S)
    (henc : EncInjOn P.enc (S.log.map Dispatch.bundle))
    {pubs : List (UInt256 × List UInt8)} (hpubs : PublishesOnlyPublicDispatches P S.log pubs)
    {d : Dispatch} (hd : d ∈ S.log) (hat : d.isAtomic = true) {txs : List Tx}
    (hsound : SoundProofRun (PublishedHash P.keccak pubs) txs)
    (hclash : ¬ ((∃ d' ∈ S.log, d'.isAtomic = false ∧ CrossSenderSaltClash P d d')
      ∨ (∃ p ∈ pubs, HashCollision P.keccak (bundlePreimage P d.bundle) (abiEncode p.1.val p.2)))) :
    NoProofRun (bundleHash P d.bundle) txs := by
  intro t ht e he
  have hsnd := hsound t ht e he
  cases e with
  | executeBundle b ok =>
    intro hbh
    cases ok with
    | false => rfl
    | true =>
      exfalso
      have hpub := hsnd rfl
      rw [hbh] at hpub
      exact hclash (Contracts.InteropHandler.published_atomic_hash_clashes hreach henc hpubs hd hat
        hpub)
  | verifyBundle b ok =>
    intro hbh
    cases ok with
    | false => rfl
    | true =>
      exfalso
      have hpub := hsnd rfl
      rw [hbh] at hpub
      exact hclash (Contracts.InteropHandler.published_atomic_hash_clashes hreach henc hpubs hd hat
        hpub)
  | unbundleBundle _ _ => trivial
  | executeAtomicBundle _ _ => trivial

theorem AtomicLegWithRevertingCallNeverExecutesOrClash :
    Properties.AtomicLegWithRevertingCallNeverExecutesOrClash := by
  intro P S hreach henc pubs hpubs d hd hat s txs hu hsound hrs
  by_cases hclash :
      (∃ d' ∈ S.log, d'.isAtomic = false ∧ CrossSenderSaltClash P d d')
      ∨ (∃ p ∈ pubs, HashCollision P.keccak (bundlePreimage P d.bundle) (abiEncode p.1.val p.2))
  · exact Or.inr hclash
  · exact Or.inl (submitAll_keeps_unreceived s txs
      (noProofRun_of_sound hreach henc hpubs hd hat hsound hclash) hrs hu)

theorem FinalizedRevertingLegNeitherDeliveredNorRefunded :
    Properties.FinalizedRevertingLegNeitherDeliveredNorRefunded := by
  intro hh z0 hl cv fh S hS F ev leg hex other hother txs hnp hrs
  refine ⟨submitAll_keeps_unreceived _ txs hnp hrs rfl, fun Ms log hrun => ?_⟩
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

/-! ## (e) The contrast: a bundle that can be verified -/

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
    submitAll .deployed init (escapeRun b i)
      = (applyRequest (init.setBundle b.hash .Verified) b.hash (escapeRequest b.calls i),
          (toExecute 0 (escapeRequest b.calls i)).map (Effect.delivered b.hash)) := by
  have h1 : submit .deployed init ⟨1, .verifyBundle b true, []⟩ = (init.setBundle b.hash .Verified, []) := by
    simp [submit, exec, commit, init]
  have hvalid : RequestValid (init.setBundle b.hash .Verified) b.hash (escapeRequest b.calls i) := by
    intro j hj
    exact ⟨fun _ => rfl, fun _ => by simp [init]⟩
  have h2 := UnbundleEnabled (init.setBundle b.hash .Verified) b (escapeRequest b.calls i) []
    (escapeRequest_length _ _) (Or.inl (by simp)) hvalid (by simp)
  simp [escapeRun, submitAll, h1, h2]

theorem PublicBundleEscapesViaUnbundle : Properties.PublicBundleEscapesViaUnbundle := by
  intro b i hi
  refine ⟨fun n ok cs s hr =>
    (Contracts.InteropHandler.AlwaysRevertingTargetRevertsTheExecution .deployed n b ok cs s hr).2, ?_⟩
  rw [escape_run]
  refine ⟨by simp [applyRequest], ?_, fun j hj hji => ?_, by rw [toExecute_escape]⟩
  · simp [applyRequest, escapeRequest_get _ _ _ hi, requestedStatus]
  · simp [applyRequest, escapeRequest_get _ _ _ hj, hji, requestedStatus]

/-! ## (f) Who may execute an atomic leg -/

theorem ExecutorGatedLegNeedsExecutor : Properties.ExecutorGatedLegNeedsExecutor := by
  intro handler thisChain ch a gc hr hent hexe hgate
  -- at the pin no arm of `receiveMessage` self-calls `executeAtomicBundle`
  have hne := AttackVectors.SelfCallAuthority.Faithful.AtomicSelfDisjunctDeadAtPin handler
    thisChain gc hr hent
  cases hr with
  | direct e attrs caller hcaller =>
    have hx : attrs.execution = .evm ch a := hexe
    simp only [InnerGate, hx] at hgate
    rcases hgate with h | ⟨hch, ha⟩
    · exact absurd h hcaller
    · exact ⟨hcaller, ha.symm, by rw [ha], hch⟩
  | relayed caller m sc hd => exact absurd rfl hne

theorem ForeignChainExecutorHasNoAtomicRoute :
    Properties.ForeignChainExecutorHasNoAtomicRoute := by
  intro handler thisChain ch a attrs hexe h1 h2
  have hd : dispatch pinnedTable handler handler ⟨some (ch, a), some (.entry .executeBundle), attrs⟩
      = some ⟨.executeBundle, attrs, (ch, a)⟩ := by
    simp [dispatch, AttackVectors.SelfCallAuthority.Faithful.branchFor, pinnedTable,
      AttackVectors.SelfCallAuthority.Faithful.Admits, hexe,
      AttackVectors.SelfCallAuthority.Faithful.AddrField.Names]
  refine ⟨fun gc hr hent hattrs hgate => ?_, hd, Reaches.relayed handler _ _ hd, ?_⟩
  · subst hattrs
    rcases (ExecutorGatedLegNeedsExecutor handler thisChain ch a gc hr hent hexe hgate).2.2.2
      with h | h
    · exact h1 h
    · exact h2 h
  · simp [InnerGate, hexe]

/-! ## (h) The atomic route stays enabled -/

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

theorem AtomicRouteStaysEnabled : Properties.AtomicRouteStaysEnabled := by
  intro b txs hnp
  rcases Contracts.InteropHandler.submitAll_atomicPart b.hash init txs hnp (Or.inl rfl)
    with hu | hfe
  · right
    refine ⟨hu, fun cs hcs => ?_⟩
    simp only [submit, exec_atomic_accepting hu hcs, commit,
      Contracts.InteropHandler.beforeCalls_deployed]
  · exact Or.inl hfe

/-! ## Witnesses -/

lemma reverts_alwaysReverts : AlwaysReverts .deployed .reverts := by
  intro m t
  cases m <;> rfl

theorem RevertingLegWitness : Properties.RevertingLegWitness := by
  intro hh z0 hl
  refine ⟨Contracts.RootImport.imtEvidence (Contracts.RootImport.twoChainEvidence hh z0 hl 0),
    Contracts.RootImport.twoChain_wf,
    Contracts.RootImport.executed_at_projects
      (Contracts.RootImport.twoChain_executed_at hh z0 hl (sl := 0) (imp := fun _ => True)
        (d := 0) trivial),
    by decide, by decide, ?_, ?_, by decide, by decide⟩
  · intro t ht e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · rcases he with rfl | ⟨c, hc, hm⟩
      · trivial
      · simp only [wRevertingAttempt, List.mem_singleton] at hc
        subst hc
        cases hm
    · rcases he with rfl | ⟨c, hc, hm⟩
      · trivial
      · simp only [wNestedRevertingAttempt, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · cases hm with
          | here => intro h3; exact absurd h3 (by decide)
          | nested hc' _ => simp at hc'
          | cont hm' => cases hm'
        · cases hm
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · refine ⟨fun _ => ⟨.reverts, by simp [wRevertingAttempt], reverts_alwaysReverts⟩,
        fun c hc => ?_⟩
      simp only [wRevertingAttempt, List.mem_singleton] at hc
      subst hc; exact .reverts
    · refine ⟨fun _ => ⟨.reverts, by simp [wNestedRevertingAttempt], reverts_alwaysReverts⟩,
        fun c hc => ?_⟩
      simp only [wNestedRevertingAttempt, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact .calls trivial (by simp) .returns
      · exact .reverts

theorem RevertingLegFromSourceWitness : Properties.RevertingLegFromSourceWitness := by
  have hlog : Contracts.InteropCenter.wS3.log =
      [Contracts.InteropCenter.wD1, Contracts.InteropCenter.wD2] := rfl
  have h12 : (1 : UInt256) ≠ 2 := by decide
  refine ⟨Contracts.InteropCenter.wReach, ?_, ?_, by rw [hlog]; simp, rfl,
    Contracts.InteropCenter.wHash1, rfl, ?_, ?_, by decide, ?_, ?_⟩
  · rw [hlog]
    exact Contracts.InteropCenter.encInjOn_pair Contracts.InteropCenter.wEnc_ne
  · intro p hp _
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨Contracts.InteropCenter.wD2, by rw [hlog]; simp, rfl, rfl⟩
  · intro t ht e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · rw [Contracts.InteropHandler.tx_mentions_nil rfl he]
      intro _
      exact ⟨_, List.mem_singleton_self _, Contracts.InteropCenter.wHash2.symm⟩
    · rcases he with rfl | ⟨c, hc, hm⟩
      · trivial
      · simp only [wRevertingAttempt, List.mem_singleton] at hc
        subst hc
        cases hm
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨trivial, by simp [wVerify]⟩
    · refine ⟨fun _ => ⟨.reverts, by simp [wRevertingAttempt], reverts_alwaysReverts⟩,
        fun c hc => ?_⟩
      simp only [wRevertingAttempt, List.mem_singleton] at hc
      subst hc; exact .reverts
  · rintro ⟨d', hd', hat', hcl⟩
    rw [hlog] at hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with rfl | rfl
    · exact absurd hat' (by decide)
    · exact absurd hcl.1 (by decide)
  · rintro ⟨p, hp, -, hk⟩
    simp only [List.mem_singleton] at hp
    subst hp
    have hk' : bundleHash Contracts.InteropCenter.wParams Contracts.InteropCenter.wD1.bundle =
        bundleHash Contracts.InteropCenter.wParams Contracts.InteropCenter.wD2.bundle := hk
    rw [Contracts.InteropCenter.wHash1, Contracts.InteropCenter.wHash2] at hk'
    exact h12 hk'

theorem EscapeWitness : Properties.EscapeWitness := by
  unfold Properties.EscapeWitness; decide

theorem EnablednessWitness : Properties.EnablednessWitness := by
  refine ⟨⟨by decide, ?_, by decide⟩, ⟨?_, ?_, by decide⟩⟩
  · intro j hj
    have hj' : j < 2 := by simpa using hj
    interval_cases j <;> simp [submit, exec, commit, wVerify, init]
  · intro t ht e he
    simp only [List.mem_singleton] at ht
    subst ht
    rw [Contracts.InteropHandler.tx_mentions_nil rfl he]
    intro h3
    exact absurd h3 (by decide)
  · intro hnp
    have := hnp (wVerify 3 2) List.mem_cons_self (.verifyBundle ⟨3, 2⟩ true) (Or.inl rfl) rfl
    exact absurd this (by decide)

theorem ExecutorGateWitness : Properties.ExecutorGateWitness :=
  ⟨Reaches.direct _ _ 7 (by decide), by simp [InnerGate], Reaches.direct _ _ 7 (by decide),
    by simp [InnerGate], by decide, by decide⟩

end Contracts.ExecutionLiveness
