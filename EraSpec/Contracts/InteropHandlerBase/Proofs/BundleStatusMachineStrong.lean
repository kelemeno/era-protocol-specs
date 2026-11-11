import EraSpec.Contracts.InteropHandlerBase.Properties.BundleStatusMachineStrong
import EraSpec.Contracts.InteropHandlerBase.Proofs.Reentrancy
import EraSpec.Contracts.InteropHandlerBase.Proofs.BundleStatusMachine
import EraSpec.Contracts.InteropCenter.Proofs.Dispatch
import Mathlib.Tactic

/-!
# Proofs: the bundle status machine, derived from the handler's guards

(a) and (b) read the deployed writes and guards directly, and use the `Good` invariant of topic
`Reentrancy` (`submitAll_good`) for the status of a bundle along a run: it moves along `Reach`,
which never returns to `Unreceived`.

(c) is one more induction over `exec`, like `exec_good`: if no call in a frame presents a valid
proof for hash `h`, the frame keeps `h` inside `AtomicPart` (`Unreceived` or `FullyExecuted`).
Every write of `Verified` for `h` needs such a proof (`verifyBundle`, and `executeBundle` of an
`Unreceived` bundle through `_verifyBundle`), and `unbundleBundle` admits only `Verified` and
`Unbundled`. With `Good.reach` this is `AtomicReach`. The cross-contract form reduces a valid
proof for an atomic leg's hash to a published message with the same hash: either a keccak
collision on the two named preimages, or the same preimage — hence the same bytes from the same
chain, which `PublishesOnlyPublicDispatches` makes a public dispatch and
`InteropCenter.AtomicBytesNeverPublished` excludes but for the cross-sender salt clash.
-/

namespace Contracts.InteropHandler

open AttackVectors.BundleStatusMachine
open AttackVectors.BundleHashEncoding (HashCollision abiEncode length_toBytesBE)

/-! ## (a) The whole-bundle write -/

theorem WholeBundleWriteIgnoresCallStatus : Properties.WholeBundleWriteIgnoresCallStatus := by
  refine ⟨fun b s i hi => by simp [hi], fun b s h i hn => ?_, fun b s i hi hx => ?_,
    fun b s s' hb hc => ?_⟩
  · simp only [beforeCalls_deployed, executeAll_call, setBundle_call]
    rw [ite_eq_right_iff]
    intro hx
    exact absurd hx hn
  · rw [hx]
    simp only [beforeCalls_deployed, executeAll_call, and_self, hi, ↓reduceIte]
    intro hs; cases hs
  · obtain ⟨sb, sc⟩ := s
    obtain ⟨sb', sc'⟩ := s'
    simp only at hb
    subst hb
    simp only [beforeCalls_deployed, State.executeAll, State.setBundle, State.mk.injEq, true_and]
    funext h' i
    split_ifs with hx
    · rfl
    · exact hc h' i hx

/-- A call loop whose targets all return, from a state where the loop's bundle is anything. -/
lemma exec_whole_returns_log {s : State} {b : Bundle} (ok : Bool)
    (hG : s.bundle b.hash = .Verified ∨ (s.bundle b.hash = .Unreceived ∧ ok = true)) :
    (submit .deployed s ⟨b.calls + 2, .executeBundle b ok, List.replicate b.calls .returns⟩).2 =
      (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash] := by
  simp only [submit]
  show (commit s (exec .deployed (b.calls + 1 + 1) _ s)).2 = _
  simp only [exec, hG, ↓reduceIte]
  rw [exec_calls_returns .deployed b.hash _ _ _ _ (fun c hc => (List.mem_replicate.1 hc).2)
    (by simp)]
  rfl

theorem CallStatusDoesNotStopWholeBundleRedelivery :
    Properties.CallStatusDoesNotStopWholeBundleRedelivery := by
  intro s b ok hpos _
  have h0 : Effect.delivered b.hash 0 ∈
      (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash] :=
    List.mem_append_left _ (List.mem_map.2 ⟨0, List.mem_range.2 hpos, rfl⟩)
  refine ⟨fun hv => ?_, fun hu => ?_⟩
  · rw [exec_whole_returns_log ok (Or.inl hv)]
    exact h0
  · simp only [submit]
    rw [exec_atomic_returns hu]
    exact h0

theorem AdmittedBundleHasOnlyUnprocessedCalls :
    Properties.AdmittedBundleHasOnlyUnprocessedCalls := by
  refine ⟨NestedExecutionFollowsTheStatusMachine.1, fun s txs hc b hadm i => ?_⟩
  obtain ⟨hc', -, -⟩ := NestedExecutionFollowsTheStatusMachine.2 s txs hc
  have hu : (submitAll .deployed s txs).1.call b.hash i = .Unprocessed := by
    by_contra hne
    rcases hc' b.hash i hne with h1 | h1 <;> rcases hadm with h2 | h2 <;> rw [h1] at h2 <;>
      exact absurd h2 (by decide)
  refine ⟨hu, fun hi => ?_⟩
  rw [hu]
  simp only [beforeCalls_deployed, executeAll_call, and_self, hi, ↓reduceIte]
  exact CallStep.execute

/-! ## (b) A verified bundle is never executed atomically -/

lemma not_reach_verified_unreceived : ¬ Reach .Verified .Unreceived := by
  have key : ∀ a b, Reach a b → b = .Unreceived → a = .Unreceived := by
    intro a b h
    induction h with
    | refl => exact id
    | tail _ st _ => intro hb; subst hb; cases st
  intro h
  exact absurd (key _ _ h rfl) (by decide)

theorem VerifiedBundleNeverExecutesAtomically :
    Properties.VerifiedBundleNeverExecutesAtomically := by
  refine ⟨not_reach_verified_unreceived, fun s txs b hv n ok cs => ?_,
    fun s b ok hv => exec_whole_returns_log ok (Or.inl hv)⟩
  have hR := (submitAll_good s txs).reach b.hash
  rw [hv] at hR
  have hne : (submitAll .deployed s txs).1.bundle b.hash ≠ .Unreceived := by
    intro e
    rw [e] at hR
    exact not_reach_verified_unreceived hR
  cases n with
  | zero => simp [exec]
  | succ n => simp [exec, hne]

/-! ## (c) The atomic sub-machine -/

theorem AtomicMachineIsDeployedMachineWithoutVerify :
    Properties.AtomicMachineIsDeployedMachineWithoutVerify := by
  refine ⟨fun a b h => by cases h; exact Step.executeAtomic, fun t => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h2 := atomic_reach_two_states h
    unfold Properties.atomic_reach_two_states at h2
    refine ⟨?_, ?_, ?_⟩
    · rcases h2 with rfl | rfl
      · exact .refl _
      · exact .tail (.refl _) Step.executeAtomic
    · rcases h2 with rfl | rfl <;> decide
    · rcases h2 with rfl | rfl <;> decide
  · obtain ⟨-, hv, hu⟩ := h
    cases t with
    | Unreceived => exact .refl _
    | FullyExecuted => exact .tail (.refl _) AtomicStep.executeAtomic
    | Verified => exact absurd rfl hv
    | Unbundled => exact absurd rfl hu

/-- The states of the atomic sub-machine. -/
def AtomicPart (st : Status) : Prop := st = .Unreceived ∨ st = .FullyExecuted

lemma mentions_headD {cs : List Callee} {e : Entry} (h : (cs.headD .returns).Mentions e) :
    ∃ c ∈ cs, c.Mentions e := by
  cases cs with
  | nil => cases h
  | cons c cs => exact ⟨c, List.mem_cons_self, h⟩

lemma mentions_tail {cs : List Callee} {e : Entry} (h : ∃ c ∈ cs.tail, c.Mentions e) :
    ∃ c ∈ cs, c.Mentions e := by
  obtain ⟨c, hc, hm⟩ := h
  exact ⟨c, List.mem_of_mem_tail hc, hm⟩

lemma verifyIfUnreceived_bundle_ne {s : State} {h h' : BundleHash} (hne : h' ≠ h) :
    (s.verifyIfUnreceived h).bundle h' = s.bundle h' := by
  unfold State.verifyIfUnreceived
  split_ifs <;> simp [hne]

lemma beforeCalls_bundle_ne {b : Bundle} {s : State} {h : BundleHash} (hne : h ≠ b.hash) :
    (beforeCalls .deployed b s).bundle h = s.bundle h := by
  simp [hne]

/-- **The invariant.** A committed frame in which no call presents a valid proof for `h` keeps
`h` inside the atomic sub-machine. -/
theorem exec_atomicPart (h : BundleHash) : ∀ (n : ℕ) (f : Frame) (s s' : State)
    (l : List Effect), exec .deployed n f s = some (s', l) →
    (∀ e, f.Mentions e → e.NoProofFor h) → AtomicPart (s.bundle h) →
    AtomicPart (s'.bundle h) := by
  intro n
  induction n with
  | zero => intro f s s' l hx; simp [exec] at hx
  | succ n ih =>
    intro f s s' l hx hnp hs
    match f with
    | .entry (.executeBundle b ok) cs =>
      simp only [exec] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₂ l₂ heq
        simp only [afterCalls_deployed, Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        by_cases hb : b.hash = h
        · exfalso
          have hok : ok = false := hnp (.executeBundle b ok) (Or.inl rfl) hb
          subst hb
          rcases hG with hv | ⟨hu, hok'⟩
          · rcases hs with h1 | h1 <;> rw [h1] at hv <;> exact absurd hv (by decide)
          · rw [hok] at hok'; exact absurd hok' (by decide)
        · have hs₀ : (beforeCalls .deployed b (s.verifyIfUnreceived b.hash)).bundle h =
              s.bundle h := by
            rw [beforeCalls_bundle_ne (Ne.symm hb), verifyIfUnreceived_bundle_ne (Ne.symm hb)]
          exact ih _ _ _ _ heq (fun e he => hnp e (Or.inr he)) (hs₀ ▸ hs)
      · simp at hx
    | .entry (.executeAtomicBundle b ok) cs =>
      simp only [exec] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₂ l₂ heq
        simp only [afterCalls_deployed, Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        have hs₀ : AtomicPart ((beforeCalls .deployed b s).bundle h) := by
          by_cases hb : h = b.hash
          · subst hb; right; simp
          · rw [beforeCalls_bundle_ne hb]; exact hs
        exact ih _ _ _ _ heq (fun e he => hnp e (Or.inr he)) hs₀
      · simp at hx
    | .entry (.verifyBundle b ok) cs =>
      simp only [exec] at hx
      split_ifs at hx with hG
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      by_cases hb : b.hash = h
      · exfalso
        have hok : ok = false := hnp (.verifyBundle b ok) (Or.inl rfl) hb
        rw [hok] at hG
        exact absurd hG.2 (by decide)
      · simpa [Ne.symm hb] using hs
    | .entry (.unbundleBundle b req) cs =>
      simp only [exec, writesCallsFirst_deployed] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₁ hm
        split at hx
        · rename_i s₂ l₂ heq
          simp only [afterUnbundle_deployed, Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          by_cases hb : b.hash = h
          · exfalso
            subst hb
            rcases hG.2 with h1 | h1 <;> rcases hs with h2 | h2 <;> rw [h1] at h2 <;>
              exact absurd h2 (by decide)
          · obtain ⟨hbs, -, -, -⟩ := markCalls_spec req 0 _ s₁ hm
            have hs₁ : s₁.bundle h = s.bundle h := by
              rw [hbs]; simp [Ne.symm hb]
            exact ih _ _ _ _ heq (fun e he => hnp e (Or.inr he)) (hs₁ ▸ hs)
        · simp at hx
      · simp at hx
    | .calls hb [] cs =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact hs
    | .calls hb (i :: is) cs =>
      simp only [exec] at hx
      split at hx
      · rename_i s₁ l₁ heq₁
        split at hx
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          have h₁ := ih _ _ _ _ heq₁ (fun e he => hnp e (mentions_headD he)) hs
          exact ih _ _ _ _ heq₂ (fun e he => hnp e (mentions_tail he)) h₁
        · simp at hx
      · simp at hx
    | .target .returns =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact hs
    | .target .reverts => simp [exec] at hx
    | .target (.calls e inner caught next) =>
      simp only [exec] at hx
      split at hx
      · rename_i s₁ l₁ heq₁
        split at hx
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          have h₁ := ih _ _ _ _ heq₁ (fun e' he' => hnp e' (by
            rcases he' with rfl | ⟨c, hc, hm⟩
            · exact Callee.Mentions.here
            · exact Callee.Mentions.nested hc hm)) hs
          exact ih _ _ _ _ heq₂ (fun e' he' => hnp e' (Callee.Mentions.cont he')) h₁
        · simp at hx
      · split_ifs at hx
        exact ih _ _ _ _ hx (fun e' he' => hnp e' (Callee.Mentions.cont he')) hs

lemma submitAll_atomicPart (h : BundleHash) : ∀ (s : State) (txs : List Tx),
    NoProofRun h txs → AtomicPart (s.bundle h) →
    AtomicPart ((submitAll .deployed s txs).1.bundle h)
  | s, [], _, hs => hs
  | s, t :: ts, hnp, hs => by
      have h₁ : AtomicPart ((submit .deployed s t).1.bundle h) := by
        unfold submit
        cases hx : exec .deployed t.fuel (.entry t.entry t.callees) s with
        | none => exact hs
        | some r =>
          obtain ⟨s', l⟩ := r
          exact exec_atomicPart h _ _ _ _ _ hx (hnp t List.mem_cons_self) hs
      exact submitAll_atomicPart h _ ts (fun t' ht' => hnp t' (List.mem_cons_of_mem _ ht')) h₁

theorem NoProofKeepsBundleInAtomicMachine : Properties.NoProofKeepsBundleInAtomicMachine := by
  intro s txs h hs hnp
  have hp := submitAll_atomicPart h s txs hnp hs
  have hr := (submitAll_good s txs).reach h
  rcases hs with h0 | h0 <;> rw [h0] at hr ⊢ <;> rcases hp with h1 | h1 <;> rw [h1] at hr ⊢
  · exact .refl _
  · exact .tail (.refl _) .executeAtomic
  · have := reach_from_fullyExecuted hr
    unfold Properties.reach_from_fullyExecuted at this
    exact absurd this (by decide)
  · exact .refl _

/-- Mentions of a transaction that calls one entry point and delivers to no target. -/
lemma tx_mentions_nil {t : Tx} (hc : t.callees = []) {e : Entry} (h : t.Mentions e) :
    e = t.entry := by
  unfold Tx.Mentions Frame.Mentions at h
  rw [hc] at h
  rcases h with h | ⟨c, hc', _⟩
  · exact h
  · simp at hc'

/-- The calls `wReenterAtomic true` makes: its own entry point, and the re-entry. -/
lemma reenterAtomic_mentions {e : Entry} (h : (wReenterAtomic true).Mentions e) :
    e = .executeAtomicBundle wC true := by
  unfold Tx.Mentions Frame.Mentions at h
  rcases h with h | ⟨c, hc, hm⟩
  · exact h
  · simp only [wReenterAtomic, List.mem_singleton] at hc
    subst hc
    cases hm with
    | here => rfl
    | nested hc _ => simp at hc
    | cont hm => cases hm

theorem ProofForAtomicHashOpensUnbundledRoute :
    Properties.ProofForAtomicHashOpensUnbundledRoute := by
  refine ⟨?_, ?_, by decide, ?_, by decide, by decide, by decide⟩
  · intro t ht e he
    simp only [List.mem_singleton] at ht
    subst ht
    rw [tx_mentions_nil rfl he]
    trivial
  · intro t ht e he
    simp only [List.mem_singleton] at ht
    subst ht
    rw [reenterAtomic_mentions he]
    trivial
  · intro hnp
    have := hnp wVerifyC List.mem_cons_self (.verifyBundle wC true) (Or.inl rfl) rfl
    exact absurd this (by decide)

/-! ### The source side -/

/-- `abi.encode(uint256, bytes)` determines its chain-id word, for `uint256` values. -/
lemma abiEncode_chain_eq {c c' : UInt256} {x y : List UInt8}
    (h : abiEncode c.val x = abiEncode c'.val y) : c = c' := by
  have h32 := congrArg (List.take 32) h
  simp only [abiEncode] at h32
  rw [List.take_left' (length_toBytesBE 32 _), List.take_left' (length_toBytesBE 32 _)] at h32
  have hm := Contracts.InteropCenter.toBytesBE_eq_mod h32
  rw [Contracts.InteropCenter.size_eq, Nat.mod_eq_of_lt c.isLt, Nat.mod_eq_of_lt c'.isLt] at hm
  exact Fin.ext hm

/-- A valid proof for an atomic leg's bundle hash lands in one of the two named clashes. -/
lemma published_atomic_hash_clashes {P : Contracts.InteropCenter.Params}
    {S : Contracts.InteropCenter.State}
    (hreach : Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed P
      Contracts.InteropCenter.init S)
    (henc : Contracts.InteropCenter.EncInjOn P.enc
      (S.log.map Contracts.InteropCenter.Dispatch.bundle))
    {pubs : List (UInt256 × List UInt8)} (hpubs : PublishesOnlyPublicDispatches P S.log pubs)
    {d : Contracts.InteropCenter.Dispatch} (hd : d ∈ S.log) (hat : d.isAtomic = true)
    (hpub : PublishedHash P.keccak pubs (Contracts.InteropCenter.bundleHash P d.bundle)) :
    (∃ d' ∈ S.log, d'.isAtomic = false ∧ Contracts.InteropCenter.CrossSenderSaltClash P d d')
      ∨ (∃ p ∈ pubs, HashCollision P.keccak (Contracts.InteropCenter.bundlePreimage P d.bundle)
            (abiEncode p.1.val p.2)) := by
  obtain ⟨p, hp, hph⟩ := hpub
  by_cases hpre : Contracts.InteropCenter.bundlePreimage P d.bundle = abiEncode p.1.val p.2
  · left
    have hpre' : abiEncode P.chainId.val (P.enc d.bundle) = abiEncode p.1.val p.2 := hpre
    have hc : P.chainId = p.1 := abiEncode_chain_eq hpre'
    have hx : P.enc d.bundle = p.2 := Contracts.InteropCenter.abiEncode_right_inj hpre'
    obtain ⟨d', hd', hpub', hx'⟩ := hpubs p hp hc.symm
    rcases Contracts.InteropCenter.AtomicBytesNeverPublished P S hreach henc d hd hat d' hd'
        hpub' with hne | hclash
    · exact absurd (hx.trans hx') hne
    · exact ⟨d', hd', hpub', hclash⟩
  · exact Or.inr ⟨p, hp, hpre, hph⟩

theorem AtomicLegStaysAtomicAtDestinationOrClash :
    Properties.AtomicLegStaysAtomicAtDestinationOrClash := by
  intro P S hreach henc pubs hpubs d hd hat s txs hs hsound
  by_cases hclash :
      (∃ d' ∈ S.log, d'.isAtomic = false ∧ Contracts.InteropCenter.CrossSenderSaltClash P d d')
      ∨ (∃ p ∈ pubs, HashCollision P.keccak (Contracts.InteropCenter.bundlePreimage P d.bundle)
            (abiEncode p.1.val p.2))
  · exact Or.inr hclash
  · left
    have hnp : NoProofRun (Contracts.InteropCenter.bundleHash P d.bundle) txs := by
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
          exact hclash (published_atomic_hash_clashes hreach henc hpubs hd hat hpub)
      | verifyBundle b ok =>
        intro hbh
        cases ok with
        | false => rfl
        | true =>
          exfalso
          have hpub := hsnd rfl
          rw [hbh] at hpub
          exact hclash (published_atomic_hash_clashes hreach henc hpubs hd hat hpub)
      | unbundleBundle _ _ => trivial
      | executeAtomicBundle _ _ => trivial
    have h := NoProofKeepsBundleInAtomicMachine s txs _ (Or.inl hs) hnp
    rwa [hs] at h

theorem AtomicLegAtDestinationWitness : Properties.AtomicLegAtDestinationWitness := by
  have hlog : Contracts.InteropCenter.wS3.log =
      [Contracts.InteropCenter.wD1, Contracts.InteropCenter.wD2] := rfl
  have h12 : (1 : UInt256) ≠ 2 := by decide
  refine ⟨Contracts.InteropCenter.wReach, ?_, ?_, by rw [hlog]; simp, rfl, rfl, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [hlog]
    exact Contracts.InteropCenter.encInjOn_pair Contracts.InteropCenter.wEnc_ne
  · intro p hp _
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨Contracts.InteropCenter.wD2, by rw [hlog]; simp, rfl, rfl⟩
  · intro t ht e he
    simp only [wDestRun, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · rw [tx_mentions_nil rfl he]
      intro _
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      exact Contracts.InteropCenter.wHash2.symm
    · rw [tx_mentions_nil rfl he]
      trivial
  · intro hnp
    have := hnp _ List.mem_cons_self (.verifyBundle ⟨2, 1⟩ true) (Or.inl rfl)
      Contracts.InteropCenter.wHash2.symm
    exact absurd this (by decide)
  · rw [Contracts.InteropCenter.wHash1]; decide
  · rw [Contracts.InteropCenter.wHash2]; decide
  · rintro ⟨hsalt, -, -⟩
    exact absurd hsalt (by decide)
  · rintro ⟨-, hk⟩
    have hk' : Contracts.InteropCenter.bundleHash Contracts.InteropCenter.wParams
        Contracts.InteropCenter.wD1.bundle =
        Contracts.InteropCenter.bundleHash Contracts.InteropCenter.wParams
        Contracts.InteropCenter.wD2.bundle := hk
    rw [Contracts.InteropCenter.wHash1, Contracts.InteropCenter.wHash2] at hk'
    exact h12 hk'

theorem StatusMachineStrongWitness : Properties.StatusMachineStrongWitness := by
  refine ⟨rfl, rfl, ?_, by decide, by decide, by decide, by decide⟩
  intro hc
  rcases hc 3 0 (by decide) with h | h <;> exact absurd h (by decide)

end Contracts.InteropHandler
