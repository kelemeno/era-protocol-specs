import EraSpec.Contracts.InteropCenter.Properties.Dispatch
import EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryLimits
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashEncoding

/-!
# Proofs: what a dispatch guarantees

One run invariant, `Inv`, carries (a) and (b): the salt flags are exactly the logged keys, every
logged bundle was formed by `_sendBundle`, every atomic one was validated, the keys are distinct,
and every leg that is not `Unset` is explained by an atomic logged dispatch. Each field is
conditional on the check it needs, so one induction (`inv_step`) serves the deployed code and the
three variants. A second invariant, `LegInv`, needs no check: appended legs stay out of `Unset`
and are pairwise distinct. (c) is then (a) plus the injectivity of the packed salt encoding
(`packed_addr_salt_inj`) and of `abi.encode(uint256, bytes)` in its second argument
(`abiEncode_right_inj`, new here: it needs no length bound, because the length word fixes the
length modulo `2^256` and the padded payload fixes it to within 32). The same lemma turns
`claimRefund`'s hash of arbitrary bytes into the logged bundle or a pinned keccak collision.
-/

namespace Contracts.InteropCenter

open AttackVectors.BundleHashEncoding
open Contracts.AtomicFlowManager (Manager LegState AppendGuard AuthorizeGuard ClaimGuard)

/-! ## Bytes -/

/-- Big-endian reading of a concatenation. -/
theorem fromBytesBE_append (l m : List UInt8) :
    fromBytesBE (l ++ m) = fromBytesBE l * 256 ^ m.length + fromBytesBE m := by
  have key : ∀ (acc : ℕ) (m : List UInt8),
      m.foldl (fun acc b => acc * 256 + b.toNat) acc
        = acc * 256 ^ m.length + m.foldl (fun acc b => acc * 256 + b.toNat) 0 := by
    intro acc m
    induction m generalizing acc with
    | nil => simp
    | cons x m ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih (acc * 256 + x.toNat), ih (0 * 256 + x.toNat)]
      ring
  simp only [fromBytesBE, List.foldl_append]
  exact key _ m

/-- `toBytesBE k` keeps the value modulo `256 ^ k`. -/
theorem fromBytesBE_toBytesBE_mod (k n : ℕ) : fromBytesBE (toBytesBE k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [toBytesBE, fromBytesBE, Nat.mod_one]
  | succ k ih =>
    rw [toBytesBE, fromBytesBE_append_singleton, ih, pow_succ, mul_comm (256 ^ k) 256, Nat.mod_mul]
    simp
    ring

theorem toBytesBE_eq_mod {k n m : ℕ} (h : toBytesBE k n = toBytesBE k m) :
    n % 256 ^ k = m % 256 ^ k := by
  have := congrArg fromBytesBE h
  rwa [fromBytesBE_toBytesBE_mod, fromBytesBE_toBytesBE_mod] at this

theorem size_eq : (256 : ℕ) ^ 32 = UInt256.size := by rfl

/-- **`abi.encode(uint256, bytes)` DETERMINES ITS BYTES ARGUMENT**, with no length bound: the
length word fixes the length modulo `2^256`, and the padded payload fixes it to within 32. -/
theorem abiEncode_right_inj {c c' : ℕ} {x y : List UInt8}
    (h : abiEncode c x = abiEncode c' y) : x = y := by
  -- peel off the chain id word, the offset word and the length word
  obtain ⟨-, h⟩ := List.append_inj h (by simp)
  obtain ⟨-, h⟩ := List.append_inj h (by simp)
  obtain ⟨hw, hp⟩ := List.append_inj h (by simp)
  have hmod := toBytesBE_eq_mod hw
  have hlen := congrArg List.length hp
  simp only [pad32, List.length_append, List.length_replicate, Nat.reducePow] at hmod hlen
  exact List.append_inj_left hp (by omega)

/-- **THE PACKED SALT PREIMAGE DETERMINES `(sender, salt)`** (`packed_addr_salt_inj`). -/
theorem saltPreimage_inj {a a' : Address} {s s' : Word}
    (h : saltPreimage a s = saltPreimage a' s') : a = a' ∧ s = s' := by
  have hs : (toBytesBE 32 s.val).length = 32 := length_toBytesBE 32 _
  have hs' : (toBytesBE 32 s'.val).length = 32 := length_toBytesBE 32 _
  obtain ⟨ha, hss⟩ := packed_addr_salt_inj a.isLt a'.isLt hs hs' h
  refine ⟨Fin.ext ha, Fin.ext ?_⟩
  have h1 := toBytesBE_eq_mod hss
  rwa [size_eq, Nat.mod_eq_of_lt s.isLt, Nat.mod_eq_of_lt s'.isLt] at h1

/-! ## The manager -/

@[simp] theorem legState_set (M : Manager) (f h f' h' : Word) (s : LegState) :
    (M.set f h s).legState f' h' = if f' = f ∧ h' = h then s else M.legState f' h' := rfl

@[simp] theorem legState_empty (f h : Word) :
    Contracts.AtomicFlowManager.empty.legState f h = .Unset := rfl

/-! ## The run invariant -/

/-- What every reachable state satisfies, each field under the check it needs. -/
structure Inv (K : Checks) (P : Params) (S : State) : Prop where
  salt : ∀ a s, S.saltUsed a s = true ↔ ∃ d ∈ S.log, d.sender = a ∧ d.salt = s
  formed : ∀ d ∈ S.log, FormedBy P d
  validated : K.atomicValueCheck = true → ∀ d ∈ S.log, d.isAtomic = true → Validated d.bundle
  keys : K.saltCheck = true → (S.log.map Dispatch.key).Nodup
  legs : K.onlyInteropCenter = true → ∀ f h, S.manager.legState f h ≠ .Unset →
    ∃ d ∈ S.log, d.isAtomic = true ∧ d.atomicSend.flowId = f ∧ bundleHash P d.bundle = h

theorem inv_init (K : Checks) (P : Params) : Inv K P init where
  salt := by intro a s; simp [init]
  formed := by simp [init]
  validated := by simp [init]
  keys := by simp [init]
  legs := by intro _ f h hne; exact absurd rfl hne

theorem mem_afterSend {P : Params} {S : State} {d d' : Dispatch} :
    d' ∈ (S.afterSend P d).log ↔ d' ∈ S.log ∨ d' = d := by
  simp [State.afterSend]

theorem afterSend_legState (P : Params) (S : State) (d : Dispatch) (f h : Word) :
    (S.afterSend P d).manager.legState f h =
      if d.isAtomic = true ∧ f = d.atomicSend.flowId ∧ h = bundleHash P d.bundle then .Committed
      else S.manager.legState f h := by
  unfold State.afterSend
  split <;> simp_all

theorem inv_step {K : Checks} {P : Params} {S S' : State} (hs : Step K P S S')
    (hI : Inv K P S) : Inv K P S' := by
  cases hs with
  | send d hsalt hform hval happ =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a s
      have := hI.salt a s
      simp only [State.afterSend, markSalt, List.mem_append, List.mem_singleton]
      grind
    · intro d' hd'
      rcases mem_afterSend.mp hd' with hd' | rfl
      · exact hI.formed d' hd'
      · exact hform
    · intro hK d' hd' hat
      rcases mem_afterSend.mp hd' with hd' | rfl
      · exact hI.validated hK d' hd' hat
      · exact hval hat hK
    · intro hK
      simp only [State.afterSend, List.map_append, List.map_singleton]
      refine (hI.keys hK).append (List.nodup_singleton _) fun x hx hx' => ?_
      obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hx
      simp only [List.mem_singleton, Dispatch.key, Prod.mk.injEq] at hx'
      have := (hI.salt d.sender d.salt).2 ⟨d', hd', hx'.1, hx'.2⟩
      simp [hsalt hK] at this
    · intro hK f h hne
      rw [afterSend_legState] at hne
      split_ifs at hne with hc
      · exact ⟨d, by simp [State.afterSend], hc.1, hc.2.1.symm, hc.2.2.symm⟩
      · obtain ⟨d', hd', h1, h2, h3⟩ := hI.legs hK f h hne
        exact ⟨d', by simp [State.afterSend, hd'], h1, h2, h3⟩
  | authorize f h hg | claim f h hg =>
    refine ⟨hI.salt, hI.formed, hI.validated, hI.keys, fun hK f' h' hne => hI.legs hK f' h' ?_⟩
    simp only [legState_set] at hne
    split_ifs at hne with hfh
    · obtain ⟨rfl, rfl⟩ := hfh
      rw [hg]; nofun
    · exact hne
  | foreignAppend caller f h hne hmod _ =>
    exact ⟨hI.salt, hI.formed, hI.validated, hI.keys, fun hK => absurd (hmod hK) hne⟩

theorem inv_reach {K : Checks} {P : Params} {S : State} (hr : Reach K P init S) : Inv K P S := by
  induction hr with
  | refl => exact inv_init K P
  | tail _ hs ih => exact inv_step hs ih

/-! ### The leg facts that need no check -/

/-- The leg an atomic dispatch commits. -/
def legKey (P : Params) (d : Dispatch) : Word × Word := (d.atomicSend.flowId, bundleHash P d.bundle)

/-- What every reachable state satisfies whichever checks are in place. -/
structure LegInv (P : Params) (S : State) : Prop where
  stay : ∀ d ∈ S.log, d.isAtomic = true →
    S.manager.legState d.atomicSend.flowId (bundleHash P d.bundle) ≠ .Unset
  once : ((S.log.filter Dispatch.isAtomic).map (legKey P)).Nodup

/-- No step writes `Unset`. -/
theorem step_keeps_set {K : Checks} {P : Params} {S S' : State} (hs : Step K P S S') (f h : Word)
    (hne : S.manager.legState f h ≠ .Unset) : S'.manager.legState f h ≠ .Unset := by
  cases hs <;> simp only [afterSend_legState, legState_set] <;> split_ifs <;>
    first | exact hne | exact LegState.noConfusion

theorem legInv_step {K : Checks} {P : Params} {S S' : State} (hs : Step K P S S')
    (hI : LegInv P S) : LegInv P S' := by
  have hstay : ∀ d ∈ S.log, d.isAtomic = true →
      S'.manager.legState d.atomicSend.flowId (bundleHash P d.bundle) ≠ .Unset :=
    fun d hd hat => step_keeps_set hs _ _ (hI.stay d hd hat)
  cases hs with
  | send d hsalt hform hval happ =>
    refine ⟨?_, ?_⟩
    · intro d' hd' hat
      rcases mem_afterSend.mp hd' with hd' | rfl
      · exact hstay d' hd' hat
      · rw [afterSend_legState, ite_eq_left ⟨hat, rfl, rfl⟩]
        exact LegState.noConfusion
    · show ((S.log ++ [d]).filter Dispatch.isAtomic |>.map (legKey P)).Nodup
      by_cases hat : d.isAtomic = true
      · simp only [List.filter_append, List.filter_singleton, hat, Bool.cond_true, List.map_append,
          List.map_singleton]
        refine hI.once.append (List.nodup_singleton _) fun x hx hx' => ?_
        obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hx
        obtain ⟨hd'log, hat'⟩ := List.mem_filter.mp hd'
        simp only [List.mem_singleton, legKey, Prod.mk.injEq] at hx'
        exact hI.stay d' hd'log hat' (by rw [hx'.1, hx'.2]; exact happ hat)
      · simpa [List.filter_append, hat] using hI.once
  | authorize | claim | foreignAppend => exact ⟨hstay, hI.once⟩

theorem legInv_reach {K : Checks} {P : Params} {S : State} (hr : Reach K P init S) :
    LegInv P S := by
  induction hr with
  | refl => exact ⟨by simp [init], by simp [init]⟩
  | tail _ hs ih => exact legInv_step hs ih

/-! ## (a) Sender salts -/

theorem SaltFlagRecordsDispatches : Properties.SaltFlagRecordsDispatches :=
  fun _ _ _ hr => (inv_reach hr).salt

theorem SaltFlagsNeverCleared : Properties.SaltFlagsNeverCleared := by
  intro K P S S' hs a s h
  cases hs with
  | send d _ _ _ _ => simp [State.afterSend, markSalt, h]
  | authorize | claim | foreignAppend => exact h

theorem UsedSaltHasNoDispatch : Properties.UsedSaltHasNoDispatch := by
  intro P S S' d hused hs hlog
  cases hs with
  | send d' hsalt _ _ _ =>
    obtain rfl : d' = d := by simpa [State.afterSend] using hlog
    simp [hsalt rfl] at hused
  | authorize | claim | foreignAppend => simp at hlog

theorem EachSaltDispatchesOnce : Properties.EachSaltDispatchesOnce :=
  fun _ _ hr => (inv_reach hr).keys rfl

/-! ## (b) The atomic-value check and the only `append` -/

theorem AtomicDispatchesCarryNoValue : Properties.AtomicDispatchesCarryNoValue :=
  fun _ _ hr => (inv_reach hr).validated rfl

theorem map_value_of_forall₂ {sender : Address} {cs : List CallStarter} {calls : List InteropCall}
    (h : List.Forall₂ (FormsCall sender) cs calls) :
    calls.map InteropCall.value = cs.map fun c => c.callAttributes.interopCallValue := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp [hab.value, ih]

theorem BurnedTotalIsCallValues : Properties.BurnedTotalIsCallValues := by
  intro K P S hr d hd
  unfold totalBurnedCallsValue
  rw [map_value_of_forall₂ ((inv_reach hr).formed d hd).calls]

theorem AtomicDispatchBurnsNothing : Properties.AtomicDispatchBurnsNothing := by
  intro P S hr d hd hat
  rw [BurnedTotalIsCallValues deployed P S hr d hd]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  exact (inv_reach hr).validated rfl d hd hat c hc

theorem OnlyADispatchCommitsALeg : Properties.OnlyADispatchCommitsALeg := by
  intro P S S' hs f h hU hne
  cases hs with
  | send d hsalt hform hval happ =>
    rw [afterSend_legState] at hne
    split_ifs at hne with hc
    · exact ⟨d, rfl, hc.1, hc.2.1.symm, hc.2.2.symm, hval hc.1 rfl⟩
    · exact absurd hU hne
  | authorize f' h' hg | claim f' h' hg =>
    simp only [legState_set] at hne
    split_ifs at hne with hfh
    · obtain ⟨rfl, rfl⟩ := hfh
      exact LegState.noConfusion (hU.symm.trans hg)
    · exact absurd hU hne
  | foreignAppend caller f' h' hne' hmod _ => exact absurd (hmod rfl) hne'

theorem AppendedLegsStayCommitted : Properties.AppendedLegsStayCommitted :=
  fun _ _ _ hr => (legInv_reach hr).stay

theorem EachLegAppendedOnce : Properties.EachLegAppendedOnce :=
  fun _ _ _ hr => (legInv_reach hr).once

theorem CommittedLegsAreValidatedDispatches : Properties.CommittedLegsAreValidatedDispatches := by
  intro P S hr f h hne
  have hI := inv_reach hr
  obtain ⟨d, hd, hat, hf, hh⟩ := hI.legs rfl f h hne
  exact ⟨d, hd, hat, hf, hh, hI.validated rfl d hd hat, (hI.formed d hd).source⟩

theorem SolePath : Properties.SolePath := by
  rintro P S hr b ⟨d, hd, hat, rfl⟩
  exact (inv_reach hr).validated rfl d hd hat

theorem ValidationUnbypassableDischarged : Properties.ValidationUnbypassableDischarged := by
  intro P S hr
  refine ⟨SolePath P S hr, fun b h => ?_⟩
  exact AttackVectors.RecoveryLimits.validation_unbypassable Validated (AppendedOn S)
    (SolePath P S hr) h

theorem PresentedBundleValidatedOrClash : Properties.PresentedBundleValidatedOrClash := by
  intro P S hr f b hne
  obtain ⟨d, hd, hat, hf, hh, hval, -⟩ := CommittedLegsAreValidatedDispatches P S hr f _ hne
  rcases eq_or_ne b d.bundle with rfl | hb
  · exact .inl hval
  · exact .inr ⟨d, hd, hat, hf, hb, hh.symm⟩

theorem ClaimedBundleValidatedOrCollision : Properties.ClaimedBundleValidatedOrCollision := by
  intro P dec S hr hdec f x hne
  obtain ⟨d, hd, hat, hf, hh, hval, -⟩ := CommittedLegsAreValidatedDispatches P S hr f _ hne
  by_cases hpre : claimPreimage dec x = bundlePreimage P d.bundle
  · left
    rw [abiEncode_right_inj hpre, hdec d hd]
    exact hval
  · exact .inr ⟨d, hd, hat, hf, hpre, hh.symm⟩

/-! ### Countermodels for (b) -/

/-- `_processCallStarter` for a direct starter: the call it forms. -/
theorem formsCall_direct (sender : Address) (v : ℕ) :
    FormsCall sender (wDirect v) ⟨5, sender, v, []⟩ :=
  ⟨rfl, fun h => (Bool.false_ne_true h).elim, fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- `_processCallStarter` for the indirect starter: `from` is the indirect sender. -/
theorem formsCall_indirect (sender : Address) :
    FormsCall sender wIndirect ⟨5, 9, 0, []⟩ :=
  ⟨rfl, fun _ => rfl, fun h => absurd h (by decide)⟩

/-- An atomic leg of flow `7` whose one call carries value `5`. -/
def valueLeg : Dispatch :=
  ⟨1, [wDirect 5], wBundle wParams 1 1 [⟨5, 1, 5, []⟩], ⟨7, 0, 100, true⟩⟩

theorem WithoutValueCheckValueLegCommits : Properties.WithoutValueCheckValueLegCommits := by
  refine ⟨wParams, init.afterSend wParams valueLeg, ?_, valueLeg, by simp [State.afterSend, init],
    rfl, ?_, ?_⟩
  · refine .tail .refl (Step.send valueLeg (fun _ => rfl) ?_ ?_ (fun _ => rfl))
    · exact ⟨rfl, rfl, List.Forall₂.cons (formsCall_direct 1 5) List.Forall₂.nil⟩
    · intro _ h; exact absurd h (by decide)
  · intro h
    exact absurd (h _ (List.mem_singleton_self _)) (by decide)
  · rw [afterSend_legState, ite_eq_left ⟨rfl, rfl, rfl⟩]

theorem WithoutOnlyInteropCenterUnbackedLegCommits :
    Properties.WithoutOnlyInteropCenterUnbackedLegCommits := by
  refine ⟨wParams, { init with manager := init.manager.set 7 42 .Committed }, 7, 42, ?_, rfl, ?_⟩
  · refine .tail .refl (Step.foreignAppend 1 7 42 (by decide) ?_ rfl)
    intro h; exact absurd h (by decide)
  · simp

/-- Under the constant keccak, an atomic leg of flow `7` with one zero-value call. -/
def collidingLeg : Dispatch :=
  ⟨1, [wDirect 0], wBundle collidingParams 1 1 [⟨5, 1, 0, []⟩], ⟨7, 0, 100, true⟩⟩

theorem CollisionLetsAValueBundleMatchACommittedLeg :
    Properties.CollisionLetsAValueBundleMatchACommittedLeg := by
  refine ⟨collidingParams, init.afterSend collidingParams collidingLeg, 7,
    wBundle collidingParams 1 1 [⟨5, 1, 5, []⟩], ?_, ?_, ?_⟩
  · refine .tail .refl (Step.send collidingLeg (fun _ => rfl) ?_ ?_ (fun _ => rfl))
    · exact ⟨rfl, rfl, List.Forall₂.cons (formsCall_direct 1 0) List.Forall₂.nil⟩
    · intro _ _ c hc
      simp only [collidingLeg, wBundle, List.mem_singleton] at hc
      subst hc; rfl
  · rw [afterSend_legState, ite_eq_left ⟨rfl, rfl, rfl⟩]
    exact LegState.noConfusion
  · intro h
    exact absurd (h _ (List.mem_singleton_self _)) (by decide)

/-! ## (c) Distinct dispatches -/

theorem DistinctDispatchesDistinctBundles : Properties.DistinctDispatchesDistinctBundles := by
  intro P S hr i j hi hj hij
  have hI := inv_reach hr
  have hkeys : (S.log.map Dispatch.key).Nodup := hI.keys rfl
  have hk : S.log[i].key ≠ S.log[j].key := fun heq =>
    hij ((hkeys.getElem_inj_iff (hi := by simpa) (hj := by simpa)).mp (by simpa using heq))
  rcases eq_or_ne S.log[i].bundle S.log[j].bundle with hb | hb
  · have hsalt : S.log[i].salt = S.log[j].salt := by simp [Dispatch.salt, hb]
    have hsender : S.log[i].sender ≠ S.log[j].sender := fun hs =>
      hk (by simp [Dispatch.key, hs, hsalt])
    refine .inr ⟨hsalt, hsender, fun hpre => hsender (saltPreimage_inj hpre).1, ?_⟩
    rw [← (hI.formed _ (List.getElem_mem hi)).salt, ← (hI.formed _ (List.getElem_mem hj)).salt,
      hb]
  · exact .inl hb

theorem DistinctDispatchesDistinctPreimages : Properties.DistinctDispatchesDistinctPreimages := by
  intro P S hr henc i j hi hj hij
  refine (DistinctDispatchesDistinctBundles P S hr i j hi hj hij).imp_left fun hb hpre => hb ?_
  exact henc _ (List.mem_map_of_mem (List.getElem_mem hi)) _
    (List.mem_map_of_mem (List.getElem_mem hj)) (abiEncode_right_inj hpre)

theorem DistinctDispatchesDistinctBundleHashes :
    Properties.DistinctDispatchesDistinctBundleHashes := by
  intro P S hr henc i j hi hj hij
  rcases DistinctDispatchesDistinctPreimages P S hr henc i j hi hj hij with hp | hc
  · exact (em' _).imp_right fun hh => .inr ⟨hp, hh⟩
  · exact .inr (.inl hc)

theorem LoggedRunBundleHashesUnique : Properties.LoggedRunBundleHashesUnique := by
  intro P S hr henc hsaltInj hbundleInj
  rw [List.nodup_iff_injective_get]
  rintro ⟨i, hi⟩ ⟨j, hj⟩ heq
  simp only [List.get_eq_getElem, List.getElem_map] at heq
  simp only [List.length_map] at hi hj
  by_contra hne
  have hij : i ≠ j := fun h => hne (Fin.ext h)
  rcases DistinctDispatchesDistinctBundleHashes P S hr henc i j hi hj hij with
    h | ⟨-, -, hs1, hs2⟩ | ⟨hb1, hb2⟩
  · exact h heq
  · exact hs1 (hsaltInj _ (List.mem_map_of_mem (List.getElem_mem hi)) _
      (List.mem_map_of_mem (List.getElem_mem hj)) hs2)
  · exact hb1 (hbundleInj _ (List.mem_map_of_mem (List.getElem_mem hi)) _
      (List.mem_map_of_mem (List.getElem_mem hj)) hb2)

theorem AtomicBytesNeverPublished : Properties.AtomicBytesNeverPublished := by
  intro P S hr henc d hd hat d' hd' hat'
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd'
  have hij : i ≠ j := by
    rintro rfl
    simp [hat] at hat'
  refine (DistinctDispatchesDistinctBundles P S hr i j hi hj hij).imp_left fun hb he => hb ?_
  exact henc _ (List.mem_map_of_mem (List.getElem_mem hi)) _
    (List.mem_map_of_mem (List.getElem_mem hj)) he

/-! ## Non-vacuity -/

theorem EncInjOnSatisfiable : Properties.EncInjOnSatisfiable := by
  intro L
  refine ⟨fun b => List.replicate (L.idxOf b) 0, ?_⟩
  intro b hb b' _ h
  have := congrArg List.length h
  simp only [List.length_replicate] at this
  exact (List.idxOf_inj hb).mp this

theorem KeccakInjOnSatisfiable : Properties.KeccakInjOnSatisfiable := by
  intro L hL
  refine ⟨fun x => Fin.ofNat _ (L.idxOf x), ?_⟩
  intro x hx y hy h
  have hxl : L.idxOf x < UInt256.size := lt_of_lt_of_le (List.idxOf_lt_length_iff.mpr hx) hL
  have hyl : L.idxOf y < UInt256.size := lt_of_lt_of_le (List.idxOf_lt_length_iff.mpr hy) hL
  have hv := congrArg Fin.val h
  simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hxl, Nat.mod_eq_of_lt hyl] at hv
  exact (List.idxOf_inj hx).mp hv

/-- The toy keccak reads the last word. -/
theorem lastWord_append_word (l : List UInt8) (n : ℕ) :
    lastWord (l ++ toBytesBE 32 n) = Fin.ofNat _ n := by
  apply Fin.ext
  simp only [lastWord, Fin.val_ofNat, fromBytesBE_append, length_toBytesBE,
    fromBytesBE_toBytesBE_mod, size_eq]
  rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]

theorem ofNat_val (s : Word) : (Fin.ofNat UInt256.size s.val : Word) = s :=
  Fin.ext (Nat.mod_eq_of_lt s.isLt)

theorem lastWord_saltPreimage (a : Address) (s : Word) : lastWord (saltPreimage a s) = s := by
  rw [saltPreimage, lastWord_append_word, ofNat_val]

/-- On the honest witness chain, a bundle's hash is its user salt. -/
theorem bundleHash_wParams (b : Bundle) : bundleHash wParams b = b.bundleAttributes.salt := by
  have hpad : pad32 (saltWordsEncoder b) = saltWordsEncoder b := by
    simp [pad32, saltWordsEncoder, length_toBytesBE]
  have hpre : bundlePreimage wParams b =
      (word wParams.chainId.val ++ (word 0x40 ++ (word (saltWordsEncoder b).length ++
        toBytesBE 32 b.interopBundleSalt.val))) ++ toBytesBE 32 b.bundleAttributes.salt.val := by
    show abiEncode wParams.chainId.val (saltWordsEncoder b) = _
    rw [abiEncode, hpad]
    simp only [saltWordsEncoder, List.append_assoc]
  show lastWord (bundlePreimage wParams b) = _
  rw [hpre, lastWord_append_word, ofNat_val]

/-- A two-element list whose images differ. -/
theorem keccakInjOn_pair {k : List UInt8 → Word} {x y : List UInt8} (h : k x ≠ k y) :
    KeccakInjOn k [x, y] := by
  intro u hu v hv huv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
  grind

theorem encInjOn_pair {enc : Bundle → List UInt8} {b b' : Bundle} (h : enc b ≠ enc b') :
    EncInjOn enc [b, b'] := by
  intro u hu v hv huv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
  grind

theorem wD1_formed : FormedBy wParams wD1 :=
  ⟨rfl, rfl, List.Forall₂.cons (formsCall_direct 1 0) List.Forall₂.nil⟩

theorem wD2_formed : FormedBy wParams wD2 :=
  ⟨rfl, rfl, List.Forall₂.cons (formsCall_direct 2 9) List.Forall₂.nil⟩

/-- Without the salt check: `wD2` dispatched twice. -/
def twiceState : State := (init.afterSend wParams wD2).afterSend wParams wD2

theorem twiceState_log : twiceState.log = [wD2, wD2] := rfl

theorem WithoutSaltCheckABundleRepeats : Properties.WithoutSaltCheckABundleRepeats := by
  have s : ∀ S : State, Step withoutSaltCheck wParams S (S.afterSend wParams wD2) := fun _ =>
    Step.send wD2 (fun h => absurd h (by decide)) wD2_formed
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
  exact ⟨wParams, twiceState, .tail (.tail .refl (s init)) (s _), 0, 1,
    by rw [twiceState_log]; decide, by rw [twiceState_log]; decide, by decide, rfl, rfl⟩

theorem wStep1 : Step deployed wParams init wS1 := by
  refine Step.send wD1 (fun _ => rfl) wD1_formed ?_ (fun _ => rfl)
  intro _ _ c hc
  simp only [wD1, wBundle, List.mem_singleton] at hc
  subst hc; rfl

theorem wStep2 : Step deployed wParams wS1 wS2 := by
  refine Step.send wD2 (fun _ => ?_) wD2_formed (fun h => absurd h (by decide))
    (fun h => absurd h (by decide))
  simp [wS1, State.afterSend, markSalt, init, wD1, wD2, Dispatch.salt, wBundle, wAttrs]

theorem wS1_leg : wS1.manager.legState 7 (bundleHash wParams wD1.bundle) = .Committed := by
  rw [wS1, afterSend_legState, ite_eq_left ⟨rfl, rfl, rfl⟩]

theorem wStep3 : Step deployed wParams wS2 wS3 := by
  refine Step.authorize 7 (bundleHash wParams wD1.bundle) ?_
  show wS2.manager.legState 7 (bundleHash wParams wD1.bundle) = .Committed
  rw [wS2, afterSend_legState, ite_eq_right (by simp [wD2]), wS1_leg]

theorem wReach : Reach deployed wParams init wS3 :=
  .tail (.tail (.tail .refl wStep1) wStep2) wStep3

theorem StepWitness : Properties.StepWitness := by
  refine ⟨wStep2, ?_, wStep1, rfl, ?_,
    ⟨wD1, by simp [wS3, wS2, wS1, State.afterSend, init], rfl, rfl⟩⟩
  · simp [wS1, State.afterSend, markSalt, Dispatch.salt]
  · show wS1.manager.legState 7 (bundleHash wParams wD1.bundle) ≠ .Unset
    rw [wS1_leg]; exact LegState.noConfusion

theorem wHash1 : bundleHash wParams wD1.bundle = 1 := bundleHash_wParams _
theorem wHash2 : bundleHash wParams wD2.bundle = 2 := bundleHash_wParams _

/-- The honest encoder separates the two bundles of the honest run (their user salts differ). -/
theorem wEnc_ne : wParams.enc wD1.bundle ≠ wParams.enc wD2.bundle := by
  intro he
  have := congrArg (List.drop 32) he
  simp only [wParams, saltWordsEncoder, List.drop_left' (length_toBytesBE 32 _)] at this
  have hm := toBytesBE_eq_mod this
  simp [wD1, wD2, wBundle, wAttrs] at hm

theorem DispatchWitness : Properties.DispatchWitness := by
  have hlog : wS3.log = [wD1, wD2] := rfl
  have hsalt1 : wParams.keccak (saltPreimage wD1.sender wD1.salt) = 1 :=
    lastWord_saltPreimage _ _
  have hsalt2 : wParams.keccak (saltPreimage wD2.sender wD2.salt) = 2 :=
    lastWord_saltPreimage _ _
  have h12 : (1 : Word) ≠ 2 := by decide
  refine ⟨wReach, hlog, ?_, ?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · rw [hlog]
    exact encInjOn_pair wEnc_ne
  · rw [hlog]
    exact keccakInjOn_pair (by rw [hsalt1, hsalt2]; exact h12)
  · rw [hlog]
    refine keccakInjOn_pair ?_
    change bundleHash wParams wD1.bundle ≠ bundleHash wParams wD2.bundle
    rw [wHash1, wHash2]; exact h12
  · show (wS2.manager.set 7 (bundleHash wParams wD1.bundle) .Revertable).legState 7
      (bundleHash wParams wD1.bundle) = .Revertable
    simp
  · intro h
    exact absurd (h _ (List.mem_singleton_self _)) (by decide)
  · rw [wHash1, wHash2]; exact h12
  · rintro ⟨-, hk⟩
    rw [hsalt1, hsalt2] at hk
    exact h12 hk
  · rintro ⟨-, hk⟩
    rw [wHash1, wHash2] at hk
    exact h12 hk

theorem wDec_wD1 : wDec (wParams.enc wD1.bundle) = wD1.bundle := by
  have hne : saltWordsEncoder wD1.bundle ≠ saltWordsEncoder wD2.bundle := wEnc_ne
  show (if saltWordsEncoder wD1.bundle = saltWordsEncoder wD2.bundle then wD2.bundle
    else wD1.bundle) = wD1.bundle
  rw [ite_eq_right hne]

theorem wDec_wD2 : wDec (wParams.enc wD2.bundle) = wD2.bundle := by
  show (if saltWordsEncoder wD2.bundle = saltWordsEncoder wD2.bundle then wD2.bundle
    else wD1.bundle) = wD2.bundle
  rw [ite_eq_left rfl]

theorem wClaimPreimage :
    claimPreimage wDec (wParams.enc wD1.bundle) = bundlePreimage wParams wD1.bundle := by
  unfold claimPreimage
  rw [wDec_wD1]
  rfl

theorem ClaimWitness : Properties.ClaimWitness := by
  refine ⟨?_, ?_, wClaimPreimage⟩
  · intro d hd
    have hlog : wS3.log = [wD1, wD2] := rfl
    rw [hlog] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    exacts [wDec_wD1, wDec_wD2]
  · rw [wClaimPreimage]
    show (wS2.manager.set 7 (bundleHash wParams wD1.bundle) .Revertable).legState 7
      (bundleHash wParams wD1.bundle) = .Revertable
    simp

/-- Under the constant keccak, two senders with salt `3` and the same indirect call. -/
def sharedBundle : Bundle := ⟨324, 325, 1, 0, [⟨5, 9, 0, []⟩], wAttrs 3⟩

def sharer1 : Dispatch := ⟨1, [wIndirect], sharedBundle, ⟨0, 0, 0, false⟩⟩
def sharer2 : Dispatch := ⟨2, [wIndirect], sharedBundle, ⟨0, 0, 0, false⟩⟩

/-- Both senders have dispatched. -/
def sharedState : State :=
  (init.afterSend collidingParams sharer1).afterSend collidingParams sharer2

theorem sharedState_log : sharedState.log = [sharer1, sharer2] := rfl

theorem collidingParams_keccak (x : List UInt8) : collidingParams.keccak x = 0 := rfl

theorem SaltClashLetsTwoSendersShareABundle :
    Properties.SaltClashLetsTwoSendersShareABundle := by
  have s1 : Step deployed collidingParams init (init.afterSend collidingParams sharer1) :=
    Step.send sharer1 (fun _ => rfl)
      ⟨rfl, rfl, List.Forall₂.cons (formsCall_indirect 1) List.Forall₂.nil⟩
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
  have s2 : Step deployed collidingParams (init.afterSend collidingParams sharer1) sharedState :=
    Step.send sharer2 (fun _ => by decide)
      ⟨rfl, rfl, List.Forall₂.cons (formsCall_indirect 2) List.Forall₂.nil⟩
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
  refine ⟨collidingParams, sharedState, .tail (.tail .refl s1) s2, 0, 1,
    by rw [sharedState_log]; decide, by rw [sharedState_log]; decide, by decide, rfl, rfl, ?_, ?_,
    (collidingParams_keccak _).trans (collidingParams_keccak _).symm⟩
  · show (1 : Address) ≠ 2
    decide
  · exact fun hpre => absurd (saltPreimage_inj hpre).1 (by decide)

end Contracts.InteropCenter
