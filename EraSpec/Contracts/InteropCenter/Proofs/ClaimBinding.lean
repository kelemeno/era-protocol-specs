import EraSpec.Contracts.InteropCenter.Properties.ClaimBinding
import EraSpec.Contracts.InteropCenter.Proofs.Dispatch

/-!
# Proofs: a claimed bundle is a dispatched bundle

The headline is O1's argument carried one step further. O1's run invariant (`inv_reach`, its `legs`
field, which needs only `onlyInteropCenter`; it is the fact behind
`CommittedLegsAreValidatedDispatches`) names the logged atomic dispatch `d` behind the leg the claim
reads. If the claim hashed the very bytes the center hashed for `d`, then `abiEncode_right_inj` (O1)
turns that equality of
`abi.encode(uint256, bytes)` preimages into `x = abi.encode(d.bundle)`, and the decoder round trip
gives `abi.decode(x) = d.bundle`. Otherwise the two preimages differ and hash equal: the pinned
collision. The corollaries add O1's run invariant (`inv_reach`: the dispatch was formed by
`_sendBundle` and validated) and its leg invariant (`legInv_reach`: each leg is appended once and
never returns to `Unset`). The two-claim result also needs three run facts proved here: runs
compose, the log only grows, and no step leaves `Reverted`.

The witnesses and countermodels are concrete runs on O1's two witness chains: the honest one
(`wParams`, whose toy keccak reads a bundle hash off the user salt) and the colliding one
(`collidingParams`, constant keccak). Their data lives in the `ClaimBinding` namespace.
-/

namespace Contracts.InteropCenter

open AttackVectors.BundleHashEncoding
open Contracts.AtomicFlowManager (Manager LegState AppendGuard AuthorizeGuard ClaimGuard)

namespace ClaimBinding

/-! ## Run facts -/

/-- Runs compose. -/
theorem reach_trans {K : Checks} {P : Params} {S T U : State} (h₁ : Reach K P S T)
    (h₂ : Reach K P T U) : Reach K P S U := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact .tail ih hs

/-- A step only appends to the ghost log. -/
theorem step_log_prefix {K : Checks} {P : Params} {S S' : State} (hs : Step K P S S') :
    S.log <+: S'.log := by
  cases hs with
  | send d _ _ _ _ => exact List.prefix_append _ _
  | authorize => exact List.prefix_refl _
  | claim => exact List.prefix_refl _
  | foreignAppend => exact List.prefix_refl _

/-- Along a run the log only grows. -/
theorem reach_log_prefix {K : Checks} {P : Params} {S T : State} (hr : Reach K P S T) :
    S.log <+: T.log := by
  induction hr with
  | refl => exact List.prefix_refl _
  | tail _ hs ih => exact ih.trans (step_log_prefix hs)

/-- No step, with or without the checks, moves a leg out of `Reverted`: every writer guards on a
different predecessor state (`Unset`, `Committed` or `Revertable`). -/
theorem step_keeps_reverted {K : Checks} {P : Params} {S S' : State} (hs : Step K P S S')
    (f h : Word) (hR : S.manager.legState f h = .Reverted) :
    S'.manager.legState f h = .Reverted := by
  cases hs with
  | send d _ _ _ happ =>
    rw [afterSend_legState]
    split_ifs with hc
    · obtain ⟨hat, rfl, rfl⟩ := hc
      have hU : S.manager.legState d.atomicSend.flowId (bundleHash P d.bundle) = .Unset :=
        happ hat
      rw [hR] at hU
      exact absurd hU (by decide)
    · exact hR
  | authorize f' h' hg =>
    simp only [legState_set]
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc
      have hC : S.manager.legState f h = .Committed := hg
      rw [hR] at hC
      exact absurd hC (by decide)
    · exact hR
  | claim f' h' _ =>
    -- `claimRefund` itself writes `Reverted`.
    simp only [legState_set]
    split_ifs
    · rfl
    · exact hR
  | foreignAppend _ f' h' _ _ hg =>
    simp only [legState_set]
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc
      have hU : S.manager.legState f h = .Unset := hg
      rw [hR] at hU
      exact absurd hU (by decide)
    · exact hR

/-- Along a run a `Reverted` leg stays `Reverted`. -/
theorem reach_keeps_reverted {K : Checks} {P : Params} {S T : State} (hr : Reach K P S T)
    (f h : Word) (hR : S.manager.legState f h = .Reverted) :
    T.manager.legState f h = .Reverted := by
  induction hr with
  | refl => exact hR
  | tail _ hs ih => exact step_keeps_reverted hs f h ih

/-! ## Lists and bytes -/

/-- If a function is injective on the elements of a list that satisfy `p` (its image of the
filtered list has no duplicates), two positions satisfying `p` with one image are one position. -/
theorem getElem_inj_of_nodup_map_filter {α β : Type*} {p : α → Bool} {g : α → β} {l : List α}
    (h : ((l.filter p).map g).Nodup) {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (hpi : p l[i] = true) (hpj : p l[j] = true) (hg : g l[i] = g l[j]) : i = j := by
  have hpw : l.Pairwise (fun a b => p a = true → p b = true → g a ≠ g b) := by
    have h' : List.Pairwise (· ≠ ·) ((l.filter p).map g) := h
    rw [List.pairwise_map, List.pairwise_filter] at h'
    exact h'
  rw [List.pairwise_iff_getElem] at hpw
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd hg (hpw i j hi hj hij hpi hpj)
  · rfl
  · exact absurd hg.symm (hpw j i hj hi hij hpj hpi)

/-- Adding a member of the list keeps keccak injective on it. -/
theorem keccakInjOn_cons_of_mem {k : List UInt8 → Word} {a : List UInt8}
    {L : List (List UInt8)} (ha : a ∈ L) (h : KeccakInjOn k L) : KeccakInjOn k (a :: L) := by
  intro u hu v hv huv
  have hu' : u ∈ L := by
    rcases List.mem_cons.mp hu with rfl | hu
    exacts [ha, hu]
  have hv' : v ∈ L := by
    rcases List.mem_cons.mp hv with rfl | hv
    exacts [ha, hv]
  exact h u hu' v hv' huv

/-- **THE CANONICAL BYTES OF A BUNDLE OF THIS CHAIN MAKE `claimRefund` HASH THE CENTER'S
PREIMAGE.** If `abi.decode(abi.encode(b)) = b` and `b.sourceChainId = block.chainid`, then
`abi.encode(b.sourceChainId, abi.encode(b))` is `abi.encode(block.chainid, abi.encode(b))`. -/
theorem claimPreimage_canonical {P : Params} {dec : List UInt8 → Bundle} {b : Bundle}
    (hdec : dec (P.enc b) = b) (hsrc : b.sourceChainId = P.chainId) :
    claimPreimage dec (P.enc b) = bundlePreimage P b := by
  unfold claimPreimage bundlePreimage
  rw [hdec, hsrc]

end ClaimBinding

open ClaimBinding

/-! ## The headline -/

theorem ClaimBindingIndependentOfSaltAndValueChecks :
    Properties.ClaimBindingIndependentOfSaltAndValueChecks := by
  intro K hK P dec S hr hdec f x hne
  obtain ⟨d, hd, hat, hf, hh⟩ := (inv_reach hr).legs hK f _ hne
  by_cases hpre : claimPreimage dec x = bundlePreimage P d.bundle
  · left
    have hx : x = P.enc d.bundle := abiEncode_right_inj hpre
    refine ⟨d, hd, hat, hf, hx, ?_⟩
    rw [hx]
    exact hdec d hd
  · right
    exact ⟨d, hd, hat, hf, hpre, hh.symm⟩

theorem ClaimedBundleIsDispatchedOrCollision : Properties.ClaimedBundleIsDispatchedOrCollision :=
  ClaimBindingIndependentOfSaltAndValueChecks deployed rfl

theorem ClaimedBundleIsDispatchedOn : Properties.ClaimedBundleIsDispatchedOn := by
  intro P dec S hr hdec f x hinj hne
  rcases ClaimedBundleIsDispatchedOrCollision P dec S hr hdec f x hne with
    h | ⟨d, hd, -, -, hpre, hh⟩
  · exact h
  · exact absurd (hinj (claimPreimage dec x) List.mem_cons_self (bundlePreimage P d.bundle)
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨d, hd, rfl⟩)) hh) hpre

theorem ClaimedBundleIsDispatchedImpliesValidated :
    Properties.ClaimedBundleIsDispatchedImpliesValidated := by
  intro P dec S hr f x h
  rcases h with ⟨d, hd, hat, -, -, hdx⟩ | ⟨d, hd, hat, hf, hpre, hh⟩
  · left
    rw [hdx]
    exact AtomicDispatchesCarryNoValue P S hr d hd hat
  · right
    exact ⟨d, hd, hat, hf, hpre, hh⟩

/-! ## Corollaries -/

theorem ClaimSourceChainIsThisChainOrCollision :
    Properties.ClaimSourceChainIsThisChainOrCollision := by
  intro P dec S hr hdec f x hne
  rcases ClaimedBundleIsDispatchedOrCollision P dec S hr hdec f x hne with
    ⟨d, hd, -, -, hx, hdx⟩ | hc
  · left
    subst hx
    have hsrc := ((inv_reach hr).formed d hd).source
    rw [hdx]
    exact ⟨hsrc, claimPreimage_canonical hdx hsrc⟩
  · right
    exact hc

theorem RecoveredCallsAreDispatchedCalls : Properties.RecoveredCallsAreDispatchedCalls := by
  intro P dec S hr hdec f x hne
  rcases ClaimedBundleIsDispatchedOrCollision P dec S hr hdec f x hne with
    ⟨d, hd, hat, hf, hx, hdx⟩ | hc
  · left
    subst hx
    have hI := inv_reach hr
    have hsrc := (hI.formed d hd).source
    refine ⟨d, hd, hat, hf, ?_, ?_, ?_, ?_⟩
    · unfold claimRefundHash bundleHash
      rw [claimPreimage_canonical hdx hsrc]
    · rw [hdx]
    · rw [hdx]
      exact (hI.formed d hd).calls
    · rw [hdx]
      exact hI.validated rfl d hd hat
  · right
    exact hc

theorem ClaimIdentifiesOneDispatch : Properties.ClaimIdentifiesOneDispatch := by
  intro K P S hr i j hi hj hai haj hf henc
  refine getElem_inj_of_nodup_map_filter (EachLegAppendedOnce K P S hr) hi hj hai haj ?_
  show (S.log[i].atomicSend.flowId, bundleHash P S.log[i].bundle) =
    (S.log[j].atomicSend.flowId, bundleHash P S.log[j].bundle)
  unfold bundleHash bundlePreimage
  rw [hf, henc]

theorem EachBundleRecoveredAtMostOnce : Properties.EachBundleRecoveredAtMostOnce := by
  intro P dec S₀ S₂ f f' x x' hr₀ hg₀ hr₁₂ hdec₂ hg₂
  have hstep : Step deployed P S₀
      { S₀ with manager := S₀.manager.set f (claimRefundHash P dec x) .Reverted } :=
    Step.claim f _ hg₀
  have hr₂ : Reach deployed P init S₂ := reach_trans (.tail hr₀ hstep) hr₁₂
  have hpre : S₀.log <+: S₂.log := by
    have h := reach_log_prefix hr₁₂
    exact h
  have hdec₀ : DecodesDispatchedBundles P dec S₀.log := fun d hd => hdec₂ d (hpre.subset hd)
  have hne₀ : S₀.manager.legState f (claimRefundHash P dec x) ≠ .Unset := by
    rw [hg₀]; decide
  have hne₂ : S₂.manager.legState f' (claimRefundHash P dec x') ≠ .Unset := by
    rw [hg₂]; decide
  rcases ClaimedBundleIsDispatchedOrCollision P dec S₀ hr₀ hdec₀ f x hne₀ with
    ⟨d, hd, hat, hf, hx, hdx⟩ | hc₀
  · rcases ClaimedBundleIsDispatchedOrCollision P dec S₂ hr₂ hdec₂ f' x' hne₂ with
      ⟨d', hd', hat', hf', hx', hdx'⟩ | hc₂
    · by_cases hb : dec x' = dec x
      · right; right; right
        have hbb : d.bundle = d'.bundle := by rw [← hdx, ← hdx', hb]
        have hd₂ : d ∈ S₂.log := hpre.subset hd
        by_cases hdd : d = d'
        · -- The same dispatch: the second claim replays the first, on a leg now `Reverted`.
          exfalso
          subst hdd
          have hff : f' = f := hf'.symm.trans hf
          have hxx : x' = x := hx'.trans hx.symm
          rw [hff, hxx] at hg₂
          have hR₂ := reach_keeps_reverted hr₁₂ f (claimRefundHash P dec x) (by simp)
          rw [hR₂] at hg₂
          exact absurd hg₂ (by decide)
        · -- Two dispatches with one bundle: O1 (c) leaves only the cross-sender salt clash.
          obtain ⟨i, hi, hi'⟩ := List.getElem_of_mem hd₂
          obtain ⟨j, hj, hj'⟩ := List.getElem_of_mem hd'
          have hij : i ≠ j := by
            rintro rfl
            exact hdd (hi'.symm.trans hj')
          rcases DistinctDispatchesDistinctBundles P S₂ hr₂ i j hi hj hij with hne | hclash
          · exact (hne (by rw [hi', hj']; exact hbb)).elim
          · refine ⟨d, hd₂, d', hd', hat, hf, hx, hat', hf', hx', hbb, ?_⟩
            rw [← hi', ← hj']
            exact hclash
      · left
        exact hb
    · right; right; left
      exact hc₂
  · right; left
    exact hc₀

theorem EachBundleRecoveredAtMostOnceOn : Properties.EachBundleRecoveredAtMostOnceOn := by
  intro P dec S₀ S₂ f f' x x' hr₀ hg₀ hr₁₂ hdec₂ hg₂ hinj hsalt
  have hpre : S₀.log <+: S₂.log := by
    have h := reach_log_prefix hr₁₂
    exact h
  have hmem : ∀ d ∈ S₂.log, bundlePreimage P d.bundle ∈ bundlePreimages P S₂.log :=
    fun d hd => List.mem_map.mpr ⟨d, hd, rfl⟩
  rcases EachBundleRecoveredAtMostOnce P dec S₀ S₂ f f' x x' hr₀ hg₀ hr₁₂ hdec₂ hg₂ with
    h | ⟨d, hd, -, -, hne, hh⟩ | ⟨d, hd, -, -, hne, hh⟩ |
      ⟨d, hd, d', hd', -, -, -, -, -, -, -, hs⟩
  · exact h
  · exact absurd (hinj (claimPreimage dec x) (by simp) (bundlePreimage P d.bundle)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hmem d (hpre.subset hd)))) hh) hne
  · exact absurd (hinj (claimPreimage dec x') (by simp) (bundlePreimage P d.bundle)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hmem d hd))) hh) hne
  · exact absurd (hsalt (saltPreimage d.sender d.salt) (List.mem_map.mpr ⟨d, hd, rfl⟩)
      (saltPreimage d'.sender d'.salt) (List.mem_map.mpr ⟨d', hd', rfl⟩) hs.2.2.2) hs.2.2.1

/-! ## The liveness note -/

theorem CanonicalBytesReadTheirLeg : Properties.CanonicalBytesReadTheirLeg := by
  intro K P dec S hr hdec d hd hat
  exact ⟨claimPreimage_canonical (hdec d hd) ((inv_reach hr).formed d hd).source,
    (legInv_reach hr).stay d hd hat⟩

theorem NonCanonicalBytesNeverClaim : Properties.NonCanonicalBytesNeverClaim := by
  intro P dec S hr hdec f x hnc
  by_cases hU : S.manager.legState f (claimRefundHash P dec x) = .Unset
  · exact Or.inl hU
  · rcases ClaimedBundleIsDispatchedOrCollision P dec S hr hdec f x hU with
      ⟨d, hd, hat, hf, hx, -⟩ | hc
    · exact absurd hx (hnc d hd hat hf)
    · exact Or.inr hc

theorem ReencodedBundleNeverClaims : Properties.ReencodedBundleNeverClaims := by
  intro P dec S hr hdec d hd f x hdx hx
  refine NonCanonicalBytesNeverClaim P dec S hr hdec f x ?_
  intro d' hd' _ _ hx'
  apply hx
  have hbb : d'.bundle = d.bundle := by rw [← hdx, hx', hdec d' hd']
  rw [hx', hbb]

/-! ## Witness and countermodel data -/

namespace ClaimBinding

/-! ### The honest run `wS3`, and a trailing zero byte -/

/-- `wS3`'s only leg that is not `Unset` is `(7, 1)`, `wD1`'s, and it is `Revertable`. -/
theorem wS3_legState (f h : Word) :
    wS3.manager.legState f h = if f = 7 ∧ h = 1 then .Revertable else .Unset := by
  show (wS2.manager.set 7 (bundleHash wParams wD1.bundle) .Revertable).legState f h = _
  rw [legState_set, wHash1, wS2, afterSend_legState, wS1, afterSend_legState, wHash1]
  by_cases hc : f = 7 ∧ h = 1
  · simp [hc]
  · simp [hc, wD1, wD2, init]

theorem saltWordsEncoder_length (b : Bundle) : (saltWordsEncoder b).length = 64 := by
  simp [saltWordsEncoder, length_toBytesBE]

/-- One trailing byte makes the witness encoding a different byte string. -/
theorem trailingByte_ne (b b' : Bundle) : saltWordsEncoder b ++ [0] ≠ saltWordsEncoder b' := by
  intro h
  have := congrArg List.length h
  simp [saltWordsEncoder_length] at this

/-- The lenient witness decoder reads `wD1`'s bytes with a trailing zero byte as `wD1`'s bundle. -/
theorem wDec_trailingByte : wDec (wParams.enc wD1.bundle ++ [0]) = wD1.bundle := by
  show (if saltWordsEncoder wD1.bundle ++ [0] = saltWordsEncoder wD2.bundle then wD2.bundle
    else wD1.bundle) = wD1.bundle
  rw [ite_eq_right (trailingByte_ne _ _)]

theorem toBytesBE_32_zero : toBytesBE 32 0 = (0 : UInt8) :: List.replicate 31 0 := by decide

/-- The claim with the trailing byte hashes a preimage whose last word is zero, so on the honest
chain it reads the leg `(7, 0)`, not `wD1`'s `(7, 1)`. -/
theorem claimRefundHash_trailingByte :
    claimRefundHash wParams wDec (wParams.enc wD1.bundle ++ [0]) = 0 := by
  unfold claimRefundHash claimPreimage
  rw [wDec_trailingByte]
  have hpad : pad32 (wParams.enc wD1.bundle ++ [0]) =
      wParams.enc wD1.bundle ++ toBytesBE 32 0 := by
    rw [toBytesBE_32_zero]
    have hl : (wParams.enc wD1.bundle ++ [0]).length = 65 := by
      simp [wParams, saltWordsEncoder_length]
    rw [pad32, hl]
    simp
  show lastWord (abiEncode _ _) = 0
  rw [abiEncode, hpad]
  have hassoc : ∀ (a b c d e : List UInt8),
      a ++ (b ++ (c ++ (d ++ e))) = (a ++ b ++ c ++ d) ++ e := by
    intros; simp
  rw [hassoc, lastWord_append_word]
  rfl

/-! ### Two atomic legs of flow `7` on the honest chain, both refunded -/

/-- Sender `3`, salt `3`: a second atomic leg of flow `7` with one direct zero-value call. -/
def twoD3 : Dispatch := ⟨3, [wDirect 0], wBundle wParams 3 3 [⟨5, 3, 0, []⟩], ⟨7, 0, 100, true⟩⟩

/-- A decoder that inverts the honest encoder on `wD1`'s and `twoD3`'s bundles. -/
def twoDec (x : List UInt8) : Bundle :=
  if x = wParams.enc twoD3.bundle then twoD3.bundle else wD1.bundle

/-- After `wS1`: dispatch `twoD3`, then authorize both legs. -/
def twoS2 : State := wS1.afterSend wParams twoD3
def twoS3 : State := { twoS2 with manager := twoS2.manager.set 7 1 .Revertable }
def twoS4 : State := { twoS3 with manager := twoS3.manager.set 7 3 .Revertable }

theorem twoHash3 : bundleHash wParams twoD3.bundle = 3 := bundleHash_wParams _

theorem twoEnc_ne : wParams.enc wD1.bundle ≠ wParams.enc twoD3.bundle := by
  intro he
  have := congrArg (List.drop 32) he
  simp only [wParams, saltWordsEncoder, List.drop_left' (length_toBytesBE 32 _)] at this
  have hm := toBytesBE_eq_mod this
  simp [wD1, twoD3, wBundle, wAttrs] at hm

theorem twoDec_wD1 : twoDec (wParams.enc wD1.bundle) = wD1.bundle := by
  unfold twoDec
  rw [ite_eq_right twoEnc_ne]

theorem twoDec_D3 : twoDec (wParams.enc twoD3.bundle) = twoD3.bundle := by
  unfold twoDec
  rw [ite_eq_left rfl]

theorem twoClaimHash1 : claimRefundHash wParams twoDec (wParams.enc wD1.bundle) = 1 := by
  unfold claimRefundHash
  rw [claimPreimage_canonical twoDec_wD1 rfl]
  exact wHash1

theorem twoClaimHash3 : claimRefundHash wParams twoDec (wParams.enc twoD3.bundle) = 3 := by
  unfold claimRefundHash
  rw [claimPreimage_canonical twoDec_D3 rfl]
  exact twoHash3

theorem twoS2_leg1 : twoS2.manager.legState 7 1 = .Committed := by
  rw [twoS2, afterSend_legState, twoHash3, ite_eq_right (by decide)]
  have h := wS1_leg
  rw [wHash1] at h
  exact h

theorem twoS2_leg3 : twoS2.manager.legState 7 3 = .Committed := by
  rw [twoS2, afterSend_legState, twoHash3, ite_eq_left ⟨rfl, rfl, rfl⟩]

theorem twoStep2 : Step deployed wParams wS1 twoS2 := by
  refine Step.send twoD3 (fun _ => ?_)
    ⟨rfl, rfl, List.Forall₂.cons (formsCall_direct 3 0) List.Forall₂.nil⟩ ?_ ?_
  · simp [wS1, State.afterSend, markSalt, init, wD1, twoD3, Dispatch.salt, wBundle, wAttrs]
  · intro _ _ c hc
    simp only [twoD3, wBundle, List.mem_singleton] at hc
    subst hc; rfl
  · intro _
    show wS1.manager.legState 7 (bundleHash wParams twoD3.bundle) = .Unset
    rw [twoHash3, wS1, afterSend_legState, wHash1]
    simp [wD1, init]

theorem twoStep3 : Step deployed wParams twoS2 twoS3 :=
  Step.authorize 7 1 twoS2_leg1

theorem twoStep4 : Step deployed wParams twoS3 twoS4 := by
  refine Step.authorize 7 3 ?_
  show (twoS2.manager.set 7 1 .Revertable).legState 7 3 = .Committed
  rw [legState_set, ite_eq_right (by decide)]
  exact twoS2_leg3

theorem twoReach : Reach deployed wParams init twoS4 :=
  .tail (.tail (.tail (.tail .refl wStep1) twoStep2) twoStep3) twoStep4

/-! ### A bundle no one dispatched -/

/-- One call, to contract `6`, carrying value `9`; user salt `4`. No run below dispatches it. -/
def foreignBundle : Bundle := ⟨324, 325, 1, 0, [⟨6, 1, 9, []⟩], wAttrs 4⟩

theorem foreignBundle_not_validated : ¬ Validated foreignBundle := by
  intro h
  exact absurd (h _ (List.mem_singleton_self _)) (by decide)

/-! ### The colliding chain: the canonical bytes of `foreignBundle` claim `collidingLeg`'s leg -/

/-- An honest decoder on the colliding chain: it inverts the encoder on `collidingLeg`'s bundle and
on `foreignBundle`. -/
def collidingDec (x : List UInt8) : Bundle :=
  if x = collidingParams.enc foreignBundle then foreignBundle else collidingLeg.bundle

/-- Dispatch `collidingLeg` (flow `7`), then authorize its leg `(7, 0)`. -/
def collidingS1 : State := init.afterSend collidingParams collidingLeg
def collidingS2 : State :=
  { collidingS1 with manager := collidingS1.manager.set 7 0 .Revertable }

theorem collidingEnc_ne :
    collidingParams.enc collidingLeg.bundle ≠ collidingParams.enc foreignBundle := by
  intro he
  have := congrArg (List.drop 32) he
  simp only [collidingParams, saltWordsEncoder, List.drop_left' (length_toBytesBE 32 _)] at this
  have hm := toBytesBE_eq_mod this
  simp [collidingLeg, foreignBundle, wBundle, wAttrs] at hm

theorem collidingStep1 : Step deployed collidingParams init collidingS1 := by
  refine Step.send collidingLeg (fun _ => rfl)
    ⟨rfl, rfl, List.Forall₂.cons (formsCall_direct 1 0) List.Forall₂.nil⟩ ?_ (fun _ => rfl)
  intro _ _ c hc
  simp only [collidingLeg, wBundle, List.mem_singleton] at hc
  subst hc; rfl

theorem collidingS1_leg : collidingS1.manager.legState 7 0 = .Committed := by
  rw [collidingS1, afterSend_legState, ite_eq_left ⟨rfl, rfl, rfl⟩]

theorem collidingStep2 : Step deployed collidingParams collidingS1 collidingS2 :=
  Step.authorize 7 0 collidingS1_leg

/-! ### The honest run with a decoder that is not a round trip -/

/-- `wD1`'s bundle, same source chain and salts, with its call redirected to contract `6` and given
value `9`. -/
def tamperedBundle : Bundle := { wD1.bundle with calls := [⟨6, 1, 9, []⟩] }

/-- A decoder that reads `wD1`'s canonical bytes as `tamperedBundle`. -/
def tamperedDec (x : List UInt8) : Bundle :=
  if x = wParams.enc wD1.bundle then tamperedBundle else wDec x

/-! ### Without `onlyInteropCenter`: a leg no dispatch backs -/

/-- The decoder of the empty run: everything decodes to `foreignBundle`. -/
def unbackedDec (_ : List UInt8) : Bundle := foreignBundle

theorem unbacked_hash : claimRefundHash wParams unbackedDec (wParams.enc foreignBundle) = 4 := by
  unfold claimRefundHash
  rw [claimPreimage_canonical (dec := unbackedDec) (b := foreignBundle) rfl rfl]
  exact bundleHash_wParams _

/-- A foreign `append` of leg `(7, 4)`, then its authorization. -/
def unbackedS1 : State := { init with manager := init.manager.set 7 4 .Committed }
def unbackedS2 : State :=
  { unbackedS1 with manager := unbackedS1.manager.set 7 4 .Revertable }

theorem unbackedReach : Reach withoutOnlyInteropCenter wParams init unbackedS2 := by
  refine .tail (.tail .refl (Step.foreignAppend 1 7 4 (by decide) ?_ rfl)) (Step.authorize 7 4 ?_)
  · intro h; exact absurd h (by decide)
  · show (init.manager.set 7 4 .Committed).legState 7 4 = .Committed
    simp

/-! ### Without the salt check: one sender dispatches `wD1`'s bundle again, on flow `8` -/

/-- `wD1` again, same sender, starters and bundle, on flow `8`. -/
def replayD8 : Dispatch := ⟨1, [wDirect 0], wD1.bundle, ⟨8, 0, 100, true⟩⟩

/-- On this run every dispatched bundle is `wD1`'s. -/
def replayDec (_ : List UInt8) : Bundle := wD1.bundle

/-- After `wS1`: dispatch `replayD8`, then authorize both legs. -/
def replayS2 : State := wS1.afterSend wParams replayD8
def replayS3 : State := { replayS2 with manager := replayS2.manager.set 7 1 .Revertable }
def replayS4 : State := { replayS3 with manager := replayS3.manager.set 8 1 .Revertable }

theorem wD1_validated : Validated wD1.bundle := by
  intro c hc
  simp only [wD1, wBundle, List.mem_singleton] at hc
  subst hc; rfl

theorem replayStep1 : Step withoutSaltCheck wParams init wS1 :=
  Step.send wD1 (fun h => absurd h (by decide)) wD1_formed (fun _ _ => wD1_validated)
    (fun _ => rfl)

theorem replayS2_leg (f h : Word) :
    replayS2.manager.legState f h =
      if f = 8 ∧ h = 1 then .Committed else if f = 7 ∧ h = 1 then .Committed else .Unset := by
  have h8 : bundleHash wParams replayD8.bundle = 1 := wHash1
  rw [replayS2, afterSend_legState, h8, wS1, afterSend_legState, wHash1]
  simp [replayD8, wD1, init]

theorem replayStep2 : Step withoutSaltCheck wParams wS1 replayS2 := by
  refine Step.send replayD8 (fun h => absurd h (by decide))
    ⟨rfl, rfl, List.Forall₂.cons (formsCall_direct 1 0) List.Forall₂.nil⟩
    (fun _ _ => wD1_validated) (fun _ => ?_)
  show wS1.manager.legState 8 (bundleHash wParams wD1.bundle) = .Unset
  rw [wHash1, wS1, afterSend_legState, wHash1]
  simp [wD1, init]

theorem replayStep3 : Step withoutSaltCheck wParams replayS2 replayS3 := by
  refine Step.authorize 7 1 ?_
  show replayS2.manager.legState 7 1 = .Committed
  rw [replayS2_leg]
  simp

theorem replayStep4 : Step withoutSaltCheck wParams replayS3 replayS4 := by
  refine Step.authorize 8 1 ?_
  show (replayS2.manager.set 7 1 .Revertable).legState 8 1 = .Committed
  rw [legState_set, replayS2_leg]
  simp

theorem replayReach : Reach withoutSaltCheck wParams init replayS4 :=
  .tail (.tail (.tail (.tail .refl replayStep1) replayStep2) replayStep3) replayStep4

/-! ### The colliding chain: two senders dispatch `sharedBundle` atomically on flows `7` and `8` -/

def clashLeg7 : Dispatch := ⟨1, [wIndirect], sharedBundle, ⟨7, 0, 100, true⟩⟩
def clashLeg8 : Dispatch := ⟨2, [wIndirect], sharedBundle, ⟨8, 0, 100, true⟩⟩

/-- On this run every dispatched bundle is `sharedBundle`. -/
def clashDec (_ : List UInt8) : Bundle := sharedBundle

/-- Dispatch both legs, then authorize both. -/
def clashS1 : State := init.afterSend collidingParams clashLeg7
def clashS2 : State := clashS1.afterSend collidingParams clashLeg8
def clashS3 : State := { clashS2 with manager := clashS2.manager.set 7 0 .Revertable }
def clashS4 : State := { clashS3 with manager := clashS3.manager.set 8 0 .Revertable }

theorem sharedBundle_validated : Validated sharedBundle := by
  intro c hc
  simp only [sharedBundle, List.mem_singleton] at hc
  subst hc; rfl

theorem clashStep1 : Step deployed collidingParams init clashS1 :=
  Step.send clashLeg7 (fun _ => rfl)
    ⟨rfl, rfl, List.Forall₂.cons (formsCall_indirect 1) List.Forall₂.nil⟩
    (fun _ _ => sharedBundle_validated) (fun _ => rfl)

theorem clashS1_leg (f h : Word) :
    clashS1.manager.legState f h = if f = 7 ∧ h = 0 then .Committed else .Unset := by
  rw [clashS1, afterSend_legState]
  simp [clashLeg7, init, bundleHash, collidingParams]

theorem clashStep2 : Step deployed collidingParams clashS1 clashS2 := by
  refine Step.send clashLeg8 (fun _ => by decide)
    ⟨rfl, rfl, List.Forall₂.cons (formsCall_indirect 2) List.Forall₂.nil⟩
    (fun _ _ => sharedBundle_validated) (fun _ => ?_)
  show clashS1.manager.legState 8 (bundleHash collidingParams sharedBundle) = .Unset
  rw [clashS1_leg]
  simp

theorem clashS2_leg (f h : Word) :
    clashS2.manager.legState f h =
      if f = 8 ∧ h = 0 then .Committed else if f = 7 ∧ h = 0 then .Committed else .Unset := by
  rw [clashS2, afterSend_legState, clashS1_leg]
  simp [clashLeg8, bundleHash, collidingParams]

theorem clashStep3 : Step deployed collidingParams clashS2 clashS3 := by
  refine Step.authorize 7 0 ?_
  show clashS2.manager.legState 7 0 = .Committed
  rw [clashS2_leg]
  simp

theorem clashStep4 : Step deployed collidingParams clashS3 clashS4 := by
  refine Step.authorize 8 0 ?_
  show (clashS2.manager.set 7 0 .Revertable).legState 8 0 = .Committed
  rw [legState_set, clashS2_leg]
  simp

theorem clashReach : Reach deployed collidingParams init clashS4 :=
  .tail (.tail (.tail (.tail .refl clashStep1) clashStep2) clashStep3) clashStep4

end ClaimBinding

/-! ## Countermodels -/

theorem CollisionLetsAClaimRecoverUndispatchedCalls :
    Properties.CollisionLetsAClaimRecoverUndispatchedCalls := by
  have hlog : collidingS2.log = [collidingLeg] := rfl
  have hdecx : collidingDec (collidingParams.enc foreignBundle) = foreignBundle := by
    unfold collidingDec
    rw [ite_eq_left rfl]
  refine ⟨collidingParams, collidingDec, collidingS2, 7, collidingParams.enc foreignBundle,
    .tail (.tail .refl collidingStep1) collidingStep2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    rw [hlog] at hd
    simp only [List.mem_singleton] at hd
    subst hd
    unfold collidingDec
    rw [ite_eq_right collidingEnc_ne]
  · show (collidingS1.manager.set 7 0 .Revertable).legState 7 0 = .Revertable
    simp
  · rintro ⟨d, hd, -, -, hx, -⟩
    rw [hlog] at hd
    simp only [List.mem_singleton] at hd
    subst hd
    exact collidingEnc_ne hx.symm
  · refine ⟨collidingLeg, by rw [hlog]; simp, rfl, rfl, ?_, rfl⟩
    intro hpre
    exact collidingEnc_ne (abiEncode_right_inj hpre).symm
  · intro d hd
    rw [hlog] at hd
    simp only [List.mem_singleton] at hd
    subst hd
    rw [hdecx]
    decide
  · rw [hdecx]
    exact foreignBundle_not_validated

theorem WithoutRoundTripClaimRecoversUndispatchedCalls :
    Properties.WithoutRoundTripClaimRecoversUndispatchedCalls := by
  have hlog : wS3.log = [wD1, wD2] := rfl
  have hdecx : tamperedDec (wParams.enc wD1.bundle) = tamperedBundle := by
    unfold tamperedDec
    rw [ite_eq_left rfl]
  have hne : tamperedBundle ≠ wD1.bundle := by
    intro h
    have := congrArg Bundle.calls h
    simp [tamperedBundle, wD1, wBundle] at this
  have hpre : claimPreimage tamperedDec (wParams.enc wD1.bundle) =
      bundlePreimage wParams wD1.bundle := by
    unfold claimPreimage bundlePreimage
    rw [hdecx]
    rfl
  have hhash : claimRefundHash wParams tamperedDec (wParams.enc wD1.bundle) = 1 := by
    unfold claimRefundHash
    rw [hpre]
    exact wHash1
  refine ⟨wParams, tamperedDec, wS3, 7, wParams.enc wD1.bundle, wReach, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have := h wD1 (by rw [hlog]; simp)
    rw [hdecx] at this
    exact hne this
  · rw [hhash, wS3_legState]
    simp
  · rintro ⟨d, hd, hat, -, -, hdx⟩
    rw [hlog] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · rw [hdecx] at hdx
      exact hne hdx
    · exact absurd hat (by decide)
  · rintro ⟨d, hd, hat, -, hpre', -⟩
    rw [hlog] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact hpre' hpre
    · exact absurd hat (by decide)
  · intro d hd
    rw [hlog] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rw [hdecx]
    rcases hd with rfl | rfl
    · decide
    · decide
  · rw [hdecx]
    intro h
    exact absurd (h _ (List.mem_singleton_self _)) (by decide)

theorem WithoutOnlyInteropCenterClaimRecoversUndispatchedCalls :
    Properties.WithoutOnlyInteropCenterClaimRecoversUndispatchedCalls := by
  have hlog : unbackedS2.log = [] := rfl
  refine ⟨wParams, unbackedDec, unbackedS2, 7, wParams.enc foreignBundle, unbackedReach, ?_, rfl,
    ?_, ?_, ?_, foreignBundle_not_validated⟩
  · intro d hd
    rw [hlog] at hd
    exact absurd hd List.not_mem_nil
  · rw [unbacked_hash]
    show ((init.manager.set 7 4 .Committed).set 7 4 .Revertable).legState 7 4 = .Revertable
    simp
  · rintro ⟨d, hd, -⟩
    rw [hlog] at hd
    exact absurd hd List.not_mem_nil
  · rintro ⟨d, hd, -⟩
    rw [hlog] at hd
    exact absurd hd List.not_mem_nil

theorem WithoutSaltCheckOneBundleRecoveredTwice :
    Properties.WithoutSaltCheckOneBundleRecoveredTwice := by
  have hpre : claimPreimage replayDec (wParams.enc wD1.bundle) =
      bundlePreimage wParams wD1.bundle :=
    claimPreimage_canonical rfl rfl
  have hh : claimRefundHash wParams replayDec (wParams.enc wD1.bundle) = 1 := by
    unfold claimRefundHash
    rw [hpre]
    exact wHash1
  refine ⟨wParams, replayDec, replayS4, _, 7, 8, wParams.enc wD1.bundle, replayReach, ?_, .refl,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hh]
    show ((replayS2.manager.set 7 1 .Revertable).set 8 1 .Revertable).legState 7 1 = .Revertable
    simp
  · intro d hd
    have hd' : d ∈ [wD1, replayD8] := hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with rfl | rfl <;> rfl
  · rw [hh]
    show (((replayS2.manager.set 7 1 .Revertable).set 8 1 .Revertable).set 7 1 .Reverted).legState
      8 1 = .Revertable
    simp
  · rintro ⟨d, hd, -, hf, hpre', -⟩
    have hd' : d ∈ [wD1, replayD8] := hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with rfl | rfl
    · exact hpre' hpre
    · exact absurd hf (by decide)
  · rintro ⟨d, hd, -, hf, hpre', -⟩
    have hd' : d ∈ [wD1, replayD8] := hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with rfl | rfl
    · exact absurd hf (by decide)
    · exact hpre' hpre
  · rintro ⟨d, hd, d', hd', -, hsend, -⟩
    have hdl : d ∈ [wD1, replayD8] := hd
    have hdl' : d' ∈ [wD1, replayD8] := hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hdl hdl'
    rcases hdl with rfl | rfl <;> rcases hdl' with rfl | rfl <;> exact hsend rfl

theorem SaltClashLetsOneBundleBeRecoveredTwice :
    Properties.SaltClashLetsOneBundleBeRecoveredTwice := by
  have hh : claimRefundHash collidingParams clashDec (collidingParams.enc sharedBundle) = 0 := rfl
  have hpre : claimPreimage clashDec (collidingParams.enc sharedBundle) =
      bundlePreimage collidingParams sharedBundle := rfl
  refine ⟨collidingParams, clashDec, clashS4, _, 7, 8, collidingParams.enc sharedBundle,
    clashReach, ?_, .refl, ?_, ?_, ?_, ?_⟩
  · rw [hh]
    show ((clashS2.manager.set 7 0 .Revertable).set 8 0 .Revertable).legState 7 0 = .Revertable
    simp
  · intro d hd
    have hd' : d ∈ [clashLeg7, clashLeg8] := hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with rfl | rfl <;> rfl
  · rw [hh]
    show (((clashS2.manager.set 7 0 .Revertable).set 8 0 .Revertable).set 7 0 .Reverted).legState
      8 0 = .Revertable
    simp
  · rintro ⟨d, hd, -, hf, hpre', -⟩
    have hd' : d ∈ [clashLeg7, clashLeg8] := hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with rfl | rfl
    · exact hpre' hpre
    · exact absurd hf (by decide)
  · rintro ⟨d, hd, -, hf, hpre', -⟩
    have hd' : d ∈ [clashLeg7, clashLeg8] := hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with rfl | rfl
    · exact absurd hf (by decide)
    · exact hpre' hpre

/-! ## Non-vacuity -/

theorem ClaimBindingWitness : Properties.ClaimBindingWitness := by
  have hlog : wS3.log = [wD1, wD2] := rfl
  obtain ⟨hdec, hleg, -⟩ := ClaimWitness
  refine ⟨wReach, hlog, rfl, hdec, hleg, ?_, ⟨wD1, by rw [hlog]; simp, rfl, rfl, rfl, wDec_wD1⟩,
    ?_, ?_⟩
  · rw [wClaimPreimage]
    refine keccakInjOn_cons_of_mem ?_ DispatchWitness.2.2.2.2.1
    exact List.mem_map.mpr ⟨wD1, by rw [hlog]; simp, rfl⟩
  · rintro ⟨d, hd, hat, -, hpre, -⟩
    rw [hlog] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact hpre wClaimPreimage
    · exact absurd hat (by decide)
  · rw [wDec_wD1]
    rfl

theorem ClaimBindingNonCanonicalWitness : Properties.ClaimBindingNonCanonicalWitness := by
  have hlog : wS3.log = [wD1, wD2] := rfl
  obtain ⟨hdec, -, -⟩ := ClaimWitness
  have hne1 : wParams.enc wD1.bundle ++ [0] ≠ wParams.enc wD1.bundle := trailingByte_ne _ _
  refine ⟨wReach, hdec, by rw [hlog]; simp, wDec_trailingByte, hne1, ?_, ?_, ?_⟩
  · intro d hd hat _
    rw [hlog] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact hne1
    · exact absurd hat (by decide)
  · rw [claimRefundHash_trailingByte, wS3_legState]
    simp
  · rintro ⟨d, hd, hat, -, -, hh⟩
    rw [hlog] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · rw [claimRefundHash_trailingByte, wHash1] at hh
      exact absurd hh (by decide)
    · exact absurd hat (by decide)

theorem ClaimBindingTwoClaimsWitness : Properties.ClaimBindingTwoClaimsWitness := by
  refine ⟨wParams, twoDec, twoS4, _, 7, 7, wParams.enc wD1.bundle, wParams.enc twoD3.bundle,
    twoReach, ?_, .refl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [twoClaimHash1]
    show ((twoS2.manager.set 7 1 .Revertable).set 7 3 .Revertable).legState 7 1 = .Revertable
    simp
  · intro d hd
    have hd' : d ∈ [wD1, twoD3] := hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with rfl | rfl
    · exact twoDec_wD1
    · exact twoDec_D3
  · rw [twoClaimHash1, twoClaimHash3]
    show ((twoS3.manager.set 7 3 .Revertable).set 7 1 .Reverted).legState 7 3 = .Revertable
    simp
  · have hpair : KeccakInjOn wParams.keccak (bundlePreimages wParams [wD1, twoD3]) := by
      refine keccakInjOn_pair ?_
      change bundleHash wParams wD1.bundle ≠ bundleHash wParams twoD3.bundle
      rw [wHash1, twoHash3]
      decide
    show KeccakInjOn wParams.keccak (claimPreimage twoDec (wParams.enc wD1.bundle) ::
      claimPreimage twoDec (wParams.enc twoD3.bundle) :: bundlePreimages wParams [wD1, twoD3])
    rw [claimPreimage_canonical twoDec_wD1 rfl, claimPreimage_canonical twoDec_D3 rfl]
    refine keccakInjOn_cons_of_mem (by simp [bundlePreimages]) ?_
    exact keccakInjOn_cons_of_mem (by simp [bundlePreimages]) hpair
  · show KeccakInjOn wParams.keccak (saltPreimages [wD1, twoD3])
    refine keccakInjOn_pair ?_
    show lastWord (saltPreimage wD1.sender wD1.salt) ≠
      lastWord (saltPreimage twoD3.sender twoD3.salt)
    rw [lastWord_saltPreimage, lastWord_saltPreimage]
    decide
  · rw [twoDec_wD1, twoDec_D3]
    intro h
    have := congrArg (fun b => b.bundleAttributes.salt) h
    simp [twoD3, wD1, wBundle, wAttrs] at this
  · rintro ⟨d, hd, -, -, hpre, hh⟩
    have hd' : d ∈ [wD1, twoD3] := hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with rfl | rfl
    · exact hpre (claimPreimage_canonical twoDec_wD1 rfl)
    · rw [twoClaimHash1, twoHash3] at hh
      exact absurd hh (by decide)
  · rintro ⟨d, hd, -, -, hpre, hh⟩
    have hd' : d ∈ [wD1, twoD3] := hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with rfl | rfl
    · rw [twoClaimHash3, wHash1] at hh
      exact absurd hh (by decide)
    · exact hpre (claimPreimage_canonical twoDec_D3 rfl)
  · rintro ⟨d, hd, d', hd', hs, hsend, -⟩
    have hdl : d ∈ [wD1, twoD3] := hd
    have hdl' : d' ∈ [wD1, twoD3] := hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hdl hdl'
    rcases hdl with rfl | rfl <;> rcases hdl' with rfl | rfl
    · exact hsend rfl
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact hsend rfl

end Contracts.InteropCenter
