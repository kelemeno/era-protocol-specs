import EraSpec.Contracts.L2InteropHandler.Properties.SourceBindingReduced
import EraSpec.Contracts.InteropCenter.Proofs.Dispatch
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashEncoding
import EraSpec.Protocol.InteropAtomicity.Proofs.OncePerLeg
import EraSpec.Protocol.InteropAtomicity.Proofs.Atomicity

/-!
# Proofs: the atomic path's source binding, from the vouching chain's code

Two projections do the work. A run of the vouching chain is a run of the center model
(`sourceReach_center`), and, with `onlyInteropCenter`, a run of the append path whose append log is
the run's atomic dispatches (`sourceReach_steps`). The headline then chains three existing facts:

* `Contracts.AppendPath.KeyPinsAppendedLegOrClash`: a nonzero key is a logged leg's commit value,
  or clashes with one;
* `Contracts.InteropCenter.inv_reach`: every logged dispatch was formed on this chain;
* the two halves of `abi.encode(uint256, bytes)`'s injectivity: the head word
  (`abiEncode_head_inj`, from the decoder's first component) and the bytes
  (`Contracts.InteropCenter.abiEncode_right_inj`).

`CommitValueOnlyInItsSourceTreeOrBreak` is the headline on the second chain, with the first
chain's dispatched bytes presented. The gate form adds
`Contracts.Atomicity.finality_means_membership_or_break`.

The witnesses reuse topic `Dispatch`'s honest run (`wD1`, `wD2`, `wS3`) with the tree attached.
-/

namespace Contracts.SourceBinding

open MerkleSpec IMTAbstract
open AttackVectors.BundleHashEncoding
open Contracts.InteropCenter
open Contracts.AtomicFlowManager (Manager LegState AppendGuard AuthorizeGuard ClaimGuard)
open Contracts.Atomicity (CommitValue FlowHash System Flow FlowLeg GateEvidence ExecutedViaBy
  InclusionBreak Wf)
open Contracts.Refund (Obligation CommitClash CommitValueInjOn)
open Contracts.AppendPath (ChainState AppendSucceeds InsertSucceeds reseed)
open Contracts.InteropCommitmentTree (Tree setup toAbs LeafHash Initialized)

/-! ## Reading the composed state -/

lemma afterSend_log (P : Params) (C : State) (d : Dispatch) :
    (C.afterSend P d).log = C.log ++ [d] := rfl

lemma appendLog_snoc_atomic (P : Params) (log : List Dispatch) {d : Dispatch}
    (hat : d.isAtomic = true) :
    appendLog P (log ++ [d]) = dispatchObligation P d :: appendLog P log := by
  simp [appendLog, List.filter_append, hat]

lemma appendLog_snoc_public (P : Params) (log : List Dispatch) {d : Dispatch}
    (hat : d.isAtomic = false) :
    appendLog P (log ++ [d]) = appendLog P log := by
  simp [appendLog, List.filter_append, hat]

lemma mem_appendLog {P : Params} {log : List Dispatch} {o : Obligation} :
    o ∈ appendLog P log ↔ ∃ d ∈ log, d.isAtomic = true ∧ dispatchObligation P d = o := by
  simp [appendLog, and_assoc]

lemma toChain_public {P : Params} {S : SourceState} {d : Dispatch} (hat : d.isAtomic = false) :
    (⟨S.center.afterSend P d, S.tree⟩ : SourceState).toChain = S.toChain := by
  simp [SourceState.toChain, State.afterSend, hat]

lemma toChain_atomic {P : Params} {cv : CommitValue} {S : SourceState} {d : Dispatch} {low : ℕ}
    (hat : d.isAtomic = true) :
    (⟨S.center.afterSend P d,
        Contracts.InteropCommitmentTree.insert S.tree
          (cv d.atomicSend.flowId (bundleHash P d.bundle)) low⟩ : SourceState).toChain
      = S.toChain.appended cv d.atomicSend.flowId (bundleHash P d.bundle) low := by
  simp [SourceState.toChain, State.afterSend, hat, ChainState.appended]

/-! ## The two projections -/

/-- Forgetting the tree: a center run with the same checks. -/
theorem sourceReach_center {K : Checks} {P : Params} {cv : CommitValue} {S T : SourceState}
    (hr : SourceReach K P cv S T) : Reach K P S.center T.center := by
  induction hr with
  | refl => exact Reach.refl
  | tail _ hs ih =>
    cases hs with
    | sendPublic d hat hsalt hform =>
      refine Reach.tail ih (Step.send d hsalt hform ?_ ?_)
      · intro h; rw [hat] at h; exact absurd h Bool.false_ne_true
      · intro h; rw [hat] at h; exact absurd h Bool.false_ne_true
    | sendAtomic d hint low hat hsalt hform hval happ =>
      exact Reach.tail ih (Step.send d hsalt hform (fun _ hK => hval hK) (fun _ => happ.legUnset))
    | authorize f h hg => exact Reach.tail ih (Step.authorize f h hg)
    | claim f h hg => exact Reach.tail ih (Step.claim f h hg)
    | initL2 _ => exact ih
    | foreignAppend caller f h hint low hne hmod happ =>
      exact Reach.tail ih (Step.foreignAppend caller f h hne hmod happ.legUnset)

/-- Forgetting the salts and the dispatch log: an append-path run, whose log is the run's atomic
dispatches. -/
theorem sourceReach_steps {K : Checks} {P : Params} {cv : CommitValue} {S : SourceState}
    (hK : K.onlyInteropCenter = true) (hr : SourceReach K P cv sourceGenesis S) :
    Contracts.AppendPath.Steps cv P.chainId Contracts.AppendPath.genesis S.toChain
      (appendLog P S.center.log) := by
  induction hr with
  | refl => exact Contracts.AppendPath.Steps.refl
  | tail _ hs ih =>
    cases hs with
    | sendPublic d hat _ _ =>
      rw [toChain_public hat, afterSend_log, appendLog_snoc_public P _ hat]
      exact ih
    | sendAtomic d hint low hat _ _ _ happ =>
      rw [toChain_atomic hat, afterSend_log, appendLog_snoc_atomic P _ hat]
      exact Contracts.AppendPath.Steps.append ih happ
    | authorize f h hg => exact Contracts.AppendPath.Steps.authorize ih hg
    | claim f h hg => exact Contracts.AppendPath.Steps.claim ih hg
    | initL2 h0 => exact Contracts.AppendPath.Steps.initL2 ih h0
    | foreignAppend caller f h hint low hne hmod _ => exact absurd (hmod hK) hne

theorem SourceRunProjectsToCenterReach : Properties.SourceRunProjectsToCenterReach :=
  fun _ _ _ _ _ hr => sourceReach_center hr

theorem SourceRunProjectsToAppendPath : Properties.SourceRunProjectsToAppendPath :=
  fun _ _ _ _ hK hr => sourceReach_steps hK hr

/-! ## LocalHonesty's links 1 and 2, on the composed run -/

theorem SourceKeysAreDispatchedCommitValues : Properties.SourceKeysAreDispatchedCommitValues := by
  intro P cv S hr v
  have hk := Contracts.AppendPath.RunKeysAreLoggedCommitValues cv P.chainId S.toChain _
    (sourceReach_steps rfl hr)
  change v ∈ keys (toAbs S.toChain.tree) ↔ _
  rw [hk, Finset.mem_insert, List.mem_toFinset, List.mem_map]
  constructor
  · rintro (h0 | ⟨o, ho, hov⟩)
    · exact Or.inl h0
    · obtain ⟨d, hd, hat, rfl⟩ := mem_appendLog.mp ho
      exact Or.inr ⟨d, hd, hat, hov⟩
  · rintro (h0 | ⟨d, hd, hat, hv⟩)
    · exact Or.inl h0
    · exact Or.inr ⟨dispatchObligation P d, mem_appendLog.mpr ⟨d, hd, hat, rfl⟩, hv⟩

/-! ## Link 3: the two halves of `abi.encode(uint256, bytes)` -/

/-- The decoder's first component reads back the `uint256` head word, with no bound on the bytes:
the head half of `abiDecode_abiEncode`. -/
lemma abiDecode_fst_abiEncode {c : ℕ} (hc : c < 256 ^ 32) (b : List UInt8) :
    (abiDecode (abiEncode c b)).1 = c := by
  have h1 : (abiEncode c b).take 32 = word c := List.take_left' (length_toBytesBE 32 c)
  unfold abiDecode
  dsimp only
  rw [h1]
  exact fromBytesBE_toBytesBE hc

/-- **`abi.encode(uint256, bytes)` DETERMINES ITS `uint256` ARGUMENT** below `2^256`. -/
lemma abiEncode_head_inj {c c' : ℕ} {x y : List UInt8} (hc : c < 256 ^ 32) (hc' : c' < 256 ^ 32)
    (h : abiEncode c x = abiEncode c' y) : c = c' :=
  calc c = (abiDecode (abiEncode c x)).1 := (abiDecode_fst_abiEncode hc x).symm
    _ = (abiDecode (abiEncode c' y)).1 := by rw [h]
    _ = c' := abiDecode_fst_abiEncode hc' y

/-- **EQUAL BUNDLE-HASH PREIMAGES BIND THE SOURCE CHAIN AND THE BYTES.** If the handler's
preimage of `x` is the center's preimage of `b`, the decoded source chain is the center's
`block.chainid` and `x` is the center's `abi.encode(b)`. Nothing is assumed about `dec`. -/
lemma preimage_eq_bound {P : Params} {dec : List UInt8 → Bundle} {x : List UInt8} {b : Bundle}
    (h : executedPreimage dec x = bundlePreimage P b) :
    (dec x).sourceChainId = P.chainId ∧ x = P.enc b := by
  have hc : (dec x).sourceChainId.val < 256 ^ 32 := by
    rw [size_eq]; exact (dec x).sourceChainId.isLt
  have hc' : P.chainId.val < 256 ^ 32 := by
    rw [size_eq]; exact P.chainId.isLt
  exact ⟨Fin.ext (abiEncode_head_inj hc hc' h), abiEncode_right_inj h⟩

/-! ## The core: a key of the vouching chain's tree names a dispatch, or a pinned break -/

/-- With `onlyInteropCenter` in place, a key of the presented leg's commit value names an atomic
dispatch of the vouching chain that committed exactly `(f, h)` from the same preimage, or a
`SourceBindingBreak` holds. -/
theorem key_names_dispatch_or_break {K : Checks} {P : Params} {cv : CommitValue} {S : SourceState}
    (hK : K.onlyInteropCenter = true) (hr : SourceReach K P cv sourceGenesis S)
    {dec : List UInt8 → Bundle} {x : List UInt8} {f h : Word}
    (hh : executedHash P.keccak dec x = h) (hkey : cv f h ∈ keys (toAbs S.tree)) :
    (∃ d ∈ S.center.log, d.isAtomic = true ∧ d.atomicSend.flowId = f ∧ bundleHash P d.bundle = h
        ∧ executedPreimage dec x = bundlePreimage P d.bundle)
      ∨ SourceBindingBreak P cv S dec x f h := by
  by_cases h0 : cv f h = 0
  · exact Or.inr (Or.inl h0)
  obtain ⟨hor, -⟩ := Contracts.AppendPath.KeyPinsAppendedLegOrClash cv P.chainId S.toChain _
    (sourceReach_steps hK hr) f h h0 hkey
  rcases hor with hmem | ⟨o, ho, hcl⟩
  · obtain ⟨d, hd, hat, hdo⟩ := mem_appendLog.mp hmem
    have hf : d.atomicSend.flowId = f := congrArg Obligation.flowId hdo
    have hb : bundleHash P d.bundle = h := congrArg Obligation.bundleHash hdo
    by_cases hpre : executedPreimage dec x = bundlePreimage P d.bundle
    · exact Or.inl ⟨d, hd, hat, hf, hb, hpre⟩
    · exact Or.inr (Or.inr (Or.inr ⟨d, hd, hat, hf, hb, hpre, hh.trans hb.symm⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨o, ho, hcl⟩))

/-! ## The source binding -/

theorem AtomicSourceBoundOrBreak : Properties.AtomicSourceBoundOrBreak := by
  intro P cv S hr dec x f h hh hkey
  rcases key_names_dispatch_or_break rfl hr hh hkey with ⟨d, -, -, -, -, hpre⟩ | hb
  · exact Or.inl (preimage_eq_bound hpre).1
  · exact Or.inr hb

theorem ExecutedBytesAreDispatchedOrBreak : Properties.ExecutedBytesAreDispatchedOrBreak := by
  intro P cv S hr dec x f h hh hkey
  rcases key_names_dispatch_or_break rfl hr hh hkey with ⟨d, hd, hat, hf, hb, hpre⟩ | hbr
  · have hI : Inv deployed P S.center := inv_reach (sourceReach_center hr)
    obtain ⟨hsrc, hx⟩ := preimage_eq_bound hpre
    exact Or.inl ⟨d, hd, hat, hf, hb, hx, hsrc, hI.formed d hd, hI.validated rfl d hd hat⟩
  · exact Or.inr hbr

/-- Every element on the right of a `Forall₂` has a partner on the left. -/
lemma forall₂_mem_right {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : ∀ b ∈ l₂, ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => intro b hb; simp at hb
  | cons hab _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, hR⟩ := ih b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hR⟩

theorem ExecutedCallersAreSourceSendersOrBreak :
    Properties.ExecutedCallersAreSourceSendersOrBreak := by
  intro P cv S hr dec hdec x f h hh hkey
  rcases ExecutedBytesAreDispatchedOrBreak P cv S hr dec x f h hh hkey with
    ⟨d, hd, hat, hf, -, hx, hsrc, hform, hval⟩ | hbr
  · have hdx : dec x = d.bundle := by rw [hx]; exact hdec d hd
    refine Or.inl ⟨d, hd, hat, hf, hdx, hsrc, ?_⟩
    intro k hk
    rw [hdx] at hk
    refine ⟨hval k hk, ?_⟩
    obtain ⟨cs, hcs, hk'⟩ := forall₂_mem_right hform.calls k hk
    cases hind : cs.callAttributes.indirectCall
    · exact Or.inl (hk'.direct hind).2.2
    · exact Or.inr ⟨cs, hcs, hind, hk'.indirect hind⟩
  · exact Or.inr hbr

theorem AtomicSourceBoundOn : Properties.AtomicSourceBoundOn := by
  intro P cv S hr dec x f h hh h0 hcv hkec hkey
  rcases AtomicSourceBoundOrBreak P cv S hr dec x f h hh hkey with hsrc | hb
  · exact hsrc
  · exfalso
    rcases hb with hs | ⟨o, ho, hcl⟩ | ⟨d, hd, _, _, _, hne, heq⟩
    · exact h0 hs
    · exact hcv _ List.mem_cons_self o (List.mem_cons_of_mem _ ho) hcl
    · exact hne (hkec _ List.mem_cons_self _
        (List.mem_cons_of_mem _ (List.mem_map_of_mem hd)) heq)

theorem CommitValueOnlyInItsSourceTreeOrBreak :
    Properties.CommitValueOnlyInItsSourceTreeOrBreak := by
  intro keccak enc center cv c c' S S' hr hr' d hd hat hkey
  have hsrc : d.bundle.sourceChainId = c :=
    ((inv_reach (sourceReach_center hr)).formed d hd).source
  have hpre : executedPreimage (fun _ => d.bundle) (enc d.bundle)
      = bundlePreimage ⟨c, center, enc, keccak⟩ d.bundle := by
    unfold executedPreimage bundlePreimage
    rw [hsrc]
  rcases AtomicSourceBoundOrBreak ⟨c', center, enc, keccak⟩ cv S' hr' (fun _ => d.bundle)
      (enc d.bundle) d.atomicSend.flowId _ (congrArg keccak hpre) hkey with h | h
  · exact Or.inl ((h.symm.trans hsrc : c' = c))
  · exact Or.inr h

/-! ## The deployed commit value -/

/-- The tag is fixed and both words are 32 bytes: the preimage determines the pair. -/
lemma commitPreimage_inj {tag : List UInt8} {f b f' b' : Word}
    (h : commitPreimage tag f b = commitPreimage tag f' b') : f = f' ∧ b = b' := by
  unfold commitPreimage at h
  have h1 : word f.val ++ word b.val = word f'.val ++ word b'.val := List.append_cancel_left h
  have hf : word f.val = word f'.val := by
    have := congrArg (List.take 32) h1
    rwa [List.take_left' (length_toBytesBE 32 _), List.take_left' (length_toBytesBE 32 _)] at this
  have hb : word b.val = word b'.val := by
    have := congrArg (List.drop 32) h1
    rwa [List.drop_left' (length_toBytesBE 32 _), List.drop_left' (length_toBytesBE 32 _)] at this
  have hf' := toBytesBE_eq_mod hf
  have hb' := toBytesBE_eq_mod hb
  rw [size_eq, Nat.mod_eq_of_lt f.isLt, Nat.mod_eq_of_lt f'.isLt] at hf'
  rw [size_eq, Nat.mod_eq_of_lt b.isLt, Nat.mod_eq_of_lt b'.isLt] at hb'
  exact ⟨Fin.ext hf', Fin.ext hb'⟩

theorem CommitClashIsKeccakClash : Properties.CommitClashIsKeccakClash := by
  intro keccak tag o o'
  constructor
  · rintro ⟨hne, heq⟩
    refine ⟨fun hpre => hne ?_, heq⟩
    obtain ⟨h1, h2⟩ := commitPreimage_inj hpre
    rw [h1, h2]
  · rintro ⟨hne, heq⟩
    refine ⟨fun hp => hne ?_, heq⟩
    obtain ⟨h1, h2⟩ := Prod.mk.inj hp
    rw [h1, h2]

theorem BreakIsKeccakEvent : Properties.BreakIsKeccakEvent := by
  intro P tag S dec x f h
  unfold SourceBindingBreak KeccakEvent SentinelHit LoggedCommitClash
  constructor
  · rintro (h0 | ⟨o, ho, hcl⟩ | hb)
    · exact Or.inl h0
    · exact Or.inr (Or.inl ⟨o, ho,
        (CommitClashIsKeccakClash P.keccak tag ⟨f, h, P.chainId⟩ o).mp hcl⟩)
    · exact Or.inr (Or.inr hb)
  · rintro (h0 | ⟨o, ho, hcl⟩ | hb)
    · exact Or.inl h0
    · exact Or.inr (Or.inl ⟨o, ho,
        (CommitClashIsKeccakClash P.keccak tag ⟨f, h, P.chainId⟩ o).mpr hcl⟩)
    · exact Or.inr (Or.inr hb)

theorem AtomicSourceBoundOrKeccakEvent : Properties.AtomicSourceBoundOrKeccakEvent := by
  intro P tag S hr dec x f h hh hkey
  rcases AtomicSourceBoundOrBreak P _ S hr dec x f h hh hkey with hs | hb
  · exact Or.inl hs
  · exact Or.inr ((BreakIsKeccakEvent P tag S dec x f h).mp hb)

/-! ## At the gate -/

theorem GateBindsExecutingSourceOrBreak : Properties.GateBindsExecutingSourceOrBreak := by
  intro hN z0 hl cv fh Sys F ev leg hex center enc keccak dec x hleg S hr htree
  have hfin := hex.2.2 leg hex.1
  rcases Contracts.Atomicity.finality_means_membership_or_break hfin.2 with hmem | hbrk
  · rw [← htree] at hmem
    rcases AtomicSourceBoundOrBreak ⟨leg.chain, center, enc, keccak⟩ cv S hr dec x F.flowId
        leg.bundleHash hleg hmem with hs | hb
    · exact Or.inl hs
    · exact Or.inr (Or.inr hb)
  · exact Or.inr (Or.inl hbrk)

/-! ## Witness data

The honest chain is topic `Dispatch`'s `wParams`: chain `324`, the toy keccak `lastWord` (the last
32 bytes, as a word) and the toy encoder `saltWordsEncoder` (the bundle's two salt words). With
these, a bundle's hash is its user salt, whatever source chain the hash's first word carries, and
the deployed commit-value shape returns the bundle hash. -/

/-- The last word of `abi.encode(c, saltWords b)` is `b`'s user salt, for every first word `c`. -/
lemma lastWord_abiEncode_saltWords (c : ℕ) (b : Bundle) :
    lastWord (abiEncode c (saltWordsEncoder b)) = b.bundleAttributes.salt := by
  have hpad : pad32 (saltWordsEncoder b) = saltWordsEncoder b := by
    simp [pad32, saltWordsEncoder, length_toBytesBE]
  have hsplit : abiEncode c (saltWordsEncoder b)
      = (word c ++ (word 0x40 ++ (word (saltWordsEncoder b).length ++
          toBytesBE 32 b.interopBundleSalt.val))) ++ toBytesBE 32 b.bundleAttributes.salt.val := by
    rw [abiEncode, hpad]
    simp only [saltWordsEncoder, List.append_assoc]
  rw [hsplit, lastWord_append_word, ofNat_val]

/-- With the toy keccak and encoder, the handler's hash of a bundle's bytes is the bundle's user
salt, for every decoder. -/
lemma executedHash_saltWords (dec : List UInt8 → Bundle) (b : Bundle) :
    executedHash lastWord dec (saltWordsEncoder b) = b.bundleAttributes.salt :=
  lastWord_abiEncode_saltWords _ b

/-- …and so is the center's bundle hash, on every chain. -/
lemma bundleHash_saltWords (c : Word) (ctr : Address) (b : Bundle) :
    bundleHash ⟨c, ctr, saltWordsEncoder, lastWord⟩ b = b.bundleAttributes.salt :=
  lastWord_abiEncode_saltWords _ b

/-- The deployed commit-value shape over the toy keccak returns the bundle hash. -/
lemma deployedCommitValue_lastWord (tag : List UInt8) (f b : Word) :
    deployedCommitValue lastWord tag f b = b := by
  unfold deployedCommitValue commitPreimage
  rw [← List.append_assoc, lastWord_append_word, ofNat_val]

/-- A nonzero commit value is no sentinel hit. -/
lemma not_sentinelHit {cv : CommitValue} {f h : Word} (hne : cv f h ≠ 0) : ¬ SentinelHit cv f h :=
  hne

/-- Injectivity on a list is inherited by a list with no new elements. -/
lemma keccakInjOn_of_subset {k : List UInt8 → Word} {L L' : List (List UInt8)}
    (hL : KeccakInjOn k L) (hsub : ∀ x ∈ L', x ∈ L) : KeccakInjOn k L' :=
  fun x hx y hy hxy => hL x (hsub x hx) y (hsub y hy) hxy

/-- The honest run's validated atomic leg. -/
lemma wD1_validated : Validated wD1.bundle := by
  intro c hc
  simp only [wD1, wBundle, List.mem_singleton] at hc
  subst hc
  rfl

/-- A bundle declaring source chain `325`, with user salt `s`. -/
def sbForeign (s : Word) : Bundle := ⟨325, 324, 1, 0, [⟨5, 1, 0, []⟩], wAttrs s⟩

/-- The honest witness's commit value: the deployed shape, with the empty tag, over the toy
keccak. -/
abbrev sbCv : CommitValue := deployedCommitValue wParams.keccak []

lemma sbCv_wD1 : sbCv 7 (bundleHash wParams wD1.bundle) = 1 := by
  rw [show sbCv 7 (bundleHash wParams wD1.bundle) = bundleHash wParams wD1.bundle from
    deployedCommitValue_lastWord [] _ _, wHash1]

/-- The honest run with the tree attached: dispatch `wD1` (atomic, flow `7`), dispatch `wD2`
(public), authorize `wD1`'s leg. The centers are topic `Dispatch`'s `wS1`, `wS2`, `wS3`. -/
def sbS1 : SourceState :=
  ⟨wS1, Contracts.InteropCommitmentTree.insert setup (sbCv 7 (bundleHash wParams wD1.bundle)) 0⟩
def sbS2 : SourceState := ⟨wS2, sbS1.tree⟩
def sbS3 : SourceState := ⟨wS3, sbS1.tree⟩

theorem sbStep1 : SourceStep deployed wParams sbCv sourceGenesis sbS1 := by
  have happ : AppendSucceeds sbCv sourceGenesis.toChain wD1.atomicSend.flowId
      (bundleHash wParams wD1.bundle) 0 0 := by
    refine ⟨rfl, ?_⟩
    show InsertSucceeds setup (sbCv 7 (bundleHash wParams wD1.bundle)) 0 0
    rw [sbCv_wD1]
    exact ⟨by unfold Initialized; decide, by decide, rfl, by decide, by decide, by decide⟩
  exact SourceStep.sendAtomic wD1 0 0 rfl (fun _ => rfl) wD1_formed (fun _ => wD1_validated) happ

theorem sbStep2 : SourceStep deployed wParams sbCv sbS1 sbS2 := by
  refine SourceStep.sendPublic wD2 rfl (fun _ => ?_) wD2_formed
  simp [sbS1, wS1, State.afterSend, markSalt, init, wD1, wD2, Dispatch.salt, wBundle, wAttrs]

theorem sbStep3 : SourceStep deployed wParams sbCv sbS2 sbS3 := by
  refine SourceStep.authorize 7 (bundleHash wParams wD1.bundle) ?_
  show wS2.manager.legState 7 (bundleHash wParams wD1.bundle) = .Committed
  rw [wS2, afterSend_legState, ite_eq_right (by simp [wD2]), wS1_leg]

theorem sbReach : SourceReach deployed wParams sbCv sourceGenesis sbS3 :=
  .tail (.tail (.tail .refl sbStep1) sbStep2) sbStep3

lemma sbS3_log : sbS3.center.log = [wD1, wD2] := rfl

lemma sbS3_appendLog :
    appendLog wParams sbS3.center.log = [⟨7, bundleHash wParams wD1.bundle, 324⟩] := rfl

/-- The handler's preimage of `wD1`'s bytes is the center's. -/
lemma sb_preimage :
    executedPreimage wDec (wParams.enc wD1.bundle) = bundlePreimage wParams wD1.bundle :=
  wClaimPreimage

/-- On the honest run, with the presented bytes `wD1`'s own, no break holds. -/
lemma sb_no_break :
    ¬ SourceBindingBreak wParams sbCv sbS3 wDec (wParams.enc wD1.bundle) 7
      (bundleHash wParams wD1.bundle) := by
  rintro (hs | ⟨o, ho, hne, _⟩ | ⟨d, hd, hat, _, _, hne, _⟩)
  · have h1 : sbCv 7 (bundleHash wParams wD1.bundle) = 0 := hs
    rw [sbCv_wD1] at h1
    exact absurd h1 (by decide)
  · rw [sbS3_appendLog, List.mem_singleton] at ho
    subst ho
    exact hne rfl
  · rw [sbS3_log] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact hne sb_preimage
    · exact absurd hat (by decide)

theorem SourceBindingWitness : Properties.SourceBindingWitness := by
  have hh : executedHash wParams.keccak wDec (wParams.enc wD1.bundle)
      = bundleHash wParams wD1.bundle := congrArg wParams.keccak sb_preimage
  have hpos : (0 : Word) < sbCv 7 (bundleHash wParams wD1.bundle) := by
    rw [sbCv_wD1]; decide
  have hnb := sb_no_break
  refine ⟨wParams, [], sbS3, wDec, wParams.enc wD1.bundle, 7, bundleHash wParams wD1.bundle,
    sbReach, ClaimWitness.1, hh, Contracts.Atomicity.mem_insertSetup hpos, ne_of_gt hpos,
    ?_, ?_, (preimage_eq_bound sb_preimage).1, hnb,
    fun hk => hnb ((BreakIsKeccakEvent wParams [] sbS3 wDec _ 7 _).mpr hk),
    ⟨wD2, by rw [sbS3_log]; simp, rfl⟩, ⟨wD1, by rw [sbS3_log]; simp, rfl, rfl, ?_⟩⟩
  · rw [sbS3_appendLog]
    rintro o ho o' ho' ⟨hne, _⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho ho'
    rcases ho with rfl | rfl <;> rcases ho' with rfl | rfl <;> exact hne rfl
  · rw [sb_preimage]
    refine keccakInjOn_of_subset (keccakInjOn_pair (k := wParams.keccak)
      (x := bundlePreimage wParams wD1.bundle) (y := bundlePreimage wParams wD2.bundle) ?_) ?_
    · change bundleHash wParams wD1.bundle ≠ bundleHash wParams wD2.bundle
      rw [wHash1, wHash2]; decide
    · intro u hu
      have hl : bundlePreimages wParams sbS3.center.log
          = [bundlePreimage wParams wD1.bundle, bundlePreimage wParams wD2.bundle] := rfl
      rw [hl] at hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu ⊢
      rcases hu with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  · show (wS2.manager.set 7 (bundleHash wParams wD1.bundle) .Revertable).legState 7
      (bundleHash wParams wD1.bundle) = .Revertable
    simp

/-! ## Each break can hold alone -/

/-- A commit value that is `0` exactly on flow `9`: nonzero on the leg the run appends, the
sentinel on the presented one. -/
def stCv : CommitValue := fun f _ => if f = 9 then 0 else 1

/-- After `wD1` (flow `7`) under `stCv`. -/
def stS1 : SourceState :=
  ⟨wS1, Contracts.InteropCommitmentTree.insert setup (stCv 7 (bundleHash wParams wD1.bundle)) 0⟩

theorem SentinelBreakFires : Properties.SentinelBreakFires := by
  have hstep : SourceStep deployed wParams stCv sourceGenesis stS1 :=
    SourceStep.sendAtomic wD1 0 0 rfl (fun _ => rfl) wD1_formed (fun _ => wD1_validated)
      ⟨rfl, by unfold Initialized; decide, by decide, rfl, by decide, by decide, by decide⟩
  have hr : SourceReach deployed wParams stCv sourceGenesis stS1 := .tail .refl hstep
  have h0 : stCv 9 (executedHash wParams.keccak (fun _ => sbForeign 5) []) = 0 := by decide
  have hlog : appendLog wParams stS1.center.log = [⟨7, bundleHash wParams wD1.bundle, 324⟩] := rfl
  refine ⟨wParams, stCv, stS1, fun _ => sbForeign 5, [], 9,
    executedHash wParams.keccak (fun _ => sbForeign 5) [], hr, rfl,
    (SourceKeysAreDispatchedCommitValues wParams stCv stS1 hr _).mpr (Or.inl h0), by decide, h0,
    ?_, ?_⟩
  · rintro ⟨o, ho, _, heq⟩
    rw [hlog, List.mem_singleton] at ho
    subst ho
    exact absurd heq (by decide)
  · rintro ⟨d, hd, _, hf, _⟩
    have hd' : d = wD1 := by simpa [stS1, wS1, State.afterSend, init] using hd
    subst hd'
    exact absurd hf (by decide)

/-- After `wD1` under the constant commit value `1`. -/
def ccS1 : SourceState := ⟨wS1, Contracts.InteropCommitmentTree.insert setup 1 0⟩

theorem CommitClashBreakFires : Properties.CommitClashBreakFires := by
  have hstep : SourceStep deployed wParams (fun _ _ => 1) sourceGenesis ccS1 :=
    SourceStep.sendAtomic wD1 0 0 rfl (fun _ => rfl) wD1_formed (fun _ => wD1_validated)
      ⟨rfl, by unfold Initialized; decide, by decide, rfl, by decide, by decide, by decide⟩
  have hlog : appendLog wParams ccS1.center.log = [⟨7, bundleHash wParams wD1.bundle, 324⟩] := rfl
  refine ⟨wParams, fun _ _ => 1, ccS1, fun _ => sbForeign 5, saltWordsEncoder (sbForeign 5), 7, 5,
    .tail .refl hstep, executedHash_saltWords _ _, Contracts.Atomicity.mem_insertSetup (by decide),
    by decide, not_sentinelHit (by decide), ?_, ?_⟩
  · refine ⟨⟨7, bundleHash wParams wD1.bundle, 324⟩, by rw [hlog]; simp, ?_, rfl⟩
    rw [wHash1]
    decide
  · rintro ⟨d, hd, _, _, hb, _⟩
    have hd' : d = wD1 := by simpa [ccS1, wS1, State.afterSend, init] using hd
    subst hd'
    rw [wHash1] at hb
    exact absurd hb (by decide)

/-- After `collidingLeg` (topic `Dispatch`) under the constant keccak and the constant commit
value `1`. -/
def bcS1 : SourceState :=
  ⟨init.afterSend collidingParams collidingLeg, Contracts.InteropCommitmentTree.insert setup 1 0⟩

theorem BundleClashBreakFires : Properties.BundleClashBreakFires := by
  have hform : FormedBy collidingParams collidingLeg :=
    ⟨rfl, rfl, List.Forall₂.cons (formsCall_direct 1 0) List.Forall₂.nil⟩
  have hval : Validated collidingLeg.bundle := by
    intro c hc
    simp only [collidingLeg, wBundle, List.mem_singleton] at hc
    subst hc
    rfl
  have hstep : SourceStep deployed collidingParams (fun _ _ => 1) sourceGenesis bcS1 :=
    SourceStep.sendAtomic collidingLeg 0 0 rfl (fun _ => rfl) hform (fun _ => hval)
      ⟨rfl, by unfold Initialized; decide, by decide, rfl, by decide, by decide, by decide⟩
  have hlog : bcS1.center.log = [collidingLeg] := rfl
  refine ⟨collidingParams, fun _ _ => 1, bcS1, fun _ => sbForeign 5, [], 7, 0,
    .tail .refl hstep, rfl, Contracts.Atomicity.mem_insertSetup (by decide), by decide,
    not_sentinelHit (by decide), ?_, ?_⟩
  · rintro ⟨o, ho, hne, _⟩
    obtain ⟨d, hd, _, rfl⟩ := mem_appendLog.mp ho
    rw [hlog, List.mem_singleton] at hd
    subst hd
    exact hne rfl
  · refine ⟨collidingLeg, by rw [hlog]; simp, rfl, rfl, rfl, ?_, rfl⟩
    intro he
    exact absurd (preimage_eq_bound he).1 (by decide)

/-! ## Two honest chains, one commit value -/

/-- Chain `325`, with the toy keccak and encoder. -/
def sbParams325 : Params := ⟨325, 0x8010, saltWordsEncoder, lastWord⟩

/-- Sender `1`, salt `2`, on chain `325`: an atomic leg of flow `7`. -/
def sbDispatch325 : Dispatch :=
  ⟨1, [wDirect 0], wBundle sbParams325 1 2 [⟨5, 1, 0, []⟩], ⟨7, 0, 100, true⟩⟩

/-- After chain `325` dispatches it under the constant commit value `1`. -/
def sbState325 : SourceState :=
  ⟨init.afterSend sbParams325 sbDispatch325, Contracts.InteropCommitmentTree.insert setup 1 0⟩

theorem CommitValueOnlyInItsSourceTreeWitness :
    Properties.CommitValueOnlyInItsSourceTreeWitness := by
  have h324 : SourceStep deployed wParams (fun _ _ => 1) sourceGenesis ccS1 :=
    SourceStep.sendAtomic wD1 0 0 rfl (fun _ => rfl) wD1_formed (fun _ => wD1_validated)
      ⟨rfl, by unfold Initialized; decide, by decide, rfl, by decide, by decide, by decide⟩
  have hform : FormedBy sbParams325 sbDispatch325 :=
    ⟨rfl, rfl, List.Forall₂.cons (formsCall_direct 1 0) List.Forall₂.nil⟩
  have hval : Validated sbDispatch325.bundle := by
    intro c hc
    simp only [sbDispatch325, wBundle, List.mem_singleton] at hc
    subst hc
    rfl
  have h325 : SourceStep deployed sbParams325 (fun _ _ => 1) sourceGenesis sbState325 :=
    SourceStep.sendAtomic sbDispatch325 0 0 rfl (fun _ => rfl) hform (fun _ => hval)
      ⟨rfl, by unfold Initialized; decide, by decide, rfl, by decide, by decide, by decide⟩
  have hlog : appendLog ⟨325, 0x8010, saltWordsEncoder, lastWord⟩ sbState325.center.log
      = [⟨7, bundleHash sbParams325 sbDispatch325.bundle, 325⟩] := rfl
  refine ⟨lastWord, saltWordsEncoder, 0x8010, fun _ _ => 1, 324, 325, ccS1, sbState325, wD1,
    .tail .refl h324, .tail .refl h325, by simp [ccS1, wS1, State.afterSend, init], rfl,
    Contracts.Atomicity.mem_insertSetup (by decide), by decide, ?_⟩
  refine ⟨⟨7, bundleHash sbParams325 sbDispatch325.bundle, 325⟩, by rw [hlog]; simp, ?_, rfl⟩
  have h1 : bundleHash ⟨324, 0x8010, saltWordsEncoder, lastWord⟩ wD1.bundle = 1 :=
    bundleHash_saltWords _ _ _
  have h2 : bundleHash sbParams325 sbDispatch325.bundle = 2 := bundleHash_saltWords _ _ _
  rw [h1, h2]
  decide

/-! ## The countermodel: without `onlyInteropCenter` -/

/-- A foreign account appends the leg `(7, 5)` directly, with the commit value `fun _ b => b`. -/
def ucS1 : SourceState :=
  ⟨{ init with manager := init.manager.set 7 5 .Committed },
    Contracts.InteropCommitmentTree.insert setup 5 0⟩

theorem WithoutOnlyInteropCenterSourceUnbound :
    Properties.WithoutOnlyInteropCenterSourceUnbound := by
  have hstep : SourceStep withoutOnlyInteropCenter wParams (fun _ b => b) sourceGenesis ucS1 :=
    SourceStep.foreignAppend 1 7 5 0 0 (by decide) (fun h => absurd h (by decide))
      ⟨rfl, by unfold Initialized; decide, by decide, rfl, by decide, by decide, by decide⟩
  refine ⟨wParams, fun _ b => b, ucS1, fun _ => sbForeign 5, saltWordsEncoder (sbForeign 5), 7, 5,
    .tail .refl hstep, executedHash_saltWords _ _, Contracts.Atomicity.mem_insertSetup (by decide),
    by decide, ?_⟩
  rintro (hs | ⟨o, ho, _⟩ | ⟨d, hd, _⟩)
  · exact not_sentinelHit (by decide) hs
  · exact absurd ho (by simp [appendLog, ucS1, init])
  · exact absurd hd (by simp [ucS1, init])

/-! ## The gate form's witness -/

/-- Chain `0`, with the toy keccak and encoder. -/
def sbGateParams : Params := ⟨0, 0x8010, saltWordsEncoder, lastWord⟩

/-- Sender `1`, salt `1`, on chain `0`: the atomic leg of flow `0` (the leg of `subsetFlow 0 1`). -/
def sbGateDispatch : Dispatch :=
  ⟨1, [wDirect 0], wBundle sbGateParams 1 1 [⟨5, 1, 0, []⟩], ⟨0, 0, 100, true⟩⟩

/-- After chain `0` dispatches it under the constant commit value `1`. -/
def sbGateState : SourceState :=
  ⟨init.afterSend sbGateParams sbGateDispatch, Contracts.InteropCommitmentTree.insert setup 1 0⟩

theorem GateSourceBindingWitness : Properties.GateSourceBindingWitness := by
  intro hN z0 hl
  have h1 : (0 : UInt256) < 1 := by decide
  have hS : Wf (Contracts.Atomicity.mixedSystem 1) := Contracts.Atomicity.mixedSystem_wf h1
  have hcount : ((Contracts.Atomicity.mixedSystem 1).tree 0 0).leafCount = 2 := by
    rw [Contracts.Atomicity.mixedSystem_tree_zero]; rfl
  have hacc : Contracts.Atomicity.Accepts hN z0 hl (Contracts.Atomicity.mixedSystem 1) 0 0 1
      (Contracts.Atomicity.honestProof hN z0 hl (Contracts.Atomicity.mixedSystem 1) 0 0 1) := by
    have := Contracts.InteropCommitmentTree.inclusion_complete (h := hN) (z0 := z0) (hl := hl)
      (T := (Contracts.Atomicity.mixedSystem 1).tree 0 0)
      (height := (Contracts.Atomicity.mixedSystem 1).height 0 0) (hS.capacity 0 0) (i := 1)
      (by rw [hcount]; norm_num)
    have hv : (((Contracts.Atomicity.mixedSystem 1).tree 0 0).leaf 1).value = 1 := by
      rw [Contracts.Atomicity.mixedSystem_tree_zero, Contracts.Atomicity.insertSetup_leaf_one_value]
    rw [hv] at this
    exact this
  have hnb : ¬ InclusionBreak hN z0 hl (Contracts.Atomicity.mixedSystem 1) 0 0
      (Contracts.Atomicity.honestProof hN z0 hl (Contracts.Atomicity.mixedSystem 1) 0 0 1) :=
    Contracts.Atomicity.honestProof_no_break hN z0 hl _ 0 0 1 (by rw [hcount]; norm_num)
  have hex : ExecutedViaBy hN z0 hl (fun _ _ => 1)
      (Contracts.Atomicity.honestFlowHash (Contracts.Atomicity.subsetFlow 0 1))
      (Contracts.Atomicity.mixedSystem 1) (Contracts.Atomicity.subsetFlow 0 1)
      (fun _ => (0, Contracts.Atomicity.honestProof hN z0 hl (Contracts.Atomicity.mixedSystem 1)
        0 0 1)) ⟨0, 1⟩ := by
    refine ⟨List.mem_singleton_self _,
      (Contracts.Atomicity.honest_flowHash_no_clash (Contracts.Atomicity.subsetFlow 0 1)).1, ?_⟩
    intro l hl'
    obtain rfl : l = ⟨0, 1⟩ := List.mem_singleton.mp hl'
    exact ⟨by simp [Contracts.Atomicity.subsetFlow], hacc⟩
  have hform : FormedBy sbGateParams sbGateDispatch :=
    ⟨rfl, rfl, List.Forall₂.cons (formsCall_direct 1 0) List.Forall₂.nil⟩
  have hval : Validated sbGateDispatch.bundle := by
    intro c hc
    simp only [sbGateDispatch, wBundle, List.mem_singleton] at hc
    subst hc
    rfl
  have hstep : SourceStep deployed sbGateParams (fun _ _ => 1) sourceGenesis sbGateState :=
    SourceStep.sendAtomic sbGateDispatch 0 0 rfl (fun _ => rfl) hform (fun _ => hval)
      ⟨rfl, by unfold Initialized; decide, by decide, rfl, by decide, by decide, by decide⟩
  refine ⟨fun _ _ => 1, _, Contracts.Atomicity.mixedSystem 1, Contracts.Atomicity.subsetFlow 0 1,
    _, ⟨0, 1⟩, 0x8010, saltWordsEncoder, lastWord, fun _ => sbGateDispatch.bundle,
    saltWordsEncoder sbGateDispatch.bundle, sbGateState, hS, hex, executedHash_saltWords _ _,
    .tail .refl hstep, by simp [sbGateState], rfl, hnb, ?_⟩
  rintro (hs | ⟨o, ho, hne, _⟩ | ⟨d, hd, _, _, _, hne, _⟩)
  · exact not_sentinelHit (by decide) hs
  · obtain ⟨d, hd, _, rfl⟩ := mem_appendLog.mp ho
    have hd' : d = sbGateDispatch := by simpa [sbGateState, State.afterSend, init] using hd
    subst hd'
    apply hne
    simp only [dispatchObligation, bundleHash_saltWords]
    rfl
  · have hd' : d = sbGateDispatch := by simpa [sbGateState, State.afterSend, init] using hd
    subst hd'
    exact hne rfl

end Contracts.SourceBinding
