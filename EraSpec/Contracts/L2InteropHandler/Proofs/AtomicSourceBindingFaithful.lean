import EraSpec.Contracts.L2InteropHandler.Properties.AtomicSourceBindingFaithful
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashPinned
import EraSpec.Contracts.InteropCenter.Proofs.Dispatch

/-!
# Proofs: the atomic path's source binding, over `executeAtomicBundle`

The headline is one case split on the two keccak preimages, after the gate has been read.

* The gate gives the vouching leg's accepted proof, naming chain `c` (`legs`, `executingIsLeg`).
* Honest vouching turns the accepted value into a logged leg `e` of chain `c` with the same commit
  value.
* Equal commit values: the two commit preimages differ (a `CommitPreimageClash`), or they are
  equal, and then they carry the same flow id and the same bundle hash (`commitPreimage_inj`: three
  fixed words).
* Equal bundle hashes: the two bundle-hash preimages differ (a `BundlePreimageClash`), or they are
  equal, and then their leading words agree (`chain_eq_of_abiEncode_eq`): the declared chain is `c`.
* `_executeCalls` hands every call the declared chain (`deliveries_sourceChainId`).

The witnesses build one-leg flows whose flow id is the keccak of their own preimage, with the ideal
verifier on a one-value tree.
-/

namespace Contracts.L2InteropHandler.AtomicSourceFaithful

open AttackVectors.BundleHashEncoding
open Contracts.InteropCenter (Address Bundle)

/-! ## Byte-level facts -/

theorem commitTagWord_length (keccak : List UInt8 → UInt256) : (commitTagWord keccak).length = 32 := by
  simp [commitTagWord]

theorem commitPreimage_length (keccak : List UInt8 → UInt256) (f h : UInt256) :
    (commitPreimage keccak f h).length = 96 := by
  simp [commitPreimage, commitTagWord_length]

/-- **THE COMMIT PREIMAGE DETERMINES ITS FLOW ID AND BUNDLE HASH.** It is three fixed words with a
common first word. -/
theorem commitPreimage_inj {keccak : List UInt8 → UInt256} {f h f' h' : UInt256}
    (hE : commitPreimage keccak f h = commitPreimage keccak f' h') : f = f' ∧ h = h' := by
  have h2 : word f.val ++ word h.val = word f'.val ++ word h'.val := List.append_cancel_left hE
  obtain ⟨hf, hh⟩ := List.append_inj h2 (by rw [word_length, word_length])
  exact ⟨word_val_inj hf, word_val_inj hh⟩

/-- **THE CORE CASE SPLIT.** If the executing leg's commit value is the commit value of a logged leg
`e` of chain `c`, then the declared chain is `c` and the two preimages agree, or one of the two
named preimage pairs collides. -/
theorem binding_core (keccak : List UInt8 → UInt256) (flowId c : UInt256) (B : List UInt8)
    (b : Bundle) (e : CommittedLeg)
    (hv : commitValue keccak flowId (keccak (executedPreimage B b)) = e.value keccak c) :
    (b.sourceChainId = c ∧ e.flowId = flowId ∧ executedPreimage B b = e.preimage c)
      ∨ CommitPreimageClash keccak flowId (keccak (executedPreimage B b)) c e
      ∨ BundlePreimageClash keccak B b c e := by
  by_cases hcp : commitPreimage keccak flowId (keccak (executedPreimage B b)) =
      commitPreimage keccak e.flowId (e.bundleHash keccak c)
  · obtain ⟨hf, hh⟩ := commitPreimage_inj hcp
    by_cases hbp : executedPreimage B b = e.preimage c
    · exact Or.inl ⟨Fin.ext (chain_eq_of_abiEncode_eq (uint256_val_lt _) (uint256_val_lt _) hbp),
        hf.symm, hbp⟩
    · exact Or.inr (Or.inr ⟨hbp, hh⟩)
  · exact Or.inr (Or.inl ⟨hcp, hv⟩)

/-! ## The three links -/

theorem lt_length_of_getElem?_eq_some {α : Type} {l : List α} {i : ℕ} {a : α}
    (h : l[i]? = some a) : i < l.length :=
  (List.getElem?_eq_some_iff.mp h).1

theorem AtomicExecutionLocatesVouchingLeg : Properties.AtomicExecutionLocatesVouchingLeg := by
  intro D st st' caller B fin b ds hx
  have hg := hx.checks.gate
  obtain ⟨i, hi⟩ := hg.executingIsLeg
  have hlt := lt_length_of_getElem?_eq_some hi
  have hlc : i < fin.flow.legSourceChainIds.length := by rw [hg.chainsLength]; exact hlt
  have hlp : i < fin.proofs.length := by rw [hg.proofCount]; exact hlt
  have hleg : LegAt fin i (executedHash D B b) fin.flow.legSourceChainIds[i] fin.proofs[i] :=
    ⟨hi, List.getElem?_eq_getElem hlc, List.getElem?_eq_getElem hlp⟩
  exact ⟨i, _, _, hleg, hg.legs i _ _ _ hleg⟩

theorem VouchingLegUnique : Properties.VouchingLegUnique := by
  intro D h fin hg i j c c' p p' hi hj
  have hnd : fin.flow.legBundleHashes.Nodup := hg.sorted.pairwise.nodup
  have hij : i = j :=
    (hnd.getElem?_inj (lt_length_of_getElem?_eq_some hi.1)).mp (hi.1.trans hj.1.symm)
  subst hij
  exact ⟨rfl, Option.some.inj (hi.2.1.symm.trans hj.2.1),
    Option.some.inj (hi.2.2.symm.trans hj.2.2)⟩

theorem deliveries_length (D : Dest) (h : UInt256) (b : Bundle) :
    (deliveries D h b).length = b.calls.length := by
  simp [deliveries]

theorem deliveries_sourceChainId (D : Dest) (h : UInt256) (b : Bundle) :
    ∀ d ∈ deliveries D h b, d.sourceChainId = b.sourceChainId := by
  intro d hd
  obtain ⟨ci, -, rfl⟩ := List.mem_map.mp hd
  rfl

theorem DeliveriesCarryDeclaredSource : Properties.DeliveriesCarryDeclaredSource := by
  intro D st st' caller B fin b ds hx
  rw [hx.delivered]
  exact ⟨deliveries_length D _ b, deliveries_sourceChainId D _ b⟩

theorem AtomicPathSourceCheckVacuous : Properties.AtomicPathSourceCheckVacuous := by
  intro D b
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem PublicPathSourceCheckBinds : Properties.PublicPathSourceCheckBinds := by
  intro D b proofChainId h
  exact h.1

theorem DeclaredSourceSeenOnlyThroughHash : Properties.DeclaredSourceSeenOnlyThroughHash := by
  intro D st caller fin B B' b s' hx hne hdec hhash
  refine
    { nonEmpty := hne
      decoded := hdec
      context := ⟨rfl, hx.context.2.1, hx.context.2.2⟩
      permitted := hx.permitted
      fresh := ?_
      gate := ?_ }
  · rw [hhash]
    exact hx.fresh
  · rw [hhash]
    exact hx.gate

/-! ## The headline -/

theorem AtomicSenderIsVouchingChainOrLoggedClash :
    Properties.AtomicSenderIsVouchingChainOrLoggedClash := by
  intro D st st' caller B fin b ds hx i c p hleg log hhon
  obtain ⟨hpc, hver⟩ := hx.checks.gate.legs i _ c p hleg
  obtain ⟨e, he, hv⟩ := hhon p _ _ _ hpc hver
  refine ⟨e, he, ?_⟩
  rcases binding_core D.keccak fin.flow.flowId c B b e hv with ⟨hs, hf, hpre⟩ | hcl | hcl
  · refine Or.inl ⟨hs, fun d hd => ?_, hf, hpre⟩
    rw [hx.delivered] at hd
    rw [deliveries_sourceChainId D _ b d hd, hs]
  · exact Or.inr (Or.inl hcl)
  · exact Or.inr (Or.inr hcl)

theorem AtomicExecutesCommittedBytesOrLoggedClash :
    Properties.AtomicExecutesCommittedBytesOrLoggedClash := by
  intro D st st' caller B fin b ds hx i c p hleg log hhon hB hlog
  obtain ⟨e, he, h⟩ :=
    AtomicSenderIsVouchingChainOrLoggedClash D st st' caller B fin b ds hx i c p hleg log hhon
  refine ⟨e, he, ?_⟩
  rcases h with ⟨hs, hds, hf, hpre⟩ | hcl | hcl
  · have hbytes := abiEncode_inj (uint256_val_lt b.sourceChainId) hB (uint256_val_lt c)
      (hlog e he) hpre
    exact Or.inl ⟨hs, hds, hf, hbytes.2⟩
  · exact Or.inr (Or.inl hcl)
  · exact Or.inr (Or.inr hcl)

theorem AtomicSenderIsVouchingChainOn : Properties.AtomicSenderIsVouchingChainOn := by
  intro D st st' caller B fin b ds hx i c p hleg log hhon hcom hbun
  obtain ⟨e, he, h⟩ :=
    AtomicSenderIsVouchingChainOrLoggedClash D st st' caller B fin b ds hx i c p hleg log hhon
  rcases h with ⟨hs, hds, -, -⟩ | hcl | hcl
  · exact ⟨hs, hds⟩
  · exact absurd hcl ((injOn_pair_iff_no_collision _ _ _).mp (hcom e he))
  · exact absurd hcl ((injOn_pair_iff_no_collision _ _ _).mp (hbun e he))

theorem HonestVouchingOfSoundVerifier : Properties.HonestVouchingOfSoundVerifier := by
  intro D tree c log hsound htree p v deadline sl hpc hver
  exact htree v (hsound p v deadline sl hpc hver)

theorem IdealVerifierSound : Properties.IdealVerifierSound := by
  intro D tree c hD p v deadline sl hpc hver
  rw [hD] at hver
  simpa [idealVerifier, hpc] using hver

/-! ## The register -/

theorem DeclaredOfHashForcesBundleBlindHash : Properties.DeclaredOfHashForcesBundleBlindHash := by
  intro keccak declared hdecl s B B'
  let g : UInt256 → UInt256 := fun t => keccak (abiEncode t.val [])
  have hg : Function.Injective g := fun t t' htt' => by
    have h1 := hdecl t []
    have h2 := hdecl t' []
    have h3 : declared (g t) = declared (g t') := congrArg declared htt'
    simp only [g] at h3
    rw [h1, h2] at h3
    exact h3
  have hsurj : Function.Surjective g := Finite.surjective_of_injective hg
  have key : ∀ X : List UInt8, keccak (abiEncode s.val X) = g s := by
    intro X
    obtain ⟨t, ht⟩ := hsurj (keccak (abiEncode s.val X))
    have h1 : declared (g t) = t := hdecl t []
    rw [ht, hdecl s X] at h1
    rw [← ht, h1]
  rw [key B, key B']

/-! ## Witness data

One-leg flows. The flow id is the keccak of the flow's own preimage, so `_checkFlowId` passes for
every keccak. The verifier is the ideal one on a tree that holds one value, on the leg's declared
chain only. Every witness is proved for an arbitrary keccak (or for a keccak given only through the
equations the argument needs) and instantiated at the end, so no proof evaluates a hash. -/

/-- The witnesses' bundle: declared source `s`, destination `325`, base token `1`, one zero-value
call from `1` to `5`, no execution address. -/
def wsBundle (s : UInt256) : Bundle := ⟨s, 325, 1, 0, [⟨5, 1, 0, []⟩], ⟨[], [1], false, 0⟩⟩

/-- The one-leg flow of bundle hash `h` declared on chain `c`; its id is the keccak of its own
preimage, which does not read the id. -/
def wsFlow (keccak : List UInt8 → UInt256) (h c : UInt256) : AtomicFlow where
  flowId := keccak (flowIdPreimage ⟨0, 100, 1, [h], [c]⟩)
  deadline := 100
  settlementLayerChainId := 1
  legBundleHashes := [h]
  legSourceChainIds := [c]

/-- Its finality proof: one proof, naming chain `c`, with an empty payload. -/
def wsFin (keccak : List UInt8 → UInt256) (h c : UInt256) : AtomicFinalityProof :=
  ⟨wsFlow keccak h c, [⟨c, []⟩]⟩

/-- The tree holding exactly `v`, on chain `c` only. -/
def wsTree (c v : UInt256) : UInt256 → Set UInt256 := fun c' => {x | c' = c ∧ x = v}

/-- A destination on chain `325` (base token `1`, L1 `1`) that decodes the bytes `B` to `b` and
nothing else, and whose verifier accepts exactly the members of `tree`. -/
def wsDest (keccak : List UInt8 → UInt256) (B : List UInt8) (b : Bundle)
    (tree : UInt256 → Set UInt256) : Dest where
  keccak := keccak
  chainId := 325
  self := 0x8010
  baseTokenAssetId := 1
  l1ChainId := 1
  decode := fun x => if x = B then some b else none
  parseEvmV1 := fun _ => none
  verifyInclusion := idealVerifier tree

/-- Fresh handler storage. -/
def wsSt : HandlerState := ⟨fun _ => .Unreceived⟩

/-- The executed bundle hash of bytes `B` declaring `s`. -/
def wsHash (keccak : List UInt8 → UInt256) (B : List UInt8) (s : UInt256) : UInt256 :=
  keccak (abiEncode s.val B)

/-- The executing leg's commit value, for bytes `B` declaring `s` and a leg declared on `c`. -/
def wsValue (keccak : List UInt8 → UInt256) (B : List UInt8) (s c : UInt256) : UInt256 :=
  commitValue keccak (wsFlow keccak (wsHash keccak B s) c).flowId (wsHash keccak B s)

theorem singleton_getElem?_eq_some {α : Type} {x y : α} {i : ℕ} (h : [x][i]? = some y) :
    i = 0 ∧ x = y := by
  rcases i with _ | i
  · exact ⟨rfl, Option.some.inj h⟩
  · simp at h

/-- The gate accepts a one-leg flow whose leg's value is in its declared chain's tree. -/
theorem ws_gate (D : Dest) (h c : UInt256) (tree : UInt256 → Set UInt256) (hl1 : D.l1ChainId = 1)
    (hver : D.verifyInclusion = idealVerifier tree)
    (hmem : commitValue D.keccak (wsFlow D.keccak h c).flowId h ∈ tree c) :
    FlowGateAccepts D h (wsFin D.keccak h c) where
  sorted := List.IsChain.singleton _
  chainsLength := rfl
  flowId := rfl
  settlementLayer := hl1.symm
  proofCount := rfl
  legs := by
    intro i bh c' p hleg
    obtain ⟨h1, h2, h3⟩ := hleg
    obtain ⟨rfl, rfl⟩ := singleton_getElem?_eq_some h1
    obtain ⟨-, rfl⟩ := singleton_getElem?_eq_some h2
    obtain ⟨-, rfl⟩ := singleton_getElem?_eq_some h3
    refine ⟨rfl, ?_⟩
    rw [hver]
    exact hmem
  executingIsLeg := ⟨0, rfl⟩

theorem ws_decode (keccak : List UInt8 → UInt256) (B : List UInt8) (b : Bundle)
    (tree : UInt256 → Set UInt256) : (wsDest keccak B b tree).decode B = some b := by
  show (if B = B then some b else none) = some b
  exact ite_eq_left rfl

/-- The witness execution: bytes `B` decoding to a bundle `b` addressed to chain `325` with base
token `1` and no execution address, under a one-leg flow declared on chain `c`. -/
theorem ws_executes (keccak : List UInt8 → UInt256) (B : List UInt8) (hB : B ≠ []) (b : Bundle)
    (c : UInt256) (tree : UInt256 → Set UInt256)
    (hdst : b.destinationChainId = 325) (hbase : b.destinationBaseTokenAssetId = 1)
    (hexec : b.bundleAttributes.executionAddress = [])
    (hmem : commitValue keccak (wsFlow keccak (wsHash keccak B b.sourceChainId) c).flowId
      (wsHash keccak B b.sourceChainId) ∈ tree c) :
    ExecutesAtomic (wsDest keccak B b tree) wsSt 0 B (wsFin keccak (wsHash keccak B b.sourceChainId) c)
      b (wsSt.markExecuted (wsHash keccak B b.sourceChainId))
      (deliveries (wsDest keccak B b tree) (wsHash keccak B b.sourceChainId) b) where
  checks :=
    { nonEmpty := hB
      decoded := ws_decode keccak B b tree
      context := ⟨rfl, hdst, hbase⟩
      permitted := Or.inl hexec
      fresh := rfl
      gate := ws_gate (wsDest keccak B b tree) (wsHash keccak B b.sourceChainId) c tree rfl rfl hmem }
  marked := rfl
  delivered := rfl

theorem ws_leg (keccak : List UInt8 → UInt256) (h c : UInt256) :
    LegAt (wsFin keccak h c) 0 h c ⟨c, []⟩ :=
  ⟨rfl, rfl, rfl⟩

theorem deliveries_ne_nil (D : Dest) (h : UInt256) {b : Bundle} (hb : b.calls ≠ []) :
    deliveries D h b ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [deliveries_length]
  exact List.length_pos_of_ne_nil hb

theorem wsBundle_calls_ne_nil (s : UInt256) : (wsBundle s).calls ≠ [] := by
  simp [wsBundle]

theorem ws_tree_mem {c v x c' : UInt256} (h : x ∈ wsTree c v c') : c' = c ∧ x = v := h

/-- The two witness byte strings. -/
abbrev wsB₁ : List UInt8 := [1]
abbrev wsB₂ : List UInt8 := [2]

theorem abiEncode_chain_ne {s c : UInt256} {B B' : List UInt8} (hsc : s ≠ c) :
    abiEncode s.val B ≠ abiEncode c.val B' := fun hE =>
  hsc (Fin.ext (chain_eq_of_abiEncode_eq (uint256_val_lt _) (uint256_val_lt _) hE))

/-! ## Witnesses and countermodels -/

theorem AtomicSourceBoundWitness : Properties.AtomicSourceBoundWitness := by
  intro keccak
  let c : UInt256 := 324
  let e : CommittedLeg := ⟨(wsFlow keccak (wsHash keccak wsB₁ c) c).flowId, wsB₁⟩
  let D := wsDest keccak wsB₁ (wsBundle c) (wsTree c (wsValue keccak wsB₁ c c))
  have hcom : ¬ CommitPreimageClash keccak (wsFin keccak (wsHash keccak wsB₁ c) c).flow.flowId
      (executedHash D wsB₁ (wsBundle c)) c e := fun hcl => hcl.1 rfl
  have hbun : ¬ BundlePreimageClash keccak wsB₁ (wsBundle c) c e := fun hcl => hcl.1 rfl
  refine ⟨D, wsSt, _, 0, wsB₁, _, wsBundle c, _, c, ⟨c, []⟩, e, rfl,
    ws_executes keccak wsB₁ (by simp) (wsBundle c) c _ rfl rfl rfl ⟨rfl, rfl⟩, ws_leg keccak _ c,
    ?_, hcom, hbun, (injOn_pair_iff_no_collision _ _ _).mpr hcom,
    (injOn_pair_iff_no_collision _ _ _).mpr hbun, deliveries_ne_nil _ _ (wsBundle_calls_ne_nil c),
    rfl, deliveries_sourceChainId _ _ _⟩
  intro p v deadline sl _ hver
  exact ⟨e, List.mem_singleton_self e, (ws_tree_mem hver).2⟩

theorem MisbehavingLegChainImpersonates : Properties.MisbehavingLegChainImpersonates := by
  intro keccak s c hsc
  let D := wsDest keccak wsB₁ (wsBundle s) (wsTree c (wsValue keccak wsB₁ s c))
  have hx := ws_executes keccak wsB₁ (by simp) (wsBundle s) c (wsTree c (wsValue keccak wsB₁ s c))
    rfl rfl rfl ⟨rfl, rfl⟩
  refine ⟨D, wsSt, _, 0, wsB₁, _, wsBundle s, _, ⟨c, []⟩, rfl, hx, ws_leg keccak _ c, rfl, rfl,
    deliveries_ne_nil _ _ (wsBundle_calls_ne_nil s), deliveries_sourceChainId _ _ _, ?_, ?_⟩
  · intro q v deadline sl hq hver
    exact hsc (hq.symm.trans (ws_tree_mem hver).1)
  · intro log hhon
    obtain ⟨e, he, h⟩ := AtomicSenderIsVouchingChainOrLoggedClash D wsSt _ 0 wsB₁ _ (wsBundle s) _
      hx 0 c ⟨c, []⟩ (ws_leg keccak _ c) log hhon
    rcases h with ⟨hs, -⟩ | hcl | hcl
    · exact absurd hs hsc
    · exact ⟨e, he, Or.inl hcl⟩
    · exact ⟨e, he, Or.inr hcl⟩

/-- The bundle-hash clash, for any keccak that collides on the two named bundle-hash preimages:
bytes `B` declaring `s` and bytes `B'` committed by `c`. -/
theorem bundlePreimageClashFires_of (keccak : List UInt8 → UInt256) (s c : UInt256)
    (B B' : List UInt8) (hsc : s ≠ c) (hB : B ≠ [])
    (hcol : keccak (abiEncode s.val B) = keccak (abiEncode c.val B')) :
    Properties.BundlePreimageClashFires := by
  let e : CommittedLeg := ⟨(wsFlow keccak (wsHash keccak B s) c).flowId, B'⟩
  have hval : commitValue keccak (wsFlow keccak (wsHash keccak B (wsBundle s).sourceChainId) c).flowId
      (wsHash keccak B (wsBundle s).sourceChainId) ∈ wsTree c (e.value keccak c) c :=
    ⟨rfl, congrArg (commitValue keccak _) hcol⟩
  refine ⟨wsDest keccak B (wsBundle s) (wsTree c (e.value keccak c)), wsSt, _, 0, B, _, wsBundle s,
    _, c, ⟨c, []⟩, e, ws_executes keccak B hB (wsBundle s) c _ rfl rfl rfl hval,
    ws_leg keccak _ c, ?_, hsc, deliveries_ne_nil _ _ (wsBundle_calls_ne_nil s), ?_, ?_,
    ⟨abiEncode_chain_ne hsc, hcol⟩⟩
  · intro p v deadline sl _ hver
    exact ⟨e, List.mem_singleton_self e, (ws_tree_mem hver).2⟩
  · intro d hd
    rw [deliveries_sourceChainId _ _ _ d hd]
    exact hsc
  · rintro ⟨hne, -⟩
    exact hne (congrArg (commitPreimage keccak _) hcol)

/-- The constant keccak. -/
def zeroKeccak : List UInt8 → UInt256 := fun _ => 0

theorem zeroKeccak_apply (x : List UInt8) : zeroKeccak x = 0 := rfl

theorem BundlePreimageClashFires : Properties.BundlePreimageClashFires :=
  bundlePreimageClashFires_of zeroKeccak 1 2 wsB₂ wsB₁ (by decide) (by simp)
    ((zeroKeccak_apply _).trans (zeroKeccak_apply _).symm)

/-- The commit-value clash, for any keccak that maps every commit preimage to `0` and reads the
declared chain back from the two named bundle-hash preimages. -/
theorem commitPreimageClashFires_of (keccak : List UInt8 → UInt256) (s c : UInt256)
    (B B' : List UInt8) (hsc : s ≠ c) (hB : B ≠ [])
    (hs : keccak (abiEncode s.val B) = s) (hc : keccak (abiEncode c.val B') = c)
    (hcv : ∀ f h : UInt256, keccak (commitPreimage keccak f h) = 0) :
    Properties.CommitPreimageClashFires := by
  let e : CommittedLeg := ⟨(wsFlow keccak (wsHash keccak B s) c).flowId, B'⟩
  have hval : commitValue keccak (wsFlow keccak (wsHash keccak B (wsBundle s).sourceChainId) c).flowId
      (wsHash keccak B (wsBundle s).sourceChainId) ∈ wsTree c (e.value keccak c) c :=
    ⟨rfl, (hcv _ _).trans (hcv _ _).symm⟩
  refine ⟨wsDest keccak B (wsBundle s) (wsTree c (e.value keccak c)), wsSt, _, 0, B, _, wsBundle s,
    _, c, ⟨c, []⟩, e, ws_executes keccak B hB (wsBundle s) c _ rfl rfl rfl hval,
    ws_leg keccak _ c, ?_, hsc, deliveries_ne_nil _ _ (wsBundle_calls_ne_nil s), ?_,
    ⟨?_, (hcv _ _).trans (hcv _ _).symm⟩, ?_⟩
  · intro p v deadline sl _ hver
    exact ⟨e, List.mem_singleton_self e, (ws_tree_mem hver).2⟩
  · intro d hd
    rw [deliveries_sourceChainId _ _ _ d hd]
    exact hsc
  · intro hE
    have hh : keccak (abiEncode s.val B) = keccak (abiEncode c.val B') := (commitPreimage_inj hE).2
    exact hsc (hs.symm.trans (hh.trans hc))
  · rintro ⟨-, hk⟩
    have hk' : keccak (abiEncode s.val B) = keccak (abiEncode c.val B') := hk
    exact hsc (hs.symm.trans (hk'.trans hc))

/-- A keccak that maps every 96-byte input (every commit preimage) to `0` and reads any other
input's leading word. -/
def commitBlindKeccak (x : List UInt8) : UInt256 :=
  if x.length = 96 then 0 else Nat.toUInt256 (fromBytesBE (x.take 32))

theorem abiEncode_length_ne_96 (c : ℕ) {B : List UInt8} (hB : B ≠ []) :
    (abiEncode c B).length ≠ 96 := by
  have hpos : 0 < B.length := List.length_pos_of_ne_nil hB
  simp [abiEncode, pad32]
  omega

theorem commitBlindKeccak_abiEncode (c : UInt256) {B : List UInt8} (hB : B ≠ []) :
    commitBlindKeccak (abiEncode c.val B) = c := by
  rw [commitBlindKeccak, ite_eq_right (abiEncode_length_ne_96 c.val hB), abiEncode_take32,
    fromBytesBE_toBytesBE (uint256_val_lt c), toUInt256_val]

theorem commitBlindKeccak_commitPreimage (k : List UInt8 → UInt256) (f h : UInt256) :
    commitBlindKeccak (commitPreimage k f h) = 0 := by
  rw [commitBlindKeccak, ite_eq_left (commitPreimage_length k f h)]

theorem CommitPreimageClashFires : Properties.CommitPreimageClashFires :=
  commitPreimageClashFires_of commitBlindKeccak 1 2 wsB₂ wsB₁ (by decide) (by simp)
    (commitBlindKeccak_abiEncode 1 (by simp)) (commitBlindKeccak_abiEncode 2 (by simp))
    (commitBlindKeccak_commitPreimage commitBlindKeccak)

/-! ## The vouching chain's run -/

theorem dispatchLeg_value (D : Dest) (P : Contracts.InteropCenter.Params) (hk : P.keccak = D.keccak)
    (d : Contracts.InteropCenter.Dispatch) :
    (⟨d.atomicSend.flowId, P.enc d.bundle⟩ : CommittedLeg).value D.keccak P.chainId =
      commitValue D.keccak d.atomicSend.flowId (Contracts.InteropCenter.bundleHash P d.bundle) := by
  show commitValue D.keccak _ (D.keccak (abiEncode P.chainId.val (P.enc d.bundle))) =
    commitValue D.keccak _ (P.keccak (abiEncode P.chainId.val (P.enc d.bundle)))
  rw [hk]

/-- An accepted value on the vouching chain comes from an atomic dispatch of its run. -/
theorem accepted_of_dispatch {D : Dest} {P : Contracts.InteropCenter.Params}
    {S : Contracts.InteropCenter.State}
    (hr : Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed P
      Contracts.InteropCenter.init S)
    (hk : P.keccak = D.keccak) (hacc : AcceptsOnlyCommittedLegs D P S)
    {p : ImtProof} {v deadline sl : UInt256} (hpc : p.sourceChainId = P.chainId)
    (hver : D.verifyInclusion p v deadline sl) :
    ∃ d ∈ S.log, d.isAtomic = true ∧ Contracts.InteropCenter.Validated d.bundle ∧
      d.bundle.sourceChainId = P.chainId ∧
      v = (⟨d.atomicSend.flowId, P.enc d.bundle⟩ : CommittedLeg).value D.keccak P.chainId := by
  obtain ⟨f, h, hne, hv⟩ := hacc p v deadline sl hpc hver
  obtain ⟨d, hd, hat, hf, hh, hval, hsrc⟩ :=
    Contracts.InteropCenter.CommittedLegsAreValidatedDispatches P S hr f h hne
  refine ⟨d, hd, hat, hval, hsrc, ?_⟩
  rw [dispatchLeg_value D P hk d, hf, hh]
  exact hv

theorem DispatchRunVouchesHonestly : Properties.DispatchRunVouchesHonestly := by
  intro D P S hr hk hacc p v deadline sl hpc hver
  obtain ⟨d, hd, hat, -, -, hv⟩ := accepted_of_dispatch hr hk hacc hpc hver
  exact ⟨_, List.mem_map.mpr ⟨d, List.mem_filter.mpr ⟨hd, hat⟩, rfl⟩, hv⟩

theorem AtomicExecutionRunsADispatchedBundleOrLoggedClash :
    Properties.AtomicExecutionRunsADispatchedBundleOrLoggedClash := by
  intro D P S hr hk hacc st st' caller B fin b ds hx i p hleg
  obtain ⟨hpc, hver⟩ := hx.checks.gate.legs i _ P.chainId p hleg
  obtain ⟨d, hd, hat, hval, hsrc, hv⟩ := accepted_of_dispatch hr hk hacc hpc hver
  refine ⟨d, hd, hat, hval, hsrc, ?_⟩
  rcases binding_core D.keccak fin.flow.flowId P.chainId B b _ hv with ⟨hs, hf, hpre⟩ | hcl | hcl
  · refine Or.inl ⟨hs, fun x hxd => ?_, hf, hpre⟩
    rw [hx.delivered] at hxd
    rw [deliveries_sourceChainId D _ b x hxd, hs]
  · exact Or.inr (Or.inl hcl)
  · exact Or.inr (Or.inr hcl)

theorem AtomicExecutionRunsTheDispatchedBundleOrLoggedClash :
    Properties.AtomicExecutionRunsTheDispatchedBundleOrLoggedClash := by
  intro D P S hr hk hacc hdec hlen st st' caller B fin b ds hx hB i p hleg
  obtain ⟨d, hd, hat, hval, -, h⟩ :=
    AtomicExecutionRunsADispatchedBundleOrLoggedClash D P S hr hk hacc st st' caller B fin b ds hx
      i p hleg
  refine ⟨d, hd, hat, ?_⟩
  rcases h with ⟨hs, hds, hf, hpre⟩ | hcl | hcl
  · have hbytes := abiEncode_inj (uint256_val_lt _) hB (uint256_val_lt _) (hlen d hd) hpre
    have hb : b = d.bundle := by
      have h1 := hx.checks.decoded
      rw [hbytes.2, hdec d hd] at h1
      exact (Option.some.inj h1).symm
    refine Or.inl ⟨hb, hbytes.2, hf, ?_, hs, hds⟩
    rw [hb]
    exact hval
  · exact Or.inr (Or.inl hcl)
  · exact Or.inr (Or.inr hcl)

/-! ### The run-level witness

One atomic dispatch on chain `324` of the deployed center, with an arbitrary keccak `k`: the bundle
of the `Dispatch` witness `wD1` (sender `1`, salt `1`, one zero-value direct call), encoded by the
`Dispatch` witness encoder, sent under the id of the one-leg flow of its own bundle hash. -/

/-- Chain `324` with keccak `k`. -/
def drParams (k : List UInt8 → UInt256) : Contracts.InteropCenter.Params :=
  ⟨324, 0x8010, Contracts.InteropCenter.saltWordsEncoder, k⟩

/-- The dispatched bundle, its bytes, and its bundle hash on chain `324`. -/
def drBundle (k : List UInt8 → UInt256) : Bundle :=
  Contracts.InteropCenter.wBundle (drParams k) 1 1 [⟨5, 1, 0, []⟩]

def drBytes (k : List UInt8 → UInt256) : List UInt8 := (drParams k).enc (drBundle k)

def drHash (k : List UInt8 → UInt256) : UInt256 := wsHash k (drBytes k) (drParams k).chainId

/-- The id of the one-leg flow of that hash, declared on chain `324`. -/
def drFlowId (k : List UInt8 → UInt256) : UInt256 :=
  (wsFlow k (drHash k) (drParams k).chainId).flowId

/-- The dispatch, and the source chain after it. -/
def drDispatch (k : List UInt8 → UInt256) : Contracts.InteropCenter.Dispatch :=
  ⟨1, [Contracts.InteropCenter.wDirect 0], drBundle k, ⟨drFlowId k, 0, 100, true⟩⟩

def drState (k : List UInt8 → UInt256) : Contracts.InteropCenter.State :=
  Contracts.InteropCenter.init.afterSend (drParams k) (drDispatch k)

/-- The destination: it decodes the dispatched bytes and accepts on chain `324` exactly the leg's
commit value. -/
def drTree (k : List UInt8 → UInt256) : UInt256 → Set UInt256 :=
  wsTree (drParams k).chainId (commitValue k (drFlowId k) (drHash k))

def drDest (k : List UInt8 → UInt256) : Dest := wsDest k (drBytes k) (drBundle k) (drTree k)

theorem drReach (k : List UInt8 → UInt256) :
    Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed (drParams k)
      Contracts.InteropCenter.init (drState k) := by
  refine .tail .refl (Contracts.InteropCenter.Step.send (drDispatch k) (fun _ => rfl)
    ⟨rfl, rfl, List.Forall₂.cons (Contracts.InteropCenter.formsCall_direct 1 0) List.Forall₂.nil⟩
    ?_ (fun _ => rfl))
  intro _ _ x hx
  simp only [drDispatch, drBundle, Contracts.InteropCenter.wBundle, List.mem_singleton] at hx
  subst hx
  rfl

theorem drBytes_length (k : List UInt8 → UInt256) : (drBytes k).length = 64 := by
  simp [drBytes, drParams, Contracts.InteropCenter.saltWordsEncoder]

theorem drBytes_ne_nil (k : List UInt8 → UInt256) : drBytes k ≠ [] :=
  List.ne_nil_of_length_pos (by rw [drBytes_length]; omega)

theorem drState_log (k : List UInt8 → UInt256) : (drState k).log = [drDispatch k] := rfl

theorem DispatchRunWitness : Properties.DispatchRunWitness := by
  intro k
  have hlen : (drBytes k).length < 256 ^ 32 := by rw [drBytes_length]; norm_num
  have hlog : ∀ d' ∈ (drState k).log, d' = drDispatch k := by
    intro d' hd'
    rw [drState_log] at hd'
    exact List.mem_singleton.mp hd'
  refine ⟨drParams k, drDest k, drState k, wsSt, _, 0, drBytes k, _, drBundle k, _,
    ⟨(drParams k).chainId, []⟩, drDispatch k, rfl, drReach k, rfl, ?_, ?_, ?_,
    ws_executes k (drBytes k) (drBytes_ne_nil k) (drBundle k) (drParams k).chainId (drTree k)
      rfl rfl rfl ⟨rfl, rfl⟩,
    hlen, ws_leg k _ _, by rw [drState_log]; exact List.mem_singleton_self _, rfl, rfl,
    deliveries_ne_nil _ _ (by simp [drBundle, Contracts.InteropCenter.wBundle]),
    fun hcl => hcl.1 rfl, fun hcl => hcl.1 rfl⟩
  · intro p v deadline sl _ hver
    refine ⟨drFlowId k, drHash k, ?_, (ws_tree_mem hver).2⟩
    rw [drState, Contracts.InteropCenter.afterSend_legState, ite_eq_left ⟨rfl, rfl, rfl⟩]
    decide
  · intro d' hd'
    rw [hlog d' hd']
    exact ws_decode k (drBytes k) (drBundle k) (drTree k)
  · intro d' hd'
    rw [hlog d' hd']
    exact hlen

end Contracts.L2InteropHandler.AtomicSourceFaithful
