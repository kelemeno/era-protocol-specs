import EraSpec.Contracts.L2InteropHandler.History.Properties.AtomicSourceBindingFaithful
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashPinned
import EraSpec.Contracts.InteropCenter.History.Proofs.Dispatch
import EraSpec.Contracts.L2InteropHandler.History.Proofs.SourceBindingReduced

/-! **History: a record of the interop pin `c67894b9`, not a claim about era-contracts `b17415d20`.**
This model transcribes the pin's atomic path. Three differences at `b17415d20` matter for it:
the destination's bundle hash is `keccak256(_bundle)` with no chain-id word
(`interop/interop-handler/InteropHandlerBase.sol:231`, `interop/InteropDataEncoding.sol:14-16`),
where the pin hashed `abi.encode(interopBundle.sourceChainId, _bundle)`; `executeAtomicBundle`
(`interop/interop-handler/L2InteropHandler.sol:61-78`) accepts a `Verified` bundle and then skips
`requireFlowFinalized`, and the new `verifyAtomicBundle` (`:83-92`) runs that gate and marks the
bundle `Verified`; and the source side is the pin's `InteropCenter` `Dispatch` model. The
self-binding destination check (`_validateBundleDestinationContext(…, interopBundle.sourceChainId)`,
`L2InteropHandler.sol:70` at `b17415d20`)
is the same at both. See the folder README. Namespaces carry a `History`
segment. -/

/-!
# Proofs: the atomic path's source binding, over `executeAtomicBundle`

The headline is one case split on the two keccak preimages, after the gate has been read.

* The gate gives the vouching leg's accepted proof, naming chain `c` (`legs`, `executingIsLeg`).
* Honest vouching turns the accepted value into the sentinel `0` (a break) or a logged leg `e` of
  chain `c` with the same commit value.
* Equal commit values: the two commit preimages differ (a `CommitPreimageClash`), or they are
  equal, and then they carry the same flow id and the same bundle hash (`commitPreimage_inj`: three
  fixed words).
* Equal bundle hashes: the two bundle-hash preimages differ (a `BundlePreimageClash`), or they are
  equal, and then their leading words agree (`chain_eq_of_abiEncode_eq`): the declared chain is `c`.
* `_executeCalls` hands every call the declared chain (`deliveries_sourceChainId`).

The run-level results read honest vouching off `SourceBindingReduced`'s
`SourceKeysAreDispatchedCommitValues`, and the validated, formed dispatch off topic `Dispatch`'s run
invariant (`inv_reach`), through `SourceBindingReduced`'s projection `sourceReach_center`.

The countermodels build one-leg flows whose flow id is the keccak of their own preimage, with the
ideal verifier on trees that hold the sentinel. The non-vacuity witnesses execute the leg of one
deployed send run on chain `324`; they are proved for every keccak whose commit value on that leg
is nonzero, and instantiated with topic `Dispatch`'s toy keccak `lastWord`.
-/

namespace Contracts.L2InteropHandler.AtomicSourceFaithful.History

open AttackVectors.BundleHashEncoding
open Contracts.InteropCenter (Address Bundle)
open IMTAbstract (keys)
open Contracts.InteropCommitmentTree (toAbs)

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

/-- Each delivery is one of the bundle's calls, with the bundle's source chain. -/
theorem mem_deliveries {D : Dest} {h : UInt256} {b : Bundle} {x : Delivery}
    (hx : x ∈ deliveries D h b) :
    ∃ k ∈ b.calls, x.sourceChainId = b.sourceChainId ∧ x.fromAddr = k.fromAddr ∧
      x.value = k.value := by
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hx
  exact ⟨ci.1, List.fst_mem_of_mem_zipIdx hci, rfl, rfl, rfl⟩

theorem DeliveriesCarryDeclaredSource : Properties.DeliveriesCarryDeclaredSource := by
  intro D st st' caller B fin b ds hx
  rw [hx.delivered]
  exact ⟨deliveries_length D _ b, deliveries_sourceChainId D _ b⟩

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

theorem AtomicSenderIsVouchingChainOrBreak :
    Properties.AtomicSenderIsVouchingChainOrBreak := by
  intro D st st' caller B fin b ds hx i c p hleg log hhon
  obtain ⟨hpc, hver⟩ := hx.checks.gate.legs i _ c p hleg
  rcases hhon p _ _ _ hpc hver with h0 | ⟨e, he, hv⟩
  · exact Or.inr h0
  · refine Or.inl ⟨e, he, ?_⟩
    rcases binding_core D.keccak fin.flow.flowId c B b e hv with ⟨hs, hf, hpre⟩ | hcl | hcl
    · refine Or.inl ⟨hs, fun d hd => ?_, hf, hpre⟩
      rw [hx.delivered] at hd
      rw [deliveries_sourceChainId D _ b d hd, hs]
    · exact Or.inr (Or.inl hcl)
    · exact Or.inr (Or.inr hcl)

theorem AtomicExecutesCommittedBytesOrBreak :
    Properties.AtomicExecutesCommittedBytesOrBreak := by
  intro D st st' caller B fin b ds hx i c p hleg log hhon hB hlog
  rcases AtomicSenderIsVouchingChainOrBreak D st st' caller B fin b ds hx i c p hleg log hhon with
    ⟨e, he, h⟩ | h0
  · refine Or.inl ⟨e, he, ?_⟩
    rcases h with ⟨hs, hds, hf, hpre⟩ | hcl | hcl
    · have hbytes := abiEncode_inj (uint256_val_lt b.sourceChainId) hB (uint256_val_lt c)
        (hlog e he) hpre
      exact Or.inl ⟨hs, hds, hf, hbytes.2⟩
    · exact Or.inr (Or.inl hcl)
    · exact Or.inr (Or.inr hcl)
  · exact Or.inr h0

theorem AtomicSenderIsVouchingChainOn : Properties.AtomicSenderIsVouchingChainOn := by
  intro D st st' caller B fin b ds hx i c p hleg log hhon hnz hcom hbun
  rcases AtomicSenderIsVouchingChainOrBreak D st st' caller B fin b ds hx i c p hleg log hhon with
    ⟨e, he, h⟩ | h0
  · rcases h with ⟨hs, hds, -, -⟩ | hcl | hcl
    · exact ⟨hs, hds⟩
    · exact absurd hcl ((injOn_pair_iff_no_collision _ _ _).mp (hcom e he))
    · exact absurd hcl ((injOn_pair_iff_no_collision _ _ _).mp (hbun e he))
  · exact absurd h0 hnz

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

/-! ## Countermodel data

One-leg flows. The flow id is the keccak of the flow's own preimage, so `_checkFlowId` passes for
every keccak. The verifier is the ideal one on a tree that holds the sentinel on every chain and one
more value on the leg's declared chain. Each countermodel is proved for an arbitrary keccak (or for
a keccak given only through the equations the argument needs) and instantiated at the end, so no
proof evaluates a hash. -/

/-- The countermodels' bundle: declared source `s`, destination `325`, base token `1`, one
zero-value call from `1` to `5`, no execution address. -/
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

/-- The trees: the sentinel `0` on every chain, and `v` on chain `c`. -/
def wsTree (c v : UInt256) : UInt256 → Set UInt256 := fun c' => {x | x = 0 ∨ (c' = c ∧ x = v)}

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

/-- The countermodel execution: bytes `B` decoding to a bundle `b` addressed to chain `325` with base
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

theorem ws_tree_mem {c v x c' : UInt256} (h : x ∈ wsTree c v c') : x = 0 ∨ (c' = c ∧ x = v) := h

/-- A tree holding the sentinel and the commit value of `e` vouches honestly against `[e]`. -/
theorem ws_honest (keccak : List UInt8 → UInt256) (B : List UInt8) (b : Bundle) (c : UInt256)
    (e : CommittedLeg) :
    HonestVouching (wsDest keccak B b (wsTree c (e.value keccak c))) c [e] := by
  intro p v deadline sl _ hver
  rcases ws_tree_mem hver with h0 | ⟨-, hv⟩
  · exact Or.inl h0
  · exact Or.inr ⟨e, List.mem_singleton_self e, hv⟩

/-- The two countermodel byte strings. -/
abbrev wsB₁ : List UInt8 := [1]
abbrev wsB₂ : List UInt8 := [2]

theorem abiEncode_chain_ne {s c : UInt256} {B B' : List UInt8} (hsc : s ≠ c) :
    abiEncode s.val B ≠ abiEncode c.val B' := fun hE =>
  hsc (Fin.ext (chain_eq_of_abiEncode_eq (uint256_val_lt _) (uint256_val_lt _) hE))

/-- A nonempty byte string's `abi.encode(uint256, bytes)` is not 96 bytes long, so it is never a
commit preimage. -/
theorem abiEncode_length_ne_96 (c : ℕ) {B : List UInt8} (hB : B ≠ []) :
    (abiEncode c B).length ≠ 96 := by
  have hpos : 0 < B.length := List.length_pos_of_ne_nil hB
  simp [abiEncode, pad32]
  omega

/-! ## Countermodels -/

theorem MisbehavingLegChainImpersonates : Properties.MisbehavingLegChainImpersonates := by
  intro keccak s c hsc
  let D := wsDest keccak wsB₁ (wsBundle s) (wsTree c (wsValue keccak wsB₁ s c))
  have hx := ws_executes keccak wsB₁ (by simp) (wsBundle s) c (wsTree c (wsValue keccak wsB₁ s c))
    rfl rfl rfl (Or.inr ⟨rfl, rfl⟩)
  refine ⟨D, wsSt, _, 0, wsB₁, _, wsBundle s, _, ⟨c, []⟩, rfl, hx, ws_leg keccak _ c, rfl, rfl,
    deliveries_ne_nil _ _ (wsBundle_calls_ne_nil s), deliveries_sourceChainId _ _ _, ?_, ?_⟩
  · intro q v deadline sl hq hver
    rcases ws_tree_mem hver with h0 | ⟨hqc, -⟩
    · exact h0
    · exact absurd (hq.symm.trans hqc) hsc
  · intro log hhon
    rcases AtomicSenderIsVouchingChainOrBreak D wsSt _ 0 wsB₁ _ (wsBundle s) _
      hx 0 c ⟨c, []⟩ (ws_leg keccak _ c) log hhon with ⟨e, he, h⟩ | h0
    · rcases h with ⟨hs, -⟩ | hcl | hcl
      · exact absurd hs hsc
      · exact Or.inl ⟨e, he, Or.inl hcl⟩
      · exact Or.inl ⟨e, he, Or.inr hcl⟩
    · exact Or.inr h0

/-- The sentinel disjunct alone, for any keccak that maps every commit preimage to its bundle hash
minus one, and reads the declared chain back from the two named bundle-hash preimages: bytes `B`
declaring `s` (with `s - 1 = 0`) and bytes `B'` committed by `c` (with `c - 1 ≠ 0`). -/
theorem sentinelCommitFires_of (keccak : List UInt8 → UInt256) (s c : UInt256)
    (B B' : List UInt8) (hsc : s ≠ c) (hB : B ≠ [])
    (hs : keccak (abiEncode s.val B) = s) (hc : keccak (abiEncode c.val B') = c)
    (hcv : ∀ f h : UInt256, keccak (commitPreimage keccak f h) = h - 1)
    (hs1 : s - 1 = 0) (hc1 : c - 1 ≠ 0) :
    Properties.SentinelCommitFires := by
  let e : CommittedLeg := ⟨(wsFlow keccak (wsHash keccak B s) c).flowId, B'⟩
  have hexec : commitValue keccak (wsFlow keccak (wsHash keccak B (wsBundle s).sourceChainId) c).flowId
      (wsHash keccak B (wsBundle s).sourceChainId) = 0 := by
    show keccak (commitPreimage keccak _ (keccak (abiEncode s.val B))) = 0
    rw [hcv, hs, hs1]
  have he : e.value keccak c = c - 1 := by
    show keccak (commitPreimage keccak _ (keccak (abiEncode c.val B'))) = c - 1
    rw [hcv, hc]
  refine ⟨wsDest keccak B (wsBundle s) (wsTree c (e.value keccak c)), wsSt, _, 0, B, _, wsBundle s,
    _, c, ⟨c, []⟩, e, ws_executes keccak B hB (wsBundle s) c _ rfl rfl rfl (Or.inl hexec),
    ws_leg keccak _ c, ws_honest keccak B (wsBundle s) c e, fun h0 => hc1 (he.symm.trans h0), hsc,
    deliveries_ne_nil _ _ (wsBundle_calls_ne_nil s), ?_, hexec, ?_, ?_⟩
  · intro d hd
    rw [deliveries_sourceChainId _ _ _ d hd]
    exact hsc
  · rintro ⟨-, hk⟩
    have hk' : commitValue keccak (wsFlow keccak (wsHash keccak B s) c).flowId (wsHash keccak B s) =
        e.value keccak c := hk
    rw [he] at hk'
    exact hc1 (hk'.symm.trans hexec)
  · rintro ⟨-, hk⟩
    have hk' : keccak (abiEncode s.val B) = keccak (abiEncode c.val B') := hk
    exact hsc (hs.symm.trans (hk'.trans hc))

/-- A keccak that maps every 96-byte input (every commit preimage) to its last word minus one, and
reads any other input's leading word. -/
def sentinelKeccak (x : List UInt8) : UInt256 :=
  if x.length = 96 then Contracts.InteropCenter.lastWord x - 1
  else Nat.toUInt256 (fromBytesBE (x.take 32))

/-- A keccak that maps every 96-byte input (every commit preimage) to `1`, and reads any other
input's leading word. -/
def commitBlindKeccak (x : List UInt8) : UInt256 :=
  if x.length = 96 then 1 else Nat.toUInt256 (fromBytesBE (x.take 32))

theorem sentinelKeccak_abiEncode (c : UInt256) {B : List UInt8} (hB : B ≠ []) :
    sentinelKeccak (abiEncode c.val B) = c := by
  rw [sentinelKeccak, ite_eq_right (abiEncode_length_ne_96 c.val hB), abiEncode_take32,
    fromBytesBE_toBytesBE (uint256_val_lt c), toUInt256_val]

theorem sentinelKeccak_commitPreimage (k : List UInt8 → UInt256) (f h : UInt256) :
    sentinelKeccak (commitPreimage k f h) = h - 1 := by
  rw [sentinelKeccak, ite_eq_left (commitPreimage_length k f h)]
  unfold commitPreimage
  rw [← List.append_assoc, Contracts.InteropCenter.lastWord_append_word,
    Contracts.InteropCenter.ofNat_val]

theorem commitBlindKeccak_abiEncode (c : UInt256) {B : List UInt8} (hB : B ≠ []) :
    commitBlindKeccak (abiEncode c.val B) = c := by
  rw [commitBlindKeccak, ite_eq_right (abiEncode_length_ne_96 c.val hB), abiEncode_take32,
    fromBytesBE_toBytesBE (uint256_val_lt c), toUInt256_val]

theorem commitBlindKeccak_commitPreimage (k : List UInt8 → UInt256) (f h : UInt256) :
    commitBlindKeccak (commitPreimage k f h) = 1 := by
  rw [commitBlindKeccak, ite_eq_left (commitPreimage_length k f h)]

theorem SentinelCommitFires : Properties.SentinelCommitFires :=
  sentinelCommitFires_of sentinelKeccak 1 2 wsB₂ wsB₁ (by decide) (by simp)
    (sentinelKeccak_abiEncode 1 (by simp)) (sentinelKeccak_abiEncode 2 (by simp))
    (sentinelKeccak_commitPreimage sentinelKeccak) (by decide) (by decide)

/-- The commit-value clash, for any keccak that maps every commit preimage to `1` and reads the
declared chain back from the two named bundle-hash preimages. -/
theorem commitPreimageClashFires_of (keccak : List UInt8 → UInt256) (s c : UInt256)
    (B B' : List UInt8) (hsc : s ≠ c) (hB : B ≠ [])
    (hs : keccak (abiEncode s.val B) = s) (hc : keccak (abiEncode c.val B') = c)
    (hcv : ∀ f h : UInt256, keccak (commitPreimage keccak f h) = 1) :
    Properties.CommitPreimageClashFires := by
  let e : CommittedLeg := ⟨(wsFlow keccak (wsHash keccak B s) c).flowId, B'⟩
  have hval : commitValue keccak (wsFlow keccak (wsHash keccak B (wsBundle s).sourceChainId) c).flowId
      (wsHash keccak B (wsBundle s).sourceChainId) ∈ wsTree c (e.value keccak c) c :=
    Or.inr ⟨rfl, (hcv _ _).trans (hcv _ _).symm⟩
  refine ⟨wsDest keccak B (wsBundle s) (wsTree c (e.value keccak c)), wsSt, _, 0, B, _, wsBundle s,
    _, c, ⟨c, []⟩, e, ws_executes keccak B hB (wsBundle s) c _ rfl rfl rfl hval,
    ws_leg keccak _ c, ws_honest keccak B (wsBundle s) c e, hsc,
    deliveries_ne_nil _ _ (wsBundle_calls_ne_nil s), ?_, ?_,
    ⟨?_, (hcv _ _).trans (hcv _ _).symm⟩, ?_⟩
  · intro d hd
    rw [deliveries_sourceChainId _ _ _ d hd]
    exact hsc
  · intro h0
    have h10 : (1 : UInt256) = 0 := (hcv _ _).symm.trans h0
    exact absurd h10 (by decide)
  · intro hE
    have hh : keccak (abiEncode s.val B) = keccak (abiEncode c.val B') := (commitPreimage_inj hE).2
    exact hsc (hs.symm.trans (hh.trans hc))
  · rintro ⟨-, hk⟩
    have hk' : keccak (abiEncode s.val B) = keccak (abiEncode c.val B') := hk
    exact hsc (hs.symm.trans (hk'.trans hc))

theorem CommitPreimageClashFires : Properties.CommitPreimageClashFires :=
  commitPreimageClashFires_of commitBlindKeccak 1 2 wsB₂ wsB₁ (by decide) (by simp)
    (commitBlindKeccak_abiEncode 1 (by simp)) (commitBlindKeccak_abiEncode 2 (by simp))
    (commitBlindKeccak_commitPreimage commitBlindKeccak)

/-- The bundle-hash clash, for any keccak that collides on the two named bundle-hash preimages,
bytes `B` declaring `s` and bytes `B'` committed by `c`, and maps no commit preimage to `0`. -/
theorem bundlePreimageClashFires_of (keccak : List UInt8 → UInt256) (s c : UInt256)
    (B B' : List UInt8) (hsc : s ≠ c) (hB : B ≠ [])
    (hcol : keccak (abiEncode s.val B) = keccak (abiEncode c.val B'))
    (hnz : ∀ f h : UInt256, keccak (commitPreimage keccak f h) ≠ 0) :
    Properties.BundlePreimageClashFires := by
  let e : CommittedLeg := ⟨(wsFlow keccak (wsHash keccak B s) c).flowId, B'⟩
  have hval : commitValue keccak (wsFlow keccak (wsHash keccak B (wsBundle s).sourceChainId) c).flowId
      (wsHash keccak B (wsBundle s).sourceChainId) ∈ wsTree c (e.value keccak c) c :=
    Or.inr ⟨rfl, congrArg (commitValue keccak _) hcol⟩
  refine ⟨wsDest keccak B (wsBundle s) (wsTree c (e.value keccak c)), wsSt, _, 0, B, _, wsBundle s,
    _, c, ⟨c, []⟩, e, ws_executes keccak B hB (wsBundle s) c _ rfl rfl rfl hval,
    ws_leg keccak _ c, ws_honest keccak B (wsBundle s) c e, hsc,
    deliveries_ne_nil _ _ (wsBundle_calls_ne_nil s), ?_, hnz _ _, ?_,
    ⟨abiEncode_chain_ne hsc, hcol⟩⟩
  · intro d hd
    rw [deliveries_sourceChainId _ _ _ d hd]
    exact hsc
  · rintro ⟨hne, -⟩
    exact hne (congrArg (commitPreimage keccak _) hcol)

/-- The constant keccak `1`. -/
def oneKeccak : List UInt8 → UInt256 := fun _ => 1

theorem uint256_one_ne_zero : (1 : UInt256) ≠ 0 := by decide

theorem BundlePreimageClashFires : Properties.BundlePreimageClashFires :=
  bundlePreimageClashFires_of oneKeccak 1 2 wsB₂ wsB₁ (by decide) (by simp) rfl
    (fun _ _ => uint256_one_ne_zero)

/-! ## Non-vacuity of the results with premises other than the headline's -/

/-- As `wsDest oneKeccak`, but decoding two byte strings: `[1]` to the bundle declaring chain `1`
and `[2]` to the same bundle declaring chain `2`. -/
def seenDest : Dest :=
  { wsDest oneKeccak wsB₁ (wsBundle 1) (wsTree 7 1) with
    decode := fun x =>
      if x = wsB₁ then some (wsBundle 1) else if x = wsB₂ then some (wsBundle 2) else none }

theorem DeclaredSourceSeenOnlyThroughHashWitness :
    Properties.DeclaredSourceSeenOnlyThroughHashWitness := by
  have hgate : FlowGateAccepts seenDest (executedHash seenDest wsB₁ (wsBundle 1))
      (wsFin seenDest.keccak (executedHash seenDest wsB₁ (wsBundle 1)) 7) :=
    ws_gate seenDest _ 7 (wsTree 7 1) rfl rfl (Or.inr ⟨rfl, rfl⟩)
  refine ⟨seenDest, wsSt, 0, _, wsB₁, wsB₂, wsBundle 1, 2,
    ⟨by simp, rfl, ⟨rfl, rfl, rfl⟩, Or.inl rfl, rfl, hgate⟩, by simp, by decide, rfl, rfl,
    by decide⟩

/-- A keccak that reads its input's leading word. -/
def leadingWordKeccak (x : List UInt8) : UInt256 := Nat.toUInt256 (fromBytesBE (x.take 32))

theorem leadingWordKeccak_abiEncode (c : UInt256) (B : List UInt8) :
    leadingWordKeccak (abiEncode c.val B) = c := by
  rw [leadingWordKeccak, abiEncode_take32, fromBytesBE_toBytesBE (uint256_val_lt c),
    toUInt256_val]

theorem DeclaredOfHashWitness : Properties.DeclaredOfHashWitness :=
  ⟨leadingWordKeccak, id, fun s B => leadingWordKeccak_abiEncode s B, 1, wsB₁, wsB₂, by decide,
    (leadingWordKeccak_abiEncode 1 wsB₁).trans (leadingWordKeccak_abiEncode 1 wsB₂).symm⟩

theorem HonestVouchingSplitWitness : Properties.HonestVouchingSplitWitness := by
  refine ⟨wsDest oneKeccak wsB₁ (wsBundle 1) (wsTree 7 1), wsTree 7 1, 7, [⟨0, wsB₁⟩],
    IdealVerifierSound _ _ 7 rfl, ?_, rfl, ⟨0, wsB₁⟩, List.mem_singleton_self _,
    uint256_one_ne_zero, Or.inr ⟨rfl, rfl⟩⟩
  intro v hv
  rcases ws_tree_mem hv with h0 | ⟨-, h1⟩
  · exact Or.inl h0
  · exact Or.inr ⟨_, List.mem_singleton_self _, h1⟩

/-! ## The vouching chain's deployed run -/

/-- A value the verifier accepts on the vouching chain is the sentinel, or the commit value of an
atomic dispatch of the run, which is validated and formed on that chain. -/
theorem accepted_of_deployedRun {D : Dest} {P : Contracts.InteropCenter.History.Params}
    {S : Contracts.SourceBinding.History.SourceState} (hk : P.keccak = D.keccak)
    (hr : Contracts.SourceBinding.History.SourceReach Contracts.InteropCenter.History.deployed P
      (commitValue P.keccak) Contracts.SourceBinding.History.sourceGenesis S)
    (hacc : AcceptsOnlyKeysOf D P.chainId S)
    {p : ImtProof} {v deadline sl : UInt256} (hpc : p.sourceChainId = P.chainId)
    (hver : D.verifyInclusion p v deadline sl) :
    v = 0 ∨ ∃ d ∈ S.center.log, d.isAtomic = true ∧ Contracts.InteropCenter.Validated d.bundle ∧
      Contracts.InteropCenter.History.FormedBy P d ∧
      v = (⟨d.atomicSend.flowId, P.enc d.bundle⟩ : CommittedLeg).value D.keccak P.chainId := by
  rcases (Contracts.SourceBinding.History.SourceKeysAreDispatchedCommitValues P (commitValue P.keccak) S hr
      v).mp (hacc p v deadline sl hpc hver) with h0 | ⟨d, hd, hat, hv⟩
  · exact Or.inl h0
  · have hI : Contracts.InteropCenter.History.Inv Contracts.InteropCenter.History.deployed P S.center :=
      Contracts.InteropCenter.History.inv_reach (Contracts.SourceBinding.History.sourceReach_center hr)
    refine Or.inr ⟨d, hd, hat, hI.validated rfl d hd hat, hI.formed d hd, ?_⟩
    rw [← hk]
    exact hv.symm

theorem DeployedRunVouchesHonestly : Properties.DeployedRunVouchesHonestly := by
  intro D P S hk hr hacc p v deadline sl hpc hver
  rcases accepted_of_deployedRun hk hr hacc hpc hver with h0 | ⟨d, hd, hat, -, -, hv⟩
  · exact Or.inl h0
  · exact Or.inr ⟨_, List.mem_map.mpr ⟨d, List.mem_filter.mpr ⟨hd, hat⟩, rfl⟩, hv⟩

theorem AtomicExecutionRunsADispatchedBundleOrBreak :
    Properties.AtomicExecutionRunsADispatchedBundleOrBreak := by
  intro D P S hk hr hacc st st' caller B fin b ds hx i p hleg
  obtain ⟨hpc, hver⟩ := hx.checks.gate.legs i _ P.chainId p hleg
  rcases accepted_of_deployedRun hk hr hacc hpc hver with h0 | ⟨d, hd, hat, hval, hform, hv⟩
  · exact Or.inr h0
  · refine Or.inl ⟨d, hd, hat, hval, hform.source, ?_⟩
    rcases binding_core D.keccak fin.flow.flowId P.chainId B b _ hv with ⟨hs, hf, hpre⟩ | hcl | hcl
    · refine Or.inl ⟨hs, fun x hxd => ?_, hf, hpre⟩
      rw [hx.delivered] at hxd
      rw [deliveries_sourceChainId D _ b x hxd, hs]
    · exact Or.inr (Or.inl hcl)
    · exact Or.inr (Or.inr hcl)

theorem AtomicExecutionRunsTheDispatchedBundleOrBreak :
    Properties.AtomicExecutionRunsTheDispatchedBundleOrBreak := by
  intro D P S hk hr hacc hdec hlen st st' caller B fin b ds hx hB i p hleg
  rcases AtomicExecutionRunsADispatchedBundleOrBreak D P S hk hr hacc st st' caller B fin b ds hx
      i p hleg with ⟨d, hd, hat, hval, -, h⟩ | h0
  · refine Or.inl ⟨d, hd, hat, ?_⟩
    rcases h with ⟨hs, -, hf, hpre⟩ | hcl | hcl
    · have hbytes := abiEncode_inj (uint256_val_lt _) hB (uint256_val_lt _) (hlen d hd) hpre
      have hb : b = d.bundle := by
        have h1 := hx.checks.decoded
        rw [hbytes.2, hdec d hd] at h1
        exact (Option.some.inj h1).symm
      have hform : Contracts.InteropCenter.History.FormedBy P d :=
        (Contracts.InteropCenter.History.inv_reach (Contracts.SourceBinding.History.sourceReach_center hr)).formed
          d hd
      have hvalb : Contracts.InteropCenter.Validated b := by rw [hb]; exact hval
      refine Or.inl ⟨hb, hbytes.2, hf, hvalb, hs, fun x hxd => ?_⟩
      rw [hx.delivered] at hxd
      obtain ⟨k, hk', hxs, hxf, hxv⟩ := mem_deliveries hxd
      refine ⟨hxs.trans hs, hxv.trans (hvalb k hk'), ?_⟩
      rw [hb] at hk'
      obtain ⟨cs, hcs, hfc⟩ := Contracts.SourceBinding.History.forall₂_mem_right hform.calls k hk'
      rw [hxf]
      cases hind : cs.callAttributes.indirectCall
      · exact Or.inl (hfc.direct hind).2.2
      · exact Or.inr ⟨cs, hcs, hind, hfc.indirect hind⟩
    · exact Or.inr (Or.inl hcl)
    · exact Or.inr (Or.inr hcl)
  · exact Or.inr h0

/-! ## Non-vacuity: one deployed run on chain `324`, and the execution of its leg

The run is proved for an arbitrary keccak `k` whose commit value on the run's one leg is nonzero
(so `append`'s tree insert succeeds), and instantiated at the end with topic `Dispatch`'s toy keccak
`lastWord` (the last 32 bytes, read as a word). Under `lastWord` with the encoder
`saltWordsEncoder`, a bundle's hash is its user salt, and the deployed commit-value shape returns
the bundle hash, so the leg's commit value is `1`. -/

/-- Chain `324` (center `0x8010`) with the toy encoder of topic `Dispatch` and keccak `k`. -/
def drParams (k : List UInt8 → UInt256) : Contracts.InteropCenter.History.Params :=
  ⟨324, 0x8010, Contracts.InteropCenter.saltWordsEncoder, k⟩

/-- Sender `1`, salt `1`, one zero-value direct call to `5`, to chain `325`. -/
def drBundle (k : List UInt8 → UInt256) : Bundle :=
  Contracts.InteropCenter.History.wBundle (drParams k) 1 1 [⟨5, 1, 0, []⟩]

/-- Its bytes `abi.encode(bundle)`, under the toy encoder. -/
def drBytes (k : List UInt8 → UInt256) : List UInt8 := (drParams k).enc (drBundle k)

/-- Its bundle hash on chain `324`. -/
def drHash (k : List UInt8 → UInt256) : UInt256 := wsHash k (drBytes k) (drParams k).chainId

/-- The id of the one-leg flow of that hash, declared on chain `324`. -/
def drFlowId (k : List UInt8 → UInt256) : UInt256 :=
  (wsFlow k (drHash k) (drParams k).chainId).flowId

/-- The atomic dispatch of that bundle under that flow id. -/
def drDispatch (k : List UInt8 → UInt256) : Contracts.InteropCenter.History.Dispatch :=
  ⟨1, [Contracts.InteropCenter.wDirect 0], drBundle k, ⟨drFlowId k, 0, 100, true⟩⟩

/-- Chain `324`'s send side after the dispatch: the leg committed, and its commit value inserted
into the tree seeded at genesis. -/
def drState (k : List UInt8 → UInt256) : Contracts.SourceBinding.History.SourceState :=
  ⟨Contracts.InteropCenter.History.init.afterSend (drParams k) (drDispatch k),
    Contracts.InteropCommitmentTree.insert Contracts.InteropCommitmentTree.setup
      (commitValue k (drFlowId k) (drHash k)) 0⟩

/-- The verifier's trees: on chain `324` the keys of that tree, elsewhere nothing. -/
def drTree (k : List UInt8 → UInt256) : UInt256 → Set UInt256 :=
  fun c' => {x | c' = (drParams k).chainId ∧ x ∈ keys (toAbs (drState k).tree)}

/-- The destination: it decodes the dispatched bytes, and its verifier accepts on chain `324`
exactly the keys of chain `324`'s tree. -/
def drDest (k : List UInt8 → UInt256) : Dest := wsDest k (drBytes k) (drBundle k) (drTree k)

/-- `IndexedMerkleTree.insert(v, 0)` succeeds on the freshly seeded tree for every nonzero `v`. -/
theorem insertSucceeds_setup {v : UInt256} (hv : 0 < v) :
    Contracts.AppendPath.InsertSucceeds Contracts.InteropCommitmentTree.setup v 0 0 :=
  ⟨by show (1 : ℕ) ≠ 0; omega, (ne_of_lt hv).symm, rfl, by show (0 : ℕ) < 1; omega, hv, rfl⟩

theorem drBundle_validated (k : List UInt8 → UInt256) :
    Contracts.InteropCenter.Validated (drBundle k) := by
  intro x hx
  simp only [drBundle, Contracts.InteropCenter.History.wBundle, List.mem_singleton] at hx
  subst hx
  rfl

theorem drReach (k : List UInt8 → UInt256) (hpos : 0 < commitValue k (drFlowId k) (drHash k)) :
    Contracts.SourceBinding.History.SourceReach Contracts.InteropCenter.History.deployed (drParams k)
      (commitValue (drParams k).keccak) Contracts.SourceBinding.History.sourceGenesis (drState k) :=
  .tail .refl (Contracts.SourceBinding.History.SourceStep.sendAtomic (drDispatch k) 0 0 rfl (fun _ => rfl)
    ⟨rfl, rfl, List.Forall₂.cons (Contracts.InteropCenter.formsCall_direct 1 0) List.Forall₂.nil⟩
    (fun _ => drBundle_validated k) ⟨rfl, insertSucceeds_setup hpos⟩)

theorem drAccepts (k : List UInt8 → UInt256) :
    AcceptsOnlyKeysOf (drDest k) (drParams k).chainId (drState k) := by
  intro p v deadline sl _ hver
  exact hver.2

theorem drLog (k : List UInt8 → UInt256) : (drState k).center.log = [drDispatch k] := rfl

theorem drDispatchLegs (k : List UInt8 → UInt256) :
    dispatchLegs (drParams k) (drState k).center = [⟨drFlowId k, drBytes k⟩] := rfl

theorem drBytes_length (k : List UInt8 → UInt256) : (drBytes k).length = 64 := by
  simp [drBytes, drParams, Contracts.InteropCenter.saltWordsEncoder]

theorem drBytes_ne_nil (k : List UInt8 → UInt256) : drBytes k ≠ [] :=
  List.ne_nil_of_length_pos (by rw [drBytes_length]; omega)

theorem drBytes_lt (k : List UInt8 → UInt256) : (drBytes k).length < 256 ^ 32 := by
  rw [drBytes_length]; norm_num

theorem drBundle_calls_ne_nil (k : List UInt8 → UInt256) : (drBundle k).calls ≠ [] := by
  simp [drBundle, Contracts.InteropCenter.History.wBundle]

/-- The witness execution: the dispatched bytes, under the one-leg flow of their hash. -/
theorem drExecutes (k : List UInt8 → UInt256) (hpos : 0 < commitValue k (drFlowId k) (drHash k)) :
    ExecutesAtomic (drDest k) wsSt 0 (drBytes k) (wsFin k (drHash k) (drParams k).chainId)
      (drBundle k) (wsSt.markExecuted (drHash k)) (deliveries (drDest k) (drHash k) (drBundle k)) :=
  ws_executes k (drBytes k) (drBytes_ne_nil k) (drBundle k) (drParams k).chainId (drTree k)
    rfl rfl rfl ⟨rfl, Contracts.Atomicity.mem_insertSetup hpos⟩

/-- The headline's witness, for every keccak with a nonzero commit value on the run's leg. Honest
vouching is not assumed: it is `DeployedRunVouchesHonestly` on the run. -/
theorem atomicSenderBindingWitness_of (k : List UInt8 → UInt256)
    (hpos : 0 < commitValue k (drFlowId k) (drHash k)) : Properties.AtomicSenderBindingWitness := by
  have hhon : HonestVouching (drDest k) (drParams k).chainId [⟨drFlowId k, drBytes k⟩] := by
    rw [← drDispatchLegs]
    exact DeployedRunVouchesHonestly (drDest k) (drParams k) (drState k) rfl (drReach k hpos)
      (drAccepts k)
  have hcom : ¬ CommitPreimageClash k (drFlowId k) (drHash k) (drParams k).chainId
      ⟨drFlowId k, drBytes k⟩ := fun hcl => hcl.1 rfl
  have hbun : ¬ BundlePreimageClash k (drBytes k) (drBundle k) (drParams k).chainId
      ⟨drFlowId k, drBytes k⟩ := fun hcl => hcl.1 rfl
  have hns : ¬ CommitValueIsSentinel k (drFlowId k) (drHash k) := (ne_of_lt hpos).symm
  exact ⟨drDest k, wsSt, _, 0, drBytes k, _, drBundle k, _, (drParams k).chainId,
    ⟨(drParams k).chainId, []⟩, ⟨drFlowId k, drBytes k⟩, drExecutes k hpos, ws_leg k _ _, hhon,
    drBytes_lt k, drBytes_lt k, hns, hcom, hbun, hns, (injOn_pair_iff_no_collision _ _ _).mpr hcom,
    (injOn_pair_iff_no_collision _ _ _).mpr hbun, deliveries_ne_nil _ _ (drBundle_calls_ne_nil k),
    rfl, deliveries_sourceChainId _ _ _⟩

/-- The run-level witness, for every keccak with a nonzero commit value on the run's leg. -/
theorem deployedRunExecutionWitness_of (k : List UInt8 → UInt256)
    (hpos : 0 < commitValue k (drFlowId k) (drHash k)) : Properties.DeployedRunExecutionWitness := by
  refine ⟨drParams k, drDest k, drState k, wsSt, _, 0, drBytes k, _, drBundle k, _,
    ⟨(drParams k).chainId, []⟩, drDispatch k, rfl, drReach k hpos, drAccepts k, ?_, ?_,
    drExecutes k hpos, drBytes_lt k, ws_leg k _ _, by rw [drLog]; exact List.mem_singleton_self _,
    rfl, rfl, deliveries_ne_nil _ _ (drBundle_calls_ne_nil k), (ne_of_lt hpos).symm,
    fun hcl => hcl.1 rfl, fun hcl => hcl.1 rfl⟩
  · intro d' hd'
    rw [drLog, List.mem_singleton] at hd'
    subst hd'
    exact ws_decode _ _ _ _
  · intro d' hd'
    rw [drLog, List.mem_singleton] at hd'
    subst hd'
    exact drBytes_lt k

/-- The toy keccak returns the bundle hash from the commit preimage. -/
theorem commitValue_lastWord (f h : UInt256) :
    commitValue Contracts.InteropCenter.lastWord f h = h := by
  unfold commitValue commitPreimage
  rw [← List.append_assoc, Contracts.InteropCenter.lastWord_append_word,
    Contracts.InteropCenter.ofNat_val]

/-- Under the toy keccak the witness bundle hashes to its user salt, `1`. -/
theorem drHash_lastWord : drHash Contracts.InteropCenter.lastWord = 1 := by
  simp only [drHash, wsHash, drBytes, drParams]
  rw [Contracts.SourceBinding.History.lastWord_abiEncode_saltWords]
  rfl

theorem drLastWord_pos :
    0 < commitValue Contracts.InteropCenter.lastWord (drFlowId Contracts.InteropCenter.lastWord)
      (drHash Contracts.InteropCenter.lastWord) := by
  rw [commitValue_lastWord, drHash_lastWord]
  decide

theorem AtomicSenderBindingWitness : Properties.AtomicSenderBindingWitness :=
  atomicSenderBindingWitness_of Contracts.InteropCenter.lastWord drLastWord_pos

theorem DeployedRunExecutionWitness : Properties.DeployedRunExecutionWitness :=
  deployedRunExecutionWitness_of Contracts.InteropCenter.lastWord drLastWord_pos

end Contracts.L2InteropHandler.AtomicSourceFaithful.History
