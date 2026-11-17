import EraSpec.Contracts.AtomicFlowManager.Properties.FlowCanonicalAtHead
import EraSpec.Contracts.AtomicFlowManager.Proofs.FlowCanonical

/-!
# Proofs: what `_validateAndComputeFlowId` accepts, at head (`3605e82`)

`validate_eq_some_iff` unfolds the four `if`s once; everything else reads off it, or off
the pin's `AttackVectors.FlowCanonical` theorems about `Valid`. The countermodels and the
witness are closed by `decide` on concrete preimages.
-/

namespace Contracts.FlowCanonicalAtHead

open AttackVectors.FlowCanonical

/-! ## The function -/

/-- **`_validateAndComputeFlowId` returns `id` iff the four checks pass and `id` is the
hash.** -/
theorem validate_eq_some_iff {enc : PreimageHash} {P : FlowPreimage} {id : UInt256} :
    validateAndComputeFlowId enc P = some id ↔ PreimageAccepted P ∧ id = enc P := by
  unfold validateAndComputeFlowId
  by_cases h1 : P.version ≠ ATOMIC_FLOW_PREIMAGE_VERSION
  · rw [ite_eq_left h1]
    exact ⟨fun h => absurd h (by simp), fun h => absurd h.1.version h1⟩
  rw [ite_eq_right h1]
  by_cases h2 : MAX_ATOMIC_FLOW_LEGS < P.legBundleHashes.length
  · rw [ite_eq_left h2]
    exact ⟨fun h => absurd h (by simp), fun h => absurd h.1.legCap (not_le.mpr h2)⟩
  rw [ite_eq_right h2]
  by_cases h3 : ¬ Ascending P.legBundleHashes
  · rw [ite_eq_left h3]
    exact ⟨fun h => absurd h (by simp), fun h => absurd h.1.sorted h3⟩
  rw [ite_eq_right h3]
  by_cases h4 : P.legSourceChainIds.length ≠ P.legBundleHashes.length
  · rw [ite_eq_left h4]
    exact ⟨fun h => absurd h (by simp), fun h => absurd h.1.lengths h4⟩
  rw [ite_eq_right h4]
  constructor
  · intro h
    exact ⟨⟨not_not.mp h1, not_lt.mp h2, not_not.mp h3, not_not.mp h4⟩,
      (Option.some.inj h).symm⟩
  · rintro ⟨_, rfl⟩
    rfl

/-- An accepted preimage hashes to its own id. -/
theorem validate_of_accepted (enc : PreimageHash) {P : FlowPreimage} (hP : PreimageAccepted P) :
    validateAndComputeFlowId enc P = some (enc P) :=
  validate_eq_some_iff.mpr ⟨hP, rfl⟩

/-- A rejected preimage makes the function revert. -/
theorem validate_eq_none_of_not_accepted (enc : PreimageHash) {P : FlowPreimage}
    (hP : ¬ PreimageAccepted P) : validateAndComputeFlowId enc P = none := by
  cases h : validateAndComputeFlowId enc P with
  | none => rfl
  | some id => exact absurd (validate_eq_some_iff.mp h).1 hP

/-- `_checkFlowId` passes iff the preimage is accepted and hashes to the claimed id. -/
theorem checkFlowId_iff {enc : PreimageHash} {F : AtomicFlow} :
    CheckFlowId enc F ↔ PreimageAccepted F.preimage ∧ enc F.preimage = F.flowId := by
  unfold CheckFlowId
  rw [validate_eq_some_iff]
  exact and_congr_right fun _ => eq_comm

/-- A checked flow's preimage is accepted. -/
theorem CheckFlowId.accepted {enc : PreimageHash} {F : AtomicFlow} (h : CheckFlowId enc F) :
    PreimageAccepted F.preimage :=
  (checkFlowId_iff.mp h).1

/-- A checked flow's id is the hash of its preimage. -/
theorem CheckFlowId.id_eq {enc : PreimageHash} {F : AtomicFlow} (h : CheckFlowId enc F) :
    enc F.preimage = F.flowId :=
  (checkFlowId_iff.mp h).2

/-- The flow a preimage computes is checked. -/
theorem checkFlowId_of_accepted (enc : PreimageHash) {P : FlowPreimage} (hP : PreimageAccepted P) :
    CheckFlowId enc ⟨enc P, P⟩ :=
  validate_of_accepted enc hP

/-! ## `Valid`, necessary and sufficient -/

/-- An accepted preimage is the pin's `Valid`. -/
theorem PreimageAccepted.valid {P : FlowPreimage} (hP : PreimageAccepted P) : Valid P.arrays :=
  ⟨hP.sorted, hP.lengths⟩

theorem accepted_iff_valid_version_cap {P : FlowPreimage} :
    PreimageAccepted P ↔
      Valid P.arrays ∧ P.version = ATOMIC_FLOW_PREIMAGE_VERSION
        ∧ P.legBundleHashes.length ≤ MAX_ATOMIC_FLOW_LEGS := by
  constructor
  · intro hP
    exact ⟨hP.valid, hP.version, hP.legCap⟩
  · rintro ⟨⟨hs, hl⟩, hv, hc⟩
    exact ⟨hv, hc, hs, hl⟩

/-- The leg pairs of a preimage whose arrays have equal length cover every bundle hash. -/
theorem legPairs_length {P : FlowPreimage}
    (hl : P.legSourceChainIds.length = P.legBundleHashes.length) :
    P.legPairs.length = P.legBundleHashes.length := by
  unfold FlowPreimage.legPairs
  rw [List.length_zip, hl, min_self]

/-- The first components of the leg pairs are the bundle hashes. -/
theorem legPairs_map_fst {P : FlowPreimage}
    (hl : P.legSourceChainIds.length = P.legBundleHashes.length) :
    P.legPairs.map Prod.fst = P.legBundleHashes := by
  unfold FlowPreimage.legPairs
  exact List.map_fst_zip (le_of_eq hl.symm)

/-- The second components of the leg pairs are the source chain ids. -/
theorem legPairs_map_snd {P : FlowPreimage}
    (hl : P.legSourceChainIds.length = P.legBundleHashes.length) :
    P.legPairs.map Prod.snd = P.legSourceChainIds := by
  unfold FlowPreimage.legPairs
  exact List.map_snd_zip (le_of_eq hl)

/-- **ONE DECLARED SOURCE CHAIN PER LEG.** -/
theorem declared_source_chain_unique {P : FlowPreimage} (hP : PreimageAccepted P)
    {b c c' : UInt256} (h : P.Declares b c) (h' : P.Declares b c') : c = c' := by
  have hnd : (P.legPairs.map Prod.fst).Nodup := by
    rw [legPairs_map_fst hP.lengths]
    exact ascending_nodup hP.sorted
  have := List.inj_on_of_nodup_map hnd h h' rfl
  exact congrArg Prod.snd this

/-- A declared leg is listed, with a listed chain. -/
theorem FlowPreimage.Declares.mem {P : FlowPreimage} {b c : UInt256} (h : P.Declares b c) :
    b ∈ P.legBundleHashes ∧ c ∈ P.legSourceChainIds :=
  ⟨List.of_mem_zip h |>.1, List.of_mem_zip h |>.2⟩

/-- Every listed bundle hash of a preimage with matching lengths is declared on some chain. -/
theorem listed_leg_is_declared {P : FlowPreimage}
    (hl : P.legSourceChainIds.length = P.legBundleHashes.length) {b : UInt256}
    (hb : b ∈ P.legBundleHashes) : ∃ c, P.Declares b c := by
  have hb' : b ∈ P.legPairs.map Prod.fst := by rw [legPairs_map_fst hl]; exact hb
  obtain ⟨⟨b', c⟩, hmem, rfl⟩ := List.mem_map.mp hb'
  exact ⟨c, hmem⟩

/-- Two checked flows with one id are equal, or their preimages clash. -/
theorem checked_flows_agree_or_clash {enc : PreimageHash} {F F' : AtomicFlow}
    (hF : CheckFlowId enc F) (hF' : CheckFlowId enc F') (hid : F.flowId = F'.flowId) :
    F = F' ∨ PreimageClash enc F.preimage F'.preimage := by
  by_cases hp : F.preimage = F'.preimage
  · left
    cases F
    cases F'
    simp only at hp hid
    rw [hp, hid]
  · right
    exact ⟨hp, hF.id_eq.trans (hid.trans hF'.id_eq.symm)⟩

/-! ## Certificates -/

theorem ValidateIsSomeIffAccepted : Properties.ValidateIsSomeIffAccepted :=
  fun _ _ _ => validate_eq_some_iff

theorem CheckFlowIdIff : Properties.CheckFlowIdIff :=
  fun _ _ => checkFlowId_iff

theorem AcceptedPreimageIsValid : Properties.AcceptedPreimageIsValid :=
  fun _ _ _ h => (validate_eq_some_iff.mp h).1.valid

theorem AcceptedIffValidVersionCap : Properties.AcceptedIffValidVersionCap :=
  fun _ => accepted_iff_valid_version_cap

/-- A version-`0x02` preimage that is otherwise fine. -/
def wrongVersionPreimage : FlowPreimage := ⟨0x02, 0, 0, [1, 2], [0, 1]⟩

/-- A version-`0x01` preimage with nine ascending legs. -/
def nineLegPreimage : FlowPreimage :=
  ⟨0x01, 0, 0, [0, 1, 2, 3, 4, 5, 6, 7, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

theorem ValidNoLongerSufficient : Properties.ValidNoLongerSufficient := by
  refine ⟨⟨wrongVersionPreimage, ⟨by decide, rfl⟩, by decide, by decide, fun enc => ?_⟩,
    ⟨nineLegPreimage, ⟨by decide, rfl⟩, rfl, by decide, fun enc => ?_⟩⟩
  · unfold validateAndComputeFlowId
    rw [ite_eq_left (by decide)]
  · unfold validateAndComputeFlowId
    rw [ite_eq_right (by decide), ite_eq_left (by decide)]

theorem NewChecksRejectOnEveryPath : Properties.NewChecksRejectOnEveryPath := by
  intro enc P h
  have hnot : ¬ PreimageAccepted P := by
    intro hP
    rcases h with hv | hc
    · exact hv hP.version
    · exact absurd hP.legCap (not_le.mpr hc)
  refine ⟨validate_eq_none_of_not_accepted enc hnot, fun id hchk => hnot hchk.accepted⟩

theorem SharedValidationNoDrift : Properties.SharedValidationNoDrift :=
  fun _ _ _ => Iff.rfl

theorem AcceptedHasAtMostMaxLegs : Properties.AcceptedHasAtMostMaxLegs := by
  intro P hP
  rw [legPairs_length hP.lengths]
  exact hP.legCap

theorem AcceptedPreimageIsCanonical : Properties.AcceptedPreimageIsCanonical := by
  intro P hP
  obtain ⟨hnd, hlen⟩ := valid_pairing_functional (f := P.arrays) hP.valid
  refine ⟨ascending_nodup hP.sorted, hnd, hlen, ?_⟩
  intro Q hQ hperm
  exact valid_unique_per_leg_set (f := Q.arrays) (g := P.arrays) hQ.valid hP.valid hperm

theorem DeclaredSourceChainUnique : Properties.DeclaredSourceChainUnique :=
  fun _ hP _ _ _ h h' => declared_source_chain_unique hP h h'

theorem ListedLegIsDeclared : Properties.ListedLegIsDeclared :=
  fun _ hP _ hb => listed_leg_is_declared hP.lengths hb

theorem DeclaredLegIsListed : Properties.DeclaredLegIsListed :=
  fun _ _ _ h => h.mem

theorem CheckedFlowsAgreeOrClash : Properties.CheckedFlowsAgreeOrClash :=
  fun _ _ _ hF hF' hid => checked_flows_agree_or_clash hF hF' hid

theorem DifferentVersionsShareAnIdOnlyByClash : Properties.DifferentVersionsShareAnIdOnlyByClash :=
  fun _ _ _ hv he => ⟨fun hp => hv (congrArg FlowPreimage.version hp), he⟩

/-- `x + 1 ≠ x` in `UInt256`: the honest preimage hash really separates. -/
theorem uint256_add_one_ne_self (x : UInt256) : x + 1 ≠ x := by
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_add] at hv
  have h1 : (1 : UInt256).val = 1 := rfl
  rw [h1] at hv
  have := x.isLt
  simp only [UInt256.size] at this hv
  omega

theorem HonestPreimageHashNoClash : Properties.HonestPreimageHashNoClash := by
  intro P0 id hP0
  refine ⟨?_, ?_⟩
  · have := checkFlowId_of_accepted (honestPreimageHash P0 id) hP0
    simpa [honestPreimageHash] using this
  · rintro P ⟨hne, heq⟩
    have hne' : P ≠ P0 := fun h => hne h.symm
    simp only [honestPreimageHash, ite_true, ite_eq_right hne'] at heq
    exact uint256_add_one_ne_self _ heq.symm

/-- The index of a preimage in a list, as a word: injective on the list's members. -/
def preimageIndexHash (Ps : List FlowPreimage) : PreimageHash :=
  fun P => if hi : Ps.idxOf P < UInt256.size then ⟨Ps.idxOf P, hi⟩ else 0

theorem PreimageHashInjOnSatisfiable : Properties.PreimageHashInjOnSatisfiable := by
  intro Ps hlen
  refine ⟨preimageIndexHash Ps, ?_⟩
  rintro P hP P' hP' ⟨hne, heq⟩
  have hlt := lt_trans (List.idxOf_lt_length_iff.mpr hP) hlen
  have hlt' := lt_trans (List.idxOf_lt_length_iff.mpr hP') hlen
  unfold preimageIndexHash at heq
  rw [dite_eq_left hlt, dite_eq_left hlt'] at heq
  exact hne ((List.idxOf_inj hP).mp (Fin.mk.inj_iff.mp heq))

/-- The witness preimage: bundle `1` on chain `0`, bundle `2` on chain `1`. -/
def twoLegPreimage : FlowPreimage := ⟨0x01, 0, 0, [1, 2], [0, 1]⟩

/-- A second accepted preimage, with another deadline. -/
def twoLegPreimageLater : FlowPreimage := ⟨0x01, 1, 0, [1, 2], [0, 1]⟩

theorem twoLegPreimage_accepted : PreimageAccepted twoLegPreimage :=
  ⟨rfl, by decide, by decide, rfl⟩

theorem twoLegPreimageLater_accepted : PreimageAccepted twoLegPreimageLater :=
  ⟨rfl, by decide, by decide, rfl⟩

theorem FlowCanonicalAtHeadWitness : Properties.FlowCanonicalAtHeadWitness := by
  refine ⟨twoLegPreimage, twoLegPreimageLater, wrongVersionPreimage, twoLegPreimage_accepted, rfl,
    by decide, by decide, fun enc => checkFlowId_of_accepted enc twoLegPreimage_accepted,
    twoLegPreimageLater_accepted, by decide,
    checkFlowId_of_accepted (fun _ => 0) twoLegPreimage_accepted,
    checkFlowId_of_accepted (fun _ => 0) twoLegPreimageLater_accepted,
    ⟨by decide, rfl⟩, by decide, ⟨by decide, rfl⟩⟩

end Contracts.FlowCanonicalAtHead
