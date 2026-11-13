import EraSpec.Contracts.MultiProofVerifier.Properties.Routing

/-!
# Proofs: what a ZKsync OS verifier accepts

`getProofMode_mask` reduces the mode to the three getter bits; `verifyMultiProof_iff`
characterises `_verifyMultiProof` as an envelope decomposition `p0 :: 0 :: c :: ab ++ zk ++
rest`; `AcceptIff` combines them. The production results instantiate it with
`ZkosAcceptIff`.
-/

namespace Contracts.MultiProofVerifier

/-! ## Mode -/

lemma getProofMode_mask (d : DisabledProofSystems) :
    getProofMode d.mask =
      if d.boojum = true ∨ d.airbender = true then none
      else if d.zisk = true then some PLONK_TYPE else some MULTI_TYPE := by
  rcases d with ⟨_ | _, _ | _, _ | _⟩ <;> decide

lemma getProofMode_some {m : ℕ} {r : Word} (h : getProofMode m = some r) :
    r = PLONK_TYPE ∨ r = MULTI_TYPE := by
  unfold getProofMode at h
  split_ifs at h <;> simp_all

theorem GetProofModeExact : Properties.GetProofModeExact := by
  unfold Properties.GetProofModeExact
  decide +kernel

/-! ## `_verifyMultiProof` as an envelope decomposition -/

lemma drop3_add (p0 p1 c : Word) (t : List Word) (n : ℕ) :
    (p0 :: p1 :: c :: t).drop (3 + n) = t.drop n := by
  rw [Nat.add_comm]; rfl

lemma verifyMultiProof_iff (W : Wiring) (pi proof : List Word) :
    verifyMultiProof W pi proof = some true ↔
      ∃ (p0 c : Word) (ab zk rest : List Word),
        proof = p0 :: 0 :: c :: (ab ++ zk ++ rest) ∧ ab.length = c.val ∧
        zk.length = ZISK_LEN ∧ W.airbender pi ab = some true ∧ W.ziskRange pi zk = some true := by
  constructor
  · intro h
    obtain ⟨p0, p1, c, t, rfl⟩ : ∃ p0 p1 c t, proof = p0 :: p1 :: c :: t := by
      rcases proof with _ | ⟨p0, _ | ⟨p1, _ | ⟨c, t⟩⟩⟩
      · simp [verifyMultiProof] at h
      · simp [verifyMultiProof] at h
      · simp [verifyMultiProof] at h
      · exact ⟨p0, p1, c, t, rfl⟩
    unfold verifyMultiProof at h
    rw [drop3_add] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.drop_succ_cons,
      List.drop_zero] at h
    split_ifs at h with h1 h2 h3 h4 h5
    have hp1 : p1 = 0 := by simpa using h2
    have hlen : c.val + ZISK_LEN ≤ t.length := by omega
    refine ⟨p0, c, t.take c.val, (t.drop c.val).take ZISK_LEN, (t.drop c.val).drop ZISK_LEN,
      ?_, ?_, ?_, ?_, ?_⟩
    · subst hp1; simp
    · simp; omega
    · simp; omega
    · simpa using h4
    · simpa using h5
  · rintro ⟨p0, c, ab, zk, rest, rfl, hab, hzk, ha, hz⟩
    unfold verifyMultiProof
    rw [drop3_add]
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.drop_succ_cons,
      List.drop_zero, List.length_append]
    have e1 : (ab ++ zk ++ rest).take c.val = ab := by
      rw [List.append_assoc, ← hab, List.take_left]
    have e2 : ((ab ++ zk ++ rest).drop c.val).take ZISK_LEN = zk := by
      rw [List.append_assoc, ← hab, List.drop_left, ← hzk, List.take_left]
    rw [e1, e2]
    simp [ha, hz]
    omega

/-! ## Any wiring -/

lemma shift_two : (PLONK_TYPE : Word).val >>> 8 = 0 := by decide
lemma shift_five : (MULTI_TYPE : Word).val >>> 8 = 0 := by decide

theorem AcceptIff : Properties.AcceptIff := by
  intro W P chain pi proof
  rcases proof with _ | ⟨p0, t⟩
  · simp [verifyForChain]
  · unfold verifyForChain
    rcases hP : P chain with _ | ⟨b, a, z⟩
    · simp
    · simp only [getProofMode_mask]
      cases b <;> cases a
      case false.false =>
        cases z
        · -- multi-proof mode
          simp only [Bool.false_eq_true, or_self, ite_false]
          by_cases hp : p0 = MULTI_TYPE
          · subst hp
            simp only [shift_five, ne_eq, not_true_eq_false, ite_false, show MULTI_TYPE ≠ PLONK_TYPE by decide,
              verifyMultiProof_iff]
            constructor
            · rintro ⟨p0', c, ab, zk, rest, he, h1, h2, h3, h4⟩
              refine ⟨_, rfl, rfl, rfl, Or.inr ⟨rfl, c, ab, zk, rest, ?_, h1, h2, h3, h4⟩⟩
              simp only [List.cons.injEq] at he ⊢
              exact ⟨trivial, he.2⟩
            · rintro ⟨d, hd, -, -, (⟨hz, -⟩ | ⟨-, c, ab, zk, rest, he, h1, h2, h3, h4⟩)⟩
              · simp at hd; subst hd; simp at hz
              · exact ⟨MULTI_TYPE, c, ab, zk, rest, he, h1, h2, h3, h4⟩
          · constructor
            · intro h; split_ifs at h <;> simp_all
            · rintro ⟨d, hd, -, -, (⟨hz, -⟩ | ⟨-, c, ab, zk, rest, he, -⟩)⟩
              · simp at hd; subst hd; simp at hz
              · simp only [List.cons.injEq] at he; exact absurd he.1 hp
        · -- Airbender-only mode
          simp only [Bool.false_eq_true, or_self, ite_false, ite_true]
          by_cases hp : p0 = PLONK_TYPE
          · subst hp
            simp only [shift_two, ne_eq, not_true_eq_false, ite_false]
            constructor
            · intro h
              refine ⟨_, rfl, rfl, rfl, Or.inl ⟨rfl, rfl, ?_⟩⟩
              split_ifs at h with h1 <;> simp_all
            · rintro ⟨d, hd, -, -, (⟨-, -, h⟩ | ⟨hz, -⟩)⟩
              · simp [h]
              · simp at hd; subst hd; simp at hz
          · constructor
            · intro h; split_ifs at h <;> simp_all
            · rintro ⟨d, hd, -, -, (⟨-, hh, -⟩ | ⟨hz, -⟩)⟩
              · simp at hh; exact absurd hh hp
              · simp at hd; subst hd; simp at hz
      all_goals
        simp only [true_or, or_true, ite_true]
        constructor
        · intro h; split_ifs at h <;> simp_all
        · rintro ⟨d, hd, hb, ha, -⟩; simp at hd; subst hd; simp_all

lemma verifyMultiProof_ne_false (W : Wiring) (pi proof : List Word) :
    verifyMultiProof W pi proof ≠ some false := by
  unfold verifyMultiProof
  split_ifs <;> simp

theorem NeverReturnsFalse : Properties.NeverReturnsFalse := by
  intro W P chain pi proof
  unfold verifyForChain
  rcases proof with _ | ⟨p0, t⟩
  · simp
  · simp only
    split_ifs
    · simp
    · rcases P chain with _ | d
      · simp
      · simp only
        rcases getProofMode d.mask with _ | req
        · simp
        · simp only
          split_ifs
          · simp
          · simp
          · simp
          · exact verifyMultiProof_ne_false W pi (p0 :: t)

lemma none_of_not_true {v : Verdict} (h1 : v ≠ some false) (h2 : v ≠ some true) : v = none := by
  rcases v with _ | _ | _ <;> simp_all

theorem NoDowngrade : Properties.NoDowngrade := by
  intro W P chain pi proof d hP
  constructor
  · intro hz hh
    apply none_of_not_true (NeverReturnsFalse W P chain pi proof)
    intro h
    obtain ⟨d', hd', -, -, (⟨hz', -⟩ | ⟨-, c, ab, zk, rest, he, -⟩)⟩ := (AcceptIff W P chain pi proof).1 h
    · rw [hP] at hd'; cases hd'; simp_all
    · subst he; simp at hh; exact absurd hh (by decide)
  · intro hz hh
    apply none_of_not_true (NeverReturnsFalse W P chain pi proof)
    intro h
    obtain ⟨d', hd', -, -, (⟨-, hh', -⟩ | ⟨hz', -⟩)⟩ := (AcceptIff W P chain pi proof).1 h
    · rw [hh] at hh'; simp at hh'; exact absurd hh' (by decide)
    · rw [hP] at hd'; cases hd'; simp_all

theorem TrailingWordsIgnored : Properties.TrailingWordsIgnored := by
  intro W P chain pi proof extra d hP hz h
  obtain ⟨d', hd', hb, ha, (⟨hz', -⟩ | ⟨hz', c, ab, zk, rest, he, h1, h2, h3, h4⟩)⟩ :=
    (AcceptIff W P chain pi proof).1 h
  · rw [hP] at hd'; cases hd'; simp_all
  · refine (AcceptIff W P chain pi (proof ++ extra)).2
      ⟨d', hd', hb, ha, Or.inr ⟨hz', c, ab, zk, rest ++ extra, ?_, h1, h2, h3, h4⟩⟩
    subst he; simp

theorem ShiftCheckRedundant : Properties.ShiftCheckRedundant := by
  intro W P chain pi proof
  unfold verifyForChainNoShiftCheck verifyForChain
  rcases proof with _ | ⟨p0, t⟩
  · rfl
  · simp only
    by_cases hs : p0.val >>> 8 = 0
    · simp [hs]
    · simp only [ne_eq, hs, not_false_eq_true, ite_true]
      rcases P chain with _ | d
      · rfl
      · simp only
        rcases hm : getProofMode d.mask with _ | req
        · rfl
        · simp only
          have hne : p0 ≠ req := by
            rintro rfl
            rcases getProofMode_some hm with rfl | rfl
            · exact hs shift_two
            · exact hs shift_five
          simp [hne]

/-! ## `ZKsyncOSVerifier` -/

lemma mock_ne_plonk : (MOCK_TYPE : Word) ≠ PLONK_TYPE := by decide

theorem ZkosAcceptIff : Properties.ZkosAcceptIff := by
  intro K fl pi proof
  constructor
  · intro h
    rcases proof with _ | ⟨p0, _ | ⟨p1, w⟩⟩
    · simp [zkosVerify, METADATA_LENGTH] at h
    · simp [zkosVerify, METADATA_LENGTH] at h
    · have hpi : pi ≠ [] := by
        rintro rfl
        simp [zkosVerify, METADATA_LENGTH] at h
      have hl : pi.length ≠ 0 := by simpa using hpi
      refine ⟨hpi, ?_⟩
      simp only [zkosVerify, METADATA_LENGTH, List.length_cons, List.getD_cons_zero,
        List.getD_cons_succ, List.drop_succ_cons, List.drop_zero, computeZKsyncOSHash, hl,
        if_false, show ¬ (w.length + 1 + 1 < 2) by omega] at h
      by_cases hp1 : p1 = 0
      · subst hp1
        simp only [ne_eq, not_true_eq_false, if_false] at h
        by_cases hp : p0 = PLONK_TYPE
        · subst hp
          simp only [if_true, Option.some.injEq] at h
          exact Or.inl ⟨w, rfl, h⟩
        · simp only [hp, if_false] at h
          by_cases hm : p0 = MOCK_TYPE
          · subst hm
            simp only [if_true] at h
            cases fl
            · simp at h
            · right
              refine ⟨rfl, ?_⟩
              rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
              · simp [zkosMockVerify, MOCK_PROOF_LENGTH] at h
              · simp [zkosMockVerify, MOCK_PROOF_LENGTH] at h
              · simp only [zkosMockVerify, MOCK_PROOF_LENGTH, List.length_cons, List.length_nil,
                  List.getD_cons_zero, List.getD_cons_succ] at h
                split_ifs at h with h1 h2 h3
                have ha : a = MOCK_MAGIC := by simpa using h2
                have hb : b = batchInput K pi := by simpa using h3
                rw [ha, hb]
              · simp [zkosMockVerify, MOCK_PROOF_LENGTH] at h
          · simp [hm] at h
      · simp only [ne_eq, hp1, not_false_eq_true, if_true] at h
        split_ifs at h
  · rintro ⟨hpi, (⟨w, rfl, hw⟩ | ⟨rfl, rfl⟩)⟩
    · have hl : pi.length ≠ 0 := by simpa using hpi
      simp [zkosVerify, METADATA_LENGTH, computeZKsyncOSHash, hl, hw]
    · have hl : pi.length ≠ 0 := by simpa using hpi
      simp [zkosVerify, METADATA_LENGTH, computeZKsyncOSHash, hl, mock_ne_plonk, zkosMockVerify,
        MOCK_PROOF_LENGTH]

/-! ## Production wiring -/

lemma zkos_production_iff (K : Crypto) (pi proof : List Word) :
    zkosVerify K .production pi proof = some true ↔
      pi ≠ [] ∧ ∃ w, proof = PLONK_TYPE :: 0 :: w ∧ K.plonk [batchInput K pi] w = true := by
  rw [ZkosAcceptIff K .production pi proof]
  constructor
  · rintro ⟨hpi, (h | ⟨h, -⟩)⟩
    · exact ⟨hpi, h⟩
    · cases h
  · rintro ⟨hpi, h⟩
    exact ⟨hpi, Or.inl h⟩

lemma lane_of_airbender {K : Crypto} {pi proof : List Word}
    (h : (productionWiring K).airbender pi proof = some true) : AirbenderAttested K pi := by
  obtain ⟨hpi, w, -, hw⟩ := (zkos_production_iff K pi proof).1 h
  exact ⟨hpi, w, hw⟩

lemma lane_of_zisk {K : Crypto} {pi zk : List Word} (hl : zk.length = ZISK_LEN)
    (h : (productionWiring K).ziskRange pi zk = some true) : ZiskAttested K pi :=
  ⟨zk, hl, by simpa [productionWiring] using h⟩

lemma lanes_of_multi {K : Crypto} {pi proof : List Word}
    (h : verifyMultiProof (productionWiring K) pi proof = some true) :
    AirbenderAttested K pi ∧ ZiskAttested K pi := by
  obtain ⟨-, -, ab, zk, -, -, -, h2, h3, h4⟩ := (verifyMultiProof_iff _ pi proof).1 h
  exact ⟨lane_of_airbender h3, lane_of_zisk h2 h4⟩

theorem ProductionAcceptsOnlyIfAllRequired : Properties.ProductionAcceptsOnlyIfAllRequired := by
  intro K P chain pi proof h
  obtain ⟨d, hd, hb, ha, (⟨hz, -, h1⟩ | ⟨hz, c, ab, zk, rest, -, -, h2, h3, h4⟩)⟩ :=
    (AcceptIff _ P chain pi proof).1 h
  · exact ⟨d, hd, hb, ha, lane_of_airbender h1, fun h' => by simp_all⟩
  · exact ⟨d, hd, hb, ha, lane_of_airbender h3, fun _ => lane_of_zisk h2 h4⟩

theorem ProductionAcceptIff : Properties.ProductionAcceptIff := by
  intro K P chain pi proof
  rw [AcceptIff (productionWiring K) P chain pi proof]
  constructor
  · rintro ⟨d, hd, hb, ha, (⟨hz, -, h1⟩ | ⟨hz, c, ab, zk, rest, rfl, hab, hzk, h3, h4⟩)⟩
    · obtain ⟨hpi, hw⟩ := (zkos_production_iff K pi proof).1 h1
      exact ⟨d, hd, hb, ha, hpi, Or.inl ⟨hz, hw⟩⟩
    · obtain ⟨hpi, w, rfl, hw⟩ := (zkos_production_iff K pi ab).1 h3
      refine ⟨d, hd, hb, ha, hpi, Or.inr ⟨hz, c, w, zk, rest, rfl, ?_, hzk, hw, ?_⟩⟩
      · simpa using hab.symm
      · simpa [productionWiring] using h4
  · rintro ⟨d, hd, hb, ha, hpi, (⟨hz, w, rfl, hw⟩ | ⟨hz, c, w, zk, rest, rfl, hc, hzk, hw, hz'⟩)⟩
    · exact ⟨d, hd, hb, ha, Or.inl ⟨hz, rfl, (zkos_production_iff K pi _).2 ⟨hpi, w, rfl, hw⟩⟩⟩
    · refine ⟨d, hd, hb, ha, Or.inr ⟨hz, c, PLONK_TYPE :: 0 :: w, zk, rest, rfl, ?_, hzk,
        (zkos_production_iff K pi _).2 ⟨hpi, w, rfl, hw⟩, ?_⟩⟩
      · simpa using hc.symm
      · simp [productionWiring, hz']

/-- The witness `Crypto`: PLONK accepts only `[7]`, ZiSK only 24 nines. -/
def witnessCrypto : Crypto where
  keccakPacked := fun _ => 0
  plonk := fun _ w => decide (w = [7])
  zisk := fun _ w => decide (w = List.replicate 24 9)

theorem MultiModeWitness : Properties.MultiModeWitness := by
  refine ⟨witnessCrypto, fun _ => some ⟨false, false, false⟩, 0, [0],
    MULTI_TYPE :: 0 :: 3 :: ((PLONK_TYPE :: 0 :: [7]) ++ List.replicate 24 9 ++ []),
    ?_, ?_, rfl, ?_, ?_⟩
  · intro a w h; simpa [witnessCrypto] using h
  · intro p w h; simpa [witnessCrypto] using h
  · exact (ProductionAcceptIff witnessCrypto _ 0 [0] _).2 ⟨_, rfl, rfl, rfl, by simp,
      Or.inr ⟨rfl, 3, [7], List.replicate 24 9, [], rfl, rfl, by simp [ZISK_LEN],
        by simp [witnessCrypto], by simp [witnessCrypto]⟩⟩
  · exact (NoDowngrade _ _ 0 [0] _ ⟨false, false, false⟩ rfl).1 rfl rfl

/-! ## Countermodels -/

/-- PLONK accepts everything, ZiSK nothing. -/
def airbenderOnlyCrypto : Crypto where
  keccakPacked := fun _ => 0
  plonk := fun _ _ => true
  zisk := fun _ _ => false

theorem SubmittedDispatchDowngrades : Properties.SubmittedDispatchDowngrades := by
  refine ⟨airbenderOnlyCrypto, fun _ => some ⟨false, false, false⟩, 0, [0], [PLONK_TYPE, 0],
    fun _ _ => rfl, rfl, ?_, ?_, ?_⟩
  · decide
  · exact (NoDowngrade _ _ 0 [0] _ ⟨false, false, false⟩ rfl).1 rfl rfl
  · rintro ⟨w, -, h⟩; simp [airbenderOnlyCrypto] at h

theorem NoTypeCheckStillSafe : Properties.NoTypeCheckStillSafe := by
  intro K P chain pi proof h
  unfold verifyForChainNoTypeCheck at h
  rcases proof with _ | ⟨p0, t⟩
  · simp at h
  · simp only at h
    by_cases hs : p0.val >>> 8 = 0
    · simp only [hs, ne_eq, not_true_eq_false, if_false] at h
      rcases hP : P chain with _ | ⟨b, a, z⟩
      · simp [hP] at h
      · simp only [hP, getProofMode_mask] at h
        cases b <;> cases a
        case false.false =>
          cases z
          · simp only [Bool.false_eq_true, or_self, if_false,
              show MULTI_TYPE ≠ PLONK_TYPE by decide] at h
            obtain ⟨h1, h2⟩ := lanes_of_multi h
            exact ⟨_, rfl, rfl, rfl, h1, fun _ => h2⟩
          · simp only [Bool.false_eq_true, or_self, if_false, if_true] at h
            by_cases h1 : (productionWiring K).airbender pi (p0 :: t) = some true
            · exact ⟨_, rfl, rfl, rfl, lane_of_airbender h1, fun h' => by simp at h'⟩
            · simp [h1] at h
        all_goals simp at h
    · simp [hs] at h

/-- PLONK accepts nothing, ZiSK everything. -/
def ziskOnlyCrypto : Crypto where
  keccakPacked := fun _ => 0
  plonk := fun _ _ => false
  zisk := fun _ _ => true

theorem AirbenderLaneMockLoadBearing : Properties.AirbenderLaneMockLoadBearing := by
  refine ⟨ziskOnlyCrypto, fun _ => some ⟨false, false, false⟩, 0, [0],
    MULTI_TYPE :: 0 :: 4 ::
      ([MOCK_TYPE, 0, MOCK_MAGIC, batchInput ziskOnlyCrypto [0]] ++ List.replicate 24 0 ++ []),
    fun _ _ => rfl, rfl, ?_, ?_⟩
  · refine (AcceptIff _ _ 0 [0] _).2 ⟨_, rfl, rfl, rfl, Or.inr ⟨rfl, 4, _, _, [], rfl, rfl,
      by simp [ZISK_LEN], ?_, rfl⟩⟩
    exact (ZkosAcceptIff ziskOnlyCrypto .testnet [0] _).2 ⟨by simp, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨-, w, h⟩; simp [ziskOnlyCrypto] at h

/-! ## Testnet wrappers -/

theorem TestnetAcceptIff : Properties.TestnetAcceptIff := by
  intro K inner sender pi proof
  rcases proof with _ | ⟨p0, t⟩
  · simp [testnetVerify]
  · by_cases hb : p0.val &&& 255 = MOCK_TYPE.val
    · simp only [testnetVerify, hb, if_true]
      rcases t with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, rest⟩⟩⟩
      · simp [multiMockVerify]
      · simp [multiMockVerify]
      · simp [multiMockVerify]
      · simp only [multiMockVerify, List.length_cons, List.getD_cons_succ, List.getD_cons_zero]
        constructor
        · intro h
          split_ifs at h with h1 h2 h3
          have hp1 : p1 = 0 := by simpa using h2
          have hp23 : p2 = MOCK_MAGIC ∧ p3 = batchInput K pi := by
            constructor
            · by_contra hc; exact h3 (Or.inl hc)
            · by_contra hc; exact h3 (Or.inr hc)
          right; left
          exact ⟨p0, rest, by rw [hp1, hp23.1, hp23.2], hb⟩
        · rintro (h | ⟨q0, rest', he, -⟩ | ⟨q0, rest', he, hne, -⟩)
          · cases h
          · simp only [List.cons.injEq] at he
            obtain ⟨-, rfl, rfl, rfl, -⟩ := he
            simp
          · simp only [List.cons.injEq] at he
            exact absurd hb (he.1 ▸ hne)
    · simp only [testnetVerify, hb, if_false]
      constructor
      · intro h
        exact Or.inr (Or.inr ⟨p0, t, rfl, hb, h⟩)
      · rintro (h | ⟨q0, rest', he, hq⟩ | ⟨q0, rest', he, -, h⟩)
        · cases h
        · simp only [List.cons.injEq] at he
          exact absurd (he.1 ▸ hq) hb
        · exact h

lemma reject_of_head (W : Wiring) (P : Policy) (chain : Address) (pi t : List Word) (p0 : Word)
    (h2 : p0 ≠ PLONK_TYPE) (h5 : p0 ≠ MULTI_TYPE) :
    verifyForChain W P chain pi (p0 :: t) = none := by
  apply none_of_not_true (NeverReturnsFalse W P chain pi _)
  intro h
  obtain ⟨d, -, -, -, (⟨-, hh, -⟩ | ⟨-, c, ab, zk, rest, he, -⟩)⟩ := (AcceptIff W P chain pi _).1 h
  · simp at hh; exact h2 hh
  · simp only [List.cons.injEq] at he; exact h5 he.1

theorem TestnetAcceptsFalseProof : Properties.TestnetAcceptsFalseProof := by
  intro K hK P sender pi
  refine ⟨rfl, ?_, ?_, ?_, rfl, ?_⟩
  · exact (TestnetAcceptIff K _ sender pi _).2 (Or.inr (Or.inl ⟨MOCK_TYPE, [], rfl, by decide⟩))
  · rintro ⟨-, w, h⟩; simp [hK.1] at h
  · rintro ⟨w, -, h⟩; simp [hK.2] at h
  · exact reject_of_head _ P sender pi _ MOCK_TYPE (by decide) (by decide)

lemma low_byte_259 : (259 : Word).val &&& 255 = MOCK_TYPE.val := by decide

theorem TestnetMockTypeIsLowByte : Properties.TestnetMockTypeIsLowByte := by
  intro K inner sender pi
  refine ⟨?_, ?_⟩
  · exact (TestnetAcceptIff K inner sender pi _).2 (Or.inr (Or.inl ⟨259, [], rfl, low_byte_259⟩))
  · intro W P
    exact reject_of_head W P sender pi _ 259 (by decide) (by decide)

lemma isZiskMock_iff (proof : List Word) :
    isZiskMock proof = true ↔
      ∃ p3 t, proof = MOCK_TYPE :: 0 :: MOCK_MAGIC :: p3 :: t ∧ t.length = 20 := by
  constructor
  · intro h
    simp only [isZiskMock, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hlen, h0⟩, h1⟩, h2⟩ := h
    rcases proof with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, t⟩⟩⟩⟩
    · simp [ZISK_LEN] at hlen
    · simp [ZISK_LEN] at hlen
    · simp [ZISK_LEN] at hlen
    · simp [ZISK_LEN] at hlen
    · simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2
      refine ⟨p3, t, by rw [h0, h1, h2], ?_⟩
      simp only [List.length_cons, ZISK_LEN] at hlen
      omega
  · rintro ⟨p3, t, rfl, ht⟩
    simp [isZiskMock, ZISK_LEN, ht]

theorem ZiskTestnetAcceptIff : Properties.ZiskTestnetAcceptIff := by
  intro K inner pi proof
  by_cases hm : isZiskMock proof = true
  · obtain ⟨p3, t, rfl, ht⟩ := (isZiskMock_iff proof).1 hm
    simp only [ziskTestnetVerify, hm, if_true, ziskMockVerify, List.getD_cons_succ,
      List.getD_cons_zero, List.drop_succ_cons, List.drop_zero]
    constructor
    · intro h
      left
      split_ifs at h with h1 h2
      have hp3 : p3 = batchInput K pi := by simpa using h1
      have hall : t.all (fun x => decide (x = 0)) = true := by simpa using h2
      have htz : t = List.replicate 20 0 := by
        refine List.eq_replicate_iff.2 ⟨ht, fun b hb => ?_⟩
        simpa using (List.all_eq_true.1 hall) b hb
      rw [hp3, htz]
    · rintro (h | ⟨h, -⟩)
      · simp only [List.cons.injEq] at h
        obtain ⟨-, -, -, rfl, rfl⟩ := h
        simp
      · simp [hm] at h
  · have hm' : isZiskMock proof = false := by simpa using hm
    simp only [ziskTestnetVerify, hm', Bool.false_eq_true, if_false]
    constructor
    · intro h; exact Or.inr ⟨trivial, h⟩
    · rintro (h | ⟨-, h⟩)
      · exfalso
        apply hm
        rw [h]
        exact (isZiskMock_iff _).2 ⟨_, _, rfl, by simp⟩
      · exact h

end Contracts.MultiProofVerifier
