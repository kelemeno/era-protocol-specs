import EraSpec.Protocol.NativeValueLegs.Properties.RouterRecoveryFrame
import EraSpec.Protocol.NativeValueLegs.Proofs.LegConservationRuns

/-!
# Proofs: the head router recovery satisfies the frame premises through the vault

Every write of the vault's refund of asset `a` is keyed by `a` (the token ledger, supply and tracker
entries of `a`) or, for the base token, moves native value; so for an asset `A ≠ a` the footprint of
`A` is unchanged (`registerIfNeeded_frames`, `trackerFinalize_frames`, `vaultRecover_frames`).  The
router adds only checks and the dispatch to a handler (`HeadRouterRecoveryFramesOthers`).
-/

namespace Contracts.NativeValueLegs

/-! ## `Frames` -/

theorem Frames.refl (cfg : Config) (A : AssetId) (w : World) : Frames cfg A w w :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Frames.trans {cfg : Config} {A : AssetId} {w₁ w₂ w₃ : World} (h₁ : Frames cfg A w₁ w₂)
    (h₂ : Frames cfg A w₂ w₃) : Frames cfg A w₁ w₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1,
    h₂.2.2.2.2.1.trans h₁.2.2.2.2.1, h₂.2.2.2.2.2.trans h₁.2.2.2.2.2⟩

theorem moveToken_frames {cfg : Config} {A a : AssetId} (h : a ≠ A) (w : World) (s d : Address)
    (v : ℕ) : Frames cfg A w (moveToken w a s d v) := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  by_cases hA : A = cfg.baseAsset
  · simp [ledger, hA, moveToken]
  · simp [ledger, hA, moveToken, Function.update_of_ne (Ne.symm h)]

theorem moveNative_frames {cfg : Config} {A : AssetId} (hA : A ≠ cfg.baseAsset) (w : World)
    (s d : Address) (v : ℕ) : Frames cfg A w (moveNative w s d v) := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  simp [ledger, hA, moveNative]

theorem registerIfNeeded_frames {cfg : Config} {A a : AssetId} (h : a ≠ A) {w w' : World}
    (hr : registerIfNeeded cfg w a = some w') : Frames cfg A w w' := by
  unfold registerIfNeeded at hr
  split_ifs at hr <;> simp only [Option.some.injEq] at hr <;> subst hr
  · exact Frames.refl cfg A w
  · exact ⟨rfl, rfl, Function.update_of_ne (Ne.symm h) _ _, rfl, rfl,
      Function.update_of_ne (Ne.symm h) _ _⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, Function.update_of_ne (Ne.symm h) _ _⟩

theorem trackerFinalize_frames {cfg : Config} {A a : AssetId} (h : a ≠ A) {w w' : World}
    {d : Chain} {amount : ℕ} (hf : trackerFinalize cfg w d a amount = some w') :
    Frames cfg A w w' := by
  unfold trackerFinalize at hf
  obtain ⟨w₁, h₁, h₂⟩ := Option.map_eq_some_iff.mp hf
  have hr := registerIfNeeded_frames h h₁
  subst h₂
  refine hr.trans ?_
  have hne := Ne.symm h
  by_cases hn : cfg.originOf a = cfg.thisChain <;>
    by_cases hl : d = cfg.l1Chain ∧ cfg.slIsL1 = true <;>
    simp only [hn, hl, ↓reduceIte] <;>
    exact ⟨rfl, rfl, by simp [Function.update_of_ne hne], rfl, by simp [Function.update_of_ne hne],
      rfl⟩

/-! ## The vault's refund of another asset -/

theorem vaultRecover_frames {cfg : Config} {code : RecoveryCode} {A a : AssetId} (ha : a ≠ A)
    (hdep : ∀ w d md w', code.deploy w d a md = some w' → Frames cfg A w w') {w w' : World}
    {d : Chain} {m : Bytes} (h : vaultRecover cfg code w d a m = some w') : Frames cfg A w w' := by
  unfold vaultRecover at h
  by_cases hp : w.ntvPaused = true
  · simp [hp] at h
  rw [ite_eq_right hp] at h
  cases hdm : code.decodeMint m with
  | none => simp [hdm] at h
  | some md =>
    simp only [hdm] at h
    by_cases hn : RecoveryNeutral cfg a d
    swap
    · simp [hn] at h
    rw [ite_eq_right (not_not.mpr hn)] at h
    by_cases hbase : a = cfg.baseAsset
    · -- the base token: native value moves, `A` is not the base token
      rw [ite_eq_left hbase] at h
      have hA : A ≠ cfg.baseAsset := fun hA' => ha (hbase.trans hA'.symm)
      unfold holderRecover sendValue at h
      split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h
      · exact Frames.refl cfg A w
      · exact moveNative_frames hA w _ _ _
    · rw [ite_eq_right hbase] at h
      obtain ⟨w₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
      refine (trackerFinalize_frames ha h₁).trans ?_
      split_ifs at h₂
      · simp only [Option.some.injEq] at h₂
        subst h₂
        exact moveToken_frames ha w₁ _ _ _
      · exact hdep _ _ _ _ h₂
      · simp only [Option.some.injEq] at h₂
        subst h₂
        exact mintToken_frames ha w₁ _ _

theorem HeadRouterRecoveryFramesOthers : Properties.HeadRouterRecoveryFramesOthers := by
  intro cfg code customBurn A hcode w d cd w' hcd h
  cases cd with
  | other raw =>
    simp only [headParams, headRouterRecover] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    exact Frames.refl cfg A w
  | finalizeDeposit src a m =>
    have ha : a ≠ A := hcd src a m rfl
    simp only [headParams, headRouterRecover] at h
    split_ifs at h
    · exact vaultRecover_frames ha (fun w d md w' => hcode.2 w d a md w' ha) h
    · exact hcode.1 _ w d a m w' ha h

/-! ## Registrations -/

theorem vaultRecover_regMono {cfg : Config} {code : RecoveryCode}
    (hdep : ∀ w d a md w', code.deploy w d a md = some w' → RegMono w w') {w w' : World}
    {d : Chain} {a : AssetId} {m : Bytes} (h : vaultRecover cfg code w d a m = some w') :
    RegMono w w' := by
  unfold vaultRecover at h
  by_cases hp : w.ntvPaused = true
  · simp [hp] at h
  rw [ite_eq_right hp] at h
  cases hdm : code.decodeMint m with
  | none => simp [hdm] at h
  | some md =>
    simp only [hdm] at h
    by_cases hn : RecoveryNeutral cfg a d
    swap
    · simp [hn] at h
    rw [ite_eq_right (not_not.mpr hn)] at h
    by_cases hbase : a = cfg.baseAsset
    · rw [ite_eq_left hbase] at h
      unfold holderRecover sendValue at h
      split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h
      · exact RegMono.refl w
      · exact RegMono.of_eq rfl
    · rw [ite_eq_right hbase] at h
      obtain ⟨w₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
      refine (trackerFinalize_regMono h₁).trans ?_
      split_ifs at h₂
      · simp only [Option.some.injEq] at h₂
        subst h₂
        exact RegMono.of_eq rfl
      · exact hdep _ _ _ _ _ h₂
      · simp only [Option.some.injEq] at h₂
        subst h₂
        exact RegMono.of_eq rfl

theorem HeadCodeFrames : Properties.HeadCodeFrames := by
  intro cfg code customBurn hframes hmono hcustom
  refine ⟨fun A => HeadRouterRecoveryFramesOthers cfg code customBurn A (hframes A), ?_, hcustom⟩
  intro w d cd w' h
  cases cd with
  | other raw =>
    simp only [headParams, headRouterRecover] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    exact RegMono.refl w
  | finalizeDeposit src a m =>
    simp only [headParams, headRouterRecover] at h
    split_ifs at h
    · exact vaultRecover_regMono hmono.2 h
    · exact hmono.1 _ _ _ _ _ _ h

theorem ClaimReturnsCollectedHeadRouter : Properties.ClaimReturnsCollectedHeadRouter := by
  intro cfg code customBurn u starters B w w' hu hp hf hcode hreg h
  exact ClaimReturnsCollected (headParams cfg code customBurn) u starters B w w' hu hp hf
    (HeadRouterRecoveryFramesOthers cfg code customBurn B.destBaseAsset hcode) hreg h

/-! ## Witness -/

theorem wCode_framesOthers (A : AssetId) : CodeFramesOthers wCfg wCode A :=
  ⟨fun _ w _ a _ w' ha h => by
      simp only [wCode, Option.some.injEq] at h
      subst h
      exact mintToken_frames ha w 8 1,
    fun w _ a md w' ha h => by
      simp only [wCode, Option.some.injEq] at h
      subst h
      exact mintToken_frames ha w _ _⟩

theorem wCode_regMono : CodeRegMono wCode :=
  ⟨fun _ w _ a _ w' h => by
      simp only [wCode, Option.some.injEq] at h
      subst h
      exact RegMono.of_eq rfl,
    fun w _ a md w' h => by
      simp only [wCode, Option.some.injEq] at h
      subst h
      exact RegMono.of_eq rfl⟩

theorem HeadRouterClaimWitness : Properties.HeadRouterClaimWitness := by
  refine ⟨wCfg, wCode, wCustomBurn, 5, [wDirect 6, wIndirect 0],
    wBundle 200 [wDirectCall 5 6, wRouterCall 300 0], wWorld, wCode_framesOthers, wCode_regMono,
    wParams_codeFrames.customMono, by decide, wPair_passes, ?_, wCode_framesOthers 200, by decide,
    ⟨wRouterCall 300 0, by simp [wBundle], rfl, 10, 300, [], rfl, by decide⟩, by decide,
    by decide⟩
  exact .cons (wDirect_forms 200 5 6) (.cons (wIndirect_forms 200 300 5 0 (by decide)) .nil)

end Contracts.NativeValueLegs
