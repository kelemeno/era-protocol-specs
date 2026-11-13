import EraSpec.Contracts.SemVer.Properties.SemVer

/-!
# Proofs: `SemVer` round trips and order
-/

namespace Contracts.SemVer

/-- The bitwise packing as a sum, for `uint32` components. -/
theorem packSemVer_eq {M m p : ℕ} (hM : M < 2 ^ 32) (hm : m < 2 ^ 32) (hp : p < 2 ^ 32) :
    packSemVer M m p = M * 2 ^ 64 + m * 2 ^ 32 + p := by
  have h1 : shl96 m SEMVER_MINOR_OFFSET = m <<< 32 := by
    unfold shl96 SEMVER_MINOR_OFFSET
    rw [Nat.shiftLeft_eq]; apply Nat.mod_eq_of_lt; omega
  have h2 : shl96 M SEMVER_MAJOR_OFFSET = M <<< 64 := by
    unfold shl96 SEMVER_MAJOR_OFFSET
    rw [Nat.shiftLeft_eq]; apply Nat.mod_eq_of_lt; omega
  have h3 : p ||| m <<< 32 = m <<< 32 + p := by
    rw [Nat.or_comm]; exact (Nat.shiftLeft_add_eq_or_of_lt hp m).symm
  have h4 : m <<< 32 + p < 2 ^ 64 := by rw [Nat.shiftLeft_eq]; omega
  have h5 : (m <<< 32 + p) ||| M <<< 64 = M <<< 64 + (m <<< 32 + p) := by
    rw [Nat.or_comm]; exact (Nat.shiftLeft_add_eq_or_of_lt h4 M).symm
  unfold packSemVer
  rw [h1, h2, h3, h5, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  omega

theorem unpackSemVer_eq (v : ℕ) :
    unpackSemVer v = (v / 2 ^ 64 % 2 ^ 32, v / 2 ^ 32 % 2 ^ 32, v % 2 ^ 32) := by
  simp [unpackSemVer, toUint32, SEMVER_MAJOR_OFFSET, SEMVER_MINOR_OFFSET, Nat.shiftRight_eq_div_pow]

theorem major_eq (v : ℕ) : major v = v / 2 ^ 64 % 2 ^ 32 := by simp [major, unpackSemVer_eq]
theorem minor_eq (v : ℕ) : minor v = v / 2 ^ 32 % 2 ^ 32 := by simp [minor, unpackSemVer_eq]
theorem patch_eq (v : ℕ) : patch v = v % 2 ^ 32 := by simp [patch, unpackSemVer_eq]

theorem PackIsPositional : Properties.PackIsPositional := by
  intro M m p hM hm hp
  rw [packSemVer_eq hM hm hp]
  exact ⟨rfl, by omega⟩

theorem UnpackPackRoundTrip : Properties.UnpackPackRoundTrip := by
  intro M m p hM hm hp
  rw [packSemVer_eq hM hm hp, unpackSemVer_eq]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> omega

theorem PackUnpackRoundTrip : Properties.PackUnpackRoundTrip := by
  intro v
  rw [major_eq, minor_eq, patch_eq]
  refine ⟨⟨by omega, by omega, by omega⟩, fun hv => ?_⟩
  rw [packSemVer_eq (by omega) (by omega) (by omega)]
  omega

theorem PackInjective : Properties.PackInjective := by
  intro M m p M' m' p' hM hm hp hM' hm' hp' h
  have h1 := UnpackPackRoundTrip M m p hM hm hp
  rw [h, UnpackPackRoundTrip M' m' p' hM' hm' hp'] at h1
  exact h1.symm

theorem PackOrderIsLexicographic : Properties.PackOrderIsLexicographic := by
  intro M m p M' m' p' hM hm hp hM' hm' hp'
  rw [packSemVer_eq hM hm hp, packSemVer_eq hM' hm' hp']
  simp only [SemVerLt]
  omega

theorem UnpackOrderIsLexicographic : Properties.UnpackOrderIsLexicographic := by
  intro v w hv hw
  rw [unpackSemVer_eq, unpackSemVer_eq]
  simp only [SemVerLt]
  omega

theorem MinorDoesNotDecreaseWhenMajorsZero : Properties.MinorDoesNotDecreaseWhenMajorsZero := by
  intro old new ho hn hlt hMo hMn
  rw [major_eq] at hMo hMn
  rw [minor_eq, minor_eq]
  omega

theorem MajorZeroCheckLoadBearingForMinorDelta :
    Properties.MajorZeroCheckLoadBearingForMinorDelta := by
  refine ⟨5 * 2 ^ 32, 2 ^ 64, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [major_eq]; norm_num
  · rw [minor_eq, minor_eq]; norm_num

theorem UpgradeNonceIsMinorWhenMajorZero : Properties.UpgradeNonceIsMinorWhenMajorZero := by
  intro v hv
  have hn : protocolUpgradeNonce v = v / 2 ^ 32 := by
    simp [protocolUpgradeNonce, SEMVER_MINOR_OFFSET, Nat.shiftRight_eq_div_pow]
  rw [hn, major_eq, minor_eq]
  constructor
  · omega
  · intro h; omega

theorem UpgradeNonceNeedsMajorZero : Properties.UpgradeNonceNeedsMajorZero := by
  refine ⟨2 ^ 64, by norm_num, ?_⟩
  have hn : protocolUpgradeNonce (2 ^ 64) = 2 ^ 64 / 2 ^ 32 := by
    simp [protocolUpgradeNonce, SEMVER_MINOR_OFFSET, Nat.shiftRight_eq_div_pow]
  rw [hn, minor_eq]; norm_num

theorem ToUint96CheckLoadBearing : Properties.ToUint96CheckLoadBearing := by
  refine ⟨⟨0, 2 ^ 96, by norm_num, by norm_num, by norm_num, ?_, ?_⟩, ?_⟩
  · simp [unpackTruncating]
  · simp [unpackChecked]
  · intro t x y hx hy
    unfold unpackChecked at hx hy
    by_cases h1 : x < 2 ^ 96 <;> by_cases h2 : y < 2 ^ 96
    · simp only [h1, h2, ↓reduceIte] at hx hy
      have e : unpackSemVer x = unpackSemVer y := by
        rw [Option.some.inj hx, Option.some.inj hy]
      rw [unpackSemVer_eq, unpackSemVer_eq] at e
      simp only [Prod.mk.injEq] at e
      omega
    · simp only [h2, ↓reduceIte] at hy; exact absurd hy (by simp)
    · simp only [h1, ↓reduceIte] at hx; exact absurd hx (by simp)
    · simp only [h1, ↓reduceIte] at hx; exact absurd hx (by simp)

theorem SemVerWitness : Properties.SemVerWitness := by
  have h1 : packSemVer 0 29 1 = 0x1d00000001 := by
    rw [packSemVer_eq (by norm_num) (by norm_num) (by norm_num)]; norm_num
  have h2 : packSemVer 0 30 0 = 30 * 2 ^ 32 := by
    rw [packSemVer_eq (by norm_num) (by norm_num) (by norm_num)]; norm_num
  refine ⟨h1, ?_, ?_, ?_⟩
  · unfold unpackChecked
    rw [unpackSemVer_eq]
    norm_num
  · rw [h1, h2]; norm_num
  · rw [h2]
    simp [protocolUpgradeNonce, SEMVER_MINOR_OFFSET, Nat.shiftRight_eq_div_pow]

end Contracts.SemVer
