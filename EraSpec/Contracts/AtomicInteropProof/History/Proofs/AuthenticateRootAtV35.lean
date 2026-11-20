import EraSpec.Contracts.AtomicInteropProof.History.Properties.AuthenticateRootAtV35
import EraSpec.Contracts.AtomicInteropProof.Proofs.AuthenticateRootAtV35

/-! # Proofs (History): the v35 `_authenticateRoot` refactor, compared with the pin -/

namespace AttackVectors.AuthenticateRootAtV35.History

open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf MerkleSpec.LastLeafFaithful

/-- On a proof whose parsed metadata is not a final node, the v35 hop read is the pin's. -/
theorem authV35_readHop_eq_pin {E : Env} {w : Proof} {md : Metadata}
    (hmd : E.parse w = some md) (hmf : md.finalProofNode = false) :
    readHop E w = readHopPin E w := by
  simp only [readHop, readHopPin, hmd, Option.bind_some, hmf]
  rfl

theorem authenticate_root_refactor_exact_v35 : Properties.AuthenticateRootRefactorExactV35 := by
  intro E roots src batch leafIndex imtRoot w
  unfold authenticateRootV35 authenticateRootPin
  cases hmd : E.parse w with
  | none => rfl
  | some md =>
    simp only [Option.bind_some]
    by_cases hd : md.logLeafProofLen ≠ treeDepth
    · rw [ite_eq_left hd, ite_eq_left hd]
    rw [ite_eq_right hd, ite_eq_right hd]
    cases hok : proveShared E roots src batch leafIndex imtRoot w with
    | none => rfl
    | some ok =>
      simp only [Option.bind_some]
      by_cases hk : ok = false
      · rw [ite_eq_left hk, ite_eq_left hk]
      rw [ite_eq_right hk, ite_eq_right hk]
      have hok' : ok = true := by simpa using hk
      subst hok'
      obtain ⟨pd, hpd, -⟩ := authV35_proveShared_true hok
      obtain ⟨md', hmd', hfeq⟩ := authV35_getProofData_final_eq hpd
      rw [hmd] at hmd'
      cases hmd'
      rw [hpd, Option.bind_some]
      by_cases hf : md.finalProofNode = true
      · rw [ite_eq_left hf, ite_eq_left (hfeq.trans hf)]
      · have hpf : pd.finalProofNode = false := by simpa [hfeq] using hf
        rw [ite_eq_right hf, ite_eq_right (by simpa using hpf)]
        exact read_sl_eq_parsed_v35 E src batch leafIndex imtRoot w pd hpd hpf

theorem end_branch_refactor_exact_v35 : Properties.EndBranchRefactorExactV35 := by
  intro E roots z0 src batch imtRoot w sl hop
  constructor
  · rintro ⟨hauth, hhop, hlast⟩
    obtain ⟨md, hmd, -, hmf, -⟩ := authV35_auth_some hauth
    refine ⟨?_, ?_, hlast⟩
    · rw [← authenticate_root_refactor_exact_v35]; exact hauth
    · rw [← authV35_readHop_eq_pin hmd hmf]; exact hhop
  · rintro ⟨hauth, hhop, hlast⟩
    have hauth' : authenticateRootV35 E roots src batch imtEndLeafIndex imtRoot w = some sl := by
      rw [authenticate_root_refactor_exact_v35]; exact hauth
    obtain ⟨md, hmd, -, hmf, -⟩ := authV35_auth_some hauth'
    exact ⟨hauth', by rw [authV35_readHop_eq_pin hmd hmf]; exact hhop, hlast⟩

theorem AuthenticateRootRefactorExactV35 : Properties.AuthenticateRootRefactorExactV35 :=
  authenticate_root_refactor_exact_v35

theorem EndBranchRefactorExactV35 : Properties.EndBranchRefactorExactV35 :=
  end_branch_refactor_exact_v35

end AttackVectors.AuthenticateRootAtV35.History
