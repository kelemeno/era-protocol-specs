import EraSpec.Contracts.L2InteropCommitmentTree.Properties.CommitmentTreeAtV35
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.CachedRoot
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.InitOnce

/-!
# Proofs: the v35 tree contract's transactions on its whole storage

Proofs of `EraSpec.Contracts.L2InteropCommitmentTree.Properties.CommitmentTreeAtV35`.  The
`FullMerkle` content is `CachedRoot`'s (`cInsert_caches`, for any padding constant) and
`FullMerkle/Proofs/CachedNodes.lean`.  What this file adds is the run invariant of the v35
machine: every state of a run from the predeploy's storage is that storage or a state whose list
state is reached and valid and whose storage caches its leaf hashes padded with `zE`.  The walk
enters only through `search_yields_guard`, which holds for every number of hops.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract MerkleSpec MerkleSpec.Verifier AttackVectors.CapacityInvariant

/-! ## The walk and the setup call -/

/-- On a valid tree the v35 checks give the guard at the walk's exit index. -/
lemma insertChecksAtV35_guard {T : Tree} (hV : Valid T) {v : UInt256} {hint low : ℕ}
    (hc : InsertChecksAtV35 T v hint low) : InsertGuard T v low := by
  obtain ⟨hops, hs⟩ := hc.walk
  exact search_yields_guard hV hc.initialized hc.nonzero hc.unregistered hc.hintInBounds
    hc.hintBelow hs

/-- `IndexedMerkleTree.setup`'s calls on the predeploy's storage, with any padding constant. -/
theorem cInitL2AtV35_predeploy (h : Hash) (hl : LeafHash) (zE : UInt256) :
    ∃ S : CState, cInitL2AtV35 h hl zE cPredeployAtV35 = some S ∧ S.tree = setup
      ∧ S.toH = hSetup ∧ FullMerkle.Represents h zE [hl ⟨0, 0, 0⟩] S.fm := by
  have hR₀ := (FullMerkle.setup_represents_empty h zE).1
  obtain ⟨F, hp, hR, hd⟩ :=
    FullMerkle.pushNewLeaf_computes_root h zE [] _ (hl ⟨0, 0, 0⟩) hR₀
  refine ⟨⟨setup, F⟩, ?_, rfl, ?_, ?_⟩
  · show (FullMerkle.pushNewLeaf h (FullMerkle.setup FullMerkle.FullTree.empty zE).1
        (hl ⟨0, 0, 0⟩)).map (fun r => (⟨setupWrites predeploy, r.1⟩ : CState)) = some ⟨setup, F⟩
    rw [hp, Option.map_some, setupWrites_predeploy]
  · show (⟨setup, ⟨F.leafNumber, F.height⟩⟩ : HState) = ⟨setup, setupDims⟩
    rw [hd]
    rfl
  · simpa using hR

/-! ## The run invariant -/

/-- What holds at every initialized state of a run from the predeploy's storage. -/
def InvAtV35 (h : Hash) (hl : LeafHash) (zE : UInt256) (S : CState) : Prop :=
  Reaches setup S.tree ∧ Valid S.tree ∧ HReaches hSetup S.toH
    ∧ FullMerkle.Represents h zE (leafHashes hl S.tree) S.fm

/-- The state `initL2()` leaves on the predeploy's storage satisfies the invariant. -/
lemma invAtV35_of_init {h : Hash} {hl : LeafHash} {zE : UInt256} {S : CState}
    (hS : cInitL2AtV35 h hl zE cPredeployAtV35 = some S) : InvAtV35 h hl zE S := by
  obtain ⟨S₀, hS₀, htree, htoH, hRep⟩ := cInitL2AtV35_predeploy h hl zE
  rw [hS] at hS₀
  cases hS₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [htree]; exact Reaches.refl
  · rw [htree]; exact setup_valid
  · rw [htoH]; exact HReaches.refl
  · rw [htree]; exact hRep

/-- `root()` of a state whose storage caches its leaf hashes is the published root of its view. -/
lemma root_eq_published_atV35 {h : Hash} {zE : UInt256} {hl : LeafHash} {S : CState}
    (hR : FullMerkle.Represents h zE (leafHashes hl S.tree) S.fm) :
    S.root = some (S.toH.root h zE hl) := by
  rw [CState.root, FullMerkle.root_is_fold h zE _ S.fm hR]
  rfl

/-- A guarded insert from an invariant state: it does not revert, the list state becomes
`insert`, the invariant is kept, the dimensions move as `hInsert`, and the returned root is the
stored one and the fold. -/
lemma invAtV35_guarded_insert {h : Hash} {hl : LeafHash} {zE : UInt256} {S : CState}
    {v : UInt256} {low : ℕ} (hI : InvAtV35 h hl zE S) (hg : InsertGuard S.tree v low) :
    ∃ (S' : CState) (r : UInt256), cInsert h hl S v low = some (S', r)
      ∧ S'.tree = insert S.tree v low ∧ InvAtV35 h hl zE S' ∧ S'.toH = hInsert S.toH v low
      ∧ S'.root = some r ∧ r = (hInsert S.toH v low).root h zE hl := by
  obtain ⟨hRe, hV, hH, hRep⟩ := hI
  obtain ⟨S', r, hins, htree, htoH, hRep', hr⟩ :=
    cInsert_caches h zE hl S v low hRep hg.inBounds
  have hroot : S'.root = some r := by
    rw [root_eq_published_atV35 hRep', hr]
    rfl
  refine ⟨S', r, hins, htree, ⟨?_, ?_, ?_, hRep'⟩, htoH, hroot, ?_⟩
  · rw [htree]; exact Reaches.tail hRe hg
  · rw [htree]; exact insert_preserves_valid hV hg
  · rw [htoH]; exact HReaches.tail hH hg
  · rw [hr, ← htoH]
    rfl

/-- A successful v35 insert from an invariant state: the guard holds at the exit index, the
invariant is kept, the dimensions move as `hInsert`, and the returned root is the stored one. -/
lemma invAtV35_insert {h : Hash} {hl : LeafHash} {zE : UInt256} {S S' : CState} {v : UInt256}
    {hint low : ℕ} {r : UInt256} (hI : InvAtV35 h hl zE S)
    (hc : InsertChecksAtV35 S.tree v hint low)
    (hins : cInsert h hl S v low = some (S', r)) :
    InvAtV35 h hl zE S' ∧ InsertGuard S.tree v low ∧ S'.toH = hInsert S.toH v low
      ∧ S'.root = some r ∧ r = (hInsert S.toH v low).root h zE hl := by
  have hg := insertChecksAtV35_guard hI.2.1 hc
  obtain ⟨S'', r'', hins', _, hI', htoH, hroot, hr⟩ := invAtV35_guarded_insert hI hg
  rw [hins] at hins'
  obtain ⟨hS', hr'⟩ := Prod.mk.inj (Option.some.inj hins')
  subst hS' hr'
  exact ⟨hI', hg, htoH, hroot, hr⟩

/-- One step from the predeploy's storage: only the upgrader's `initL2()` succeeds, and it leaves
the storage `cInitL2AtV35` writes. -/
lemma cTxStepAtV35_from_predeploy {h : Hash} {hl : LeafHash} {zE : UInt256} {K : Roles}
    {c : Caller} {call : Call} {S' : CState}
    (hs : CTxStepAtV35 h hl zE K cPredeployAtV35 c call S') :
    call = .initL2 ∧ c = K.upgrader ∧ cInitL2AtV35 h hl zE cPredeployAtV35 = some S' := by
  rcases hs with ⟨hc, _, hinit⟩ | ⟨_, hchk, _⟩
  · exact ⟨rfl, hc, hinit⟩
  · exact absurd hchk.initialized predeploy_not_initialized

/-- One step from an invariant state: an insert at a guarded exit index, never an `initL2()`. -/
lemma cTxStepAtV35_from_inv {h : Hash} {hl : LeafHash} {zE : UInt256} {K : Roles}
    {S S' : CState} {c : Caller} {call : Call} (hI : InvAtV35 h hl zE S)
    (hs : CTxStepAtV35 h hl zE K S c call S') :
    ∃ (v : UInt256) (hint low : ℕ) (r : UInt256), call = .insert v hint ∧ c = K.appender
      ∧ WalkExitsAtV35 S.tree v hint low ∧ InsertGuard S.tree v low
      ∧ cInsert h hl S v low = some (S', r) ∧ InvAtV35 h hl zE S'
      ∧ S'.toH = hInsert S.toH v low ∧ S'.root = some r
      ∧ r = (hInsert S.toH v low).root h zE hl := by
  cases hs with
  | initL2 _ hlc _ => exact absurd hlc (Nat.pos_iff_ne_zero.mp hI.2.1.occupied)
  | insert hc hchk hins =>
    obtain ⟨hI', hg, htoH, hroot, hr⟩ := invAtV35_insert hI hchk hins
    exact ⟨_, _, _, _, rfl, hc, hchk.walk, hg, hins, hI', htoH, hroot, hr⟩

/-- **The run invariant.** -/
theorem cTxRunAtV35_inv {h : Hash} {hl : LeafHash} {zE : UInt256} {K : Roles}
    {R : ℕ → CState} {tx : Trace} (hR : CTxRunAtV35 h hl zE K R tx)
    (h0 : R 0 = cPredeployAtV35) : ∀ n : ℕ, R n = cPredeployAtV35 ∨ InvAtV35 h hl zE (R n) := by
  intro n
  induction n with
  | zero => exact Or.inl h0
  | succ n ih =>
    rcases hR n with ⟨_, heq⟩ | ⟨c, call, _, hs⟩
    · rw [heq]; exact ih
    · rcases ih with hpre | hI
      · rw [hpre] at hs
        exact Or.inr (invAtV35_of_init (cTxStepAtV35_from_predeploy hs).2.2)
      · obtain ⟨_, _, _, _, _, _, _, _, _, hI', _⟩ := cTxStepAtV35_from_inv hI hs
        exact Or.inr hI'

/-- Once a state of a run satisfies the invariant, every later state does. -/
lemma cTxRunAtV35_inv_from {h : Hash} {hl : LeafHash} {zE : UInt256} {K : Roles}
    {R : ℕ → CState} {tx : Trace} (hR : CTxRunAtV35 h hl zE K R tx) {m : ℕ}
    (hm : InvAtV35 h hl zE (R m)) : ∀ j : ℕ, InvAtV35 h hl zE (R (m + j)) := by
  intro j
  induction j with
  | zero => exact hm
  | succ j ih =>
    rcases hR (m + j) with ⟨_, heq⟩ | ⟨c, call, _, hs⟩
    · rw [← Nat.add_assoc, heq]; exact ih
    · obtain ⟨_, _, _, _, _, _, _, _, _, hI', _⟩ := cTxStepAtV35_from_inv ih hs
      rw [← Nat.add_assoc]; exact hI'

/-- From an invariant state on, a run is a `CachedRoot.CRun`. -/
lemma cRun_of_cTxRunAtV35 {h : Hash} {hl : LeafHash} {zE : UInt256} {K : Roles}
    {R : ℕ → CState} {tx : Trace} (hR : CTxRunAtV35 h hl zE K R tx) {m : ℕ}
    (hm : InvAtV35 h hl zE (R m)) : CRun h hl (fun n => R (m + n)) := by
  intro j
  rcases hR (m + j) with ⟨_, heq⟩ | ⟨c, call, _, hs⟩
  · exact Or.inl heq
  · obtain ⟨v, _, low, r, _, _, _, hg, hins, _⟩ :=
      cTxStepAtV35_from_inv (cTxRunAtV35_inv_from hR hm j) hs
    exact Or.inr ⟨v, low, r, hg, hins⟩

/-- A successful transaction is a step of the run. -/
lemma cTxRunAtV35_step {h : Hash} {hl : LeafHash} {zE : UInt256} {K : Roles} {R : ℕ → CState}
    {tx : Trace} (hR : CTxRunAtV35 h hl zE K R tx) {n : ℕ} {c : Caller} {call : Call}
    (htx : tx n = some (c, call)) : CTxStepAtV35 h hl zE K (R n) c call (R (n + 1)) := by
  rcases hR n with ⟨hnone, _⟩ | ⟨c', call', htx', hs⟩
  · rw [htx] at hnone; cases hnone
  · rw [htx] at htx'
    obtain ⟨hc, hcall⟩ := Prod.mk.inj (Option.some.inj htx')
    subst hc hcall
    exact hs

/-- An idle step leaves the storage unchanged. -/
lemma cTxRunAtV35_idle {h : Hash} {hl : LeafHash} {zE : UInt256} {K : Roles} {R : ℕ → CState}
    {tx : Trace} (hR : CTxRunAtV35 h hl zE K R tx) {n : ℕ} (htx : tx n = none) :
    R (n + 1) = R n := by
  rcases hR n with ⟨_, heq⟩ | ⟨_, _, htx', _⟩
  · exact heq
  · rw [htx] at htx'; cases htx'

/-- The predeploy's storage has no root: `root()` reads `_nodes[_height][0]` of empty storage
and reverts. -/
lemma cPredeployAtV35_root : cPredeployAtV35.root = none := rfl

/-! ## Setup -/

theorem cInitL2AtV35_on_predeploy (h : Hash) (hl : LeafHash) (zE : UInt256) :
    (∃ S : CState, cInitL2AtV35 h hl zE cPredeployAtV35 = some S ∧ S.tree = setup
      ∧ S.toH = hSetup ∧ FullMerkle.Represents h zE [hl ⟨0, 0, 0⟩] S.fm)
    ∧ (∀ (K : Roles) (c : Caller) (S' : CState),
        CTxStepAtV35 h hl zE K cPredeployAtV35 c .initL2 S'
          ↔ c = K.upgrader ∧ cInitL2AtV35 h hl zE cPredeployAtV35 = some S')
    ∧ ∀ (K : Roles) (c : Caller) (v : UInt256) (hint : ℕ) (S' : CState),
        ¬ CTxStepAtV35 h hl zE K cPredeployAtV35 c (.insert v hint) S' := by
  refine ⟨cInitL2AtV35_predeploy h hl zE, ?_, ?_⟩
  · intro K c S'
    constructor
    · intro hs
      obtain ⟨_, hc, hinit⟩ := cTxStepAtV35_from_predeploy hs
      exact ⟨hc, hinit⟩
    · rintro ⟨hc, hinit⟩
      exact CTxStepAtV35.initL2 hc rfl hinit
  · intro K c v hint S' hs
    exact absurd (cTxStepAtV35_from_predeploy hs).1 (by simp)

theorem cInitL2AtV35_at_pin_padding (h : Hash) (hl : LeafHash) :
    cInitL2AtV35 h hl (zeroLeafHash hl) cPredeployAtV35 = cSetup h hl := by
  show (FullMerkle.pushNewLeaf h (FullMerkle.setup FullMerkle.FullTree.empty (zeroLeafHash hl)).1
      (hl ⟨0, 0, 0⟩)).map (fun r => (⟨setupWrites predeploy, r.1⟩ : CState)) = _
  rw [setupWrites_predeploy]
  rfl

/-! ## The shape of a run -/

theorem cTxRunAtV35_shape (h : Hash) (hl : LeafHash) (zE : UInt256) (K : Roles)
    (R : ℕ → CState) (tx : Trace) (hR : CTxRunAtV35 h hl zE K R tx)
    (h0 : R 0 = cPredeployAtV35) :
    (∀ n : ℕ, R n = cPredeployAtV35 ∧ tx n = none)
    ∨ ∃ k : ℕ, (∀ n ≤ k, R n = cPredeployAtV35) ∧ (∀ n < k, tx n = none)
        ∧ tx k = some (K.upgrader, .initL2)
        ∧ cInitL2AtV35 h hl zE cPredeployAtV35 = some (R (k + 1))
        ∧ (∀ n : ℕ, k < n → ∀ c : Caller, tx n ≠ some (c, .initL2))
        ∧ CRun h hl (fun n => R (k + 1 + n)) := by
  classical
  by_cases hex : ∃ n, tx n ≠ none
  · right
    let k := Nat.find hex
    have hk : tx k ≠ none := Nat.find_spec hex
    have hbefore : ∀ n < k, tx n = none := fun n hn => not_not.mp (Nat.find_min hex hn)
    have hpre : ∀ n ≤ k, R n = cPredeployAtV35 := by
      intro n hn
      induction n with
      | zero => exact h0
      | succ n ih =>
        rw [cTxRunAtV35_idle hR (hbefore n (by omega))]
        exact ih (by omega)
    obtain ⟨⟨c, call⟩, hck⟩ := Option.ne_none_iff_exists'.mp hk
    have hs := cTxRunAtV35_step hR hck
    rw [hpre k le_rfl] at hs
    obtain ⟨hcall, hc, hinit⟩ := cTxStepAtV35_from_predeploy hs
    subst hcall hc
    have hI : InvAtV35 h hl zE (R (k + 1)) := invAtV35_of_init hinit
    refine ⟨k, hpre, hbefore, hck, hinit, ?_, cRun_of_cTxRunAtV35 hR hI⟩
    intro n hn c' htx
    obtain ⟨j, rfl⟩ : ∃ j, n = k + 1 + j := ⟨n - (k + 1), by omega⟩
    obtain ⟨_, _, _, _, hcall', _⟩ :=
      cTxStepAtV35_from_inv (cTxRunAtV35_inv_from hR hI j) (cTxRunAtV35_step hR htx)
    cases hcall'
  · left
    have hnone : ∀ n, tx n = none := fun n => not_not.mp (not_exists.mp hex n)
    intro n
    refine ⟨?_, hnone n⟩
    induction n with
    | zero => exact h0
    | succ n ih => rw [cTxRunAtV35_idle hR (hnone n)]; exact ih

theorem cTxRunAtV35_at_pin_padding (h : Hash) (hl : LeafHash) (K : Roles) (R : ℕ → CState)
    (tx : Trace) (hR : CTxRunAtV35 h hl (zeroLeafHash hl) K R tx)
    (h0 : R 0 = cPredeployAtV35) (k : ℕ) (hk : tx k = some (K.upgrader, .initL2)) :
    cSetup h hl = some (R (k + 1)) ∧ CRun h hl (fun n => R (k + 1 + n)) := by
  have hs := cTxRunAtV35_step hR hk
  rcases cTxRunAtV35_inv hR h0 k with hpre | hI
  · rw [hpre] at hs
    obtain ⟨_, _, hinit⟩ := cTxStepAtV35_from_predeploy hs
    rw [cInitL2AtV35_at_pin_padding] at hinit
    exact ⟨hinit, cRun_of_cTxRunAtV35 hR (invAtV35_of_init
      (by rw [cInitL2AtV35_at_pin_padding]; exact hinit))⟩
  · obtain ⟨_, _, _, _, hcall, _⟩ := cTxStepAtV35_from_inv hI hs
    cases hcall

theorem cTxRunAtV35_insert_is_guarded (h : Hash) (hl : LeafHash) (zE : UInt256) (K : Roles)
    (R : ℕ → CState) (tx : Trace) (hR : CTxRunAtV35 h hl zE K R tx)
    (h0 : R 0 = cPredeployAtV35) (n : ℕ) (c : Caller) (v : UInt256) (hint : ℕ)
    (htx : tx n = some (c, .insert v hint)) :
    c = K.appender
      ∧ ∃ (low : ℕ) (r : UInt256), WalkExitsAtV35 (R n).tree v hint low
        ∧ InsertGuard (R n).tree v low
        ∧ cInsert h hl (R n) v low = some (R (n + 1), r)
        ∧ (R (n + 1)).toH = hInsert (R n).toH v low
        ∧ (R (n + 1)).root = some r
        ∧ r = (hInsert (R n).toH v low).root h zE hl := by
  have hs := cTxRunAtV35_step hR htx
  rcases cTxRunAtV35_inv hR h0 n with hpre | hI
  · rw [hpre] at hs
    obtain ⟨hcall, _, _⟩ := cTxStepAtV35_from_predeploy hs
    cases hcall
  · obtain ⟨v', hint', low, r, hcall, hc, hw, hg, hins, _, htoH, hroot, hr⟩ :=
      cTxStepAtV35_from_inv hI hs
    obtain ⟨rfl, rfl⟩ := Call.insert.inj hcall
    exact ⟨hc, low, r, hw, hg, hins, htoH, hroot, hr⟩

/-! ## The stored root -/

theorem cTxRunAtV35_stored_root_is_published (h : Hash) (hl : LeafHash) (zE : UInt256)
    (K : Roles) (R : ℕ → CState) (tx : Trace) (hR : CTxRunAtV35 h hl zE K R tx)
    (h0 : R 0 = cPredeployAtV35) (n : ℕ) :
    R n = cPredeployAtV35
      ∨ (Reaches setup (R n).tree ∧ Valid (R n).tree ∧ HReaches hSetup (R n).toH
          ∧ (R n).fm.leafNumber = (R n).tree.leafCount
          ∧ (R n).fm.height = fmHeight (R n).tree.leafCount
          ∧ FullMerkle.Represents h zE (leafHashes hl (R n).tree) (R n).fm
          ∧ (R n).root = some ((R n).toH.root h zE hl)) := by
  rcases cTxRunAtV35_inv hR h0 n with hpre | ⟨hRe, hV, hH, hRep⟩
  · exact Or.inl hpre
  · refine Or.inr ⟨hRe, hV, hH, ?_, ?_, hRep, root_eq_published_atV35 hRep⟩
    · rw [hRep.leafNumber_eq, leafHashes_length]
    · exact congrArg TreeDims.height (hReaches_dims hH)

/-! ## The contract's own proofs against the stored root -/

/-- The contract's path for leaf `i`: `merklePath(i)` on storage caching `leafHashes`. -/
lemma contract_path_atV35 {h : Hash} {z0 : UInt256} {hl : LeafHash} {S : CState}
    (hR : FullMerkle.Represents h z0 (leafHashes hl S.tree) S.fm) {i : ℕ}
    (hi : i < S.tree.leafCount) :
    S.merklePath i
      = some ((List.range S.fm.height).map (honestSibs h z0 (leafHashes hl S.tree) i)) :=
  FullMerkle.merklePath_is_honest h z0 _ S.fm i hR (by rw [leafHashes_length]; exact hi)

/-- An accepted path at height `H` over the honest stream is accepted over the contract's
returned path, which has length `H`. -/
lemma pathAccepts_contract_atV35 {h : Hash} {z0 : UInt256} {L : List UInt256} {R : UInt256}
    {H i : ℕ} {x : UInt256} (hA : PathAccepts h R (honestSibs h z0 L i) H i x) :
    PathAccepts h R (FullMerkle.pathSibs ((List.range H).map (honestSibs h z0 L i)))
      ((List.range H).map (honestSibs h z0 L i)).length i x := by
  rw [List.length_map, List.length_range]
  refine ⟨hA.inBounds, ?_⟩
  rw [walkPure_congr_sibs h _ (honestSibs h z0 L i) H 0 i x
    (fun l _ hl => FullMerkle.pathSibs_honest h z0 L H i l (by omega))]
  exact hA.recompute

/-- No located break on the contract's own path for an occupied index. -/
lemma contract_path_no_break_atV35 (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree)
    (H i : ℕ) (hi : i < T.leafCount) :
    ¬ TreeRootBreak h z0 hl T H
        (FullMerkle.pathSibs ((List.range H).map (honestSibs h z0 (leafHashes hl T) i)))
        ((List.range H).map (honestSibs h z0 (leafHashes hl T) i)).length i (T.leaf i) := by
  rw [List.length_map, List.length_range]
  intro hb
  cases hb with
  | wrongLength hh => exact heightBreak_not_tautology.1 _ _ _ _ _ _ _ hh
  | pathCollision _ hc =>
    obtain ⟨j, hj, hne, _⟩ := hc
    apply hne
    refine walkPair_honest h z0 (leafHashes hl T) _ j 0 i (hl (T.leaf i)) ?_ ?_
    · intro l _ hl'
      rw [FullMerkle.pathSibs_honest h z0 _ H i l (by omega), Nat.sub_zero]
      rfl
    · rw [levels_zero, zeros_zero, leafHashes_getD hi]
  | leafCollision _ hne _ => exact hne rfl
  | paddingHit hle _ => omega

theorem cTxRunAtV35_contract_proofs_at_stored_root (h : Hash) (hl : LeafHash) (zE : UInt256)
    (K : Roles) (R : ℕ → CState) (tx : Trace) (hR : CTxRunAtV35 h hl zE K R tx)
    (h0 : R 0 = cPredeployAtV35) (n : ℕ) (hinit : Initialized (R n).tree) :
    ∃ Rt : UInt256, (R n).root = some Rt
      ∧ (∀ v : UInt256, v ∈ keys (toAbs (R n).tree) →
          ∃ i < (R n).tree.leafCount, ((R n).tree.leaf i).value = v
            ∧ ∃ p : List UInt256, (R n).merklePath i = some p ∧ p.length = (R n).fm.height
              ∧ InclusionAccepted h hl Rt v ((R n).tree.leaf i) i (FullMerkle.pathSibs p) p.length
              ∧ ¬ TreeRootBreak h zE hl (R n).tree (R n).fm.height (FullMerkle.pathSibs p)
                  p.length i ((R n).tree.leaf i))
      ∧ (∀ v : UInt256, v ≠ 0 → v ∉ keys (toAbs (R n).tree) →
          ∃ i < (R n).tree.leafCount,
            ∃ p : List UInt256, (R n).merklePath i = some p ∧ p.length = (R n).fm.height
              ∧ NonInclusionAccepted h hl Rt v ((R n).tree.leaf i) i (FullMerkle.pathSibs p)
                  p.length
              ∧ ¬ TreeRootBreak h zE hl (R n).tree (R n).fm.height (FullMerkle.pathSibs p)
                  p.length i ((R n).tree.leaf i))
      ∧ (∀ (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
          InclusionAccepted h hl Rt v ℓ₁ i₁ s₁ k₁ → NonInclusionAccepted h hl Rt v ℓ₂ i₂ s₂ k₂ →
            TreeRootBreak h zE hl (R n).tree (R n).fm.height s₁ k₁ i₁ ℓ₁
              ∨ TreeRootBreak h zE hl (R n).tree (R n).fm.height s₂ k₂ i₂ ℓ₂) := by
  rcases cTxRunAtV35_inv hR h0 n with hpre | ⟨_, _, hH, hRep⟩
  · rw [hpre] at hinit
    exact absurd hinit predeploy_not_initialized
  obtain ⟨c1, c2, c3⟩ := proofs_exclusive_or_break_at_own_height h zE hl (R n).toH hH
  refine ⟨_, root_eq_published_atV35 hRep, ?_, ?_, c3⟩
  · intro v hv
    obtain ⟨i, hi, hval, hI, _⟩ := c1 v hv
    refine ⟨i, hi, hval, _, contract_path_atV35 hRep hi, by rw [List.length_map, List.length_range],
      ⟨hI.valueMatch, pathAccepts_contract_atV35 hI.path⟩,
      contract_path_no_break_atV35 h zE hl (R n).tree (R n).fm.height i hi⟩
  · intro v hv0 habs
    obtain ⟨i, hi, hN, _⟩ := c2 v hv0 habs
    refine ⟨i, hi, _, contract_path_atV35 hRep hi, by rw [List.length_map, List.length_range],
      ⟨hN.nonzero, hN.lowBelow, hN.window, pathAccepts_contract_atV35 hN.path⟩,
      contract_path_no_break_atV35 h zE hl (R n).tree (R n).fm.height i hi⟩

/-! ## Empty slots -/

theorem cTxRunAtV35_empty_slot_locates_padding (h : Hash) (hl : LeafHash) (zE : UInt256)
    (K : Roles) (R : ℕ → CState) (tx : Trace) (hR : CTxRunAtV35 h hl zE K R tx)
    (h0 : R 0 = cPredeployAtV35) (n : ℕ) (Rt : UInt256) (ℓ : Leaf) (j k : ℕ)
    (s : ℕ → UInt256) (hroot : (R n).root = some Rt) (hj : (R n).tree.leafCount ≤ j)
    (hA : PathAccepts h Rt s k j (hl ℓ)) :
    hl ℓ = zE
      ∨ (k = (R n).fm.height
          ∧ PathCollision h zE (leafHashes hl (R n).tree) s 0 k j (hl ℓ))
      ∨ HeightBreak h zE (leafHashes hl (R n).tree) s k (R n).fm.height j (hl ℓ) := by
  rcases cTxRunAtV35_inv hR h0 n with hpre | ⟨_, _, _, hRep⟩
  · rw [hpre, cPredeployAtV35_root] at hroot
    cases hroot
  rw [root_eq_published_atV35 hRep] at hroot
  have hacc : walkPure h s 0 k j (hl ℓ)
      = rootOf h zE (leafHashes hl (R n).tree) (R n).fm.height := by
    rw [hA.recompute]
    exact (Option.some.inj hroot).symm
  rcases accept_forces_height_or_break h zE _ s k (R n).fm.height j (hl ℓ) hA.inBounds hacc
    with hk | hb
  · subst hk
    rcases accept_pins_entry_or_collision h zE _ s (R n).fm.height j (hl ℓ) hA.inBounds hacc
      with he | hc
    · left
      rw [getD_default _ _ _ (by rw [leafHashes_length]; exact hj)] at he
      exact he.symm
    · exact Or.inr (Or.inl ⟨rfl, hc⟩)
  · exact Or.inr (Or.inr hb)

/-! ## Witnesses -/

/-- `_height` of an invariant state is the source's `fmHeight` of its leaf count. -/
lemma invAtV35_height {h : Hash} {hl : LeafHash} {zE : UInt256} {S : CState}
    (hI : InvAtV35 h hl zE S) : S.fm.height = fmHeight S.tree.leafCount :=
  congrArg TreeDims.height (hReaches_dims hI.2.2.1)

/-- The honest inserts of `chainTree` are guarded, up to `chainTree 7`. -/
lemma chainTree_guard_atV35 (k : ℕ) (hk : k < 7) :
    InsertGuard (chainTree k) ((k + 1 : ℕ) : UInt256) k := by
  interval_cases k <;>
    exact ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The honest inserts `insert(k + 1, k)` pass the v35 checks with exit index `k` (no hop), for
`k < 6`. -/
lemma chainTree_checks_atV35 (k : ℕ) (hk : k < 6) :
    InsertChecksAtV35 (chainTree k) ((k + 1 : ℕ) : UInt256) k k := by
  interval_cases k <;>
    exact ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide,
      ⟨0, by decide⟩⟩

/-- The stale insert `insert(7, 0)` on `chainTree 6` passes the v35 checks: its walk makes six
hops and exits at index `6`. -/
lemma chainTree_stale_checks_atV35 : InsertChecksAtV35 (chainTree 6) 7 0 6 :=
  ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide, ⟨6, by decide⟩⟩

/-- The whole storage of `chainTree k`, for `k ≤ 7`: its list state is `chainTree k`, and it
satisfies the run invariant. -/
lemma chainCStateAtV35_spec (h : Hash) (hl : LeafHash) (zE : UInt256) :
    ∀ k : ℕ, k ≤ 7 → (chainCStateAtV35 h hl zE k).tree = chainTree k
      ∧ InvAtV35 h hl zE (chainCStateAtV35 h hl zE k)
  | 0, _ => by
      obtain ⟨S, hS, htree, _, _⟩ := cInitL2AtV35_predeploy h hl zE
      have h0 : chainCStateAtV35 h hl zE 0 = S := by
        show (cInitL2AtV35 h hl zE cPredeployAtV35).getD cPredeployAtV35 = S
        rw [hS]
        rfl
      rw [h0]
      exact ⟨htree, invAtV35_of_init hS⟩
  | k + 1, hk => by
      obtain ⟨htree, hI⟩ := chainCStateAtV35_spec h hl zE k (by omega)
      have hg : InsertGuard (chainCStateAtV35 h hl zE k).tree ((k + 1 : ℕ) : UInt256) k := by
        rw [htree]; exact chainTree_guard_atV35 k (by omega)
      obtain ⟨S', r, hins, htree', hI', _⟩ := invAtV35_guarded_insert hI hg
      have hnext : chainCStateAtV35 h hl zE (k + 1) = S' := by
        show ((cInsert h hl (chainCStateAtV35 h hl zE k) ((k + 1 : ℕ) : UInt256) k).map
          Prod.fst).getD (chainCStateAtV35 h hl zE k) = S'
        rw [hins]
        rfl
      rw [hnext]
      refine ⟨?_, hI'⟩
      rw [htree', htree]
      rfl

/-- Each insert of the chain, up to `chainTree 7`, does not revert and gives the next state. -/
lemma chainCStateAtV35_step (h : Hash) (hl : LeafHash) (zE : UInt256) (k : ℕ) (hk : k < 7) :
    ∃ r : UInt256, cInsert h hl (chainCStateAtV35 h hl zE k) ((k + 1 : ℕ) : UInt256) k
      = some (chainCStateAtV35 h hl zE (k + 1), r) := by
  obtain ⟨htree, hI⟩ := chainCStateAtV35_spec h hl zE k (by omega)
  have hg : InsertGuard (chainCStateAtV35 h hl zE k).tree ((k + 1 : ℕ) : UInt256) k := by
    rw [htree]; exact chainTree_guard_atV35 k hk
  obtain ⟨S', r, hins, _⟩ := invAtV35_guarded_insert hI hg
  have hnext : chainCStateAtV35 h hl zE (k + 1) = S' := by
    show ((cInsert h hl (chainCStateAtV35 h hl zE k) ((k + 1 : ℕ) : UInt256) k).map
      Prod.fst).getD (chainCStateAtV35 h hl zE k) = S'
    rw [hins]
    rfl
  exact ⟨r, by rw [hnext]; exact hins⟩

/-- The honest step `insert(k + 1, k)` of the chain is a v35 transaction of the appender. -/
lemma chainCStateAtV35_honest_step (h : Hash) (hl : LeafHash) (zE : UInt256) (K : Roles)
    (k : ℕ) (hk : k < 6) :
    CTxStepAtV35 h hl zE K (chainCStateAtV35 h hl zE k) K.appender
      (.insert ((k + 1 : ℕ) : UInt256) k) (chainCStateAtV35 h hl zE (k + 1)) := by
  obtain ⟨htree, _⟩ := chainCStateAtV35_spec h hl zE k (by omega)
  obtain ⟨r, hins⟩ := chainCStateAtV35_step h hl zE k (by omega)
  exact CTxStepAtV35.insert rfl (by rw [htree]; exact chainTree_checks_atV35 k hk) hins

/-- The stale step `insert(7, 0)` on the storage of `chainTree 6` is a v35 transaction of the
appender, written at the exit index `6`. -/
lemma chainCStateAtV35_stale_step (h : Hash) (hl : LeafHash) (zE : UInt256) (K : Roles) :
    CTxStepAtV35 h hl zE K (chainCStateAtV35 h hl zE 6) K.appender (.insert 7 0)
      (chainCStateAtV35 h hl zE 7) := by
  obtain ⟨htree, _⟩ := chainCStateAtV35_spec h hl zE 6 (by omega)
  obtain ⟨r, hins⟩ := chainCStateAtV35_step h hl zE 6 (by omega)
  exact CTxStepAtV35.insert (low := 6) rfl (by rw [htree]; exact chainTree_stale_checks_atV35) hins

/-- `staleHintCRunAtV35` with `staleHintTxV35 K` is a run of the v35 machine. -/
lemma staleHintCRunAtV35_run (h : Hash) (hl : LeafHash) (zE : UInt256) (K : Roles) :
    CTxRunAtV35 h hl zE K (staleHintCRunAtV35 h hl zE) (staleHintTxV35 K) := by
  intro n
  rcases Nat.lt_or_ge n 8 with hn | hn
  · interval_cases n
    · refine Or.inr ⟨K.upgrader, .initL2, rfl, ?_⟩
      obtain ⟨S, hS, _⟩ := cInitL2AtV35_predeploy h hl zE
      have h1 : staleHintCRunAtV35 h hl zE (0 + 1) = S := by
        show (cInitL2AtV35 h hl zE cPredeployAtV35).getD cPredeployAtV35 = S
        rw [hS]
        rfl
      exact CTxStepAtV35.initL2 rfl rfl (by rw [h1]; exact hS)
    · exact Or.inr ⟨_, _, rfl, chainCStateAtV35_honest_step h hl zE K 0 (by omega)⟩
    · exact Or.inr ⟨_, _, rfl, chainCStateAtV35_honest_step h hl zE K 1 (by omega)⟩
    · exact Or.inr ⟨_, _, rfl, chainCStateAtV35_honest_step h hl zE K 2 (by omega)⟩
    · exact Or.inr ⟨_, _, rfl, chainCStateAtV35_honest_step h hl zE K 3 (by omega)⟩
    · exact Or.inr ⟨_, _, rfl, chainCStateAtV35_honest_step h hl zE K 4 (by omega)⟩
    · exact Or.inr ⟨_, _, rfl, chainCStateAtV35_honest_step h hl zE K 5 (by omega)⟩
    · exact Or.inr ⟨_, _, rfl, chainCStateAtV35_stale_step h hl zE K⟩
  · left
    refine ⟨?_, ?_⟩
    · simp only [staleHintTxV35]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    · simp only [staleHintCRunAtV35]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.min_eq_right (by omega),
        Nat.min_eq_right (by omega)]

/-- The list states of `staleHintCRunAtV35` are `staleHintRunV35`. -/
lemma staleHintCRunAtV35_tree (h : Hash) (hl : LeafHash) (zE : UInt256) (n : ℕ) :
    (staleHintCRunAtV35 h hl zE n).tree = staleHintRunV35 n := by
  by_cases hn : n = 0
  · subst hn; rfl
  · rw [staleHintCRunAtV35, staleHintRunV35, ite_eq_right hn, ite_eq_right hn]
    exact (chainCStateAtV35_spec h hl zE _ (Nat.min_le_right _ _)).1

/-- The states of `staleHintCRunAtV35` from step 1 on satisfy the run invariant. -/
lemma staleHintCRunAtV35_inv (h : Hash) (hl : LeafHash) (zE : UInt256) (n : ℕ) (hn : n ≠ 0) :
    InvAtV35 h hl zE (staleHintCRunAtV35 h hl zE n) := by
  rw [staleHintCRunAtV35, ite_eq_right hn]
  exact (chainCStateAtV35_spec h hl zE _ (Nat.min_le_right _ _)).2

/-- `root()` of an invariant state whose list state and height are known. -/
lemma invAtV35_root_eq {h : Hash} {hl : LeafHash} {zE : UInt256} {S : CState} {T : Tree}
    {H : ℕ} (hI : InvAtV35 h hl zE S) (ht : S.tree = T) (hH : S.fm.height = H) :
    S.root = some (root h zE hl T H) := by
  rw [root_eq_published_atV35 hI.2.2.2, ← ht, ← hH]
  rfl

theorem staleHint_cRun_witness_atV35 (h : Hash) (hl : LeafHash) (zE : UInt256) (K : Roles) :
    CTxRunAtV35 h hl zE K (staleHintCRunAtV35 h hl zE) (staleHintTxV35 K)
      ∧ staleHintCRunAtV35 h hl zE 0 = cPredeployAtV35
      ∧ (∀ n : ℕ, (staleHintCRunAtV35 h hl zE n).tree = staleHintRunV35 n)
      ∧ staleHintTxV35 K 0 = some (K.upgrader, .initL2)
      ∧ staleHintTxV35 K 7 = some (K.appender, .insert 7 0)
      ∧ staleHintRunV35 7 = chainTree 6 ∧ staleHintRunV35 8 = chainTree 7
      ∧ WalkExitsAtV35 (chainTree 6) 7 0 6 ∧ lowSearch (chainTree 6) 7 6 0 = some 6
      ∧ lowSearch (chainTree 6) 7 maxLowIndexSearchAttempts 0 = none
      ∧ (∀ low : ℕ, ¬ InsertChecks (chainTree 6) 7 0 low)
      ∧ Initialized (staleHintCRunAtV35 h hl zE 7).tree
      ∧ (1 : UInt256) ∈ keys (toAbs (staleHintCRunAtV35 h hl zE 7).tree)
      ∧ (8 : UInt256) ∉ keys (toAbs (staleHintCRunAtV35 h hl zE 7).tree)
      ∧ (staleHintCRunAtV35 h hl zE 7).fm.height = 3
      ∧ (staleHintCRunAtV35 h hl zE 8).fm.height = 3
      ∧ (staleHintCRunAtV35 h hl zE 8).root = some (root h zE hl (chainTree 7) 3) := by
  have ht7 : (staleHintCRunAtV35 h hl zE 7).tree = chainTree 6 := staleHintCRunAtV35_tree h hl zE 7
  have ht8 : (staleHintCRunAtV35 h hl zE 8).tree = chainTree 7 := staleHintCRunAtV35_tree h hl zE 8
  have hI7 := staleHintCRunAtV35_inv h hl zE 7 (by omega)
  have hI8 := staleHintCRunAtV35_inv h hl zE 8 (by omega)
  have hsearch : lowSearch (chainTree 6) 7 maxLowIndexSearchAttempts 0 = none := by decide
  have hH7 : (staleHintCRunAtV35 h hl zE 7).fm.height = 3 := by
    rw [invAtV35_height hI7, ht7]; decide
  have hH8 : (staleHintCRunAtV35 h hl zE 8).fm.height = 3 := by
    rw [invAtV35_height hI8, ht8]; decide
  refine ⟨staleHintCRunAtV35_run h hl zE K, rfl, staleHintCRunAtV35_tree h hl zE, rfl, rfl, rfl,
    rfl, ⟨6, by decide⟩, by decide, hsearch, ?_, ?_, ?_, ?_, hH7, hH8,
    invAtV35_root_eq hI8 ht8 hH8⟩
  · intro low hc
    rw [hc.search] at hsearch
    cases hsearch
  · rw [ht7]; unfold Initialized; decide
  · rw [ht7]; exact mem_keys_iff_index.mpr ⟨1, by decide, by decide⟩
  · rw [ht7, mem_keys_iff_index]
    rintro ⟨i, hi, hv⟩
    have hi7 : i < 7 := hi
    interval_cases i <;> revert hv <;> decide

/-- The padding forgery on an invariant state of `chainTree 6` whose padding constant is the
pin's. -/
lemma padding_forgery_of_invAtV35 {h : Hash} {hl : LeafHash} {S : CState}
    (hI : InvAtV35 h hl (hl ⟨0, 0, 0⟩) S) (ht : S.tree = chainTree 6) :
    S.root = some (root h (hl ⟨0, 0, 0⟩) hl (chainTree 6) 3)
      ∧ (∃ p : List UInt256, S.merklePath 1 = some p
          ∧ InclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (chainTree 6) 3) 1
              ((chainTree 6).leaf 1) 1 (FullMerkle.pathSibs p) p.length)
      ∧ S.merklePath 7 = none
      ∧ NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (chainTree 6) 3) 1 ⟨0, 0, 0⟩ 7
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (chainTree 6)) 7) 3
      ∧ TreeRootBreakExactly h (hl ⟨0, 0, 0⟩) hl (chainTree 6) 3
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (chainTree 6)) 7) 3 7 ⟨0, 0, 0⟩
          .paddingHit := by
  have hRep := hI.2.2.2
  have hH : S.fm.height = 3 := by rw [invAtV35_height hI, ht]; decide
  have hcount : (chainTree 6).leafCount = 7 := by decide
  have hget : (leafHashes hl (chainTree 6)).getD 7 (hl ⟨0, 0, 0⟩) = hl ⟨0, 0, 0⟩ :=
    getD_default _ _ _ (by rw [leafHashes_length, hcount])
  refine ⟨invAtV35_root_eq hI ht hH, ?_, ?_, ?_, ?_⟩
  · have hi : 1 < S.tree.leafCount := by rw [ht, hcount]; omega
    refine ⟨_, contract_path_atV35 hRep hi, ?_⟩
    have hI1 := inclusion_complete (h := h) (z0 := hl ⟨0, 0, 0⟩) (hl := hl) (T := chainTree 6)
      (height := 3) (by rw [hcount]; norm_num) (i := 1) (by rw [hcount]; omega)
    have hval : ((chainTree 6).leaf 1).value = 1 := by decide
    rw [hval] at hI1
    rw [ht, hH]
    exact ⟨hI1.valueMatch, pathAccepts_contract_atV35 hI1.path⟩
  · refine FullMerkle.merklePath_out_of_range_reverts S.fm 7 ?_
    rw [hRep.leafNumber_eq, leafHashes_length, ht, hcount]
  · refine ⟨by decide, by decide, Or.inl rfl, by norm_num, ?_⟩
    have := honest_walk_root h (hl ⟨0, 0, 0⟩) (leafHashes hl (chainTree 6)) 3 7 (by norm_num)
    rw [hget] at this
    exact this
  · refine treeRootBreakExactly_of ⟨by rw [hcount], rfl⟩ ?_
    intro c' hc'
    cases c' with
    | wrongLength => exact not_wrongLength_at_height
    | pathCollision =>
        rintro ⟨_, hpc⟩
        apply honest_walk_no_collision h _ (leafHashes hl (chainTree 6)) 3 7
        rw [hget]; exact hpc
    | leafCollision =>
        rintro ⟨hlt, _⟩
        rw [hcount] at hlt
        exact absurd hlt (lt_irrefl 7)
    | paddingHit => exact absurd rfl hc'

theorem padding_forgery_atV35_witness (h : Hash) (hl : LeafHash) :
    (staleHintCRunAtV35 h hl (hl ⟨0, 0, 0⟩) 7).root
        = some (root h (hl ⟨0, 0, 0⟩) hl (chainTree 6) 3)
      ∧ (∃ p : List UInt256, (staleHintCRunAtV35 h hl (hl ⟨0, 0, 0⟩) 7).merklePath 1 = some p
          ∧ InclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (chainTree 6) 3) 1
              ((chainTree 6).leaf 1) 1 (FullMerkle.pathSibs p) p.length)
      ∧ (staleHintCRunAtV35 h hl (hl ⟨0, 0, 0⟩) 7).merklePath 7 = none
      ∧ NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (chainTree 6) 3) 1 ⟨0, 0, 0⟩ 7
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (chainTree 6)) 7) 3
      ∧ TreeRootBreakExactly h (hl ⟨0, 0, 0⟩) hl (chainTree 6) 3
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (chainTree 6)) 7) 3 7 ⟨0, 0, 0⟩
          .paddingHit :=
  padding_forgery_of_invAtV35 (staleHintCRunAtV35_inv h hl (hl ⟨0, 0, 0⟩) 7 (by omega))
    (staleHintCRunAtV35_tree h hl (hl ⟨0, 0, 0⟩) 7)

end Contracts.InteropCommitmentTree

/-! ## Certificates -/

namespace Contracts.InteropCommitmentTree

theorem CInitL2AtV35OnPredeploy : Properties.CInitL2AtV35OnPredeploy :=
  cInitL2AtV35_on_predeploy
theorem CInitL2AtV35AtPinPaddingIsCSetup : Properties.CInitL2AtV35AtPinPaddingIsCSetup :=
  cInitL2AtV35_at_pin_padding
theorem CTxRunAtV35Shape : Properties.CTxRunAtV35Shape := cTxRunAtV35_shape
theorem CTxRunAtV35AtPinPaddingIsCRunFromCSetup :
    Properties.CTxRunAtV35AtPinPaddingIsCRunFromCSetup := cTxRunAtV35_at_pin_padding
theorem CTxRunAtV35InsertIsGuardedCInsert : Properties.CTxRunAtV35InsertIsGuardedCInsert :=
  cTxRunAtV35_insert_is_guarded
theorem CTxRunAtV35StoredRootIsPublished : Properties.CTxRunAtV35StoredRootIsPublished :=
  cTxRunAtV35_stored_root_is_published
theorem CTxRunAtV35ContractProofsAtStoredRoot :
    Properties.CTxRunAtV35ContractProofsAtStoredRoot := cTxRunAtV35_contract_proofs_at_stored_root
theorem CTxRunAtV35EmptySlotLocatesPadding : Properties.CTxRunAtV35EmptySlotLocatesPadding :=
  cTxRunAtV35_empty_slot_locates_padding
theorem StaleHintCRunWitnessAtV35 : Properties.StaleHintCRunWitnessAtV35 :=
  staleHint_cRun_witness_atV35
theorem PaddingForgeryAtV35Witness : Properties.PaddingForgeryAtV35Witness :=
  padding_forgery_atV35_witness

end Contracts.InteropCommitmentTree
