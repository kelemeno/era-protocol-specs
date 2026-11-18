import EraSpec.Contracts.L1NativeTokenVault.Properties.InteropPool

/-!
# Proofs: the L1 vault's per-chain ledger and the interop pool

Proofs of `EraSpec.Contracts.L1NativeTokenVault.Properties.InteropPool`.

Each call has an inversion lemma (`…_some`): on success, the guards it passed and the exact state
it leaves. The invariants are then checked call by call (`flagInv_step`, `identity_step`,
`covered_step`) and carried along runs (`PoolRun.preserves`). The pool identity's sum ranges over
all chain ids (`Fintype UInt256`); a call changes at most one summand per asset, which
`movedNet_point` accounts for. The commutation is checked in both directions from the inversion
lemmas and the exact results of the two calls. The witnesses evaluate concrete runs with `decide`.
-/

namespace Contracts.L1NativeTokenVault.InteropPool

/-- The pool's key is above every chain id the Bridgehub accepts. -/
theorem pool_above_cap : chainIdCap ≤ interopPoolChainId.val := by decide

theorem setAt_apply {β : Type} (f : UInt256 → β) (k : UInt256) (v : β) (k' : UInt256) :
    setAt f k v k' = if k' = k then v else f k' := rfl

theorem setAt2_apply {β : Type} (f : ChainId → AssetId → β) (c : ChainId) (a : AssetId)
    (v : β) (c' : ChainId) (a' : AssetId) :
    setAt2 f c a v c' a' = if c' = c ∧ a' = a then v else f c' a' := rfl

theorem setAt_self {β : Type} (f : UInt256 → β) (k : UInt256) (v : β) : setAt f k v k = v :=
  ite_eq_left rfl

theorem setAt_of_ne {β : Type} {f : UInt256 → β} {k k' : UInt256} {v : β} (h : k' ≠ k) :
    setAt f k v k' = f k' :=
  ite_eq_right h

theorem setAt2_self {β : Type} (f : ChainId → AssetId → β) (c : ChainId) (a : AssetId) (v : β) :
    setAt2 f c a v c a = v :=
  ite_eq_left (show c = c ∧ a = a from ⟨rfl, rfl⟩)

theorem setAt2_of_ne {β : Type} {f : ChainId → AssetId → β} {c c' : ChainId} {a a' : AssetId}
    {v : β} (h : ¬(c' = c ∧ a' = a)) : setAt2 f c a v c' a' = f c' a' :=
  ite_eq_right h

theorem netOf_eq (b w : ℕ) : netOf b w = b - w := by
  unfold netOf; split_ifs <;> omega

theorem trackedBalance_key (s : PoolSys) (c o : ChainId) :
    (trackedBalance s c o).2 = if s.interop c = true then interopPoolChainId else c := by
  unfold trackedBalance; split_ifs <;> rfl

/-! ## Inversion of each call -/

theorem handleBridgeToChain_some {l1 : ChainId} {s t : PoolSys} {c a : ChainId} {x : UInt256}
    {o : ChainId} (h : handleBridgeToChain l1 s c a x o = some t) :
    ((trackedBalance s c o).1 = true
      ∧ s.deposited (trackedBalance s c o).2 a + x.val < UInt256.size
      ∧ t = { s with
          bridgedOut := if o = l1 then setAt s.bridgedOut a (s.bridgedOut a + x.val) else s.bridgedOut
          deposited := setAt2 s.deposited (trackedBalance s c o).2 a
            (s.deposited (trackedBalance s c o).2 a + x.val)
          directToPool := if (trackedBalance s c o).2 = interopPoolChainId
            then setAt s.directToPool a (s.directToPool a + x.val) else s.directToPool })
    ∨ ((trackedBalance s c o).1 = false
      ∧ t = { s with bridgedOut :=
          if o = l1 then setAt s.bridgedOut a (s.bridgedOut a + x.val) else s.bridgedOut }) := by
  unfold handleBridgeToChain at h
  by_cases h1 : o = l1 ∧ UInt256.size ≤ s.bridgedOut a + x.val
  · rw [ite_eq_left h1] at h; cases h
  · rw [ite_eq_right h1] at h
    dsimp only at h
    by_cases h2 : (trackedBalance s c o).1 = true
    · rw [ite_eq_left h2] at h
      by_cases h3 : UInt256.size ≤ s.deposited (trackedBalance s c o).2 a + x.val
      · rw [ite_eq_left h3] at h; cases h
      · rw [ite_eq_right h3] at h
        cases h
        exact Or.inl ⟨h2, by omega, rfl⟩
    · rw [ite_eq_right h2] at h
      cases h
      exact Or.inr ⟨by simpa using h2, rfl⟩

theorem handleBridgeFromChain_some {l1 : ChainId} {s t : PoolSys} {c a : ChainId} {x : UInt256}
    {o : ChainId} (h : handleBridgeFromChain l1 s c a x o = some t) :
    ((trackedBalance s c o).1 = true
      ∧ s.withdrawn (trackedBalance s c o).2 a + x.val < UInt256.size
      ∧ (s.pending (trackedBalance s c o).2 = false →
          s.withdrawn (trackedBalance s c o).2 a + x.val
            ≤ s.deposited (trackedBalance s c o).2 a + s.backfill (trackedBalance s c o).2 a)
      ∧ t = { s with
          bridgedOut := if o = l1 then setAt s.bridgedOut a (s.bridgedOut a - x.val) else s.bridgedOut
          withdrawn := setAt2 s.withdrawn (trackedBalance s c o).2 a
            (s.withdrawn (trackedBalance s c o).2 a + x.val) })
    ∨ ((trackedBalance s c o).1 = false
      ∧ t = { s with bridgedOut :=
          if o = l1 then setAt s.bridgedOut a (s.bridgedOut a - x.val) else s.bridgedOut }) := by
  unfold handleBridgeFromChain at h
  by_cases h1 : o = l1 ∧ s.bridgedOut a < x.val
  · rw [ite_eq_left h1] at h; cases h
  · rw [ite_eq_right h1] at h
    dsimp only at h
    by_cases h2 : (trackedBalance s c o).1 = true
    · rw [ite_eq_left h2] at h
      by_cases h3 : UInt256.size ≤ s.withdrawn (trackedBalance s c o).2 a + x.val
      · rw [ite_eq_left h3] at h; cases h
      · rw [ite_eq_right h3] at h
        by_cases h4 : s.pending (trackedBalance s c o).2 = false ∧
            (UInt256.size ≤ s.deposited (trackedBalance s c o).2 a
                + s.backfill (trackedBalance s c o).2 a ∨
              s.deposited (trackedBalance s c o).2 a + s.backfill (trackedBalance s c o).2 a
                < s.withdrawn (trackedBalance s c o).2 a + x.val)
        · rw [ite_eq_left h4] at h; cases h
        · rw [ite_eq_right h4] at h
          cases h
          refine Or.inl ⟨h2, by omega, fun hp => ?_, rfl⟩
          by_contra hlt
          exact h4 ⟨hp, Or.inr (by omega)⟩
    · rw [ite_eq_right h2] at h
      cases h
      exact Or.inr ⟨by simpa using h2, rfl⟩

theorem setChainBalanceBackfill_some {s t : PoolSys} {c a : ChainId} {x : UInt256}
    (h : setChainBalanceBackfill s c a x = some t) :
    c ≠ interopPoolChainId ∧ s.backfill c a = 0 ∧
    ((s.inPool c a = true ∧ s.deposited c a + x.val < UInt256.size
      ∧ s.deposited interopPoolChainId a
          + ((s.deposited c a + x.val - s.withdrawn c a) - (s.deposited c a - s.withdrawn c a))
          < UInt256.size
      ∧ t = { s with
          deposited := setAt2 s.deposited interopPoolChainId a
            (s.deposited interopPoolChainId a
              + ((s.deposited c a + x.val - s.withdrawn c a) - (s.deposited c a - s.withdrawn c a)))
          backfill := setAt2 s.backfill c a x.val })
    ∨ (s.inPool c a = false ∧ t = { s with backfill := setAt2 s.backfill c a x.val })) := by
  unfold setChainBalanceBackfill at h
  by_cases h1 : c = interopPoolChainId
  · rw [ite_eq_left h1] at h; cases h
  · rw [ite_eq_right h1] at h
    by_cases h2 : s.backfill c a ≠ 0
    · rw [ite_eq_left h2] at h; cases h
    · rw [ite_eq_right h2] at h
      refine ⟨h1, by simpa using h2, ?_⟩
      by_cases h3 : s.inPool c a = true
      · rw [ite_eq_left h3] at h
        by_cases h4 : UInt256.size ≤ s.deposited c a + x.val
        · rw [ite_eq_left h4] at h; cases h
        · rw [ite_eq_right h4] at h
          dsimp only at h
          simp only [netOf_eq, Nat.add_zero] at h
          by_cases h5 : s.deposited c a + x.val - s.withdrawn c a < s.deposited c a - s.withdrawn c a
          · rw [ite_eq_left h5] at h; cases h
          · rw [ite_eq_right h5] at h
            by_cases h6 : UInt256.size ≤ s.deposited interopPoolChainId a
                + ((s.deposited c a + x.val - s.withdrawn c a) - (s.deposited c a - s.withdrawn c a))
            · rw [ite_eq_left h6] at h; cases h
            · rw [ite_eq_right h6] at h
              cases h
              exact Or.inl ⟨h3, by omega, by omega, rfl⟩
      · rw [ite_eq_right h3] at h
        cases h
        exact Or.inr ⟨by simpa using h3, rfl⟩

theorem markBackfilled_some {s t : PoolSys} {c : ChainId} (h : markBackfilled s c = some t) :
    s.pending c = true ∧ t = { s with pending := setAt s.pending c false } := by
  unfold markBackfilled at h
  by_cases h1 : s.pending c = true
  · rw [ite_eq_left h1] at h; cases h; exact ⟨h1, rfl⟩
  · rw [ite_eq_right h1] at h; cases h

theorem moveChainBalanceToInteropPool_some {s t : PoolSys} {c a : ChainId}
    (h : moveChainBalanceToInteropPool s c a = some t) :
    s.interop c = true ∧ s.pending c = false ∧ s.inPool c a = false
    ∧ s.deposited c a + s.backfill c a < UInt256.size
    ∧ s.deposited interopPoolChainId a + (s.deposited c a + s.backfill c a - s.withdrawn c a)
        < UInt256.size
    ∧ t = { s with
        inPool := setAt2 s.inPool c a true
        deposited := setAt2 s.deposited interopPoolChainId a
          (s.deposited interopPoolChainId a + (s.deposited c a + s.backfill c a - s.withdrawn c a)) } := by
  unfold moveChainBalanceToInteropPool at h
  by_cases h1 : s.interop c = false
  · rw [ite_eq_left h1] at h; cases h
  · rw [ite_eq_right h1] at h
    by_cases h2 : s.pending c = true
    · rw [ite_eq_left h2] at h; cases h
    · rw [ite_eq_right h2] at h
      by_cases h3 : s.inPool c a = true
      · rw [ite_eq_left h3] at h; cases h
      · rw [ite_eq_right h3] at h
        by_cases h4 : UInt256.size ≤ s.deposited c a + s.backfill c a
        · rw [ite_eq_left h4] at h; cases h
        · rw [ite_eq_right h4] at h
          dsimp only at h
          simp only [netOf_eq] at h
          by_cases h5 : UInt256.size ≤ s.deposited interopPoolChainId a
              + (s.deposited c a + s.backfill c a - s.withdrawn c a)
          · rw [ite_eq_left h5] at h; cases h
          · rw [ite_eq_right h5] at h
            cases h
            exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by omega, by omega, rfl⟩

theorem enableInterop_some {s t : PoolSys} {c : ChainId} (h : enableInterop s c = some t) :
    s.registered c = true ∧ s.interop c = false ∧ s.pending c = false
    ∧ t = { s with interop := setAt s.interop c true } := by
  unfold enableInterop at h
  by_cases h1 : s.registered c = false
  · rw [ite_eq_left h1] at h; cases h
  · rw [ite_eq_right h1] at h
    by_cases h2 : s.interop c = true
    · rw [ite_eq_left h2] at h; cases h
    · rw [ite_eq_right h2] at h
      by_cases h3 : s.pending c = true
      · rw [ite_eq_left h3] at h; cases h
      · rw [ite_eq_right h3] at h
        cases h
        exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, rfl⟩

theorem initializeUpgrade_some {s t : PoolSys} (h : initializeUpgrade s = some t) :
    s.initVersion < 2
    ∧ t = { s with initVersion := 2, pending := fun c => s.pending c || s.registered c } := by
  unfold initializeUpgrade at h
  by_cases h1 : s.initVersion < 2
  · rw [ite_eq_left h1] at h; cases h; exact ⟨h1, rfl⟩
  · rw [ite_eq_right h1] at h; cases h

theorem registerChain_some {l1 : ChainId} {s t : PoolSys} {c : ChainId}
    (h : registerChain l1 s c = some t) :
    c.val ≠ 0 ∧ c.val < chainIdCap ∧ c ≠ l1 ∧ s.registered c = false
    ∧ t = { s with registered := setAt s.registered c true } := by
  unfold registerChain at h
  by_cases h1 : c.val = 0 ∨ chainIdCap ≤ c.val ∨ c = l1 ∨ s.registered c = true
  · rw [ite_eq_left h1] at h; cases h
  · rw [ite_eq_right h1] at h
    cases h
    simp only [not_or] at h1
    exact ⟨h1.1, by omega, h1.2.2.1, by simpa using h1.2.2.2, rfl⟩

theorem populateBridgedOutEntry_some {s t : PoolSys} {a : AssetId} {x : UInt256}
    (h : populateBridgedOutEntry s a x = some t) :
    s.bridgedOut a + x.val < UInt256.size
    ∧ t = { s with bridgedOut := setAt s.bridgedOut a (s.bridgedOut a + x.val) } := by
  unfold populateBridgedOutEntry at h
  by_cases h1 : UInt256.size ≤ s.bridgedOut a + x.val
  · rw [ite_eq_left h1] at h; cases h
  · rw [ite_eq_right h1] at h
    cases h
    exact ⟨by omega, rfl⟩

/-! ## Facts from the flag invariant -/

variable {s t : PoolSys}

theorem PoolFlagInv.interop_pool (hs : PoolFlagInv s) : s.interop interopPoolChainId = false := by
  cases h : s.interop interopPoolChainId
  · rfl
  · have := hs.interopRegistered _ h
    rw [hs.poolUnregistered] at this
    cases this

theorem PoolFlagInv.pending_pool (hs : PoolFlagInv s) : s.pending interopPoolChainId = false := by
  cases h : s.pending interopPoolChainId
  · rfl
  · have := hs.pendingRegistered _ h
    rw [hs.poolUnregistered] at this
    cases this

theorem PoolFlagInv.inPool_pool (hs : PoolFlagInv s) (a : AssetId) :
    s.inPool interopPoolChainId a = false := by
  cases h : s.inPool interopPoolChainId a
  · rfl
  · have := hs.inPoolInterop _ _ h
    rw [hs.interop_pool] at this
    cases this

theorem PoolFlagInv.ne_pool_of_interop (hs : PoolFlagInv s) {c : ChainId}
    (hc : s.interop c = true) : c ≠ interopPoolChainId := by
  rintro rfl
  rw [hs.interop_pool] at hc
  cases hc

theorem PoolFlagInv.inPool_key (hs : PoolFlagInv s) (c o a' : ChainId) :
    s.inPool (trackedBalance s c o).2 a' = false := by
  rw [trackedBalance_key]
  split_ifs with h
  · exact hs.inPool_pool a'
  · cases h' : s.inPool c a'
    · rfl
    · have := hs.inPoolInterop _ _ h'
      simp_all

theorem PoolFlagInv.key_ne (hs : PoolFlagInv s) {c : ChainId} (hc : s.interop c = true)
    (chain o : ChainId) : (trackedBalance s chain o).2 ≠ c := by
  rw [trackedBalance_key]
  split_ifs with h
  · exact (hs.ne_pool_of_interop hc).symm
  · rintro rfl
    simp_all

/-! ## The flag invariant is preserved -/

theorem flagInv_step {l1 : ChainId} {call : PoolCall} (hs : PoolFlagInv s)
    (h : poolCall l1 call s = some t) : PoolFlagInv t := by
  cases call with
  | toChain c a x o =>
    rcases handleBridgeToChain_some h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;>
    exact ⟨hs.upgraded, hs.poolUnregistered, hs.interopRegistered, hs.pendingRegistered,
      hs.interopNotPending, hs.inPoolInterop, hs.poolNoBackfill⟩
  | fromChain c a x o =>
    rcases handleBridgeFromChain_some h with ⟨-, -, -, rfl⟩ | ⟨-, rfl⟩ <;>
    exact ⟨hs.upgraded, hs.poolUnregistered, hs.interopRegistered, hs.pendingRegistered,
      hs.interopNotPending, hs.inPoolInterop, hs.poolNoBackfill⟩
  | setBackfill c a x =>
    obtain ⟨hc, -, hcase⟩ := setChainBalanceBackfill_some h
    have hbf : ∀ a', (setAt2 s.backfill c a x.val) interopPoolChainId a' = 0 := by
      intro a'
      simp [setAt2_apply, Ne.symm hc, hs.poolNoBackfill]
    rcases hcase with ⟨-, -, -, rfl⟩ | ⟨-, rfl⟩ <;>
    exact ⟨hs.upgraded, hs.poolUnregistered, hs.interopRegistered, hs.pendingRegistered,
      hs.interopNotPending, hs.inPoolInterop, hbf⟩
  | markBackfilled c =>
    obtain ⟨-, rfl⟩ := markBackfilled_some h
    refine ⟨hs.upgraded, hs.poolUnregistered, hs.interopRegistered, ?_, ?_, hs.inPoolInterop,
      hs.poolNoBackfill⟩
    · intro c' hc'
      simp only [setAt_apply] at hc'
      split_ifs at hc' with hh
      exact hs.pendingRegistered c' hc'
    · intro c' hc'
      simp only [setAt_apply]
      split_ifs
      · rfl
      · exact hs.interopNotPending c' hc'
  | move c a =>
    obtain ⟨hi, -, -, -, -, rfl⟩ := moveChainBalanceToInteropPool_some h
    refine ⟨hs.upgraded, hs.poolUnregistered, hs.interopRegistered, hs.pendingRegistered,
      hs.interopNotPending, ?_, hs.poolNoBackfill⟩
    intro c' a' h'
    simp only [setAt2_apply] at h'
    split_ifs at h' with hh
    · rw [hh.1]; exact hi
    · exact hs.inPoolInterop c' a' h'
  | enableInterop c =>
    obtain ⟨hr, -, hp, rfl⟩ := enableInterop_some h
    refine ⟨hs.upgraded, hs.poolUnregistered, ?_, hs.pendingRegistered, ?_, ?_, hs.poolNoBackfill⟩
    · intro c' hc'
      simp only [setAt_apply] at hc'
      split_ifs at hc' with hh
      · rw [hh]; exact hr
      · exact hs.interopRegistered c' hc'
    · intro c' hc'
      simp only [setAt_apply] at hc'
      split_ifs at hc' with hh
      · rw [hh]; exact hp
      · exact hs.interopNotPending c' hc'
    · intro c' a' h'
      simp only [setAt_apply]
      split_ifs
      · rfl
      · exact hs.inPoolInterop c' a' h'
  | initializeUpgrade =>
    obtain ⟨hv, -⟩ := initializeUpgrade_some h
    exact absurd hs.upgraded (by omega)
  | register c =>
    obtain ⟨-, hcap, -, -, rfl⟩ := registerChain_some h
    have hne : interopPoolChainId ≠ c := by
      intro he
      have := pool_above_cap
      rw [he] at this
      omega
    refine ⟨hs.upgraded, ?_, ?_, ?_, hs.interopNotPending, hs.inPoolInterop, hs.poolNoBackfill⟩
    · simp [setAt_apply, hne, hs.poolUnregistered]
    · intro c' hc'
      simp only [setAt_apply]
      split_ifs
      · rfl
      · exact hs.interopRegistered c' hc'
    · intro c' hc'
      simp only [setAt_apply]
      split_ifs
      · rfl
      · exact hs.pendingRegistered c' hc'
  | populateBridgedOut a' x =>
    obtain ⟨-, rfl⟩ := populateBridgedOutEntry_some h
    exact ⟨hs.upgraded, hs.poolUnregistered, hs.interopRegistered, hs.pendingRegistered,
      hs.interopNotPending, hs.inPoolInterop, hs.poolNoBackfill⟩

/-! ## The sum over chains -/

theorem netTerm_congr {a : AssetId} {c : ChainId} (hin : t.inPool c a = s.inPool c a)
    (hval : s.inPool c a = true → t.deposited c a = s.deposited c a
      ∧ t.backfill c a = s.backfill c a ∧ t.withdrawn c a = s.withdrawn c a) :
    netTerm t a c = netTerm s a c := by
  unfold netTerm
  rw [hin]
  split_ifs with h
  · obtain ⟨h1, h2, h3⟩ := hval h
    rw [h1, h2, h3]
  · rfl

theorem movedNet_congr {a : AssetId} (h : ∀ c, netTerm t a c = netTerm s a c) :
    movedNet t a = movedNet s a :=
  Finset.sum_congr rfl (fun c _ => h c)

theorem movedNet_point {a : AssetId} (c₀ : ChainId)
    (h : ∀ c, c ≠ c₀ → netTerm t a c = netTerm s a c) :
    movedNet t a + netTerm s a c₀ = movedNet s a + netTerm t a c₀ := by
  unfold movedNet
  rw [← Finset.add_sum_erase Finset.univ (netTerm t a) (Finset.mem_univ c₀),
    ← Finset.add_sum_erase Finset.univ (netTerm s a) (Finset.mem_univ c₀),
    Finset.sum_congr rfl (fun c hc => h c (Finset.ne_of_mem_erase hc))]
  ring



theorem identity_step {l1 : ChainId} {call : PoolCall} (hs : PoolFlagInv s)
    (hid : PoolIdentity s) (h : poolCall l1 call s = some t) : PoolIdentity t := by
  cases call with
  | toChain c a x o =>
    rcases handleBridgeToChain_some h with ⟨-, -, ht⟩ | ⟨-, ht⟩
    · have hkey := hs.inPool_key c o
      have hmn : ∀ a', movedNet t a' = movedNet s a' := by
        intro a'
        apply movedNet_congr
        intro c'
        apply netTerm_congr (by rw [ht])
        intro hin
        refine ⟨?_, by rw [ht], by rw [ht]⟩
        rw [ht]
        show setAt2 s.deposited _ a _ c' a' = s.deposited c' a'
        apply setAt2_of_ne
        rintro ⟨rfl, rfl⟩
        rw [hkey] at hin
        cases hin
      intro a'
      rw [hmn a', ht]
      show setAt2 s.deposited (trackedBalance s c o).2 a _ interopPoolChainId a'
        = (if (trackedBalance s c o).2 = interopPoolChainId
            then setAt s.directToPool a (s.directToPool a + x.val) else s.directToPool) a'
          + movedNet s a'
      have h1 := hid a'
      by_cases hk : (trackedBalance s c o).2 = interopPoolChainId
      · rw [ite_eq_left hk]
        rw [hk]
        by_cases ha : a' = a
        · subst ha
          rw [setAt2_self, setAt_self]
          omega
        · rw [setAt2_of_ne (fun h => ha h.2), setAt_of_ne ha]
          exact h1
      · rw [ite_eq_right hk, setAt2_of_ne (fun h => hk h.1.symm)]
        exact h1
    · intro a'
      rw [ht]
      exact hid a'
  | fromChain c a x o =>
    rcases handleBridgeFromChain_some h with ⟨-, -, -, ht⟩ | ⟨-, ht⟩
    · have hkey := hs.inPool_key c o
      have hmn : ∀ a', movedNet t a' = movedNet s a' := by
        intro a'
        apply movedNet_congr
        intro c'
        apply netTerm_congr (by rw [ht])
        intro hin
        refine ⟨by rw [ht], by rw [ht], ?_⟩
        rw [ht]
        show setAt2 s.withdrawn _ a _ c' a' = s.withdrawn c' a'
        apply setAt2_of_ne
        rintro ⟨rfl, rfl⟩
        rw [hkey] at hin
        cases hin
      intro a'
      rw [hmn a', ht]
      exact hid a'
    · intro a'
      rw [ht]
      exact hid a'
  | setBackfill c a x =>
    obtain ⟨hc, hb0, hcase⟩ := setChainBalanceBackfill_some h
    rcases hcase with ⟨hin, -, -, ht⟩ | ⟨hin, ht⟩
    · intro a'
      have h1 := hid a'
      by_cases ha : a' = a
      · subst ha
        have hpt := movedNet_point (s := s) (t := t) (a := a') c (fun c' hc' => by
          apply netTerm_congr (by rw [ht])
          intro hin'
          refine ⟨?_, ?_, by rw [ht]⟩
          · rw [ht]
            show setAt2 s.deposited interopPoolChainId a' _ c' a' = s.deposited c' a'
            apply setAt2_of_ne
            rintro ⟨rfl, -⟩
            rw [hs.inPool_pool] at hin'
            cases hin'
          · rw [ht]
            show setAt2 s.backfill c a' _ c' a' = s.backfill c' a'
            apply setAt2_of_ne
            rintro ⟨rfl, -⟩
            exact hc' rfl)
        have e1 : netTerm s a' c = s.deposited c a' - s.withdrawn c a' := by
          unfold netTerm; rw [ite_eq_left hin, hb0, Nat.add_zero]
        have e2 : netTerm t a' c = s.deposited c a' + x.val - s.withdrawn c a' := by
          unfold netTerm
          rw [ht]
          show (if s.inPool c a' = true then
              setAt2 s.deposited interopPoolChainId a' _ c a' + setAt2 s.backfill c a' x.val c a'
                - s.withdrawn c a' else 0) = _
          rw [ite_eq_left hin, setAt2_of_ne (fun h => hc h.1), setAt2_self]
        have e3 : t.deposited interopPoolChainId a' = s.deposited interopPoolChainId a'
            + ((s.deposited c a' + x.val - s.withdrawn c a')
              - (s.deposited c a' - s.withdrawn c a')) := by
          rw [ht]
          show setAt2 s.deposited interopPoolChainId a' _ interopPoolChainId a' = _
          rw [setAt2_self]
        have e4 : t.directToPool a' = s.directToPool a' := by rw [ht]
        rw [e1, e2] at hpt
        rw [e3, e4]
        omega
      · rw [movedNet_congr (s := s) (t := t) (a := a') (fun c' => by
          apply netTerm_congr (by rw [ht])
          intro hin'
          refine ⟨?_, ?_, by rw [ht]⟩
          · rw [ht]
            show setAt2 s.deposited interopPoolChainId a _ c' a' = s.deposited c' a'
            exact setAt2_of_ne (fun h => ha h.2)
          · rw [ht]
            show setAt2 s.backfill c a _ c' a' = s.backfill c' a'
            exact setAt2_of_ne (fun h => ha h.2))]
        rw [ht]
        show setAt2 s.deposited interopPoolChainId a _ interopPoolChainId a' = _
        rw [setAt2_of_ne (fun h => ha h.2)]
        exact h1
    · intro a'
      rw [movedNet_congr (s := s) (t := t) (a := a') (fun c' => by
        apply netTerm_congr (by rw [ht])
        intro hin'
        refine ⟨by rw [ht], ?_, by rw [ht]⟩
        rw [ht]
        show setAt2 s.backfill c a _ c' a' = s.backfill c' a'
        apply setAt2_of_ne
        rintro ⟨rfl, rfl⟩
        rw [hin] at hin'
        cases hin')]
      rw [ht]
      exact hid a'
  | markBackfilled c =>
    obtain ⟨-, rfl⟩ := markBackfilled_some h
    exact hid
  | move c a =>
    obtain ⟨hi, -, hin, -, -, ht⟩ := moveChainBalanceToInteropPool_some h
    have hc := hs.ne_pool_of_interop hi
    intro a'
    have h1 := hid a'
    by_cases ha : a' = a
    · subst ha
      have hpt := movedNet_point (s := s) (t := t) (a := a') c (fun c' hc' => by
        apply netTerm_congr
        · rw [ht]
          show setAt2 s.inPool c a' true c' a' = s.inPool c' a'
          apply setAt2_of_ne
          rintro ⟨rfl, -⟩
          exact hc' rfl
        · intro hin'
          refine ⟨?_, by rw [ht], by rw [ht]⟩
          rw [ht]
          show setAt2 s.deposited interopPoolChainId a' _ c' a' = s.deposited c' a'
          apply setAt2_of_ne
          rintro ⟨rfl, -⟩
          rw [hs.inPool_pool] at hin'
          cases hin')
      have e1 : netTerm s a' c = 0 := by
        unfold netTerm; rw [hin]; rfl
      have e2 : netTerm t a' c = s.deposited c a' + s.backfill c a' - s.withdrawn c a' := by
        unfold netTerm
        rw [ht]
        show (if setAt2 s.inPool c a' true c a' = true then
            setAt2 s.deposited interopPoolChainId a' _ c a' + s.backfill c a'
              - s.withdrawn c a' else 0) = _
        rw [setAt2_self, ite_eq_left rfl, setAt2_of_ne (fun h => hc h.1)]
      have e3 : t.deposited interopPoolChainId a' = s.deposited interopPoolChainId a'
          + (s.deposited c a' + s.backfill c a' - s.withdrawn c a') := by
        rw [ht]
        show setAt2 s.deposited interopPoolChainId a' _ interopPoolChainId a' = _
        rw [setAt2_self]
      have e4 : t.directToPool a' = s.directToPool a' := by rw [ht]
      rw [e1, e2] at hpt
      rw [e3, e4]
      omega
    · rw [movedNet_congr (s := s) (t := t) (a := a') (fun c' => by
        apply netTerm_congr
        · rw [ht]
          show setAt2 s.inPool c a true c' a' = s.inPool c' a'
          exact setAt2_of_ne (fun h => ha h.2)
        · intro hin'
          refine ⟨?_, by rw [ht], by rw [ht]⟩
          rw [ht]
          show setAt2 s.deposited interopPoolChainId a _ c' a' = s.deposited c' a'
          exact setAt2_of_ne (fun h => ha h.2))]
      rw [ht]
      show setAt2 s.deposited interopPoolChainId a _ interopPoolChainId a' = _
      rw [setAt2_of_ne (fun h => ha h.2)]
      exact h1
  | enableInterop c =>
    obtain ⟨-, -, -, rfl⟩ := enableInterop_some h
    exact hid
  | initializeUpgrade =>
    obtain ⟨-, rfl⟩ := initializeUpgrade_some h
    exact hid
  | register c =>
    obtain ⟨-, -, -, -, rfl⟩ := registerChain_some h
    exact hid
  | populateBridgedOut a' x =>
    obtain ⟨-, rfl⟩ := populateBridgedOutEntry_some h
    exact hid


theorem covered_step {l1 : ChainId} {call : PoolCall} (hs : PoolFlagInv s)
    (hcov : PoolCovered s) (h : poolCall l1 call s = some t) : PoolCovered t := by
  cases call with
  | toChain c a x o =>
    rcases handleBridgeToChain_some h with ⟨-, -, ht⟩ | ⟨-, ht⟩
    · intro a'
      have h1 := hcov a'
      rw [ht]
      show s.withdrawn interopPoolChainId a' ≤ setAt2 s.deposited _ a _ interopPoolChainId a'
      rw [setAt2_apply]
      split_ifs with hh
      · rw [← hh.1, ← hh.2]; omega
      · exact h1
    · intro a'; rw [ht]; exact hcov a'
  | fromChain c a x o =>
    rcases handleBridgeFromChain_some h with ⟨-, -, hcap, ht⟩ | ⟨-, ht⟩
    · intro a'
      have h1 := hcov a'
      rw [ht]
      show setAt2 s.withdrawn _ a _ interopPoolChainId a' ≤ s.deposited interopPoolChainId a'
      rw [setAt2_apply]
      split_ifs with hh
      · obtain ⟨hk, rfl⟩ := hh
        rw [← hk] at hcap
        have h2 := hcap hs.pending_pool
        rw [hs.poolNoBackfill] at h2
        rw [← hk]
        omega
      · exact h1
    · intro a'; rw [ht]; exact hcov a'
  | setBackfill c a x =>
    obtain ⟨-, -, hcase⟩ := setChainBalanceBackfill_some h
    rcases hcase with ⟨-, -, -, ht⟩ | ⟨-, ht⟩
    · intro a'
      have h1 := hcov a'
      rw [ht]
      show s.withdrawn interopPoolChainId a' ≤ setAt2 s.deposited interopPoolChainId a _ interopPoolChainId a'
      rw [setAt2_apply]
      split_ifs with hh
      · rw [← hh.2]; omega
      · exact h1
    · intro a'; rw [ht]; exact hcov a'
  | markBackfilled c =>
    obtain ⟨-, rfl⟩ := markBackfilled_some h
    exact hcov
  | move c a =>
    obtain ⟨-, -, -, -, -, ht⟩ := moveChainBalanceToInteropPool_some h
    intro a'
    have h1 := hcov a'
    rw [ht]
    show s.withdrawn interopPoolChainId a' ≤ setAt2 s.deposited interopPoolChainId a _ interopPoolChainId a'
    rw [setAt2_apply]
    split_ifs with hh
    · rw [← hh.2]; omega
    · exact h1
  | enableInterop c =>
    obtain ⟨-, -, -, rfl⟩ := enableInterop_some h
    exact hcov
  | initializeUpgrade =>
    obtain ⟨-, rfl⟩ := initializeUpgrade_some h
    exact hcov
  | register c =>
    obtain ⟨-, -, -, -, rfl⟩ := registerChain_some h
    exact hcov
  | populateBridgedOut a' x =>
    obtain ⟨-, rfl⟩ := populateBridgedOutEntry_some h
    exact hcov

/-! ## Runs -/

theorem PoolRun.append {l1 : ChainId} {s m t : PoolSys} {L₁ L₂ : List PoolCall}
    (h₁ : PoolRun l1 s L₁ m) (h₂ : PoolRun l1 m L₂ t) : PoolRun l1 s (L₁ ++ L₂) t := by
  induction h₁ with
  | nil => exact h₂
  | cons hs _ ih => exact PoolRun.cons hs (ih h₂)

theorem poolRun_of_runPoolCalls {l1 : ChainId} :
    ∀ {L : List PoolCall} {s t : PoolSys}, runPoolCalls l1 L s = some t → PoolRun l1 s L t
  | [], s, t, h => by
    simp only [runPoolCalls, Option.some.injEq] at h
    subst h
    exact PoolRun.nil s
  | call :: L, s, t, h => by
    simp only [runPoolCalls] at h
    cases hc : poolCall l1 call s with
    | none => rw [hc] at h; cases h
    | some m =>
      rw [hc] at h
      exact PoolRun.cons hc (poolRun_of_runPoolCalls h)

theorem runPoolCalls_of_poolRun {l1 : ChainId} {s t : PoolSys} {L : List PoolCall}
    (h : PoolRun l1 s L t) : runPoolCalls l1 L s = some t := by
  induction h with
  | nil => rfl
  | cons hs _ ih =>
    simp only [runPoolCalls, hs]
    exact ih

/-- An invariant of every call holds along every run. -/
theorem PoolRun.preserves {l1 : ChainId} (P : PoolSys → Prop)
    (hstep : ∀ (call : PoolCall) (s t : PoolSys), P s → poolCall l1 call s = some t → P t)
    {s t : PoolSys} {L : List PoolCall} (h : PoolRun l1 s L t) (hs : P s) : P t := by
  induction h with
  | nil => exact hs
  | cons hc _ ih => exact ih (hstep _ _ _ hs hc)

/-- The three invariants together. -/
theorem ledgerInv_step {l1 : ChainId} {call : PoolCall}
    (hs : PoolFlagInv s ∧ PoolIdentity s ∧ PoolCovered s) (h : poolCall l1 call s = some t) :
    PoolFlagInv t ∧ PoolIdentity t ∧ PoolCovered t :=
  ⟨flagInv_step hs.1 h, identity_step hs.1 hs.2.1 h, covered_step hs.1 hs.2.2 h⟩

theorem movedNet_zero_of_noneInPool (h : ∀ c a, s.inPool c a = false) (a : AssetId) :
    movedNet s a = 0 := by
  unfold movedNet
  apply Finset.sum_eq_zero
  intro c _
  unfold netTerm
  rw [h c a]
  rfl

/-- `initializeUpgrade` from a `PreUpgrade` state establishes the three invariants. -/
theorem postUpgrade_inv {pre s₀ : PoolSys} (hpre : PreUpgrade pre)
    (hinit : initializeUpgrade pre = some s₀) :
    PoolFlagInv s₀ ∧ PoolIdentity s₀ ∧ PoolCovered s₀ := by
  obtain ⟨-, rfl⟩ := initializeUpgrade_some hinit
  refine ⟨⟨le_refl 2, hpre.poolUnregistered, ?_, ?_, ?_, ?_, hpre.poolBackfillZero⟩, ?_, ?_⟩
  · intro c hc
    rw [show pre.interop c = false from hpre.noInterop c] at hc
    cases hc
  · intro c hc
    show pre.registered c = true
    simp only [Bool.or_eq_true] at hc
    rcases hc with hc | hc
    · exact hpre.pendingRegistered c hc
    · exact hc
  · intro c hc
    rw [show pre.interop c = false from hpre.noInterop c] at hc
    cases hc
  · intro c a hc
    rw [show pre.inPool c a = false from hpre.noneInPool c a] at hc
    cases hc
  · intro a
    show pre.deposited interopPoolChainId a = pre.directToPool a + movedNet _ a
    rw [hpre.poolDepositedZero a, hpre.noDirect a, Nat.zero_add]
    exact (movedNet_zero_of_noneInPool hpre.noneInPool a).symm
  · intro a
    show pre.withdrawn interopPoolChainId a ≤ pre.deposited interopPoolChainId a
    rw [hpre.poolDepositedZero a, hpre.poolWithdrawnZero a]

/-! ## Per-call frame facts -/

/-- An enabled chain's own totals are not written. -/
theorem enabled_totals_step {l1 : ChainId} {call : PoolCall} (hs : PoolFlagInv s) {c : ChainId}
    (hc : s.interop c = true) (h : poolCall l1 call s = some t) (a : AssetId) :
    t.deposited c a = s.deposited c a ∧ t.withdrawn c a = s.withdrawn c a := by
  have hcp := hs.ne_pool_of_interop hc
  cases call with
  | toChain c' a' x o =>
    rcases handleBridgeToChain_some h with ⟨-, -, ht⟩ | ⟨-, ht⟩
    · rw [ht]
      exact ⟨setAt2_of_ne (fun hh => hs.key_ne hc c' o hh.1.symm), rfl⟩
    · rw [ht]; exact ⟨rfl, rfl⟩
  | fromChain c' a' x o =>
    rcases handleBridgeFromChain_some h with ⟨-, -, -, ht⟩ | ⟨-, ht⟩
    · rw [ht]
      exact ⟨rfl, setAt2_of_ne (fun hh => hs.key_ne hc c' o hh.1.symm)⟩
    · rw [ht]; exact ⟨rfl, rfl⟩
  | setBackfill c' a' x =>
    obtain ⟨-, -, hcase⟩ := setChainBalanceBackfill_some h
    rcases hcase with ⟨-, -, -, ht⟩ | ⟨-, ht⟩
    · rw [ht]; exact ⟨setAt2_of_ne (fun hh => hcp hh.1), rfl⟩
    · rw [ht]; exact ⟨rfl, rfl⟩
  | markBackfilled c' =>
    obtain ⟨-, rfl⟩ := markBackfilled_some h
    exact ⟨rfl, rfl⟩
  | move c' a' =>
    obtain ⟨-, -, -, -, -, ht⟩ := moveChainBalanceToInteropPool_some h
    rw [ht]; exact ⟨setAt2_of_ne (fun hh => hcp hh.1), rfl⟩
  | enableInterop c' =>
    obtain ⟨-, -, -, rfl⟩ := enableInterop_some h
    exact ⟨rfl, rfl⟩
  | initializeUpgrade =>
    obtain ⟨-, rfl⟩ := initializeUpgrade_some h
    exact ⟨rfl, rfl⟩
  | register c' =>
    obtain ⟨-, -, -, -, rfl⟩ := registerChain_some h
    exact ⟨rfl, rfl⟩
  | populateBridgedOut a' x =>
    obtain ⟨-, rfl⟩ := populateBridgedOutEntry_some h
    exact ⟨rfl, rfl⟩

/-- Totals never decrease, from any state. -/
theorem totals_grow_step {l1 : ChainId} {call : PoolCall} (h : poolCall l1 call s = some t)
    (k a : ChainId) : s.deposited k a ≤ t.deposited k a ∧ s.withdrawn k a ≤ t.withdrawn k a := by
  cases call with
  | toChain c' a' x o =>
    rcases handleBridgeToChain_some h with ⟨-, -, ht⟩ | ⟨-, ht⟩
    · rw [ht]
      refine ⟨?_, le_refl _⟩
      show s.deposited k a ≤ setAt2 s.deposited _ a' _ k a
      rw [setAt2_apply]
      split_ifs with hh
      · rw [hh.1, hh.2]; omega
      · exact le_refl _
    · rw [ht]; exact ⟨le_refl _, le_refl _⟩
  | fromChain c' a' x o =>
    rcases handleBridgeFromChain_some h with ⟨-, -, -, ht⟩ | ⟨-, ht⟩
    · rw [ht]
      refine ⟨le_refl _, ?_⟩
      show s.withdrawn k a ≤ setAt2 s.withdrawn _ a' _ k a
      rw [setAt2_apply]
      split_ifs with hh
      · rw [hh.1, hh.2]; omega
      · exact le_refl _
    · rw [ht]; exact ⟨le_refl _, le_refl _⟩
  | setBackfill c' a' x =>
    obtain ⟨-, -, hcase⟩ := setChainBalanceBackfill_some h
    rcases hcase with ⟨-, -, -, ht⟩ | ⟨-, ht⟩
    · rw [ht]
      refine ⟨?_, le_refl _⟩
      show s.deposited k a ≤ setAt2 s.deposited interopPoolChainId a' _ k a
      rw [setAt2_apply]
      split_ifs with hh
      · rw [hh.1, hh.2]; omega
      · exact le_refl _
    · rw [ht]; exact ⟨le_refl _, le_refl _⟩
  | markBackfilled c' =>
    obtain ⟨-, rfl⟩ := markBackfilled_some h
    exact ⟨le_refl _, le_refl _⟩
  | move c' a' =>
    obtain ⟨-, -, -, -, -, ht⟩ := moveChainBalanceToInteropPool_some h
    rw [ht]
    refine ⟨?_, le_refl _⟩
    show s.deposited k a ≤ setAt2 s.deposited interopPoolChainId a' _ k a
    rw [setAt2_apply]
    split_ifs with hh
    · rw [hh.1, hh.2]; omega
    · exact le_refl _
  | enableInterop c' =>
    obtain ⟨-, -, -, rfl⟩ := enableInterop_some h
    exact ⟨le_refl _, le_refl _⟩
  | initializeUpgrade =>
    obtain ⟨-, rfl⟩ := initializeUpgrade_some h
    exact ⟨le_refl _, le_refl _⟩
  | register c' =>
    obtain ⟨-, -, -, -, rfl⟩ := registerChain_some h
    exact ⟨le_refl _, le_refl _⟩
  | populateBridgedOut a' x =>
    obtain ⟨-, rfl⟩ := populateBridgedOutEntry_some h
    exact ⟨le_refl _, le_refl _⟩

/-- The flags, from any state: `interop` and `inPool` never go from true to false; the version
never decreases; from version 2 on, `pending` never goes from false to true. -/
theorem flags_step {l1 : ChainId} {call : PoolCall} (h : poolCall l1 call s = some t) :
    (∀ c, s.interop c = true → t.interop c = true)
    ∧ (∀ c a, s.inPool c a = true → t.inPool c a = true)
    ∧ s.initVersion ≤ t.initVersion
    ∧ (2 ≤ s.initVersion → ∀ c, t.pending c = true → s.pending c = true) := by
  cases call with
  | toChain c' a' x o =>
    rcases handleBridgeToChain_some h with ⟨-, -, ht⟩ | ⟨-, ht⟩ <;>
    · rw [ht]; exact ⟨fun _ h => h, fun _ _ h => h, le_refl _, fun _ _ h => h⟩
  | fromChain c' a' x o =>
    rcases handleBridgeFromChain_some h with ⟨-, -, -, ht⟩ | ⟨-, ht⟩ <;>
    · rw [ht]; exact ⟨fun _ h => h, fun _ _ h => h, le_refl _, fun _ _ h => h⟩
  | setBackfill c' a' x =>
    obtain ⟨-, -, hcase⟩ := setChainBalanceBackfill_some h
    rcases hcase with ⟨-, -, -, ht⟩ | ⟨-, ht⟩ <;>
    · rw [ht]; exact ⟨fun _ h => h, fun _ _ h => h, le_refl _, fun _ _ h => h⟩
  | markBackfilled c' =>
    obtain ⟨-, rfl⟩ := markBackfilled_some h
    refine ⟨fun _ h => h, fun _ _ h => h, le_refl _, fun _ c hc => ?_⟩
    simp only [setAt_apply] at hc
    split_ifs at hc
    exact hc
  | move c' a' =>
    obtain ⟨-, -, -, -, -, rfl⟩ := moveChainBalanceToInteropPool_some h
    refine ⟨fun _ h => h, fun c a hc => ?_, le_refl _, fun _ _ h => h⟩
    show setAt2 s.inPool c' a' true c a = true
    rw [setAt2_apply]
    split_ifs
    · rfl
    · exact hc
  | enableInterop c' =>
    obtain ⟨-, -, -, rfl⟩ := enableInterop_some h
    refine ⟨fun c hc => ?_, fun _ _ h => h, le_refl _, fun _ _ h => h⟩
    show setAt s.interop c' true c = true
    rw [setAt_apply]
    split_ifs
    · rfl
    · exact hc
  | initializeUpgrade =>
    obtain ⟨hv, rfl⟩ := initializeUpgrade_some h
    exact ⟨fun _ h => h, fun _ _ h => h, by show s.initVersion ≤ 2; omega,
      fun h2 => absurd h2 (by omega)⟩
  | register c' =>
    obtain ⟨-, -, -, -, rfl⟩ := registerChain_some h
    exact ⟨fun _ h => h, fun _ _ h => h, le_refl _, fun _ _ h => h⟩
  | populateBridgedOut a' x =>
    obtain ⟨-, rfl⟩ := populateBridgedOutEntry_some h
    exact ⟨fun _ h => h, fun _ _ h => h, le_refl _, fun _ _ h => h⟩

/-- A nonzero backfill is never rewritten, from any state. -/
theorem backfill_nonzero_step {l1 : ChainId} {call : PoolCall} (h : poolCall l1 call s = some t)
    {c a : ChainId} (hb : s.backfill c a ≠ 0) : t.backfill c a = s.backfill c a := by
  cases call with
  | toChain c' a' x o =>
    rcases handleBridgeToChain_some h with ⟨-, -, ht⟩ | ⟨-, ht⟩ <;> rw [ht]
  | fromChain c' a' x o =>
    rcases handleBridgeFromChain_some h with ⟨-, -, -, ht⟩ | ⟨-, ht⟩ <;> rw [ht]
  | setBackfill c' a' x =>
    obtain ⟨-, hb0, hcase⟩ := setChainBalanceBackfill_some h
    have hne : ¬(c = c' ∧ a = a') := by
      rintro ⟨rfl, rfl⟩
      exact hb hb0
    rcases hcase with ⟨-, -, -, ht⟩ | ⟨-, ht⟩ <;>
    · rw [ht]; exact setAt2_of_ne hne
  | markBackfilled c' =>
    obtain ⟨-, rfl⟩ := markBackfilled_some h
    rfl
  | move c' a' =>
    obtain ⟨-, -, -, -, -, ht⟩ := moveChainBalanceToInteropPool_some h
    rw [ht]
  | enableInterop c' =>
    obtain ⟨-, -, -, rfl⟩ := enableInterop_some h
    rfl
  | initializeUpgrade =>
    obtain ⟨-, rfl⟩ := initializeUpgrade_some h
    rfl
  | register c' =>
    obtain ⟨-, -, -, -, rfl⟩ := registerChain_some h
    rfl
  | populateBridgedOut a' x =>
    obtain ⟨-, rfl⟩ := populateBridgedOutEntry_some h
    rfl


/-! ## Commutation of `move` and a late backfill -/

theorem setChainBalanceBackfill_eq_out {c a : ChainId} {x : UInt256}
    (hc : c ≠ interopPoolChainId) (hb0 : s.backfill c a = 0) (hin : s.inPool c a = false) :
    setChainBalanceBackfill s c a x = some { s with backfill := setAt2 s.backfill c a x.val } := by
  unfold setChainBalanceBackfill
  rw [ite_eq_right hc, ite_eq_right (by simpa using hb0), ite_eq_right (by simp [hin])]

theorem setChainBalanceBackfill_eq_in {c a : ChainId} {x : UInt256}
    (hc : c ≠ interopPoolChainId) (hb0 : s.backfill c a = 0) (hin : s.inPool c a = true)
    (h1 : s.deposited c a + x.val < UInt256.size)
    (h2 : s.deposited interopPoolChainId a
      + ((s.deposited c a + x.val - s.withdrawn c a) - (s.deposited c a - s.withdrawn c a))
      < UInt256.size) :
    setChainBalanceBackfill s c a x = some { s with
      deposited := setAt2 s.deposited interopPoolChainId a
        (s.deposited interopPoolChainId a
          + ((s.deposited c a + x.val - s.withdrawn c a) - (s.deposited c a - s.withdrawn c a)))
      backfill := setAt2 s.backfill c a x.val } := by
  unfold setChainBalanceBackfill
  rw [ite_eq_right hc, ite_eq_right (by simpa using hb0), ite_eq_left hin,
    ite_eq_right (by omega)]
  dsimp only
  simp only [netOf_eq, Nat.add_zero]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem moveChainBalanceToInteropPool_eq {c a : ChainId} (hi : s.interop c = true)
    (hp : s.pending c = false) (hin : s.inPool c a = false)
    (h1 : s.deposited c a + s.backfill c a < UInt256.size)
    (h2 : s.deposited interopPoolChainId a + (s.deposited c a + s.backfill c a - s.withdrawn c a)
      < UInt256.size) :
    moveChainBalanceToInteropPool s c a = some { s with
      inPool := setAt2 s.inPool c a true
      deposited := setAt2 s.deposited interopPoolChainId a
        (s.deposited interopPoolChainId a
          + (s.deposited c a + s.backfill c a - s.withdrawn c a)) } := by
  unfold moveChainBalanceToInteropPool
  rw [ite_eq_right (by simp [hi]), ite_eq_right (by simp [hp]), ite_eq_right (by simp [hin]),
    ite_eq_right (by omega)]
  dsimp only
  simp only [netOf_eq]
  rw [ite_eq_right (by omega)]

theorem move_backfill_commute (s : PoolSys) (c a : ChainId) (x : UInt256) :
    (moveChainBalanceToInteropPool s c a).bind (fun m => setChainBalanceBackfill m c a x)
      = (setChainBalanceBackfill s c a x).bind (fun m => moveChainBalanceToInteropPool m c a) := by
  apply Option.ext
  intro u
  rw [Option.bind_eq_some_iff, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨m, hm, hu⟩
    obtain ⟨hi, hp, hin, hb1, hb2, rfl⟩ := moveChainBalanceToInteropPool_some hm
    obtain ⟨hc, hb0, hcase⟩ := setChainBalanceBackfill_some hu
    change s.backfill c a = 0 at hb0
    rcases hcase with ⟨-, hx1, hx2, rfl⟩ | ⟨hin', -⟩
    · change setAt2 s.deposited interopPoolChainId a _ c a + x.val < UInt256.size at hx1
      rw [setAt2_of_ne (fun h => hc h.1)] at hx1
      change setAt2 s.deposited interopPoolChainId a _ interopPoolChainId a
        + ((setAt2 s.deposited interopPoolChainId a _ c a + x.val - s.withdrawn c a)
          - (setAt2 s.deposited interopPoolChainId a _ c a - s.withdrawn c a)) < UInt256.size at hx2
      rw [setAt2_self, setAt2_of_ne (fun h => hc h.1)] at hx2
      rw [hb0, Nat.add_zero] at hb2
      refine ⟨{ s with backfill := setAt2 s.backfill c a x.val },
        setChainBalanceBackfill_eq_out hc hb0 hin, ?_⟩
      rw [moveChainBalanceToInteropPool_eq (s := { s with backfill := setAt2 s.backfill c a x.val })
        hi hp hin (by show s.deposited c a + setAt2 s.backfill c a x.val c a < UInt256.size
                      rw [setAt2_self]; exact hx1)
        (by show s.deposited interopPoolChainId a
                + (s.deposited c a + setAt2 s.backfill c a x.val c a - s.withdrawn c a)
                < UInt256.size
            rw [setAt2_self]; omega)]
      congr 1
      simp only [setAt2_self, setAt2_of_ne (fun h : c = interopPoolChainId ∧ a = a => hc h.1),
        hb0, Nat.add_zero]
      congr 1
      funext c' a'
      simp only [setAt2_apply]
      split_ifs <;> omega
    · exfalso
      change setAt2 s.inPool c a true c a = false at hin'
      rw [setAt2_self] at hin'
      cases hin'
  · rintro ⟨m, hm, hu⟩
    obtain ⟨hc, hb0, hcase⟩ := setChainBalanceBackfill_some hm
    rcases hcase with ⟨hin, -, -, rfl⟩ | ⟨hin, rfl⟩
    · exfalso
      obtain ⟨-, -, hin', -⟩ := moveChainBalanceToInteropPool_some hu
      change s.inPool c a = false at hin'
      rw [hin] at hin'
      cases hin'
    · obtain ⟨hi, hp, -, hb1, hb2, rfl⟩ := moveChainBalanceToInteropPool_some hu
      change s.deposited c a + setAt2 s.backfill c a x.val c a < UInt256.size at hb1
      change s.deposited interopPoolChainId a
        + (s.deposited c a + setAt2 s.backfill c a x.val c a - s.withdrawn c a)
        < UInt256.size at hb2
      rw [setAt2_self] at hb1 hb2
      refine ⟨{ s with
          inPool := setAt2 s.inPool c a true
          deposited := setAt2 s.deposited interopPoolChainId a
            (s.deposited interopPoolChainId a
              + (s.deposited c a + s.backfill c a - s.withdrawn c a)) },
        moveChainBalanceToInteropPool_eq hi hp hin (by omega) (by rw [hb0]; omega), ?_⟩
      rw [setChainBalanceBackfill_eq_in (s := { s with
          inPool := setAt2 s.inPool c a true
          deposited := setAt2 s.deposited interopPoolChainId a
            (s.deposited interopPoolChainId a
              + (s.deposited c a + s.backfill c a - s.withdrawn c a)) })
        hc hb0 (setAt2_self _ _ _ _)
        (by show setAt2 s.deposited interopPoolChainId a _ c a + x.val < UInt256.size
            rw [setAt2_of_ne (fun h => hc h.1)]; exact hb1)
        (by show setAt2 s.deposited interopPoolChainId a _ interopPoolChainId a
                + ((setAt2 s.deposited interopPoolChainId a _ c a + x.val - s.withdrawn c a)
                  - (setAt2 s.deposited interopPoolChainId a _ c a - s.withdrawn c a))
                < UInt256.size
            rw [setAt2_self, setAt2_of_ne (fun h => hc h.1), hb0]
            omega)]
      congr 1
      simp only [setAt2_self, setAt2_of_ne (fun h : c = interopPoolChainId ∧ a = a => hc h.1),
        hb0, Nat.add_zero]
      congr 1
      funext c' a'
      simp only [setAt2_apply]
      split_ifs <;> omega


/-! ## More per-call facts -/

/-- Only `initializeUpgrade` writes the version. -/
theorem version_step {l1 : ChainId} {call : PoolCall} (h : poolCall l1 call s = some t)
    (hc : call ≠ PoolCall.initializeUpgrade) : t.initVersion = s.initVersion := by
  cases call with
  | toChain c' a' x o =>
    rcases handleBridgeToChain_some h with ⟨-, -, ht⟩ | ⟨-, ht⟩ <;> rw [ht]
  | fromChain c' a' x o =>
    rcases handleBridgeFromChain_some h with ⟨-, -, -, ht⟩ | ⟨-, ht⟩ <;> rw [ht]
  | setBackfill c' a' x =>
    obtain ⟨-, -, hcase⟩ := setChainBalanceBackfill_some h
    rcases hcase with ⟨-, -, -, ht⟩ | ⟨-, ht⟩ <;> rw [ht]
  | markBackfilled c' =>
    obtain ⟨-, rfl⟩ := markBackfilled_some h
    rfl
  | move c' a' =>
    obtain ⟨-, -, -, -, -, ht⟩ := moveChainBalanceToInteropPool_some h
    rw [ht]
  | enableInterop c' =>
    obtain ⟨-, -, -, rfl⟩ := enableInterop_some h
    rfl
  | initializeUpgrade => exact absurd rfl hc
  | register c' =>
    obtain ⟨-, -, -, -, rfl⟩ := registerChain_some h
    rfl
  | populateBridgedOut a' x =>
    obtain ⟨-, rfl⟩ := populateBridgedOutEntry_some h
    rfl

/-- Only `moveChainBalanceToInteropPool(c, a)` writes `chainBalanceInInteropPool[c][a]`. -/
theorem inPool_step_other {l1 : ChainId} {call : PoolCall} (h : poolCall l1 call s = some t)
    {c a : ChainId} (hc : call ≠ PoolCall.move c a) : t.inPool c a = s.inPool c a := by
  cases call with
  | toChain c' a' x o =>
    rcases handleBridgeToChain_some h with ⟨-, -, ht⟩ | ⟨-, ht⟩ <;> rw [ht]
  | fromChain c' a' x o =>
    rcases handleBridgeFromChain_some h with ⟨-, -, -, ht⟩ | ⟨-, ht⟩ <;> rw [ht]
  | setBackfill c' a' x =>
    obtain ⟨-, -, hcase⟩ := setChainBalanceBackfill_some h
    rcases hcase with ⟨-, -, -, ht⟩ | ⟨-, ht⟩ <;> rw [ht]
  | markBackfilled c' =>
    obtain ⟨-, rfl⟩ := markBackfilled_some h
    rfl
  | move c' a' =>
    obtain ⟨-, -, -, -, -, ht⟩ := moveChainBalanceToInteropPool_some h
    rw [ht]
    show setAt2 s.inPool c' a' true c a = s.inPool c a
    apply setAt2_of_ne
    rintro ⟨rfl, rfl⟩
    exact hc rfl
  | enableInterop c' =>
    obtain ⟨-, -, -, rfl⟩ := enableInterop_some h
    rfl
  | initializeUpgrade =>
    obtain ⟨-, rfl⟩ := initializeUpgrade_some h
    rfl
  | register c' =>
    obtain ⟨-, -, -, -, rfl⟩ := registerChain_some h
    rfl
  | populateBridgedOut a' x =>
    obtain ⟨-, rfl⟩ := populateBridgedOutEntry_some h
    rfl

/-- A call that does not name `c` leaves `c`'s slots alone, if `c` is neither the pool's key nor
registered. -/
theorem unnamed_step {l1 : ChainId} {call : PoolCall} (h : poolCall l1 call s = some t)
    {c : ChainId} (hcp : c ≠ interopPoolChainId) (hreg : s.registered c = false)
    (hname : call.chainArg ≠ some c) :
    t.registered c = false ∧ t.pending c = s.pending c ∧ t.interop c = s.interop c
      ∧ ∀ a, t.inPool c a = s.inPool c a ∧ t.deposited c a = s.deposited c a
        ∧ t.withdrawn c a = s.withdrawn c a ∧ t.backfill c a = s.backfill c a := by
  cases call with
  | toChain c' a' x o =>
    have hc' : c' ≠ c := fun he => hname (by rw [he]; rfl)
    have hk : (trackedBalance s c' o).2 ≠ c := by
      rw [trackedBalance_key]
      split_ifs
      · exact Ne.symm hcp
      · exact hc'
    rcases handleBridgeToChain_some h with ⟨-, -, ht⟩ | ⟨-, ht⟩ <;> rw [ht]
    · exact ⟨hreg, rfl, rfl, fun a => ⟨rfl, setAt2_of_ne (fun hh => hk hh.1.symm), rfl, rfl⟩⟩
    · exact ⟨hreg, rfl, rfl, fun a => ⟨rfl, rfl, rfl, rfl⟩⟩
  | fromChain c' a' x o =>
    have hc' : c' ≠ c := fun he => hname (by rw [he]; rfl)
    have hk : (trackedBalance s c' o).2 ≠ c := by
      rw [trackedBalance_key]
      split_ifs
      · exact Ne.symm hcp
      · exact hc'
    rcases handleBridgeFromChain_some h with ⟨-, -, -, ht⟩ | ⟨-, ht⟩ <;> rw [ht]
    · exact ⟨hreg, rfl, rfl, fun a => ⟨rfl, rfl, setAt2_of_ne (fun hh => hk hh.1.symm), rfl⟩⟩
    · exact ⟨hreg, rfl, rfl, fun a => ⟨rfl, rfl, rfl, rfl⟩⟩
  | setBackfill c' a' x =>
    have hc' : c' ≠ c := fun he => hname (by rw [he]; rfl)
    obtain ⟨-, -, hcase⟩ := setChainBalanceBackfill_some h
    rcases hcase with ⟨-, -, -, ht⟩ | ⟨-, ht⟩ <;> rw [ht]
    · exact ⟨hreg, rfl, rfl, fun a => ⟨rfl, setAt2_of_ne (fun hh => hcp hh.1), rfl,
        setAt2_of_ne (fun hh => hc' hh.1.symm)⟩⟩
    · exact ⟨hreg, rfl, rfl, fun a => ⟨rfl, rfl, rfl, setAt2_of_ne (fun hh => hc' hh.1.symm)⟩⟩
  | markBackfilled c' =>
    have hc' : c' ≠ c := fun he => hname (by rw [he]; rfl)
    obtain ⟨-, rfl⟩ := markBackfilled_some h
    exact ⟨hreg, setAt_of_ne (Ne.symm hc'), rfl, fun a => ⟨rfl, rfl, rfl, rfl⟩⟩
  | move c' a' =>
    have hc' : c' ≠ c := fun he => hname (by rw [he]; rfl)
    obtain ⟨-, -, -, -, -, ht⟩ := moveChainBalanceToInteropPool_some h
    rw [ht]
    exact ⟨hreg, rfl, rfl, fun a => ⟨setAt2_of_ne (fun hh => hc' hh.1.symm),
      setAt2_of_ne (fun hh => hcp hh.1), rfl, rfl⟩⟩
  | enableInterop c' =>
    have hc' : c' ≠ c := fun he => hname (by rw [he]; rfl)
    obtain ⟨-, -, -, rfl⟩ := enableInterop_some h
    exact ⟨hreg, rfl, setAt_of_ne (Ne.symm hc'), fun a => ⟨rfl, rfl, rfl, rfl⟩⟩
  | initializeUpgrade =>
    obtain ⟨-, rfl⟩ := initializeUpgrade_some h
    refine ⟨hreg, ?_, rfl, fun a => ⟨rfl, rfl, rfl, rfl⟩⟩
    show (s.pending c || s.registered c) = s.pending c
    rw [hreg, Bool.or_false]
  | register c' =>
    have hc' : c' ≠ c := fun he => hname (by rw [he]; rfl)
    obtain ⟨-, -, -, -, rfl⟩ := registerChain_some h
    refine ⟨?_, rfl, rfl, fun a => ⟨rfl, rfl, rfl, rfl⟩⟩
    show setAt s.registered c' true c = false
    rw [setAt_of_ne (Ne.symm hc')]
    exact hreg
  | populateBridgedOut a' x =>
    obtain ⟨-, rfl⟩ := populateBridgedOutEntry_some h
    exact ⟨hreg, rfl, rfl, fun a => ⟨rfl, rfl, rfl, rfl⟩⟩

/-- What a call adds to the ghost. -/
theorem ghost_step {l1 : ChainId} {call : PoolCall} (h : poolCall l1 call s = some t)
    (a : AssetId) : t.directToPool a = s.directToPool a + poolKeyedDeposit s call a := by
  cases call with
  | toChain c' a' x o =>
    rcases handleBridgeToChain_some h with ⟨htr, -, ht⟩ | ⟨htr, ht⟩ <;> rw [ht]
    · show (if (trackedBalance s c' o).2 = interopPoolChainId
          then setAt s.directToPool a' (s.directToPool a' + x.val) else s.directToPool) a
        = s.directToPool a
          + (if a' = a ∧ trackedBalance s c' o = (true, interopPoolChainId) then x.val else 0)
      have hpair : trackedBalance s c' o = (true, interopPoolChainId)
          ↔ (trackedBalance s c' o).2 = interopPoolChainId := by
        constructor
        · intro hh; rw [hh]
        · intro hh; exact Prod.ext htr hh
      by_cases hk : (trackedBalance s c' o).2 = interopPoolChainId
      · rw [ite_eq_left hk, setAt_apply]
        by_cases ha : a' = a
        · subst ha
          rw [ite_eq_left rfl, ite_eq_left ⟨rfl, hpair.2 hk⟩]
        · rw [ite_eq_right (Ne.symm ha), ite_eq_right (fun hh => ha hh.1), Nat.add_zero]
      · rw [ite_eq_right hk, ite_eq_right (fun hh => hk (hpair.1 hh.2)), Nat.add_zero]
    · show s.directToPool a = s.directToPool a
          + (if a' = a ∧ trackedBalance s c' o = (true, interopPoolChainId) then x.val else 0)
      rw [ite_eq_right (fun hh => by rw [hh.2] at htr; cases htr), Nat.add_zero]
  | fromChain c' a' x o =>
    rcases handleBridgeFromChain_some h with ⟨-, -, -, ht⟩ | ⟨-, ht⟩ <;> rw [ht] <;> rfl
  | setBackfill c' a' x =>
    obtain ⟨-, -, hcase⟩ := setChainBalanceBackfill_some h
    rcases hcase with ⟨-, -, -, ht⟩ | ⟨-, ht⟩ <;> rw [ht] <;> rfl
  | markBackfilled c' =>
    obtain ⟨-, rfl⟩ := markBackfilled_some h
    rfl
  | move c' a' =>
    obtain ⟨-, -, -, -, -, ht⟩ := moveChainBalanceToInteropPool_some h
    rw [ht]
    rfl
  | enableInterop c' =>
    obtain ⟨-, -, -, rfl⟩ := enableInterop_some h
    rfl
  | initializeUpgrade =>
    obtain ⟨-, rfl⟩ := initializeUpgrade_some h
    rfl
  | register c' =>
    obtain ⟨-, -, -, -, rfl⟩ := registerChain_some h
    rfl
  | populateBridgedOut a' x =>
    obtain ⟨-, rfl⟩ := populateBridgedOutEntry_some h
    rfl

/-! ## Run-level facts -/

theorem flags_run {l1 : ChainId} {L : List PoolCall} (h : PoolRun l1 s L t) :
    (∀ c, s.interop c = true → t.interop c = true)
    ∧ (∀ c a, s.inPool c a = true → t.inPool c a = true)
    ∧ s.initVersion ≤ t.initVersion
    ∧ (2 ≤ s.initVersion → ∀ c, t.pending c = true → s.pending c = true) := by
  induction h with
  | nil s => exact ⟨fun _ h => h, fun _ _ h => h, le_refl _, fun _ _ h => h⟩
  | cons hstep _ ih =>
    obtain ⟨i1, p1, v1, d1⟩ := flags_step hstep
    obtain ⟨i2, p2, v2, d2⟩ := ih
    exact ⟨fun c h => i2 c (i1 c h), fun c a h => p2 c a (p1 c a h), le_trans v1 v2,
      fun hv c hc => d1 hv c (d2 (le_trans hv v1) c hc)⟩

theorem init_count_run {l1 : ChainId} {L : List PoolCall} (h : PoolRun l1 s L t) :
    L.count PoolCall.initializeUpgrade ≤ (if s.initVersion < 2 then 1 else 0) := by
  induction h with
  | nil s => exact Nat.zero_le _
  | @cons s m t call calls hstep _ ih =>
    rw [List.count_cons]
    by_cases hc : call = PoolCall.initializeUpgrade
    · subst hc
      obtain ⟨hv, rfl⟩ := initializeUpgrade_some hstep
      rw [ite_eq_left hv]
      have ih' : calls.count PoolCall.initializeUpgrade ≤ 0 := by
        have := ih
        rw [ite_eq_right (show ¬ (2 : ℕ) < 2 by omega)] at this
        exact this
      rw [ite_eq_left (beq_self_eq_true _)]
      omega
    · rw [version_step hstep hc] at ih
      rw [ite_eq_right (by simpa using hc), Nat.add_zero]
      exact ih

theorem move_count_run {l1 : ChainId} {L : List PoolCall} (h : PoolRun l1 s L t) (c a : ChainId) :
    L.count (PoolCall.move c a) ≤ (if s.inPool c a = true then 0 else 1) := by
  induction h with
  | nil s => exact Nat.zero_le _
  | @cons s m t call calls hstep _ ih =>
    rw [List.count_cons]
    by_cases hc : call = PoolCall.move c a
    · subst hc
      obtain ⟨-, -, hin, -, -, ht⟩ := moveChainBalanceToInteropPool_some hstep
      have hm : m.inPool c a = true := by
        rw [ht]
        exact setAt2_self _ _ _ _
      rw [hm, ite_eq_left rfl] at ih
      rw [hin, ite_eq_left (beq_self_eq_true _)]
      simp only [Bool.false_eq_true, ite_false]
      omega
    · rw [inPool_step_other hstep hc] at ih
      rw [ite_eq_right (by simpa using hc), Nat.add_zero]
      exact ih

theorem backfill_nonzero_run {l1 : ChainId} {L : List PoolCall} (h : PoolRun l1 s L t)
    {c a : ChainId} (hb : s.backfill c a ≠ 0) : t.backfill c a = s.backfill c a := by
  induction h with
  | nil s => rfl
  | cons hstep _ ih =>
    have e := backfill_nonzero_step hstep hb
    rw [ih (by rw [e]; exact hb), e]

theorem totals_grow_run {l1 : ChainId} {L : List PoolCall} (h : PoolRun l1 s L t) (k a : ChainId) :
    s.deposited k a ≤ t.deposited k a ∧ s.withdrawn k a ≤ t.withdrawn k a := by
  induction h with
  | nil s => exact ⟨le_refl _, le_refl _⟩
  | cons hstep _ ih =>
    obtain ⟨d1, w1⟩ := totals_grow_step hstep k a
    exact ⟨le_trans d1 ih.1, le_trans w1 ih.2⟩

theorem frozen_run {l1 : ChainId} {L : List PoolCall} (h : PoolRun l1 s L t)
    (hs : PoolFlagInv s) {c : ChainId} (hc : s.interop c = true) (a : AssetId) :
    t.deposited c a = s.deposited c a ∧ t.withdrawn c a = s.withdrawn c a := by
  induction h with
  | nil s => exact ⟨rfl, rfl⟩
  | cons hstep _ ih =>
    obtain ⟨d1, w1⟩ := enabled_totals_step hs hc hstep a
    obtain ⟨d2, w2⟩ := ih (flagInv_step hs hstep) ((flags_step hstep).1 c hc)
    exact ⟨d2.trans d1, w2.trans w1⟩

theorem unnamed_run {l1 : ChainId} {L : List PoolCall} (h : PoolRun l1 s L t) {c : ChainId}
    (hcp : c ≠ interopPoolChainId) (hreg : s.registered c = false)
    (hname : ∀ call ∈ L, call.chainArg ≠ some c) :
    t.registered c = false ∧ t.pending c = s.pending c ∧ t.interop c = s.interop c
      ∧ ∀ a, t.inPool c a = s.inPool c a ∧ t.deposited c a = s.deposited c a
        ∧ t.withdrawn c a = s.withdrawn c a ∧ t.backfill c a = s.backfill c a := by
  induction h with
  | nil s => exact ⟨hreg, rfl, rfl, fun a => ⟨rfl, rfl, rfl, rfl⟩⟩
  | @cons s m t call calls hstep _ ih =>
    obtain ⟨r1, p1, i1, f1⟩ :=
      unnamed_step hstep hcp hreg (hname call List.mem_cons_self)
    obtain ⟨r2, p2, i2, f2⟩ := ih r1 (fun call' hm => hname call' (List.mem_cons_of_mem _ hm))
    refine ⟨r2, p2.trans p1, i2.trans i1, fun a => ?_⟩
    obtain ⟨a1, b1, c1, d1⟩ := f1 a
    obtain ⟨a2, b2, c2, d2⟩ := f2 a
    exact ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1⟩

theorem inv_run {l1 : ChainId} {pre s₀ : PoolSys} {L : List PoolCall} (hpre : PreUpgrade pre)
    (hinit : initializeUpgrade pre = some s₀) (h : PoolRun l1 s₀ L t) :
    PoolFlagInv t ∧ PoolIdentity t ∧ PoolCovered t :=
  PoolRun.preserves (fun s => PoolFlagInv s ∧ PoolIdentity s ∧ PoolCovered s)
    (fun _ _ _ hs hc => ledgerInv_step hs hc) h (postUpgrade_inv hpre hinit)

/-! ## The properties -/

theorem PostUpgradeEstablishesInvariants : Properties.PostUpgradeEstablishesInvariants :=
  fun _ _ hpre hinit => postUpgrade_inv hpre hinit

theorem CallPreservesInvariants : Properties.CallPreservesInvariants :=
  fun _ _ _ _ hf hi hc h => ledgerInv_step ⟨hf, hi, hc⟩ h

theorem FlagsAfterUpgrade : Properties.FlagsAfterUpgrade := by
  intro l1 pre s₀ t L hpre hinit hrun
  have ht := (inv_run hpre hinit hrun).1
  exact ⟨ht.interopNotPending, ht.inPoolInterop, ht.poolUnregistered, ht.pending_pool,
    ht.interop_pool, ht.poolNoBackfill⟩

theorem FlagsMonotone : Properties.FlagsMonotone := by
  intro l1 s t L h
  obtain ⟨i, p, -, d⟩ := flags_run h
  exact ⟨i, p, d⟩

theorem InitializeUpgradeAtMostOnce : Properties.InitializeUpgradeAtMostOnce := by
  intro l1 s t L h
  have := init_count_run h
  refine ⟨?_, fun hv => ?_⟩
  · split_ifs at this <;> omega
  · rw [ite_eq_right (by omega)] at this
    omega

theorem LaterChainNeverPending : Properties.LaterChainNeverPending := by
  intro l1 pre s₀ t L c hpre hinit hrun hp
  have hv : 2 ≤ s₀.initVersion := (postUpgrade_inv hpre hinit).1.upgraded
  have h0 := (flags_run hrun).2.2.2 hv c hp
  obtain ⟨-, rfl⟩ := initializeUpgrade_some hinit
  change (pre.pending c || pre.registered c) = true at h0
  rw [Bool.or_eq_true] at h0
  rcases h0 with h0 | h0
  · exact hpre.pendingRegistered c h0
  · exact h0

theorem UnnamedUnregisteredChainUntouched : Properties.UnnamedUnregisteredChainUntouched :=
  fun _ _ _ _ _ h hcp hreg hname => unnamed_run h hcp hreg hname

theorem RegisteredLaterStartsAtUpgradeSlots : Properties.RegisteredLaterStartsAtUpgradeSlots := by
  intro l1 pre s₀ m t L c hpre hinit hreg hrun hname hregc
  obtain ⟨-, hcap, -, -, ht⟩ := registerChain_some hregc
  have hcp : c ≠ interopPoolChainId := by
    intro he
    have := pool_above_cap
    rw [← he] at this
    omega
  obtain ⟨-, rfl⟩ := initializeUpgrade_some hinit
  have hpend : pre.pending c = false := by
    cases hp : pre.pending c
    · rfl
    · rw [hpre.pendingRegistered c hp] at hreg
      cases hreg
  obtain ⟨-, p1, i1, f1⟩ := unnamed_run hrun hcp hreg hname
  rw [ht]
  refine ⟨setAt_self _ _ _, ?_, ?_, fun a => ?_⟩
  · show m.pending c = false
    rw [p1]
    show (pre.pending c || pre.registered c) = false
    rw [hpend, hreg]
    rfl
  · show m.interop c = false
    rw [i1]
    exact hpre.noInterop c
  · obtain ⟨a1, b1, c1, d1⟩ := f1 a
    exact ⟨a1.trans (hpre.noneInPool c a), b1, c1, d1⟩

theorem EnabledChainTotalsFrozen : Properties.EnabledChainTotalsFrozen := by
  intro l1 pre s₀ s t L₁ L₂ c a hpre hinit h₁ hc h₂
  exact frozen_run h₂ (inv_run hpre hinit h₁).1 hc a

theorem PoolDepositIdentity : Properties.PoolDepositIdentity := by
  intro l1 pre s₀ t L hpre hinit hrun a
  exact (inv_run hpre hinit hrun).2.1 a

theorem PoolWithdrawalsCovered : Properties.PoolWithdrawalsCovered := by
  intro l1 pre s₀ t L hpre hinit hrun a
  obtain ⟨-, hid, hcov⟩ := inv_run hpre hinit hrun
  have h1 := hcov a
  rw [hid a] at h1
  exact h1

theorem DirectToPoolIsPoolKeyedDeposits : Properties.DirectToPoolIsPoolKeyedDeposits :=
  fun _ _ _ _ a h => ghost_step h a

theorem PoolKeyedMeansEnabledDestination : Properties.PoolKeyedMeansEnabledDestination := by
  intro s c o hc
  unfold trackedBalance
  by_cases hi : s.interop c = true
  · rw [ite_eq_left hi]
    constructor
    · intro h
      refine ⟨hi, ?_⟩
      have h1 := congrArg Prod.fst h
      simpa using h1
    · rintro ⟨-, ho⟩
      rw [ho]
      rfl
  · rw [ite_eq_right hi]
    constructor
    · intro h
      exact absurd (congrArg Prod.snd h) hc
    · rintro ⟨h1, -⟩
      exact absurd h1 hi

theorem MoveBackfillCommute : Properties.MoveBackfillCommute := move_backfill_commute

theorem MoveAtMostOncePerPair : Properties.MoveAtMostOncePerPair := by
  intro l1 s t L c a h
  have := move_count_run h c a
  refine ⟨?_, fun hin => ?_⟩
  · split_ifs at this <;> omega
  · rw [ite_eq_left hin] at this
    omega

theorem NonzeroBackfillNeverRewritten : Properties.NonzeroBackfillNeverRewritten :=
  fun _ _ _ _ _ _ h hb => backfill_nonzero_run h hb

theorem TotalsOnlyGrow : Properties.TotalsOnlyGrow :=
  fun _ _ _ _ h k a => totals_grow_run h k a


/-! ## Witness data

L1 is chain `1`. Chain `10` is registered before the upgrade, chain `20` after it. Asset `7` is
L1-native (origin `1`); asset `8` comes from chain `30`. -/

/-- The `PreUpgrade` state of the witnesses: chain `10` registered, every v35 slot zero,
version 1. -/
def poolWPre : PoolSys where
  bridgedOut := fun _ => 0
  deposited := fun _ _ => 0
  withdrawn := fun _ _ => 0
  backfill := fun _ _ => 0
  inPool := fun _ _ => false
  pending := fun _ => false
  initVersion := 1
  interop := fun _ => false
  registered := fun c => decide (c = 10)
  directToPool := fun _ => 0

theorem poolWPre_preUpgrade : PreUpgrade poolWPre where
  version := by decide
  noInterop := fun _ => rfl
  noneInPool := fun _ _ => rfl
  pendingRegistered := fun _ h => by cases h
  poolUnregistered := by decide
  poolDepositedZero := fun _ => rfl
  poolWithdrawnZero := fun _ => rfl
  poolBackfillZero := fun _ => rfl
  noDirect := fun _ => rfl

/-- Up to enabling chain `10`: deposits and uncapped withdrawals while it is pending, a backfill,
`markBackfilled`, `enableInterop`. -/
def poolWRunA : List PoolCall :=
  [.toChain 10 7 100 1, .fromChain 10 7 30 1, .toChain 10 8 20 30, .fromChain 10 8 25 30,
   .setBackfill 10 7 50, .markBackfilled 10, .enableInterop 10]

/-- A deposit to the enabled chain, both moves, and a late backfill in deficit. -/
def poolWRunB₁ : List PoolCall :=
  [.toChain 10 7 40 1, .move 10 7, .move 10 8, .setBackfill 10 8 9]

/-- Chain `20` registered and enabled, a deposit to it, and withdrawals by both enabled chains. -/
def poolWRunB₂ : List PoolCall :=
  [.register 20, .enableInterop 20, .toChain 20 7 5 1, .fromChain 20 7 60 1, .fromChain 10 7 10 1]

theorem poolW_init_isSome : (initializeUpgrade poolWPre).isSome = true := by decide

/-- The post-upgrade state: chain `10` pending. -/
def poolWS₀ : PoolSys := (initializeUpgrade poolWPre).get poolW_init_isSome

theorem poolW_init : initializeUpgrade poolWPre = some poolWS₀ := (Option.some_get _).symm

theorem poolW_A_isSome : (runPoolCalls 1 poolWRunA poolWS₀).isSome = true := by decide

/-- After `poolWRunA`: chain `10` enabled. -/
def poolWS : PoolSys := (runPoolCalls 1 poolWRunA poolWS₀).get poolW_A_isSome

theorem poolW_runA : PoolRun 1 poolWS₀ poolWRunA poolWS :=
  poolRun_of_runPoolCalls (Option.some_get _).symm

theorem poolW_B₁_isSome : (runPoolCalls 1 poolWRunB₁ poolWS).isSome = true := by decide

/-- After `poolWRunB₁`: both pairs of chain `10` moved, asset `8` backfilled late. -/
def poolWM : PoolSys := (runPoolCalls 1 poolWRunB₁ poolWS).get poolW_B₁_isSome

theorem poolW_runB₁ : PoolRun 1 poolWS poolWRunB₁ poolWM :=
  poolRun_of_runPoolCalls (Option.some_get _).symm

theorem poolW_B₂_isSome : (runPoolCalls 1 poolWRunB₂ poolWM).isSome = true := by decide

/-- The end state. -/
def poolWT : PoolSys := (runPoolCalls 1 poolWRunB₂ poolWM).get poolW_B₂_isSome

theorem poolW_runB₂ : PoolRun 1 poolWM poolWRunB₂ poolWT :=
  poolRun_of_runPoolCalls (Option.some_get _).symm

theorem poolW_dep_isSome : (poolCall 1 (.toChain 10 7 40 1) poolWS).isSome = true := by decide

/-- After the first call of `poolWRunB₁`: 40 of asset `7` deposited to the enabled chain `10`,
credited to the pool. -/
def poolWD : PoolSys := (poolCall 1 (.toChain 10 7 40 1) poolWS).get poolW_dep_isSome

theorem poolW_dep : poolCall 1 (.toChain 10 7 40 1) poolWS = some poolWD :=
  (Option.some_get _).symm

theorem poolW_move_isSome : (poolCall 1 (.move 10 7) poolWD).isSome = true := by decide

/-- After the move of `(10, 7)`. -/
def poolWE : PoolSys := (poolCall 1 (.move 10 7) poolWD).get poolW_move_isSome

theorem poolW_move : poolCall 1 (.move 10 7) poolWD = some poolWE := (Option.some_get _).symm

theorem poolW_reg_isSome : (poolCall 1 (.register 20) poolWM).isSome = true := by decide

/-- Chain `20` registered after `poolWRunA ++ poolWRunB₁`. -/
def poolWR : PoolSys := (poolCall 1 (.register 20) poolWM).get poolW_reg_isSome

theorem poolW_reg : poolCall 1 (.register 20) poolWM = some poolWR := (Option.some_get _).symm

theorem poolW_commute_isSome : ((moveChainBalanceToInteropPool poolWS 10 8).bind
    (fun m => setChainBalanceBackfill m 10 8 9)).isSome = true := by decide

/-- Move then backfill of `(10, 8)` from `poolWS`. -/
def poolWU : PoolSys := ((moveChainBalanceToInteropPool poolWS 10 8).bind
    (fun m => setChainBalanceBackfill m 10 8 9)).get poolW_commute_isSome

theorem poolW_commute : (moveChainBalanceToInteropPool poolWS 10 8).bind
    (fun m => setChainBalanceBackfill m 10 8 9) = some poolWU := (Option.some_get _).symm

theorem poolW_preset_isSome :
    (runPoolCalls 1 [.setBackfill 20 7 9, .register 20] poolWS₀).isSome = true := by decide

/-- A backfill for chain `20`, then its registration, from the post-upgrade state. -/
def poolWV : PoolSys := (runPoolCalls 1 [.setBackfill 20 7 9, .register 20] poolWS₀).get
  poolW_preset_isSome

theorem poolW_preset : PoolRun 1 poolWS₀ [.setBackfill 20 7 9, .register 20] poolWV :=
  poolRun_of_runPoolCalls (Option.some_get _).symm

/-! ## Witnesses and countermodels -/

theorem PostUpgradeRunWitness : Properties.PostUpgradeRunWitness := by
  have hB : PoolRun 1 poolWS (poolWRunB₁ ++ poolWRunB₂) poolWT := poolW_runB₁.append poolW_runB₂
  refine ⟨1, poolWPre, poolWS₀, poolWS, poolWT, poolWRunA, poolWRunB₁ ++ poolWRunB₂,
    poolWPre_preUpgrade, poolW_init, poolW_runA, hB, PoolRun.cons poolW_init (poolW_runA.append hB),
    ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, poolWD, poolW_dep, by decide⟩

theorem PoolKeyedWitness : Properties.PoolKeyedWitness :=
  ⟨poolWT, 10, 1, 20, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem LaterChainWitness : Properties.LaterChainWitness :=
  ⟨1, poolWPre, poolWS₀, poolWM, poolWR, poolWRunA ++ poolWRunB₁, poolWPre_preUpgrade,
    poolW_init, by decide, poolW_runA.append poolW_runB₁, by decide, by decide, by decide,
    poolW_reg, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem InvariantStepWitness : Properties.InvariantStepWitness := by
  have hrun : PoolRun 1 poolWS₀ (poolWRunA ++ [.toChain 10 7 40 1]) poolWD :=
    poolW_runA.append (PoolRun.cons poolW_dep (PoolRun.nil _))
  obtain ⟨hf, hi, hc⟩ := inv_run poolWPre_preUpgrade poolW_init hrun
  exact ⟨1, poolWD, poolWE, hf, hi, hc, poolW_move, by decide, by decide, by decide, by decide⟩

theorem MoveBackfillCommuteWitness : Properties.MoveBackfillCommuteWitness := by
  refine ⟨poolWS, poolWU, by decide, by decide, by decide, by decide, poolW_commute, ?_,
    by decide, by decide, by decide⟩
  rw [← move_backfill_commute]
  exact poolW_commute

theorem BackfillAcceptsUnregisteredChain : Properties.BackfillAcceptsUnregisteredChain :=
  ⟨1, poolWPre, poolWS₀, poolWV, 20, 7, 9, poolWPre_preUpgrade, poolW_init, by decide, rfl,
    poolW_preset, by decide, by decide, by decide, by decide⟩

theorem EnableBeforeUpgradeBlocksMove : Properties.EnableBeforeUpgradeBlocksMove := by
  let m : PoolSys := { poolWPre with interop := setAt poolWPre.interop 10 true }
  let t : PoolSys :=
    { m with initVersion := 2, pending := fun c => m.pending c || m.registered c }
  let u : PoolSys := { t with pending := setAt t.pending 10 false }
  have hm : enableInterop poolWPre 10 = some m := by
    unfold enableInterop
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
  have ht : initializeUpgrade m = some t := by
    unfold initializeUpgrade
    rw [ite_eq_left (show m.initVersion < 2 by decide)]
  have hu : markBackfilled t 10 = some u := by
    unfold markBackfilled
    rw [ite_eq_left (show t.pending 10 = true by decide)]
  refine ⟨1, poolWPre, t, 10, poolWPre_preUpgrade,
    PoolRun.cons hm (PoolRun.cons ht (PoolRun.nil _)), by decide, by decide, fun a => ?_,
    u, hu, fun a => ?_⟩
  · show moveChainBalanceToInteropPool t 10 a = none
    unfold moveChainBalanceToInteropPool
    rw [ite_eq_right (show ¬ t.interop 10 = false by decide),
      ite_eq_left (show t.pending 10 = true by decide)]
  · exact ⟨_, moveChainBalanceToInteropPool_eq (s := u) (by decide) (by decide) rfl
      (show 0 + 0 < UInt256.size by decide)
      (show 0 + (0 + 0 - 0) < UInt256.size by decide)⟩

end Contracts.L1NativeTokenVault.InteropPool
