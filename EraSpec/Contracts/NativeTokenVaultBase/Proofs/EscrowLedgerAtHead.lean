import EraSpec.Contracts.NativeTokenVaultBase.Properties.EscrowLedgerAtHead
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.RegistryAndEscrow

/-!
# Proofs: the escrow ledger at head, with `populateBridgedOut`

Solvency is one invariant, `LedgerBackedAtHead`.  A pin step keeps any fixed reserve backed,
because registrations do not touch the ledger and flows move the ledger and the escrow
together (`stepOp_keeps_reserve`).  A population moves an asset's legacy amount from the
reserve into the ledger.  No registry fact is used, so no hash premise either.

The run-local headline carries the registry invariant and the head audit along a logged run,
with the id hash bounded to the start's recorded pairs plus the run's own.  Registry steps
reuse the pin's `stepIn_preserves_valid_on`.  The head audit is the pin's audit with the
populated legacy amount on the outflow side, which pin steps leave fixed.  Its proof follows
`stepIn_preserves_audited` with that extra term (`stepIn_preserves_shiftedAudit`).
-/

namespace Contracts.NativeTokenVault

/-! ## Reading the head state -/

section Pop
variable (legacy : LegacyAmounts) (W : WorldAtHead) (a : AssetId)

@[simp] lemma populateAtHead_escrowed :
    (populateAtHead legacy W a).world.vault.escrowed = W.world.vault.escrowed := rfl
@[simp] lemma populateAtHead_audit : (populateAtHead legacy W a).world.audit = W.world.audit := rfl
@[simp] lemma populateAtHead_originChain :
    (populateAtHead legacy W a).world.vault.originChain = W.world.vault.originChain := rfl
@[simp] lemma populateAtHead_token :
    (populateAtHead legacy W a).world.vault.token = W.world.vault.token := rfl
@[simp] lemma populateAtHead_assetOf :
    (populateAtHead legacy W a).world.vault.assetOf = W.world.vault.assetOf := rfl
@[simp] lemma populateAtHead_originToken :
    (populateAtHead legacy W a).world.vault.originToken = W.world.vault.originToken := rfl
lemma populateAtHead_bridgedOut :
    (populateAtHead legacy W a).world.vault.bridgedOut
      = upd W.world.vault.bridgedOut a (W.world.vault.bridgedOut a + legacy a) := rfl
lemma populateAtHead_populated :
    (populateAtHead legacy W a).populated = upd W.populated a true := rfl

end Pop

lemma pendingLegacy_false {legacy : LegacyAmounts} {W : WorldAtHead} {a : AssetId}
    (h : W.populated a = false) : pendingLegacy legacy W a = legacy a := by
  simp [pendingLegacy, h]

lemma pendingLegacy_true {legacy : LegacyAmounts} {W : WorldAtHead} {a : AssetId}
    (h : W.populated a = true) : pendingLegacy legacy W a = 0 := by
  simp [pendingLegacy, h]

lemma populatedLegacy_false {legacy : LegacyAmounts} {W : WorldAtHead} {a : AssetId}
    (h : W.populated a = false) : populatedLegacy legacy W a = 0 := by
  simp [populatedLegacy, h]

lemma populatedLegacy_true {legacy : LegacyAmounts} {W : WorldAtHead} {a : AssetId}
    (h : W.populated a = true) : populatedLegacy legacy W a = legacy a := by
  simp [populatedLegacy, h]

/-- `Native` implies `Registered` on a valid vault of a nonzero chain. -/
lemma registered_of_native {e : NtvAssetId} {thisChain : Chain} (hc0 : thisChain ≠ 0)
    {V : Vault} (hV : Valid e thisChain V) {a : AssetId} (hnat : Native thisChain V a) :
    Registered V a :=
  (hV.originIff a).mpr (by rw [hnat]; exact hc0)

/-- `Valid` survives a change of the ledger alone that keeps it native-only and solvent. -/
lemma valid_with_bridgedOut {e : NtvAssetId} {thisChain : Chain} {V : Vault}
    (hV : Valid e thisChain V) (f : AssetId → ℕ)
    (hledg : ∀ a, ¬ Native thisChain V a → f a = 0) (hsolv : ∀ a, f a ≤ V.escrowed a) :
    Valid e thisChain { V with bridgedOut := f } :=
  ⟨hV.inverse, hV.tokenOfAsset, hV.originIff, hV.zeroUnregistered, hV.zeroTokenFree,
    hV.idShape, hV.nativeToken, hledg, hsolv⟩

/-- `Valid` survives a change of the escrow alone that keeps the ledger below it. -/
lemma valid_with_escrowed {e : NtvAssetId} {thisChain : Chain} {V : Vault}
    (hV : Valid e thisChain V) (g : AssetId → ℕ) (hsolv : ∀ a, V.bridgedOut a ≤ g a) :
    Valid e thisChain { V with escrowed := g } :=
  ⟨hV.inverse, hV.tokenOfAsset, hV.originIff, hV.zeroUnregistered, hV.zeroTokenFree,
    hV.idShape, hV.nativeToken, hV.ledgerNative, hsolv⟩

/-! ## Solvency, with no hash premise -/

/-- **A PIN STEP KEEPS ANY FIXED RESERVE BACKED.** -/
theorem stepOp_keeps_reserve {e : NtvAssetId} {thisChain : Chain} {o : Op} {W X : World}
    (hs : StepOp e thisChain o W X) (p : AssetId → ℕ)
    (hB : ∀ a, W.vault.bridgedOut a + p a ≤ W.vault.escrowed a) :
    ∀ a, X.vault.bridgedOut a + p a ≤ X.vault.escrowed a := by
  cases hs with
  | registerNative _ => exact hB
  | registerBridged _ => exact hB
  | @bridgeOut _ c a amt _ =>
    intro a'
    by_cases hnat : Native thisChain W.vault a
    · rw [bridgeOut_bridgedOut_native thisChain W c a amt hnat,
        bridgeOut_escrowed_native thisChain W c a amt hnat]
      by_cases h : a' = a
      · subst h
        rw [upd_same, upd_same]
        have := hB a'
        omega
      · rw [upd_ne _ _ h, upd_ne _ _ h]
        exact hB a'
    · rw [bridgeOut_vault_foreign thisChain W c a amt hnat]
      exact hB a'
  | @bridgeIn _ c a amt hg =>
    intro a'
    by_cases hnat : Native thisChain W.vault a
    · rw [bridgeIn_bridgedOut_native thisChain W c a amt hnat,
        bridgeIn_escrowed_native thisChain W c a amt hnat]
      by_cases h : a' = a
      · subst h
        rw [upd_same, upd_same]
        have h1 := hB a'
        have h2 := hg.sufficient hnat
        omega
      · rw [upd_ne _ _ h, upd_ne _ _ h]
        exact hB a'
    · rw [bridgeIn_vault_foreign thisChain W c a amt hnat]
      exact hB a'
  | @donate _ a amt =>
    intro a'
    rw [donate_bridgedOut, donate_escrowed]
    by_cases h : a' = a
    · subst h
      rw [upd_same]
      have := hB a'
      omega
    · rw [upd_ne _ _ h]
      exact hB a'

theorem stepOpAtHead_preserves_backed {e : NtvAssetId} {thisChain : Chain}
    {legacy : LegacyAmounts} {o : OpAtHead} {W X : WorldAtHead}
    (hs : StepOpAtHead e thisChain legacy o W X) (hB : LedgerBackedAtHead legacy W) :
    LedgerBackedAtHead legacy X := by
  cases hs with
  | pin hp => exact stepOp_keeps_reserve hp (pendingLegacy legacy W) hB
  | populateSkip _ => exact hB
  | @populate _ a hfalse _ =>
    intro a'
    show (populateAtHead legacy W a).world.vault.bridgedOut a'
        + pendingLegacy legacy (populateAtHead legacy W a) a'
      ≤ (populateAtHead legacy W a).world.vault.escrowed a'
    rw [populateAtHead_bridgedOut, populateAtHead_escrowed]
    by_cases h : a' = a
    · subst h
      have hp : (populateAtHead legacy W a').populated a' = true := by
        rw [populateAtHead_populated, upd_same]
      rw [upd_same, pendingLegacy_true hp]
      have := hB a'
      rw [pendingLegacy_false hfalse] at this
      omega
    · have hp : pendingLegacy legacy (populateAtHead legacy W a) a' = pendingLegacy legacy W a' := by
        simp only [pendingLegacy, populateAtHead_populated, upd_ne _ _ h]
      rw [upd_ne _ _ h, hp]
      exact hB a'

theorem reachLogAtHead_backed {e : NtvAssetId} {thisChain : Chain} {legacy : LegacyAmounts}
    {W₀ W : WorldAtHead} {log : List OpAtHead} (hr : ReachLogAtHead e thisChain legacy W₀ W log)
    (h0 : LedgerBackedAtHead legacy W₀) : LedgerBackedAtHead legacy W := by
  induction hr with
  | refl => exact h0
  | tail _ hs ih => exact stepOpAtHead_preserves_backed hs ih

lemma solvent_of_backed {legacy : LegacyAmounts} {W : WorldAtHead}
    (hB : LedgerBackedAtHead legacy W) (a : AssetId) :
    W.world.vault.bridgedOut a ≤ W.world.vault.escrowed a :=
  le_trans (Nat.le_add_right _ _) (hB a)

theorem upgradeStart_backed {legacy : LegacyAmounts} {W : WorldAtHead}
    (h : UpgradeStartAtHead legacy W) : LedgerBackedAtHead legacy W := by
  intro a
  rw [h.ledgerZero a, pendingLegacy_false (h.unpopulated a), Nat.zero_add]
  exact h.legacyBacked a

/-! ## The pin's runs embed -/

theorem pin_stepOp_atHead {e : NtvAssetId} {thisChain : Chain} {legacy : LegacyAmounts}
    {o : Op} {W X : World} (hs : StepOp e thisChain o W X) :
    StepOpAtHead e thisChain legacy (.pin o) (WorldAtHead.ofWorld W) (WorldAtHead.ofWorld X) :=
  StepOpAtHead.pin (W := WorldAtHead.ofWorld W) hs

theorem pin_reachLog_atHead {e : NtvAssetId} {thisChain : Chain} {legacy : LegacyAmounts}
    {W X : World} {log : List Op} (hr : ReachLog e thisChain W X log) :
    ReachLogAtHead e thisChain legacy (WorldAtHead.ofWorld W) (WorldAtHead.ofWorld X)
      (log.map OpAtHead.pin) := by
  induction hr with
  | refl => exact ReachLogAtHead.refl
  | tail _ hs ih =>
    rw [List.map_append, List.map_singleton]
    exact ReachLogAtHead.tail ih (pin_stepOp_atHead hs)

/-! ## Population -/

theorem populate_effect {e : NtvAssetId} {thisChain : Chain} {legacy : LegacyAmounts}
    {W X : WorldAtHead} {a : AssetId} (hs : StepOpAtHead e thisChain legacy (.populate a) W X) :
    (W.populated a = true → X = W)
      ∧ (W.populated a = false →
          X.world.vault.bridgedOut a = W.world.vault.bridgedOut a + legacy a
            ∧ X.populated a = true)
      ∧ (∀ a', a' ≠ a →
          X.world.vault.bridgedOut a' = W.world.vault.bridgedOut a'
            ∧ X.populated a' = W.populated a')
      ∧ X.world.vault.escrowed = W.world.vault.escrowed
      ∧ X.world.audit = W.world.audit := by
  cases hs with
  | populateSkip htrue =>
    refine ⟨fun _ => rfl, fun hf => ?_, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
    rw [htrue] at hf
    exact absurd hf (by decide)
  | populate hfalse _ =>
    refine ⟨fun ht => ?_, fun _ => ⟨?_, ?_⟩, fun a' h => ⟨?_, ?_⟩, rfl, rfl⟩
    · rw [hfalse] at ht
      exact absurd ht (by decide)
    · rw [populateAtHead_bridgedOut, upd_same]
    · rw [populateAtHead_populated, upd_same]
    · rw [populateAtHead_bridgedOut, upd_ne _ _ h]
    · rw [populateAtHead_populated, upd_ne _ _ h]

theorem stepOpAtHead_populated_mono {e : NtvAssetId} {thisChain : Chain}
    {legacy : LegacyAmounts} {o : OpAtHead} {W X : WorldAtHead}
    (hs : StepOpAtHead e thisChain legacy o W X) (a : AssetId) (h : W.populated a = true) :
    X.populated a = true := by
  cases hs with
  | pin _ => exact h
  | populateSkip _ => exact h
  | @populate _ b _ _ =>
    rw [populateAtHead_populated]
    by_cases hab : a = b
    · subst hab
      rw [upd_same]
    · rw [upd_ne _ _ hab]
      exact h

theorem reachLogAtHead_populated_mono {e : NtvAssetId} {thisChain : Chain}
    {legacy : LegacyAmounts} {W X : WorldAtHead} {log : List OpAtHead}
    (hr : ReachLogAtHead e thisChain legacy W X log) (a : AssetId) (h : W.populated a = true) :
    X.populated a = true := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact stepOpAtHead_populated_mono hs a ih

/-! ## The flow audit -/

/-- **THE PIN'S AUDIT STEP, WITH A FIXED EXTRA OUTFLOW TERM.**  As `stepIn_preserves_audited`,
with `P a` added on the outflow side and a side condition `Q` on unregistered assets that
forces `P` to vanish there.  Pin steps change neither `P` nor `Q`. -/
theorem stepIn_preserves_shiftedAudit {e : NtvAssetId} {S : Set (Chain × Address)}
    (he : IdAssumptionsOn e S) {thisChain : Chain} (hc0 : thisChain ≠ 0) {W X : World}
    (hs : StepIn e thisChain S W X) (hV : Valid e thisChain W.vault) (hP : PairsIn S W.vault)
    (P : AssetId → ℕ) (Q : AssetId → Prop) (hPQ : ∀ a, Q a → P a = 0)
    (hnet : ∀ a, Native thisChain W.vault a →
      W.vault.bridgedOut a + W.audit.totalIn a = W.audit.totalOut a + P a)
    (hq : ∀ a, ¬ Registered W.vault a → W.audit.totalIn a = 0 ∧ W.audit.totalOut a = 0 ∧ Q a) :
    (∀ a, Native thisChain X.vault a →
      X.vault.bridgedOut a + X.audit.totalIn a = X.audit.totalOut a + P a)
    ∧ (∀ a, ¬ Registered X.vault a → X.audit.totalIn a = 0 ∧ X.audit.totalOut a = 0 ∧ Q a) := by
  cases hs with
  | @registerNative t hmem hg =>
    have hfresh : ¬ Registered W.vault (e thisChain t) :=
      registerNative_id_fresh_on he hV hP hmem hg
    refine ⟨?_, ?_⟩
    · intro a' hnat
      by_cases h : a' = e thisChain t
      · subst h
        obtain ⟨hin, hout, hQ⟩ := hq (e thisChain t) hfresh
        have hchain0 : W.vault.originChain (e thisChain t) = 0 := by
          by_contra hne
          exact hfresh ((hV.originIff (e thisChain t)).mpr hne)
        have hbo : W.vault.bridgedOut (e thisChain t) = 0 := by
          refine hV.ledgerNative (e thisChain t) ?_
          simp only [Native, hchain0]
          exact fun hx => hc0 hx.symm
        show (setNewTokenStorage W.vault (e thisChain t) t t thisChain).bridgedOut (e thisChain t)
            + W.audit.totalIn (e thisChain t) = W.audit.totalOut (e thisChain t) + P (e thisChain t)
        rw [sn_bridgedOut, hbo, hin, hout, hPQ _ hQ]
      · exact hnet a' ((sn_native_of_ne W.vault _ t t thisChain thisChain h).mp hnat)
    · intro a' hnn
      refine hq a' ?_
      intro hreg
      refine hnn ?_
      by_cases h : a' = e thisChain t
      · subst h
        exact (sn_registered_self W.vault (e thisChain t) t t thisChain).mpr hg.nonzero
      · exact (sn_registered_of_ne W.vault _ t t thisChain h).mpr hreg
  | @registerBridged a t ot origin _ hg =>
    refine ⟨?_, ?_⟩
    · intro a' hnat
      by_cases h : a' = a
      · subst h
        exact absurd ((sn_native_self W.vault a' t ot origin thisChain).mp hnat) hg.notNative
      · exact hnet a' ((sn_native_of_ne W.vault a t ot origin thisChain h).mp hnat)
    · intro a' hnn
      refine hq a' ?_
      intro hreg
      refine hnn ?_
      by_cases h : a' = a
      · subst h
        exact (sn_registered_self W.vault a' t ot origin).mpr hg.tokenNonzero
      · exact (sn_registered_of_ne W.vault a t ot origin h).mpr hreg
  | @bridgeOut c a amt hg =>
    refine ⟨?_, ?_⟩
    · intro a' hnat
      have hnatW : Native thisChain W.vault a' := by simpa using hnat
      by_cases hnata : Native thisChain W.vault a
      · by_cases h : a' = a
        · subst h
          have hn := hnet a' hnatW
          rw [bridgeOut_bridgedOut_native _ _ _ _ _ hnata, bridgeOut_totalIn,
            bridgeOut_totalOut, upd_same, upd_same]
          omega
        · rw [bridgeOut_bridgedOut_native _ _ _ _ _ hnata, bridgeOut_totalIn,
            bridgeOut_totalOut, upd_ne _ _ h, upd_ne _ _ h]
          exact hnet a' hnatW
      · have h : a' ≠ a := by
          intro h
          subst h
          exact hnata hnatW
        rw [bridgeOut_vault_foreign _ _ _ _ _ hnata, bridgeOut_totalIn, bridgeOut_totalOut,
          upd_ne _ _ h]
        exact hnet a' hnatW
    · intro a' hnn
      have hnnW : ¬ Registered W.vault a' := by simpa using hnn
      have h : a' ≠ a := by
        intro h
        rw [h] at hnnW
        exact hnnW hg.registered
      obtain ⟨hin, hout, hQ⟩ := hq a' hnnW
      exact ⟨by rw [bridgeOut_totalIn]; exact hin,
        by rw [bridgeOut_totalOut, upd_ne _ _ h]; exact hout, hQ⟩
  | @bridgeIn c a amt hg =>
    refine ⟨?_, ?_⟩
    · intro a' hnat
      have hnatW : Native thisChain W.vault a' := by simpa using hnat
      by_cases hnata : Native thisChain W.vault a
      · by_cases h : a' = a
        · subst h
          have hn := hnet a' hnatW
          have hsuf := hg.sufficient hnata
          rw [bridgeIn_bridgedOut_native _ _ _ _ _ hnata, bridgeIn_totalIn,
            bridgeIn_totalOut, upd_same, upd_same]
          omega
        · rw [bridgeIn_bridgedOut_native _ _ _ _ _ hnata, bridgeIn_totalIn,
            bridgeIn_totalOut, upd_ne _ _ h, upd_ne _ _ h]
          exact hnet a' hnatW
      · have h : a' ≠ a := by
          intro h
          subst h
          exact hnata hnatW
        rw [bridgeIn_vault_foreign _ _ _ _ _ hnata, bridgeIn_totalOut, bridgeIn_totalIn,
          upd_ne _ _ h]
        exact hnet a' hnatW
    · intro a' hnn
      have hnnW : ¬ Registered W.vault a' := by simpa using hnn
      have h : a' ≠ a := by
        intro h
        rw [h] at hnnW
        exact hnnW hg.registered
      obtain ⟨hin, hout, hQ⟩ := hq a' hnnW
      exact ⟨by rw [bridgeIn_totalIn, upd_ne _ _ h]; exact hin,
        by rw [bridgeIn_totalOut]; exact hout, hQ⟩
  | @donate a amt =>
    refine ⟨?_, ?_⟩
    · intro a' hnat
      rw [donate_audit, donate_bridgedOut]
      exact hnet a' (by simpa using hnat)
    · intro a' hnn
      rw [donate_audit]
      exact hq a' (by simpa using hnn)

/-- Everything a logged head run carries, for a fixed pair set `S`. -/
private structure InvAtHead (e : NtvAssetId) (thisChain : Chain) (legacy : LegacyAmounts)
    (S : Set (Chain × Address)) (W : WorldAtHead) : Prop where
  valid : Valid e thisChain W.world.vault
  pairs : PairsIn S W.world.vault
  backed : LedgerBackedAtHead legacy W
  audited : AuditedAtHead legacy thisChain W

private theorem stepOpAtHead_preserves_inv {e : NtvAssetId} {S : Set (Chain × Address)}
    (he : IdAssumptionsOn e S) {thisChain : Chain} (hc0 : thisChain ≠ 0) {legacy : LegacyAmounts}
    {o : OpAtHead} {W X : WorldAtHead} (hs : StepOpAtHead e thisChain legacy o W X)
    (hS : ∀ p, o.pair thisChain = some p → p ∈ S) (hI : InvAtHead e thisChain legacy S W) :
    InvAtHead e thisChain legacy S X := by
  have hB' := stepOpAtHead_preserves_backed hs hI.backed
  cases hs with
  | @pin o _ Xw hp =>
    have hin : StepIn e thisChain S W.world Xw := stepOp_stepIn hp hS
    obtain ⟨hV', hP'⟩ := stepIn_preserves_valid_on he hc0 hin hI.valid hI.pairs
    obtain ⟨hnet, hq⟩ := stepIn_preserves_shiftedAudit he hc0 hin hI.valid hI.pairs
      (populatedLegacy legacy W) (fun a => W.populated a = false)
      (fun _ h => populatedLegacy_false h) hI.audited.netFlow hI.audited.unregisteredQuiet
    exact ⟨hV', hP', hB', ⟨hnet, hq⟩⟩
  | populateSkip _ => exact hI
  | @populate _ a hfalse hnat =>
    have hreg : Registered W.world.vault a := registered_of_native hc0 hI.valid hnat
    refine ⟨?_, hI.pairs, hB', ?_, ?_⟩
    · refine valid_with_bridgedOut hI.valid _ ?_ (solvent_of_backed hB')
      intro a' hnn
      have h : a' ≠ a := by
        intro h
        subst h
        exact hnn hnat
      rw [upd_ne _ _ h]
      exact hI.valid.ledgerNative a' hnn
    · intro a' hnat'
      have hnatW : Native thisChain W.world.vault a' := hnat'
      show (populateAtHead legacy W a).world.vault.bridgedOut a' + W.world.audit.totalIn a'
        = W.world.audit.totalOut a' + populatedLegacy legacy (populateAtHead legacy W a) a'
      have hn := hI.audited.netFlow a' hnatW
      rw [populateAtHead_bridgedOut]
      by_cases h : a' = a
      · subst h
        have hp : (populateAtHead legacy W a').populated a' = true := by
          rw [populateAtHead_populated, upd_same]
        rw [upd_same, populatedLegacy_true hp]
        rw [populatedLegacy_false hfalse] at hn
        omega
      · have hp : populatedLegacy legacy (populateAtHead legacy W a) a'
            = populatedLegacy legacy W a' := by
          simp only [populatedLegacy, populateAtHead_populated, upd_ne _ _ h]
        rw [upd_ne _ _ h, hp]
        exact hn
    · intro a' hnn
      have hnnW : ¬ Registered W.world.vault a' := hnn
      have h : a' ≠ a := by
        intro h
        subst h
        exact hnnW hreg
      obtain ⟨hin, hout, hpop⟩ := hI.audited.unregisteredQuiet a' hnnW
      refine ⟨hin, hout, ?_⟩
      show (populateAtHead legacy W a).populated a' = false
      rw [populateAtHead_populated, upd_ne _ _ h]
      exact hpop

lemma mem_registeredPairsAtHead {thisChain : Chain} {log : List OpAtHead}
    {p : Chain × Address} :
    p ∈ registeredPairsAtHead thisChain log ↔ ∃ o ∈ log, o.pair thisChain = some p := by
  simp [registeredPairsAtHead]

lemma registeredPairsAtHead_append (thisChain : Chain) (log log' : List OpAtHead) :
    registeredPairsAtHead thisChain (log ++ log')
      = registeredPairsAtHead thisChain log ∪ registeredPairsAtHead thisChain log' := by
  rw [registeredPairsAtHead, registeredPairsAtHead, registeredPairsAtHead, List.filterMap_append,
    List.toFinset_append]

private theorem reachLogAtHead_inv {e : NtvAssetId} {thisChain : Chain} (hc0 : thisChain ≠ 0)
    {legacy : LegacyAmounts} {S : Set (Chain × Address)} (he : IdAssumptionsOn e S)
    {W₀ W : WorldAtHead} {log : List OpAtHead} (hr : ReachLogAtHead e thisChain legacy W₀ W log)
    (hS : ↑(registeredPairsAtHead thisChain log) ⊆ S) (h0 : InvAtHead e thisChain legacy S W₀) :
    InvAtHead e thisChain legacy S W := by
  induction hr with
  | refl => exact h0
  | @tail X Y log o _ hs ih =>
    rw [registeredPairsAtHead_append, Finset.coe_union] at hS
    refine stepOpAtHead_preserves_inv he hc0 hs ?_ (ih (subset_trans Set.subset_union_left hS))
    intro p hp
    apply hS
    apply Set.mem_union_right
    rw [Finset.mem_coe, mem_registeredPairsAtHead]
    exact ⟨o, List.mem_singleton_self _, hp⟩

theorem logged_run_sound_at_head {e : NtvAssetId} {thisChain : Chain} {legacy : LegacyAmounts}
    (hc0 : thisChain ≠ 0) {S₀ : Set (Chain × Address)} {W₀ W : WorldAtHead}
    {log : List OpAtHead} (hstart : UpgradeStartAtHead legacy W₀)
    (hV₀ : Valid e thisChain W₀.world.vault) (hP₀ : PairsIn S₀ W₀.world.vault)
    (hr : ReachLogAtHead e thisChain legacy W₀ W log)
    (he : IdAssumptionsOn e (S₀ ∪ ↑(registeredPairsAtHead thisChain log))) :
    Valid e thisChain W.world.vault ∧ AuditedAtHead legacy thisChain W
      ∧ LedgerBackedAtHead legacy W
      ∧ (∀ a, W.world.vault.bridgedOut a ≤ W.world.vault.escrowed a)
      ∧ (∀ a, Native thisChain W.world.vault a →
          W.world.audit.totalIn a ≤ W.world.audit.totalOut a + populatedLegacy legacy W a) := by
  have h0 : InvAtHead e thisChain legacy (S₀ ∪ ↑(registeredPairsAtHead thisChain log)) W₀ :=
    ⟨hV₀, fun a h => Set.mem_union_left _ (hP₀ a h), upgradeStart_backed hstart,
      ⟨fun a _ => by
        rw [hstart.ledgerZero a, hstart.auditInZero a, hstart.auditOutZero a,
          populatedLegacy_false (hstart.unpopulated a)],
       fun a _ => ⟨hstart.auditInZero a, hstart.auditOutZero a, hstart.unpopulated a⟩⟩⟩
  have hI := reachLogAtHead_inv hc0 he hr Set.subset_union_right h0
  refine ⟨hI.valid, hI.audited, hI.backed, solvent_of_backed hI.backed, fun a hnat => ?_⟩
  have := hI.audited.netFlow a hnat
  omega

/-! ## The concrete upgraded vault -/

section Upgraded
variable {e : NtvAssetId} {thisChain : Chain} {t : Address}

lemma upgraded_vault_eq (held : ℕ) :
    (upgradedVaultAtHead e thisChain t held).world.vault
      = { (afterRegister e thisChain t).vault with
          escrowed := upd (fun _ => 0) (e thisChain t) held } := rfl

lemma upgraded_valid (hc0 : thisChain ≠ 0) (ht0 : t ≠ 0) (he0 : e thisChain t ≠ 0) (held : ℕ) :
    Valid e thisChain (upgradedVaultAtHead e thisChain t held).world.vault := by
  rw [upgraded_vault_eq]
  exact valid_with_escrowed
    (run_valid_on (idAssumptionsOn_singleton he0) hc0
      (afterRegister_reachIn (Set.mem_singleton _) ht0)) _ (fun _ => Nat.zero_le _)

lemma upgraded_pairsIn (ht0 : t ≠ 0) (held : ℕ) :
    PairsIn {(thisChain, t)} (upgradedVaultAtHead e thisChain t held).world.vault := by
  intro a h
  exact reachIn_pairsIn (afterRegister_reachIn (e := e) (thisChain := thisChain)
    (S := {(thisChain, t)}) (Set.mem_singleton _) ht0) a h

lemma upgraded_registered (ht0 : t ≠ 0) (held : ℕ) :
    Registered (upgradedVaultAtHead e thisChain t held).world.vault (e thisChain t) :=
  afterRegister_registered ht0

lemma upgraded_native (held : ℕ) :
    Native thisChain (upgradedVaultAtHead e thisChain t held).world.vault (e thisChain t) :=
  afterRegister_native

@[simp] lemma upgraded_bridgedOut (held : ℕ) (a : AssetId) :
    (upgradedVaultAtHead e thisChain t held).world.vault.bridgedOut a = 0 := rfl

@[simp] lemma upgraded_populated (held : ℕ) (a : AssetId) :
    (upgradedVaultAtHead e thisChain t held).populated a = false := rfl

@[simp] lemma upgraded_totalIn (held : ℕ) (a : AssetId) :
    (upgradedVaultAtHead e thisChain t held).world.audit.totalIn a = 0 := rfl

@[simp] lemma upgraded_totalOut (held : ℕ) (a : AssetId) :
    (upgradedVaultAtHead e thisChain t held).world.audit.totalOut a = 0 := rfl

lemma upgraded_escrowed_self (held : ℕ) :
    (upgradedVaultAtHead e thisChain t held).world.vault.escrowed (e thisChain t) = held := by
  show upd (fun _ => 0) (e thisChain t) held (e thisChain t) = held
  rw [upd_same]

lemma legacyOf_self (amt : ℕ) : legacyOfAtHead e thisChain t amt (e thisChain t) = amt := by
  show upd (fun _ => 0) (e thisChain t) amt (e thisChain t) = amt
  rw [upd_same]

lemma legacyOf_le_escrowed (amt : ℕ) (a : AssetId) :
    legacyOfAtHead e thisChain t amt a
      ≤ (upgradedVaultAtHead e thisChain t amt).world.vault.escrowed a := by
  show upd (fun _ => 0) (e thisChain t) amt a ≤ upd (fun _ => 0) (e thisChain t) amt a
  exact le_rfl

lemma upgraded_start (amt : ℕ) :
    UpgradeStartAtHead (legacyOfAtHead e thisChain t amt) (upgradedVaultAtHead e thisChain t amt) :=
  ⟨upgraded_bridgedOut amt, upgraded_populated amt, upgraded_totalIn amt, upgraded_totalOut amt,
    legacyOf_le_escrowed amt⟩

end Upgraded

theorem unbacked_legacy_breaks_solvency {e : NtvAssetId} {thisChain : Chain}
    (hc0 : thisChain ≠ 0) {t : Address} (ht0 : t ≠ 0) (he0 : e thisChain t ≠ 0) (held : ℕ) :
    let W := upgradedVaultAtHead e thisChain t held
    let legacy := legacyOfAtHead e thisChain t (held + 1)
    Valid e thisChain W.world.vault
      ∧ (∀ a, W.world.vault.bridgedOut a = 0) ∧ (∀ a, W.populated a = false)
      ∧ (∀ a, W.world.audit.totalIn a = 0 ∧ W.world.audit.totalOut a = 0)
      ∧ ¬ UpgradeStartAtHead legacy W
      ∧ ∃ X, StepOpAtHead e thisChain legacy (.populate (e thisChain t)) W X
        ∧ X.world.vault.escrowed (e thisChain t) < X.world.vault.bridgedOut (e thisChain t)
        ∧ FlowInGuard thisChain X.world.vault (e thisChain t) (held + 1)
        ∧ X.world.vault.escrowed (e thisChain t) < held + 1 := by
  intro W legacy
  have hesc : W.world.vault.escrowed (e thisChain t) = held := upgraded_escrowed_self held
  have hleg : legacy (e thisChain t) = held + 1 := legacyOf_self (held + 1)
  have hbo : (populateAtHead legacy W (e thisChain t)).world.vault.bridgedOut (e thisChain t)
      = held + 1 := by
    rw [populateAtHead_bridgedOut, upd_same, hleg]
    exact Nat.zero_add _
  refine ⟨upgraded_valid hc0 ht0 he0 held, upgraded_bridgedOut held, upgraded_populated held,
    fun a => ⟨upgraded_totalIn held a, upgraded_totalOut held a⟩, ?_, ?_⟩
  · intro hstart
    have := hstart.legacyBacked (e thisChain t)
    rw [hleg, hesc] at this
    omega
  · refine ⟨populateAtHead legacy W (e thisChain t),
      StepOpAtHead.populate (upgraded_populated held _) (upgraded_native held), ?_, ?_, ?_⟩
    · rw [populateAtHead_escrowed, hesc, hbo]
      omega
    · refine ⟨upgraded_registered ht0 held, fun _ => ?_⟩
      rw [hbo]
    · rw [populateAtHead_escrowed, hesc]
      omega

theorem populate_restores_legacy_withdrawal {e : NtvAssetId} {thisChain : Chain}
    (hc0 : thisChain ≠ 0) {t : Address} (ht0 : t ≠ 0) (he0 : e thisChain t ≠ 0) (L : ℕ)
    (hL : 0 < L) (c : Chain) :
    let W := upgradedVaultAtHead e thisChain t L
    let legacy := legacyOfAtHead e thisChain t L
    UpgradeStartAtHead legacy W ∧ Valid e thisChain W.world.vault
      ∧ ¬ FlowInGuard thisChain W.world.vault (e thisChain t) L
      ∧ ∃ X, StepOpAtHead e thisChain legacy (.populate (e thisChain t)) W X
        ∧ FlowInGuard thisChain X.world.vault (e thisChain t) L
        ∧ (bridgeIn thisChain X.world c (e thisChain t) L).vault.bridgedOut (e thisChain t) = 0
        ∧ (bridgeIn thisChain X.world c (e thisChain t) L).vault.escrowed (e thisChain t) = 0 := by
  intro W legacy
  have hnat : Native thisChain W.world.vault (e thisChain t) := upgraded_native L
  have hesc : W.world.vault.escrowed (e thisChain t) = L := upgraded_escrowed_self L
  have hleg : legacy (e thisChain t) = L := legacyOf_self L
  have hbo : (populateAtHead legacy W (e thisChain t)).world.vault.bridgedOut (e thisChain t)
      = L := by
    rw [populateAtHead_bridgedOut, upd_same, hleg]
    exact Nat.zero_add _
  have hnatX : Native thisChain (populateAtHead legacy W (e thisChain t)).world.vault
      (e thisChain t) := hnat
  refine ⟨upgraded_start L, upgraded_valid hc0 ht0 he0 L, ?_, ?_⟩
  · intro hg
    have := hg.sufficient hnat
    rw [upgraded_bridgedOut] at this
    omega
  · refine ⟨populateAtHead legacy W (e thisChain t),
      StepOpAtHead.populate (upgraded_populated L _) hnat,
      ⟨upgraded_registered ht0 L, fun _ => by rw [hbo]⟩, ?_, ?_⟩
    · rw [bridgeIn_bridgedOut_native _ _ _ _ _ hnatX, upd_same, hbo]
      omega
    · rw [bridgeIn_escrowed_native _ _ _ _ _ hnatX, upd_same, populateAtHead_escrowed, hesc]
      omega

theorem pre_population_headroom_is_shared {e : NtvAssetId} {thisChain : Chain}
    {t : Address} (ht0 : t ≠ 0) (L d : ℕ)
    (hdL : d ≤ L) (hd : 0 < d) (cA cB : Chain) :
    let W := upgradedVaultAtHead e thisChain t L
    let legacy := legacyOfAtHead e thisChain t L
    let a := e thisChain t
    ∃ X Y : WorldAtHead,
      StepOpAtHead e thisChain legacy (.pin (.bridgeOut cA a d)) W X
        ∧ StepOpAtHead e thisChain legacy (.pin (.bridgeIn cB a d)) X Y
        ∧ ¬ FlowInGuard thisChain Y.world.vault a d
        ∧ ∃ Z, StepOpAtHead e thisChain legacy (.populate a) Y Z
          ∧ FlowInGuard thisChain Z.world.vault a d := by
  show ∃ X Y : WorldAtHead,
      StepOpAtHead e thisChain (legacyOfAtHead e thisChain t L)
          (.pin (.bridgeOut cA (e thisChain t) d)) (upgradedVaultAtHead e thisChain t L) X
        ∧ StepOpAtHead e thisChain (legacyOfAtHead e thisChain t L)
          (.pin (.bridgeIn cB (e thisChain t) d)) X Y
        ∧ ¬ FlowInGuard thisChain Y.world.vault (e thisChain t) d
        ∧ ∃ Z, StepOpAtHead e thisChain (legacyOfAtHead e thisChain t L)
            (.populate (e thisChain t)) Y Z
          ∧ FlowInGuard thisChain Z.world.vault (e thisChain t) d
  have hreg := upgraded_registered (e := e) (thisChain := thisChain) ht0 L
  have hnat := upgraded_native (e := e) (thisChain := thisChain) (t := t) L
  have hnatX : Native thisChain (bridgeOut thisChain (upgradedVaultAtHead e thisChain t L).world
      cA (e thisChain t) d).vault (e thisChain t) := by simpa using hnat
  have hregX : Registered (bridgeOut thisChain (upgradedVaultAtHead e thisChain t L).world
      cA (e thisChain t) d).vault (e thisChain t) := by simpa using hreg
  have hboX : (bridgeOut thisChain (upgradedVaultAtHead e thisChain t L).world
      cA (e thisChain t) d).vault.bridgedOut (e thisChain t) = d := by
    rw [bridgeOut_bridgedOut_native _ _ _ _ _ hnat, upd_same, upgraded_bridgedOut]
    omega
  have hnatY : Native thisChain (bridgeIn thisChain (bridgeOut thisChain
      (upgradedVaultAtHead e thisChain t L).world cA (e thisChain t) d) cB (e thisChain t) d).vault
      (e thisChain t) := by simpa using hnatX
  have hregY : Registered (bridgeIn thisChain (bridgeOut thisChain
      (upgradedVaultAtHead e thisChain t L).world cA (e thisChain t) d) cB (e thisChain t) d).vault
      (e thisChain t) := by simpa using hregX
  have hboY : (bridgeIn thisChain (bridgeOut thisChain
      (upgradedVaultAtHead e thisChain t L).world cA (e thisChain t) d) cB (e thisChain t) d).vault.bridgedOut
      (e thisChain t) = 0 := by
    rw [bridgeIn_bridgedOut_native _ _ _ _ _ hnatX, upd_same, hboX]
    omega
  refine ⟨⟨bridgeOut thisChain (upgradedVaultAtHead e thisChain t L).world cA (e thisChain t) d,
      (upgradedVaultAtHead e thisChain t L).populated⟩,
    ⟨bridgeIn thisChain (bridgeOut thisChain (upgradedVaultAtHead e thisChain t L).world cA
      (e thisChain t) d) cB (e thisChain t) d, (upgradedVaultAtHead e thisChain t L).populated⟩,
    StepOpAtHead.pin (StepOp.bridgeOut ⟨hreg, by omega⟩),
    StepOpAtHead.pin (StepOp.bridgeIn ⟨hregX, fun _ => by rw [hboX]⟩), ?_, ?_⟩
  · intro hg
    have := hg.sufficient hnatY
    rw [hboY] at this
    omega
  · refine ⟨_, StepOpAtHead.populate
      (upgraded_populated (e := e) (thisChain := thisChain) (t := t) L (e thisChain t)) hnatY,
      ⟨hregY, fun _ => ?_⟩⟩
    rw [populateAtHead_bridgedOut, upd_same, hboY, Nat.zero_add, legacyOf_self]
    exact hdL

/-! ## The witness of the run-local headline -/

/-- The honest encoding on chain `1`, token `1`: the upgraded vault holds `2` of it, all
legacy. -/
private def witnessStart : WorldAtHead := upgradedVaultAtHead honestId 1 1 2

private def witnessLegacy : LegacyAmounts := legacyOfAtHead honestId 1 1 2

/-- Populate the asset, bridge one unit out to chain `5`, withdraw two units from chain `6`. -/
private def witnessLog : List OpAtHead :=
  (([] ++ [.populate 1]) ++ [.pin (.bridgeOut 5 1 1)]) ++ [.pin (.bridgeIn 6 1 2)]

private def witnessX1 : WorldAtHead := populateAtHead witnessLegacy witnessStart 1
private def witnessX2 : WorldAtHead := ⟨bridgeOut 1 witnessX1.world 5 1 1, witnessX1.populated⟩
private def witnessX3 : WorldAtHead := ⟨bridgeIn 1 witnessX2.world 6 1 2, witnessX2.populated⟩

theorem logged_run_sound_at_head_satisfiable :
    ∃ (e : NtvAssetId) (thisChain : Chain) (legacy : LegacyAmounts)
      (S₀ : Set (Chain × Address)) (W₀ W : WorldAtHead) (log : List OpAtHead),
      thisChain ≠ 0 ∧ UpgradeStartAtHead legacy W₀ ∧ Valid e thisChain W₀.world.vault
        ∧ PairsIn S₀ W₀.world.vault ∧ ReachLogAtHead e thisChain legacy W₀ W log
        ∧ IdAssumptionsOn e (S₀ ∪ ↑(registeredPairsAtHead thisChain log))
        ∧ ∃ a, Native thisChain W.world.vault a ∧ W.populated a = true ∧ legacy a ≠ 0
          ∧ W.world.audit.totalOut a ≠ 0
          ∧ W.world.audit.totalOut a < W.world.audit.totalIn a := by
  have hnat0 : Native 1 witnessStart.world.vault 1 :=
    upgraded_native (e := honestId) (thisChain := 1) (t := 1) 2
  have hreg0 : Registered witnessStart.world.vault 1 :=
    upgraded_registered (e := honestId) (thisChain := 1) (t := 1) (by decide) 2
  have hnat2 : Native 1 witnessX2.world.vault 1 := by
    show Native 1 (bridgeOut 1 witnessX1.world 5 1 1).vault 1
    rw [bridgeOut_native]
    exact hnat0
  have hreg2 : Registered witnessX2.world.vault 1 := by
    show Registered (bridgeOut 1 witnessX1.world 5 1 1).vault 1
    rw [bridgeOut_registered]
    exact hreg0
  have hnat3 : Native 1 witnessX3.world.vault 1 := by
    show Native 1 (bridgeIn 1 witnessX2.world 6 1 2).vault 1
    rw [bridgeIn_native]
    exact hnat2
  have hbo2 : witnessX2.world.vault.bridgedOut 1 = 3 := by decide
  have s1 : StepOpAtHead honestId 1 witnessLegacy (.populate 1) witnessStart witnessX1 :=
    StepOpAtHead.populate rfl hnat0
  have s2 : StepOpAtHead honestId 1 witnessLegacy (.pin (.bridgeOut 5 1 1)) witnessX1 witnessX2 :=
    StepOpAtHead.pin (StepOp.bridgeOut ⟨hreg0, by decide⟩)
  have s3 : StepOpAtHead honestId 1 witnessLegacy (.pin (.bridgeIn 6 1 2)) witnessX2 witnessX3 :=
    StepOpAtHead.pin (StepOp.bridgeIn ⟨hreg2, fun _ => by rw [hbo2]; decide⟩)
  have hr : ReachLogAtHead honestId 1 witnessLegacy witnessStart witnessX3 witnessLog :=
    ReachLogAtHead.tail (ReachLogAtHead.tail (ReachLogAtHead.tail ReachLogAtHead.refl s1) s2) s3
  have hpairs : registeredPairsAtHead 1 witnessLog = ∅ := rfl
  have he : IdAssumptionsOn honestId
      ({((1 : Chain), (1 : Address))} ∪ ↑(registeredPairsAtHead 1 witnessLog)) := by
    rw [hpairs, Finset.coe_empty, Set.union_empty]
    exact idAssumptionsOn_singleton (by decide)
  refine ⟨honestId, 1, witnessLegacy, {(1, 1)}, witnessStart, witnessX3, witnessLog, by decide,
    upgraded_start (e := honestId) (thisChain := 1) (t := 1) 2,
    upgraded_valid (e := honestId) (thisChain := 1) (t := 1) (by decide) (by decide) (by decide) 2,
    upgraded_pairsIn (e := honestId) (thisChain := 1) (t := 1) (by decide) 2, hr, he, 1, hnat3,
    by decide, by decide, by decide, by decide⟩

theorem escrow_ledger_at_head_witness :
    ∃ (e : NtvAssetId) (thisChain : Chain) (legacy : LegacyAmounts) (W₀ X W : WorldAtHead)
      (log₁ log₂ : List OpAtHead) (a : AssetId),
      LedgerBackedAtHead legacy W₀ ∧ ReachLogAtHead e thisChain legacy W₀ X (log₁ ++ [.populate a])
        ∧ ReachLogAtHead e thisChain legacy X W log₂ ∧ log₂ ≠ []
        ∧ W₀.populated a = false ∧ X.populated a = true ∧ legacy a ≠ 0
        ∧ Native thisChain W.world.vault a ∧ FlowInGuard thisChain W.world.vault a 1 := by
  have hnat0 : Native 1 witnessStart.world.vault 1 :=
    upgraded_native (e := honestId) (thisChain := 1) (t := 1) 2
  have hreg0 : Registered witnessStart.world.vault 1 :=
    upgraded_registered (e := honestId) (thisChain := 1) (t := 1) (by decide) 2
  have hnat2 : Native 1 witnessX2.world.vault 1 := by
    show Native 1 (bridgeOut 1 witnessX1.world 5 1 1).vault 1
    rw [bridgeOut_native]
    exact hnat0
  have hreg2 : Registered witnessX2.world.vault 1 := by
    show Registered (bridgeOut 1 witnessX1.world 5 1 1).vault 1
    rw [bridgeOut_registered]
    exact hreg0
  have hbo2 : witnessX2.world.vault.bridgedOut 1 = 3 := by decide
  have s1 : StepOpAtHead honestId 1 witnessLegacy (.populate 1) witnessStart witnessX1 :=
    StepOpAtHead.populate rfl hnat0
  have s2 : StepOpAtHead honestId 1 witnessLegacy (.pin (.bridgeOut 5 1 1)) witnessX1 witnessX2 :=
    StepOpAtHead.pin (StepOp.bridgeOut ⟨hreg0, by decide⟩)
  refine ⟨honestId, 1, witnessLegacy, witnessStart, witnessX1, witnessX2, [],
    [] ++ [.pin (.bridgeOut 5 1 1)], 1,
    upgradeStart_backed (upgraded_start (e := honestId) (thisChain := 1) (t := 1) 2),
    ReachLogAtHead.tail ReachLogAtHead.refl s1, ReachLogAtHead.tail ReachLogAtHead.refl s2,
    by simp, rfl, by decide, by decide, hnat2, ⟨hreg2, fun _ => by rw [hbo2]; decide⟩⟩

/-! ## The named statements -/

theorem PinStepOpIsStepOpAtHead : Properties.PinStepOpIsStepOpAtHead :=
  fun _ _ _ _ _ _ hs => pin_stepOp_atHead hs

theorem PinReachLogIsReachLogAtHead : Properties.PinReachLogIsReachLogAtHead :=
  fun _ _ _ _ _ _ hr => pin_reachLog_atHead hr

theorem StepAtHeadPreservesLedgerBacked : Properties.StepAtHeadPreservesLedgerBacked :=
  fun _ _ _ _ _ _ hs hB => stepOpAtHead_preserves_backed hs hB

theorem SolvencyAtHead : Properties.SolvencyAtHead := by
  intro e thisChain legacy W₀ W log h0 hr
  have hB := reachLogAtHead_backed hr h0
  exact ⟨hB, solvent_of_backed hB⟩

theorem UpgradeStartIsLedgerBacked : Properties.UpgradeStartIsLedgerBacked :=
  fun _ _ h => upgradeStart_backed h

theorem GuardedInflowIsBackedAtHead : Properties.GuardedInflowIsBackedAtHead :=
  fun _ _ _ hB a _ hg hnat => le_trans (hg.sufficient hnat) (solvent_of_backed hB a)

theorem UnbackedLegacyBreaksSolvencyAtHead : Properties.UnbackedLegacyBreaksSolvencyAtHead :=
  fun _ _ hc0 _ ht0 he0 held => unbacked_legacy_breaks_solvency hc0 ht0 he0 held

theorem PopulateEffectAtHead : Properties.PopulateEffectAtHead :=
  fun _ _ _ _ _ _ hs => populate_effect hs

theorem PopulatedFlagsPersistAtHead : Properties.PopulatedFlagsPersistAtHead :=
  fun _ _ _ _ _ _ hr a h => reachLogAtHead_populated_mono hr a h

theorem LoggedRunSoundAtHead : Properties.LoggedRunSoundAtHead :=
  fun _ _ _ hc0 _ _ _ _ hstart hV₀ hP₀ hr he => logged_run_sound_at_head hc0 hstart hV₀ hP₀ hr he

theorem LoggedRunSoundAtHeadSatisfiable : Properties.LoggedRunSoundAtHeadSatisfiable :=
  logged_run_sound_at_head_satisfiable

theorem PopulateRestoresLegacyWithdrawalAtHead :
    Properties.PopulateRestoresLegacyWithdrawalAtHead :=
  fun _ _ hc0 _ ht0 he0 L hL c => populate_restores_legacy_withdrawal hc0 ht0 he0 L hL c

theorem PrePopulationHeadroomIsSharedAtHead : Properties.PrePopulationHeadroomIsSharedAtHead :=
  fun _ _ _ ht0 L d hdL hd cA cB => pre_population_headroom_is_shared ht0 L d hdL hd cA cB

theorem EscrowLedgerAtHeadWitness : Properties.EscrowLedgerAtHeadWitness :=
  escrow_ledger_at_head_witness

end Contracts.NativeTokenVault
