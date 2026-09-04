import EraSpec.Properties.NativeTokenVault

/-!
# Proofs: the native token vault

Two arguments carry the file.

`setNewTokenStorage_preserves_valid` is the registry induction, done once for the
single writer both registration paths call.  Its hypotheses are what each path has
to supply, and the interesting one is id-freshness: the bridged path is *given* it
by the `token == address(0)` test that gates the deploy branch, while the native
path has to *derive* it — that derivation is `registerNative_id_fresh`, and it is
where the id being a hash of the token does its work.

The ledger side is arithmetic on two counters that move together, so solvency is
`omega` per step once the guard is in hand.  The two countermodels are short
explicit runs.

The `Registered` / `Native` bridging lemmas below exist because both predicates are
reducible abbreviations of the tests the contract branches on: they stay folded in
terms, so every proof step goes through a named lemma rather than through the
projection.
-/

namespace Contracts.NativeTokenVault

/-! ## Mapping updates -/

@[simp] lemma upd_same {β : Type} (f : AssetId → β) (a : AssetId) (v : β) : upd f a v a = v := by
  simp [upd]

lemma upd_ne {β : Type} (f : AssetId → β) {x a : AssetId} (v : β) (h : x ≠ a) :
    upd f a v x = f x := by simp [upd, h]

@[simp] lemma updA_same {β : Type} (f : Address → β) (t : Address) (v : β) : updA f t v t = v := by
  simp [updA]

lemma updA_ne {β : Type} (f : Address → β) {x t : Address} (v : β) (h : x ≠ t) :
    updA f t v x = f x := by simp [updA, h]

@[simp] lemma updCA_same (f : Chain → AssetId → ℕ) (c : Chain) (a : AssetId) (v : ℕ) :
    updCA f c a v c a = v := by simp [updCA]

lemma updCA_ne (f : Chain → AssetId → ℕ) {x c : Chain} {y a : AssetId} (v : ℕ)
    (h : ¬(x = c ∧ y = a)) : updCA f c a v x y = f x y := by simp [updCA, h]

/-! ## The registry write, field by field -/

section Fields
variable (V : Vault) (a : AssetId) (t ot : Address) (origin : Chain)

@[simp] lemma sn_bridgedOut : (setNewTokenStorage V a t ot origin).bridgedOut = V.bridgedOut := rfl
@[simp] lemma sn_escrowed : (setNewTokenStorage V a t ot origin).escrowed = V.escrowed := rfl
@[simp] lemma sn_token_self : (setNewTokenStorage V a t ot origin).token a = t := by
  simp [setNewTokenStorage]
@[simp] lemma sn_assetOf_self : (setNewTokenStorage V a t ot origin).assetOf t = a := by
  simp [setNewTokenStorage]
@[simp] lemma sn_originChain_self : (setNewTokenStorage V a t ot origin).originChain a = origin := by
  simp [setNewTokenStorage]
@[simp] lemma sn_originToken_self : (setNewTokenStorage V a t ot origin).originToken a = ot := by
  simp [setNewTokenStorage]

lemma sn_token_of_ne {a' : AssetId} (h : a' ≠ a) :
    (setNewTokenStorage V a t ot origin).token a' = V.token a' := by
  simp [setNewTokenStorage, upd, h]
lemma sn_assetOf_of_ne {t' : Address} (h : t' ≠ t) :
    (setNewTokenStorage V a t ot origin).assetOf t' = V.assetOf t' := by
  simp [setNewTokenStorage, updA, h]
lemma sn_originChain_of_ne {a' : AssetId} (h : a' ≠ a) :
    (setNewTokenStorage V a t ot origin).originChain a' = V.originChain a' := by
  simp [setNewTokenStorage, upd, h]
lemma sn_originToken_of_ne {a' : AssetId} (h : a' ≠ a) :
    (setNewTokenStorage V a t ot origin).originToken a' = V.originToken a' := by
  simp [setNewTokenStorage, upd, h]

/-! ### …and how the two branch predicates read off it -/

lemma sn_registered_self : Registered (setNewTokenStorage V a t ot origin) a ↔ t ≠ 0 := by
  simp [Registered]
lemma sn_registered_of_ne {a' : AssetId} (h : a' ≠ a) :
    Registered (setNewTokenStorage V a t ot origin) a' ↔ Registered V a' := by
  simp [Registered, sn_token_of_ne V a t ot origin h]
lemma sn_native_self (thisChain : Chain) :
    Native thisChain (setNewTokenStorage V a t ot origin) a ↔ origin = thisChain := by
  simp [Native]
lemma sn_native_of_ne (thisChain : Chain) {a' : AssetId} (h : a' ≠ a) :
    Native thisChain (setNewTokenStorage V a t ot origin) a' ↔ Native thisChain V a' := by
  simp [Native, sn_originChain_of_ne V a t ot origin h]

end Fields

@[simp] lemma rn_as_sn (e : NtvAssetId) (thisChain : Chain) (V : Vault) (t : Address) :
    registerNative e thisChain V t = setNewTokenStorage V (e thisChain t) t t thisChain := rfl

@[simp] lemma rb_as_sn (V : Vault) (a : AssetId) (t ot : Address) (origin : Chain) :
    registerBridged V a t ot origin = setNewTokenStorage V a t ot origin := rfl

/-! ## The flows, field by field -/

section FlowFields
variable (thisChain : Chain) (W : World) (c : Chain) (a : AssetId) (amt : ℕ)

@[simp] lemma bridgeOut_originChain :
    (bridgeOut thisChain W c a amt).vault.originChain = W.vault.originChain := by
  by_cases hnat : Native thisChain W.vault a
  · simp [bridgeOut, if_pos hnat]
  · simp [bridgeOut, if_neg hnat]
@[simp] lemma bridgeOut_token :
    (bridgeOut thisChain W c a amt).vault.token = W.vault.token := by
  by_cases hnat : Native thisChain W.vault a
  · simp [bridgeOut, if_pos hnat]
  · simp [bridgeOut, if_neg hnat]
@[simp] lemma bridgeOut_assetOf :
    (bridgeOut thisChain W c a amt).vault.assetOf = W.vault.assetOf := by
  by_cases hnat : Native thisChain W.vault a
  · simp [bridgeOut, if_pos hnat]
  · simp [bridgeOut, if_neg hnat]
@[simp] lemma bridgeOut_originToken :
    (bridgeOut thisChain W c a amt).vault.originToken = W.vault.originToken := by
  by_cases hnat : Native thisChain W.vault a
  · simp [bridgeOut, if_pos hnat]
  · simp [bridgeOut, if_neg hnat]
@[simp] lemma bridgeIn_originChain :
    (bridgeIn thisChain W c a amt).vault.originChain = W.vault.originChain := by
  by_cases hnat : Native thisChain W.vault a
  · simp [bridgeIn, if_pos hnat]
  · simp [bridgeIn, if_neg hnat]
@[simp] lemma bridgeIn_token :
    (bridgeIn thisChain W c a amt).vault.token = W.vault.token := by
  by_cases hnat : Native thisChain W.vault a
  · simp [bridgeIn, if_pos hnat]
  · simp [bridgeIn, if_neg hnat]
@[simp] lemma bridgeIn_assetOf :
    (bridgeIn thisChain W c a amt).vault.assetOf = W.vault.assetOf := by
  by_cases hnat : Native thisChain W.vault a
  · simp [bridgeIn, if_pos hnat]
  · simp [bridgeIn, if_neg hnat]
@[simp] lemma bridgeIn_originToken :
    (bridgeIn thisChain W c a amt).vault.originToken = W.vault.originToken := by
  by_cases hnat : Native thisChain W.vault a
  · simp [bridgeIn, if_pos hnat]
  · simp [bridgeIn, if_neg hnat]
@[simp] lemma donate_originChain :
    (donate W a amt).vault.originChain = W.vault.originChain := rfl
@[simp] lemma donate_token : (donate W a amt).vault.token = W.vault.token := rfl
@[simp] lemma donate_assetOf : (donate W a amt).vault.assetOf = W.vault.assetOf := rfl
@[simp] lemma donate_originToken : (donate W a amt).vault.originToken = W.vault.originToken := rfl

@[simp] lemma bridgeOut_registered {a' : AssetId} :
    Registered (bridgeOut thisChain W c a amt).vault a' ↔ Registered W.vault a' := by
  simp [Registered]
@[simp] lemma bridgeOut_native {a' : AssetId} :
    Native thisChain (bridgeOut thisChain W c a amt).vault a' ↔ Native thisChain W.vault a' := by
  simp [Native]
@[simp] lemma bridgeIn_registered {a' : AssetId} :
    Registered (bridgeIn thisChain W c a amt).vault a' ↔ Registered W.vault a' := by
  simp [Registered]
@[simp] lemma bridgeIn_native {a' : AssetId} :
    Native thisChain (bridgeIn thisChain W c a amt).vault a' ↔ Native thisChain W.vault a' := by
  simp [Native]
@[simp] lemma donate_registered {a' : AssetId} :
    Registered (donate W a amt).vault a' ↔ Registered W.vault a' := by simp [Registered]
@[simp] lemma donate_native {a' : AssetId} :
    Native thisChain (donate W a amt).vault a' ↔ Native thisChain W.vault a' := by simp [Native]

@[simp] lemma bridgeOut_totalOut :
    (bridgeOut thisChain W c a amt).audit.totalOut
      = upd W.audit.totalOut a (W.audit.totalOut a + amt) := rfl
@[simp] lemma bridgeOut_totalIn :
    (bridgeOut thisChain W c a amt).audit.totalIn = W.audit.totalIn := rfl
@[simp] lemma bridgeOut_outTo :
    (bridgeOut thisChain W c a amt).audit.outTo
      = updCA W.audit.outTo c a (W.audit.outTo c a + amt) := rfl
@[simp] lemma bridgeOut_innFrom :
    (bridgeOut thisChain W c a amt).audit.innFrom = W.audit.innFrom := rfl
@[simp] lemma bridgeIn_totalIn :
    (bridgeIn thisChain W c a amt).audit.totalIn
      = upd W.audit.totalIn a (W.audit.totalIn a + amt) := rfl
@[simp] lemma bridgeIn_totalOut :
    (bridgeIn thisChain W c a amt).audit.totalOut = W.audit.totalOut := rfl
@[simp] lemma bridgeIn_innFrom :
    (bridgeIn thisChain W c a amt).audit.innFrom
      = updCA W.audit.innFrom c a (W.audit.innFrom c a + amt) := rfl
@[simp] lemma bridgeIn_outTo :
    (bridgeIn thisChain W c a amt).audit.outTo = W.audit.outTo := rfl
@[simp] lemma donate_audit : (donate W a amt).audit = W.audit := rfl

lemma bridgeOut_bridgedOut_native (hnat : Native thisChain W.vault a) :
    (bridgeOut thisChain W c a amt).vault.bridgedOut
      = upd W.vault.bridgedOut a (W.vault.bridgedOut a + amt) := by
  simp [bridgeOut, if_pos hnat]
lemma bridgeOut_escrowed_native (hnat : Native thisChain W.vault a) :
    (bridgeOut thisChain W c a amt).vault.escrowed
      = upd W.vault.escrowed a (W.vault.escrowed a + amt) := by
  simp [bridgeOut, if_pos hnat]
lemma bridgeOut_vault_foreign (hnat : ¬ Native thisChain W.vault a) :
    (bridgeOut thisChain W c a amt).vault = W.vault := by
  simp [bridgeOut, if_neg hnat]
lemma bridgeIn_bridgedOut_native (hnat : Native thisChain W.vault a) :
    (bridgeIn thisChain W c a amt).vault.bridgedOut
      = upd W.vault.bridgedOut a (W.vault.bridgedOut a - amt) := by
  simp [bridgeIn, if_pos hnat]
lemma bridgeIn_escrowed_native (hnat : Native thisChain W.vault a) :
    (bridgeIn thisChain W c a amt).vault.escrowed
      = upd W.vault.escrowed a (W.vault.escrowed a - amt) := by
  simp [bridgeIn, if_pos hnat]
lemma bridgeIn_vault_foreign (hnat : ¬ Native thisChain W.vault a) :
    (bridgeIn thisChain W c a amt).vault = W.vault := by
  simp [bridgeIn, if_neg hnat]
@[simp] lemma donate_bridgedOut : (donate W a amt).vault.bridgedOut = W.vault.bridgedOut := rfl
@[simp] lemma donate_escrowed :
    (donate W a amt).vault.escrowed = upd W.vault.escrowed a (W.vault.escrowed a + amt) := rfl

end FlowFields

/-! ## The registry induction -/

/-- **THE SINGLE REGISTRY WRITE PRESERVES THE INVARIANT.**  Stated for
`_setNewTokenStorage` directly, so both registration paths get it from one proof.

The hypotheses are exactly what a caller must establish: the id and token are
nonzero and free, the origin chain is set, the id has the right shape, and a native
asset's origin token is the token itself. -/
theorem setNewTokenStorage_preserves_valid {e : NtvAssetId} {thisChain : Chain}
    (hc0 : thisChain ≠ 0) {V : Vault} (hV : Valid e thisChain V)
    {a : AssetId} {t ot : Address} {origin : Chain}
    (ha0 : a ≠ 0) (ht0 : t ≠ 0) (horg0 : origin ≠ 0)
    (hfreshId : ¬ Registered V a) (hfreshTok : V.assetOf t = 0)
    (hshape : a = e origin ot) (hnat : origin = thisChain → ot = t) :
    Valid e thisChain (setNewTokenStorage V a t ot origin) := by
  -- the asset is untouched in `V`, so its origin chain is unset and it is not native
  have hchain0 : V.originChain a = 0 := by
    by_contra hne
    exact hfreshId ((hV.originIff a).mpr hne)
  have hnotNative : ¬ Native thisChain V a := by
    simp only [Native, hchain0]
    exact fun h => hc0 h.symm
  refine ⟨?inv, ?tok, ?oiff, ?zu, ?ztf, ?shape, ?nt, ?ledg, ?solv⟩
  case inv =>
    intro a' hreg
    by_cases h : a' = a
    · subst h; simp
    · have hregV : Registered V a' := (sn_registered_of_ne V a t ot origin h).mp hreg
      have hne : V.token a' ≠ t := by
        intro heq
        have hinv := hV.inverse a' hregV
        rw [heq, hfreshTok] at hinv
        exact hV.zeroUnregistered (by rw [hinv]; exact hregV)
      rw [sn_token_of_ne V a t ot origin h, sn_assetOf_of_ne V a t ot origin hne]
      exact hV.inverse a' hregV
  case tok =>
    intro t' hreg
    by_cases h : t' = t
    · subst h; simp
    · have hregV : V.assetOf t' ≠ 0 := by
        rw [← sn_assetOf_of_ne V a t ot origin h]; exact hreg
      have hne : V.assetOf t' ≠ a := by
        intro heq
        have htok := hV.tokenOfAsset t' hregV
        rw [heq] at htok
        have ht'0 : t' ≠ 0 := by
          intro h0
          rw [h0, hV.zeroTokenFree] at hregV
          exact hregV rfl
        exact hfreshId (by simp only [Registered, htok]; exact ht'0)
      rw [sn_assetOf_of_ne V a t ot origin h, sn_token_of_ne V a t ot origin hne]
      exact hV.tokenOfAsset t' hregV
  case oiff =>
    intro a'
    by_cases h : a' = a
    · subst h
      rw [sn_registered_self V a' t ot origin, sn_originChain_self]
      exact ⟨fun _ => horg0, fun _ => ht0⟩
    · rw [sn_registered_of_ne V a t ot origin h, sn_originChain_of_ne V a t ot origin h]
      exact hV.originIff a'
  case zu =>
    rw [sn_registered_of_ne V a t ot origin (fun h => ha0 h.symm)]
    exact hV.zeroUnregistered
  case ztf =>
    rw [sn_assetOf_of_ne V a t ot origin (fun h => ht0 h.symm)]
    exact hV.zeroTokenFree
  case shape =>
    intro a' hreg
    by_cases h : a' = a
    · subst h
      rw [sn_originChain_self, sn_originToken_self]
      exact hshape
    · rw [sn_originChain_of_ne V a t ot origin h, sn_originToken_of_ne V a t ot origin h]
      exact hV.idShape a' ((sn_registered_of_ne V a t ot origin h).mp hreg)
  case nt =>
    intro a' hreg hnative
    by_cases h : a' = a
    · subst h
      rw [sn_originToken_self, sn_token_self]
      exact hnat ((sn_native_self V a' t ot origin thisChain).mp hnative)
    · rw [sn_originToken_of_ne V a t ot origin h, sn_token_of_ne V a t ot origin h]
      exact hV.nativeToken a' ((sn_registered_of_ne V a t ot origin h).mp hreg)
        ((sn_native_of_ne V a t ot origin thisChain h).mp hnative)
  case ledg =>
    intro a' hnn
    rw [sn_bridgedOut]
    by_cases h : a' = a
    · subst h; exact hV.ledgerNative a' hnotNative
    · exact hV.ledgerNative a'
        (fun hx => hnn ((sn_native_of_ne V a t ot origin thisChain h).mpr hx))
  case solv => intro a'; rw [sn_bridgedOut, sn_escrowed]; exact hV.solvent a'

/-- **THE DERIVED ID IS FREE.**  The one-sided guard of `_registerToken` is enough:
if the id were taken, `idShape` and injectivity would force the taker to be a
native asset whose token is exactly `t`, and `inverse` would then contradict
`assetId[t] == 0`. -/
theorem registerNative_id_fresh {e : NtvAssetId} (he : IdAssumptions e)
    {thisChain : Chain} {V : Vault} (hV : Valid e thisChain V)
    {t : Address} (hg : RegisterNativeGuard V t) : ¬ Registered V (e thisChain t) := by
  intro hreg
  obtain ⟨hc, hot⟩ := he.inj _ _ _ _ (hV.idShape _ hreg)
  have hnative : Native thisChain V (e thisChain t) := hc.symm
  have htok : V.token (e thisChain t) = t := by
    rw [← hV.nativeToken _ hreg hnative, ← hot]
  have hinv := hV.inverse _ hreg
  rw [htok, hg.fresh] at hinv
  exact he.nonzero thisChain t hinv.symm

theorem registerNative_preserves_valid {e : NtvAssetId} (he : IdAssumptions e)
    {thisChain : Chain} (hc0 : thisChain ≠ 0) {V : Vault} (hV : Valid e thisChain V)
    {t : Address} (hg : RegisterNativeGuard V t) :
    Valid e thisChain (registerNative e thisChain V t) :=
  setNewTokenStorage_preserves_valid hc0 hV (he.nonzero thisChain t) hg.nonzero hc0
    (registerNative_id_fresh he hV hg) hg.fresh rfl (fun _ => rfl)

theorem registerBridged_preserves_valid {e : NtvAssetId} (he : IdAssumptions e)
    {thisChain : Chain} (hc0 : thisChain ≠ 0) {V : Vault} (hV : Valid e thisChain V)
    {a : AssetId} {t ot : Address} {origin : Chain}
    (hg : RegisterBridgedGuard e thisChain V a t ot origin) :
    Valid e thisChain (registerBridged V a t ot origin) :=
  setNewTokenStorage_preserves_valid hc0 hV
    (by rw [hg.idChecked]; exact he.nonzero origin ot) hg.tokenNonzero hg.originNonzero
    hg.freshId hg.freshToken hg.idChecked (fun h => absurd h hg.notNative)

/-! ## The ledger -/

/-- The registry half of `Valid`, carried across a step that touches none of the
four registry fields. -/
private lemma flow_registry {e : NtvAssetId} {thisChain : Chain} {V V' : Vault}
    (hV : Valid e thisChain V)
    (hoc : V'.originChain = V.originChain) (htk : V'.token = V.token)
    (hao : V'.assetOf = V.assetOf) (hot : V'.originToken = V.originToken)
    (hledg : ∀ a, ¬ Native thisChain V' a → V'.bridgedOut a = 0)
    (hsolv : ∀ a, V'.bridgedOut a ≤ V'.escrowed a) :
    Valid e thisChain V' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hledg, hsolv⟩
  · intro a hreg
    rw [htk, hao]
    exact hV.inverse a (by simp only [Registered, htk] at hreg; exact hreg)
  · intro t hreg
    rw [hao, htk]
    exact hV.tokenOfAsset t (by rw [hao] at hreg; exact hreg)
  · intro a
    simp only [Registered, htk, hoc]
    exact hV.originIff a
  · simp only [Registered, htk]
    exact hV.zeroUnregistered
  · rw [hao]; exact hV.zeroTokenFree
  · intro a hreg
    rw [hoc, hot]
    exact hV.idShape a (by simp only [Registered, htk] at hreg; exact hreg)
  · intro a hreg hnative
    rw [hot, htk]
    refine hV.nativeToken a ?_ ?_
    · simp only [Registered, htk] at hreg; exact hreg
    · simp only [Native, hoc] at hnative; exact hnative

theorem bridgeOut_preserves_valid {e : NtvAssetId} {thisChain : Chain} {W : World}
    (hV : Valid e thisChain W.vault) {c : Chain} {a : AssetId} {amt : ℕ} :
    Valid e thisChain (bridgeOut thisChain W c a amt).vault := by
  by_cases hnat : Native thisChain W.vault a
  · refine flow_registry hV (by simp) (by simp) (by simp) (by simp) ?_ ?_
    · intro a' hnn
      have h : a' ≠ a := by
        intro h; subst h; exact hnn (by simpa using hnat)
      rw [bridgeOut_bridgedOut_native _ _ _ _ _ hnat, upd_ne _ _ h]
      exact hV.ledgerNative a' (by simpa using hnn)
    · intro a'
      rw [bridgeOut_bridgedOut_native _ _ _ _ _ hnat, bridgeOut_escrowed_native _ _ _ _ _ hnat]
      by_cases h : a' = a
      · subst h; rw [upd_same, upd_same]; have := hV.solvent a'; omega
      · rw [upd_ne _ _ h, upd_ne _ _ h]; exact hV.solvent a'
  · rw [bridgeOut_vault_foreign _ _ _ _ _ hnat]; exact hV

theorem bridgeIn_preserves_valid {e : NtvAssetId} {thisChain : Chain} {W : World}
    (hV : Valid e thisChain W.vault) {c : Chain} {a : AssetId} {amt : ℕ}
    (hg : FlowInGuard thisChain W.vault a amt) :
    Valid e thisChain (bridgeIn thisChain W c a amt).vault := by
  by_cases hnat : Native thisChain W.vault a
  · refine flow_registry hV (by simp) (by simp) (by simp) (by simp) ?_ ?_
    · intro a' hnn
      have h : a' ≠ a := by
        intro h; subst h; exact hnn (by simpa using hnat)
      rw [bridgeIn_bridgedOut_native _ _ _ _ _ hnat, upd_ne _ _ h]
      exact hV.ledgerNative a' (by simpa using hnn)
    · intro a'
      rw [bridgeIn_bridgedOut_native _ _ _ _ _ hnat, bridgeIn_escrowed_native _ _ _ _ _ hnat]
      by_cases h : a' = a
      · subst h
        rw [upd_same, upd_same]
        have h1 := hV.solvent a'
        have h2 := hg.sufficient hnat
        omega
      · rw [upd_ne _ _ h, upd_ne _ _ h]; exact hV.solvent a'
  · rw [bridgeIn_vault_foreign _ _ _ _ _ hnat]; exact hV

theorem donate_preserves_valid {e : NtvAssetId} {thisChain : Chain} {W : World}
    (hV : Valid e thisChain W.vault) {a : AssetId} {amt : ℕ} :
    Valid e thisChain (donate W a amt).vault := by
  refine flow_registry hV rfl rfl rfl rfl
    (fun a' hnn => hV.ledgerNative a' (by simpa using hnn)) ?_
  intro a'
  rw [donate_bridgedOut, donate_escrowed]
  by_cases h : a' = a
  · subst h; rw [upd_same]; have := hV.solvent a'; omega
  · rw [upd_ne _ _ h]; exact hV.solvent a'

theorem step_preserves_valid {e : NtvAssetId} (he : IdAssumptions e) {thisChain : Chain}
    (hc0 : thisChain ≠ 0) {W X : World} (hs : Step e thisChain W X)
    (hV : Valid e thisChain W.vault) : Valid e thisChain X.vault := by
  cases hs with
  | registerNative hg => exact registerNative_preserves_valid he hc0 hV hg
  | registerBridged hg => exact registerBridged_preserves_valid he hc0 hV hg
  | bridgeOut _ => exact bridgeOut_preserves_valid hV
  | bridgeIn hg => exact bridgeIn_preserves_valid hV hg
  | donate => exact donate_preserves_valid hV

theorem empty_valid {e : NtvAssetId} {thisChain : Chain} : Valid e thisChain empty.vault := by
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_, fun _ _ => rfl, fun _ => le_refl _⟩
  · intro a hreg; exact absurd rfl hreg
  · intro t hreg; exact absurd rfl hreg
  · intro a; exact ⟨fun h => absurd rfl h, fun h => absurd rfl h⟩
  · intro h; exact absurd rfl h
  · intro a hreg; exact absurd rfl hreg
  · intro a hreg; exact absurd rfl hreg

theorem run_valid {e : NtvAssetId} (he : IdAssumptions e) {thisChain : Chain}
    (hc0 : thisChain ≠ 0) {W : World} (hr : Reach e thisChain empty W) :
    Valid e thisChain W.vault := by
  induction hr with
  | refl => exact empty_valid
  | tail _ hs ih => exact step_preserves_valid he hc0 hs ih

/-! ## Solvency and its consequences -/

theorem guarded_inflow_is_backed {e : NtvAssetId} {thisChain : Chain} {V : Vault}
    (hV : Valid e thisChain V) {a : AssetId} {amt : ℕ}
    (hg : FlowInGuard thisChain V a amt) (hnat : Native thisChain V a) : amt ≤ V.escrowed a :=
  le_trans (hg.sufficient hnat) (hV.solvent a)

theorem surplus_monotone {e : NtvAssetId} {thisChain : Chain} {W X : World}
    (hs : Step e thisChain W X) (hV : Valid e thisChain W.vault) (a : AssetId) :
    W.vault.escrowed a - W.vault.bridgedOut a ≤ X.vault.escrowed a - X.vault.bridgedOut a := by
  cases hs with
  | registerNative hg => simp
  | registerBridged hg => simp
  | @bridgeOut c a' amt hg =>
    by_cases hnat : Native thisChain W.vault a'
    · rw [bridgeOut_bridgedOut_native _ _ _ _ _ hnat, bridgeOut_escrowed_native _ _ _ _ _ hnat]
      by_cases h : a = a'
      · subst h; rw [upd_same, upd_same]; omega
      · rw [upd_ne _ _ h, upd_ne _ _ h]
    · rw [bridgeOut_vault_foreign _ _ _ _ _ hnat]
  | @bridgeIn c a' amt hg =>
    by_cases hnat : Native thisChain W.vault a'
    · rw [bridgeIn_bridgedOut_native _ _ _ _ _ hnat, bridgeIn_escrowed_native _ _ _ _ _ hnat]
      by_cases h : a = a'
      · subst h
        rw [upd_same, upd_same]
        have h1 := hV.solvent a
        have h2 := hg.sufficient hnat
        omega
      · rw [upd_ne _ _ h, upd_ne _ _ h]
    · rw [bridgeIn_vault_foreign _ _ _ _ _ hnat]
  | @donate a' amt =>
    rw [donate_bridgedOut, donate_escrowed]
    by_cases h : a = a'
    · subst h; rw [upd_same]; omega
    · rw [upd_ne _ _ h]

/-! ## The flow audit -/

theorem empty_audited {thisChain : Chain} : Audited thisChain empty :=
  ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩

/-- A flow only ever touches a REGISTERED asset, which is what keeps
`unregisteredQuiet` inductive. -/
private lemma ne_of_unreg {V : Vault} {a a' : AssetId} (hreg : Registered V a)
    (hnn : ¬ Registered V a') : a' ≠ a := by
  intro h; rw [h] at hnn; exact hnn hreg

theorem step_preserves_audited {e : NtvAssetId} (he : IdAssumptions e) {thisChain : Chain}
    (hc0 : thisChain ≠ 0) {W X : World} (hs : Step e thisChain W X)
    (hV : Valid e thisChain W.vault) (hA : Audited thisChain W) : Audited thisChain X := by
  cases hs with
  | @registerNative t hg =>
    have hfresh : ¬ Registered W.vault (e thisChain t) := registerNative_id_fresh he hV hg
    refine ⟨?_, ?_⟩
    · intro a' hnat
      by_cases h : a' = e thisChain t
      · -- the fresh id has seen no flow and carries no ledger
        subst h
        obtain ⟨hin, hout⟩ := hA.unregisteredQuiet (e thisChain t) hfresh
        have hchain0 : W.vault.originChain (e thisChain t) = 0 := by
          by_contra hne
          exact hfresh ((hV.originIff (e thisChain t)).mpr hne)
        have hbo : W.vault.bridgedOut (e thisChain t) = 0 := by
          refine hV.ledgerNative (e thisChain t) ?_
          simp only [Native, hchain0]
          exact fun hx => hc0 hx.symm
        show (setNewTokenStorage W.vault (e thisChain t) t t thisChain).bridgedOut (e thisChain t)
            + W.audit.totalIn (e thisChain t) = W.audit.totalOut (e thisChain t)
        rw [sn_bridgedOut, hbo, hin, hout]
      · exact hA.netFlow a' ((sn_native_of_ne W.vault _ t t thisChain thisChain h).mp hnat)
    · intro a' hnn
      refine hA.unregisteredQuiet a' ?_
      intro hreg
      refine hnn ?_
      by_cases h : a' = e thisChain t
      · subst h
        exact (sn_registered_self W.vault (e thisChain t) t t thisChain).mpr hg.nonzero
      · exact (sn_registered_of_ne W.vault _ t t thisChain h).mpr hreg
  | @registerBridged a t ot origin hg =>
    refine ⟨?_, ?_⟩
    · intro a' hnat
      by_cases h : a' = a
      · subst h
        exact absurd ((sn_native_self W.vault a' t ot origin thisChain).mp hnat) hg.notNative
      · exact hA.netFlow a' ((sn_native_of_ne W.vault a t ot origin thisChain h).mp hnat)
    · intro a' hnn
      refine hA.unregisteredQuiet a' ?_
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
          have hnet := hA.netFlow a' hnatW
          rw [bridgeOut_bridgedOut_native _ _ _ _ _ hnata, bridgeOut_totalIn,
            bridgeOut_totalOut, upd_same, upd_same]
          omega
        · rw [bridgeOut_bridgedOut_native _ _ _ _ _ hnata, bridgeOut_totalIn,
            bridgeOut_totalOut, upd_ne _ _ h, upd_ne _ _ h]
          exact hA.netFlow a' hnatW
      · have h : a' ≠ a := by
          intro h; subst h; exact hnata hnatW
        rw [bridgeOut_vault_foreign _ _ _ _ _ hnata, bridgeOut_totalIn, bridgeOut_totalOut,
          upd_ne _ _ h]
        exact hA.netFlow a' hnatW
    · intro a' hnn
      have hnnW : ¬ Registered W.vault a' := by simpa using hnn
      have h : a' ≠ a := ne_of_unreg hg.registered hnnW
      obtain ⟨hin, hout⟩ := hA.unregisteredQuiet a' hnnW
      exact ⟨by rw [bridgeOut_totalIn]; exact hin,
        by rw [bridgeOut_totalOut, upd_ne _ _ h]; exact hout⟩
  | @bridgeIn c a amt hg =>
    refine ⟨?_, ?_⟩
    · intro a' hnat
      have hnatW : Native thisChain W.vault a' := by simpa using hnat
      by_cases hnata : Native thisChain W.vault a
      · by_cases h : a' = a
        · subst h
          have hnet := hA.netFlow a' hnatW
          have hsuf := hg.sufficient hnata
          rw [bridgeIn_bridgedOut_native _ _ _ _ _ hnata, bridgeIn_totalIn,
            bridgeIn_totalOut, upd_same, upd_same]
          omega
        · rw [bridgeIn_bridgedOut_native _ _ _ _ _ hnata, bridgeIn_totalIn,
            bridgeIn_totalOut, upd_ne _ _ h, upd_ne _ _ h]
          exact hA.netFlow a' hnatW
      · have h : a' ≠ a := by
          intro h; subst h; exact hnata hnatW
        rw [bridgeIn_vault_foreign _ _ _ _ _ hnata, bridgeIn_totalOut, bridgeIn_totalIn]
        rw [upd_ne _ _ h]
        exact hA.netFlow a' hnatW
    · intro a' hnn
      have hnnW : ¬ Registered W.vault a' := by simpa using hnn
      have h : a' ≠ a := ne_of_unreg hg.registered hnnW
      obtain ⟨hin, hout⟩ := hA.unregisteredQuiet a' hnnW
      exact ⟨by rw [bridgeIn_totalIn, upd_ne _ _ h]; exact hin,
        by rw [bridgeIn_totalOut]; exact hout⟩
  | @donate a amt =>
    refine ⟨?_, ?_⟩
    · intro a' hnat
      rw [donate_audit, donate_bridgedOut]
      exact hA.netFlow a' (by simpa using hnat)
    · intro a' hnn
      rw [donate_audit]
      exact hA.unregisteredQuiet a' (by simpa using hnn)

theorem run_audited {e : NtvAssetId} (he : IdAssumptions e) {thisChain : Chain}
    (hc0 : thisChain ≠ 0) {W : World} (hr : Reach e thisChain empty W) :
    Audited thisChain W := by
  induction hr with
  | refl => exact empty_audited
  | @tail X Y hrx hs ih =>
    exact step_preserves_audited he hc0 hs (run_valid he hc0 hrx) ih

theorem no_inflation {e : NtvAssetId} (he : IdAssumptions e) {thisChain : Chain}
    (hc0 : thisChain ≠ 0) {W : World} (hr : Reach e thisChain empty W)
    (a : AssetId) (hnat : Native thisChain W.vault a) :
    W.audit.totalIn a ≤ W.audit.totalOut a := by
  have := (run_audited he hc0 hr).netFlow a hnat
  omega

/-! ## The two boundaries -/

/-- One native token registered, nothing bridged yet. -/
def afterRegister (e : NtvAssetId) (thisChain : Chain) (t : Address) : World :=
  { empty with vault := registerNative e thisChain empty.vault t }

lemma afterRegister_reach {e : NtvAssetId} {thisChain : Chain} {t : Address} (ht0 : t ≠ 0) :
    Reach e thisChain empty (afterRegister e thisChain t) :=
  Reach.tail Reach.refl (Step.registerNative ⟨ht0, rfl⟩)

lemma afterRegister_registered {e : NtvAssetId} {thisChain : Chain} {t : Address} (ht0 : t ≠ 0) :
    Registered (afterRegister e thisChain t).vault (e thisChain t) := by
  show Registered (setNewTokenStorage empty.vault (e thisChain t) t t thisChain) (e thisChain t)
  exact (sn_registered_self _ _ t t thisChain).mpr ht0

lemma afterRegister_native {e : NtvAssetId} {thisChain : Chain} {t : Address} :
    Native thisChain (afterRegister e thisChain t).vault (e thisChain t) := by
  show Native thisChain (setNewTokenStorage empty.vault (e thisChain t) t t thisChain)
    (e thisChain t)
  exact (sn_native_self _ _ t t thisChain thisChain).mpr rfl

@[simp] lemma afterRegister_escrowed {e : NtvAssetId} {thisChain : Chain} {t : Address}
    (a : AssetId) : (afterRegister e thisChain t).vault.escrowed a = 0 := rfl

@[simp] lemma afterRegister_bridgedOut {e : NtvAssetId} {thisChain : Chain} {t : Address}
    (a : AssetId) : (afterRegister e thisChain t).vault.bridgedOut a = 0 := rfl

/-- **THE `InsufficientChainBalance` CHECK IS LOAD-BEARING.** -/
theorem unguarded_inflow_unbacked {e : NtvAssetId} (he : IdAssumptions e) {thisChain : Chain}
    (hc0 : thisChain ≠ 0) {t : Address} (ht0 : t ≠ 0) :
    ∃ W : World, Reach e thisChain empty W ∧ Valid e thisChain W.vault
      ∧ Registered W.vault (e thisChain t)
      ∧ Native thisChain W.vault (e thisChain t)
      ∧ W.vault.escrowed (e thisChain t) = 0
      ∧ FlowInGuardUnchecked W.vault (e thisChain t) 1
      ∧ ¬ FlowInGuard thisChain W.vault (e thisChain t) 1 :=
  ⟨afterRegister e thisChain t, afterRegister_reach ht0,
    run_valid he hc0 (afterRegister_reach ht0), afterRegister_registered ht0,
    afterRegister_native, afterRegister_escrowed _, ⟨afterRegister_registered ht0⟩, by
      intro hg
      have := hg.sufficient afterRegister_native
      rw [afterRegister_bridgedOut] at this
      omega⟩

/-- The two-chain run: bridge one unit out towards `cB`, then bring one unit in
from `cA`. -/
def isolationRun (e : NtvAssetId) (thisChain : Chain) (t : Address) (cA cB : Chain) : World :=
  bridgeIn thisChain
    (bridgeOut thisChain (afterRegister e thisChain t) cB (e thisChain t) 1)
    cA (e thisChain t) 1

/-- **PER-CHAIN ISOLATION DOES NOT HOLD.** -/
theorem per_chain_isolation_fails {e : NtvAssetId} {thisChain : Chain}
    {t : Address} (ht0 : t ≠ 0) {cA cB : Chain} (hAB : cA ≠ cB) :
    Reach e thisChain empty (isolationRun e thisChain t cA cB)
      ∧ (isolationRun e thisChain t cA cB).audit.totalIn (e thisChain t)
        = (isolationRun e thisChain t cA cB).audit.totalOut (e thisChain t)
      ∧ (isolationRun e thisChain t cA cB).audit.outTo cA (e thisChain t) = 0
      ∧ (isolationRun e thisChain t cA cB).audit.innFrom cA (e thisChain t) = 1 := by
  have hreg := afterRegister_registered (e := e) (thisChain := thisChain) ht0
  have hnat := afterRegister_native (e := e) (thisChain := thisChain) (t := t)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Reach.tail (Reach.tail (afterRegister_reach ht0) (Step.bridgeOut ⟨hreg, one_ne_zero⟩))
      (Step.bridgeIn ⟨by simpa using hreg, ?_⟩)
    intro _
    rw [bridgeOut_bridgedOut_native _ _ _ _ _ hnat, upd_same, afterRegister_bridgedOut]
    omega
  · show upd _ (e thisChain t) _ (e thisChain t) = upd _ (e thisChain t) _ (e thisChain t)
    rw [upd_same, upd_same]
    rfl
  · show updCA _ cB (e thisChain t) _ cA (e thisChain t) = 0
    rw [updCA_ne _ _ (fun h => hAB h.1)]
    rfl
  · show updCA _ cA (e thisChain t) _ cA (e thisChain t) = 1
    rw [updCA_same]
    rfl

end Contracts.NativeTokenVault

/-! ## Certificates -/

namespace Proofs.NativeTokenVault

open Contracts.NativeTokenVault

theorem EmptyValid : Properties.NativeTokenVault.EmptyValid := fun _ _ => empty_valid
theorem RegisterNativeIdFresh : Properties.NativeTokenVault.RegisterNativeIdFresh :=
  fun _ he _ _ hV _ hg => registerNative_id_fresh he hV hg
theorem RegisterNativePreservesValid :
    Properties.NativeTokenVault.RegisterNativePreservesValid :=
  fun _ he _ hc0 _ hV _ hg => registerNative_preserves_valid he hc0 hV hg
theorem RegisterBridgedPreservesValid :
    Properties.NativeTokenVault.RegisterBridgedPreservesValid :=
  fun _ he _ hc0 _ hV _ _ _ _ hg => registerBridged_preserves_valid he hc0 hV hg
theorem StepPreservesValid : Properties.NativeTokenVault.StepPreservesValid :=
  fun _ he _ hc0 _ _ hs hV => step_preserves_valid he hc0 hs hV
theorem RunValid : Properties.NativeTokenVault.RunValid :=
  fun _ he _ hc0 _ hr => run_valid he hc0 hr
theorem Solvency : Properties.NativeTokenVault.Solvency :=
  fun _ he _ hc0 _ hr a => (run_valid he hc0 hr).solvent a
theorem GuardedInflowIsBacked : Properties.NativeTokenVault.GuardedInflowIsBacked :=
  fun _ _ _ hV _ _ hg hnat => guarded_inflow_is_backed hV hg hnat
theorem SurplusMonotone : Properties.NativeTokenVault.SurplusMonotone :=
  fun _ _ _ _ _ _ hs hV a => surplus_monotone hs hV a
theorem RunAudited : Properties.NativeTokenVault.RunAudited :=
  fun _ he _ hc0 _ hr => run_audited he hc0 hr
theorem LedgerIsNetFlow : Properties.NativeTokenVault.LedgerIsNetFlow :=
  fun _ he _ hc0 _ hr a hnat => (run_audited he hc0 hr).netFlow a hnat
theorem NoInflation : Properties.NativeTokenVault.NoInflation :=
  fun _ he _ hc0 _ hr a hnat => no_inflation he hc0 hr a hnat
theorem UnguardedInflowUnbacked : Properties.NativeTokenVault.UnguardedInflowUnbacked :=
  fun _ he _ hc0 _ ht0 => unguarded_inflow_unbacked he hc0 ht0
theorem PerChainIsolationFails : Properties.NativeTokenVault.PerChainIsolationFails :=
  fun _ _ _ _ _ ht0 _ _ hAB =>
    ⟨_, (per_chain_isolation_fails ht0 hAB).1, (per_chain_isolation_fails ht0 hAB).2.1,
      (per_chain_isolation_fails ht0 hAB).2.2.1, (per_chain_isolation_fails ht0 hAB).2.2.2⟩

end Proofs.NativeTokenVault
