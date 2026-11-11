import EraSpec.Contracts.NativeTokenVaultBase.Properties.RegistryAndEscrow

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

/-! ## Bounded runs: the hash assumption on the run's own pairs

The registry argument uses the id hash at exactly two kinds of input: the pair a
registration hashes, and the recorded pair of an asset already registered.
`PairsIn S` carries the second along the run, so `IdAssumptionsOn e S` is all that
is needed. -/

theorem idAssumptionsOn_of_global {e : NtvAssetId} (he : IdAssumptions e)
    (S : Set (Chain × Address)) : IdAssumptionsOn e S :=
  ⟨fun p _ q _ h => by
    obtain ⟨h1, h2⟩ := he.inj _ _ _ _ h
    exact Prod.ext h1 h2,
   fun p _ => he.nonzero p.1 p.2⟩

theorem pairsIn_univ (V : Vault) : PairsIn Set.univ V := fun _ _ => Set.mem_univ _

theorem pairsIn_empty (S : Set (Chain × Address)) : PairsIn S empty.vault :=
  fun _ hreg => absurd rfl hreg

theorem stepIn_step {e : NtvAssetId} {thisChain : Chain} {S : Set (Chain × Address)}
    {W X : World} (hs : StepIn e thisChain S W X) : Step e thisChain W X := by
  cases hs with
  | registerNative _ hg => exact Step.registerNative hg
  | registerBridged _ hg => exact Step.registerBridged hg
  | bridgeOut hg => exact Step.bridgeOut hg
  | bridgeIn hg => exact Step.bridgeIn hg
  | donate => exact Step.donate

theorem reachIn_reach {e : NtvAssetId} {thisChain : Chain} {S : Set (Chain × Address)}
    {W X : World} (hr : ReachIn e thisChain S W X) : Reach e thisChain W X := by
  induction hr with
  | refl => exact Reach.refl
  | tail _ hs ih => exact Reach.tail ih (stepIn_step hs)

theorem stepIn_mono {e : NtvAssetId} {thisChain : Chain} {S S' : Set (Chain × Address)}
    (hSS : S ⊆ S') {W X : World} (hs : StepIn e thisChain S W X) : StepIn e thisChain S' W X := by
  cases hs with
  | registerNative hm hg => exact StepIn.registerNative (hSS hm) hg
  | registerBridged hm hg => exact StepIn.registerBridged (hSS hm) hg
  | bridgeOut hg => exact StepIn.bridgeOut hg
  | bridgeIn hg => exact StepIn.bridgeIn hg
  | donate => exact StepIn.donate

theorem reachIn_mono {e : NtvAssetId} {thisChain : Chain} {S S' : Set (Chain × Address)}
    (hSS : S ⊆ S') {W X : World} (hr : ReachIn e thisChain S W X) :
    ReachIn e thisChain S' W X := by
  induction hr with
  | refl => exact ReachIn.refl
  | tail _ hs ih => exact ReachIn.tail ih (stepIn_mono hSS hs)

theorem step_stepIn_univ {e : NtvAssetId} {thisChain : Chain} {W X : World}
    (hs : Step e thisChain W X) : StepIn e thisChain Set.univ W X := by
  cases hs with
  | registerNative hg => exact StepIn.registerNative (Set.mem_univ _) hg
  | registerBridged hg => exact StepIn.registerBridged (Set.mem_univ _) hg
  | bridgeOut hg => exact StepIn.bridgeOut hg
  | bridgeIn hg => exact StepIn.bridgeIn hg
  | donate => exact StepIn.donate

/-- Each step hashes at most one pair, so it is a `StepIn` for a finite set. -/
theorem step_stepIn_finset {e : NtvAssetId} {thisChain : Chain} {W X : World}
    (hs : Step e thisChain W X) :
    ∃ S : Finset (Chain × Address), StepIn e thisChain ↑S W X := by
  cases hs with
  | @registerNative t hg =>
    exact ⟨{(thisChain, t)}, StepIn.registerNative (by simp) hg⟩
  | @registerBridged a t ot origin hg =>
    exact ⟨{(origin, ot)}, StepIn.registerBridged (by simp) hg⟩
  | bridgeOut hg => exact ⟨∅, StepIn.bridgeOut hg⟩
  | bridgeIn hg => exact ⟨∅, StepIn.bridgeIn hg⟩
  | donate => exact ⟨∅, StepIn.donate⟩

theorem reach_reachIn_finset {e : NtvAssetId} {thisChain : Chain} {W X : World}
    (hr : Reach e thisChain W X) :
    ∃ S : Finset (Chain × Address), ReachIn e thisChain ↑S W X := by
  classical
  induction hr with
  | refl => exact ⟨∅, ReachIn.refl⟩
  | tail _ hs ih =>
    obtain ⟨S₁, h₁⟩ := ih
    obtain ⟨S₂, h₂⟩ := step_stepIn_finset hs
    refine ⟨S₁ ∪ S₂, ReachIn.tail (reachIn_mono ?_ h₁) (stepIn_mono ?_ h₂)⟩
    · intro x hx
      exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_coe.mp hx))
    · intro x hx
      exact Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_coe.mp hx))

/-- **THE DERIVED ID IS FREE, under injectivity on `S`.**  As
`registerNative_id_fresh`: the taker's recorded pair is in `S` by `PairsIn`, the new
pair is in `S` by hypothesis, and injectivity on `S` identifies them. -/
theorem registerNative_id_fresh_on {e : NtvAssetId} {S : Set (Chain × Address)}
    (he : IdAssumptionsOn e S) {thisChain : Chain} {V : Vault} (hV : Valid e thisChain V)
    (hP : PairsIn S V) {t : Address} (hmem : (thisChain, t) ∈ S)
    (hg : RegisterNativeGuard V t) : ¬ Registered V (e thisChain t) := by
  intro hreg
  have hpair := he.inj _ (hP _ hreg) _ hmem (hV.idShape _ hreg).symm
  obtain ⟨hc, hot⟩ := Prod.mk.inj_iff.mp hpair
  have hnative : Native thisChain V (e thisChain t) := hc
  have htok : V.token (e thisChain t) = t := by
    rw [← hV.nativeToken _ hreg hnative, hot]
  have hinv := hV.inverse _ hreg
  rw [htok, hg.fresh] at hinv
  exact he.nonzero _ hmem hinv.symm

/-- The registry write records a pair of `S` when its pair is in `S`. -/
theorem setNewTokenStorage_pairsIn {S : Set (Chain × Address)} {V : Vault} (hP : PairsIn S V)
    {a : AssetId} {t ot : Address} {origin : Chain} (hmem : (origin, ot) ∈ S) :
    PairsIn S (setNewTokenStorage V a t ot origin) := by
  intro a' hreg
  by_cases h : a' = a
  · subst h
    rw [sn_originChain_self, sn_originToken_self]
    exact hmem
  · rw [sn_originChain_of_ne V a t ot origin h, sn_originToken_of_ne V a t ot origin h]
    exact hP a' ((sn_registered_of_ne V a t ot origin h).mp hreg)

theorem registerNative_preserves_valid_on {e : NtvAssetId} {S : Set (Chain × Address)}
    (he : IdAssumptionsOn e S) {thisChain : Chain} (hc0 : thisChain ≠ 0) {V : Vault}
    (hV : Valid e thisChain V) (hP : PairsIn S V) {t : Address} (hmem : (thisChain, t) ∈ S)
    (hg : RegisterNativeGuard V t) :
    Valid e thisChain (registerNative e thisChain V t)
      ∧ PairsIn S (registerNative e thisChain V t) :=
  ⟨setNewTokenStorage_preserves_valid hc0 hV (he.nonzero _ hmem) hg.nonzero hc0
    (registerNative_id_fresh_on he hV hP hmem hg) hg.fresh rfl (fun _ => rfl),
   setNewTokenStorage_pairsIn hP hmem⟩

theorem registerBridged_preserves_valid_on {e : NtvAssetId} {S : Set (Chain × Address)}
    (he : IdAssumptionsOn e S) {thisChain : Chain} (hc0 : thisChain ≠ 0) {V : Vault}
    (hV : Valid e thisChain V) (hP : PairsIn S V)
    {a : AssetId} {t ot : Address} {origin : Chain} (hmem : (origin, ot) ∈ S)
    (hg : RegisterBridgedGuard e thisChain V a t ot origin) :
    Valid e thisChain (registerBridged V a t ot origin)
      ∧ PairsIn S (registerBridged V a t ot origin) :=
  ⟨setNewTokenStorage_preserves_valid hc0 hV
    (by rw [hg.idChecked]; exact he.nonzero _ hmem) hg.tokenNonzero hg.originNonzero
    hg.freshId hg.freshToken hg.idChecked (fun h => absurd h hg.notNative),
   setNewTokenStorage_pairsIn hP hmem⟩

theorem stepIn_preserves_valid_on {e : NtvAssetId} {S : Set (Chain × Address)}
    (he : IdAssumptionsOn e S) {thisChain : Chain} (hc0 : thisChain ≠ 0) {W X : World}
    (hs : StepIn e thisChain S W X) (hV : Valid e thisChain W.vault) (hP : PairsIn S W.vault) :
    Valid e thisChain X.vault ∧ PairsIn S X.vault := by
  cases hs with
  | registerNative hm hg => exact registerNative_preserves_valid_on he hc0 hV hP hm hg
  | registerBridged hm hg => exact registerBridged_preserves_valid_on he hc0 hV hP hm hg
  | bridgeOut _ =>
    exact ⟨bridgeOut_preserves_valid hV, fun a h => by simpa using hP a (by simpa using h)⟩
  | bridgeIn hg =>
    exact ⟨bridgeIn_preserves_valid hV hg, fun a h => by simpa using hP a (by simpa using h)⟩
  | donate =>
    exact ⟨donate_preserves_valid hV, fun a h => by simpa using hP a (by simpa using h)⟩

theorem run_inv_on {e : NtvAssetId} {S : Set (Chain × Address)} (he : IdAssumptionsOn e S)
    {thisChain : Chain} (hc0 : thisChain ≠ 0) {W : World} (hr : ReachIn e thisChain S empty W) :
    Valid e thisChain W.vault ∧ PairsIn S W.vault := by
  induction hr with
  | refl => exact ⟨empty_valid, pairsIn_empty S⟩
  | tail _ hs ih => exact stepIn_preserves_valid_on he hc0 hs ih.1 ih.2

theorem run_valid_on {e : NtvAssetId} {S : Set (Chain × Address)} (he : IdAssumptionsOn e S)
    {thisChain : Chain} (hc0 : thisChain ≠ 0) {W : World} (hr : ReachIn e thisChain S empty W) :
    Valid e thisChain W.vault :=
  (run_inv_on he hc0 hr).1

/-! ## The flow audit -/

theorem empty_audited {thisChain : Chain} : Audited thisChain empty :=
  ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩

/-- A flow only ever touches a REGISTERED asset, which is what keeps
`unregisteredQuiet` inductive. -/
private lemma ne_of_unreg {V : Vault} {a a' : AssetId} (hreg : Registered V a)
    (hnn : ¬ Registered V a') : a' ≠ a := by
  intro h; rw [h] at hnn; exact hnn hreg

/-- The audit step, for a bounded step.  The unbounded `step_preserves_audited` is
its `S := univ` instance. -/
theorem stepIn_preserves_audited {e : NtvAssetId} {S : Set (Chain × Address)}
    (he : IdAssumptionsOn e S) {thisChain : Chain}
    (hc0 : thisChain ≠ 0) {W X : World} (hs : StepIn e thisChain S W X)
    (hV : Valid e thisChain W.vault) (hP : PairsIn S W.vault)
    (hA : Audited thisChain W) : Audited thisChain X := by
  cases hs with
  | @registerNative t hmem hg =>
    have hfresh : ¬ Registered W.vault (e thisChain t) :=
      registerNative_id_fresh_on he hV hP hmem hg
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
  | @registerBridged a t ot origin _ hg =>
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

theorem step_preserves_audited {e : NtvAssetId} (he : IdAssumptions e) {thisChain : Chain}
    (hc0 : thisChain ≠ 0) {W X : World} (hs : Step e thisChain W X)
    (hV : Valid e thisChain W.vault) (hA : Audited thisChain W) : Audited thisChain X :=
  stepIn_preserves_audited (idAssumptionsOn_of_global he Set.univ) hc0 (step_stepIn_univ hs)
    hV (pairsIn_univ _) hA

theorem run_audited_on {e : NtvAssetId} {S : Set (Chain × Address)} (he : IdAssumptionsOn e S)
    {thisChain : Chain} (hc0 : thisChain ≠ 0) {W : World} (hr : ReachIn e thisChain S empty W) :
    Audited thisChain W := by
  induction hr with
  | refl => exact empty_audited
  | @tail X Y hrx hs ih =>
    have hinv := run_inv_on he hc0 hrx
    exact stepIn_preserves_audited he hc0 hs hinv.1 hinv.2 ih

theorem no_inflation_on {e : NtvAssetId} {S : Set (Chain × Address)} (he : IdAssumptionsOn e S)
    {thisChain : Chain} (hc0 : thisChain ≠ 0) {W : World} (hr : ReachIn e thisChain S empty W)
    (a : AssetId) (hnat : Native thisChain W.vault a) :
    W.audit.totalIn a ≤ W.audit.totalOut a := by
  have := (run_audited_on he hc0 hr).netFlow a hnat
  omega

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

/-! ## Bounded runs: the boundaries, the pinned collision, and anti-vacuity -/

theorem idAssumptionsOn_singleton {e : NtvAssetId} {c : Chain} {t : Address} (h0 : e c t ≠ 0) :
    IdAssumptionsOn e {(c, t)} :=
  ⟨fun p hp q hq _ => by rw [Set.mem_singleton_iff.mp hp, Set.mem_singleton_iff.mp hq],
   fun p hp => by rw [Set.mem_singleton_iff.mp hp]; exact h0⟩

lemma afterRegister_reachIn {e : NtvAssetId} {thisChain : Chain} {S : Set (Chain × Address)}
    {t : Address} (hm : (thisChain, t) ∈ S) (ht0 : t ≠ 0) :
    ReachIn e thisChain S empty (afterRegister e thisChain t) :=
  ReachIn.tail ReachIn.refl (StepIn.registerNative hm ⟨ht0, rfl⟩)

/-- **THE `InsufficientChainBalance` CHECK IS LOAD-BEARING**, bounded. -/
theorem unguarded_inflow_unbacked_on {e : NtvAssetId} {thisChain : Chain}
    (hc0 : thisChain ≠ 0) {t : Address} (ht0 : t ≠ 0) (he0 : e thisChain t ≠ 0) :
    ∃ W : World, ReachIn e thisChain {(thisChain, t)} empty W ∧ Valid e thisChain W.vault
      ∧ Registered W.vault (e thisChain t)
      ∧ Native thisChain W.vault (e thisChain t)
      ∧ W.vault.escrowed (e thisChain t) = 0
      ∧ FlowInGuardUnchecked W.vault (e thisChain t) 1
      ∧ ¬ FlowInGuard thisChain W.vault (e thisChain t) 1 :=
  ⟨afterRegister e thisChain t, afterRegister_reachIn (Set.mem_singleton _) ht0,
    run_valid_on (idAssumptionsOn_singleton he0) hc0
      (afterRegister_reachIn (Set.mem_singleton _) ht0),
    afterRegister_registered ht0, afterRegister_native, afterRegister_escrowed _,
    ⟨afterRegister_registered ht0⟩, by
      intro hg
      have := hg.sufficient afterRegister_native
      rw [afterRegister_bridgedOut] at this
      omega⟩

/-- `isolationRun` is a bounded run: it registers one pair. -/
lemma isolationRun_reachIn {e : NtvAssetId} {thisChain : Chain} {t : Address} (ht0 : t ≠ 0)
    (cA cB : Chain) :
    ReachIn e thisChain {(thisChain, t)} empty (isolationRun e thisChain t cA cB) := by
  have hreg := afterRegister_registered (e := e) (thisChain := thisChain) ht0
  have hnat := afterRegister_native (e := e) (thisChain := thisChain) (t := t)
  refine ReachIn.tail (ReachIn.tail (afterRegister_reachIn (Set.mem_singleton _) ht0)
    (StepIn.bridgeOut ⟨hreg, one_ne_zero⟩)) (StepIn.bridgeIn ⟨by simpa using hreg, ?_⟩)
  intro _
  rw [bridgeOut_bridgedOut_native _ _ _ _ _ hnat, upd_same, afterRegister_bridgedOut]
  omega

/-- **THE DERIVED ID IS FREE, OR A PINNED COLLISION** — no hash assumption. -/
theorem registerNative_id_fresh_or_collision {e : NtvAssetId} {thisChain : Chain} {V : Vault}
    (hV : Valid e thisChain V) {t : Address} (hg : RegisterNativeGuard V t) :
    ¬ Registered V (e thisChain t)
    ∨ e thisChain t = 0
    ∨ (Registered V (e thisChain t)
        ∧ (V.originChain (e thisChain t), V.originToken (e thisChain t)) ≠ (thisChain, t)
        ∧ e (V.originChain (e thisChain t)) (V.originToken (e thisChain t)) = e thisChain t) := by
  by_cases hreg : Registered V (e thisChain t)
  · by_cases h0 : e thisChain t = 0
    · exact Or.inr (Or.inl h0)
    · refine Or.inr (Or.inr ⟨hreg, ?_, (hV.idShape _ hreg).symm⟩)
      intro hpair
      obtain ⟨hc, hot⟩ := Prod.mk.inj_iff.mp hpair
      have hnative : Native thisChain V (e thisChain t) := hc
      have htok : V.token (e thisChain t) = t := by
        rw [← hV.nativeToken _ hreg hnative, hot]
      have hinv := hV.inverse _ hreg
      rw [htok, hg.fresh] at hinv
      exact h0 hinv.symm
  · exact Or.inl hreg

/-- **A FINITE SET ADMITS AN INJECTIVE, NONZERO ENCODING.**  Number its elements
`1, 2, …, |S|`. -/
theorem idAssumptionsOn_of_card (S : Finset (Chain × Address)) (hS : S.card < UInt256.size) :
    ∃ e : NtvAssetId, IdAssumptionsOn e ↑S := by
  classical
  let f := S.equivFin
  refine ⟨fun c t => if h : (c, t) ∈ S then
      ⟨(f ⟨(c, t), h⟩).val + 1, by have := (f ⟨(c, t), h⟩).isLt; omega⟩ else 0, ?_, ?_⟩
  · rintro ⟨c₁, t₁⟩ h₁ ⟨c₂, t₂⟩ h₂ heq
    rw [Finset.mem_coe] at h₁ h₂
    simp only [dif_pos h₁, dif_pos h₂, Fin.mk.injEq, add_left_inj] at heq
    have hf : f ⟨(c₁, t₁), h₁⟩ = f ⟨(c₂, t₂), h₂⟩ := Fin.ext heq
    exact congrArg Subtype.val (f.injective hf)
  · rintro ⟨c, t⟩ h
    rw [Finset.mem_coe] at h
    simp only [dif_pos h]
    intro h0
    have := congrArg Fin.val h0
    simp at this

/-- The honest instance: the id is the token itself.  Not injective globally, but
injective (and nonzero) on any set of nonzero tokens over one chain. -/
def honestId : NtvAssetId := fun _ t => t

/-- A colliding instance: every pair gets id `1`. -/
def constId : NtvAssetId := fun _ _ => 1

/-- The two-pair set of the honest instance. -/
def honestPairs : Set (Chain × Address) := {((1 : Chain), (1 : Address)), (1, 2)}

lemma honestId_on : IdAssumptionsOn honestId honestPairs := by
  refine ⟨?_, ?_⟩
  · intro p hp q hq h
    simp only [honestPairs, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · rfl
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · rfl
  · intro p hp
    simp only [honestPairs, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl <;> decide

/-- One honest native registration of token `1` on chain `1`. -/
lemma honest_inv :
    Valid honestId 1 (afterRegister honestId 1 1).vault
      ∧ PairsIn honestPairs (afterRegister honestId 1 1).vault :=
  run_inv_on honestId_on (by decide)
    (afterRegister_reachIn (by simp [honestPairs]) (by decide))

lemma honest_guard2 : RegisterNativeGuard (afterRegister honestId 1 1).vault 2 := by
  refine ⟨by decide, ?_⟩
  show (setNewTokenStorage empty.vault (honestId 1 1) 1 1 1).assetOf 2 = 0
  rw [sn_assetOf_of_ne _ _ _ _ _ (by decide)]
  rfl

theorem register_native_on_satisfiable :
    ∃ (e : NtvAssetId) (S : Set (Chain × Address)) (thisChain : Chain) (V : Vault)
      (t : Address),
      IdAssumptionsOn e S ∧ thisChain ≠ 0 ∧ Valid e thisChain V ∧ PairsIn S V
      ∧ (∃ a, Registered V a) ∧ (thisChain, t) ∈ S ∧ RegisterNativeGuard V t :=
  ⟨honestId, honestPairs, 1, (afterRegister honestId 1 1).vault, 2, honestId_on, by decide,
    honest_inv.1, honest_inv.2, ⟨_, afterRegister_registered (by decide)⟩,
    by simp [honestPairs], honest_guard2⟩

theorem register_native_collision_not_tautology :
    ∃ (e : NtvAssetId) (thisChain : Chain) (V : Vault) (t : Address),
      Valid e thisChain V ∧ (∃ a, Registered V a) ∧ RegisterNativeGuard V t
      ∧ ¬ (e thisChain t = 0)
      ∧ ¬ (Registered V (e thisChain t)
            ∧ (V.originChain (e thisChain t), V.originToken (e thisChain t)) ≠ (thisChain, t)
            ∧ e (V.originChain (e thisChain t)) (V.originToken (e thisChain t))
                = e thisChain t) := by
  refine ⟨honestId, 1, (afterRegister honestId 1 1).vault, 2, honest_inv.1,
    ⟨_, afterRegister_registered (by decide)⟩, honest_guard2, by decide, ?_⟩
  rintro ⟨hreg, _⟩
  apply hreg
  show (setNewTokenStorage empty.vault (honestId 1 1) 1 1 1).token (honestId 1 2) = 0
  rw [sn_token_of_ne _ _ _ _ _ (by decide)]
  rfl

theorem register_native_collision_reachable :
    ∃ (e : NtvAssetId) (thisChain : Chain) (V : Vault) (t : Address),
      Valid e thisChain V ∧ RegisterNativeGuard V t ∧ Registered V (e thisChain t)
      ∧ (V.originChain (e thisChain t), V.originToken (e thisChain t)) ≠ (thisChain, t)
      ∧ e (V.originChain (e thisChain t)) (V.originToken (e thisChain t))
          = e thisChain t := by
  have hon : IdAssumptionsOn constId {((1 : Chain), (1 : Address))} :=
    idAssumptionsOn_singleton (by decide)
  have hreach := afterRegister_reachIn (e := constId) (Set.mem_singleton ((1 : Chain), (1 : Address)))
    (by decide)
  refine ⟨constId, 1, (afterRegister constId 1 1).vault, 2,
    run_valid_on hon (by decide) hreach, ?_, afterRegister_registered (by decide), ?_, rfl⟩
  · refine ⟨by decide, ?_⟩
    show (setNewTokenStorage empty.vault (constId 1 1) 1 1 1).assetOf 2 = 0
    rw [sn_assetOf_of_ne _ _ _ _ _ (by decide)]
    rfl
  · show ((setNewTokenStorage empty.vault (constId 1 1) 1 1 1).originChain (constId 1 1),
        (setNewTokenStorage empty.vault (constId 1 1) 1 1 1).originToken (constId 1 1))
        ≠ ((1 : Chain), (2 : Address))
    rw [sn_originChain_self, sn_originToken_self]
    decide

theorem run_on_satisfiable :
    ∃ (e : NtvAssetId) (S : Set (Chain × Address)) (thisChain : Chain) (W : World),
      IdAssumptionsOn e S ∧ thisChain ≠ 0 ∧ ReachIn e thisChain S empty W
      ∧ ∃ a, Registered W.vault a ∧ Native thisChain W.vault a
        ∧ W.audit.totalOut a ≠ 0 ∧ W.audit.totalIn a ≠ 0 := by
  have hreg := afterRegister_registered (e := honestId) (thisChain := 1) (t := 1) (by decide)
  have hnat := afterRegister_native (e := honestId) (thisChain := 1) (t := 1)
  refine ⟨honestId, {(1, 1)}, 1, isolationRun honestId 1 1 1 2,
    idAssumptionsOn_singleton (by decide), by decide, isolationRun_reachIn (by decide) 1 2,
    honestId 1 1, ?_, ?_, ?_, ?_⟩
  · exact (bridgeIn_registered _ _ _ _ _).mpr ((bridgeOut_registered _ _ _ _ _).mpr hreg)
  · exact (bridgeIn_native _ _ _ _ _).mpr ((bridgeOut_native _ _ _ _ _).mpr hnat)
  · rw [isolationRun, bridgeIn_totalOut, bridgeOut_totalOut, upd_same]; omega
  · rw [isolationRun, bridgeIn_totalIn, upd_same]; omega

theorem register_bridged_on_satisfiable :
    ∃ (e : NtvAssetId) (S : Set (Chain × Address)) (thisChain : Chain) (V : Vault)
      (a : AssetId) (t ot : Address) (origin : Chain),
      IdAssumptionsOn e S ∧ thisChain ≠ 0 ∧ Valid e thisChain V ∧ PairsIn S V
      ∧ (origin, ot) ∈ S ∧ RegisterBridgedGuard e thisChain V a t ot origin :=
  ⟨honestId, {(2, 5)}, 1, empty.vault, honestId 2 5, 7, 5, 2,
    idAssumptionsOn_singleton (by decide), by decide, empty_valid, pairsIn_empty _,
    Set.mem_singleton _,
    ⟨by decide, by decide, rfl, by decide, rfl, fun h => h rfl⟩⟩

end Contracts.NativeTokenVault

/-! ## Certificates -/

namespace Contracts.NativeTokenVault

theorem EmptyValid : Properties.EmptyValid := fun _ _ => empty_valid
theorem RegisterNativeIdFresh : Properties.RegisterNativeIdFresh :=
  fun _ he _ _ hV _ hg => registerNative_id_fresh he hV hg
theorem RegisterNativePreservesValid :
    Properties.RegisterNativePreservesValid :=
  fun _ he _ hc0 _ hV _ hg => registerNative_preserves_valid he hc0 hV hg
theorem RegisterBridgedPreservesValid :
    Properties.RegisterBridgedPreservesValid :=
  fun _ he _ hc0 _ hV _ _ _ _ hg => registerBridged_preserves_valid he hc0 hV hg
theorem StepPreservesValid : Properties.StepPreservesValid :=
  fun _ he _ hc0 _ _ hs hV => step_preserves_valid he hc0 hs hV
theorem RunValid : Properties.RunValid :=
  fun _ he _ hc0 _ hr => run_valid he hc0 hr
theorem Solvency : Properties.Solvency :=
  fun _ he _ hc0 _ hr a => (run_valid he hc0 hr).solvent a
theorem GuardedInflowIsBacked : Properties.GuardedInflowIsBacked :=
  fun _ _ _ hV _ _ hg hnat => guarded_inflow_is_backed hV hg hnat
theorem SurplusMonotone : Properties.SurplusMonotone :=
  fun _ _ _ _ _ _ hs hV a => surplus_monotone hs hV a
theorem RunAudited : Properties.RunAudited :=
  fun _ he _ hc0 _ hr => run_audited he hc0 hr
theorem LedgerIsNetFlow : Properties.LedgerIsNetFlow :=
  fun _ he _ hc0 _ hr a hnat => (run_audited he hc0 hr).netFlow a hnat
theorem NoInflation : Properties.NoInflation :=
  fun _ he _ hc0 _ hr a hnat => no_inflation he hc0 hr a hnat
theorem UnguardedInflowUnbacked : Properties.UnguardedInflowUnbacked :=
  fun _ he _ hc0 _ ht0 => unguarded_inflow_unbacked he hc0 ht0
theorem PerChainIsolationFails : Properties.PerChainIsolationFails :=
  fun _ _ _ ht0 _ _ hAB =>
    ⟨_, (per_chain_isolation_fails ht0 hAB).1, (per_chain_isolation_fails ht0 hAB).2.1,
      (per_chain_isolation_fails ht0 hAB).2.2.1, (per_chain_isolation_fails ht0 hAB).2.2.2⟩


/-- Pigeonhole: no map `UInt256 → UInt256 → UInt256` is injective on pairs. -/
theorem not_pair_inj (f : UInt256 → UInt256 → UInt256)
    (hinj : ∀ a b c d : UInt256, f a b = f c d → a = c ∧ b = d) : False := by
  have hf : Function.Injective (fun p : UInt256 × UInt256 => f p.1 p.2) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ he
    obtain ⟨rfl, rfl⟩ := hinj a b c d he
    rfl
  have hc := Fintype.card_le_of_injective _ hf
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  have hpos : 1 < UInt256.size := by decide
  nlinarith

theorem IdAssumptionsUnsatisfiable : Properties.IdAssumptionsUnsatisfiable :=
  fun e hA => not_pair_inj e hA.inj

/-! ### Repaired forms -/

theorem IdAssumptionsOnSatisfiable : Properties.IdAssumptionsOnSatisfiable :=
  idAssumptionsOn_of_card
theorem IdAssumptionsOnOfGlobal : Properties.IdAssumptionsOnOfGlobal :=
  fun _ he S => idAssumptionsOn_of_global he S
theorem ReachInIsReach : Properties.ReachInIsReach :=
  fun _ _ _ _ _ hr => reachIn_reach hr
theorem ReachCoveredByFinitePairs : Properties.ReachCoveredByFinitePairs :=
  fun _ _ _ _ hr => reach_reachIn_finset hr
theorem RegisterNativeIdFreshOn : Properties.RegisterNativeIdFreshOn :=
  fun _ _ he _ _ hV hP _ hm hg => registerNative_id_fresh_on he hV hP hm hg
theorem RegisterNativeIdFreshOrCollision : Properties.RegisterNativeIdFreshOrCollision :=
  fun _ _ _ hV _ hg => registerNative_id_fresh_or_collision hV hg
theorem RegisterNativeCollisionNotTautology : Properties.RegisterNativeCollisionNotTautology :=
  register_native_collision_not_tautology
theorem RegisterNativeCollisionReachable : Properties.RegisterNativeCollisionReachable :=
  register_native_collision_reachable
theorem RegisterNativePreservesValidOn : Properties.RegisterNativePreservesValidOn :=
  fun _ _ he _ hc0 _ hV hP _ hm hg => registerNative_preserves_valid_on he hc0 hV hP hm hg
theorem RegisterBridgedPreservesValidOn : Properties.RegisterBridgedPreservesValidOn :=
  fun _ _ he _ hc0 _ hV hP _ _ _ _ hm hg =>
    registerBridged_preserves_valid_on he hc0 hV hP hm hg
theorem StepInPreservesValidOn : Properties.StepInPreservesValidOn :=
  fun _ _ he _ hc0 _ _ hs hV hP => stepIn_preserves_valid_on he hc0 hs hV hP
theorem RunValidOn : Properties.RunValidOn :=
  fun _ _ he _ hc0 _ hr => run_valid_on he hc0 hr
theorem SolvencyOn : Properties.SolvencyOn :=
  fun _ _ he _ hc0 _ hr a => (run_valid_on he hc0 hr).solvent a
theorem SurplusMonotoneNoHash : Properties.SurplusMonotoneNoHash :=
  fun _ _ _ _ hs hV a => surplus_monotone hs hV a
theorem RunAuditedOn : Properties.RunAuditedOn :=
  fun _ _ he _ hc0 _ hr => run_audited_on he hc0 hr
theorem LedgerIsNetFlowOn : Properties.LedgerIsNetFlowOn :=
  fun _ _ he _ hc0 _ hr a hnat => (run_audited_on he hc0 hr).netFlow a hnat
theorem NoInflationOn : Properties.NoInflationOn :=
  fun _ _ he _ hc0 _ hr a hnat => no_inflation_on he hc0 hr a hnat
theorem UnguardedInflowUnbackedOn : Properties.UnguardedInflowUnbackedOn :=
  fun _ _ hc0 _ ht0 he0 => unguarded_inflow_unbacked_on hc0 ht0 he0
theorem RunOnSatisfiable : Properties.RunOnSatisfiable := run_on_satisfiable
theorem RegisterNativeOnSatisfiable : Properties.RegisterNativeOnSatisfiable :=
  register_native_on_satisfiable
theorem RegisterBridgedOnSatisfiable : Properties.RegisterBridgedOnSatisfiable :=
  register_bridged_on_satisfiable

end Contracts.NativeTokenVault
