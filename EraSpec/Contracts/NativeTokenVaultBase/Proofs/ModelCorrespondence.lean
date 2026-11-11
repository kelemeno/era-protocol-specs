import EraSpec.Contracts.NativeTokenVaultBase.Properties.ModelCorrespondence
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.Initialization
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.RepresentationPreparation
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.RegistryAndEscrow
import EraSpec.Contracts.BridgedStandardERC20.Proofs.Model

/-!
# Proofs: how the two native-token-vault models relate

The registration results go through the representation model's public frame and
consistency theorems (`registration_registry_frame`,
`registration_establishes_representation`, `registration_initial_fields`), so the
correspondence is checked against what that model proves about itself, not against a
re-derivation.  The registry side reuses `registerBridged_preserves_valid_on`.  The
countermodels are explicit small instances with the toy encoding `c ↦ c + 1`, which
is injective and nonzero on every pair set they use.
-/

namespace Contracts.NativeTokenVaultBase

open NativeTokenVault (Chain Vault World NtvAssetId Valid IdAssumptionsOn PairsIn
  RegisterBridgedGuard)

/-! ## `widen` -/

theorem widen_val (t : Address) : (widen t).val = t.val := rfl

theorem widen_inj {t t' : Address} : widen t = widen t' ↔ t = t' := by
  constructor
  · intro h
    exact Fin.ext (by simpa [widen_val] using congrArg Fin.val h)
  · rintro rfl; rfl

theorem widen_zero : widen 0 = 0 := by
  apply Fin.ext
  rw [widen_val]
  rfl

theorem widen_eq_zero {t : Address} : widen t = 0 ↔ t = 0 := by
  rw [← widen_zero, widen_inj]

/-! ## The map correspondence across the registry write -/

/-- The registry write of `(A, T)` on the registry side corresponds to any
representation-side registry that changes exactly the slots `A` and `T` to each other. -/
theorem registryCorr_write {R R' : Registry} {V : Vault} (h : RegistryCorr R V)
    {A : UInt256} {T : Address} (ot : NativeTokenVault.Address) (oc : Chain)
    (hfa : ∀ a, a ≠ A → R'.tokenForAsset a = R.tokenForAsset a)
    (hA : R'.tokenForAsset A = T)
    (hft : ∀ t, t ≠ T → R'.assetForToken t = R.assetForToken t)
    (hT : R'.assetForToken T = A) :
    RegistryCorr R' (NativeTokenVault.setNewTokenStorage V A (widen T) ot oc) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    by_cases ha : a = A
    · subst ha
      rw [NativeTokenVault.sn_token_self, hA]
    · rw [NativeTokenVault.sn_token_of_ne V A (widen T) ot oc ha, hfa a ha, h.token]
  · intro t
    by_cases ht : t = T
    · subst ht
      rw [NativeTokenVault.sn_assetOf_self, hT]
    · rw [NativeTokenVault.sn_assetOf_of_ne V A (widen T) ot oc
        (fun h' => ht (widen_inj.mp h')), hft t ht, h.assetOf]
  · intro w hw
    rw [NativeTokenVault.sn_assetOf_of_ne V A (widen T) ot oc (fun h' => hw T h'.symm),
      h.assetOfWide w hw]

theorem registryCorr_install {R : Registry} {V : Vault} (h : RegistryCorr R V)
    (A : UInt256) (T : Address) (ot : NativeTokenVault.Address) (oc : Chain) :
    RegistryCorr (installRegistry R A T) (NativeTokenVault.setNewTokenStorage V A (widen T) ot oc) :=
  registryCorr_write h ot oc (fun _ ha => Function.update_of_ne ha _ _) (Function.update_self _ _ _)
    (fun _ ht => Function.update_of_ne ht _ _) (Function.update_self _ _ _)

theorem registryCorr_empty :
    RegistryCorr ⟨fun _ => 0, fun _ => 0⟩ NativeTokenVault.empty.vault :=
  ⟨fun _ => widen_zero.symm, fun _ => rfl, fun _ _ => rfl⟩

/-! ## Registration -/

variable {Accounting : Type}

/-- What a successful representation registration does to the overlapping state, read
off the representation model's own public theorems. -/
theorem registration_overlap {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerRepresentation hooks s origin = some out) :
    out.state.config = s.config ∧ out.state.token.config.originToken = origin ∧
    (∀ a, a ≠ s.config.assetId →
      out.state.registry.tokenForAsset a = s.registry.tokenForAsset a) ∧
    out.state.registry.tokenForAsset s.config.assetId = s.config.tokenAddress ∧
    (∀ t, t ≠ s.config.tokenAddress →
      out.state.registry.assetForToken t = s.registry.assetForToken t) ∧
    out.state.registry.assetForToken s.config.tokenAddress = s.config.assetId := by
  obtain ⟨hc, _hp, hfa, hft⟩ := registration_registry_frame h
  have hr := registration_establishes_representation h
  have ho := (registration_initial_fields h).1
  unfold Properties.registration_establishes_representation RepresentationConsistent at hr
  rw [hc] at hr
  exact ⟨hc, ho, hfa, hr.2.2.1, hft, hr.2.2.2⟩

theorem registrationEffectCorresponds {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    {thisChain : Chain} {V : Vault} (hc : CorrPre s thisChain V)
    (h : registerRepresentation hooks s origin = some out) :
    Corr out.state thisChain (correspondingRegistration s origin V) := by
  obtain ⟨hcfg, ho, hfa, hA, hft, hT⟩ := registration_overlap h
  refine ⟨?_, ?_, ?_⟩
  · rw [hcfg]; exact hc.1
  · exact registryCorr_write hc.2 _ _ hfa hA hft hT
  · intro _
    rw [hcfg, ho]
    exact ⟨NativeTokenVault.sn_originChain_self _ _ _ _ _,
      NativeTokenVault.sn_originToken_self _ _ _ _ _⟩

theorem registrationGuardGap {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    {e : NtvAssetId} {thisChain : Chain} {V : Vault} (hc : CorrPre s thisChain V)
    (h : registerFreshBranch hooks s origin = some out)
    (henc : hooks.assetIdFor s.config.originChainId origin =
      e s.config.originChainId (widen origin)) :
    RegisterBridgedGuard e thisChain V s.config.assetId (widen s.config.tokenAddress)
        (widen origin) s.config.originChainId ↔ RegistryOnlyGuards s := by
  obtain ⟨hfree, hreg⟩ := fresh_registration_preconditions h
  obtain ⟨hid, hnn⟩ := registration_checks_asset hreg
  constructor
  · intro g
    refine ⟨fun h0 => g.tokenNonzero (by rw [h0, widen_zero]), ?_, g.originNonzero⟩
    rw [← hc.2.assetOf]
    exact g.freshToken
  · intro g
    refine ⟨?_, g.originNonzero, ?_, ?_, ?_, ?_⟩
    · rw [hc.1]; exact hnn
    · rw [hid, henc]
    · exact fun h0 => g.tokenNonzero (widen_eq_zero.mp h0)
    · rw [hc.2.assetOf]; exact g.freshToken
    · intro hr
      apply hr
      rw [hc.2.token, hfree, widen_zero]

theorem registrationIsRegistryStep {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    {e : NtvAssetId} {thisChain : Chain} {W : World} (hc : CorrPre s thisChain W.vault)
    (h : registerFreshBranch hooks s origin = some out)
    (henc : hooks.assetIdFor s.config.originChainId origin =
      e s.config.originChainId (widen origin))
    (hg : RegistryOnlyGuards s) :
    NativeTokenVault.Step e thisChain W
        { W with vault := correspondingRegistration s origin W.vault }
      ∧ Corr out.state thisChain (correspondingRegistration s origin W.vault) :=
  ⟨NativeTokenVault.Step.registerBridged ((registrationGuardGap hc h henc).mpr hg),
   registrationEffectCorresponds hc (fresh_registration_preconditions h).2⟩

theorem registrationPreservesValidOn {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    {e : NtvAssetId} {S : Set (Chain × NativeTokenVault.Address)} {thisChain : Chain}
    {V : Vault} (he : IdAssumptionsOn e S) (hc0 : thisChain ≠ 0) (hV : Valid e thisChain V)
    (hP : PairsIn S V) (hmem : (s.config.originChainId, widen origin) ∈ S)
    (hc : CorrPre s thisChain V) (h : registerFreshBranch hooks s origin = some out)
    (henc : hooks.assetIdFor s.config.originChainId origin =
      e s.config.originChainId (widen origin))
    (hg : RegistryOnlyGuards s) :
    Valid e thisChain (correspondingRegistration s origin V)
      ∧ PairsIn S (correspondingRegistration s origin V)
      ∧ Corr out.state thisChain (correspondingRegistration s origin V) := by
  obtain ⟨hv, hp⟩ := NativeTokenVault.registerBridged_preserves_valid_on he hc0 hV hP hmem
    ((registrationGuardGap hc h henc).mpr hg)
  exact ⟨hv, hp, registrationEffectCorresponds hc (fresh_registration_preconditions h).2⟩

/-! ## The burn path -/

/-- The successful `prepare` path, unfolded (the representation model's own unfolding
is private to its proof module). -/
private theorem prepare_view' {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} {out : Result Accounting} (h : prepare hooks s r = some out) :
    InScope s r ∧ EntryAllowed s r ∧
    ∃ accounted burned metadata,
      BridgedStandardERC20.burn s.token s.config.vault r.depositor r.data.amount = some burned ∧
      out = ⟨{ s with token := burned, accounting := accounted }, mintData r burned metadata⟩ := by
  unfold prepare at h
  split at h
  · rename_i hg
    cases ha : hooks.account s.accounting s.token r.destinationChain r.assetId r.data.amount with
    | none => simp only [ha, reduceCtorEq] at h
    | some accounted =>
      simp only [ha] at h
      split at h
      · cases hb : BridgedStandardERC20.burn s.token s.config.vault r.depositor r.data.amount with
        | none => simp only [hb, reduceCtorEq] at h
        | some burned =>
          simp only [hb] at h
          split at h
          · cases hm : hooks.metadata burned s.config.originChainId with
            | none => simp only [hm, reduceCtorEq] at h
            | some metadata =>
              simp only [hm] at h
              exact ⟨hg.1, hg.2, accounted, burned, metadata, rfl, (Option.some.inj h).symm⟩
          · cases h
      · cases h
  · cases h

private theorem burn_config {t burned : BridgedStandardERC20.State}
    {caller owner : Address} {amount : UInt256}
    (h : BridgedStandardERC20.burn t caller owner amount = some burned) :
    burned.config = t.config := by
  unfold BridgedStandardERC20.burn at h
  split at h
  · cases h; rfl
  · cases h

theorem preparationIsForeignBridgeOut {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} {out : Result Accounting} (e : NtvAssetId) {thisChain : Chain} {W : World}
    (hc : Corr s thisChain W.vault) (hr : RepresentationConsistent s)
    (h : prepare hooks s r = some out) :
    NativeTokenVault.Step e thisChain W
        (NativeTokenVault.bridgeOut thisChain W r.destinationChain r.assetId r.data.amount.val)
      ∧ ¬ NativeTokenVault.Native thisChain W.vault r.assetId
      ∧ (NativeTokenVault.bridgeOut thisChain W r.destinationChain r.assetId
          r.data.amount.val).vault = W.vault
      ∧ Corr out.state thisChain W.vault := by
  obtain ⟨hs, he, accounted, burned, metadata, hb, rfl⟩ := prepare_view' h
  -- the request's asset is the tracked one: reverse-map check plus consistency
  have hasset : r.assetId = s.config.assetId := by
    have hrev := he.2.2.2.2.1
    rw [hs.2.2.2.2, hr.2.2.2] at hrev
    exact hrev.symm
  have hreg : NativeTokenVault.Registered W.vault r.assetId := by
    show W.vault.token r.assetId ≠ 0
    rw [hasset, hc.registry.token, hr.2.2.1]
    exact fun h0 => hs.2.1 (widen_eq_zero.mp h0)
  have hforeign : ¬ NativeTokenVault.Native thisChain W.vault r.assetId := by
    show ¬ W.vault.originChain r.assetId = thisChain
    have ho := (hc.tracked (hasset ▸ hreg)).1
    rw [hasset, ho, hc.chain]
    exact hs.2.2.2.1
  have hamt : r.data.amount.val ≠ 0 := fun h0 => he.2.2.2.2.2 (Fin.ext h0)
  have hvault : (NativeTokenVault.bridgeOut thisChain W r.destinationChain r.assetId
      r.data.amount.val).vault = W.vault := by
    simp [NativeTokenVault.bridgeOut, ite_eq_right hforeign]
  refine ⟨NativeTokenVault.Step.bridgeOut ⟨hreg, hamt⟩, hforeign, hvault, ?_⟩
  refine ⟨hc.chain, hc.registry, ?_⟩
  intro hreg'
  have := hc.tracked hreg'
  simp only [burn_config hb]
  exact this

/-! ## The invariants -/

theorem validRegistryHalvesAgree {e : NtvAssetId} {thisChain : Chain} {V : Vault}
    {R : Registry} (hV : Valid e thisChain V) (hc : RegistryCorr R V)
    (a : UInt256) (t : Address) :
    (R.tokenForAsset a = t ∧ t ≠ 0) ↔ (R.assetForToken t = a ∧ a ≠ 0) := by
  constructor
  · rintro ⟨hta, ht0⟩
    have hreg : NativeTokenVault.Registered V a := by
      show V.token a ≠ 0
      rw [hc.token, hta]
      exact fun h0 => ht0 (widen_eq_zero.mp h0)
    refine ⟨?_, fun h0 => hV.zeroUnregistered (h0 ▸ hreg)⟩
    have hinv := hV.inverse a hreg
    rw [hc.token, hta, hc.assetOf] at hinv
    exact hinv
  · rintro ⟨hat, ha0⟩
    have hne : V.assetOf (widen t) ≠ 0 := by rw [hc.assetOf, hat]; exact ha0
    have htok := hV.tokenOfAsset (widen t) hne
    rw [hc.assetOf, hat, hc.token] at htok
    refine ⟨widen_inj.mp htok, ?_⟩
    rintro rfl
    apply hne
    rw [widen_zero]
    exact hV.zeroTokenFree

/-! ## Concrete instances

All on chain `1`, with the toy encoding `(c, t) ↦ c + 1`.  Each pair set used below
has pairwise distinct chain components and no chain `-1`, so the toy encoding is
injective and nonzero on it (`toyId_on`). -/

/-- The toy asset-id encoding. -/
def toyId : NtvAssetId := fun c _ => c + 1

theorem toyId_on {S : Set (Chain × NativeTokenVault.Address)}
    (hinj : ∀ p ∈ S, ∀ q ∈ S, p.1 = q.1 → p = q) (hnz : ∀ p ∈ S, p.1 + 1 ≠ 0) :
    IdAssumptionsOn toyId S :=
  ⟨fun p hp q hq h => hinj p hp q hq (add_right_cancel h), fun p hp => hnz p hp⟩

/-- Registration hooks agreeing with `toyId`, deploying at `deployed`, with metadata
decoding and the tracker succeeding. -/
def toyHooks (deployed : Address) : RegistrationHooks Unit :=
  ⟨fun c _ => c + 1, fun _ _ => some deployed, true, fun acc _ _ _ _ => some acc⟩

/-- Vault and router `1`, base asset `0`. -/
def toyConfig (token : Address) (asset chain originChain : UInt256) : Config :=
  ⟨1, 1, token, asset, 0, chain, originChain⟩

/-- A fresh-branch registration with the toy hooks succeeds whenever the forward slot
is free, the origin chain is not this chain, and the origin token is nonzero. -/
theorem toy_registration (R : Registry) (token origin : Address) (chain oc : UInt256)
    (hfree : R.tokenForAsset (oc + 1) = 0) (hnn : oc ≠ chain) (ho : origin ≠ 0) :
    ∃ out, registerFreshBranch (toyHooks token)
      ⟨toyConfig token (oc + 1) chain oc, R, false, ()⟩ origin = some out := by
  have hb : registerFreshBranch (toyHooks token) ⟨toyConfig token (oc + 1) chain oc, R, false, ()⟩
      origin = registerRepresentation (toyHooks token)
        ⟨toyConfig token (oc + 1) chain oc, R, false, ()⟩ origin := ite_eq_left hfree
  rw [hb]
  exact registration_enabled (hooks := toyHooks token)
    (s := ⟨toyConfig token (oc + 1) chain oc, R, false, ()⟩) (accounting := ())
    rfl hnn ho rfl rfl rfl

/-- The registry vault holding one native token `n`, under `toyId` on chain `1`. -/
def nativeVault (n : Address) : Vault :=
  NativeTokenVault.registerNative toyId 1 NativeTokenVault.empty.vault (widen n)

/-- The representation-side maps of `nativeVault n`. -/
def nativeRegistry (n : Address) : Registry :=
  installRegistry ⟨fun _ => 0, fun _ => 0⟩ (toyId 1 (widen n)) n

theorem nativeRegistry_corr (n : Address) : RegistryCorr (nativeRegistry n) (nativeVault n) :=
  registryCorr_install registryCorr_empty _ _ _ _

theorem nativeVault_valid {S : Set (Chain × NativeTokenVault.Address)} (he : IdAssumptionsOn toyId S)
    {n : Address} (hn : n ≠ 0) (hmem : ((1 : Chain), widen n) ∈ S) :
    Valid toyId 1 (nativeVault n) ∧ PairsIn S (nativeVault n) :=
  NativeTokenVault.registerNative_preserves_valid_on he (by decide)
    NativeTokenVault.empty_valid (NativeTokenVault.pairsIn_empty S) hmem
    ⟨fun h0 => hn (widen_eq_zero.mp h0), rfl⟩

theorem nativeVault_registered (n : Address) (hn : n ≠ 0) :
    NativeTokenVault.Registered (nativeVault n) (1 + 1) := by
  show (nativeVault n).token (1 + 1) ≠ 0
  have h := NativeTokenVault.sn_token_self NativeTokenVault.empty.vault (toyId 1 (widen n))
    (widen n) (widen n) 1
  unfold nativeVault
  rw [NativeTokenVault.rn_as_sn]
  exact h ▸ fun h0 => hn (widen_eq_zero.mp h0)

/-- The two-pair set `{(c₁, t₁), (c₂, t₂)}` with distinct chains satisfies the toy
hash premise. -/
theorem toyId_on_pair {c₁ c₂ : Chain} {t₁ t₂ : NativeTokenVault.Address} (hc : c₁ ≠ c₂)
    (h₁ : c₁ + 1 ≠ 0) (h₂ : c₂ + 1 ≠ 0) :
    IdAssumptionsOn toyId {(c₁, t₁), (c₂, t₂)} := by
  apply toyId_on
  · rintro p (rfl | rfl) q (rfl | rfl) h
    · rfl
    · exact absurd h hc
    · exact absurd h.symm hc
    · rfl
  · rintro p (rfl | rfl)
    · exact h₁
    · exact h₂

theorem toyId_on_single {c : Chain} {t : NativeTokenVault.Address} (h : c + 1 ≠ 0) :
    IdAssumptionsOn toyId {(c, t)} := by
  apply toyId_on
  · rintro p rfl q rfl _; rfl
  · rintro p rfl; exact h

/-! ### Rebinding a live token -/

/-- The representation state: native token `5` registered as asset `1 + 1`; the new
asset `2 + 1` (origin chain `2`) is to be deployed at `5`. -/
def rebindState : RegistrationState Unit := ⟨toyConfig 5 (2 + 1) 1 2, nativeRegistry 5, false, ()⟩

theorem nativeRegistry_token_ne (n : Address) {a : UInt256} (ha : a ≠ 1 + 1) :
    (nativeRegistry n).tokenForAsset a = 0 := by
  show Function.update (fun _ => (0 : Address)) (toyId 1 (widen n)) n a = 0
  exact Function.update_of_ne ha _ _

theorem nativeRegistry_asset_self (n : Address) : (nativeRegistry n).assetForToken n = 1 + 1 := by
  show Function.update (fun _ => (0 : UInt256)) n (toyId 1 (widen n)) n = 1 + 1
  exact Function.update_self _ _ _

theorem nativeRegistry_asset_ne (n : Address) {t : Address} (ht : t ≠ n) :
    (nativeRegistry n).assetForToken t = 0 := by
  show Function.update (fun _ => (0 : UInt256)) n (toyId 1 (widen n)) t = 0
  exact Function.update_of_ne ht _ _

theorem nativeVault_token (n : Address) : (nativeVault n).token (1 + 1) = widen n :=
  NativeTokenVault.sn_token_self NativeTokenVault.empty.vault (toyId 1 (widen n)) (widen n)
    (widen n) 1

theorem repRegistrationRebindsLiveToken : Properties.RepRegistrationRebindsLiveToken := by
  have he : IdAssumptionsOn toyId {((1 : Chain), widen 5), ((2 : Chain), widen 7)} :=
    toyId_on_pair (by decide) (by decide) (by decide)
  obtain ⟨hv, hp⟩ := nativeVault_valid he (n := 5) (by decide) (Or.inl rfl)
  have hfree : (nativeRegistry 5).tokenForAsset (2 + 1) = 0 :=
    nativeRegistry_token_ne 5 (by decide)
  obtain ⟨out, hout⟩ := toy_registration (nativeRegistry 5) 5 7 1 2 hfree (by decide) (by decide)
  have hc : CorrPre rebindState 1 (nativeVault 5) := ⟨rfl, nativeRegistry_corr 5⟩
  have hbound : (nativeRegistry 5).assetForToken 5 = 1 + 1 := nativeRegistry_asset_self 5
  have hne : (1 + 1 : UInt256) ≠ 2 + 1 := by decide
  -- the live asset `1 + 1` still points at `5`, but `5` now points at `2 + 1`
  have htok : (correspondingRegistration rebindState 7 (nativeVault 5)).token (1 + 1) = widen 5 := by
    show (NativeTokenVault.setNewTokenStorage (nativeVault 5) (2 + 1) (widen 5) (widen 7) 2).token
      (1 + 1) = widen 5
    rw [NativeTokenVault.sn_token_of_ne _ _ _ _ _ hne]
    exact nativeVault_token 5
  have hnew : (correspondingRegistration rebindState 7 (nativeVault 5)).assetOf (widen 5) = 2 + 1 :=
    NativeTokenVault.sn_assetOf_self _ _ _ _ _
  refine ⟨toyId, _, 1, nativeVault 5, toyHooks 5, rebindState, 7, out, 1 + 1, he, by decide, hv, hp,
    Or.inr rfl, hc, hout, rfl, by decide, by decide, hne, nativeVault_registered 5 (by decide),
    nativeVault_token 5, ?_, ?_, htok, hnew, ?_⟩
  · exact registration_establishes_wellformed (fresh_registration_preconditions hout).2
  · intro g
    have := ((registrationGuardGap hc hout rfl).mp g).freshToken
    change (nativeRegistry 5).assetForToken 5 = 0 at this
    rw [hbound] at this
    exact absurd this (by decide)
  · intro hV'
    have hreg : NativeTokenVault.Registered (correspondingRegistration rebindState 7 (nativeVault 5))
        (1 + 1) := by
      show (correspondingRegistration rebindState 7 (nativeVault 5)).token (1 + 1) ≠ 0
      rw [htok]; decide
    have hinv := hV'.inverse _ hreg
    rw [htok, hnew] at hinv
    exact absurd hinv (by decide)

/-! ### Origin chain zero -/

theorem repRegistrationAcceptsZeroOriginChain : Properties.RepRegistrationAcceptsZeroOriginChain := by
  have he : IdAssumptionsOn toyId {((0 : Chain), widen 7)} := toyId_on_single (by decide)
  obtain ⟨out, hout⟩ := toy_registration ⟨fun _ => 0, fun _ => 0⟩ 5 7 1 0 rfl (by decide) (by decide)
  refine ⟨toyId, _, 1, NativeTokenVault.empty.vault, toyHooks 5,
    ⟨toyConfig 5 (0 + 1) 1 0, ⟨fun _ => 0, fun _ => 0⟩, false, ()⟩, 7, out, he, by decide,
    NativeTokenVault.empty_valid, NativeTokenVault.pairsIn_empty _, rfl, ⟨rfl, registryCorr_empty⟩,
    hout, rfl, by decide, rfl, rfl, ?_, ?_, NativeTokenVault.sn_originChain_self _ _ _ _ _, ?_⟩
  · exact registration_establishes_wellformed (fresh_registration_preconditions hout).2
  · exact (NativeTokenVault.sn_registered_self NativeTokenVault.empty.vault (0 + 1)
      (widen 5) (widen 7) 0).mpr (by decide)
  · intro hV'
    -- the new asset is registered, but its recorded origin chain is the unset value
    have hreg := (NativeTokenVault.sn_registered_self NativeTokenVault.empty.vault (0 + 1)
      (widen 5) (widen 7) 0).mpr (by decide)
    have hchain := (hV'.originIff (0 + 1)).mp hreg
    exact hchain (NativeTokenVault.sn_originChain_self _ _ _ _ _)

/-! ### Deployed address zero -/

theorem repRegistrationAcceptsZeroToken : Properties.RepRegistrationAcceptsZeroToken := by
  have he : IdAssumptionsOn toyId {((2 : Chain), widen 7)} := toyId_on_single (by decide)
  obtain ⟨out, hout⟩ := toy_registration ⟨fun _ => 0, fun _ => 0⟩ 0 7 1 2 rfl (by decide) (by decide)
  refine ⟨toyId, _, 1, NativeTokenVault.empty.vault, toyHooks 0,
    ⟨toyConfig 0 (2 + 1) 1 2, ⟨fun _ => 0, fun _ => 0⟩, false, ()⟩, 7, out, he, by decide,
    NativeTokenVault.empty_valid, NativeTokenVault.pairsIn_empty _, rfl, ⟨rfl, registryCorr_empty⟩,
    hout, rfl, rfl, by decide, ?_, ?_, by decide, ?_⟩
  · exact registration_establishes_wellformed (fresh_registration_preconditions hout).2
  · have h := NativeTokenVault.sn_assetOf_self NativeTokenVault.empty.vault (2 + 1) (widen 0)
      (widen 7) 2
    rw [widen_zero] at h
    exact h
  · intro hV'
    -- the zero address now carries the new asset id
    have h := NativeTokenVault.sn_assetOf_self NativeTokenVault.empty.vault (2 + 1) (widen 0)
      (widen 7) 2
    rw [widen_zero] at h
    have hz := hV'.zeroTokenFree
    change (NativeTokenVault.setNewTokenStorage NativeTokenVault.empty.vault (2 + 1) (widen 0)
      (widen 7) 2).assetOf 0 = 0 at hz
    rw [widen_zero, h] at hz
    exact absurd hz (by decide)

/-! ### Origin token zero -/

theorem registryBridgedAcceptsZeroOriginToken :
    Properties.RegistryBridgedAcceptsZeroOriginToken := by
  refine ⟨?_, ?_⟩
  · have he : IdAssumptionsOn toyId {((2 : Chain), (0 : NativeTokenVault.Address))} :=
      toyId_on_single (by decide)
    have hg : RegisterBridgedGuard toyId 1 NativeTokenVault.empty.vault (2 + 1) (widen 5) 0 2 :=
      ⟨by decide, by decide, rfl, by decide, rfl, fun h => h rfl⟩
    exact ⟨toyId, _, 1, NativeTokenVault.empty.vault, 2 + 1, widen 5, 2, he, by decide,
      NativeTokenVault.empty_valid, NativeTokenVault.pairsIn_empty _, rfl, hg,
      (NativeTokenVault.registerBridged_preserves_valid_on he (by decide)
        NativeTokenVault.empty_valid (NativeTokenVault.pairsIn_empty _) rfl hg).1⟩
  · intro Accounting hooks s origin h0
    cases hr : registerRepresentation hooks s origin with
    | none => rfl
    | some out =>
      exact absurd (widen_eq_zero.mp h0) (registration_initial_fields hr).2.1

/-! ### The satisfiability witnesses -/

/-- Native token `9` registered as `1 + 1`; asset `2 + 1` (origin chain `2`, origin
token `7`) to be deployed at the fresh address `5`. -/
def witnessState : RegistrationState Unit := ⟨toyConfig 5 (2 + 1) 1 2, nativeRegistry 9, false, ()⟩

def witnessPairs : Set (Chain × NativeTokenVault.Address) :=
  {((1 : Chain), widen 9), ((2 : Chain), widen 7)}

theorem witnessPairs_on : IdAssumptionsOn toyId witnessPairs :=
  toyId_on_pair (by decide) (by decide) (by decide)

theorem witness_registration :
    ∃ out, registerFreshBranch (toyHooks 5) witnessState 7 = some out :=
  toy_registration (nativeRegistry 9) 5 7 1 2 (nativeRegistry_token_ne 9 (by decide))
    (by decide) (by decide)

theorem witness_guards : RegistryOnlyGuards witnessState :=
  ⟨by decide, nativeRegistry_asset_ne 9 (by decide), by decide⟩

theorem correspondenceSatisfiable : Properties.CorrespondenceSatisfiable := by
  obtain ⟨hv, hp⟩ := nativeVault_valid witnessPairs_on (n := 9) (by decide) (Or.inl rfl)
  obtain ⟨out, hout⟩ := witness_registration
  exact ⟨toyId, witnessPairs, 1, nativeVault 9, toyHooks 5, witnessState, 7, out, witnessPairs_on,
    by decide, hv, hp, Or.inr rfl, ⟨rfl, nativeRegistry_corr 9⟩, hout, rfl, witness_guards,
    1 + 1, by decide, nativeVault_registered 9 (by decide)⟩

/-- The registry vault after the witness registration. -/
def witnessVault : Vault := correspondingRegistration witnessState 7 (nativeVault 9)

theorem witnessVault_valid : Valid toyId 1 witnessVault := by
  obtain ⟨hv, hp⟩ := nativeVault_valid witnessPairs_on (n := 9) (by decide) (Or.inl rfl)
  obtain ⟨out, hout⟩ := witness_registration
  exact (registrationPreservesValidOn (s := witnessState) (origin := 7) witnessPairs_on
    (by decide) hv hp (Or.inr rfl) ⟨rfl, nativeRegistry_corr 9⟩ hout rfl witness_guards).1

/-- A ledger holding one unit for account `11`. -/
def witnessToken : BridgedStandardERC20.State :=
  BridgedStandardERC20.mintEffect (BridgedStandardERC20.empty ⟨1, 7, 2 + 1⟩) 11 1

theorem witnessToken_ledger : BridgedStandardERC20.WellFormed witnessToken := by
  have hempty : BridgedStandardERC20.WellFormed (BridgedStandardERC20.empty ⟨1, 7, 2 + 1⟩) := by
    refine ⟨Finset.sum_const_zero, ?_, rfl⟩
    norm_num [BridgedStandardERC20.empty, UInt256.size]
  have hmint : BridgedStandardERC20.mint (BridgedStandardERC20.empty ⟨1, 7, 2 + 1⟩) 1 11 1
      = some witnessToken := by
    unfold BridgedStandardERC20.mint
    rw [ite_eq_left]
    · rfl
    · refine ⟨by decide, rfl, by decide, ?_⟩
      norm_num [BridgedStandardERC20.empty, UInt256.size]
  exact BridgedStandardERC20.mint_preserves_ledger hempty hmint

/-- The representation state with that ledger, on the witness registry. -/
def witnessPrepState : State Unit :=
  ⟨toyConfig 5 (2 + 1) 1 2, installRegistry (nativeRegistry 9) (2 + 1) 5, false, witnessToken, ()⟩

/-- Burn one unit of `11`'s balance towards chain `4`, resolving the token from the
registry (zero hint). -/
def witnessRequest : Request := ⟨1, 4, 2 + 1, 11, 0, 0, ⟨1, 12, 0⟩⟩

def witnessPrepHooks : Hooks Unit := ⟨fun a _ _ _ _ => some a, fun _ _ => some []⟩

theorem witnessPrep_token :
    witnessPrepState.registry.tokenForAsset (2 + 1) = 5 := by
  show Function.update (nativeRegistry 9).tokenForAsset (2 + 1) 5 (2 + 1) = 5
  exact Function.update_self _ _ _

theorem witnessPrep_asset :
    witnessPrepState.registry.assetForToken 5 = 2 + 1 := by
  show Function.update (nativeRegistry 9).assetForToken 5 (2 + 1) 5 = 2 + 1
  exact Function.update_self _ _ _

theorem witnessPrep_rc : RepresentationConsistent witnessPrepState :=
  ⟨rfl, rfl, witnessPrep_token, witnessPrep_asset⟩

theorem witnessPrep_corr : Corr witnessPrepState 1 witnessVault := by
  refine ⟨rfl, registryCorr_install (nativeRegistry_corr 9) _ _ _ _, ?_⟩
  intro _
  exact ⟨NativeTokenVault.sn_originChain_self _ _ _ _ _,
    NativeTokenVault.sn_originToken_self _ _ _ _ _⟩

theorem preparationCorrespondenceSatisfiable : Properties.PreparationCorrespondenceSatisfiable := by
  have hw : WellFormed witnessPrepState := ⟨witnessToken_ledger, witnessPrep_rc⟩
  have htok : witnessPrepState.registry.tokenForAsset (2 + 1) = 5 := witnessPrep_token
  have hs : InScope witnessPrepState witnessRequest := by
    refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    show (if (0 : Address) = 0 then witnessPrepState.registry.tokenForAsset (2 + 1) else 0) = 5
    rw [ite_eq_left rfl, htok]
  have hsel : selectedToken witnessPrepState witnessRequest = 5 := hs.2.2.2.2
  have he : EntryAllowed witnessPrepState witnessRequest := by
    refine ⟨rfl, rfl, rfl, ?_, ?_, by decide⟩
    · rw [hsel]; decide
    · rw [hsel]; exact witnessPrep_asset
  have hb : witnessRequest.data.amount.val ≤ witnessPrepState.token.balances 11 := by
    show (1 : UInt256).val ≤ Function.update (fun _ => 0) (11 : Address) (0 + (1 : UInt256).val) 11
    rw [Function.update_self]
    decide
  obtain ⟨out, hout⟩ := preparation_enabled (hooks := witnessPrepHooks) (accounted := ())
    (metadata := []) hw hs he rfl (by decide) hb (by decide) (by decide) rfl rfl
  exact ⟨toyId, 1, ⟨witnessVault, NativeTokenVault.empty.audit⟩, witnessPrepHooks,
    witnessPrepState, witnessRequest, out, witnessVault_valid, witnessPrep_corr, hw,
    by show witnessPrepState.registry.tokenForAsset (2 + 1) ≠ 0
       rw [htok]; decide, hout⟩

/-! ## Certificates -/

theorem RegistrationEffectCorresponds : Properties.RegistrationEffectCorresponds :=
  fun _ _ _ _ _ _ _ hc h => registrationEffectCorresponds hc h

theorem RegistrationGuardGap : Properties.RegistrationGuardGap :=
  fun _ _ _ _ _ _ _ _ hc h henc => registrationGuardGap hc h henc

theorem RegistrationIsRegistryStep : Properties.RegistrationIsRegistryStep :=
  fun _ _ _ _ _ _ _ _ hc h henc hg => registrationIsRegistryStep hc h henc hg

theorem RegistrationPreservesValidOn : Properties.RegistrationPreservesValidOn :=
  fun _ _ _ _ _ _ _ _ _ he hc0 hV hP hmem hc h henc hg =>
    registrationPreservesValidOn he hc0 hV hP hmem hc h henc hg

theorem PreparationIsForeignBridgeOut : Properties.PreparationIsForeignBridgeOut :=
  fun _ _ _ _ _ e _ _ hc hr h => preparationIsForeignBridgeOut e hc hr h

theorem ValidRegistryHalvesAgree : Properties.ValidRegistryHalvesAgree :=
  fun _ _ _ _ hV hc a t => validRegistryHalvesAgree hV hc a t

theorem RepRegistrationRebindsLiveToken : Properties.RepRegistrationRebindsLiveToken :=
  repRegistrationRebindsLiveToken

theorem RepRegistrationAcceptsZeroOriginChain : Properties.RepRegistrationAcceptsZeroOriginChain :=
  repRegistrationAcceptsZeroOriginChain

theorem RepRegistrationAcceptsZeroToken : Properties.RepRegistrationAcceptsZeroToken :=
  repRegistrationAcceptsZeroToken

theorem RegistryBridgedAcceptsZeroOriginToken : Properties.RegistryBridgedAcceptsZeroOriginToken :=
  registryBridgedAcceptsZeroOriginToken

theorem CorrespondenceSatisfiable : Properties.CorrespondenceSatisfiable :=
  correspondenceSatisfiable

theorem PreparationCorrespondenceSatisfiable : Properties.PreparationCorrespondenceSatisfiable :=
  preparationCorrespondenceSatisfiable

end Contracts.NativeTokenVaultBase
