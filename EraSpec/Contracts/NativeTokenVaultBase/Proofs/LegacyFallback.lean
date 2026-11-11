import EraSpec.Contracts.NativeTokenVaultBase.Properties.LegacyFallback
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.ModelCorrespondence
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.RegistryAndEscrow
import EraSpec.Contracts.BridgedStandardERC20.Proofs.LegacyFallback

/-!
# Proofs: the legacy fallback's asset id against the vault's registry

The token side contributes one fact, `fired_assetId`: once the fallback has fired on a run
from a legacy token, the token's id is `e l1 (widen originToken)`, from
`BridgedStandardERC20.legacy_run_fallback_fired`. The registry side contributes `vaultId_shape`:
on a `Valid` vault a nonzero id for `T` is the encoding of the pair it records (`idShape`, after
`tokenOfAsset` and `zeroTokenFree` show the id is registered). Agreement is then an equation
between two encodings, and the bounded hash premise on those two pairs decides it.

The preparation results read `prepareLegacy` off its definition (`prepareLegacy_view`) and use
the token side's `legacy_bridge_burn_exact`. The reduction to `prepare` is definitional once the
hook's token argument is rewritten (`HookIgnoresTokenConfig`).

The registry witnesses are one bridged registration from fresh storage (`bridgedWorld`), with
the toy encoding `toyId = (c, _) ↦ c + 1` of `Proofs/ModelCorrespondence.lean`, which is
injective and nonzero on any pair set with distinct chains and no chain `-1`, and `constId` of
`Proofs/RegistryAndEscrow.lean` for the collision. The preparation witnesses are one funded
legacy token tracked by the L2 vault (`legacyPrepState`).
-/

namespace Contracts.NativeTokenVaultBase

open NativeTokenVault (Chain Vault World NtvAssetId Valid IdAssumptionsOn Op ReachLog
  registeredPairs)

/-! ## The token side: the fallback's id -/

/-- Once the fallback has fired on a run from a legacy token, the token's id is the encoding of
`(l1, originToken)`. -/
theorem fired_assetId {e : NtvAssetId} {l1 : Chain} {s t : BridgedStandardERC20.State}
    (hl : s.config.vault = 0) (h : BridgedStandardERC20.LegacyReach (legacyEnv e l1) s t)
    (hv : t.config.vault ≠ 0) : t.config.assetId = e l1 (widen s.config.originToken) := by
  have hc : t.config = BridgedStandardERC20.fallbackConfig (legacyEnv e l1) s.config :=
    BridgedStandardERC20.legacy_run_fallback_fired (legacyEnv e l1) hl h hv
  rw [hc]
  rfl

/-! ## The registry side -/

/-- On a valid vault, a nonzero id for `T` is registered, and its token is `T`. -/
theorem registered_of_vaultId_ne {e : NtvAssetId} {thisChain : Chain} {V : Vault}
    (hV : Valid e thisChain V) {T : Address} (h : vaultIdOf V T ≠ 0) :
    NativeTokenVault.Registered V (vaultIdOf V T) ∧ V.token (vaultIdOf V T) = widen T := by
  have htok : V.token (V.assetOf (widen T)) = widen T := hV.tokenOfAsset (widen T) h
  refine ⟨?_, htok⟩
  show V.token (V.assetOf (widen T)) ≠ 0
  rw [htok]
  intro h0
  apply h
  have hT : T = 0 := widen_eq_zero.mp h0
  subst hT
  show V.assetOf (widen 0) = 0
  rw [widen_zero]
  exact hV.zeroTokenFree

/-- On a valid vault, a nonzero id for `T` is the encoding of the pair it records. -/
theorem vaultId_shape {e : NtvAssetId} {thisChain : Chain} {V : Vault}
    (hV : Valid e thisChain V) {T : Address} (h : vaultIdOf V T ≠ 0) :
    vaultIdOf V T = e (recordedPair V T).1 (recordedPair V T).2 :=
  hV.idShape _ (registered_of_vaultId_ne hV h).1

/-- The recorded legacy pair gives the fallback's id. No hash premise. -/
theorem vaultId_of_records {e : NtvAssetId} {thisChain : Chain} {V : Vault}
    (hV : Valid e thisChain V) {T : Address} {l1 : Chain} {ot : Address}
    (h : RecordsLegacyPair V T l1 ot) : vaultIdOf V T = e l1 (widen ot) := by
  rw [vaultId_shape hV h.1, h.2]
  rfl

/-- The fallback's id as the vault's id forces the recorded legacy pair or a pinned break. No
hash premise. -/
theorem records_or_break_of_vaultId {e : NtvAssetId} {thisChain : Chain} {V : Vault}
    (hV : Valid e thisChain V) {T : Address} {l1 : Chain} {ot : Address}
    (h : vaultIdOf V T = e l1 (widen ot)) :
    RecordsLegacyPair V T l1 ot ∨ LegacyIdBreak e V T l1 ot := by
  by_cases h0 : vaultIdOf V T = 0
  · exact Or.inr (Or.inl ⟨h.symm.trans h0, h0⟩)
  · by_cases hp : recordedPair V T = legacyPair l1 ot
    · exact Or.inl ⟨h0, hp⟩
    · exact Or.inr (Or.inr ⟨h0, hp, (vaultId_shape hV h0).symm.trans h⟩)

/-- With the hash premise on the two pairs, the fallback's id is the vault's id exactly when the
vault records the legacy pair. -/
theorem vaultId_iff_records_on {e : NtvAssetId} {thisChain : Chain} {V : Vault}
    (hV : Valid e thisChain V) {T : Address} {l1 : Chain} {ot : Address}
    (he : IdAssumptionsOn e {legacyPair l1 ot, recordedPair V T}) :
    vaultIdOf V T = e l1 (widen ot) ↔ RecordsLegacyPair V T l1 ot := by
  refine ⟨fun h => ?_, vaultId_of_records hV⟩
  rcases records_or_break_of_vaultId hV h with hr | hb
  · exact hr
  · exfalso
    rcases hb with ⟨h0, _⟩ | ⟨_, hne, hcol⟩
    · exact he.nonzero (legacyPair l1 ot) (Set.mem_insert _ _) h0
    · exact hne (he.inj _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)) _
        (Set.mem_insert _ _) hcol)

/-! ## Agreement -/

theorem LegacyAssetIdAgreesIffRecordedOn : Properties.LegacyAssetIdAgreesIffRecordedOn := by
  intro e thisChain l1 V T s t hV hl hr hv he
  unfold AssetIdAgrees
  rw [fired_assetId hl hr hv]
  exact vaultId_iff_records_on hV he

theorem LegacyAssetIdAgreementOrBreak : Properties.LegacyAssetIdAgreementOrBreak := by
  intro e thisChain l1 V T s t hV hl hr hv
  unfold AssetIdAgrees
  rw [fired_assetId hl hr hv]
  exact ⟨vaultId_of_records hV, records_or_break_of_vaultId hV⟩

theorem LegacyAssetIdAgreesIffL1OriginOn : Properties.LegacyAssetIdAgreesIffL1OriginOn := by
  intro e thisChain l1 V T s t hV hl hr hv hot he
  rw [LegacyAssetIdAgreesIffRecordedOn e thisChain l1 V T s t hV hl hr hv he]
  unfold RecordsLegacyPair recordedPair legacyPair
  constructor
  · rintro ⟨h0, hp⟩
    exact ⟨h0, (Prod.mk_inj.mp hp).1⟩
  · rintro ⟨h0, hc⟩
    exact ⟨h0, by rw [hc, hot]⟩

/-! ## Permanence -/

/-- One vault operation leaves a nonzero `assetId[T]` alone. -/
theorem step_assetOf_frozen {e : NtvAssetId} {thisChain : Chain} {W X : World}
    (hs : NativeTokenVault.Step e thisChain W X) {T : NativeTokenVault.Address}
    (hT : W.vault.assetOf T ≠ 0) : X.vault.assetOf T = W.vault.assetOf T := by
  cases hs with
  | @registerNative t hg =>
    have hne : T ≠ t := fun h => hT (by rw [h]; exact hg.fresh)
    exact NativeTokenVault.sn_assetOf_of_ne _ _ _ _ _ hne
  | @registerBridged a t ot origin hg =>
    have hne : T ≠ t := fun h => hT (by rw [h]; exact hg.freshToken)
    exact NativeTokenVault.sn_assetOf_of_ne _ _ _ _ _ hne
  | bridgeOut _ => simp
  | bridgeIn _ => simp
  | donate => simp

theorem RegisteredTokenIdFrozen : Properties.RegisteredTokenIdFrozen := by
  intro e thisChain W X T hr hT
  induction hr with
  | refl => rfl
  | @tail Y Z _ hs ih =>
    have hY : Y.vault.assetOf T ≠ 0 := by rw [ih]; exact hT
    rw [step_assetOf_frozen hs hY, ih]

theorem LegacyAgreementPermanent : Properties.LegacyAgreementPermanent := by
  intro env e thisChain W X T t t' hv ht hW hr
  have hcfg : t'.config = t.config := by
    rcases BridgedStandardERC20.legacy_run_config env ht with hc | ⟨h0, _⟩
    · exact hc
    · exact absurd h0 hv
  have hid : vaultIdOf X.vault T = vaultIdOf W.vault T :=
    RegisteredTokenIdFrozen e thisChain W X (widen T) hr hW
  unfold AssetIdAgrees
  rw [hid, hcfg]

/-- `registerNative` of `T` gives `T` the id `e thisChain (widen T)`. -/
theorem registerNative_vaultId (e : NtvAssetId) (thisChain : Chain) (V : Vault) (T : Address) :
    vaultIdOf (NativeTokenVault.registerNative e thisChain V (widen T)) T = e thisChain (widen T) :=
  NativeTokenVault.sn_assetOf_self _ _ _ _ _

/-- …and records the pair `(thisChain, T)` for it. -/
theorem registerNative_recorded (e : NtvAssetId) (thisChain : Chain) (V : Vault) (T : Address) :
    recordedPair (NativeTokenVault.registerNative e thisChain V (widen T)) T
      = (thisChain, widen T) := by
  unfold recordedPair
  rw [registerNative_vaultId]
  exact Prod.ext
    (NativeTokenVault.sn_originChain_self V (e thisChain (widen T)) (widen T) (widen T) thisChain)
    (NativeTokenVault.sn_originToken_self V (e thisChain (widen T)) (widen T) (widen T) thisChain)

theorem UnregisteredLegacyTokenRegistersNative :
    Properties.UnregisteredLegacyTokenRegistersNative := by
  intro e thisChain l1 W T ot hT h0 hl1 he
  have hg : NativeTokenVault.RegisterNativeGuard W.vault (widen T) :=
    ⟨fun h => hT (widen_eq_zero.mp h), h0⟩
  have hid := registerNative_vaultId e thisChain W.vault T
  have hrec := registerNative_recorded e thisChain W.vault T
  have hnz : e thisChain (widen T) ≠ 0 := he.nonzero _ (Set.mem_insert _ _)
  have hdiff : e thisChain (widen T) ≠ e l1 (widen ot) := by
    intro h
    have hp := he.inj _ (Set.mem_insert _ _) _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)) h
    exact hl1 (Prod.mk_inj.mp hp).1.symm
  have hnat : NativeTokenVault.Native thisChain
      (NativeTokenVault.registerNative e thisChain W.vault (widen T))
      (vaultIdOf (NativeTokenVault.registerNative e thisChain W.vault (widen T)) T) := by
    show (recordedPair (NativeTokenVault.registerNative e thisChain W.vault (widen T)) T).1
      = thisChain
    rw [hrec]
  refine ⟨{ W with vault := NativeTokenVault.registerNative e thisChain W.vault (widen T) },
    NativeTokenVault.Step.registerNative hg, hid, hnat, fun hb => hb.2 hnat, ?_, ?_, ?_⟩
  · rintro ⟨_, hp⟩
    have h1 := congrArg Prod.fst (hrec.symm.trans hp)
    exact hl1 h1.symm
  · show vaultIdOf (NativeTokenVault.registerNative e thisChain W.vault (widen T)) T
      ≠ e l1 (widen ot)
    rw [hid]
    exact hdiff
  · intro Y hY
    exact RegisteredTokenIdFrozen e thisChain _ Y (widen T) hY (by
      show vaultIdOf (NativeTokenVault.registerNative e thisChain W.vault (widen T)) T ≠ 0
      rw [hid]
      exact hnz)

/-! ## The representation model -/

theorem LegacyFallbackRepresentationIff : Properties.LegacyFallbackRepresentationIff := by
  intro Accounting σ env t hvault hl hr hv
  have hcfg : t.config = BridgedStandardERC20.fallbackConfig env σ.token.config :=
    BridgedStandardERC20.legacy_run_fallback_fired env hl hr hv
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h1, _⟩
    rw [hl, hvault] at h1
    exact BridgedStandardERC20.l2_vault_nonzero h1.symm
  · intro hw
    exact (BridgedStandardERC20.legacy_reachable_ledger env hw hr).1
  · show (t.config.vault = σ.config.vault ∧ t.config.assetId = σ.config.assetId ∧
        σ.registry.tokenForAsset σ.config.assetId = σ.config.tokenAddress ∧
        σ.registry.assetForToken σ.config.tokenAddress = σ.config.assetId) ↔ _
    rw [hcfg]
    constructor
    · rintro ⟨_, ha, hfa, hft⟩
      exact ⟨ha.symm, hfa, hft⟩
    · rintro ⟨ha, hfa, hft⟩
      exact ⟨hvault.symm, ha.symm, hfa, hft⟩

/-! ## Preparation of a legacy token -/

section Preparation

variable {Accounting : Type}

/-- What a successful deployed preparation did, read off its definition (as `prepare_view` in
`Proofs/RepresentationPreparation.lean`, with the deployed token call). -/
theorem prepareLegacy_view {env : BridgedStandardERC20.LegacyEnv} {hooks : Hooks Accounting}
    {s : State Accounting} {r : Request} {out : Result Accounting}
    (h : prepareLegacy env hooks s r = some out) :
    InScope s r ∧ EntryAllowed s r ∧ r.msgValue = 0 ∧
    ∃ accounted burned metadata,
      hooks.account s.accounting s.token r.destinationChain r.assetId r.data.amount =
        some accounted ∧
      BridgedStandardERC20.bridgeBurn env s.token s.config.vault r.depositor r.data.amount
        = some burned ∧
      burned.config.originToken ≠ 0 ∧ s.config.originChainId ≠ 0 ∧
      hooks.metadata burned s.config.originChainId = some metadata ∧
      out = ⟨{ s with token := burned, accounting := accounted },
        mintData r burned metadata⟩ := by
  unfold prepareLegacy at h
  split at h
  · rename_i hg
    cases ha : hooks.account s.accounting s.token r.destinationChain r.assetId r.data.amount with
    | none => simp only [ha, reduceCtorEq] at h
    | some accounted =>
      simp only [ha] at h
      split at h
      · rename_i hv
        cases hb : BridgedStandardERC20.bridgeBurn env s.token s.config.vault r.depositor
            r.data.amount with
        | none => simp only [hb, reduceCtorEq] at h
        | some burned =>
          simp only [hb] at h
          split at h
          · rename_i ho
            cases hm : hooks.metadata burned s.config.originChainId with
            | none => simp only [hm, reduceCtorEq] at h
            | some metadata =>
              simp only [hm] at h
              exact ⟨hg.1, hg.2, hv, accounted, burned, metadata, rfl, rfl,
                ho.1, ho.2, hm, (Option.some.inj h).symm⟩
          · cases h
      · cases h
  · cases h

/-- The deployed preparation succeeds when each of its steps does. -/
theorem prepareLegacy_eq_some {env : BridgedStandardERC20.LegacyEnv} {hooks : Hooks Accounting}
    {s : State Accounting} {r : Request} {accounted : Accounting}
    {burned : BridgedStandardERC20.State} {metadata : Bytes}
    (hg : InScope s r ∧ EntryAllowed s r)
    (ha : hooks.account s.accounting s.token r.destinationChain r.assetId r.data.amount =
      some accounted)
    (hv : r.msgValue = 0)
    (hb : BridgedStandardERC20.bridgeBurn env s.token s.config.vault r.depositor r.data.amount
      = some burned)
    (ho : burned.config.originToken ≠ 0 ∧ s.config.originChainId ≠ 0)
    (hm : hooks.metadata burned s.config.originChainId = some metadata) :
    prepareLegacy env hooks s r
      = some ⟨{ s with token := burned, accounting := accounted },
          mintData r burned metadata⟩ := by
  simp only [prepareLegacy, ite_eq_left hg, ha, ite_eq_left hv, hb, ite_eq_left ho, hm]

/-- `prepare` fails when its token burn does. -/
theorem prepare_none_of_burn_none {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request}
    (hb : BridgedStandardERC20.burn s.token s.config.vault r.depositor r.data.amount = none) :
    prepare hooks s r = none := by
  unfold prepare
  split
  · cases hooks.account s.accounting s.token r.destinationChain r.assetId r.data.amount with
    | none => rfl
    | some accounted =>
      dsimp only
      split
      · rw [hb]
      · rfl
  · rfl

end Preparation

theorem LegacyPreparationConservative : Properties.LegacyPreparationConservative := by
  intro Accounting env hooks s r hv
  have hb : ∀ o a, BridgedStandardERC20.bridgeBurn env s.token s.config.vault o a
      = BridgedStandardERC20.burn s.token s.config.vault o a :=
    fun o a => (BridgedStandardERC20.nonlegacy_bridge_calls_unchanged env hv s.config.vault o a).2
  unfold prepareLegacy prepare
  simp only [hb]
  rfl

theorem LegacyPreparationIsPreparation : Properties.LegacyPreparationIsPreparation := by
  intro Accounting env hooks s r hl hh
  have hacc : hooks.account s.accounting (BridgedStandardERC20.legacyFallback env s.token)
      r.destinationChain r.assetId r.data.amount
        = hooks.account s.accounting s.token r.destinationChain r.assetId r.data.amount := by
    rw [BridgedStandardERC20.legacyFallback_of_vault_eq hl]
    exact hh _ _ _ _ _ _
  unfold prepareLegacy prepare
  dsimp only
  rw [hacc]
  rfl

theorem LegacyFirstPreparation : Properties.LegacyFirstPreparation := by
  intro Accounting env hooks s r out hvault hl hw h
  obtain ⟨_, _, _, accounted, burned, metadata, _, hb, _, _, _, rfl⟩ := prepareLegacy_view h
  obtain ⟨_, hcfg, hbal, hsup, _⟩ := BridgedStandardERC20.legacy_bridge_burn_exact env hw hl hb
  have hwb : BridgedStandardERC20.WellFormed burned :=
    (BridgedStandardERC20.legacy_reachable_ledger env hw
      (BridgedStandardERC20.LegacyReach.tail BridgedStandardERC20.LegacyReach.refl
        (BridgedStandardERC20.LegacyStep.bridgeBurn hb))).1
  refine ⟨hcfg, hbal, hsup, hwb, ?_⟩
  show (burned.config.vault = s.config.vault ∧ burned.config.assetId = s.config.assetId ∧
      s.registry.tokenForAsset s.config.assetId = s.config.tokenAddress ∧
      s.registry.assetForToken s.config.tokenAddress = s.config.assetId) ↔ _
  rw [hcfg]
  constructor
  · rintro ⟨_, ha, hfa, hft⟩
    exact ⟨ha.symm, hfa, hft⟩
  · rintro ⟨ha, hfa, hft⟩
    exact ⟨hvault.symm, ha.symm, hfa, hft⟩

/-! ### A legacy preparation instance -/

/-- A legacy token (vault slot zero, origin token `5`) whose account `3` holds one unit. -/
def fundedLegacy : BridgedStandardERC20.State :=
  ⟨⟨0, 5, 0⟩, Function.update (fun _ => 0) 3 1, 1⟩

theorem fundedLegacy_wellFormed : BridgedStandardERC20.WellFormed fundedLegacy := by
  refine ⟨?_, ?_, ?_⟩
  · simp [fundedLegacy, Function.update_apply]
  · norm_num [fundedLegacy, UInt256.size]
  · show Function.update (fun _ => 0) (3 : Address) 1 0 = 0
    rw [Function.update_of_ne (by decide)]

/-- The L2 vault tracking the token at `7` under id `asset` (base asset `asset + 1`, this chain
`2`, origin chain `1`), with both registry maps installed. -/
def legacyPrepState (asset : UInt256) : State Unit :=
  ⟨⟨BridgedStandardERC20.l2NativeTokenVaultAddr, 1, 7, asset, asset + 1, 2, 1⟩,
    installRegistry ⟨fun _ => 0, fun _ => 0⟩ asset 7, false, fundedLegacy, ()⟩

/-- Router `1` asks to burn one unit of the token at `7` from account `3` towards chain `9`. -/
def legacyPrepRequest (asset : UInt256) : Request :=
  ⟨1, 9, asset, 3, 0, 0, ⟨1, 4, 7⟩⟩

/-- Hooks that always succeed and read nothing. -/
def trivialHooks : Hooks Unit :=
  ⟨fun acc _ _ _ _ => some acc, fun _ _ => some []⟩

theorem trivialHooks_ignore : HookIgnoresTokenConfig trivialHooks :=
  fun _ _ _ _ _ _ => rfl

theorem ne_add_one (x : UInt256) : x ≠ x + 1 := fun h =>
  absurd (add_left_cancel (h.symm.trans (add_zero x).symm)) (by decide)

/-- On the instance, the deployed preparation succeeds and fires the fallback. -/
theorem legacyPrep_succeeds (env : BridgedStandardERC20.LegacyEnv) (asset : UInt256) :
    ∃ out, prepareLegacy env trivialHooks (legacyPrepState asset) (legacyPrepRequest asset)
      = some out := by
  have h1 : (1 : UInt256).val = 1 := rfl
  have h7 : (7 : Address) ≠ 0 := by decide
  have hg : InScope (legacyPrepState asset) (legacyPrepRequest asset) ∧
      EntryAllowed (legacyPrepState asset) (legacyPrepRequest asset) := by
    refine ⟨⟨BridgedStandardERC20.l2_vault_nonzero, h7, ne_add_one asset,
      (by decide : (1 : UInt256) ≠ 2), rfl⟩, rfl, rfl, rfl, h7, ?_,
      (by decide : (1 : UInt256) ≠ 0)⟩
    show Function.update (fun _ => (0 : UInt256)) (7 : Address) asset 7 = asset
    exact Function.update_self _ _ _
  have hb := BridgedStandardERC20.legacy_bridge_burn_enabled env (s := fundedLegacy)
    (owner := 3) (amount := 1) rfl (by decide)
    (by show (1 : UInt256).val ≤ Function.update (fun _ => 0) (3 : Address) 1 3
        rw [Function.update_self, h1])
  exact ⟨_, prepareLegacy_eq_some (accounted := ()) (metadata := []) hg rfl rfl hb
    ⟨(by decide : (5 : Address) ≠ 0), (by decide : (1 : UInt256) ≠ 0)⟩ rfl⟩

theorem LegacyFirstPreparationWitness : Properties.LegacyFirstPreparationWitness := by
  intro env
  let asset : UInt256 := env.assetIdFor env.l1ChainId 5
  obtain ⟨out, hout⟩ := legacyPrep_succeeds env asset
  have hvault :
      (legacyPrepState asset).config.vault = BridgedStandardERC20.l2NativeTokenVaultAddr :=
    rfl
  have hl : (legacyPrepState asset).token.config.vault = 0 := rfl
  have hw : LedgerInvariant (legacyPrepState asset) := fundedLegacy_wellFormed
  obtain ⟨hcfg, _, _, hlw, hiff⟩ :=
    LegacyFirstPreparation Unit env trivialHooks _ _ out hvault hl hw hout
  have hnone : prepare trivialHooks (legacyPrepState asset) (legacyPrepRequest asset) = none :=
    prepare_none_of_burn_none
      (BridgedStandardERC20.original_model_rejects_legacy (s := fundedLegacy) rfl _ _ _).2
  refine ⟨trivialHooks, legacyPrepState asset, legacyPrepRequest asset, out, hvault, hl, hw,
    trivialHooks_ignore, hnone, hout, ⟨hlw, hiff.mpr ⟨rfl, ?_, ?_⟩⟩, ?_⟩
  · show Function.update (fun _ => (0 : Address)) asset (7 : Address) asset = 7
    exact Function.update_self _ _ _
  · show Function.update (fun _ => (0 : UInt256)) (7 : Address) asset 7 = asset
    exact Function.update_self _ _ _
  · rw [hcfg]
    exact BridgedStandardERC20.fallbackConfig_vault_ne env _

theorem LegacyPreparationMismatch : Properties.LegacyPreparationMismatch := by
  intro env
  let asset : UInt256 := env.assetIdFor env.l1ChainId 5 + 1
  obtain ⟨out, hout⟩ := legacyPrep_succeeds env asset
  have hvault :
      (legacyPrepState asset).config.vault = BridgedStandardERC20.l2NativeTokenVaultAddr :=
    rfl
  have hl : (legacyPrepState asset).token.config.vault = 0 := rfl
  have hw : LedgerInvariant (legacyPrepState asset) := fundedLegacy_wellFormed
  obtain ⟨hcfg, _, _, _, hiff⟩ :=
    LegacyFirstPreparation Unit env trivialHooks _ _ out hvault hl hw hout
  have hfa : (legacyPrepState asset).registry.tokenForAsset (legacyPrepState asset).config.assetId
      = (legacyPrepState asset).config.tokenAddress := by
    show Function.update (fun _ => (0 : Address)) asset (7 : Address) asset = 7
    exact Function.update_self _ _ _
  have hft : (legacyPrepState asset).registry.assetForToken
      (legacyPrepState asset).config.tokenAddress = (legacyPrepState asset).config.assetId := by
    show Function.update (fun _ => (0 : UInt256)) (7 : Address) asset 7 = asset
    exact Function.update_self _ _ _
  have hid : out.state.token.config.assetId = env.assetIdFor env.l1ChainId 5 := by
    rw [hcfg]
    rfl
  refine ⟨trivialHooks, legacyPrepState asset, legacyPrepRequest asset, out, hvault, hl, hw,
    trivialHooks_ignore, hfa, hft, hout, fun hr => ?_, ?_⟩
  · exact ne_add_one (env.assetIdFor env.l1ChainId 5) (hiff.mp hr).1.symm
  · show out.state.token.config.assetId ≠ asset
    rw [hid]
    exact ne_add_one _

/-! ## Concrete instances -/

/-- One bridged registration of the token at `T` (origin chain `c`, origin token `ot`) from fresh
storage. It stands for a registry entry inherited from before the pin: no pinned writer records
an already-deployed token as bridged (`Specs/LegacyFallback.lean`). -/
def bridgedWorld (e : NtvAssetId) (c : Chain) (T ot : Address) : World :=
  { NativeTokenVault.empty with
    vault := NativeTokenVault.registerBridged NativeTokenVault.empty.vault (e c (widen ot))
      (widen T) (widen ot) c }

/-- Its log. -/
def bridgedLog (e : NtvAssetId) (c : Chain) (T ot : Address) : List Op :=
  [Op.registerBridged (e c (widen ot)) (widen T) (widen ot) c]

theorem bridgedWorld_guard {e : NtvAssetId} {thisChain c : Chain} {T ot : Address}
    (hc : c ≠ thisChain) (hc0 : c ≠ 0) (hT : T ≠ 0) :
    NativeTokenVault.RegisterBridgedGuard e thisChain NativeTokenVault.empty.vault
      (e c (widen ot)) (widen T) (widen ot) c :=
  ⟨hc, hc0, rfl, fun h => hT (widen_eq_zero.mp h), rfl, fun h => h rfl⟩

theorem bridgedWorld_reachLog {e : NtvAssetId} {thisChain c : Chain} {T ot : Address}
    (hc : c ≠ thisChain) (hc0 : c ≠ 0) (hT : T ≠ 0) :
    ReachLog e thisChain NativeTokenVault.empty (bridgedWorld e c T ot) (bridgedLog e c T ot) :=
  ReachLog.tail (log := []) ReachLog.refl
    (NativeTokenVault.StepOp.registerBridged (bridgedWorld_guard hc hc0 hT))

theorem bridgedLog_pairs (e : NtvAssetId) (thisChain c : Chain) (T ot : Address) :
    registeredPairs thisChain (bridgedLog e c T ot) = {(c, widen ot)} := by
  simp [registeredPairs, bridgedLog, Op.pair]

theorem bridgedWorld_valid {e : NtvAssetId} {thisChain c : Chain} {T ot : Address}
    (he : IdAssumptionsOn e {(c, widen ot)}) (hthis : thisChain ≠ 0) (hc : c ≠ thisChain)
    (hc0 : c ≠ 0) (hT : T ≠ 0) : Valid e thisChain (bridgedWorld e c T ot).vault :=
  (NativeTokenVault.registerBridged_preserves_valid_on he hthis NativeTokenVault.empty_valid
    (NativeTokenVault.pairsIn_empty _) (Set.mem_singleton _) (bridgedWorld_guard hc hc0 hT)).1

theorem bridgedWorld_vaultId (e : NtvAssetId) (c : Chain) (T ot : Address) :
    vaultIdOf (bridgedWorld e c T ot).vault T = e c (widen ot) :=
  NativeTokenVault.sn_assetOf_self _ _ _ _ _

theorem bridgedWorld_recorded (e : NtvAssetId) (c : Chain) (T ot : Address) :
    recordedPair (bridgedWorld e c T ot).vault T = (c, widen ot) := by
  unfold recordedPair
  rw [bridgedWorld_vaultId]
  exact Prod.ext
    (NativeTokenVault.sn_originChain_self NativeTokenVault.empty.vault (e c (widen ot)) (widen T)
      (widen ot) c)
    (NativeTokenVault.sn_originToken_self NativeTokenVault.empty.vault (e c (widen ot)) (widen T)
      (widen ot) c)

/-- On an L2 chain, the token at `T` registered as bridged from `c ≠ thisChain` is bridged by
the vault, provided its id is nonzero. -/
theorem bridgedWorld_bridges {e : NtvAssetId} {thisChain c : Chain} {T ot : Address}
    (hc : c ≠ thisChain) (h0 : e c (widen ot) ≠ 0) :
    VaultBridgesToken thisChain (bridgedWorld e c T ot).vault T := by
  refine ⟨by rw [bridgedWorld_vaultId]; exact h0, ?_⟩
  show (recordedPair (bridgedWorld e c T ot).vault T).1 ≠ thisChain
  rw [bridgedWorld_recorded]
  exact hc

/-- The empty legacy token with origin token `ot`. -/
def emptyLegacy (ot : Address) : BridgedStandardERC20.State :=
  BridgedStandardERC20.empty ⟨0, ot, 0⟩

theorem emptyLegacy_wellFormed (ot : Address) :
    BridgedStandardERC20.WellFormed (emptyLegacy ot) :=
  ⟨Finset.sum_const_zero,
    by norm_num [emptyLegacy, BridgedStandardERC20.empty, UInt256.size], rfl⟩

/-- On the empty legacy token, the L2 vault's one-unit mint to a nonzero recipient succeeds and
fires the fallback. -/
theorem emptyLegacy_mint (env : BridgedStandardERC20.LegacyEnv) (ot recipient : Address)
    (hr : recipient ≠ 0) :
    ∃ t, BridgedStandardERC20.bridgeMint env (emptyLegacy ot)
        BridgedStandardERC20.l2NativeTokenVaultAddr recipient 1 = some t ∧
      BridgedStandardERC20.LegacyReach env (emptyLegacy ot) t ∧
      t.config = BridgedStandardERC20.fallbackConfig env (emptyLegacy ot).config ∧
      t.config.vault ≠ 0 := by
  have h1 : (1 : UInt256).val = 1 := rfl
  have hm := BridgedStandardERC20.legacy_bridge_mint_enabled env (s := emptyLegacy ot)
    (amount := 1) rfl hr (by norm_num [emptyLegacy, BridgedStandardERC20.empty, h1, UInt256.size])
  exact ⟨_, hm, BridgedStandardERC20.LegacyReach.tail BridgedStandardERC20.LegacyReach.refl
    (BridgedStandardERC20.LegacyStep.bridgeMint hm), rfl,
    BridgedStandardERC20.fallbackConfig_vault_ne env _⟩

/-! ## Anti-vacuity and the countermodel -/

theorem LegacyAssetIdAgreementWitness : Properties.LegacyAssetIdAgreementWitness := by
  obtain ⟨t, hm, hr, hcfg, hv⟩ := emptyLegacy_mint (legacyEnv toyId 1) 5 1 (by decide)
  have hS : IdAssumptionsOn toyId ↑(insert (legacyPair 1 (emptyLegacy 5).config.originToken)
      (registeredPairs 2 (bridgedLog toyId 1 7 5))) := by
    rw [bridgedLog_pairs, Finset.coe_insert, Finset.coe_singleton]
    apply toyId_on
    · rintro p (rfl | rfl) q (rfl | rfl) _ <;> rfl
    · rintro p (rfl | rfl) <;> decide
  have hrec := bridgedWorld_recorded toyId 1 7 5
  have hid := bridgedWorld_vaultId toyId 1 7 5
  have hS2 : IdAssumptionsOn toyId {legacyPair 1 (emptyLegacy 5).config.originToken,
      recordedPair (bridgedWorld toyId 1 7 5).vault 7} := by
    rw [hrec]
    apply toyId_on
    · rintro p (rfl | rfl) q (rfl | rfl) _ <;> rfl
    · rintro p (rfl | rfl) <;> decide
  refine ⟨toyId, 2, 1, bridgedWorld toyId 1 7 5, bridgedLog toyId 1 7 5, 7, emptyLegacy 5, t, 1,
    by decide, by decide, bridgedWorld_reachLog (by decide) (by decide) (by decide), hS,
    bridgedWorld_valid (toyId_on_single (by decide)) (by decide) (by decide) (by decide)
      (by decide),
    bridgedWorld_bridges (by decide) (by decide), ?_, emptyLegacy_wellFormed 5, rfl, hm, hr, hv,
    hS2, ?_, ?_, ?_⟩
  · exact congrArg Prod.snd hrec
  · exact ⟨by rw [hid]; decide, hrec⟩
  · show vaultIdOf (bridgedWorld toyId 1 7 5).vault 7 = t.config.assetId
    rw [hid, hcfg]
    rfl
  · rintro (⟨_, h0⟩ | ⟨_, hne, _⟩)
    · rw [hid] at h0
      exact absurd h0 (by decide)
    · exact hne hrec

theorem LegacyAssetIdMismatch : Properties.LegacyAssetIdMismatch := by
  obtain ⟨t, hm, hr, hcfg, hv⟩ := emptyLegacy_mint (legacyEnv toyId 1) 5 1 (by decide)
  have hS : IdAssumptionsOn toyId ↑(insert (legacyPair 1 (emptyLegacy 5).config.originToken)
      (registeredPairs 2 (bridgedLog toyId 3 7 5))) := by
    rw [bridgedLog_pairs, Finset.coe_insert, Finset.coe_singleton]
    exact toyId_on_pair (by decide) (by decide) (by decide)
  have hrec := bridgedWorld_recorded toyId 3 7 5
  have hid := bridgedWorld_vaultId toyId 3 7 5
  have hS2 : IdAssumptionsOn toyId {legacyPair 1 (emptyLegacy 5).config.originToken,
      recordedPair (bridgedWorld toyId 3 7 5).vault 7} := by
    rw [hrec]
    exact toyId_on_pair (by decide) (by decide) (by decide)
  refine ⟨toyId, 2, 1, bridgedWorld toyId 3 7 5, bridgedLog toyId 3 7 5, 7, emptyLegacy 5, t, 1,
    by decide, by decide, bridgedWorld_reachLog (by decide) (by decide) (by decide), hS,
    bridgedWorld_valid (toyId_on_single (by decide)) (by decide) (by decide) (by decide)
      (by decide),
    bridgedWorld_bridges (by decide) (by decide), ?_, ?_, emptyLegacy_wellFormed 5, rfl, hm, hr,
    hv, hS2, ?_, ?_⟩
  · exact congrArg Prod.snd hrec
  · show (recordedPair (bridgedWorld toyId 3 7 5).vault 7).1 ≠ 1
    rw [hrec]
    decide
  · rintro ⟨_, hp⟩
    rw [hrec] at hp
    have h1 : (3 : Chain) = 1 := congrArg Prod.fst hp
    exact absurd h1 (by decide)
  · show ¬ vaultIdOf (bridgedWorld toyId 3 7 5).vault 7 = t.config.assetId
    rw [hid, hcfg]
    decide

theorem LegacyIdCollisionAgreesWrongly : Properties.LegacyIdCollisionAgreesWrongly := by
  obtain ⟨t, _, hr, hcfg, hv⟩ :=
    emptyLegacy_mint (legacyEnv NativeTokenVault.constId 1) 5 1 (by decide)
  have hrec := bridgedWorld_recorded NativeTokenVault.constId 3 7 5
  have hid := bridgedWorld_vaultId NativeTokenVault.constId 3 7 5
  have hne : recordedPair (bridgedWorld NativeTokenVault.constId 3 7 5).vault 7
      ≠ legacyPair 1 (emptyLegacy 5).config.originToken := by
    rw [hrec]
    intro h
    have h1 : (3 : Chain) = 1 := congrArg Prod.fst h
    exact absurd h1 (by decide)
  refine ⟨NativeTokenVault.constId, 2, 1, (bridgedWorld NativeTokenVault.constId 3 7 5).vault, 7,
    emptyLegacy 5, t,
    bridgedWorld_valid (NativeTokenVault.idAssumptionsOn_singleton (by decide)) (by decide)
      (by decide) (by decide) (by decide),
    rfl, hr, hv, ?_, fun h => hne h.2, Or.inr ⟨?_, hne, ?_⟩⟩
  · show vaultIdOf (bridgedWorld NativeTokenVault.constId 3 7 5).vault 7 = t.config.assetId
    rw [hid, hcfg]
    rfl
  · rw [hid]
    decide
  · rw [hrec]
    rfl

theorem UnregisteredLegacyTokenRegistersNativeSatisfiable :
    Properties.UnregisteredLegacyTokenRegistersNativeSatisfiable :=
  ⟨toyId, 2, 1, NativeTokenVault.empty, 7, 5, by decide, NativeTokenVault.empty_valid,
    by decide, rfl, by decide, toyId_on_pair (by decide) (by decide) (by decide)⟩

theorem LegacyFallbackRepresentationWitness : Properties.LegacyFallbackRepresentationWitness := by
  intro env
  obtain ⟨t, _, hr, _, hv⟩ := emptyLegacy_mint env 5 1 (by decide)
  let asset : UInt256 := env.assetIdFor env.l1ChainId 5
  let σ : State Unit :=
    ⟨⟨BridgedStandardERC20.l2NativeTokenVaultAddr, 1, 7, asset, 0, 2, 1⟩,
      installRegistry ⟨fun _ => 0, fun _ => 0⟩ asset 7, false, emptyLegacy 5, ()⟩
  have hvault : σ.config.vault = BridgedStandardERC20.l2NativeTokenVaultAddr := rfl
  have hl : σ.token.config.vault = 0 := rfl
  refine ⟨σ, t, hvault, hl, emptyLegacy_wellFormed 5, hr, hv, ?_⟩
  refine ((LegacyFallbackRepresentationIff Unit σ env t hvault hl hr hv).2.2).mpr ⟨rfl, ?_, ?_⟩
  · show Function.update (fun _ => (0 : Address)) asset (7 : Address) asset = 7
    exact Function.update_self _ _ _
  · show Function.update (fun _ => (0 : UInt256)) (7 : Address) asset 7 = asset
    exact Function.update_self _ _ _

end Contracts.NativeTokenVaultBase
