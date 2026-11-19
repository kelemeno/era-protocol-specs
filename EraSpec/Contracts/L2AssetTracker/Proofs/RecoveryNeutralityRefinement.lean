import EraSpec.Contracts.L2AssetTracker.Properties.RecoveryNeutralityRefinement

/-! # Proofs: `RecoveryNeutrality`'s tracker is the canonical tracker -/

namespace Contracts.L2AssetTracker.RecoveryNeutralityRefinement

open Contracts.L2AssetTracker

/-! ## The writes commute with the projection -/

theorem toStorage_setChainBalance (cfg : RecoveryNeutrality.Config) (t : RecoveryNeutrality.Tracker)
    (c : ChainId) (a : AssetId) (v : UInt256) :
    toStorage cfg (t.setChainBalance c a v) = setChainBalance (toStorage cfg t) c a v := rfl

theorem toStorage_markRegistered (cfg : RecoveryNeutrality.Config) (t : RecoveryNeutrality.Tracker)
    (a : AssetId) (snap : RecoveryNeutrality.SavedTotalSupply) :
    toStorage cfg (t.markRegistered a snap) = markRegistered (toStorage cfg t) a (toSaved snap) := by
  simp only [toStorage, RecoveryNeutrality.Tracker.markRegistered, markRegistered,
    Function.comp_update]

theorem toStorage_setInterop (cfg : RecoveryNeutrality.Config) (t : RecoveryNeutrality.Tracker)
    (a : AssetId) (info : RecoveryNeutrality.InteropL2Info) :
    toStorage cfg (t.setInterop a info) = setInterop (toStorage cfg t) a (toInfo info) := by
  simp only [toStorage, RecoveryNeutrality.Tracker.setInterop, setInterop, Function.comp_update]

theorem checkedAdd_eq : RecoveryNeutrality.checkedAdd = checkedAdd := rfl

theorem checkedSub_eq : RecoveryNeutrality.checkedSub = checkedSub := rfl

theorem decrease_comm (cfg : RecoveryNeutrality.Config) (t : RecoveryNeutrality.Tracker)
    (c : ChainId) (a : AssetId) (x : UInt256) :
    decreaseChainBalance (toStorage cfg t) c a x =
      (RecoveryNeutrality.decreaseChainBalance t c a x).map (toStorage cfg) := by
  unfold decreaseChainBalance RecoveryNeutrality.decreaseChainBalance
  rw [checkedSub_eq]
  show (checkedSub (t.chainBalance c a) x).map _ = _
  cases checkedSub (t.chainBalance c a) x <;> rfl

theorem increase_comm (cfg : RecoveryNeutrality.Config) (t : RecoveryNeutrality.Tracker)
    (c : ChainId) (a : AssetId) (x : UInt256) :
    increaseChainBalance (toStorage cfg t) c a x =
      (RecoveryNeutrality.increaseChainBalance t c a x).map (toStorage cfg) := by
  unfold increaseChainBalance RecoveryNeutrality.increaseChainBalance
  rw [checkedAdd_eq]
  show (checkedAdd (t.chainBalance c a) x).map _ = _
  cases checkedAdd (t.chainBalance c a) x <;> rfl

theorem addWithdrawal_comm (cfg : RecoveryNeutrality.Config) (t : RecoveryNeutrality.Tracker)
    (a : AssetId) (x : UInt256) :
    addWithdrawalToL1 (toStorage cfg t) a x =
      (RecoveryNeutrality.addWithdrawalToL1 t a x).map (toStorage cfg) := by
  unfold addWithdrawalToL1 RecoveryNeutrality.addWithdrawalToL1
  rw [checkedAdd_eq]
  show (checkedAdd (t.interopInfo a).totalWithdrawalsToL1 x).map _ = _
  cases checkedAdd (t.interopInfo a).totalWithdrawalsToL1 x with
  | none => rfl
  | some w => simp only [Option.map_some, toStorage_setInterop]; rfl

theorem addDeposit_comm (cfg : RecoveryNeutrality.Config) (t : RecoveryNeutrality.Tracker)
    (a : AssetId) (x : UInt256) :
    addDepositFromL1 (toStorage cfg t) a x =
      (RecoveryNeutrality.addDepositFromL1 t a x).map (toStorage cfg) := by
  unfold addDepositFromL1 RecoveryNeutrality.addDepositFromL1
  rw [checkedAdd_eq]
  show (checkedAdd (t.interopInfo a).totalSuccessfulDepositsFromL1 x).map _ = _
  cases checkedAdd (t.interopInfo a).totalSuccessfulDepositsFromL1 x with
  | none => rfl
  | some w => simp only [Option.map_some, toStorage_setInterop]; rfl

/-! ## Registration -/

theorem RegisterNewTokenIsCanonical : Properties.RegisterNewTokenIsCanonical := by
  intro cfg sys holder upgrader t a o
  unfold registerNewTokenIfNeeded RecoveryNeutrality.registerNewToken
  rw [if_neg (show ¬ (cfg.ntv ≠ (toConfig cfg sys holder upgrader).ntv) from fun h => h rfl)]
  by_cases hr : t.isAssetRegistered a = true
  · rw [if_pos (show (toStorage cfg t).isAssetRegistered a = true from hr), if_pos hr]
  · rw [if_neg (show ¬ (toStorage cfg t).isAssetRegistered a = true from hr), if_neg hr]
    by_cases ho : o = cfg.thisChain
    · rw [if_pos (show o = (toConfig cfg sys holder upgrader).thisChain from ho), if_pos ho,
        toStorage_markRegistered, toStorage_setChainBalance]
      subst ho
      rfl
    · rw [if_neg (show ¬ o = (toConfig cfg sys holder upgrader).thisChain from ho), if_neg ho,
        toStorage_markRegistered]
      rfl

theorem RegisterLegacyIsCanonical : Properties.RegisterLegacyIsCanonical := by
  intro cfg sys holder upgrader reads t a tok
  unfold registerLegacyTokenInner RecoveryNeutrality.registerLegacyInner Native
  dsimp only [toConfig]
  by_cases h1 : sys.origin a = 0
  · simp only [h1, ↓reduceIte, Option.map_none]
  simp only [h1, ↓reduceIte]
  by_cases h2 : tok = 0
  · simp only [h2, ↓reduceIte, Option.map_none]
  simp only [h2, ↓reduceIte]
  by_cases h3 : sys.origin a = cfg.thisChain
  · simp only [h3, ↓reduceIte]
    by_cases h4 : t.chainBalance cfg.thisChain a = 0
    · have h4' : (toStorage cfg t).chainBalance cfg.thisChain a = 0 := h4
      simp only [h4, h4', ne_eq, not_true_eq_false, ↓reduceIte, Option.map_some,
        toStorage_markRegistered, toStorage_setChainBalance]
      rfl
    · have h4' : ¬ (toStorage cfg t).chainBalance cfg.thisChain a = 0 := h4
      simp only [h4, h4', ne_eq, not_false_eq_true, ↓reduceIte, Option.map_none]
  · simp only [h3, ↓reduceIte, Option.map_some, toStorage_markRegistered]
    rfl

theorem registerIfNeeded_comm (cfg : RecoveryNeutrality.Config) (sys : RecoveryNeutrality.Sys)
    (holder upgrader : Address) (reads : RecoveryNeutrality.TokenReads)
    (t : RecoveryNeutrality.Tracker) (a : AssetId) (tok : Address) :
    registerLegacyTokenIfNeeded (toConfig cfg sys holder upgrader) (toStorage cfg t)
        (toReads reads) a tok =
      (RecoveryNeutrality.registerIfNeeded cfg sys reads t a tok).map (toStorage cfg) := by
  unfold registerLegacyTokenIfNeeded RecoveryNeutrality.registerIfNeeded
  by_cases hr : t.isAssetRegistered a = true
  · simp [toStorage, hr]
  · rw [if_neg (by simpa [toStorage] using hr), if_neg hr]
    exact RegisterLegacyIsCanonical cfg sys holder upgrader reads t a tok

/-! ## The flow hooks -/

theorem initiateInner_comm (cfg : RecoveryNeutrality.Config) (sys : RecoveryNeutrality.Sys)
    (holder upgrader : Address) (reads : RecoveryNeutrality.TokenReads) (d : ChainId) (a : AssetId)
    (x : UInt256) (o : ChainId) :
    initiateInner (toConfig cfg sys holder upgrader) (toStorage cfg sys.trk) sys.sl (toReads reads)
        d a x o =
      (RecoveryNeutrality.initiateInner cfg sys reads d a x o).map (toStorage cfg) := by
  unfold initiateInner RecoveryNeutrality.initiateInner
  simp only [toConfig]
  by_cases h0 : sys.token a = 0
  · simp only [h0, ↓reduceIte, Option.map_none]
  simp only [h0, ↓reduceIte]
  have hreg := registerIfNeeded_comm cfg sys holder upgrader reads sys.trk a (sys.token a)
  simp only [toConfig] at hreg
  rw [hreg]
  cases RecoveryNeutrality.registerIfNeeded cfg sys reads sys.trk a (sys.token a) with
  | none => rfl
  | some t₁ =>
    simp only [Option.map_some, Option.bind_some]
    by_cases ho : o = cfg.thisChain
    · simp only [ho, ite_true, decrease_comm]
      cases RecoveryNeutrality.decreaseChainBalance t₁ cfg.thisChain a x with
      | none => rfl
      | some t₂ =>
        simp only [Option.map_some, Option.bind_some]
        show (if d = cfg.l1 ∧ sys.sl = cfg.l1 then _ else _) = _
        split
        · exact addWithdrawal_comm cfg t₂ a x
        · rfl
    · simp only [ho, ite_false, Option.bind_some]
      show (if d = cfg.l1 ∧ sys.sl = cfg.l1 then _ else _) = _
      split
      · exact addWithdrawal_comm cfg t₁ a x
      · rfl

theorem finalizeInner_comm (cfg : RecoveryNeutrality.Config) (sys : RecoveryNeutrality.Sys)
    (holder upgrader : Address) (reads : RecoveryNeutrality.TokenReads) (c : ChainId) (a : AssetId)
    (x : UInt256) (isNative : Bool) (tok : Address) :
    finalizeInner (toConfig cfg sys holder upgrader) (toStorage cfg sys.trk) sys.sl (toReads reads)
        c a x isNative tok =
      (RecoveryNeutrality.finalizeInner cfg sys reads c a x isNative tok).map (toStorage cfg) := by
  unfold finalizeInner RecoveryNeutrality.finalizeInner
  rw [registerIfNeeded_comm]
  cases RecoveryNeutrality.registerIfNeeded cfg sys reads sys.trk a tok with
  | none => rfl
  | some t₁ =>
    simp only [Option.map_some, Option.bind_some]
    cases isNative with
    | true =>
      simp only [ite_true, toConfig, increase_comm]
      cases RecoveryNeutrality.increaseChainBalance t₁ cfg.thisChain a x with
      | none => rfl
      | some t₂ =>
        simp only [Option.map_some, Option.bind_some]
        show (if c = cfg.l1 ∧ sys.sl = cfg.l1 then _ else _) = _
        split
        · exact addDeposit_comm cfg t₂ a x
        · rfl
    | false =>
      simp only [Bool.false_eq_true, ite_false, Option.bind_some]
      show (if c = cfg.l1 ∧ sys.sl = cfg.l1 then _ else _) = _
      split
      · exact addDeposit_comm cfg t₁ a x
      · rfl

theorem TrackerInitiateIsCanonical : Properties.TrackerInitiateIsCanonical := by
  intro cfg sys holder upgrader reads d a x
  unfold handleInitiateBridgingOnL2 RecoveryNeutrality.trackerInitiate
  rw [if_neg (by simp [toConfig])]
  exact initiateInner_comm cfg sys holder upgrader reads d a x (sys.origin a)

theorem TrackerInitiateBaseIsCanonical : Properties.TrackerInitiateBaseIsCanonical := by
  intro cfg sys holder upgrader reads d x
  unfold handleInitiateBaseTokenBridgingOnL2 RecoveryNeutrality.trackerInitiateBase
  rw [if_neg (by simp [toConfig])]
  exact initiateInner_comm cfg sys holder upgrader reads d cfg.base x (sys.origin cfg.base)

theorem TrackerFinalizeIsCanonical : Properties.TrackerFinalizeIsCanonical := by
  intro cfg sys holder upgrader reads c a x
  unfold handleFinalizeBridgingOnL2 RecoveryNeutrality.trackerFinalize
  rw [if_neg (by simp [toConfig])]
  exact finalizeInner_comm cfg sys holder upgrader reads c a x _ (sys.token a)

theorem TrackerFinalizeBaseIsCanonical : Properties.TrackerFinalizeBaseIsCanonical := by
  intro cfg sys holder upgrader reads caller c x hcaller
  unfold handleFinalizeBaseTokenBridgingOnL2 RecoveryNeutrality.trackerFinalizeBase
  rw [if_neg (by rcases hcaller with h | h <;> simp [toConfig, h])]
  by_cases hx : x = 0
  · simp [hx]
  rw [if_neg hx, if_neg hx]
  by_cases hb : cfg.base = 0
  · simp [toStorage, hb]
  rw [if_neg (by simpa [toStorage] using hb), if_neg hb]
  exact finalizeInner_comm cfg sys holder upgrader reads c cfg.base x false cfg.baseTokenAddr

/-! ## The recovery guard -/

theorem VaultRecoverGuardIsHeadGuard : Properties.VaultRecoverGuardIsHeadGuard := by
  intro cfg sys holder upgrader a d
  simp [RecoveryAccountingNeutral, Native, toConfig, toStorage, RecoveryNeutrality.Guards.v35]

theorem VaultRecoverChecksHeadGuard : Properties.VaultRecoverChecksHeadGuard := by
  intro cfg sys holder upgrader reads d a m hg
  rw [VaultRecoverGuardIsHeadGuard] at hg
  cases m with
  | none => rfl
  | some md =>
    simp only [RecoveryNeutrality.Guards.v35, true_and, not_and_or, not_not] at hg
    simp only [RecoveryNeutrality.vaultRecover, RecoveryNeutrality.Guards.v35, true_and]
    rcases hg with h | h
    · simp only [h, ↓reduceIte]
    · by_cases h1 : d = cfg.l1
      · simp only [h1, ↓reduceIte]
      · have h' : a = cfg.base ∧ sys.origin a = cfg.thisChain := by tauto
        rw [if_neg h1, if_pos h']

end Contracts.L2AssetTracker.RecoveryNeutralityRefinement
