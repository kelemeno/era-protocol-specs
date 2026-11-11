import EraSpec.Contracts.NativeTokenVaultBase.Properties.TrackerHooks
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.Resolution
import EraSpec.Contracts.L2AssetTracker.Proofs.Accounting

/-! # Proofs: the deployed chain-balance hooks -/

namespace Contracts.NativeTokenVaultBase

open Contracts.L2AssetTracker (checkedAdd checkedSub checkedAdd_eq_some checkedSub_eq_some
  checkedSub_of_checkedAdd)

variable {Accounting : Type}

/-! ## L1 -/

theorem L1HooksCancel : Properties.L1HooksCancel := by
  intro thisChain metadata a a' _ _ _ asset amount h
  change l1ToChain thisChain a asset amount = some a' at h
  change l1FromChain thisChain a' asset amount = some a
  unfold l1ToChain at h
  by_cases hn : a.originChainId asset = thisChain
  · rw [ite_eq_left hn, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    have hv' := checkedSub_of_checkedAdd hv
    simp only [l1FromChain, hn, ite_true, Function.update_self, hv', Option.map_some,
      Function.update_idem, Function.update_eq_self]
  · rw [ite_eq_right hn] at h
    cases h
    unfold l1FromChain
    rw [ite_eq_right hn]

theorem L1NativeHooksMoveBridgedOut : Properties.L1NativeHooksMoveBridgedOut := by
  intro thisChain acc asset amount hn
  have hto : l1ToChain thisChain acc asset amount =
      (checkedAdd (acc.bridgedOut asset) amount).map fun v =>
        { acc with bridgedOut := Function.update acc.bridgedOut asset v } := by
    unfold l1ToChain; rw [ite_eq_left hn]
  have hfrom : l1FromChain thisChain acc asset amount =
      (checkedSub (acc.bridgedOut asset) amount).map fun v =>
        { acc with bridgedOut := Function.update acc.bridgedOut asset v } := by
    unfold l1FromChain; rw [ite_eq_left hn]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hto, L2AssetTracker.exists_map_eq_some]
    constructor
    · rintro ⟨v, hv⟩; exact (checkedAdd_eq_some.1 hv).1
    · intro h
      obtain ⟨v, hv, _⟩ := L2AssetTracker.checkedAdd_some_of_lt h
      exact ⟨v, hv⟩
  · intro acc' h
    rw [hto, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    exact ⟨rfl, by simp [(checkedAdd_eq_some.1 hv).2], fun b hb => by simp [hb]⟩
  · rw [hfrom, L2AssetTracker.exists_map_eq_some]
    constructor
    · rintro ⟨v, hv⟩; exact (checkedSub_eq_some.1 hv).1
    · intro h
      obtain ⟨v, hv, _⟩ := L2AssetTracker.checkedSub_some_of_le h
      exact ⟨v, hv⟩
  · intro acc' h
    rw [hfrom, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    exact ⟨rfl, by simp [(checkedSub_eq_some.1 hv).2], fun b hb => by simp [hb]⟩

theorem L1BridgedBranchHooksAreIdentity : Properties.L1BridgedBranchHooksAreIdentity := by
  intro thisChain metadata acc _ _ _ asset amount hn
  refine ⟨?_, ?_⟩
  · change l1ToChain thisChain acc asset amount = some acc
    unfold l1ToChain
    rw [ite_eq_right hn]
  · change l1FromChain thisChain acc asset amount = some acc
    unfold l1FromChain
    rw [ite_eq_right hn]

theorem L1PrepareThenRecoverRoundTrip : Properties.L1PrepareThenRecoverRoundTrip := by
  intro thisChain metadata s r out hw hp
  exact PrepareThenRecoverRoundTrip L1Ledger (l1Hooks thisChain metadata)
    (l1ResolutionHooks thisChain) s r out (L1HooksCancel thisChain metadata) hw hp

private theorem prepare_inScope {hooks : Hooks Accounting} {s : State Accounting} {r : Request}
    {out : Result Accounting} (h : prepare hooks s r = some out) : InScope s r := by
  unfold prepare at h
  split at h
  · rename_i hg; exact hg.1
  · cases h

theorem L1BridgedResolutionLeavesLedger : Properties.L1BridgedResolutionLeavesLedger := by
  intro thisChain metadata s hagree
  -- the tracked asset is bridged on L1, so both hooks are the identity on it
  refine ⟨fun r out hw hp => ?_, fun c t h => ?_, fun c t h => ?_⟩
  · have hacc : (l1Hooks thisChain metadata).account s.accounting s.token r.destinationChain
        r.assetId r.data.amount = some out.state.accounting := preparation_accounting hp
    have hasset := (preparation_asset_binding hw hp).1
    have hscope := prepare_inScope hp
    have hid' : s.accounting.originChainId r.assetId ≠ thisChain := by
      rw [hasset, hagree.2, hagree.1]; exact hscope.2.2.2.1
    rw [(L1BridgedBranchHooksAreIdentity thisChain metadata _ s.token s.token _ _ _ hid').1] at hacc
    exact (Option.some.inj hacc).symm
  · obtain ⟨_, hreg, hhook, _⟩ := BridgeMintExact L1Ledger _ s t c h
    have hid' : s.accounting.originChainId c.assetId ≠ thisChain := by
      rw [hreg.2.1, hagree.2, hagree.1]; exact hreg.2.2.1
    rw [(L1BridgedBranchHooksAreIdentity thisChain metadata _ s.token s.token _ _ _ hid').2] at hhook
    exact (Option.some.inj hhook).symm
  · obtain ⟨_, hreg, hhook, _⟩ := RecoverExact L1Ledger _ s t c h
    have hid' : s.accounting.originChainId c.assetId ≠ thisChain := by
      rw [hreg.2.1, hagree.2, hagree.1]; exact hreg.2.2.1
    rw [(L1BridgedBranchHooksAreIdentity thisChain metadata _ s.token s.token _ _ _ hid').2] at hhook
    exact (Option.some.inj hhook).symm

/-! ## The generalized law -/

theorem HooksCancelIsModuloNothing : Properties.HooksCancelIsModuloNothing := by
  intro Accounting hooks rh
  constructor
  · intro h a a' before after chain asset amount _ ha
    exact ⟨a, rfl, h a a' before after chain asset amount ha⟩
  · intro h a a' before after chain asset amount ha
    obtain ⟨a₀, h₀, hf⟩ := h a a' before after chain asset amount trivial ha
    cases h₀
    exact hf

private theorem state_with_accounting {s t : State Accounting} {a₀ : Accounting}
    (h1 : t.config = s.config) (h2 : t.registry = s.registry) (h3 : t.paused = s.paused)
    (h4 : t.token = s.token) (h5 : t.accounting = a₀) : t = { s with accounting := a₀ } := by
  cases t
  cases s
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  rfl

theorem PrepareThenRecoverRoundTripModulo : Properties.PrepareThenRecoverRoundTripModulo := by
  intro Accounting hooks rh Off reg s r out hcancel hw hp hoff
  have hacc := preparation_accounting hp
  obtain ⟨a₀, hreg, hback⟩ :=
    hcancel _ _ s.token out.state.token r.destinationChain r.assetId r.data.amount hoff hacc
  obtain ⟨_, _, t, ht⟩ :=
    PrepareThenRecoverEnabled Accounting hooks rh s r out a₀ hw hp hback
  obtain ⟨htok, hcfg, hregy, hpause, _, hfrom⟩ :=
    PrepareThenRecoverRestoresToken Accounting hooks rh s r out s.config.router t hw.1 hp ht
  have hacc' : t.accounting = a₀ := by
    rw [hback] at hfrom
    exact (Option.some.inj hfrom).symm
  have hts := state_with_accounting hcfg hregy hpause htok hacc'
  rw [hts] at ht
  refine ⟨a₀, hreg, ht, ?_⟩
  simp only [recoverTransact, transact, hp, ht, commitResolution]

/-! ## L2 -/

theorem L2HooksCancelModuloRegistration : Properties.L2HooksCancelModuloRegistration := by
  intro cfg metadata a a' before after chain asset amount hoff h
  change (L2AssetTracker.handleInitiateBridgingOnL2 cfg a.st a.sl
    (L2AssetTracker.tokenReads cfg before) cfg.ntv chain asset amount
    (cfg.ntvOriginChainId asset)).map (fun st => { a with st := st }) = some a' at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨st', hinit, rfl⟩ := h
  have hoff' : chain ≠ a.st.l1ChainId ∨ (a.sl ≠ a.st.l1ChainId ∧ a.sl ≠ a.st.l1ChainId) := by
    rcases hoff with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, h⟩
  obtain ⟨st₀, hreg, hfin, _⟩ := L2AssetTracker.TrackerHooksCancelOffL1 cfg a.st st' a.sl a.sl
    (L2AssetTracker.tokenReads cfg before) (L2AssetTracker.tokenReads cfg after) chain asset amount
    hinit hoff'
  refine ⟨{ a with st := st₀ }, ?_, ?_⟩
  · show (L2AssetTracker.registerLegacyTokenIfNeeded cfg a.st (L2AssetTracker.tokenReads cfg before)
      asset (cfg.ntvTokenAddress asset)).map (fun st => { a with st := st }) = _
    rw [hreg]; rfl
  · show (L2AssetTracker.handleFinalizeBridgingOnL2 cfg st' a.sl
      (L2AssetTracker.tokenReads cfg after) cfg.ntv chain asset amount
      (cfg.ntvOriginChainId asset) (cfg.ntvTokenAddress asset)).map
        (fun st => { ({ a with st := st' } : L2Accounting) with st := st }) = _
    rw [hfin]; rfl

theorem AtomicRecoveryRestoresVaultAndTrackerL2 :
    Properties.AtomicRecoveryRestoresVaultAndTrackerL2 := by
  intro cfg metadata s r out hw hp hoff
  obtain ⟨a₀, hreg, hrec, htr⟩ := PrepareThenRecoverRoundTripModulo L2Accounting
    (l2Hooks cfg metadata) (l2ResolutionHooks cfg) L2OffL1 (l2Registration cfg) s r out
    (L2HooksCancelModuloRegistration cfg metadata) hw hp hoff
  change (L2AssetTracker.registerLegacyTokenIfNeeded cfg s.accounting.st
    (L2AssetTracker.tokenReads cfg s.token) r.assetId (cfg.ntvTokenAddress r.assetId)).map
      (fun st => { s.accounting with st := st }) = some a₀ at hreg
  rw [Option.map_eq_some_iff] at hreg
  obtain ⟨st₀, hreg₀, rfl⟩ := hreg
  refine ⟨st₀, hreg₀, hrec, htr, fun hr => ?_⟩
  have hst : st₀ = s.accounting.st := by
    rw [L2AssetTracker.registerLegacyTokenIfNeeded_of_registered hr] at hreg₀
    exact (Option.some.inj hreg₀).symm
  subst hst
  exact ⟨rfl, hrec⟩

/-! ## The first bridge on L2 -/

/-- A successful fresh registration's accounting is the tracker hook's result. -/
private theorem registerFreshBranch_tracker {reg : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {registered : Registered Accounting}
    (h : registerFreshBranch reg s origin = some registered) :
    ∃ registry tok, reg.registerTracker s.accounting registry tok s.config.assetId
      s.config.originChainId = some registered.state.accounting := by
  unfold registerFreshBranch at h
  split at h
  · unfold registerRepresentation at h
    split at h
    · cases hd : reg.deploy s.config.originChainId origin with
      | none => simp only [hd, reduceCtorEq] at h
      | some deployed =>
        simp only [hd] at h
        cases hi : BridgedStandardERC20.initializeToken BridgedStandardERC20.freshProxy
            s.config.vault s.config.assetId origin reg.metadataDecoded with
        | none => simp only [hi, reduceCtorEq] at h
        | some initialized =>
          simp only [hi] at h
          split at h
          · cases ht : reg.registerTracker s.accounting
                (installRegistry s.registry s.config.assetId deployed) initialized.token
                s.config.assetId s.config.originChainId with
            | none => simp only [ht, reduceCtorEq] at h
            | some accounting =>
              simp only [ht, Option.some.injEq] at h
              subst h
              exact ⟨_, _, ht⟩
          · cases h
    · cases h
  · cases h

theorem L2FirstBridgeRegistersAsNew : Properties.L2FirstBridgeRegistersAsNew := by
  intro cfg reg s c t hreg hr hnn h
  obtain ⟨_, hfirst, _, _, _, _, _, _, _, _, _, _, registered, hfresh, _, hhook⟩ :=
    FirstBridgeMintExact L2Accounting reg _ s c t h
  obtain ⟨registry, tok, htr⟩ := registerFreshBranch_tracker hfresh
  rw [hreg] at htr
  change (L2AssetTracker.registerNewTokenIfNeeded cfg s.accounting.st cfg.ntv s.config.assetId
    s.config.originChainId).map (fun st => { s.accounting with st := st }) =
      some registered.state.accounting at htr
  rw [Option.map_eq_some_iff] at htr
  obtain ⟨st₁, hst₁, hacc⟩ := htr
  unfold L2AssetTracker.registerNewTokenIfNeeded at hst₁
  rw [ite_eq_right (not_not.2 rfl), ite_eq_right (by simpa using hr), ite_eq_right hnn] at hst₁
  have hst₁' := (Option.some.inj hst₁).symm
  -- the inbound hook, on the freshly registered asset, keeps its snapshot
  change (L2AssetTracker.handleFinalizeBridgingOnL2 cfg registered.state.accounting.st
    registered.state.accounting.sl (L2AssetTracker.tokenReads cfg registered.state.token) cfg.ntv
    c.chain c.assetId c.data.amount (cfg.ntvOriginChainId c.assetId)
    (cfg.ntvTokenAddress c.assetId)).map (fun st => { registered.state.accounting with st := st }) =
      some t.accounting at hhook
  rw [Option.map_eq_some_iff] at hhook
  obtain ⟨st₂, hst₂, hacc₂⟩ := hhook
  unfold L2AssetTracker.handleFinalizeBridgingOnL2 at hst₂
  rw [ite_eq_right (not_not.2 rfl)] at hst₂
  obtain ⟨st₃, h₃, _, hreg₂, hsnap₂, _⟩ := L2AssetTracker.finalizeInner_spec hst₂
  have hasset : c.assetId = s.config.assetId := hfirst.2
  have hregd : registered.state.accounting.st.isAssetRegistered c.assetId = true := by
    rw [← hacc, hst₁', hasset]; simp
  rw [L2AssetTracker.registerLegacyTokenIfNeeded_of_registered hregd] at h₃
  cases h₃
  rw [← hacc₂, ← hasset]
  refine ⟨hreg₂, ?_⟩
  rw [hsnap₂, ← hacc, hst₁', hasset]
  simp

/-! ## Witnesses -/

/-- Two values differ if some computable field of theirs does. -/
theorem trackerHooks_ne_of_field {α β : Type} {x y : α} (f : α → β) (h : f x ≠ f y) : x ≠ y :=
  fun e => h (congrArg f e)

namespace TrackerHooksExample

open ResolutionExample

/-- The tracker's view of `ResolutionExample.exConfig`: vault `1`, this chain `1`, asset `3`
from chain `4` with local token `5`. -/
def l2Cfg : L2AssetTracker.Config :=
  ⟨1, 20, 21, 22, 1, fun a => if a = 3 then 4 else 0, fun a => if a = 3 then 5 else 0, 9, 0⟩

/-- Tracker storage with every asset registered or none, `L1_CHAIN_ID = l1`, `initL2` done. -/
def trk (reg : Bool) (l1 : UInt256) : L2AssetTracker.Storage :=
  ⟨fun _ _ => 0, fun _ => reg, l1, 0, fun _ => ⟨0, 0⟩, fun _ => ⟨false, 0⟩, false, true⟩

/-- A metadata dependency that always succeeds with empty metadata. -/
def md0 : BridgedStandardERC20.State → UInt256 → Option Bytes := fun _ _ => some []

/-- The L1 ledger agreeing with `exConfig`: asset `3` from chain `4`; asset `8` native on chain
`1` with `bridgedOut` `10`. -/
def l1Acc : L1Ledger :=
  ⟨fun a => if a = 3 then 4 else if a = 8 then 1 else 0, fun a => if a = 8 then 10 else 0⟩

/-- The example vault state, holder `11` with `4` units, and tracker storage `trk reg l1` on
settlement layer `sl`. -/
def l2State (reg : Bool) (l1 sl : UInt256) : State L2Accounting :=
  stateWith (tokenWith 11 4) ⟨trk reg l1, sl⟩

/-- A placeholder result, never reached. -/
def dummyResult : Result L2Accounting := ⟨l2State false 0 0, ⟨0, 0, 0, 0, []⟩⟩

/-- The preparation of `prepRequest 12` (one unit from `11` towards chain `6`). -/
def l2Out (reg : Bool) (l1 sl : UInt256) : Result L2Accounting :=
  (prepare (l2Hooks l2Cfg md0) (l2State reg l1 sl) (prepRequest 12)).getD dummyResult

/-- The router's recovery, from `u`, of the data of `o`. -/
def l2Rec (u : State L2Accounting) (o : Result L2Accounting) : State L2Accounting :=
  (bridgeRecoverFailedTransfer (l2ResolutionHooks l2Cfg) u (recoveryCall 2 (prepRequest 12) o.data)).getD u

end TrackerHooksExample

open ResolutionExample TrackerHooksExample in
theorem L1TrackerHooksSatisfiable : Properties.L1TrackerHooksSatisfiable := by
  obtain ⟨out, hp⟩ := prep_enabled (l1Hooks 1 md0) l1Acc l1Acc 12 rfl rfl
  have hw := stateWith_wf (A := L1Ledger) (holder := 11) (by decide) 4 l1Acc
  exact ⟨1, md0, _, _, out, l1Acc, _, 8, 10, 11, hw, ⟨rfl, by decide⟩, hp, by decide, by decide,
    rfl, trackerHooks_ne_of_field (fun acc => (L1Ledger.bridgedOut acc 8).val) (by decide),
    by decide, by decide⟩

open ResolutionExample TrackerHooksExample in
theorem AtomicRecoveryL2Satisfiable : Properties.AtomicRecoveryL2Satisfiable :=
  ⟨l2Cfg, md0, l2State true 9 9, prepRequest 12, _, stateWith_wf (by decide) 4 _, rfl, by decide,
    rfl, by decide⟩

open ResolutionExample TrackerHooksExample in
theorem L2L1DestinationCountersDiverge : Properties.L2L1DestinationCountersDiverge := by
  have hw : WellFormed (l2State true 6 6) := stateWith_wf (by decide) 4 _
  have hp : prepare (l2Hooks l2Cfg md0) (l2State true 6 6) (prepRequest 12) =
      some (l2Out true 6 6) := rfl
  have ht : bridgeRecoverFailedTransfer (l2ResolutionHooks l2Cfg) (l2Out true 6 6).state
      (recoveryCall (l2State true 6 6).config.router (prepRequest 12) (l2Out true 6 6).data) =
      some (l2Rec (l2Out true 6 6).state (l2Out true 6 6)) := rfl
  refine ⟨l2Cfg, md0, l2State true 6 6, prepRequest 12, l2Out true 6 6,
    l2Rec (l2Out true 6 6).state (l2Out true 6 6), hw, rfl, rfl, rfl, hp, by decide, ht,
    (PrepareThenRecoverRestoresToken L2Accounting _ _ _ _ _ _ _ hw.1 hp ht).1, by decide,
    by decide,
    trackerHooks_ne_of_field
      (fun x : State L2Accounting => (x.accounting.st.interopInfo 3).totalWithdrawalsToL1.val)
      (by decide), fun hc => ?_⟩
  have h := hc ⟨trk true 6, 6⟩ _ (tokenWith 11 4) (tokenWith 11 4) 6 3 1 rfl
  have h' := congrArg
    (Option.map fun x : L2Accounting => (x.st.interopInfo 3).totalWithdrawalsToL1.val) h
  revert h'
  decide

open ResolutionExample TrackerHooksExample in
theorem L2SlSwitchBetweenPrepareAndRecover : Properties.L2SlSwitchBetweenPrepareAndRecover := by
  have hw : WellFormed (l2State true 6 6) := stateWith_wf (by decide) 4 _
  have hp : prepare (l2Hooks l2Cfg md0) (l2State true 6 6) (prepRequest 12) =
      some (l2Out true 6 6) := rfl
  -- the recovery from the unmodified state restores the token
  have ht₀ : bridgeRecoverFailedTransfer (l2ResolutionHooks l2Cfg) (l2Out true 6 6).state
      (recoveryCall (l2State true 6 6).config.router (prepRequest 12) (l2Out true 6 6).data) =
      some (l2Rec (l2Out true 6 6).state (l2Out true 6 6)) := rfl
  have htok₀ := (PrepareThenRecoverRestoresToken L2Accounting _ _ _ _ _ _ _ hw.1 hp ht₀).1
  -- the recovery after the switch to layer `7`
  have ht : bridgeRecoverFailedTransfer (l2ResolutionHooks l2Cfg)
      { (l2Out true 6 6).state with accounting := { (l2Out true 6 6).state.accounting with sl := 7 } }
      (recoveryCall (l2State true 6 6).config.router (prepRequest 12) (l2Out true 6 6).data) =
      some (l2Rec { (l2Out true 6 6).state with
        accounting := { (l2Out true 6 6).state.accounting with sl := 7 } } (l2Out true 6 6)) := rfl
  have hm := (RecoverExact L2Accounting _ _ _ _ ht).2.2.2.1
  have hm₀ := (RecoverExact L2Accounting _ _ _ _ ht₀).2.2.2.1
  have htok : (l2Rec { (l2Out true 6 6).state with
      accounting := { (l2Out true 6 6).state.accounting with sl := 7 } } (l2Out true 6 6)).token =
      (l2State true 6 6).token := by
    rw [← htok₀]
    exact Option.some.inj (hm.symm.trans hm₀)
  refine ⟨l2Cfg, md0, l2State true 6 6, prepRequest 12, l2Out true 6 6, 7, _, hw, rfl, rfl, rfl,
    by decide, hp, by decide, ht, htok, by decide, by decide,
    trackerHooks_ne_of_field
      (fun st : L2AssetTracker.Storage => (st.interopInfo 3).totalWithdrawalsToL1.val)
      (by decide)⟩

open ResolutionExample TrackerHooksExample in
theorem L2FirstLegacyBridgeLeavesRegistration :
    Properties.L2FirstLegacyBridgeLeavesRegistration := by
  have hw : WellFormed (l2State false 9 9) := stateWith_wf (by decide) 4 _
  have hp : prepare (l2Hooks l2Cfg md0) (l2State false 9 9) (prepRequest 12) =
      some (l2Out false 9 9) := rfl
  have ht : bridgeRecoverFailedTransfer (l2ResolutionHooks l2Cfg) (l2Out false 9 9).state
      (recoveryCall (l2State false 9 9).config.router (prepRequest 12) (l2Out false 9 9).data) =
      some (l2Rec (l2Out false 9 9).state (l2Out false 9 9)) := rfl
  obtain ⟨htok, hcfg, hreg, hpause, _⟩ :=
    PrepareThenRecoverRestoresToken L2Accounting _ _ _ _ _ _ _ hw.1 hp ht
  exact ⟨l2Cfg, md0, l2State false 9 9, prepRequest 12, l2Out false 9 9, _, hw, rfl,
    Or.inl (by decide), hp, by decide, ht, htok, hcfg, hreg, hpause, by decide, by decide,
    by decide,
    trackerHooks_ne_of_field
      (fun x : State L2Accounting => x.accounting.st.isAssetRegistered 3) (by decide)⟩

open ResolutionExample TrackerHooksExample in
theorem L2FirstBridgeSatisfiable : Properties.L2FirstBridgeSatisfiable :=
  ⟨l2Cfg, { firstHooks with registerTracker := l2RegistrationHook l2Cfg },
    ⟨exConfig, ⟨fun _ => 0, fun _ => 0⟩, false, ⟨trk false 9, 9⟩⟩, mintCall, _, rfl, rfl,
    by decide, by decide, rfl⟩

end Contracts.NativeTokenVaultBase
