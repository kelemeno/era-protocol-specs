import EraSpec.Contracts.NativeTokenVaultBase.Properties.Resolution
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.RepresentationPreparation
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.Initialization

namespace Contracts.NativeTokenVaultBase

variable {Accounting : Type}

/-! ## Extensionality and views of the token operations -/

private theorem token_ext {x y : BridgedStandardERC20.State} (hc : x.config = y.config)
    (hb : ∀ a, x.balances a = y.balances a) (hs : x.totalSupply = y.totalSupply) : x = y := by
  cases x
  cases y
  simp only at hc hs
  subst hc hs
  congr 1
  exact funext hb

private theorem state_ext {x y : State Accounting} (h1 : x.config = y.config)
    (h2 : x.registry = y.registry) (h3 : x.paused = y.paused) (h4 : x.token = y.token)
    (h5 : x.accounting = y.accounting) : x = y := by
  cases x
  cases y
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  rfl

private theorem burn_view_res {tok burned : BridgedStandardERC20.State} {caller owner : Address}
    {amount : UInt256} (h : BridgedStandardERC20.burn tok caller owner amount = some burned) :
    BridgedStandardERC20.BurnAllowed tok caller owner amount ∧
      burned = BridgedStandardERC20.burnEffect tok owner amount := by
  unfold BridgedStandardERC20.burn at h
  split at h <;> cases h
  exact ⟨‹_›, rfl⟩

private theorem mint_view_res {tok minted : BridgedStandardERC20.State}
    {caller recipient : Address} {amount : UInt256}
    (h : BridgedStandardERC20.mint tok caller recipient amount = some minted) :
    BridgedStandardERC20.MintAllowed tok caller recipient amount ∧
      minted = BridgedStandardERC20.mintEffect tok recipient amount := by
  unfold BridgedStandardERC20.mint at h
  split at h <;> cases h
  exact ⟨‹_›, rfl⟩

/-- Re-minting what a burn removed, to the same account, restores the token exactly. -/
private theorem mint_after_burn {tok burned minted : BridgedStandardERC20.State}
    {caller caller' owner : Address} {amount : UInt256}
    (hl : BridgedStandardERC20.WellFormed tok)
    (hb : BridgedStandardERC20.burn tok caller owner amount = some burned)
    (hm : BridgedStandardERC20.mint burned caller' owner amount = some minted) :
    minted = tok := by
  rcases BridgedStandardERC20.burn_exact hl hb with ⟨_, _, hbal, hsup, hframe, hcfg⟩
  rcases BridgedStandardERC20.mint_exact hm with ⟨_, _, hbal', hsup', hframe', hcfg'⟩
  refine token_ext (hcfg'.trans hcfg) (fun a => ?_) (hsup'.trans hsup)
  by_cases ha : a = owner
  · exact ha ▸ hbal'.trans hbal
  · exact (hframe' a ha).trans (hframe a ha)

/-! ## Views of the resolution operations -/

private theorem hookThenMint_view {rh : ResolutionHooks Accounting} {s t : State Accounting}
    {chain asset : UInt256} {recipient : Address} {amount : UInt256}
    (h : hookThenMint rh s chain asset recipient amount = some t) :
    ∃ accounted minted,
      rh.fromChain s.accounting s.token chain asset amount = some accounted ∧
      BridgedStandardERC20.mint s.token s.config.vault recipient amount = some minted ∧
      t = { s with token := minted, accounting := accounted } := by
  unfold hookThenMint at h
  repeat (split at h <;> try contradiction)
  cases h
  exact ⟨_, _, ‹_›, ‹_›, rfl⟩

private theorem hookThenMint_some {rh : ResolutionHooks Accounting} {s : State Accounting}
    {chain asset : UInt256} {recipient : Address} {amount : UInt256}
    {accounted : Accounting} {minted : BridgedStandardERC20.State}
    (ha : rh.fromChain s.accounting s.token chain asset amount = some accounted)
    (hm : BridgedStandardERC20.mint s.token s.config.vault recipient amount = some minted) :
    hookThenMint rh s chain asset recipient amount =
      some { s with token := minted, accounting := accounted } := by
  simp only [hookThenMint, ha, hm]

private theorem hookThenMint_of_hook_none {rh : ResolutionHooks Accounting}
    {s : State Accounting} {chain asset : UInt256} {recipient : Address} {amount : UInt256}
    (h : rh.fromChain s.accounting s.token chain asset amount = none) :
    hookThenMint rh s chain asset recipient amount = none := by
  simp only [hookThenMint, h]

private theorem hookThenMint_of_mint_none {rh : ResolutionHooks Accounting}
    {s : State Accounting} {chain asset : UInt256} {recipient : Address} {amount : UInt256}
    (h : BridgedStandardERC20.mint s.token s.config.vault recipient amount = none) :
    hookThenMint rh s chain asset recipient amount = none := by
  unfold hookThenMint
  split <;> simp only [h]

private theorem bridgeMint_view {rh : ResolutionHooks Accounting} {s t : State Accounting}
    {c : ResolutionCall} (h : bridgeMint rh s c = some t) :
    (ResolveEntryAllowed s c ∧ RegisteredBridged s c) ∧
      hookThenMint rh s c.chain c.assetId c.data.remoteReceiver c.data.amount = some t :=
  Option.ite_none_right_eq_some.mp h

private theorem recover_view {rh : ResolutionHooks Accounting} {s t : State Accounting}
    {c : ResolutionCall} (h : bridgeRecoverFailedTransfer rh s c = some t) :
    (ResolveEntryAllowed s c ∧ RegisteredBridged s c) ∧
      hookThenMint rh s c.chain c.assetId c.data.originalCaller c.data.amount = some t :=
  Option.ite_none_right_eq_some.mp h

private theorem bridgeMint_of_tail_none {rh : ResolutionHooks Accounting} {s : State Accounting}
    {c : ResolutionCall}
    (h : hookThenMint rh s c.chain c.assetId c.data.remoteReceiver c.data.amount = none) :
    bridgeMint rh s c = none := by
  unfold bridgeMint
  split <;> [exact h; rfl]

private theorem recover_of_tail_none {rh : ResolutionHooks Accounting} {s : State Accounting}
    {c : ResolutionCall}
    (h : hookThenMint rh s c.chain c.assetId c.data.originalCaller c.data.amount = none) :
    bridgeRecoverFailedTransfer rh s c = none := by
  unfold bridgeRecoverFailedTransfer
  split <;> [exact h; rfl]

private theorem not_entry_rejects {rh : ResolutionHooks Accounting} {s : State Accounting}
    {c : ResolutionCall} (h : ¬ ResolveEntryAllowed s c) :
    bridgeMint rh s c = none ∧ bridgeRecoverFailedTransfer rh s c = none := by
  have hn : ¬ (ResolveEntryAllowed s c ∧ RegisteredBridged s c) := fun hg => h hg.1
  exact ⟨by unfold bridgeMint; exact ite_eq_right hn,
    by unfold bridgeRecoverFailedTransfer; exact ite_eq_right hn⟩

/-- The shared exactness of the hook-then-mint tail. -/
private theorem credit_exact {rh : ResolutionHooks Accounting} {s t : State Accounting}
    {chain asset : UInt256} {recipient : Address} {amount : UInt256}
    (h : hookThenMint rh s chain asset recipient amount = some t) :
    rh.fromChain s.accounting s.token chain asset amount = some t.accounting ∧
    BridgedStandardERC20.mint s.token s.config.vault recipient amount = some t.token ∧
    t.token.balances recipient = s.token.balances recipient + amount.val ∧
    t.token.totalSupply = s.token.totalSupply + amount.val ∧
    (∀ a, a ≠ recipient → t.token.balances a = s.token.balances a) ∧
    t.token.config = s.token.config ∧
    t.config = s.config ∧ t.registry = s.registry ∧ t.paused = s.paused := by
  obtain ⟨accounted, minted, ha, hm, rfl⟩ := hookThenMint_view h
  rcases BridgedStandardERC20.mint_exact hm with ⟨_, _, hbal, hsup, hframe, hcfg⟩
  exact ⟨ha, hm, hbal, hsup, hframe, hcfg, rfl, rfl, rfl⟩

private theorem credit_preserves_wellFormed {rh : ResolutionHooks Accounting}
    {s t : State Accounting} {chain asset : UInt256} {recipient : Address} {amount : UInt256}
    (hw : WellFormed s) (h : hookThenMint rh s chain asset recipient amount = some t) :
    WellFormed t := by
  obtain ⟨accounted, minted, _ha, hm, rfl⟩ := hookThenMint_view h
  rcases BridgedStandardERC20.mint_exact hm with ⟨_, _, _, _, _, hcfg⟩
  refine ⟨BridgedStandardERC20.mint_preserves_ledger hw.1 hm, ?_, ?_, hw.2.2.2.1, hw.2.2.2.2⟩
  · exact (congrArg BridgedStandardERC20.Config.vault hcfg).trans hw.2.1
  · exact (congrArg BridgedStandardERC20.Config.assetId hcfg).trans hw.2.2.1

/-! ## Destination `bridgeMint` -/

theorem BridgeMintExact : Properties.BridgeMintExact := by
  intro Accounting rh s t c h
  obtain ⟨⟨he, hs⟩, hm⟩ := bridgeMint_view h
  exact ⟨he, hs, credit_exact hm⟩

theorem BridgeMintAssetBinding : Properties.BridgeMintAssetBinding := by
  intro Accounting rh s t c hr h
  obtain ⟨⟨_he, hs⟩, hm⟩ := bridgeMint_view h
  obtain ⟨_, _, _, _, _, hcfg, _⟩ := credit_exact hm
  refine ⟨hs.2.2.2.1, ?_, ?_⟩
  · exact (congrArg BridgedStandardERC20.Config.assetId hcfg).trans (hr.2.1.trans hs.2.1.symm)
  · exact (congrArg BridgedStandardERC20.Config.vault hcfg).trans hr.1

theorem BridgeMintIgnoresUnreadFields : Properties.BridgeMintIgnoresUnreadFields := by
  intro Accounting rh s c caller origin metadata
  rfl

theorem BridgeMintPreservesWellFormed : Properties.BridgeMintPreservesWellFormed := by
  intro Accounting rh s t c hw h
  exact credit_preserves_wellFormed hw (bridgeMint_view h).2

theorem BridgeMintEnabled : Properties.BridgeMintEnabled := by
  intro Accounting rh s c accounted hr he hs hrec hsup ha
  have hallowed : BridgedStandardERC20.MintAllowed s.token s.config.vault c.data.remoteReceiver
      c.data.amount :=
    ⟨by rw [hr.1]; exact hs.1, hr.1.symm, hrec, hsup⟩
  exact ⟨_, (ite_eq_left ⟨he, hs⟩).trans (hookThenMint_some ha (ite_eq_left hallowed))⟩

/-! ## Source `bridgeRecoverFailedTransfer` -/

theorem RecoverExact : Properties.RecoverExact := by
  intro Accounting rh s t c h
  obtain ⟨⟨he, hs⟩, hm⟩ := recover_view h
  exact ⟨he, hs, credit_exact hm⟩

theorem RecoverIgnoresReceiver : Properties.RecoverIgnoresReceiver := by
  intro Accounting rh s c receiver origin metadata
  rfl

theorem RecoverPreservesWellFormed : Properties.RecoverPreservesWellFormed := by
  intro Accounting rh s t c hw h
  exact credit_preserves_wellFormed hw (recover_view h).2

theorem RecoverEnabled : Properties.RecoverEnabled := by
  intro Accounting rh s c accounted hr he hs hrec hsup ha
  have hallowed : BridgedStandardERC20.MintAllowed s.token s.config.vault c.data.originalCaller
      c.data.amount :=
    ⟨by rw [hr.1]; exact hs.1, hr.1.symm, hrec, hsup⟩
  exact ⟨_, (ite_eq_left ⟨he, hs⟩).trans (hookThenMint_some ha (ite_eq_left hallowed))⟩

/-! ## Round trip -/

private theorem prepare_view_res {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} {out : Result Accounting} (h : prepare hooks s r = some out) :
    InScope s r ∧ EntryAllowed s r ∧ r.msgValue = 0 ∧
    ∃ accounted burned metadata,
      hooks.account s.accounting s.token r.destinationChain r.assetId r.data.amount =
        some accounted ∧
      BridgedStandardERC20.burn s.token s.config.vault r.depositor r.data.amount = some burned ∧
      burned.config.originToken ≠ 0 ∧ s.config.originChainId ≠ 0 ∧
      hooks.metadata burned s.config.originChainId = some metadata ∧
      out = ⟨{ s with token := burned, accounting := accounted }, mintData r burned metadata⟩ := by
  unfold prepare at h
  repeat (split at h <;> try contradiction)
  rename_i hg _ accounted ha hv _ burned hb ho _ metadata hm
  cases h
  exact ⟨hg.1, hg.2, hv, accounted, burned, metadata, ha, hb, ho.1, ho.2, hm, rfl⟩

theorem PrepareThenRecoverRestoresToken : Properties.PrepareThenRecoverRestoresToken := by
  intro Accounting hooks rh s r out router t hl hp hrec
  obtain ⟨_hs, _he, _hv, accounted, burned, metadata, ha, hb, _ho, _hc, _hm, rfl⟩ :=
    prepare_view_res hp
  obtain ⟨_, hc⟩ := recover_view hrec
  obtain ⟨accounted', minted, ha', hm', rfl⟩ := hookThenMint_view hc
  have hmint : minted = s.token := mint_after_burn hl hb hm'
  exact ⟨hmint, rfl, rfl, rfl, ha, ha'⟩

theorem PrepareThenRecoverEnabled : Properties.PrepareThenRecoverEnabled := by
  intro Accounting hooks rh s r out accounted' hw hp ha'
  have hbind := preparation_asset_binding hw hp
  obtain ⟨hs, he, _hv, accounted, burned, metadata, _ha, hb, _ho, _hc, _hm, rfl⟩ :=
    prepare_view_res hp
  obtain ⟨⟨hvault, hcaller, hdep, hbal⟩, rfl⟩ := burn_view_res hb
  have hentry : ResolveEntryAllowed
      { s with token := BridgedStandardERC20.burnEffect s.token r.depositor r.data.amount,
               accounting := accounted }
      (recoveryCall s.config.router r (mintData r (BridgedStandardERC20.burnEffect s.token
        r.depositor r.data.amount) metadata)) :=
    ⟨rfl, rfl, he.2.1⟩
  have hreg : RegisteredBridged
      { s with token := BridgedStandardERC20.burnEffect s.token r.depositor r.data.amount,
               accounting := accounted }
      (recoveryCall s.config.router r (mintData r (BridgedStandardERC20.burnEffect s.token
        r.depositor r.data.amount) metadata)) := by
    refine ⟨hs.1, hbind.1, hs.2.2.2.1, ?_, hs.2.1⟩
    show s.registry.tokenForAsset r.assetId = s.config.tokenAddress
    rw [hbind.1]
    exact hw.2.2.2.1
  have hle := (BridgedStandardERC20.balance_bounded hw.1 r.depositor).1
  have hsz := hw.1.2.1
  have hallowed : BridgedStandardERC20.MintAllowed
      (BridgedStandardERC20.burnEffect s.token r.depositor r.data.amount) s.config.vault
      r.depositor r.data.amount := by
    refine ⟨hvault, hcaller, hdep, ?_⟩
    show s.token.totalSupply - r.data.amount.val + r.data.amount.val < UInt256.size
    omega
  exact ⟨hentry, hreg, _,
    (ite_eq_left ⟨hentry, hreg⟩).trans (hookThenMint_some ha' (ite_eq_left hallowed))⟩

theorem PrepareThenRecoverRoundTrip : Properties.PrepareThenRecoverRoundTrip := by
  intro Accounting hooks rh s r out hcancel hw hp
  have hacc := preparation_accounting hp
  have hback : rh.fromChain out.state.accounting out.state.token r.destinationChain r.assetId
      r.data.amount = some s.accounting := hcancel _ _ _ _ _ _ _ hacc
  obtain ⟨_, _, t, ht⟩ :=
    PrepareThenRecoverEnabled Accounting hooks rh s r out s.accounting hw hp hback
  obtain ⟨htok, hcfg, hreg, hpause, _, hfrom⟩ :=
    PrepareThenRecoverRestoresToken Accounting hooks rh s r out s.config.router t hw.1 hp ht
  have hacc' : t.accounting = s.accounting := by
    rw [hback] at hfrom
    exact (Option.some.inj hfrom).symm
  have hts : t = s := state_ext hcfg hreg hpause htok hacc'
  rw [hts] at ht
  refine ⟨ht, ?_⟩
  simp only [recoverTransact, transact, hp, ht, commitResolution]

/-- Ordinary transfers keep the vault well-formed and change nothing but token balances. -/
private theorem spendReach_frame {s u : State Accounting} (hw : WellFormed s)
    (h : SpendReach s u) :
    WellFormed u ∧ u.config = s.config ∧ u.registry = s.registry ∧ u.paused = s.paused ∧
    u.accounting = s.accounting ∧ u.token.config = s.token.config ∧
    u.token.totalSupply = s.token.totalSupply := by
  induction h with
  | refl => exact ⟨hw, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | tail _ ht ih =>
    obtain ⟨hwu, hc, hr, hp, ha, htc, hts⟩ := ih
    obtain ⟨hl', hsup, hcfg⟩ := BridgedStandardERC20.transfer_preserves_ledger hwu.1 ht
    refine ⟨⟨hl', ?_, ?_, hwu.2.2.2.1, hwu.2.2.2.2⟩, hc, hr, hp, ha, hcfg.trans htc,
      hsup.trans hts⟩
    · exact (congrArg BridgedStandardERC20.Config.vault hcfg).trans hwu.2.1
    · exact (congrArg BridgedStandardERC20.Config.assetId hcfg).trans hwu.2.2.1

theorem RecoverAfterSpending : Properties.RecoverAfterSpending := by
  intro Accounting hooks rh s r out u accounted' hw hp hspend ha'
  have hbind := preparation_asset_binding hw hp
  have hprep := preparation_preserves_ledger hw hp
  have hback := preparation_backed hw hp
  have hdep : r.depositor ≠ 0 := (burn_view_res hback.1).1.2.2.1
  obtain ⟨hs, he, _hv, accounted, burned, metadata, _ha, _hb, _ho, _hc, _hm, rfl⟩ :=
    prepare_view_res hp
  obtain ⟨hwu, hc, hr, hpz, _, _, hts⟩ := spendReach_frame hprep.1 hspend
  have hentry : ResolveEntryAllowed u (recoveryCall s.config.router r
      (mintData r burned metadata)) := by
    refine ⟨rfl, ?_, ?_⟩
    · show s.config.router = u.config.router
      rw [hc]
    · rw [hpz]
      exact he.2.1
  have hscope : RegisteredBridged u (recoveryCall s.config.router r
      (mintData r burned metadata)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hc]; exact hs.1
    · show r.assetId = u.config.assetId
      rw [hc]; exact hbind.1
    · rw [hc]; exact hs.2.2.2.1
    · show u.registry.tokenForAsset r.assetId = u.config.tokenAddress
      rw [hr, hc]
      show s.registry.tokenForAsset r.assetId = s.config.tokenAddress
      rw [hbind.1]
      exact hw.2.2.2.1
    · rw [hc]; exact hs.2.1
  have hsup : u.token.totalSupply + r.data.amount.val < UInt256.size := by
    have h1 : burned.totalSupply + r.data.amount.val = s.token.totalSupply := hback.2.2.1
    have h2 := hw.1.2.1
    have h3 : u.token.totalSupply = burned.totalSupply := hts
    omega
  obtain ⟨t, ht⟩ := RecoverEnabled Accounting rh u _ accounted' hwu.2 hentry hscope hdep hsup ha'
  obtain ⟨_, _, _, _, hbal, hsup', _⟩ := RecoverExact Accounting rh u t _ ht
  refine ⟨hentry, hscope, t, ht, hbal, ?_, RecoverPreservesWellFormed Accounting rh u t _ hwu ht⟩
  have h1 : burned.totalSupply + r.data.amount.val = s.token.totalSupply := hback.2.2.1
  have h3 : u.token.totalSupply = burned.totalSupply := hts
  have h4 : t.token.totalSupply = u.token.totalSupply + r.data.amount.val := hsup'
  omega

theorem PrepareThenDeliverConserves : Properties.PrepareThenDeliverConserves := by
  intro A B hooks rh s r out d d' c hl hp hc hm
  obtain ⟨_, _, _, accounted, burned, metadata, _, hb, _, _, _, rfl⟩ := prepare_view_res hp
  rcases BridgedStandardERC20.burn_exact hl hb with ⟨_, _, hbal, hsup, _, _⟩
  obtain ⟨_, _, _, _, hrecv, hsup', _⟩ := BridgeMintExact B rh d d' c hm
  have hrr : c.data.remoteReceiver = r.data.receiver := by rw [hc]; rfl
  have ham : c.data.amount = r.data.amount := by rw [hc]; rfl
  refine ⟨?_, hbal, ?_⟩
  · rw [← hrr, hrecv, ham]
  · show burned.totalSupply + d'.token.totalSupply = s.token.totalSupply + d.token.totalSupply
    rw [hsup', ham]
    omega

/-! ## Guards and rollback -/

theorem ResolutionWrongRouterRejected : Properties.ResolutionWrongRouterRejected := by
  intro Accounting rh s c h
  exact not_entry_rejects fun hg => h hg.2.1

theorem ResolutionPausedRejected : Properties.ResolutionPausedRejected := by
  intro Accounting rh s c h
  exact not_entry_rejects fun hg => Bool.noConfusion (h.symm.trans hg.2.2)

theorem ResolutionValueRejected : Properties.ResolutionValueRejected := by
  intro Accounting rh s c h
  exact not_entry_rejects fun hg => h hg.1

theorem ResolutionFailureAtomic : Properties.ResolutionFailureAtomic := by
  intro Accounting rh s c
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [mintTransact, h, commitResolution]
  · simp only [recoverTransact, h, commitResolution]

theorem ResolutionHookFailureAtomic : Properties.ResolutionHookFailureAtomic := by
  intro Accounting rh s c h
  refine ⟨?_, ?_⟩
  · simp only [mintTransact, bridgeMint_of_tail_none (hookThenMint_of_hook_none h),
      commitResolution]
  · simp only [recoverTransact, recover_of_tail_none (hookThenMint_of_hook_none h),
      commitResolution]

theorem MintRejectionRollsBackHook : Properties.MintRejectionRollsBackHook := by
  intro Accounting rh s c
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [mintTransact, bridgeMint_of_tail_none (hookThenMint_of_mint_none h),
      commitResolution]
  · simp only [recoverTransact, recover_of_tail_none (hookThenMint_of_mint_none h),
      commitResolution]

private theorem mint_zero_rejected (tok : BridgedStandardERC20.State) (caller : Address)
    (amount : UInt256) : BridgedStandardERC20.mint tok caller 0 amount = none := by
  simp [BridgedStandardERC20.mint, BridgedStandardERC20.MintAllowed]

theorem ZeroReceiverMintRejected : Properties.ZeroReceiverMintRejected := by
  intro Accounting rh s c _hs h0
  apply bridgeMint_of_tail_none
  apply hookThenMint_of_mint_none
  rw [h0]
  exact mint_zero_rejected _ _ _

theorem MintSupplyOverflowRejected : Properties.MintSupplyOverflowRejected := by
  intro Accounting rh s c _hs h
  exact ⟨bridgeMint_of_tail_none (hookThenMint_of_mint_none
      (BridgedStandardERC20.overflowing_mint_rejected h)),
    recover_of_tail_none (hookThenMint_of_mint_none
      (BridgedStandardERC20.overflowing_mint_rejected h))⟩

/-! ## First bridge -/

private theorem bridgeMintFirst_view {reg : RegistrationHooks Accounting}
    {rh : ResolutionHooks Accounting} {s : RegistrationState Accounting} {c : ResolutionCall}
    {t : State Accounting} (h : bridgeMintFirst reg rh s c = some t) :
    (FirstEntryAllowed s c ∧ FirstBridge s c) ∧ ∃ registered,
      registerFreshBranch reg s c.data.originToken = some registered ∧
      hookThenMint rh registered.state c.chain c.assetId c.data.remoteReceiver c.data.amount =
        some t := by
  unfold bridgeMintFirst at h
  repeat (split at h <;> try contradiction)
  exact ⟨‹_›, _, ‹_›, h⟩

/-- What a successful registration wrote, in one equation. -/
private theorem registration_view_res {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerRepresentation hooks s origin = some out) :
    (s.config.assetId = hooks.assetIdFor s.config.originChainId origin ∧
      s.config.originChainId ≠ s.config.chainId) ∧ origin ≠ 0 ∧
    ∃ accounting,
      hooks.registerTracker s.accounting
          (installRegistry s.registry s.config.assetId s.config.tokenAddress)
          (registeredToken s.config origin) s.config.assetId s.config.originChainId =
        some accounting ∧
      out.state = ⟨s.config, installRegistry s.registry s.config.assetId s.config.tokenAddress,
        s.paused, registeredToken s.config origin, accounting⟩ := by
  simp only [registerRepresentation] at h
  repeat (split at h <;> try contradiction)
  rename_i hg _ _ _ _ _ hi he _ accounting ht
  unfold BridgedStandardERC20.initializeToken at hi
  split at hi <;> cases hi
  rename_i hallowed
  subst he
  cases h
  exact ⟨hg, hallowed.1.2, accounting, ht, rfl⟩

theorem FirstBridgeMintExact : Properties.FirstBridgeMintExact := by
  intro Accounting reg rh s c t h
  obtain ⟨⟨he, hf⟩, ⟨st, ver⟩, hr, hmint⟩ := bridgeMintFirst_view h
  obtain ⟨hfree, hrep⟩ := fresh_registration_preconditions hr
  have hwf : WellFormed st := registration_establishes_wellformed hrep
  obtain ⟨⟨hasset, _hchain⟩, _ho, tracked, _htr, hstate⟩ := registration_view_res hrep
  dsimp only at hstate hmint
  subst hstate
  have hwt := credit_preserves_wellFormed hwf hmint
  obtain ⟨accounted, minted, ha, hm, rfl⟩ := hookThenMint_view hmint
  rcases BridgedStandardERC20.mint_exact hm with ⟨_, _, hbal, hsup, hframe, hcfg⟩
  refine ⟨he, hf, hfree, hf.2.trans hasset, ?_, hbal.trans (Nat.zero_add _),
    hsup.trans (Nat.zero_add _), fun a ha => hframe a ha, rfl, rfl, rfl, hwt,
    ⟨_, ver⟩, hr, rfl, ha⟩
  rw [hcfg, hf.2]
  rfl

theorem FirstBridgeChecksOriginToken : Properties.FirstBridgeChecksOriginToken := by
  intro Accounting reg rh s c hne
  cases h : bridgeMintFirst reg rh s c with
  | none => rfl
  | some t => exact absurd (FirstBridgeMintExact Accounting reg rh s c t h).2.2.2.1 hne

theorem FirstBridgeRejected : Properties.FirstBridgeRejected := by
  intro Accounting reg rh s c hbad
  cases h : bridgeMintFirst reg rh s c with
  | none => rfl
  | some t =>
    obtain ⟨⟨⟨hv, hc, hp⟩, _⟩, registered, _, hmint⟩ := bridgeMintFirst_view h
    obtain ⟨_, minted, _, hm, _⟩ := hookThenMint_view hmint
    obtain ⟨⟨_, _, hrec, _⟩, _⟩ := mint_view_res hm
    rcases hbad with h1 | h1 | h1 | h1
    · exact absurd hc h1
    · exact Bool.noConfusion (h1.symm.trans hp)
    · exact absurd hv h1
    · exact absurd h1 hrec

theorem FirstBridgeEnabled : Properties.FirstBridgeEnabled := by
  intro Accounting reg rh s c tracked accounted he hf hfree hasset hchain ho hmeta hdeploy
    htrack hrec hhook
  have hg : s.config.assetId = reg.assetIdFor s.config.originChainId c.data.originToken ∧
      s.config.originChainId ≠ s.config.chainId := ⟨hasset, hchain⟩
  have hi : BridgedStandardERC20.initializeToken BridgedStandardERC20.freshProxy s.config.vault
      s.config.assetId c.data.originToken reg.metadataDecoded =
        some ⟨registeredToken s.config c.data.originToken, 1⟩ := by
    simp [BridgedStandardERC20.initializeToken, BridgedStandardERC20.InitializeAllowed,
      BridgedStandardERC20.freshProxy, BridgedStandardERC20.empty, registeredToken, ho, hmeta]
  have hreg : registerFreshBranch reg s c.data.originToken =
      some ⟨⟨s.config, installRegistry s.registry s.config.assetId s.config.tokenAddress,
        s.paused, registeredToken s.config c.data.originToken, tracked⟩, 1⟩ := by
    simp only [registerFreshBranch, ite_eq_left hfree, registerRepresentation, ite_eq_left hg,
      hdeploy, hi, htrack]
    simp
  have hallowed : BridgedStandardERC20.MintAllowed (registeredToken s.config c.data.originToken)
      s.config.vault c.data.remoteReceiver c.data.amount :=
    ⟨hf.1, rfl, hrec, by
      show 0 + c.data.amount.val < UInt256.size
      exact (Nat.zero_add _).symm ▸ c.data.amount.isLt⟩
  have h : bridgeMintFirst reg rh s c = some
      { config := s.config,
        registry := installRegistry s.registry s.config.assetId s.config.tokenAddress,
        paused := s.paused,
        token := BridgedStandardERC20.mintEffect (registeredToken s.config c.data.originToken)
          c.data.remoteReceiver c.data.amount,
        accounting := accounted } := by
    unfold bridgeMintFirst
    rw [ite_eq_left ⟨he, hf⟩, hreg]
    exact hookThenMint_some hhook (ite_eq_left hallowed)
  exact ⟨_, h⟩

theorem FirstBridgeEstablishesRegistered : Properties.FirstBridgeEstablishesRegistered := by
  intro Accounting reg rh s c c' t htok h hsame
  have hx := FirstBridgeMintExact Accounting reg rh s c t h
  obtain ⟨_, hf, _, _, _, _, _, _, hcfg, _, hreg, hwt, ⟨st, ver⟩, hr, _, _⟩ := hx
  obtain ⟨_, hrep⟩ := fresh_registration_preconditions hr
  obtain ⟨⟨_, hchain⟩, _, _, _, _⟩ := registration_view_res hrep
  refine ⟨hwt, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcfg]; exact hf.1
  · rw [hcfg, hsame]; exact hf.2
  · rw [hcfg]; exact hchain
  · rw [hreg, hcfg, hsame, hf.2]
    exact Function.update_self _ _ _
  · rw [hcfg]; exact htok

/-! ## Witnesses -/

namespace ResolutionExample

/-- Vault `1`, router `2`, tracked token `5`, asset `3`, base asset `0`, this chain `1`, origin
chain `4`. -/
def exConfig : Config := ⟨1, 2, 5, 3, 0, 1, 4⟩

/-- Asset `3` and token `5` installed in both directions, nothing else. -/
def exRegistry : Registry := installRegistry ⟨fun _ => 0, fun _ => 0⟩ 3 5

/-- The representation (minter `1`, origin token `7`, asset `3`) with `amount` held by
`holder` and nothing else. -/
def tokenWith (holder : Address) (amount : UInt256) : BridgedStandardERC20.State :=
  BridgedStandardERC20.mintEffect (BridgedStandardERC20.empty ⟨1, 7, 3⟩) holder amount

def stateWith {A : Type} (tok : BridgedStandardERC20.State) (acc : A) : State A :=
  ⟨exConfig, exRegistry, false, tok, acc⟩

theorem exRegistry_token : exRegistry.tokenForAsset 3 = 5 := by
  simp [exRegistry, installRegistry]

theorem exRegistry_asset : exRegistry.assetForToken 5 = 3 := by
  simp [exRegistry, installRegistry]

/-- The concrete facts about the configuration that the witnesses use. -/
theorem exConfig_facts : exConfig.vault ≠ 0 ∧ exConfig.tokenAddress ≠ 0 ∧
    exConfig.assetId ≠ exConfig.baseAssetId ∧ exConfig.originChainId ≠ exConfig.chainId ∧
    exConfig.originChainId ≠ 0 := by
  decide

theorem one_ne_zero_word : (1 : UInt256) ≠ 0 := by decide

theorem tokenWith_ledger {holder : Address} (hh : holder ≠ 0) (amount : UInt256) :
    BridgedStandardERC20.WellFormed (tokenWith holder amount) := by
  have hempty : BridgedStandardERC20.WellFormed (BridgedStandardERC20.empty ⟨1, 7, 3⟩) := by
    refine ⟨Finset.sum_const_zero, ?_, rfl⟩
    norm_num [BridgedStandardERC20.empty, UInt256.size]
  have hmint : BridgedStandardERC20.mint (BridgedStandardERC20.empty ⟨1, 7, 3⟩) 1 holder amount
      = some (tokenWith holder amount) := by
    unfold BridgedStandardERC20.mint
    rw [ite_eq_left ⟨by decide, rfl, hh, by
      show 0 + amount.val < UInt256.size
      exact (Nat.zero_add _).symm ▸ amount.isLt⟩]
    rfl
  exact BridgedStandardERC20.mint_preserves_ledger hempty hmint

theorem stateWith_wf {A : Type} {holder : Address} (hh : holder ≠ 0) (amount : UInt256)
    (acc : A) : WellFormed (stateWith (tokenWith holder amount) acc) :=
  ⟨tokenWith_ledger hh amount, rfl, rfl, exRegistry_token, exRegistry_asset⟩

/-- Preparation hook: a counter that grows by the amount bridged out. -/
def countOut : Hooks ℕ := ⟨fun a _ _ _ amount => some (a + amount.val), fun _ _ => some []⟩

/-- Resolution hook: the same counter, shrinking by the amount bridged in and failing below
zero (the shape of the L1 vault's `bridgedOut`, `L1NativeTokenVault.sol:260-277`). -/
def countIn : ResolutionHooks ℕ :=
  ⟨fun a _ _ _ amount => if amount.val ≤ a then some (a - amount.val) else none⟩

theorem count_cancel : HooksCancel countOut countIn := by
  intro a a' _ _ _ _ amount h
  have h' : a + amount.val = a' := Option.some.inj h
  subst h'
  show (if amount.val ≤ a + amount.val then some (a + amount.val - amount.val) else none) = some a
  rw [ite_eq_left (Nat.le_add_left _ _), Nat.add_sub_cancel]

/-- Burn one unit of holder `11`'s balance towards chain `6` for `receiver`, resolving the
token from the registry (zero hint). -/
def prepRequest (receiver : Address) : Request := ⟨2, 6, 3, 11, 0, 0, ⟨1, receiver, 0⟩⟩

theorem prep_enabled {A : Type} (hooks : Hooks A) (acc accounted : A) (receiver : Address)
    (ha : hooks.account acc (tokenWith 11 4) 6 3 1 = some accounted)
    (hm : hooks.metadata (BridgedStandardERC20.burnEffect (tokenWith 11 4) 11 1) 4 = some []) :
    ∃ out, prepare hooks (stateWith (tokenWith 11 4) acc) (prepRequest receiver) = some out := by
  have hw := stateWith_wf (A := A) (holder := 11) (by decide) 4 acc
  have hsel : selectedToken (stateWith (tokenWith 11 4) acc) (prepRequest receiver) = 5 := by
    show (if (0 : Address) = 0 then exRegistry.tokenForAsset 3 else 0) = 5
    rw [ite_eq_left rfl]
    exact exRegistry_token
  have hs : InScope (stateWith (tokenWith 11 4) acc) (prepRequest receiver) :=
    ⟨exConfig_facts.1, exConfig_facts.2.1, exConfig_facts.2.2.1, exConfig_facts.2.2.2.1, hsel⟩
  have he : EntryAllowed (stateWith (tokenWith 11 4) acc) (prepRequest receiver) := by
    refine ⟨rfl, rfl, rfl, ?_, ?_, one_ne_zero_word⟩
    · rw [hsel]; exact exConfig_facts.2.1
    · rw [hsel]; exact exRegistry_asset
  have hb : (prepRequest receiver).data.amount.val ≤
      (stateWith (tokenWith 11 4) acc).token.balances 11 := by
    show (1 : UInt256).val ≤ Function.update (fun _ => 0) (11 : Address) (0 + (4 : UInt256).val) 11
    rw [Function.update_self]
    decide
  exact preparation_enabled hw hs he rfl (show (11 : Address) ≠ 0 by decide) hb
    (show (7 : Address) ≠ 0 by decide) exConfig_facts.2.2.2.2 ha hm

/-- A destination mint of one unit to `12` from chain `6`, with original caller `13`. -/
def mintCall : ResolutionCall := ⟨2, 0, 6, 3, ⟨13, 12, 7, 1, []⟩⟩

theorem mintCall_entry {A : Type} (tok : BridgedStandardERC20.State) (acc : A) :
    ResolveEntryAllowed (stateWith tok acc) mintCall := ⟨rfl, rfl, rfl⟩

theorem mintCall_scope {A : Type} (tok : BridgedStandardERC20.State) (acc : A) :
    RegisteredBridged (stateWith tok acc) mintCall :=
  ⟨exConfig_facts.1, rfl, exConfig_facts.2.2.2.1, exRegistry_token, exConfig_facts.2.1⟩

theorem countIn_ten : countIn.fromChain 10 (tokenWith 11 4) 6 3 1 = some 9 := by decide

theorem countIn_apply (a : ℕ) (tok : BridgedStandardERC20.State) (chain asset amount : UInt256)
    (h : amount.val ≤ a) : countIn.fromChain a tok chain asset amount = some (a - amount.val) :=
  ite_eq_left h

theorem resolutionSatisfiable : Properties.ResolutionSatisfiable := by
  obtain ⟨out, hp⟩ := prep_enabled countOut 10 11 12 rfl rfl
  have hw := stateWith_wf (A := ℕ) (holder := 11) (by decide) 4 10
  have hround := (PrepareThenRecoverRoundTrip ℕ countOut countIn _ _ out count_cancel hw hp).1
  have hacc := preparation_accounting hp
  have hsup : (stateWith (tokenWith 11 4) 10).token.totalSupply + mintCall.data.amount.val <
      UInt256.size := by decide
  obtain ⟨t, ht⟩ := BridgeMintEnabled ℕ countIn (stateWith (tokenWith 11 4) 10) mintCall 9 hw.2
    (mintCall_entry _ _) (mintCall_scope _ _) (by decide) hsup countIn_ten
  have htacc := (BridgeMintExact ℕ countIn _ t mintCall ht).2.2.1
  refine ⟨countOut, countIn, _, _, out, mintCall, t, count_cancel, hw, hp, by decide, ?_, hround,
    ht, by decide, by decide, ?_⟩
  · intro h
    have h1 : 10 + (1 : UInt256).val = 10 := (Option.some.inj hacc).trans h
    exact absurd h1 (by decide)
  · intro h
    have h1 : some t.accounting = some 9 := htacc.symm.trans countIn_ten
    rw [h] at h1
    exact absurd h1 (by decide)

/-- Preparation hook counting outflow in the first component. -/
def pairOut : Hooks (ℕ × ℕ) :=
  ⟨fun a _ _ _ amount => some (a.1 + amount.val, a.2), fun _ _ => some []⟩

/-- Resolution hook counting inflow in the second component. -/
def pairIn : ResolutionHooks (ℕ × ℕ) := ⟨fun a _ _ _ amount => some (a.1, a.2 + amount.val)⟩

theorem roundTripNeedsCancellingHooks : Properties.RoundTripNeedsCancellingHooks := by
  obtain ⟨out, hp⟩ := prep_enabled pairOut (0, 0) (1, 0) 12 rfl rfl
  have hw := stateWith_wf (A := ℕ × ℕ) (holder := 11) (by decide) 4 (0, 0)
  have hacc : out.state.accounting = (1, 0) := (Option.some.inj (preparation_accounting hp)).symm
  have hhook : pairIn.fromChain out.state.accounting out.state.token
      (prepRequest 12).destinationChain (prepRequest 12).assetId (prepRequest 12).data.amount =
        some (1, 1) := by
    rw [hacc]
    rfl
  obtain ⟨_, _, t, ht⟩ :=
    PrepareThenRecoverEnabled (ℕ × ℕ) pairOut pairIn _ _ out (1, 1) hw hp hhook
  obtain ⟨htok, _, _, _, _, hfrom⟩ :=
    PrepareThenRecoverRestoresToken (ℕ × ℕ) pairOut pairIn _ _ out _ t hw.1 hp ht
  have htacc : t.accounting = (1, 1) := Option.some.inj (hfrom.symm.trans hhook)
  have hnc : ¬ HooksCancel pairOut pairIn := by
    intro h
    have h1 := h (0, 0) (1, 0) (tokenWith 11 4) (tokenWith 11 4) 6 3 1 rfl
    have h2 := congrArg Prod.snd (Option.some.inj h1)
    exact absurd h2 (by decide)
  refine ⟨pairOut, pairIn, _, _, out, t, hnc, hw, hp, ht, htok, ?_⟩
  intro h
  have h1 := congrArg State.accounting h
  rw [htacc] at h1
  exact absurd h1 (by decide)

theorem zeroReceiverOnlyRecoverable : Properties.ZeroReceiverOnlyRecoverable := by
  obtain ⟨out, hp⟩ := prep_enabled countOut 10 11 0 rfl rfl
  have hw := stateWith_wf (A := ℕ) (holder := 11) (by decide) 4 10
  have hzero : out.data.remoteReceiver = 0 := (preparation_payload hw hp).2.1
  refine ⟨countOut, countIn, _, _, out, hw, hp, hzero, ?_, ?_,
    (PrepareThenRecoverRoundTrip ℕ countOut countIn _ _ out count_cancel hw hp).1⟩
  · intro A rh' d c hc hreg
    exact ZeroReceiverMintRejected A rh' d c hreg (by rw [hc]; exact hzero)
  · intro A reg rh' d c hc
    exact FirstBridgeRejected A reg rh' d c (Or.inr (Or.inr (Or.inr (by rw [hc]; exact hzero))))

/-- The largest word, `2^256 - 1`. -/
def maxWord : UInt256 :=
  ⟨UInt256.size - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne _)) Nat.one_pos⟩

theorem resolutionRejectionsSatisfiable : Properties.ResolutionRejectionsSatisfiable := by
  have hw := stateWith_wf (A := ℕ) (holder := 11) (by decide) 4 10
  have hsup : (stateWith (tokenWith 11 4) 10).token.totalSupply + mintCall.data.amount.val <
      UInt256.size := by decide
  obtain ⟨t, ht⟩ := BridgeMintEnabled ℕ countIn (stateWith (tokenWith 11 4) 10) mintCall 9 hw.2
    (mintCall_entry _ _) (mintCall_scope _ _) (by decide) hsup countIn_ten
  obtain ⟨t', ht'⟩ := RecoverEnabled ℕ countIn (stateWith (tokenWith 11 4) 10) mintCall 9 hw.2
    (mintCall_entry _ _) (mintCall_scope _ _) (by decide) hsup countIn_ten
  have hzeroScope : RegisteredBridged (stateWith (tokenWith 11 4) 10)
      { mintCall with data := { mintCall.data with remoteReceiver := 0 } } :=
    mintCall_scope _ _
  have hzero : bridgeMint countIn (stateWith (tokenWith 11 4) 10)
      { mintCall with data := { mintCall.data with remoteReceiver := 0 } } = none :=
    ZeroReceiverMintRejected ℕ countIn _ _ hzeroScope rfl
  have hmax : 0 < UInt256.size := Nat.pos_of_ne_zero (NeZero.ne _)
  -- with the counter at `0` the hook has nothing to take the amount from
  have hhook0 : countIn.fromChain 0 (tokenWith 11 4) mintCall.chain mintCall.assetId
      mintCall.data.amount = none := by
    decide
  refine ⟨countIn, stateWith (tokenWith 11 4) 10, mintCall, t, 9, hw, ht,
    by rw [ht']; exact Option.some_ne_none _, by decide,
    (ResolutionWrongRouterRejected ℕ countIn _ _ (by decide)).1,
    (ResolutionWrongRouterRejected ℕ countIn _ _ (by decide)).2,
    (ResolutionPausedRejected ℕ countIn _ _ rfl).1,
    (ResolutionPausedRejected ℕ countIn _ _ rfl).2,
    (ResolutionValueRejected ℕ countIn _ _ (by decide)).1,
    (ResolutionValueRejected ℕ countIn _ _ (by decide)).2,
    hzeroScope, hzero, ?_, ?_, (ResolutionFailureAtomic ℕ countIn _ _).1 hzero, hhook0,
    (ResolutionHookFailureAtomic ℕ countIn _ _ hhook0).1, ?_⟩
  · intro h
    exact absurd (countIn_ten.symm.trans h) (by decide)
  · intro h
    exact absurd (countIn_ten.symm.trans h) (by decide)
  · refine ⟨stateWith (tokenWith 11 maxWord) 10, stateWith_wf (by decide) maxWord 10,
      mintCall_scope _ _, mintCall_entry _ _, ?_⟩
    show UInt256.size ≤ 0 + (UInt256.size - 1) + (1 : UInt256).val
    have h1 : (1 : UInt256).val = 1 := rfl
    omega

/-- Asset ids `token - chain`: asset `3` is origin token `7` on chain `4`; deployment at the
expected address `5`; the tracker registration adds `2` to a counter. -/
def firstHooks : RegistrationHooks ℕ :=
  ⟨fun chain token => (token.val : UInt256) - chain, fun _ _ => some 5, true,
    fun a _ _ _ _ => some (a + 2)⟩

/-- The configuration above with nothing registered yet. -/
def firstState : RegistrationState ℕ := ⟨exConfig, ⟨fun _ => 0, fun _ => 0⟩, false, 0⟩

theorem firstBridgeSatisfiable : Properties.FirstBridgeSatisfiable := by
  have hasset : firstState.config.assetId =
      firstHooks.assetIdFor firstState.config.originChainId mintCall.data.originToken := by
    decide
  have hhook : countIn.fromChain 2 (registeredToken firstState.config mintCall.data.originToken)
      mintCall.chain mintCall.assetId mintCall.data.amount = some 1 := by decide
  obtain ⟨t, ht⟩ := FirstBridgeEnabled ℕ firstHooks countIn firstState mintCall 2 1
    ⟨rfl, rfl, rfl⟩ ⟨by decide, rfl⟩ rfl hasset (by decide) (by decide) rfl rfl rfl
    (by decide) hhook
  refine ⟨firstHooks, countIn, firstState, mintCall, t, 8, by decide, ht, by decide, by decide,
    ?_, ?_⟩
  · exact FirstBridgeChecksOriginToken ℕ firstHooks countIn firstState _ (by decide)
  · exact FirstBridgeRejected ℕ firstHooks countIn firstState _ (Or.inr (Or.inr (Or.inr rfl)))

/-- The scope and entry facts hold for any call naming asset `3` from the router with no value,
whatever its chain and data. -/
theorem asset3_scope {A : Type} (tok : BridgedStandardERC20.State) (acc : A) (chain : UInt256)
    (data : MintData) : RegisteredBridged (stateWith tok acc) ⟨2, 0, chain, 3, data⟩ :=
  ⟨exConfig_facts.1, rfl, exConfig_facts.2.2.2.1, exRegistry_token, exConfig_facts.2.1⟩

theorem asset3_entry {A : Type} (tok : BridgedStandardERC20.State) (acc : A) (chain : UInt256)
    (data : MintData) : ResolveEntryAllowed (stateWith tok acc) ⟨2, 0, chain, 3, data⟩ :=
  ⟨rfl, rfl, rfl⟩

theorem vaultHasNoReplayGuard : Properties.VaultHasNoReplayGuard := by
  obtain ⟨out, hp⟩ := prep_enabled countOut 10 11 12 rfl rfl
  have hw := stateWith_wf (A := ℕ) (holder := 11) (by decide) 4 10
  have hround := (PrepareThenRecoverRoundTrip ℕ countOut countIn _ _ out count_cancel hw hp).1
  have hpay := preparation_payload hw hp
  have hcaller : out.data.originalCaller = 11 := hpay.1
  have hamt : out.data.amount = 1 := hpay.2.2.2.1
  -- the second recovery runs on the restored state itself
  have hsup : (stateWith (tokenWith 11 4) 10).token.totalSupply +
      (recoveryCall 2 (prepRequest 12) out.data).data.amount.val < UInt256.size := by
    show 0 + (4 : UInt256).val + out.data.amount.val < UInt256.size
    rw [hamt]
    decide
  have hhook : countIn.fromChain (stateWith (tokenWith 11 4) 10).accounting
      (stateWith (tokenWith 11 4) 10).token (recoveryCall 2 (prepRequest 12) out.data).chain
      (recoveryCall 2 (prepRequest 12) out.data).assetId
      (recoveryCall 2 (prepRequest 12) out.data).data.amount = some 9 := by
    show countIn.fromChain 10 (tokenWith 11 4) 6 3 out.data.amount = some 9
    rw [hamt]
    exact countIn_ten
  have hcaller' : (recoveryCall 2 (prepRequest 12) out.data).data.originalCaller ≠ 0 := by
    show out.data.originalCaller ≠ 0
    rw [hcaller]
    decide
  obtain ⟨t', ht'⟩ := RecoverEnabled ℕ countIn (stateWith (tokenWith 11 4) 10)
    (recoveryCall 2 (prepRequest 12) out.data) 9 hw.2 (asset3_entry _ _ _ _)
    (asset3_scope _ _ _ _) hcaller' hsup hhook
  obtain ⟨_, _, _, _, hbal, hsup', _⟩ := RecoverExact ℕ countIn _ t' _ ht'
  -- the destination mint, twice
  have hsupm : (stateWith (tokenWith 11 4) 10).token.totalSupply + mintCall.data.amount.val <
      UInt256.size := by decide
  obtain ⟨d, hd⟩ := BridgeMintEnabled ℕ countIn (stateWith (tokenWith 11 4) 10) mintCall 9 hw.2
    (mintCall_entry _ _) (mintCall_scope _ _) (by decide) hsupm countIn_ten
  obtain ⟨_, _, hdacc, _, hdbal, hdsup, _, _, hdcfg, hdreg, hdpause⟩ :=
    BridgeMintExact ℕ countIn _ d mintCall hd
  have hdwf := BridgeMintPreservesWellFormed ℕ countIn _ d mintCall hw hd
  have hdacc' : d.accounting = 9 := Option.some.inj (hdacc.symm.trans countIn_ten)
  have hentry : ResolveEntryAllowed d mintCall := by
    refine ⟨rfl, ?_, ?_⟩
    · show (2 : Address) = d.config.router
      rw [hdcfg]; rfl
    · rw [hdpause]; rfl
  have hscope : RegisteredBridged d mintCall := by
    unfold RegisteredBridged
    rw [hdcfg, hdreg]
    exact mintCall_scope (tokenWith 11 4) 10
  have hsupd : d.token.totalSupply + mintCall.data.amount.val < UInt256.size := by
    rw [hdsup]
    decide
  have hhookd : countIn.fromChain d.accounting d.token mintCall.chain mintCall.assetId
      mintCall.data.amount = some 8 := by
    rw [hdacc']
    exact countIn_apply 9 d.token _ _ _ (by decide)
  obtain ⟨d', hd'⟩ := BridgeMintEnabled ℕ countIn d mintCall 8 hdwf.2 hentry hscope (by decide)
    hsupd hhookd
  obtain ⟨_, _, _, _, hd'bal, _⟩ := BridgeMintExact ℕ countIn d d' mintCall hd'
  refine ⟨countOut, countIn, _, _, out, _, t', hw, count_cancel, hp, one_ne_zero_word, hround,
    ht', ?_, ?_, mintCall, d, d', hd, hd', one_ne_zero_word, ?_⟩
  · have hbal' : t'.token.balances out.data.originalCaller =
        (stateWith (tokenWith 11 4) 10).token.balances out.data.originalCaller +
          out.data.amount.val := hbal
    rw [hcaller, hamt] at hbal'
    exact hbal'
  · have hsup'' : t'.token.totalSupply =
        (stateWith (tokenWith 11 4) 10).token.totalSupply + out.data.amount.val := hsup'
    rw [hamt] at hsup''
    exact hsup''
  · rw [hd'bal, hdbal]
    omega

theorem spendingAndDeliverySatisfiable : Properties.SpendingAndDeliverySatisfiable := by
  obtain ⟨out, hp⟩ := prep_enabled countOut 10 11 12 rfl rfl
  have hw := stateWith_wf (A := ℕ) (holder := 11) (by decide) 4 10
  have hpay := preparation_payload hw hp
  have hback := preparation_backed hw hp
  have hacc : out.state.accounting = 11 := (Option.some.inj (preparation_accounting hp)).symm
  have hrecv : out.data.remoteReceiver = 12 := hpay.2.1
  have hamt : out.data.amount = 1 := hpay.2.2.2.1
  -- the depositor holds `3` after the burn
  have hheld : out.state.token.balances 11 = 3 := by
    have h1 : out.state.token.balances 11 + out.data.amount.val =
        Function.update (fun _ => 0) (11 : Address) (0 + (4 : UInt256).val) 11 := hback.2.1
    rw [hamt, Function.update_self] at h1
    have h2 : (1 : UInt256).val = 1 := rfl
    have h3 : (4 : UInt256).val = 4 := rfl
    omega
  have hallowed : BridgedStandardERC20.TransferAllowed out.state.token 11 12 3 :=
    ⟨by decide, by decide, by rw [hheld]; rfl⟩
  have htr : BridgedStandardERC20.transfer out.state.token 11 12 3 =
      some (BridgedStandardERC20.transferEffect out.state.token 11 12 3) := ite_eq_left hallowed
  have hspend : SpendReach out.state
      { out.state with token := BridgedStandardERC20.transferEffect out.state.token 11 12 3 } :=
    SpendReach.tail SpendReach.refl htr
  have hzero : (BridgedStandardERC20.transferEffect out.state.token 11 12 3).balances 11 = 0 := by
    show Function.update (Function.update out.state.token.balances 11
        (out.state.token.balances 11 - (3 : UInt256).val)) 12
      ((Function.update out.state.token.balances 11
        (out.state.token.balances 11 - (3 : UInt256).val)) 12 + (3 : UInt256).val) 11 = 0
    rw [Function.update_of_ne (show (11 : Address) ≠ 12 by decide), Function.update_self, hheld]
    rfl
  have hne : BridgedStandardERC20.transferEffect out.state.token 11 12 3 ≠ out.state.token := by
    intro h
    have h1 := congrArg (fun tok => BridgedStandardERC20.State.balances tok 11) h
    simp only [hzero, hheld] at h1
    exact absurd h1 (by decide)
  have hhook : countIn.fromChain
      ({ out.state with
          token := BridgedStandardERC20.transferEffect out.state.token 11 12 3 }).accounting
      ({ out.state with
          token := BridgedStandardERC20.transferEffect out.state.token 11 12 3 }).token
      (prepRequest 12).destinationChain (prepRequest 12).assetId (prepRequest 12).data.amount =
        some 10 := by
    show countIn.fromChain out.state.accounting _ 6 3 1 = some 10
    rw [hacc]
    exact countIn_apply 11 _ _ _ _ (by decide)
  -- the destination receives the returned data
  have hsupm : (stateWith (tokenWith 11 4) 10).token.totalSupply +
      (⟨2, 0, 6, 3, out.data⟩ : ResolutionCall).data.amount.val < UInt256.size := by
    show 0 + (4 : UInt256).val + out.data.amount.val < UInt256.size
    rw [hamt]
    decide
  have hhookm : countIn.fromChain (stateWith (tokenWith 11 4) 10).accounting
      (stateWith (tokenWith 11 4) 10).token 6 3
      (⟨2, 0, 6, 3, out.data⟩ : ResolutionCall).data.amount = some 9 := by
    show countIn.fromChain 10 (tokenWith 11 4) 6 3 out.data.amount = some 9
    rw [hamt]
    exact countIn_ten
  obtain ⟨d', hd'⟩ := BridgeMintEnabled ℕ countIn (stateWith (tokenWith 11 4) 10)
    ⟨2, 0, 6, 3, out.data⟩ 9 hw.2 (asset3_entry _ _ _ _) (asset3_scope _ _ _ _)
    (by show out.data.remoteReceiver ≠ 0; rw [hrecv]; decide) hsupm hhookm
  exact ⟨countOut, countIn, _, _, out, _, 10, ⟨2, 0, 6, 3, out.data⟩, _, d', hw, hp,
    one_ne_zero_word, hspend, hne, hzero, hhook, rfl, hd'⟩

end ResolutionExample

theorem ResolutionSatisfiable : Properties.ResolutionSatisfiable :=
  ResolutionExample.resolutionSatisfiable

theorem RoundTripNeedsCancellingHooks : Properties.RoundTripNeedsCancellingHooks :=
  ResolutionExample.roundTripNeedsCancellingHooks

theorem ZeroReceiverOnlyRecoverable : Properties.ZeroReceiverOnlyRecoverable :=
  ResolutionExample.zeroReceiverOnlyRecoverable

theorem ResolutionRejectionsSatisfiable : Properties.ResolutionRejectionsSatisfiable :=
  ResolutionExample.resolutionRejectionsSatisfiable

theorem FirstBridgeSatisfiable : Properties.FirstBridgeSatisfiable :=
  ResolutionExample.firstBridgeSatisfiable

theorem VaultHasNoReplayGuard : Properties.VaultHasNoReplayGuard :=
  ResolutionExample.vaultHasNoReplayGuard

theorem SpendingAndDeliverySatisfiable : Properties.SpendingAndDeliverySatisfiable :=
  ResolutionExample.spendingAndDeliverySatisfiable

end Contracts.NativeTokenVaultBase
