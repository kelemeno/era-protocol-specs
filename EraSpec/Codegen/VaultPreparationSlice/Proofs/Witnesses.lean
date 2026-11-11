import EraSpec.Codegen.VaultPreparationSlice.Properties.Witnesses
import EraSpec.Codegen.VaultPreparationSlice.Proofs.Refinement
import EraSpec.Codegen.VaultPreparationSlice.Proofs.MintDataBytes
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.PreparationGuards

/-! # Proofs: the refinement's premises are satisfiable -/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.BridgedStandardERC20 (Address)
open Codegen.BridgedTokenSlice (addrWord addrWord_inj addrWord_zero addrWord_eq_zero)
open Contracts.NativeTokenVaultBase (State Hooks Request Result prepare WellFormed InScope
  EntryAllowed selectedToken mintData MintData BurnData Config Registry)

variable {Acct : Type}

/-! ## Hooks: run the model's on the represented token -/

/-- An address from a word, keeping its low 160 bits. -/
def lowAddr (w : Word) : Address := ⟨w.val % 2 ^ 160, Nat.mod_lt _ (by positivity)⟩

theorem lowAddr_addrWord (a : Address) : lowAddr (addrWord a) = a :=
  Fin.ext (Nat.mod_eq_of_lt a.isLt)

/-- The model token a token storage represents. -/
def absToken (st : Storage) : Contracts.BridgedStandardERC20.State :=
  ⟨⟨lowAddr (st.scalars "_nativeTokenVault"), lowAddr (st.scalars "_originToken"),
      st.scalars "_assetId"⟩,
    fun a => (st.maps "_balances" (addrWord a)).val, (st.scalars "_totalSupply").val⟩

theorem absToken_eq {st : Storage} {t : Contracts.BridgedStandardERC20.State}
    (h : TokenRel st t) : absToken st = t := by
  obtain ⟨⟨vault, originToken, assetId⟩, balances, supply⟩ := t
  simp only [absToken, h.base.vault, h.originToken, h.assetId, lowAddr_addrWord]
  congr
  · funext a; exact h.base.balances a
  · exact h.base.supply

/-- Concrete hooks running the model's on the token state the storage represents. -/
def liftHooks (h : Hooks Acct) : CHooks Acct where
  account acc st c a m :=
    match h.account acc (absToken st) c a m with
    | some x => .ok x
    | none => .error .empty
  metadata st o :=
    match h.metadata (absToken st) o with
    | some b => .ok b
    | none => .error .empty

theorem liftHooks_agree (h : Hooks Acct) : HooksAgree (liftHooks h) h := by
  constructor
  · intro acc st t c a m ht
    simp only [liftHooks, ← absToken_eq ht]
    split <;> simp_all [Except.toOption]
  · intro st t o ht
    simp only [liftHooks, ← absToken_eq ht]
    split <;> simp_all [Except.toOption]

theorem HooksAgreeSatisfiable : Properties.HooksAgreeSatisfiable :=
  fun h => ⟨liftHooks h, liftHooks_agree h⟩

/-! ## Storages: write the model state's values into slots -/

/-- The token storage holding a model token's values. -/
def tokenStorageOf (t : Contracts.BridgedStandardERC20.State) : Storage :=
  ⟨fun k => if k = "_nativeTokenVault" then addrWord t.config.vault
      else if k = "_totalSupply" then (t.totalSupply : Word)
      else if k = "_originToken" then addrWord t.config.originToken
      else if k = "_assetId" then t.config.assetId else 0,
    fun m key => if m = "_balances" then
        (if hk : key.val < 2 ^ 160 then (t.balances ⟨key.val, hk⟩ : Word) else 0) else 0⟩

/-- The vault storage holding a model state's values. -/
def vaultStorageOf (s : State Acct) : Storage :=
  ⟨fun k => if k = "_assetRouter" then addrWord s.config.router
      else if k = "_paused" then (if s.paused then 1 else 0)
      else if k = "_baseTokenAssetId" then s.config.baseAssetId else 0,
    fun m key =>
      if m = "_tokenAddress" then addrWord (s.registry.tokenForAsset key)
      else if m = "_assetIdOf" then
        (if hk : key.val < 2 ^ 160 then s.registry.assetForToken ⟨key.val, hk⟩ else 0)
      else if m = "_originChainId" then
        (if key = s.config.assetId then s.config.originChainId else 0)
      else 0⟩

def deploymentOf (s : State Acct) : Deployment :=
  ⟨s.config.vault, s.config.tokenAddress, s.config.chainId⟩

theorem natCast_val_of_lt {n : ℕ} (h : n < UInt256.size) : ((n : Word)).val = n := by
  simp only [Fin.val_natCast]
  exact Nat.mod_eq_of_lt h

theorem tokenRel_of (t : Contracts.BridgedStandardERC20.State)
    (hw : Contracts.BridgedStandardERC20.WellFormed t) (hv : t.config.vault ≠ 0) :
    TokenRel (tokenStorageOf t) t := by
  refine ⟨⟨?_, hv, ?_, ?_⟩, ?_, ?_⟩
  · simp [tokenStorageOf]
  · simp only [tokenStorageOf]
    simp only [show ("_totalSupply" = "_nativeTokenVault") = False by decide, ite_false, ite_true]
    exact natCast_val_of_lt hw.2.1
  · intro a
    have hb := (Contracts.BridgedStandardERC20.balance_bounded hw a).2
    simp only [tokenStorageOf, ite_true, addrWord]
    rw [dite_eq_left a.isLt]
    exact natCast_val_of_lt hb
  · simp [tokenStorageOf]
  · simp [tokenStorageOf]

theorem rel_of (s : State Acct) (hw : WellFormed s) (hv : s.token.config.vault ≠ 0) :
    Rel (deploymentOf s) (vaultStorageOf s) ⟨tokenStorageOf s.token, s.accounting⟩ s := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, tokenRel_of s.token hw.1 hv, rfl⟩
  · simp [vaultStorageOf]
  · simp [vaultStorageOf]
  · simp [vaultStorageOf]
  · intro id; simp [vaultStorageOf]
  · intro a
    simp only [vaultStorageOf, addrWord]
    simp only [show ("_assetIdOf" = "_tokenAddress") = False by decide, ite_false, ite_true]
    rw [dite_eq_left a.isLt]
  · simp [vaultStorageOf]

theorem EveryWellFormedStateIsRepresented : Properties.EveryWellFormedStateIsRepresented :=
  fun s hw hv => ⟨_, _, _, rel_of s hw hv⟩

/-! ## A concrete vault -/

/-- One registered token at address 3 for asset 7 (origin chain 1, on chain 10), vault 1,
router 2; address 4 holds all 100 units. -/
def s0 : State Unit where
  config := ⟨1, 2, 3, 7, 8, 10, 1⟩
  registry := ⟨fun id => if id = 7 then 3 else 0, fun a => if a = 3 then 7 else 0⟩
  paused := false
  token := ⟨⟨1, 5, 7⟩, fun a => if a = 4 then 100 else 0, 100⟩
  accounting := ()

/-- Hooks that always succeed, with empty metadata. -/
def h0 : Hooks Unit := ⟨fun acc _ _ _ _ => some acc, fun _ _ => some []⟩

/-- Address 4 sends 10 units to address 6 on chain 20, naming the asset, not the token. -/
def r0 : Request := ⟨2, 20, 7, 4, 0, 0, ⟨10, 6, 0⟩⟩

theorem s0_wellFormed : WellFormed s0 := by
  refine ⟨⟨?_, by decide, by decide⟩, rfl, rfl, by decide, by decide⟩
  simp [s0, Finset.sum_ite_eq']

theorem s0_vault : s0.token.config.vault ≠ 0 := by decide

theorem r0_accepted : ∃ out, prepare h0 s0 r0 = some out := by
  have hs : InScope s0 r0 := by
    refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    decide
  have he : EntryAllowed s0 r0 := by
    refine ⟨rfl, rfl, rfl, by decide, by decide, by decide⟩
  exact Contracts.NativeTokenVaultBase.preparation_enabled s0_wellFormed hs he rfl (by decide)
    (by decide) (by decide) (by decide) rfl rfl

theorem RefinementAcceptWitness : Properties.RefinementAcceptWitness := by
  obtain ⟨out, hp⟩ := r0_accepted
  exact ⟨_, liftHooks h0, h0, _, _, s0, r0, out, liftHooks_agree h0, s0_wellFormed,
    rel_of s0 s0_wellFormed s0_vault, hp⟩

theorem RefinementRejectWitness : Properties.RefinementRejectWitness := by
  refine ⟨_, liftHooks h0, h0, _, _, s0, { r0 with data := ⟨0, 6, 0⟩ }, liftHooks_agree h0,
    s0_wellFormed, rel_of s0 s0_wellFormed s0_vault, ?_⟩
  exact Contracts.NativeTokenVaultBase.zero_amount_rejected rfl

/-- The successful call of `r0`. -/
theorem r0_call : ∃ out res,
    prepare h0 s0 r0 = some out ∧
    xcall ((deploymentOf s0).machine (liftHooks h0)) vaultProgram "bridgeBurn"
      ((deploymentOf s0).env r0.caller r0.msgValue) (requestArgs r0) (vaultStorageOf s0)
      ⟨tokenStorageOf s0.token, s0.accounting⟩ = some (.ok res) ∧
    res.ret = some (.bytes (encodeMintData out.data)) := by
  obtain ⟨out, hp⟩ := r0_accepted
  obtain ⟨res, hx, -, -, hret, -⟩ := (BridgeBurnRefines (deploymentOf s0) (liftHooks h0) h0
    (vaultStorageOf s0) ⟨tokenStorageOf s0.token, s0.accounting⟩ s0 r0 (liftHooks_agree h0)
    s0_wellFormed (rel_of s0 s0_wellFormed s0_vault)).2 out hp
  exact ⟨out, res, hp, hx, hret⟩

theorem r0_amount {out : Result Unit} (hp : prepare h0 s0 r0 = some out) :
    out.data.amount.val = 10 := by
  rw [(Contracts.NativeTokenVaultBase.preparation_payload s0_wellFormed hp).2.2.2.1]
  rfl

theorem BridgeBurnSuccessWitness : Properties.BridgeBurnSuccessWitness := by
  obtain ⟨out, res, hp, hx, hret⟩ := r0_call
  refine ⟨_, liftHooks h0, h0, _, _, s0, r0.caller, r0.msgValue, _, _, _, _, _, res,
    liftHooks_agree h0, s0_wellFormed, rel_of s0 s0_wellFormed s0_vault, r0.depositor.isLt, hx,
    ?_⟩
  rw [hret, mintAmount_encodeMintData, r0_amount hp]
  decide

theorem JournalBackedNonTrivial : Properties.JournalBackedNonTrivial := by
  obtain ⟨out, res, hp, hx, hret⟩ := r0_call
  refine ⟨deploymentOf s0, liftHooks h0, h0, s0, ⟨vaultStorageOf s0,
      ⟨tokenStorageOf s0.token, s0.accounting⟩, []⟩, _, liftHooks_agree h0, s0_wellFormed,
    rel_of s0 s0_wellFormed s0_vault, rfl,
    LayeredVerification.Run.tail (LayeredVerification.Run.refl _)
      (Step.bridgeBurn r0.depositor.isLt hx), ?_⟩
  simp only [journalTotal, List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero]
  rw [hret, mintAmount_encodeMintData, r0_amount hp]
  decide

theorem ViewCallWitness : Properties.ViewCallWitness := by
  intro Acct d ch caller st w
  exact ⟨_, by simp [xcall, XContract.find, vaultProgram, bridgeBurn, pausedFn, bindXParams,
    Deployment.env]; rfl⟩

theorem EncodeMintDataInjectiveWitness : Properties.EncodeMintDataInjectiveWitness := by
  refine ⟨⟨0, 0, 0, 0, []⟩, ⟨0, 0, 0, 0, [1]⟩, by decide, by decide, by simp, ?_⟩
  intro h
  have := congrArg List.length h
  simp [encodeMintData_eq, pad32, AttackVectors.BundleHashEncoding.pad32] at this

end Codegen.VaultPreparationSlice
