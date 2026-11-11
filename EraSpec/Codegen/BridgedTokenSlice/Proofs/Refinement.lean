import EraSpec.Codegen.BridgedTokenSlice.Properties.Refinement
import EraSpec.Contracts.BridgedStandardERC20.Proofs.Model

/-!
# Proofs: the generated program refines the token model

Two layers.  First a *denotation* per entry point: what `call` returns, in
closed form, obtained by case-splitting on each `require` and evaluating the
interpreter.  Then the refinement statements, from the denotations plus the
model's ledger bounds — the only place `WellFormed` is needed is to show that
the source's `unchecked` additions and subtractions do not wrap.
-/

namespace Codegen.BridgedTokenSlice

open Codegen
open Contracts.BridgedStandardERC20 (Address State WellFormed Config empty)

/-! ## Denotations -/

/-- The balances mapping with one key set. -/
def setBal (maps : String → Word → Word) (k v : Word) : String → Word → Word :=
  upd maps "_balances" (fun w => if w = k then v else maps "_balances" w)

/-- Dispatch: each external name resolves to its body. -/
theorem find_bridgeMint : program.find "bridgeMint" = some bridgeMint := rfl
theorem find_bridgeBurn : program.find "bridgeBurn" = some bridgeBurn := rfl
theorem find_transfer : program.find "transfer" = some transfer := rfl
theorem find_balanceOf : program.find "balanceOf" = some balanceOf := rfl
theorem find_totalSupply : program.find "totalSupply" = some totalSupply := rfl
theorem find_nativeTokenVault : program.find "nativeTokenVault" = some nativeTokenVault := rfl

theorem call_mint (st : Storage) (snd rcpt amt : Word) :
    call program "bridgeMint" snd [rcpt, amt] st =
      some (if snd ≠ st.scalars "_nativeTokenVault" then .error (.custom "Unauthorized" [snd])
        else if rcpt = 0 then .error (.message "ERC20: mint to the zero address")
        else if UInt256.size ≤ (st.scalars "_totalSupply").val + amt.val then
          .error (.panic panicOverflow)
        else .ok ⟨⟨upd st.scalars "_totalSupply" (st.scalars "_totalSupply" + amt),
                   setBal st.maps rcpt (st.maps "_balances" rcpt + amt)⟩,
                 [⟨"Transfer", [0, rcpt, amt]⟩, ⟨"BridgeMint", [rcpt, amt]⟩], none⟩) := by
  by_cases h1 : snd = st.scalars "_nativeTokenVault" <;>
  by_cases h2 : rcpt = 0 <;>
  by_cases h3 : UInt256.size ≤ (st.scalars "_totalSupply").val + amt.val <;>
  simp [call, find_bridgeMint, bindParams, bridgeMint, execBody, execStmt, evalExpr,
    evalCond, evalList, reasonFailure, upd, setBal, onlyNTV, zeroAddr, h1, h2, h3,
    -UInt256.size]

theorem call_burn (st : Storage) (snd acct amt : Word) :
    call program "bridgeBurn" snd [acct, amt] st =
      some (if snd ≠ st.scalars "_nativeTokenVault" then .error (.custom "Unauthorized" [snd])
        else if acct = 0 then .error (.message "ERC20: burn from the zero address")
        else if ¬ amt.val ≤ (st.maps "_balances" acct).val then
          .error (.message "ERC20: burn amount exceeds balance")
        else .ok ⟨⟨upd st.scalars "_totalSupply" (st.scalars "_totalSupply" - amt),
                   setBal st.maps acct (st.maps "_balances" acct - amt)⟩,
                 [⟨"Transfer", [acct, 0, amt]⟩, ⟨"BridgeBurn", [acct, amt]⟩], none⟩) := by
  by_cases h1 : snd = st.scalars "_nativeTokenVault" <;>
  by_cases h2 : acct = 0 <;>
  by_cases h3 : amt.val ≤ (st.maps "_balances" acct).val <;>
  simp [call, find_bridgeBurn, bindParams, bridgeBurn, execBody, execStmt, evalExpr,
    evalCond, evalList, reasonFailure, upd, setBal, onlyNTV, zeroAddr, h1, h2, h3,
    -UInt256.size]

theorem call_transfer (st : Storage) (snd rcpt amt : Word) :
    call program "transfer" snd [rcpt, amt] st =
      some (if snd = 0 then .error (.message "ERC20: transfer from the zero address")
        else if rcpt = 0 then .error (.message "ERC20: transfer to the zero address")
        else if ¬ amt.val ≤ (st.maps "_balances" snd).val then
          .error (.message "ERC20: transfer amount exceeds balance")
        else
          let debited := setBal st.maps snd (st.maps "_balances" snd - amt)
          .ok ⟨⟨st.scalars, setBal debited rcpt (debited "_balances" rcpt + amt)⟩,
               [⟨"Transfer", [snd, rcpt, amt]⟩], some 1⟩) := by
  by_cases h1 : snd = 0 <;>
  by_cases h2 : rcpt = 0 <;>
  by_cases h3 : amt.val ≤ (st.maps "_balances" snd).val <;>
  simp [call, find_transfer, bindParams, transfer, execBody, execStmt, evalExpr,
    evalCond, evalList, reasonFailure, upd, setBal, zeroAddr, h1, h2, h3, -UInt256.size]

theorem call_balanceOf (st : Storage) (snd a : Word) :
    call program "balanceOf" snd [a] st = some (.ok ⟨st, [], some (st.maps "_balances" a)⟩) := by
  simp [call, find_balanceOf, bindParams, balanceOf, execBody, execStmt, evalExpr, upd]

theorem call_totalSupply (st : Storage) (snd : Word) :
    call program "totalSupply" snd [] st = some (.ok ⟨st, [], some (st.scalars "_totalSupply")⟩) := by
  simp [call, find_totalSupply, bindParams, totalSupply, execBody, execStmt, evalExpr]

theorem call_nativeTokenVault (st : Storage) (snd : Word) :
    call program "nativeTokenVault" snd [] st =
      some (.ok ⟨st, [], some (st.scalars "_nativeTokenVault")⟩) := by
  simp [call, find_nativeTokenVault, bindParams, nativeTokenVault, execBody, execStmt, evalExpr]

theorem deploy_eq (snd v : Word) :
    deploy program snd [v] =
      some (if v = 0 then .error (.custom "ZeroAddress" [])
        else .ok ⟨⟨upd Storage.zero.scalars "_nativeTokenVault" v, Storage.zero.maps⟩, [], none⟩) := by
  by_cases h : v = 0 <;>
  simp [deploy, program, bindParams, execBody, execStmt, evalExpr, evalCond, evalList,
    reasonFailure, upd, zeroAddr, h]

/-! ## Words and addresses -/

theorem addrWord_inj {a b : Address} : addrWord a = addrWord b ↔ a = b := by
  constructor
  · intro h
    exact Fin.ext (by simpa [addrWord] using congrArg Fin.val h)
  · rintro rfl; rfl

theorem addrWord_zero : addrWord 0 = 0 := Fin.ext (by simp [addrWord])

theorem addrWord_eq_zero {a : Address} : addrWord a = 0 ↔ a = 0 := by
  rw [← addrWord_zero, addrWord_inj]

theorem val_add_of_lt {x y : Word} (h : x.val + y.val < UInt256.size) :
    (x + y).val = x.val + y.val := by
  rw [Fin.val_add, Nat.mod_eq_of_lt h]

theorem val_sub_of_le {x y : Word} (h : y.val ≤ x.val) : (x - y).val = x.val - y.val :=
  Fin.coe_sub_iff_le.mpr h

theorem two_le_supply {s : State} (hw : WellFormed s) {a b : Address} (h : a ≠ b) :
    s.balances a + s.balances b ≤ s.totalSupply := by
  rw [← hw.1, ← Finset.sum_pair (f := s.balances) h]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-! ## Entry points -/

theorem mint_refines {st : Storage} {s : State} (hw : WellFormed s) (hr : Rel st s)
    (caller recipient : Address) (amount : Word) :
    Properties.mint_refines hw hr caller recipient amount := by
  have hle := (Contracts.BridgedStandardERC20.balance_bounded hw recipient).1
  unfold Properties.mint_refines Contracts.BridgedStandardERC20.mint
  rw [call_mint]
  by_cases hg : Contracts.BridgedStandardERC20.MintAllowed s caller recipient amount
  · rw [ite_eq_left hg]
    obtain ⟨-, hc, hr0, hsz⟩ := hg
    refine ⟨fun h => (nomatch h), ?_⟩
    rintro t ⟨⟩
    rw [ite_eq_right (by rw [hr.vault, hc]; exact fun h => h rfl),
      ite_eq_right (fun h => hr0 (addrWord_eq_zero.mp h)),
      ite_eq_right (by rw [hr.supply]; omega)]
    refine ⟨_, rfl, ⟨?_, hr.vault_ne, ?_, ?_⟩, rfl, rfl⟩
    · simp [upd, hr.vault, Contracts.BridgedStandardERC20.mintEffect]
    · simp only [upd, ite_true]
      rw [val_add_of_lt (by rw [hr.supply]; omega), hr.supply]
      rfl
    · intro a
      simp only [setBal, upd, ite_true]
      by_cases ha : a = recipient
      · subst ha
        simp only [ite_true, Contracts.BridgedStandardERC20.mintEffect, Function.update_self]
        rw [val_add_of_lt (by rw [hr.balances]; omega), hr.balances]
      · have : addrWord a ≠ addrWord recipient := fun h => ha (addrWord_inj.mp h)
        simp only [this, ite_false, Contracts.BridgedStandardERC20.mintEffect,
          Function.update_of_ne ha]
        exact hr.balances a
  · rw [ite_eq_right hg]
    refine ⟨fun _ => ?_, fun t h => (nomatch h)⟩
    by_cases h1 : addrWord caller ≠ st.scalars "_nativeTokenVault"
    · rw [ite_eq_left h1]; exact ⟨_, rfl⟩
    rw [ite_eq_right h1]
    by_cases h2 : addrWord recipient = 0
    · rw [ite_eq_left h2]; exact ⟨_, rfl⟩
    rw [ite_eq_right h2]
    by_cases h3 : UInt256.size ≤ (st.scalars "_totalSupply").val + amount.val
    · rw [ite_eq_left h3]; exact ⟨_, rfl⟩
    exfalso
    apply hg
    refine ⟨hr.vault_ne, ?_, fun h => h2 (by rw [h, addrWord_zero]), ?_⟩
    · rw [hr.vault] at h1; exact addrWord_inj.mp (not_not.mp h1)
    · rw [hr.supply] at h3; omega

theorem burn_refines {st : Storage} {s : State} (hw : WellFormed s) (hr : Rel st s)
    (caller account : Address) (amount : Word) :
    Properties.burn_refines hw hr caller account amount := by
  have hle := (Contracts.BridgedStandardERC20.balance_bounded hw account).1
  unfold Properties.burn_refines Contracts.BridgedStandardERC20.burn
  rw [call_burn]
  by_cases hg : Contracts.BridgedStandardERC20.BurnAllowed s caller account amount
  · rw [ite_eq_left hg]
    obtain ⟨-, hc, ha0, hamt⟩ := hg
    refine ⟨fun h => (nomatch h), ?_⟩
    rintro t ⟨⟩
    have hamt' : amount.val ≤ (st.maps "_balances" (addrWord account)).val := by
      rw [hr.balances]; exact hamt
    rw [ite_eq_right (by rw [hr.vault, hc]; exact fun h => h rfl),
      ite_eq_right (fun h => ha0 (addrWord_eq_zero.mp h)), ite_eq_right (not_not.mpr hamt')]
    refine ⟨_, rfl, ⟨?_, hr.vault_ne, ?_, ?_⟩, rfl, rfl⟩
    · simp [upd, hr.vault, Contracts.BridgedStandardERC20.burnEffect]
    · simp only [upd, ite_true]
      rw [val_sub_of_le (by rw [hr.supply]; omega), hr.supply]
      rfl
    · intro a
      simp only [setBal, upd, ite_true]
      by_cases ha : a = account
      · subst ha
        simp only [ite_true, Contracts.BridgedStandardERC20.burnEffect, Function.update_self]
        rw [val_sub_of_le hamt', hr.balances]
      · have : addrWord a ≠ addrWord account := fun h => ha (addrWord_inj.mp h)
        simp only [this, ite_false, Contracts.BridgedStandardERC20.burnEffect,
          Function.update_of_ne ha]
        exact hr.balances a
  · rw [ite_eq_right hg]
    refine ⟨fun _ => ?_, fun t h => (nomatch h)⟩
    by_cases h1 : addrWord caller ≠ st.scalars "_nativeTokenVault"
    · rw [ite_eq_left h1]; exact ⟨_, rfl⟩
    rw [ite_eq_right h1]
    by_cases h2 : addrWord account = 0
    · rw [ite_eq_left h2]; exact ⟨_, rfl⟩
    rw [ite_eq_right h2]
    by_cases h3 : ¬ amount.val ≤ (st.maps "_balances" (addrWord account)).val
    · rw [ite_eq_left h3]; exact ⟨_, rfl⟩
    exfalso
    apply hg
    refine ⟨hr.vault_ne, ?_, fun h => h2 (by rw [h, addrWord_zero]), ?_⟩
    · rw [hr.vault] at h1; exact addrWord_inj.mp (not_not.mp h1)
    · rw [hr.balances] at h3; exact not_not.mp h3

theorem transfer_refines {st : Storage} {s : State} (hw : WellFormed s) (hr : Rel st s)
    (owner recipient : Address) (amount : Word) :
    Properties.transfer_refines hw hr owner recipient amount := by
  unfold Properties.transfer_refines Contracts.BridgedStandardERC20.transfer
  rw [call_transfer]
  by_cases hg : Contracts.BridgedStandardERC20.TransferAllowed s owner recipient amount
  · rw [ite_eq_left hg]
    obtain ⟨ho0, hr0, hamt⟩ := hg
    refine ⟨fun h => (nomatch h), ?_⟩
    rintro t ⟨⟩
    have hamt' : amount.val ≤ (st.maps "_balances" (addrWord owner)).val := by
      rw [hr.balances]; exact hamt
    rw [ite_eq_right (fun h => ho0 (addrWord_eq_zero.mp h)),
      ite_eq_right (fun h => hr0 (addrWord_eq_zero.mp h)), ite_eq_right (not_not.mpr hamt')]
    refine ⟨_, rfl, ⟨hr.vault, hr.vault_ne, hr.supply, ?_⟩, rfl, rfl⟩
    intro a
    simp only [Contracts.BridgedStandardERC20.transferEffect]
    by_cases hself : recipient = owner
    · subst hself
      by_cases ha : a = recipient
      · subst ha
        simp only [setBal, upd, ite_true, Function.update_self]
        have hlt := (Contracts.BridgedStandardERC20.balance_bounded hw a).2
        have hsub : (st.maps "_balances" (addrWord a) - amount).val = s.balances a - amount.val := by
          rw [val_sub_of_le hamt', hr.balances]
        rw [val_add_of_lt (by rw [hsub]; omega), hsub]
      · have : addrWord a ≠ addrWord recipient := fun h => ha (addrWord_inj.mp h)
        simp only [setBal, upd, ite_true, this, ite_false, Function.update_of_ne ha]
        exact hr.balances a
    · have hne : addrWord recipient ≠ addrWord owner := fun h => hself (addrWord_inj.mp h)
      have hpair := two_le_supply hw (Ne.symm hself)
      have hlt := (Contracts.BridgedStandardERC20.balance_bounded hw owner).2
      by_cases ha : a = recipient
      · subst ha
        simp only [setBal, upd, ite_true, hne, ite_false, Function.update_self,
          Function.update_of_ne hself]
        have hs := hw.2.1
        rw [val_add_of_lt (by rw [hr.balances]; omega), hr.balances]
      · have ha' : addrWord a ≠ addrWord recipient := fun h => ha (addrWord_inj.mp h)
        simp only [setBal, upd, ite_true, ha', ite_false, Function.update_of_ne ha]
        by_cases hao : a = owner
        · subst hao
          simp only [ite_true, Function.update_self]
          rw [val_sub_of_le hamt', hr.balances]
        · have hao' : addrWord a ≠ addrWord owner := fun h => hao (addrWord_inj.mp h)
          simp only [hao', ite_false, Function.update_of_ne hao]
          exact hr.balances a
  · rw [ite_eq_right hg]
    refine ⟨fun _ => ?_, fun t h => (nomatch h)⟩
    by_cases h1 : addrWord owner = 0
    · rw [ite_eq_left h1]; exact ⟨_, rfl⟩
    rw [ite_eq_right h1]
    by_cases h2 : addrWord recipient = 0
    · rw [ite_eq_left h2]; exact ⟨_, rfl⟩
    rw [ite_eq_right h2]
    by_cases h3 : ¬ amount.val ≤ (st.maps "_balances" (addrWord owner)).val
    · rw [ite_eq_left h3]; exact ⟨_, rfl⟩
    exfalso
    apply hg
    refine ⟨fun h => h1 (by rw [h, addrWord_zero]), fun h => h2 (by rw [h, addrWord_zero]), ?_⟩
    rw [hr.balances] at h3; exact not_not.mp h3

theorem views_exact {st : Storage} {s : State} (hr : Rel st s) (caller a : Address) :
    Properties.views_exact hr caller a := by
  refine ⟨⟨_, call_balanceOf _ _ _, rfl, rfl, ?_⟩, ⟨_, call_totalSupply _ _, rfl, rfl, ?_⟩,
    ⟨_, call_nativeTokenVault _ _, rfl, rfl, by rw [hr.vault]⟩⟩
  · exact congrArg some (hr.balances a)
  · exact congrArg some hr.supply

theorem deploy_establishes (deployer : Address) (config : Config) (hv : config.vault ≠ 0) :
    Properties.deploy_establishes deployer config hv := by
  have hv' : addrWord config.vault ≠ 0 := fun h => hv (addrWord_eq_zero.mp h)
  unfold Properties.deploy_establishes
  rw [deploy_eq, ite_eq_right hv']
  refine ⟨_, rfl, ⟨?_, hv, ?_, ?_⟩, rfl⟩
  · simp [upd, empty]
  · simp [upd, Storage.zero, empty]
  · intro _; simp [Storage.zero, empty]

theorem deploy_zero_vault_reverts (deployer : Address) :
    Properties.deploy_zero_vault_reverts deployer := by
  unfold Properties.deploy_zero_vault_reverts
  rw [deploy_eq, ite_eq_left addrWord_zero]

/-! ## Every call -/

theorem forall₂_two {R : Param → Word → Prop} {p q : Param} {args : List Word}
    (h : List.Forall₂ R [p, q] args) : ∃ x y, args = [x, y] ∧ R p x := by
  cases h with
  | cons hx t => cases t with
    | cons _ t2 => cases t2; exact ⟨_, _, rfl, hx⟩

theorem forall₂_one {R : Param → Word → Prop} {p : Param} {args : List Word}
    (h : List.Forall₂ R [p] args) : ∃ x, args = [x] := by
  cases h with
  | cons _ t => cases t; exact ⟨_, rfl⟩

theorem forall₂_nil {R : Param → Word → Prop} {args : List Word}
    (h : List.Forall₂ R [] args) : args = [] := by
  cases h; rfl

/-- An ABI-valid address argument as a model address. -/
def toAddr (v : Word) (h : v.val < 2 ^ 160) : Address := ⟨v.val, h⟩

theorem addrWord_toAddr (v : Word) (h : v.val < 2 ^ 160) : addrWord (toAddr v h) = v :=
  Fin.ext rfl

open LayeredVerification in
theorem match_step {st st' : Storage} {s : State} (hr : Rel st s) (hw : WellFormed s)
    (hstep : Step st st') :
    ∃ t, Run Contracts.BridgedStandardERC20.Step s t ∧ Rel st' t ∧ WellFormed t := by
  obtain ⟨⟨fn, hfind, hargs⟩, hcall⟩ := hstep
  rename_i fname caller args r
  have hmem := List.mem_of_find?_eq_some hfind
  have hname : fn.name = fname := by simpa using List.find?_some hfind
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at hmem
  -- getters: storage is unchanged, so the model stutters
  have stutter : r.st = st → ∃ t, Run Contracts.BridgedStandardERC20.Step s t ∧
      Rel r.st t ∧ WellFormed t := fun h => ⟨s, Run.refl s, h ▸ hr, hw⟩
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · -- bridgeMint
    obtain rfl : fname = "bridgeMint" := by rw [← hname]; rfl
    obtain ⟨x, y, rfl, hx⟩ := forall₂_two hargs
    have hx' := hx rfl
    rw [← addrWord_toAddr x hx'] at hcall
    rcases hm : Contracts.BridgedStandardERC20.mint s caller (toAddr x hx') y with _ | t
    · obtain ⟨e, he⟩ := (mint_refines hw hr caller _ y).1 hm
      rw [he] at hcall; exact nomatch hcall
    · obtain ⟨r', he, hrel, -⟩ := (mint_refines hw hr caller _ y).2 t hm
      rw [he] at hcall; cases hcall
      exact ⟨t, Run.tail (Run.refl s) (.mint hm), hrel,
        Contracts.BridgedStandardERC20.mint_preserves_ledger hw hm⟩
  · -- bridgeBurn
    obtain rfl : fname = "bridgeBurn" := by rw [← hname]; rfl
    obtain ⟨x, y, rfl, hx⟩ := forall₂_two hargs
    have hx' := hx rfl
    rw [← addrWord_toAddr x hx'] at hcall
    rcases hm : Contracts.BridgedStandardERC20.burn s caller (toAddr x hx') y with _ | t
    · obtain ⟨e, he⟩ := (burn_refines hw hr caller _ y).1 hm
      rw [he] at hcall; exact nomatch hcall
    · obtain ⟨r', he, hrel, -⟩ := (burn_refines hw hr caller _ y).2 t hm
      rw [he] at hcall; cases hcall
      exact ⟨t, Run.tail (Run.refl s) (.burn hm), hrel,
        Contracts.BridgedStandardERC20.burn_preserves_ledger hw hm⟩
  · -- transfer
    obtain rfl : fname = "transfer" := by rw [← hname]; rfl
    obtain ⟨x, y, rfl, hx⟩ := forall₂_two hargs
    have hx' := hx rfl
    rw [← addrWord_toAddr x hx'] at hcall
    rcases hm : Contracts.BridgedStandardERC20.transfer s caller (toAddr x hx') y with _ | t
    · obtain ⟨e, he⟩ := (transfer_refines hw hr caller _ y).1 hm
      rw [he] at hcall; exact nomatch hcall
    · obtain ⟨r', he, hrel, -⟩ := (transfer_refines hw hr caller _ y).2 t hm
      rw [he] at hcall; cases hcall
      exact ⟨t, Run.tail (Run.refl s) (.transfer hm), hrel,
        (Contracts.BridgedStandardERC20.transfer_preserves_ledger hw hm).1⟩
  · -- balanceOf
    obtain rfl : fname = "balanceOf" := by rw [← hname]; rfl
    obtain ⟨x, rfl⟩ := forall₂_one hargs
    rw [call_balanceOf] at hcall; cases hcall; exact stutter rfl
  · -- totalSupply
    obtain rfl : fname = "totalSupply" := by rw [← hname]; rfl
    rw [forall₂_nil hargs] at hcall
    rw [call_totalSupply] at hcall; cases hcall; exact stutter rfl
  · -- nativeTokenVault
    obtain rfl : fname = "nativeTokenVault" := by rw [← hname]; rfl
    rw [forall₂_nil hargs] at hcall
    rw [call_nativeTokenVault] at hcall; cases hcall; exact stutter rfl

def simulationWitness :
    LayeredVerification.Simulation Step Contracts.BridgedStandardERC20.Step where
  Rel st s := Rel st s ∧ WellFormed s
  match_step := by
    rintro st st' s ⟨hr, hw⟩ hstep
    obtain ⟨t, hrun, hrel, hwt⟩ := match_step hr hw hstep
    exact ⟨t, hrun, hrel, hwt⟩

theorem simulation : Properties.simulation := ⟨simulationWitness, fun _ _ => Iff.rfl⟩

theorem run_reach {s t : State}
    (h : LayeredVerification.Run Contracts.BridgedStandardERC20.Step s t) :
    Contracts.BridgedStandardERC20.Reach s t := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact .tail ih hstep

theorem empty_wellFormed (config : Config) : WellFormed (empty config) :=
  ⟨by simp only [empty, Finset.sum_const_zero], NeZero.pos _, rfl⟩

theorem reachable_ledger (deployer vault : Address) (hv : vault ≠ 0) :
    Properties.reachable_ledger deployer vault hv := by
  let config : Config := ⟨vault, 0, 0⟩
  obtain ⟨r, hdep, hrel, -⟩ := deploy_establishes deployer config hv
  refine ⟨r, hdep, ?_⟩
  refine LayeredVerification.safety_transfer (sim := simulationWitness)
    (SafeB := fun b => WellFormed b ∧ b.config = config)
    ⟨hrel, empty_wellFormed config⟩ ?_ ?_
  · intro b hb
    exact Contracts.BridgedStandardERC20.reachable_ledger (empty_wellFormed config) (run_reach hb)
  · rintro st b ⟨hr, -⟩ ⟨hwb, hcfg⟩
    refine ⟨?_, by rw [hr.vault, hcfg]⟩
    simp only [hr.balances, hr.supply]
    exact hwb.1

end Codegen.BridgedTokenSlice
