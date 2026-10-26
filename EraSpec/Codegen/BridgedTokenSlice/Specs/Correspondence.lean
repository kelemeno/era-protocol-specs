import EraSpec.Codegen.BridgedTokenSlice.Specs.Program
import EraSpec.Contracts.BridgedStandardERC20.Specs.Model

/-!
# Correspondence between the generated program and the token model

The definitions the refinement statements are phrased in.  `Rel` is the
representation claim and is the definition to review: the vault slot holds the
model's vault and it is nonzero; the supply slot's value is the model's supply;
and every *address-range* key of the balances mapping holds that address's model
balance.  Keys at or above `2^160` are unconstrained — no ABI-valid call can name
them.  `Step` is "any successful external call": every function, any caller, any
ABI-valid arguments.
-/

namespace Codegen.BridgedTokenSlice

open Codegen
open Contracts.BridgedStandardERC20 (Address State)

/-- An address as the word the ABI decoder produces. -/
def addrWord (a : Address) : Word := ⟨a.val, lt_trans a.isLt (by decide)⟩

/-- Storage of the generated contract represents the model state. -/
structure Rel (st : Storage) (s : State) : Prop where
  vault : st.scalars "_nativeTokenVault" = addrWord s.config.vault
  vault_ne : s.config.vault ≠ 0
  supply : (st.scalars "_totalSupply").val = s.totalSupply
  balances : ∀ a : Address, (st.maps "_balances" (addrWord a)).val = s.balances a

/-- The logs a successful mint emits, in order. -/
def mintLogs (recipient : Address) (amount : Word) : List Log :=
  [⟨"Transfer", [0, addrWord recipient, amount]⟩, ⟨"BridgeMint", [addrWord recipient, amount]⟩]

def burnLogs (account : Address) (amount : Word) : List Log :=
  [⟨"Transfer", [addrWord account, 0, amount]⟩, ⟨"BridgeBurn", [addrWord account, amount]⟩]

def transferLogs (owner recipient : Address) (amount : Word) : List Log :=
  [⟨"Transfer", [addrWord owner, addrWord recipient, amount]⟩]

/-- ABI-valid arguments: the function exists, the arity matches, and every
address argument is below `2^160` (`SOL-ABI`). -/
def AbiValid (fname : String) (args : List Word) : Prop :=
  ∃ fn, program.find fname = some fn ∧
    List.Forall₂ (fun p (v : Word) => p.ty = .address → v.val < 2 ^ 160) fn.params args

/-- Any successful external call to the generated contract, by any address. -/
inductive Step : Storage → Storage → Prop
  | call {st : Storage} {fname : String} {caller : Address} {args : List Word} {r : Success} :
      AbiValid fname args →
      Codegen.call program fname (addrWord caller) args st = some (.ok r) → Step st r.st

end Codegen.BridgedTokenSlice
