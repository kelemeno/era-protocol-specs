import EraSpec.Contracts.NativeTokenVaultBase.Specs.RepresentationPreparation

/-!
# Accounting for prepared representation transfers

The pending list is trace bookkeeping, NOT vault storage or proof of publication.
Each successful preparation contributes its exact returned data and outer route
context once. Ordinary source-token transfers remain possible between preparations.
This closed slice admits no independent minting, destination delivery, or refund;
those require new transitions and conservation proofs before being included.
-/

namespace AssetBridgePreparation

open Contracts

structure Obligation where
  destinationChain : UInt256
  assetId : UInt256
  data : NativeTokenVaultBase.MintData

structure Ledger (Accounting : Type) where
  vault : NativeTokenVaultBase.State Accounting
  pending : List Obligation

def pendingAmount (pending : List Obligation) : ℕ :=
  (pending.map fun obligation => obligation.data.amount.val).sum

def obligation (r : NativeTokenVaultBase.Request) (data : NativeTokenVaultBase.MintData) :
    Obligation := ⟨r.destinationChain, r.assetId, data⟩

variable {Accounting : Type}

inductive Step (hooks : NativeTokenVaultBase.Hooks Accounting) :
    Ledger Accounting → Ledger Accounting → Prop
  | prepare {s : Ledger Accounting} {r out} :
      NativeTokenVaultBase.prepare hooks s.vault r = some out →
      Step hooks s ⟨out.state, s.pending ++ [obligation r out.data]⟩
  | spend {s : Ledger Accounting} {owner recipient amount token} :
      BridgedStandardERC20.transfer s.vault.token owner recipient amount = some token →
      Step hooks s ⟨{ s.vault with token := token }, s.pending⟩

inductive Reach (hooks : NativeTokenVaultBase.Hooks Accounting) :
    Ledger Accounting → Ledger Accounting → Prop
  | refl {s} : Reach hooks s s
  | tail {s t u} : Reach hooks s t → Step hooks t u → Reach hooks s u

end AssetBridgePreparation
