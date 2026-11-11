import EraSpec.Codegen.VaultPreparationSlice.Specs.Correspondence
import EraSpec.Contracts.NativeTokenVaultBase.Specs.TrackerHooks

/-!
# The deployed L1 chain-balance hook as a concrete hook of the vault slice

`Codegen.VaultPreparationSlice` runs the vault program against concrete hooks `CHooks` and asks
only that they agree with the model's (`HooksAgree`).  On L1 the accounting hook is
`L1NativeTokenVault._handleBridgeToChain` (`bridge/ntv/L1NativeTokenVault.sol:259-264`, pin
`c67894b9`): it reads `originChainId` and reads and writes `bridgedOut`, and never reads the token.
`l1CHooks` is that hook over the ledger `Contracts.NativeTokenVaultBase.L1Ledger`; it ignores the
token storage the machine passes it.  Its failure (checked-addition overflow) is given empty revert
data here, which `HooksAgree` does not constrain.  The metadata hook is a parameter.

The ledger's `originChainId` is a copy of the vault's `_originChainId` map kept in the accounting
state, because the slice's hooks see only the accounting state and the token: nothing in the slice
writes either, so the copy stays what it was; that it equals the vault's slot is a representation
premise outside `Rel` (which relates the tracked asset's slot only).
-/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.NativeTokenVaultBase (L1Ledger l1ToChain)

/-- The L1 vault's outbound hook as a concrete hook, and a given metadata hook. -/
def l1CHooks (thisChain : Word) (cm : Storage → Word → Except XFailure Bytes) : CHooks L1Ledger where
  account acc _ _ a m :=
    match l1ToChain thisChain acc a m with
    | some x => .ok x
    | none => .error .empty
  metadata := cm

/-- The metadata half of `HooksAgree`. -/
def MetadataAgrees (cm : Storage → Word → Except XFailure Bytes)
    (md : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes) : Prop :=
  ∀ st t o, TokenRel st t → (cm st o).toOption = md t o

end Codegen.VaultPreparationSlice
