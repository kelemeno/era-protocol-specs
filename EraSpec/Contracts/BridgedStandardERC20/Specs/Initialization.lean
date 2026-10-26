import EraSpec.Contracts.BridgedStandardERC20.Specs.Model

/-!
# Fresh-proxy initialization, token-state projection

Locally specified from `bridgeInitialize` and the top-level post-construction
OpenZeppelin v4 initializer branch at source pin c67894b970a0dac6fe9144d8ebf4b0806e15a9af.
The implementation constructor disables its own initialization (version 255);
fresh proxy storage starts at version zero. Constructor-only/nested initializer
cases, metadata contents, events, permit/allowance fields, and proxy execution
semantics are outside this projection. `metadataDecoded` records success of the
required outer metadata decode/setup, not success of every caught getter decode.

Initialization assigns vault := caller; it has no owner/vault caller guard.
The vault's deployment sequence must supply the intended caller. Ledger values
are preserved, not reset: a zero ledger follows from fresh proxy storage.
-/

namespace Contracts.BridgedStandardERC20

structure InitState where
  token : State
  version : UInt8

def freshProxy : InitState := ⟨empty ⟨0, 0, 0⟩, 0⟩

def disabledImplementation : InitState := ⟨empty ⟨0, 0, 0⟩, 255⟩

def InitializeAllowed (s : InitState) (originToken : Address) : Prop :=
  s.version = 0 ∧ originToken ≠ 0

instance (s : InitState) (originToken : Address) : Decidable (InitializeAllowed s originToken) :=
  inferInstanceAs (Decidable (_ ∧ _))

def initializeToken (s : InitState) (caller : Address) (assetId : UInt256)
    (originToken : Address) (metadataDecoded : Bool) : Option InitState :=
  if InitializeAllowed s originToken ∧ metadataDecoded = true then
    some ⟨{ s.token with config := ⟨caller, originToken, assetId⟩ }, 1⟩
  else none

end Contracts.BridgedStandardERC20
