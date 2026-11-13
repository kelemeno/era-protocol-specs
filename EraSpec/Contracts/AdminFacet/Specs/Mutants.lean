import EraSpec.Contracts.AdminFacet.Specs.AdminFacet

/-!
# Mutants: the facet with one source check removed

Definitions only. Each mutant is the transcription in `Specs/AdminFacet.lean` with exactly one
check deleted. The countermodels in `Properties/PriorityMode.lean` and `Properties/Upgrade.lean`
use them to show that the deleted check is what a guarantee rests on. Source: era-contracts
`d9f678900e1bc8286412b78f56d4a9f443983c29`.
-/

namespace Contracts.AdminFacet

/-- `setTransactionFilterer` (`Admin.sol:368-373`) without the
`if (s.priorityModeInfo.canBeActivated) revert NotCompatibleWithPriorityMode();` check
(`:369-371`). -/
def setTransactionFiltererWithoutGuard (K : Config) (s : State) (sender a : Address) :
    Option State :=
  req (sender = s.admin) <| onlyL1 K <|
  some { s with transactionFilterer := a }

/-- `setZKsyncOSL1TxFiltering` (`Admin.sol:190-199`) without the
`if (_enabled && s.priorityModeInfo.canBeActivated) revert NotCompatibleWithPriorityMode();`
check (`:191-193`). -/
def setL1TxFilteringWithoutGuard (s : State) (sender : Address) (b : Bool) : Option State :=
  req (sender = s.admin) <| onlySettlementLayer s <|
  noUnverifiedBatches s <|
  some { s with l1TxFiltering := b }

/-- `upgradeChainFromVersion` (`Admin.sol:559-590`) without the final
`if (s.protocolVersion <= _oldProtocolVersion) revert ProtocolIdNotGreater();` (`:587-589`). -/
def upgradeWithoutPostCheck (K : Config) (e : Env) (s : State) (c : Call) (v : ℕ) :
    Option State :=
  req (c.sender = s.admin ∨ c.sender = s.chainTypeManager ∨ s.validators c.sender = true) <|
  match e.upgradeCutForVersion s.chainTypeManager v with
  | none => none
  | some cut =>
    req (s.protocolVersion = v) <|
    req (c.sender ≠ s.admin ∧ c.sender ≠ s.chainTypeManager →
        e.upgradeTimestamp s.chainTypeManager v ≠ 0
          ∧ e.upgradeTimestamp s.chainTypeManager v ≤ c.time) <|
    executeDiamondCut K e cut s

end Contracts.AdminFacet
