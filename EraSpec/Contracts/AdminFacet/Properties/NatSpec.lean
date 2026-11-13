import EraSpec.Contracts.AdminFacet.Specs.AdminFacet

/-!
# Properties: two NatSpec statements of `IAdmin` that the code does not match

Statements about `EraSpec.Contracts.AdminFacet.Specs.AdminFacet`; proofs in
`EraSpec.Contracts.AdminFacet.Proofs.NatSpec`. Internal findings; not published.

* `IAdmin.sol:56` documents `setPubdataPricingMode` as "Change the pubdata pricing mode before the
  first batch is processed". The batch check was removed in `fd7e4cd6e3` ("Fix audittens L03");
  the code reads no batch counter. `PricingModeIgnoresBatches` states the exact behaviour and
  `PricingModeChangesAfterFirstBatch` refutes the comment.
* `IAdmin.sol:78-80` says priority mode "can be activated if: 1. The Chain Admin has explicitly
  enabled the Priority Mode feature. 2. A priority transaction has been outstanding for at least
  `PRIORITY_EXPIRATION` since it was requested." The code also requires a permanent rollup
  (`Admin.sol:528-530`), which `permanentlyAllowPriorityMode` does not establish.
  `ActivationNatSpecConditionsInsufficient` exhibits a reachable chain meeting both listed
  conditions on which activation reverts.
-/

namespace Contracts.AdminFacet

/-- **`setPubdataPricingMode`, EXACTLY.** When the diamond does not block it, the call succeeds
iff the caller is the admin, the chain is on L1 and priority mode is not allowed; it then writes
only the pricing mode. No batch counter is read. -/
def Properties.PricingModeIgnoresBatches : Prop :=
  ∀ (K : Config) (e : Env) (s : State) (a : Address) (τ m : ℕ),
    ¬ (s.frozen = true ∧ s.freezable (Entry.setPubdataPricingMode 0).sel = true) →
    call K e s ⟨a, τ, .setPubdataPricingMode m⟩ =
      if a = s.admin ∧ K.onL1 = true ∧ s.priorityMode.canBeActivated = false then
        some { s with feeParams := { s.feeParams with pricingMode := m } }
      else none

/-- **REFUTES `IAdmin.sol:56`.** On a chain with committed and executed batches, the admin's
`setPubdataPricingMode` succeeds and changes the pricing mode. -/
def Properties.PricingModeChangesAfterFirstBatch : Prop :=
  ∃ (K : Config) (e : Env) (s s' : State) (τ m : ℕ),
    s.totalBatchesCommitted ≠ 0 ∧ s.totalBatchesExecuted ≠ 0 ∧
    call K e s ⟨s.admin, τ, .setPubdataPricingMode m⟩ = some s' ∧
    s'.feeParams.pricingMode ≠ s.feeParams.pricingMode

/-- **REFUTES THE SUFFICIENCY READING OF `IAdmin.sol:78-80`.** A run without cuts from a chain
with priority mode neither allowed nor active reaches a state where the admin has allowed priority
mode, the first unprocessed priority transaction was requested at `t ≠ 0` with
`t + PRIORITY_EXPIRATION ≤ τ`, the chain is on L1 and on its settlement layer, priority mode is
inactive and the diamond is not frozen; yet `activatePriorityMode` at `τ` reverts, because the
chain is not a permanent rollup. -/
def Properties.ActivationNatSpecConditionsInsufficient : Prop :=
  ∃ (K : Config) (w w' : World) (ls : List Label) (a : Address) (τ : ℕ),
    Run K w ls w' ∧ (∀ l ∈ ls, l.runsCut = false) ∧
    w.st.priorityMode.canBeActivated = false ∧ w.st.priorityMode.activated = false ∧
    w'.st.priorityMode.canBeActivated = true ∧ w'.st.priorityMode.activated = false ∧
    w'.st.requestTimestamp w'.st.firstUnprocessed ≠ 0 ∧
    w'.st.requestTimestamp w'.st.firstUnprocessed + PRIORITY_EXPIRATION ≤ τ ∧
    K.onL1 = true ∧ w'.st.settlementLayer = 0 ∧ w'.st.frozen = false ∧
    call K w'.env w'.st ⟨a, τ, .activatePriorityMode⟩ = none

end Contracts.AdminFacet
