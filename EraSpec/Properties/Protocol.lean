import EraSpec.Contracts.Protocol

/-!
# Properties: the multi-chain protocol

Statements about `EraSpec.Contracts.Protocol`: the bound refund gate is safe, the
unbound one is exploitable, and real per-chain deployments inherit the guarantee.
Proofs are in `EraSpec.Proofs.Protocol`.

Together, `BoundGateExcludesDelivered` and `UnboundGateRefundsDeliveredLeg` make
the one-line `sourceChainId` comparison in `authorizeRefund` a theorem's worth of
necessity rather than a comment.
-/

namespace Properties.Protocol

open IMTAbstract Contracts.Protocol Contracts.InteropCommitmentTree

/-! ## The bound gate is safe -/

/-- The source-chain check is sufficient: with the binding in place, a delivered
leg never passes the refund gate — in a multi-chain world, with any number of
other chains in any state. -/
def BoundGateExcludesDelivered : Prop :=
  ∀ (P : Protocol) (src : Chain) (v : UInt256),
    SoundState (P.trees src) → Delivered P src v → ¬ BoundGate P src v

/-- The same, over a fully sound protocol. -/
def BoundGateExcludesDelivered' : Prop :=
  ∀ (P : Protocol), AllSound P → ∀ (src : Chain) (v : UInt256),
    Delivered P src v → ¬ BoundGate P src v

/-- Delivery and refund are mutually exclusive across the whole system, once the
gate is bound. -/
def NoDoubleSpendMultichain : Prop :=
  ∀ (P : Protocol), AllSound P → ∀ (src : Chain) (v : UInt256),
    ¬ (Delivered P src v ∧ BoundGate P src v)

/-- Real deployments satisfy the guarantee: if every chain's commitment tree
contract is in a valid state, no leg is both delivered and refundable through a
bound gate. -/
def ChainsNoDoubleSpend : Prop :=
  ∀ (T : Chain → Tree), (∀ c, Valid (T c)) → ∀ (src : Chain) (v : UInt256),
    ¬ (Delivered (ofChains T) src v ∧ BoundGate (ofChains T) src v)

/-! ## The unbound gate is exploitable

The countermodel `attackProtocol v`: `v` delivered on chain `0`, every other chain
at genesis. -/

/-- Every chain of the attack configuration is sound — so it cannot be dismissed
as a malformed state the real contract would never reach. -/
def AttackProtocolAllSound : Prop :=
  ∀ v : UInt256, 0 < v → AllSound (attackProtocol v)

/-- The leg IS delivered on its own source chain. -/
def AttackProtocolDelivered : Prop :=
  ∀ v : UInt256, Delivered (attackProtocol v) 0 v

/-- …and it is truthfully absent from the unrelated chain `1`, which therefore
supplies a valid witness. -/
def AttackProtocolWitnessElsewhere : Prop :=
  ∀ v : UInt256, 0 < v → AbsenceWitnessAt (attackProtocol v) 1 v

/-- The source-chain check is necessary: there is a sound two-chain configuration
in which `v` is delivered on its declared source chain AND an unbound gate accepts
a witness for it.  The witness is not forged — chain `1` really does not contain
`v`.  The flaw is entirely in accepting a TRUE statement about the WRONG chain,
which is why no strengthening of the Merkle machinery could fix it. -/
def UnboundGateRefundsDeliveredLeg : Prop :=
  ∀ v : UInt256, 0 < v →
    AllSound (attackProtocol v) ∧ Delivered (attackProtocol v) 0 v ∧ UnboundGate (attackProtocol v) v

/-- Side by side on the same configuration: exclusivity holds for the bound gate
and fails for the unbound one. -/
def BindingIsExactlyWhatSeparatesThem : Prop :=
  ∀ v : UInt256, 0 < v → ¬ BoundGate (attackProtocol v) 0 v ∧ UnboundGate (attackProtocol v) v

end Properties.Protocol
