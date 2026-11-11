import EraSpec.Protocol.MultichainGate.Specs.Model

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false

/-!
# The multi-chain protocol, and why `authorizeRefund` checks the source chain

Atomic interop runs across many chains, each with its own commitment tree.  This
file states the one security question the single-tree theory cannot even state.

## The gap this file closes

`EraSpec.Contracts.IndexedMerkleTree.Proofs.Model` proves exclusivity for ONE tree: a delivered commit value has
no reclaim witness *in that tree* (`present_not_reclaimable`).  Nothing in it
mentions a chain id.  So a reader of that layer alone would reasonably conclude
that the multi-chain case had been handled — and it had not.  The sibling repo's
`AGENTS.md` records exactly this hazard:

> the payoff case was `authorizeRefund`'s source-chain binding, which is what
> makes the abstract single-tree exclusivity sound for a multi-chain system — a
> reader of the Lean alone would assume multi-chain was modelled and discharged,
> because no hypothesis there mentions a chain id.

## The attack, precisely

`commitValue(flowId, specHash) = keccak(TAG, flowId, specHash)` — note there is
**no chain id in it**.  The value is the same number on every chain.  What makes
it chain-specific is only *where it was inserted*: a leg's `append` runs on its
own source chain, so the value enters that chain's tree.

Absence does not bind to a chain: the very same number is trivially absent from
the tree of any chain that never inserted it.  So an attacker with a delivered,
finalized leg can point the refund gate at an unrelated chain, prove absence
there truthfully, and collect a refund on a leg that was already delivered — a
double spend.

The only thing standing between the protocol and that attack is one comparison in
`authorizeRefund`:

    if (_absence.sourceChainId != _flow.legSourceChainIds[_missingLegIndex]) revert;

`unbound_gate_refunds_delivered_leg` is the countermodel showing the attack is
real without it; `bound_gate_excludes_delivered` shows the check is sufficient.

## What is assumed

Nothing about keccak: no statement here has a hash premise.  The countermodel is
an explicit configuration in which every chain's tree is sound;
`chains_unbound_gate_refunds_delivered_leg` realizes it by actual contract states
(`setup` and one guarded `insert`).

## Anti-vacuity

* `bound_gate_not_dead` / `chains_unbound_gate_refunds_delivered_leg`: the
  premises of the safety results hold with the leg delivered, and the bound gate
  does open for a leg whose declared source chain never inserted it — so the
  safety results do not come from a gate that never fires.
* `chains_bound_gate_iff_undelivered`: on a valid contract state and a nonzero
  value, the bound gate fires exactly on the undelivered legs.
-/

namespace Contracts.Protocol

open IMTAbstract

/-! ## The bound gate is safe -/

/-- **THE SOURCE-CHAIN CHECK IS SUFFICIENT.**  With the binding in place, a
delivered leg can never pass the refund gate.  Only the source chain's tree is
assumed sound; the other chains may be in any state. -/
abbrev Properties.bound_gate_excludes_delivered {P : Protocol} {src : Chain} {v : UInt256}
    (hsound : SoundState (P.trees src)) (hdel : Delivered P src v) :=
  ¬ BoundGate P src v

/-- The same, stated over a fully sound protocol — the form a caller wants. -/
abbrev Properties.bound_gate_excludes_delivered' {P : Protocol} (hP : AllSound P)
    {src : Chain} {v : UInt256} (hdel : Delivered P src v) :=
  ¬ BoundGate P src v

/-- **DELIVERY AND REFUND ARE MUTUALLY EXCLUSIVE ACROSS THE WHOLE SYSTEM.**  No
leg is both delivered and refundable, once the gate is bound. -/
abbrev Properties.no_double_spend_multichain {P : Protocol} (hP : AllSound P)
    {src : Chain} {v : UInt256} :=
  ¬ (Delivered P src v ∧ BoundGate P src v)

/-! ## The unbound gate is exploitable

The countermodel.  Two chains suffice: chain `0` is the leg's real source and has
delivered it; chain `1` is an unrelated chain that has never seen it. -/

/-- Every chain of the attack configuration is sound. -/
abbrev Properties.attackProtocol_allSound {v : UInt256} (hv : 0 < v) :=
  AllSound (attackProtocol v)

/-- The leg IS delivered on its own source chain. -/
abbrev Properties.attackProtocol_delivered {v : UInt256} :=
  Delivered (attackProtocol v) 0 v

/-- …and the unrelated chain `1` supplies a valid absence witness for it. -/
abbrev Properties.attackProtocol_witness_elsewhere {v : UInt256} (hv : 0 < v) :=
  AbsenceWitnessAt (attackProtocol v) 1 v

/-- **THE SOURCE-CHAIN CHECK IS NECESSARY.**  Without it, a delivered leg passes
the refund gate: in a configuration where every chain is sound, `v` is delivered
on its declared source chain AND an unbound gate accepts a witness for it.

The witness is not forged: it is a leaf of chain `1`'s tree whose window
straddles `v`.  The flaw is accepting a statement about the *wrong* chain. -/
abbrev Properties.unbound_gate_refunds_delivered_leg {v : UInt256} (hv : 0 < v) :=
  AllSound (attackProtocol v)
      ∧ Delivered (attackProtocol v) 0 v
      ∧ UnboundGate (attackProtocol v) v

/-- The two results side by side on the same configuration: the bound gate
rejects the delivered leg, the unbound gate accepts it. -/
abbrev Properties.binding_is_exactly_what_separates_them {v : UInt256} (hv : 0 < v) :=
  ¬ BoundGate (attackProtocol v) 0 v
      ∧ UnboundGate (attackProtocol v) v

/-- **ANTI-VACUITY (abstract layer).**  The premises of
`bound_gate_excludes_delivered`, `bound_gate_excludes_delivered'` and
`no_double_spend_multichain` hold with the leg delivered on chain `0`, and the
bound gate does open for value `v` against chain `1`, which never inserted it. -/
abbrev Properties.bound_gate_not_dead {v : UInt256} (hv : 0 < v) :=
  AllSound (attackProtocol v)
      ∧ Delivered (attackProtocol v) 0 v
      ∧ BoundGate (attackProtocol v) 1 v

/-! ## Lifting real contract states -/

open Contracts.InteropCommitmentTree in
/-- **REAL DEPLOYMENTS SATISFY THE MULTI-CHAIN GUARANTEE.**  If every chain's
commitment tree contract is in a valid state, then no leg is both delivered and
refundable through a bound gate.  (`run_valid` gives validity for every state of
a run from `setup`.) -/
abbrev Properties.chains_no_double_spend {T : Chain → Tree} (hV : ∀ c, Valid (T c))
    {src : Chain} {v : UInt256} :=
  ¬ (Delivered (ofChains T) src v ∧ BoundGate (ofChains T) src v)

open Contracts.InteropCommitmentTree in
/-- **THE BOUND GATE FIRES EXACTLY ON UNDELIVERED LEGS.**  For a valid contract
state on the declared source chain and a nonzero commit value, the bound gate
accepts iff the value is not a key of that chain's tree.  Only the source chain's
validity is assumed.  This is safety (`→`) and liveness (`←`) together, so
`chains_no_double_spend` is not explained by a gate that never opens. -/
abbrev Properties.chains_bound_gate_iff_undelivered {T : Chain → Tree} {src : Chain}
    (hV : Valid (T src)) {v : UInt256} (hv : v ≠ 0) :=
  BoundGate (ofChains T) src v ↔ ¬ Delivered (ofChains T) src v

open Contracts.InteropCommitmentTree in
/-- Every chain of the contract-level attack configuration is in a valid state. -/
abbrev Properties.attackChains_valid {v : UInt256} (hv : 0 < v) :=
  ∀ c, Valid (attackChains v c)

/-- **THE ATTACK IS REALIZED BY ACTUAL CONTRACT STATES.**  On `attackChains v`
(chain `0`: `setup` then `insert(v, 0)`; every other chain: `setup`), every
chain is valid, `v` is delivered on chain `0`, the unbound gate accepts it, the
bound gate for source chain `0` rejects it, and the bound gate for source chain
`1` accepts it.

This is the contract-level counterpart of `unbound_gate_refunds_delivered_leg`,
and the anti-vacuity witness for `chains_no_double_spend` (its premise holds with
the leg delivered) and `chains_bound_gate_iff_undelivered` (both sides of the iff
are exercised, true at chain `1` and false at chain `0`). -/
abbrev Properties.chains_unbound_gate_refunds_delivered_leg {v : UInt256} (hv : 0 < v) :=
  (∀ c, Contracts.InteropCommitmentTree.Valid (attackChains v c))
      ∧ Delivered (ofChains (attackChains v)) 0 v
      ∧ UnboundGate (ofChains (attackChains v)) v
      ∧ ¬ BoundGate (ofChains (attackChains v)) 0 v
      ∧ BoundGate (ofChains (attackChains v)) 1 v

end Contracts.Protocol
