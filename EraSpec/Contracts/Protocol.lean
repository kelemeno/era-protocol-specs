import EraSpec.Core.IMT
import EraSpec.Contracts.InteropCommitmentTree

/-!
# The multi-chain protocol, and why `authorizeRefund` checks the source chain

Atomic interop runs across many chains, each with its own commitment tree.  This
file models that, and settles the one security question the single-tree theory
cannot even state.

## The gap this file closes

`EraSpec.Core.IMT` proves exclusivity for ONE tree: a delivered commit value has
no reclaim witness *in that tree* (`present_not_reclaimable`).  Nothing in it
mentions a chain id.  So a reader of that layer alone would reasonably conclude
that the multi-chain case had been handled — and it had not.  The sibling repo's
`AGENTS.md` records exactly this hazard:

> the payoff case was `authorizeRefund`'s source-chain binding, which is what
> makes the abstract single-tree exclusivity sound for a multi-chain system — a
> reader of the Lean alone would assume multi-chain was modelled and discharged,
> because no hypothesis there mentions a chain id.

The concrete repo cannot close it: its proofs are per-contract, over one
deployment's storage, and a cross-chain statement has nowhere to live there.  At
this level it is easy, so it belongs here.

## The attack, precisely

`commitValue(flowId, specHash) = keccak(TAG, flowId, specHash)` — note there is
**no chain id in it**.  The value is the same number on every chain.  What makes
it chain-specific is only *where it was inserted*: a leg's `append` runs on its
own source chain, so the value enters that chain's tree and no other.

That is a one-way binding, and it cuts the wrong way for refunds.  Membership
self-binds — a value can only be *found* in the tree it was inserted into.  But
absence does not: the very same number is trivially absent from every *other*
chain's tree, because nothing ever put it there.  So an attacker with a delivered,
finalized leg can point the refund gate at an unrelated chain, prove absence
there truthfully, and collect a refund on a leg that was already delivered — a
double spend.

The only thing standing between the protocol and that attack is one comparison in
`authorizeRefund`:

    if (_absence.sourceChainId != _flow.legSourceChainIds[_missingLegIndex]) revert;

`unbound_gate_refunds_delivered_leg` is the countermodel showing the attack is
real without it; `bound_gate_excludes_delivered` shows the check is sufficient.
Together they make the comparison's necessity a theorem rather than a comment.

## What is assumed

Nothing about keccak.  The countermodel is an explicit two-chain configuration
whose trees are both sound, so it cannot be dismissed as an artifact of a
degenerate state; the positive direction is `present_not_reclaimable` applied to
one chain.  Both are axiom-free.
-/

namespace Contracts.Protocol

open IMTAbstract

/-- Chain ids, as `uint256`. -/
abbrev Chain := UInt256

/-- The multi-chain state: every chain's commitment tree, viewed abstractly.

One `Finset AbsLeaf` per chain.  The indexed layer
(`Contracts.InteropCommitmentTree.Tree`) is what each chain actually stores;
`toAbs` projects to this, so `sound_of_valid_chains` below lifts a family of real
contract states into this model. -/
structure Protocol where
  trees : Chain → Finset AbsLeaf

/-- Every chain's tree is well-formed. -/
def AllSound (P : Protocol) : Prop := ∀ c, SoundState (P.trees c)

/-- The leg with commit value `v`, whose declared source chain is `src`, was
delivered: its value is a key of ITS OWN chain's tree.  Membership self-binds, so
this is the only chain where it could be. -/
def Delivered (P : Protocol) (src : Chain) (v : UInt256) : Prop :=
  v ∈ keys (P.trees src)

/-- A valid non-inclusion witness for `v` against chain `c`'s tree: a leaf whose
window straddles `v`.  This is what `IndexedMerkleTree.verifyNonInclusion`
accepts (modulo the Merkle path, which authenticates the leaf as belonging to
`c`'s tree — see `EraSpec.Core.Merkle`). -/
def AbsenceWitnessAt (P : Protocol) (c : Chain) (v : UInt256) : Prop :=
  ∃ W ∈ P.trees c, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)

/-- **The gate WITHOUT the source-chain check**: accepts an absence witness from
whatever chain the prover names. -/
def UnboundGate (P : Protocol) (v : UInt256) : Prop :=
  ∃ c, AbsenceWitnessAt P c v

/-- **The gate WITH the source-chain check**: the witness must come from the
leg's declared source chain, as `authorizeRefund` requires. -/
def BoundGate (P : Protocol) (src : Chain) (v : UInt256) : Prop :=
  AbsenceWitnessAt P src v

/-! ## The bound gate is safe -/

/-- **THE SOURCE-CHAIN CHECK IS SUFFICIENT.**  With the binding in place, a
delivered leg can never pass the refund gate — in a multi-chain world, with any
number of other chains in any state.

The proof is one chain's exclusivity: the binding forces the witness into
`P.trees src`, which is exactly where `v` is present.  The other chains'
contents become irrelevant, which is the whole point of the check. -/
theorem bound_gate_excludes_delivered {P : Protocol} {src : Chain} {v : UInt256}
    (hsound : SoundState (P.trees src)) (hdel : Delivered P src v) :
    ¬ BoundGate P src v :=
  present_not_reclaimable hsound.1 hdel

/-- The same, stated over a fully sound protocol — the form a caller wants. -/
theorem bound_gate_excludes_delivered' {P : Protocol} (hP : AllSound P)
    {src : Chain} {v : UInt256} (hdel : Delivered P src v) :
    ¬ BoundGate P src v :=
  bound_gate_excludes_delivered (hP src) hdel

/-- **DELIVERY AND REFUND ARE MUTUALLY EXCLUSIVE ACROSS THE WHOLE SYSTEM.**  The
headline multi-chain guarantee: no leg is both delivered and refundable, once the
gate is bound. -/
theorem no_double_spend_multichain {P : Protocol} (hP : AllSound P)
    {src : Chain} {v : UInt256} :
    ¬ (Delivered P src v ∧ BoundGate P src v) := by
  rintro ⟨hdel, hgate⟩
  exact bound_gate_excludes_delivered' hP hdel hgate

/-! ## The unbound gate is exploitable

The countermodel.  Two chains suffice: chain `0` is the leg's real source and has
delivered it; chain `1` is an unrelated chain that has never seen it. -/

/-- The attack configuration: `v` delivered on chain `0`, every other chain still
at genesis.

Chain `0`'s tree is built by an actual guarded insert from genesis, not written
down by hand — so its soundness is inherited rather than asserted, and the
countermodel cannot be dismissed as a malformed state that the real contract
would never reach. -/
def attackProtocol (v : UInt256) : Protocol where
  trees := fun c => if c = 0 then imtInsert ({⟨0, 0⟩} : Finset AbsLeaf) ⟨0, 0⟩ v
                    else ({⟨0, 0⟩} : Finset AbsLeaf)

lemma genesis_mem : (⟨0, 0⟩ : AbsLeaf) ∈ ({⟨0, 0⟩} : Finset AbsLeaf) :=
  Finset.mem_singleton_self _

/-- `v` is fresh at genesis whenever it is nonzero. -/
lemma genesis_fresh {v : UInt256} (hv : 0 < v) : v ∉ keys ({⟨0, 0⟩} : Finset AbsLeaf) := by
  intro hmem
  obtain ⟨X, hX, hXv⟩ := Finset.mem_image.mp hmem
  rw [Finset.mem_singleton] at hX
  subst hX
  have hz : (0 : UInt256) = v := hXv
  exact absurd hz (ne_of_lt hv)

/-- Every chain of the attack configuration is sound. -/
theorem attackProtocol_allSound {v : UInt256} (hv : 0 < v) :
    AllSound (attackProtocol v) := by
  intro c
  unfold attackProtocol
  by_cases hc : c = 0
  · simp only [hc, if_pos rfl]
    exact (guarded_insert_sound_step genesis_soundState genesis_mem hv
      (Or.inl rfl) (genesis_fresh hv)).1
  · simp only [if_neg hc]
    exact genesis_soundState

/-- The leg IS delivered on its own source chain. -/
theorem attackProtocol_delivered {v : UInt256} :
    Delivered (attackProtocol v) 0 v := by
  unfold Delivered attackProtocol
  simp only [if_pos rfl]
  exact imtInsert_key_mem genesis_mem

/-- …and it is *truthfully* absent from the unrelated chain `1`, which therefore
supplies a valid witness. -/
theorem attackProtocol_witness_elsewhere {v : UInt256} (hv : 0 < v) :
    AbsenceWitnessAt (attackProtocol v) 1 v := by
  refine ⟨⟨0, 0⟩, ?_, hv, Or.inl rfl⟩
  unfold attackProtocol
  simp only [if_neg (by decide : ¬ (1 : Chain) = 0)]
  exact genesis_mem

/-- **THE SOURCE-CHAIN CHECK IS NECESSARY.**  Without it, a delivered leg passes
the refund gate: there is a sound two-chain configuration in which `v` is
delivered on its declared source chain AND an unbound gate accepts a witness for
it — the double spend the check exists to prevent.

Note what makes this sharp: the witness is not forged.  Chain `1`'s tree really
does not contain `v`, and its non-inclusion proof is genuine.  The flaw is
entirely in accepting a *true* statement about the *wrong* chain, which is why no
amount of strengthening the Merkle machinery could fix it — only the binding
can. -/
theorem unbound_gate_refunds_delivered_leg {v : UInt256} (hv : 0 < v) :
    AllSound (attackProtocol v)
      ∧ Delivered (attackProtocol v) 0 v
      ∧ UnboundGate (attackProtocol v) v :=
  ⟨attackProtocol_allSound hv, attackProtocol_delivered,
   ⟨1, attackProtocol_witness_elsewhere hv⟩⟩

/-- The two results side by side: exclusivity holds for the bound gate and fails
for the unbound one, on the same configuration.  This is the precise sense in
which the one-line comparison in `authorizeRefund` is load-bearing. -/
theorem binding_is_exactly_what_separates_them {v : UInt256} (hv : 0 < v) :
    ¬ BoundGate (attackProtocol v) 0 v
      ∧ UnboundGate (attackProtocol v) v :=
  ⟨bound_gate_excludes_delivered' (attackProtocol_allSound hv) attackProtocol_delivered,
   ⟨1, attackProtocol_witness_elsewhere hv⟩⟩

/-! ## Lifting real contract states

The model above is over `Finset AbsLeaf`.  This connects it to the indexed
contract state machine, so the multi-chain results apply to actual per-chain
deployments rather than to an abstraction chosen for convenience. -/

open Contracts.InteropCommitmentTree in
/-- A family of valid per-chain contract states induces a sound `Protocol`. -/
def ofChains (T : Chain → Tree) : Protocol where
  trees := fun c => toAbs (T c)

open Contracts.InteropCommitmentTree in
/-- **REAL DEPLOYMENTS SATISFY THE MULTI-CHAIN GUARANTEE.**  If every chain's
commitment tree contract is in a valid state, then no leg is both delivered and
refundable through a bound gate.

This is the end-to-end protocol statement at this level: per-chain contract
validity (which `run_valid` gives for every run from `setup`) implies system-wide
no-double-spend. -/
theorem chains_no_double_spend {T : Chain → Tree} (hV : ∀ c, Valid (T c))
    {src : Chain} {v : UInt256} :
    ¬ (Delivered (ofChains T) src v ∧ BoundGate (ofChains T) src v) := by
  refine no_double_spend_multichain ?_
  intro c
  exact (hV c).absSound

end Contracts.Protocol
