import EraSpec.Contracts.AtomicFlowManager.Specs.FlowCanonicalAtV35

/-!
# Properties at `draft/v0.35.0`: what `_validateAndComputeFlowId` accepts

Statements about `EraSpec.Contracts.AtomicFlowManager.Specs.FlowCanonicalAtV35` (era-contracts
`draft/v0.35.0`, commit `d9f678900`).  Proofs are in
`EraSpec.Contracts.AtomicFlowManager.Proofs.FlowCanonicalAtV35`.

* **The pin's `Valid` is still necessary** (`AcceptedV35ImpliesValid`), so every pin theorem of
  the form `Valid f → …` applies to every preimage v35 accepts.  The three that the source
  relies on are restated over `AcceptedV35`: no duplicated leg, a unique presentation per leg
  set, and a functional leg-to-source-chain pairing.
* **It is no longer sufficient**: the version byte and the leg cap reject valid preimages
  (`ValidNotSufficientVersionV35`, `ValidNotSufficientLegCapV35`).  `AcceptedV35Iff` is the
  exact acceptance condition, and `ValidateV35SomeIff` / `CheckFlowIdV35Iff` tie the executable
  transcription of `AtomicFlowManager.sol:348-379` to it.
* **An oversized flow can never touch a manager**: `_validateAndComputeFlowId` reverts on it,
  and `append` (`:109`), `requireFlowFinalized` (`:182`) and `authorizeRefund` (`:217`) all run
  it (`TooManyLegsRejectedV35`).
* **The flow id binds the whole preimage, up to a named collision**
  (`SameFlowIdSamePreimageOrClashV35`): two checked flows with one id have the same legs, source
  chains, deadline and settlement layer, or the two preimages are a `PreimageClashV35`.  The
  clash disjunct is not a tautology (`PreimageClashNotForcedV35`).

No property assumes a hash fact.
-/

namespace Contracts.FlowCanonicalAtV35

open AttackVectors.FlowCanonical

/-! ## Valid is necessary, not sufficient -/

/-- **`Valid` IS STILL NECESSARY.**  Every preimage `_validateAndComputeFlowId` accepts at v35
passes the pin's two checks (`AtomicFlowManager.sol:370-377`). -/
def Properties.AcceptedV35ImpliesValid : Prop :=
  ∀ p : PreimageV35, AcceptedV35 p → Valid p.arrays

/-- **THE EXACT ACCEPTANCE CONDITION.**  Version byte `0x01`, at most eight legs, and the pin's
`Valid` (`AtomicFlowManager.sol:360-377`). -/
def Properties.AcceptedV35Iff : Prop :=
  ∀ p : PreimageV35, AcceptedV35 p ↔
    p.version = ATOMIC_FLOW_PREIMAGE_VERSION_V35
      ∧ p.legBundleHashes.length ≤ MAX_ATOMIC_FLOW_LEGS_V35 ∧ Valid p.arrays

/-- **`Valid` IS NOT SUFFICIENT: THE VERSION BYTE.**  A preimage the pin's checks accept, within
the leg cap, that v35 rejects for its version (`:361-363`). -/
def Properties.ValidNotSufficientVersionV35 : Prop :=
  ∃ p : PreimageV35, Valid p.arrays ∧ p.legBundleHashes.length ≤ MAX_ATOMIC_FLOW_LEGS_V35
    ∧ ¬ AcceptedV35 p

/-- **`Valid` IS NOT SUFFICIENT: THE LEG CAP.**  A preimage with the right version that the
pin's checks accept and v35 rejects for having nine legs (`:367-369`). -/
def Properties.ValidNotSufficientLegCapV35 : Prop :=
  ∃ p : PreimageV35, Valid p.arrays ∧ p.version = ATOMIC_FLOW_PREIMAGE_VERSION_V35
    ∧ ¬ AcceptedV35 p

/-- **THE TRANSCRIPTION MEANS WHAT IT SAYS.**  `validateV35` returns an id exactly when the
preimage is accepted, and the id is its hash (`AtomicFlowManager.sol:360-379`). -/
def Properties.ValidateV35SomeIff : Prop :=
  ∀ (enc : PreimageHashV35) (p : PreimageV35) (id : UInt256),
    validateV35 enc p = some id ↔ AcceptedV35 p ∧ enc p = id

/-- **`_checkFlowId` AT v35** (`AtomicFlowManager.sol:348-353`) passes exactly when the preimage
is accepted and hashes to the claimed id. -/
def Properties.CheckFlowIdV35Iff : Prop :=
  ∀ (enc : PreimageHashV35) (F : AtomicFlowV35),
    CheckFlowIdV35 enc F ↔ AcceptedV35 F.preimage ∧ enc F.preimage = F.flowId

/-- **AN OVERSIZED FLOW IS REJECTED ON EVERY PATH.**  More than `MAX_ATOMIC_FLOW_LEGS` legs make
`_validateAndComputeFlowId` revert, whatever the hash; it is the first thing `append` (`:109`),
`requireFlowFinalized` (`:182`) and `authorizeRefund` (`:217`) run, so such a flow can never
commit, finalize or refund a leg (`IAtomicInterop.sol:93-98`). -/
def Properties.TooManyLegsRejectedV35 : Prop :=
  ∀ (enc : PreimageHashV35) (p : PreimageV35),
    MAX_ATOMIC_FLOW_LEGS_V35 < p.legBundleHashes.length → validateV35 enc p = none

/-! ## The pin's canonicity results, over v35's acceptance -/

/-- **NO DUPLICATED LEG.**  Distinct positions of an accepted preimage carry distinct bundle
hashes: the neighbour scan (`:370-374`) still lifts to all pairs. -/
def Properties.AcceptedV35NoDuplicateLeg : Prop :=
  ∀ (p : PreimageV35), AcceptedV35 p → ∀ (i j : Fin p.legBundleHashes.length), i ≠ j →
    p.legBundleHashes.get i ≠ p.legBundleHashes.get j

/-- **THE PRESENTATION IS UNIQUE PER LEG SET.**  Two accepted preimages over the same legs in any
order have identical leg lists. -/
def Properties.AcceptedV35UniquePerLegSet : Prop :=
  ∀ (p q : PreimageV35), AcceptedV35 p → AcceptedV35 q →
    p.legBundleHashes.Perm q.legBundleHashes → p.legBundleHashes = q.legBundleHashes

/-- **EVERY LEG HAS EXACTLY ONE SOURCE CHAIN.**  In an accepted preimage the zipped
`(bundleHash, sourceChainId)` pairing has distinct keys and loses no leg (`:375-377`). -/
def Properties.AcceptedV35PairingFunctional : Prop :=
  ∀ (p : PreimageV35), AcceptedV35 p →
    ((p.legBundleHashes.zip p.legSourceChainIds).map Prod.fst).Nodup
      ∧ (p.legBundleHashes.zip p.legSourceChainIds).length = p.legBundleHashes.length

/-! ## The flow id binds the whole preimage, up to a named collision -/

/-- **ONE ID, ONE PREIMAGE, OR A NAMED CLASH.**  Two flows that pass `_checkFlowId` with the same
id have the same preimage — legs, source chains, deadline, settlement layer and version — or
their two preimages are a `PreimageClashV35`.  `flowId = keccak256(abi.encode(preimage))`
(`:378`) covers every field, unlike the pin's four-argument encoding. -/
def Properties.SameFlowIdSamePreimageOrClashV35 : Prop :=
  ∀ (enc : PreimageHashV35) (F G : AtomicFlowV35), CheckFlowIdV35 enc F → CheckFlowIdV35 enc G →
    F.flowId = G.flowId →
      (F.preimage.legBundleHashes = G.preimage.legBundleHashes
        ∧ F.preimage.legSourceChainIds = G.preimage.legSourceChainIds
        ∧ F.preimage.deadline = G.preimage.deadline
        ∧ F.preimage.settlementLayerChainId = G.preimage.settlementLayerChainId)
      ∨ PreimageClashV35 enc F.preimage G.preimage

/-- **THE CLASH DISJUNCT IS NOT A TAUTOLOGY.**  For any two distinct preimages there is a hash
that does not clash on them, so `SameFlowIdSamePreimageOrClashV35` does not hold merely because
its second disjunct always does. -/
def Properties.PreimageClashNotForcedV35 : Prop :=
  ∀ (p q : PreimageV35), p ≠ q → ∃ enc : PreimageHashV35, ¬ PreimageClashV35 enc p q

end Contracts.FlowCanonicalAtV35
