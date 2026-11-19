import EraSpec.Contracts.SecondProofSystem.Specs.FlagAuthorityV35
import EraSpec.Contracts.SecondProofSystem.Specs.MigrationV35

/-!
# Model bridge: MigrationV35's diamonds are FlagAuthorityV35 diamonds

Source: era-contracts `draft/v0.35.0` at commit `b17415d20`, as for both models it relates.
FlagAuthorityV35 is this folder's canonical one-diamond model (every `AdminFacet` entry point,
`St`, `step`). MigrationV35 models one chain with two diamonds (`Diamond`, `dstep`) and the
migration between them, and re-proved the one-diamond facts in its own model. This file maps a
MigrationV35 diamond and diamond call onto FlagAuthorityV35, so that those facts can be derived
from FlagAuthorityV35 instead (`Properties/DiamondRefinement.lean`).

**This file is definitions only.** The statements are in
`EraSpec.Contracts.SecondProofSystem.Properties.DiamondRefinement` and are proved in
`EraSpec.Contracts.SecondProofSystem.Proofs.DiamondRefinement`.

## The maps

* A diamond projects onto `St` by dropping `isPermanentRollup` (which FlagAuthorityV35 does not
  track) and adding the two fields MigrationV35 keeps outside the diamond: the CTM address the
  diamond's `chainTypeManager` holds and the owner of the Bridgehub `setProofSystemStatus`
  reads (`dstep`'s `owner` argument).
* The two `Env`s have the same field, `proofMode : Address → UInt8 → Option ℕ`.
* Each `DCall` maps to the FlagAuthorityV35 `Call` the same Solidity entry point is:
  `upgrade` is `upgradeChainFromVersion` with a genuine init (`_setVerifier`, or no verifier),
  `makePermanentRollup` is the `AdminFacet` entry point FlagAuthorityV35 lists as writing none of
  its fields, and a break-glass cut with init `f` is `upgradeChainFromVersion` with the arbitrary
  init that writes the projection of `f d` (the init FlagAuthorityV35 runs is chosen per call,
  so it may depend on the diamond the call starts from).
-/

namespace Contracts.SecondProofSystem.DiamondRefinement

/-- MigrationV35's `ProofSystem` as FlagAuthorityV35's. -/
def projPS : MigrationV35.ProofSystem → FlagAuthorityV35.ProofSystem
  | .boojum => .boojum
  | .airbender => .airbender
  | .zisk => .zisk

/-- The verifier answers, unchanged. -/
def projEnv (E : MigrationV35.Env) : FlagAuthorityV35.Env := ⟨E.proofMode⟩

/-- A MigrationV35 diamond as a FlagAuthorityV35 state, with the diamond's CTM `ctm` and the
Bridgehub owner `owner`. -/
def proj (ctm owner : MigrationV35.Address) (d : MigrationV35.Diamond) : FlagAuthorityV35.St where
  admin := d.admin
  pendingAdmin := d.pendingAdmin
  chainTypeManager := ctm
  bridgehubOwner := owner
  settlementLayer := d.settlementLayer
  verifier := d.verifier
  secondProofSystemRequired := d.secondProofSystemRequired
  disabledProofSystems := d.disabledProofSystems

/-- A diamond call as the FlagAuthorityV35 call of the same entry point, from diamond `d`. -/
def projCall (ctm owner : MigrationV35.Address) (d : MigrationV35.Diamond) :
    MigrationV35.DCall → FlagAuthorityV35.Call
  | .setPendingAdmin a => .setPendingAdmin a
  | .acceptAdmin => .acceptAdmin
  | .setProofSystemStatus p en => .setProofSystemStatus (projPS p) en
  | .permanentlyRequireSecondProofSystem => .permanentlyRequireSecondProofSystem
  | .makePermanentRollup => .adminOther .makePermanentRollup
  | .upgrade nv => .upgradeChainFromVersion (.genuine ⟨nv⟩)
  | .breakGlassCut f => .upgradeChainFromVersion (.arbitrary fun _ => (f d).map (proj ctm owner))

/-- The diamond call is a break-glass cut. -/
def isBreakGlassD : MigrationV35.DCall → Bool
  | .breakGlassCut _ => true
  | _ => false

end Contracts.SecondProofSystem.DiamondRefinement
