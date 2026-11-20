import EraSpec.Contracts.SecondProofSystem.Specs.DiamondRefinement

/-!
# Properties: MigrationV35's diamond calls refine FlagAuthorityV35's

Statements about `EraSpec.Contracts.SecondProofSystem.Specs.DiamondRefinement`. Proofs are in
`EraSpec.Contracts.SecondProofSystem.Proofs.DiamondRefinement`.

* `DiamondStepRefines`: every successful MigrationV35 diamond call is a successful
  FlagAuthorityV35 call of the same entry point on the projected state, ending in the
  projection of its result, and it is a break-glass cut exactly when the image is. No premise.
* Three one-diamond facts of MigrationV35 follow from FlagAuthorityV35 through it, for either of
  a chain's diamonds: the flag is one-way (`DiamondFlagMonotoneStep`), only an admitted
  `setProofSystemStatus(Zisk, _)` writes the mask (`DiamondMaskWrittenOnlyBySetStatus`), and
  ZiSK-off on a flagged diamond is the Bridgehub owner's (`DiamondZiskOffOnFlaggedIsOwners`).
  Each assumes only that the call is not a break-glass cut.
-/

namespace Contracts.SecondProofSystem.DiamondRefinement

/-- **A MIGRATIONV35 DIAMOND CALL IS A FLAGAUTHORITYV35 CALL.** For every verifier
environment, Bridgehub owner, CTM, caller, diamond call and diamond: if the call succeeds, the
FlagAuthorityV35 call of the same entry point succeeds on the projected diamond and ends in the
projection of the result; and it is a break-glass cut exactly when the image is. -/
def Properties.DiamondStepRefines : Prop :=
  ∀ (E : MigrationV35.Env) (owner ctm c : MigrationV35.Address) (dc : MigrationV35.DCall)
    (d d' : MigrationV35.Diamond),
    MigrationV35.dstep E owner c dc d = some d' →
    FlagAuthorityV35.step (projEnv E) c (projCall ctm owner d dc) (proj ctm owner d)
        = some (proj ctm owner d')
      ∧ (projCall ctm owner d dc).isBreakGlass = isBreakGlassD dc

/-- **THE FLAG IS ONE-WAY ON EITHER DIAMOND**, derived from FlagAuthorityV35's
`FlagMonotoneStep`. A diamond call other than a break-glass cut never clears the flag. -/
def Properties.DiamondFlagMonotoneStep : Prop :=
  ∀ (E : MigrationV35.Env) (owner c : MigrationV35.Address) (dc : MigrationV35.DCall)
    (d d' : MigrationV35.Diamond),
    isBreakGlassD dc = false → MigrationV35.dstep E owner c dc d = some d' →
    d.secondProofSystemRequired = true → d'.secondProofSystemRequired = true

/-- **ONLY `setProofSystemStatus(Zisk, _)` WRITES THE MASK ON EITHER DIAMOND**, derived from
FlagAuthorityV35's `MaskWrittenOnlyBySetStatus`. -/
def Properties.DiamondMaskWrittenOnlyBySetStatus : Prop :=
  ∀ (E : MigrationV35.Env) (owner c : MigrationV35.Address) (dc : MigrationV35.DCall)
    (d d' : MigrationV35.Diamond),
    isBreakGlassD dc = false → MigrationV35.dstep E owner c dc d = some d' →
    d'.disabledProofSystems ≠ d.disabledProofSystems →
    ∃ en, dc = .setProofSystemStatus .zisk en

/-- **ZISK-OFF ON A FLAGGED DIAMOND IS THE BRIDGEHUB OWNER'S**, on either diamond, derived from
FlagAuthorityV35's `ZiskOffOnFlaggedIsOwners`: a diamond call other than a break-glass cut that
turns ZiSK off on a flagged diamond is `setProofSystemStatus(Zisk, false)` sent by the owner of
the Bridgehub that diamond reads. -/
def Properties.DiamondZiskOffOnFlaggedIsOwners : Prop :=
  ∀ (E : MigrationV35.Env) (owner c : MigrationV35.Address) (dc : MigrationV35.DCall)
    (d d' : MigrationV35.Diamond),
    isBreakGlassD dc = false → MigrationV35.dstep E owner c dc d = some d' →
    d.secondProofSystemRequired = true →
    d.disabledProofSystems &&& MigrationV35.ziskBit = 0 → MigrationV35.ziskOff d' →
    dc = .setProofSystemStatus .zisk false ∧ c = owner

end Contracts.SecondProofSystem.DiamondRefinement
