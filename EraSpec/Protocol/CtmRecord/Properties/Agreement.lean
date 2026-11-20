import EraSpec.Protocol.CtmRecord.Specs.Agreement
import EraSpec.Core.Headline

/-!
# Properties: the Bridgehub's CTM record agrees with the CTM the chain's diamond obeys

Statements about `EraSpec.Protocol.CtmRecord.Specs.Agreement` (`b17415d20`). Proofs are in
`EraSpec.Protocol.CtmRecord.Proofs.Agreement`. The asset-id function is uninterpreted. The only
conditions on it are logged ones: `NoRebind` asks that each registration's own asset id be
nonzero, `PairDiscipline` that the run's registration words have nonzero, non-colliding asset
ids on each layer, and the witnesses and countermodels that the two named words `10` and `11`
have nonzero, distinct ones.

* **Invariant.** Along every run in which each `setCTMAssetAddress` keeps its layer's two
  asset maps a partial bijection (`NoRebind`), on every layer every registered chain's record
  `chainTypeManager[c]` is its diamond's `s.chainTypeManager`
  (`CtmRecordAgreesWithDiamond`, from the inductive `CtmInv`: `CtmRecordInvInit`,
  `CtmRecordInvStep`, `CtmRecordInvReachable`). A chain's diamond on a settlement layer
  belongs to the CTM that layer registered under the asset id of the chain's L1 CTM
  (`CtmRecordSettlementDiamondFollowsL1Ctm`).
* **Corollaries.** On those runs the CTM whose version a burn or a mint checks, and the CTM
  whose migration pause gates it (for a burn: whenever the asset id it must carry is nonzero,
  which off L1 always holds), are the CTM the diamond admits as its chain type manager
  (`CtmRecordBurnGatesAreDiamondCtm`, `CtmRecordMintGatesAreDiamondCtm`), and the diamond's
  `onlyChainTypeManager` gate admits exactly the recorded CTM (`CtmRecordNamesAdmittedCtm`).
  In every state whose records all agree with their diamonds, a chain burned on L1 towards a
  layer that has a diamond on L1 goes to a layer whose L1 diamond is under the chain's own CTM
  (`CtmRecordBurnTargetsSameCtmLayer`, `CtmRecordBurnTargetsSameCtmLayerWitness`).
* **Witness.** A disciplined round trip L1 → settlement layer → L1 with two CTM families
  satisfies every premise of the invariant and of the gate corollaries
  (`CtmRecordDisciplinedRoundTripWitness`).
* **Countermodels.** One registration that gives a settlement-layer CTM a second asset id makes
  the round trip end with L1's record naming a different CTM than the returning diamond obeys
  (`CtmRecordUndisciplinedRoundTripDrifts`); a chain created on L1 under the recorded CTM can
  then be burned towards the returned chain, whose diamond is under the other CTM
  (`CtmRecordDriftAdmitsForeignLayer`). One registration that re-points an asset id leaves the
  record and the diamond in agreement but makes another CTM's pause gate the chain's burn
  (`CtmRecordStaleReverseEntryMisgatesPause`).
* **Repaired mint.** A mint that compared the existing diamond's CTM with the asset's CTM would
  keep the record and the diamond in agreement on every run, disciplined or not
  (`CtmRecordRepairedMintAgrees`), and would reject no mint of a disciplined run
  (`CtmRecordRepairAdmitsDisciplinedRuns`, `CtmRecordRepairedRoundTripWitness`). It does not
  fix the burn's pause gate (`CtmRecordRepairedMintKeepsStalePauseGate`).
* **Both conditions are the weakest per call.** A registration keeps the asset maps mutually
  inverse exactly when it is `NoRebind` (`CtmRecordNoRebindIffKeepsBijection`,
  `CtmRecordNoRebindIffKeepsBijectionWitness`). A mint keeps every record in agreement with its
  diamond exactly when it passes the repaired mint's check (`CtmRecordMintKeepsAgreementIff`,
  `CtmRecordMintKeepsAgreementIffWitness`).
* **Only a mint can break the agreement.** Along every run with no `bridgeMint`, disciplined or
  not, the record agrees with the diamond (`CtmRecordAgreesWithoutMints`,
  `CtmRecordAgreesWithoutMintsWitness`); at `b17415d20` and `70096e2ea` every `bridgeMint`
  reverts (`CHAIN_MIGRATIONS_ENABLED = false`).
* **The tracker's form of the premise.** If on each layer the registered
  `(additionalData, CTM)` pairs determine each other and their asset ids are nonzero and do
  not collide, every registration is `NoRebind` (`CtmRecordPairDisciplineGivesNoRebind`,
  `CtmRecordAgreesUnderPairDiscipline`, `CtmRecordPairDisciplineWitness`).
-/

namespace Protocol.CtmRecord

/-! ## The invariant -/

/-- Fresh storage satisfies `CtmInv`. -/
def Properties.CtmRecordInvInit : Prop := ∀ W : World, CtmInv W Sys.init

/-- A successful call that satisfies the discipline, from a state satisfying `CtmInv`, ends in a
state satisfying `CtmInv`. -/
def Properties.CtmRecordInvStep : Prop :=
  ∀ (W : World) (s : Sys) (op : Op) (s' : Sys),
    CtmInv W s → Disciplined W s op → Step W s op s' → CtmInv W s'

/-- Every state a disciplined run reaches from fresh storage satisfies `CtmInv`. -/
def Properties.CtmRecordInvReachable : Prop :=
  ∀ (W : World) (s : Sys), DReach W s → CtmInv W s

/-- **HEADLINE.** In every state a disciplined run reaches from fresh storage, on every layer
`h`, every chain `c` that layer's `zkChainMap` holds has `chainTypeManager[c]` equal to its
diamond's `s.chainTypeManager`.
A disciplined run is one in which every `setCTMAssetAddress(d, y)` call keeps that layer's two asset
maps a partial bijection (`NoRebind`: the asset id is nonzero, it is not already mapped to another
CTM, and the CTM is not already mapped to another asset id); every other call, mints included, is
unrestricted. No other premise. -/
@[headline] def Properties.CtmRecordAgreesWithDiamond : Prop :=
  ∀ (W : World) (s : Sys), DReach W s →
    ∀ h c D, s.diamond h c = some D → s.bhCtm h c = D

/-- In every state a disciplined run reaches, a chain's diamond on a layer other than L1 has
L1 holding a diamond for the same chain, whose CTM `X` has a nonzero asset id on L1, and that
layer maps that asset id to the diamond's CTM. -/
def Properties.CtmRecordSettlementDiamondFollowsL1Ctm : Prop :=
  ∀ (W : World) (s : Sys), DReach W s →
    ∀ h c D, h ≠ W.l1 → s.diamond h c = some D →
      ∃ X, s.diamond W.l1 c = some X ∧ s.ctmAsset W.l1 X ≠ 0 ∧
        s.assetCtm h (s.ctmAsset W.l1 X) = D

/-! ## Which CTM the migration checks consult -/

/-- In every state a disciplined run reaches, for every chain `c` with a diamond `D` on layer
`h`: the CTM whose `forwardedBridgeBurn` a burn of `c` calls is `D`; if the asset id that burn
must carry is nonzero, the CTM whose migration pause gates it is `D`; and off L1 that asset id
is nonzero. -/
def Properties.CtmRecordBurnGatesAreDiamondCtm : Prop :=
  ∀ (W : World) (s : Sys), DReach W s →
    ∀ h c D, s.diamond h c = some D →
      burnVersionCtm s h c = D ∧ (burnAsset s h c ≠ 0 → burnPauseCtm s h c = D) ∧
        (h ≠ W.l1 → burnAsset s h c ≠ 0)

/-- From every state a disciplined run reaches, a successful mint of `m` checks the version of
the same CTM whose pause gates it, and afterwards that CTM is both the record of `m.chain` on
`m.dst` and the CTM of its diamond there. -/
def Properties.CtmRecordMintGatesAreDiamondCtm : Prop :=
  ∀ (W : World) (s : Sys) (m : Msg) (s' : Sys), DReach W s → Step W s (.bridgeMint m) s' →
    mintVersionCtm s m = mintPauseCtm s m ∧
      s'.diamond m.dst m.chain = some (mintPauseCtm s m) ∧
      s'.bhCtm m.dst m.chain = mintPauseCtm s m

/-- In every state a disciplined run reaches, on every layer `h`, for every chain `c` that
layer's `zkChainMap` holds, a CTM `X` passes the diamond's `onlyChainTypeManager` gate exactly
when `X` is the Bridgehub's record `chainTypeManager[c]`.
A disciplined run is one in which every `setCTMAssetAddress(d, y)` call keeps that layer's two asset
maps a partial bijection (`NoRebind`: the asset id is nonzero, it is not already mapped to another
CTM, and the CTM is not already mapped to another asset id); every other call, mints included, is
unrestricted. No other premise. -/
@[headline] def Properties.CtmRecordNamesAdmittedCtm : Prop :=
  ∀ (W : World) (s : Sys), DReach W s → ∀ h c, s.diamond h c ≠ none →
    ∀ X, diamondAdmits s h c X ↔ X = s.bhCtm h c

/-- **THE SETTLEMENT LAYER'S CTM.** From every state in which every record agrees with its
diamond (`RecordAgrees`; by `CtmRecordAgreesWithDiamond`, every state a disciplined run
reaches), a successful `bridgeBurn` of chain `c` on L1 towards `dst` goes to a layer whose own
diamond on L1, if L1's `zkChainMap` holds one, is under the migrating diamond's CTM. The burn's
two CTM checks (`CAH:232-237`, `MIG:181-189`) compare against L1's record of `dst`. -/
def Properties.CtmRecordBurnTargetsSameCtmLayer : Prop :=
  ∀ (W : World) (s s' : Sys) (c dst : ChainId), RecordAgrees s →
    Step W s (.bridgeBurn W.l1 c dst) s' →
    ∀ D E, s.diamond W.l1 c = some D → s.diamond W.l1 dst = some E → E = D

/-! ## Witness -/

/-- **WITNESS (the premises above, except `CtmRecordBurnTargetsSameCtmLayer`'s, witnessed
next).** For every asset-id function `e` with `e 10`, `e 11` nonzero and distinct, on
`wWorld e`: a disciplined run from fresh storage creates chains `2`
and `3` under CTM `10` on L1, registers `10 ↦ 10` and `11 ↦ 11` on L1 and `10 ↦ 20`,
`11 ↦ 21` and again `10 ↦ 20` on layer `2`, sends chain `3` to layer `2` and burns it back.
In the state `s₁` it reaches, chain `3` is away from L1 with its L1 diamond still under `10`,
its layer-`2` diamond is under `20`, and the returning mint's pause and version CTM are both
`10`. That mint succeeds and `s₂`, the state after it, is reachable by a disciplined run. In
`s₂` chain `3` settles on L1 again, its record and diamond are `10` on L1 and `20` on layer
`2`, and on both layers the asset id a burn of chain `3` must carry is `e 10` and its pause
CTM is that layer's diamond CTM. -/
@[witness] def Properties.CtmRecordDisciplinedRoundTripWitness : Prop :=
  ∀ e : Word → AssetId, e 10 ≠ 0 → e 11 ≠ 0 → e 10 ≠ e 11 →
    ∃ s₁ s₂, Run (wWorld e) (Disciplined (wWorld e)) Sys.init (wSetup ++ wRegs ++ wOut e) s₁ ∧
      Step (wWorld e) s₁ (.bridgeMint (wReturnMsg e)) s₂ ∧ DReach (wWorld e) s₂ ∧
      s₁.diamond 1 3 = some 10 ∧ s₁.settlement 1 3 = 2 ∧ s₁.diamond 2 3 = some 20 ∧
      mintPauseCtm s₁ (wReturnMsg e) = 10 ∧ mintVersionCtm s₁ (wReturnMsg e) = 10 ∧
      s₂.diamond 1 3 = some 10 ∧ s₂.bhCtm 1 3 = 10 ∧ s₂.settlement 1 3 = 1 ∧
      s₂.diamond 2 3 = some 20 ∧ s₂.bhCtm 2 3 = 20 ∧
      burnAsset s₂ 1 3 = e 10 ∧ burnPauseCtm s₂ 1 3 = 10 ∧
      burnAsset s₂ 2 3 = e 10 ∧ burnPauseCtm s₂ 2 3 = 20

/-- **WITNESS (`CtmRecordBurnTargetsSameCtmLayer`).** For every asset-id function `e` with
`e 10`, `e 11` nonzero and distinct, on `wWorld e`: the state `s` after the disciplined
`wSetup ++ wRegs` satisfies `RecordAgrees`; L1 holds diamonds under CTM `10` for chain `3` and
for the settlement layer `2`, and the burn of chain `3` on L1 towards `2` succeeds. -/
def Properties.CtmRecordBurnTargetsSameCtmLayerWitness : Prop :=
  ∀ e : Word → AssetId, e 10 ≠ 0 → e 11 ≠ 0 → e 10 ≠ e 11 →
    ∃ s s', Run (wWorld e) (Disciplined (wWorld e)) Sys.init (wSetup ++ wRegs) s ∧
      RecordAgrees s ∧ Step (wWorld e) s (.bridgeBurn 1 3 2) s' ∧
      s.diamond 1 3 = some 10 ∧ s.diamond 1 2 = some 10

/-! ## Countermodels -/

/-- **COUNTERMODEL: ONE SETTLEMENT-LAYER CTM UNDER TWO ASSET IDS.** For every asset-id
function `e` with `e 10`, `e 11` nonzero and distinct, on `wWorld e`: after the disciplined
`wSetup`, the one registration `cmRebind` (`11 ↦ 20` on layer `2`, while `20` already has asset
id `e 10` there) violates `NoRebind`. The disciplined `wOut e` then sends chain `3` to layer
`2` and burns it back; in the state `s₂` it reaches, chain `3`'s diamond and record on layer
`2` are `20`, and the messages sent include `cmReturnMsg e = ⟨3, e 11, 2, 1⟩`
(`ctmAssetIdFromAddress[20] = e 11`). The mint of that message is gated by CTM `11`'s pause
while checking CTM `10`'s version, the repaired mint's check rejects it, and it succeeds:
afterwards L1's record for chain `3` is `11` while its L1 diamond's CTM is `10`. -/
@[countermodel] def Properties.CtmRecordUndisciplinedRoundTripDrifts : Prop :=
  ∀ e : Word → AssetId, e 10 ≠ 0 → e 11 ≠ 0 → e 10 ≠ e 11 →
    ∃ s₀ s₁ s₂ s₃, Run (wWorld e) (Disciplined (wWorld e)) Sys.init wSetup s₀ ∧
      ¬ Disciplined (wWorld e) s₀ cmRebind ∧ Step (wWorld e) s₀ cmRebind s₁ ∧
      Run (wWorld e) (Disciplined (wWorld e)) s₁ (wOut e) s₂ ∧
      s₂.diamond 2 3 = some 20 ∧ s₂.bhCtm 2 3 = 20 ∧ cmReturnMsg e ∈ s₂.sent ∧
      Step (wWorld e) s₂ (.bridgeMint (cmReturnMsg e)) s₃ ∧
      mintPauseCtm s₂ (cmReturnMsg e) = 11 ∧ mintVersionCtm s₂ (cmReturnMsg e) = 10 ∧
      ¬ RepairGuard s₂ (.bridgeMint (cmReturnMsg e)) ∧
      s₃.diamond 1 3 = some 10 ∧ s₃.bhCtm 1 3 = 11

/-- **COUNTERMODEL: A DRIFTED RECORD ADMITS A SETTLEMENT LAYER UNDER ANOTHER CTM.** For every
asset-id function `e` with `e 10`, `e 11` nonzero and distinct, on `wWorld e`: after the
disciplined `wSetup` and the one registration `cmRebind`, which violates `NoRebind`, the
disciplined calls `wOut e`, the mint of `cmReturnMsg e` and `createNewChain(4, 11)` reach a
state `s₄` that fails `RecordAgrees`: L1 records chain `3` under `11`, while its diamond there
admits `10` and not `11`. Chain `4`'s L1 diamond admits `11`, and the burn of chain `4` on L1
towards `3` succeeds, so `CtmRecordBurnTargetsSameCtmLayer`'s conclusion fails at `s₄`. -/
@[countermodel] def Properties.CtmRecordDriftAdmitsForeignLayer : Prop :=
  ∀ e : Word → AssetId, e 10 ≠ 0 → e 11 ≠ 0 → e 10 ≠ e 11 →
    ∃ s₀ s₁ s₄ s₅, Run (wWorld e) (Disciplined (wWorld e)) Sys.init wSetup s₀ ∧
      ¬ Disciplined (wWorld e) s₀ cmRebind ∧ Step (wWorld e) s₀ cmRebind s₁ ∧
      Run (wWorld e) (Disciplined (wWorld e)) s₁
        (wOut e ++ [.bridgeMint (cmReturnMsg e), .createNewChain 4 11]) s₄ ∧
      ¬ RecordAgrees s₄ ∧ s₄.bhCtm 1 3 = 11 ∧
      diamondAdmits s₄ 1 3 10 ∧ ¬ diamondAdmits s₄ 1 3 11 ∧ diamondAdmits s₄ 1 4 11 ∧
      Step (wWorld e) s₄ (.bridgeBurn 1 4 3) s₅

/-- **COUNTERMODEL: A STALE REVERSE ENTRY.** For every asset-id function `e` with `e 10 ≠ 0`,
on `wWorld e`: a disciplined run `staleSetup e` brings chain `3` to layer `2`; then the one
registration `staleRebind` (`10 ↦ 21` on layer `2`, while `e 10` already maps to `20`) violates
`NoRebind`. In the state after it, chain `3`'s record agrees with its diamond on both layers
(`10` on L1, `20` on layer `2`) and a burn of chain `3` on layer `2` calls CTM `20`, but it must
carry `e 10`, whose CTM is now `21`, so `21`'s pause gates it. That burn towards L1 succeeds,
and so does the L1 mint of the message `⟨3, e 10, 2, 1⟩` after it, after which L1's record and
diamond for chain `3` are both `10`. -/
def Properties.CtmRecordStaleReverseEntryMisgatesPause : Prop :=
  ∀ e : Word → AssetId, e 10 ≠ 0 →
    ∃ s₀ s₁, Run (wWorld e) (Disciplined (wWorld e)) Sys.init (staleSetup e) s₀ ∧
      ¬ Disciplined (wWorld e) s₀ staleRebind ∧ Step (wWorld e) s₀ staleRebind s₁ ∧
      s₁.diamond 2 3 = some 20 ∧ s₁.bhCtm 2 3 = 20 ∧
      s₁.diamond 1 3 = some 10 ∧ s₁.bhCtm 1 3 = 10 ∧
      burnVersionCtm s₁ 2 3 = 20 ∧ burnAsset s₁ 2 3 = e 10 ∧ burnPauseCtm s₁ 2 3 = 21 ∧
      ∃ s₂ s₃, Step (wWorld e) s₁ (.bridgeBurn 2 3 1) s₂ ∧
        Step (wWorld e) s₂ (.bridgeMint ⟨3, e 10, 2, 1⟩) s₃ ∧
        s₃.diamond 1 3 = some 10 ∧ s₃.bhCtm 1 3 = 10

/-! ## The repaired mint -/

/-- **REPAIRED FORM.** Along every run from fresh storage whose mints all pass `RepairGuard`,
with no registration discipline, every registered chain's record on every layer is its
diamond's CTM. -/
def Properties.CtmRecordRepairedMintAgrees : Prop :=
  ∀ (W : World) (ops : List Op) (s : Sys), Run W RepairGuard Sys.init ops s →
    ∀ h c D, s.diamond h c = some D → s.bhCtm h c = D

/-- Every disciplined run from fresh storage is a run of the repaired mint: the extra check
holds at each of its mints. -/
def Properties.CtmRecordRepairAdmitsDisciplinedRuns : Prop :=
  ∀ (W : World) (ops : List Op) (s : Sys), Run W (Disciplined W) Sys.init ops s →
    Run W RepairGuard Sys.init ops s

/-- **WITNESS (`CtmRecordRepairedMintAgrees`).** For every asset-id function `e` with `e 10`,
`e 11` nonzero and distinct, the calls of `CtmRecordDisciplinedRoundTripWitness`'s round trip,
whose last call mints chain `3` back on L1 (an L1 mint requires the chain's diamond there),
form a run of the repaired mint, ending with chain `3`'s record and diamond `10` on L1 and
diamond `20` on layer `2`. -/
def Properties.CtmRecordRepairedRoundTripWitness : Prop :=
  ∀ e : Word → AssetId, e 10 ≠ 0 → e 11 ≠ 0 → e 10 ≠ e 11 →
    ∃ s, Run (wWorld e) RepairGuard Sys.init
        (wSetup ++ wRegs ++ wOut e ++ [.bridgeMint (wReturnMsg e)]) s ∧
      s.diamond 1 3 = some 10 ∧ s.bhCtm 1 3 = 10 ∧ s.diamond 2 3 = some 20

/-- **COUNTERMODEL (the repaired mint alone).** For every asset-id function `e` with
`e 10 ≠ 0`, on `wWorld e`: the calls `staleSetup e ++ [staleRebind]` form a run of the repaired
mint from fresh storage, ending with chain `3`'s record and diamond `20` on layer `2` and the
pause CTM of a burn of chain `3` there `21`. -/
def Properties.CtmRecordRepairedMintKeepsStalePauseGate : Prop :=
  ∀ e : Word → AssetId, e 10 ≠ 0 →
    ∃ s, Run (wWorld e) RepairGuard Sys.init (staleSetup e ++ [staleRebind]) s ∧
      s.diamond 2 3 = some 20 ∧ s.bhCtm 2 3 = 20 ∧ burnPauseCtm s 2 3 = 21

/-- **WEAKEST PER-MINT CONDITION.** From a state satisfying `RecordAgrees`, a successful
`bridgeMint` of `m` ends in a state satisfying `RecordAgrees` exactly when it passes
`RepairGuard`: a diamond the destination already holds for `m.chain` is under the CTM
`ctmAssetIdToAddress[m.asset]`. -/
def Properties.CtmRecordMintKeepsAgreementIff : Prop :=
  ∀ (W : World) (s s' : Sys) (m : Msg), RecordAgrees s → Step W s (.bridgeMint m) s' →
    (RepairGuard s (.bridgeMint m) ↔ RecordAgrees s')

/-- **WITNESS (`CtmRecordMintKeepsAgreementIff`, both sides, with an existing diamond).** For
every asset-id function `e` with `e 10`, `e 11` nonzero and distinct, on `wWorld e`, L1 holds
chain `3`'s diamond under `10` before each of two return mints. After the disciplined round trip
the mint of `wReturnMsg e` starts and ends in states satisfying `RecordAgrees` and passes
`RepairGuard`. After `wSetup`, `cmRebind` and `wOut e`, a run of the repaired mint, the mint of
`cmReturnMsg e` starts in a state satisfying `RecordAgrees`, fails `RepairGuard`, succeeds, and
ends in a state that does not satisfy it. -/
def Properties.CtmRecordMintKeepsAgreementIffWitness : Prop :=
  ∀ e : Word → AssetId, e 10 ≠ 0 → e 11 ≠ 0 → e 10 ≠ e 11 →
    (∃ s₁ s₂, Run (wWorld e) (Disciplined (wWorld e)) Sys.init (wSetup ++ wRegs ++ wOut e) s₁ ∧
      RecordAgrees s₁ ∧ s₁.diamond 1 3 = some 10 ∧
      Step (wWorld e) s₁ (.bridgeMint (wReturnMsg e)) s₂ ∧
      RepairGuard s₁ (.bridgeMint (wReturnMsg e)) ∧ RecordAgrees s₂) ∧
    (∃ s₂ s₃, Run (wWorld e) RepairGuard Sys.init (wSetup ++ cmRebind :: wOut e) s₂ ∧
      RecordAgrees s₂ ∧ s₂.diamond 1 3 = some 10 ∧
      Step (wWorld e) s₂ (.bridgeMint (cmReturnMsg e)) s₃ ∧
      ¬ RepairGuard s₂ (.bridgeMint (cmReturnMsg e)) ∧ ¬ RecordAgrees s₃)

/-! ## The discipline is exactly what keeps the asset maps a partial bijection -/

/-- **WEAKEST PER-CALL CONDITION.** From a state satisfying `AssetBij`, a successful
`setCTMAssetAddress(d, y)` on layer `h` ends in a state satisfying `AssetBij` exactly when it
satisfies `NoRebind`.
`AssetBij`: on every layer the two asset maps are mutually inverse on their nonzero entries.
`NoRebind`: the call's asset id is nonzero, it is not already mapped to another CTM, and the CTM is
not already mapped to another asset id. -/
@[headline] def Properties.CtmRecordNoRebindIffKeepsBijection : Prop :=
  ∀ (W : World) (s s' : Sys) (h : ChainId) (d : Word) (y : Address),
    AssetBij s → Step W s (.setCTMAssetAddress h d y) s' → (NoRebind W s h d y ↔ AssetBij s')

/-- **WITNESS (`CtmRecordNoRebindIffKeepsBijection`, both sides).** For every asset-id function
`e` with `e 10`, `e 11` nonzero and distinct, on `wWorld e`: the state `s₀` after the
disciplined `wSetup` satisfies `AssetBij`. From `s₀`, the registration `11 ↦ 21` on layer `2`
succeeds, satisfies `NoRebind` and ends in a state satisfying `AssetBij`; `cmRebind`
(`11 ↦ 20`) succeeds, violates `NoRebind` and ends in a state that does not. -/
@[witness] def Properties.CtmRecordNoRebindIffKeepsBijectionWitness : Prop :=
  ∀ e : Word → AssetId, e 10 ≠ 0 → e 11 ≠ 0 → e 10 ≠ e 11 →
    ∃ s₀ s₁ s₂, Run (wWorld e) (Disciplined (wWorld e)) Sys.init wSetup s₀ ∧ AssetBij s₀ ∧
      Step (wWorld e) s₀ (.setCTMAssetAddress 2 11 21) s₁ ∧ NoRebind (wWorld e) s₀ 2 11 21 ∧
      AssetBij s₁ ∧
      Step (wWorld e) s₀ (.setCTMAssetAddress 2 11 20) s₂ ∧ ¬ NoRebind (wWorld e) s₀ 2 11 20 ∧
      ¬ AssetBij s₂

/-! ## Runs without a mint -/

/-- Along every run from fresh storage that contains no `bridgeMint` call, with no
registration discipline, every registered chain's record on every layer is its diamond's CTM.
At `b17415d20`, `CHAIN_MIGRATIONS_ENABLED = false` (`CFG:320`) makes every `bridgeMint` revert
(`CAH:365` with `:151-156`); at `70096e2ea` the constant is `false` too
(`common/Config.sol:306`). -/
@[headline] def Properties.CtmRecordAgreesWithoutMints : Prop :=
  ∀ (W : World) (ops : List Op) (s : Sys), Run W AnyCall Sys.init ops s →
    (∀ m, Op.bridgeMint m ∉ ops) → ∀ h c D, s.diamond h c = some D → s.bhCtm h c = D

/-- **WITNESS (`CtmRecordAgreesWithoutMints`).** For every asset-id function `e` with `e 10`,
`e 11` nonzero and distinct, on `wWorld e`: `wSetup`, then `cmRebind`, then the burn of chain
`3` from L1 towards layer `2` is a run from fresh storage with no mint. In its final state
layer `2`'s maps are not mutually inverse (`e 10 ↦ 20` but `20 ↦ e 11`), the chain is away
from L1, and its L1 record and diamond are both `10`. -/
@[witness] def Properties.CtmRecordAgreesWithoutMintsWitness : Prop :=
  ∀ e : Word → AssetId, e 10 ≠ 0 → e 11 ≠ 0 → e 10 ≠ e 11 →
    ∃ s, Run (wWorld e) AnyCall Sys.init (wSetup ++ [cmRebind, .bridgeBurn 1 3 2]) s ∧
      (∀ m, Op.bridgeMint m ∉ wSetup ++ [cmRebind, .bridgeBurn 1 3 2]) ∧
      s.assetCtm 2 (e 10) = 20 ∧ s.ctmAsset 2 20 = e 11 ∧ s.settlement 1 3 = 2 ∧
      s.diamond 1 3 = some 10 ∧ s.bhCtm 1 3 = 10

/-! ## The tracker-level discipline -/

/-- Every run from fresh storage whose registrations satisfy `PairDiscipline` is disciplined:
each of its registrations is `NoRebind` in the state it runs in. -/
def Properties.CtmRecordPairDisciplineGivesNoRebind : Prop :=
  ∀ (W : World) (ops : List Op) (s : Sys), Run W AnyCall Sys.init ops s →
    PairDiscipline W ops → Run W (Disciplined W) Sys.init ops s

/-- Along every run from fresh storage whose registrations satisfy `PairDiscipline`, every
registered chain's record on every layer is its diamond's CTM.
`PairDiscipline`: on each layer, across the run's registrations, the additional data and the CTM
determine each other, and the asset ids of the registered words are nonzero and do not collide. No
other premise; mints are allowed. -/
@[headline] def Properties.CtmRecordAgreesUnderPairDiscipline : Prop :=
  ∀ (W : World) (ops : List Op) (s : Sys), Run W AnyCall Sys.init ops s →
    PairDiscipline W ops → ∀ h c D, s.diamond h c = some D → s.bhCtm h c = D

/-- **WITNESS (`PairDiscipline`).** For every asset-id function `e` with `e 10`, `e 11` nonzero
and distinct, on `wWorld e`: the calls of the disciplined round trip form a run from fresh
storage and satisfy `PairDiscipline` (layer `2` registers `10 ↦ 20`, `11 ↦ 21`, and `10 ↦ 20`
again), while the calls of the drifting run, whose layer `2` registers `20` under both `10`
and `11`, do not. -/
@[witness] def Properties.CtmRecordPairDisciplineWitness : Prop :=
  ∀ e : Word → AssetId, e 10 ≠ 0 → e 11 ≠ 0 → e 10 ≠ e 11 →
    (∃ s, Run (wWorld e) AnyCall Sys.init
        (wSetup ++ wRegs ++ wOut e ++ [.bridgeMint (wReturnMsg e)]) s) ∧
      PairDiscipline (wWorld e) (wSetup ++ wRegs ++ wOut e ++ [.bridgeMint (wReturnMsg e)]) ∧
      ¬ PairDiscipline (wWorld e) (wSetup ++ cmRebind :: wOut e ++ [.bridgeMint (cmReturnMsg e)])

end Protocol.CtmRecord
