import EraSpec.Contracts.SecondProofSystem.Specs.MigrationV35

/-!
# Properties: the second-proof-system requirement across a settlement-layer migration

Statements about `EraSpec.Contracts.SecondProofSystem.Specs.MigrationV35` (era-contracts
`draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`). Proofs are in
`EraSpec.Contracts.SecondProofSystem.Proofs.MigrationV35`.

`protocol-docs/interop-gating.md:26-27` says the requirement "makes every batch of an enabled
chain carry both an Airbender and a ZiSK proof from then on, unless governance turns ZiSK off in
an emergency", and `:35-42` that it is one-way and that, once set, ZiSK-off is governance's and
upgrades keep the second proof system. The flag is storage of one diamond. A chain has one
diamond per settlement layer.

* **What the migration carries.** The commitment reads `isPermanentRollup` and no other
  projected field (`CommitmentReadsOnlyThePermanentRollupFlag`); the mint writes neither the
  flag nor the mask, and a new diamond starts without them (`MintLeavesTheRequirementAlone`).
  `isPermanentRollup` is carried and guarded (`PermanentRollupCarried`), and is kept along every
  run, migrations included (`PermanentRollupKeptAcrossMigration`).
* **At `d9f6789` the requirement is permanent, because nothing migrates.** With
  `CHAIN_MIGRATIONS_ENABLED = false` every burn and mint reverts
  (`MigrationBanRefusesEveryMigration`), so a chain settling on L1 keeps settling on its L1
  diamond, the flag stays set, the verifier stays multi-proof, and ZiSK-off stays with the
  Bridgehub owner (`RequirementPermanentWhileMigrationsDisabled`,
  `ZiskStaysOnWithoutTheBridgehubOwner`; `RequirementPermanentWitness`).
* **The ban is the only thing that protects it.** With migrations enabled, the same chain
  arrives on a new gateway diamond that does not have the flag: its admin alone turns ZiSK off
  there and a single-proof verifier passes the upgrade check, while L1 still reports the
  requirement and interop stays enabled (`RequirementDroppedByMigration`). The same run is
  refused under the ban (`MigrationBanIsLoadBearing`).
* **`enableInterop` reads the L1 diamond** (`EnableInteropReadsTheL1Diamond`), whichever diamond
  accepts the chain's batches: it passes for a chain whose settlement diamond has dropped the
  requirement (`EnableInteropAcceptsAStaleL1Flag`), and it refuses a gateway-settled chain
  that set the requirement where it settles (`AwayDiamondCannotRequire`,
  `GatewaySettledChainCannotEnableInterop`, `GatewayRequirementDoesNotCount`).
* **A hypothetical repair.** With the flag added to the commitment and guarded like
  `isPermanentRollup`, the flag is kept across migration (`RepairedCommitmentKeepsRequirement`,
  `RepairedCarriesRequirementWitness`). The mask is still not carried
  (`RepairedArrivalCanHaveZiskOff`).

No statement here has a hash premise.
-/

namespace Contracts.SecondProofSystem.MigrationV35

/-! ## What the migration carries -/

/-- **THE COMMITMENT READS `isPermanentRollup` AND NOTHING ELSE OF THE PROJECTION**
(`common/Config.sol:234-261`, `Migrator.sol:339-375`). Two diamonds with the same
`isPermanentRollup` produce the same commitment from the same unprojected storage, whatever
their flag, mask, verifier, admin and settlement layer. -/
def Properties.CommitmentReadsOnlyThePermanentRollupFlag : Prop :=
  ∀ (payload : Commitment) (d d' : Diamond), d'.isPermanentRollup = d.isPermanentRollup →
    prepareChainCommitment payload d' = prepareChainCommitment payload d

/-- **THE MINT LEAVES THE REQUIREMENT ALONE** (`Migrator.sol:213-305`,
`DiamondInit.sol:52-150`). A successful `Migrator.forwardedBridgeMint` changes neither the
flag, the mask, the verifier nor the admin of the diamond it runs on; a newly deployed diamond
has the flag unset, ZiSK enabled and the admin the burn named; and in the source
(`repaired = false`) the mint's result does not depend on the flag of the diamond that was
burned. -/
def Properties.MintLeavesTheRequirementAlone : Prop :=
  (∀ (c : Commitment) (d d' : Diamond), forwardedBridgeMint c d = some d' →
    d'.secondProofSystemRequired = d.secondProofSystemRequired ∧
    d'.disabledProofSystems = d.disabledProofSystems ∧
    d'.verifier = d.verifier ∧ d'.admin = d.admin) ∧
  (∀ (cfg : Cfg) (a : Address),
    (freshDiamond cfg a).secondProofSystemRequired = false ∧
    (freshDiamond cfg a).disabledProofSystems = 0 ∧ (freshDiamond cfg a).admin = a) ∧
  ∀ (cfg : Cfg) (w : RepairedCommitment) (b : Bool) (d : Diamond), cfg.repaired = false →
    mintWith cfg { w with secondProofSystemRequired := b } d = mintWith cfg w d

/-- **(a) `isPermanentRollup` IS CARRIED** (`Migrator.sol:346`, `:234-241`). The commitment
holds the burned diamond's `isPermanentRollup`; a successful mint leaves the destination with
the commitment's; and a mint that would clear it on a diamond that has it reverts. -/
def Properties.PermanentRollupCarried : Prop :=
  (∀ (payload c : Commitment) (d : Diamond), prepareChainCommitment payload d = some c →
    c.isPermanentRollup = d.isPermanentRollup) ∧
  (∀ (c : Commitment) (d d' : Diamond), forwardedBridgeMint c d = some d' →
    d'.isPermanentRollup = c.isPermanentRollup) ∧
  ∀ (c : Commitment) (d : Diamond), d.isPermanentRollup = true → c.isPermanentRollup = false →
    forwardedBridgeMint c d = none

/-- **`isPermanentRollup` IS KEPT ACROSS MIGRATION.** In every system of the model, migrations
enabled or not, repaired or not: along a run with no break-glass cut, `PermanentRollupKept` is
preserved. So once every diamond accepting the chain's batches is a permanent rollup, every
diamond that later accepts them is. -/
def Properties.PermanentRollupKeptAcrossMigration : Prop :=
  ∀ (cfg : Cfg) (E : Env) (s s' : Sys) (tr : List (Address × Call)),
    Run cfg E Tame s tr s' → PermanentRollupKept s → PermanentRollupKept s'

/-! ## At `d9f6789`: migrations disabled -/

/-- **THE BAN REFUSES EVERY MIGRATION** (`ChainAssetHandlerBase.sol:151-156, 201, 365`,
`common/Config.sol:320`). With `migrationsEnabled = false`, each of the four burn and mint
calls reverts, for every caller and in every state. -/
def Properties.MigrationBanRefusesEveryMigration : Prop :=
  ∀ (cfg : Cfg) (E : Env) (c : Address) (call : Call) (s : Sys),
    cfg.migrationsEnabled = false → call.isMigration = true → step cfg E c call s = none

/-- **(b) THE REQUIREMENT IS PERMANENT WHILE MIGRATIONS ARE DISABLED**
(`protocol-docs/interop-gating.md:35-42` at `d9f6789`). With `migrationsEnabled = false`, take
a chain that settles on L1 and whose L1 diamond has the flag. Along every run with no
break-glass cut, by any callers:

* the chain still settles on L1, on the same diamond;
* the flag is still set;
* if the verifier reported multi-proof mode with nothing disabled, it still does;
* in the state reached, a call turning a proof system off on the L1 diamond succeeds only for
  the owner of L1's Bridgehub. -/
def Properties.RequirementPermanentWhileMigrationsDisabled : Prop :=
  ∀ (cfg : Cfg) (E : Env) (s s' : Sys) (tr : List (Address × Call)),
    cfg.migrationsEnabled = false → Run cfg E Tame s tr s' →
    SettlesOnL1 s → s.l1.secondProofSystemRequired = true →
      SettlesOnL1 s' ∧ s'.l1.secondProofSystemRequired = true ∧
      (E.proofMode s.l1.verifier 0 = some MULTI_PROOF_TYPE →
        E.proofMode s'.l1.verifier 0 = some MULTI_PROOF_TYPE) ∧
      ∀ (c : Address) (p : ProofSystem) (s'' : Sys),
        step cfg E c (.diamond .l1 (.setProofSystemStatus p false)) s' = some s'' →
        c = s'.l1BridgehubOwner

/-- **ZiSK STAYS ON WITHOUT THE BRIDGEHUB OWNER.** With `migrationsEnabled = false`, a chain
settling on L1 with the flag set and ZiSK enabled keeps ZiSK enabled along every run with no
break-glass cut in which the owner of a layer's Bridgehub turns no proof system off there
(`AdminSide`). The chain admin, and every other caller, is unrestricted. -/
def Properties.ZiskStaysOnWithoutTheBridgehubOwner : Prop :=
  ∀ (cfg : Cfg) (E : Env) (s s' : Sys) (tr : List (Address × Call)),
    cfg.migrationsEnabled = false → Run cfg E AdminSide s tr s' →
    SettlesOnL1 s → s.l1.secondProofSystemRequired = true → ¬ ziskOff s.l1 →
      ¬ ziskOff s'.l1

/-- **THE PREMISES OF (b) ARE SATISFIABLE, AND THE OWNER'S SWITCH WORKS.** In the source
(`wSource`): the admin makes the chain a permanent rollup and requires the second proof system,
and the Bridgehub owner enables interop with the requirement (`w3`). `w3` settles on L1 with
the flag set and satisfies `RequirementKept` and `PermanentRollupKept`. From `w3` the run
`wOnL1` succeeds (an upgrade to another multi-proof verifier, the owner's emergency ZiSK-off,
the admin turning ZiSK back on), and in `w3` the admin's ZiSK-off, an upgrade to the
single-proof verifier `20` and the admin's migration burn are refused. -/
def Properties.RequirementPermanentWitness : Prop :=
  Run wSource wEnv AdminSide w0 (wRequire ++ wEnable) w3 ∧
  SettlesOnL1 w3 ∧ w3.l1.secondProofSystemRequired = true ∧ ¬ ziskOff w3.l1 ∧
  wEnv.proofMode w3.l1.verifier 0 = some MULTI_PROOF_TYPE ∧
  RequirementKept w3 ∧ PermanentRollupKept w3 ∧
  (∃ s, Run wSource wEnv Tame w3 wOnL1 s ∧ s.l1.verifier = 12 ∧ ¬ ziskOff s.l1 ∧
    s.l1.secondProofSystemRequired = true) ∧
  step wSource wEnv 1 (.diamond .l1 (.setProofSystemStatus .zisk false)) w3 = none ∧
  step wSource wEnv 5 (.diamond .l1 (.upgrade (some 20))) w3 = none ∧
  step wSource wEnv 1 (.bridgeBurnToGateway 77 1 wPayload) w3 = none

/-! ## With migrations enabled: the requirement is lost -/

/-- **COUNTERMODEL: THE REQUIREMENT IS DROPPED BY A MIGRATION.** `wEnabled` is the source with
`migrationsEnabled = true` and nothing else changed. From `w0`, with no break-glass cut and no
ZiSK-off by either Bridgehub's owner (`AdminSide`):

* `wRequire ++ wEnable` reaches `w3`, where the requirement and the permanent-rollup flag are
  both kept;
* `wLeave` (the admin's burn, then the mint on the gateway) reaches `w5`, where the
  permanent-rollup flag is kept and the requirement is **not**;
* `wDrop` reaches `w7`: the chain admin, who is not the gateway Bridgehub's owner, turns ZiSK
  off on the gateway diamond, and an upgrade installs the single-proof verifier `20` there.

In `w7` the L1 diamond still reports the requirement, interop is still enabled, and the L1
diamond does not accept batches. The diamond that does is a permanent rollup, does not have the
flag, has ZiSK off, and its proof mode is single-proof PLONK. The same two calls on the L1
diamond are refused. -/
def Properties.RequirementDroppedByMigration : Prop :=
  Run wEnabled wEnv AdminSide w0 (wRequire ++ wEnable) w3 ∧
  RequirementKept w3 ∧ PermanentRollupKept w3 ∧
  Run wEnabled wEnv AdminSide w3 wLeave w5 ∧
  ¬ RequirementKept w5 ∧ PermanentRollupKept w5 ∧
  Run wEnabled wEnv AdminSide w5 wDrop w7 ∧
  w7.l1.secondProofSystemRequired = true ∧ w7.interopEnabled = true ∧ ¬ w7.l1.accepts ∧
  w7.gw = some wDropped ∧ wDropped.accepts ∧ wDropped.isPermanentRollup = true ∧
  wDropped.secondProofSystemRequired = false ∧ ziskOff wDropped ∧
  wDropped.admin ≠ w7.gwBridgehubOwner ∧
  wEnv.proofMode wDropped.verifier wDropped.disabledProofSystems = some PLONK_TYPE ∧
  step wEnabled wEnv 1 (.diamond .l1 (.setProofSystemStatus .zisk false)) w7 = none ∧
  step wEnabled wEnv 5 (.diamond .l1 (.upgrade (some 20))) w7 = none

/-- **THE MIGRATION BAN IS LOAD-BEARING.** In the source (`wSource`, which differs from
`wEnabled` only in `migrationsEnabled = false`) the set-up `wRequire ++ wEnable` reaches the
same `w3`, the admin's burn is refused there, and the run of `RequirementDroppedByMigration`
does not exist, under any restriction on callers. With `wEnabled` the same burn succeeds. -/
def Properties.MigrationBanIsLoadBearing : Prop :=
  Run wSource wEnv AdminSide w0 (wRequire ++ wEnable) w3 ∧
  step wSource wEnv 1 (.bridgeBurnToGateway 77 1 wPayload) w3 = none ∧
  (∀ (ok : Sys → Address → Call → Prop) (s : Sys),
    ¬ Run wSource wEnv ok w0 (wRequire ++ wEnable ++ wLeave ++ wDrop) s) ∧
  (step wEnabled wEnv 1 (.bridgeBurnToGateway 77 1 wPayload) w3).isSome = true

/-! ## `enableInterop` -/

/-- **(c) `enableInterop` READS THE L1 DIAMOND** (`L1MessageRoot.sol:72-89`, `:74`). Whether
`enableInterop` succeeds does not depend on the chain's gateway diamond, on what is in flight or
on the gateway Bridgehub's owner; and when it succeeds with `requireSecondProofSystem`, the
caller owns L1's Bridgehub, the **L1** diamond has the flag and reports multi-proof mode under
its own mask, and the only change is `interopEnabled`. -/
def Properties.EnableInteropReadsTheL1Diamond : Prop :=
  (∀ (cfg : Cfg) (E : Env) (c : Address) (req : Bool) (s : Sys) (g : Option Diamond)
      (fl : List InFlight) (o : Address),
    (step cfg E c (.enableInterop req)
        { s with gw := g, inFlight := fl, gwBridgehubOwner := o }).isSome =
      (step cfg E c (.enableInterop req) s).isSome) ∧
  ∀ (cfg : Cfg) (E : Env) (c : Address) (s s' : Sys),
    step cfg E c (.enableInterop true) s = some s' →
      c = s.l1BridgehubOwner ∧ s.l1.secondProofSystemRequired = true ∧
      E.proofMode s.l1.verifier s.l1.disabledProofSystems = some MULTI_PROOF_TYPE ∧
      s' = { s with interopEnabled := true }

/-- **COUNTERMODEL: `enableInterop` ACCEPTS A STALE L1 FLAG.** With migrations enabled, run
`RequirementDroppedByMigration` without the enabling: `wRequire ++ wLeave ++ wDrop` from `w0`
reaches a state where interop is not enabled and the diamond accepting the chain's batches is
`wDropped` (no flag, ZiSK off, single-proof verifier). There the Bridgehub owner's
`enableInterop(chainId, true)` succeeds. -/
def Properties.EnableInteropAcceptsAStaleL1Flag : Prop :=
  ∃ s s' : Sys, Run wEnabled wEnv AdminSide w0 (wRequire ++ wLeave ++ wDrop) s ∧
    s.interopEnabled = false ∧ s.gw = some wDropped ∧ ¬ s.l1.accepts ∧
    step wEnabled wEnv 2 (.enableInterop true) s = some s' ∧ s'.interopEnabled = true

/-- **(d), ONE CALL: A DIAMOND THAT IS AWAY CANNOT SET THE FLAG** (`Admin.sol:454`,
`ZKChainBase.sol:141-146`). `permanentlyRequireSecondProofSystem` reverts on a diamond whose
`settlementLayer` is not `address(0)`, for every caller. -/
def Properties.AwayDiamondCannotRequire : Prop :=
  ∀ (E : Env) (owner c : Address) (d : Diamond), ¬ d.accepts →
    dstep E owner c .permanentlyRequireSecondProofSystem d = none

/-- **(d) A GATEWAY-SETTLED CHAIN CANNOT BE ENABLED WITH THE REQUIREMENT.** In every system of
the model: take a chain whose L1 diamond is away and has no flag. Along every run with no
break-glass cut in which the chain does not come back to L1 (`StaysAway`: no mint on L1 and no
failed-departure confirmation), the L1 diamond stays away and without the flag, and
`enableInterop(chainId, true)` reverts for every caller in the state reached. If moreover
governance never waives the requirement (`StaysAwayNoWaiver`), a chain that was not enabled is
not enabled. No state of this kind is reachable at `d9f6789` from chains settling on L1
(`MigrationBanRefusesEveryMigration`). -/
def Properties.GatewaySettledChainCannotEnableInterop : Prop :=
  (∀ (cfg : Cfg) (E : Env) (s s' : Sys) (tr : List (Address × Call)),
    Run cfg E StaysAway s tr s' → ¬ s.l1.accepts → s.l1.secondProofSystemRequired = false →
      ¬ s'.l1.accepts ∧ s'.l1.secondProofSystemRequired = false ∧
      ∀ c, step cfg E c (.enableInterop true) s' = none) ∧
  ∀ (cfg : Cfg) (E : Env) (s s' : Sys) (tr : List (Address × Call)),
    Run cfg E StaysAwayNoWaiver s tr s' → ¬ s.l1.accepts →
    s.l1.secondProofSystemRequired = false → s.interopEnabled = false →
      s'.interopEnabled = false

/-- **THE REQUIREMENT SET ON THE GATEWAY DOES NOT COUNT.** With migrations enabled: an unflagged
chain migrates to the gateway and its admin sets the requirement on the gateway diamond
(`wRequireOnGateway`, a `StaysAwayNoWaiver` run from `w0` to `wAway`). The diamond accepting
the chain's batches then has the flag and is in multi-proof mode, the L1 diamond is away without
it, the Bridgehub owner's `enableInterop(chainId, true)` reverts, and the waived
`enableInterop(chainId, false)` succeeds. -/
def Properties.GatewayRequirementDoesNotCount : Prop :=
  Run wEnabled wEnv StaysAwayNoWaiver w0 wRequireOnGateway wAway ∧
  ¬ wAway.l1.accepts ∧ wAway.l1.secondProofSystemRequired = false ∧
  (∃ d, wAway.gw = some d ∧ d.accepts ∧ d.secondProofSystemRequired = true ∧
    wEnv.proofMode d.verifier d.disabledProofSystems = some MULTI_PROOF_TYPE) ∧
  step wEnabled wEnv 2 (.enableInterop true) wAway = none ∧
  (step wEnabled wEnv 2 (.enableInterop false) wAway).isSome = true

/-! ## The hypothetical repair -/

/-- **(e) A REPAIRED COMMITMENT KEEPS THE REQUIREMENT.** This is **not** the source: it is the
system with `repaired = true`, where the commitment carries the flag and the mint guards and
writes it as `Migrator.sol:234-241` does for `isPermanentRollup`. There, migrations enabled or
not, along every run with no break-glass cut `RequirementKept` is preserved, and in the state
reached a call turning a proof system off on a diamond that accepts the chain's batches
succeeds only for the owner of that layer's Bridgehub. The statement says nothing about the
mask or the verifier a diamond has when the chain arrives (`RepairedArrivalCanHaveZiskOff`). -/
def Properties.RepairedCommitmentKeepsRequirement : Prop :=
  ∀ (cfg : Cfg) (E : Env) (s s' : Sys) (tr : List (Address × Call)),
    cfg.repaired = true → Run cfg E Tame s tr s' → RequirementKept s →
      RequirementKept s' ∧
      ∀ (L : Layer) (d : Diamond) (c : Address) (p : ProofSystem) (s'' : Sys),
        s'.diamondAt L = some d → d.accepts →
        step cfg E c (.diamond L (.setProofSystemStatus p false)) s' = some s'' →
        c = s'.ownerAt L

/-- **THE REPAIR ON THE COUNTERMODEL'S RUN.** Under the repair (`wRepaired`, migrations
enabled), the run of `RequirementDroppedByMigration` up to the arrival reaches `w5Repaired`:
`RequirementKept` holds at `w3` and at `w5Repaired`, the gateway diamond accepts the chain's
batches and has both flags, and both calls of `wDrop` are refused there. -/
def Properties.RepairedCarriesRequirementWitness : Prop :=
  Run wRepaired wEnv Tame w0 (wRequire ++ wEnable) w3 ∧ RequirementKept w3 ∧
  Run wRepaired wEnv Tame w3 wLeave w5Repaired ∧ RequirementKept w5Repaired ∧
  (∃ d, w5Repaired.gw = some d ∧ d.accepts ∧ d.secondProofSystemRequired = true ∧
    d.isPermanentRollup = true) ∧
  step wRepaired wEnv 1 (.diamond .gw (.setProofSystemStatus .zisk false)) w5Repaired = none ∧
  step wRepaired wEnv 5 (.diamond .gw (.upgrade (some 20))) w5Repaired = none

/-- **COUNTERMODEL: THE REPAIR DOES NOT CARRY THE MASK.** Under the repair, with no break-glass
cut and no ZiSK-off by either Bridgehub's owner (`wRoundTrip`, an `AdminSide` run from `w0` to
`wBack`): an unflagged chain migrates to the gateway; its admin turns ZiSK off on the L1 diamond
it left (`setProofSystemStatus` is not `onlySettlementLayer`, and that diamond has no flag) and
sets the requirement on the gateway; the chain comes back. The L1 diamond then accepts the
chain's batches, has the flag (`RequirementKept wBack`), has ZiSK off, and its proof mode is
single-proof PLONK. Carrying the flag alone does not give "both proofs from then on". -/
def Properties.RepairedArrivalCanHaveZiskOff : Prop :=
  Run wRepaired wEnv AdminSide w0 wRoundTrip wBack ∧
  RequirementKept wBack ∧ wBack.l1.accepts ∧ wBack.l1.secondProofSystemRequired = true ∧
  ziskOff wBack.l1 ∧
  wEnv.proofMode wBack.l1.verifier wBack.l1.disabledProofSystems = some PLONK_TYPE

end Contracts.SecondProofSystem.MigrationV35
