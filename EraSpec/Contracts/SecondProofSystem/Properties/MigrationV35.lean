import EraSpec.Contracts.SecondProofSystem.Specs.MigrationV35

/-!
# Properties: the second-proof-system requirement of one chain, its two diamonds and migration

Statements about `EraSpec.Contracts.SecondProofSystem.Specs.MigrationV35` (era-contracts
`draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`). Proofs are in
`EraSpec.Contracts.SecondProofSystem.Proofs.MigrationV35`.

`protocol-docs/interop-gating.md:26-27` says the requirement "makes every batch of an enabled
chain carry both an Airbender and a ZiSK proof from then on, unless governance turns ZiSK off in
an emergency", and `:35-42` that it is one-way and that, once set, ZiSK-off is governance's and
upgrades keep the second proof system. "Both proofs" is read here as the proof mode the
chain's diamond reports (`getProofMode()`, the value `enableInterop` checks): what a verifier's
`verify` then accepts is outside the model.

* **The source setting, where migrations are disabled** (`CHAIN_MIGRATIONS_ENABLED = false`).
  Every burn and mint reverts (`MigrationBanRefusesEveryMigration`). Along runs of modelled
  calls, a chain that settles on L1 with the requirement keeps settling on its L1 diamond and
  keeps the requirement; if its L1 verifier reported multi-proof mode for the empty mask, every
  later L1 verifier does; and ZiSK-off there stays with the owner of L1's Bridgehub
  (`RequirementPermanentWhileMigrationsDisabled`). If the L1 diamond starts with mask `0` or
  the ZiSK bit, it always either has mask `0` and reports multi-proof mode, or has exactly the
  ZiSK bit set (`MultiProofOrZiskOffWhileMigrationsDisabled`). If the owner of L1's Bridgehub
  turns no proof system off on the L1 diamond, the L1 diamond's ZiSK bit stays clear
  (`ZiskStaysOnWithoutTheBridgehubOwner`), and an L1 diamond that started with mask `0` and such
  a verifier keeps mask `0` and keeps reporting multi-proof mode
  (`MultiProofKeptWhileMigrationsDisabled`).
* **Enabling interop with the requirement.** In the model, which omits its registration and
  backfill checks, `enableInterop(chainId, true)` succeeds exactly for the owner of L1's
  Bridgehub, on a chain not yet enabled whose L1 diamond has the requirement and reports
  multi-proof mode, and it changes only `interopEnabled` (`EnableInteropSucceedsIff`).
  `MultiProofVerifier` reports multi-proof mode exactly for the empty mask
  (`MultiProofModeIffNothingDisabled`). Together: in the source setting, a chain settling on L1
  that is enabled with the requirement while its L1 verifier runs
  `MultiProofVerifier.getProofMode` stays enabled and keeps reporting multi-proof mode along
  every run of modelled calls without a break-glass cut in which the owner of L1's Bridgehub
  turns no proof system off on the L1 diamond (`EnabledChainStaysMultiProof`). Witnesses:
  `RequirementPermanentWitness` (with the owner's emergency switch), `MultiProofKeptWitness`,
  and `ReturnedChainWitness` (a chain that also has a gateway diamond, left before the pin, on
  which the owner of the gateway's Bridgehub, made its admin, turns ZiSK off).
* **The migration path, migrations enabled or not.** The requirement can be set only on a
  diamond that accepts the chain's batches (`AwayDiamondCannotRequire`). `isPermanentRollup` is
  carried by the commitment and guarded by the mint (`PermanentRollupCarried`), and is kept
  along every run of modelled calls without a break-glass cut, migrations included
  (`PermanentRollupKeptAcrossMigration`; `PermanentRollupKeptWitness` migrates a permanent rollup
  to the gateway and back, under the dev setting `migrationsEnabled = true`).

No statement here has a hash premise. The positive run-level results quantify over every `Env`,
every caller and every modelled call except break-glass cuts (and, where stated, a ZiSK-off on
the L1 diamond by the owner of L1's Bridgehub). They say nothing about calls outside the model:
among them `setAddresses`, by which a Bridgehub's owner repoints its `chainAssetHandler` and
`messageRoot`, and proxy upgrades of a chain asset handler, `L1MessageRoot` or a Bridgehub
(`OPS-CONFIG`; see "Not modelled" in the Specs). The transport assumption
`MODEL-SECOND-PROOF-MIGRATION` concerns only `PermanentRollupKeptAcrossMigration`.
-/

namespace Contracts.SecondProofSystem.MigrationV35

/-! ## The source: migrations disabled -/

/-- **THE BAN REFUSES EVERY MIGRATION** (`ChainAssetHandlerBase.sol:151-156, 201, 365`,
`common/Config.sol:320`). With `migrationsEnabled = false`, each of the four burn and mint
calls reverts, for every caller and in every state. The failed-departure confirmation is not
gated and is not among them. -/
def Properties.MigrationBanRefusesEveryMigration : Prop :=
  ∀ (cfg : Cfg) (E : Env) (c : Address) (call : Call) (s : Sys),
    cfg.migrationsEnabled = false → call.isMigration = true → step cfg E c call s = none

/-- **THE REQUIREMENT IS PERMANENT WHILE MIGRATIONS ARE DISABLED**
(`protocol-docs/interop-gating.md:35-42`). With `migrationsEnabled = false`, take a chain that
settles on L1 and whose L1 diamond has the flag. Along every run of modelled calls with no
break-glass cut, by any callers (the Bridgehub owners' ZiSK-off included):

* the chain still settles on L1, on its L1 diamond, and the flag is still set;
* if the L1 verifier reported multi-proof mode for the empty mask (`getProofMode(0)`), the L1
  verifier of the state reached still does;
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

/-- **MULTI-PROOF MODE, OR ZiSK OFF AND NOTHING ELSE** (`protocol-docs/interop-gating.md:26-27`,
"unless governance turns ZiSK off in an emergency"). With `migrationsEnabled = false`, take a
chain that settles on L1 whose L1 diamond has the flag, a mask that is `0` or the ZiSK bit, and
a verifier reporting multi-proof mode for the empty mask. Along every run of modelled calls
with no break-glass cut, by any callers (the Bridgehub owners' ZiSK-off included), the L1
diamond of the state reached either has mask `0` and reports multi-proof mode, or has exactly
the ZiSK bit set. By `RequirementPermanentWhileMigrationsDisabled`, only the owner of L1's
Bridgehub can make a ZiSK-off call there succeed. -/
def Properties.MultiProofOrZiskOffWhileMigrationsDisabled : Prop :=
  ∀ (cfg : Cfg) (E : Env) (s s' : Sys) (tr : List (Address × Call)),
    cfg.migrationsEnabled = false → Run cfg E Tame s tr s' →
    SettlesOnL1 s → s.l1.secondProofSystemRequired = true →
    (s.l1.disabledProofSystems = 0 ∨ s.l1.disabledProofSystems = ziskBit) →
    E.proofMode s.l1.verifier 0 = some MULTI_PROOF_TYPE →
      (s'.l1.disabledProofSystems = 0 ∧
        E.proofMode s'.l1.verifier s'.l1.disabledProofSystems = some MULTI_PROOF_TYPE) ∨
      s'.l1.disabledProofSystems = ziskBit

/-- **ZiSK STAYS ON WITHOUT THE BRIDGEHUB OWNER.** With `migrationsEnabled = false`, a chain
settling on L1 whose L1 diamond has the flag set and the ZiSK bit clear keeps that ZiSK bit
clear along every run of modelled calls with no break-glass cut in which the owner of L1's
Bridgehub turns no proof system off on the L1 diamond (`NoL1OwnerZiskOff`). No other modelled
call is excluded, whoever makes it: a ZiSK-off on the gateway diamond by the owner of the
gateway's Bridgehub may occur. -/
def Properties.ZiskStaysOnWithoutTheBridgehubOwner : Prop :=
  ∀ (cfg : Cfg) (E : Env) (s s' : Sys) (tr : List (Address × Call)),
    cfg.migrationsEnabled = false → Run cfg E NoL1OwnerZiskOff s tr s' →
    SettlesOnL1 s → s.l1.secondProofSystemRequired = true → ¬ ziskOff s.l1 →
      ¬ ziskOff s'.l1

/-- **THE L1 DIAMOND KEEPS REPORTING MULTI-PROOF MODE.** With `migrationsEnabled = false`, take
a chain that settles on L1 whose L1 diamond has the flag, nothing disabled (mask `0`), and a
verifier reporting multi-proof mode for the empty mask. Along every run of modelled calls with
no break-glass cut and no proof system turned off on the L1 diamond by the owner of L1's
Bridgehub (`NoL1OwnerZiskOff`; every other modelled call, by anyone, is allowed): the chain
still settles on L1, the flag is set, the mask is still `0`, the proof mode the L1 diamond
reports (`getProofMode(s.disabledProofSystems)`, `ZKChainBase.sol:187-190`) is multi-proof, and
interop, if enabled, is still enabled. -/
def Properties.MultiProofKeptWhileMigrationsDisabled : Prop :=
  ∀ (cfg : Cfg) (E : Env) (s s' : Sys) (tr : List (Address × Call)),
    cfg.migrationsEnabled = false → Run cfg E NoL1OwnerZiskOff s tr s' →
    SettlesOnL1 s → s.l1.secondProofSystemRequired = true → s.l1.disabledProofSystems = 0 →
    E.proofMode s.l1.verifier 0 = some MULTI_PROOF_TYPE →
      SettlesOnL1 s' ∧ s'.l1.secondProofSystemRequired = true ∧
      s'.l1.disabledProofSystems = 0 ∧
      E.proofMode s'.l1.verifier s'.l1.disabledProofSystems = some MULTI_PROOF_TYPE ∧
      (s.interopEnabled = true → s'.interopEnabled = true)

/-! ## Enabling interop -/

/-- **`MultiProofVerifier` REPORTS MULTI-PROOF MODE EXACTLY FOR THE EMPTY MASK**
(`MultiProofVerifier.sol:101-109`). -/
def Properties.MultiProofModeIffNothingDisabled : Prop :=
  ∀ m : UInt8, multiProofGetProofMode m = some MULTI_PROOF_TYPE ↔ m = 0

/-- **WHEN `enableInterop` SUCCEEDS, IN THE MODEL** (`L1MessageRoot.sol:72-89` without the
registration and backfill checks `:75, :80`, which the model omits; in the source they can still
revert a call that succeeds in the model). In the model, `enableInterop(chainId, req)` by `c`
succeeds with result `s'` exactly when `c` owns L1's Bridgehub, interop is not yet enabled, with
`req` the chain's **L1** diamond has the flag and reports multi-proof mode under its own mask,
and `s'` is `s` with interop enabled. -/
def Properties.EnableInteropSucceedsIff : Prop :=
  ∀ (cfg : Cfg) (E : Env) (c : Address) (req : Bool) (s s' : Sys),
    step cfg E c (.enableInterop req) s = some s' ↔
      c = s.l1BridgehubOwner ∧ s.interopEnabled = false ∧
      (req = true → s.l1.secondProofSystemRequired = true ∧
        E.proofMode s.l1.verifier s.l1.disabledProofSystems = some MULTI_PROOF_TYPE) ∧
      s' = { s with interopEnabled := true }

/-- **AN ENABLED CHAIN STAYS IN MULTI-PROOF MODE** (`protocol-docs/interop-gating.md:26-27`, in
the source setting). With `migrationsEnabled = false`: take a chain that settles on L1 whose L1
verifier runs `MultiProofVerifier.getProofMode`, and let `enableInterop(chainId, true)` succeed
on it. Along every run of modelled calls that follows with no break-glass cut and no proof
system turned off on the L1 diamond by the owner of L1's Bridgehub (`NoL1OwnerZiskOff`; every
other modelled call is allowed, upgrades to any verifier passing the upgrade check included),
interop stays enabled, the chain settles on its L1 diamond, which has the flag and mask `0`,
and the proof mode it reports is multi-proof. -/
def Properties.EnabledChainStaysMultiProof : Prop :=
  ∀ (cfg : Cfg) (E : Env) (c : Address) (s s₁ s' : Sys) (tr : List (Address × Call)),
    cfg.migrationsEnabled = false → SettlesOnL1 s →
    (∀ m, E.proofMode s.l1.verifier m = multiProofGetProofMode m) →
    step cfg E c (.enableInterop true) s = some s₁ → Run cfg E NoL1OwnerZiskOff s₁ tr s' →
      s'.interopEnabled = true ∧ SettlesOnL1 s' ∧ s'.l1.secondProofSystemRequired = true ∧
      s'.l1.disabledProofSystems = 0 ∧
      E.proofMode s'.l1.verifier s'.l1.disabledProofSystems = some MULTI_PROOF_TYPE

/-- **THE PREMISES OF `RequirementPermanentWhileMigrationsDisabled` AND
`MultiProofOrZiskOffWhileMigrationsDisabled` ARE SATISFIABLE, BOTH CASES OF THE LATTER OCCUR,
AND THE OWNER'S SWITCH WORKS.** In the source (`wSource`): the admin makes the chain a permanent
rollup and requires the second proof system, and the Bridgehub owner enables interop with the
requirement, reaching `w3`, which settles on L1 with the flag set, mask `0` and a verifier in
multi-proof mode for the empty mask. From `w3` the run `wOnL1` succeeds: an upgrade to the
multi-proof verifier `12`, then the owner's emergency ZiSK-off, after which the L1 diamond has
exactly the ZiSK bit set and reports single-proof PLONK mode, then the admin turning ZiSK back
on, after which it reports multi-proof mode again. In `w3` the owner's ZiSK-off succeeds, and
the admin's ZiSK-off, an upgrade to the single-proof verifier `20` and the admin's migration
burn are refused. -/
def Properties.RequirementPermanentWitness : Prop :=
  Run wSource wEnv Tame w0 (wRequire ++ wEnable) w3 ∧
  SettlesOnL1 w3 ∧ w3.l1.secondProofSystemRequired = true ∧ w3.l1.disabledProofSystems = 0 ∧
  wEnv.proofMode w3.l1.verifier 0 = some MULTI_PROOF_TYPE ∧
  (∃ s₁ s₂, Run wSource wEnv Tame w3 (wOnL1.take 2) s₁ ∧
    s₁.l1.disabledProofSystems = ziskBit ∧
    wEnv.proofMode s₁.l1.verifier s₁.l1.disabledProofSystems = some PLONK_TYPE ∧
    Run wSource wEnv Tame s₁ (wOnL1.drop 2) s₂ ∧ s₂.l1.verifier = 12 ∧ ¬ ziskOff s₂.l1 ∧
    s₂.l1.secondProofSystemRequired = true ∧
    wEnv.proofMode s₂.l1.verifier s₂.l1.disabledProofSystems = some MULTI_PROOF_TYPE) ∧
  (step wSource wEnv 2 (.diamond .l1 (.setProofSystemStatus .zisk false)) w3).isSome = true ∧
  step wSource wEnv 1 (.diamond .l1 (.setProofSystemStatus .zisk false)) w3 = none ∧
  step wSource wEnv 5 (.diamond .l1 (.upgrade (some 20))) w3 = none ∧
  step wSource wEnv 1 (.bridgeBurnToGateway 77 1 wPayload) w3 = none

/-- **THE PREMISES OF `ZiskStaysOnWithoutTheBridgehubOwner`,
`MultiProofKeptWhileMigrationsDisabled` AND `EnabledChainStaysMultiProof` ARE SATISFIABLE.** In
the source: the admin's `wRequire` reaches `w2`, which settles on L1 with the flag set, mask
`0`, and the L1 verifier `10` running `MultiProofVerifier.getProofMode`. There the owner's
`enableInterop(chainId, true)` succeeds with `w3`, while on `w0` (no flag) it is refused and the
waived `enableInterop(chainId, false)` succeeds. From `w3` the `NoL1OwnerZiskOff` run `wKeep`
(an upgrade to the multi-proof verifier `12`, the admin turning ZiSK on, an admin handover to
`4`, and L1's Bridgehub changing owner to `6`) reaches `wKept`, which reports multi-proof mode.
In `wKept` the new admin's ZiSK-off, an upgrade to the single-proof verifier `20` and the new
admin's migration burn are refused, and the new owner's ZiSK-off succeeds. -/
def Properties.MultiProofKeptWitness : Prop :=
  Run wSource wEnv NoL1OwnerZiskOff w0 wRequire w2 ∧
  SettlesOnL1 w2 ∧ w2.l1.secondProofSystemRequired = true ∧ w2.l1.disabledProofSystems = 0 ∧
  ¬ ziskOff w2.l1 ∧ (∀ m, wEnv.proofMode w2.l1.verifier m = multiProofGetProofMode m) ∧
  step wSource wEnv 2 (.enableInterop true) w2 = some w3 ∧
  step wSource wEnv 2 (.enableInterop true) w0 = none ∧
  (step wSource wEnv 2 (.enableInterop false) w0).isSome = true ∧
  Run wSource wEnv NoL1OwnerZiskOff w3 wKeep wKept ∧
  wKept.l1.verifier = 12 ∧ wKept.l1.admin = 4 ∧ wKept.l1BridgehubOwner = 6 ∧
  wEnv.proofMode wKept.l1.verifier wKept.l1.disabledProofSystems = some MULTI_PROOF_TYPE ∧
  step wSource wEnv 4 (.diamond .l1 (.setProofSystemStatus .zisk false)) wKept = none ∧
  step wSource wEnv 5 (.diamond .l1 (.upgrade (some 20))) wKept = none ∧
  step wSource wEnv 4 (.bridgeBurnToGateway 77 4 wPayload) wKept = none ∧
  (step wSource wEnv 6 (.diamond .l1 (.setProofSystemStatus .zisk false)) wKept).isSome = true

/-- **THE SOURCE RESULTS COVER A CHAIN WITH A GATEWAY DIAMOND, AND `NoL1OwnerZiskOff` ADMITS A
ZiSK-OFF THERE BY THE OWNER OF THE GATEWAY'S BRIDGEHUB.** `wReturned` is `w3` for a chain that
went to the gateway and came back before the pin: it also has a gateway diamond, `wDormant`,
which forwards to L1. It settles on L1 with the flag set, mask `0` and a verifier in multi-proof
mode for the empty mask, and the gateway's Bridgehub is owned by `3`. The `NoL1OwnerZiskOff` run
`wDormantHandover` (the gateway diamond's admin hands over to `3`, who then turns ZiSK off on
the gateway diamond) succeeds and reaches `wReturnedEnd`, which still settles on L1, whose
gateway diamond has the ZiSK bit set, and whose L1 diamond reports multi-proof mode. -/
def Properties.ReturnedChainWitness : Prop :=
  SettlesOnL1 wReturned ∧ wReturned.gw = some wDormant ∧ ¬ wDormant.accepts ∧
  wReturned.gwBridgehubOwner = 3 ∧
  wReturned.l1.secondProofSystemRequired = true ∧ wReturned.l1.disabledProofSystems = 0 ∧
  wEnv.proofMode wReturned.l1.verifier 0 = some MULTI_PROOF_TYPE ∧
  Run wSource wEnv NoL1OwnerZiskOff wReturned wDormantHandover wReturnedEnd ∧
  SettlesOnL1 wReturnedEnd ∧
  wReturnedEnd.gw = some { wDormant with admin := 3, disabledProofSystems := ziskBit } ∧
  wEnv.proofMode wReturnedEnd.l1.verifier wReturnedEnd.l1.disabledProofSystems =
    some MULTI_PROOF_TYPE

/-! ## The migration path -/

/-- **ONLY A DIAMOND THAT ACCEPTS THE CHAIN'S BATCHES CAN TAKE THE REQUIREMENT**
(`Admin.sol:454`, `ZKChainBase.sol:141-146`). `permanentlyRequireSecondProofSystem` reverts on
a diamond whose `settlementLayer` is not `address(0)`, for every caller. -/
def Properties.AwayDiamondCannotRequire : Prop :=
  ∀ (E : Env) (owner c : Address) (d : Diamond), ¬ d.accepts →
    dstep E owner c .permanentlyRequireSecondProofSystem d = none

/-- **THE PREMISE OF `AwayDiamondCannotRequire` IS SATISFIABLE AND THE CONCLUSION IS NOT
ALWAYS TRUE.** The witness L1 diamond, forwarding to `77`, refuses its admin's call; the same
diamond accepting the chain's batches takes the requirement. -/
def Properties.AwayDiamondCannotRequireWitness : Prop :=
  ¬ ({ wL1 with settlementLayer := 77 } : Diamond).accepts ∧
  dstep wEnv 2 1 .permanentlyRequireSecondProofSystem { wL1 with settlementLayer := 77 } = none ∧
  dstep wEnv 2 1 .permanentlyRequireSecondProofSystem wL1 =
    some { wL1 with secondProofSystemRequired := true }

/-- **`isPermanentRollup` IS CARRIED** (`Migrator.sol:346`, `:234-241`). The commitment holds
the burned diamond's `isPermanentRollup`; a successful mint leaves the destination with the
commitment's; and a mint that would clear it on a diamond that has it reverts. -/
def Properties.PermanentRollupCarried : Prop :=
  (∀ (payload c : Commitment) (d : Diamond), prepareChainCommitment payload d = some c →
    c.isPermanentRollup = d.isPermanentRollup) ∧
  (∀ (c : Commitment) (d d' : Diamond), forwardedBridgeMint c d = some d' →
    d'.isPermanentRollup = c.isPermanentRollup) ∧
  ∀ (c : Commitment) (d : Diamond), d.isPermanentRollup = true → c.isPermanentRollup = false →
    forwardedBridgeMint c d = none

/-- **`isPermanentRollup` IS KEPT ACROSS MIGRATION.** In every system of the model, migrations
enabled or not: along a run of modelled calls with no break-glass cut, `PermanentRollupKept` is
preserved. So once every diamond accepting the chain's batches is a permanent rollup (and every
migration in flight says so), every diamond that later accepts them is. The in-flight clause
rests on the transport assumption `MODEL-SECOND-PROOF-MIGRATION`: a mint consumes data a burn
produced. -/
def Properties.PermanentRollupKeptAcrossMigration : Prop :=
  ∀ (cfg : Cfg) (E : Env) (s s' : Sys) (tr : List (Address × Call)),
    Run cfg E Tame s tr s' → PermanentRollupKept s → PermanentRollupKept s'

/-- **THE PREMISES OF `PermanentRollupKeptAcrossMigration` AND `PermanentRollupCarried` ARE
SATISFIABLE, ACROSS A ROUND TRIP.** With migrations enabled (`wEnabled`, the dev setting): the
admin makes the chain a permanent rollup (`wRollup`, where `PermanentRollupKept` holds); the
chain migrates to the gateway (`wRollupAway`: the new gateway diamond accepts the chain's
batches and is a permanent rollup, the L1 diamond does not accept them) and comes back
(`wRollupHome`: the L1 diamond accepts them and is a permanent rollup, the gateway diamond does
not accept them). `PermanentRollupKept` holds in all three states. In the source (`wSource`)
the same burn is refused. For `PermanentRollupCarried`: the burn's commitment is `wRollupWire`,
which says `isPermanentRollup = true`, and a mint of `wPayload` (which says `false`) on the
permanent-rollup L1 diamond reverts. -/
def Properties.PermanentRollupKeptWitness : Prop :=
  prepareChainCommitment wPayload wRollup.l1 = some wRollupWire ∧
  wRollupWire.isPermanentRollup = true ∧
  forwardedBridgeMint wPayload wRollup.l1 = none ∧
  Run wEnabled wEnv Tame w0 [(1, .diamond .l1 .makePermanentRollup)] wRollup ∧
  PermanentRollupKept wRollup ∧
  Run wEnabled wEnv Tame wRollup wRollupLeave wRollupAway ∧ PermanentRollupKept wRollupAway ∧
  ¬ wRollupAway.l1.accepts ∧
  (∃ d, wRollupAway.gw = some d ∧ d.accepts ∧ d.isPermanentRollup = true) ∧
  Run wEnabled wEnv Tame wRollupAway wRollupReturn wRollupHome ∧
  PermanentRollupKept wRollupHome ∧
  wRollupHome.l1.accepts ∧ wRollupHome.l1.isPermanentRollup = true ∧
  (∃ d, wRollupHome.gw = some d ∧ ¬ d.accepts ∧ d.isPermanentRollup = true) ∧
  step wSource wEnv 1 (.bridgeBurnToGateway 77 1 wPayload) wRollup = none

end Contracts.SecondProofSystem.MigrationV35
