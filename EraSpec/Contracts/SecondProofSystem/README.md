# SecondProofSystem

## Headline guarantees

About era-contracts `draft/v0.35.0` at `b17415d20`. A revert is the absence of a step; the
installed facets are those at `b17415d20`.

- `Contracts.SecondProofSystem.FlagAuthorityV35.Properties.FlagMonotone`: premise: no
  break-glass cut (a CTM diamond cut whose init is arbitrary code) along the run. Then a
  diamond that requires the second proof system keeps requiring it, whatever every other
  caller does and whatever the verifier answers.
- `Contracts.SecondProofSystem.FlagAuthorityV35.Properties.AdminCannotDropSecondProof`:
  premises: no break-glass cut and no `setProofSystemStatus` by whoever owns the Bridgehub at
  that moment. Then a flagged diamond with ZiSK on stays flagged with ZiSK on, whatever the
  verifier answers.
- `Contracts.SecondProofSystem.MigrationV35.Properties.EnabledChainStaysMultiProof`:
  premises: chain migrations are disabled (`CHAIN_MIGRATIONS_ENABLED = false`, as at
  `b17415d20`); the chain settles on L1; its L1 verifier answers `getProofMode` as
  `MultiProofVerifier` does; `enableInterop` with the requirement succeeds; afterwards no
  break-glass cut and no proof system turned off on the L1 diamond by L1's Bridgehub owner.
  Then the chain stays interop-enabled, on L1, flagged, with mask `0` and in multi-proof mode.
- `Contracts.SecondProofSystem.UpgradeGateV35.Properties.FlaggedChainsStayMultiProof`:
  premises: every verifier that answers multi-proof under some mask answers it under mask `0`
  (`MaskMonotone`; both deployed verifiers do); every flagged chain starts on a verifier that
  passes the gate. Then along every run every flagged chain's verifier passes the gate. This
  topic extends `../ChainTypeManager/`'s `UpgradeTiming` model (written at `e561b9cc2`).
- `Contracts.SecondProofSystem.UpgradeGateV35.Properties.LockedChainCannotUpgrade`: premise:
  the chain is locked (flagged, and the edge committed at its version lands on a release whose
  verifier fails the gate, with nothing committed above). Then no upgrade step of that chain
  succeeds, by any path, caller or time.

Witnesses: `FlagMonotoneRunWitness`, `AdminSideRunWitness`, `MultiProofKeptWitness`,
`UpgradeGateV35Witness`, `ReleasePolicyWitness`. Countermodels: `InitClearsFlag`,
`BreakGlassDropsSecondProof`, `LyingVerifierFlagsWithZiskOff`, `AdminOnlyRuleLetsAdminDrop`,
`MaskMonotoneIsLoadBearing`, `ReleasePolicyIsLoadBearing`.

## Source and layout

The second-proof-system requirement of ZKsync OS chains: a chain's admin can make its diamond
permanently require the ZiSK proof next to the Airbender one, after which switching ZiSK off is
reserved for the Bridgehub owner (`protocol-docs/interop-gating.md`, "Second proof system
requirement"). The folder is named after the requirement, not after one contract. The code is
spread over `state-transition/chain-deps/facets/Admin.sol` (`setProofSystemStatus`,
`permanentlyRequireSecondProofSystem`, `_executeDiamondCut`), `ZKChainBase.sol` (the modifiers,
`_getProofMode`), `upgrades/BaseZkSyncUpgrade.sol` (`_setVerifier`), the verifiers'
`getProofMode` (`state-transition/verifiers/MultiProofVerifier.sol`, `ZKsyncOSVerifier.sol`) and
the second-proof checks of `core/message-root/L1MessageRoot.sol` (`enableInterop`).
`UpgradeGateV35` also reads `DefaultUpgrade`, `DiamondInit` and the `ChainTypeManager` paths
that commit and replace transitions. `MigrationV35` also reads the `Getters` and `Migrator`
facets, `DiamondInit`, the `ChainTypeManager` and chain-asset-handler migration entry points
and `protocol-docs/chain-lifecycle.md`.

Source: era-contracts branch `draft/v0.35.0` at **`b17415d20`**
(`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`). Paths are relative to `l1-contracts/contracts/`;
every `file:line` in the specs is at that commit.

The three topics are three models: one diamond (FlagAuthorityV35, the canonical diamond
model), one chain with its L1 and gateway diamonds (MigrationV35) and the CTM-level gate over
`../ChainTypeManager/`'s upgrade model (UpgradeGateV35). No theorem relates them yet; see
"Relation to FlagAuthorityV35 and UpgradeGateV35" below.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact
named propositions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| FlagAuthorityV35 | [Specs/FlagAuthorityV35.lean](Specs/FlagAuthorityV35.lean) | [Properties/FlagAuthorityV35.lean](Properties/FlagAuthorityV35.lean) | [Proofs/FlagAuthorityV35.lean](Proofs/FlagAuthorityV35.lean) |
| UpgradeGateV35 | [Specs/UpgradeGateV35.lean](Specs/UpgradeGateV35.lean) | [Properties/UpgradeGateV35.lean](Properties/UpgradeGateV35.lean) | [Proofs/UpgradeGateV35.lean](Proofs/UpgradeGateV35.lean) |
| MigrationV35 | [Specs/MigrationV35.lean](Specs/MigrationV35.lean) | [Properties/MigrationV35.lean](Properties/MigrationV35.lean) | [Proofs/MigrationV35.lean](Proofs/MigrationV35.lean) |

Namespaces: `Contracts.SecondProofSystem.FlagAuthorityV35`,
`Contracts.SecondProofSystem.UpgradeGateV35` and `Contracts.SecondProofSystem.MigrationV35`.
Statements are `<namespace>.Properties.*`; each certificate has the same name without the
`Properties` segment.

## FlagAuthorityV35: what the model is

One diamond, projected onto `verifier`, `admin`, `pendingAdmin`, `chainTypeManager`,
`settlementLayer`, the mask `disabledProofSystems` and the flag `secondProofSystemRequired`,
plus the Bridgehub owner that `setProofSystemStatus` reads. The calls are every state-changing
`AdminFacet` entry point (the seven that touch the projection transcribed, the other eighteen as
no-ops on it), the `Migrator`'s settlement-layer writes, a change of Bridgehub owner, and every
other facet as a no-op. A diamond cut's init is none, a genuine engine (which can only install a
verifier through `_setVerifier`), or arbitrary code: the **break-glass cut**. A verifier is an
`Env`: what `getProofMode(mask)` returns at each address, fixed for a run of `Reach` and chosen
per call in a run of `ReachEnvs`.

Run predicates name who acts. `AdminSide`: no break-glass cut and no `setProofSystemStatus` by
the Bridgehub owner of that moment; everything else, by anyone. `OwnerSide`: no break-glass cut
and no `setProofSystemStatus` by the chain admin of that moment. `AdminSideHonest`: `AdminSide`,
and the verifier reports ZiSK honestly whenever the flag is set.

### What to check

**(a) The flag is one-way.**

- `PermanentlyRequireExact`: `permanentlyRequireSecondProofSystem` succeeds iff the caller is the
  admin, the diamond is on its settlement layer, the flag is clear and the verifier reports
  multi-proof mode for the current mask; it then sets the flag and nothing else.
  `PermanentlyRequireOnce`: on a flagged diamond it reverts for everyone.
- `FlagMonotoneStep`, `FlagMonotone`: no call and no run without a break-glass cut clears the
  flag. `FlagSetOnlyByAdmin`: outside break-glass only that call of the admin sets it.
  `CtmCutEntryPointsAreCtmOnly`: `executeUpgrade` and `genesisUpgrade` succeed only for the CTM.
- `DiamondCutRecheck`: after any successful cut, break-glass included, a diamond that is still
  flagged has a verifier that reports multi-proof mode for the zero mask.
- **Countermodel** `InitClearsFlag`: the CTM's break-glass cut with an init that writes the flag
  `false` succeeds, and the re-check is skipped because it reads the flag the init left.
- Witnesses: `PermanentlyRequireGuardsWitness` (each guard decides a call, including an
  Airbender-only verifier), `FlagMonotoneRunWitness`, `VerifierChecksWitness` (on a flagged
  diamond a genuine upgrade to the Airbender-only verifier is refused by `_setVerifier`, and a
  cut writing it directly is refused by the re-check; on an unflagged one both succeed).

**(b) The caller rule of `setProofSystemStatus`.**

- `ZiskOffAuthorityExact`: the call for ZiSK succeeds for exactly one caller, the Bridgehub
  owner when it disables on a flagged diamond and the chain admin otherwise; for any other proof
  system it reverts. `SetProofSystemStatusEffect`: it writes only the ZiSK bit.
- `MaskWrittenOnlyBySetStatus`, `NonZiskBitsFrozen`: without break-glass nothing else writes the
  mask and the other bits never move.
- `OwnerDisablesOnFlagged`: the owner's ZiSK-off on a flagged diamond succeeds in every model
  state (for a call that reaches the facet, with `owner()` returning).
- **Countermodel** `AdminOnlyRuleLetsAdminDrop`: with the ternary of `Admin.sol:417` replaced by
  `s.admin`, the admin reaches a flagged diamond with ZiSK off.
- Witnesses: `CallerRuleWitness`, `NonZiskBitsWitness`.

**(c) The chain admin cannot drop the second proof system.**

- `AdminCannotDropSecondProof`: along `AdminSide` runs a flagged diamond with ZiSK on stays so,
  whatever the verifier. `ZiskOffOnFlaggedIsOwners` is the one-step form.
- `AdminNeverReachesFlaggedZiskOff`: along `AdminSideHonest` runs, from any diamond that is not
  flagged with ZiSK off. **Countermodel** `LyingVerifierFlagsWithZiskOff`: with a verifier that
  reports multi-proof mode for every mask, the admin switches ZiSK off and then sets the flag;
  under the genuine verifier the second call reverts.
- `InteropGatePersists`: if `enableInterop`'s second-proof checks pass on a diamond with a zero
  mask, they keep passing along `AdminSide` runs, across genuine verifier upgrades.
  `InteropGatePersistsMultiProof`: under the genuine verifier they pass exactly on a flagged
  diamond with a zero mask. **Countermodel** `InteropGateNeedsZeroMask`.
- **Countermodel** `BreakGlassDropsSecondProof`: the CTM's break-glass cut sets the ZiSK bit on a
  flagged diamond; the re-check asks `getProofMode(0)`, not the mask.
- Witnesses: `AdminSideRunWitness` (admin handover, owner change and a genuine upgrade, after
  which the new owner, not the new admin, can switch ZiSK off), `HonestRunWitness`.

**(d) Re-enabling is the chain admin's.**

- `ReenableIsAdmins`, `BridgehubOwnerCannotReenable`, `AdminReenables`: only the admin
  re-enables, and it always can in the model. `ZiskStaysOffWithoutAdmin`: along `OwnerSide`
  runs ZiSK off stays off. **Countermodel** `BreakGlassReenables`. Witness:
  `OwnerSideRunWitness`.

**(e)** `MultiProofVerifierReportsZisk`: the genuine `MultiProofVerifier.getProofMode` reports
multi-proof mode exactly for the zero mask, so it satisfies the honesty premise of (c).

**(f) Verifier answers that change between calls.** `ReachEnvs` runs let every call see its own
`getProofMode` answers, and contain the fixed-answer runs (`ReachEnvsExtendsReach`).
`FlagMonotoneAnyVerifiers`, `AdminCannotDropSecondProofAnyVerifiers`,
`AdminNeverReachesFlaggedZiskOffAnyVerifiers` and `ZiskStaysOffWithoutAdminAnyVerifiers` hold
along them. `InteropGatePersists` is not restated: its conclusion is about the answers
themselves. Witness: `AnyVerifiersRunWitness`.

### Model boundaries

- A revert is the absence of a step. Guards over storage outside the projection (callers of
  `upgradeChainFromVersion`, version and timestamp checks, the engines' batch and settlement
  checks, the other eighteen entry points' guards) are omitted, which only adds runs.
- The installed facets are those at `b17415d20` throughout: a cut that replaces them leaves the
  model. Dispatch and the freeze check of the diamond proxy are not modelled, so the statements
  that say a call succeeds are about the facet code for a call that reaches it.
- That no other facet or contract writes the projected fields is a source reading (a `grep` of
  the tree at `b17415d20`), not a theorem.
- `IOwnable(s.bridgehub).owner()` is assumed to return, and its answer may change between any
  two calls. The verifier answers are fixed for a run except in (f).
- One diamond. Nothing here is about the flag or the mask of another diamond of the same chain.

## UpgradeGateV35: the model

`UpgradeGateV35` extends `ChainTypeManager`'s `UpgradeTiming` model (written at `e561b9cc2`;
the Specs header lists where each of its checks sits at `b17415d20`) with each chain's flag,
verifier and mask. Every registry cut installs the target release's verifier through both checks
(`VerifierGate`); genesis and migration in start a fresh diamond with the flag unset; a
break-glass cut writes any gate fields, subject to the post-cut check. `getProofMode` and each
release's `verifier()` are configuration; the two deployed verifiers are transcribed. Every cut
is checked as if the v35 Admin facet were routed (`MODEL-SECOND-PROOF-GATE` in
[ASSUMPTIONS.md](../../../ASSUMPTIONS.md)).

### What to check

- **The gate holds.** `FlaggedCutsKeepMultiProof`: after any cut of a flagged chain, its
  verifier answers MULTI to `getProofMode(0)`; it follows from the cut steps' guards
  (`VerifierGate.postCut`, or the break-glass post-cut premise), except at genesis and
  migration in, which install an unflagged fresh gate, so it holds there because the flag is
  unset. `FlagSurvivesAllButBreakGlass`: only a break-glass cut of a registered chain clears its
  flag. `FlaggedChainsStayMultiProof`: along every run, every flagged chain's verifier passes
  the gate, if the verifiers are `MaskMonotone`; both deployed
  verifiers are (`MaskMonotoneHoldsForDeployedVerifiers`), and without it a chain can be flagged
  on a verifier that fails the gate (`MaskMonotoneIsLoadBearing`).
- **The emergency switch.** The gate reads mask `0`, so the chain's own mask never decides
  whether it upgrades (`EmergencyOffDoesNotBlockUpgrades`, `EmergencyOffFlaggedChainStillUpgrades`).
- **Commits do not read verifiers** (`CommitIgnoresProofMode`).
- **The repaired characterisation.** `UpgradeChainEnabledIffTimedV35` adds two conjuncts to
  `UpgradeTiming.UpgradeChainEnabledIffTimed`: a nonzero target verifier and, for a flagged
  chain, a target verifier passing the gate. Without them the `e561b9cc2` statements fail here
  (`UpgradeChainEnabledIffTimedFailsV35`, `UpgradesStayEnabledFailsV35`).
  `GatedRunIsATimedRun` projects every gated run to an `UpgradeTiming` run.
- **The lock**, documented upstream (`protocol-docs/interop-gating.md:43-48`). A flagged chain
  whose committed edge installs a verifier failing the gate cannot upgrade by any path, caller or
  time (`LockedChainCannotUpgrade`, `StuckChainCannotUpgrade`). A locked chain stays locked until
  the CTM moves its version or a break-glass cut reaches the chain (`LockHoldsUntilAnEscape`); a
  locked chain is stuck (`LockedIsStuck`), and a stuck chain stays stuck until the CTM installs a
  release whose verifier passes the gate or a break-glass cut reaches it
  (`StuckUntilMultiReleaseOrBreakGlass`). Replacements cannot bring in a release the CTM has not
  installed (`ReplacementAtCurrentVersionIsPinned`, `ReplacementLandsOnAnInstalledRelease`). The escapes fire (`EscapesUnlockTheLockedChain`); a
  skip-replacement onto another single-proof release does not help
  (`SkipOntoSingleProofReleaseDoesNotHelp`). Without a deadline override the departing version
  expires at the edge's deadline (`LockedChainNeedsDeadlineOverride`).
- **Countermodel** `FlaggedChainCannotCrossNonMultiProofEdge`: two identical chains, one flagged;
  the CTM commits an edge onto a single-proof release. The unflagged chain crosses, the flagged one
  cannot, along any run without an escape.
- **The release policy.** The source's answer is the off-chain `protocol-ops` check
  (`judge_proof_mode_kept`, `protocol-ops/src/upgrade_verification/registry/upgrade.rs:915-955`):
  a transition whose departing release's verifier passes the gate must land on a release whose
  verifier does (`KeepsProofMode`). `ReleasePolicyKeepsFlaggedChainsCrossable`: along any run
  with no break-glass cut in which every commit and replacement passes the check, from a state
  satisfying `PolicyInv` (`SysInv`, flagged chains pass the gate, every chain runs its release's
  verifier, committed transitions keep the proof mode), `PolicyInv` is kept and no committed edge
  refuses a flagged chain's verifier. `UpgradesStayEnabledUnderReleasePolicy` is the failing
  `UpgradesStayEnabled` analogue with these premises added: every chain at a committed edge onto a
  well-formed release with a nonzero verifier, batches executed and on its settlement layer, has a
  direct upgrade step by its admin. `ReleasePolicyWitness` meets every premise with a flagged
  chain; `ReleasePolicyIsLoadBearing` drops only the policy, on one commit, and the conclusion
  fails.

Witnesses: `UpgradeGateV35Witness` (every lock premise bundle on a reachable state, a
same-target replacement that keeps the lock, and a flagged chain crossing a multi-proof edge)
and `ReleasePolicyWitness`.

### Model boundaries

- A revert is the absence of a step. Reject-only checks are omitted as in `UpgradeTiming` (the
  L2 upgrade transaction, semver shape, precondition checker, code existence, `onlyL1`), which
  only adds runs; a positive result means no check the model keeps blocks the step.
- The post-cut check is code of the v35 `Admin` facet. A break-glass cut that routes another
  Admin facet, or a chain crossing an opaque legacy edge on a pre-v35 facet, is still gated in the
  model, so `FlaggedCutsKeepMultiProof` and `FlaggedChainsStayMultiProof` hold for chains that
  keep the v35 Admin facet. On the bootstrap edge the engine's own check is the same condition.
- `getProofMode` answers and release verifiers are fixed configuration; arbitrary verifier code
  is covered only through `MaskMonotone`.
- The mask is a natural number; a break-glass cut may write values a `uint8` cannot hold, which
  only adds runs.
- `ChainRouting`'s migration in deploys a diamond for a chain id that has none on this CTM; a
  chain returning to a diamond it kept is not modelled here.
- The release policy is a premise on the run's labels: that governance runs `protocol-ops` on
  every vote is outside the model (`OPS-CONFIG`).

## MigrationV35: the model

One chain and its two diamonds: the one on L1 and the one on a gateway (absent until the chain
first arrives there), each projected onto `verifier`, `admin`, `pendingAdmin`,
`settlementLayer`, `isPermanentRollup`, `disabledProofSystems` and `secondProofSystemRequired`,
with L1's `interopEnabled[chainId]` and the owners of both layers' Bridgehubs. The modelled
calls are the `Admin` facet's calls on either diamond, a genuine upgrade, break-glass cuts, the
burns and mints of the settlement-layer migration (`ChainAssetHandlerBase`, `Migrator`,
`ChainTypeManager`, and `DiamondInit` for a new gateway diamond), the failed-departure
confirmation, `L1MessageRoot.enableInterop` and Bridgehub ownership changes. A verifier is only
its `getProofMode` (`Env`). Model boundary `MODEL-SECOND-PROOF-MIGRATION` in
[ASSUMPTIONS.md](../../../ASSUMPTIONS.md).

Run predicates: `Tame`, no break-glass cut; `NoL1OwnerZiskOff`, no break-glass cut and no proof
system turned off on the L1 diamond by the owner of L1's Bridgehub. Both allow every other
modelled call, by anyone. `NoL1OwnerZiskOff` is not FlagAuthorityV35's `AdminSide`, which
excludes every `setProofSystemStatus` call by the Bridgehub owner.

### What to check

- At the pin `CHAIN_MIGRATIONS_ENABLED = false`, and every burn and mint of the chain asset
  handler reverts (`MigrationBanRefusesEveryMigration`). The failed-departure confirmation is
  not gated.
- With migrations disabled, along `Tame` runs of modelled calls, a chain settling on L1 with
  the requirement keeps settling on its L1 diamond and keeps the requirement; if its L1 verifier
  reported multi-proof mode for the empty mask, the L1 verifier of every state reached still
  does; and ZiSK-off on the L1 diamond succeeds only for the owner of L1's Bridgehub
  (`RequirementPermanentWhileMigrationsDisabled`). An L1 diamond that starts with mask `0` or
  the ZiSK bit always either has mask `0` and reports multi-proof mode, or has exactly the ZiSK
  bit set, the emergency state (`MultiProofOrZiskOffWhileMigrationsDisabled`).
- With migrations disabled, along `NoL1OwnerZiskOff` runs, such a chain's L1 diamond keeps its
  ZiSK bit clear (`ZiskStaysOnWithoutTheBridgehubOwner`), and one that starts with mask `0` and
  a verifier in multi-proof mode for the empty mask keeps mask `0` and keeps reporting
  multi-proof mode (`MultiProofKeptWhileMigrationsDisabled`).
- In the model, which omits its registration and backfill checks, `enableInterop(chainId, req)`
  succeeds exactly for the owner of L1's Bridgehub on a chain not yet enabled, with `req` only if
  the chain's L1 diamond has the flag and reports multi-proof mode, and changes only
  `interopEnabled` (`EnableInteropSucceedsIff`). `MultiProofVerifier` reports multi-proof mode
  exactly for the empty mask (`MultiProofModeIffNothingDisabled`).
- Headline, `protocol-docs/interop-gating.md:26-27` in the source setting: a chain settling on L1
  that is enabled with the requirement while its L1 verifier runs
  `MultiProofVerifier.getProofMode` stays enabled, on its L1 diamond, with the flag, mask `0` and
  multi-proof mode, along every `NoL1OwnerZiskOff` run of modelled calls
  (`EnabledChainStaysMultiProof`). "Both proofs" is read as the proof mode the diamond reports;
  what a verifier's `verify` accepts is outside the model.
- Only a diamond that accepts the chain's batches can take the requirement
  (`AwayDiamondCannotRequire`).
- `isPermanentRollup` is carried by the migration commitment and guarded by the mint
  (`PermanentRollupCarried`), and is kept along every `Tame` run, migrations included, in every
  setting (`PermanentRollupKeptAcrossMigration`).

Witnesses: `RequirementPermanentWitness` (the owner's emergency ZiSK-off makes the L1 diamond
report PLONK mode, the admin's ZiSK-on restores multi-proof mode; the admin's ZiSK-off, a
single-proof upgrade and a migration burn are refused), `MultiProofKeptWitness` (enabling, an
upgrade, an admin handover and a Bridgehub ownership change), `ReturnedChainWitness` (a chain
that also has a gateway diamond, left before the pin, on which the owner of the gateway's
Bridgehub, made its admin, turns ZiSK off), `AwayDiamondCannotRequireWitness`,
`PermanentRollupKeptWitness` (a permanent rollup's round trip to the gateway under the dev
setting `migrationsEnabled = true`).

### Relation to FlagAuthorityV35 and UpgradeGateV35

The one-diamond facts the run results rest on are proved again in this topic's own model, for
each of the chain's two diamonds (`dstep_frame` in `Proofs/MigrationV35.lean`). FlagAuthorityV35
proves them for one diamond, over every `AdminFacet` entry point: the flag is one-way
(`FlagMonotoneStep`, `FlagMonotone`), only `setProofSystemStatus` writes the mask
(`MaskWrittenOnlyBySetStatus`), ZiSK-off on a flagged diamond is the Bridgehub owner's
(`ZiskOffOnFlaggedIsOwners`, `AdminCannotDropSecondProof`), and the second-proof checks of
`enableInterop(_, true)`, once they pass on a diamond with mask `0`, keep passing along its
`AdminSide` runs (`InteropGatePersists`). That a flagged chain's verifier keeps answering
multi-proof mode to `getProofMode(0)` across upgrades is also UpgradeGateV35's
`FlaggedCutsKeepMultiProof` and `FlaggedChainsStayMultiProof`, over `ChainTypeManager`'s
upgrade model. The three models are separate: no statement of one topic is derived from
another's. What MigrationV35 adds is the chain's second diamond, the migration path,
`L1MessageRoot.interopEnabled` and both layers' Bridgehub owners. Each namespace has its own
`ziskBit` (a `UInt8` here and in FlagAuthorityV35, a `ℕ` in UpgradeGateV35).

### Model boundaries

- Each Bridgehub's `chainAssetHandler` and `messageRoot` pointers, and the code of the chain
  asset handlers, `L1MessageRoot` and the Bridgehubs, are fixed along runs: `setAddresses`
  (`core/bridgehub/L1Bridgehub.sol:268-280`, open to the Bridgehub's owner) and proxy upgrades
  of these contracts are not steps (`OPS-CONFIG`). The migration entry points admit whatever
  address that pointer names, so the results with migrations disabled cover runs of the
  modelled calls only. `Cfg.migrationsEnabled` is constant along a run.
- Not modelled: reject-only checks that read no projected field (whitelists, pauses, the
  same-CTM rule, the migration counter, priority mode, deposit pauses, protocol versions,
  `enableInterop`'s registration and backfill checks), the rest of both diamonds' storage, more
  than one gateway, and what a verifier accepts. The run-level results quantify over every
  verifier behaviour (`Env`), every caller and every modelled call their run predicate allows.
