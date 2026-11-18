# SecondProofSystem

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
that commit and replace transitions.

Source: era-contracts branch `draft/v0.35.0` at **`b17415d20`**
(`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`, 2026-11-16). Paths are relative to
`l1-contracts/contracts/`. **The branch moves**: every `file:line` in the spec is at that commit.
Both topics were first written against `d9f678900`; each Specs header records what changed.
The commit is outside the interop pin `c67894b9`.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact
named propositions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| FlagAuthorityV35 | [Specs/FlagAuthorityV35.lean](Specs/FlagAuthorityV35.lean) | [Properties/FlagAuthorityV35.lean](Properties/FlagAuthorityV35.lean) | [Proofs/FlagAuthorityV35.lean](Proofs/FlagAuthorityV35.lean) |
| UpgradeGateV35 | [Specs/UpgradeGateV35.lean](Specs/UpgradeGateV35.lean) | [Properties/UpgradeGateV35.lean](Properties/UpgradeGateV35.lean) | [Proofs/UpgradeGateV35.lean](Proofs/UpgradeGateV35.lean) |

Namespaces: `Contracts.SecondProofSystem.FlagAuthorityV35` and
`Contracts.SecondProofSystem.UpgradeGateV35`. Statements are `<namespace>.Properties.*`; each
certificate has the same name without the `Properties` segment.

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
