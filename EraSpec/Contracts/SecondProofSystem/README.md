# SecondProofSystem

The v35 second-proof-system requirement: a chain's one-way flag
`s.secondProofSystemRequired`, the `getProofMode` checks that guard it, and the emergency switch
`s.disabledProofSystems`. The code is spread over several contracts, so this folder is named
after the feature: the chain's `Admin` facet (`permanentlyRequireSecondProofSystem`,
`setProofSystemStatus`, `_executeDiamondCut`'s post-cut check), `BaseZkSyncUpgrade._setVerifier`
and `DefaultUpgrade`, `DiamondInit`, the verifiers' `getProofMode`, and the `ChainTypeManager`
paths that commit and replace transitions.

Source: era-contracts branch `draft/v0.35.0` at commit **`b17415d20`**
(`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`, 2026-11-16), outside the interop pin `c67894b9`.
The model was first written at `d9f678900` and re-read against `b17415d20`; the Specs header
records what changed between them. **The branch moves**: every `file:line` quoted in the spec is
at `b17415d20`.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the guarantees
and their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact named
propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| UpgradeGateV35 | [Specs/UpgradeGateV35.lean](Specs/UpgradeGateV35.lean) | [Properties/UpgradeGateV35.lean](Properties/UpgradeGateV35.lean) | [Proofs/UpgradeGateV35.lean](Proofs/UpgradeGateV35.lean) |

Namespace: `Contracts.SecondProofSystem.UpgradeGateV35`. Statements are
`Contracts.SecondProofSystem.UpgradeGateV35.Properties.*`; each certificate has the same name
without the `Properties` segment.

## The model

`UpgradeGateV35` extends `ChainTypeManager`'s `UpgradeTiming` model (written at `e561b9cc2`;
the Specs header lists where each of its checks sits at `b17415d20`) with each chain's flag,
verifier and mask. Every registry cut installs the target release's verifier through both checks
(`VerifierGate`); genesis and migration in start a fresh diamond with the flag unset; a
break-glass cut writes any gate fields, subject to the post-cut check. `getProofMode` and each
release's `verifier()` are configuration; the two deployed verifiers are transcribed. Every cut
is checked as if the v35 Admin facet were routed (`MODEL-SECOND-PROOF-GATE` in
[ASSUMPTIONS.md](../../../ASSUMPTIONS.md)).

## What to check

- **The gate holds.** `FlaggedCutsKeepMultiProof`: after any cut of a flagged chain, its
  verifier answers MULTI to `getProofMode(0)`. `FlagSurvivesAllButBreakGlass`: only a break-glass
  cut of a registered chain clears its flag. `FlaggedChainsStayMultiProof`: along every run, every
  flagged chain's verifier passes the gate, if the verifiers are `MaskMonotone`; both deployed
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

## Model boundaries

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
