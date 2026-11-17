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

Source: era-contracts branch `draft/v0.35.0` at **`b17415d20`**
(`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`, 2026-11-16). Paths are relative to
`l1-contracts/contracts/`. **The branch moves**: every `file:line` in the spec is at that commit.
The topic was first written against `d9f678900`; the Specs header records what changed.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact
named propositions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| FlagAuthorityV35 | [Specs/FlagAuthorityV35.lean](Specs/FlagAuthorityV35.lean) | [Properties/FlagAuthorityV35.lean](Properties/FlagAuthorityV35.lean) | [Proofs/FlagAuthorityV35.lean](Proofs/FlagAuthorityV35.lean) |

Namespace: `Contracts.SecondProofSystem.FlagAuthorityV35`. Statements are
`Contracts.SecondProofSystem.FlagAuthorityV35.Properties.*`; each certificate has the same name
without the `Properties` segment.

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

## What to check

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

## Model boundaries

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
