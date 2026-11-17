# SecondProofSystem

The second-proof-system requirement of a ZKsync OS chain: the one-way flag
`ZKChainStorage.secondProofSystemRequired`, the mask `disabledProofSystems` it guards, the
upgrade check that keeps a multi-proof verifier, `L1MessageRoot.enableInterop`, and the
settlement-layer migration that moves a chain between its diamonds. The folder is named after
the feature; its sources span several contracts (`Admin`, `Migrator` and `Getters` facets,
`ZKChainBase`, `DiamondInit`, `BaseZkSyncUpgrade`, `ChainTypeManager`, the chain asset
handlers, `L1MessageRoot`, `MultiProofVerifier`).

Source: era-contracts branch `draft/v0.35.0` at commit **`b17415d20`**
(`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`). The model was first written at `d9f6789`;
every Solidity file it cites is unchanged between the two commits. `draft/v0.35.0` moves:
re-check the cited lines before relying on the results for a later commit.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those
exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| MigrationV35 | [Specs/MigrationV35.lean](Specs/MigrationV35.lean) | [Properties/MigrationV35.lean](Properties/MigrationV35.lean) | [Proofs/MigrationV35.lean](Proofs/MigrationV35.lean) |

Namespace: `Contracts.SecondProofSystem.MigrationV35`. Statements are
`Contracts.SecondProofSystem.MigrationV35.Properties.*`; each certificate has the same name
without the `Properties` segment.

## What to check

**MigrationV35** (one chain, its L1 diamond and its gateway diamond; model boundary
`MODEL-SECOND-PROOF-MIGRATION` in [ASSUMPTIONS.md](../../../ASSUMPTIONS.md)):

- At the pin `CHAIN_MIGRATIONS_ENABLED = false`, and every burn and mint of the chain asset
  handler reverts (`MigrationBanRefusesEveryMigration`). The failed-departure confirmation is
  not gated.
- With migrations disabled, a chain settling on L1 with the requirement keeps settling on its
  L1 diamond and keeps the requirement; if its L1 verifier reported multi-proof mode for the
  empty mask, the L1 verifier of every state reached still does; and ZiSK-off on the L1 diamond
  succeeds only for the owner of L1's Bridgehub (`RequirementPermanentWhileMigrationsDisabled`).
  Break-glass cuts are excluded. An L1 diamond that starts with mask `0` or the ZiSK bit always
  either has mask `0` and reports multi-proof mode, or has exactly the ZiSK bit set, the
  emergency state (`MultiProofOrZiskOffWhileMigrationsDisabled`).
- If, moreover, no Bridgehub owner turns a proof system off, the ZiSK bit stays clear
  (`ZiskStaysOnWithoutTheBridgehubOwner`), and an L1 diamond that starts with mask `0` keeps
  mask `0` and keeps reporting multi-proof mode (`MultiProofKeptWhileMigrationsDisabled`).
- `enableInterop(chainId, req)` succeeds exactly for the owner of L1's Bridgehub on a chain not
  yet enabled, with `req` only if the chain's L1 diamond has the flag and reports multi-proof
  mode, and changes only `interopEnabled` (`EnableInteropSucceedsIff`). `MultiProofVerifier`
  reports multi-proof mode exactly for the empty mask (`MultiProofModeIffNothingDisabled`).
- Headline, `protocol-docs/interop-gating.md:26-27` in the source: a chain settling on L1 that
  is enabled with the requirement while its L1 verifier runs `MultiProofVerifier.getProofMode`
  stays enabled, on its L1 diamond, with the flag, mask `0` and multi-proof mode, along every
  run without a break-glass cut in which no Bridgehub owner turns a proof system off
  (`EnabledChainStaysMultiProof`). "Both proofs" is read as the proof mode the diamond reports;
  what a verifier's `verify` accepts is outside the model.
- Only a diamond that accepts the chain's batches can take the requirement
  (`AwayDiamondCannotRequire`).
- `isPermanentRollup` is carried by the migration commitment and guarded by the mint
  (`PermanentRollupCarried`), and is kept along every run without a break-glass cut,
  migrations included, in every setting (`PermanentRollupKeptAcrossMigration`).

Witnesses: `RequirementPermanentWitness` (the owner's emergency ZiSK-off makes the L1 diamond
report PLONK mode, the admin's ZiSK-on restores multi-proof mode; the admin's ZiSK-off, a
single-proof upgrade and a migration burn are refused), `MultiProofKeptWitness` (enabling, an
upgrade, an admin handover and a Bridgehub ownership change), `ReturnedChainWitness` (a chain
that also has a gateway diamond, left before the pin), `AwayDiamondCannotRequireWitness`,
`PermanentRollupKeptWitness` (a permanent rollup's round trip to the gateway under the dev
setting `migrationsEnabled = true`).

Not modelled: reject-only checks that read no projected field (whitelists, pauses, the same-CTM
rule, the migration counter, priority mode, deposit pauses, protocol versions,
`enableInterop`'s registration and backfill checks), the rest of both diamonds' storage, more
than one gateway, and what a verifier accepts. The run-level results quantify over every
verifier behaviour (`Env`) and every caller.
