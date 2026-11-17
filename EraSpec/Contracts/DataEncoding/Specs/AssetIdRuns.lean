import EraSpec.Contracts.DataEncoding.Specs.AssetId

/-!
# Spec: the router's and the vault's results, with keccak in place of the abstract id hash

This topic adds no definitions. It instantiates the router model
(`Contracts.AssetRouter`, `AssetRouterBase/Specs/HandlerRegistration.lean` and
`HandlerRegistrationRuns.lean`) with `enc := routerEnc keccak`, and the vault registry model
(`Contracts.NativeTokenVault`, `NativeTokenVaultBase/Specs/RegistryAndEscrow.lean`) with
`e := vaultEnc keccak`, both from `Specs/AssetId.lean`.

Statements are in `EraSpec.Contracts.DataEncoding.Properties.AssetIdRuns`, proofs in
`EraSpec.Contracts.DataEncoding.Proofs.AssetIdRuns`.

## What changes at byte level

Those models state their hash-dependent results in two ways: with a bounded premise
(`IdInjOn enc S`, `IdAssumptionsOn e S`) or with a disjunct "these two ids are equal". At
byte level both become statements about keccak alone:

* the bounded premise holds iff keccak has no collision (and, for the vault, no zero
  preimage) among the 96-byte preimages of `S` (`Properties.RouterIdInjOnIffNoCollision`,
  `Properties.VaultIdAssumptionsOnIffNoKeccakEvent`);
* two ids of distinct arguments are equal only through a keccak collision on the two named
  preimages (`Properties.RouterIdClashIsNamedCollision`).

So each result can be restated in reduction form: the conclusion holds, or keccak has a
collision (or a zero preimage) among byte strings the run itself names. For a run, the named
set is the triples or pairs its logged calls hashed (`loggedTriples`, `registeredPairs`),
plus the one triple the statement watches. That is R3's missing reduction-style form, and the
byte-level discharge of `CRYPTO-ID` for these results.

## Model boundaries

Those of the two models, unchanged; and those of `Specs/AssetId.lean` (keccak arbitrary,
the ABI layout from the specification).
-/
