# NativeTokenVaultBase

These local models cover a fresh representation-token registration projection and
one `NativeTokenVaultBase.bridgeBurn` case: one already registered token on the
non-base, non-native branch, with nonlegacy configured-vault behavior. They build
on the local [BridgedStandardERC20 models](../BridgedStandardERC20/README.md).
They are abstract specifications and do not establish Solidity correspondence.

Review the [layered assumption register](../../../ASSUMPTIONS.md) alongside these
models: `REP-INIT`/`MODEL-FRESH` for registration, `REP-VAULT`/`DEP-FRAME` for
preparation, `MODEL-COMMIT`/`VM-REVERT`/`SOL-CONTROL` for rollback, and
`DEP-RESULTS` for enabledness. Generic safety-refinement composition does not
discharge these concrete obligations.

| Review | File |
|---|---|
| Fresh deployment, initializer, registry installation, and tracker-hook sequence | [Specs/Initialization.lean](Specs/Initialization.lean) |
| Registration invariants, fields, map frame, and hook properties | [Properties/Initialization.lean](Properties/Initialization.lean) |
| Checked registration derivations | [Proofs/Initialization.lean](Proofs/Initialization.lean) |
| Request/state, registry maps, hooks, branch selection, and preparation order | [Specs/RepresentationPreparation.lean](Specs/RepresentationPreparation.lean) |
| Preparation payload, accounting, ledger, and failure properties | [Properties/RepresentationPreparation.lean](Properties/RepresentationPreparation.lean) |
| Router, pause, amount, and asset guard properties | [Properties/PreparationGuards.lean](Properties/PreparationGuards.lean) |
| Checked preparation derivations | [Proofs/RepresentationPreparation.lean](Proofs/RepresentationPreparation.lean) |
| Checked guard derivations | [Proofs/PreparationGuards.lean](Proofs/PreparationGuards.lean) |
| Registry-wide asset registry and escrow ledger (separate model, namespace `Contracts.NativeTokenVault`) | [Specs/RegistryAndEscrow.lean](Specs/RegistryAndEscrow.lean) |
| Registry coherence, solvency, net-flow, and two boundary countermodels | [Properties/RegistryAndEscrow.lean](Properties/RegistryAndEscrow.lean) |
| Checked registry and ledger derivations | [Proofs/RegistryAndEscrow.lean](Proofs/RegistryAndEscrow.lean) |

## Two overlapping models

`RegistryAndEscrow` is a separate, older model in its own namespace,
`Contracts.NativeTokenVault`. It is not built on the `Contracts.NativeTokenVaultBase`
models above. It covers the whole registry (`originChainId`, `tokenAddress`,
`assetId` written by `_setNewTokenStorage`), both registration paths, and the
aggregate `bridgedOut` escrow ledger. The ledger hooks themselves are in
`L1NativeTokenVault.sol` at the same pin. The two models overlap on registration
and the registry maps and use different state types. Unifying them is open.
Neither model's results transfer to the other.

Twelve of its fourteen properties take `IdAssumptions e`, whose `inj` field
asserts that `encodeNTVAssetId` is injective on all (chain, token) pairs of 256-bit
words. No function into 256-bit words can satisfy that, so as stated those twelve
hold vacuously, including the two countermodels. Only `EmptyValid` and
`GuardedInflowIsBacked` are free of it. See `CRYPTO-ID` in the
[assumption register](../../../ASSUMPTIONS.md). The model also treats the vault's
token balance as an exact counter (`MODEL-ESCROW`).

## Invariants and initialization

The vault state separates `LedgerInvariant` from `RepresentationConsistent`.
`LedgerInvariant` is the token's balance-sum, bounded-supply, and zero-address
condition. `RepresentationConsistent` records agreement of the token's vault and
asset identity with the vault config, plus both directions of the registry maps.
`WellFormed` remains a compatibility bundle of the same five top-level conditions:
the ledger invariant and those four representation relationships. Preparation
assumes this bundle; it does not add a production guard for global consistency.

The registration projection establishes both invariants from a fresh deployment
without assuming prior `WellFormed` state or prior agreement with entries being
installed. Fresh proxy storage starts at initializer version 0; the implementation
is modeled at disabled version 255. Token initialization records its caller as the
vault and has no owner/vault caller guard, so the real vault's internal atomic
deployment sequence must supply the intended caller. Initialization preserves
balances and supply; it does not reset the ledger. The zero ledger follows from
fresh storage. The model proves agreement for this newly installed representation,
not a global no-alias property across all assets and tokens.

Registration's asset encoder and deployer are explicit dependencies. The model
checks the deployed address against the expected configured token address after
token initialization. It installs the forward asset-to-token and reverse
token-to-asset maps before calling the tracker hook. The metadata flag represents
success of outer metadata decoding/setup, not truth of every caught name, symbol,
or decimals getter result. The hook is parametric: this development does not prove
tracker registration, tracker migration, or tracker accounting behavior.

This initialization is a projection, not a proof of the full Solidity deployment
mechanism. The vault's origin-chain mapping, token enumeration/index/count, and
metadata contents remain unmodeled. There is no actual ABI encoding, asset-ID hash,
CREATE2/address derivation, transaction rollback, or proxy execution proof here.
It starts with the resolved origin-chain input to the inner helper; earlier
metadata decoding and chain-ID normalization are not proved. The deploy dependency
supplies a genuinely fresh proxy in the model. Equality of identities alone does
not establish nonzero vault/token addresses or all preparation guards.

## Preparation branch and assumptions

Reviewed source context is era-contracts commit
`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`. `InScope` selects the configured
representation-token case for this model; it is not an additional production
requirement that rejects other routes. The preparation model contains one
registered token. Its forward `tokenForAsset` and reverse `assetForToken` maps are
assumed consistent for that token, and the selected token is assumed to have the
genuine standard-token behavior modeled locally.

Preparation calls the accounting hook before burning. The hook receives the
pre-burn token snapshot together with destination chain, asset, and amount. The
origin-token getter and origin chain are checked after burn; the getter is assumed
to return the genuine standard-token field. Metadata is then read from the burned
token snapshot and remains opaque `List UInt8`, with no ABI/byte correspondence
claim.

The returned mint-data tuple contains original caller, remote receiver, origin
token, amount, and metadata. It does not contain asset ID or destination chain;
those remain outer request context in the separate protocol trace model. The source
does not reject a zero receiver in this branch. Successful preparation therefore
does not establish unconditional destination readiness or any later delivery.

`prepare` returns `Option`, and `transact` commits only a successful result.
Failure and rollback statements are laws of this abstract interface, including
failures after a tentative accounting update or token burn. They are not a proof
of EVM atomicity, external-call behavior, or concrete tracker semantics.

## Proven local properties and remaining work

The preparation proofs establish exact source-token debit and supply reduction,
payload-field relationships, preservation of other token balances, use of the
pre-burn accounting snapshot, and the modeled failure law. Guard proofs reject a
wrong router, paused preparation, zero amount, and an asset inconsistent with the
assumed well-formed registry. Registration proofs establish ledger and
representation consistency, initial fields, registry map framing, and the tracker
hook snapshot for a successful modeled registration.
The wrong-initializer-caller countermodel produces an inconsistent representation
from a successful public initializer call, showing why the intended vault caller
is essential. Preparation separately preserves `LedgerInvariant` and
`RepresentationConsistent`, without using one as a premise to prove the other.

These results cover the registration projection and one initialized
representation-token preparation branch. They do not establish router publication,
destination execution, refund, replay protection, unique resolution, or completion
of the first end-to-end bridge milestone. See the
[asset-bridging verification plan](../../../ASSET_BRIDGING_VERIFICATION_PLAN.md)
and [refinement obligations](../../Refinement.lean) for the broader open work.
