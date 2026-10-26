# One suite, two implementations: the bridged-token slice

The first experiment of [CODE_GENERATION.md](../CODE_GENERATION.md). The same
tests run against

| Implementation | Source | Build |
|---|---|---|
| **original** | era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`, `l1-contracts/contracts/bridge/BridgedStandardERC20.sol` and its OZ v4 bases, behind an `ERC1967Proxy`, initialized from the vault | solc 0.8.28, evm `prague`, optimizer 9 999 999 runs — the pin's own l1-contracts settings |
| **generated** | [src/generated/BridgedTokenSlice.sol](src/generated/BridgedTokenSlice.sol), emitted from `Codegen.BridgedTokenSlice.program` | same |

## Running

```bash
ERA_CONTRACTS=/path/to/era-contracts scripts/fetch-solidity-deps.sh   # vendors the pinned sources
scripts/emit-solidity.sh --check                                       # emitted files are current
cd solidity && forge test --offline                                    # 512 fuzz seeds
cd solidity && FOUNDRY_PROFILE=ci forge test --offline                 # 4096 fuzz seeds
scripts/mutation-check.sh                                              # the suite is not vacuous
```

`fetch-solidity-deps.sh` reads everything from a local clone and checks each
library against the commit the pin's gitlink names; `vendor/PINS.txt` records
them. Nothing is downloaded.

## The three layers of evidence

| Suite | What it compares | Size |
|---|---|---|
| [TokenSliceSuite.sol](test/TokenSliceSuite.sol) via [TokenSlice.t.sol](test/TokenSlice.t.sol) | Explicit assertions written once, instantiated per implementation: upstream's in-scope tests (marked `upstream:`) with bare `expectRevert()` tightened to exact revert data, plus the boundary list in CODE_GENERATION.md | 28 tests × 2 |
| [Differential.t.sol](test/Differential.t.sol) | Seeded call sequences against both, compared after **every** call on success, raw return/revert bytes, every log (topics, data, emitter is the token), all balances, supply, vault; also checks balances sum to supply | 48 calls × 512 seeds (CI: 4096) |
| [generated/LeanVectors.t.sol](test/generated/LeanVectors.t.sol) via [LeanVectors.t.sol](test/LeanVectors.t.sol) | Sequences run through the **Lean interpreter**; every outcome it computed — revert data, return bytes, logs, all balances and supply after each call — asserted against each implementation | 24 × 40 calls × 2 (339 successes: 176 mints, 89 burns, 74 transfers; 621 reverts covering all 8 revert kinds) |

The first two compare the implementations with each other; they would both pass
if the two shared a bug. The third compares each with the semantics the Lean
proofs are about, so it is the one that tests the emitter boundary `GEN-EMIT`
directly. None of them checks a property nobody stated: they inherit the
intent captured in `Contracts/BridgedStandardERC20/Properties`.

[scripts/mutation-check.sh](../scripts/mutation-check.sh) plants eight realistic
emitter or transcription bugs in the generated contract one at a time — swapped
check order, a strict inequality, a dropped zero-address check, swapped events,
an unchecked supply increment, a wrong error argument, the recipient read before
the debit, a changed message — and requires the suite to fail on each. All eight
are killed.

## Results

All suites pass for both implementations at the pinned settings: on every
covered input the original, the generated contract and the Lean interpreter agree
on success, return and revert bytes, logs and the full observable ledger.

This is test evidence on the covered inputs, not a proof about either Solidity
contract. Gas is not compared: semantic agreement on generously funded calls
says nothing about enabledness under a production gas limit.

## Comparison scope and exclusions

The scope is the initialized, nonzero-vault mint/burn/transfer slice. Every
upstream test in `l1-contracts/test/foundry/l1/unit/concrete/Bridges/BridgedStandardERC20/`
at the pin is either ported above or listed here.

| Upstream test | Reason excluded |
|---|---|
| `OnlyNTV.test_LazyInitSetsDefaultNTVAndAssetId_OnFirstMint` | Zero-vault legacy fallback of `onlyNTV`; not transcribed (the generated vault is a nonzero constructor argument) |
| `Additional.test_bridgeInitialize_*` (8) | Initializer, origin token, asset id and metadata setup are outside the slice; the generated contract has no initializer |
| `InitializeFallbacks.*` (4) | Metadata getter fallbacks (`name`/`symbol`/`decimals`) |
| `ReinitializeGuard.test_Reinitialize_OnlyBeaconOwner_And_VersionPlusOne` | Reinitializer and beacon ownership |
| `Additional.test_decodeString_*`, `test_decodeUint8_*`, `testFuzz_decodeString`, `testFuzz_decodeUint8` (9) | Metadata decoding helpers |
| `Additional.test_l2Bridge_isZeroByDefault` | Deprecated `l2Bridge` getter |
| `Additional.test_approve_and_transferFrom` | Allowances / `transferFrom` / permit |

Ported (9): `test_bridgeMint_mintsTokens`, `test_bridgeMint_increasesTotalSupply`,
`test_bridgeMint_multipleRecipients`, `test_bridgeBurn_burnsTokens`,
`test_bridgeBurn_decreasesTotalSupply`, `test_bridgeBurn_revertsOnInsufficientBalance`,
`test_transfer_works`, `testFuzz_bridgeMint`, `testFuzz_bridgeBurn`, and
`OnlyNTV.test_UnauthorizedSenderReverts_OnMint` on the initialized branch.

Also outside scope, and therefore not claimed equal: storage layout and proxy
compatibility, `ERC1967Upgrade` surface, deployment addresses, gas.
