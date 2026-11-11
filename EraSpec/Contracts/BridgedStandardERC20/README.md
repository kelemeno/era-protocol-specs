# BridgedStandardERC20

Locally authored token-ledger and fresh-proxy initialization projections. The
operational model covers the initialized, nonzero configured-vault branch; the
initializer model explains how that configuration and a fresh zero ledger are
represented here. Neither model establishes Solidity correspondence.

| Review | File |
|---|---|
| State, successful-call guards, ledger operations, and allowed traces | [Specs/Model.lean](Specs/Model.lean) |
| Exact security/accounting statements | [Properties/Model.lean](Properties/Model.lean) |
| Checked ledger derivations | [Proofs/Model.lean](Proofs/Model.lean) |
| Fresh-proxy initializer projection | [Specs/Initialization.lean](Specs/Initialization.lean) |
| Initialization input, ledger, once-only, and failure properties | [Properties/Initialization.lean](Properties/Initialization.lean) |
| Checked initialization derivations | [Proofs/Initialization.lean](Proofs/Initialization.lean) |

## Source and scope

Reviewed source: era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`,
`l1-contracts/contracts/bridge/BridgedStandardERC20.sol`, and its OpenZeppelin v4
`ERC20Upgradeable` `_mint`, `_burn`, `_transfer`, and initializer behavior. The
inherited before/after transfer hooks are empty. These are local abstract models;
source and compiled-code correspondence has not been established.

Assumption IDs: `MODEL-LEDGER`, `MODEL-FRESH`, `REP-TOKEN`, `REP-INIT`, and the
applicable VM/language/build laws in [the layer register](../../../ASSUMPTIONS.md).
Ledger/initialization theorems are proved locally; the concrete storage, caller,
proxy, and compilation connections are separate open obligations.

The initialization projection distinguishes a fresh proxy at initializer version
0 from a disabled implementation at version 255. It models the initializer as
callable by any caller and records that caller as the configured vault; it has no
owner or vault caller guard. The real deployment sequence must therefore supply
the intended caller through the vault's internal atomic deployment flow. The
initializer preserves balances and total supply rather than resetting them. A
zero ledger follows from fresh proxy storage, not from a ledger-reset operation.
Fresh allocation is an explicit model boundary; no BeaconProxy/deployer storage
semantics have been proved here. Nonzero caller identity in the intended flow
comes from the deployed-vault context, rather than a new initializer guard.

The metadata input is represented by a flag for success of the outer metadata
decode/setup path. It does not assert that each caught name, symbol, or decimals
getter decode succeeds. Constructor-only/nested initializer cases, metadata
contents, events, permit/allowance fields, and proxy execution semantics are not
modeled.

Balances and total supply are natural numbers with an explicit uint256 bound.
`WellFormed` requires the sum of every account's balance to equal total supply,
bounded supply, and a zero balance at the zero address. This accounts for all
160-bit addresses and justifies the nonwrapping arithmetic in the operational
slice.

| Operation | Successful-call conditions | Ledger effect |
|---|---|---|
| `burn` | Nonzero configured vault; caller is that vault; nonzero account; enough balance | Decrease that balance and total supply by exactly the input amount. |
| `mint` | Nonzero configured vault; caller is that vault; nonzero recipient; resulting supply fits uint256 | Increase that balance and total supply by exactly the input amount. |
| `transfer` | Nonzero sender/recipient; enough balance | Debit then credit, preserving supply. Self-transfers leave the ledger unchanged. |

Zero amounts are permitted. `burn` has no allowance requirement. Mint/burn leave
other account balances and vault/origin/asset identity unchanged. Ledger bounds
and accounting are preserved through arbitrary interleavings of these operations.
A one-unit mint/burn roundtrip supplies a non-vacuous execution witness.

## Remaining work

- Legacy zero-vault fallback, constructor-only/nested initializer behavior,
  metadata contents and reinitializers, allowances/permit, events, proxy execution,
  and upgrades.
- Vault authorization linked to actual funded obligations: an authorized mint
  alone does not prove backing or one-time delivery.
- The burn's connection to vault preparation, calldata, publication, and later
  delivery or refund. This slice does not create a cross-chain obligation record.
- Concrete uint256 storage/call/revert behavior, initializer caller flow, and
  transaction rollback corresponding to these local transitions.

Continue review with [Properties/Initialization.lean](Properties/Initialization.lean)
and `Properties.burn_exact`, then the
[native token vault registration and preparation models](../NativeTokenVaultBase/README.md).
