# L1Messenger

Source: `contracts/l2-system/zksync-os/L1Messenger.sol` (ZKsync OS, deployed at `0x8008`), with the L1
branch of `interop/InteropCenter.sol`'s `_dispatchBundle`, the hook addresses of
`common/l2-helpers/L2ContractAddresses.sol`, and `protocol-docs/system/system-hooks.md`, at era-contracts
`draft/v0.35.0` head `b17415d20`. At main `70096e2ea` the messenger is `L1MessengerZKOS.sol` with the
same body.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| SenderKeying | [Specs/SenderKeying.lean](Specs/SenderKeying.lean) | [Properties/SenderKeying.lean](Properties/SenderKeying.lean) | [Proofs/SenderKeying.lean](Proofs/SenderKeying.lean) |

Namespace `Contracts.L1MessengerKeying`.

## Sender keying (`SenderKeying`)

`L1InteropHandler._verifyBundle` accepts a message only if L1's inclusion proof names
`L2_INTEROP_CENTER_ADDR` as its sender. The proven log carries that sender as its key, and on L2 the key
is the 20-byte prefix the messenger puts in front of the message before calling the
`L1_MESSENGER_HOOK` (`L1Messenger.sol:44`). So the binding of an L1-proven message to the account that
sent it rests on who can make the hook record a log.

The model is one chain's L2→L1 output, written by the center's L1 dispatches, other accounts' messages,
direct calls of either hook, and bootloader logs. The hooks' behaviour is a parameter. The VM premise
`HooksAsDocumented` is `system-hooks.md:19, :22, :53-55`: the messenger hook records only for the
messenger, and records the message log of the 20-byte sender and the message; the leaf hook records only
for the commitment tree, and its log is not a messenger log keyed by the center. The Solidity constant's
own comment (`L2ContractAddresses.sol:18-19`) states no caller restriction for `L1_MESSENGER_HOOK`.

- `CenterKeyedLogsAreItsWithdrawals`: under the premise, along every run from genesis, the center-keyed
  logs are exactly the logs of the center's L1 dispatches, one per dispatch, in order, and every
  dispatched bundle is a one-call, zero-value withdrawal from `L2_ASSET_ROUTER_ADDR`
  (`WithdrawalShape`). No hash premise.
- `SenderKeyingWitness`: the premise holds for documented hooks, on a run with a withdrawal, another
  account's message, a rejected direct hook call and a leaf insert.
- `UngatedHookForgesACenterKeyedLog`: a messenger hook that records for every caller, and is otherwise as
  documented, lets an account with no role record a center-keyed log of a two-call bundle the center never
  dispatched.

The hooks are ZKsync OS code outside this repository; the premise is not proved here. EraVM chains,
whose messenger is a different contract, are out of scope.
