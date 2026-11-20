# L1Messenger

## Headline guarantees

About the ZKsync OS messenger `l2-system/zksync-os/L1Messenger.sol` (at `0x8008`) and the L1 branch of
`InteropCenter._dispatchBundle`, at era-contracts `draft/v0.35.0` head `b17415d20`.

| Guarantee | Premises | Lean name |
|---|---|---|
| On one chain, the L2 → L1 logs attributed to the messenger and keyed by `L2_INTEROP_CENTER_ADDR` are exactly the message logs of the center's L1 dispatches, one per dispatch, in order; every dispatched bundle is a one-call, zero-value withdrawal from `L2_ASSET_ROUTER_ADDR` | the ZKsync OS hooks behave as `protocol-docs/system/system-hooks.md` documents them (`HooksAsDocumented`: the messenger hook records only for the messenger, and records the message log of the 20-byte sender prefix and the message; the leaf hook records only for the commitment tree, and its log is not a messenger log keyed by the center); the run starts at genesis; the model's steps are every source of L2 → L1 logs (`MODEL-L2-MESSAGE-KEYING`). No hash premise | `Contracts.L1MessengerKeying.Properties.CenterKeyedLogsAreItsWithdrawals` |

Witness (`@[witness]`): `SenderKeyingWitness` (documented hooks on a run with a withdrawal, another
account's message, a rejected direct hook call and a leaf insert). Countermodel
(`@[countermodel]`): `UngatedHookForgesACenterKeyedLog` (a messenger hook that records for every
caller lets an account with no role forge a center-keyed log of a bundle the center never sent).
The hooks are ZKsync OS code outside this repository; the premise is not proved here.

## Source and scope

Source: `contracts/l2-system/zksync-os/L1Messenger.sol`, with the L1 branch of
`interop/InteropCenter.sol`'s `_dispatchBundle`, the hook addresses of
`common/l2-helpers/L2ContractAddresses.sol`, and `protocol-docs/system/system-hooks.md`, at
`b17415d20`.

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
  (`WithdrawalShape`). No hash premise. The shape conjunct holds by construction: the withdrawal step
  takes `WithdrawalShape` as its guard, which models `InteropCenter.sol:262-264`, `:552-556`,
  `:629-658`, `:782-822` (argued from source in the Specs header, not transcribed). "Exactly" also rests
  on the model's closure: ZKsync OS writes no other L2→L1 log with sender `0x8008`, i.e. the model's
  steps cover every log source (`MODEL-L2-MESSAGE-KEYING`).
- `SenderKeyingWitness`: the premise holds for documented hooks, on a run with a withdrawal, another
  account's message, a rejected direct hook call and a leaf insert.
- `UngatedHookForgesACenterKeyedLog`: a messenger hook that records for every caller, and is otherwise as
  documented, lets an account with no role record a center-keyed log of a two-call bundle the center never
  dispatched.

The hooks are ZKsync OS code outside this repository; the premise is not proved here. EraVM chains,
whose messenger is a different contract, are out of scope.
