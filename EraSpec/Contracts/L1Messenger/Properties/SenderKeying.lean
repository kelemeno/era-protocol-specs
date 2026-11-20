import EraSpec.Contracts.L1Messenger.Specs.SenderKeying
import EraSpec.Core.Headline

/-!
# Properties: how an L2→L1 message is keyed by its sender

Statements about `EraSpec.Contracts.L1Messenger.Specs.SenderKeying` (era-contracts `draft/v0.35.0` head
`b17415d20`). Proofs are in `EraSpec.Contracts.L1Messenger.Proofs.SenderKeying`.

* `CenterKeyedLogsAreItsWithdrawals` (headline). Under the VM premise `HooksAsDocumented`, along every
  run of one chain from genesis, the logs attributed to the messenger and keyed by
  `L2_INTEROP_CENTER_ADDR` (the only logs `L1InteropHandler._verifyBundle`'s sender check accepts) are
  exactly the message logs of the center's L1 dispatches, `BUNDLE_IDENTIFIER ++ abi.encode(bundle)`, one
  per dispatch, in order; and every dispatched bundle is a one-call, zero-value withdrawal from
  `L2_ASSET_ROUTER_ADDR` (`WithdrawalShape`). The shape conjunct holds by construction: the `withdrawal`
  step takes `WithdrawalShape` as its guard, which models IC:262-264, :552-556, :629-658, :782-822, and
  is the only step that appends to `dispatched`; it is no evidence about the center's code. "Exactly"
  also rests on the model's closure: its five steps are taken to be every writer of the output (Specs
  header). No hash premise: the log's key is the sender's address, padded.
* `SenderKeyingWitness`: the premise holds for documented hooks, and a run with a withdrawal, another
  account's message, a rejected direct hook call and a leaf insert keeps exactly the withdrawal's log.
* `UngatedHookForgesACenterKeyedLog` (countermodel): with a messenger hook that records for every caller
  and otherwise behaves as documented, a direct hook call by an account with no role records a
  center-keyed log of a two-call bundle the center never dispatched.
-/

namespace Contracts.L1MessengerKeying

open Contracts.L1WithdrawalGate

/-- **EVERY CENTER-KEYED LOG IS ONE OF THE CENTER'S WITHDRAWALS, ONE TO ONE.** For every codec, chain and
hook behaviour satisfying `HooksAsDocumented`, along every run from genesis of the modelled steps: the
logs of the output that are attributed to the messenger and keyed by the center are exactly the message
logs of the center's L1 dispatches (`dispatchLog`: the message `BUNDLE_IDENTIFIER ++ abi.encode(bundle)`
from the center), in dispatch order and with multiplicity; and every dispatched bundle has
`WithdrawalShape` (the shape conjunct holds by construction: the withdrawal step takes `WithdrawalShape`
as its guard, which models IC:262-264, :552-556, :629-658, :782-822). -/
@[headline] def Properties.CenterKeyedLogsAreItsWithdrawals : Prop :=
  ∀ (C : Codec) (Q : ChainParams) (H : HookSem) (S : L2State), HooksAsDocumented C H →
    Reach C Q H L2State.init S →
      S.out.filter (fun L => decide (CenterKeyed L)) = S.dispatched.map (dispatchLog C) ∧
        ∀ d ∈ S.dispatched, WithdrawalShape C Q d.bundle

/-- **THE DOCUMENTED HOOKS, ON A RUN.** `wGatedHooks` satisfies `HooksAsDocumented` for `wCodec`. The run
to `wS₄ wGatedHooks` (the center withdraws `wOne`; `wForger` sends a message; `wForger` calls the
messenger hook directly, naming the center; the tree inserts a leaf) is a run of chain `wChain` from
genesis. Its output has three logs, and the center-keyed ones are exactly the withdrawal's. -/
@[witness] def Properties.SenderKeyingWitness : Prop :=
  HooksAsDocumented wCodec wGatedHooks ∧
    Reach wCodec wChain wGatedHooks L2State.init (wS₄ wGatedHooks) ∧
    (wS₄ wGatedHooks).out.length = 3 ∧
    (wS₄ wGatedHooks).out.filter (fun L => decide (CenterKeyed L)) = [dispatchLog wCodec ⟨wOne, 0⟩]

/-- **WITHOUT THE CALLER GATE, A CENTER-KEYED LOG IS FORGED.** `wUngatedHooks` fails the messenger hook's
caller gate and satisfies the other three clauses of `HooksAsDocumented`. The run to
`wS₄ wUngatedHooks` is a run of chain `wChain` from genesis in which the center dispatched only `wOne`;
its output holds the message log of `BUNDLE_IDENTIFIER ++ abi.encode(wTwo)` from the center, recorded by
`wForger`'s direct hook call, and its center-keyed logs are not the dispatches' logs. -/
@[countermodel] def Properties.UngatedHookForgesACenterKeyedLog : Prop :=
  ¬ (∀ c t x, c ≠ l2ToL1MessengerAddr → wUngatedHooks.messengerHook c t x = none) ∧
    (∀ t a m, wUngatedHooks.messengerHook l2ToL1MessengerAddr t (a, m) =
      some (messageLog wCodec t a m)) ∧
    (∀ c t v, c ≠ l2CommitmentTreeAddr → wUngatedHooks.leafHook c t v = none) ∧
    (∀ t v L, wUngatedHooks.leafHook l2CommitmentTreeAddr t v = some L → ¬ CenterKeyed L) ∧
    Reach wCodec wChain wUngatedHooks L2State.init (wS₄ wUngatedHooks) ∧
    (wS₄ wUngatedHooks).dispatched.map (·.bundle) = [wOne] ∧
    messageLog wCodec 2 l2InteropCenterAddr (bundleIdentifier :: wCodec.enc wTwo) ∈
      (wS₄ wUngatedHooks).out ∧
    (wS₄ wUngatedHooks).out.filter (fun L => decide (CenterKeyed L)) ≠
      (wS₄ wUngatedHooks).dispatched.map (dispatchLog wCodec)

end Contracts.L1MessengerKeying
