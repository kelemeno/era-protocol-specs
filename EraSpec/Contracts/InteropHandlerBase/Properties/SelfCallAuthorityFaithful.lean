import EraSpec.Contracts.InteropHandlerBase.Specs.SelfCallAuthorityFaithful

/-!
# Properties: the self-call delegation relays authority, at the pin and at the upgrade

Statements about `EraSpec.Contracts.InteropHandlerBase.Specs.SelfCallAuthorityFaithful`. Proofs are
in `EraSpec.Contracts.InteropHandlerBase.Proofs.SelfCallAuthorityFaithful`.

These replace the content `SelfCallAuthority.selfCall_relays_authority` was meant to have. That
statement is a tautology (its conclusion holds for every attribute); the ones below quantify over
every call that reaches a permission gate (`Reaches`), so they fail for a handler with an unchecked
or miswired self-call site, and two of them exhibit such handlers.

* **The headline** (`DelegationSoundIffMatched`): for any dispatch table, every call that passes a
  permission gate carries a principal the bundle's attribute admits, **if and only if** each arm
  `receiveMessage` can take checks the attribute its target's gate reads (or the target has no
  gate). So soundness is exactly a property of the dispatch table, which the next two results
  decide for the deployed tables.
* `PinnedDelegationSound`, `UpgradeDelegationSound`: the pin's table and both upgrade tables are
  sound.
* `DirectCallsAreGatedExactly`: for every caller other than the handler, the gate passes exactly
  when the attribute admits `(block.chainid, msg.sender)`. `SelfDisjunctPassesWhateverTheAttribute`:
  for the handler itself it passes whenever the attribute parses, which is why the dispatch has to
  check. `RelayedCallActsForTheMessageSender`: what a relayed call carries.
* `RelayEstablishesTheOriginalHypothesis`: at the pin, every self-call into a gated entry point has
  the original file's hypothesis `checked : attrAllows a senderChain senderChain senderAddr`
  established by the outer handler, for the bundle's own attribute.
* `AtomicSelfDisjunctDeadAtPin`: at the pin no call reaches `executeAtomicBundle` with
  `msg.sender = address(this)`. `AtomicSelfDisjunctLiveAndCheckedAtUpgrade`: at the upgrade one
  does, and the arm that makes it checks first.
* Countermodels: `UncheckedAtomicArmWidensAuthority` (the fourth arm the pin's header warns about)
  and `MiswiredCheckWidensAuthority` (an execute arm checking the unbundler attribute) are unsound,
  each with a concrete principal the attribute does not admit.

The inventory behind `Reaches` (no other way for the handler to call itself) is the model
boundary; `scripts/check-interop-handler-inventory.sh` checks it against the pinned tree.
-/

namespace AttackVectors.SelfCallAuthority.Faithful

/-- **THE DELEGATION IS SOUND EXACTLY WHEN THE DISPATCH IS MATCHED.** For every dispatch table: every
call that passes an entry point's permission gate, whether made directly by any account or by the
handler itself at an arm's self-call site, carries a principal the bundle's attribute admits, if and
only if each arm `receiveMessage` can take checks the attribute its target's gate reads, or its
target has no gate. -/
def Properties.DelegationSoundIffMatched : Prop :=
  ∀ tbl : Table, DelegationSound tbl ↔ Matched tbl

/-- **AT THE PIN, AUTHORITY IS RELAYED, NOT WIDENED.** For the handler at any address on any chain,
every call that passes the gate of `executeBundle`, `unbundleBundle`, `executeAtomicBundle` or
`verifyBundle` carries a principal the bundle's attribute admits: `(block.chainid, msg.sender)` for a
direct call, the rescue message's `(senderChainId, senderAddress)` for one of the three self-calls
(:391, :401, :425). -/
def Properties.PinnedDelegationSound : Prop :=
  ∀ (handler thisChain : ℕ) (gc : GateCall), Reaches pinnedTable handler thisChain gc →
    InnerGate handler thisChain gc.entry.gate gc.attrs gc.sender →
      Admits gc.entry.gate gc.attrs gc.principal

/-- **AND AT THE UPGRADE, ON BOTH LAYERS** (`e561b9cc2`): the L2 table, whose execute arm self-calls
`executeAtomicBundle`, and the L1 table. -/
def Properties.UpgradeDelegationSound : Prop :=
  DelegationSound upgradeL2Table ∧ DelegationSound upgradeL1Table

/-- **A DIRECT CALL IS GATED EXACTLY.** For every caller other than the handler, every gate passes if
and only if the bundle's attribute admits `(block.chainid, msg.sender)`. -/
def Properties.DirectCallsAreGatedExactly : Prop :=
  ∀ (handler thisChain : ℕ) (g : Gate) (a : GateAttrs) (caller : ℕ), caller ≠ handler →
    (InnerGate handler thisChain g a caller ↔ Admits g a (thisChain, caller))

/-- **FOR THE HANDLER ITSELF, THE GATE CHECKS NOTHING.** With `msg.sender = address(this)`, the
execution gate passes whenever its attribute is not unparseable, and the unbundler gate whenever its
attribute parses, whoever the attribute names. -/
def Properties.SelfDisjunctPassesWhateverTheAttribute : Prop :=
  ∀ (handler thisChain : ℕ) (a : GateAttrs),
    (a.execution ≠ .malformed → InnerGate handler thisChain .execution a handler) ∧
    (∀ ch addr, a.unbundler = .evm ch addr → InnerGate handler thisChain .unbundler a handler)

/-- **WHAT A RELAYED CALL CARRIES.** For every table: if `receiveMessage` makes a self-call, its
caller was the handler, the self-call acts for the message's own sender and names the message's
bundle, and it is the target of the arm the selector selects, whose check the sender passed. -/
def Properties.RelayedCallActsForTheMessageSender : Prop :=
  ∀ (tbl : Table) (handler caller : ℕ) (m : Message) (sc : SelfCall),
    dispatch tbl handler caller m = some sc →
      caller = handler ∧ m.sender = some sc.principal ∧ sc.attrs = m.attrs ∧
        ∃ br, m.selector = some (.entry br.selector) ∧ branchFor tbl br.selector = some br ∧
          sc.target = br.target ∧ Admits br.check sc.attrs sc.principal

/-- **THE ORIGINAL HYPOTHESIS, DISCHARGED.** At the pin, every self-call into a gated entry point
satisfies `SelfCallAuthority`'s hypothesis `checked : attrAllows a senderChain senderChain senderAddr`
for the bundle's own attribute `a` and the message's sender: for the execution gate `a` is the
parsed execution address (`none` when empty), for the unbundler gate the parsed unbundler address. -/
def Properties.RelayEstablishesTheOriginalHypothesis : Prop :=
  ∀ (handler caller : ℕ) (m : Message) (sc : SelfCall),
    dispatch pinnedTable handler caller m = some sc →
      (sc.target.gate = .execution → ∃ at' : Attr, sc.attrs.execution.toAttr = some at' ∧
          attrAllows at' sc.principal.1 sc.principal.1 sc.principal.2) ∧
      (sc.target.gate = .unbundler → ∃ ch addr, sc.attrs.unbundler = .evm ch addr ∧
          attrAllows (some (ch, addr)) sc.principal.1 sc.principal.1 sc.principal.2)

/-- **AT THE PIN, `executeAtomicBundle`'S SELF DISJUNCT IS DEAD.** No call reaches
`executeAtomicBundle` with `msg.sender = address(this)`: no arm of the pin's dispatch targets it. -/
def Properties.AtomicSelfDisjunctDeadAtPin : Prop :=
  ∀ (handler thisChain : ℕ) (gc : GateCall), Reaches pinnedTable handler thisChain gc →
    gc.entry = .executeAtomicBundle → gc.sender ≠ handler

/-- **AT THE UPGRADE IT IS LIVE, AND CHECKED FIRST.** With the L2 table, the handler at `0` on chain
`1` receives a self-call into `executeAtomicBundle` acting for `(1, 7)`, the principal the bundle's
execution attribute names; the same request from `(1, 9)` is refused by the arm's check
(`_requireRescueExecutionAllowed`) before any self-call. -/
def Properties.AtomicSelfDisjunctLiveAndCheckedAtUpgrade : Prop :=
  Reaches upgradeL2Table 0 1 ⟨.executeAtomicBundle, wAttrs, 0, (1, 7)⟩ ∧
    dispatch upgradeL2Table 0 0 wAtomicMsgOk = some ⟨.executeAtomicBundle, wAttrs, (1, 7)⟩ ∧
    dispatch upgradeL2Table 0 0 wAtomicMsg = none

/-- **AN UNCHECKED FOURTH ARM WOULD WIDEN AUTHORITY.** With the pin's table plus an arm that
self-calls `executeAtomicBundle` without a check, the delegation is unsound: the handler at `0` on
chain `1` passes `executeAtomicBundle`'s gate for `(1, 9)`, whom the bundle's execution attribute
(naming `(1, 7)`) does not admit. -/
def Properties.UncheckedAtomicArmWidensAuthority : Prop :=
  ¬ DelegationSound uncheckedAtomicTable ∧
    Reaches uncheckedAtomicTable 0 1 ⟨.executeAtomicBundle, wAttrs, 0, (1, 9)⟩ ∧
    InnerGate 0 1 Gate.execution wAttrs 0 ∧ ¬ Admits .execution wAttrs (1, 9)

/-- **SO WOULD A MISWIRED CHECK.** If the execute arm checked the unbundler attribute instead, the
delegation is unsound: `(1, 9)`, the bundle's unbundler, gets `executeBundle` past its gate although
the execution attribute names `(1, 7)`. -/
def Properties.MiswiredCheckWidensAuthority : Prop :=
  ¬ DelegationSound miswiredTable ∧
    Reaches miswiredTable 0 1 ⟨.executeBundle, wAttrs, 0, (1, 9)⟩ ∧
    InnerGate 0 1 Gate.execution wAttrs 0 ∧ ¬ Admits .execution wAttrs (1, 9)

end AttackVectors.SelfCallAuthority.Faithful
