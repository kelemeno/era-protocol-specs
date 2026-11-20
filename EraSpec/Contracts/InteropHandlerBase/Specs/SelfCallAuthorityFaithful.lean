import Mathlib.Tactic
import EraSpec.Contracts.InteropHandlerBase.Specs.SelfCallAuthority

/-!
# Model: the self-call delegation, with the dispatch and every caller of a gate

Source: era-contracts `draft/v0.35.0` at `b17415d20`, `l1-contracts/contracts/interop/interop-handler/`
(`IHB` = `InteropHandlerBase.sol`, `L1` = `L1InteropHandler.sol`, `L2` = `L2InteropHandler.sol`). The
pin `c67894b9`'s table (`pinnedTable`) is kept with its own line numbers: as a list it equals the
`b17415d20` L1 table.

**This file is definitions only.** The statements are in
`EraSpec.Contracts.InteropHandlerBase.Properties.SelfCallAuthorityFaithful` and are proved in
`EraSpec.Contracts.InteropHandlerBase.Proofs.SelfCallAuthorityFaithful`.

## Why a second model

`SelfCallAuthority.selfCall_relays_authority` concludes `∃ ch addr, attrAllows a ch ch addr`. That
holds for every attribute `a` (take `ch, addr` from `a` itself, or `a = none`), so its hypothesis is
never used and the statement cannot tell a sound handler from one with an unchecked self-call site.
What the delegation argument is about is not in it: the gates' `msg.sender == address(this)`
disjunct, `receiveMessage`'s dispatch, and which calls can carry `msg.sender = address(this)` at
all. This file models those three things.

## The code (`b17415d20`)

The permission gates, each with the self disjunct:

    execute (L1 executeBundle L1:81-98, L2 executeAtomicBundle L2:61-78)
                          _requireExecutionAllowed (IHB:239-255):
                          if (executionAddress.length == 0) return;                    // IHB:240-242
                          (chainId, addr) = parseEvmV1(executionAddress);              // IHB:243-245
                          require(msg.sender == address(this) ||
                                  ((chainId == block.chainid || chainId == 0) && addr == msg.sender)) // IHB:246-254
    unbundleBundle        (chainId, addr) = parseEvmV1(unbundlerAddress);              // IHB:118-120
                          require(msg.sender == address(this) ||
                                  ((chainId == block.chainid || chainId == 0) && addr == msg.sender))   // IHB:124-132
    verify (L1 verifyBundle L1:103-110, L2 verifyAtomicBundle L2:83-92)   no permission gate

`parseEvmV1` reverts on bytes that are not an EVM ERC-7930 address, including empty bytes
(`vendor/draft-InteroperableAddress.sol:159-163`, `:95-101`); a chain id of `0` is the wildcard.

`receiveMessage` (IHB:188-213):

    require(msg.sender == address(this));                                              // IHB:194
    require(payload.length >= 4);  selector = bytes4(payload[:4]);                     // IHB:197-198
    (senderChainId, senderAddress) = parseEvmV1Calldata(sender);                       // IHB:200
    if      (selector == _getExecuteBundleSelector()) _receiveExecuteBundle(...)       // IHB:202-203
    else if (selector == _getVerifyBundleSelector())  _receiveVerifyBundle(...)        // IHB:204-205
    else if (selector == this.unbundleBundle.selector) _handleUnbundleBundle(...)      // IHB:206-207
    else revert InvalidSelector(selector);                                             // IHB:208-209

    _receiveExecuteBundle  _requireRescueExecutionAllowed (IHB:261-278):
                           if (executionAddress.length != 0)
                             require((chainId == senderChainId || chainId == 0) && addr == senderAddress)
                           then this.executeBundle (L1:148) / this.executeAtomicBundle (L2:130)
    _receiveVerifyBundle   this.verifyBundle (L1:159) / this.verifyAtomicBundle (L2:141)
    _handleUnbundleBundle  require((chainId == senderChainId || chainId == 0) && addr == senderAddress) // IHB:427-430
                           this.unbundleBundle(bundle, providedCallStatus);            // IHB:432

## The inventory `Reaches` rests on (checked against `b17415d20` by hand)

The handler is `msg.sender` of a call into itself only where its own code calls itself:

* `this.executeBundle` (`L1:148`), `this.verifyBundle` (`L1:159`), `this.executeAtomicBundle`
  (`L2:130`), `this.verifyAtomicBundle` (`L2:141`) and `this.unbundleBundle` (`IHB:432`) are the
  only `this.<function>(` call sites in `interop-handler/*.sol`, each inside a `receiveMessage` arm;
* the only call to any recipient's `receiveMessage` is `_executeCalls`' (`IHB:374-380`), which
  reaches the handler's own `receiveMessage` when a delivered call's target is the handler, passing
  `sender = formatEvmV1(_sourceChainId, interopCall.from)` (`IHB:378`). On L1 the target is pinned to
  `L1_ASSET_ROUTER` (`L1:189-192`), so the L1 handler never calls itself; `Reaches` over-approximates;
* its other external calls go to other contracts: `_proveInclusion` (`L1:227-236`),
  `requireFlowFinalized` (`L2:74`, `:89`), `BaseTokenHolder.give` (`L2:152`, which pays the handler's
  `receive()` with the holder as `msg.sender`) and `BASE_TOKEN_ASSET_ID()` (`L2:158`).

`scripts/check-interop-handler-inventory.sh` checks this inventory on the pin `c67894b9`'s layout
only; at `b17415d20` it was checked by hand (the sites above). That inventory is the model
boundary: `Reaches` has one constructor per kind of caller, and nothing in Lean derives it from the
source.

## Modelling choices

* **An attribute is what `parseEvmV1` makes of it** (`AddrField`): empty, unparseable, or a
  `(chainId, address)` pair. Chain ids and addresses are naturals.
* **A principal is a `(chainId, address)` pair**: `(block.chainid, msg.sender)` for a direct call,
  `(senderChainId, senderAddress)` of the rescue message for a relayed one.
* **The dispatch is a table** (`Table`): one `Branch` per `if` arm, in source order, naming the
  selector it matches, the attribute its handler checks against the message sender (`Gate`), and
  the entry point it then self-calls. The first matching arm is taken (`branchFor`). The tables
  given are `b17415d20`'s L2 and L1 tables (`l2TableAtV35`, `l1TableAtV35`), where the execute and
  verify arms sit behind per-layer hooks, and the pin's (`pinnedTable`, equal to `l1TableAtV35`).
* **Reject-only steps are omitted**: payload decoding, `_getBundleData`'s emptiness and version
  checks, destination context, pause. Omitting a check that can only revert removes no passing
  gate call that the model would otherwise have to cover.
-/

namespace AttackVectors.SelfCallAuthority.Faithful

/-- A principal: a chain id and an address. -/
abbrev Principal := ℕ × ℕ

/-- An ERC-7930 address attribute (`bundleAttributes.executionAddress` or `.unbundlerAddress`) as
`InteroperableAddress.parseEvmV1` reads it. -/
inductive AddrField
  /-- Zero-length bytes. The execution gate skips its check (`IHB:240-242`); `parseEvmV1` reverts on them. -/
  | empty
  /-- Non-empty bytes `tryParseEvmV1` rejects: `parseEvmV1` reverts. -/
  | malformed
  /-- Bytes that parse to `(chainId, addr)`; `chainId = 0` is the chain-agnostic wildcard. -/
  | evm (chain addr : ℕ)
  deriving DecidableEq, Repr

/-- The two attributes the permission gates read. -/
structure GateAttrs where
  /-- `bundleAttributes.executionAddress`. -/
  execution : AddrField
  /-- `bundleAttributes.unbundlerAddress`. -/
  unbundler : AddrField
  deriving DecidableEq, Repr

/-- Which attribute an entry point's permission gate reads. -/
inductive Gate
  /-- The execution gate (`_requireExecutionAllowed`, `IHB:239-255`). -/
  | execution
  /-- The unbundler gate (`IHB:118-132`). -/
  | unbundler
  /-- No permission gate (`verifyBundle`, `L1:103-110`; `verifyAtomicBundle`, `L2:83-92`). -/
  | permissionless
  deriving DecidableEq, Repr

/-- The handler entry points a self-call can reach, at `b17415d20` (L1 and L2) and at the pin. -/
inductive Entry
  | executeBundle
  | verifyBundle
  | unbundleBundle
  | executeAtomicBundle
  /-- L2's verify entry point at `b17415d20` (`L2:83-92`); not at the pin. -/
  | verifyAtomicBundle
  deriving DecidableEq, Repr

/-- The gate each entry point runs. -/
def Entry.gate : Entry → Gate
  | .executeBundle => .execution
  | .executeAtomicBundle => .execution
  | .unbundleBundle => .unbundler
  | .verifyBundle => .permissionless
  | .verifyAtomicBundle => .permissionless

/-- `(chainId == p.1 || chainId == 0) && addr == p.2` on a parsed attribute: the comparison every
gate makes, against `(block.chainid, msg.sender)` (`IHB:246-248`, `:124-126`) or, on the
rescue path, against `(senderChainId, senderAddress)` (`IHB:275`, `:428`). An attribute that does not parse
names nobody. -/
def AddrField.Names : AddrField → Principal → Prop
  | .evm ch a, p => (ch = p.1 ∨ ch = 0) ∧ a = p.2
  | .empty, _ => False
  | .malformed, _ => False

instance AddrField.decNames : (f : AddrField) → (p : Principal) → Decidable (f.Names p)
  | .evm ch a, p => inferInstanceAs (Decidable ((ch = p.1 ∨ ch = 0) ∧ a = p.2))
  | .empty, _ => isFalse fun h => h
  | .malformed, _ => isFalse fun h => h

/-- **What the attribute permits**: the principals a gate of kind `g` is meant to let through. An
empty execution address is permissionless (`IHB:240-242`); the unbundler gate always
parses its attribute. This is the check `_receiveExecuteBundle` (`L1:127-149` / `L2:109-131`) /
`_handleUnbundleBundle` (`IHB:413`) run against
the message sender, so it is also what a dispatch branch establishes. -/
def Admits : Gate → GateAttrs → Principal → Prop
  | .permissionless, _, _ => True
  | .execution, a, p => a.execution = .empty ∨ a.execution.Names p
  | .unbundler, a, p => a.unbundler.Names p

instance decAdmits : (g : Gate) → (a : GateAttrs) → (p : Principal) → Decidable (Admits g a p)
  | .permissionless, _, _ => isTrue trivial
  | .execution, a, p =>
      inferInstanceAs (Decidable (a.execution = .empty ∨ a.execution.Names p))
  | .unbundler, a, p => inferInstanceAs (Decidable (a.unbundler.Names p))

/-- **The inner gate as deployed**, for the handler at address `handler` on chain `thisChain`, at
`msg.sender = sender`: the self disjunct, then the attribute check against
`(block.chainid, msg.sender)`. The parse precedes the `require`, so an unparseable attribute reverts
even for a self-call; the execution gate is skipped when its attribute is empty. -/
def InnerGate (handler thisChain : ℕ) : Gate → GateAttrs → ℕ → Prop
  | .permissionless, _, _ => True
  | .execution, a, sender =>
      match a.execution with
      | .empty => True
      | .malformed => False
      | .evm ch addr => sender = handler ∨ ((ch = thisChain ∨ ch = 0) ∧ addr = sender)
  | .unbundler, a, sender =>
      match a.unbundler with
      | .evm ch addr => sender = handler ∨ ((ch = thisChain ∨ ch = 0) ∧ addr = sender)
      | .empty => False
      | .malformed => False

/-- The first four bytes of a rescue payload: a handler entry point's selector, or another value. -/
inductive Selector
  | entry (e : Entry)
  | other (n : ℕ)
  deriving DecidableEq, Repr

/-- A `receiveMessage(receiveId, sender, payload)` call (`IHB:188-193`), as the dispatch reads it. -/
structure Message where
  /-- `parseEvmV1Calldata(sender)` (`IHB:200`); `none` when it reverts. `_executeCalls`, the only caller
  (see the header), passes `formatEvmV1(_sourceChainId, interopCall.from)` (`IHB:378`). -/
  sender : Option Principal
  /-- `bytes4(payload[:4])` (`IHB:198`); `none` when `payload.length < 4` (`IHB:197`). -/
  selector : Option Selector
  /-- The gate attributes of the bundle the payload carries (`_getBundleData`, `L1:139`, `L2:121`, `IHB:421`). -/
  attrs : GateAttrs
  deriving DecidableEq, Repr

/-- One arm of `receiveMessage`'s `if / else if` chain. -/
structure Branch where
  /-- The selector the arm matches. -/
  selector : Entry
  /-- The attribute its handler checks against the message's sender before the self-call. -/
  check : Gate
  /-- The entry point it then calls as `this.<entry>(…)`, so with `msg.sender = address(this)`. -/
  target : Entry
  deriving DecidableEq, Repr

/-- A dispatch: the arms in source order. -/
abbrev Table := List Branch

/-- The arm `receiveMessage` takes on a selector: the first that matches, if any (none reverts with
`InvalidSelector`, `IHB:208-209`). -/
def branchFor (tbl : Table) (sel : Entry) : Option Branch :=
  tbl.find? fun br => decide (br.selector = sel)

/-- **The pin `c67894b9`'s dispatch** (its `InteropHandlerBase.sol:351-359`; the line numbers in this
definition are the pin's). As a list it is `l1TableAtV35`, the `b17415d20` L1 dispatch, so the
statements about it are also statements about `b17415d20`'s L1 handler. -/
def pinnedTable : Table :=
  [ -- :351-352 -> _handleExecuteBundle: check :379-389, `this.executeBundle` :391
    ⟨.executeBundle, .execution, .executeBundle⟩,
    -- :353-354 -> _handleVerifyBundle: no check, `this.verifyBundle` :401
    ⟨.verifyBundle, .permissionless, .verifyBundle⟩,
    -- :355-356 -> _handleUnbundleBundle: check :415-423, `this.unbundleBundle` :425
    ⟨.unbundleBundle, .unbundler, .unbundleBundle⟩ ]

/-- **The `b17415d20` L2 dispatch** (`IHB:202-210` with `L2:99-142`; first transcribed at
`e561b9cc2`, every line re-checked at `b17415d20`): the execute arm self-calls
`executeAtomicBundle`. -/
def l2TableAtV35 : Table :=
  [ -- `_getExecuteBundleSelector()` = executeAtomicBundle (L2:99-101) -> `_receiveExecuteBundle`:
    -- `_requireRescueExecutionAllowed` (L2:122-128, IHB:261-278), `this.executeAtomicBundle` L2:130
    ⟨.executeAtomicBundle, .execution, .executeAtomicBundle⟩,
    -- `_getVerifyBundleSelector()` = verifyAtomicBundle (L2:104-106) -> `this.verifyAtomicBundle` L2:141
    ⟨.verifyAtomicBundle, .permissionless, .verifyAtomicBundle⟩,
    -- IHB:206-207 -> `_handleUnbundleBundle`: check IHB:427-430, `this.unbundleBundle` IHB:432
    ⟨.unbundleBundle, .unbundler, .unbundleBundle⟩ ]

/-- **The `b17415d20` L1 dispatch** (`IHB:202-210` with `L1:117-160`; first transcribed at
`e561b9cc2`, every line re-checked at `b17415d20`). -/
def l1TableAtV35 : Table :=
  [ -- executeBundle (L1:117-119) -> `_requireRescueExecutionAllowed` (L1:140-146), `this.executeBundle` L1:148
    ⟨.executeBundle, .execution, .executeBundle⟩,
    -- verifyBundle (L1:122-124) -> `this.verifyBundle` L1:159
    ⟨.verifyBundle, .permissionless, .verifyBundle⟩,
    ⟨.unbundleBundle, .unbundler, .unbundleBundle⟩ ]

/-- **The change the pin's header warns about**: a fourth arm that self-calls
`executeAtomicBundle` before anyone writes its permission check. -/
def uncheckedAtomicTable : Table :=
  pinnedTable ++ [⟨.executeAtomicBundle, .permissionless, .executeAtomicBundle⟩]

/-- A copy-paste slip of the same kind: the execute arm checks the unbundler attribute. -/
def miswiredTable : Table :=
  [⟨.executeBundle, .unbundler, .executeBundle⟩,
    ⟨.verifyBundle, .permissionless, .verifyBundle⟩,
    ⟨.unbundleBundle, .unbundler, .unbundleBundle⟩]

/-- A self-call `receiveMessage` makes: the entry point, the bundle's gate attributes, and the
principal it acts for. -/
structure SelfCall where
  target : Entry
  attrs : GateAttrs
  principal : Principal
  deriving DecidableEq, Repr

/-- **`receiveMessage`** (`IHB:188-213`) on the handler at `handler`, called by `caller`: the self-call it
makes, or `none` when it reverts. -/
def dispatch (tbl : Table) (handler caller : ℕ) (m : Message) : Option SelfCall :=
  if caller = handler then
    match m.selector, m.sender with
    | some (.entry sel), some p =>
        match branchFor tbl sel with
        | some br => if Admits br.check m.attrs p then some ⟨br.target, m.attrs, p⟩ else none
        | none => none
    | _, _ => none
  else none

/-- A call arriving at an entry point's permission gate. -/
structure GateCall where
  /-- The entry point called. -/
  entry : Entry
  /-- The gate attributes of the bundle it names. -/
  attrs : GateAttrs
  /-- `msg.sender`. -/
  sender : ℕ
  /-- Whose authority the call carries. -/
  principal : Principal
  deriving DecidableEq, Repr

/-- **The inventory: every call the handler at `handler` on chain `thisChain` receives at an entry
point.** Either an account other than the handler calls it, carrying `(thisChain, caller)`; or
`receiveMessage`, called by anyone, makes the self-call of one of its arms, carrying the message's
sender. `receiveMessage` itself refuses every caller but the handler (`IHB:194`), so in the second case
the caller is the handler delivering one of its bundles' calls (`IHB:374`). -/
inductive Reaches (tbl : Table) (handler thisChain : ℕ) : GateCall → Prop
  | direct (e : Entry) (a : GateAttrs) (caller : ℕ) (hne : caller ≠ handler) :
      Reaches tbl handler thisChain ⟨e, a, caller, (thisChain, caller)⟩
  | relayed (caller : ℕ) (m : Message) (sc : SelfCall)
      (hd : dispatch tbl handler caller m = some sc) :
      Reaches tbl handler thisChain ⟨sc.target, sc.attrs, handler, sc.principal⟩

/-- **The delegation is sound for `tbl`**: every call that passes an entry point's permission gate
carries a principal the bundle's attribute admits. -/
def DelegationSound (tbl : Table) : Prop :=
  ∀ (handler thisChain : ℕ) (gc : GateCall), Reaches tbl handler thisChain gc →
    InnerGate handler thisChain gc.entry.gate gc.attrs gc.sender →
      Admits gc.entry.gate gc.attrs gc.principal

/-- **A table is matched** when each arm `receiveMessage` can take checks the attribute its target's
gate reads, or its target has no gate. An arm shadowed by an earlier one with the same selector is
never taken, so it is not constrained. -/
def Matched (tbl : Table) : Prop :=
  ∀ br ∈ tbl, branchFor tbl br.selector = some br →
    br.check = br.target.gate ∨ br.target.gate = .permissionless

instance (tbl : Table) : Decidable (Matched tbl) := by
  unfold Matched; infer_instance

/-- The original model's attribute for a parsed field: `none` when empty (permissionless). An
unparseable field has none. -/
def AddrField.toAttr : AddrField → Option Attr
  | .empty => some none
  | .malformed => none
  | .evm ch a => some (some (ch, a))

/-! ## Witness data -/

/-- An execution attribute naming `(1, 7)` and an unbundler attribute naming `(1, 9)`. -/
def wAttrs : GateAttrs := ⟨.evm 1 7, .evm 1 9⟩

/-- A rescue message from `(1, 9)` asking for `executeAtomicBundle` on a bundle with `wAttrs`. -/
def wAtomicMsg : Message := ⟨some (1, 9), some (.entry .executeAtomicBundle), wAttrs⟩

/-- The same request from `(1, 7)`, the principal `wAttrs` names for execution. -/
def wAtomicMsgOk : Message := ⟨some (1, 7), some (.entry .executeAtomicBundle), wAttrs⟩

/-- A rescue message from `(1, 9)` asking for `executeBundle` on a bundle with `wAttrs`. -/
def wExecMsg : Message := ⟨some (1, 9), some (.entry .executeBundle), wAttrs⟩

end AttackVectors.SelfCallAuthority.Faithful
