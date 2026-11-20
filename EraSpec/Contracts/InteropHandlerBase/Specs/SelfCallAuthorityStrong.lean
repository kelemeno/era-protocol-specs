import EraSpec.Contracts.InteropHandlerBase.Specs.SelfCallAuthority

/-!
# Model: the self-call relay, from the entry point back to the original sender

Source: era-contracts `draft/v0.35.0` at `b17415d20`, `l1-contracts/contracts/interop/interop-handler/`
(`IHB` = `InteropHandlerBase.sol`, `L1` = `L1InteropHandler.sol`, `L2` = `L2InteropHandler.sol`), and
`l1-contracts/contracts/vendor/draft-InteroperableAddress.sol`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.InteropHandlerBase.Properties.SelfCallAuthorityStrong` and are proved in
`EraSpec.Contracts.InteropHandlerBase.Proofs.SelfCallAuthorityStrong`.

## Why this file exists

`Properties.selfCall_relays_authority` (topic `SelfCallAuthority`) concludes
`∃ ch addr, attrAllows a ch ch addr`, which holds for every attribute (`none` allows anyone; for
`some (ch, addr)` take that `ch` and `addr`). Its premise is discarded, and it never mentions the
inner gate, the self-call, or the original sender. This file models the path the claim is about.

## The code

Two entry points of each handler have a permission gate with a self-call disjunct:

    execute (L1 executeBundle, L2 executeAtomicBundle)
                         _requireExecutionAllowed, IHB:239-255: msg.sender == address(this) ||
                         ((executionChainId == block.chainid || executionChainId == 0)
                          && executionAddress == msg.sender)   (IHB:246-248)
    unbundleBundle       IHB:124-126, the same with unbundlerChainId / unbundlerAddress
    verify (L1 verifyBundle, L2 verifyAtomicBundle)   no permission gate

`msg.sender == address(this)` holds only for calls the handler's own code makes. The handler
calls its own entry points only from `receiveMessage` (`IHB:188-213`), which runs when a delivered
call of an outer bundle targets the handler: `_executeCalls` passes
`sender: InteroperableAddress.formatEvmV1(_sourceChainId, interopCall.from)` (`IHB:378`), the outer
bundle's source chain and the call's `from`. `receiveMessage` requires `msg.sender ==
address(this)` (`IHB:194`), reads the pair back with `parseEvmV1Calldata(sender)` (`IHB:200`), and
dispatches on the payload's selector (`IHB:202-210`):

    execute selector  _receiveExecuteBundle   L1:127-149 / L2:109-131: _requireRescueExecutionAllowed
                                              (IHB:261-278) checks executionAddress against the pair,
                                              then this.executeBundle (L1:148) / this.executeAtomicBundle (L2:130)
    verify selector   _receiveVerifyBundle    L1:152-160 / L2:134-142: this.verifyBundle (L1:159) /
                                              this.verifyAtomicBundle (L2:141), no check
    unbundleBundle    _handleUnbundleBundle   IHB:413-433: checks unbundlerAddress against the pair
                                              (IHB:427-430), then this.unbundleBundle (IHB:432)

`deployedDispatch` is L1's table and `deployedDispatchL2` L2's. The model's `Gated.verifyBundle`
stands for the layer's verify entry point (`verifyAtomicBundle` on L2), which has no gate. At the
pin `c67894b9` the table was L1's on both layers.

## Modelling choices

* **The dispatch table is data** (`Branch`, `deployedDispatch`): each branch names the entry point
  it self-calls and whether its `_handle*` function checks that entry point's attribute against
  the parsed sender first. The results quantify over every table, so they say what an added
  branch — such as one for `executeAtomicBundle` — would do.
  A checked branch is assumed to check its OWN target's attribute (`gateAttr br.target`), so
  "every table" means every table of that shape: a branch that checks the wrong attribute (say
  `unbundlerAddress` before `this.executeBundle`) is not expressible. The deployed table has
  that shape (`L1:127-149`, `L2:109-131`, `IHB:413-433` each check their own target's attribute).
* **A call reaching a gate is either direct or relayed** (`GateCall`). Direct: `msg.sender` is any
  account other than the handler, on this chain. Relayed: `receiveMessage`, on a delivered call
  of an outer bundle from chain `src` with `from = fromAddr`, took one branch of the table.
* **The two ERC-7930 functions are parameters** (`Handler.fmt`, `Handler.parse`). The results that
  need `parseEvmV1Calldata(formatEvmV1(src, from)) = (src, from)` take it for the one pair the
  relay carries (`RoundTripOn`); it is an encoding fact of the library (`SOL-ABI`).
* **The unbundler attribute.** `unbundleBundle` always parses `unbundlerAddress` (`IHB:118-120`), which
  reverts on an empty one, while the model's `none` allows everyone. Allowing more only adds
  admitted calls, so the soundness results hold a fortiori.
* **What is left out.** Which bundle a relayed call names, the proof and the call statuses: the
  results are about who is authorised, not what the call then does.
-/

namespace AttackVectors.SelfCallAuthority

/-- The handler's entry points that a self-call can reach. -/
inductive Gated
  | executeBundle
  | verifyBundle
  | unbundleBundle
  | executeAtomicBundle
  deriving DecidableEq

/-- Whether the entry point has a permission gate: all but `verifyBundle`, which is
permissionless (`L1:103-110`, `L2:83-92`). -/
def Gated.isGated : Gated → Bool
  | .verifyBundle => false
  | _ => true

/-- The two permission attributes of a bundle (`BundleAttributes`, `common/Messaging.sol:224-229`),
parsed: `executionAddress` and `unbundlerAddress`. `none` is an empty attribute. -/
structure BundleAttrs where
  execution : Attr
  unbundler : Attr

/-- The attribute an entry point's gate compares the caller to: `executionAddress` for both
execution entry points, `unbundlerAddress` for `unbundleBundle`, nothing for `verifyBundle`. -/
def gateAttr : Gated → BundleAttrs → Attr
  | .executeBundle, A => A.execution
  | .executeAtomicBundle, A => A.execution
  | .unbundleBundle, A => A.unbundler
  | .verifyBundle, _ => none

/-- One branch of `receiveMessage`'s selector dispatch: the entry point it calls on `this`, and
whether it first checks that entry point's attribute against the parsed sender. -/
structure Branch where
  target : Gated
  checked : Bool
  deriving DecidableEq

/-- **THE DEPLOYED L1 DISPATCH** (`IHB:202-210` with `L1:117-160`): `executeBundle` after
`_receiveExecuteBundle`'s check, `verifyBundle` with none, `unbundleBundle` after
`_handleUnbundleBundle`'s check. No branch reaches `executeAtomicBundle`. -/
def deployedDispatch : List Branch :=
  [⟨.executeBundle, true⟩, ⟨.verifyBundle, false⟩, ⟨.unbundleBundle, true⟩]

/-- **THE DEPLOYED L2 DISPATCH** (`IHB:202-210` with `L2:99-142`): `executeAtomicBundle` after
`_receiveExecuteBundle`'s check (`L2:122-128`), `verifyAtomicBundle` (here `.verifyBundle`) with
none, `unbundleBundle` after `_handleUnbundleBundle`'s check. -/
def deployedDispatchL2 : List Branch :=
  [⟨.executeAtomicBundle, true⟩, ⟨.verifyBundle, false⟩, ⟨.unbundleBundle, true⟩]

/-- The handler's deployment: `block.chainid`, `address(this)`, and the ERC-7930 functions of the
relay — `formatEvmV1(chainid, addr)` (`InteroperableAddress.sol:48-51`), with which
`_executeCalls` builds `sender` (`IHB:378`), and `parseEvmV1Calldata` (`:168-172`), with which
`receiveMessage` reads it (`IHB:200`). -/
structure Handler (Sender : Type) where
  chainId : ℕ
  self : ℕ
  fmt : ℕ → ℕ → Sender
  parse : Sender → ℕ × ℕ

/-- How a call reaches an entry point's gate. -/
inductive GateCall
  /-- `msg.sender = caller`, an account on this chain that is not the handler: a transaction, or
  another contract's call. -/
  | direct (e : Gated) (caller : ℕ)
  /-- The handler's own call: `_executeCalls` of an outer bundle whose `sourceChainId` is `src`
  delivered a call with `from = fromAddr` to the handler, and `receiveMessage` took branch
  `br`. -/
  | relayed (src fromAddr : ℕ) (br : Branch)

/-- The entry point the call reaches. -/
def GateCall.entry : GateCall → Gated
  | .direct e _ => e
  | .relayed _ _ br => br.target

/-- **THE PRINCIPAL ON WHOSE AUTHORITY THE CALL RUNS.** For a direct call, the caller on this
chain. For a relayed call, the ORIGINAL sender of the outer message: the outer bundle's source
chain and the delivered call's `from`. -/
def GateCall.principal {Sender : Type} (H : Handler Sender) : GateCall → ℕ × ℕ
  | .direct _ caller => (H.chainId, caller)
  | .relayed src fromAddr _ => (src, fromAddr)

/-- **EVERY CHECK ON THE PATH PASSES.** A direct call: the caller is not the handler, and the
entry point's gate passes for it (its self-call disjunct is false). A relayed call: the branch is
in the dispatch table; if the branch checks, the attribute allows the pair `parseEvmV1Calldata`
reads from `formatEvmV1(src, fromAddr)`; and the entry point's gate passes — by its self-call
disjunct, since `msg.sender` is the handler. -/
def Admitted {Sender : Type} (H : Handler Sender) (dispatch : List Branch) (A : BundleAttrs) :
    GateCall → Prop
  | .direct e caller =>
      caller ≠ H.self ∧ innerGate (gateAttr e A) H.chainId H.chainId caller (caller = H.self)
  | .relayed src fromAddr br =>
      br ∈ dispatch ∧
      (br.checked = true →
        attrAllows (gateAttr br.target A) (H.parse (H.fmt src fromAddr)).1
          (H.parse (H.fmt src fromAddr)).1 (H.parse (H.fmt src fromAddr)).2) ∧
      innerGate (gateAttr br.target A) H.chainId H.chainId H.self (H.self = H.self)

/-- **THE PRINCIPAL IS AUTHORISED**: the entry point's attribute allows the call's principal,
checked against the principal's own chain. -/
def Authorized {Sender : Type} (H : Handler Sender) (A : BundleAttrs) (c : GateCall) : Prop :=
  attrAllows (gateAttr c.entry A) (c.principal H).1 (c.principal H).1 (c.principal H).2

/-- `parseEvmV1Calldata(formatEvmV1(src, fromAddr)) = (src, fromAddr)`, for the one pair. -/
def RoundTripOn {Sender : Type} (H : Handler Sender) (src fromAddr : ℕ) : Prop :=
  H.parse (H.fmt src fromAddr) = (src, fromAddr)

/-- The ERC-7930 round trip holds for the pair a relayed call carries (a direct call carries
none). -/
def RelayRoundTrips {Sender : Type} (H : Handler Sender) : GateCall → Prop
  | .direct _ _ => True
  | .relayed src fromAddr _ => RoundTripOn H src fromAddr

/-! ## Witness data -/

/-- A handler on chain `1` at address `99` whose sender encoding is the pair itself. -/
def wHandler : Handler (ℕ × ℕ) := ⟨1, 99, Prod.mk, id⟩

/-- A handler whose parser reads every sender as `(1, 7)`. -/
def wMisparsingHandler : Handler (ℕ × ℕ) := ⟨1, 99, Prod.mk, fun _ => (1, 7)⟩

/-- A bundle whose executor and unbundler are address `7` on chain `1`. -/
def wAttrs7 : BundleAttrs := ⟨some (1, 7), some (1, 7)⟩

/-- A bundle whose executor and unbundler are address `42` on any chain. -/
def wAttrs42 : BundleAttrs := ⟨some (0, 42), some (0, 42)⟩

/-- The deployed table with an `executeAtomicBundle` branch added without its check. -/
def withUncheckedAtomicBranch : List Branch := ⟨.executeAtomicBundle, false⟩ :: deployedDispatch

end AttackVectors.SelfCallAuthority
