import EraSpec.Contracts.InteropHandlerBase.Specs.ReentrancyAtHead

/-!
# Model: atomic bundles on the unbundled route at head

Source: era-contracts `main` at **`3605e82`**, with the same handler logic at the upgrade pin
`e561b9cc2` and draft v0.35 (`d9f6789`); see `Specs/ReentrancyAtHead.lean`, whose model this file
uses. Paths are relative to `l1-contracts/contracts/interop/interop-handler/` unless they name
another directory of `l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.InteropHandlerBase.Properties.AtomicUnbundlingAtHead` and are proved in
`EraSpec.Contracts.InteropHandlerBase.Proofs.AtomicUnbundlingAtHead`.

## The finding

At the pin `c67894b9` an atomic bundle had one entry point, `executeAtomicBundle`, which required
`Unreceived` and ran every call or reverted. The register (`REVIEW.md`, the `L2InteropHandler` row)
says "public verify/unbundle routes cannot consume atomic bundles". At head that is false:

    verifyAtomicBundle(bundle, finality)       // L2InteropHandler.sol:73-82: the flow gate, then Verified
    unbundleBundle(bundle, [Executed, Cancelled])   // InteropHandlerBase.sol:113-175

commits call 0 and permanently cancels call 1. It is an ordinary successful path: no hash collision and
no reverting target is needed. `unbundleBundle` has no atomic or flow check (`:113-175`), cancelling
is permanent (a later `Executed` request fails at `:154`; whole execution refuses an `Unbundled`
bundle, `:282-287`), and only the calls requested `Executed` run (`:359-364`). main documents this as
intended (`docs/atomic-interop/03-reference.md:78-80`; `protocol-docs/interop.md:267`;
`protocol-docs/atomicity/security.md:17-24`). Its Safety section (`03-reference.md:147-151`) adds that
nothing is refunded, and that by default the sender, as unbundler, can cancel the leg that pays the
other party.

Nothing is refunded because the flow was finalized: `verifyAtomicBundle` passed
`requireFlowFinalized`, so every leg is in its source chain's commitment tree before the deadline,
and `AtomicFlowManager.authorizeRefund` needs a timeout proof that one leg is absent
(`atomic-interop/AtomicFlowManager.sol:214-244`), which the finality and timeout conditions exclude
(`../../AtomicInteropProof/`). A cancelled call's source-side burn or escrow is therefore never
returned, and its destination effect never happens. That includes base-token value: at head a direct
atomic call may carry value (`interop/InteropCenter.sol:707-709`), released only when the call runs
(`L2InteropHandler.sol:139-144`).

## Who can do it

Unbundling is gated on the bundle's `unbundlerAddress` (`InteropHandlerBase.sol:118-132`; through
`receiveMessage`, `:413-433`). `InteropCenter` defaults it to the sender on the source chain
(`interop/InteropCenter.sol:211-216` for `sendMessage`, `:515-521` for `sendBundle`; `:320-321` is
`previewMessageHash`). The direct gate compares the unbundler's chain with the destination's
`block.chainid`, so with the default the sender cannot call `unbundleBundle` on the destination.
It sends another atomic message from the source chain to the destination handler's
`receiveMessage`, carrying `unbundleBundle(...)`, and any relayer executes it
(`protocol-docs/atomicity/security.md:124-127`). `verifyAtomicBundle` itself is permissionless
(`L2InteropHandler.sol:73-82`, `:130`). The exec model omits these reject-only gates; the last section
below states them on their own.
-/

namespace Contracts.InteropHandlerAtHead

open AttackVectors.BundleStatusMachine (CallStatus)
open Contracts.InteropHandler (Bundle wA)

/-! ## The runs -/

/-- An `unbundleBundle` request for a bundle with `n ≥ 2` calls that executes call 0, cancels call 1
and skips the rest (`InteropHandlerBase.sol:149-164`). -/
def partialRequest (n : ℕ) : List CallStatus :=
  .Executed :: .Cancelled :: List.replicate (n - 2) .Unprocessed

/-- The run that executes a strict subset of bundle `b`: anyone verifies it with a passing flow gate,
then its unbundler executes call 0 and cancels call 1. The one delivered call's target returns. -/
def partialRun (b : Bundle) : List Tx :=
  [⟨1, .verifyAtomicBundle b true, []⟩, ⟨4, .unbundleBundle b (partialRequest b.calls), []⟩]

/-- Atomic execution of `wA` (hash `1`, two calls) with a passing gate, whose call 0 target returns and
whose call 1 target reverts. -/
def wFailingExecute : Tx := ⟨8, .executeAtomicBundle wA true, [.returns, .reverts]⟩

/-- `wA` verified, then unbundled executing call 0 only; call 1 is skipped, so its target is never
called. The one delivered call's target returns. -/
def wSkipFailing : List Tx :=
  [⟨1, .verifyAtomicBundle wA true, []⟩, ⟨4, .unbundleBundle wA [.Executed, .Unprocessed], [.returns]⟩]

/-! ## Who may unbundle

The gates `unbundleBundle` applies, which the exec model omits. -/

/-- An ERC-7930 EVM address as `InteroperableAddress.parseEvmV1` reads it: a chain id, where `0`
matches any chain in these gates (`protocol-docs/interop.md:78`), and an account. -/
structure InteropAddress where
  /-- The chain id; `0` is the chain wildcard. -/
  chain : ℕ
  /-- The account. -/
  account : ℕ
deriving DecidableEq

/-- The unbundler `InteropCenter` writes when the sender sets none: the sender, on the source chain
(`interop/InteropCenter.sol:214-215`, `:519-521`). -/
def defaultUnbundler (sourceChain sender : ℕ) : InteropAddress := ⟨sourceChain, sender⟩

/-- `unbundleBundle`'s gate for a direct call by `caller` on chain `here`, where the handler is `self`
(`InteropHandlerBase.sol:124-132`). -/
def DirectUnbundleAllowed (here self caller : ℕ) (u : InteropAddress) : Prop :=
  caller = self ∨ ((u.chain = here ∨ u.chain = 0) ∧ u.account = caller)

/-- The `receiveMessage` rescue gate (`InteropHandlerBase.sol:423-430`): the wrapped message's sender,
an account on the chain the message came from, against the unbundler. When it passes, the handler
calls `this.unbundleBundle` (`:432`), whose direct gate it passes as `self`. -/
def RescueUnbundleAllowed (sender u : InteropAddress) : Prop :=
  (u.chain = sender.chain ∨ u.chain = 0) ∧ u.account = sender.account

end Contracts.InteropHandlerAtHead
