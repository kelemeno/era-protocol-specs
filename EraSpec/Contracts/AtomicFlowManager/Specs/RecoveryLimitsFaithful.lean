import EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryLimits
import EraSpec.Contracts.InteropCenter.Specs.Dispatch

/-!
# Model: what the pinned refund loop calls — the source-chain code at `InteropCall.to`

Source: era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af` (`contracts/` below is
`l1-contracts/contracts/`). The repair is read at `e561b9cc2` (`feat/upgrade-simplification`, a
moving branch outside the source pin; see PROVENANCE.md).

**This file is definitions only.** The statements are in
`EraSpec.Contracts.AtomicFlowManager.Properties.RecoveryLimitsFaithful` and are proved in
`EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryLimitsFaithful`.

## The gap this file closes

`AttackVectors.RecoveryLimits` (`Specs/RecoveryLimits.lean`) reasons about a list of
`Outcome`s. Its Limit 2 frames `reverts` as a target "that REVERTS rather than returning
`false`", that is, as an `IAtomicRecoverable` implementer that misbehaves. It never records
*which contract* produces an outcome. The pinned loop (`atomic-interop/AtomicFlowManager.sol:219-230`)
is

    InteropCall memory c = _bundle.calls[i];
    if (IAtomicRecoverable(c.to).recoverAtomicCall(destChainId, c.data)) { ++recovered; }

and it runs inside `claimRefund` (`:165-180`), on the leg's SOURCE chain. `c.to` is whatever
`_processCallStarter` (`interop/InteropCenter.sol:701-751`) wrote:

* for a direct call, `to: recipientAddress` (`:745`): the recipient on the DESTINATION chain;
* for an indirect call, `to: actualCallRecipient` (`:736`), the recipient the indirect sender
  returned. The L2 asset router returns
  `_chainId == L1_CHAIN_ID ? address(L1_ASSET_ROUTER) : request.l2Contract`
  (`bridge/asset-router/L2AssetRouter.sol:336`), and `request.l2Contract` is
  `_l2AssetRouterAddress(_) = L2_ASSET_ROUTER_ADDR` (`bridge/asset-router/AssetRouterBase.sol:365,
  374-376`). For an L2 destination that is the router itself, which exists on the source chain.
  For an L1 destination it is the L1 router's address.

So for a direct call the manager calls, on the source chain, an address that was chosen on
another chain. If nothing runs there, the call returns no data. The 0.8.28 decoder of the `bool`
return value then reverts, and since nothing catches it, the whole claim reverts.
`_validateAtomicBundle` (`InteropCenter.sol:670-677`) rejects only nonzero `value`, and
`_dispatchBundle` (`:646-655`) rejects neither direct calls nor an L1 destination. A zero-value
direct call is the "flipping a flag" call that `AtomicFlowManager.sol:208-211` says
"legitimately return[s] `false`", and that `InteropCenter.sol:663-665` and
`IAtomicRecoverable.sol:13-15` say a bundle may mix with recoverable calls. Such a call therefore
makes its leg unrefundable for as long as its recipient has no conforming code on the source
chain. The same holds for an indirect call through a sender other than the router (the pin does
not restrict indirect senders) whose returned recipient exists only on the destination.

At `e561b9cc2` the hazard is named and closed. `_recoverBundle` (`AtomicFlowManager.sol:288-321`)
probes only calls with `c.from == L2_ASSET_ROUTER_ADDR`. Any other `from` is "a direct call's
sender (possibly an EOA, which must not be probed — the revert would take down the whole claim)"
(`:302-304`). It ignores the answer, no longer requires a recovery, refunds a non-router call's
`value` through the router (`:312-319`), and requires `destChainId != L1_CHAIN_ID` (`:295`). The
center rejects atomic bundles to L1 (`InteropCenter.sol:550-554`, `AtomicBundleToL1NotSupported`)
and pins indirect calls to the router (`:657-666`).

## What is modelled

* **One external call** (`SourceChain`, `SourceChain.call`). `runsCode` says whether a CALL to an
  address runs any code in the current world. `exec` says what that code does with the manager's
  `recoverAtomicCall(destChainId, data)`: revert, or return bytes and a new world. An account that
  runs no code accepts the call, executes nothing, changes nothing (the manager sends no value)
  and returns no data. Such an account is an EOA, or an address with nothing deployed on THIS
  chain. That is the EVM's rule. On EraVM an account without deployed code runs the default
  account, whose fallback likewise executes nothing and returns no data
  (`system-contracts/contracts/DefaultAccount.sol:265-270`) (`VM-CALL`). A contract that does run
  but has no `recoverAtomicCall` reverts in its dispatcher (`exec` gives `reverted`), or runs a
  fallback that returns nothing (`exec` gives `returned []`, and the decoder reverts).
* **The return-value decoder** (`decodeBool`). Solidity 0.8.28 with ABI coder v2 reverts on fewer
  than 32 bytes of return data, and on a first word other than `0` or `1`. Trailing bytes are
  ignored. Since 0.8.10 the `extcodesize` pre-check is skipped for a call whose return data is
  decoded, so the decoder is what reverts on an empty account. With the pre-check the call would
  revert one step earlier, with the same outcome (`SOL-ABI`, `SOL-CONTROL`).
* **The pinned loop** (`pinnedProbe`, `recoverLoop`, `claimRefundPinned`). It covers the calls in
  order on the threaded world, with no `try/catch`, plus the `recovered == 0` revert (`:229`) and
  `claimRefund`'s `Revertable` gate (`:169-170`). A revert of the claim is `none`: the leg stays
  `Revertable` and nothing the loop did persists (`VM-REVERT`). `outcomes` reads a run as
  `AttackVectors.RecoveryLimits.Outcome`s, so that file's acceptance rule applies to it.
* **The repaired loop at `e561b9cc2`** (`upgradeStep`, `upgradeLoop`, `claimRefundUpgrade`). It
  covers the router probe for `from == router` only, the base-token refund as an abstract router
  step `baseRecover`, no recovery count, and the L1 `require`.
* **Bundles and their formation** are `Contracts.InteropCenter`'s (`MODEL-CENTER`):
  `InteropCall.target` is `to`, `fromAddr` is `from`, and `FormsCall` pins a direct call's `to` to
  the starter's recipient. `routerIndirectRecipient` is the router's choice of `to`.
* **Not modelled.** Gas: an out-of-gas callee is one more `reverted`. Events. The proof checks of
  `authorizeRefund`: `Contracts.InteropCenter.Step.authorize` omits them, so the witness leg reaches
  `Revertable` in that model only. Which bundle bytes a claimant presents: the claim is stated for
  the bundle presented, and a different bundle with the same hash needs a bundle-hash collision
  (`Contracts.InteropCenter.ClaimedBundleValidatedOrCollision`). Any real target's code beyond its
  answers.
-/

namespace Contracts.AtomicFlowManager.RecoveryLimitsFaithful

open AttackVectors.RecoveryLimits (Outcome)
open Contracts.InteropCenter (Address Word InteropCall Bundle CallStarter)

/-! ## One external call on the source chain -/

/-- What one external call returns to its caller: it reverted (and its own effects are undone),
or it returned the bytes `data` and left the world in state `post`. -/
inductive CallResult (W : Type) where
  | reverted
  | returned (data : List UInt8) (post : W)

/-- The source chain, as the manager's recovery calls see it. `W` is the rest of the world: the
storage, balances and deployed code of every contract the calls may touch. -/
structure SourceChain (W : Type) where
  /-- A CALL to `a` in world `w` runs code: a deployed contract, a precompile or system contract,
  or an account that delegates to code. `false` for an empty account: an EOA, or an address with
  nothing deployed on this chain. -/
  runsCode : W → Address → Bool
  /-- What the code at `a` does with `recoverAtomicCall(destChainId, data)` sent by the manager
  with no value. It is read only where `runsCode w a`. -/
  exec : W → Address → Word → List UInt8 → CallResult W

variable {W : Type}

/-- The external call `IAtomicRecoverable(a).recoverAtomicCall(dest, data)` (`VM-CALL`). An account
that runs no code accepts it, executes nothing, changes nothing and returns no data. -/
def SourceChain.call (S : SourceChain W) (w : W) (a : Address) (dest : Word) (data : List UInt8) :
    CallResult W :=
  if S.runsCode w a = true then S.exec w a dest data else .returned [] w

/-- The ABI encoding of a `bool` return value: one 32-byte big-endian word, `0` or `1`. -/
def abiBool (b : Bool) : List UInt8 := List.replicate 31 0 ++ [if b then 1 else 0]

/-- Solidity 0.8.28's decoding of a `bool` return value (ABI coder v2). The first 32 bytes must be
the word `0` or `1`. Fewer than 32 bytes, or any other word, make the caller revert (`none`). Bytes
after the first word are ignored. -/
def decodeBool (rd : List UInt8) : Option Bool :=
  if rd.take 32 = abiBool false then some false
  else if rd.take 32 = abiBool true then some true
  else none

/-- A high-level call of `recoverAtomicCall` on `a`, followed by the decoding of its `bool`. `none`
is a revert of the caller. Otherwise the result is the world after the call and the answer. -/
def probeAt (S : SourceChain W) (dest : Word) (w : W) (a : Address) (data : List UInt8) :
    Option (W × Bool) :=
  match S.call w a dest data with
  | .reverted => none
  | .returned rd w' => (decodeBool rd).map fun b => (w', b)

/-! ## The pinned loop (c67894b9) -/

/-- One iteration of the pinned `_recoverBundle` (`AtomicFlowManager.sol:224-227`):
`IAtomicRecoverable(c.to).recoverAtomicCall(destChainId, c.data)`, so the call goes to `c.to`. -/
def pinnedProbe (S : SourceChain W) (dest : Word) (w : W) (c : InteropCall) : Option (W × Bool) :=
  probeAt S dest w c.target c.data

/-- The loop of `_recoverBundle` (`AtomicFlowManager.sol:223-228`). It takes the calls in order,
each on the world the previous one left, with no `try/catch`. `some (w, n)` counts the calls that
answered `true`. -/
def recoverLoop (step : W → InteropCall → Option (W × Bool)) :
    W → List InteropCall → Option (W × ℕ)
  | w, [] => some (w, 0)
  | w, c :: cs =>
    match step w c with
    | none => none
    | some (w', b) =>
      match recoverLoop step w' cs with
      | none => none
      | some (w'', n) => some (w'', (if b then 1 else 0) + n)

/-- The outcomes the loop produces on the threaded world, as `AttackVectors.RecoveryLimits` names
them. The list stops at the first revert. -/
def outcomes (step : W → InteropCall → Option (W × Bool)) : W → List InteropCall → List Outcome
  | _, [] => []
  | w, c :: cs =>
    match step w c with
    | none => [Outcome.reverts]
    | some (w', b) => (if b then Outcome.recovered else Outcome.declined) :: outcomes step w' cs

/-- The pinned `claimRefund` of the leg whose bundle is `b`, when the leg is in state `s`
(`AtomicFlowManager.sol:165-180`). It is enabled only on a `Revertable` leg (`:169-170`). The leg
is set `Reverted` before the loop (`:175`), and the loop must recover at least one call (`:229`).
`none` is a revert of the whole transaction: the leg stays `s` and nothing the loop did persists. -/
def claimRefundPinned (S : SourceChain W) (s : LegState) (w : W) (b : Bundle) :
    Option (LegState × W) :=
  if s ≠ .Revertable then none else
  match recoverLoop (pinnedProbe S b.destinationChainId) w b.calls with
  | none => none
  | some (w', n) => if n = 0 then none else some (.Reverted, w')

/-! ## Predicates used by the statements -/

/-- No world of the source chain runs code at `a`. Examples are an EOA that never delegates to
code, and an address that only the destination chain deployed to. -/
def NeverRunsCode (S : SourceChain W) (a : Address) : Prop := ∀ w, S.runsCode w a = false

/-- The code at `a` meets `IAtomicRecoverable` in every world (`IAtomicRecoverable.sol:13-15`): it
runs, and it answers every `recoverAtomicCall` with a well-formed `bool` instead of reverting. -/
def Conforms (S : SourceChain W) (a : Address) : Prop :=
  ∀ w dest data, S.runsCode w a = true ∧ ∃ b w', S.exec w a dest data = .returned (abiBool b) w'

/-- In every world, the code at `a` recovers `data` for destination `dest`: it answers `true`. -/
def AlwaysRecovers (S : SourceChain W) (a : Address) (dest : Word) (data : List UInt8) : Prop :=
  ∀ w, ∃ w', S.exec w a dest data = .returned (abiBool true) w'

/-! ## The router's indirect recipient, and the L1-destination checks -/

/-- The recipient `L2AssetRouter.initiateIndirectCall` returns for destination `dest`
(`L2AssetRouter.sol:336`, with `request.l2Contract = L2_ASSET_ROUTER_ADDR`,
`AssetRouterBase.sol:365, 374-376`). It is the L1 asset router for an L1 destination, and
otherwise the L2 asset router, which has the same address on every chain. -/
def routerIndirectRecipient (l1ChainId : Word) (l1AssetRouter l2AssetRouter : Address)
    (dest : Word) : Address :=
  if dest = l1ChainId then l1AssetRouter else l2AssetRouter

/-- The pinned send-time checks on an L1 destination. `_ensureValidDestination`
(`InteropCenter.sol:378-386`) requires exactly one call starter, and `_sendBundle` (`:520-538`)
requires it to be indirect, through the L2 asset router, with zero `interopCallValue`. Nothing at
the pin rejects the `atomicBundle` attribute for an L1 destination: `parseAttributes` (`:843-854`)
and `_parseAtomicSend` (`:874-883`) read no destination, and the atomic branch of
`_dispatchBundle` (`:646-655`) adds only `_validateAtomicBundle`. -/
def PinnedL1SendChecks (l1ChainId : Word) (l2AssetRouter : Address) (dest : Word)
    (starters : List CallStarter) : Prop :=
  dest = l1ChainId → starters.length = 1 ∧
    ∀ cs ∈ starters, cs.callAttributes.indirectCall = true ∧ cs.target = l2AssetRouter ∧
      cs.callAttributes.interopCallValue = 0

/-- The destination check `_sendBundle` makes at `e561b9cc2` (`InteropCenter.sol:550-554`). An
atomic bundle must not go to L1 (`AtomicBundleToL1NotSupported`), and a non-atomic one must
(`NonAtomicSendUnsupported`). -/
def UpgradeDestinationCheck (l1ChainId dest : Word) (isAtomic : Bool) : Prop :=
  (isAtomic = true → dest ≠ l1ChainId) ∧ (isAtomic = false → dest = l1ChainId)

/-! ## The repaired loop (e561b9cc2) -/

/-- One iteration of `_recoverBundle` at `e561b9cc2` (`AtomicFlowManager.sol:298-320`). Only a
call whose `from` is the asset router is probed, as `IAtomicRecoverable(c.from)`, and its answer is
discarded (`:308-311`). A non-router call with nonzero `value` has the router refund that base
token (`bridgehubRecoverBaseToken`, `:312-319`), here the abstract router step `baseRecover`
(`world → destination → destination base-token asset id → payer → amount`, `none` a revert). No
other address is called. -/
def upgradeStep (S : SourceChain W) (router : Address)
    (baseRecover : W → Word → Word → Address → ℕ → Option W) (dest baseAsset : Word) (w : W)
    (c : InteropCall) : Option W :=
  match (if c.fromAddr = router then (probeAt S dest w c.fromAddr c.data).map Prod.fst
    else some w) with
  | none => none
  | some w₁ =>
    if c.fromAddr ≠ router ∧ c.value ≠ 0 then baseRecover w₁ dest baseAsset c.fromAddr c.value
    else some w₁

/-- The repaired loop: the calls in order on the threaded world, with no `try/catch`. -/
def upgradeLoop (step : W → InteropCall → Option W) : W → List InteropCall → Option W
  | w, [] => some w
  | w, c :: cs =>
    match step w c with
    | none => none
    | some w' => upgradeLoop step w' cs

/-- `claimRefund` at `e561b9cc2` (`AtomicFlowManager.sol:246-261`). It has the same `Revertable`
gate. Its `_recoverBundle` requires `destChainId != L1_CHAIN_ID` (`:295`, `RecoverToL1NotSupported`)
and no longer reverts when nothing was recovered (`:286-287`). -/
def claimRefundUpgrade (S : SourceChain W) (router : Address) (l1ChainId : Word)
    (baseRecover : W → Word → Word → Address → ℕ → Option W) (s : LegState) (w : W)
    (b : Bundle) : Option (LegState × W) :=
  if s ≠ .Revertable then none
  else if b.destinationChainId = l1ChainId then none
  else (upgradeLoop (upgradeStep S router baseRecover b.destinationChainId
      b.destinationBaseTokenAssetId) w b.calls).map fun w' => (.Reverted, w')

/-! ## Witness data

The witnesses reuse `Contracts.InteropCenter`'s honest chain `wParams` (chain `324`, sending to
chain `325`), its direct starter `wDirect` (recipient `5`) and its indirect starter `wIndirect`
(through `9`, read here as the L2 asset router). Call data bytes are placeholders. The witness
router recognises exactly `wDepositData`. -/

/-- Placeholder bytes standing for the router's `finalizeDeposit(...)` call data. -/
def wDepositData : List UInt8 := [1]

/-- The router's deposit call for an L2 destination: `to` and `from` the L2 asset router `9`
(`InteropCenter.sol:733-740`, `L2AssetRouter.sol:336`), with zero value. -/
def wRouterCall : InteropCall := ⟨9, 9, 0, wDepositData⟩

/-- The flag flip: a zero-value direct call from sender `1` to contract `5`
(`InteropCenter.sol:742-749`). Contract `5` lives on the destination chain. -/
def wFlagCall : InteropCall := ⟨5, 1, 0, []⟩

/-- The mixed leg. Sender `1`, salt `3`, flow `7`: the router's deposit and a flag flip, the
bundle `AtomicFlowManager.sol:208-211` describes as refundable. -/
def mixD : Contracts.InteropCenter.Dispatch :=
  ⟨1, [Contracts.InteropCenter.wIndirect, Contracts.InteropCenter.wDirect 0],
    Contracts.InteropCenter.wBundle Contracts.InteropCenter.wParams 1 3 [wRouterCall, wFlagCall],
    ⟨7, 0, 100, true⟩⟩

/-- After the send: the mixed leg is `Committed`. -/
def mixS1 : Contracts.InteropCenter.State :=
  Contracts.InteropCenter.init.afterSend Contracts.InteropCenter.wParams mixD

/-- After `authorizeRefund`: the mixed leg is `Revertable`. -/
def mixS2 : Contracts.InteropCenter.State :=
  { mixS1 with
    manager := (mixS1.manager.set 7
      (Contracts.InteropCenter.bundleHash Contracts.InteropCenter.wParams mixD.bundle) .Revertable) }

/-- The witness source chain. Only the asset router `9` runs code. It answers `true` to its
deposit bytes and `false` to anything else, as `L2AssetRouter.recoverAtomicCall` does
(`L2AssetRouter.sol:281-296`). The flag contract `5` exists only on the destination. -/
def wSource : SourceChain Unit where
  runsCode := fun _ a => decide (a = 9)
  exec := fun w _ _ data => .returned (abiBool (decide (data = wDepositData))) w

/-- The same chain with a conforming contract deployed at `5` on the source chain, which answers
`false` as `IAtomicRecoverable.sol:13-15` asks. -/
def wSourceConforming : SourceChain Unit where
  runsCode := fun _ a => decide (a = 9) || decide (a = 5)
  exec := fun w a _ data =>
    .returned (abiBool (decide (a = 9) && decide (data = wDepositData))) w

/-- The witness L1 chain id. -/
def wL1 : Word := 1

/-- The witness L1 asset router address. Nothing runs at it on `wSource`. -/
def wL1Router : Address := 11

/-- The router's withdrawal call for an L1 destination: `to` the L1 asset router
(`L2AssetRouter.sol:336`), `from` the L2 asset router `9`, value zero (`InteropCenter.sol:533-537`). -/
def wWithdrawCall : InteropCall := ⟨routerIndirectRecipient wL1 wL1Router 9 wL1, 9, 0, wDepositData⟩

/-- An atomic L2→L1 withdrawal leg's bundle: its one call is `wWithdrawCall`. The base-token asset
id and the salt are placeholders. -/
def wWithdrawBundle : Bundle :=
  ⟨324, wL1, 0, 0, [wWithdrawCall], Contracts.InteropCenter.wAttrs 4⟩

end Contracts.AtomicFlowManager.RecoveryLimitsFaithful
