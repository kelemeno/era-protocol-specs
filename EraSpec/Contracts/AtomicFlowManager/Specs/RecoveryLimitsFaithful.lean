import EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryLimits
import EraSpec.Contracts.InteropCenter.Specs.Dispatch

/-!
# Model: the refund loop's external call, at the pin and at `draft/v0.35.0`

Source: era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`, the pin (`contracts/` below is
`l1-contracts/contracts/`). The loop of the section "The loop at `draft/v0.35.0`" is read at
`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`, the head of branch `draft/v0.35.0`. That commit is not
a successor of the pin: the two diverge at `76f40b530`, with 20 commits only on the pin's side and
310 only on the other. `claimRefund` and `_recoverBundle` are the same lines at `main` commit
`70096e2ea6eeb5373992e178064c4b26dcf6436a`, three lines earlier (`:247-262`, `:289-322`). Line
numbers without a commit are at the pin.

**This file is definitions only.** The statements are in
`EraSpec.Contracts.AtomicFlowManager.Properties.RecoveryLimitsFaithful` and are proved in
`EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryLimitsFaithful`.

## What this file adds to `RecoveryLimits`

`AttackVectors.RecoveryLimits` (`Specs/RecoveryLimits.lean`) reasons about lists of `Outcome`s.
It does not say which contract produces an outcome, or when a call reverts rather than returning
`false`. This file models the loop's one external call and the decoding of its answer, so that
each outcome is computed from the code at the call's target on the source chain.

The loop at the pin (`atomic-interop/AtomicFlowManager.sol:219-230`) is

    InteropCall memory c = _bundle.calls[i];
    if (IAtomicRecoverable(c.to).recoverAtomicCall(destChainId, c.data)) { ++recovered; }

and it runs inside `claimRefund` (`:165-180`), on the leg's source chain. `c.to` is what
`_processCallStarter` (`interop/InteropCenter.sol:701-751`) wrote into the bundle: for a direct
call the starter's recipient (`to: recipientAddress`, `:745`), and for an indirect call the
recipient the indirect sender returned (`to: actualCallRecipient`, `:736`).
`Contracts.InteropCenter.FormsCall` records the direct case, and `InteropCall.target` documents
`to` as the contract called on the destination. The router-produced call to an L1 destination,
whose `to` is `L1_ASSET_ROUTER` (`bridge/asset-router/L2AssetRouter.sol:336`), and the pin's send
checks for that destination are modelled in `AssetRouterBase/Specs/AtomicRecoveryFaithful.lean`.

## What is modelled

* **One external call** (`SourceChain`, `SourceChain.call`). `runsCode` says whether a CALL to an
  address runs any code in the current world. `exec` says what that code does with the manager's
  `recoverAtomicCall(destChainId, data)`: it reverts, or it returns bytes and a new world. An
  account that runs no code accepts the call, executes nothing, changes nothing (the manager sends
  no value) and returns no data. That is the EVM's rule for an account without code, such as an
  EOA. On EraVM such an account runs the default account, whose fallback executes nothing and
  returns no data to a caller other than the bootloader
  (`system-contracts/contracts/DefaultAccount.sol:266-271`) (`VM-CALL`). A contract that runs but
  has no `recoverAtomicCall` either reverts in its dispatcher (`exec` gives `reverted`) or runs a
  fallback (`exec` gives what the fallback returns).
* **The decoding of the answer** (`decodeBool`). The manager is compiled with Solidity 0.8.28
  (`AtomicFlowManager.sol:2`), whose ABI coder v2 makes the caller revert on fewer than 32 bytes
  of return data, and on a first word other than `0` or `1`. Bytes after the first word are
  ignored. Since 0.8.10 the compiler emits no `extcodesize` check before a call whose return data
  it decodes, so for an account without code it is the decoding that reverts (`SOL-ABI`,
  `SOL-CONTROL`).
* **The loop at the pin** (`pinnedProbe`, `recoverLoop`, `claimRefundPinned`). The calls are taken
  in order, each on the world the previous one left, with no `try/catch`. The `recovered == 0`
  revert (`:229`) and `claimRefund`'s `Revertable` gate (`:169-170`) are modelled. A revert of the
  claim is `none`: the leg keeps its state and nothing the loop did persists (`VM-REVERT`).
  `outcomes` reads a run as `AttackVectors.RecoveryLimits.Outcome`s, so that file's acceptance rule
  applies to it.
* **The loop at `draft/v0.35.0`** (`v35Step`, `v35Loop`, `claimRefundV35`). At `b17415d`,
  `_recoverBundle` (`AtomicFlowManager.sol:292-325`) requires `destChainId != L1_CHAIN_ID`
  (`:299`, `RecoverToL1NotSupported`). For each call whose `from` is `L2_ASSET_ROUTER_ADDR` it calls
  `IAtomicRecoverable(c.from).recoverAtomicCall(destChainId, c.data)` and does not use the answer
  (`:312-315`). For each call with another `from` and nonzero `value` it calls the router's
  `bridgehubRecoverBaseToken(destChainId, destBaseTokenAssetId, c.from, c.value)` (`:316-323`),
  here the abstract step `baseRecover`. It calls nothing else and counts no recoveries.
  `claimRefund` (`:250-265`) has the same `Revertable` gate (`:254-257`) and write (`:260`) as at
  the pin. The bundle fields the loop reads are the pin's (`common/Messaging.sol:240-247, 268-276`
  at `b17415d`).
* **Bundles and their formation** are `Contracts.InteropCenter`'s, at the pin (`MODEL-CENTER`):
  `InteropCall.target` is `to`, `fromAddr` is `from`, and `FormsCall` pins a direct call's `to` to
  the starter's recipient.
* **Not modelled.** Gas: a call that runs out of gas is one more `reverted`. Events. Re-entry into
  the manager from a recovery call: the manager's storage is not part of the world `W`
  (`MODEL-AFM-NESTED` models re-entry). The proof checks of `authorizeRefund`:
  `Contracts.InteropCenter.Step.authorize` omits them, so the witness leg reaches `Revertable` in
  that model only. Which bundle bytes a claimant presents: the claim is stated for the bundle
  presented. Bytes other than the leg's own reach the leg's key only through a keccak collision on
  the bundle-hash preimage, as `RecoveryLimitsStrong` records (`Specs/RecoveryLimitsStrong.lean`;
  the center model's form is `Contracts.InteropCenter.ClaimedBundleValidatedOrCollision`). What the
  code at any target does beyond its answer. At `b17415d`: the send side (including
  `AtomicBundleToL1NotSupported`, `IndirectCallOnlyToAssetRouter` and
  `IndirectCallCannotCarryValue`, `InteropCenter.sol:553, 659-678`), the bundle hash, which no
  longer includes the source chain id (`AtomicFlowManager.sol:252`,
  `InteropDataEncoding.sol:14-16`), and the leg-source checks of `authorizeRefund` and
  `requireFlowFinalized`.
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
storage, balances and deployed code of every contract the calls may touch, except the manager's
own storage. -/
structure SourceChain (W : Type) where
  /-- A CALL to `a` in world `w` runs code: a deployed contract, a precompile or system contract,
  or an account that delegates to code. `false` for an account without code: an EOA, or an
  address with nothing deployed on this chain. -/
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

/-! ## The loop at the pin (c67894b9) -/

/-- One iteration of the pinned `_recoverBundle` (`AtomicFlowManager.sol:224-225`):
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
code, and an address with nothing deployed on the source chain. -/
def NeverRunsCode (S : SourceChain W) (a : Address) : Prop := ∀ w, S.runsCode w a = false

/-- In every world, the code at `a` runs and answers every `recoverAtomicCall` with a well-formed
`bool` instead of reverting, as `IAtomicRecoverable.sol:13-15` requires of an implementation. -/
def Conforms (S : SourceChain W) (a : Address) : Prop :=
  ∀ w dest data, S.runsCode w a = true ∧ ∃ b w', S.exec w a dest data = .returned (abiBool b) w'

/-- In every world, the code at `a` recovers `data` for destination `dest`: it answers `true`. -/
def AlwaysRecovers (S : SourceChain W) (a : Address) (dest : Word) (data : List UInt8) : Prop :=
  ∀ w, ∃ w', S.exec w a dest data = .returned (abiBool true) w'

/-! ## The loop at `draft/v0.35.0` (b17415d) -/

/-- One iteration of `_recoverBundle` at `b17415d` (`AtomicFlowManager.sol:303-323`). A call whose
`from` is the asset router `router` is sent `recoverAtomicCall`, to `c.from`, and its decoded answer
is discarded (`:312-315`). A call with another `from` and nonzero `value` has the router refund
that base-token value to `c.from` (`bridgehubRecoverBaseToken`, `:316-323`), here the abstract
step `baseRecover` (world, destination, destination base-token asset id, receiver, amount; `none`
is a revert). No other address is called. -/
def v35Step (S : SourceChain W) (router : Address)
    (baseRecover : W → Word → Word → Address → ℕ → Option W) (dest baseAsset : Word) (w : W)
    (c : InteropCall) : Option W :=
  match (if c.fromAddr = router then (probeAt S dest w c.fromAddr c.data).map Prod.fst
    else some w) with
  | none => none
  | some w₁ =>
    if c.fromAddr ≠ router ∧ c.value ≠ 0 then baseRecover w₁ dest baseAsset c.fromAddr c.value
    else some w₁

/-- The loop of `_recoverBundle` at `b17415d` (`:302-324`): the calls in order on the threaded
world, with no `try/catch`. -/
def v35Loop (step : W → InteropCall → Option W) : W → List InteropCall → Option W
  | w, [] => some w
  | w, c :: cs =>
    match step w c with
    | none => none
    | some w' => v35Loop step w' cs

/-- `claimRefund` at `b17415d` (`AtomicFlowManager.sol:250-265`), with `L2_ASSET_ROUTER_ADDR` as
`router` and the manager's `L1_CHAIN_ID` as `l1ChainId`. It has the pin's `Revertable` gate
(`:254-257`). Its `_recoverBundle` requires `destChainId != L1_CHAIN_ID` (`:299`) and has no
`recovered == 0` revert. -/
def claimRefundV35 (S : SourceChain W) (router : Address) (l1ChainId : Word)
    (baseRecover : W → Word → Word → Address → ℕ → Option W) (s : LegState) (w : W)
    (b : Bundle) : Option (LegState × W) :=
  if s ≠ .Revertable then none
  else if b.destinationChainId = l1ChainId then none
  else (v35Loop (v35Step S router baseRecover b.destinationChainId
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

/-- A zero-value direct call from sender `1` to contract `5` (`InteropCenter.sol:742-749`). -/
def wDirectCall : InteropCall := ⟨5, 1, 0, []⟩

/-- The two-call leg. Sender `1`, salt `3`, flow `7`: the router's deposit call and the direct
call. -/
def mixD : Contracts.InteropCenter.Dispatch :=
  ⟨1, [Contracts.InteropCenter.wIndirect, Contracts.InteropCenter.wDirect 0],
    Contracts.InteropCenter.wBundle Contracts.InteropCenter.wParams 1 3 [wRouterCall, wDirectCall],
    ⟨7, 0, 100, true⟩⟩

/-- After the send: the two-call leg is `Committed`. -/
def mixS1 : Contracts.InteropCenter.State :=
  Contracts.InteropCenter.init.afterSend Contracts.InteropCenter.wParams mixD

/-- After `authorizeRefund`: the two-call leg is `Revertable`. -/
def mixS2 : Contracts.InteropCenter.State :=
  { mixS1 with
    manager := (mixS1.manager.set 7
      (Contracts.InteropCenter.bundleHash Contracts.InteropCenter.wParams mixD.bundle) .Revertable) }

/-- A source chain on which code runs only at the router `9`, for any world type. The router
answers `true` to its deposit bytes and `false` to anything else, and changes nothing.
`L2AssetRouter.recoverAtomicCall` answers `false` to data without the `finalizeDeposit` selector
and `true` after the vault's refund of `finalizeDeposit` data (`L2AssetRouter.sol:281-296`). -/
def wSourceOver (W : Type) : SourceChain W where
  runsCode := fun _ a => decide (a = 9)
  exec := fun w _ _ data => .returned (abiBool (decide (data = wDepositData))) w

/-- `wSourceOver` on the one-point world. Nothing runs at `5`. -/
abbrev wSource : SourceChain Unit := wSourceOver Unit

/-- The same chain with code at `5` that answers `false`, as `IAtomicRecoverable.sol:13-15` asks of
an implementation that does not recognise the call. -/
def wSourceConforming : SourceChain Unit where
  runsCode := fun _ a => decide (a = 9) || decide (a = 5)
  exec := fun w a _ data =>
    .returned (abiBool (decide (a = 9) && decide (data = wDepositData))) w

/-- The same chain with code at `5` that has no `recoverAtomicCall`: its dispatcher reverts. -/
def wSourceNoHook : SourceChain Unit where
  runsCode := fun _ a => decide (a = 9) || decide (a = 5)
  exec := fun w a _ data =>
    if a = 9 then .returned (abiBool (decide (data = wDepositData))) w else .reverted

/-- The witness L1 chain id. -/
def wL1 : Word := 1

/-- A direct call from sender `1` to contract `5` carrying base-token value `3`. At `b17415d` the
call loop of the send side restricts a call's value only for an L1 destination and for an indirect
call (`InteropCenter.sol:645-678`), and `_recoverBundle` refunds a direct call's value
(`AtomicFlowManager.sol:316-323`). -/
def wValueCall : InteropCall := ⟨5, 1, 3, []⟩

/-- A bundle to chain `325` with the router's deposit call and the value-carrying direct call.
Source chain, base-token asset id, salt and attributes are placeholders. -/
def wValueBundle : Bundle :=
  ⟨324, 325, 1, 0, [wRouterCall, wValueCall], Contracts.InteropCenter.wAttrs 5⟩

/-- A base-token refund that never reverts and adds the refunded amount to a counter world. -/
def wBaseRecover : ℕ → Word → Word → Address → ℕ → Option ℕ :=
  fun w _ _ _ amount => some (w + amount)

end Contracts.AtomicFlowManager.RecoveryLimitsFaithful
