import EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryLimits
import EraSpec.Contracts.InteropCenter.History.Specs.Dispatch

/-!
# Model: the refund loop's external call at `draft/v0.35.0`

Source: era-contracts `draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5` (`contracts/` below
is `l1-contracts/contracts/`). A bare `:N` is a line of `atomic-interop/AtomicFlowManager.sol`.

**This file is definitions only.** The statements are in
`EraSpec.Contracts.AtomicFlowManager.Properties.RecoveryLimitsFaithful` and are proved in
`EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryLimitsFaithful`. The loop of era-contracts
`c67894b9`, which called every call's `to` and required one recovery, is kept as a record in
`History/Specs/RecoveryLimitsFaithful.lean` (namespace `…RecoveryLimitsFaithful.History`); it is
not a claim about `b17415d20`.

## The code

    function claimRefund(bytes32 _flowId, bytes calldata _bundle) external {               // :250
        InteropBundle memory bundle = abi.decode(_bundle, (InteropBundle));                 // :251
        bytes32 bundleHash = InteropDataEncoding.encodeInteropBundleHash(_bundle);          // :252
        LegState s = _state[_flowId][bundleHash];                                           // :254
        if (s != LegState.Revertable) revert ManagerLegNotRevertable(...);                  // :255-257
        _state[_flowId][bundleHash] = LegState.Reverted;                                    // :260
        _recoverBundle(bundle);                                                             // :262
    }
    function _recoverBundle(InteropBundle memory _bundle) internal {                        // :292
        uint256 destChainId = _bundle.destinationChainId;
        require(destChainId != L1_CHAIN_ID, RecoverToL1NotSupported());                     // :299
        for each call c:                                                                    // :302-324
            if (c.from == L2_ASSET_ROUTER_ADDR)
                IAtomicRecoverable(c.from).recoverAtomicCall(destChainId, c.data);          // :312-315
            if (c.from != L2_ASSET_ROUTER_ADDR && c.value != 0)
                IAssetRouterShared(L2_ASSET_ROUTER_ADDR).bridgehubRecoverBaseToken(
                    destChainId, destBaseTokenAssetId, c.from, c.value);                    // :316-323
    }

## What is modelled

* **One external call** (`SourceChain`, `SourceChain.call`). `runsCode` says whether a CALL to an
  address runs any code in the current world. `exec` says what that code does with the manager's
  `recoverAtomicCall(destChainId, data)`: it reverts, or it returns bytes and a new world. An
  account that runs no code accepts the call, executes nothing, changes nothing (the manager sends
  no value) and returns no data. That is the EVM's rule for an account without code, such as an
  EOA. On EraVM such an account runs the default account, whose fallback executes nothing and
  returns no data to a caller other than the bootloader
  (`system-contracts/contracts/DefaultAccount.sol`) (`VM-CALL`). A contract that runs but has no
  `recoverAtomicCall` either reverts in its dispatcher (`exec` gives `reverted`) or runs a
  fallback (`exec` gives what the fallback returns).
* **The decoding of the answer** (`decodeBool`). The manager is compiled with Solidity 0.8.28
  (`AtomicFlowManager.sol:2`), whose ABI coder v2 makes the caller revert on fewer than 32 bytes
  of return data, and on a first word other than `0` or `1`. Bytes after the first word are
  ignored. Since 0.8.10 the compiler emits no `extcodesize` check before a call whose return data
  it decodes, so for an account without code it is the decoding that reverts (`SOL-ABI`,
  `SOL-CONTROL`). At `b17415d20` the answer is decoded and then discarded (`:312-315`).
* **The loop** (`v35Step`, `v35Loop`, `claimRefundV35`). `claimRefund`'s `Revertable` gate
  (`:254-257`) and write (`:260`), then `_recoverBundle` (`:292-325`): the L1-destination check
  (`:299`), then the calls in order, each on the world the previous one left, with no `try/catch`.
  A call whose `from` is `L2_ASSET_ROUTER_ADDR` (the parameter `router`) is sent
  `recoverAtomicCall` at `c.from`; a call with another `from` and nonzero `value` has the router
  refund that value (`bridgehubRecoverBaseToken`), here the abstract step `baseRecover`. No other
  address is called and no recovery is counted. A revert of the claim is `none`: the leg keeps its
  state and nothing the loop did persists (`VM-REVERT`).
* **Bundles** are `Contracts.InteropCenter`'s `Bundle` and `InteropCall` (`MODEL-CENTER`): `fromAddr`
  is `from`, `value` and `data` are the call's fields, and `destinationChainId` and
  `destinationBaseTokenAssetId` are the bundle's; these are the fields of `InteropBundle` and
  `InteropCall` the loop reads at `b17415d20` (`common/Messaging.sol:240-247`, `:268-276`).
* **Not modelled.** Gas: a call that runs out of gas is one more `reverted`. Events. What
  `baseRecover` calls (the base token, the asset tracker). Re-entry into the manager from a
  recovery call: the manager's storage is not part of the world `W` (`MODEL-AFM-NESTED` models
  re-entry). Which bundle bytes a claimant presents: the claim is stated for the bundle presented;
  bytes other than the leg's own reach the leg's key only through a keccak collision on the
  bundle-hash preimage (`:252`, `interop/InteropDataEncoding.sol:14-16`). The proof checks of
  `authorizeRefund`. The send side.
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

/-- In every world, the code at `a` runs and answers every `recoverAtomicCall` with a well-formed
`bool` instead of reverting, as `IAtomicRecoverable.sol:14-16` requires of an implementation. -/
def Conforms (S : SourceChain W) (a : Address) : Prop :=
  ∀ w dest data, S.runsCode w a = true ∧ ∃ b w', S.exec w a dest data = .returned (abiBool b) w'

/-! ## The loop at `draft/v0.35.0` (b17415d20) -/

/-- One iteration of `_recoverBundle` at `b17415d20` (`AtomicFlowManager.sol:303-323`). A call whose
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

/-- The loop of `_recoverBundle` at `b17415d20` (`:302-324`): the calls in order on the threaded
world, with no `try/catch`. -/
def v35Loop (step : W → InteropCall → Option W) : W → List InteropCall → Option W
  | w, [] => some w
  | w, c :: cs =>
    match step w c with
    | none => none
    | some w' => v35Loop step w' cs

/-- `claimRefund` at `b17415d20` (`AtomicFlowManager.sol:250-265`), with `L2_ASSET_ROUTER_ADDR` as
`router` and the manager's `L1_CHAIN_ID` as `l1ChainId`. It has the `Revertable` gate
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

/-- The router's deposit call for an L2 destination: `to` and `from` the L2 asset router `9`,
with zero value. -/
def wRouterCall : InteropCall := ⟨9, 9, 0, wDepositData⟩

/-- A zero-value direct call from sender `1` to contract `5`. -/
def wDirectCall : InteropCall := ⟨5, 1, 0, []⟩

/-- The two-call leg. Sender `1`, salt `3`, flow `7`: the router's deposit call and the direct
call. -/
def mixD : Contracts.InteropCenter.History.Dispatch :=
  ⟨1, [Contracts.InteropCenter.wIndirect, Contracts.InteropCenter.wDirect 0],
    Contracts.InteropCenter.History.wBundle Contracts.InteropCenter.History.wParams 1 3 [wRouterCall, wDirectCall],
    ⟨7, 0, 100, true⟩⟩

/-- A source chain on which code runs only at the router `9`, for any world type. The router
answers `true` to its deposit bytes and `false` to anything else, and changes nothing.
`L2AssetRouter.recoverAtomicCall` answers `false` to data without the `finalizeDeposit` selector
and `true` after the asset handler's refund of `finalizeDeposit` data
(`bridge/asset-router/L2AssetRouter.sol:269-303`). -/
def wSourceOver (W : Type) : SourceChain W where
  runsCode := fun _ a => decide (a = 9)
  exec := fun w _ _ data => .returned (abiBool (decide (data = wDepositData))) w

/-- `wSourceOver` on the one-point world. Nothing runs at `5`. -/
abbrev wSource : SourceChain Unit := wSourceOver Unit

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
