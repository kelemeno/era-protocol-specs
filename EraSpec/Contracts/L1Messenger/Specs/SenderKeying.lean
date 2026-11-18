import Mathlib.Tactic
import EraSpec.Contracts.L1InteropHandler.Specs.WithdrawalGate

/-!
# Model: how an L2→L1 message is keyed by its sender (ZKsync OS, v0.35 head)

Source: era-contracts branch `draft/v0.35.0` at head `b17415d20`. Paths are relative to
`l1-contracts/contracts/` unless they start with `protocol-docs/`. In this header `LM` is
`l2-system/zksync-os/L1Messenger.sol`, `IC` is `interop/InteropCenter.sol`, `ADDR` is
`common/l2-helpers/L2ContractAddresses.sol` and `HOOKS` is `protocol-docs/system/system-hooks.md`; every
line number is at `b17415d20`. At main `70096e2ea` the messenger is `L1MessengerZKOS.sol` with the same
body, `HOOKS` and the cited `ADDR` lines are unchanged, and the center's L1 branch is the same; its send
entry points gain `whenNotPaused`, which only rejects.

**This file is definitions only.** The results are in
`EraSpec.Contracts.L1Messenger.Properties.SenderKeying` and are proved in
`EraSpec.Contracts.L1Messenger.Proofs.SenderKeying`.

## The code

    // L1Messenger, at L2_TO_L1_MESSENGER_SYSTEM_CONTRACT_ADDR = 0x8008 (ADDR:56)
    function sendToL1(bytes calldata _message) external returns (bytes32 hash) {          // LM:38
        burnGas(_message);                                                                // LM:40
        (bool ok, ) = L1_MESSENGER_HOOK.call(abi.encodePacked(msg.sender, _message));     // LM:44
        require(ok, L1MessengerHookFailed());                                             // LM:45
        hash = keccak256(_message);                                                       // LM:46
        emit L1MessageSent(msg.sender, hash, _message);                                   // LM:48
    }
    fallback() external payable { require(msg.sender == address(this)); invalid(); }      // LM:53-60

    // L1_MESSENGER_HOOK = SYSTEM_HOOKS_OFFSET + 0x01 = 0x7001                             (ADDR:18-19)
    // INTEROP_COMMITMENT_LEAF_HOOK = 0x7004, "Can only be called from the
    //   L2_INTEROP_COMMITMENT_TREE_ADDR contract"                                         (ADDR:24-27)

    // InteropCenter._dispatchBundle, the L1 branch                                       (IC:727-737)
    bundleHash = _hashBundle(_bundle);
    if (_bundle.destinationChainId == L1_CHAIN_ID) {
        msgHash = L2_TO_L1_MESSENGER_SYSTEM_CONTRACT.sendToL1(
            bytes.concat(BUNDLE_IDENTIFIER, abi.encode(_bundle)));                       // IC:735
        return (bundleHash, msgHash);
    }

On L1, `proveL2MessageInclusionShared` proves the log `{0, true, txNumberInBatch, 0x8008,
bytes32(uint160(message.sender)), keccak256(message.data)}` (`common/libraries/MessageHashing.sol:27-37`,
`Contracts.L1WithdrawalGate.msgToLog`), and `L1InteropHandler._verifyBundle` requires
`message.sender == L2_INTEROP_CENTER_ADDR` (`interop/interop-handler/L1InteropHandler.sol:213-216`). The
only on-chain link between that `sender` and the L2 account that sent the message is the 20-byte prefix
the messenger puts in front of the message (LM:44), which the hook turns into the log's key.

## The hooks: a named VM premise

The hooks are ZKsync OS code, not part of this repository. `HOOKS` documents them:

* `HOOKS:19`: 0x7001 is the "L1 messenger; only `L1MessengerZKOS` at `0x8008`"; it "accepts the 20-byte
  sender followed by the message and records a variable-length L2 -> L1 message in the OS output".
* `HOOKS:22`: 0x7004 is the "interop commitment leaf; only `L2InteropCommitmentTree` at `0x10012`"; it
  "records each inserted 32-byte commitment-tree value as an L2 -> L1 log".
* `HOOKS:53-55`: "Each privileged call hook checks its immediate caller. Hooks that must remain
  indistinguishable from an empty EVM account return empty success to an unauthorized caller".

The Solidity constant's own comment (ADDR:18-19) states no caller restriction for `L1_MESSENGER_HOOK`,
while ADDR:21-31 state one for the other three hooks. `HooksAsDocumented` is the documented behaviour,
as a premise. Its fourth clause, that a leaf log is not a messenger log keyed by the center, is about the
leaf log's format, which `HOOKS` does not give; it is the weakest form the result needs.

## The inventory the model rests on (checked against `b17415d20`)

* The center calls `sendToL1` at one site, IC:735 (`grep -n sendToL1 interop/InteropCenter.sol`), in
  `_dispatchBundle`'s L1 branch. `_dispatchBundle` is called only by `_sendBundle` (IC:602), and
  `_sendBundle` only by `sendMessage` (IC:235) and `sendBundle` (IC:274); the preview functions build a
  bundle and always revert (IC:346-354). `msg.sender` is the center only while the center's own code
  makes the call.
* What reaches IC:735 has passed: `sendMessage` reverts for an L1 destination (`_ensureL2ToL2`, IC:207,
  :399-405); `sendBundle` requires one call starter for L1 (IC:262-264); `_sendBundle` requires a
  non-atomic send for L1 (IC:552-556); `_buildInteropBundle` sets `version` (IC:633), `sourceChainId =
  block.chainid` (IC:634), the destination (IC:635), the base asset `encodeNTVAssetId(L1_CHAIN_ID,
  ETH_TOKEN_ADDRESS)` (IC:629-630), and for an L1 destination requires the starter to be indirect, to
  `L2_ASSET_ROUTER_ADDR`, with zero `interopCallValue` (IC:645-658); `_processCallStarter`'s indirect
  branch (IC:782-822) sets call `version` 1 and `shadowAccount` false (IC:815-816), `value` to the
  starter's `interopCallValue` (IC:819) and `from` to the starter's recipient (IC:820), and takes the
  recipient and data the router returns, the recipient nonzero (IC:810-813).
* Other contracts call `sendToL1` with themselves as `msg.sender` (for example
  `state-transition/data-availability/RelayedSLDAValidator.sol:42`): a `message` step.

## Modelling choices

* **One chain's L2→L1 output.** `L2State.out` is the list of logs the chain's batches commit, oldest
  first; `dispatched` is a ghost log of the center's L1 dispatches. Batches, transaction order and
  everything that writes no L2→L1 log (atomic sends, fees, other contracts' storage) are not modelled.
* **Hook calldata as parsed.** The messenger hook's calldata `abi.encodePacked(sender, message)` is
  the pair `(sender, message)`; calldata shorter than 20 bytes is malformed, and HOOKS:56-57 says
  state-changing hooks reject it.
* **The center's L1 branch as its shape.** A `withdrawal` step is a successful `sendBundle` to L1,
  whose bundle has `WithdrawalShape` (the fields the code above fixes; the router-returned recipient
  and data, the attributes and the salt are free). Its effect is the messenger hook called by 0x8008
  with `(L2_INTEROP_CENTER_ADDR, BUNDLE_IDENTIFIER ++ abi.encode(bundle))`.
* **Who calls what.** `message` is `sendToL1` by an account other than the center; `hookCall` is any
  account other than the messenger calling the messenger hook directly; `leafCall` is any account
  calling the leaf hook (the commitment tree does on each insert, `atomic-interop/
  L2InteropCommitmentTree.sol:74`); `bootloaderLog` is a log with sender `L2_BOOTLOADER_ADDRESS`
  (`MessageHashing.sol:39-62`). What the hooks record is `HookSem`; the steps take no premise on it.
* **The steps are every log source (closure).** The model takes its five steps to be the only writers
  of the chain's L2→L1 output: ZKsync OS writes no other L2→L1 log with sender `0x8008`, i.e. the `Step`
  constructors cover every log source. This is not derived (the ZKsync OS output code is not in this
  repository); it is load-bearing for "exactly the center's dispatch logs" in
  `CenterKeyedLogsAreItsWithdrawals`, and is recorded in `ASSUMPTIONS.md` (`MODEL-L2-MESSAGE-KEYING`).
* System-contract upgrades and EraVM chains (whose messenger is not this contract) are out of scope.
-/

namespace Contracts.L1MessengerKeying

open Contracts.L1WithdrawalGate

/-! ## Constants (`ADDR`) -/

/-- `L2_BOOTLOADER_ADDRESS = SYSTEM_CONTRACTS_OFFSET + 0x01` (ADDR:41). -/
def l2BootloaderAddr : Address := 0x8001

/-- `L2_ASSET_ROUTER_ADDR = BUILT_IN_CONTRACTS_OFFSET + 0x03` (ADDR:84). -/
def l2AssetRouterAddr : Address := 0x10003

/-- `L2_INTEROP_COMMITMENT_TREE_ADDR = BUILT_IN_CONTRACTS_OFFSET + 0x12` (ADDR:136). -/
def l2CommitmentTreeAddr : Address := 0x10012

/-! ## The hooks -/

/-- What the two ZKsync OS hooks record. -/
structure HookSem where
  /-- `L1_MESSENGER_HOOK` called by `caller`, in the transaction numbered `t` in its batch, with
  calldata `abi.encodePacked(sender, message)`: the log it records, or `none`. -/
  messengerHook : (caller : Address) → (t : ℕ) → Address × Bytes → Option L2Log
  /-- `INTEROP_COMMITMENT_LEAF_HOOK` called by `caller`, in transaction `t`, with the value `v`. -/
  leafHook : (caller : Address) → (t : ℕ) → (v : Word) → Option L2Log

/-- The log of message `m` from `a` in transaction `t`: exactly what L1 proves for the message
`{t, a, m}` (`MessageHashing.sol:27-37`). -/
def messageLog (C : Codec) (t : ℕ) (a : Address) (m : Bytes) : L2Log := msgToLog C ⟨t, a, m⟩

/-- A log attributed to the messenger and keyed by the center: the logs `_verifyBundle`'s sender check
accepts. -/
def CenterKeyed (L : L2Log) : Prop :=
  L.sender = l2ToL1MessengerAddr ∧ L.key = padAddr l2InteropCenterAddr

instance (L : L2Log) : Decidable (CenterKeyed L) := by unfold CenterKeyed; infer_instance

/-- **THE VM PREMISE** (HOOKS:19, :22, :53-55). -/
structure HooksAsDocumented (C : Codec) (H : HookSem) : Prop where
  /-- Only the messenger at 0x8008 gets the messenger hook to record a log. -/
  messengerCallerGated : ∀ c t x, c ≠ l2ToL1MessengerAddr → H.messengerHook c t x = none
  /-- Called by the messenger with `(a, m)`, it records the message log of `a` and `m`. -/
  messengerRecords : ∀ t a m,
    H.messengerHook l2ToL1MessengerAddr t (a, m) = some (messageLog C t a m)
  /-- Only the commitment tree gets the leaf hook to record a log. -/
  leafCallerGated : ∀ c t v, c ≠ l2CommitmentTreeAddr → H.leafHook c t v = none
  /-- The leaf hook's log is not a messenger log keyed by the center. -/
  leafNotCenterKeyed : ∀ t v L, H.leafHook l2CommitmentTreeAddr t v = some L → ¬ CenterKeyed L

/-! ## One chain -/

/-- One chain: its `block.chainid` and the `L1_CHAIN_ID` its center stores. -/
structure ChainParams where
  chainId : ℕ
  l1ChainId : ℕ

/-- The shape `_sendBundle` and `_buildInteropBundle` give a bundle that reaches the L1 branch of
`_dispatchBundle` (IC:262-264, :552-556, :629-658, :782-822). -/
def WithdrawalShape (C : Codec) (Q : ChainParams) (b : Bundle) : Prop :=
  b.version = interopBundleVersion ∧ b.sourceChainId = Q.chainId ∧
    b.destinationChainId = Q.l1ChainId ∧ b.destinationBaseTokenAssetId = C.ethAssetId Q.l1ChainId ∧
    ∃ c, b.calls = [c] ∧ c.version = interopCallVersion ∧ c.shadowAccount = false ∧
      c.fromAddr = l2AssetRouterAddr ∧ c.value = 0 ∧ c.target ≠ 0

/-- One L1 dispatch of the center: the bundle and the transaction number of its message. -/
structure Dispatch where
  bundle : Bundle
  txNumber : ℕ
deriving DecidableEq

/-- One chain's L2→L1 output, and the center's L1 dispatches (ghost). -/
structure L2State where
  out : List L2Log
  dispatched : List Dispatch

/-- Genesis: no log, no dispatch. -/
def L2State.init : L2State := ⟨[], []⟩

/-- The steps that write the chain's L2→L1 output. -/
inductive Step (C : Codec) (Q : ChainParams) (H : HookSem) : L2State → L2State → Prop
  /-- A successful `sendBundle` to L1: the messenger, called by the center, calls the messenger hook
  with `(L2_INTEROP_CENTER_ADDR, BUNDLE_IDENTIFIER ++ abi.encode(b))` (IC:735, LM:44). -/
  | withdrawal (S : L2State) (b : Bundle) (t : ℕ) : WithdrawalShape C Q b →
      Step C Q H S ⟨S.out ++ (H.messengerHook l2ToL1MessengerAddr t
        (l2InteropCenterAddr, bundleIdentifier :: C.enc b)).toList, S.dispatched ++ [⟨b, t⟩]⟩
  /-- `sendToL1(m)` called by an account `a` other than the center (LM:44). -/
  | message (S : L2State) (a : Address) (m : Bytes) (t : ℕ) : a ≠ l2InteropCenterAddr →
      Step C Q H S ⟨S.out ++ (H.messengerHook l2ToL1MessengerAddr t (a, m)).toList, S.dispatched⟩
  /-- An account `c` other than the messenger calls the messenger hook directly. -/
  | hookCall (S : L2State) (c : Address) (x : Address × Bytes) (t : ℕ) :
      c ≠ l2ToL1MessengerAddr →
      Step C Q H S ⟨S.out ++ (H.messengerHook c t x).toList, S.dispatched⟩
  /-- An account `c` calls the leaf hook with `v`. -/
  | leafCall (S : L2State) (c : Address) (v : Word) (t : ℕ) :
      Step C Q H S ⟨S.out ++ (H.leafHook c t v).toList, S.dispatched⟩
  /-- A bootloader log (`MessageHashing.sol:39-62`). -/
  | bootloaderLog (S : L2State) (L : L2Log) : L.sender = l2BootloaderAddr →
      Step C Q H S ⟨S.out ++ [L], S.dispatched⟩

/-- Runs of steps. -/
inductive Reach (C : Codec) (Q : ChainParams) (H : HookSem) : L2State → L2State → Prop
  | refl (S : L2State) : Reach C Q H S S
  | tail {S S₁ S₂ : L2State} : Reach C Q H S S₁ → Step C Q H S₁ S₂ → Reach C Q H S S₂

/-- The message log of a center dispatch. -/
def dispatchLog (C : Codec) (d : Dispatch) : L2Log :=
  messageLog C d.txNumber l2InteropCenterAddr (bundleIdentifier :: C.enc d.bundle)

/-! ## Witness data -/

/-- Chain `270`, whose center stores L1 chain id `1`. -/
def wChain : ChainParams := ⟨270, 1⟩

/-- Hooks as documented: the messenger hook records for 0x8008 only; the leaf hook records, for the
tree only, a log attributed to the tree. -/
def wGatedHooks : HookSem where
  messengerHook c t x :=
    if c = l2ToL1MessengerAddr then some (messageLog wCodec t x.1 x.2) else none
  leafHook c t v := if c = l2CommitmentTreeAddr then some ⟨0, true, t, l2CommitmentTreeAddr, 0, v⟩
    else none

/-- The messenger hook records for every caller; otherwise as `wGatedHooks`. -/
def wUngatedHooks : HookSem where
  messengerHook _ t x := some (messageLog wCodec t x.1 x.2)
  leafHook := wGatedHooks.leafHook

/-- An account with no role. -/
def wForger : Address := 0xF00

/-- After the center withdraws `wOne` in transaction `0`. -/
def wS₁ (H : HookSem) : L2State :=
  ⟨L2State.init.out ++ (H.messengerHook l2ToL1MessengerAddr 0
      (l2InteropCenterAddr, bundleIdentifier :: wCodec.enc wOne)).toList,
    L2State.init.dispatched ++ [⟨wOne, 0⟩]⟩

/-- Then `wForger` sends the message `[0x42]` in transaction `1`. -/
def wS₂ (H : HookSem) : L2State :=
  ⟨(wS₁ H).out ++ (H.messengerHook l2ToL1MessengerAddr 1 (wForger, [0x42])).toList,
    (wS₁ H).dispatched⟩

/-- Then `wForger` calls the messenger hook directly in transaction `2`, with calldata naming the
center as sender and `BUNDLE_IDENTIFIER ++ abi.encode(wTwo)` as message. -/
def wS₃ (H : HookSem) : L2State :=
  ⟨(wS₂ H).out ++ (H.messengerHook wForger 2
      (l2InteropCenterAddr, bundleIdentifier :: wCodec.enc wTwo)).toList, (wS₂ H).dispatched⟩

/-- Then the tree inserts the value `7` in transaction `3`. -/
def wS₄ (H : HookSem) : L2State :=
  ⟨(wS₃ H).out ++ (H.leafHook l2CommitmentTreeAddr 3 7).toList, (wS₃ H).dispatched⟩

end Contracts.L1MessengerKeying
