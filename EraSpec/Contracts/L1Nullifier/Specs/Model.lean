import EraSpec.Core.Word

/-!
# Model: `L1Nullifier` and the L1 asset router's deposit-record paths

Source: era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`. Paths are
relative to `l1-contracts/contracts/`; `N` is `bridge/L1Nullifier.sol`, `R` is
`bridge/asset-router/L1AssetRouter.sol`, `RB` is `bridge/asset-router/AssetRouterBase.sol`,
`BH` is `core/bridgehub/L1Bridgehub.sol`.

**This file is definitions only.** The statements are in
`EraSpec.Contracts.L1Nullifier.Properties.Model` and are proved in
`EraSpec.Contracts.L1Nullifier.Proofs.Model`.

## What the nullifier does at this pin

At v0.35.0 the nullifier keeps one live mapping, `depositHappened[chainId][l2TxHash]`
(`N:67-69`), the data hash of an initiated L1 → L2 deposit. Withdrawal finalization moved to the
interop handler: `__DEPRECATED_isWithdrawalFinalized` (`N:75-76`) and every legacy-bridge slot
(`N:45-62`, `:81-92`) are "no longer read or written". So the nullifier is now a deposit ledger:

1. **Record.** `bridgehubConfirmL2TransactionForwarded(c, v, h)` (`N:155-163`) is `onlyAssetRouter`
   (`N:105-108`) and `whenNotPaused`, then

        require(depositHappened[_chainId][_txHash] == 0x00, DepositExists());   // N:160
        depositHappened[_chainId][_txHash] = _txDataHash;                          // N:161

   The asset router calls it only from `bridgehubConfirmL2Transaction` (`R:244-250`, `onlyBridgehub`,
   `whenNotPaused`), and the bridgehub calls that only at the end of
   `requestL2TransactionTwoBridges` (`BH:260-264`) with the `txDataHash` the router itself returned
   from `bridgehubDeposit` (`R:201-241`). That is
   `DataEncoding.encodeTxDataHash(originalCaller, assetId, transferData)` for a deposit
   (`RB:162-166`; the version byte must be `NEW_ENCODING_VERSION`, else `UnsupportedEncodingVersion`,
   `RB:125-137`), and `bytes32(0)` for a `SET_ASSET_HANDLER_COUNTERPART` request (`R:216-227`, `:181`).
2. **Clear.** `bridgeConfirmTransferResult(data)` (`N:166-177`) and
   `bridgeRecoverFailedTransfer(...)` (`N:180-213`, the same with `_txStatus = Failure`) are
   `nonReentrant` and run `_verifyAndClearTransfer` (`N:218-248`, `whenNotPaused`):

        bool proofValid = MESSAGE_ROOT.proveL1ToL2TransactionStatusShared({... _status: ...}); // N:222-230
        require(proofValid, InvalidProof());                                                    // N:231
        bytes32 dataHash = depositHappened[chainId][l2TxHash];                                  // N:235-237
        bytes32 txDataHash = DataEncoding.encodeTxDataHash(depositSender, assetId, assetData);  // N:238-242
        if (dataHash != txDataHash) revert DepositDoesNotExist(dataHash, txDataHash);           // N:243-245
        delete depositHappened[chainId][l2TxHash];                                              // N:247

   and then call `l1AssetRouter.bridgeConfirmTransferResult(chainId, status, sender, assetId,
   data)` (`N:170-176`, `:206-212`). The router's function (`R:306-325`) is `onlyNullifier`,
   `nonReentrant`, `whenNotPaused`, checks the asset handler is allowed and forwards to it.
3. **Configuration.** `initialize` (`N:122-125`, `initializer`), the set-once owner setters
   `setL1NativeTokenVault` (`N:130-134`), `setL1AssetRouter` (`N:139-143`),
   `setL1InteropHandler` (`N:148-152`), `pause`/`unpause` (`N:255-262`), and the inherited
   `Ownable2StepUpgradeable` calls (`transferOwnership`, `acceptOwnership`, `renounceOwnership`).

## Modelling choices

* **One step is one successful top-level call**; a revert is the absence of a step. The
  `nonReentrant` guards are not modelled: each step is atomic and no callback is modelled
  (`MODEL-NULLIFIER`). `_verifyAndClearTransfer` clears the slot before the external call
  (`N:247` before `N:170`), so a nested claim would see the cleared slot in any case.
* **Callers.** `ExternalSender` is a caller other than `0` and the three system contracts
  (nullifier, router, bridgehub). Those contracts issue only the calls their code issues, which are
  the composite steps below: the bridgehub's `requestL2TransactionTwoBridges` → router →
  nullifier chain is `twoBridges`, and the nullifier's call to the router is part of `confirm` and
  `recover`. That the system contracts' addresses do not appear as external callers is `VM-CALL`.
* **The hash** `encodeTxDataHash` is an arbitrary function `Env.txDataHash : Triple → Bytes32`;
  no injectivity is assumed anywhere in the model. The legacy hash format the source mentions
  (`DataEncoding.sol:164-166`) has no writer at this pin.
* **The status proof.** `Env.accepts q` is the set of queries for which
  `proveL1ToL2TransactionStatusShared` may return `true` at some time (the message root's
  answers can change as batches settle; taking the union over time covers every schedule).
  Soundness of that oracle is a theorem premise, never part of the model (`PROTO-TX-STATUS`).
* **Reject-only checks downstream are omitted**, which only adds runs: the bridgehub's own
  guards and `_sendRequest`, the router's `_checkAssetHandlerAllowed`, `baseTokenAssetId` and
  `msg.value` checks, the vault's `_burn`, and the asset handler's `bridgeConfirmTransferResult`
  (the native token vault rejects `Success`, `L1NativeTokenVault.sol:358`). Their effects outside
  the two contracts' storage are not modelled. If the nullifier's `l1AssetRouter` is not the router,
  the nullifier's call goes to an unmodelled contract, which may accept.
* **The router's pause flag** is `Sys.routerPaused`; the router's owner is not modelled, so
  `routerSetPaused` may fire at any time (an over-approximation).
* **Checks.** The four source checks that the countermodels remove are flags of `Checks`;
  the source is `Checks.source`, all `true`. Every safety statement is about `Checks.source`.
* **Ghost log.** `Sys.log` records each write to `depositHappened` with its origin, each clear,
  and each call into the asset handler that did not come through a clear. It is not contract state.
-/

namespace Contracts.L1Nullifier

/-- A 20-byte address, as a word. -/
abbrev Address := UInt256
/-- A chain id. -/
abbrev ChainId := UInt256
/-- A `bytes32`. -/
abbrev Bytes32 := UInt256
/-- A `bytes` value. -/
abbrev Bytes := List UInt8

/-- `TxStatus` (`common/Messaging.sol:12-15`). -/
inductive TxStatus
  | failure
  | success
  deriving DecidableEq, Repr

/-- The three inputs of `DataEncoding.encodeTxDataHash` (`common/libraries/DataEncoding.sol:159-170`):
`(originalCaller, assetId, transferData)`. -/
structure Triple where
  sender : Address
  assetId : Bytes32
  data : Bytes
  deriving DecidableEq

/-- `ConfirmTransferResultData` (`common/Messaging.sol:357-368`), the claim of one deposit's result. -/
structure Claim where
  chainId : ChainId
  depositSender : Address
  l2TxNumberInBatch : ℕ
  txStatus : TxStatus
  assetId : Bytes32
  assetData : Bytes
  l2TxHash : Bytes32
  l2BatchNumber : UInt256
  l2MessageIndex : UInt256
  merkleProof : List Bytes32
  deriving DecidableEq

/-- The triple the claim hashes (`N:238-242`). -/
def Claim.triple (cl : Claim) : Triple := ⟨cl.depositSender, cl.assetId, cl.assetData⟩

/-- The arguments of `MESSAGE_ROOT.proveL1ToL2TransactionStatusShared` (`N:222-230`). -/
structure StatusQuery where
  chainId : ChainId
  l2TxHash : Bytes32
  l2BatchNumber : UInt256
  l2MessageIndex : UInt256
  l2TxNumberInBatch : ℕ
  merkleProof : List Bytes32
  status : TxStatus

/-- The status query a claim makes (`N:222-230`). -/
def Claim.query (cl : Claim) : StatusQuery :=
  ⟨cl.chainId, cl.l2TxHash, cl.l2BatchNumber, cl.l2MessageIndex, cl.l2TxNumberInBatch,
    cl.merkleProof, cl.txStatus⟩

/-- `bridgeRecoverFailedTransfer` builds the claim with `_txStatus: TxStatus.Failure` (`N:191-204`). -/
def Claim.asFailure (cl : Claim) : Claim := { cl with txStatus := .failure }

/-- The environment the two contracts read. -/
structure Env where
  /-- `DataEncoding.encodeTxDataHash` (keccak of `0x01 ‖ abi.encode(...)`), arbitrary. -/
  txDataHash : Triple → Bytes32
  /-- The queries `proveL1ToL2TransactionStatusShared` may answer `true` to, at some time. -/
  accepts : StatusQuery → Prop

/-- The addresses of the three system contracts (immutables: `R:47`, `R:56`; the bridgehub's
`assetRouter`). -/
structure Cfg where
  nullifier : Address
  router : Address
  bridgehub : Address

/-- The source checks a countermodel may remove. `Checks.source` is the contract. -/
structure Checks where
  /-- `require(proofValid, InvalidProof())` (`N:231`). -/
  proof : Bool
  /-- `if (dataHash != txDataHash) revert DepositDoesNotExist(...)` (`N:243-245`). -/
  dataHash : Bool
  /-- `require(depositHappened[..][..] == 0x00, DepositExists())` (`N:160`). -/
  depositExists : Bool
  /-- `onlyNullifier` on the router's `bridgeConfirmTransferResult` (`R:70-73`, `:312`). -/
  onlyNullifier : Bool

/-- The contract: every check present. -/
def Checks.source : Checks := ⟨true, true, true, true⟩

/-- The deprecated storage of the nullifier (`N:45-62`, `:75-92`), kept only for layout. -/
structure Deprecated where
  eraPostDiamondUpgradeFirstBatch : UInt256
  eraPostLegacyBridgeUpgradeFirstBatch : UInt256
  eraLegacyBridgeLastDepositBatch : UInt256
  eraLegacyBridgeLastDepositTxNumber : UInt256
  legacyBridge : Address
  l2BridgeAddress : ChainId → Address
  isWithdrawalFinalized : ChainId → UInt256 → UInt256 → Bool
  hyperbridgingEnabled : ChainId → Bool
  chainBalance : ChainId → Address → UInt256
  admin : Address
  pendingAdmin : Address

/-- The nullifier's storage (proxy storage, so it starts wherever the deployment left it). -/
structure Nullifier where
  /-- OpenZeppelin `Initializable`: whether `initialize` has run. -/
  initialized : Bool
  /-- `Ownable2StepUpgradeable.owner()`. -/
  owner : Address
  /-- `Ownable2StepUpgradeable.pendingOwner()`. -/
  pendingOwner : Address
  /-- `PausableUpgradeable.paused()`. -/
  paused : Bool
  /-- `depositHappened` (`N:67-69`). -/
  depositHappened : ChainId → Bytes32 → Bytes32
  /-- `l1AssetRouter` (`N:95`). -/
  l1AssetRouter : Address
  /-- `l1NativeTokenVault` (`N:98`). -/
  l1NativeTokenVault : Address
  /-- `l1InteropHandler` (`N:102`). -/
  l1InteropHandler : Address
  /-- The deprecated slots. -/
  deprecated : Deprecated

/-- Write one entry of `depositHappened`. -/
def setSlot (m : ChainId → Bytes32 → Bytes32) (c : ChainId) (h v : Bytes32) :
    ChainId → Bytes32 → Bytes32 :=
  fun c' h' => if c' = c ∧ h' = h then v else m c' h'

/-- Who wrote a `depositHappened` entry. -/
inductive Origin
  /-- The bridgehub's two-bridges deposit of this triple, through the router (`BH:260`, `R:249`). -/
  | deposit (t : Triple)
  /-- The bridgehub's two-bridges counterpart registration through the router (hash `0`). -/
  | counterpart
  /-- A direct call by the address configured as `l1AssetRouter`. -/
  | direct (sender : Address)
  deriving DecidableEq

/-- The ghost log. -/
inductive Event
  /-- `depositHappened[c][h] = v` was written. -/
  | write (o : Origin) (c : ChainId) (h : Bytes32) (v : Bytes32)
  /-- A claim cleared its slot and the nullifier called `target.bridgeConfirmTransferResult`. -/
  | clear (cl : Claim) (target : Address)
  /-- A call into the asset handler that did not come through the nullifier. -/
  | handler (c : ChainId) (st : TxStatus) (t : Triple)
  deriving DecidableEq

/-- The two contracts' modelled state, with the ghost log. -/
structure Sys where
  n : Nullifier
  /-- The router's `PausableUpgradeable.paused()`. -/
  routerPaused : Bool
  log : List Event

/-- A caller of a top-level call: not zero and not one of the system contracts (`VM-CALL`). -/
def ExternalSender (cfg : Cfg) (a : Address) : Prop :=
  a ≠ 0 ∧ a ≠ cfg.nullifier ∧ a ≠ cfg.router ∧ a ≠ cfg.bridgehub

/-- The second-bridge request the router answers in `bridgehubDeposit` (`R:201-241`). -/
inductive SecondBridge
  /-- `NEW_ENCODING_VERSION`: a deposit of `data` for `assetId` (`RB:140-183`). -/
  | deposit (assetId : Bytes32) (data : Bytes)
  /-- `SET_ASSET_HANDLER_COUNTERPART_ENCODING_VERSION`: `txDataHash: bytes32(0x00)` (`R:181`). -/
  | counterpart

/-- The origin recorded for a request by `caller`. -/
def SecondBridge.origin (caller : Address) : SecondBridge → Origin
  | .deposit a d => .deposit ⟨caller, a, d⟩
  | .counterpart => .counterpart

/-- `outputRequest.txDataHash` (`BH:262`): `encodeTxDataHash(caller, assetId, transferData)` for a
deposit (`RB:162-166`), zero for a counterpart registration (`R:181`). -/
def SecondBridge.hash (env : Env) (caller : Address) : SecondBridge → Bytes32
  | .deposit a d => env.txDataHash ⟨caller, a, d⟩
  | .counterpart => 0

/-- One top-level call. -/
inductive Label
  | initialize (sender owner : Address)
  | transferOwnership (sender newOwner : Address)
  | acceptOwnership (sender : Address)
  | renounceOwnership (sender : Address)
  | setL1NativeTokenVault (sender a : Address)
  | setL1AssetRouter (sender a : Address)
  | setL1InteropHandler (sender a : Address)
  | pause (sender : Address)
  | unpause (sender : Address)
  /-- `bridgehubConfirmL2TransactionForwarded(c, v, h)` called directly. -/
  | forwarded (sender : Address) (c : ChainId) (v h : Bytes32)
  /-- `bridgeConfirmTransferResult(cl)` (`N:166-177`). -/
  | confirm (sender : Address) (cl : Claim)
  /-- `bridgeRecoverFailedTransfer(...)` (`N:180-213`); the claim's status is ignored. -/
  | recover (sender : Address) (cl : Claim)
  /-- `requestL2TransactionTwoBridges` by `caller` with the router as second bridge, whose
  canonical transaction hash is `h` (`BH:200-264`). -/
  | twoBridges (caller : Address) (c : ChainId) (req : SecondBridge) (h : Bytes32)
  /-- The router's `bridgeConfirmTransferResult` (`R:306-325`) called directly. -/
  | routerConfirm (sender : Address) (c : ChainId) (st : TxStatus) (t : Triple)
  /-- The router owner's `pause`/`unpause` (`RB:378-385`). -/
  | routerSetPaused (b : Bool)

/-- The guards of `_verifyAndClearTransfer` and of the call to the router, in source order:
`whenNotPaused` (`N:220`), the proof (`N:231`), the data hash (`N:243-245`); then, if the target is
the router, the router's `whenNotPaused` (`R:312`; `onlyNullifier` holds, the caller is the
nullifier). -/
structure ClaimOk (chk : Checks) (env : Env) (cfg : Cfg) (s : Sys) (cl : Claim) : Prop where
  notPaused : s.n.paused = false
  proof : chk.proof = true → env.accepts cl.query
  dataHash : chk.dataHash = true →
    s.n.depositHappened cl.chainId cl.l2TxHash = env.txDataHash cl.triple
  routerLive : s.n.l1AssetRouter = cfg.router → s.routerPaused = false

/-- The state after a claim: the slot deleted (`N:247`), the call to `l1AssetRouter` logged. -/
def afterClaim (s : Sys) (cl : Claim) : Sys :=
  { s with
    n := { s.n with depositHappened := setSlot s.n.depositHappened cl.chainId cl.l2TxHash 0 }
    log := s.log ++ [.clear cl s.n.l1AssetRouter] }

/-- The state after a write of `v` at `(c, h)` by origin `o` (`N:161`). -/
def afterWrite (s : Sys) (o : Origin) (c : ChainId) (h v : Bytes32) : Sys :=
  { s with
    n := { s.n with depositHappened := setSlot s.n.depositHappened c h v }
    log := s.log ++ [.write o c h v] }

/-- One successful top-level call. -/
inductive Step (chk : Checks) (env : Env) (cfg : Cfg) : Sys → Label → Sys → Prop
  /-- `initialize` (`N:122-125`): `initializer`, nonzero owner, `_transferOwnership`
  (which also deletes `pendingOwner`). -/
  | initialize {s : Sys} {a o : Address} :
      ExternalSender cfg a → s.n.initialized = false → o ≠ 0 →
      Step chk env cfg s (.initialize a o)
        { s with n := { s.n with initialized := true, owner := o, pendingOwner := 0 } }
  /-- `Ownable2Step.transferOwnership`: `onlyOwner`, sets the pending owner. -/
  | transferOwnership {s : Sys} {a x : Address} :
      ExternalSender cfg a → a = s.n.owner →
      Step chk env cfg s (.transferOwnership a x) { s with n := { s.n with pendingOwner := x } }
  /-- `Ownable2Step.acceptOwnership`: the pending owner becomes the owner. -/
  | acceptOwnership {s : Sys} {a : Address} :
      ExternalSender cfg a → a = s.n.pendingOwner →
      Step chk env cfg s (.acceptOwnership a)
        { s with n := { s.n with owner := a, pendingOwner := 0 } }
  /-- `Ownable.renounceOwnership`: `onlyOwner`, owner and pending owner become zero. -/
  | renounceOwnership {s : Sys} {a : Address} :
      ExternalSender cfg a → a = s.n.owner →
      Step chk env cfg s (.renounceOwnership a)
        { s with n := { s.n with owner := 0, pendingOwner := 0 } }
  /-- `setL1NativeTokenVault` (`N:130-134`). -/
  | setL1NativeTokenVault {s : Sys} {a x : Address} :
      ExternalSender cfg a → a = s.n.owner → s.n.l1NativeTokenVault = 0 → x ≠ 0 →
      Step chk env cfg s (.setL1NativeTokenVault a x)
        { s with n := { s.n with l1NativeTokenVault := x } }
  /-- `setL1AssetRouter` (`N:139-143`). -/
  | setL1AssetRouter {s : Sys} {a x : Address} :
      ExternalSender cfg a → a = s.n.owner → s.n.l1AssetRouter = 0 → x ≠ 0 →
      Step chk env cfg s (.setL1AssetRouter a x) { s with n := { s.n with l1AssetRouter := x } }
  /-- `setL1InteropHandler` (`N:148-152`). -/
  | setL1InteropHandler {s : Sys} {a x : Address} :
      ExternalSender cfg a → a = s.n.owner → s.n.l1InteropHandler = 0 → x ≠ 0 →
      Step chk env cfg s (.setL1InteropHandler a x)
        { s with n := { s.n with l1InteropHandler := x } }
  /-- `pause` (`N:255-257`): `onlyOwner`, then `_pause` (`whenNotPaused`). -/
  | pause {s : Sys} {a : Address} :
      ExternalSender cfg a → a = s.n.owner → s.n.paused = false →
      Step chk env cfg s (.pause a) { s with n := { s.n with paused := true } }
  /-- `unpause` (`N:260-262`): `onlyOwner`, then `_unpause` (`whenPaused`). -/
  | unpause {s : Sys} {a : Address} :
      ExternalSender cfg a → a = s.n.owner → s.n.paused = true →
      Step chk env cfg s (.unpause a) { s with n := { s.n with paused := false } }
  /-- `bridgehubConfirmL2TransactionForwarded` called directly (`N:155-163`): `onlyAssetRouter`,
  `whenNotPaused`, `DepositExists`. -/
  | forwarded {s : Sys} {a : Address} {c : ChainId} {v h : Bytes32} :
      ExternalSender cfg a → a = s.n.l1AssetRouter → s.n.paused = false →
      (chk.depositExists = true → s.n.depositHappened c h = 0) →
      Step chk env cfg s (.forwarded a c v h) (afterWrite s (.direct a) c h v)
  /-- `bridgeConfirmTransferResult` (`N:166-177`). -/
  | confirm {s : Sys} {a : Address} {cl : Claim} :
      ExternalSender cfg a → ClaimOk chk env cfg s cl →
      Step chk env cfg s (.confirm a cl) (afterClaim s cl)
  /-- `bridgeRecoverFailedTransfer` (`N:180-213`): the claim with status `Failure`. -/
  | recover {s : Sys} {a : Address} {cl : Claim} :
      ExternalSender cfg a → ClaimOk chk env cfg s cl.asFailure →
      Step chk env cfg s (.recover a cl) (afterClaim s cl.asFailure)
  /-- The bridgehub's `requestL2TransactionTwoBridges` with the router as second bridge: the
  router's `bridgehubDeposit` (`whenNotPaused`, `R:212`) returns `req.hash`, the bridgehub calls the
  router's `bridgehubConfirmL2Transaction` (`whenNotPaused`, `R:248`), which calls the nullifier
  (`onlyAssetRouter`: the nullifier's `l1AssetRouter` must be the router; `whenNotPaused`;
  `DepositExists`). -/
  | twoBridges {s : Sys} {caller : Address} {c : ChainId} {req : SecondBridge} {h : Bytes32} :
      s.routerPaused = false → cfg.router = s.n.l1AssetRouter → s.n.paused = false →
      (chk.depositExists = true → s.n.depositHappened c h = 0) →
      Step chk env cfg s (.twoBridges caller c req h)
        (afterWrite s (req.origin caller) c h (req.hash env caller))
  /-- The router's `bridgeConfirmTransferResult` called directly (`R:306-325`): `onlyNullifier`,
  `whenNotPaused`; it would call the asset handler. -/
  | routerConfirm {s : Sys} {a : Address} {c : ChainId} {st : TxStatus} {t : Triple} :
      ExternalSender cfg a → (chk.onlyNullifier = true → a = cfg.nullifier) →
      s.routerPaused = false →
      Step chk env cfg s (.routerConfirm a c st t) { s with log := s.log ++ [.handler c st t] }
  /-- The router owner's `pause`/`unpause`. -/
  | routerSetPaused {s : Sys} {b : Bool} :
      Step chk env cfg s (.routerSetPaused b) { s with routerPaused := b }

/-- Runs: any sequence of steps, any interleaving of the entry points. -/
inductive Reach (chk : Checks) (env : Env) (cfg : Cfg) : Sys → Sys → Prop
  | refl (s : Sys) : Reach chk env cfg s s
  | step {s t u : Sys} {l : Label} : Reach chk env cfg s t → Step chk env cfg t l u →
      Reach chk env cfg s u

/-! ## Counting the log -/

/-- `e` is a write of a nonzero value at `(c, h)`. -/
def isNzWrite (c : ChainId) (h : Bytes32) : Event → Bool
  | .write _ c' h' v => decide (c' = c ∧ h' = h ∧ v ≠ 0)
  | _ => false

/-- `e` is a clear of `(c, h)`. -/
def isClear (c : ChainId) (h : Bytes32) : Event → Bool
  | .clear cl _ => decide (cl.chainId = c ∧ cl.l2TxHash = h)
  | _ => false

/-- `e` is a clear of `(c, h)` whose triple hashes to zero. -/
def isZeroClear (env : Env) (c : ChainId) (h : Bytes32) : Event → Bool
  | .clear cl _ => decide (cl.chainId = c ∧ cl.l2TxHash = h ∧ env.txDataHash cl.triple = 0)
  | _ => false

/-- `1` if the slot is occupied, else `0`. -/
def occupied (n : Nullifier) (c : ChainId) (h : Bytes32) : ℕ :=
  if n.depositHappened c h = 0 then 0 else 1

/-- A call reached the asset handler without a clear. -/
def isHandler : Event → Bool
  | .handler _ _ _ => true
  | _ => false

/-- The nullifier's `l1AssetRouter` is unset or the router. -/
def RouterConfigured (cfg : Cfg) (s : Sys) : Prop :=
  s.n.l1AssetRouter = 0 ∨ s.n.l1AssetRouter = cfg.router

/-- A clear of `cl` is backed by what precedes it in the log, `pre`, given the start storage `n0`:
its triple hashes to zero, or to the start value of its slot, or to the value a write in `pre`
put in that slot. -/
def Backed (env : Env) (n0 : Nullifier) (pre : List Event) (cl : Claim) : Prop :=
  env.txDataHash cl.triple = 0 ∨
  n0.depositHappened cl.chainId cl.l2TxHash = env.txDataHash cl.triple ∨
  ∃ o, Event.write o cl.chainId cl.l2TxHash (env.txDataHash cl.triple) ∈ pre

end Contracts.L1Nullifier
