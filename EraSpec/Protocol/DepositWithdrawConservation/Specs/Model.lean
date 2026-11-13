import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# End-to-end deposit / withdrawal conservation for one L1-native token

**This file is definitions only.**  The guarantees are stated in
`EraSpec.Protocol.DepositWithdrawConservation.Properties.Model` and proved in
`EraSpec.Protocol.DepositWithdrawConservation.Proofs.Model`.

Source: era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`,
`l1-contracts/contracts/`.  Every `file:line` below is at that commit.

## What is modelled

One ERC20 token native to L1, registered in `L1NativeTokenVault` under asset id `a`
with the vault as its asset handler, bridged to chains `c : ι` that have no interop
(`MessageRoot.isInteropEnabled(c) = false`, so `_trackedBalance(c, L1) = (true, c)`,
`bridge/ntv/L1NativeTokenVault.sol:468-477`).  The model is the projection of the
following onto that one asset.

* **L1 deposit** (`Action.deposit`): `L1AssetRouter.bridgehubDeposit`
  (`bridge/asset-router/L1AssetRouter.sol:201-241`)
  → `AssetRouterBase._bridgehubDepositNonBaseTokenAsset` (`bridge/asset-router/AssetRouterBase.sol:140-183`)
  → `_burn` (`:303-331`) → `NativeTokenVaultBase.bridgeBurn`
  (`bridge/ntv/NativeTokenVaultBase.sol:294-318`) → `_bridgeBurnToken` (`:361-410`,
  `require(_amount != 0)` at `:370`) → `_getTokenAndBridgeToChain` (`:425-457`)
  → `L1NativeTokenVault._handleBridgeToChain` (`L1NativeTokenVault.sol:424-433`) and
  `_depositFunds` (`NativeTokenVaultBase.sol:468-475`); then, in the same L1
  transaction, the Bridgehub's `L1AssetRouter.bridgehubConfirmL2Transaction`
  (`L1AssetRouter.sol:244-250`) → `L1Nullifier.bridgehubConfirmL2TransactionForwarded`
  (`bridge/L1Nullifier.sol:155-163`, `DepositExists` at `:160`).
* **L2 execution of the deposit** (`Action.l2Mint`, `Action.l2Fail`):
  `L2AssetRouter.finalizeDeposit` (`bridge/asset-router/L2AssetRouter.sol:253-262`)
  → `NativeTokenVaultBase.bridgeMint` (`NativeTokenVaultBase.sol:180-189`), which mints the
  bridged token (`:243`); or the priority transaction fails.
* **L2 withdrawal** (`Action.l2Withdraw`): `L2AssetRouter.initiateIndirectCall`
  (`L2AssetRouter.sol:331-361`) → `NativeTokenVaultBase.bridgeBurn`, which burns the bridged
  token (`NativeTokenVaultBase.sol:450`); the call sent to L1 is
  `finalizeDeposit(block.chainid, a, mintData)` (`AssetRouterBase.sol:365-371`).
* **L1 finalization of a withdrawal**:
  `L1InteropHandler.verifyBundle` (`interop/interop-handler/L1InteropHandler.sol:103-110`,
  `Action.verify`); `L1InteropHandler.executeBundle` (`:81-98`, `Action.execute`) with
  `_validateExecutable` (`interop/interop-handler/InteropHandlerBase.sol:292-300`),
  `_verifyBundle` (`L1InteropHandler.sol:203-224`) → `_validateVerifiable`
  (`InteropHandlerBase.sol:306-314`) and `_markFullyExecutedAndRun` (`:325-342`);
  `InteropHandlerBase.unbundleBundle` (`:113-175`) with the requested call status
  `Executed` (`Action.unbundleExecute`), `Cancelled` (`Action.unbundleCancel`) or any other
  (`Action.unbundleSkip`).  An executed call runs
  `AssetRouterBase.receiveMessage` (`AssetRouterBase.sol:213-251`, source-chain equality
  `:235-239`) → `L1AssetRouter.finalizeDeposit` (`L1AssetRouter.sol:291-299`)
  → `_finalizeDeposit` (`AssetRouterBase.sol:267-283`) → `NativeTokenVaultBase.bridgeMint`
  → `_bridgeMintToken` (`NativeTokenVaultBase.sol:220-247`)
  → `L1NativeTokenVault._handleBridgeFromChain` (`L1NativeTokenVault.sol:439-459`) and
  `_withdrawFunds` (`:399-411`).
* **Confirmation of a deposit's L2 result / claim of a failed deposit**
  (`Action.confirm`, `Action.confirmOther`): `L1Nullifier.bridgeConfirmTransferResult`
  (`L1Nullifier.sol:166-177`, any status) and `bridgeRecoverFailedTransfer`
  (`:180-213`, status `Failure`) → `_verifyAndClearTransfer` (`:218-248`)
  → `L1AssetRouter.bridgeConfirmTransferResult` (`L1AssetRouter.sol:306-325`)
  → `L1NativeTokenVault.bridgeConfirmTransferResult` (`L1NativeTokenVault.sol:351-380`,
  `OnlyFailureStatusAllowed` at `:358`, `NoFundsTransferred` at `:361`)
  → `NativeTokenVaultBase._disburseFailedTransfer` (`NativeTokenVaultBase.sol:264-286`).
* **Donation** (`Action.donate`): anyone transfers the token to the vault directly.

Every entry point is `step … a s : Option (St ι)`; `none` is a revert (no step), and the
guards are the conjuncts of each `if`, in source order.  `Reach` is the closure under
every action from fresh storage, in any interleaving.

## The messages, and the authentication assumption (`PROTO-EVIDENCE`)

Cross-chain messages are not bytes here.  They are the two logs in the state:

* `dep i`, `i < nd`: the L1→L2 priority transactions created by bridge deposits, each with
  the L2 outcome `dst i`;
* `wd j`, `j < nw`: the L2→L1 bundles (one call each) sent through a chain's L2 interop
  center with the L2 asset router as the call's sender.

**Authentication assumption.**

1. *L1→L2 status proofs.*  For a chain with `bad c = false`,
   `MessageRoot.proveL1ToL2TransactionStatusShared(c, h, …, status)` (`L1Nullifier.sol:222-231`)
   returns `true` for the canonical hash `h` of bridge deposit `i` only if the transaction
   was executed on `c` with that status: `dst i = status`.  Each priority transaction is
   executed on L2 at most once with one outcome (`dst` only leaves `pending`), and a
   successful execution mints exactly the deposited amount.
2. *L2→L1 inclusion proofs.*  `MessageRoot.proveL2MessageInclusionShared(c, …)`
   (`L1InteropHandler.sol:226-236`) accepts a bundle for chain `c` only if `c` sent it: it is
   some `wd j`, `j < nw`, with `(wd j).chain = c`.  For `bad c = false` the bundle was
   produced by `l2Withdraw`: the bridged token was burned first, and the payload's
   `_sourceChainId` is `c`.
3. *Canonical hashes.*  The Bridgehub never gives two bridge deposits to one chain the
   same canonical transaction hash (the guard `∀ i < nd, …` of `deposit`; `PROTO-TXHASH`).
4. *Compromised chains.*  For `bad c = true` (compromised prover or operator) nothing is
   assumed: status proofs for its transactions are forgeable (`confirm` needs no L2
   outcome there), it sends arbitrary withdrawal bundles with any payload source chain
   (`forge`), and its bridged-token supply is arbitrary (`badMint`).

A status proof for a hash that is not a bridge deposit's (`confirmOther`) is not
constrained at all: some other L1→L2 transaction with that hash may exist, with any status.

## Hashes

`H` is `DataEncoding.encodeTxDataHash(originalCaller, a, transferData)`
(`AssetRouterBase.sol:162-166`) as a function of the caller and transfer data.  **No
property assumes anything of `H` globally.**  The guarantees that depend on it take the
pinned premise that the run's own deposits to the chain do not hash to the zero sentinel,
and the ghost flag `clash c = false`.  The flag is raised exactly when a confirmation on
`c` succeeded with data other than the confirmed deposit's own;
`Properties.ClashExhibitsPinnedCollision` shows that a raised flag exhibits data submitted
in the run that hashes to zero or collides with a logged deposit's data.

## Storage and ghost state

L1 storage: `escrow` (the token's balance of the vault), `bridgedOut[a]`,
`chainTotalDeposited[c][a]`, `chainTotalWithdrawn[c][a]`, `depositHappened[c][h]`, the
interop handler's `bundleStatus` and `callStatus` (keyed here by the bundle's log index
`j`; the contract keys them by bundle hash, see `MODEL-BUNDLE-ID` in the README).
L2 state: `supply c`, the bridged token's total supply on `c`.  Everything else is
protocol bookkeeping: the two logs, `dst`, and the ghosts `claims i` (confirmations of
deposit `i` with its own data), `fins j` (releases for bundle `j`), `clash`, `donated`.

## Not modelled (see the README)

Chains with interop and the interop pool; a nonzero `chainBalanceBackfill` (the `pend`
flag of the environment is `chainBalanceBackfillPending`, fixed along a run); the base
token; pause and caller permissions (they only remove steps); `uint256` overflow (amounts
are `ℕ`; overflowing steps revert in Solidity, so the model has more runs, not fewer);
per-holder L2 balances (only total supply); token registration; `populateBridgedOut`;
multi-call bundles from compromised chains; the L2 asset tracker.
-/

namespace Contracts.Protocol.DepositWithdrawConservation

/-- 256-bit words: canonical transaction hashes and stored data hashes. -/
abbrev Word := UInt256
/-- Addresses. -/
abbrev Address := UInt256

/-- What a deposit's `txDataHash` commits to, for the fixed asset: `_originalCaller` and
the bridge-burn data `(amount, receiver, tokenAddress)` (`DataEncoding.encodeTxDataHash`,
`AssetRouterBase.sol:162-166`). -/
structure TxData where
  /-- `_originalCaller` at deposit; `_depositSender`, who receives the refund, at claim. -/
  sender : Address
  /-- The L2 receiver in the burn data. -/
  receiver : Address
  /-- The burn data's token-address field (zero or the token). -/
  token : Address
  /-- The amount. -/
  amount : ℕ
deriving DecidableEq

/-- A bridge deposit: an L1→L2 priority transaction created by the L1 asset router. -/
structure Deposit (ι : Type) where
  /-- Destination chain. -/
  chain : ι
  /-- Canonical L1→L2 transaction hash. -/
  txHash : Word
  /-- The committed transfer data. -/
  data : TxData

/-- An L2→L1 withdrawal bundle with its single call.  `chain` is the chain whose message
root contains it (`_proof.chainId`, equal to the bundle's `sourceChainId` by
`InteropHandlerBase.sol:395-398`); `src` is the payload's `_sourceChainId`. -/
structure Withdrawal (ι : Type) where
  chain : ι
  src : ι
  receiver : Address
  amount : ℕ

/-- L2 outcome of an L1→L2 transaction.  For a bridge deposit, `succeeded` means
`finalizeDeposit` ran and minted. -/
inductive L2Status
  | pending
  | succeeded
  | failed
deriving DecidableEq

/-- The `TxStatus` argument of a confirmation (`common/Messaging.sol`). -/
inductive TxStatus
  | failure
  | success
deriving DecidableEq

/-- The L2 outcome a status proof for `st` attests. -/
def TxStatus.toL2 : TxStatus → L2Status
  | .failure => .failed
  | .success => .succeeded

/-- `BundleStatus` (`interop/interop-handler/IInteropHandlerBase.sol`). -/
inductive BundleStatus
  | unreceived
  | verified
  | fullyExecuted
  | unbundled
deriving DecidableEq

/-- `CallStatus` of the bundle's single call. -/
inductive CallStatus
  | unprocessed
  | executed
  | cancelled
deriving DecidableEq

/-- Protocol state for the one asset.  See the header for storage vs ghost. -/
structure St (ι : Type) where
  /-- `token.balanceOf(L1NativeTokenVault)` (exact counter, `MODEL-ESCROW`). -/
  escrow : ℕ
  /-- `L1NativeTokenVault.bridgedOut[a]` (`L1NativeTokenVault.sol:90`). -/
  bridgedOut : ℕ
  /-- `chainTotalDeposited[c][a]` (`L1NativeTokenVault.sol:96`). -/
  deposited : ι → ℕ
  /-- `chainTotalWithdrawn[c][a]` (`L1NativeTokenVault.sol:99`). -/
  withdrawn : ι → ℕ
  /-- `L1Nullifier.depositHappened[c][h]` (`L1Nullifier.sol:67-69`); `0` is unset. -/
  depositHappened : ι → Word → Word
  /-- `InteropHandlerBase.bundleStatus` of withdrawal bundle `j`. -/
  bundleStatus : ℕ → BundleStatus
  /-- `InteropHandlerBase.callStatus` of bundle `j`'s single call. -/
  callStatus : ℕ → CallStatus
  /-- Number of bridge deposits so far. -/
  nd : ℕ
  /-- The bridge deposits (meaningful below `nd`). -/
  dep : ℕ → Deposit ι
  /-- L2 outcome of each deposit's priority transaction. -/
  dst : ℕ → L2Status
  /-- Total supply of the bridged token on each chain. -/
  supply : ι → ℕ
  /-- Number of withdrawal bundles sent so far. -/
  nw : ℕ
  /-- The withdrawal bundles (meaningful below `nw`). -/
  wd : ℕ → Withdrawal ι
  /-- Ghost: successful confirmations of deposit `i` with its own data. -/
  claims : ℕ → ℕ
  /-- Ghost: number of releases made for bundle `j`. -/
  fins : ℕ → ℕ
  /-- Ghost: a confirmation on `c` succeeded with data other than the deposit's own. -/
  clash : ι → Bool
  /-- Ghost: total donated directly to the vault. -/
  donated : ℕ

variable {ι : Type}

/-- Fresh storage, empty message logs. -/
def init (ι : Type) [Inhabited ι] : St ι where
  escrow := 0
  bridgedOut := 0
  deposited := fun _ => 0
  withdrawn := fun _ => 0
  depositHappened := fun _ _ => 0
  bundleStatus := fun _ => .unreceived
  callStatus := fun _ => .unprocessed
  nd := 0
  dep := fun _ => ⟨default, 0, ⟨0, 0, 0, 0⟩⟩
  dst := fun _ => .pending
  supply := fun _ => 0
  nw := 0
  wd := fun _ => ⟨default, default, 0, 0⟩
  claims := fun _ => 0
  fins := fun _ => 0
  clash := fun _ => false
  donated := 0

/-- Which source checks and writes are in force.  `Checks.source` is the contract; each
countermodel switches exactly one off. -/
structure Checks where
  /-- `_requireExecutable` in `executeBundle` (`InteropHandlerBase.sol:282-287`, called at `:299`). -/
  requireExecutable : Bool
  /-- The write `bundleStatus[_bundleHash] = FullyExecuted` (`InteropHandlerBase.sol:326`). -/
  markExecuted : Bool
  /-- `senderChainId == payloadSourceChainId` (`AssetRouterBase.sol:235-239`). -/
  srcMatch : Bool
  /-- `require(proofValid, InvalidProof())` (`L1Nullifier.sol:222-231`). -/
  statusProof : Bool
  /-- `dataHash == txDataHash` (`L1Nullifier.sol:235-245`). -/
  hashCheck : Bool
  /-- `delete depositHappened[c][h]` (`L1Nullifier.sol:247`). -/
  clear : Bool
  /-- `require(_txStatus == TxStatus.Failure, …)` (`L1NativeTokenVault.sol:358`). -/
  failureOnly : Bool

/-- The contract as written: every check and write on. -/
def Checks.source : Checks := ⟨true, true, true, true, true, true, true⟩

/-- The environment of a run: the hash, which chains are compromised, and which chains
are pending their backfill. -/
structure Env (ι : Type) where
  /-- `encodeTxDataHash` for the fixed asset. -/
  H : TxData → Word
  /-- The chain's proofs and L2 state are not trusted. -/
  bad : ι → Bool
  /-- `chainBalanceBackfillPending[c]` (`L1NativeTokenVault.sol:108`): the per-chain cap is
  not enforced for `c` (`:450`). -/
  pend : ι → Bool

/-- Every entry point and environment move of the model. -/
inductive Action (ι : Type)
  /-- A bridge deposit of `d` to chain `c`, with canonical L1→L2 hash `h`. -/
  | deposit (c : ι) (h : Word) (d : TxData)
  /-- L2 executes deposit `i` successfully: `finalizeDeposit` mints. -/
  | l2Mint (i : ℕ)
  /-- L2 executes deposit `i` and it fails. -/
  | l2Fail (i : ℕ)
  /-- A holder on chain `c` withdraws `amount` to L1: burn, then the bundle is sent. -/
  | l2Withdraw (c : ι) (receiver : Address) (amount : ℕ)
  /-- A compromised chain mints `x` of the bridged token out of nothing. -/
  | badMint (c : ι) (x : ℕ)
  /-- A compromised chain `c` sends an arbitrary withdrawal bundle. -/
  | forge (c src : ι) (receiver : Address) (amount : ℕ)
  /-- `L1InteropHandler.verifyBundle` of bundle `j`. -/
  | verify (j : ℕ)
  /-- `L1InteropHandler.executeBundle` of bundle `j`. -/
  | execute (j : ℕ)
  /-- `unbundleBundle` of bundle `j`, requesting `Executed` for its call. -/
  | unbundleExecute (j : ℕ)
  /-- `unbundleBundle` of bundle `j`, requesting `Cancelled` for its call. -/
  | unbundleCancel (j : ℕ)
  /-- `unbundleBundle` of bundle `j`, requesting any other status (the call is skipped). -/
  | unbundleSkip (j : ℕ)
  /-- `bridgeConfirmTransferResult` with status `st` (`bridgeRecoverFailedTransfer` when
  `st = failure`) against bridge deposit `i`'s transaction, supplying data `d`. -/
  | confirm (i : ℕ) (st : TxStatus) (d : TxData)
  /-- The same against an L1→L2 transaction hash `h` on `c` that is no bridge deposit's. -/
  | confirmOther (c : ι) (h : Word) (st : TxStatus) (d : TxData)
  /-- Anyone transfers `x` tokens to the vault directly. -/
  | donate (x : ℕ)

variable [DecidableEq ι]

/-- `_handleBridgeFromChain(c, a, amt)` (`L1NativeTokenVault.sol:439-459`) followed by
`_withdrawFunds` (`:399-411`) succeed: `bridgedOut ≥ amt` (`:442-444`), the per-chain cap
unless the chain is pending its backfill (`:450-456`, zero backfill), and the token
transfer out of the vault. -/
abbrev ReleaseOk (E : Env ι) (s : St ι) (c : ι) (amt : ℕ) : Prop :=
  amt ≤ s.bridgedOut ∧ (E.pend c = false → s.withdrawn c + amt ≤ s.deposited c) ∧ amt ≤ s.escrow

/-- The effect of a successful release of `amt` charged to chain `c`
(`L1NativeTokenVault.sol:445`, `:457`, and the transfer). -/
def release (s : St ι) (c : ι) (amt : ℕ) : St ι :=
  { s with
    bridgedOut := s.bridgedOut - amt
    withdrawn := Function.update s.withdrawn c (s.withdrawn c + amt)
    escrow := s.escrow - amt }

/-- `delete depositHappened[c][h]` (`L1Nullifier.sol:247`) when `ck.clear`. -/
def clearSlot (ck : Checks) (s : St ι) (c : ι) (h : Word) : St ι :=
  if ck.clear = true then
    { s with depositHappened := fun c' h' => if c' = c ∧ h' = h then 0 else s.depositHappened c' h' }
  else s

/-- The asset-router call of a withdrawal bundle can run: `receiveMessage`'s source-chain
equality (`AssetRouterBase.sol:235-239`), then the vault's release charged to the payload's
`_sourceChainId`. -/
abbrev CallOk (ck : Checks) (E : Env ι) (s : St ι) (j : ℕ) : Prop :=
  (ck.srcMatch = true → (s.wd j).src = (s.wd j).chain)
    ∧ ReleaseOk E s (s.wd j).src (s.wd j).amount

/-- One entry point.  `none` = revert. -/
def step (ck : Checks) (E : Env ι) : Action ι → St ι → Option (St ι)
  | .deposit c h d, s =>
    -- `_bridgeBurnToken`: amount ≠ 0 (`NativeTokenVaultBase.sol:370`); Bridgehub: a canonical
    -- hash not used by an earlier bridge deposit to `c` (environment); nullifier:
    -- `DepositExists` (`L1Nullifier.sol:160`).
    if d.amount ≠ 0 ∧ (∀ i, i < s.nd → ¬ ((s.dep i).chain = c ∧ (s.dep i).txHash = h))
        ∧ s.depositHappened c h = 0 then
      some { s with
        bridgedOut := s.bridgedOut + d.amount
        deposited := Function.update s.deposited c (s.deposited c + d.amount)
        escrow := s.escrow + d.amount
        depositHappened := fun c' h' => if c' = c ∧ h' = h then E.H d else s.depositHappened c' h'
        nd := s.nd + 1
        dep := Function.update s.dep s.nd ⟨c, h, d⟩
        dst := Function.update s.dst s.nd .pending
        claims := Function.update s.claims s.nd 0 }
    else none
  | .l2Mint i, s =>
    if i < s.nd ∧ s.dst i = .pending then
      some { s with
        dst := Function.update s.dst i .succeeded
        supply := Function.update s.supply (s.dep i).chain
          (s.supply (s.dep i).chain + (s.dep i).data.amount) }
    else none
  | .l2Fail i, s =>
    if i < s.nd ∧ s.dst i = .pending then
      some { s with dst := Function.update s.dst i .failed }
    else none
  | .l2Withdraw c r amt, s =>
    -- `_bridgeBurnToken`: amount ≠ 0 (`NativeTokenVaultBase.sol:370`); the bridged token's
    -- `bridgeBurn` (`:450`) needs the holder's balance, hence at most the supply.
    if amt ≠ 0 ∧ amt ≤ s.supply c then
      some { s with
        supply := Function.update s.supply c (s.supply c - amt)
        nw := s.nw + 1
        wd := Function.update s.wd s.nw ⟨c, c, r, amt⟩ }
    else none
  | .badMint c x, s =>
    if E.bad c = true then
      some { s with supply := Function.update s.supply c (s.supply c + x) }
    else none
  | .forge c src r amt, s =>
    if E.bad c = true then
      some { s with
        nw := s.nw + 1
        wd := Function.update s.wd s.nw ⟨c, src, r, amt⟩ }
    else none
  | .verify j, s =>
    -- `_validateVerifiable`: status `Unreceived` (`InteropHandlerBase.sol:313`); inclusion
    -- proof (`L1InteropHandler.sol:221`).
    if s.bundleStatus j = .unreceived ∧ j < s.nw then
      some { s with bundleStatus := Function.update s.bundleStatus j .verified }
    else none
  | .execute j, s =>
    -- `_requireExecutable` (`InteropHandlerBase.sol:299`); unless `Verified`, `_verifyBundle`
    -- (`L1InteropHandler.sol:92-95`): status `Unreceived` and the inclusion proof; mark
    -- `FullyExecuted` and the call `Executed` (`InteropHandlerBase.sol:326-331`); run the call.
    if (ck.requireExecutable = true →
          s.bundleStatus j = .unreceived ∨ s.bundleStatus j = .verified)
        ∧ (s.bundleStatus j ≠ .verified → s.bundleStatus j = .unreceived ∧ j < s.nw)
        ∧ CallOk ck E s j then
      some { release s (s.wd j).src (s.wd j).amount with
        bundleStatus := Function.update s.bundleStatus j
          (if ck.markExecuted = true then .fullyExecuted else .verified)
        callStatus := Function.update s.callStatus j .executed
        fins := Function.update s.fins j (s.fins j + 1) }
    else none
  | .unbundleExecute j, s =>
    -- status `Verified` or `Unbundled` (`InteropHandlerBase.sol:139`); mark `Unbundled`
    -- (`:147`); the call must be `Unprocessed` (`:154`) and becomes `Executed` (`:155`);
    -- run the call (`:166-172`).
    if (s.bundleStatus j = .verified ∨ s.bundleStatus j = .unbundled)
        ∧ s.callStatus j = .unprocessed ∧ CallOk ck E s j then
      some { release s (s.wd j).src (s.wd j).amount with
        bundleStatus := Function.update s.bundleStatus j .unbundled
        callStatus := Function.update s.callStatus j .executed
        fins := Function.update s.fins j (s.fins j + 1) }
    else none
  | .unbundleCancel j, s =>
    -- status `Verified` or `Unbundled` (`:139`); the call must not be `Executed` (`:158`);
    -- an `Unprocessed` call becomes `Cancelled` (`:159-162`), a `Cancelled` one stays.
    if (s.bundleStatus j = .verified ∨ s.bundleStatus j = .unbundled)
        ∧ s.callStatus j ≠ .executed then
      some { s with
        bundleStatus := Function.update s.bundleStatus j .unbundled
        callStatus := Function.update s.callStatus j .cancelled }
    else none
  | .unbundleSkip j, s =>
    if s.bundleStatus j = .verified ∨ s.bundleStatus j = .unbundled then
      some { s with bundleStatus := Function.update s.bundleStatus j .unbundled }
    else none
  | .confirm i st d, s =>
    -- status proof (`L1Nullifier.sol:222-231`); hash comparison (`:235-245`); delete (`:247`);
    -- vault: `OnlyFailureStatusAllowed` (`L1NativeTokenVault.sol:358`), amount ≠ 0 (`:361`),
    -- then the release charged to the confirmation's chain.
    if i < s.nd
        ∧ (ck.statusProof = true → E.bad (s.dep i).chain = true ∨ s.dst i = st.toL2)
        ∧ (ck.hashCheck = true → s.depositHappened (s.dep i).chain (s.dep i).txHash = E.H d)
        ∧ (ck.failureOnly = true → st = .failure)
        ∧ d.amount ≠ 0 ∧ ReleaseOk E s (s.dep i).chain d.amount then
      some { release (clearSlot ck s (s.dep i).chain (s.dep i).txHash) (s.dep i).chain d.amount with
        claims := if d = (s.dep i).data then Function.update s.claims i (s.claims i + 1)
          else s.claims
        clash := if d = (s.dep i).data then s.clash
          else Function.update s.clash (s.dep i).chain true }
    else none
  | .confirmOther c h st d, s =>
    -- as `confirm`, for a hash that is no bridge deposit's; the status proof is unconstrained.
    if (∀ i, i < s.nd → ¬ ((s.dep i).chain = c ∧ (s.dep i).txHash = h))
        ∧ (ck.hashCheck = true → s.depositHappened c h = E.H d)
        ∧ (ck.failureOnly = true → st = .failure)
        ∧ d.amount ≠ 0 ∧ ReleaseOk E s c d.amount then
      some { release (clearSlot ck s c h) c d.amount with
        clash := Function.update s.clash c true }
    else none
  | .donate x, s => some { s with escrow := s.escrow + x, donated := s.donated + x }

/-- Reachable states: any interleaving of any actions from `init`. -/
inductive Reach [Inhabited ι] (ck : Checks) (E : Env ι) : St ι → Prop
  | init : Reach ck E (init ι)
  | step {s s' : St ι} (a : Action ι) : Reach ck E s → step ck E a s = some s' → Reach ck E s'

/-- Run a list of actions; `none` if any reverts. -/
def run (ck : Checks) (E : Env ι) : List (Action ι) → St ι → Option (St ι)
  | [], s => some s
  | a :: as, s => (step ck E a s).bind (run ck E as)

/-- The data submitted to the confirmation entry points along a list of actions. -/
def confirmData : List (Action ι) → List TxData
  | [] => []
  | .confirm _ _ d :: as => d :: confirmData as
  | .confirmOther _ _ _ d :: as => d :: confirmData as
  | _ :: as => confirmData as

/-! ## Per-chain quantities -/

/-- Deposits to `c` neither minted nor reclaimed: pending on L2, or failed and unclaimed. -/
def unresolvedD (s : St ι) (c : ι) : ℕ :=
  ∑ i ∈ Finset.range s.nd,
    if (s.dep i).chain = c ∧ (s.dst i = .pending ∨ (s.dst i = .failed ∧ s.claims i = 0))
    then (s.dep i).data.amount else 0

/-- Amount paid out on L1 by confirmations of deposits to `c` with their own data. -/
def claimedD (s : St ι) (c : ι) : ℕ :=
  ∑ i ∈ Finset.range s.nd, if (s.dep i).chain = c then s.claims i * (s.dep i).data.amount else 0

/-- In-flight withdrawals from `c`: sent, call neither executed nor cancelled. -/
def inFlightW (s : St ι) (c : ι) : ℕ :=
  ∑ j ∈ Finset.range s.nw,
    if (s.wd j).chain = c ∧ s.callStatus j = .unprocessed then (s.wd j).amount else 0

/-- Withdrawals from `c` whose call was cancelled: burned on L2, not released on L1. -/
def cancelledW (s : St ι) (c : ι) : ℕ :=
  ∑ j ∈ Finset.range s.nw,
    if (s.wd j).chain = c ∧ s.callStatus j = .cancelled then (s.wd j).amount else 0

/-- Amount released on L1 by executed withdrawal calls charged to `c`. -/
def finalizedW (s : St ι) (c : ι) : ℕ :=
  ∑ j ∈ Finset.range s.nw, if (s.wd j).src = c then s.fins j * (s.wd j).amount else 0

/-- What the L1 escrow must hold for chain `c`: its L2 supply, its deposits not yet
resolved, its withdrawals in flight, and its cancelled withdrawals. -/
def backing (s : St ι) (c : ι) : ℕ :=
  s.supply c + unresolvedD s c + inFlightW s c + cancelledW s c

/-- The premises under which chain `c` is accounted exactly in state `s`: not
compromised, no clash flag raised on it, and none of its logged deposits' data hashes to
the zero sentinel. -/
def Honest (E : Env ι) (s : St ι) (c : ι) : Prop :=
  E.bad c = false ∧ s.clash c = false ∧
    ∀ i, i < s.nd → (s.dep i).chain = c → E.H (s.dep i).data ≠ 0

end Contracts.Protocol.DepositWithdrawConservation
