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
with the vault as its asset handler, bridged to a finite set `ι` of ZK chains.  The
model is the projection of the following onto that one asset:

* **L1 deposit**: `L1AssetRouter.bridgehubDeposit` (`bridge/asset-router/L1AssetRouter.sol:201-241`)
  → `AssetRouterBase._bridgehubDepositNonBaseTokenAsset` (`AssetRouterBase.sol:140-183`)
  → `_burn` (`AssetRouterBase.sol:303-331`) → `NativeTokenVaultBase.bridgeBurn`
  (`bridge/ntv/NativeTokenVaultBase.sol:294-318`) → `_bridgeBurnToken` (`:361-410`)
  → `_getTokenAndBridgeToChain` (`:425-457`) → `L1NativeTokenVault._handleBridgeToChain`
  (`bridge/ntv/L1NativeTokenVault.sol:424-433`) and `_depositFunds` (`NativeTokenVaultBase.sol:468-475`);
  then the Bridgehub's confirmation `L1AssetRouter.bridgehubConfirmL2Transaction`
  (`L1AssetRouter.sol:244-250`) → `L1Nullifier.bridgehubConfirmL2TransactionForwarded`
  (`bridge/L1Nullifier.sol:155-163`).
* **L2 execution of the deposit**: `L2AssetRouter.finalizeDeposit`
  (`bridge/asset-router/L2AssetRouter.sol:253-262`) minting the bridged token, or the
  priority transaction failing.
* **L2 withdrawal**: `L2AssetRouter.initiateIndirectCall` (`L2AssetRouter.sol:331-361`)
  → `NativeTokenVaultBase.bridgeBurn` on L2, which burns the bridged token.
* **L1 finalization of a withdrawal**: `L1InteropHandler.executeBundle`
  (`interop/interop-handler/L1InteropHandler.sol:81-98`, single-call bundles, `:85`) with its
  replay gate `_requireExecutable` (`interop/interop-handler/InteropHandlerBase.sol:282-287`)
  and `_markFullyExecutedAndRun` (`:325-341`); then `AssetRouterBase.receiveMessage`
  (`AssetRouterBase.sol:213-251`, source-chain equality `:235-239`) → `L1AssetRouter.finalizeDeposit`
  (`L1AssetRouter.sol:291-299`) → `_finalizeDeposit` (`AssetRouterBase.sol:267-283`)
  → `NativeTokenVaultBase.bridgeMint` / `_bridgeMintToken` (`NativeTokenVaultBase.sol:180-189`, `:220-247`)
  → `L1NativeTokenVault._handleBridgeFromChain` (`L1NativeTokenVault.sol:439-459`) and
  `_withdrawFunds` (`:399-411`).
* **Cancelling a withdrawal call**: `InteropHandlerBase.unbundleBundle` with a `Cancelled`
  status (`InteropHandlerBase.sol:113-178`, cancel branch `:157-163`).
* **Claim of a failed deposit**: `L1Nullifier.bridgeRecoverFailedTransfer`
  (`L1Nullifier.sol:180-213`) → `_verifyAndClearTransfer` (`:218-248`)
  → `L1AssetRouter.bridgeConfirmTransferResult` (`L1AssetRouter.sol:306-325`)
  → `L1NativeTokenVault.bridgeConfirmTransferResult` (`L1NativeTokenVault.sol:351-380`)
  → `NativeTokenVaultBase._disburseFailedTransfer` (`NativeTokenVaultBase.sol:264-286`).

Every entry point is a function `step … a s : Option St`; `none` is a revert (no
step), and the guards are evaluated in source order (left to right in each
conjunction).  `Reach` is the closure under every action, in any interleaving.

## The messages, and the authentication assumption (`PROTO-EVIDENCE`)

Cross-chain messages are not bytes here; they are the two logs in the state:

* `dep i` (with `dst i`): the L1→L2 priority transactions created by bridge deposits,
  and `issued`/`otherFailed` for every other L1→L2 transaction;
* `wd j`: the L2→L1 withdrawal calls sent by the L2 asset router.

**Authentication assumption.**  For a chain `c` with `bad c = false`:
(1) `MessageRoot.proveL1ToL2TransactionStatusShared(c, h, …, Failure)` (`L1Nullifier.sol:222-231`)
returns `true` only if the L1→L2 transaction with canonical hash `h` was executed on
`c` and failed: in the model, `dst i = failed` for the deposit with that hash, or
`otherFailed c h` for a non-bridge transaction; (2) a bundle passes the
`executeBundle` inclusion proof only if chain `c`'s L2 asset router actually sent it,
i.e. it is some `wd j` with `(wd j).chain = c`, and an honest chain's router sets the
payload's `_sourceChainId` to its own id and burns before sending; (3) each L1→L2
priority transaction is executed on L2 at most once, with one outcome
(`dst` moves only out of `pending`).  For a chain with `bad c = true` (compromised
prover, malicious operator) nothing is assumed: its failure proofs are forgeable
(`claim` needs no failed status there) and it can send arbitrary withdrawal messages
with any payload source chain (`forge`).

## Hashes

`H` is `DataEncoding.encodeTxDataHash(sender, assetId, transferData)`
(`AssetRouterBase.sol:162-166`), as a function of the transfer data for the fixed
asset.  **No property assumes anything of `H` globally.**  The guarantees that depend
on it use either the pinned premise that the run's own deposits do not hash to the
zero sentinel, or the ghost flag `clash c`, raised exactly when a claim on `c`
passed the hash comparison with data other than the deposit's own.  A separate
theorem shows a raised flag exhibits a concrete collision between the claimed
data and that deposit's data, or a zero preimage.

The canonical L1→L2 transaction hash `h` is supplied by the environment (the
Bridgehub) and is assumed fresh per chain (`issued c h = false`; `PROTO-TXHASH`).

## Ghost state

`dep`, `dst`, `claims`, `supply`, `wd`, `fins`, `clash`, `issued`, `otherFailed`
are protocol bookkeeping, not L1 storage: `dep`/`wd` are the authenticated
message sets; `claims i`/`fins j` count successful claims/finalizations; `supply c`
is the bridged token's total supply on chain `c`.  L1 storage is `escrow` (the
token's balance of the vault), `bridgedOut[a]`, `chainTotalDeposited[c][a]`,
`chainTotalWithdrawn[c][a]`, `depositHappened[c][h]`, and the interop handler's
call status (`executed`, `cancelled`).

## Not modelled (see the README)

Interop-enabled chains and the interop pool; a nonzero or pending
`chainBalanceBackfill`; the base-token path; pause (it only removes steps);
`uint256` overflow (amounts are `ℕ`; overflowing steps revert in Solidity, so the
model has more runs, not fewer); per-holder L2 balances (only total supply);
registration; the deprecated `populateBridgedOut` migration.
-/

namespace Contracts.Protocol.DepositWithdrawConservation

/-- 256-bit words: canonical transaction hashes and stored data hashes. -/
abbrev Word := UInt256
/-- Addresses. -/
abbrev Address := UInt256

/-- The transfer data a deposit commits to: `_originalCaller` and the bridge-burn data
`(amount, receiver)` for the fixed asset (`DataEncoding.encodeTxDataHash`). -/
structure TxData where
  sender : Address
  receiver : Address
  amount : ℕ
deriving DecidableEq

/-- A bridge deposit (an L1→L2 priority transaction created by the L1 asset router). -/
structure Deposit (ι : Type) where
  chain : ι
  txHash : Word
  data : TxData

/-- An L2→L1 withdrawal call.  `chain` is the authenticated sending chain; `src` is the
payload's `_sourceChainId` (equal to `chain` for an honest router). -/
structure Withdrawal (ι : Type) where
  chain : ι
  src : ι
  receiver : Address
  amount : ℕ

/-- L2 outcome of a deposit's priority transaction. -/
inductive DStatus
  | pending
  | minted
  | failed
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
  /-- Environment: L1→L2 transaction hash `h` has been used on chain `c`. -/
  issued : ι → Word → Bool
  /-- Environment: the non-bridge L1→L2 transaction `h` on `c` failed on L2. -/
  otherFailed : ι → Word → Bool
  /-- Number of bridge deposits so far. -/
  nd : ℕ
  /-- The bridge deposits (meaningful below `nd`). -/
  dep : ℕ → Deposit ι
  /-- L2 outcome of each deposit. -/
  dst : ℕ → DStatus
  /-- Ghost: successful claims of deposit `i` with its own data. -/
  claims : ℕ → ℕ
  /-- Total supply of the bridged token on each chain. -/
  supply : ι → ℕ
  /-- Number of withdrawal calls sent so far. -/
  nw : ℕ
  /-- The withdrawal calls (meaningful below `nw`). -/
  wd : ℕ → Withdrawal ι
  /-- Interop handler: call `j` has status `Executed`. -/
  executed : ℕ → Bool
  /-- Interop handler: call `j` has status `Cancelled`. -/
  cancelled : ℕ → Bool
  /-- Ghost: number of successful finalizations of call `j`. -/
  fins : ℕ → ℕ
  /-- Ghost: a claim on `c` passed the hash check with data other than the deposit's. -/
  clash : ι → Bool

variable {ι : Type}

/-- Fresh storage, empty message logs. -/
def init (ι : Type) [Inhabited ι] : St ι where
  escrow := 0
  bridgedOut := 0
  deposited := fun _ => 0
  withdrawn := fun _ => 0
  depositHappened := fun _ _ => 0
  issued := fun _ _ => false
  otherFailed := fun _ _ => false
  nd := 0
  dep := fun _ => ⟨default, 0, ⟨0, 0, 0⟩⟩
  dst := fun _ => .pending
  claims := fun _ => 0
  supply := fun _ => 0
  nw := 0
  wd := fun _ => ⟨default, default, 0, 0⟩
  executed := fun _ => false
  cancelled := fun _ => false
  fins := fun _ => 0
  clash := fun _ => false

/-- Which source checks are in force.  `Checks.source` is the contract; each
countermodel switches exactly one off. -/
structure Checks where
  /-- `_requireExecutable` / unbundle's `Unprocessed` requirement: a call executes once
  (`InteropHandlerBase.sol:282-287`, `:150`). -/
  replay : Bool
  /-- `senderChainId == payloadSourceChainId` (`AssetRouterBase.sol:235-239`). -/
  srcMatch : Bool
  /-- The per-chain cap `newWithdrawn ≤ chainTotalDeposited + backfill`
  (`L1NativeTokenVault.sol:450-456`). -/
  cap : Bool
  /-- `require(proofValid, InvalidProof())` on the failure proof (`L1Nullifier.sol:222-231`). -/
  statusProof : Bool
  /-- `dataHash == txDataHash` (`L1Nullifier.sol:235-245`). -/
  hashCheck : Bool
  /-- `delete depositHappened[c][h]` (`L1Nullifier.sol:247`). -/
  clear : Bool

/-- The contract as written: every check on. -/
def Checks.source : Checks := ⟨true, true, true, true, true, true⟩

/-- Every L1 entry point and environment move of the model. -/
inductive Action (ι : Type)
  /-- A bridge deposit of `d` to chain `c`, with canonical L1→L2 hash `h`. -/
  | deposit (c : ι) (h : Word) (d : TxData)
  /-- Any other L1→L2 transaction `h` on `c`, executed with the given outcome. -/
  | otherTx (c : ι) (h : Word) (failed : Bool)
  /-- L2 executes deposit `i` successfully: `finalizeDeposit` mints. -/
  | l2Mint (i : ℕ)
  /-- L2 executes deposit `i` and it fails. -/
  | l2Fail (i : ℕ)
  /-- A holder on chain `c` withdraws `amount` to L1 (burn + message). -/
  | withdraw (c : ι) (receiver : Address) (amount : ℕ)
  /-- A compromised chain `c` sends an arbitrary withdrawal message. -/
  | forge (c src : ι) (receiver : Address) (amount : ℕ)
  /-- `executeBundle` of withdrawal call `j` on L1. -/
  | finalize (j : ℕ)
  /-- `unbundleBundle` cancelling withdrawal call `j`. -/
  | cancel (j : ℕ)
  /-- `bridgeRecoverFailedTransfer` against deposit `i`'s transaction, supplying data `d`. -/
  | claim (i : ℕ) (d : TxData)
  /-- `bridgeRecoverFailedTransfer` against an L1→L2 transaction `h` on `c` that is not a
  bridge deposit, supplying data `d`. -/
  | claimOther (c : ι) (h : Word) (d : TxData)
  /-- Anyone transfers `x` tokens to the vault directly. -/
  | donate (x : ℕ)

variable [DecidableEq ι]

/-- `_handleBridgeFromChain(c, a, amt)` (`L1NativeTokenVault.sol:439-459`) followed by
`_withdrawFunds` (`:399-411`) succeed: `bridgedOut ≥ amt` (`:442-444`), the per-chain cap
(`:450-456`; the chain is tracked since it has no interop and the asset's origin is L1,
`:468-477`; zero backfill, not pending), and the token transfer out of the vault. -/
abbrev ReleaseOk (ck : Checks) (s : St ι) (c : ι) (amt : ℕ) : Prop :=
  amt ≤ s.bridgedOut ∧ (ck.cap = true → s.withdrawn c + amt ≤ s.deposited c) ∧ amt ≤ s.escrow

/-- The effect of a successful release of `amt` charged to chain `c`. -/
def release (s : St ι) (c : ι) (amt : ℕ) : St ι :=
  { s with
    bridgedOut := s.bridgedOut - amt
    withdrawn := Function.update s.withdrawn c (s.withdrawn c + amt)
    escrow := s.escrow - amt }

/-- `delete depositHappened[c][h]` when `ck.clear`. -/
def clearSlot (ck : Checks) (s : St ι) (c : ι) (h : Word) : St ι :=
  if ck.clear = true then
    { s with depositHappened := fun c' h' => if c' = c ∧ h' = h then 0 else s.depositHappened c' h' }
  else s

/-- One entry point.  `none` = revert. -/
def step (ck : Checks) (H : TxData → Word) (bad : ι → Bool) : Action ι → St ι → Option (St ι)
  | .deposit c h d, s =>
    -- Bridgehub: fresh canonical hash (environment); `_bridgeBurnToken`: amount ≠ 0
    -- (`NativeTokenVaultBase.sol:370`); nullifier: `DepositExists` (`L1Nullifier.sol:160`).
    if s.issued c h = false ∧ d.amount ≠ 0 ∧ s.depositHappened c h = 0 then
      some { s with
        bridgedOut := s.bridgedOut + d.amount
        deposited := Function.update s.deposited c (s.deposited c + d.amount)
        escrow := s.escrow + d.amount
        depositHappened := fun c' h' => if c' = c ∧ h' = h then H d else s.depositHappened c' h'
        issued := fun c' h' => if c' = c ∧ h' = h then true else s.issued c' h'
        nd := s.nd + 1
        dep := Function.update s.dep s.nd ⟨c, h, d⟩
        dst := Function.update s.dst s.nd .pending
        claims := Function.update s.claims s.nd 0 }
    else none
  | .otherTx c h f, s =>
    if s.issued c h = false then
      some { s with
        issued := fun c' h' => if c' = c ∧ h' = h then true else s.issued c' h'
        otherFailed := fun c' h' => if c' = c ∧ h' = h then f else s.otherFailed c' h' }
    else none
  | .l2Mint i, s =>
    if i < s.nd ∧ s.dst i = .pending then
      some { s with
        dst := Function.update s.dst i .minted
        supply := Function.update s.supply (s.dep i).chain
          (s.supply (s.dep i).chain + (s.dep i).data.amount) }
    else none
  | .l2Fail i, s =>
    if i < s.nd ∧ s.dst i = .pending then
      some { s with dst := Function.update s.dst i .failed }
    else none
  | .withdraw c r amt, s =>
    -- `_bridgeBurnToken`: amount ≠ 0 (`NativeTokenVaultBase.sol:370`); the bridged token's
    -- `bridgeBurn` (`:450`) needs the holder's balance, hence at most the supply.
    if amt ≠ 0 ∧ amt ≤ s.supply c then
      some { s with
        supply := Function.update s.supply c (s.supply c - amt)
        nw := s.nw + 1
        wd := Function.update s.wd s.nw ⟨c, c, r, amt⟩
        executed := Function.update s.executed s.nw false
        cancelled := Function.update s.cancelled s.nw false
        fins := Function.update s.fins s.nw 0 }
    else none
  | .forge c src r amt, s =>
    if bad c = true then
      some { s with
        nw := s.nw + 1
        wd := Function.update s.wd s.nw ⟨c, src, r, amt⟩
        executed := Function.update s.executed s.nw false
        cancelled := Function.update s.cancelled s.nw false
        fins := Function.update s.fins s.nw 0 }
    else none
  | .finalize j, s =>
    -- the call exists (inclusion proof); `_requireExecutable` (status `Unreceived`/`Verified`,
    -- so not executed and not unbundled); `receiveMessage`'s source-chain equality; then the
    -- vault's release charged to the payload's `_sourceChainId`.
    if j < s.nw ∧ (ck.replay = true → s.executed j = false ∧ s.cancelled j = false)
        ∧ (ck.srcMatch = true → (s.wd j).src = (s.wd j).chain)
        ∧ ReleaseOk ck s (s.wd j).src (s.wd j).amount then
      some { release s (s.wd j).src (s.wd j).amount with
        executed := Function.update s.executed j true
        fins := Function.update s.fins j (s.fins j + 1) }
    else none
  | .cancel j, s =>
    -- unbundle's cancel branch: `require(recordedCallStatus != Executed)` (`InteropHandlerBase.sol:158`).
    if j < s.nw ∧ s.executed j = false then
      some { s with cancelled := Function.update s.cancelled j true }
    else none
  | .claim i d, s =>
    -- failure proof (`L1Nullifier.sol:222-231`), hash comparison (`:235-245`), delete (`:247`),
    -- then `bridgeConfirmTransferResult`: amount ≠ 0 (`L1NativeTokenVault.sol:361`) and the release.
    if i < s.nd ∧ (ck.statusProof = true → bad (s.dep i).chain = true ∨ s.dst i = .failed)
        ∧ (ck.hashCheck = true → s.depositHappened (s.dep i).chain (s.dep i).txHash = H d)
        ∧ d.amount ≠ 0 ∧ ReleaseOk ck s (s.dep i).chain d.amount then
      if d = (s.dep i).data then
        some { release (clearSlot ck s (s.dep i).chain (s.dep i).txHash) (s.dep i).chain d.amount with
          claims := Function.update s.claims i (s.claims i + 1) }
      else if ck.hashCheck = true then
        some { release (clearSlot ck s (s.dep i).chain (s.dep i).txHash) (s.dep i).chain d.amount with
          clash := Function.update s.clash (s.dep i).chain true }
      else some (release (clearSlot ck s (s.dep i).chain (s.dep i).txHash) (s.dep i).chain d.amount)
    else none
  | .claimOther c h d, s =>
    if (∀ i, i < s.nd → ¬ ((s.dep i).chain = c ∧ (s.dep i).txHash = h))
        ∧ (ck.statusProof = true → bad c = true ∨ s.otherFailed c h = true)
        ∧ (ck.hashCheck = true → s.depositHappened c h = H d)
        ∧ d.amount ≠ 0 ∧ ReleaseOk ck s c d.amount then
      if ck.hashCheck = true then
        some { release (clearSlot ck s c h) c d.amount with
          clash := Function.update s.clash c true }
      else some (release (clearSlot ck s c h) c d.amount)
    else none
  | .donate x, s => some { s with escrow := s.escrow + x }

/-- Reachable states: any interleaving of any actions from `init`. -/
inductive Reach [Inhabited ι] (ck : Checks) (H : TxData → Word) (bad : ι → Bool) : St ι → Prop
  | init : Reach ck H bad (init ι)
  | step {s s' : St ι} (a : Action ι) : Reach ck H bad s → step ck H bad a s = some s' →
      Reach ck H bad s'

/-- Run a list of actions; `none` if any reverts. -/
def run (ck : Checks) (H : TxData → Word) (bad : ι → Bool) : List (Action ι) → St ι → Option (St ι)
  | [], s => some s
  | a :: as, s => (step ck H bad a s).bind (run ck H bad as)

/-! ## Per-chain quantities -/

/-- Sum of the amounts of the deposits made to `c`. -/
def depTotal (s : St ι) (c : ι) : ℕ :=
  ∑ i ∈ Finset.range s.nd, if (s.dep i).chain = c then (s.dep i).data.amount else 0

/-- Deposits to `c` neither minted nor reclaimed: pending on L2, or failed and unclaimed. -/
def outD (s : St ι) (c : ι) : ℕ :=
  ∑ i ∈ Finset.range s.nd,
    if (s.dep i).chain = c ∧ (s.dst i = .pending ∨ (s.dst i = .failed ∧ s.claims i = 0))
    then (s.dep i).data.amount else 0

/-- Amount paid out on L1 by legitimate claims of deposits to `c`. -/
def claimW (s : St ι) (c : ι) : ℕ :=
  ∑ i ∈ Finset.range s.nd, if (s.dep i).chain = c then s.claims i * (s.dep i).data.amount else 0

/-- In-flight withdrawals from `c`: sent, not executed, not cancelled. -/
def inW (s : St ι) (c : ι) : ℕ :=
  ∑ j ∈ Finset.range s.nw,
    if (s.wd j).chain = c ∧ s.executed j = false ∧ s.cancelled j = false then (s.wd j).amount else 0

/-- Withdrawals from `c` whose call was cancelled: burned on L2, never released on L1. -/
def strandW (s : St ι) (c : ι) : ℕ :=
  ∑ j ∈ Finset.range s.nw,
    if (s.wd j).chain = c ∧ s.executed j = false ∧ s.cancelled j = true then (s.wd j).amount else 0

/-- Amount released on L1 by finalized withdrawals charged to `c`. -/
def finW (s : St ι) (c : ι) : ℕ :=
  ∑ j ∈ Finset.range s.nw, if (s.wd j).src = c then s.fins j * (s.wd j).amount else 0

/-- What chain `c` owes its users: L2 supply, deposits not yet resolved, withdrawals
in flight, and cancelled withdrawals. -/
def backing (s : St ι) (c : ι) : ℕ :=
  s.supply c + outD s c + inW s c + strandW s c

/-- The vault's per-chain net balance, `_netChainBalance(c, a, 0)` (`L1NativeTokenVault.sol:484-488`). -/
def chainBalance (s : St ι) (c : ι) : ℕ :=
  s.deposited c - s.withdrawn c

/-- The premises under which chain `c` is accounted exactly: honest, no hash clash raised on
it, and none of its deposits' data hashes to the zero sentinel (pinned to the run's own
deposits). -/
def Honest (H : TxData → Word) (bad : ι → Bool) (s : St ι) (c : ι) : Prop :=
  bad c = false ∧ s.clash c = false ∧ ∀ i, i < s.nd → (s.dep i).chain = c → H (s.dep i).data ≠ 0

end Contracts.Protocol.DepositWithdrawConservation
