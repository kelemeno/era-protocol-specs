import EraSpec.Codegen.VaultPreparationSlice.Specs.Correspondence

/-!
# The L1 vault's per-chain balance cap, at draft/v0.35.0

Transcribed from era-contracts `draft/v0.35.0` at
`d9f678900e1bc8286412b78f56d4a9f443983c29` (paths under `l1-contracts/contracts/`). The
cap is new on that branch (#2628); `main` at `3605e82` has none of it. Everything else the
vault slice transcribes is unchanged there apart from renames (`_assetRouter()` is
`_getAssetRouter()`, `_baseTokenAssetId()` is `_getBaseTokenAssetId()`), so
`Specs/Program.lean` still describes the v35 `bridgeBurn` statement for statement:
`NativeTokenVaultBase.sol` `bridgeBurn` (294-318), `_decodeBurnAndCheckAssetId` (337-354),
`_bridgeBurnToken` (361-410), `_getERC20Metadata` (412-423), `_getTokenAndBridgeToChain`
(425-457).

## What changed in the slice: the L1 accounting hook

At the pin, `L1NativeTokenVault._handleBridgeToChain` recorded `bridgedOut` for L1-native
assets only, so for a bridged token it did nothing (pin `L1NativeTokenVault.sol:260-264`).
At v35 it is (`bridge/ntv/L1NativeTokenVault.sol:424-433`):

    function _handleBridgeToChain(uint256 _chainId, bytes32 _assetId, uint256 _amount) internal override {
        uint256 assetOriginChainId = originChainId[_assetId];
        if (assetOriginChainId == block.chainid) {
            bridgedOut[_assetId] += _amount;
        }
        (bool tracked, uint256 balanceChainId) = _trackedBalance(_chainId, assetOriginChainId);
        if (tracked) {
            chainTotalDeposited[balanceChainId][_assetId] += _amount;
        }
    }

with `_trackedBalance` (`:468-477`):

    IL1MessageRoot messageRoot = _messageRoot();
    if (messageRoot.isInteropEnabled(_chainId)) {
        return (!messageRoot.isInteropEnabled(_assetOriginChainId), INTEROP_POOL_CHAIN_ID);
    }
    return (_assetOriginChainId != _chainId, _chainId);

So for a bridged token the hook is no longer a no-op: when the destination's balance is
tracked it adds the amount to `chainTotalDeposited[key][asset]`, in checked arithmetic
(`pragma solidity 0.8.28`, `:3`), and an overflow reverts the whole `bridgeBurn` with
`Panic(0x11)`. `handleBridgeToChainV35` is that function; `l1HooksV35` is the `CHooks` the
slice's machine runs it as, and `l1ModelHooksV35` the model `Hooks` it stands for.

**What the hook reads.** `originChainId[_assetId]` is the vault's own storage; the hook
closes over it (`CapEnvV35.originChainId`). That is sound for the slice because no slice
step writes vault storage (`SliceNeverWritesVaultStorageV35`), so the map the hook reads is
the one in the vault's storage at every point of a run. `block.chainid` is L1's chain id.
`_messageRoot()` (`:491-493`) is `L1_NULLIFIER.BRIDGE_HUB().messageRoot()`, and
`isInteropEnabled` (`core/message-root/L1MessageRoot.sol:92-94`) is a view of its
`interopEnabled` flags. Those answers are `CapEnvV35.interop`, a `DEP-RESULTS` input: the
three view calls are assumed to return. The hook emits no event, so the slice's exact-log
statements still hold for it.

## The rest of the cap (v35-only), as a run model

`CapStepV35` is every entry point that writes the cap's storage (`:96-108`):

* the two hooks: `_handleBridgeToChain` (above) and `_handleBridgeFromChain` (`:439-459`),
  reached from `bridgeBurn`, `bridgeMint` and the recovery paths (`NativeTokenVaultBase.sol`
  `_getTokenAndBridgeToChain` :444, :447; `_bridgeMintToken` :240; `_disburseFailedTransfer`
  :276). `_handleBridgeFromChain` caps a tracked withdrawal at
  `chainTotalDeposited + chainBalanceBackfill` unless the key's backfill is pending:

        uint256 newWithdrawn = chainTotalWithdrawn[balanceChainId][_assetId] + _amount;
        if (!chainBalanceBackfillPending[balanceChainId]) {
            uint256 limit = chainTotalDeposited[balanceChainId][_assetId] +
                chainBalanceBackfill[balanceChainId][_assetId];
            if (newWithdrawn > limit) revert ChainBalanceExceeded(...);
        }
        chainTotalWithdrawn[balanceChainId][_assetId] = newWithdrawn;

* `setChainBalanceBackfill` (`:219-239`, one array entry per step: a successful call is
  the sequence of its entries, each of which touches only its own `(chain, asset)` and the
  pool's deposits), `markBackfilled` (`:242-246`), `moveChainBalanceToInteropPool`
  (`:249-258`), and `initializeUpgrade` (`:291-298`), which marks every chain the Bridgehub
  lists as pending.

Each hook step takes its own `CapEnvV35`: the interop flags and the origin map may be
anything at each step (they live in other contracts or change by registration), so every
history of `enableInterop` (`L1MessageRoot.sol:71-89`) and every registration is covered.
`onlyOwner`, the proxy-admin check of `initializeUpgrade` and `reinitializer(2)` are
dropped: every run of the real vault is a run here, so the safety results carry over.

**The pool key.** `INTEROP_POOL_CHAIN_ID = uint256(keccak256("interop.pool")) - 1`
(`common/Config.sol:37`). The Bridgehub refuses chain ids above `type(uint48).max`
(`core/bridgehub/BridgehubBase.sol:496-499`, "also keeps `INTEROP_POOL_CHAIN_ID` from ever
being registered"), so `initializeUpgrade` never marks the pool pending. The results take
that as the pinned premise `PoolKeyOutsideChainIds pool` on the one constant, and
`interopPoolChainIdV35` is its value, computed off-line (`cast keccak "interop.pool"` is
`0x9cc7…2d0a`); `Proofs/L1PerChainCapAtV35.lean` checks the premise for it by `decide`.
-/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls

/-! ## Constants -/

/-- `INTEROP_POOL_CHAIN_ID = uint256(keccak256("interop.pool")) - 1` (`common/Config.sol:37`),
computed off-line: `keccak256("interop.pool") = 0x9cc761dc…13382d0a`. -/
def interopPoolChainIdV35 : Word :=
  0x9cc761dc886485f14b36f25560c0fb8022a9b62e0778612e6cc02bf213382d09

/-- The Bridgehub's bound on chain ids: `_chainId > type(uint48).max` reverts
(`core/bridgehub/BridgehubBase.sol:497-499`), so every registered chain id is below `2^48`. -/
def chainIdBoundV35 : ℕ := 2 ^ 48

/-- **THE PINNED PREMISE ON THE POOL KEY.** The pool key is not below the chain-id bound, so no
chain the Bridgehub lists has it. It is a fact about the one value
`uint256(keccak256("interop.pool")) - 1`, not a hash property. -/
def PoolKeyOutsideChainIds (pool : Word) : Prop := chainIdBoundV35 ≤ pool.val

/-! ## State and environment -/

/-- The vault's per-chain storage (`L1NativeTokenVault.sol:90-108`). Maps are indexed
`[chainId][assetId]`. -/
structure CapStateV35 where
  /-- `bridgedOut[assetId]` (`:90`). -/
  bridgedOut : Word → Word
  /-- `chainTotalDeposited[chainId][assetId]` (`:96`). -/
  deposited : Word → Word → Word
  /-- `chainTotalWithdrawn[chainId][assetId]` (`:99`). -/
  withdrawn : Word → Word → Word
  /-- `chainBalanceBackfill[chainId][assetId]` (`:102`). -/
  backfill : Word → Word → Word
  /-- `chainBalanceInInteropPool[chainId][assetId]` (`:105`). -/
  inPool : Word → Word → Bool
  /-- `chainBalanceBackfillPending[chainId]` (`:108`). -/
  pending : Word → Bool

/-- Fresh cap storage: every slot zero, as after the upgrade that introduces it. -/
def CapStateV35.zero : CapStateV35 :=
  ⟨fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => false, fun _ => false⟩

/-- What the hooks read besides their arguments and the cap storage. -/
structure CapEnvV35 where
  /-- `block.chainid`: L1's chain id. -/
  chainId : Word
  /-- The vault's `originChainId` mapping (`NativeTokenVaultBase.sol:76`). -/
  originChainId : Word → Word
  /-- The answers of `messageRoot.isInteropEnabled` (`L1MessageRoot.sol:92-94`): `DEP-RESULTS`. -/
  interop : Word → Bool
  /-- `INTEROP_POOL_CHAIN_ID` (`common/Config.sol:37`). -/
  pool : Word

/-- `map[k][a] = v` on a two-level mapping. -/
def update2 {β : Type} (f : Word → Word → β) (k a : Word) (v : β) : Word → Word → β :=
  Function.update f k (Function.update (f k) a v)

/-! ## The functions -/

/-- `x + y` in Solidity 0.8 checked `uint256` arithmetic: `Panic(0x11)` on overflow. -/
def checkedAddV35 (x y : Word) : Except XFailure Word :=
  if UInt256.size ≤ x.val + y.val then .error (.data (.panic panicOverflow)) else .ok (x + y)

/-- `_trackedBalance(chain, origin)` (`L1NativeTokenVault.sol:468-477`): whether the asset's
balance on `chain` is tracked, and the key of its totals. -/
def trackedBalanceV35 (env : CapEnvV35) (chain origin : Word) : Bool × Word :=
  if env.interop chain = true then (!env.interop origin, env.pool) else (decide (origin ≠ chain), chain)

/-- `bridgedOut[asset] += amount`, checked (`:427`). -/
def creditBridgedOutV35 (s : CapStateV35) (asset amount : Word) : Except XFailure CapStateV35 :=
  match checkedAddV35 (s.bridgedOut asset) amount with
  | .ok v => .ok { s with bridgedOut := Function.update s.bridgedOut asset v }
  | .error e => .error e

/-- `chainTotalDeposited[key][asset] += amount`, checked (`:431`, `:233`, `:256`). -/
def creditDepositedV35 (s : CapStateV35) (key asset amount : Word) :
    Except XFailure CapStateV35 :=
  match checkedAddV35 (s.deposited key asset) amount with
  | .ok v => .ok { s with deposited := update2 s.deposited key asset v }
  | .error e => .error e

/-- **`_handleBridgeToChain(chain, asset, amount)` AT V35** (`L1NativeTokenVault.sol:424-433`). -/
def handleBridgeToChainV35 (env : CapEnvV35) (s : CapStateV35) (chain asset amount : Word) :
    Except XFailure CapStateV35 :=
  match (if env.originChainId asset = env.chainId then creditBridgedOutV35 s asset amount
      else .ok s) with
  | .error e => .error e
  | .ok s₁ =>
    if (trackedBalanceV35 env chain (env.originChainId asset)).1 = true then
      creditDepositedV35 s₁ (trackedBalanceV35 env chain (env.originChainId asset)).2 asset amount
    else .ok s₁

/-- `_handleBridgeToChain` at the pin (pin `L1NativeTokenVault.sol:260-264`): `bridgedOut` for
L1-native assets, nothing else. Not v35 code; it shows what changed. -/
def handleBridgeToChainPin (env : CapEnvV35) (s : CapStateV35) (asset amount : Word) :
    Except XFailure CapStateV35 :=
  if env.originChainId asset = env.chainId then creditBridgedOutV35 s asset amount else .ok s

/-- The cap check of `_handleBridgeFromChain` (`:450-456`): nothing while the key's backfill
is pending, else `newWithdrawn ≤ deposited + backfill` with the sum checked. -/
def capCheckV35 (s : CapStateV35) (chain key asset newWithdrawn : Word) : Except XFailure Unit :=
  if s.pending key = true then .ok ()
  else
    match checkedAddV35 (s.deposited key asset) (s.backfill key asset) with
    | .error e => .error e
    | .ok limit =>
      if limit.val < newWithdrawn.val then
        .error (.data (.custom "ChainBalanceExceeded" [chain, asset, newWithdrawn, limit]))
      else .ok ()

/-- `bridgedOut[asset] -= amount` after `require(bridgedOut[asset] >= amount)` (`:442-445`). -/
def debitBridgedOutV35 (s : CapStateV35) (chain asset amount : Word) :
    Except XFailure CapStateV35 :=
  if (s.bridgedOut asset).val < amount.val then
    .error (.data (.custom "InsufficientChainBalance" [chain, asset, amount]))
  else .ok { s with bridgedOut := Function.update s.bridgedOut asset (s.bridgedOut asset - amount) }

/-- The tracked branch of `_handleBridgeFromChain` (`:448-458`) for the key `key`: the checked
`newWithdrawn`, the cap check, then the write. -/
def recordWithdrawalV35 (s : CapStateV35) (chain key asset amount : Word) :
    Except XFailure CapStateV35 :=
  match checkedAddV35 (s.withdrawn key asset) amount with
  | .error e => .error e
  | .ok newW =>
    match capCheckV35 s chain key asset newW with
    | .error e => .error e
    | .ok () => .ok { s with withdrawn := update2 s.withdrawn key asset newW }

/-- **`_handleBridgeFromChain(chain, asset, amount)` AT V35** (`L1NativeTokenVault.sol:439-459`). -/
def handleBridgeFromChainV35 (env : CapEnvV35) (s : CapStateV35) (chain asset amount : Word) :
    Except XFailure CapStateV35 :=
  match (if env.originChainId asset = env.chainId then debitBridgedOutV35 s chain asset amount
      else .ok s) with
  | .error e => .error e
  | .ok s₁ =>
    if (trackedBalanceV35 env chain (env.originChainId asset)).1 = true then
      recordWithdrawalV35 s₁ chain (trackedBalanceV35 env chain (env.originChainId asset)).2 asset
        amount
    else .ok s₁

/-- `_netChainBalance(chain, asset, backfill)` (`:484-488`): deposits plus `backfill` (checked),
less withdrawals, and zero if withdrawals are larger. -/
def netChainBalanceV35 (s : CapStateV35) (chain asset backfill : Word) : Except XFailure Word :=
  match checkedAddV35 (s.deposited chain asset) backfill with
  | .error e => .error e
  | .ok balance =>
    .ok (if (s.withdrawn chain asset).val < balance.val then balance - s.withdrawn chain asset else 0)

/-- What a backfill adds to the pool for a chain already in it (`:233-234`):
`_netChainBalance(chain, asset, amount) - _netChainBalance(chain, asset, 0)`, the subtraction
checked, credited to the pool's deposits. -/
def poolBackfillCreditV35 (pool : Word) (s : CapStateV35) (chain asset amount : Word) :
    Except XFailure CapStateV35 :=
  match netChainBalanceV35 s chain asset amount, netChainBalanceV35 s chain asset 0 with
  | .ok n₁, .ok n₀ =>
    if n₁.val < n₀.val then .error (.data (.panic panicOverflow))
    else creditDepositedV35 s pool asset (n₁ - n₀)
  | .error e, _ => .error e
  | .ok _, .error e => .error e

/-- One entry of `setChainBalanceBackfill(chain, assets, amounts)` (`:219-239`). For a chain whose
balance is already in the pool, the pool's deposits gain what the move would have added with the
backfill set (`:230-235`); the subtraction is checked. -/
def setChainBalanceBackfillV35 (pool : Word) (s : CapStateV35) (chain asset amount : Word) :
    Except XFailure CapStateV35 :=
  if chain = pool then .error (.data (.custom "InvalidChainId" []))
  else if s.backfill chain asset ≠ 0 then
    .error (.data (.custom "ChainBalanceBackfillAlreadySet" [chain, asset]))
  else
    match (if s.inPool chain asset = true then poolBackfillCreditV35 pool s chain asset amount
        else .ok s) with
    | .error e => .error e
    | .ok s₁ => .ok { s₁ with backfill := update2 s₁.backfill chain asset amount }

/-- `markBackfilled(chain)` (`:242-246`). -/
def markBackfilledV35 (s : CapStateV35) (chain : Word) : Except XFailure CapStateV35 :=
  if s.pending chain = true then .ok { s with pending := Function.update s.pending chain false }
  else .error (.data (.custom "ChainBalanceBackfillNotPending" [chain]))

/-- `moveChainBalanceToInteropPool(chain, asset)` (`:249-258`), with `interop` the message root's
answer for `chain`. -/
def moveChainBalanceToInteropPoolV35 (pool : Word) (interop : Bool) (s : CapStateV35)
    (chain asset : Word) : Except XFailure CapStateV35 :=
  if interop = false then .error (.data (.custom "InteropNotEnabled" [chain]))
  else if s.pending chain = true then .error (.data (.custom "ChainBalanceBackfillPending" [chain]))
  else if s.inPool chain asset = true then
    .error (.data (.custom "ChainBalanceAlreadyInInteropPool" [chain, asset]))
  else
    match netChainBalanceV35 s chain asset (s.backfill chain asset) with
    | .error e => .error e
    | .ok amount => creditDepositedV35 { s with inPool := update2 s.inPool chain asset true } pool
        asset amount

/-- `initializeUpgrade()`'s writes (`:291-298`): every listed chain becomes pending. -/
def markPendingV35 (s : CapStateV35) (chains : List Word) : CapStateV35 :=
  { s with pending := fun c => if c ∈ chains then true else s.pending c }

/-! ## Runs of the cap -/

/-- **ONE SUCCESSFUL CALL THAT WRITES THE CAP'S STORAGE.** The hooks may run under any
environment with the given pool key; `initializeUpgrade` lists chains the Bridgehub accepted,
so below `2^48`. -/
inductive CapStepV35 (pool : Word) : CapStateV35 → CapStateV35 → Prop
  | toChain {s t : CapStateV35} {env : CapEnvV35} {chain asset amount : Word} :
      env.pool = pool → handleBridgeToChainV35 env s chain asset amount = .ok t →
      CapStepV35 pool s t
  | fromChain {s t : CapStateV35} {env : CapEnvV35} {chain asset amount : Word} :
      env.pool = pool → handleBridgeFromChainV35 env s chain asset amount = .ok t →
      CapStepV35 pool s t
  | setBackfill {s t : CapStateV35} {chain asset amount : Word} :
      setChainBalanceBackfillV35 pool s chain asset amount = .ok t → CapStepV35 pool s t
  | markBackfilled {s t : CapStateV35} {chain : Word} :
      markBackfilledV35 s chain = .ok t → CapStepV35 pool s t
  | moveToPool {s t : CapStateV35} {interop : Bool} {chain asset : Word} :
      moveChainBalanceToInteropPoolV35 pool interop s chain asset = .ok t → CapStepV35 pool s t
  | initializeUpgrade {s : CapStateV35} {chains : List Word} :
      (∀ c ∈ chains, c.val < chainIdBoundV35) → CapStepV35 pool s (markPendingV35 s chains)

/-- `chain`'s totals cover what left it: for every asset, withdrawals are at most deposits plus
backfill. -/
def BackfillCovers (s : CapStateV35) (chain : Word) : Prop :=
  ∀ asset, (s.withdrawn chain asset).val ≤ (s.deposited chain asset).val + (s.backfill chain asset).val

/-- **THE CAP INVARIANT.** Every key whose backfill is not pending is covered. -/
def CapInvV35 (s : CapStateV35) : Prop :=
  ∀ key, s.pending key = false → BackfillCovers s key

/-- **THE POOL INVARIANT.** The pool key is never pending, has no backfill, and its withdrawals
are at most its deposits. -/
def PoolInvV35 (pool : Word) (s : CapStateV35) : Prop :=
  s.pending pool = false ∧ (∀ asset, s.backfill pool asset = 0) ∧
    ∀ asset, (s.withdrawn pool asset).val ≤ (s.deposited pool asset).val

/-- A step whose owner calls are disciplined: whenever it clears a chain's pending flag
(only `markBackfilled` does), that chain was covered first. -/
def CoveredCapStepV35 (pool : Word) (s t : CapStateV35) : Prop :=
  CapStepV35 pool s t ∧ ∀ c, s.pending c = true → t.pending c = false → BackfillCovers s c

/-! ## The slice's hooks on L1 at v35 -/

/-- The slice's concrete hooks on L1: the accounting hook is `handleBridgeToChainV35`, on the
cap storage; `metadata` is any implementation of `_getERC20GettersInner`. -/
def l1HooksV35 (env : CapEnvV35) (metadata : Storage → Word → Except XFailure Bytes) :
    CHooks CapStateV35 where
  account acc _ c a m := handleBridgeToChainV35 env acc c a m
  metadata := metadata

/-- The model hooks `l1HooksV35` stands for. -/
def l1ModelHooksV35 (env : CapEnvV35)
    (metadata : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes) :
    Contracts.NativeTokenVaultBase.Hooks CapStateV35 where
  account acc _ c a m := (handleBridgeToChainV35 env acc c a m).toOption
  metadata := metadata

/-- The metadata implementations agree, on every token storage representing a model token. -/
def MetadataAgreesV35 (md : Storage → Word → Except XFailure Bytes)
    (mdm : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes) : Prop :=
  ∀ st t o, TokenRel st t → (md st o).toOption = mdm t o

/-- The environment is the deployment's: `block.chainid` is the deployment's chain and the origin
map is the vault storage's `originChainId` mapping. -/
def EnvMatchesV35 (env : CapEnvV35) (d : Deployment) (vault : Storage) : Prop :=
  env.chainId = d.chainId ∧ env.originChainId = vault.maps "_originChainId"

/-- What one journal entry adds to `chainTotalDeposited[key][asset]`: the entry's returned amount,
if it is for `asset` and its destination's balance is tracked under `key`. -/
def entryDepositV35 (env : CapEnvV35) (key asset : Word) (e : Entry) : ℕ :=
  if e.assetId = asset ∧ trackedBalanceV35 env e.destinationChain (env.originChainId asset) = (true, key)
  then mintAmount e.ret else 0

/-- What a journal adds to `chainTotalDeposited[key][asset]`. -/
def journalDepositsV35 (env : CapEnvV35) (key asset : Word) (j : List Entry) : ℕ :=
  (j.map (entryDepositV35 env key asset)).sum

end Codegen.VaultPreparationSlice
