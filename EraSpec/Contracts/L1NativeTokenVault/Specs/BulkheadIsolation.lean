import Mathlib.Tactic

/-!
# The L1 vault's per-chain cap at v35, with chains whose proofs are not trusted

Local specification at era-contracts `draft/v0.35.0` head
`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`, paths under `l1-contracts/contracts/`.
`L1NTV` is `bridge/ntv/L1NativeTokenVault.sol`, `NTVB` is `bridge/ntv/NativeTokenVaultBase.sol`,
`L1AR` is `bridge/asset-router/L1AssetRouter.sol`, `L1MR` is `core/message-root/L1MessageRoot.sol`,
`BHB` is `core/bridgehub/BridgehubBase.sol`.  The per-chain cap is new at `b17415d20`: the pin
`c67894b9` had the aggregate `bridgedOut` ledger alone, whose boundary
`Contracts.NativeTokenVault.History.Properties.PerChainIsolationFails` records.

**This file is definitions only.**  The statements are in
`EraSpec.Contracts.L1NativeTokenVault.Properties.BulkheadIsolation` and the proofs in
`EraSpec.Contracts.L1NativeTokenVault.Proofs.BulkheadIsolation`.

## The same code as `InteropPool`

`Contracts.L1NativeTokenVault.InteropPool` (`Specs/InteropPool.lean`, `MODEL-INTEROP-POOL`)
transcribes the same functions at the same commit: both hooks with `_trackedBalance`, one entry of
`setChainBalanceBackfill` with `_netChainBalance`, `markBackfilled`,
`moveChainBalanceToInteropPool`, `initializeUpgrade`, one entry of `populateBridgedOut`,
`enableInterop` and chain registration.  The two transcriptions were written separately and are
framed differently.  Here ids are naturals, not words; the origin map is part of the state, while
there each hook call takes the origin as an input; the hooks require a registered chain, while there
they take any chain; `populate` keeps the populated flag and the L1-origin check, which only
reject; and there is no ghost counter.  `BulkheadStepIsPoolCall`
(`Properties/BulkheadPoolSimulation.lean`) proves that, on the same constants and from
corresponding states, every successful call here whose arguments are `uint256` words is the
matching successful `InteropPool.poolCall`, with the same effect on the storage both models keep
(`registerAsset` has no counterpart and changes none of it).  `BulkheadUpgradeStateIsPostUpgrade`
proves that a `CapUpgradeState` whose origin values are words corresponds to an `InteropPool`
post-upgrade state.  So every run here from `CapUpgradeState` on such arguments is an `InteropPool`
run from a post-upgrade state to a corresponding state (`BulkheadRunsArePoolRuns`), and that topic's
results hold of that state.  A third transcription of the cap's writers,
`Codegen.VaultPreparationSlice` topic `L1PerChainCapAtV35` (`CapStepV35`), lets the interop flags
and the origin map change freely at every step; it is not connected to this model.

## State

`CapState` holds the vault storage the cap uses (`L1NTV:90-108`): `bridgedOut`,
`bridgedOutPopulated`, `chainTotalDeposited`, `chainTotalWithdrawn`, `chainBalanceBackfill`,
`chainBalanceInInteropPool` and `chainBalanceBackfillPending`; the `reinitializer(2)` version of
`initializeUpgrade` as a flag; the vault's `originChainId` map (`NTVB`, written by
`_setNewTokenStorage`, `NTVB:565-575`, at `:568`); and two things the cap reads from other contracts:
`L1MessageRoot.interopEnabled` (`L1MR:49`, read through `isInteropEnabled`, `:92-94`) and whether
the Bridgehub has registered a chain.  Amounts and ids are `ℕ`; every write is a checked
`uint256` result, and the checked additions are explicit (`pragma solidity 0.8.28`): an overflow is
a revert.  The two-level mappings are indexed `[key][asset]`, where a key is a chain id or the
pool key.

## Steps

`capStep cfg l s` is one successful call (`some`) or a revert (`none`).  A revert is no step.

* `toChain c a x` is `_handleBridgeToChain(c, a, x)` (`L1NTV:424-433`).  Every L1 deposit reaches
  it through `bridgeBurn` (`NTVB:294-318`), `_bridgeBurnToken` (`NTVB:361-410`, at `:378`) and
  `_getTokenAndBridgeToChain` (`NTVB:425-457`, at `:444` and `:447`), base-token deposits included.
* `fromChain c a x` is `_handleBridgeFromChain(c, a, x)` (`L1NTV:439-459`).  A finalized withdrawal
  reaches it through `bridgeMint` (`NTVB:180-189`) and `_bridgeMintToken` (`NTVB:220-247`, at
  `:240`), and a claimed failed deposit through `bridgeConfirmTransferResult` (`L1NTV:351-380`) and
  `_disburseFailedTransfer` (`NTVB:264-286`, at `:276`).  The token transfer or mint that follows
  is not modelled.
* `setBackfill c a v` is one entry of the owner's `setChainBalanceBackfill(c, [a], [v])`
  (`L1NTV:219-239`).  A call with several entries is the sequence of its entries; the model also
  has the prefixes, so it has more runs than the source.
* `markBackfilled c` (`L1NTV:242-246`), `moveToPool c a` (`moveChainBalanceToInteropPool`,
  `L1NTV:249-258`) and `initializeUpgrade` (`L1NTV:291-298`, the chains the Bridgehub lists are
  the registered ones).
* `enableInterop c` is `L1MessageRoot.enableInterop` (`L1MR:72-89`): registered, not yet enabled,
  not pending.  Its owner check and second-proof-system checks only remove steps and are dropped.
* `registerChain c` is the Bridgehub registering a chain, with `_validateChainParams`'s id checks
  (`BHB:491-503`): `c ≠ 0`, `c ≤ type(uint48).max`, `c ≠ block.chainid`.  Chains are never
  deregistered.
* `registerAsset a o` is the first write of `originChainId[a]` (`_setNewTokenStorage`): the origin
  is set once, never to `0` (`tokenDataOriginChainId`, `NTVB:542-548`).  That the registry writes it
  only for a fresh asset id is the registry model's concern (`CRYPTO-ID`).
* `populate a L` is one asset of `populateBridgedOut` (`L1NTV:189-212`), with `L` the value
  `legacyBridgedOut(a)` (`:152-186`) returns; it reverts unless `a` is native to L1.  The skip of an
  already populated asset writes nothing and is not a step.

The owner, proxy-admin and router modifiers only make calls revert, so they are dropped: the model
has more runs than the source, not fewer.  That the deployed code executes these transcriptions is
the open correspondence obligation (`MODEL-BULKHEAD-CAP` in `ASSUMPTIONS.md`).

## Untrusted chains

A chain whose proofs are not trusted (a "broken prover" in `protocol-docs/interop-gating.md`) can
have L1 finalize any withdrawal or failed-deposit claim: `fromChain c a x` with any asset `a` and
any `uint256` amount `x`, interleaved arbitrarily with other chains' deposits and withdrawals and
the owner's calls.  The nullifier, interop-handler and router checks only remove steps, so they
are abstracted away.  What the model keeps is that a withdrawal's chain is a registered chain: the
router accepts only a proven message's sender chain, never L1 itself (`L1AR:264-269`), the message
root proves messages only for chains whose batches it stores or whose settlement layer the chain
asset handler confirms (`L1MR:96-120`), and a failed-deposit claim names the chain the deposit went
to.  Deposits go to registered chains through the Bridgehub.  That restriction is the guard
`registered c` on the two hooks, a model boundary: that L1 accepts no message or claim for an
unregistered chain id is argued from those lines, not proved here.

The guard matters only for an id that is not registered when the call runs.  Such an id is never
pending and never enabled (only chains registered at the upgrade become pending, and
`enableInterop` requires registration), so a withdrawal of an L1-native asset attributed to it
would be capped under its own key at its `deposited + backfill`: zero, unless the owner set a
backfill for that id (`setChainBalanceBackfill` refuses only `INTEROP_POOL_CHAIN_ID`, `L1NTV:224`).
There are two exceptions.  Under L1's own chain id the asset's origin equals the chain, so
`_trackedBalance` does not track the withdrawal and only `bridgedOut` bounds it.  A withdrawal
attributed to `INTEROP_POOL_CHAIN_ID` would be counted under the pool key and draw on the pool.

Only the vault applies the cap, so transfers through another asset handler are outside this model.
`L1AssetRouter._checkAssetHandlerAllowed` (`L1AR:271-288`) lets a chain without interop use only
the vault and the Bridgehub's chain asset handler; that this keeps every token transfer of a
disabled chain inside the model is argued from source, not proved here.  Enabled chains may use any
handler, and such transfers are not counted under the pool key.

## Ghost-free run quantities

`releasedFrom c a ls` adds the amounts of the `fromChain c a ·` labels of a run: what the vault
released or minted for chain `c` in asset `a`.  `releasedUnderKey` and `releasedByEnabled` follow
the run's states: the amounts of withdrawals counted under a given key, and of withdrawals by chains
enabled at the time.  `populatedIn a ls` adds the legacy amounts of the run's `populate a ·` labels.
`capHeadroom s k a = deposited + backfill - withdrawn` (an integer) is the headroom of key `k` in
asset `a`.
-/

namespace Contracts.L1NativeTokenVault.Bulkhead

/-! ## Constants -/

/-- `2^256`: every `uint256` value is below it. -/
def capWordBound : ℕ := 2 ^ 256

/-- `type(uint48).max + 1 = 2^48`.  `_validateChainParams` (`BHB:497-499`) refuses a larger chain id
("also keeps `INTEROP_POOL_CHAIN_ID` from ever being registered"), so registered ids are below it. -/
def chainIdCap : ℕ := 2 ^ 48

/-- `INTEROP_POOL_CHAIN_ID = uint256(keccak256("interop.pool")) - 1` (`common/Config.sol:37`),
computed off-line: `cast keccak "interop.pool"` is
`0x9cc761dc886485f14b36f25560c0fb8022a9b62e0778612e6cc02bf213382d0a`. -/
def interopPoolChainId : ℕ := 0x9cc761dc886485f14b36f25560c0fb8022a9b62e0778612e6cc02bf213382d09

/-- The constants the cap reads: L1's chain id (`block.chainid`) and the pool key. -/
structure CapConfig where
  /-- `block.chainid` on L1, which is also the vault's `L1_CHAIN_ID` (`L1NTV:273`). -/
  l1 : ℕ
  /-- `INTEROP_POOL_CHAIN_ID` (`common/Config.sol:37`). -/
  pool : ℕ

/-- **THE PINNED PREMISE ON THE CONSTANTS.**  L1's chain id is nonzero, and the pool key is a
`uint256` at or above the chain-id cap, so no registered chain has it.  This is a fact about the two
deployed values (`deployedCapConfig`), not a hash property. -/
def CapConfig.Ok (cfg : CapConfig) : Prop :=
  0 < cfg.l1 ∧ chainIdCap ≤ cfg.pool ∧ cfg.pool < capWordBound

/-- The deployed constants on Ethereum mainnet (`block.chainid = 1`). -/
def deployedCapConfig : CapConfig := ⟨1, interopPoolChainId⟩

/-! ## State -/

/-- The cap's storage, and what it reads from the message root, the Bridgehub and the registry. -/
structure CapState where
  /-- `bridgedOut[assetId]` (`L1NTV:90`): the net amount of an L1-native asset bridged out. -/
  bridgedOut : ℕ → ℕ
  /-- `bridgedOutPopulated[assetId]` (`L1NTV:93`). -/
  populated : ℕ → Bool
  /-- `chainTotalDeposited[key][assetId]` (`L1NTV:96`). -/
  deposited : ℕ → ℕ → ℕ
  /-- `chainTotalWithdrawn[key][assetId]` (`L1NTV:99`). -/
  withdrawn : ℕ → ℕ → ℕ
  /-- `chainBalanceBackfill[chainId][assetId]` (`L1NTV:102`). -/
  backfill : ℕ → ℕ → ℕ
  /-- `chainBalanceInInteropPool[chainId][assetId]` (`L1NTV:105`). -/
  inPool : ℕ → ℕ → Bool
  /-- `chainBalanceBackfillPending[chainId]` (`L1NTV:108`). -/
  pending : ℕ → Bool
  /-- `initializeUpgrade`'s `reinitializer(2)` has run (`L1NTV:291`). -/
  upgraded : Bool
  /-- `L1MessageRoot.interopEnabled[chainId]` (`L1MR:49`). -/
  interop : ℕ → Bool
  /-- The Bridgehub has registered the chain (`getZKChain(chainId) != address(0)`, `L1MR:74-75`). -/
  registered : ℕ → Bool
  /-- `originChainId[assetId]` (`NTVB`, written at `:568`); `0` while the asset is unregistered. -/
  origin : ℕ → ℕ

/-- `map[k][a] = v` on a two-level mapping. -/
def capUpd2 {β : Type} (f : ℕ → ℕ → β) (k a : ℕ) (v : β) : ℕ → ℕ → β :=
  Function.update f k (Function.update (f k) a v)

/-! ## Labels -/

/-- One call that writes the cap's storage or what it reads. -/
inductive CapLabel where
  /-- `_handleBridgeToChain(chain, asset, amount)`: a deposit. -/
  | toChain (chain asset amount : ℕ)
  /-- `_handleBridgeFromChain(chain, asset, amount)`: a withdrawal or a failed-deposit claim. -/
  | fromChain (chain asset amount : ℕ)
  /-- One entry of `setChainBalanceBackfill(chain, [asset], [amount])`. -/
  | setBackfill (chain asset amount : ℕ)
  /-- `markBackfilled(chain)`. -/
  | markBackfilled (chain : ℕ)
  /-- `moveChainBalanceToInteropPool(chain, asset)`. -/
  | moveToPool (chain asset : ℕ)
  /-- `initializeUpgrade()`. -/
  | initializeUpgrade
  /-- `L1MessageRoot.enableInterop(chain, _)`. -/
  | enableInterop (chain : ℕ)
  /-- The Bridgehub registers `chain`. -/
  | registerChain (chain : ℕ)
  /-- The registry's first write of `originChainId[asset] = originChain`. -/
  | registerAsset (asset originChain : ℕ)
  /-- One asset of `populateBridgedOut`, whose `legacyBridgedOut(asset)` is `legacyAmount`. -/
  | populate (asset legacyAmount : ℕ)
  deriving DecidableEq

/-- The chain a label acts for, if any. -/
def CapLabel.chain? : CapLabel → Option ℕ
  | .toChain c _ _ => some c
  | .fromChain c _ _ => some c
  | .setBackfill c _ _ => some c
  | .markBackfilled c => some c
  | .moveToPool c _ => some c
  | .enableInterop c => some c
  | .registerChain c => some c
  | .initializeUpgrade => none
  | .registerAsset _ _ => none
  | .populate _ _ => none

/-! ## The functions -/

/-- `_trackedBalance(chain, origin)` (`L1NTV:468-477`), as `some key` when the balance is tracked
and `none` when it is not:

    if (messageRoot.isInteropEnabled(_chainId)) {
        return (!messageRoot.isInteropEnabled(_assetOriginChainId), INTEROP_POOL_CHAIN_ID);
    }
    return (_assetOriginChainId != _chainId, _chainId); -/
def capTrackedKey (cfg : CapConfig) (s : CapState) (chain originChain : ℕ) : Option ℕ :=
  if s.interop chain = true then
    if s.interop originChain = true then none else some cfg.pool
  else if originChain = chain then none else some chain

/-- `bridgedOut[asset] += amount`, checked (`L1NTV:427`, `:207`). -/
def capCreditBridgedOut (s : CapState) (asset amount : ℕ) : Option CapState :=
  if s.bridgedOut asset + amount < capWordBound then
    some { s with bridgedOut := Function.update s.bridgedOut asset (s.bridgedOut asset + amount) }
  else none

/-- `chainTotalDeposited[key][asset] += amount`, checked (`L1NTV:431`, `:233-234`, `:256`). -/
def capCreditDeposited (s : CapState) (key asset amount : ℕ) : Option CapState :=
  if s.deposited key asset + amount < capWordBound then
    some { s with deposited := capUpd2 s.deposited key asset (s.deposited key asset + amount) }
  else none

/-- **`_handleBridgeToChain(chain, asset, amount)`** (`L1NTV:424-433`):

    uint256 assetOriginChainId = originChainId[_assetId];
    if (assetOriginChainId == block.chainid) {
        bridgedOut[_assetId] += _amount;
    }
    (bool tracked, uint256 balanceChainId) = _trackedBalance(_chainId, assetOriginChainId);
    if (tracked) {
        chainTotalDeposited[balanceChainId][_assetId] += _amount;
    } -/
def capHandleToChain (cfg : CapConfig) (s : CapState) (chain asset amount : ℕ) :
    Option CapState :=
  match (if s.origin asset = cfg.l1 then capCreditBridgedOut s asset amount else some s) with
  | none => none
  | some s₁ =>
    match capTrackedKey cfg s chain (s.origin asset) with
    | none => some s₁
    | some key => capCreditDeposited s₁ key asset amount

/-- `require(bridgedOut[asset] >= amount); bridgedOut[asset] -= amount` (`L1NTV:442-445`). -/
def capDebitBridgedOut (s : CapState) (asset amount : ℕ) : Option CapState :=
  if s.bridgedOut asset < amount then none
  else some { s with bridgedOut := Function.update s.bridgedOut asset (s.bridgedOut asset - amount) }

/-- The tracked branch of `_handleBridgeFromChain` for the key `key` (`L1NTV:449-457`):

    uint256 newWithdrawn = chainTotalWithdrawn[balanceChainId][_assetId] + _amount;
    if (!chainBalanceBackfillPending[balanceChainId]) {
        uint256 limit = chainTotalDeposited[balanceChainId][_assetId] +
            chainBalanceBackfill[balanceChainId][_assetId];
        if (newWithdrawn > limit) revert ChainBalanceExceeded(...);
    }
    chainTotalWithdrawn[balanceChainId][_assetId] = newWithdrawn;

Both additions are checked. -/
def capRecordWithdrawal (s : CapState) (key asset amount : ℕ) : Option CapState :=
  if capWordBound ≤ s.withdrawn key asset + amount then none
  else if s.pending key = false then
    if capWordBound ≤ s.deposited key asset + s.backfill key asset then none
    else if s.deposited key asset + s.backfill key asset < s.withdrawn key asset + amount then none
    else some { s with withdrawn := capUpd2 s.withdrawn key asset (s.withdrawn key asset + amount) }
  else some { s with withdrawn := capUpd2 s.withdrawn key asset (s.withdrawn key asset + amount) }

/-- **`_handleBridgeFromChain(chain, asset, amount)`** (`L1NTV:439-459`): the `bridgedOut` check
and debit for an L1-native asset, then the tracked branch. -/
def capHandleFromChain (cfg : CapConfig) (s : CapState) (chain asset amount : ℕ) :
    Option CapState :=
  match (if s.origin asset = cfg.l1 then capDebitBridgedOut s asset amount else some s) with
  | none => none
  | some s₁ =>
    match capTrackedKey cfg s chain (s.origin asset) with
    | none => some s₁
    | some key => capRecordWithdrawal s₁ key asset amount

/-- `_netChainBalance(chain, asset, backfill)` (`L1NTV:484-488`): deposits plus `backfill`
(checked), less withdrawals, and `0` if withdrawals are larger. -/
def capNetChainBalance (s : CapState) (chain asset backfillAmount : ℕ) : Option ℕ :=
  if capWordBound ≤ s.deposited chain asset + backfillAmount then none
  else some (s.deposited chain asset + backfillAmount - s.withdrawn chain asset)

/-- **One entry of `setChainBalanceBackfill`** (`L1NTV:219-239`): refuses the pool key (`:224`), is
write-once while nonzero (`:229`), credits the pool with what the move would have added with the
backfill set if the chain's balance is already in the pool (`:230-235`, the subtraction checked),
then writes the backfill (`:236`).  The amount is a `uint256` calldata word. -/
def capSetBackfillEntry (cfg : CapConfig) (s : CapState) (chain asset amount : ℕ) :
    Option CapState :=
  if chain = cfg.pool then none
  else if capWordBound ≤ amount then none
  else if s.backfill chain asset ≠ 0 then none
  else
    match (if s.inPool chain asset = true then
        match capNetChainBalance s chain asset amount, capNetChainBalance s chain asset 0 with
        | some n₁, some n₀ => if n₁ < n₀ then none else capCreditDeposited s cfg.pool asset (n₁ - n₀)
        | _, _ => none
      else some s) with
    | none => none
    | some s₁ => some { s₁ with backfill := capUpd2 s₁.backfill chain asset amount }

/-- `markBackfilled(chain)` (`L1NTV:242-246`): requires the chain to be pending, clears the flag.
It reads no counter. -/
def capMarkBackfilled (s : CapState) (chain : ℕ) : Option CapState :=
  if s.pending chain = true then some { s with pending := Function.update s.pending chain false }
  else none

/-- `moveChainBalanceToInteropPool(chain, asset)` (`L1NTV:249-258`): interop enabled, not pending,
not yet moved; the pool's deposits gain `_netChainBalance(chain, asset, backfill)`. -/
def capMoveToPool (cfg : CapConfig) (s : CapState) (chain asset : ℕ) : Option CapState :=
  if s.interop chain = false then none
  else if s.pending chain = true then none
  else if s.inPool chain asset = true then none
  else
    match capNetChainBalance s chain asset (s.backfill chain asset) with
    | none => none
    | some amount =>
      capCreditDeposited { s with inPool := capUpd2 s.inPool chain asset true } cfg.pool asset amount

/-- `initializeUpgrade()` (`L1NTV:291-298`): once (`reinitializer(2)`), marks every registered chain
pending and leaves the other flags. -/
def capInitializeUpgrade (s : CapState) : Option CapState :=
  if s.upgraded = true then none
  else some { s with upgraded := true, pending := fun c => s.registered c || s.pending c }

/-- `L1MessageRoot.enableInterop(chain, _)` (`L1MR:72-89`): registered (`:74-75`), not yet enabled
(`:76`), not pending its backfill (`:80`). -/
def capEnableInterop (s : CapState) (chain : ℕ) : Option CapState :=
  if s.registered chain = false then none
  else if s.interop chain = true then none
  else if s.pending chain = true then none
  else some { s with interop := Function.update s.interop chain true }

/-- The Bridgehub registers a chain, with `_validateChainParams`'s id checks (`BHB:491-503`). -/
def capRegisterChain (cfg : CapConfig) (s : CapState) (chain : ℕ) : Option CapState :=
  if chain = 0 ∨ chainIdCap ≤ chain ∨ chain = cfg.l1 ∨ s.registered chain = true then none
  else some { s with registered := Function.update s.registered chain true }

/-- The registry's first write of `originChainId[asset]`, never `0`. -/
def capRegisterAsset (s : CapState) (asset originChain : ℕ) : Option CapState :=
  if s.origin asset ≠ 0 ∨ originChain = 0 then none
  else some { s with origin := Function.update s.origin asset originChain }

/-- One asset of `populateBridgedOut` (`L1NTV:189-212`): not yet populated (the skip writes
nothing), native to L1 (`legacyBridgedOut` reverts otherwise, `:156-157`), then
`bridgedOut[asset] += legacyAmount`, checked. -/
def capPopulate (cfg : CapConfig) (s : CapState) (asset legacyAmount : ℕ) : Option CapState :=
  if s.populated asset = true then none
  else if s.origin asset ≠ cfg.l1 then none
  else if capWordBound ≤ s.bridgedOut asset + legacyAmount then none
  else some { s with
    populated := Function.update s.populated asset true
    bridgedOut := Function.update s.bridgedOut asset (s.bridgedOut asset + legacyAmount) }

/-- **ONE SUCCESSFUL CALL.**  The two hooks are reached only for registered chains and `uint256`
amounts (see the header). -/
def capStep (cfg : CapConfig) : CapLabel → CapState → Option CapState
  | .toChain c a x, s =>
    if s.registered c = true ∧ x < capWordBound then capHandleToChain cfg s c a x else none
  | .fromChain c a x, s =>
    if s.registered c = true ∧ x < capWordBound then capHandleFromChain cfg s c a x else none
  | .setBackfill c a v, s => capSetBackfillEntry cfg s c a v
  | .markBackfilled c, s => capMarkBackfilled s c
  | .moveToPool c a, s => capMoveToPool cfg s c a
  | .initializeUpgrade, s => capInitializeUpgrade s
  | .enableInterop c, s => capEnableInterop s c
  | .registerChain c, s => capRegisterChain cfg s c
  | .registerAsset a o, s => capRegisterAsset s a o
  | .populate a L, s => capPopulate cfg s a L

/-- **RUNS.**  A sequence of successful calls, in any interleaving. -/
inductive CapRun (cfg : CapConfig) : CapState → List CapLabel → CapState → Prop
  | nil (s : CapState) : CapRun cfg s [] s
  | cons {s t u : CapState} {l : CapLabel} {ls : List CapLabel} :
      capStep cfg l s = some t → CapRun cfg t ls u → CapRun cfg s (l :: ls) u

/-! ## Run quantities -/

/-- The total amount of the run's withdrawals and claims for `chain` in `asset`: the sum of `x` over
its `fromChain chain asset x` labels. -/
def releasedFrom (chain asset : ℕ) : List CapLabel → ℕ
  | [] => 0
  | l :: ls =>
    (match l with
      | .fromChain c a x => if c = chain ∧ a = asset then x else 0
      | _ => 0) + releasedFrom chain asset ls

/-- The total amount of a run's withdrawals and claims in `asset` that were counted under `key`
(tracked, with `_trackedBalance` returning `key` in the state the call ran in). -/
def releasedUnderKey (cfg : CapConfig) (key asset : ℕ) : CapState → List CapLabel → ℕ
  | _, [] => 0
  | s, l :: ls =>
    (match l with
      | .fromChain c a x =>
        if a = asset ∧ capTrackedKey cfg s c (s.origin a) = some key then x else 0
      | _ => 0) +
    (match capStep cfg l s with
      | some t => releasedUnderKey cfg key asset t ls
      | none => 0)

/-- The total amount of a run's withdrawals and claims in `asset` by chains that had interop
enabled when the call ran. -/
def releasedByEnabled (cfg : CapConfig) (asset : ℕ) : CapState → List CapLabel → ℕ
  | _, [] => 0
  | s, l :: ls =>
    (match l with
      | .fromChain c a x => if a = asset ∧ s.interop c = true then x else 0
      | _ => 0) +
    (match capStep cfg l s with
      | some t => releasedByEnabled cfg asset t ls
      | none => 0)

/-- The legacy amounts a run's `populate asset ·` labels add to `bridgedOut[asset]`. -/
def populatedIn (asset : ℕ) : List CapLabel → ℕ
  | [] => 0
  | l :: ls =>
    (match l with
      | .populate a L => if a = asset then L else 0
      | _ => 0) + populatedIn asset ls

/-- **HEADROOM** `h_k(a) = deposited + backfill - withdrawn`, as an integer. -/
def capHeadroom (s : CapState) (key asset : ℕ) : ℤ :=
  (s.deposited key asset : ℤ) + (s.backfill key asset : ℤ) - (s.withdrawn key asset : ℤ)

/-- What a key withdrew beyond its deposits and backfill (`0` if nothing). -/
def capDeficit (s : CapState) (key asset : ℕ) : ℕ :=
  s.withdrawn key asset - (s.deposited key asset + s.backfill key asset)

/-! ## Start states and the run invariant -/

/-- **THE STATE RIGHT AFTER THE v35 UPGRADE.**  `upgradeToAndCall` runs `initializeUpgrade` in the
upgrade transaction, so the cap's counters are fresh storage, every registered chain is pending,
and the message root has enabled no chain.  `bridgedOut`, `bridgedOutPopulated` and the origin map
are whatever they were. -/
structure CapUpgradeState (cfg : CapConfig) (s : CapState) : Prop where
  deposited_zero : ∀ k a, s.deposited k a = 0
  withdrawn_zero : ∀ k a, s.withdrawn k a = 0
  backfill_zero : ∀ k a, s.backfill k a = 0
  inPool_false : ∀ c a, s.inPool c a = false
  interop_false : ∀ c, s.interop c = false
  upgraded : s.upgraded = true
  pending_eq : ∀ c, s.pending c = s.registered c
  registered_valid : ∀ c, s.registered c = true → c ≠ 0 ∧ c < chainIdCap ∧ c ≠ cfg.l1
  bridgedOut_lt : ∀ a, s.bridgedOut a < capWordBound

/-- **THE RUN INVARIANT.**  Registered chain ids pass the Bridgehub's checks; interop is enabled
only on registered, non-pending chains; only enabled chains have moved balances; the upgrade has
run; the pool key is never pending and has no backfill; every stored value is a `uint256`. -/
structure CapWF (cfg : CapConfig) (s : CapState) : Prop where
  registered_valid : ∀ c, s.registered c = true → c ≠ 0 ∧ c < chainIdCap ∧ c ≠ cfg.l1
  interop_registered : ∀ c, s.interop c = true → s.registered c = true
  inPool_interop : ∀ c a, s.inPool c a = true → s.interop c = true
  interop_not_pending : ∀ c, s.interop c = true → s.pending c = false
  upgraded : s.upgraded = true
  pool_not_pending : s.pending cfg.pool = false
  pool_backfill_zero : ∀ a, s.backfill cfg.pool a = 0
  deposited_lt : ∀ k a, s.deposited k a < capWordBound
  withdrawn_lt : ∀ k a, s.withdrawn k a < capWordBound
  backfill_lt : ∀ k a, s.backfill k a < capWordBound
  bridgedOut_lt : ∀ a, s.bridgedOut a < capWordBound

end Contracts.L1NativeTokenVault.Bulkhead
