import EraSpec.Contracts.NativeTokenVaultBase.Specs.RegistryAndEscrow

/-!
# Model at head: the escrow ledger with `populateBridgedOut`

**Commits.** era-contracts `main` at `70096e2ea6eeb5373992e178064c4b26dcf6436a` and
`draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`.  `bridge/ntv/L1NativeTokenVault.sol`
and `bridge/ntv/NativeTokenVaultBase.sol` are unchanged on `main` since
`3605e82dbdca5b60bd7bc6bde14ebb52a6b09b73` and on `draft/v0.35.0` since
`d9f678900e1bc8286412b78f56d4a9f443983c29`, where this model was first written.  Line numbers
are `main`'s unless marked.  `draft/v0.35.0` has the same `populateBridgedOut` and
`legacyBridgedOut` (`L1NativeTokenVault.sol:146-212` there) and the same `bridgedOut` updates
in its hooks (`:424-459` there), plus per-chain caps that only reject inflows (see the last
section).  Paths are relative to `l1-contracts/contracts/`.

**This file is definitions only.**  Statements are in
`EraSpec.Contracts.NativeTokenVaultBase.Properties.EscrowLedgerAtHead`, proofs in
`EraSpec.Contracts.NativeTokenVaultBase.Proofs.EscrowLedgerAtHead`.

## What changed since the pin

`Contracts.NativeTokenVault` (`Specs/RegistryAndEscrow.lean`, pin `c67894b9`) says that
`bridgedOut` moves only in `_handleBridgeToChain` and `_handleBridgeFromChain`, and its runs
start from fresh storage.  At head `L1NativeTokenVault` has a third writer
(`bridge/ntv/L1NativeTokenVault.sol:157-181`):

    function populateBridgedOut(bytes32[] calldata _assetIds) external returns (..) {
        for (..) {
            if (bridgedOutPopulated[assetIdToPopulate]) continue;              // :167-169
            bridgedOutPopulated[assetIdToPopulate] = true;                     // :170
            uint256 legacyAmount = legacyBridgedOut(assetIdToPopulate);        // :174
            if (legacyAmount != 0) bridgedOut[assetIdToPopulate] += legacyAmount; // :175-178
        }
    }

It takes no privilege, and `bridgedOutPopulated` (`:77`) has no other writer; `bridgedOut`
(`:74`) is otherwise written only by the two hooks (`:335`, `:348`).
`legacyBridgedOut(a)` (`:121-155`) reverts with `AssetNotNativeToL1` unless
`originChainId[a] == L1_CHAIN_ID` (`:125-126`).  `L1_CHAIN_ID` is `block.chainid`
(constructor, `:196`), so the check is the pin's `Native`.  The function then reads one of
two legacy sources:

* for an asset the removed v31 `L1AssetTracker` registered, `MAX_TOKEN_BALANCE -
  tracker.chainBalance(L1_CHAIN_ID, a)` (`:143-145`), the complement of L1's bulkhead there;
* otherwise the sum of the vault's own `DEPRECATED_chainBalance[c][a]` over
  `getAllZKChainChainIDs()` (`:150-154`).

The motivation (`protocol-docs/bridging.md:183-214` at `main`) is an in-place upgrade: the
upgraded vault starts with `bridgedOut == 0` while it still holds the escrow of everything
bridged out before.  Until an asset is populated, its `bridgedOut` counts only what was
bridged out after the upgrade, and an inflow larger than that fails
`InsufficientChainBalance` (`:343-350`).  The two hooks are unchanged since the pin
(`:333-337`, `:343-350`), and so are their call sites in `NativeTokenVaultBase.sol` (`:240`,
`:276`, `:444`, `:447`), which the pin's `bridgeOut` and `bridgeIn` model.  On L1 the registry
maps still have one writer, `_setNewTokenStorage` (`NativeTokenVaultBase.sol:565-575`), reached
from the two registration paths the pin's `StepOp` models (`_registerToken`, `:131-137`, now
with a WETH check that only reverts, and `_ensureAndSaveTokenDeployedInner`, `:550-563`).  The
pin's steps are reused unchanged, with their boundaries (`MODEL-ESCROW`).

## How the model reads it

* **The legacy amount is a parameter.**  `legacy a` is what `legacyBridgedOut(a)` returns.
  The model assumes the call returns: its external reads (`:143-144`, `:150`) and the
  subtraction at `:144` are taken not to revert, so a `populate` step exists for every
  unpopulated native asset.  The amount is taken as fixed for a run.  The source comments say
  that nothing writes the vault's legacy entries any more (`:138-139`, `:147-148`) and that
  the tracker branch is immune to amounts moving between chains, which the tracker's migration
  entry points can still do (`:130-134`); the docs say that chains are never removed from
  the bridgehub list (`protocol-docs/bridging.md:202-205`).  These are claims about deployed
  legacy state that this model does not check.
* **The legacy amount must be backed.**  `populateBridgedOut` does not compare `legacy a`
  with what the vault holds.  The headline results take it as a premise: an unpopulated
  asset's outstanding ledger plus its legacy amount is at most what the vault holds
  (`LedgerBackedAtHead`).  At the in-place upgrade this is `legacy a ≤ escrowed a`
  (`UpgradeStartAtHead.legacyBacked`), the legacy accounting's own solvency.
  `Contracts.NativeTokenVault.Properties.UnbackedLegacyBreaksSolvencyAtHead` shows that the
  model's solvency needs this premise.
* **One asset per step.**  A successful batch is a sequence of successful single-asset steps
  with nothing in between, so the model's runs contain every batch.  A batch that reverts
  midway is no step.  A repeated or already-populated asset is skipped before the native
  check (`:167-169`), so skipping never reverts (`StepOpAtHead.populateSkip`).
* **Start states.**  The pin's runs start at `empty`.  Here a run starts at any state.  The
  run results take either the invariant `LedgerBackedAtHead` or the in-place-upgrade state
  `UpgradeStartAtHead`: `bridgedOut` zero, nothing populated, the post-upgrade flow audit
  zero, and the legacy amounts backed.  A fresh deployment after the trackers were removed
  is the case `legacy = 0` (`protocol-docs/bridging.md:206-207`), in which `populate` only
  sets the flag.

## `draft/v0.35.0`

At `b17415d` (as at `d9f6789`) the population code is the same.  `_handleBridgeToChain`
additionally adds to `chainTotalDeposited` (`L1NativeTokenVault.sol:429-432` there), and
`_handleBridgeFromChain` additionally reverts with `ChainBalanceExceeded` when a tracked
chain's withdrawals would exceed its deposits plus backfill and adds to `chainTotalWithdrawn`
(`:447-458` there).  The new entry points, owner-only `setChainBalanceBackfill` and
`markBackfilled`, permissionless `moveChainBalanceToInteropPool` (`:219-258` there) and the
proxy admin's `initializeUpgrade` (`:291-298` there), write only the per-chain maps, never
`bridgedOut`, `bridgedOutPopulated` or the escrow.  So, projected to the storage modelled
here, every successful operation of the v35 vault is a `StepOpAtHead` step (argued from the
source, not proved), and the statements about all runs apply to it.  The enabledness
statements additionally need the per-chain check to pass.  The per-chain maps are not
modelled.
-/

namespace Contracts.NativeTokenVault

/-! ## State -/

/-- The vault at head: the pin's world, plus `bridgedOutPopulated`
(`L1NativeTokenVault.sol:77`). -/
structure WorldAtHead where
  /-- The pin's registry, ledger, escrow and flow audit. -/
  world : World
  /-- `bridgedOutPopulated[assetId]`. -/
  populated : AssetId → Bool

/-- The head world over a pin world with nothing populated. -/
def WorldAtHead.ofWorld (W : World) : WorldAtHead := ⟨W, fun _ => false⟩

/-- What `legacyBridgedOut(a)` returns, for every asset, fixed for the run. -/
abbrev LegacyAmounts := AssetId → ℕ

/-- The legacy amount still to be folded in for `a`: all of it until `a` is populated, then
nothing. -/
def pendingLegacy (legacy : LegacyAmounts) (W : WorldAtHead) (a : AssetId) : ℕ :=
  if W.populated a then 0 else legacy a

/-- The legacy amount already folded into `bridgedOut` for `a`. -/
def populatedLegacy (legacy : LegacyAmounts) (W : WorldAtHead) (a : AssetId) : ℕ :=
  if W.populated a then legacy a else 0

/-! ## `populateBridgedOut` -/

/-- One asset of `populateBridgedOut` past its skip test: the flag is set, and the legacy
amount is added to `bridgedOut` (`L1NativeTokenVault.sol:170-178`).  Adding `0` is the
source's `legacyAmount == 0` case. -/
def populateAtHead (legacy : LegacyAmounts) (W : WorldAtHead) (a : AssetId) : WorldAtHead where
  world :=
    { W.world with vault :=
        { W.world.vault with
          bridgedOut := upd W.world.vault.bridgedOut a (W.world.vault.bridgedOut a + legacy a) } }
  populated := upd W.populated a true

/-! ## Runs at head -/

/-- One operation of the vault at head: a pin operation, or one asset of
`populateBridgedOut`. -/
inductive OpAtHead where
  /-- A registration, flow or donation, as at the pin. -/
  | pin (o : Op)
  /-- `populateBridgedOut` on the single asset `a`. -/
  | populate (a : AssetId)

/-- The (chain, token) pair an operation hashes: a pin operation's, and none for a
population. -/
def OpAtHead.pair (thisChain : Chain) : OpAtHead → Option (Chain × Address)
  | .pin o => o.pair thisChain
  | .populate _ => none

/-- The pairs a logged head run hashes. -/
def registeredPairsAtHead (thisChain : Chain) (log : List OpAtHead) : Finset (Chain × Address) :=
  (log.filterMap (OpAtHead.pair thisChain)).toFinset

/-- **ONE OPERATION OF THE VAULT AT HEAD, LABELLED.** -/
inductive StepOpAtHead (e : NtvAssetId) (thisChain : Chain) (legacy : LegacyAmounts) :
    OpAtHead → WorldAtHead → WorldAtHead → Prop
  /-- A pin operation.  It leaves the population flags alone. -/
  | pin {o : Op} {W : WorldAtHead} {X : World} : StepOp e thisChain o W.world X →
      StepOpAtHead e thisChain legacy (.pin o) W ⟨X, W.populated⟩
  /-- An asset already populated is skipped (`:167-169`), whether or not it is native. -/
  | populateSkip {W : WorldAtHead} {a : AssetId} : W.populated a = true →
      StepOpAtHead e thisChain legacy (.populate a) W W
  /-- An unpopulated asset native to this chain is populated (`:170-178`).  `legacyBridgedOut`
  reverts for an asset that is not native (`:125-126`); its other reads are assumed to return
  `legacy a` (see the module header). -/
  | populate {W : WorldAtHead} {a : AssetId} : W.populated a = false →
      Native thisChain W.world.vault a →
      StepOpAtHead e thisChain legacy (.populate a) W (populateAtHead legacy W a)

/-- **A RUN AT HEAD, WITH EVERY OPERATION LOGGED, OLDEST FIRST.** -/
inductive ReachLogAtHead (e : NtvAssetId) (thisChain : Chain) (legacy : LegacyAmounts) :
    WorldAtHead → WorldAtHead → List OpAtHead → Prop
  | refl {W} : ReachLogAtHead e thisChain legacy W W []
  | tail {W X Y log o} : ReachLogAtHead e thisChain legacy W X log →
      StepOpAtHead e thisChain legacy o X Y → ReachLogAtHead e thisChain legacy W Y (log ++ [o])

/-! ## Start states and invariants -/

/-- **THE LEDGER IS BACKED, LEGACY INCLUDED.**  For every asset, what `bridgedOut` records
plus the legacy amount still to be populated is at most what the vault holds.  For a
populated asset this is the pin's solvency. -/
def LedgerBackedAtHead (legacy : LegacyAmounts) (W : WorldAtHead) : Prop :=
  ∀ a, W.world.vault.bridgedOut a + pendingLegacy legacy W a ≤ W.world.vault.escrowed a

/-- **THE VAULT RIGHT AFTER THE IN-PLACE UPGRADE.**  `bridgedOut` is zero
(`protocol-docs/bridging.md:185`), nothing is populated, the flow audit counts from here, and
the legacy accounting never claims more than the vault holds.  The registry is whatever the
upgraded vault had. -/
structure UpgradeStartAtHead (legacy : LegacyAmounts) (W : WorldAtHead) : Prop where
  ledgerZero : ∀ a, W.world.vault.bridgedOut a = 0
  unpopulated : ∀ a, W.populated a = false
  auditInZero : ∀ a, W.world.audit.totalIn a = 0
  auditOutZero : ∀ a, W.world.audit.totalOut a = 0
  /-- The premise the source does not check: the legacy accounting is backed by escrow. -/
  legacyBacked : ∀ a, legacy a ≤ W.world.vault.escrowed a

/-- **THE FLOW AUDIT AT HEAD.**  For a native asset, the ledger is the post-start net flow
plus the legacy amount already populated.  An unregistered asset has seen no flow and has
not been populated. -/
structure AuditedAtHead (legacy : LegacyAmounts) (thisChain : Chain) (W : WorldAtHead) :
    Prop where
  netFlow : ∀ a, Native thisChain W.world.vault a →
    W.world.vault.bridgedOut a + W.world.audit.totalIn a
      = W.world.audit.totalOut a + populatedLegacy legacy W a
  unregisteredQuiet : ∀ a, ¬ Registered W.world.vault a →
    W.world.audit.totalIn a = 0 ∧ W.world.audit.totalOut a = 0 ∧ W.populated a = false

/-! ## A concrete in-place upgrade, for the witnesses -/

/-- A vault that had registered the native token `t` before the upgrade and holds `held` of
it.  Nothing is recorded in `bridgedOut` yet, nothing is populated, the post-upgrade audit is
empty. -/
def upgradedVaultAtHead (e : NtvAssetId) (thisChain : Chain) (t : Address) (held : ℕ) :
    WorldAtHead where
  world :=
    { vault :=
        { registerNative e thisChain empty.vault t with
          escrowed := upd (fun _ => 0) (e thisChain t) held }
      audit := empty.audit }
  populated := fun _ => false

/-- The legacy amounts of that vault: `amt` for `t`'s asset, zero elsewhere. -/
def legacyOfAtHead (e : NtvAssetId) (thisChain : Chain) (t : Address) (amt : ℕ) :
    LegacyAmounts :=
  upd (fun _ => 0) (e thisChain t) amt

end Contracts.NativeTokenVault
