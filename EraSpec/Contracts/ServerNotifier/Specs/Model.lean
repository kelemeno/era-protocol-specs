import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: `ServerNotifier`, every state-changing entry point

Source: era-contracts `draft/v0.35.0`, commit `d9f678900e1bc8286412b78f56d4a9f443983c29`,
`l1-contracts/contracts/governance/ServerNotifier.sol` (142 lines), with OpenZeppelin v4
`Ownable2Step`, `Initializable`, and `common/ReentrancyGuard.sol` (`reentrancyGuardInitializer`,
:43-63).

**This file is definitions only.** Statements are in
`EraSpec.Contracts.ServerNotifier.Properties.Model`, proofs in
`EraSpec.Contracts.ServerNotifier.Proofs.Model`.

## The source (guards in order)

    modifier onlyChainAdmin(uint256 _chainId) {
        if (msg.sender != chainTypeManager.getChainAdmin(_chainId)) revert Unauthorized(...); _; } // :43-48
    function initialize(address _initialOwner) public initializer reentrancyGuardInitializer {
        if (_initialOwner == address(0)) revert ZeroAddress();                              // :58-60
        _transferOwnership(_initialOwner); }                                                // :61
    function setChainTypeManager(IChainTypeManager _ctm) external onlyOwner {
        if (address(_ctm) == address(0)) revert ZeroAddress();                              // :68-70
        chainTypeManager = _ctm; }                                                          // :71
    function migrateToGateway(uint256 _chainId) external onlyChainAdmin(_chainId) {
        uint256 migrationNumber = _getMigrationNumber(_chainId) + 1;                        // :79
        ... require(IL1ChainAssetHandler(cah).isReadyForMigration(_chainId), ...);         // :84-87
        emit MigrateToGateway(_chainId, migrationNumber); }                                 // :89
    function migrateFromGateway(uint256 _chainId) external onlyChainAdmin(_chainId) {
        uint256 migrationNumber = _getMigrationNumber(_chainId) + 1;                        // :97
        emit MigrateFromGateway(_chainId, migrationNumber); }                               // :98
    function setUpgradeTimestamp(uint256 _chainId, uint256 _upgradeTimestamp) external onlyChainAdmin(_chainId) {
        if (_upgradeTimestamp == 0) revert ZeroUpgradeTimestamp();                         // :114-116
        uint256 oldProtocolVersion = chainTypeManager.getProtocolVersion(_chainId);         // :117
        if (ctm.upgradeTransition(old) == address(0) && ctm.upgradeCutHash(old) == bytes32(0))
            revert CutDataForProtocolVersionNotAvailable(old);                              // :120-125
        IUpgradePreconditionChecker checker = upgradePreconditionChecker[old];              // :126
        if (address(checker) != address(0))
            checker.checkUpgradePreconditions(_chainId, ctm.getZKChain(_chainId));          // :127-129
        protocolVersionToUpgradeTimestamp[_chainId][old] = _upgradeTimestamp;               // :130
        emit UpgradeTimestampUpdated(...); }                                                // :131
    function setUpgradePreconditionChecker(uint256 _old, IUpgradePreconditionChecker _checker)
        external onlyOwner { upgradePreconditionChecker[_old] = _checker; ... }             // :135-141

## Modelling choices

* **The CTM is a view per transaction.** Every call into `chainTypeManager` (and, through its
  `BRIDGE_HUB()`, into the bridgehub and chain asset handler) is a read of external state. The
  environment `Env` gives, for each address, the answers of the contract there
  (`CtmView`), or `none` when calls to it revert. The zero address has no code
  (`Env.zeroNoCode`); a high-level call with a return value to it reverts. One `CtmView` is
  used for the whole transaction. Between transactions the environment is arbitrary.
* **The precondition checker** either returns (`Env.checkerOk`) or reverts (no step).
* **Ownership** is OpenZeppelin v4 `Ownable2Step`: `transferOwnership` (owner) nominates,
  `acceptOwnership` (nominee) takes over and clears the nomination, `renounceOwnership` (owner)
  clears both. `_transferOwnership` in `initialize` clears the nomination too.
* **Initialization.** `initialized` is OpenZeppelin `Initializable._initialized ≠ 0` on the
  proxy (top-level call; the constructor branch for a contract without code does not apply).
  `guard` is the reentrancy slot being nonzero; no function here is `nonReentrant`, so it is
  only set.
* **Ghost logs.** `writes` records each `setUpgradeTimestamp` with the caller, the CTM address
  and the `CtmView` it read; `events` records each migration event with its caller and view.
* **Not modelled:** proxy implementation swaps by the CTM-domain `ProxyAdmin` (they can
  rewrite any storage and are outside every result here); events other than the migration
  events (the timestamp write is the `writes` log).
* `msg.sender` is never the zero address (`caller ≠ 0` in every step).
-/

namespace Contracts.ServerNotifier

open Clear

/-- Addresses as 256-bit words; `0` is the zero address. -/
abbrev Address := UInt256

/-- What the contract at `chainTypeManager` answers during one transaction. -/
structure CtmView where
  /-- `getChainAdmin(chainId)`. -/
  chainAdmin : UInt256 → Address
  /-- `getProtocolVersion(chainId)`. -/
  protocolVersion : UInt256 → UInt256
  /-- `upgradeTransition(v)`. -/
  upgradeTransition : UInt256 → Address
  /-- `upgradeCutHash(v)`. -/
  upgradeCutHash : UInt256 → UInt256
  /-- `getZKChain(chainId)`. -/
  zkChain : UInt256 → Address
  /-- `IChainAssetHandlerBase(BRIDGE_HUB().chainAssetHandler()).migrationNumber(chainId)`. -/
  migrationNumber : UInt256 → ℕ
  /-- `IL1ChainAssetHandler(...).isReadyForMigration(chainId)`. -/
  readyForMigration : UInt256 → Bool

/-- The environment of one transaction. -/
structure Env where
  /-- The answers of the contract at each address; `none` when calls to it revert. -/
  ctm : Address → Option CtmView
  /-- The zero address has no code: calls to it revert. -/
  zeroNoCode : ctm 0 = none
  /-- `checker.checkUpgradePreconditions(chainId, zkChain)` returns (`true`) or reverts. -/
  checkerOk : Address → UInt256 → Address → Bool

/-- One `setUpgradeTimestamp` that took effect. -/
structure Write where
  chain : UInt256
  version : UInt256
  value : UInt256
  caller : Address
  /-- The `chainTypeManager` read. -/
  ctmAddr : Address
  /-- What it answered. -/
  view : CtmView

/-- The migration events. -/
inductive Dir where
  | toGateway
  | fromGateway
deriving DecidableEq

/-- One `MigrateToGateway` / `MigrateFromGateway` event. -/
structure MigEvent where
  dir : Dir
  chain : UInt256
  number : ℕ
  caller : Address
  view : CtmView

/-- `ServerNotifier`'s storage plus ghost logs. -/
structure State where
  /-- `Initializable._initialized ≠ 0`. -/
  initialized : Bool
  /-- The reentrancy slot is nonzero. -/
  guard : Bool
  owner : Address
  pending : Address
  /-- `chainTypeManager`. -/
  ctm : Address
  /-- `protocolVersionToUpgradeTimestamp[chainId][oldProtocolVersion]`. -/
  ts : UInt256 → UInt256 → UInt256
  /-- `upgradePreconditionChecker[oldProtocolVersion]`. -/
  checker : UInt256 → Address
  /-- Ghost: timestamp writes, oldest first. -/
  writes : List Write
  /-- Ghost: migration events, oldest first. -/
  events : List MigEvent

/-- Transactions. -/
inductive Label where
  | init (caller newOwner : Address)
  | setCTM (caller newCtm : Address)
  | setChecker (caller : Address) (v : UInt256) (checker : Address)
  | setTs (caller : Address) (chain t : UInt256)
  | migrate (caller : Address) (dir : Dir) (chain : UInt256)
  | transferOwnership (caller newOwner : Address)
  | acceptOwnership (caller : Address)
  | renounceOwnership (caller : Address)

/-- Update one entry of the schedule. -/
def setEntry (ts : UInt256 → UInt256 → UInt256) (c v t : UInt256) : UInt256 → UInt256 → UInt256 :=
  fun c' v' => if c' = c ∧ v' = v then t else ts c' v'

/-- An upgrade from `v` is scheduled on the CTM: a registry transition or a legacy cut hash
(`ServerNotifier.sol:120-125`). -/
def Scheduled (V : CtmView) (v : UInt256) : Prop :=
  V.upgradeTransition v ≠ 0 ∨ V.upgradeCutHash v ≠ 0

/-- One successful transaction in environment `E`. -/
inductive Step (E : Env) : State → Label → State → Prop where
  /-- `initialize` (:57-62): `initializer`, `reentrancyGuardInitializer`, nonzero owner. -/
  | init {s : State} {caller o : Address} :
      caller ≠ 0 → s.initialized = false → s.guard = false → o ≠ 0 →
      Step E s (.init caller o)
        { s with initialized := true, guard := true, owner := o, pending := 0 }
  /-- `setChainTypeManager` (:67-72). -/
  | setCTM {s : State} {caller a : Address} :
      caller ≠ 0 → caller = s.owner → a ≠ 0 →
      Step E s (.setCTM caller a) { s with ctm := a }
  /-- `setUpgradePreconditionChecker` (:135-141). -/
  | setChecker {s : State} {caller : Address} {v : UInt256} {a : Address} :
      caller ≠ 0 → caller = s.owner →
      Step E s (.setChecker caller v a) { s with checker := Function.update s.checker v a }
  /-- `setUpgradeTimestamp` (:113-132), guards in source order. -/
  | setTs {s : State} {caller : Address} {c t : UInt256} {V : CtmView} :
      caller ≠ 0 →
      E.ctm s.ctm = some V → caller = V.chainAdmin c →                  -- onlyChainAdmin
      t ≠ 0 →                                                           -- :114-116
      Scheduled V (V.protocolVersion c) →                               -- :117-125
      (s.checker (V.protocolVersion c) = 0 ∨
        E.checkerOk (s.checker (V.protocolVersion c)) c (V.zkChain c) = true) → -- :126-129
      Step E s (.setTs caller c t)
        { s with ts := setEntry s.ts c (V.protocolVersion c) t,         -- :130
                 writes := s.writes ++ [⟨c, V.protocolVersion c, t, caller, s.ctm, V⟩] }
  /-- `migrateToGateway` (:78-90) and `migrateFromGateway` (:96-99). -/
  | migrate {s : State} {caller : Address} {d : Dir} {c : UInt256} {V : CtmView} :
      caller ≠ 0 →
      E.ctm s.ctm = some V → caller = V.chainAdmin c →                  -- onlyChainAdmin
      V.migrationNumber c + 1 < 2 ^ 256 →                               -- checked `+ 1`
      (d = .toGateway → V.readyForMigration c = true) →                 -- :84-87
      Step E s (.migrate caller d c)
        { s with events := s.events ++ [⟨d, c, V.migrationNumber c + 1, caller, V⟩] }
  /-- `Ownable2Step.transferOwnership`, `onlyOwner`. -/
  | transferOwnership {s : State} {caller a : Address} :
      caller ≠ 0 → caller = s.owner →
      Step E s (.transferOwnership caller a) { s with pending := a }
  /-- `Ownable2Step.acceptOwnership`. -/
  | acceptOwnership {s : State} {caller : Address} :
      caller ≠ 0 → s.pending = caller →
      Step E s (.acceptOwnership caller) { s with owner := caller, pending := 0 }
  /-- `Ownable.renounceOwnership`, `onlyOwner`. -/
  | renounceOwnership {s : State} {caller : Address} :
      caller ≠ 0 → caller = s.owner →
      Step E s (.renounceOwnership caller) { s with owner := 0, pending := 0 }

/-- Reachability: any interleaving of transactions, each in any environment. -/
inductive Reach (s₀ : State) : State → Prop where
  | refl : Reach s₀ s₀
  | step {E : Env} {s s' : State} {l : Label} : Reach s₀ s → Step E s l s' → Reach s₀ s'

/-- A logged write was authorized by the CTM it read: nonzero value, caller is that CTM's
admin for the chain, the version is the chain's version there, an upgrade from it is
scheduled, and the CTM address is nonzero. -/
def Write.Authorized (w : Write) : Prop :=
  w.ctmAddr ≠ 0 ∧ w.value ≠ 0 ∧ w.caller = w.view.chainAdmin w.chain ∧
    w.view.protocolVersion w.chain = w.version ∧ Scheduled w.view w.version

/-- A logged migration event was emitted by the chain's admin per the CTM read, with the
chain asset handler's migration number plus one, and (to the gateway) for a chain ready. -/
def MigEvent.Authorized (e : MigEvent) : Prop :=
  e.caller = e.view.chainAdmin e.chain ∧ e.number = e.view.migrationNumber e.chain + 1 ∧
    (e.dir = .toGateway → e.view.readyForMigration e.chain = true)

/-- The proxy's storage before `initialize`. -/
def fresh : State :=
  ⟨false, false, 0, 0, 0, fun _ _ => 0, fun _ => 0, [], []⟩

/-! ## Countermodel: `setUpgradeTimestamp` without the zero check -/

/-- `setUpgradeTimestamp` with `if (_upgradeTimestamp == 0) revert` (:114-116) deleted. -/
inductive SetTsNoZeroCheck (E : Env) : State → Label → State → Prop where
  | setTs {s : State} {caller : Address} {c t : UInt256} {V : CtmView} :
      caller ≠ 0 → E.ctm s.ctm = some V → caller = V.chainAdmin c →
      Scheduled V (V.protocolVersion c) →
      (s.checker (V.protocolVersion c) = 0 ∨
        E.checkerOk (s.checker (V.protocolVersion c)) c (V.zkChain c) = true) →
      SetTsNoZeroCheck E s (.setTs caller c t)
        { s with ts := setEntry s.ts c (V.protocolVersion c) t,
                 writes := s.writes ++ [⟨c, V.protocolVersion c, t, caller, s.ctm, V⟩] }

end Contracts.ServerNotifier
