import Mathlib.Tactic

/-!
# Model: the L2 side a registry transition derives from its two releases

Source: era-contracts branch `draft/v0.35.0` at commit `b17415d20`
(`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`). Paths are relative to `l1-contracts/contracts/`,
and every `file:line` below is at that commit unless another commit is named. This pin is newer
than the `e561b9cc2` snapshot most topics of this folder describe; the L2 tables modelled here
are not part of those topics.

**This file is definitions only.** Statements: `Properties/L2Derivation.lean`; proofs:
`Proofs/L2Derivation.lean`. The run-level topic built on it is `L2Convergence`.

## The derivation

A `CTMTransition` is constructed once and stores the final L2 plan that every chain crossing its
edge executes (`upgrades/registry/objects/CTMTransition.sol:50-122`):

    L2UpgradePlan memory derivedPlan = L2PlanLib.build(
        TransitionDerivationLib.deriveL2Deployments(fromRelease, newRelease), _manifest.l2Plan);  // :80-86
    bool hasL2Side = derivedPlan.deployments.length != 0;                                         // :90
    VersionEdgeLib.requireValidEdge({ ..., _hasL2Side: hasL2Side });                              // :91-97
    if (!hasL2Side) { _requireL2StateKept(fromRelease, newRelease); }                             // :101-109

* `deriveL2Deployments` (`upgrades/registry/libraries/TransitionDerivationLib.sol:95-104`) is
  `deriveL2DeploymentsFromTable(changedL2Rows(from.l2BytecodeInfos(), new.l2BytecodeInfos()),
  new.l2SystemProxyBytecodeInfo())`.
* `changedL2Rows` (:110-134) reverts when the new table is shorter (:118-120) or a nonempty row
  becomes empty (:123-127), and keeps row `i` of the new table exactly when it is nonempty and
  `i >= fromLength || keccak256(_fromTable[i]) != keccak256(_newTable[i])` (:130-132).
* `deriveL2DeploymentsFromTable` (:145-169) turns every nonempty row `i` into one
  `ZKsyncOSSystemProxyUpgrade` at `L2InventoryLib.fixedAddress(L2EcosystemContract(i))` (:165),
  whose descriptor is `abi.encode(row, shell)` (:164).
* `L2PlanLib.build` (`upgrades/registry/libraries/L2PlanLib.sol:47-82`) appends the authored
  delegate and extras as `Unsafe` deployments at `generateRandomAddress(info)` (:61-69, :100-112)
  and reverts on a deployment or a composer without a delegate (:73-75) and on a delegate without
  a composer (:76-78).
* `_requireL2StateKept` (`CTMTransition.sol:129-143`) compares the tables member by member
  (`_l2TableChanged`, :173-185, a row past the shorter table counting as empty), the proxy shell
  and the genesis blob by keccak, and the genesis parameters by value.

The bootstrap edge has no departing release: `RegistryBootstrapMigration._buildL2Plan`
(`upgrades/registry/bootstrap/RegistryBootstrapMigration.sol:229-241`) installs the whole table
through `deriveL2DeploymentsFromTable`, and its constructor builds that plan (:83).

`CTMRelease`'s constructor checks the table (`upgrades/registry/objects/CTMRelease.sol:63-68`):
its length is the member count, the `L2WrappedBaseToken` row is empty (:185-189), every nonempty
row and the shell are `BYTECODE_INFO_LENGTH` bytes (:195-212), and nine fields of the genesis blob
equal their members' `(row, shell)` descriptors by keccak (:147-178).

## Modelling choices

* **A revert is `none`.** The loops are transcribed by their results: a revert condition, and
  the list they build when they do not revert. Which error a revert carries is not modelled.
* **Bytes are `List UInt8`; keccak is any function `kec : Bytes → H` into a type with
  decidable equality.** No property of `kec` is assumed. A result that needs two keccak-equal
  values to be equal concludes "equal, or these two named values collide" (`KeccakClash`).
* **A release is its L2 getters** (`ReleaseL2`): `l2BytecodeInfos()`, `l2SystemProxyBytecodeInfo()`,
  `fixedForceDeploymentsData()`, `genesisParams()`, and the nine bytecode fields its blob decodes
  to. Releases are write-once (`CTMRelease.sol:31-35`). Its version is passed separately.
* **Descriptors are kept as pairs.** A system-proxy deployment's `abi.encode(row, shell)` is the
  pair `(row, shell)` (`ProxyDeployment`): `L2GenesisForceDeploymentsHelper.upgradeSystemContractProxy`
  decodes it back and checks the encoding is canonical
  (`l2-upgrades/L2GenesisForceDeploymentsHelper.sol:113-122`). Relating the two is `SOL-ABI`.
* **Omitted reject-only checks.** The constructor's zero-address checks (`CTMTransition.sol:54-60`;
  the model takes getter values, not addresses), both releases' `validate()` (:74-75; code
  existence and the L1 facet set), `L2PlanLib.build`'s factory-dependency cap (`L2PlanLib.sol:79-81`)
  and the decoding inside `_factoryDepHashes` (:118-167). These only remove successful
  constructions, so every result about all successful constructions holds a fortiori. Witnesses
  use plans of at most four deployments (at most eight factory dependencies against the cap of
  64) and 96-byte descriptors whose `uint32` word is in range.
* **Versions are `ℕ`**, unpacked as `SemVer.unpackSemVer` does after `SafeCast.toUint96`
  (`common/libraries/SemVer.sol:25-31`): `minorOf v = (v >> 32) mod 2^32`,
  `majorOf v = (v >> 64) mod 2^32`.
* **Before the OpenZeppelin L-01 fix.** `ctmTransitionL2PreFix` is the constructor at the parent
  commit `4e073f09b` of the fix `9775be946`, where `_requireL2StateKept` compared
  `keccak256(abi.encode(table))` (`CTMTransition.sol:129-130` at `4e073f09b`). Nothing else on
  this path differs between `4e073f09b` and `b17415d20`
  (`TransitionDerivationLib.sol`, `L2PlanLib.sol`, `VersionEdgeLib.sol` are unchanged; the
  `L2InventoryLib.sol` change is a comment). `abi.encode` of a `bytes[]` is a parameter `encT`.
-/

namespace Contracts.ChainTypeManager.L2Tables

/-! ## Values -/

/-- A `bytes` value. Emptiness (`.length == 0`) is `= []`. -/
abbrev Bytes := List UInt8

/-- An L2 address; only equality matters. -/
abbrev L2Addr := ℕ

/-- Two distinct byte strings with the same hash. -/
def KeccakClash {H : Type} (kec : Bytes → H) (x y : Bytes) : Prop :=
  x ≠ y ∧ kec x = kec y

/-- `BYTECODE_INFO_LENGTH` (`common/libraries/ZKSyncOSBytecodeInfo.sol:12`). -/
def bytecodeInfoLength : ℕ := 96

/-- `L2_ECOSYSTEM_CONTRACT_COUNT = uint256(type(L2EcosystemContract).max) + 1`
(`upgrades/registry/libraries/ContractIdentifiers.sol:135`): the enum has 27 members
(:11-48). -/
def memberCount : ℕ := 27

/-- `L2InventoryLib.fixedAddress(L2EcosystemContract(i))`
(`upgrades/registry/libraries/L2InventoryLib.sol:48-113`). `none` is a revert:
`RegistryMemberHasNoFixedAddress` (`L2InventoryLib.sol:112`) for `BeaconProxy`,
`L2DefaultUpgrade`, `BridgedStandardERC20`, `DiamondProxy`, `ProxyAdmin` and
`TransparentUpgradeableProxy` (members 14-19), and the enum conversion's panic for `i ≥ 27`.
The values are the constants of `common/l2-helpers/L2ContractAddresses.sol`
(`SYSTEM_CONTRACTS_OFFSET = 0x8000` at its line 6, `BUILT_IN_CONTRACTS_OFFSET = 0x10000` at its
line 12); the `:n` in the comments below are lines of that file. -/
def fixedAddress : ℕ → Option L2Addr
  | 0 => some 0x10002   -- L2Bridgehub → L2_BRIDGEHUB_ADDR (:81)
  | 1 => some 0x10003   -- L2AssetRouter → L2_ASSET_ROUTER_ADDR (:84)
  | 2 => some 0x10004   -- L2NativeTokenVault → L2_NATIVE_TOKEN_VAULT_ADDR (:89)
  | 3 => some 0x10005   -- L2MessageRoot → L2_MESSAGE_ROOT_ADDR (:92)
  | 4 => some 0x1000b   -- UpgradeableBeaconDeployer → L2_NTV_BEACON_DEPLOYER_ADDR (:112)
  | 5 => some 0x10011   -- BaseTokenHolder → L2_BASE_TOKEN_HOLDER_ADDR (:133)
  | 6 => some 0x1000a   -- L2ChainAssetHandler → L2_CHAIN_ASSET_HANDLER_ADDR (:107)
  | 7 => some 0x1000d   -- InteropCenter → L2_INTEROP_CENTER_ADDR (:118)
  | 8 => some 0x10015   -- InteropAttributeParser → L2_INTEROP_ATTRIBUTE_PARSER_ADDR (:147)
  | 9 => some 0x1000e   -- L2InteropHandler → L2_INTEROP_HANDLER_ADDR (:121)
  | 10 => some 0x1000f  -- L2AssetTracker → L2_ASSET_TRACKER_ADDR (:124)
  | 11 => some 0x10007  -- L2WrappedBaseToken → L2_WRAPPED_BASE_TOKEN_IMPL_ADDR (:98)
  | 12 => some 0x10009  -- L2MessageVerification → L2_MESSAGE_VERIFICATION_ADDR (:104)
  | 13 => some 0x10008  -- L2InteropRootStorage → L2_INTEROP_ROOT_STORAGE_ADDR (:101)
  | 20 => some 0x10012  -- L2InteropCommitmentTree → L2_INTEROP_COMMITMENT_TREE_ADDR (:136)
  | 21 => some 0x10014  -- AtomicFlowManager → L2_ATOMIC_FLOW_MANAGER_ADDR (:142)
  | 22 => some 0x800a   -- L2BaseToken → L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR (:59)
  | 23 => some 0x8008   -- L1Messenger → L2_TO_L1_MESSENGER_SYSTEM_CONTRACT_ADDR (:56)
  | 24 => some 0x800b   -- SystemContext → L2_SYSTEM_CONTEXT_SYSTEM_CONTRACT_ADDR (:62)
  | 25 => some 0x10010  -- RemovedGWAssetTracker → L2_REMOVED_GW_ASSET_TRACKER_ADDR (:130)
  | 26 => some 0x800f   -- L2ComplexUpgrader → L2_COMPLEX_UPGRADER_ADDR (:65)
  | _ => none

/-- Row `i` of a table, empty past its end. This is how both comparisons read a shorter
table: `changedL2Rows` treats `i >= fromLength` as "no row to compare" (`TransitionDerivationLib.sol:106-109`)
and `_l2TableChanged` hashes it as `keccak256("")` (`CTMTransition.sol:178-179`). -/
def rowAt (t : List Bytes) (i : ℕ) : Bytes := t.getD i []

/-! ## `TransitionDerivationLib.changedL2Rows` (`:110-134`) -/

/-- The revert conditions:

    if (length < fromLength) { revert L2BytecodeTableShrunk(fromLength, length); }        // :118-120
    if (_newTable[i].length == 0) {
        if (i < fromLength && _fromTable[i].length != 0) { revert L2BytecodeRowRemoved(i); }  // :125-127
        continue; }
-/
def changedL2RowsReverts (fromT newT : List Bytes) : Bool :=
  decide (newT.length < fromT.length) ||
    (List.range newT.length).any
      (fun i => decide (rowAt newT i = [] ∧ i < fromT.length ∧ rowAt fromT i ≠ []))

/-- Row `i` of the new table is kept in `changed`:

    if (i >= fromLength || keccak256(_fromTable[i]) != keccak256(_newTable[i])) { changed[i] = _newTable[i]; }  // :130-132

for a nonempty `_newTable[i]` (an empty one is skipped at :123-129). "New or changed by keccak". -/
abbrev RowChanged {H : Type} (kec : Bytes → H) (fromT newT : List Bytes) (i : ℕ) : Prop :=
  rowAt newT i ≠ [] ∧ (fromT.length ≤ i ∨ kec (rowAt fromT i) ≠ kec (rowAt newT i))

/-- `changedL2Rows(_fromTable, _newTable)`: `none` is a revert. Otherwise a table of the new
table's length holding the new or changed rows, every other slot empty. -/
def changedL2Rows {H : Type} [DecidableEq H] (kec : Bytes → H) (fromT newT : List Bytes) :
    Option (List Bytes) :=
  if changedL2RowsReverts fromT newT then none
  else some ((List.range newT.length).map
    (fun i => if RowChanged kec fromT newT i then rowAt newT i else []))

/-! ## `TransitionDerivationLib.deriveL2DeploymentsFromTable` (`:145-169`) -/

/-- One `ZKsyncOSSystemProxyUpgrade` (`:162-166`): at `newAddress`, the descriptor
`abi.encode(_l2BytecodeInfos[i], _l2SystemProxyBytecodeInfo)`, kept as the pair. -/
structure ProxyDeployment where
  /-- `newAddress = L2InventoryLib.fixedAddress(L2EcosystemContract(i))`. -/
  addr : L2Addr
  /-- The implementation's bytecode info: the table row. -/
  impl : Bytes
  /-- The system-proxy shell's bytecode info. -/
  shell : Bytes
deriving DecidableEq

/-- It reverts iff some nonempty row's member has no fixed address (`:165`). -/
def deriveReverts (rows : List Bytes) : Bool :=
  (List.range rows.length).any (fun i => decide (rowAt rows i ≠ [] ∧ fixedAddress i = none))

/-- Otherwise: one deployment per nonempty row, in member order (`:158-168`). -/
def deriveOut (rows : List Bytes) (shell : Bytes) : List ProxyDeployment :=
  (List.range rows.length).filterMap
    (fun i => if rowAt rows i = [] then none
      else (fixedAddress i).map (fun a => ⟨a, rowAt rows i, shell⟩))

/-- `deriveL2DeploymentsFromTable(_l2BytecodeInfos, _l2SystemProxyBytecodeInfo)`. -/
def deriveL2DeploymentsFromTable (rows : List Bytes) (shell : Bytes) :
    Option (List ProxyDeployment) :=
  if deriveReverts rows then none else some (deriveOut rows shell)

/-! ## `L2PlanLib.build` (`:47-82`) -/

/-- An entry of `L2UpgradePlan.deployments`. -/
inductive Deployment
  /-- A table-derived `ZKsyncOSSystemProxyUpgrade`. -/
  | proxy (d : ProxyDeployment)
  /-- An authored `ZKsyncOSUnsafeForceDeployment` (`L2PlanLib.sol:100-112`): the bytecode info
  at its derived address. -/
  | unsafeForce (addr : L2Addr) (info : Bytes)
deriving DecidableEq

/-- The system-proxy part of a deployment. -/
def Deployment.proxyPart : Deployment → Option ProxyDeployment
  | .proxy d => some d
  | .unsafeForce _ _ => none

/-- `L2UpgradePlan` without `factoryDepHashes` (see the omitted checks). -/
structure L2Plan where
  /-- `deployments`: the derived ones first, then the delegate, then the extras. -/
  deployments : List Deployment
  /-- `delegateTo`: the delegate's derived address, zero without one. -/
  delegateTo : L2Addr
  /-- `delegateComposer`. -/
  composer : ℕ
deriving DecidableEq

/-- The manifest's authored L2 input (`AuthoredL2Plan`). -/
structure AuthoredL2 where
  /-- `delegateBytecodeInfo`; empty means no delegate. -/
  delegate : Bytes
  /-- `extraBytecodeInfos`. -/
  extras : List Bytes
  /-- `delegateComposer`; zero means none. -/
  composer : ℕ
deriving DecidableEq

/-- `L2PlanLib.build(_derived, _authored)` (the `:n` below are lines of `L2PlanLib.sol`), with
`rnd` standing for `L2GenesisForceDeploymentsHelper.generateRandomAddress`
(`l2-upgrades/L2GenesisForceDeploymentsHelper.sol:109-111`), which `_unsafeDeployment` calls:

    bool hasDelegate = _authored.delegateBytecodeInfo.length != 0;                              // :51
    ... deployments = _derived ++ [delegate] ++ extras, each authored one `_unsafeDeployment`    // :54-69
    if (_bytecodeInfo.length != BYTECODE_INFO_LENGTH) { revert L2BytecodeInfoLength(...); }      // :103-105
    if (!hasDelegate && (plan.deployments.length != 0 || plan.delegateComposer != address(0))) {
        revert L2PlanNeedsDelegate(); }                                                          // :73-75
    if (hasDelegate && plan.delegateComposer == address(0)) { revert L2PlanDelegateNeedsComposer(); } // :76-78
-/
def buildPlan (rnd : Bytes → L2Addr) (derived : List ProxyDeployment) (a : AuthoredL2) :
    Option L2Plan :=
  let hasDelegate : Prop := a.delegate ≠ []
  let deps : List Deployment :=
    derived.map Deployment.proxy ++
      (if hasDelegate then [Deployment.unsafeForce (rnd a.delegate) a.delegate] else []) ++
      a.extras.map (fun x => Deployment.unsafeForce (rnd x) x)
  if hasDelegate ∧ a.delegate.length ≠ bytecodeInfoLength then none
  else if ∃ x ∈ a.extras, x.length ≠ bytecodeInfoLength then none
  else if ¬ hasDelegate ∧ (deps ≠ [] ∨ a.composer ≠ 0) then none
  else if hasDelegate ∧ a.composer = 0 then none
  else some ⟨deps, if hasDelegate then rnd a.delegate else 0, a.composer⟩

/-- `hasL2Side = derivedPlan.deployments.length != 0` (`CTMTransition.sol:90`). -/
def hasL2Side (p : L2Plan) : Bool := !p.deployments.isEmpty

/-! ## `VersionEdgeLib.requireValidEdge` (`upgrades/registry/libraries/VersionEdgeLib.sol:35-91`) -/

/-- The minor component `SemVer.unpackSemVer` reads (`common/libraries/SemVer.sol:29`). -/
def minorOf (v : ℕ) : ℕ := v / 2 ^ 32 % 2 ^ 32

/-- The major component (`SemVer.sol:30`). -/
def majorOf (v : ℕ) : ℕ := v / 2 ^ 64 % 2 ^ 32

/-- `requireValidEdge` returns:

    if (_newVersion <= _oldVersion) { revert ProtocolVersionTooSmall(...); }                 // :44-46
    if (_oldVersionDeadline == 0) { revert TransitionDeadlineZero(); }                       // :55-57
    if (_oldVersionDeadline < _upgradeTimestamp) { revert TransitionDeadlineBeforeUpgrade(...); } // :60-62
    ... SafeCast.toUint96 of both versions ...                                               // :66-68
    if (oldMajor != 0) { revert ...; }  if (newMajor != 0) { revert ...; }                   // :72-77
    uint256 minorDelta = newMinor - oldMinor;
    if (minorDelta > MAX_ALLOWED_MINOR_VERSION_DELTA) { revert ...; }                         // :80-83
    if (oldMinor == newMinor && _hasL2Side) { revert PatchCannotCarryL2Upgrade(); }          // :88-90

`MAX_ALLOWED_MINOR_VERSION_DELTA = 100` (`common/Config.sol:73`). The subtraction cannot
underflow once the earlier checks pass, so `ℕ` subtraction is exact here. -/
def ValidEdge (old new deadline ts : ℕ) (l2Side : Bool) : Prop :=
  old < new ∧ deadline ≠ 0 ∧ ts ≤ deadline ∧ old < 2 ^ 96 ∧ new < 2 ^ 96 ∧
    majorOf old = 0 ∧ majorOf new = 0 ∧ minorOf new - minorOf old ≤ 100 ∧
    ¬ (minorOf old = minorOf new ∧ l2Side = true)

instance (old new deadline ts : ℕ) (l2Side : Bool) :
    Decidable (ValidEdge old new deadline ts l2Side) := by
  unfold ValidEdge; infer_instance

/-! ## `CTMTransition._requireL2StateKept` (`:129-143`) -/

/-- `GenesisParams`: `genesisParams()`'s `(genesisUpgrade, genesisBatchHash,
genesisIndexRepeatedStorageChanges)` (`CTMRelease.sol:112-115`). -/
structure GenesisParams where
  /-- The genesis upgrade's address. -/
  genesisUpgrade : ℕ
  /-- `genesisBatchHash`. -/
  batchHash : ℕ
  /-- `genesisIndexRepeatedStorageChanges`. -/
  index : ℕ
deriving DecidableEq

/-- A release's L2 getters. -/
structure ReleaseL2 where
  /-- `l2BytecodeInfos()`: the table, indexed by `L2EcosystemContract`. -/
  table : List Bytes
  /-- `l2SystemProxyBytecodeInfo()`: the one proxy shell. -/
  shell : Bytes
  /-- `fixedForceDeploymentsData()`: the genesis blob. -/
  blob : Bytes
  /-- `genesisParams()`. -/
  genesis : GenesisParams
  /-- The bytecode fields `abi.decode(blob, (FixedForceDeploymentsData))` yields, by member
  (`CTMRelease.sol:148-151`); read only by `ReleaseL2Accepted`. -/
  blobField : ℕ → Bytes

/-- Row `i`'s hash as `_l2TableChanged` computes it (`:178-179`): `keccak256(table[i])` inside
the table, `keccak256("")` past it. -/
def tableRowHash {H : Type} (kec : Bytes → H) (t : List Bytes) (i : ℕ) : H :=
  if i < t.length then kec (rowAt t i) else kec []

/-- `_l2TableChanged(_fromTable, _newTable)` (`:173-185`): some member's row hash differs, over
the longer table. `releaseDiff()` reports the same value as `diff.l2BytecodeInfos` (:159). -/
def l2TableChanged {H : Type} [DecidableEq H] (kec : Bytes → H) (fromT newT : List Bytes) : Bool :=
  (List.range (max fromT.length newT.length)).any
    (fun i => decide (tableRowHash kec fromT i ≠ tableRowHash kec newT i))

/-- `_requireL2StateKept(from, new)` returns:

    if (_l2TableChanged(...) || keccak256(from.shell) != keccak256(new.shell)
        || keccak256(from.blob) != keccak256(new.blob)) { revert L1OnlyEdgeChangesL2State(); } // :130-136
    if (fromGenesisUpgrade != newGenesisUpgrade || fromBatchHash != newBatchHash
        || fromIndex != newIndex) { revert L1OnlyEdgeChangesL2State(); }                     // :138-142
-/
def L2StateKept {H : Type} [DecidableEq H] (kec : Bytes → H) (Rf Rn : ReleaseL2) : Prop :=
  l2TableChanged kec Rf.table Rn.table = false ∧ kec Rf.shell = kec Rn.shell ∧
    kec Rf.blob = kec Rn.blob ∧ Rf.genesis = Rn.genesis

instance {H : Type} [DecidableEq H] (kec : Bytes → H) (Rf Rn : ReleaseL2) :
    Decidable (L2StateKept kec Rf Rn) := by
  unfold L2StateKept; infer_instance

/-- The pre-fix comparison at `4e073f09b` (`CTMTransition.sol:128-135` there), with `encT`
standing for `abi.encode` of a `bytes[]`:

    if (keccak256(abi.encode(_fromRelease.l2BytecodeInfos())) !=
            keccak256(abi.encode(_newRelease.l2BytecodeInfos())) || ...) { revert L1OnlyEdgeChangesL2State(); }
-/
def L2StateKeptPreFix {H : Type} [DecidableEq H] (kec : Bytes → H) (encT : List Bytes → Bytes)
    (Rf Rn : ReleaseL2) : Prop :=
  kec (encT Rf.table) = kec (encT Rn.table) ∧ kec Rf.shell = kec Rn.shell ∧
    kec Rf.blob = kec Rn.blob ∧ Rf.genesis = Rn.genesis

instance {H : Type} [DecidableEq H] (kec : Bytes → H) (encT : List Bytes → Bytes)
    (Rf Rn : ReleaseL2) : Decidable (L2StateKeptPreFix kec encT Rf Rn) := by
  unfold L2StateKeptPreFix; infer_instance

/-! ## The constructor's L2 part -/

/-- The manifest fields the L2 part reads: `oldProtocolVersionDeadline`, `upgradeTimestamp` and
the authored `l2Plan`. -/
structure EdgeInput where
  /-- `oldProtocolVersionDeadline`. -/
  deadline : ℕ
  /-- `upgradeTimestamp`. -/
  timestamp : ℕ
  /-- `l2Plan`, the authored part. -/
  authored : AuthoredL2

/-- The plan `deriveL2Deployments` and `L2PlanLib.build` produce, before the edge checks. -/
def derivedPlan {H : Type} [DecidableEq H] (kec : Bytes → H) (rnd : Bytes → L2Addr)
    (Rf Rn : ReleaseL2) (a : AuthoredL2) : Option L2Plan :=
  (changedL2Rows kec Rf.table Rn.table).bind fun changed =>
    (deriveL2DeploymentsFromTable changed Rn.shell).bind fun derived =>
      buildPlan rnd derived a

/-- **`new CTMTransition(manifest)`, its L2 part** (`CTMTransition.sol:50-122`), for departing
release `Rf` at version `vFrom` and target `Rn` at `vNew` (the versions are the releases' own,
`:61-64`): the stored plan, or `none` for a revert. -/
def ctmTransitionL2 {H : Type} [DecidableEq H] (kec : Bytes → H) (rnd : Bytes → L2Addr)
    (vFrom vNew : ℕ) (Rf Rn : ReleaseL2) (e : EdgeInput) : Option L2Plan :=
  (derivedPlan kec rnd Rf Rn e.authored).bind fun p =>
    if ValidEdge vFrom vNew e.deadline e.timestamp (hasL2Side p) ∧
        (hasL2Side p = true ∨ L2StateKept kec Rf Rn) then some p else none

/-- The same constructor at `4e073f09b`, before the OZ L-01 fix: identical except for the table
comparison of `_requireL2StateKept`. -/
def ctmTransitionL2PreFix {H : Type} [DecidableEq H] (kec : Bytes → H) (encT : List Bytes → Bytes)
    (rnd : Bytes → L2Addr) (vFrom vNew : ℕ) (Rf Rn : ReleaseL2) (e : EdgeInput) : Option L2Plan :=
  (derivedPlan kec rnd Rf Rn e.authored).bind fun p =>
    if ValidEdge vFrom vNew e.deadline e.timestamp (hasL2Side p) ∧
        (hasL2Side p = true ∨ L2StateKeptPreFix kec encT Rf Rn) then some p else none

/-- The bootstrap migration's L2 plan (`RegistryBootstrapMigration.sol:229-241`), which its
constructor builds (:83): the whole table of the genesis release `R`, then the authored part. -/
def bootstrapPlanL2 (rnd : Bytes → L2Addr) (R : ReleaseL2) (a : AuthoredL2) : Option L2Plan :=
  (deriveL2DeploymentsFromTable R.table R.shell).bind fun derived => buildPlan rnd derived a

/-! ## `CTMRelease`'s table checks -/

/-- The nine members whose blob field `_requireForceDeploymentsMatchTable` compares
(`CTMRelease.sol:154-162`): `L2Bridgehub`, `L2AssetRouter`, `L2NativeTokenVault`,
`L2MessageRoot`, `L2ChainAssetHandler`, `InteropCenter`, `L2InteropHandler`, `L2AssetTracker`,
`BaseTokenHolder`. -/
def blobMembers : List ℕ := [0, 1, 2, 3, 6, 7, 9, 10, 5]

/-- The L2 checks of `new CTMRelease(manifest)` (`CTMRelease.sol:63-68`), with `enc` standing for
`abi.encode(row, shell)`:

    if (_manifest.l2BytecodeInfos.length != L2_ECOSYSTEM_CONTRACT_COUNT) { revert ...; }       // :63-65
    _requireNoWrappedBaseTokenRow(...)      // row 11 empty                                    // :185-189
    _requireCanonicalBytecodeInfos(...)     // shell and nonempty rows are 96 bytes             // :195-212
    _requireForceDeploymentsMatchTable(...) // keccak(field) == keccak(row empty ? "" : enc(row, shell)) // :147-178

The constructor's other checks (zero addresses, the genesis batch hash, the facet rows,
`CTMRelease.sol:36-58`) read fields this model does not have. -/
def ReleaseL2Accepted {H : Type} (kec : Bytes → H) (enc : Bytes → Bytes → Bytes) (R : ReleaseL2) :
    Prop :=
  R.table.length = memberCount ∧ rowAt R.table 11 = [] ∧
    (R.shell ≠ [] → R.shell.length = bytecodeInfoLength) ∧
    (∀ i < R.table.length, rowAt R.table i ≠ [] → (rowAt R.table i).length = bytecodeInfoLength) ∧
    ∀ m ∈ blobMembers,
      kec (R.blobField m) = kec (if rowAt R.table m = [] then [] else enc (rowAt R.table m) R.shell)

/-! ## Witness data

Bytecode infos are 96-byte `(bytes32, uint32, bytes32)` descriptors whose `uint32` word is in
range, so the decoding `_factoryDepHashes` performs (omitted in the model) accepts them. Every
plan built from these has at most four deployments. Versions are packed semver values
`minor << 32`, so `2 ^ 32 → 2 * 2 ^ 32` is a minor edge and `2 * 2 ^ 32 → 2 * 2 ^ 32 + 1` a
patch edge. The raw blob `[7]` stands in for the ABI encoding of a release's blob fields: the
model reads only the decoded fields (`blobField`) and compares raw blobs by hash. -/

/-- A 96-byte descriptor whose three words are `k` repeated, `k`, and `k` repeated. -/
def wDesc (k : UInt8) : Bytes :=
  List.replicate 32 k ++ List.replicate 31 0 ++ [k] ++ List.replicate 32 k

/-- The witnesses' `generateRandomAddress`: a constant. -/
def wRnd : Bytes → L2Addr := fun _ => 0x1234

/-- Genesis parameters shared by the witness releases. -/
def wGenesis : GenesisParams := ⟨1, 2, 0⟩

/-- A witness release: the given table, shell `wDesc 50`, a fixed blob. -/
def wRel (t : List Bytes) : ReleaseL2 := ⟨t, wDesc 50, [7], wGenesis, fun _ => []⟩

/-- A minor edge's input: a delegate and a composer. -/
def wMinorEdge : EdgeInput := ⟨10, 5, ⟨wDesc 90, [], 77⟩⟩

/-- An L1-only edge's input: no authored L2 part. -/
def wL1OnlyEdge : EdgeInput := ⟨10, 5, ⟨[], [], 0⟩⟩

/-- `abi.encode(row, shell)` in the frozen-row witness: concatenation. -/
def wEnc : Bytes → Bytes → Bytes := fun r s => r ++ s

/-- A 27-row table with rows 0 and 14 set, the others empty. -/
def wTable27 (r0 r14 : Bytes) : List Bytes :=
  ((List.replicate 27 ([] : Bytes)).set 0 r0).set 14 r14

/-- A 27-row release whose nine blob fields are its rows' descriptors. -/
def wRel27 (r0 r14 : Bytes) : ReleaseL2 :=
  ⟨wTable27 r0 r14, wDesc 50, [7], wGenesis,
    fun m => if rowAt (wTable27 r0 r14) m = [] then [] else wEnc (rowAt (wTable27 r0 r14) m) (wDesc 50)⟩

/-- A hash under which `wDesc 7` hashes like the empty row; the identity elsewhere. -/
def wClashKec : Bytes → Bytes := fun b => if b = wDesc 7 then [] else b

end Contracts.ChainTypeManager.L2Tables
