import EraSpec.Contracts.ChainTypeManager.Specs.ChainRouting

/-!
# Model: the diamond writers on the chain-creation path — `DiamondInit` and `L1GenesisUpgrade`

Source: branch `feat/upgrade-simplification` of the zksync-era `contracts` repository at
commit `e561b9cc2` (2026-10-19), as for the rest of this folder. Paths are relative to
`l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.GenesisWriters` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.GenesisWriters`.

## Why this is modelled

`ChainRouting` takes chain creation as one step, `Step.genesis` (and `Step.migrateIn` for a
chain arriving where it has no diamond): a fresh diamond at the CTM's version that routes
exactly the CTM's current release. That step is a modelling choice. The routing is written by
code delegatecalled into the new diamond, `DiamondInit.initialize` and then (through the Admin
facet) `L1GenesisUpgrade.genesisUpgrade`, and the assumption register lists both as not
modelled (`MODEL-CTM-ROUTING`). This file transcribes that code over the diamond's own storage
(`Diamond.DiamondStorage` and the part of `ZKChainStorage` the path reads), so that the step
becomes a theorem.

## The creation path

`ChainTypeManager.createNewChain(_chainId, _admin)` (`state-transition/ChainTypeManager.sol:708-716`):

    zkChainAddress = _deployNewChain(_chainId, _admin);                    // :709
    IAdmin(zkChainAddress).genesisUpgrade();                               // :712
    IMigrator(zkChainAddress).pauseDepositsBeforeInitiatingMigration();    // :715

1. **Deployment.** `_deployNewChain` (:679-697) refuses a registered id (:680-683) and runs
   `new DiamondProxy{salt: bytes32(0)}(block.chainid, diamondCut)` (:693) with

        facetCuts: new Diamond.FacetCut[](0),                                // :687
        initAddress: ICTMRelease(currentRelease).diamondInit(),              // :685, :688
        initCalldata: abi.encodeCall(IDiamondInit.initialize, (_chainId, _admin)) // :689

   The proxy's constructor is `Diamond.diamondCut(_diamondCut)` (`state-transition/chain-deps/DiamondProxy.sol:16-21`):
   no facet cut, then the init delegatecall (`state-transition/libraries/Diamond.sol:135, 310-340`)
   into `DiamondInit.initialize` (`state-transition/chain-deps/DiamondInit.sol:52-150`), whose
   diamond write is

        address currentRelease = ctm.currentRelease();                           // :77
        Diamond.FacetCut[] memory facetCuts = ReleaseFacetReader.newChainInstallations(release); // :82
        if (facetCuts.length != 0) { Diamond.diamondCut({facetCuts, address(0), ""}); }   // :83-87

   and `newChainInstallations` (`upgrades/registry/libraries/ReleaseFacetReader.sol:14-26`) is
   one `Add` cut per `genesisFacets()` row, with the facet's own `selectors()`. DiamondInit also
   writes `s.chainTypeManager = msg.sender` (:91, the CTM) and
   `s.protocolVersion = ctm.protocolVersion()` (:58, :110).
2. **Genesis upgrade.** `genesisUpgrade()` reaches the Admin facet through the proxy's
   `fallback` (`DiamondProxy.sol:25-60`). `Admin.genesisUpgrade`
   (`state-transition/chain-deps/facets/Admin.sol:566-578`):

        address l1GenesisUpgrade = IChainTypeManager(s.chainTypeManager).l1GenesisUpgrade(); // :569
        Diamond.FacetCut[] memory emptyArray;                                                // :570
        ... DiamondCutData({facetCuts: emptyArray, initAddress: l1GenesisUpgrade,
                            initCalldata: abi.encodeCall(IL1GenesisUpgrade.genesisUpgrade, ())}) // :571-575
        _executeDiamondCut(cutData);                                                          // :577

   where `l1GenesisUpgrade()` is the first field of `currentRelease.genesisParams()`
   (`ChainTypeManager.sol:327-330`). The init is `L1GenesisUpgrade.genesisUpgrade`
   (`upgrades/L1GenesisUpgrade.sol:31-53`):

        uint256 protocolVersion = s.protocolVersion;                               // :32
        L2CanonicalTransaction memory l2ProtocolUpgradeTx = _genesisUpgradeTx(...); // :35-40, a `view` (:77-104)
        _upgrade({_newProtocolVersion: protocolVersion, _upgradeTimestamp: 0,
                  _verifier: address(0), _l2ProtocolUpgradeTx: l2ProtocolUpgradeTx}); // :42-47

   `BaseZkSyncUpgrade._upgrade` (`upgrades/BaseZkSyncUpgrade.sol:66-102`) has no timestamp gate
   at `0` (:76-78), skips the verifier at `address(0)` (:91-93), runs the genesis
   `_setNewProtocolVersion` (`upgrades/BaseZkSyncUpgradeGenesis.sol:25-82`), which writes the
   **same** version back (:80), and `_setL2SystemContractUpgrade` (`BaseZkSyncUpgrade.sol:148-188`),
   which writes `s.l2SystemContractsUpgradeTxHash` (:185). Nothing on this path calls
   `Diamond.diamondCut` or touches `Diamond.DiamondStorage`: the helpers it calls are `pure`
   or `view`.
3. **Deposit pause.** `Migrator.pauseDepositsBeforeInitiatingMigration`
   (`state-transition/chain-deps/facets/Migrator.sol:105-129`) writes `s.pausedDepositsTimestamp` (:121).

Migration in, `ChainTypeManager.forwardedBridgeMint` (:751-763), checks the incoming version
(:759-761) and deploys through the same `_deployNewChain` (:762). The chain asset handler then
calls the new diamond's `Migrator.forwardedBridgeMint(chainData, false)`
(`core/chain-asset-handler/ChainAssetHandlerBase.sol:399, 417`; `Migrator.sol:213-305`). There
is no genesis upgrade on that path.

## Modelling choices

* **Storage.** A chain's storage is three disjoint regions: `Diamond.DiamondStorage` at
  `DIAMOND_STORAGE_POSITION` (`Diamond.sol:33-34, 62-67`), the reentrancy lock at
  `LOCK_FLAG_ADDRESS` (`common/ReentrancyGuard.sol:31`), and `ZKChainStorage s` from slot 0
  (`state-transition/chain-deps/facets/ZKChainBase.sol:42`). That the three do not overlap is
  a storage-layout fact, assumed (the two fixed positions are `keccak256(...) - 1`).
  `DiamondStorage` is transcribed whole. Of `ZKChainStorage`, only the fields the path reads
  or that the routing model uses are kept (`AppStorage`). The other fields DiamondInit writes
  (fee parameters, priority tree, validators, base token, batch zero, ...) are read by nothing
  modelled here.
* **Mappings are total.** An unset `selectorToFacet` entry is the zero struct, and a selector
  is routed iff its `facetAddress` is nonzero. That is the proxy's own test
  (`DiamondProxy.sol:35`) and the diamond library's (`Diamond.sol:158, 183, 209`).
  `DiamondStorage.routing` projects the storage onto `ChainRouting`'s `Routing`.
* **Code is a tag** (`Code`). The code on the creation path is transcribed: `DiamondInit`,
  `L1GenesisUpgrade`, and the two facet entry points the path calls (`Admin.genesisUpgrade`;
  `Migrator`'s `pauseDepositsBeforeInitiatingMigration` and `forwardedBridgeMint`). Any other
  code is `Code.other`, with an arbitrary effect on the storage it is delegatecalled into. A
  release names its members by address (`ICTMRelease.diamondInit()`, `genesisParams()`,
  `genesisFacets()`). That these addresses hold the code named here is what governance reviews
  (`upgrades/registry/objects/CTMRelease.sol:23-26`). In the properties it is the premise
  `GenuineRelease`, and it is load-bearing.
* **A delegatecall's success** is the init returning `DIAMOND_INIT_SUCCESS_RETURN_VALUE`
  (`Diamond.sol:318-338`). The genuine inits return it (`DiamondInit.sol:149`,
  `L1GenesisUpgrade.sol:52`). A codeless init address succeeds with empty return data, which
  fails the length check (:333-335). A function the code does not have reverts.
* **The CTM is `msg.sender`** of the proxy's constructor and of every call it makes into the
  diamond. Reads through `IChainTypeManager(s.chainTypeManager)` are reads of the CTM's state
  `c`. That is justified on this path: DiamondInit sets `s.chainTypeManager` to the CTM
  (`DiamondInit.sol:91`) and nothing later on the path writes it
  (`Properties.DiamondInitInstallsTheRelease`, `Properties.GenesisUpgradeWritesNoDiamondStorage`).
* **Checks that only reject are omitted**, as in the rest of this folder. They are: the
  callers (`onlyChainTypeManager`, `onlyAdminOrChainTypeManager`, `onlyChainAssetHandler`,
  `onlyL1`), the zero checks of DiamondInit (:55-57, :64-72, :96-106, :115-117, :123-125),
  `SafeCast.toUint16` overflow in the diamond library (:225, :238, :272, :301), the genesis
  version's major/minor checks (`BaseZkSyncUpgradeGenesis.sol:41-60`), the upgrade
  transaction's validation (`BaseZkSyncUpgrade.sol:158-181`, all `pure`),
  `canBeActivated` (`Migrator.sol:106-108`), and the commitment's consistency checks and the
  L1-only branch of `forwardedBridgeMint` (`Migrator.sol:217-219, 234-236, 247-283`). Omitting
  a rejecting check only adds executions, so every "a successful creation is a `Step`" result
  holds a fortiori. The exactness and enabledness results are about this model, which
  accepts at least what the code accepts.
* **Values that do not matter are inputs.** The genesis transaction's hash is a function
  `Env.genesisTxHash` of the release, chain id and version (its composition is a `view`,
  `L1GenesisUpgrade.sol:77-104`). The deposit-pause timestamp and the migration commitment's
  two upgrade fields are arguments of the calls (`ProxyCall`).
* **Freshness.** A newly deployed proxy's storage is all zero (`ChainState.fresh`). That
  `CREATE2` at salt `0` yields a fresh address is `VM-DEPLOY`.
-/

namespace Contracts.ChainTypeManager.GenesisWriters

/-! ## `Diamond.DiamondStorage` -/

/-- `Diamond.SelectorToFacet` (`state-transition/libraries/Diamond.sol:42-46`). -/
structure SelectorToFacet where
  facetAddress : Address
  selectorPosition : ℕ
  isFreezable : Bool
deriving DecidableEq

/-- The zero struct: an unset `selectorToFacet` entry, and what `delete` leaves (:279). -/
def SelectorToFacet.zero : SelectorToFacet := ⟨0, 0, false⟩

/-- `Diamond.FacetToSelectors` (`Diamond.sol:51-54`). -/
structure FacetToSelectors where
  selectors : List Selector
  facetPosition : ℕ
deriving DecidableEq

/-- An unset `facetToSelectors` entry. -/
def FacetToSelectors.zero : FacetToSelectors := ⟨[], 0⟩

/-- `Diamond.DiamondStorage` (`Diamond.sol:62-67`), at `DIAMOND_STORAGE_POSITION` (:33-34). -/
structure DiamondStorage where
  selectorToFacet : Selector → SelectorToFacet
  facetToSelectors : Address → FacetToSelectors
  facets : List Address
  isFrozen : Bool

/-- A newly deployed proxy's diamond storage: every slot zero. -/
def DiamondStorage.empty : DiamondStorage := ⟨fun _ => .zero, fun _ => .zero, [], false⟩

/-- The routing the proxy serves (`DiamondProxy.sol:32-35`): a selector is routed iff its
`facetAddress` is nonzero, to that facet with its freezability. This is `ChainRouting`'s
`Routing`. -/
def DiamondStorage.routing (ds : DiamondStorage) : Routing := fun x =>
  if (ds.selectorToFacet x).facetAddress = 0 then none
  else some ((ds.selectorToFacet x).facetAddress, (ds.selectorToFacet x).isFreezable)

/-! ## Facet cuts -/

/-- `Diamond.Action` (`Diamond.sol:93-97`). -/
inductive CutAction
  | add
  | replace
  | remove
deriving DecidableEq

/-- `Diamond.FacetCut` (`Diamond.sol:75-80`). -/
structure FacetCut where
  facet : Address
  action : CutAction
  isFreezable : Bool
  selectors : List Selector
deriving DecidableEq

/-- The routing a list of facet cuts describes, one entry per selector in cut order: what
`ChainRouting` calls a release's flattened rows. -/
def flattenCuts (cs : List FacetCut) : ReleaseRows :=
  cs.flatMap (fun c => c.selectors.map (fun x => (x, (c.facet, c.isFreezable))))

/-! ## The diamond library (`Diamond.sol:109-306`) -/

/-- `_saveFacetIfNew` (`Diamond.sol:219-228`): a facet with no selectors is appended to
`facets` and records its position. -/
def saveFacetIfNew (ds : DiamondStorage) (f : Address) : DiamondStorage :=
  if (ds.facetToSelectors f).selectors.length = 0 then
    { ds with
      facetToSelectors := upd ds.facetToSelectors f
        { ds.facetToSelectors f with facetPosition := ds.facets.length },
      facets := ds.facets ++ [f] }
  else ds

/-- The writes of `_addOneFunction` (`Diamond.sol:250-255`): route `x` to `f` at the end of
`f`'s selector list. -/
def pushSelector (ds : DiamondStorage) (f : Address) (x : Selector) (frz : Bool) :
    DiamondStorage :=
  { ds with
    selectorToFacet := upd ds.selectorToFacet x ⟨f, (ds.facetToSelectors f).selectors.length, frz⟩,
    facetToSelectors := upd ds.facetToSelectors f
      { ds.facetToSelectors f with selectors := (ds.facetToSelectors f).selectors ++ [x] } }

/-- `_addOneFunction` (`Diamond.sol:235-256`): if the facet already has selectors, the new one
must have the freezability of its first (:243-248). -/
def addOneFunction (ds : DiamondStorage) (f : Address) (x : Selector) (frz : Bool) :
    Option DiamondStorage :=
  match (ds.facetToSelectors f).selectors with
  | [] => some (pushSelector ds f x frz)
  | y :: _ =>
    if frz = (ds.selectorToFacet y).isFreezable then some (pushSelector ds f x frz) else none

/-- The selector loop of `_addFunctions` (`Diamond.sol:154-163`): a routed selector reverts
`FacetExists` (:157-160). -/
def addSelectors (f : Address) (frz : Bool) : DiamondStorage → List Selector → Option DiamondStorage
  | ds, [] => some ds
  | ds, x :: xs =>
    if (ds.selectorToFacet x).facetAddress = 0 then
      (addOneFunction ds f x frz).bind (fun ds' => addSelectors f frz ds' xs)
    else none

/-- `_addFunctions` (`Diamond.sol:141-164`): a facet without code reverts (:147-149); this
also refuses facet `0`, which has no code. -/
def addFunctions (hasCode : Address → Bool) (ds : DiamondStorage) (f : Address)
    (xs : List Selector) (frz : Bool) : Option DiamondStorage :=
  if hasCode f = true then addSelectors f frz (saveFacetIfNew ds f) xs else none

/-- `_removeFacet` (`Diamond.sol:289-306`): move the last facet into `f`'s position, then pop.
`facets.length - 1` is checked arithmetic, and the array accesses are bounds-checked. -/
def removeFacet (ds : DiamondStorage) (f : Address) : Option DiamondStorage :=
  let pos := (ds.facetToSelectors f).facetPosition
  if ds.facets.length = 0 then none
  else
    let last := ds.facets.length - 1
    let moved : Option DiamondStorage :=
      if pos = last then some ds
      else if pos < ds.facets.length then
        let lastFacet := ds.facets.getD last 0
        some { ds with
          facets := ds.facets.set pos lastFacet,
          facetToSelectors := upd ds.facetToSelectors lastFacet
            { ds.facetToSelectors lastFacet with facetPosition := pos } }
      else none
    moved.map (fun ds1 => { ds1 with facets := ds1.facets.dropLast })

/-- `_removeOneFunction` (`Diamond.sol:260-285`): move the facet's last selector into the
removed one's position, pop, delete the entry (:279), and drop the facet when it has no
selectors left (:282-284). `selectors.length - 1` is checked arithmetic, and the array
accesses are bounds-checked. -/
def removeOneFunction (ds : DiamondStorage) (f : Address) (x : Selector) :
    Option DiamondStorage :=
  let sels := (ds.facetToSelectors f).selectors
  let pos := (ds.selectorToFacet x).selectorPosition
  if sels.length = 0 then none
  else
    let last := sels.length - 1
    let moved : Option DiamondStorage :=
      if pos = last then some ds
      else if pos < sels.length then
        let lastSel := sels.getD last 0
        some { ds with
          facetToSelectors := upd ds.facetToSelectors f
            { ds.facetToSelectors f with selectors := sels.set pos lastSel },
          selectorToFacet := upd ds.selectorToFacet lastSel
            { ds.selectorToFacet lastSel with selectorPosition := pos } }
      else none
    moved.bind (fun ds1 =>
      let ds2 : DiamondStorage := { ds1 with
        facetToSelectors := upd ds1.facetToSelectors f
          { ds1.facetToSelectors f with selectors := (ds1.facetToSelectors f).selectors.dropLast },
        selectorToFacet := upd ds1.selectorToFacet x .zero }
      if last = 0 then removeFacet ds2 f else some ds2)

/-- The selector loop of `_removeFunctions` (`Diamond.sol:204-214`): an unrouted selector
reverts (:209-211). -/
def removeSelectors : DiamondStorage → List Selector → Option DiamondStorage
  | ds, [] => some ds
  | ds, x :: xs =>
    if (ds.selectorToFacet x).facetAddress = 0 then none
    else (removeOneFunction ds (ds.selectorToFacet x).facetAddress x).bind
      (fun ds' => removeSelectors ds' xs)

/-- `_removeFunctions` (`Diamond.sol:196-215`): the cut's facet must be zero (:199-202). -/
def removeFunctions (ds : DiamondStorage) (f : Address) (xs : List Selector) :
    Option DiamondStorage :=
  if f = 0 then removeSelectors ds xs else none

/-- The selector loop of `_replaceFunctions` (`Diamond.sol:178-191`). -/
def replaceSelectors (f : Address) (frz : Bool) : DiamondStorage → List Selector → Option DiamondStorage
  | ds, [] => some ds
  | ds, x :: xs =>
    if (ds.selectorToFacet x).facetAddress = 0 then none
    else ((removeOneFunction ds (ds.selectorToFacet x).facetAddress x).bind (fun ds1 =>
        addOneFunction (saveFacetIfNew ds1 f) f x frz)).bind (fun ds' => replaceSelectors f frz ds' xs)

/-- `_replaceFunctions` (`Diamond.sol:168-192`): a facet without code reverts (:174-176). -/
def replaceFunctions (hasCode : Address → Bool) (ds : DiamondStorage) (f : Address)
    (xs : List Selector) (frz : Bool) : Option DiamondStorage :=
  if hasCode f = true then replaceSelectors f frz ds xs else none

/-- One facet cut (`Diamond.sol:124-132`). -/
def applyFacetCut (hasCode : Address → Bool) (ds : DiamondStorage) (c : FacetCut) :
    Option DiamondStorage :=
  match c.action with
  | .add => addFunctions hasCode ds c.facet c.selectors c.isFreezable
  | .replace => replaceFunctions hasCode ds c.facet c.selectors c.isFreezable
  | .remove => removeFunctions ds c.facet c.selectors

/-- The facet-cut loop of `Diamond.diamondCut` (`Diamond.sol:113-133`): a cut with no
selectors reverts `NoFunctionsForDiamondCut` (:120-122). -/
def applyFacetCuts (hasCode : Address → Bool) : DiamondStorage → List FacetCut → Option DiamondStorage
  | ds, [] => some ds
  | ds, c :: cs =>
    if c.selectors = [] then none
    else (applyFacetCut hasCode ds c).bind (fun ds' => applyFacetCuts hasCode ds' cs)

/-! ## The chain's storage, calls and code -/

/-- The modelled fields of `ZKChainStorage` (`state-transition/chain-deps/ZKChainStorage.sol:74-272`). -/
structure AppStorage where
  /-- `protocolVersion` (:156). -/
  protocolVersion : ℕ
  /-- `chainId` (:181). -/
  chainId : ChainId
  /-- `chainTypeManager` (:187). -/
  chainTypeManager : Address
  /-- `admin` (:166). -/
  admin : Address
  /-- `verifier` (:89). -/
  verifier : Address
  /-- `settlementLayer` (:218); zero while the chain settles here. -/
  settlementLayer : Address
  /-- `l2SystemContractsUpgradeTxHash` (:159); zero is `bytes32(0)`. -/
  l2SystemContractsUpgradeTxHash : ℕ
  /-- `l2SystemContractsUpgradeBatchNumber` (:163). -/
  l2SystemContractsUpgradeBatchNumber : ℕ
  /-- `pausedDepositsTimestamp` (:255). -/
  pausedDepositsTimestamp : ℕ

/-- Every modelled field zero. -/
def AppStorage.zero : AppStorage := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- A chain diamond's storage. -/
structure ChainState where
  /-- The reentrancy lock at `LOCK_FLAG_ADDRESS` (`common/ReentrancyGuard.sol:31`). -/
  lock : ℕ
  /-- `Diamond.DiamondStorage`. -/
  diamond : DiamondStorage
  /-- The modelled part of `ZKChainStorage s`. -/
  app : AppStorage

/-- A newly deployed proxy: all storage zero. -/
def ChainState.fresh : ChainState := ⟨0, DiamondStorage.empty, AppStorage.zero⟩

/-- What `ChainRouting` sees of a chain: its version and its routing. -/
def ChainState.chain (st : ChainState) : Chain := ⟨st.app.protocolVersion, st.diamond.routing⟩

/-- The calldata of a cut's init delegatecall (`DiamondCutData.initCalldata`). -/
inductive InitCalldata
  /-- `""`. -/
  | empty
  /-- `abi.encodeCall(IDiamondInit.initialize, (_chainId, _admin))` (`ChainTypeManager.sol:689`). -/
  | initialize (chainId : ChainId) (admin : Address)
  /-- `abi.encodeCall(IL1GenesisUpgrade.genesisUpgrade, ())` (`Admin.sol:574`). -/
  | genesisUpgrade
deriving DecidableEq

/-- `Diamond.DiamondCutData` (`Diamond.sol:86-90`). -/
structure DiamondCutData where
  facetCuts : List FacetCut
  initAddress : Address
  initCalldata : InitCalldata

/-- The calls the creation paths make through the diamond proxy. -/
inductive ProxyCall
  /-- `IAdmin.genesisUpgrade()` (`ChainTypeManager.sol:712`). -/
  | genesisUpgrade
  /-- `IMigrator.pauseDepositsBeforeInitiatingMigration()` (`ChainTypeManager.sol:715`). `ts` is
  not calldata: it is the timestamp the call computes from `block.timestamp`
  (`Migrator.sol:110-120`). -/
  | pauseDeposits (ts : ℕ)
  /-- `IZKChain.forwardedBridgeMint(chainData, false)` (`ChainAssetHandlerBase.sol:417`), with
  the two fields of the decoded `ZKChainCommitment` the model keeps
  (`l2SystemContractsUpgradeTxHash`, `l2SystemContractsUpgradeBatchNumber`). -/
  | forwardedBridgeMint (txHash batch : ℕ)

/-- `genesisUpgrade()` (`Admin.sol:657-658`). -/
def selGenesisUpgrade : Selector := 0xd241f618

/-- `pauseDepositsBeforeInitiatingMigration()` (`Migrator.sol:390-391`). -/
def selPauseDeposits : Selector := 0x42249f9f

/-- `forwardedBridgeMint(bytes,bool)` (`Migrator.sol:386-387`). -/
def selForwardedBridgeMint : Selector := 0x3f42d5dd

/-- The selector the proxy dispatches a call on (`msg.sig`, `DiamondProxy.sol:32`). -/
def ProxyCall.selector : ProxyCall → Selector
  | .genesisUpgrade => selGenesisUpgrade
  | .pauseDeposits _ => selPauseDeposits
  | .forwardedBridgeMint _ _ => selForwardedBridgeMint

/-- The code at an address. -/
inductive Code
  /-- No code (`extcodesize == 0`). -/
  | none
  /-- `DiamondInit` (`state-transition/chain-deps/DiamondInit.sol`). -/
  | diamondInit
  /-- `L1GenesisUpgrade` (`upgrades/L1GenesisUpgrade.sol`). -/
  | l1GenesisUpgrade
  /-- `AdminFacet` (`state-transition/chain-deps/facets/Admin.sol`); of its entry points the
  creation path calls only `genesisUpgrade()`. -/
  | adminFacet
  /-- `MigratorFacet` (`state-transition/chain-deps/facets/Migrator.sol`); of its entry points
  the creation paths call only `pauseDepositsBeforeInitiatingMigration()` and
  `forwardedBridgeMint`. -/
  | migratorFacet
  /-- Any other code: what a delegatecall into it does, as an init and as a facet. -/
  | other (onInit : InitCalldata → ChainState → Option ChainState)
      (onCall : ProxyCall → ChainState → Option ChainState)

/-- `extcodesize != 0`. -/
def Code.hasCode : Code → Bool
  | .none => false
  | _ => true

/-- One row of `ICTMRelease.genesisFacets()` (`upgrades/registry/RegistryTypes.sol:22-25`). -/
structure GenesisFacet where
  facet : Address
  isFreezable : Bool
deriving DecidableEq

/-- What the creation path reads outside the diamond. Releases and facets are their getters,
fixed functions of their address, as in the rest of this folder. For a facet's `selectors()`
that is an assumption about the facet's code (one answer, constant and independent of the
caller), not a property of the release; topic `MutableSelectors` drops it. -/
structure Env where
  /-- The CTM's own address: `msg.sender` of the proxy's constructor and of the CTM's calls. -/
  ctm : Address
  /-- The code at each address. -/
  code : Address → Code
  /-- `ISelfDescribingFacet(f).selectors()`. -/
  selectorsOf : Address → List Selector
  /-- `ICTMRelease(R).genesisFacets()`. -/
  genesisFacets : Address → List GenesisFacet
  /-- `ICTMRelease(R).diamondInit()`. -/
  diamondInitOf : Address → Address
  /-- The first field of `ICTMRelease(R).genesisParams()`: the L1 genesis upgrade. -/
  genesisUpgradeOf : Address → Address
  /-- `ICTMRelease(R).verifier()`. -/
  verifierOf : Address → Address
  /-- `keccak256(abi.encode(tx))` of the genesis transaction composed for a release, a chain
  id and a version (`L1GenesisUpgrade.sol:35-40`, `BaseZkSyncUpgrade.sol:165, 183`). -/
  genesisTxHash : Address → ChainId → ℕ → ℕ

/-- `_facet.code.length != 0`. -/
def Env.hasCode (E : Env) (a : Address) : Bool := (E.code a).hasCode

/-- `ReleaseFacetReader.newChainInstallations` (`ReleaseFacetReader.sol:14-26`): one `Add` cut
per facet row, with the facet's own `selectors()`. -/
def newChainInstallations (E : Env) (R : Address) : List FacetCut :=
  (E.genesisFacets R).map (fun g => ⟨g.facet, .add, g.isFreezable, E.selectorsOf g.facet⟩)

/-- A release's routing, flattened: its facet rows with each facet's `selectors()`
(`TransitionDerivationLib._loadRouting`, `upgrades/registry/libraries/TransitionDerivationLib.sol:172-183`).
This is what `World.relRows` stands for. -/
def releaseRows (E : Env) (R : Address) : ReleaseRows :=
  (E.genesisFacets R).flatMap (fun g => (E.selectorsOf g.facet).map (fun x => (x, (g.facet, g.isFreezable))))

/-! ## The inits -/

/-- `DiamondInit.initialize(_chainId, _admin)` (`DiamondInit.sol:52-150`), delegatecalled into
the diamond by the CTM, whose version state is `c`:

    reentrancyGuardInitializer                                 // :52 → ReentrancyGuard.sol:43-63
    uint256 protocolVersion = ctm.protocolVersion();           // :58
    address currentRelease = ctm.currentRelease();             // :77
    if (currentRelease == address(0)) { revert ZeroAddress(); } // :78-80
    ... newChainInstallations(release) ... Diamond.diamondCut  // :82-87
    s.chainId = _chainId;                                      // :89
    s.chainTypeManager = msg.sender;                           // :91
    s.protocolVersion = protocolVersion;                       // :110
    s.verifier = IVerifier(release.verifier());                // :114-118
    s.admin = _admin;                                          // :119

The cut's init is `address(0)` with empty calldata, so `_initializeDiamondCut` does nothing
(`Diamond.sol:311-315`); with no facet rows the cut is skipped, which leaves the same storage.
DiamondInit's other writes (:90, :94, :107, :109, :120, :126-143) are to fields not modelled. -/
def diamondInitialize (E : Env) (c : CTM) (id : ChainId) (admin : Address) (st : ChainState) :
    Option ChainState :=
  if st.lock ≠ 0 then none
  else if c.cur = 0 then none
  else (applyFacetCuts E.hasCode st.diamond (newChainInstallations E c.cur)).map (fun ds =>
    { lock := 1, diamond := ds,
      app := { st.app with
        chainId := id, chainTypeManager := E.ctm, protocolVersion := c.pv,
        verifier := E.verifierOf c.cur, admin := admin } })

/-- `L1GenesisUpgrade.genesisUpgrade()` (`L1GenesisUpgrade.sol:31-53`), delegatecalled into the
diamond; the CTM at `s.chainTypeManager` has version state `c`:

    uint256 protocolVersion = s.protocolVersion;                                  // :32
    _upgrade({_newProtocolVersion: protocolVersion, _upgradeTimestamp: 0,
              _verifier: address(0), _l2ProtocolUpgradeTx: ...});                // :42-47

and in `_upgrade` (`BaseZkSyncUpgrade.sol:66-102`) and the genesis `_setNewProtocolVersion`
(`BaseZkSyncUpgradeGenesis.sol:25-82`):

    if (block.timestamp < 0) ...                                   // :76-78, never
    bool isOnSettlementLayer = s.settlementLayer == address(0);    // :81
    if (!_isOnSettlementLayer) { revert GenesisUpgradeExpectedOnSettlementLayer(); } // Genesis :62-64
    if (s.l2SystemContractsUpgradeTxHash != bytes32(0)) { revert ... }               // Genesis :72-74
    if (s.l2SystemContractsUpgradeBatchNumber != 0) { revert ... }                   // Genesis :75-77
    s.protocolVersion = _newProtocolVersion;                       // Genesis :80, the same value
    if (_verifier != address(0)) { ... }                           // :91-93, skipped
    s.l2SystemContractsUpgradeTxHash = l2ProtocolUpgradeTxHash;    // :97-99 → :185

The version check `_newProtocolVersion < previousProtocolVersion` (Genesis :30-35) cannot fire:
the two are equal. The upgrade transaction always has the system-upgrade type
(`state-transition/libraries/L2CanonicalTransactionLib.sol:54-55`), so its hash is written. -/
def l1GenesisUpgradeRun (E : Env) (c : CTM) (st : ChainState) : Option ChainState :=
  if st.app.settlementLayer ≠ 0 then none
  else if st.app.l2SystemContractsUpgradeTxHash ≠ 0 then none
  else if st.app.l2SystemContractsUpgradeBatchNumber ≠ 0 then none
  else some { st with app := { st.app with
    protocolVersion := st.app.protocolVersion,
    l2SystemContractsUpgradeTxHash := E.genesisTxHash c.cur st.app.chainId st.app.protocolVersion } }

/-- An init delegatecall into the code at `a` (`Diamond.sol:318`): the genuine inits run their
one function and refuse any other calldata; any other code does what it does. A genuine facet
used as an init reverts: it has neither function, except the Admin facet's
`genesisUpgrade()`, which returns no data and so fails the magic-value check (:333-335). -/
def runInit (E : Env) (c : CTM) (a : Address) (cd : InitCalldata) (st : ChainState) :
    Option ChainState :=
  match E.code a, cd with
  | .diamondInit, .initialize id admin => diamondInitialize E c id admin st
  | .l1GenesisUpgrade, .genesisUpgrade => l1GenesisUpgradeRun E c st
  | .other onInit _, cd => onInit cd st
  | _, _ => none

/-- `_initializeDiamondCut` (`Diamond.sol:310-340`): no init needs empty calldata
(`NonEmptyCalldata`, :311-315); otherwise the delegatecall must succeed. -/
def initializeDiamondCut (E : Env) (c : CTM) (st : ChainState) (init : Address)
    (cd : InitCalldata) : Option ChainState :=
  if init = 0 then (if cd = .empty then some st else none) else runInit E c init cd st

/-- `Diamond.diamondCut` (`Diamond.sol:109-137`): the facet cuts, then the init. -/
def diamondCut (E : Env) (c : CTM) (st : ChainState) (cut : DiamondCutData) : Option ChainState :=
  (applyFacetCuts E.hasCode st.diamond cut.facetCuts).bind (fun ds =>
    initializeDiamondCut E c { st with diamond := ds } cut.initAddress cut.initCalldata)

/-! ## The facet entry points and the proxy -/

/-- The cut `Admin.genesisUpgrade` builds (`Admin.sol:569-575`): no facet cuts, the release's
L1 genesis upgrade as init (`ChainTypeManager.sol:327-330`). -/
def genesisUpgradeCut (E : Env) (c : CTM) : DiamondCutData :=
  ⟨[], E.genesisUpgradeOf c.cur, .genesisUpgrade⟩

/-- `Admin.genesisUpgrade()` (`Admin.sol:566-578`): `_executeDiamondCut(cutData)` (:577, :112-115). -/
def adminGenesisUpgrade (E : Env) (c : CTM) (st : ChainState) : Option ChainState :=
  diamondCut E c st (genesisUpgradeCut E c)

/-- `Migrator.pauseDepositsBeforeInitiatingMigration()` (`Migrator.sol:105-129`):

    require(s.pausedDepositsTimestamp == 0, DepositsAlreadyPaused());   // :109
    s.pausedDepositsTimestamp = timestamp;                              // :121

The call to the chain asset handler when the chain settles elsewhere (:122-127) writes nothing
in this diamond. -/
def pauseDeposits (ts : ℕ) (st : ChainState) : Option ChainState :=
  if st.app.pausedDepositsTimestamp ≠ 0 then none
  else some { st with app := { st.app with pausedDepositsTimestamp := ts } }

/-- `Migrator.forwardedBridgeMint(_data, false)` (`Migrator.sol:213-305`) on a diamond the CTM has
just deployed; the CTM at `s.chainTypeManager` has version state `c`:

    if (currentProtocolVersion != protocolVersion) { revert OutdatedProtocolVersion(...); } // :223-229
    s.l2SystemContractsUpgradeTxHash = _commitment.l2SystemContractsUpgradeTxHash;           // :295
    s.l2SystemContractsUpgradeBatchNumber = _commitment.l2SystemContractsUpgradeBatchNumber; // :296
    s.settlementLayer = address(0);                                                          // :299
    _unpauseDeposits();                                     // :302 → :141-144, `pausedDepositsTimestamp = 0`

Its other writes (batch counters and hashes, priority tree, DA pair) are to fields not
modelled. -/
def migratorForwardedBridgeMint (c : CTM) (txHash batch : ℕ) (st : ChainState) :
    Option ChainState :=
  if st.app.protocolVersion ≠ c.pv then none
  else some { st with app := { st.app with
    l2SystemContractsUpgradeTxHash := txHash, l2SystemContractsUpgradeBatchNumber := batch,
    settlementLayer := 0, pausedDepositsTimestamp := 0 } }

/-- The facet code for a call. A genuine contract that lacks the called function reverts: none
has a `fallback`. Of the three selectors (`ProxyCall.selector`), `genesisUpgrade()` is in
`Admin.selectors()` (`Admin.sol:657-658`) and the other two in `Migrator.selectors()`
(`Migrator.sol:386-391`); `L1GenesisUpgrade` also has a `genesisUpgrade()`
(`L1GenesisUpgrade.sol:31`), so it runs if a release routed that selector to it. -/
def runFacet (E : Env) (c : CTM) : Code → ProxyCall → ChainState → Option ChainState
  | .adminFacet, .genesisUpgrade, st => adminGenesisUpgrade E c st
  | .l1GenesisUpgrade, .genesisUpgrade, st => l1GenesisUpgradeRun E c st
  | .migratorFacet, .pauseDeposits ts, st => pauseDeposits ts st
  | .migratorFacet, .forwardedBridgeMint h b, st => migratorForwardedBridgeMint c h b st
  | .other _ onCall, call, st => onCall call st
  | _, _, _ => none

/-- A call through the proxy's `fallback` (`DiamondProxy.sol:25-60`): an unrouted selector
reverts `"F"` (:35), a freezable one on a frozen diamond reverts `"q1"` (:36), otherwise the
routed facet runs in the diamond's storage (:44). -/
def proxyCall (E : Env) (c : CTM) (st : ChainState) (call : ProxyCall) : Option ChainState :=
  if (st.diamond.selectorToFacet call.selector).facetAddress = 0 then none
  else if st.diamond.isFrozen = true ∧ (st.diamond.selectorToFacet call.selector).isFreezable = true
  then none
  else runFacet E c (E.code (st.diamond.selectorToFacet call.selector).facetAddress) call st

/-! ## Creation -/

/-- The cut `_deployNewChain` hands the proxy (`ChainTypeManager.sol:685-690`). -/
def genesisCut (E : Env) (c : CTM) (id : ChainId) (admin : Address) : DiamondCutData :=
  ⟨[], E.diamondInitOf c.cur, .initialize id admin⟩

/-- `_deployNewChain` after its registration check (`ChainTypeManager.sol:685-693`): the
`DiamondProxy` constructor runs the genesis cut on fresh storage (`DiamondProxy.sol:16-21`; its
`_chainId == block.chainid` check passes, the CTM passes `block.chainid`). -/
def deployNewChain (E : Env) (c : CTM) (id : ChainId) (admin : Address) : Option ChainState :=
  diamondCut E c ChainState.fresh (genesisCut E c id admin)

/-- `createNewChain(_chainId, _admin)` after its registration check
(`ChainTypeManager.sol:708-716`). -/
def createNewChain (E : Env) (c : CTM) (id : ChainId) (admin : Address) (ts : ℕ) :
    Option ChainState :=
  (deployNewChain E c id admin).bind (fun st1 =>
    (proxyCall E c st1 .genesisUpgrade).bind (fun st2 =>
      proxyCall E c st2 (.pauseDeposits ts)))

/-- A chain arriving where it has no diamond: `ChainTypeManager.forwardedBridgeMint`
(`ChainTypeManager.sol:751-763`) with incoming version `v`, then the diamond's
`forwardedBridgeMint(chainData, false)` (`ChainAssetHandlerBase.sol:399, 417`). In between, the
chain asset handler registers the diamond with the bridgehub and the message root (:405, :409),
which write their own storage, not the diamond's (`core/bridgehub/BridgehubBase.sol:301-307`). -/
def migrateInNewChain (E : Env) (c : CTM) (v : ℕ) (id : ChainId) (admin : Address)
    (txHash batch : ℕ) : Option ChainState :=
  if v ≠ c.pv then none
  else (deployNewChain E c id admin).bind (fun st => proxyCall E c st (.forwardedBridgeMint txHash batch))

/-! ## The system with chain creation run as code -/

/-- A chain creation as the code runs it. The registration check is `getZKChain(_chainId) ==
address(0)` (`ChainTypeManager.sol:680-683`); the model keeps `ChainRouting`'s chains map, so
the new chain is recorded under `id` as `ChainRouting` records it. -/
inductive CodeCreation (E : Env) : Sys → Label → Sys → Prop
  | createNewChain {s : Sys} {id : ChainId} {admin : Address} {ts : ℕ} {st : ChainState} :
      s.chains id = none →
      createNewChain E s.ctm id admin ts = some st →
      CodeCreation E s (.genesis id) { s with chains := upd s.chains id (some st.chain) }
  | forwardedBridgeMint {s : Sys} {id : ChainId} {admin : Address} {v txHash batch : ℕ}
      {st : ChainState} :
      s.chains id = none →
      migrateInNewChain E s.ctm v id admin txHash batch = some st →
      CodeCreation E s (.migrateIn id) { s with chains := upd s.chains id (some st.chain) }

/-- The labels that create a chain. -/
def creationLabel : Label → Prop
  | .genesis _ => True
  | .migrateIn _ => True
  | _ => False

/-- One step with chain creation run as code, every other step as in `ChainRouting`. -/
inductive CodeStep (W : World) (E : Env) : Sys → Label → Sys → Prop
  | create {s s' : Sys} {l : Label} : CodeCreation E s l s' → CodeStep W E s l s'
  | other {s s' : Sys} {l : Label} : ¬ creationLabel l → Step W s l s' → CodeStep W E s l s'

/-- A sequence of such steps. -/
inductive CodeRun (W : World) (E : Env) : Sys → List Label → Sys → Prop
  | nil {s : Sys} : CodeRun W E s [] s
  | cons {s s' s'' : Sys} {l : Label} {ls : List Label} :
      CodeStep W E s l s' → CodeRun W E s' ls s'' → CodeRun W E s (l :: ls) s''

/-! ## What the properties assume about a release -/

/-- **The release's members are the code they are named for.** Its `diamondInit()` is
`DiamondInit`, its genesis upgrade is `L1GenesisUpgrade`, the facet its rows route
`genesisUpgrade()` to is the Admin facet, the ones for the two Migrator entry points are the
Migrator facet, and the world's flattened rows of `R` are the release's rows
(`World.relRows`, "objects are their getters"). Governance's review of a release is what
establishes this (`CTMRelease.sol:23-26`); nothing on chain checks it. -/
structure GenuineRelease (E : Env) (W : World) (R : Address) : Prop where
  diamondInit : E.code (E.diamondInitOf R) = .diamondInit
  genesisUpgrade : E.code (E.genesisUpgradeOf R) = .l1GenesisUpgrade
  adminFacet : ∀ f b, rowsRouting (releaseRows E R) selGenesisUpgrade = some (f, b) →
    E.code f = .adminFacet
  migratorFacet : ∀ x, (x = selPauseDeposits ∨ x = selForwardedBridgeMint) →
    ∀ f b, rowsRouting (releaseRows E R) x = some (f, b) → E.code f = .migratorFacet
  rows : W.relRows R = releaseRows E R

/-- **What `CTMRelease` checks about a release** (`upgrades/registry/objects/CTMRelease.sol`):
one row per facet (the constructor, :171-184), every facet with code (`validate()`, :117), every
facet with at least one selector (:121-123), and no selector routed twice (:128, :190-213). The
CTM runs `validate()` on every release it installs (`ChainTypeManager.sol:310`). -/
structure ReleaseWf (E : Env) (R : Address) : Prop where
  uniqueFacets : ((E.genesisFacets R).map GenesisFacet.facet).Nodup
  facetsHaveCode : ∀ g ∈ E.genesisFacets R, E.hasCode g.facet = true
  selectorsNonempty : ∀ g ∈ E.genesisFacets R, E.selectorsOf g.facet ≠ []
  uniqueSelectors : ((releaseRows E R).map Prod.fst).Nodup

/-- **The release routes the entry point `x` to code `k`.** -/
def RoutesTo (E : Env) (R : Address) (x : Selector) (k : Code) : Prop :=
  ∃ f b, rowsRouting (releaseRows E R) x = some (f, b) ∧ E.code f = k

/-! ## Witness data

A world `gWorld` whose releases are made of facets: releases `100`, `200`, `250` (versions 1,
2, 3, from `wWorld`) each have an Admin facet (`11`, `21`, `31`, not freezable) routing
`genesisUpgrade()` and selector `1`, and a Migrator facet (`12`, `22`, `32`, freezable) routing
the two Migrator entry points and selector `2`. `DiamondInit` is at `7` and `L1GenesisUpgrade`
at `8` for every release. The CTM is at `1000`. Transitions are `wWorld`'s. -/

/-- The Admin facets of the witness releases. -/
def gAdminFacets : List Address := [11, 21, 31]

/-- The Migrator facets of the witness releases. -/
def gMigratorFacets : List Address := [12, 22, 32]

/-- The witness code. -/
def gCode : Address → Code := fun a =>
  if a = 7 then .diamondInit
  else if a = 8 then .l1GenesisUpgrade
  else if a ∈ gAdminFacets then .adminFacet
  else if a ∈ gMigratorFacets then .migratorFacet
  else .none

/-- The witness facets' self-descriptions. -/
def gSelectors : Address → List Selector := fun a =>
  if a ∈ gAdminFacets then [selGenesisUpgrade, 1]
  else if a ∈ gMigratorFacets then [selPauseDeposits, selForwardedBridgeMint, 2]
  else []

/-- The witness releases' facet rows. -/
def gGenesisFacets : Address → List GenesisFacet := fun R =>
  if R = 100 then [⟨11, false⟩, ⟨12, true⟩]
  else if R = 200 then [⟨21, false⟩, ⟨22, true⟩]
  else if R = 250 then [⟨31, false⟩, ⟨32, true⟩]
  else []

/-- The witness environment. -/
def gEnv : Env where
  ctm := 1000
  code := gCode
  selectorsOf := gSelectors
  genesisFacets := gGenesisFacets
  diamondInitOf := fun _ => 7
  genesisUpgradeOf := fun _ => 8
  verifierOf := fun _ => 9
  genesisTxHash := fun _ _ _ => 1

/-- The witness world: `wWorld`'s versions and transitions, with each release's rows read off
its facets. -/
def gWorld : World := ⟨wRelVersion, releaseRows gEnv, wTr⟩

/-- The fresh witness system: a CTM initialized on release `100`, no chains. -/
def gSys0 : Sys := ⟨initState gWorld 100, fun _ => none⟩

/-- **A foreign `DiamondInit`.** It routes only the three entry points, to the right facets, and
records the CTM (`1000`) and version `1`, as DiamondInit would on the witness CTM, but installs
nothing else of the release. -/
def foreignInit : InitCalldata → ChainState → Option ChainState
  | .initialize _ _, st =>
    let sel := upd (upd (upd st.diamond.selectorToFacet selGenesisUpgrade ⟨11, 0, false⟩)
      selPauseDeposits ⟨12, 0, true⟩) selForwardedBridgeMint ⟨12, 1, true⟩
    some { st with
      lock := 1,
      diamond := { st.diamond with selectorToFacet := sel },
      app := { st.app with chainTypeManager := 1000, protocolVersion := 1 } }
  | _, _ => none

/-- The witness environment with `foreignInit` at the release's `diamondInit()` address. -/
def fInitEnv : Env :=
  { gEnv with code := fun a => if a = 7 then .other foreignInit (fun _ _ => none) else gCode a }

/-- **A foreign genesis upgrade.** It routes one extra selector, `9`, to facet `99`. -/
def foreignUpgrade : InitCalldata → ChainState → Option ChainState
  | .genesisUpgrade, st => some { st with diamond := { st.diamond with
      selectorToFacet := upd st.diamond.selectorToFacet 9 ⟨99, 0, false⟩ } }
  | _, _ => none

/-- The witness environment with `foreignUpgrade` at the release's genesis-upgrade address. -/
def fUpgradeEnv : Env :=
  { gEnv with code := fun a => if a = 8 then .other foreignUpgrade (fun _ _ => none) else gCode a }

/-- Witness release rows with one facet row that has no selectors: release `100`'s facets plus
facet `13`, which describes no selector. -/
def eGenesisFacets : Address → List GenesisFacet := fun R =>
  if R = 100 then [⟨11, false⟩, ⟨12, true⟩, ⟨13, false⟩] else gGenesisFacets R

/-- The witness environment whose release `100` has the selector-less row (facet `13` has code
and describes no selector). -/
def eEnv : Env :=
  { gEnv with
    genesisFacets := eGenesisFacets,
    code := fun a => if a = 13 then .other (fun _ _ => none) (fun _ _ => none) else gCode a }

/-- The world of `eEnv`. -/
def eWorld : World := ⟨wRelVersion, releaseRows eEnv, wTr⟩

end Contracts.ChainTypeManager.GenesisWriters
