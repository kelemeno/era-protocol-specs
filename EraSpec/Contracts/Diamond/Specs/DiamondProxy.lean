import EraSpec.Contracts.ChainTypeManager.Specs.DiamondStorage

/-!
# Model: the diamond proxy — dispatch, freezing, the init call, and runs

Source: era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`. Paths are
relative to `l1-contracts/contracts/`:

* `state-transition/libraries/Diamond.sol` (the library: storage, `diamondCut`, the init call);
* `state-transition/chain-deps/DiamondProxy.sol` (constructor and `fallback`);
* `state-transition/chain-deps/DiamondInit.sol` (the init the chain-creation path uses);
* `state-transition/chain-deps/facets/Admin.sol:559-639` (the facet functions that write
  diamond storage: `upgradeChainFromVersion`, `executeUpgrade` and `genesisUpgrade` through
  `_executeDiamondCut` (:117-118), and `freezeDiamond`/`unfreezeDiamond`);
* `state-transition/chain-deps/facets/Getters.sol:207-217, 245-252` (the freezability getters).

**This file is definitions only.** Statements are in
`EraSpec.Contracts.Diamond.Properties.DiamondProxy`, proofs in
`EraSpec.Contracts.Diamond.Proofs.DiamondProxy`.

## What is reused

The three source files are byte-identical at `d9f6789` and at `e561b9cc2`, the commit
`Contracts.ChainTypeManager.Specs.DiamondStorage` transcribes (`git diff --stat e561b9cc2 d9f6789`
on the three paths is empty). That file's `DiamondStorage`, `addFunctions`, `replaceFunctions`,
`removeFunctions`, `facetCut`, `diamondCut` (the facet-cut loop, `Diamond.sol:109-133`) and the
storage invariant `DiamondOk` are used here unchanged, and its modelling choices apply: storage
arrays are lists, `uint16` positions are `ℕ`, the code-existence check is modelled only for
address zero, and the `toUint16` casts are omitted. Each omission only removes reverts.

## What this file adds

* `isFrozen` (`Diamond.sol:66`), which `DiamondStorage` above omits, in `ProxyState`.
* The proxy's `fallback` (`DiamondProxy.sol:25-60`) as `fallbackTarget`.
* `_initializeDiamondCut` (`Diamond.sol:310-340`) with its return-data checks, the whole
  `diamondCut` (cuts, then init) as `diamondCutFull`, and the constructor
  (`DiamondProxy.sol:16-21`).
* The facet entry points that write diamond storage, and a labelled step relation over every
  call through the proxy (`Step`, `Run`, `Reach`).
* The getters `isFacetFreezable` and `isFunctionFreezable`.
* Countermodel variants of `Diamond.sol`, each with one check deleted.

## Modelling choices

* **Calldata** is its length and its first four bytes, read as a `Selector` (`Calldata`).
  `msg.sig` of empty calldata is `0x00000000` (`Calldata.sig`). Calldata of length 1-3 reverts
  before `msg.sig` is used (`DiamondProxy.sol:30`).
* **What a facet does** is `Env.fn f x`: the function the code at facet `f` runs for selector
  `x`, classified by its effect on diamond storage. `Admin.sol` is the only facet that writes
  `Diamond.DiamondStorage`. At the pin, the only files that call `getDiamondStorage()` are
  `Diamond.sol`, `DiamondProxy.sol`, `Admin.sol`, `Getters.sol`, `LiveRoutingReader.sol` and the
  test contract `dev-contracts/test/DiamondProxyTest.sol`; `Getters` and `LiveRoutingReader`
  only read. The writers are the cut entry points (`.executeCut`) and `freezeDiamond` /
  `unfreezeDiamond`. Every other facet function is `.other` and leaves diamond storage alone.
  Facet storage (`ZKChainStorage`) is not modelled; `Env.ctm` is the value of
  `s.chainTypeManager` that `onlyChainTypeManager` reads (`ZKChainBase.sol:85-90`).
* **The cut entry points' own guards are not modelled.** `executeUpgrade` and `genesisUpgrade`
  are `onlyChainTypeManager`; `upgradeChainFromVersion` checks its caller and versions. A
  `.executeCut` step may run any cut for any caller. This only adds runs, so the safety results
  still hold; the freeze results name the caller.
* **The init's delegatecall** (`Diamond.sol:318`) is an `InitRun`: the nested
  `Diamond.diamondCut` calls the init code makes (with `initAddress == 0`, as
  `DiamondInit.sol:84-86` and `BaseZkSyncUpgrade.sol:128` do), and whether it reverted or
  returned, with its return data. Init code that writes diamond storage other than through
  `Diamond.diamondCut` (an arbitrary `sstore` into `isFrozen` or `selectorToFacet`) is outside
  the model (`MODEL-DIAMOND-INIT`). A delegatecall to an address without code succeeds and
  returns no data (`codelessInit`, a `VM-CALL` fact).
* **Revert is the absence of a step** (`Option.none`). A reverted init or nested cut reverts
  the whole call (`VM-REVERT`).
-/

namespace Contracts.Diamond

open Clear
open Contracts.ChainTypeManager

/-! ## Bytes and the magic value -/

/-- A byte string (`bytes memory`): return data and init calldata. -/
abbrev Bytes := List UInt8

/-- Big-endian value of a byte string, accumulated from the left. -/
def bytesToNat : Bytes → ℕ → ℕ
  | [], acc => acc
  | b :: bs, acc => bytesToNat bs (acc * 256 + b.toNat)

/-- `abi.decode(data, (bytes32))` of 32-byte return data (`Diamond.sol:336`), as a word. The
source reaches it only after checking `data.length == 32` (:333). -/
def decodeBytes32 (data : Bytes) : UInt256 := Fin.ofNat UInt256.size (bytesToNat data 0)

/-- `DIAMOND_INIT_SUCCESS_RETURN_VALUE` (`Diamond.sol:29-30`). The source comment says it is
`keccak256("diamond.zksync.init") - 1`; nothing here depends on that. -/
def MAGIC : UInt256 := 0x33774e659306e47509050e97cb651e731180a42d458212294d30751925c551a2

/-- The 32 bytes of `abi.encode(DIAMOND_INIT_SUCCESS_RETURN_VALUE)`, which
`DiamondInit.initialize` returns (`DiamondInit.sol:149`). -/
def magicBytes : Bytes :=
  [0x33, 0x77, 0x4e, 0x65, 0x93, 0x06, 0xe4, 0x75, 0x09, 0x05, 0x0e, 0x97, 0xcb, 0x65, 0x1e, 0x73,
   0x11, 0x80, 0xa4, 0x2d, 0x45, 0x82, 0x12, 0x29, 0x4d, 0x30, 0x75, 0x19, 0x25, 0xc5, 0x51, 0xa2]

/-! ## The proxy's state -/

/-- `Diamond.DiamondStorage` (`Diamond.sol:62-67`) in full: the routing structures of
`ChainTypeManager.DiamondStorage` and `isFrozen`. -/
structure ProxyState where
  /-- `selectorToFacet`, `facetToSelectors`, `facets`. -/
  ds : DiamondStorage
  /-- `isFrozen`. -/
  isFrozen : Bool

/-- A newly deployed proxy's diamond storage: every slot zero. -/
def ProxyState.fresh : ProxyState := ⟨DiamondStorage.fresh, false⟩

/-! ## The fallback -/

/-- The calldata of a call into the proxy: `msg.data.length`, and its first four bytes as a
selector (meaningful when the length is at least 4). -/
structure Calldata where
  /-- `msg.data.length`. -/
  len : ℕ
  /-- `bytes4(msg.data[0:4])`. -/
  head : Selector

/-- `msg.sig`: the first four bytes, and `0x00000000` for empty calldata. -/
def Calldata.sig (cd : Calldata) : Selector := if cd.len = 0 then 0 else cd.head

/-- `DiamondProxy.fallback` (`DiamondProxy.sol:25-60`): the facet the proxy delegatecalls, or
`none` for a revert.

    require(msg.data.length >= 4 || msg.data.length == 0, "Ut");
    Diamond.SelectorToFacet memory facet = diamondStorage.selectorToFacet[msg.sig];
    address facetAddress = facet.facetAddress;
    require(facetAddress != address(0), "F");
    require(!diamondStorage.isFrozen || !facet.isFreezable, "q1");
    ... delegatecall(gas(), facetAddress, ptr, calldatasize(), 0, 0) ...

What the facet then does, and whether it reverts, is the facet's business (`Env.fn`). -/
def fallbackTarget (s : ProxyState) (cd : Calldata) : Option Address :=
  if ¬ (4 ≤ cd.len ∨ cd.len = 0) then none
  else
    let facet := s.ds.selectorToFacet cd.sig
    if facet.facetAddress = 0 then none
    else if (!s.isFrozen || !facet.isFreezable) = false then none
    else some facet.facetAddress

/-! ## The init call -/

/-- How an init's delegatecall ended. -/
inductive InitOutcome
  /-- `success == false`, with its return data. -/
  | reverted (data : Bytes)
  /-- `success == true`, with its return data. -/
  | returned (data : Bytes)

/-- What the init code at `initAddress` does when delegatecalled with the init calldata: the
`Diamond.diamondCut` calls it makes (each with `initAddress == 0`; concatenated, they are one
`diamondCut`), and how it ends. -/
structure InitRun where
  /-- The facet cuts the init applies through `Diamond.diamondCut`. -/
  nested : List FacetCut
  /-- The delegatecall's result. -/
  outcome : InitOutcome

/-- A delegatecall to an address with no code: it succeeds and returns nothing. -/
def codelessInit : InitRun := ⟨[], .returned []⟩

/-- `Diamond._initializeDiamondCut` (`Diamond.sol:310-340`):

    if (_init == address(0)) {
        if (_calldata.length != 0) { revert NonEmptyCalldata(); }
    } else {
        (bool success, bytes memory data) = _init.delegatecall(_calldata);
        if (!success) { ... revert ... }                   // both branches revert (:319-329)
        if (data.length != 32) { revert DelegateCallFailed(data); }
        if (abi.decode(data, (bytes32)) != DIAMOND_INIT_SUCCESS_RETURN_VALUE) {
            revert DelegateCallFailed(data);
        }
    }

The init's own writes (its nested cuts) happen inside the delegatecall, before the checks; a
failed check reverts them with everything else. -/
def initializeDiamondCut (s : ProxyState) (init : Address) (cd : Bytes) (r : InitRun) :
    Option ProxyState :=
  if init = 0 then
    if cd.length ≠ 0 then none else some s
  else
    match r.outcome with
    | .reverted _ => none
    | .returned data =>
      (diamondCut s.ds r.nested).bind fun ds' =>
        if data.length ≠ 32 then none
        else if decodeBytes32 data ≠ MAGIC then none
        else some { s with ds := ds' }

/-- `Diamond.DiamondCutData` (`Diamond.sol:86-90`). -/
structure CutData where
  /-- `facetCuts`. -/
  facetCuts : List FacetCut
  /-- `initAddress`. -/
  initAddress : Address
  /-- `initCalldata`. -/
  initCalldata : Bytes

/-- `Diamond.diamondCut` (`Diamond.sol:109-137`): the facet cuts in order, then
`_initializeDiamondCut`. `r` is what the init code does. -/
def diamondCutFull (s : ProxyState) (cut : CutData) (r : InitRun) : Option ProxyState :=
  (diamondCut s.ds cut.facetCuts).bind fun ds₁ =>
    initializeDiamondCut { s with ds := ds₁ } cut.initAddress cut.initCalldata r

/-- The proxy's constructor (`DiamondProxy.sol:16-21`) on fresh storage:

    require(_chainId == block.chainid, "pr");
    Diamond.diamondCut(_diamondCut); -/
def construct (chainId blockChainId : ℕ) (cut : CutData) (r : InitRun) : Option ProxyState :=
  if chainId ≠ blockChainId then none else diamondCutFull ProxyState.fresh cut r

/-! ## The facet entry points and runs -/

/-- What a facet function does to diamond storage. -/
inductive FacetFn
  /-- A cut entry point: `Admin.upgradeChainFromVersion` (`Admin.sol:559-587`),
  `executeUpgrade` (:593-595), `genesisUpgrade` (:599-609); each runs `Diamond.diamondCut`. -/
  | executeCut
  /-- `Admin.freezeDiamond` (`Admin.sol:616-626`). -/
  | freeze
  /-- `Admin.unfreezeDiamond` (`Admin.sol:629-639`). -/
  | unfreeze
  /-- Any other function: writes no diamond storage (it may revert). -/
  | other
deriving DecidableEq

/-- The environment of a run. -/
structure Env where
  /-- `s.chainTypeManager`, the address `onlyChainTypeManager` compares the caller with. -/
  ctm : Address
  /-- The function the code at facet `f` runs for selector `x`. -/
  fn : Address → Selector → FacetFn

/-- **One call through the proxy, by `caller`.** The proxy dispatches by `fallbackTarget`; the
facet function then runs in the proxy's storage.

* `cut`: a cut entry point runs `Diamond.diamondCut` (its caller and version checks are not
  modelled: any cut, any caller).
* `freeze`: `freezeDiamond`, guards in source order: `onlyChainTypeManager`
  (`ZKChainBase.sol:85-90`), then `if (diamondStorage.isFrozen) revert DiamondAlreadyFrozen()`
  (`Admin.sol:620-622`), then `isFrozen = true` (:623).
* `unfreeze`: `unfreezeDiamond`: `onlyChainTypeManager`, then
  `if (!diamondStorage.isFrozen) revert DiamondNotFrozen()` (:633-635), then `isFrozen = false`
  (:636).
* `other`: any other function; diamond storage is unchanged.

A reverted call is no step. -/
inductive Step (E : Env) : Address → ProxyState → ProxyState → Prop
  | cut {caller : Address} {s s' : ProxyState} {cd : Calldata} {f : Address} (c : CutData)
      (r : InitRun) :
      fallbackTarget s cd = some f → E.fn f cd.sig = .executeCut →
      diamondCutFull s c r = some s' → Step E caller s s'
  | freeze {caller : Address} {s : ProxyState} {cd : Calldata} {f : Address} :
      fallbackTarget s cd = some f → E.fn f cd.sig = .freeze →
      caller = E.ctm → s.isFrozen = false → Step E caller s { s with isFrozen := true }
  | unfreeze {caller : Address} {s : ProxyState} {cd : Calldata} {f : Address} :
      fallbackTarget s cd = some f → E.fn f cd.sig = .unfreeze →
      caller = E.ctm → s.isFrozen = true → Step E caller s { s with isFrozen := false }
  | other {caller : Address} {s : ProxyState} {cd : Calldata} {f : Address} :
      fallbackTarget s cd = some f → E.fn f cd.sig = .other → Step E caller s s

/-- A run: successive steps, any entry point in any order, with their callers. -/
inductive Run (E : Env) : List Address → ProxyState → ProxyState → Prop
  | nil (s : ProxyState) : Run E [] s s
  | cons {c : Address} {cs : List Address} {s s₁ s₂ : ProxyState} :
      Step E c s s₁ → Run E cs s₁ s₂ → Run E (c :: cs) s s₂

/-- A state some deployment reaches: a successful constructor, then a run. -/
def Reach (E : Env) (s : ProxyState) : Prop :=
  ∃ (chainId : ℕ) (cut : CutData) (r : InitRun) (s₀ : ProxyState) (cs : List Address),
    construct chainId chainId cut r = some s₀ ∧ Run E cs s₀ s

/-! ## Getters -/

/-- `Getters.isFacetFreezable` (`Getters.sol:207-217`): the freezability of the facet's first
selector, `false` for a facet with none. -/
def isFacetFreezable (ds : DiamondStorage) (f : Address) : Bool :=
  match (ds.facetToSelectors f).selectors with
  | [] => false
  | x₀ :: _ => (ds.selectorToFacet x₀).isFreezable

/-- `Getters.isFunctionFreezable` (`Getters.sol:245-252`). -/
def isFunctionFreezable (ds : DiamondStorage) (x : Selector) : Bool :=
  if (ds.selectorToFacet x).facetAddress = 0 then false else (ds.selectorToFacet x).isFreezable

/-! ## The freezability invariant -/

/-- **Every facet has one freezability**: two selectors routed to the same facet have the same
`isFreezable`. `_addOneFunction` checks a new selector against the facet's first selector
(`Diamond.sol:240-248`). -/
def FreezeUniform (ds : DiamondStorage) : Prop :=
  ∀ (x y : Selector) (f : Address) (b c : Bool),
    ds.routing x = some (f, b) → ds.routing y = some (f, c) → b = c

/-! ## Countermodel variants, each with one check deleted -/

/-- `_addOneFunction` with the freezability check (`Diamond.sol:243-248`) deleted. -/
def addOneFunctionNoFrzCheck (ds : DiamondStorage) (f : Address) (x : Selector) (b : Bool) :
    DiamondStorage :=
  let sels := (ds.facetToSelectors f).selectors
  { ds with
    selectorToFacet := upd ds.selectorToFacet x ⟨f, sels.length, b⟩,
    facetToSelectors := upd ds.facetToSelectors f
      { ds.facetToSelectors f with selectors := sels ++ [x] } }

/-- `_addFunctions`'s loop over `addOneFunctionNoFrzCheck` (the `FacetExists` check kept). -/
def addLoopNoFrzCheck : DiamondStorage → Address → List Selector → Bool → Option DiamondStorage
  | ds, _, [], _ => some ds
  | ds, f, x :: xs, b =>
      if (ds.selectorToFacet x).facetAddress ≠ 0 then none
      else addLoopNoFrzCheck (addOneFunctionNoFrzCheck ds f x b) f xs b

/-- `_addFunctions` without the freezability check. -/
def addFunctionsNoFrzCheck (ds : DiamondStorage) (f : Address) (xs : List Selector) (b : Bool) :
    Option DiamondStorage :=
  if f = 0 then none else addLoopNoFrzCheck (saveFacetIfNew ds f) f xs b

/-- `_addFunctions`'s loop with the `FacetExists` check (`Diamond.sol:157-160`) deleted. -/
def addLoopNoExistsCheck : DiamondStorage → Address → List Selector → Bool →
    Option DiamondStorage
  | ds, _, [], _ => some ds
  | ds, f, x :: xs, b => (addOneFunction ds f x b).bind fun d => addLoopNoExistsCheck d f xs b

/-- `_addFunctions` without the `FacetExists` check. -/
def addFunctionsNoExistsCheck (ds : DiamondStorage) (f : Address) (xs : List Selector)
    (b : Bool) : Option DiamondStorage :=
  if f = 0 then none else addLoopNoExistsCheck (saveFacetIfNew ds f) f xs b

/-- `_initializeDiamondCut` with the two return-data checks (`Diamond.sol:333-338`) deleted:
any successful delegatecall is accepted. -/
def initializeNoReturnCheck (s : ProxyState) (init : Address) (cd : Bytes) (r : InitRun) :
    Option ProxyState :=
  if init = 0 then
    if cd.length ≠ 0 then none else some s
  else
    match r.outcome with
    | .reverted _ => none
    | .returned _ => (diamondCut s.ds r.nested).map fun ds' => { s with ds := ds' }

/-! ## Witness data

A chain-like proxy: an Admin-like facet `21` routes `1` (a cut entry point), `2`
(`freezeDiamond`) and `3` (`unfreezeDiamond`); an Executor-like facet `22` (freezable) routes
`5`. The CTM is `99`. -/

/-- The witness's facet functions. -/
def wEnv : Env :=
  ⟨99, fun f x =>
    if f = 21 ∧ x = 1 then .executeCut
    else if f = 21 ∧ x = 2 then .freeze
    else if f = 21 ∧ x = 3 then .unfreeze
    else .other⟩

/-- What the witness's init does, as `DiamondInit.initialize` does (`DiamondInit.sol:82-86,
149`): it installs the two facets through `Diamond.diamondCut` and returns the magic value.
`adminFreezable` is the Admin-like facet's freezability. -/
def wInit (adminFreezable : Bool) : InitRun :=
  ⟨[⟨21, .add, adminFreezable, [1, 2, 3]⟩, ⟨22, .add, true, [5]⟩], .returned magicBytes⟩

/-- The constructor's cut data, shaped as `ChainTypeManager._deployNewChain` passes it: no facet
cuts, the init at `50` with some calldata. -/
def wCtorCut : CutData := ⟨[], 50, [1, 2, 3, 4]⟩

/-- A cut made while frozen: add a freezable facet `23` routing `6`, no init. -/
def wFrozenCut : CutData := ⟨[⟨23, .add, true, [6]⟩], 0, []⟩

end Contracts.Diamond
