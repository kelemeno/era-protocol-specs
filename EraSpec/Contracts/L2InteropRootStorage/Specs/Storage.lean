import EraSpec.Core.Word

/-!
# Model: `L2InteropRootStorage` — the interop roots an L2 has imported

**This file is definitions only.**  Statements are in
`EraSpec.Contracts.L2InteropRootStorage.Properties.Storage`, proofs in
`EraSpec.Contracts.L2InteropRootStorage.Proofs.Storage`.

## Source

era-contracts `draft/v0.35.0` head `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`, under
`l1-contracts/contracts/`.  Every file cited below is byte-identical at `d9f678900e1b`, where this
model was first written, and at `e561b9cc2`.  At `main` `70096e2ea6ee` the contract's code is the
same: it imports `Unauthorized` from another file and has one more comment line (`:29`), so its
source lines from `:29` on are one higher than those cited here.  At `c67894b9` the contract has no
`latestInteropRootTimestamp`; the last section of this file transcribes that version.

`interop/L2InteropRootStorage.sol` (104 lines, the whole contract):

    modifier onlyCallFromBootloader() {                                            // :20-25
        if (msg.sender != L2_BOOTLOADER_ADDRESS) revert Unauthorized(msg.sender);
        _;
    }
    mapping(uint256 chainId => mapping(uint256 blockOrBatchNumber => StoredInteropRoot))
        internal storedInteropRoots;                                               // :32
    mapping(uint256 chainId => uint256 timestamp) public latestInteropRootTimestamp;   // :36

    function interopRoots(uint256 chainId, uint256 blockOrBatchNumber) external view
        returns (StoredInteropRoot memory) { return storedInteropRoots[chainId][blockOrBatchNumber]; }  // :39-44

    function addSingleInteropRoot(InteropRoot calldata interopRoot) external onlyCallFromBootloader {   // :50-52
        _addInteropRoot(interopRoot.chainId, interopRoot.blockOrBatchNumber, interopRoot.timestamp, interopRoot.sides);
    }
    function addInteropRootsInBatch(InteropRoot[] calldata interopRootsInput) external onlyCallFromBootloader {  // :56-68
        unchecked { for (uint256 i; i < amountOfRoots; ++i) { _addInteropRoot(interopRootsInput[i]. …); } }
    }
    function _addInteropRoot(uint256 chainId, uint256 blockOrBatchNumber, uint256 timestamp,
                             bytes32[] calldata sides) private {                   // :70-103
        if (sides.length != 1) revert SidesLengthNotOne();                         // :77-79
        if (sides[0] == bytes32(0)) revert MessageRootIsZero();                    // :80-82
        if (timestamp == 0) revert InteropRootTimestampIsZero();                   // :85-87
        if (storedInteropRoots[chainId][blockOrBatchNumber].root != bytes32(0))
            revert InteropRootAlreadyExists();                                     // :89-91
        storedInteropRoots[chainId][blockOrBatchNumber] =
            StoredInteropRoot({root: sides[0], timestamp: timestamp});             // :93
        if (timestamp > latestInteropRootTimestamp[chainId])
            latestInteropRootTimestamp[chainId] = timestamp;                       // :98-100
        emit InteropRootAdded(chainId, blockOrBatchNumber, timestamp, sides);      // :102
    }

`InteropRoot` and `StoredInteropRoot` are `common/Messaging.sol:147-154` and `:161-164`;
`L2_BOOTLOADER_ADDRESS = address(SYSTEM_CONTRACTS_OFFSET + 0x01)` with
`SYSTEM_CONTRACTS_OFFSET = 0x8000` (`common/l2-helpers/L2ContractAddresses.sol:6`, `:41`).  The
interface's claims about the two views are `interop/IL2InteropRootStorage.sol:16-27`.

## What is modelled

* The whole storage: both mappings, as total functions (an unset slot reads as zero).
* Both writers, with every guard in source order.  A revert is `none`: no state.
  `addInteropRootsInBatch` is all-or-nothing, as one transaction is (`addRoots`).
* The view `interopRoots`; the public getter `latestInteropRootTimestamp` is the field itself.
* Runs: `Step` is one successful external call by any caller, with any arguments; `Reach` is any
  finite sequence of them.  `ReachLog` is `Reach` with every successful call written down
  (caller and arguments), oldest first.
* Four *mutants* (`addInteropRootNoExistsCheck`, `…NoZeroRootCheck`, `…NoZeroTimestampCheck`,
  `addSingleNoAuth`): the source with ONE check deleted.  They are not the contract; the
  countermodels in the Properties file use them to show each check is load-bearing.

## What is not modelled (`MODEL-ROOT-STORAGE` in `ASSUMPTIONS.md`)

* The `InteropRootAdded` event.  The logged run (`ReachLog`) records the same data per call.
* Who the bootloader is and what it imports: `msg.sender` and the imported tuples are inputs.
  That an imported tuple is the settlement layer's `MessageRoot.historicalRoot` (checked when the
  importing batch executes, `ExecutorFacet._verifyDependencyInteropRoots`) is a protocol fact
  outside this contract.
* The storage the contract starts with.  The source comment at `:29-31` says the mapping was
  empty at the v31 upgrade; `empty` is that state, and the results that need it say so.  At
  `03634a64b` ("Set of patches for draft-v31") the mapping's value was a plain `bytes32`; a root
  stored under that layout would read here as that root with timestamp zero, the struct's second
  word being a slot that layout did not write.  `LegacyRootBreaksZeroTimestampClaim` shows what
  such a start state breaks.
* Replacement of the contract's code by a protocol upgrade (`OPS-CONFIG`): runs are runs of this
  code.
* Calldata decoding (`SOL-ABI`), the array-length word of the batch (a `List` has no `2^256`
  bound), gas, and the `unchecked { ++i }` overflow (unreachable below `2^256` elements).
* `msg.sender` is a word, not a 160-bit address: callers that cannot exist only add rejected calls.
-/

namespace Contracts.InteropRootStorage

/-- An `address`, as a word. -/
abbrev Address := UInt256

/-- `L2_BOOTLOADER_ADDRESS = address(SYSTEM_CONTRACTS_OFFSET + 0x01)`
(`common/l2-helpers/L2ContractAddresses.sol:41`, with `SYSTEM_CONTRACTS_OFFSET = 0x8000`, `:6`). -/
def L2_BOOTLOADER_ADDRESS : Address := 0x8001

/-- `StoredInteropRoot` (`common/Messaging.sol:161-164`). -/
structure StoredInteropRoot where
  /-- `bytes32 root`. -/
  root : UInt256
  /-- `uint256 timestamp`. -/
  timestamp : UInt256
  deriving DecidableEq

/-- `InteropRoot` (`common/Messaging.sol:147-154`), the calldata argument of both writers. -/
structure InteropRoot where
  /-- `uint256 chainId`. -/
  chainId : UInt256
  /-- `uint256 blockOrBatchNumber`. -/
  blockOrBatchNumber : UInt256
  /-- `uint256 timestamp`. -/
  timestamp : UInt256
  /-- `bytes32[] sides`. -/
  sides : List UInt256
  deriving DecidableEq

/-- The contract's storage (`L2InteropRootStorage.sol:32`, `:36`). -/
structure State where
  /-- `storedInteropRoots[chainId][blockOrBatchNumber]`. -/
  storedInteropRoots : UInt256 → UInt256 → StoredInteropRoot
  /-- `latestInteropRootTimestamp[chainId]`. -/
  latestInteropRootTimestamp : UInt256 → UInt256

/-- Fresh storage: every slot zero. -/
def empty : State where
  storedInteropRoots := fun _ _ => ⟨0, 0⟩
  latestInteropRootTimestamp := fun _ => 0

/-- `interopRoots(chainId, blockOrBatchNumber)` (`:39-44`). -/
def interopRoots (S : State) (chainId blockOrBatchNumber : UInt256) : StoredInteropRoot :=
  S.storedInteropRoots chainId blockOrBatchNumber

/-- The state after lines `:93-100`, with no guard checked: the pair is stored at the key and
the chain's tracked timestamp is raised to `timestamp` if it was below it. -/
def writeRoot (S : State) (chainId blockOrBatchNumber timestamp root : UInt256) : State where
  storedInteropRoots := fun c b =>
    if c = chainId ∧ b = blockOrBatchNumber then ⟨root, timestamp⟩ else S.storedInteropRoots c b
  latestInteropRootTimestamp := fun c =>
    if c = chainId ∧ S.latestInteropRootTimestamp chainId < timestamp then timestamp
    else S.latestInteropRootTimestamp c

/-- `_addInteropRoot` (`:70-103`), guards in source order; `none` is a revert.
`sides.headD 0` is `sides[0]`, read only after the length check. -/
def addInteropRoot (S : State) (chainId blockOrBatchNumber timestamp : UInt256)
    (sides : List UInt256) : Option State :=
  if sides.length ≠ 1 then none                                                     -- :77 SidesLengthNotOne
  else if sides.headD 0 = 0 then none                                               -- :80 MessageRootIsZero
  else if timestamp = 0 then none                                                   -- :85 InteropRootTimestampIsZero
  else if (S.storedInteropRoots chainId blockOrBatchNumber).root ≠ 0 then none      -- :89 InteropRootAlreadyExists
  else some (writeRoot S chainId blockOrBatchNumber timestamp (sides.headD 0))      -- :93-100

/-- `_addInteropRoot` applied to one `InteropRoot` struct. -/
def addRoot (S : State) (r : InteropRoot) : Option State :=
  addInteropRoot S r.chainId r.blockOrBatchNumber r.timestamp r.sides

/-- The loop of `addInteropRootsInBatch` (`:59-66`): the roots in order, the whole call
reverting if any one does. -/
def addRoots (S : State) : List InteropRoot → Option State
  | [] => some S
  | r :: rs =>
    match addRoot S r with
    | none => none
    | some S' => addRoots S' rs

/-- `addSingleInteropRoot` (`:50-52`), called by `caller`. -/
def addSingleInteropRoot (S : State) (caller : Address) (r : InteropRoot) : Option State :=
  if caller ≠ L2_BOOTLOADER_ADDRESS then none                                       -- :21 Unauthorized
  else addRoot S r

/-- `addInteropRootsInBatch` (`:56-68`), called by `caller`. -/
def addInteropRootsInBatch (S : State) (caller : Address) (rs : List InteropRoot) : Option State :=
  if caller ≠ L2_BOOTLOADER_ADDRESS then none                                       -- :21 Unauthorized
  else addRoots S rs

/-! ## Runs -/

/-- A state-changing external call: the contract has exactly these two. -/
inductive Call where
  /-- `addSingleInteropRoot(interopRoot)`. -/
  | single (r : InteropRoot)
  /-- `addInteropRootsInBatch(interopRootsInput)`. -/
  | batch (rs : List InteropRoot)

/-- The `InteropRoot` structs a call asks to import, in order. -/
def Call.roots : Call → List InteropRoot
  | .single r => [r]
  | .batch rs => rs

/-- One external call by `caller`; `none` is a revert. -/
def exec (S : State) (caller : Address) : Call → Option State
  | .single r => addSingleInteropRoot S caller r
  | .batch rs => addInteropRootsInBatch S caller rs

/-- One successful call, by anyone, with any arguments. -/
inductive Step : State → State → Prop
  | call {S S' : State} (caller : Address) (c : Call) : exec S caller c = some S' → Step S S'

/-- Any finite sequence of successful calls. -/
inductive Reach : State → State → Prop
  | refl {S : State} : Reach S S
  | tail {S T U : State} : Reach S T → Step T U → Reach S U

/-- `Reach` with every successful call logged (caller and arguments), oldest first. -/
inductive ReachLog : State → State → List (Address × Call) → Prop
  | refl {S : State} : ReachLog S S []
  | tail {S T U : State} {log : List (Address × Call)} (caller : Address) (c : Call) :
      ReachLog S T log → exec T caller c = some U → ReachLog S U (log ++ [(caller, c)])

/-- Every `InteropRoot` the logged calls imported, oldest first (a batch contributes its
elements in order). -/
def imports (log : List (Address × Call)) : List InteropRoot :=
  log.flatMap (fun p => p.2.roots)

/-- The storage key of an import: `(chainId, blockOrBatchNumber)`. -/
def InteropRoot.key (r : InteropRoot) : UInt256 × UInt256 := (r.chainId, r.blockOrBatchNumber)

/-- The pair an accepted import stores: `(sides[0], timestamp)`. -/
def InteropRoot.stored (r : InteropRoot) : StoredInteropRoot := ⟨r.sides.headD 0, r.timestamp⟩

/-! ## The interface's claims, as predicates on a state -/

/-- The interface's claim about `interopRoots` (`IL2InteropRootStorage.sol:18-20`, restated at
`L2InteropRootStorage.sol:83-84`): "a zero stored timestamp only ever means nothing imported at
this key".  Read here as: at every key the root is zero exactly when the timestamp is. -/
def ZeroTimestampIffUnset (S : State) : Prop :=
  ∀ c b, (S.storedInteropRoots c b).root = 0 ↔ (S.storedInteropRoots c b).timestamp = 0

/-- The interface's claim about `latestInteropRootTimestamp` (`IL2InteropRootStorage.sol:23-26`):
"the maximum creation timestamp over all roots imported for `chainId` (zero if none was
imported yet)".  Read here as: it bounds every stored timestamp of the chain, and if nonzero it
is the timestamp stored at some key of the chain holding a nonzero root. -/
def LatestIsMax (S : State) : Prop :=
  (∀ c b, (S.storedInteropRoots c b).timestamp ≤ S.latestInteropRootTimestamp c) ∧
  (∀ c, S.latestInteropRootTimestamp c ≠ 0 →
    ∃ b, (S.storedInteropRoots c b).root ≠ 0 ∧
      (S.storedInteropRoots c b).timestamp = S.latestInteropRootTimestamp c)

/-! ## Mutants: the source with one check deleted (for countermodels only) -/

/-- `_addInteropRoot` with the `InteropRootAlreadyExists` check (`:89-91`) deleted. -/
def addInteropRootNoExistsCheck (S : State) (chainId blockOrBatchNumber timestamp : UInt256)
    (sides : List UInt256) : Option State :=
  if sides.length ≠ 1 then none
  else if sides.headD 0 = 0 then none
  else if timestamp = 0 then none
  else some (writeRoot S chainId blockOrBatchNumber timestamp (sides.headD 0))

/-- `_addInteropRoot` with the `MessageRootIsZero` check (`:80-82`) deleted. -/
def addInteropRootNoZeroRootCheck (S : State) (chainId blockOrBatchNumber timestamp : UInt256)
    (sides : List UInt256) : Option State :=
  if sides.length ≠ 1 then none
  else if timestamp = 0 then none
  else if (S.storedInteropRoots chainId blockOrBatchNumber).root ≠ 0 then none
  else some (writeRoot S chainId blockOrBatchNumber timestamp (sides.headD 0))

/-- `_addInteropRoot` with the `InteropRootTimestampIsZero` check (`:85-87`) deleted. -/
def addInteropRootNoZeroTimestampCheck (S : State) (chainId blockOrBatchNumber timestamp : UInt256)
    (sides : List UInt256) : Option State :=
  if sides.length ≠ 1 then none
  else if sides.headD 0 = 0 then none
  else if (S.storedInteropRoots chainId blockOrBatchNumber).root ≠ 0 then none
  else some (writeRoot S chainId blockOrBatchNumber timestamp (sides.headD 0))

/-- `addSingleInteropRoot` with the `onlyCallFromBootloader` modifier (`:20-25`) deleted:
the caller is not read. -/
def addSingleNoAuth (S : State) (_caller : Address) (r : InteropRoot) : Option State :=
  addRoot S r

/-! ## The contract at `c67894b9`

`interop/L2InteropRootStorage.sol` at `c67894b970a0dac6fe9144d8ebf4b0806e15a9af` (107 lines): the
storage is `storedInteropRoots` alone (`:40`); the modifier is `:20-25`, `addSingleInteropRoot`
`:58-60`, `addInteropRootsInBatch` `:64-76`, and `_addInteropRoot` (`:78-106`) has the same four
checks in the same order (`:85-87`, `:88-90`, `:93-95`, `:98-100`) and the same write (`:103`),
with no `latestInteropRootTimestamp` update.  Apart from comments and the `Unauthorized` import,
that is the only difference from the code above. -/

/-- The storage at `c67894b9`: `storedInteropRoots` (`:40` there). -/
abbrev RootsAtC67 := UInt256 → UInt256 → StoredInteropRoot

/-- `_addInteropRoot` at `c67894b9` (`:78-106` there); `none` is a revert. -/
def addInteropRootAtC67 (R : RootsAtC67) (chainId blockOrBatchNumber timestamp : UInt256)
    (sides : List UInt256) : Option RootsAtC67 :=
  if sides.length ≠ 1 then none                                                     -- :85 SidesLengthNotOne
  else if sides.headD 0 = 0 then none                                               -- :88 MessageRootIsZero
  else if timestamp = 0 then none                                                   -- :93 InteropRootTimestampIsZero
  else if (R chainId blockOrBatchNumber).root ≠ 0 then none                         -- :98 InteropRootAlreadyExists
  else some (fun c b =>                                                             -- :103
    if c = chainId ∧ b = blockOrBatchNumber then ⟨sides.headD 0, timestamp⟩ else R c b)

/-- The loop of `addInteropRootsInBatch` at `c67894b9` (`:67-74` there), all or nothing; a single
import is the one-element case. -/
def addRootsAtC67 (R : RootsAtC67) : List InteropRoot → Option RootsAtC67
  | [] => some R
  | r :: rs =>
    match addInteropRootAtC67 R r.chainId r.blockOrBatchNumber r.timestamp r.sides with
    | none => none
    | some R' => addRootsAtC67 R' rs

/-- Either writer at `c67894b9`, called by `caller`: the modifier (`:20-25`), then
`_addInteropRoot` on the call's roots in order. -/
def execAtC67 (R : RootsAtC67) (caller : Address) (c : Call) : Option RootsAtC67 :=
  if caller ≠ L2_BOOTLOADER_ADDRESS then none else addRootsAtC67 R c.roots

/-- Any finite sequence of successful calls of the `c67894b9` contract. -/
inductive ReachAtC67 : RootsAtC67 → RootsAtC67 → Prop
  | refl {R : RootsAtC67} : ReachAtC67 R R
  | tail {R T U : RootsAtC67} (caller : Address) (c : Call) :
      ReachAtC67 R T → execAtC67 T caller c = some U → ReachAtC67 R U

end Contracts.InteropRootStorage
