import Mathlib.Tactic
import EraSpec.Contracts.AssetRouterBase.Specs.HandlerRegistration

/-!
# Model: every writer of the router's two mappings

Source: era-contracts `draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`.
Paths are relative to `l1-contracts/contracts/`; `bridge/asset-router/` is shortened to
`AR/` and `bridge/ntv/` to `NTV/`.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.AssetRouterBase.Properties.AllWriters` and are proved in
`EraSpec.Contracts.AssetRouterBase.Proofs.AllWriters`.

## Why this file exists

`HandlerRegistration` models one writer, `_setAssetHandlerAddressThisChain`, and proves
`RunValid` ("a live route has an accountable tracker") for runs of that writer alone.
The deployed routers have more writers.  This file adds every other write to
`assetHandlerAddress` and `assetDeploymentTracker`, so that `RunValid` can be
tested against the deployed routers and the invariant that does hold can be stated.

## The writers

A grep of `_setAssetHandler(` and `assetDeploymentTracker[` over the whole `b17415d20` tree
(tests excluded) finds these, all in `AR/` (no other contract inherits from either router):

| `Op` | Source | Router | Writes | Who can call |
|---|---|---|---|---|
| `register` | `_setAssetHandlerAddressThisChain`, `AR/AssetRouterBase.sol:65-77` | both | handler := `h` and tracker := caller, at an id hashed from the caller | the vault, or the id's recorded tracker (:73) |
| `finalize` | `_finalizeDeposit`'s `else` branch, `AR/AssetRouterBase.sol:277-282` | both | handler := vault, at the deposit's id, only if unset | whoever may call `finalizeDeposit` (below) |
| `seed` | L1 `setNativeTokenVault`, `AR/L1AssetRouter.sol:116-121` (write :120); L2 `initL2`, `AR/L2AssetRouter.sol:154-163` (write :162) | both | handler := vault, at `ETH_TOKEN_ASSET_ID` (L1) / `_baseTokenAssetId` (L2) | L1 owner; L2 complex upgrader |
| `counterpartSet` | `setAssetHandlerAddress`, `AR/L2AssetRouter.sol:198-204` | L2 | handler := any `h` (zero included), at any id | the aliased L1 asset router (`onlyAssetRouterCounterpart`, :96-107) |
| `setTracker` | `setAssetDeploymentTracker`, `AR/L1AssetRouter.sol:135-142` | L1 | tracker := `t`, at `encodeAssetId(block.chainid, d, t)` | owner |

The quoted bodies:

    // AR/AssetRouterBase.sol:273-282                     (_finalizeDeposit)
    address assetHandler = assetHandlerAddress[_assetId];
    if (assetHandler != address(0)) {
        IAssetHandler(assetHandler).bridgeMint{value: msg.value}(_sourceChainId, _assetId, _transferData);
    } else {
        _setAssetHandler(_assetId, _nativeTokenVault);
        ... IAssetHandler(_nativeTokenVault).bridgeMint{value: msg.value}(_sourceChainId, _assetId, _transferData);
    }

    // AR/L2AssetRouter.sol:198-204
    function setAssetHandlerAddress(uint256 _sourceChainId, bytes32 _assetId, address _assetHandlerAddress)
        external override onlyAssetRouterCounterpart(_sourceChainId) {
        _setAssetHandler(_assetId, _assetHandlerAddress);
    }

    // AR/L1AssetRouter.sol:135-142
    function setAssetDeploymentTracker(bytes32 _assetRegistrationData, address _assetDeploymentTracker)
        external onlyOwner {
        bytes32 assetId = DataEncoding.encodeAssetId(block.chainid, _assetRegistrationData, _assetDeploymentTracker);
        assetDeploymentTracker[assetId] = _assetDeploymentTracker;
        ...
    }

    // AR/L1AssetRouter.sol:120 and AR/L2AssetRouter.sol:162
    _setAssetHandler(ETH_TOKEN_ASSET_ID, address(_nativeTokenVault));
    _setAssetHandler(_baseTokenAssetId, L2_NATIVE_TOKEN_VAULT_ADDR);

Only `register` writes the tracker alongside the handler.  `finalize`, `seed` and
`counterpartSet` write the handler and leave the tracker as it was, so after any of
them a live route can have tracker zero.  `finalize` is the common case: the first
deposit of every token the destination has not seen takes it.

`_burn` (`AR/AssetRouterBase.sol:303-331`) is not a writer: when the handler is unset it
calls the vault's `tryRegisterTokenFromBurnData` (`NTV/NativeTokenVaultBase.sol:321-335`), which
registers through `_registerToken` and `_unsafeRegisterNativeToken`, that is through
`setAssetHandlerAddressThisChain` with the vault as caller (`NTV/NativeTokenVaultBase.sol:492-499`),
which is a `register` step.  The comment at `AR/AssetRouterBase.sol:319` says so.

## Who reaches `_finalizeDeposit`

`L2AssetRouter.finalizeDeposit` (`AR/L2AssetRouter.sol:253-262`) admits the aliased L1
asset router or the router itself (`onlyAssetRouterCounterpartOrSelf`, :111-126; the interop
self-call from `receiveMessage`, `AR/AssetRouterBase.sol:213-251`), and rejects
`BASE_TOKEN_ASSET_ID` (:258).  `L1AssetRouter.finalizeDeposit` (`AR/L1AssetRouter.sol:291-299`)
admits only the self-call, and first runs the v35 handler gate `_checkAssetHandlerAllowed`
(:276-288), which lets an unset handler through, so it never stops the fallback; it can only
remove runs (`HandlerGateAtV35` models it).  The model does not track callers for `finalize`: the fallback's write does
not depend on who called, and admitting every caller only adds runs.  The L2
base-token check is kept, as `finalize`'s side condition.

## What the fallback relies on from the vault

The fallback's write survives only if the vault's `bridgeMint` succeeds; otherwise the
whole call reverts (`VM-REVERT`), which the model represents as the absence of a step.
`Cfg.ntvMints` is the set of ids for which that `bridgeMint` can succeed, in some vault
state.  The property file assumes (as `MintsOnlyNtvIds`) that every such id is a vault
id, `encodeNTVAssetId(c, t) = encodeAssetId(c, t, L2_NATIVE_TOKEN_VAULT_ADDR)`
(`common/libraries/DataEncoding.sol:125-127, 150-152`).  The reason:

* `bridgeMint` → `_bridgeMintToken` (`NTV/NativeTokenVaultBase.sol:180-189, 220-247`).  An id
  the vault has not seen has `originChainId = 0 ≠ block.chainid` and `tokenAddress = 0`,
  so it takes `_ensureAndSaveTokenDeployed` (:233-235), whose `assetIdCheck` (:557;
  `DataEncoding.sol:207-213`) reverts unless the id is `encodeNTVAssetId(origin, originToken)`.
* An id the vault has seen was written by `_setNewTokenStorage` (:565-575), from
  `_unsafeRegisterNativeToken` (id `encodeNTVAssetId(block.chainid, token)`, :493) or from
  `_ensureAndSaveTokenDeployedInner` (checked at :557).  The one other registry write,
  `L2NativeTokenVault.updateL2`'s base-token entry (`NTV/L2NativeTokenVault.sol:165-167`),
  is unchecked, but `L2AssetRouter.finalizeDeposit` rejects that id (:258), given that the
  router's and the vault's `BASE_TOKEN_ASSET_ID` slots hold the same value (both written by
  the upgrader's `updateL2`; `OPS-CONFIG`).  This is the
  `idShape` field of `Contracts.NativeTokenVault.Valid` (`Specs/RegistryAndEscrow.lean`).
  The `VaultMintGate` topic proves that field along every vault run with no hash premise,
  and derives `MintsOnlyNtvIds` from it.

It also relies on the vault's `bridgeMint` not writing router storage (`DEP-FRAME`): the
vault calls the router only from registration, which is a separate `register` step.

## The other boundaries

* **The counterpart is trusted.**  On L2, `setAssetHandlerAddress` can point any id at
  any handler.  Its only check on L2 is the caller.  On L1 the message is built by
  `_setAssetHandlerAddressOnCounterpart` (`AR/L1AssetRouter.sol:158-183`), which asks the
  id's L1 tracker to approve (:164-170; the vault approves only
  `L2_NATIVE_TOKEN_VAULT_ADDR`, `NTV/L1NativeTokenVault.sol:313-320`).  This model's L2
  step does not see that check.  The `CounterpartGate` topic models it and narrows the
  exception to ids that are not vault triples' ids.
* **The seeded id.**  On L1 it is `ETH_TOKEN_ASSET_ID = encodeNTVAssetId(block.chainid,
  ETH_TOKEN_ADDRESS)` (`AR/L1AssetRouter.sol:101`), a vault id by construction.  On L2 it
  is the upgrader's `_baseTokenAssetId`; that it is a vault id is a premise on the
  upgrade's input (`OPS-CONFIG`).
* **One-shot initializers are repeatable here.**  `seed` may fire any number of times
  (`setNativeTokenVault` requires an unset vault, `AR/L1AssetRouter.sol:117`; `initL2` is an
  initializer).  That only adds runs.
* **The vault address is fixed.**  On L2 it is the constant `L2_NATIVE_TOKEN_VAULT_ADDR`,
  so `ntv = ntvAddr`.  On L1, `nativeTokenVault` is zero until `setNativeTokenVault`
  sets it once (:117-119).  Before that the L1 router is this model with `ntv = 0`
  (`senderIsNTV` is then always false, and `bridgeMint` on address zero reverts).
  `WeakValid` at `ntv = 0` implies `WeakValid` at any vault address
  (`Contracts.AssetRouter.AllWriters.Properties.WeakValidAtZeroVault`), so the invariant
  carries across that switch.
* **Router upgrades are out of scope.**  A new router implementation could rewrite both
  mappings (`OPS-CONFIG`).
* **Not modelled:** events, `msg.value`, pause, reentrancy guards, the live branch of
  `_finalizeDeposit` (it writes no router storage), and the vault's own state.
-/

namespace Contracts.AssetRouter.AllWriters

/-! ## Configuration -/

/-- Which deployed router.  Both inherit `AssetRouterBase`, and each adds its own
writers. -/
inductive Side where
  /-- `L1AssetRouter`: adds `setNativeTokenVault` and `setAssetDeploymentTracker`. -/
  | l1
  /-- `L2AssetRouter`: adds `initL2` and `setAssetHandlerAddress`. -/
  | l2
  deriving DecidableEq

/-- One deployed router's fixed configuration, and the one thing it relies on from the
vault. -/
structure Cfg where
  /-- `DataEncoding.encodeAssetId(chainId, assetData, sender)`, as in
  `HandlerRegistration`. -/
  enc : AssetIdOf
  /-- `block.chainid`. -/
  thisChain : Chain
  /-- The router's native token vault: the constant `L2_NATIVE_TOKEN_VAULT_ADDR` on L2
  (`_getNativeTokenVaultAddr`, `AR/L2AssetRouter.sol:79-81`), the stored `nativeTokenVault`
  on L1 (`AR/L1AssetRouter.sol:59`). -/
  ntv : Address
  /-- `L2_NATIVE_TOKEN_VAULT_ADDR`, the sender every vault id is hashed from
  (`common/l2-helpers/L2ContractAddresses.sol:89`, `0x10004`). -/
  ntvAddr : Address
  /-- Which router this is. -/
  side : Side
  /-- The id the initializer points at the vault: `ETH_TOKEN_ASSET_ID` on L1
  (`AR/L1AssetRouter.sol:101`), `_baseTokenAssetId` on L2, which `updateL2` also stores
  as `BASE_TOKEN_ASSET_ID` (`AR/L2AssetRouter.sol:162, 182`). -/
  seedId : AssetId
  /-- The ids for which the vault's `bridgeMint`, called from the fallback, can succeed
  in some vault state.  See the header for why the properties may assume these are
  vault ids. -/
  ntvMints : AssetId → Prop

/-! ## Operations -/

/-- One call that writes router storage, with its arguments. -/
inductive Op where
  /-- `setAssetHandlerAddressThisChain(d, h)` called by `caller`. -/
  | register (caller : Address) (d : AssetData) (h : Address)
  /-- `finalizeDeposit` for asset `a`, taking the unset-handler branch. -/
  | finalize (a : AssetId)
  /-- The initializer's write: `setNativeTokenVault` on L1, `initL2` on L2. -/
  | seed
  /-- `L2AssetRouter.setAssetHandlerAddress(_, a, h)` by the L1 counterpart. -/
  | counterpartSet (a : AssetId) (h : Address)
  /-- `L1AssetRouter.setAssetDeploymentTracker(d, t)` by the owner. -/
  | setTracker (d : AssetData) (t : Address)

/-- `_setAssetHandler(a, h)` alone (`AR/AssetRouterBase.sol:289-292`): the handler moves,
the tracker does not. -/
def pointAt (R : Router) (a : AssetId) (h : Address) : Router :=
  { R with handler := upd R.handler a h }

/-- `setAssetDeploymentTracker(d, t)`'s write (`AR/L1AssetRouter.sol:139-140`): the
tracker of the id hashed from `t` itself becomes `t`.  No zero check on `t`. -/
def recordTracker (K : Cfg) (R : Router) (d : AssetData) (t : Address) : Router :=
  { R with tracker := upd R.tracker (K.enc K.thisChain t d) t }

/-- One successful call.  A revert is the absence of a step. -/
inductive AStep (K : Cfg) : Op → Router → Router → Prop
  /-- The modelled writer of `HandlerRegistration`, with its guard. -/
  | register {R : Router} {caller : Address} {d : AssetData} {h : Address} :
      SetGuard K.enc K.thisChain K.ntv K.ntvAddr R caller d →
      AStep K (.register caller d h) R (setHandler K.enc K.thisChain K.ntv K.ntvAddr R caller d h)
  /-- The fallback: the handler was unset (:275), the vault's `bridgeMint` succeeded,
  and on L2 the id is not the base token (`AR/L2AssetRouter.sol:258`). -/
  | finalize {R : Router} {a : AssetId} :
      R.handler a = 0 → K.ntvMints a → (K.side = .l2 → a ≠ K.seedId) →
      AStep K (.finalize a) R (pointAt R a K.ntv)
  /-- The initializer's route to the vault. -/
  | seed {R : Router} : AStep K .seed R (pointAt R K.seedId K.ntv)
  /-- The counterpart's write: L2 only, any id, any handler. -/
  | counterpartSet {R : Router} {a : AssetId} {h : Address} : K.side = .l2 →
      AStep K (.counterpartSet a h) R (pointAt R a h)
  /-- The owner's tracker write: L1 only. -/
  | setTracker {R : Router} {d : AssetData} {t : Address} : K.side = .l1 →
      AStep K (.setTracker d t) R (recordTracker K R d t)

/-- A run with every call logged, oldest first. -/
inductive ARun (K : Cfg) : Router → List Op → Router → Prop
  | nil {R : Router} : ARun K R [] R
  | snoc {R S T : Router} {ops : List Op} {op : Op} :
      ARun K R ops S → AStep K op S T → ARun K R (ops ++ [op]) T

/-! ## Vault ids, and the weakened invariant -/

/-- `a` is a vault id: `encodeNTVAssetId(c, d) = encodeAssetId(c, d,
L2_NATIVE_TOKEN_VAULT_ADDR)` for some chain `c` and token `d`
(`common/libraries/DataEncoding.sol:125-127, 150-152`).  The chain is the token's
origin chain, not necessarily this one.

This is existential.  For a keccak-like encoding over full 256-bit words, nearly every
id has some vault preimage, so the condition is weak.  The informative part of
`VaultRoute` is its handler conjunct.  Where a specific preimage matters, results name
it: a registration's triple, or a vault triple `q` given as an argument
(`NoHijackOnExceptCounterpart`, the `CounterpartGate` topic).  The vault's own record
of each id's preimage is `VaultMintGate.VaultRunIdShape`. -/
def IsNtvId (enc : AssetIdOf) (ntvAddr : Address) (a : AssetId) : Prop :=
  ∃ (c : Chain) (d : AssetData), a = enc c ntvAddr d

/-- The vault's behaviour the fallback relies on: the vault's `bridgeMint` succeeds only
for vault ids.  See the header. -/
def MintsOnlyNtvIds (K : Cfg) : Prop :=
  ∀ a, K.ntvMints a → IsNtvId K.enc K.ntvAddr a

/-- A vault route: the id is a vault id and its handler is the vault. -/
def VaultRoute (K : Cfg) (R : Router) (a : AssetId) : Prop :=
  R.handler a = K.ntv ∧ IsNtvId K.enc K.ntvAddr a

/-- **The weakened invariant.**  Every live route has a nonzero tracker, or is a vault
route.  `HandlerRegistration.Valid` is the first disjunct alone. -/
def WeakValid (K : Cfg) (R : Router) : Prop :=
  ∀ a, R.handler a ≠ 0 → R.tracker a ≠ 0 ∨ VaultRoute K R a

/-- Every recorded tracker sits at an id that has a preimage, on this chain, whose sender
is that tracker itself, or (for the vault, which is normalised before hashing)
`L2_NATIVE_TOKEN_VAULT_ADDR`.

Like `IsNtvId`, this is existential in the data word, and the word is not tied to any call.
An encoding that reaches every id as the data word varies satisfies it in every router
state, reachable or not (`AllWritersStrong.TrackerHashedAdmitsUnreachableRouter`).  For a
keccak-like encoding, heuristically about `1 - 1/e` of all ids have such a preimage for any
fixed tracker.  It also does not exclude that an id with such a preimage is hashed from
someone else as well.  The pinned form, which names the logged call that recorded each
tracker, is `TrackerRecorded` (`Specs/AllWritersStrong.lean`). -/
def TrackerHashed (K : Cfg) (R : Router) : Prop :=
  ∀ a, R.tracker a ≠ 0 →
    ∃ d : AssetData, a = K.enc K.thisChain (R.tracker a) d
      ∨ (R.tracker a = K.ntv ∧ a = K.enc K.thisChain K.ntvAddr d)

/-! ## Classifying operations -/

/-- The counterpart's write, the trusted exception. -/
def Op.IsCounterpart : Op → Prop
  | .counterpartSet _ _ => True
  | _ => False

/-- An owner tracker write naming the zero tracker.  It writes zero at
`encodeAssetId(block.chainid, d, address(0))`, an id no registration can write
without a hash collision. -/
def Op.ZeroTracker : Op → Prop
  | .setTracker _ t => t = 0
  | _ => False

/-- The one id whose handler a call may write: the registration's derived id, the
deposit's id, the seeded id, or the counterpart's argument.  A tracker write moves no
handler. -/
def Op.target (K : Cfg) : Op → Option AssetId
  | .register caller d _ => some (writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d)
  | .finalize a => some a
  | .seed => some K.seedId
  | .counterpartSet a _ => some a
  | .setTracker _ _ => none

/-- The (chain, sender, data) triples a call's written id is hashed from.  A
registration hashes exactly `(block.chainid, normalised caller, d)`, and a tracker
write `(block.chainid, t, d)`.  The fallback and the seed are given an id, not a
triple; their triples are the vault triples that hash to that id.  The counterpart's
id is hashed from nothing. -/
def Op.HashedFrom (K : Cfg) : Op → Chain × Address × AssetData → Prop
  | .register caller d _, p => p = (K.thisChain, senderOf K.ntv K.ntvAddr caller, d)
  | .finalize a, p => p.2.1 = K.ntvAddr ∧ a = K.enc p.1 p.2.1 p.2.2
  | .seed, p => p.2.1 = K.ntvAddr ∧ K.seedId = K.enc p.1 p.2.1 p.2.2
  | .counterpartSet _ _, _ => False
  | .setTracker d t, p => p = (K.thisChain, t, d)

/-! ## Logged triples

The triples a run's registrations and tracker writes hash, for the run-local hash
premise.  The fallback, the seed and the counterpart hash nothing (their id is given). -/

/-- The triple a call feeds to `encodeAssetId`, if any. -/
def Op.triple (K : Cfg) : Op → Option (Chain × Address × AssetData)
  | .register caller d _ => some (K.thisChain, senderOf K.ntv K.ntvAddr caller, d)
  | .setTracker d t => some (K.thisChain, t, d)
  | _ => none

/-- **The triples a logged run hashes**, at most one per call. -/
def loggedTriples (K : Cfg) (ops : List Op) : Finset (Chain × Address × AssetData) :=
  (ops.filterMap (Op.triple K)).toFinset

end Contracts.AssetRouter.AllWriters
