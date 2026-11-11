import Mathlib.Tactic
import EraSpec.Contracts.AssetRouterBase.Specs.HandlerRegistration

/-!
# Model: every writer of the router's two mappings at the pin

Source: the pinned era-contracts tree (`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`).
Paths are relative to `l1-contracts/contracts/`; `bridge/asset-router/` is shortened to
`AR/` and `bridge/ntv/` to `NTV/`.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.AssetRouterBase.Properties.AllWriters` and are proved in
`EraSpec.Contracts.AssetRouterBase.Proofs.AllWriters`.

## Why this file exists

`HandlerRegistration` models one writer, `_setAssetHandlerAddressThisChain`, and proves
`RunValid` ("a live route has an accountable tracker") for runs of that writer alone.
The deployed routers have more writers.  This file adds every other write to
`assetHandlerAddress` and `assetDeploymentTracker` at the pin, so that `RunValid` can be
tested against the deployed routers and the invariant that does hold can be stated.

## The writers

A grep of `_setAssetHandler(` and `assetDeploymentTracker[` over the whole pinned tree
finds these, all in `AR/` (no contract inherits from either router):

| `Op` | Source | Router | Writes | Who can call |
|---|---|---|---|---|
| `register` | `_setAssetHandlerAddressThisChain`, `AR/AssetRouterBase.sol:73-85` | both | handler := `h` and tracker := caller, at an id hashed from the caller | the vault, or the id's recorded tracker (:81) |
| `finalize` | `_finalizeDeposit`'s `else` branch, `AR/AssetRouterBase.sol:285-291` | both | handler := vault, at the deposit's id, only if unset | whoever may call `finalizeDeposit` (below) |
| `seed` | L1 `setNativeTokenVault`, `AR/L1AssetRouter.sol:140-145` (write :144); L2 `initL2`, `AR/L2AssetRouter.sol:157-168` (write :167) | both | handler := vault, at `ETH_TOKEN_ASSET_ID` (L1) / `_baseTokenAssetId` (L2) | L1 owner; L2 complex upgrader |
| `counterpartSet` | `setAssetHandlerAddress`, `AR/L2AssetRouter.sol:200-206` | L2 | handler := any `h` (zero included), at any id | the aliased L1 asset router (`onlyAssetRouterCounterpart`, :91-102) |
| `setTracker` | `setAssetDeploymentTracker`, `AR/L1AssetRouter.sol:159-166` | L1 | tracker := `t`, at `encodeAssetId(block.chainid, d, t)` | owner |

The quoted bodies:

    // AR/AssetRouterBase.sol:281-291                     (_finalizeDeposit)
    address assetHandler = assetHandlerAddress[_assetId];
    if (assetHandler != address(0)) {
        IAssetHandler(assetHandler).bridgeMint{value: msg.value}(_sourceChainId, _assetId, _transferData);
    } else {
        _setAssetHandler(_assetId, _nativeTokenVault);
        ... IAssetHandler(_nativeTokenVault).bridgeMint{value: msg.value}(_sourceChainId, _assetId, _transferData);
    }

    // AR/L2AssetRouter.sol:200-206
    function setAssetHandlerAddress(uint256 _sourceChainId, bytes32 _assetId, address _assetHandlerAddress)
        external override onlyAssetRouterCounterpart(_sourceChainId) {
        _setAssetHandler(_assetId, _assetHandlerAddress);
    }

    // AR/L1AssetRouter.sol:159-166
    function setAssetDeploymentTracker(bytes32 _assetRegistrationData, address _assetDeploymentTracker)
        external onlyOwner {
        bytes32 assetId = DataEncoding.encodeAssetId(block.chainid, _assetRegistrationData, _assetDeploymentTracker);
        assetDeploymentTracker[assetId] = _assetDeploymentTracker;
        ...
    }

    // AR/L1AssetRouter.sol:144 and AR/L2AssetRouter.sol:167
    _setAssetHandler(ETH_TOKEN_ASSET_ID, address(_nativeTokenVault));
    _setAssetHandler(_baseTokenAssetId, L2_NATIVE_TOKEN_VAULT_ADDR);

Only `register` writes the tracker alongside the handler.  `finalize`, `seed` and
`counterpartSet` write the handler and leave the tracker as it was, so after any of
them a live route can have tracker zero.  `finalize` is the common case: the first
deposit of every token the destination has not seen takes it.

`_burn` (`AR/AssetRouterBase.sol:313-346`) is not a writer: when the handler is unset it
calls the vault's `tryRegisterTokenFromBurnData`, which registers through
`setAssetHandlerAddressThisChain` with the vault as caller (`NTV/NativeTokenVaultBase.sol:515-522`),
which is a `register` step.  The comment at `AR/AssetRouterBase.sol:332-333` says so.

## Who reaches `_finalizeDeposit`

`L2AssetRouter.finalizeDeposit` (`AR/L2AssetRouter.sol:265-274`) admits the aliased L1
asset router or the router itself (the interop self-call from `receiveMessage`,
`AR/AssetRouterBase.sol:215-256`), and rejects `BASE_TOKEN_ASSET_ID` (:270).
`L1AssetRouter.finalizeDeposit` (`AR/L1AssetRouter.sol:288-295`) admits only the
self-call.  The model does not track callers for `finalize`: the fallback's write does
not depend on who called, and admitting every caller only adds runs.  The L2
base-token check is kept, as `finalize`'s side condition.

## What the fallback relies on from the vault

The fallback's write survives only if the vault's `bridgeMint` succeeds; otherwise the
whole call reverts (`VM-REVERT`), which the model represents as the absence of a step.
`Cfg.ntvMints` is the set of ids for which that `bridgeMint` can succeed, in some vault
state.  The property file assumes (as `MintsOnlyNtvIds`) that every such id is a vault
id, `encodeNTVAssetId(c, t) = encodeAssetId(c, t, L2_NATIVE_TOKEN_VAULT_ADDR)`
(`common/libraries/DataEncoding.sol:126-128, 151-153`).  The reason, at the pin:

* `bridgeMint` → `_bridgeMintToken` (`NTV/NativeTokenVaultBase.sol:193-205, 240-267`).  An id
  the vault has not seen has `originChainId = 0 ≠ block.chainid` and `tokenAddress = 0`,
  so it takes `_ensureAndSaveTokenDeployed` (:253-255), whose `assetIdCheck` (:580;
  `DataEncoding.sol:208-214`) reverts unless the id is `encodeNTVAssetId(origin, originToken)`.
* An id the vault has seen was written by `_setNewTokenStorage` (:588-598), from
  `_unsafeRegisterNativeToken` (id `encodeNTVAssetId(block.chainid, token)`, :516) or from
  `_ensureAndSaveTokenDeployedInner` (checked at :580).  The one other registry write,
  `L2NativeTokenVault.updateL2`'s base-token entry (`NTV/L2NativeTokenVault.sol:170-172`),
  is unchecked, but `L2AssetRouter.finalizeDeposit` rejects that id (:270).  This is the
  `idShape` field of `Contracts.NativeTokenVault.Valid` (`Specs/RegistryAndEscrow.lean`).

It also relies on the vault's `bridgeMint` not writing router storage (`DEP-FRAME`): the
vault calls the router only from registration, which is a separate `register` step.

## The other boundaries

* **The counterpart is trusted.**  On L2, `setAssetHandlerAddress` can point any id at
  any handler.  Its only check on L2 is the caller.  On L1 the message is built by
  `_setAssetHandlerAddressOnCounterpart` (`AR/L1AssetRouter.sol:182-206`), which asks the
  id's L1 tracker to approve (:188-193; the vault approves only
  `L2_NATIVE_TOKEN_VAULT_ADDR`, `NTV/L1NativeTokenVault.sol:146-153`).  This model's L2
  step does not see that check.  The `CounterpartGate` topic models it and narrows the
  exception to ids that are not vault triples' ids.
* **The seeded id.**  On L1 it is `ETH_TOKEN_ASSET_ID = encodeNTVAssetId(block.chainid,
  ETH_TOKEN_ADDRESS)` (`AR/L1AssetRouter.sol:125`), a vault id by construction.  On L2 it
  is the upgrader's `_baseTokenAssetId`; that it is a vault id is a premise on the
  upgrade's input (`OPS-CONFIG`).
* **One-shot initializers are repeatable here.**  `seed` may fire any number of times.
  That only adds runs.
* **The vault address is fixed.**  On L2 it is the constant `L2_NATIVE_TOKEN_VAULT_ADDR`,
  so `ntv = ntvAddr`.  On L1, `nativeTokenVault` is zero until `setNativeTokenVault`
  sets it once (:141-143).  Before that the L1 router is this model with `ntv = 0`
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
  (`_nativeTokenVaultAddr`, `AR/L2AssetRouter.sol:72-74`), the stored `nativeTokenVault`
  on L1 (`AR/L1AssetRouter.sol:59`). -/
  ntv : Address
  /-- `L2_NATIVE_TOKEN_VAULT_ADDR`, the sender every vault id is hashed from
  (`common/l2-helpers/L2ContractAddresses.sol:99`, `0x10004`). -/
  ntvAddr : Address
  /-- Which router this is. -/
  side : Side
  /-- The id the initializer points at the vault: `ETH_TOKEN_ASSET_ID` on L1
  (`AR/L1AssetRouter.sol:125`), `_baseTokenAssetId` on L2, which `updateL2` also stores
  as `BASE_TOKEN_ASSET_ID` (`AR/L2AssetRouter.sol:167, 189`). -/
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

/-- `_setAssetHandler(a, h)` alone (`AR/AssetRouterBase.sol:298-301`): the handler moves,
the tracker does not. -/
def pointAt (R : Router) (a : AssetId) (h : Address) : Router :=
  { R with handler := upd R.handler a h }

/-- `setAssetDeploymentTracker(d, t)`'s write (`AR/L1AssetRouter.sol:163-164`): the
tracker of the id hashed from `t` itself becomes `t`.  No zero check on `t`. -/
def recordTracker (K : Cfg) (R : Router) (d : AssetData) (t : Address) : Router :=
  { R with tracker := upd R.tracker (K.enc K.thisChain t d) t }

/-- One successful call.  A revert is the absence of a step. -/
inductive AStep (K : Cfg) : Op → Router → Router → Prop
  /-- The modelled writer of `HandlerRegistration`, with its guard. -/
  | register {R : Router} {caller : Address} {d : AssetData} {h : Address} :
      SetGuard K.enc K.thisChain K.ntv K.ntvAddr R caller d →
      AStep K (.register caller d h) R (setHandler K.enc K.thisChain K.ntv K.ntvAddr R caller d h)
  /-- The fallback: the handler was unset (:283), the vault's `bridgeMint` succeeded,
  and on L2 the id is not the base token (`AR/L2AssetRouter.sol:270`). -/
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
(`common/libraries/DataEncoding.sol:126-128, 151-153`).  The chain is the token's
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

/-- Every recorded tracker sits at an id hashed, on this chain, from that tracker
itself, or (for the vault, which is normalised before hashing) from
`L2_NATIVE_TOKEN_VAULT_ADDR`. -/
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
