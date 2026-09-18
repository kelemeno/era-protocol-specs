import Mathlib.Tactic
import EraSpec.Word

/-!
# Model: `AssetRouter` — who may point an asset at a handler

The asset router is the routing table of the bridge: `assetHandlerAddress[assetId]`
is where funds for an asset are locked, and `_burn` / `_finalizeDeposit` send every
transfer to whatever that mapping says.  So the question worth settling is who can
write it.

**This file is definitions only.**  The results are in
`EraSpec.Properties.AssetRouter` and proved in `EraSpec.Proofs.AssetRouter`.

## The mechanism

`_setAssetHandlerAddressThisChain` is the only writer, and its shape is unusual —
the caller is folded into the *key*:

    bool senderIsNTV = msg.sender == _nativeTokenVault;
    address sender = senderIsNTV ? L2_NATIVE_TOKEN_VAULT_ADDR : msg.sender;
    bytes32 assetId = DataEncoding.encodeAssetId(block.chainid, _assetRegistrationData, sender);
    require(senderIsNTV || msg.sender == assetDeploymentTracker[assetId], Unauthorized(msg.sender));
    _setAssetHandler(assetId, _assetHandlerAddress);
    assetDeploymentTracker[assetId] = msg.sender;

with `encodeAssetId(chainId, assetData, sender) = keccak256(abi.encode(chainId, sender, assetData))`.

So there are two independent protections, and it is worth separating them:

* **The key is derived from the caller.**  A caller cannot even *name* an asset id
  that encodes somebody else — whatever registration data it supplies, the id it
  writes hashes its own address.  This is structural, and it holds regardless of the
  `require`.  `Properties.AssetRouter.NoHijack` is that statement.
* **The `require` governs re-registration.**  Among the ids a caller can name, it
  may only write one whose recorded deployment tracker is already itself.
  `Properties.AssetRouter.OnlyTrackerOrNtvWrites` is that one.

The native token vault is the exception on both counts: it is normalised to the
fixed `L2_NATIVE_TOKEN_VAULT_ADDR` before hashing — so that an asset registered by
the L1 vault and by an L2 vault get the same id — and it bypasses the tracker
check.  Which is why `Properties.AssetRouter.FreshIdNeedsNtv` matters: a
non-vault caller can never make the *first* registration for one of its own ids,
because the tracker starts at zero and `msg.sender` never does.
-/

namespace Contracts.AssetRouter

open Clear

/-- Chain ids, asset ids, addresses and the opaque `_assetRegistrationData`, all as
256-bit words.  `0` is the zero address and every mapping's unset value. -/
abbrev Chain := UInt256
abbrev AssetId := UInt256
abbrev Address := UInt256
abbrev AssetData := UInt256

/-- Point update of an asset-keyed mapping. -/
def upd (f : AssetId → Address) (a : AssetId) (v : Address) : AssetId → Address :=
  fun x => if x = a then v else f x

/-- `DataEncoding.encodeAssetId(chainId, assetData, sender)`, i.e.
`keccak256(abi.encode(chainId, sender, assetData))`. -/
abbrev AssetIdOf := Chain → Address → AssetData → AssetId

/-- The keccak idealizations, as elsewhere in this package. -/
structure IdAssumptions (enc : AssetIdOf) : Prop where
  /-- Distinct (chain, sender, data) triples get distinct asset ids.  This is what
  makes the caller-in-the-key mechanism airtight. -/
  inj : ∀ c₁ s₁ d₁ c₂ s₂ d₂, enc c₁ s₁ d₁ = enc c₂ s₂ d₂ → c₁ = c₂ ∧ s₁ = s₂ ∧ d₁ = d₂
  /-- No asset id collides with the mappings' unset sentinel. -/
  nonzero : ∀ c s d, enc c s d ≠ 0

/-! ## State -/

/-- The router's two mappings. -/
structure Router where
  /-- `assetHandlerAddress[assetId]` — where funds for the asset are held. -/
  handler : AssetId → Address
  /-- `assetDeploymentTracker[assetId]` — who may re-point it. -/
  tracker : AssetId → Address

/-- Fresh storage. -/
def empty : Router := ⟨fun _ => 0, fun _ => 0⟩

/-- The address the id is hashed from: the native token vault is normalised to the
fixed system address, so the same asset gets the same id whichever vault registers
it.  Every other caller hashes as itself. -/
def senderOf (ntv ntvSystemAddr caller : Address) : Address :=
  if caller = ntv then ntvSystemAddr else caller

/-- The id a call by `caller` with registration data `d` writes to.  Note it is a
function of the caller — that is the whole mechanism. -/
def writtenId (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr caller : Address)
    (d : AssetData) : AssetId :=
  enc thisChain (senderOf ntv ntvAddr caller) d

/-- The guard: the native token vault always passes, anybody else must already be
the recorded deployment tracker of the id it is writing. -/
structure SetGuard (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address)
    (R : Router) (caller : Address) (d : AssetData) : Prop where
  /-- `require(senderIsNTV || msg.sender == assetDeploymentTracker[assetId])`. -/
  authorized : caller = ntv ∨ caller = R.tracker (writtenId enc thisChain ntv ntvAddr caller d)
  /-- `msg.sender` is never the zero address. -/
  callerNonzero : caller ≠ 0

/-- `_setAssetHandler` plus the tracker write. -/
def setHandler (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R : Router)
    (caller : Address) (d : AssetData) (h : Address) : Router :=
  { handler := upd R.handler (writtenId enc thisChain ntv ntvAddr caller d) h
    tracker := upd R.tracker (writtenId enc thisChain ntv ntvAddr caller d) caller }

/-- What the router must satisfy: a pointed-at asset has a recorded tracker, so
there is always somebody accountable for a live route. -/
def Valid (R : Router) : Prop := ∀ a, R.handler a ≠ 0 → R.tracker a ≠ 0

/-! ## Runs -/

/-- One registration. -/
inductive Step (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) :
    Router → Router → Prop
  | setHandler {R caller d h} : SetGuard enc thisChain ntv ntvAddr R caller d →
      Step enc thisChain ntv ntvAddr R (setHandler enc thisChain ntv ntvAddr R caller d h)

/-- Reachability. -/
inductive Reach (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) :
    Router → Router → Prop
  | refl {R} : Reach enc thisChain ntv ntvAddr R R
  | tail {R S T} : Reach enc thisChain ntv ntvAddr R S → Step enc thisChain ntv ntvAddr S T →
      Reach enc thisChain ntv ntvAddr R T

end Contracts.AssetRouter
