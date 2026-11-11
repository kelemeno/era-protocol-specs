import EraSpec.Contracts.AssetRouterBase.Specs.AllWriters

/-!
# Model: where each deployment tracker came from, pinned to the run's log

Source: the pinned era-contracts tree (`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`).
Paths are relative to `l1-contracts/contracts/`; `bridge/asset-router/` is shortened to
`AR/`.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.AssetRouterBase.Properties.AllWritersStrong` and are proved in
`EraSpec.Contracts.AssetRouterBase.Proofs.AllWritersStrong`.

## Why this file exists

`AllWriters.Properties.RunTrackerHashed` proves `TrackerHashed` along every run.  That
predicate says a nonzero tracker `t` sits at an id `a` with
`a = enc block.chainid t d`, or, when `t` is the vault,
`a = enc block.chainid L2_NATIVE_TOKEN_VAULT_ADDR d`, for SOME data word `d`.  Nothing
ties `d` to the run.

* If the encoding reaches every id as `d` varies, every router state satisfies
  `TrackerHashed`, reachable or not (`Properties.TrackerHashedAdmitsUnreachableRouter`).
* A keccak-like encoding does not exclude much either.  Its data argument ranges over as
  many words as there are ids, so, heuristically, about `1 - 1/e` of all ids have a
  preimage with any fixed sender.
* `TrackerHashed` does not say that `t` never tracks an id that is also hashed from
  someone else.

The definitions below let the results name the call behind each tracker instead.

## The two tracker writers at the pin

    // AR/AssetRouterBase.sol:78-83   (_setAssetHandlerAddressThisChain: the `register` step)
    bool senderIsNTV = msg.sender == _nativeTokenVault;
    address sender = senderIsNTV ? L2_NATIVE_TOKEN_VAULT_ADDR : msg.sender;
    bytes32 assetId = DataEncoding.encodeAssetId(block.chainid, _assetRegistrationData, sender);
    require(senderIsNTV || msg.sender == assetDeploymentTracker[assetId], Unauthorized(msg.sender));
    _setAssetHandler(assetId, _assetHandlerAddress);
    assetDeploymentTracker[assetId] = msg.sender;

    // AR/L1AssetRouter.sol:163-164   (setAssetDeploymentTracker, onlyOwner: the `setTracker` step)
    bytes32 assetId = DataEncoding.encodeAssetId(block.chainid, _assetRegistrationData, _assetDeploymentTracker);
    assetDeploymentTracker[assetId] = _assetDeploymentTracker;

No other code at the pin writes `assetDeploymentTracker` (`Specs/AllWriters.lean` lists the
writers).  Each of the two writes one value at the id of the one triple the call itself
hashes (`Op.triple`).  The value depends only on the call's caller and arguments, and reads
no storage.  The `require` at `:81` decides whether the call succeeds, not what it writes.
So:

* the tracker mapping after a run is the run's log replayed on the start mapping
  (`replayTrackers`);
* at the id of a triple `q`, it is what the last logged call hashing `q` recorded
  (`lastTrackerWriteOn`), once no other logged triple shares that id (`LoggedClash`).
-/

namespace Contracts.AssetRouter.AllWriters

/-! ## What one call writes to the tracker mapping -/

/-- The tracker write a call makes, if any: the triple whose id it writes, and the value it
records there.

* A registration records `msg.sender` at `(block.chainid, normalised caller, d)`
  (`AR/AssetRouterBase.sol:79-83`).
* An owner tracker write records `t` at `(block.chainid, t, d)`
  (`AR/L1AssetRouter.sol:163-164`).
* The fallback, the seed and the counterpart write the handler only.

The triple is the call's `Op.triple`. -/
def Op.trackerWrite (K : Cfg) : Op → Option ((Chain × Address × AssetData) × Address)
  | .register caller d _ => some ((K.thisChain, senderOf K.ntv K.ntvAddr caller, d), caller)
  | .setTracker d t => some ((K.thisChain, t, d), t)
  | _ => none

/-- One call's effect on a tracker mapping `f`.  It is computed from the call alone: the
call's `trackerWrite` value goes to the id of its `trackerWrite` triple. -/
def trackerAfterOp (K : Cfg) (f : AssetId → Address) : Op → AssetId → Address
  | .register caller d _ => upd f (writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d) caller
  | .setTracker d t => upd f (K.enc K.thisChain t d) t
  | _ => f

/-- **The tracker mapping a log predicts**: the logged calls' tracker writes replayed in
order on a start mapping `f₀`.  It reads the log only, not the handler mapping and not the
guards. -/
def replayTrackers (K : Cfg) (f₀ : AssetId → Address) (ops : List Op) : AssetId → Address :=
  ops.foldl (trackerAfterOp K) f₀

/-- The value recorded by the LAST logged call whose tracker write hashed the triple `q`,
or `none` if no logged call hashed `q`. -/
def lastTrackerWriteOn (K : Cfg) (ops : List Op) (q : Chain × Address × AssetData) :
    Option Address :=
  (((ops.filterMap (Op.trackerWrite K)).filter (fun w => w.1 = q)).getLast?).map Prod.snd

/-! ## The run-local hash premise -/

/-- **A logged clash at `q`**: a triple of the run's log other than `q` has `q`'s id.

It names a triple of the run's finite log, so it is not an existential over all
preimages.  It is false whenever the encoding is injective on the logged triples together
with `q` (`Properties.IdInjOnExcludesLoggedClash`), and it can also be false when the log
collides elsewhere (`Properties.LastOwnWriteHoldsDespiteClashElsewhere`).  So
`¬ LoggedClash K ops q` is a weaker premise than `IdInjOn` on the log plus `q`. -/
def LoggedClash (K : Cfg) (ops : List Op) (q : Chain × Address × AssetData) : Prop :=
  ∃ p ∈ loggedTriples K ops, p ≠ q ∧ K.enc p.1 p.2.1 p.2.2 = K.enc q.1 q.2.1 q.2.2

/-! ## `TrackerHashed`, with the preimage named by the run -/

/-- **Every nonzero tracker was recorded by a logged call, at that call's own id.**  For
every id `a` whose tracker `t` is nonzero there is a data word `d` such that either

* the log holds the owner's `setAssetDeploymentTracker(d, t)` and `a` is its id
  `enc block.chainid t d`, or
* the log holds a registration by `t` itself with data `d`, and `a` is the id that
  registration writes, `writtenId … t d`.  That is `enc block.chainid t d`, or
  `enc block.chainid L2_NATIVE_TOKEN_VAULT_ADDR d` when `t` is the vault.

`TrackerHashed` is this with the two membership conjuncts dropped
(`Properties.TrackerRecordedImpliesTrackerHashed`).  With them, the data word is an
argument of a call the run made, so the condition can fail for a state the run did not
reach. -/
def TrackerRecorded (K : Cfg) (ops : List Op) (R : Router) : Prop :=
  ∀ a, R.tracker a ≠ 0 → ∃ d : AssetData,
    (Op.setTracker d (R.tracker a) ∈ ops ∧ a = K.enc K.thisChain (R.tracker a) d) ∨
    ((∃ h, Op.register (R.tracker a) d h ∈ ops) ∧
      a = writtenId K.enc K.thisChain K.ntv K.ntvAddr (R.tracker a) d)

end Contracts.AssetRouter.AllWriters
