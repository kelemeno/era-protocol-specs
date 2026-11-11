import EraSpec.Contracts.AssetRouterBase.Specs.HandlerRegistration

/-!
# Model: `AssetRouter` runs, logged — the (chain, sender, data) triples a run hashes

`HandlerRegistration` states its structural results, `NoHijack` and
`NtvTouchesOnlyItsOwnIds`, for ONE call; their bounded forms (`NoHijackOn`,
`NtvTouchesOnlyItsOwnIdsOn`) need the id hash injective on the two triples that one
call compares.  This file adds what a statement about a whole RUN needs: the run with
every call written down, and the set of triples those calls fed to `encodeAssetId`,
one per call.  It changes nothing in `HandlerRegistration`: a logged step is that
file's `Step`, labelled.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.AssetRouterBase.Properties.HandlerRegistrationRuns` and proved in
`EraSpec.Contracts.AssetRouterBase.Proofs.HandlerRegistrationRuns`.

## Source (pinned tree `c67894b9`, `l1-contracts/contracts/`)

The writer is `_setAssetHandlerAddressThisChain` (`bridge/asset-router/AssetRouterBase.sol:73-85`):

    bool senderIsNTV = msg.sender == _nativeTokenVault;
    address sender = senderIsNTV ? L2_NATIVE_TOKEN_VAULT_ADDR : msg.sender;
    bytes32 assetId = DataEncoding.encodeAssetId(block.chainid, _assetRegistrationData, sender);
    require(senderIsNTV || msg.sender == assetDeploymentTracker[assetId], Unauthorized(msg.sender));
    _setAssetHandler(assetId, _assetHandlerAddress);
    assetDeploymentTracker[assetId] = msg.sender;

with `encodeAssetId(_chainId, _assetData, _sender) = keccak256(abi.encode(_chainId, _sender, _assetData))`
(`common/libraries/DataEncoding.sol:126-128`).  So each call hashes exactly one triple,
`(block.chainid, sender, _assetRegistrationData)` — `Call.triple` below.

**Anyone can schedule the vault's calls**, the ones that skip the tracker check:
`NativeTokenVaultBase.registerToken` is permissionless (`bridge/ntv/NativeTokenVaultBase.sol:129-142`;
it needs only code at the token and the token unregistered), and it makes the vault call
`setAssetHandlerAddressThisChain(bytes32(uint256(uint160(_nativeToken))), address(this))`
(`:515-522`).  So the data of a vault call is any address an attacker can put code at,
and its handler is the vault itself.

## Where non-vault trackers come from, and why runs start from any router

At the pin the tracker mapping has exactly two writers: line 83 above, which records
`msg.sender`, and `L1AssetRouter.setAssetDeploymentTracker` (`bridge/asset-router/L1AssetRouter.sol:159-166`,
`onlyOwner`), which records `_assetDeploymentTracker` at the id hashed from that same
address.  Line 83 alone never records anybody but the vault when started from fresh
storage: the first write to an id must pass the guard while its tracker is still zero,
and only the vault does (`Contracts.AssetRouter.Properties.OnlyVaultActsFromEmpty`).  So
on a run of this model from `empty` every call is the vault's, and the non-vault half of
`NoHijack` has nothing to say.  On L1 a custom tracker exists once the owner has
whitelisted it.  The one in use at the pin is the `CTMDeploymentTracker`, which registers
each chain type manager's asset — the route chain migrations take — with handler
`BRIDGE_HUB.chainAssetHandler()` (`core/ctm-deployment/CTMDeploymentTracker.sol:71-91`); the
guard admits it only after the owner's `setAssetDeploymentTracker` for that data.  The L2
router has no tracker writer besides line 83 (its other writers,
`initL2` at `L2AssetRouter.sol:167`, the counterpart-only `setAssetHandlerAddress` at
`:200-206` and `_finalizeDeposit`'s fallback at `AssetRouterBase.sol:285-286`, all go
through `_setAssetHandler` at `:298-301`, which writes the handler only), so on L2 only
the vault ever passes the guard (`Contracts.AssetRouter.Properties.OnlyVaultActsAmidOtherWriters`).

The run results therefore start from an ARBITRARY router `R₀` — whatever the owner's
whitelisting, the initializers or the counterpart path left.  `afterSetDeploymentTracker`
names the state the owner's whitelisting leaves, so that the witnesses can start from a
realistic one; it is not a step of the runs here.  (The other writers are not steps of
these runs; on L1 the owner's tracker writes in the middle of a run are outside them.)
Both observations assume the router's storage starts fresh; an upgrade that wrote the
tracker mapping would be outside the model.

## Logged runs

`Reach` records states, not calls, so the triples a run hashed are not visible in it.
`ReachLog` is `Reach` with every call written to a log, oldest first, and
`loggedTriples thisChain ntv ntvAddr log` is the set of triples the logged calls hashed —
at most one per call.  It is the `S` of `IdInjOn enc S` in the run-level results: they
need the id hash injective on the triples the run itself hashed, plus the one triple whose
route they talk about.  No property here asks for injectivity anywhere else.

`applyCalls` is the same sequence of writes with NO guard checked (the router with its
`require` deleted).  It is there so that the structural result can be stated without the
guard, as `NoHijack` is, and so that intermediate states of a run have names.
-/

namespace Contracts.AssetRouter

open Clear

/-! ## A logged call -/

/-- One call of `_setAssetHandlerAddressThisChain`, with its arguments. -/
structure Call where
  /-- `msg.sender`. -/
  caller : Address
  /-- `_assetRegistrationData`. -/
  data : AssetData
  /-- `_assetHandlerAddress`. -/
  handler : Address

/-- The (chain, sender, data) triple a call feeds to `encodeAssetId`: this chain, the
caller normalised by `senderOf` (the vault becomes `L2_NATIVE_TOKEN_VAULT_ADDR`), and the
registration data.  The id the call writes is `enc` of it
(`writtenId enc thisChain ntv ntvAddr c.caller c.data`). -/
def Call.triple (thisChain : Chain) (ntv ntvAddr : Address) (c : Call) :
    Chain × Address × AssetData :=
  (thisChain, senderOf ntv ntvAddr c.caller, c.data)

/-- **The triples a logged run hashes**: one per logged call. -/
def loggedTriples (thisChain : Chain) (ntv ntvAddr : Address) (log : List Call) :
    Finset (Chain × Address × AssetData) :=
  (log.map (Call.triple thisChain ntv ntvAddr)).toFinset

/-! ## Logged runs -/

/-- `Step`, labelled by the call taken: the guard holds and the call's write happens. -/
inductive StepCall (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) :
    Call → Router → Router → Prop
  | setHandler {R : Router} {c : Call} : SetGuard enc thisChain ntv ntvAddr R c.caller c.data →
      StepCall enc thisChain ntv ntvAddr c R
        (setHandler enc thisChain ntv ntvAddr R c.caller c.data c.handler)

/-- `Reach`, with every call logged, oldest first. -/
inductive ReachLog (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) :
    Router → Router → List Call → Prop
  | refl {R : Router} : ReachLog enc thisChain ntv ntvAddr R R []
  | tail {R S T : Router} {log : List Call} {c : Call} :
      ReachLog enc thisChain ntv ntvAddr R S log → StepCall enc thisChain ntv ntvAddr c S T →
      ReachLog enc thisChain ntv ntvAddr R T (log ++ [c])

/-- The calls of a log applied in order with NO guard checked: the router with its
`require` deleted.  A logged run ends exactly here
(`Contracts.AssetRouter.Properties.ReachLogIsApplyCalls`). -/
def applyCalls (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ : Router)
    (log : List Call) : Router :=
  log.foldl (fun R c => setHandler enc thisChain ntv ntvAddr R c.caller c.data c.handler) R₀

/-! ## What the log predicts for one route -/

/-- The last logged call that hashed the triple `q`, if any. -/
def lastCallOn (thisChain : Chain) (ntv ntvAddr : Address) (log : List Call)
    (q : Chain × Address × AssetData) : Option Call :=
  (log.filter (fun c => c.triple thisChain ntv ntvAddr = q)).getLast?

/-- The handler the log predicts at `enc q`: the one the last call that hashed `q` set,
or the one `R₀` held if no logged call hashed `q`. -/
def loggedHandler (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ : Router)
    (log : List Call) (q : Chain × Address × AssetData) : Address :=
  match lastCallOn thisChain ntv ntvAddr log q with
  | some c => c.handler
  | none => R₀.handler (enc q.1 q.2.1 q.2.2)

/-- The tracker the log predicts at `enc q`: the `msg.sender` of the last call that hashed
`q`, or the tracker `R₀` held if no logged call hashed `q`. -/
def loggedTracker (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ : Router)
    (log : List Call) (q : Chain × Address × AssetData) : Address :=
  match lastCallOn thisChain ntv ntvAddr log q with
  | some c => c.caller
  | none => R₀.tracker (enc q.1 q.2.1 q.2.2)

/-! ## Trackers that only the vault can satisfy -/

/-- Every recorded tracker is unset or the vault.  Fresh storage is like this, and so is
every state line 83 alone can reach from it; under it only the vault passes the guard. -/
def VaultOnlyTrackers (ntv : Address) (R : Router) : Prop :=
  ∀ a, R.tracker a = 0 ∨ R.tracker a = ntv

/-- A run of guarded calls (logged) interleaved with writes by the router's OTHER writers,
abstracted to what they all share at the pin on L2: they leave the tracker mapping as it
was.  (`initL2`, the counterpart's `setAssetHandlerAddress` and `_finalizeDeposit`'s
fallback all write through `_setAssetHandler`, which writes the handler only; see the
header.)  The other writers' steps are not logged — they hash nothing the guard reads. -/
inductive ReachAmidOtherWriters (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) :
    Router → Router → List Call → Prop
  | refl {R : Router} : ReachAmidOtherWriters enc thisChain ntv ntvAddr R R []
  | call {R S T : Router} {log : List Call} {c : Call} :
      ReachAmidOtherWriters enc thisChain ntv ntvAddr R S log →
      StepCall enc thisChain ntv ntvAddr c S T →
      ReachAmidOtherWriters enc thisChain ntv ntvAddr R T (log ++ [c])
  | other {R S T : Router} {log : List Call} :
      ReachAmidOtherWriters enc thisChain ntv ntvAddr R S log → T.tracker = S.tracker →
      ReachAmidOtherWriters enc thisChain ntv ntvAddr R T log

/-! ## Start states -/

/-- The storage `L1AssetRouter.setAssetDeploymentTracker(d, t)` leaves
(`L1AssetRouter.sol:159-166`, `onlyOwner`):

    bytes32 assetId = DataEncoding.encodeAssetId(block.chainid, _assetRegistrationData, _assetDeploymentTracker);
    assetDeploymentTracker[assetId] = _assetDeploymentTracker;

so the tracker of the id hashed from `t` itself becomes `t`.  Used only to name realistic
start states for the witnesses; it is not a step of the runs in this file. -/
def afterSetDeploymentTracker (enc : AssetIdOf) (thisChain : Chain) (R : Router)
    (d : AssetData) (t : Address) : Router :=
  { R with tracker := upd R.tracker (enc thisChain t d) t }

end Contracts.AssetRouter
