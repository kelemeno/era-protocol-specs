import EraSpec.Contracts.AssetRouterBase.Specs.AllWriters

/-!
# Properties: the router with every writer at the pin

Statements about `EraSpec.Contracts.AssetRouterBase.Specs.AllWriters`.  Proofs are in
`EraSpec.Contracts.AssetRouterBase.Proofs.AllWriters`.

## (a) `RunValid` fails at the pin

`HandlerRegistration.RunValid` says every live route has a nonzero deployment
tracker.  With every writer, it is false.  The first deposit of any token the
destination has not seen takes `_finalizeDeposit`'s fallback, which points the id at the
vault and records no tracker (`FinalizeFallbackBreaksValid`, for every configuration).
This happens with a well-behaved vault, on both routers, after one call
(`RunValidFailsAfterOneDeposit`; `AllWritersRunValidFalse`).  The initializers and the
counterpart's write do the same (`SeedAndCounterpartBreakValid`).  The single-writer
model is exactly the registration-only fragment (`SingleWriterIsRegisterOnlyFragment`),
so `RunValid` was a property of that fragment.

## (b) The invariant that holds

`WeakValid`: every live route has a nonzero tracker, **or** is a vault route (its
handler is the vault and its id is a vault id).  Its premises are that the vault mints
only vault ids (`MintsOnlyNtvIds`) and that the seeded id is a vault id.
`MintsOnlyNtvIds` is proved from the vault's own registry model, with no hash premise,
in the `VaultMintGate` topic (`VaultModelDischargesMintPremise`).

* No hash premise is needed, for any run without a counterpart write or a zero-tracker
  write (`StepPreservesWeakValid`, `RunWeakValid`).  On L2 that is every run without a
  counterpart write (`L2RunWeakValid`).
* Owner tracker writes naming the zero tracker are harmless under a run-local hash
  premise: injectivity on the triples the run's registrations and tracker writes hash,
  at most one per call (`RunWeakValidOn`, `LoggedTriplesCardLe`,
  `LoggedPremiseSatisfiable`).  On L1, which has no counterpart, that is every run
  (`L1RunWeakValidOn`).
* Witnesses: `RunWeakValidWitness` runs every non-counterpart writer on each router
  and ends violating `Valid`.  `RunWeakValidOnWitness` includes a zero-tracker write,
  with an encoding that collides off the log.
* Each premise is needed: `CounterpartBreaksWeakValid`,
  `ZeroTrackerBreaksWeakValidUnderCollision`, `NonVaultMintBreaksWeakValid`,
  `NonVaultSeedBreaksWeakValid`.
* `WeakValidAtZeroVault` carries the invariant across L1's `setNativeTokenVault`.

## (c) Who can re-point a route

* Every call moves at most one handler, its target (`AllWritersFrame`).  The fallback
  never moves a live one (`FinalizeLeavesLiveRoutes`).
* **No hijack, for every writer but the counterpart** (`NoHijackOnExceptCounterpart`).
  Every other call's written id is hashed from a triple of the call's own sender: the
  normalised caller for a registration, `L2_NATIVE_TOKEN_VAULT_ADDR` for the fallback and
  the seed.  The call leaves alone every id hashed from a different sender, under
  injectivity on just that pair of triples.  `NoHijackOnExceptCounterpartWitness` fires
  it for a fallback deposit, with a live custom route as the victim.
* **The counterpart is the trusted exception, made explicit.**  On L2 it can point any
  id at any handler from any state (`CounterpartRepointsAnyRoute`).  In particular it
  re-points a route that the vault itself registered, with no collision involved
  (`CounterpartRepointsVaultRoute`).  Both are about the L2 router alone.  With the L1
  router's own check modelled (the `CounterpartGate` topic), a vault triple's id on L2
  can only be pointed at the L2 vault (`CounterpartCannotMisrouteVaultTriple`).  The
  exception remains for custom assets (`CustomTrackerNamesAnyHandler`).
* **On L2 only the vault ever registers** (`L2OnlyVaultRegisters`, no hash premise).
  So on L2, outside the counterpart, only vault ids ever change handler
  (`L2OnlyCounterpartTouchesNonVaultIds`, no hash premise; witness
  `L2OnlyCounterpartTouchesNonVaultIdsWitness`).  On L2, the handler of an id that is not
  a vault id is written by the counterpart alone.  On L1 the owner's tracker writes let
  custom trackers register; `RunWeakValidWitness`'s L1 run does that.
* Every recorded tracker sits at an id with some preimage whose sender is that tracker
  (`RunTrackerHashed`).  The preimage is existential, so this alone is weak: for an
  encoding that reaches every id as the data word varies it holds in every state.  The
  `AllWritersStrong` topic pins it.  Each tracker was recorded by a logged call, at that
  call's own id (`RunTrackerRecorded`).  The owner cannot hand a tracker an id hashed from
  someone else, under injectivity on the run's logged triples plus that id's triple
  (`RunTrackerNotHandedToOtherSenderOn`).  Without that premise it can
  (`TrackerHandedToOtherSenderUnderCollision`).
-/

namespace Contracts.AssetRouter.AllWriters

/-! ## (a) `RunValid` fails at the pin -/

/-- **ONE FALLBACK DEPOSIT BREAKS `Valid`, ON EVERY DEPLOYMENT.**  From any router state
in which an id has neither handler nor tracker, a `finalizeDeposit` for that id that the
vault accepts (and that is not L2's base token) succeeds, points the id at the vault and
leaves its tracker zero.  So `Valid` fails, whenever the vault address is nonzero. -/
def Properties.FinalizeFallbackBreaksValid : Prop :=
  ∀ (K : Cfg) (R : Router) (a : AssetId), R.handler a = 0 → R.tracker a = 0 → K.ntv ≠ 0 →
    K.ntvMints a → (K.side = .l2 → a ≠ K.seedId) →
      AStep K (.finalize a) R (pointAt R a K.ntv) ∧ ¬ Valid (pointAt R a K.ntv)

/-- **`RunValid` FAILS AFTER ONE DEPOSIT, ON EITHER ROUTER, WITH A WELL-BEHAVED VAULT.**
For each side there is a configuration meeting every premise of `RunWeakValid` (the
vault mints only vault ids and the seeded id is a vault id), and a one-call run from
fresh storage — a fallback deposit — that ends violating `Valid` and satisfying
`WeakValid`. -/
def Properties.RunValidFailsAfterOneDeposit : Prop :=
  ∀ side : Side, ∃ (K : Cfg) (a : AssetId) (R : Router),
    K.side = side ∧ K.ntv ≠ 0 ∧ MintsOnlyNtvIds K ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧
    ARun K empty [.finalize a] R ∧ ¬ Valid R ∧ WeakValid K R

/-- **`RunValid`, LIFTED TO EVERY WRITER, IS FALSE.** -/
def Properties.AllWritersRunValidFalse : Prop :=
  ¬ ∀ (K : Cfg) (ops : List Op) (R : Router), ARun K empty ops R → Valid R

/-- **THE INITIALIZERS AND THE COUNTERPART BREAK `Valid` TOO.**  From fresh storage, with
a nonzero vault and the seeded id a vault id: L1's `setNativeTokenVault` alone (`ETH`
then has the vault as handler and no tracker until `registerEthToken`), L2's `initL2`
alone, and one L2 `setAssetHandlerAddress`. -/
def Properties.SeedAndCounterpartBreakValid : Prop :=
  (∃ (K : Cfg) (R : Router), K.side = .l1 ∧ K.ntv ≠ 0 ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧
      ARun K empty [.seed] R ∧ ¬ Valid R) ∧
  (∃ (K : Cfg) (R : Router), K.side = .l2 ∧ K.ntv ≠ 0 ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧
      ARun K empty [.seed] R ∧ ¬ Valid R) ∧
  (∃ (K : Cfg) (a : AssetId) (h : Address) (R : Router), K.side = .l2 ∧
      ARun K empty [.counterpartSet a h] R ∧ ¬ Valid R)

/-! ## How the single-writer model sits inside this one -/

/-- **THE SINGLE-WRITER MODEL IS EXACTLY THE REGISTRATION-ONLY FRAGMENT.**  A state is
reachable in `HandlerRegistration` iff it is reachable here by a run whose log contains
only registrations.  So `HandlerRegistration.RunValid` is a statement about that
fragment. -/
def Properties.SingleWriterIsRegisterOnlyFragment : Prop :=
  ∀ (K : Cfg) (R S : Router), Reach K.enc K.thisChain K.ntv K.ntvAddr R S ↔
    ∃ ops : List Op, ARun K R ops S ∧ ∀ op ∈ ops, ∃ caller d h, op = .register caller d h

/-- `Valid` implies `WeakValid`. -/
def Properties.ValidImpliesWeakValid : Prop :=
  ∀ (K : Cfg) (R : Router), Valid R → WeakValid K R

/-- **`WeakValid` CARRIES ACROSS L1's `setNativeTokenVault`.**  Before the L1 vault is set,
the router is this model with `ntv = 0`.  `WeakValid` there is `Valid`, which implies
`WeakValid` for any configuration, in particular the one with the vault set. -/
def Properties.WeakValidAtZeroVault : Prop :=
  ∀ (K K' : Cfg) (R : Router), K.ntv = 0 → WeakValid K R → WeakValid K' R

/-! ## (b) The weakened invariant -/

/-- **ONE CALL PRESERVES `WeakValid`.**  When the vault mints only vault ids and the
seeded id is a vault id, every call except the counterpart's write and an owner tracker
write naming zero preserves `WeakValid`.  No hash premise. -/
def Properties.StepPreservesWeakValid : Prop :=
  ∀ (K : Cfg), MintsOnlyNtvIds K → IsNtvId K.enc K.ntvAddr K.seedId →
    ∀ (op : Op) (R R' : Router), AStep K op R R' → ¬ op.IsCounterpart → ¬ op.ZeroTracker →
      WeakValid K R → WeakValid K R'

/-- **EVERY LIVE ROUTE HAS A TRACKER OR IS A VAULT ROUTE.**  Along every run from fresh
storage that has no counterpart write and no zero-tracker write, when the vault mints
only vault ids and the seeded id is a vault id.  No hash premise. -/
def Properties.RunWeakValid : Prop :=
  ∀ (K : Cfg), MintsOnlyNtvIds K → IsNtvId K.enc K.ntvAddr K.seedId →
    ∀ (ops : List Op) (R : Router), ARun K empty ops R →
      (∀ op ∈ ops, ¬ op.IsCounterpart ∧ ¬ op.ZeroTracker) → WeakValid K R

/-- **ON L2: EVERY RUN WITHOUT A COUNTERPART WRITE.**  L2 has no tracker writer besides
registration, so `RunWeakValid`'s zero-tracker exclusion is automatic there.  No hash
premise. -/
def Properties.L2RunWeakValid : Prop :=
  ∀ (K : Cfg), K.side = .l2 → MintsOnlyNtvIds K → IsNtvId K.enc K.ntvAddr K.seedId →
    ∀ (ops : List Op) (R : Router), ARun K empty ops R →
      (∀ op ∈ ops, ¬ op.IsCounterpart) → WeakValid K R

/-- **ZERO-TRACKER WRITES ALLOWED, UNDER A RUN-LOCAL HASH PREMISE.**  Along every run from
fresh storage with no counterpart write, if the encoding is injective on the triples the
run's own registrations and tracker writes hash (`loggedTriples`), `WeakValid` holds.
It also takes `L2_NATIVE_TOKEN_VAULT_ADDR ≠ 0`, which is true (`0x10004`). -/
def Properties.RunWeakValidOn : Prop :=
  ∀ (K : Cfg), K.ntvAddr ≠ 0 → MintsOnlyNtvIds K → IsNtvId K.enc K.ntvAddr K.seedId →
    ∀ (ops : List Op) (R : Router), ARun K empty ops R →
      (∀ op ∈ ops, ¬ op.IsCounterpart) → IdInjOn K.enc ↑(loggedTriples K ops) →
        WeakValid K R

/-- **ON L1: EVERY RUN, UNDER THE RUN-LOCAL HASH PREMISE.**  The L1 router has no
counterpart write. -/
def Properties.L1RunWeakValidOn : Prop :=
  ∀ (K : Cfg), K.side = .l1 → K.ntvAddr ≠ 0 → MintsOnlyNtvIds K →
    IsNtvId K.enc K.ntvAddr K.seedId →
    ∀ (ops : List Op) (R : Router), ARun K empty ops R →
      IdInjOn K.enc ↑(loggedTriples K ops) → WeakValid K R

/-- **AT MOST ONE LOGGED TRIPLE PER CALL.** -/
def Properties.LoggedTriplesCardLe : Prop :=
  ∀ (K : Cfg) (ops : List Op), (loggedTriples K ops).card ≤ ops.length

/-- **THE RUN-LOCAL PREMISE IS SATISFIABLE FOR EVERY REALISTIC LOG.**  Any log no longer
than the id space has an encoding injective on its triples.  (The triples do not depend
on the encoding.) -/
def Properties.LoggedPremiseSatisfiable : Prop :=
  ∀ (K : Cfg) (ops : List Op), ops.length ≤ UInt256.size →
    ∃ enc : AssetIdOf, IdInjOn enc ↑(loggedTriples K ops)

/-- **`RunWeakValid`'s PREMISES HOLD ON A RUN OF EVERY NON-COUNTERPART WRITER, ON EACH
ROUTER.**  For each side: a configuration with a well-behaved vault and a run from fresh
storage containing a seed, a registration and a fallback deposit, with no counterpart or
zero-tracker write, ending in a state that violates `Valid`.  On L1 the log also holds an
owner tracker write for a custom tracker (not the vault) and that tracker's own
registration. -/
def Properties.RunWeakValidWitness : Prop :=
  ∀ side : Side, ∃ (K : Cfg) (ops : List Op) (R : Router),
    K.side = side ∧ MintsOnlyNtvIds K ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧
    ARun K empty ops R ∧ (∀ op ∈ ops, ¬ op.IsCounterpart ∧ ¬ op.ZeroTracker) ∧
    Op.seed ∈ ops ∧ (∃ caller d h, Op.register caller d h ∈ ops) ∧
    (∃ a, Op.finalize a ∈ ops) ∧
    (side = .l1 → ∃ d t h, Op.setTracker d t ∈ ops ∧ Op.register t d h ∈ ops ∧ t ≠ K.ntv) ∧
    ¬ Valid R

/-- **`L1RunWeakValidOn`'s PREMISES HOLD ON A RUN WITH A ZERO-TRACKER WRITE, FOR AN ENCODING
THAT COLLIDES OFF THE LOG.**  An L1 configuration with a well-behaved vault, and a run
from fresh storage that includes an owner tracker write naming zero.  The encoding is
injective on the logged triples, but maps a logged triple and an unlogged one to the
same id.  The run ends violating `Valid`. -/
def Properties.RunWeakValidOnWitness : Prop :=
  ∃ (K : Cfg) (ops : List Op) (R : Router),
    K.side = .l1 ∧ K.ntvAddr ≠ 0 ∧ MintsOnlyNtvIds K ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧
    ARun K empty ops R ∧ IdInjOn K.enc ↑(loggedTriples K ops) ∧
    (∃ op ∈ ops, op.ZeroTracker) ∧
    (∃ p ∈ loggedTriples K ops, ∃ q, q ∉ loggedTriples K ops ∧
        K.enc p.1 p.2.1 p.2.2 = K.enc q.1 q.2.1 q.2.2) ∧
    ¬ Valid R

/-- **THE COUNTERPART BREAKS `WeakValid`, ON EVERY L2 ROUTER.**  Pointing an id that has no
tracker at a nonzero handler other than the vault succeeds and violates `WeakValid`. -/
def Properties.CounterpartBreaksWeakValid : Prop :=
  ∀ (K : Cfg) (R : Router) (a : AssetId) (h : Address), K.side = .l2 → R.tracker a = 0 →
    h ≠ 0 → h ≠ K.ntv →
      AStep K (.counterpartSet a h) R (pointAt R a h) ∧ ¬ WeakValid K (pointAt R a h)

/-- **UNDER A COLLISION, A ZERO-TRACKER WRITE BREAKS `WeakValid`.**  An L1 run with a
well-behaved vault and a colliding encoding.  The owner records a custom tracker, which
registers a custom handler.  Then an owner write naming the zero tracker, which hashes
to the same id, erases that tracker.  So `RunWeakValid`'s zero-tracker exclusion and
`RunWeakValidOn`'s hash premise are both load-bearing. -/
def Properties.ZeroTrackerBreaksWeakValidUnderCollision : Prop :=
  ∃ (K : Cfg) (ops : List Op) (R : Router),
    K.side = .l1 ∧ K.ntvAddr ≠ 0 ∧ MintsOnlyNtvIds K ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧
    ARun K empty ops R ∧ (∀ op ∈ ops, ¬ op.IsCounterpart) ∧ (∃ op ∈ ops, op.ZeroTracker) ∧
    ¬ IdInjOn K.enc ↑(loggedTriples K ops) ∧ ¬ WeakValid K R

/-- **A VAULT THAT MINTED A NON-VAULT ID WOULD BREAK `WeakValid`.**  So `MintsOnlyNtvIds` is
load-bearing: one fallback deposit for an id that is not a vault id, from fresh storage. -/
def Properties.NonVaultMintBreaksWeakValid : Prop :=
  ∃ (K : Cfg) (a : AssetId) (R : Router),
    K.ntv ≠ 0 ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧ K.ntvMints a ∧
    ¬ IsNtvId K.enc K.ntvAddr a ∧ ARun K empty [.finalize a] R ∧ ¬ WeakValid K R

/-- **A SEEDED ID THAT IS NOT A VAULT ID WOULD BREAK `WeakValid`.**  So the seed premise is
load-bearing.  On L2 it is a premise on the upgrade's `_baseTokenAssetId`. -/
def Properties.NonVaultSeedBreaksWeakValid : Prop :=
  ∃ (K : Cfg) (R : Router), K.side = .l2 ∧ K.ntv ≠ 0 ∧ MintsOnlyNtvIds K ∧
    ¬ IsNtvId K.enc K.ntvAddr K.seedId ∧ ARun K empty [.seed] R ∧ ¬ WeakValid K R

/-! ## (c) Who can re-point a route -/

/-- **EACH CALL MOVES AT MOST ITS TARGET'S HANDLER.**  For every call, the counterpart's
included: a handler that changed is the call's `target`.  A tracker write moves none. -/
def Properties.AllWritersFrame : Prop :=
  ∀ (K : Cfg) (op : Op) (R R' : Router), AStep K op R R' →
    ∀ x, R'.handler x ≠ R.handler x → op.target K = some x

/-- **THE FALLBACK NEVER MOVES A LIVE ROUTE.** -/
def Properties.FinalizeLeavesLiveRoutes : Prop :=
  ∀ (K : Cfg) (a : AssetId) (R R' : Router), AStep K (.finalize a) R R' →
    ∀ x, R.handler x ≠ 0 → R'.handler x = R.handler x

/-- **NO HIJACK, FOR EVERY WRITER BUT THE COUNTERPART.**  Assume the vault mints only vault
ids and the seeded id is a vault id.  Take any successful call other than the
counterpart's `setAssetHandlerAddress`.

* Its written id is hashed from some triple `p` (`HashedFrom`).  For a registration, `p`
  is `(block.chainid, normalised caller, d)`.  For the fallback and the seed, `p` is a
  vault triple of the given id.
* For every such `p`, and every victim triple `(c, s, d')` whose sender `s` is not
  `p`'s, the call leaves the handler of `enc c s d'` unchanged.  The only premise is
  injectivity on the two triples `p` and `(c, s, d')`.

The vault's own registrations are covered: their sender is `L2_NATIVE_TOKEN_VAULT_ADDR`.
The aliased L1 router's `finalizeDeposit` on L2 is a fallback, so it is covered too.
Only its `setAssetHandlerAddress` is excluded. -/
def Properties.NoHijackOnExceptCounterpart : Prop :=
  ∀ (K : Cfg), MintsOnlyNtvIds K → IsNtvId K.enc K.ntvAddr K.seedId →
    ∀ (op : Op) (R R' : Router), AStep K op R R' → ¬ op.IsCounterpart →
      (∃ p, op.HashedFrom K p) ∧
      ∀ (p : Chain × Address × AssetData) (c : Chain) (s : Address) (d' : AssetData),
        op.HashedFrom K p → s ≠ p.2.1 → IdInjOn K.enc {p, (c, s, d')} →
          R'.handler (K.enc c s d') = R.handler (K.enc c s d')

/-- **`NoHijackOnExceptCounterpart`'s PREMISES HOLD FOR A FALLBACK, WITH A LIVE VICTIM.**  A
configuration with a well-behaved vault and a state reachable from fresh storage in which
the victim's route is live.  A fallback deposit succeeds from that state, and the
victim's triple and a vault triple of the deposit's id are separated by the encoding.
(The witness is an L1 run in which the owner records a custom tracker and that tracker
registers the victim's route.) -/
def Properties.NoHijackOnExceptCounterpartWitness : Prop :=
  ∃ (K : Cfg) (ops : List Op) (R R' : Router) (a : AssetId)
    (p : Chain × Address × AssetData) (c : Chain) (s : Address) (d' : AssetData),
    MintsOnlyNtvIds K ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧ ARun K empty ops R ∧
    AStep K (.finalize a) R R' ∧ (Op.finalize a).HashedFrom K p ∧ s ≠ p.2.1 ∧
    IdInjOn K.enc {p, (c, s, d')} ∧ R.handler (K.enc c s d') ≠ 0

/-- **THE COUNTERPART CAN POINT ANY ID AT ANY HANDLER.**  The trust boundary, stated
outright.  On every L2 router, from every state, `setAssetHandlerAddress` succeeds for
every id and every handler, the zero address included, and sets exactly that handler.
Its only check on L2 is the caller (`onlyAssetRouterCounterpart`,
`AR/L2AssetRouter.sol:91-102`). -/
def Properties.CounterpartRepointsAnyRoute : Prop :=
  ∀ (K : Cfg) (R : Router) (a : AssetId) (h : Address), K.side = .l2 →
    ∃ R', AStep K (.counterpartSet a h) R R' ∧ R'.handler a = h ∧
      ∀ x, x ≠ a → R'.handler x = R.handler x

/-- **THE COUNTERPART CAN RE-POINT A ROUTE THE VAULT REGISTERED.**  The trusted exception,
made explicit.  On an L2 router with a well-behaved vault, a run from fresh storage with
no counterpart write leaves a vault route whose tracker is the vault.  One
`setAssetHandlerAddress` then points that id at a nonzero handler other than the vault.
No collision is involved: the counterpart's id is an argument, not a hash of its
caller.  This is the L2 router taken alone.  With trackers that behave as at the pin
(`VaultApprovals`), the L1 router would not send that message for a vault triple's id
unless its own log holds a clash (`CounterpartGate.L1CounterpartAtVaultIdOrLoggedClash`). -/
def Properties.CounterpartRepointsVaultRoute : Prop :=
  ∃ (K : Cfg) (ops : List Op) (R R' : Router) (a : AssetId) (h : Address),
    K.side = .l2 ∧ K.ntv = K.ntvAddr ∧ MintsOnlyNtvIds K ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧
    ARun K empty ops R ∧ (∀ op ∈ ops, ¬ op.IsCounterpart) ∧
    VaultRoute K R a ∧ R.tracker a = K.ntv ∧
    AStep K (.counterpartSet a h) R R' ∧ R'.handler a = h ∧ h ≠ 0 ∧ h ≠ K.ntv

/-- **ON L2, ONLY THE VAULT EVER REGISTERS.**  Along every L2 run from fresh storage, every
tracker is zero or the vault, and every registration in the log was made by the vault.
This holds for every encoding, colliding or not.  L2 has no tracker writer other than
registration, and the first registration of an id needs the vault (`FreshIdNeedsNtv`).
So on L2 a handler other than what the vault registers, the fallback or the seed can
only come from the counterpart. -/
def Properties.L2OnlyVaultRegisters : Prop :=
  ∀ (K : Cfg), K.side = .l2 → ∀ (ops : List Op) (R : Router), ARun K empty ops R →
    (∀ a, R.tracker a = 0 ∨ R.tracker a = K.ntv) ∧
    ∀ (caller : Address) (d : AssetData) (h : Address), Op.register caller d h ∈ ops →
      caller = K.ntv

/-- **ON L2, OUTSIDE THE COUNTERPART, ONLY VAULT IDS EVER CHANGE HANDLER.**  On an L2
router whose vault mints only vault ids and whose seeded id is a vault id: in any state
reachable from fresh storage, every call other than the counterpart's changes handlers
only at vault ids.  No hash premise.  So on L2 the handler of an id that is not a vault
id is written by the counterpart alone. -/
def Properties.L2OnlyCounterpartTouchesNonVaultIds : Prop :=
  ∀ (K : Cfg), K.side = .l2 → MintsOnlyNtvIds K → IsNtvId K.enc K.ntvAddr K.seedId →
    ∀ (ops : List Op) (R : Router) (op : Op) (R' : Router),
      ARun K empty ops R → AStep K op R R' → ¬ op.IsCounterpart →
        ∀ x, R'.handler x ≠ R.handler x → IsNtvId K.enc K.ntvAddr x

/-- **`L2OnlyCounterpartTouchesNonVaultIds`'s PREMISES HOLD, WITH A HANDLER THAT CHANGES.**
On an L2 router with a well-behaved vault, after the seed, the vault's registration of its
own token changes a handler. -/
def Properties.L2OnlyCounterpartTouchesNonVaultIdsWitness : Prop :=
  ∃ (K : Cfg) (ops : List Op) (R : Router) (op : Op) (R' : Router) (x : AssetId),
    K.side = .l2 ∧ MintsOnlyNtvIds K ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧
    ARun K empty ops R ∧ AStep K op R R' ∧ ¬ op.IsCounterpart ∧ R'.handler x ≠ R.handler x

/-- **EVERY RECORDED TRACKER SITS AT AN ID WITH A PREIMAGE FROM ITSELF.**  Along every run
from fresh storage, on either router, a nonzero tracker `t` sits only at an id equal to
`enc block.chainid t d`, or (for the vault) `enc block.chainid L2_NATIVE_TOKEN_VAULT_ADDR
d`, for some data word `d`.  No hash premise.

This is weak, because `d` is existential and not tied to the run.  An encoding that reaches
every id as `d` varies satisfies the conclusion in every router state, reachable or not
(`AllWritersStrong.TrackerHashedAdmitsUnreachableRouter`).  For a keccak-like encoding,
heuristically about `1 - 1/e` of all ids have such a preimage for any fixed `t`.  It does not
show that the owner cannot hand `t` an id hashed from someone else.  The `AllWritersStrong`
topic has the pinned forms:

* the call that recorded each tracker is in the run's log, at that call's own id
  (`RunTrackerRecorded`, no hash premise);
* `t` is never the tracker of an id hashed from another sender, when the encoding is
  injective on the run's logged triples plus that sender's triple
  (`RunTrackerNotHandedToOtherSenderOn`);
* without that premise it can be (`TrackerHandedToOtherSenderUnderCollision`). -/
def Properties.RunTrackerHashed : Prop :=
  ∀ (K : Cfg) (ops : List Op) (R : Router), ARun K empty ops R → TrackerHashed K R

end Contracts.AssetRouter.AllWriters
