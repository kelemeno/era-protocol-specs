import EraSpec.Contracts.AssetRouterBase.Specs.HandlerRegistrationRuns

/-!
# Properties: run-level `NoHijack`, under a premise on the run's own triples

Statements about `EraSpec.Contracts.AssetRouterBase.Specs.HandlerRegistrationRuns`.  Proofs
are in `EraSpec.Contracts.AssetRouterBase.Proofs.HandlerRegistrationRuns`.

`NoHijack` and `NtvTouchesOnlyItsOwnIds` take a global injectivity premise that no
encoding meets (`IdAssumptionsUnsatisfiable`), and their repaired forms are per call.
Here they are lifted to whole runs, as `NativeTokenVault.LoggedRunSound` lifts the
vault's registry results: log the run, and assume the id hash injective only on the
triples the run's own calls hashed (`loggedTriples`, at most one per call) plus the one
triple whose route is in question.

## What holds

* **The headline** (`LoggedRouteIsLastOwnWrite`).  For every logged run from any router,
  the route at an asset id, and its tracker, are exactly what the last logged call
  hashing that id's triple set, or what the run started with.  No call hashing another
  triple — another sender, other data, another chain's id — moved them.  The guard plays
  no part (`RouteIsLastOwnWriteWithoutGuard`); like `NoHijack` this is the
  caller-in-the-key mechanism.  Special cases: a run never touches a route it did not
  hash (`LoggedRunLeavesUnhashedRoutes`); at every step, a non-vault call leaves the ids
  of other senders alone (`LoggedRunNoHijack`) and the vault's call leaves the ids of
  every sender but `L2_NATIVE_TOKEN_VAULT_ADDR` alone (`LoggedRunNtvTouchesOnlyItsOwnIds`).
* **A custom route answers only to its registrant** (`LoggedRunCustomRouteAnswersToRegistrant`).
  With the guard added: the tracker of an id hashed from a non-vault sender never changes
  along the run, and its handler moves only by that sender's own calls.  The vault —
  which skips the tracker check and which anyone can drive through `registerToken` —
  never lands on it.
* **The vault's routes need no hash premise against non-vault callers**
  (`NtvRouteSurvivesNonVaultCalls`, from `VaultTrackerIsPermanent` and
  `NonVaultRunKeepsVaultRoutes`).  "No non-vault caller overwrites a handler installed by
  the vault" is the guard's doing: the vault's call records the vault as tracker, and the
  `require` is evaluated on the id itself, so no collision gets a non-vault caller past
  it.  Against every later call, the vault's own other registrations included, the route
  survives under the run-local premise alone (`LoggedRunKeepsVaultRoutes`); and as
  deployed — every vault call names the vault as handler — every route the vault holds
  points at the vault, with no hash premise, along every run from fresh storage
  (`VaultHeldRoutesPointAtVault`).
* **From fresh storage only the vault acts** (`OnlyVaultActsFromEmpty`), and on L2 that
  stays so with the router's other writers interleaved (`OnlyVaultActsAmidOtherWriters`).
  This is why the run results start from any router: in the single-writer model a
  custom tracker exists only if something outside the model (on L1, the owner's
  `setAssetDeploymentTracker`) put it there.

## Anti-vacuity, and why the premise is needed

* Each bounded result's premises hold on a four-call L1 run from the storage the owner's
  whitelisting leaves, with an encoding that is injective on the run's triples but
  collides off them: `…Satisfiable` below.  `LogAssumptionSatisfiable` gives an encoding
  for every log shorter than the id space.
* `LoggedCollisionTakesOverLiveRoute`: if the vault's token id collides with a live custom
  route — two triples of the log — one vault call takes the route over and locks its
  registrant out.  So the run-local premise cannot be dropped, and unlike
  `HijackUnderCollision` the route taken here was live.
* `HashAloneDoesNotProtectVaultRoutes`: with the `require` deleted, a non-vault caller at
  the vault's normalised address overwrites a vault route although the encoding is
  injective on the run's triples.  So the vault's routes are protected by the guard, not
  by the hash.
* `CollidingVaultCallMovesVaultRoute`: without its premise `LoggedRunKeepsVaultRoutes`
  fails in the model, through a later vault call for colliding data that names another
  handler — which the deployed vault never does.
-/

namespace Contracts.AssetRouter

/-! ## Logging loses nothing -/

/-- **LOGGING LOSES NO RUN.**  `Reach` and `ReachLog` have the same reachable states. -/
def Properties.ReachIffReachLog : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R S : Router),
    Reach enc thisChain ntv ntvAddr R S ↔ ∃ log, ReachLog enc thisChain ntv ntvAddr R S log

/-- **THE LOG DETERMINES THE RUN.**  A logged run ends where its calls, applied in order,
lead. -/
def Properties.ReachLogIsApplyCalls : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ R : Router)
    (log : List Call),
    ReachLog enc thisChain ntv ntvAddr R₀ R log → R = applyCalls enc thisChain ntv ntvAddr R₀ log

/-- **A LOGGED RUN SPLITS AT ANY POINT, AND LOGGED RUNS COMPOSE.**  So every prefix of a
logged run is a logged run, and a result stated for logged runs from any router applies
from any point of a run. -/
def Properties.ReachLogAppend : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ R : Router)
    (log₁ log₂ : List Call),
    ReachLog enc thisChain ntv ntvAddr R₀ R (log₁ ++ log₂) ↔
      ∃ S, ReachLog enc thisChain ntv ntvAddr R₀ S log₁ ∧ ReachLog enc thisChain ntv ntvAddr S R log₂

/-- **ONE TRIPLE PER CALL.** -/
def Properties.LoggedTriplesCardLe : Prop :=
  ∀ (thisChain : Chain) (ntv ntvAddr : Address) (log : List Call),
    (loggedTriples thisChain ntv ntvAddr log).card ≤ log.length

/-- `loggedTriples` is exactly the triples of the logged calls. -/
def Properties.MemLoggedTriples : Prop :=
  ∀ (thisChain : Chain) (ntv ntvAddr : Address) (log : List Call)
    (p : Chain × Address × AssetData),
    p ∈ loggedTriples thisChain ntv ntvAddr log ↔ ∃ c ∈ log, c.triple thisChain ntv ntvAddr = p

/-- **THE RUN-LOCAL PREMISE IS SATISFIABLE FOR EVERY REALISTIC LOG.**  For any log shorter
than the id space and any one further triple, some encoding is injective on the log's
triples together with that triple. -/
def Properties.LogAssumptionSatisfiable : Prop :=
  ∀ (thisChain : Chain) (ntv ntvAddr : Address) (log : List Call)
    (q : Chain × Address × AssetData),
    log.length < UInt256.size →
      ∃ enc : AssetIdOf, IdInjOn enc ↑(insert q (loggedTriples thisChain ntv ntvAddr log))

/-! ## The headline: every route is where its own registrant's last call put it -/

/-- **THE HEADLINE.**  For every logged run from any router `R₀`, and every triple `q` — the
asset whose route is in question — if the id hash is injective on the triples the run's
calls hashed together with `q`, then at the end the handler at `enc q` and its tracker are
exactly what the LAST logged call hashing `q` set (its `_assetHandlerAddress` and its
`msg.sender`), or what `R₀` held there if no logged call hashed `q`.  So no call hashing a
different triple — a different sender, different data, or a different chain — changed that
route.  Applied to the prefixes of the run (`ReachLogAppend`; a prefix's triples are among
the run's) it says the same at every point of the run. -/
def Properties.LoggedRouteIsLastOwnWrite : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ R : Router)
    (log : List Call),
    ReachLog enc thisChain ntv ntvAddr R₀ R log →
    ∀ q : Chain × Address × AssetData,
      IdInjOn enc ↑(insert q (loggedTriples thisChain ntv ntvAddr log)) →
      R.handler (enc q.1 q.2.1 q.2.2) = loggedHandler enc thisChain ntv ntvAddr R₀ log q
      ∧ R.tracker (enc q.1 q.2.1 q.2.2) = loggedTracker enc thisChain ntv ntvAddr R₀ log q

/-- **THE GUARD PLAYS NO PART IN IT.**  The same for any sequence of calls applied with the
`require` deleted.  As with `NoHijack`, the protection is that the key is hashed from the
caller; the hash premise is on the run's own triples and `q` only. -/
def Properties.RouteIsLastOwnWriteWithoutGuard : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ : Router)
    (log : List Call) (q : Chain × Address × AssetData),
    IdInjOn enc ↑(insert q (loggedTriples thisChain ntv ntvAddr log)) →
      (applyCalls enc thisChain ntv ntvAddr R₀ log).handler (enc q.1 q.2.1 q.2.2)
          = loggedHandler enc thisChain ntv ntvAddr R₀ log q
      ∧ (applyCalls enc thisChain ntv ntvAddr R₀ log).tracker (enc q.1 q.2.1 q.2.2)
          = loggedTracker enc thisChain ntv ntvAddr R₀ log q

/-- **A RUN NEVER TOUCHES A ROUTE IT DID NOT HASH.**  If no logged call hashed `q`, the run
leaves the handler and the tracker at `enc q` as `R₀` had them, given injectivity on the
run's triples and `q`.  This covers the routes the run's callers cannot name: an asset
whose registrant never called, and an id hashed with another chain's id (as the ids the
L1 counterpart installs on an L2 are). -/
def Properties.LoggedRunLeavesUnhashedRoutes : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ R : Router)
    (log : List Call),
    ReachLog enc thisChain ntv ntvAddr R₀ R log →
    ∀ q : Chain × Address × AssetData, q ∉ loggedTriples thisChain ntv ntvAddr log →
      IdInjOn enc ↑(insert q (loggedTriples thisChain ntv ntvAddr log)) →
      R.handler (enc q.1 q.2.1 q.2.2) = R₀.handler (enc q.1 q.2.1 q.2.2)
      ∧ R.tracker (enc q.1 q.2.1 q.2.2) = R₀.tracker (enc q.1 q.2.1 q.2.2)

/-- **RUN-LEVEL NO HIJACK.**  At every step of every logged run (the call `c` taken from the
state `S` after the prefix `pre`), a call by anyone but the vault leaves the route of every
id hashed on this chain from a different sender `s` as it was, given injectivity on the
run's triples and `(thisChain, s, d')`.  This is `NoHijack` with its global premise
replaced by the run-local one; like `NoHijack` it does not use the guard. -/
def Properties.LoggedRunNoHijack : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ R : Router)
    (log : List Call),
    ReachLog enc thisChain ntv ntvAddr R₀ R log →
    ∀ (pre post : List Call) (c : Call) (S T : Router), log = pre ++ c :: post →
      ReachLog enc thisChain ntv ntvAddr R₀ S pre → StepCall enc thisChain ntv ntvAddr c S T →
      c.caller ≠ ntv →
    ∀ (s : Address) (d' : AssetData), s ≠ c.caller →
      IdInjOn enc ↑(insert (thisChain, s, d') (loggedTriples thisChain ntv ntvAddr log)) →
      T.handler (enc thisChain s d') = S.handler (enc thisChain s d')

/-- **RUN-LEVEL: THE VAULT IS NO EXCEPTION.**  At every step of every logged run, a call by
the vault — which skips the tracker check, and which anyone can trigger through
`registerToken` — leaves the route of every id hashed on this chain from a sender other
than `L2_NATIVE_TOKEN_VAULT_ADDR` as it was, given injectivity on the run's triples and
that id's triple.  `NtvTouchesOnlyItsOwnIds` with the run-local premise. -/
def Properties.LoggedRunNtvTouchesOnlyItsOwnIds : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ R : Router)
    (log : List Call),
    ReachLog enc thisChain ntv ntvAddr R₀ R log →
    ∀ (pre post : List Call) (c : Call) (S T : Router), log = pre ++ c :: post →
      ReachLog enc thisChain ntv ntvAddr R₀ S pre → StepCall enc thisChain ntv ntvAddr c S T →
      c.caller = ntv →
    ∀ (s : Address) (d' : AssetData), s ≠ ntvAddr →
      IdInjOn enc ↑(insert (thisChain, s, d') (loggedTriples thisChain ntv ntvAddr log)) →
      T.handler (enc thisChain s d') = S.handler (enc thisChain s d')

/-- **A CUSTOM ROUTE ANSWERS ONLY TO ITS REGISTRANT.**  The guard and the run-local premise
together.  In every logged run from any router `R₀`, take an id hashed on this chain from
a sender `s` other than `L2_NATIVE_TOKEN_VAULT_ADDR`, with the id hash injective on the
run's triples and `(thisChain, s, d')`.  Then the run never changes that id's tracker; and
if it changed its handler, then `s` was already the tracker in `R₀` and some logged call
was `s`'s own, with data `d'`.  Neither the vault, whatever tokens are registered through
it, nor any other caller moved the route. -/
def Properties.LoggedRunCustomRouteAnswersToRegistrant : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ R : Router)
    (log : List Call),
    ReachLog enc thisChain ntv ntvAddr R₀ R log →
    ∀ (s : Address) (d' : AssetData), s ≠ ntvAddr →
      IdInjOn enc ↑(insert (thisChain, s, d') (loggedTriples thisChain ntv ntvAddr log)) →
      R.tracker (enc thisChain s d') = R₀.tracker (enc thisChain s d')
      ∧ (R.handler (enc thisChain s d') ≠ R₀.handler (enc thisChain s d') →
          R₀.tracker (enc thisChain s d') = s ∧ ∃ c ∈ log, c.caller = s ∧ c.data = d')

/-! ## Without any hash premise: the guard keeps the vault's routes

That no run lets a non-vault caller overwrite a handler installed by the vault needs no
hash premise.  The vault's call records the vault as the id's tracker; the `require` then
turns away every non-vault caller at that id, whatever the hash does, because the check is
on the written id itself; so the tracker stays the vault.  The hash premise is needed for
the other direction (`LoggedRunNtvTouchesOnlyItsOwnIds`,
`LoggedRunCustomRouteAnswersToRegistrant`), where the vault, which skips the check, could
land on somebody else's id. -/

/-- **ONCE THE VAULT IS AN ID'S TRACKER, IT STAYS THE TRACKER.**  No hash premise. -/
def Properties.VaultTrackerIsPermanent : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (S T : Router)
    (log : List Call),
    ReachLog enc thisChain ntv ntvAddr S T log → ∀ a, S.tracker a = ntv → T.tracker a = ntv

/-- **NON-VAULT CALLS NEVER MOVE A ROUTE THE VAULT HOLDS.**  No hash premise: along any
logged run in which no call is the vault's, every id whose tracker is the vault keeps its
handler. -/
def Properties.NonVaultRunKeepsVaultRoutes : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (S T : Router)
    (log : List Call),
    ReachLog enc thisChain ntv ntvAddr S T log → (∀ c ∈ log, c.caller ≠ ntv) →
    ∀ a, S.tracker a = ntv → T.handler a = S.handler a

/-- **A ROUTE THE VAULT INSTALLS SURVIVES EVERY LATER NON-VAULT CALL.**  No hash premise.
From any router — so at any point of any run (`ReachLogAppend`): once the vault's call `c`
has installed `c.handler` at its id `enc thisChain ntvAddr c.data`, any logged run of
non-vault calls leaves that handler there, with the vault as its tracker. -/
def Properties.NtvRouteSurvivesNonVaultCalls : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (S S' T : Router) (c : Call)
    (post : List Call),
    StepCall enc thisChain ntv ntvAddr c S S' → c.caller = ntv →
    ReachLog enc thisChain ntv ntvAddr S' T post → (∀ c' ∈ post, c'.caller ≠ ntv) →
      T.handler (enc thisChain ntvAddr c.data) = c.handler
      ∧ T.tracker (enc thisChain ntvAddr c.data) = ntv

/-- **…AND EVERY LATER CALL, UNDER THE RUN-LOCAL PREMISE ALONE.**  In every logged run whose
id hash is injective on the triples the run hashed (the vault's own triple is one of them):
once the vault's call `c` has installed `c.handler` at `enc thisChain ntvAddr c.data`, every
later call — a non-vault call, or a vault call for other data — leaves that handler there,
with the vault as tracker.  The guard turns the non-vault calls away; the premise keeps the
vault's later registrations, which skip the guard and which anyone can trigger through
`registerToken`, off this id.  (A later vault call for the same data writes it again.) -/
def Properties.LoggedRunKeepsVaultRoutes : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ R : Router)
    (log : List Call),
    ReachLog enc thisChain ntv ntvAddr R₀ R log →
    IdInjOn enc ↑(loggedTriples thisChain ntv ntvAddr log) →
    ∀ (pre post : List Call) (c : Call), log = pre ++ c :: post → c.caller = ntv →
      (∀ c' ∈ post, c'.caller = ntv → c'.data ≠ c.data) →
      R.handler (enc thisChain ntvAddr c.data) = c.handler
      ∧ R.tracker (enc thisChain ntvAddr c.data) = ntv

/-- **AS DEPLOYED, A ROUTE THE VAULT HOLDS POINTS AT THE VAULT.**  No hash premise, and not
even the guard: if every vault call in the run names the vault itself as handler — the one
vault call site at the pin, `_unsafeRegisterNativeToken`, passes `address(this)`
(`NativeTokenVaultBase.sol:518-521`) — and every id the vault holds at the start routes to
the vault (fresh storage: there are none), then at the end every id whose tracker is the
vault routes to the vault.  With `VaultTrackerIsPermanent`, a route the deployed vault
installed therefore stays the vault's in every run, hash or no hash; the premise of
`LoggedRunKeepsVaultRoutes` is needed only because a model vault call may name any handler. -/
def Properties.VaultHeldRoutesPointAtVault : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ R : Router)
    (log : List Call),
    ReachLog enc thisChain ntv ntvAddr R₀ R log →
    (∀ c ∈ log, c.caller = ntv → c.handler = ntv) →
    (∀ a, R₀.tracker a = ntv → R₀.handler a = ntv) →
    ∀ a, R.tracker a = ntv → R.handler a = ntv

/-! ## From fresh storage, and on L2, only the vault acts -/

/-- Fresh storage records no tracker at all, so in particular none but the vault. -/
def Properties.EmptyHasVaultOnlyTrackers : Prop :=
  ∀ ntv : Address, VaultOnlyTrackers ntv empty

/-- **ONLY THE VAULT PASSES THE GUARD** when every tracker is unset or the vault, because
`msg.sender` is never zero. -/
def Properties.VaultOnlyTrackersAdmitOnlyTheVault : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R : Router)
    (caller : Address) (d : AssetData),
    VaultOnlyTrackers ntv R → SetGuard enc thisChain ntv ntvAddr R caller d → caller = ntv

/-- A guarded call keeps every tracker unset or the vault. -/
def Properties.StepKeepsVaultOnlyTrackers : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R S : Router),
    Step enc thisChain ntv ntvAddr R S → VaultOnlyTrackers ntv R → VaultOnlyTrackers ntv S

/-- **FROM FRESH STORAGE, EVERY SUCCESSFUL CALL IS THE VAULT'S.**  On every logged run of
this model from `empty`, every call is by the vault.  A custom deployment tracker can never
be bootstrapped through `_setAssetHandlerAddressThisChain` itself (the vault's call records
the vault, not a custom tracker); it needs a write from outside this model. -/
def Properties.OnlyVaultActsFromEmpty : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R : Router)
    (log : List Call),
    ReachLog enc thisChain ntv ntvAddr empty R log → ∀ c ∈ log, c.caller = ntv

/-- **…AND ON L2 THAT STAYS SO WITH THE OTHER WRITERS INTERLEAVED.**  Along any run from
fresh storage that interleaves guarded calls with arbitrary writes leaving the tracker
mapping alone — which is what every other L2 writer at the pin does (see the Specs header)
— every guarded call is by the vault.  So on L2 the non-vault half of `NoHijack` has no
instances: custom assets get their L2 routes through the counterpart path, not this one. -/
def Properties.OnlyVaultActsAmidOtherWriters : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R : Router)
    (log : List Call),
    ReachAmidOtherWriters enc thisChain ntv ntvAddr empty R log → ∀ c ∈ log, c.caller = ntv

/-! ## Anti-vacuity

Each witness instantiates the premises of one result literally, mostly on one L1 run of
four calls from the storage the owner's `setAssetDeploymentTracker` leaves on fresh storage
(custom registrant `s` points its asset, the vault registers a token, `s` re-points its
asset, the vault registers another token), with an encoding injective on the run's triples
that maps one of them and a triple the run never hashed to the same id.  So the run-local
premise is strictly weaker than any global one (which no encoding meets anyway,
`IdAssumptionsUnsatisfiable`). -/

/-- **THE HEADLINE'S PREMISES HOLD, NONTRIVIALLY.**  A logged run from the owner's
whitelisting state, with a vault call and a non-vault call, and a triple `q` whose last
logged call was followed by other calls and whose route is live at the end, under an
encoding injective on the run's triples and `q` that collides off them. -/
def Properties.LoggedRouteIsLastOwnWriteSatisfiable : Prop :=
  ∃ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ R : Router)
    (log : List Call) (q : Chain × Address × AssetData),
    ReachLog enc thisChain ntv ntvAddr R₀ R log
    ∧ IdInjOn enc ↑(insert q (loggedTriples thisChain ntv ntvAddr log))
    ∧ (∃ d t, R₀ = afterSetDeploymentTracker enc thisChain empty d t)
    ∧ (∃ c ∈ log, c.caller = ntv) ∧ (∃ c ∈ log, c.caller ≠ ntv)
    ∧ (∃ (pre post : List Call) (c : Call), log = pre ++ c :: post
        ∧ lastCallOn thisChain ntv ntvAddr log q = some c ∧ post ≠ [])
    ∧ R.handler (enc q.1 q.2.1 q.2.2) ≠ 0
    ∧ ∃ p ∈ loggedTriples thisChain ntv ntvAddr log, ∃ p',
        p' ∉ insert q (loggedTriples thisChain ntv ntvAddr log)
        ∧ enc p.1 p.2.1 p.2.2 = enc p'.1 p'.2.1 p'.2.2

/-- **`LoggedRunLeavesUnhashedRoutes`'s PREMISES HOLD, NONTRIVIALLY.**  The run includes a
vault call, and the unhashed route is live from the start (as one installed by another
writer would be). -/
def Properties.LoggedRunLeavesUnhashedRoutesSatisfiable : Prop :=
  ∃ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ R : Router)
    (log : List Call) (q : Chain × Address × AssetData),
    ReachLog enc thisChain ntv ntvAddr R₀ R log
    ∧ q ∉ loggedTriples thisChain ntv ntvAddr log
    ∧ IdInjOn enc ↑(insert q (loggedTriples thisChain ntv ntvAddr log))
    ∧ (∃ c ∈ log, c.caller = ntv)
    ∧ R₀.handler (enc q.1 q.2.1 q.2.2) ≠ 0

/-- **`LoggedRunNoHijack`'s PREMISES HOLD, NONTRIVIALLY.**  The non-vault call is taken while
the route it is claimed not to touch is the vault's, and live. -/
def Properties.LoggedRunNoHijackSatisfiable : Prop :=
  ∃ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ R : Router)
    (log pre post : List Call) (c : Call) (S T : Router) (s : Address) (d' : AssetData),
    ReachLog enc thisChain ntv ntvAddr R₀ R log ∧ log = pre ++ c :: post
    ∧ ReachLog enc thisChain ntv ntvAddr R₀ S pre ∧ StepCall enc thisChain ntv ntvAddr c S T
    ∧ c.caller ≠ ntv ∧ s ≠ c.caller
    ∧ IdInjOn enc ↑(insert (thisChain, s, d') (loggedTriples thisChain ntv ntvAddr log))
    ∧ (∃ d t, R₀ = afterSetDeploymentTracker enc thisChain empty d t)
    ∧ s = ntvAddr ∧ S.tracker (enc thisChain s d') = ntv ∧ S.handler (enc thisChain s d') ≠ 0
    ∧ ∃ p ∈ loggedTriples thisChain ntv ntvAddr log, ∃ p',
        p' ∉ insert (thisChain, s, d') (loggedTriples thisChain ntv ntvAddr log)
        ∧ enc p.1 p.2.1 p.2.2 = enc p'.1 p'.2.1 p'.2.2

/-- **`LoggedRunNtvTouchesOnlyItsOwnIds`'s PREMISES HOLD, NONTRIVIALLY.**  The vault's call
is taken while the custom route it is claimed not to touch is live. -/
def Properties.LoggedRunNtvTouchesOnlyItsOwnIdsSatisfiable : Prop :=
  ∃ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ R : Router)
    (log pre post : List Call) (c : Call) (S T : Router) (s : Address) (d' : AssetData),
    ReachLog enc thisChain ntv ntvAddr R₀ R log ∧ log = pre ++ c :: post
    ∧ ReachLog enc thisChain ntv ntvAddr R₀ S pre ∧ StepCall enc thisChain ntv ntvAddr c S T
    ∧ c.caller = ntv ∧ s ≠ ntvAddr
    ∧ IdInjOn enc ↑(insert (thisChain, s, d') (loggedTriples thisChain ntv ntvAddr log))
    ∧ (∃ d t, R₀ = afterSetDeploymentTracker enc thisChain empty d t)
    ∧ S.tracker (enc thisChain s d') = s ∧ S.handler (enc thisChain s d') ≠ 0
    ∧ ∃ p ∈ loggedTriples thisChain ntv ntvAddr log, ∃ p',
        p' ∉ insert (thisChain, s, d') (loggedTriples thisChain ntv ntvAddr log)
        ∧ enc p.1 p.2.1 p.2.2 = enc p'.1 p'.2.1 p'.2.2

/-- **`LoggedRunCustomRouteAnswersToRegistrant`'s PREMISES HOLD, NONTRIVIALLY.**  The run
includes a vault call, and the custom route did move, so the implication's antecedent holds. -/
def Properties.LoggedRunCustomRouteAnswersToRegistrantSatisfiable : Prop :=
  ∃ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ R : Router)
    (log : List Call) (s : Address) (d' : AssetData),
    ReachLog enc thisChain ntv ntvAddr R₀ R log ∧ s ≠ ntvAddr
    ∧ IdInjOn enc ↑(insert (thisChain, s, d') (loggedTriples thisChain ntv ntvAddr log))
    ∧ (∃ d t, R₀ = afterSetDeploymentTracker enc thisChain empty d t)
    ∧ (∃ c ∈ log, c.caller = ntv)
    ∧ R.handler (enc thisChain s d') ≠ R₀.handler (enc thisChain s d')
    ∧ ∃ p ∈ loggedTriples thisChain ntv ntvAddr log, ∃ p',
        p' ∉ insert (thisChain, s, d') (loggedTriples thisChain ntv ntvAddr log)
        ∧ enc p.1 p.2.1 p.2.2 = enc p'.1 p'.2.1 p'.2.2

/-- **THE GUARD RESULTS' PREMISES HOLD, NONTRIVIALLY.**  A vault call `c` from `S` to `S'`,
then a nonempty logged run of non-vault calls from `S'` to `T` that changes the router:
the premises of `NtvRouteSurvivesNonVaultCalls`, and — with `S'`, `post` and the vault's id
— those of `VaultTrackerIsPermanent` and `NonVaultRunKeepsVaultRoutes`. -/
def Properties.VaultRouteGuardSatisfiable : Prop :=
  ∃ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (S S' T : Router) (c : Call)
    (post : List Call),
    StepCall enc thisChain ntv ntvAddr c S S' ∧ c.caller = ntv
    ∧ ReachLog enc thisChain ntv ntvAddr S' T post ∧ (∀ c' ∈ post, c'.caller ≠ ntv)
    ∧ S'.tracker (enc thisChain ntvAddr c.data) = ntv ∧ c.handler ≠ 0
    ∧ post ≠ [] ∧ T ≠ S'

/-- **`LoggedRunKeepsVaultRoutes`'s PREMISES HOLD, NONTRIVIALLY.**  After the vault's call
come both a non-vault call and a vault call for other data — the case the premise is
for — under an encoding injective on the run's triples that collides off them. -/
def Properties.LoggedRunKeepsVaultRoutesSatisfiable : Prop :=
  ∃ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ R : Router)
    (log pre post : List Call) (c : Call),
    ReachLog enc thisChain ntv ntvAddr R₀ R log
    ∧ IdInjOn enc ↑(loggedTriples thisChain ntv ntvAddr log)
    ∧ log = pre ++ c :: post ∧ c.caller = ntv
    ∧ (∀ c' ∈ post, c'.caller = ntv → c'.data ≠ c.data)
    ∧ (∃ d t, R₀ = afterSetDeploymentTracker enc thisChain empty d t)
    ∧ (∃ c' ∈ post, c'.caller = ntv) ∧ (∃ c' ∈ post, c'.caller ≠ ntv)
    ∧ ∃ p ∈ loggedTriples thisChain ntv ntvAddr log, ∃ p',
        p' ∉ loggedTriples thisChain ntv ntvAddr log
        ∧ enc p.1 p.2.1 p.2.2 = enc p'.1 p'.2.1 p'.2.2

/-- **`VaultHeldRoutesPointAtVault`'s PREMISES HOLD, NONTRIVIALLY.**  A logged run from the
owner's whitelisting state, with a non-vault call, every vault call naming the vault, and
some id held by the vault at the end. -/
def Properties.VaultHeldRoutesPointAtVaultSatisfiable : Prop :=
  ∃ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R₀ R : Router)
    (log : List Call),
    ReachLog enc thisChain ntv ntvAddr R₀ R log
    ∧ (∀ c ∈ log, c.caller = ntv → c.handler = ntv)
    ∧ (∀ a, R₀.tracker a = ntv → R₀.handler a = ntv)
    ∧ (∃ d t, R₀ = afterSetDeploymentTracker enc thisChain empty d t)
    ∧ (∃ c ∈ log, c.caller ≠ ntv) ∧ ∃ a, R.tracker a = ntv

/-- **THE FROM-EMPTY RESULTS' PREMISES HOLD, NONTRIVIALLY.**  A guarded vault call from
fresh storage — a `Step` from a state with vault-only trackers, through a passing guard —
installs a live route; and a run from fresh storage that interleaves another writer's
handler write with that call is a `ReachAmidOtherWriters` run. -/
def Properties.FromEmptyWitness : Prop :=
  ∃ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (d : AssetData)
    (h : Address) (R R' : Router),
    VaultOnlyTrackers ntv empty ∧ SetGuard enc thisChain ntv ntvAddr empty ntv d
    ∧ Step enc thisChain ntv ntvAddr empty R ∧ ReachLog enc thisChain ntv ntvAddr empty R [⟨ntv, d, h⟩]
    ∧ R.handler (enc thisChain ntvAddr d) = h ∧ h ≠ 0
    ∧ ReachAmidOtherWriters enc thisChain ntv ntvAddr empty R' [⟨ntv, d, h⟩] ∧ R' ≠ R

/-! ## Why the run-local premise cannot be dropped, and why the vault's routes are the guard's -/

/-- **ONE COLLISION ON THE LOG TAKES A LIVE ROUTE OVER.**  From the storage the owner's
`setAssetDeploymentTracker(d', s)` leaves on fresh storage: `s` points its asset at a live
handler `h`; then the vault registers token data `d` — which anyone can make it do through
`registerToken` — and the vault's id collides with `s`'s.  The vault's call re-points `s`'s
live route at the vault, records the vault as its tracker, and `s` can no longer re-point
its own asset.  The colliding triples are the two the run hashed, so it is exactly the
run-local premise that fails (last conjunct). -/
def Properties.LoggedCollisionTakesOverLiveRoute : Prop :=
  ∃ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr s : Address) (d d' : AssetData)
    (h : Address) (R₀ S R : Router),
    s ≠ ntv ∧ s ≠ ntvAddr ∧ h ≠ 0 ∧ h ≠ ntv
    ∧ R₀ = afterSetDeploymentTracker enc thisChain empty d' s
    ∧ ReachLog enc thisChain ntv ntvAddr R₀ S [⟨s, d', h⟩]
    ∧ S.handler (enc thisChain s d') = h
    ∧ StepCall enc thisChain ntv ntvAddr ⟨ntv, d, ntv⟩ S R
    ∧ R.handler (enc thisChain s d') = ntv ∧ R.tracker (enc thisChain s d') = ntv
    ∧ ¬ SetGuard enc thisChain ntv ntvAddr R s d'
    ∧ enc thisChain ntvAddr d = enc thisChain s d'
    ∧ ¬ IdInjOn enc ↑(loggedTriples thisChain ntv ntvAddr [⟨s, d', h⟩, ⟨ntv, d, ntv⟩])

/-- **THE HASH ALONE DOES NOT KEEP THE VAULT'S ROUTES.**  With the `require` deleted
(`applyCalls`), from fresh storage: the vault installs its route for data `d`, then a
non-vault caller whose address is the vault's normalised one, `ntvAddr`, writes the same
id and re-points it — although the encoding is injective on the run's triples (both calls
hash the same one).  With the guard that second call is rejected (last conjunct).  So
`NtvRouteSurvivesNonVaultCalls` is the guard's result, not the hash's.  (On L2 the vault IS
at `ntvAddr`; on L1 it is not, and nobody holds `ntvAddr` there, but no hash property rules
the call out.) -/
def Properties.HashAloneDoesNotProtectVaultRoutes : Prop :=
  ∃ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (d : AssetData)
    (h : Address),
    ntvAddr ≠ ntv ∧ h ≠ ntv
    ∧ IdInjOn enc ↑(loggedTriples thisChain ntv ntvAddr [⟨ntv, d, ntv⟩, ⟨ntvAddr, d, h⟩])
    ∧ (applyCalls enc thisChain ntv ntvAddr empty [⟨ntv, d, ntv⟩]).handler
        (enc thisChain ntvAddr d) = ntv
    ∧ (applyCalls enc thisChain ntv ntvAddr empty [⟨ntv, d, ntv⟩, ⟨ntvAddr, d, h⟩]).handler
        (enc thisChain ntvAddr d) = h
    ∧ ¬ SetGuard enc thisChain ntv ntvAddr (applyCalls enc thisChain ntv ntvAddr empty [⟨ntv, d, ntv⟩])
        ntvAddr d

/-- **IN THE MODEL, A COLLIDING LATER VAULT CALL MOVES THE VAULT'S ROUTE.**  Without its
run-local premise `LoggedRunKeepsVaultRoutes` fails: from fresh storage the vault registers
data `d` naming itself as handler, then data `d' ≠ d` whose id collides with it, naming
another handler `h`, and the route for `d` now points at `h`.  The deployed vault cannot
do the second half — it always names itself, which is why `VaultHeldRoutesPointAtVault`
needs no hash premise — so this refutes the model statement without its premise, not the
deployed router. -/
def Properties.CollidingVaultCallMovesVaultRoute : Prop :=
  ∃ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (d d' : AssetData)
    (h : Address) (R : Router),
    d ≠ d' ∧ h ≠ ntv
    ∧ ReachLog enc thisChain ntv ntvAddr empty R [⟨ntv, d, ntv⟩, ⟨ntv, d', h⟩]
    ∧ enc thisChain ntvAddr d = enc thisChain ntvAddr d'
    ∧ R.handler (enc thisChain ntvAddr d) = h

end Contracts.AssetRouter
