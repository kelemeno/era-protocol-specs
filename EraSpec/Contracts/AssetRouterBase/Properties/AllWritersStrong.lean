import EraSpec.Contracts.AssetRouterBase.Specs.AllWritersStrong

/-!
# Properties: where each deployment tracker came from, pinned to the run's log

Statements about `EraSpec.Contracts.AssetRouterBase.Specs.AllWritersStrong`.  Proofs are
in `EraSpec.Contracts.AssetRouterBase.Proofs.AllWritersStrong`.

`AllWriters.Properties.RunTrackerHashed` is weak.  Its preimage is existential, so an
encoding that reaches every id as the data word varies satisfies its conclusion in every
router state (`TrackerHashedAdmitsUnreachableRouter`).  This topic restates it with the
preimage named by the run.  It also states the reading that property's docstring claimed,
that the owner cannot hand a tracker an id hashed from someone else.  That reading needs a
hash premise; here the premise is run-local.

## No hash premise

* **Each tracker was recorded by a logged call, at that call's own id**
  (`RunTrackerRecorded`).  The call is the owner's `setAssetDeploymentTracker(d, t)`, or a
  registration by `t` itself.  This implies `TrackerHashed`
  (`TrackerRecordedImpliesTrackerHashed`).  It promotes and sharpens the internal lemma
  `run_trackerSource` of `Proofs/CounterpartGate.lean`.
* **The log determines the tracker mapping** (`RunTrackerIsLogReplay`).  After any run, from
  any start, the mapping is the log's tracker writes replayed on the start mapping.  The
  guards and the handler mapping play no part.
* **At most one tracked id per logged triple** (`RunTrackedIdsCardLe`).  `TrackerHashed`
  allows every id to carry a tracker.
* **At a triple's id, the tracker matches that triple's sender, or the log holds a clash**
  (`RunTrackerAtTripleOrLoggedClash`).  The clash (`LoggedClash`) names a triple of the
  run's own finite log, as in `CounterpartGate.L1CounterpartAtVaultIdOrLoggedClash`.

## Under the run-local premise: no logged triple other than `q` has `q`'s id

The premise is `¬ LoggedClash K ops q`.  Injectivity on the run's logged triples plus `q`
implies it (`IdInjOnExcludesLoggedClash`), and it can hold when the log itself collides
(`LastOwnWriteHoldsDespiteClashElsewhere`).

* **The owner cannot hand `t` an id hashed from someone else**
  (`RunTrackerNotHandedToOtherSenderOn`).  If `q`'s sender is neither `t` nor, for the
  vault, `L2_NATIVE_TOKEN_VAULT_ADDR`, then `t` is not the tracker of `enc q`.
* **The tracker at `enc q` is what the last logged call hashing `q` recorded**
  (`RunTrackerIsLastOwnWriteOn`), or the start router's if no logged call hashed `q`.

## Witnesses and countermodels

* `RunTrackerRecordedWitness`: an L1 run in which one tracker is explained only by an owner
  write.  Another, the vault, is explained only by a registration, at an id not hashed from
  the vault's own address.  So neither disjunct of `TrackerRecorded` can be dropped.  The
  encoding is injective on the log, and the bound of `RunTrackedIdsCardLe` is attained.
* `RunTrackerNotHandedToOtherSenderOnWitness`: the premises hold.  A custom tracker is live,
  and the victim is a vault asset whose route is live and tracked.
* `TrackerHandedToOtherSenderUnderCollision`: with a logged clash, the reading fails.  A custom
  tracker (in the proof, recorded by one owner write) ends at a vault triple's id.  The encoding is injective on the
  run's log; it is the victim's triple that collides.
* `RunTrackerIsLastOwnWriteOnWitness`: the last write wins.  On L1 the vault registers a
  token.  Then the owner's `setAssetDeploymentTracker(d, L2_NATIVE_TOKEN_VAULT_ADDR)`, whose
  id is that token's vault id, overwrites the vault's tracker there.
* `LastOwnWriteHoldsDespiteClashElsewhere`: two logged custom triples collide, and the
  vault triple's tracker is still the last own write.
* `TrackerHashedAdmitsUnreachableRouter`: the weakness of the original, formally.
-/

namespace Contracts.AssetRouter.AllWriters

/-! ## No hash premise -/

/-- **EVERY TRACKER WAS RECORDED BY A LOGGED CALL, AT THAT CALL'S OWN ID.**  Along every run
from fresh storage, on either router, take any id `a` whose tracker `t` is nonzero.  Then
the run's log holds one of two calls with some data word `d`:

* the owner's `setAssetDeploymentTracker(d, t)`, and `a = enc block.chainid t d`; or
* a registration by `t` itself, and `a` is the id it writes.

No hash premise.

This is the pinned form of `AllWriters.Properties.RunTrackerHashed`.  Its data word `d` is
an argument of a call in the log, not an arbitrary preimage.  The run of
`RunTrackerRecordedWitness` meets the premise with two nonzero trackers. -/
def Properties.RunTrackerRecorded : Prop :=
  ∀ (K : Cfg) (ops : List Op) (R : Router), ARun K empty ops R → TrackerRecorded K ops R

/-- **THE PINNED FORM IMPLIES THE ORIGINAL.**  For any log and any router state,
`TrackerRecorded` implies `TrackerHashed`.  The premise holds on every run
(`RunTrackerRecorded`).  So `RunTrackerRecorded` is at least as strong as
`AllWriters.Properties.RunTrackerHashed`.  It is strictly stronger:
`TrackerHashedAdmitsUnreachableRouter`. -/
def Properties.TrackerRecordedImpliesTrackerHashed : Prop :=
  ∀ (K : Cfg) (ops : List Op) (R : Router), TrackerRecorded K ops R → TrackerHashed K R

/-- **THE LOG DETERMINES THE TRACKER MAPPING.**  Along every run, on either router and from
any start router, the tracker mapping at the end is the log's tracker writes replayed in
order on the start router's tracker mapping.  No hash premise.  Nothing about the guards or
the handler mapping is needed either: they decide which calls succeed, not what a
successful call writes.  The run of `RunTrackerRecordedWitness` changes the mapping at two
ids. -/
def Properties.RunTrackerIsLogReplay : Prop :=
  ∀ (K : Cfg) (R₀ : Router) (ops : List Op) (R : Router), ARun K R₀ ops R →
    R.tracker = replayTrackers K R₀.tracker ops

/-- **AT MOST ONE TRACKED ID PER LOGGED TRIPLE.**  Along every run from fresh storage, take
any finite set of ids that all carry a nonzero tracker.  It has at most as many elements as
the run has logged triples, so at most as many as the run has calls
(`AllWriters.Properties.LoggedTriplesCardLe`).  No hash premise.  `TrackerHashed` bounds
nothing of the kind (`TrackerHashedAdmitsUnreachableRouter`).  The bound is attained on the
run of `RunTrackerRecordedWitness`. -/
def Properties.RunTrackedIdsCardLe : Prop :=
  ∀ (K : Cfg) (ops : List Op) (R : Router), ARun K empty ops R →
    ∀ A : Finset AssetId, (∀ a ∈ A, R.tracker a ≠ 0) → A.card ≤ (loggedTriples K ops).card

/-- **AT A TRIPLE'S ID, THE TRACKER MATCHES THE TRIPLE'S SENDER, OR THE LOG HOLDS A CLASH.**
Along every run from fresh storage, take any triple `q` whose id carries a nonzero tracker
`t`.  Then one of two things holds:

* `q` is one of the run's logged triples, on this chain, and its sender is `t` or, when
  `t` is the vault, `L2_NATIVE_TOKEN_VAULT_ADDR`;
* the log holds a clash at `q` (`LoggedClash`): a logged triple other than `q` has `q`'s
  id.

No hash premise.  `RunTrackerNotHandedToOtherSenderOnWitness` is an instance where the
first disjunct holds, and `TrackerHandedToOtherSenderUnderCollision` one where only the
clash does. -/
def Properties.RunTrackerAtTripleOrLoggedClash : Prop :=
  ∀ (K : Cfg) (ops : List Op) (R : Router), ARun K empty ops R →
    ∀ q : Chain × Address × AssetData, R.tracker (K.enc q.1 q.2.1 q.2.2) ≠ 0 →
      (q ∈ loggedTriples K ops ∧ q.1 = K.thisChain ∧
        (q.2.1 = R.tracker (K.enc q.1 q.2.1 q.2.2) ∨
          (R.tracker (K.enc q.1 q.2.1 q.2.2) = K.ntv ∧ q.2.1 = K.ntvAddr))) ∨
      LoggedClash K ops q

/-! ## Under the run-local premise -/

/-- **INJECTIVITY ON THE LOG PLUS `q` EXCLUDES A LOGGED CLASH AT `q`.**  So the per-triple
results below, stated under `¬ LoggedClash K ops q`, hold in particular under the run-local
premise used elsewhere in this folder.  The witnesses below meet both. -/
def Properties.IdInjOnExcludesLoggedClash : Prop :=
  ∀ (K : Cfg) (ops : List Op) (q : Chain × Address × AssetData),
    IdInjOn K.enc (↑(loggedTriples K ops) ∪ {q}) → ¬ LoggedClash K ops q

/-- **THE OWNER CANNOT HAND A TRACKER AN ID HASHED FROM SOMEONE ELSE.**  Along every run
from fresh storage, take a nonzero address `t` and a triple `q` whose sender is someone
else: not `t`, and not `L2_NATIVE_TOKEN_VAULT_ADDR` when `t` is the vault.  If no logged
triple other than `q` has `q`'s id, then `t` is not the tracker of `enc q`.

This is the reading `AllWriters.Properties.RunTrackerHashed`'s docstring claimed.  The hash
premise is needed (`TrackerHandedToOtherSenderUnderCollision`).  It is run-local: it
compares `q` with the run's logged triples only, one per call
(`AllWriters.Properties.LoggedTriplesCardLe`), and injectivity on those plus `q` implies it
(`IdInjOnExcludesLoggedClash`).  `RunTrackerNotHandedToOtherSenderOnWitness` meets every
premise. -/
def Properties.RunTrackerNotHandedToOtherSenderOn : Prop :=
  ∀ (K : Cfg) (ops : List Op) (R : Router), ARun K empty ops R →
    ∀ (q : Chain × Address × AssetData) (t : Address), t ≠ 0 → q.2.1 ≠ t →
      (t = K.ntv → q.2.1 ≠ K.ntvAddr) → ¬ LoggedClash K ops q →
        R.tracker (K.enc q.1 q.2.1 q.2.2) ≠ t

/-- **THE TRACKER AT A TRIPLE'S ID IS THE LAST OWN WRITE.**  Along every run, on either
router and from any start router `R₀`, take any triple `q`.  Suppose no logged triple other
than `q` has `q`'s id.  Then the tracker at `enc q` at the end is the value recorded by the
last logged call that hashed `q`.  If no logged call hashed `q`, it is `R₀`'s.

This is the tracker half of `Contracts.AssetRouter.Properties.LoggedRouteIsLastOwnWrite`,
for every writer, under a weaker premise: the log may collide elsewhere
(`LastOwnWriteHoldsDespiteClashElsewhere`).  `RunTrackerIsLastOwnWriteOnWitness` meets the
premise with two writes to the same triple that record different values. -/
def Properties.RunTrackerIsLastOwnWriteOn : Prop :=
  ∀ (K : Cfg) (R₀ : Router) (ops : List Op) (R : Router), ARun K R₀ ops R →
    ∀ q : Chain × Address × AssetData, ¬ LoggedClash K ops q →
      R.tracker (K.enc q.1 q.2.1 q.2.2) =
        (lastTrackerWriteOn K ops q).getD (R₀.tracker (K.enc q.1 q.2.1 q.2.2))

/-! ## Witnesses and countermodels -/

/-- **`RunTrackerRecorded` FIRES, AND NEITHER DISJUNCT CAN BE DROPPED.**  Take an L1 router
whose vault address differs from `L2_NATIVE_TOKEN_VAULT_ADDR`, and a run from fresh storage
whose encoding is injective on its logged triples.  The run ends with two distinct tracked
ids `a` and `b`:

* `a`'s tracker never registered in the run, so only an owner write explains it;
* `b`'s tracker is the vault, which no owner write in the run names, so only a registration
  explains it.  `b` is not hashed from the vault's own address with any data word, so the
  vault's normalisation to `L2_NATIVE_TOKEN_VAULT_ADDR` is needed too.

The run has two logged triples, so `{a, b}` attains the bound of `RunTrackedIdsCardLe`. -/
def Properties.RunTrackerRecordedWitness : Prop :=
  ∃ (K : Cfg) (ops : List Op) (R : Router) (a b : AssetId),
    K.side = .l1 ∧ K.ntv ≠ K.ntvAddr ∧ ARun K empty ops R ∧
    IdInjOn K.enc ↑(loggedTriples K ops) ∧ a ≠ b ∧ (loggedTriples K ops).card = 2 ∧
    R.tracker a ≠ 0 ∧ (∀ d h, Op.register (R.tracker a) d h ∉ ops) ∧
    R.tracker b = K.ntv ∧ (∀ d, Op.setTracker d (R.tracker b) ∉ ops) ∧
    (∀ d, b ≠ K.enc K.thisChain K.ntv d)

/-- **`RunTrackerNotHandedToOtherSenderOn`'S PREMISES HOLD, WITH BOTH SIDES LIVE.**  An L1 run
from fresh storage in which the owner records a custom tracker `t`, not the vault, and the
vault registers a token.  The victim `q` is that token's vault triple, whose sender
`L2_NATIVE_TOKEN_VAULT_ADDR` is not `t`.  The encoding is injective on the log plus `q`, so
there is no logged clash at `q`.  `t` is the tracker of some id, and the victim's route is
live with a nonzero tracker. -/
def Properties.RunTrackerNotHandedToOtherSenderOnWitness : Prop :=
  ∃ (K : Cfg) (ops : List Op) (R : Router) (q : Chain × Address × AssetData) (t : Address)
    (a : AssetId),
    K.side = .l1 ∧ ARun K empty ops R ∧ t ≠ 0 ∧ t ≠ K.ntv ∧ q.2.1 = K.ntvAddr ∧ q.2.1 ≠ t ∧
    (t = K.ntv → q.2.1 ≠ K.ntvAddr) ∧ IdInjOn K.enc (↑(loggedTriples K ops) ∪ {q}) ∧
    ¬ LoggedClash K ops q ∧ R.tracker a = t ∧ R.tracker (K.enc q.1 q.2.1 q.2.2) ≠ 0 ∧
    R.handler (K.enc q.1 q.2.1 q.2.2) ≠ 0

/-- **WITH A LOGGED CLASH, THE OWNER CAN HAND A TRACKER AN ID HASHED FROM SOMEONE ELSE.**  An
L1 run from fresh storage in which a custom tracker `t` is recorded (in the proof, by a
single owner write).  The encoding is injective on the run's logged triples.  Yet `t` ends
as the tracker of the id of a vault triple `q`.  `q`'s sender `L2_NATIVE_TOKEN_VAULT_ADDR`
is neither `t` nor, as `t` is not the vault, its normalised form.  The cause is a logged
clash: a logged triple other than `q` (in the proof, the owner's) has `q`'s id.

So the premise of `RunTrackerNotHandedToOtherSenderOn` is load-bearing, and injectivity on
the log alone does not give it.  Without a hash premise, the reading of
`AllWriters.Properties.RunTrackerHashed`'s docstring is false. -/
def Properties.TrackerHandedToOtherSenderUnderCollision : Prop :=
  ∃ (K : Cfg) (ops : List Op) (R : Router) (q : Chain × Address × AssetData) (t : Address),
    K.side = .l1 ∧ ARun K empty ops R ∧ t ≠ 0 ∧ q.2.1 = K.ntvAddr ∧ q.2.1 ≠ t ∧
    (t = K.ntv → q.2.1 ≠ K.ntvAddr) ∧ IdInjOn K.enc ↑(loggedTriples K ops) ∧
    LoggedClash K ops q ∧ R.tracker (K.enc q.1 q.2.1 q.2.2) = t

/-- **THE LAST WRITE WINS, AND A VAULT ID'S TRACKER NEED NOT BE THE VAULT.**  An L1 run from
fresh storage, with the encoding injective on its logged triples plus a vault triple `q`,
so there is no logged clash at `q`.  The vault registers `q`'s token, recording itself as
tracker at `enc q`.  A later logged call hashes the same triple and records a different
value there; the statement does not name it, and in the proof it is the owner's
`setAssetDeploymentTracker(d, L2_NATIVE_TOKEN_VAULT_ADDR)`.  The state holds the last
value, not the vault's.  So `RunTrackerIsLastOwnWriteOn` cannot read "some write" in place
of "the last write".  No collision is involved. -/
def Properties.RunTrackerIsLastOwnWriteOnWitness : Prop :=
  ∃ (K : Cfg) (ops : List Op) (R : Router) (q : Chain × Address × AssetData)
    (v₁ v₂ : Address),
    K.side = .l1 ∧ ARun K empty ops R ∧ IdInjOn K.enc (↑(loggedTriples K ops) ∪ {q}) ∧
    ¬ LoggedClash K ops q ∧ q.2.1 = K.ntvAddr ∧ Op.register K.ntv q.2.2 K.ntv ∈ ops ∧
    (∃ op ∈ ops, op.trackerWrite K = some (q, v₁)) ∧ v₁ = K.ntv ∧
    lastTrackerWriteOn K ops q = some v₂ ∧ v₂ ≠ v₁ ∧
    R.tracker (K.enc q.1 q.2.1 q.2.2) = v₂

/-- **A CLASH ELSEWHERE IN THE LOG DOES NOT MATTER.**  An L1 run from fresh storage whose
encoding is not injective on its own logged triples (in the proof, two owner writes for
different custom trackers hash to the same id).  There is still no logged clash at the
vault triple `q` the vault registered.  So `RunTrackerIsLastOwnWriteOn` applies where
injectivity on the log plus `q` fails, and the tracker at `enc q` is the vault, the value of
the last write to `q`. -/
def Properties.LastOwnWriteHoldsDespiteClashElsewhere : Prop :=
  ∃ (K : Cfg) (ops : List Op) (R : Router) (q : Chain × Address × AssetData),
    K.side = .l1 ∧ ARun K empty ops R ∧ ¬ IdInjOn K.enc ↑(loggedTriples K ops) ∧
    q.2.1 = K.ntvAddr ∧ (∃ h, Op.register K.ntv q.2.2 h ∈ ops) ∧
    ¬ LoggedClash K ops q ∧ lastTrackerWriteOn K ops q = some K.ntv ∧
    R.tracker (K.enc q.1 q.2.1 q.2.2) = K.ntv

/-- **THE ORIGINAL'S CONCLUSION HOLDS EVEN WHERE NO RUN CAN REACH.**  There is a
configuration (in the proof, one whose encoding returns its data word) for which every
router state satisfies `TrackerHashed`.  That includes a state in which every id carries a
nonzero tracker, and no run with fewer calls than there are ids reaches that state.  So, for such an encoding,
`AllWriters.Properties.RunTrackerHashed` cannot tell reachable states from unreachable
ones.  `RunTrackedIdsCardLe`, which follows from `RunTrackerRecorded`, can. -/
def Properties.TrackerHashedAdmitsUnreachableRouter : Prop :=
  ∃ (K : Cfg) (R : Router), (∀ R' : Router, TrackerHashed K R') ∧ (∀ a, R.tracker a ≠ 0) ∧
    ∀ ops : List Op, ops.length < UInt256.size → ¬ ARun K empty ops R

end Contracts.AssetRouter.AllWriters
