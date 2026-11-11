import EraSpec.Contracts.AssetRouterBase.Specs.CounterpartGate

/-!
# Properties: the counterpart exception, narrowed by the L1 side

Statements about `EraSpec.Contracts.AssetRouterBase.Specs.CounterpartGate`.  Proofs are in
`EraSpec.Contracts.AssetRouterBase.Proofs.CounterpartGate`.

* **On L1, at a vault id, the counterpart message names the L2 vault, or the L1 log holds
  a clash** (`L1CounterpartAtVaultIdOrLoggedClash`, no hash premise).  Take any state of an
  L1 router reachable from fresh storage and any vault triple `q`.  Either every message
  the L1 router can send for `enc q` names `L2_NATIVE_TOKEN_VAULT_ADDR`, or a triple the
  L1 run itself logged is distinct from `q` and has the same id.  The clash names a
  triple in the run's finite log, so it is not an existential over all preimages.
  `L1CounterpartAtVaultIdOn` is the same under injectivity on the log plus `q`;
  `L1CounterpartAtVaultIdWitness` fires it.
* **Neither part can be dropped.**  At a non-vault id a custom tracker can let any handler
  through (`CustomTrackerNamesAnyHandler`), so the exception stays for custom assets.
  Under a clash a custom tracker names a non-vault handler for a vault id
  (`CounterpartGateClashFires`).
* **On L2 a route stays accountable if every counterpart write to it names the vault**
  (`L2RouteAccountable`, no hash premise).
* **Composed** (`CounterpartCannotMisrouteVaultTriple`): an L1 and an L2 router share the
  encoding and `L2_NATIVE_TOKEN_VAULT_ADDR`, and the L2 vault sits at that address.  Each
  counterpart write to a vault triple's id on L2 was sent by the L1 router from a state
  its run reached, with the encoding injective on that run's log plus the triple.  Then
  that id's route on L2 always has a tracker or points at the vault.
  `CounterpartCannotMisrouteVaultTripleWitness` fires it with a live route.
-/

namespace Contracts.AssetRouter.AllWriters

/-- **ON L1, A COUNTERPART MESSAGE FOR A VAULT ID NAMES THE L2 VAULT, OR THE L1 LOG HOLDS A
CLASH.**  For an L1 router whose trackers behave as `VaultApprovals` says, in any state
its run reaches from fresh storage, and any vault triple `q`: every handler `h` the L1
router can send for `enc q` is `L2_NATIVE_TOKEN_VAULT_ADDR`, or some triple in the run's
own log is distinct from `q` and has the same id.  No hash premise. -/
def Properties.L1CounterpartAtVaultIdOrLoggedClash : Prop :=
  ∀ (K1 : Cfg) (approves : Approvals), K1.side = .l1 → VaultApprovals K1 approves →
    ∀ (ops1 : List Op) (R1 : Router), ARun K1 empty ops1 R1 →
    ∀ (q : Chain × Address × AssetData), q.2.1 = K1.ntvAddr →
    ∀ h, L1Emits approves R1 (K1.enc q.1 q.2.1 q.2.2) h →
      h = K1.ntvAddr ∨
        ∃ p ∈ loggedTriples K1 ops1, p ≠ q ∧ K1.enc p.1 p.2.1 p.2.2 = K1.enc q.1 q.2.1 q.2.2

/-- **ON L1, A COUNTERPART MESSAGE FOR A VAULT ID NAMES THE L2 VAULT**, when the encoding is
injective on the L1 run's logged triples together with the vault triple `q`. -/
def Properties.L1CounterpartAtVaultIdOn : Prop :=
  ∀ (K1 : Cfg) (approves : Approvals), K1.side = .l1 → VaultApprovals K1 approves →
    ∀ (ops1 : List Op) (R1 : Router), ARun K1 empty ops1 R1 →
    ∀ (q : Chain × Address × AssetData), q.2.1 = K1.ntvAddr →
      IdInjOn K1.enc (↑(loggedTriples K1 ops1) ∪ {q}) →
      ∀ h, L1Emits approves R1 (K1.enc q.1 q.2.1 q.2.2) h → h = K1.ntvAddr

/-- **`L1CounterpartAtVaultIdOn`'s PREMISES HOLD, AND A MESSAGE IS SENDABLE.**  An L1 router
whose vault lets through only the L2 vault.  In a run from fresh storage the vault
registers a token.  The encoding is injective on the log plus that token's vault triple,
and the L1 router can send a counterpart message for its id. -/
def Properties.L1CounterpartAtVaultIdWitness : Prop :=
  ∃ (K1 : Cfg) (approves : Approvals) (ops1 : List Op) (R1 : Router)
    (q : Chain × Address × AssetData) (h : Address),
    K1.side = .l1 ∧ VaultApprovals K1 approves ∧ ARun K1 empty ops1 R1 ∧
    q.2.1 = K1.ntvAddr ∧ IdInjOn K1.enc (↑(loggedTriples K1 ops1) ∪ {q}) ∧
    L1Emits approves R1 (K1.enc q.1 q.2.1 q.2.2) h

/-- **AT A NON-VAULT ID, A CUSTOM TRACKER CAN LET ANY HANDLER THROUGH.**  The counterpart
exception stays for custom assets.  An L1 router whose trackers meet `VaultApprovals`.
The owner records a custom tracker, which lets every handler through for its id, and the
L1 router can then send a message pointing that non-vault id at a handler that is
neither the L2 vault nor zero. -/
def Properties.CustomTrackerNamesAnyHandler : Prop :=
  ∃ (K1 : Cfg) (approves : Approvals) (ops1 : List Op) (R1 : Router) (a : AssetId)
    (h : Address),
    K1.side = .l1 ∧ VaultApprovals K1 approves ∧ ARun K1 empty ops1 R1 ∧
    ¬ IsNtvId K1.enc K1.ntvAddr a ∧ L1Emits approves R1 a h ∧ h ≠ K1.ntvAddr ∧ h ≠ 0

/-- **UNDER A CLASH, A CUSTOM TRACKER NAMES A NON-VAULT HANDLER FOR A VAULT ID.**  An L1
router whose trackers meet `VaultApprovals` and a colliding encoding.  The owner records
a custom tracker whose id equals a vault triple's id.  The L1 router can then send a
message pointing that vault id at a handler other than the L2 vault, and the encoding is
not injective on the log plus the triple.  So the clash disjunct of
`L1CounterpartAtVaultIdOrLoggedClash` is load-bearing. -/
def Properties.CounterpartGateClashFires : Prop :=
  ∃ (K1 : Cfg) (approves : Approvals) (ops1 : List Op) (R1 : Router)
    (q : Chain × Address × AssetData) (h : Address),
    K1.side = .l1 ∧ VaultApprovals K1 approves ∧ ARun K1 empty ops1 R1 ∧
    q.2.1 = K1.ntvAddr ∧ L1Emits approves R1 (K1.enc q.1 q.2.1 q.2.2) h ∧
    h ≠ K1.ntvAddr ∧ ¬ IdInjOn K1.enc (↑(loggedTriples K1 ops1) ∪ {q})

/-- **ON L2, A ROUTE STAYS ACCOUNTABLE IF EVERY COUNTERPART WRITE TO IT NAMES THE VAULT.**
Along every L2 run from fresh storage, an id whose every counterpart write names the
vault is unset, has a nonzero tracker, or points at the vault.  No hash premise, and no
premise on the vault's mints: the fallback and the seed point at the vault whatever the
id. -/
def Properties.L2RouteAccountable : Prop :=
  ∀ (K : Cfg), K.side = .l2 → ∀ (x : AssetId) (ops : List Op) (R : Router),
    ARun K empty ops R → (∀ h, Op.counterpartSet x h ∈ ops → h = K.ntv) →
      R.handler x ≠ 0 → R.tracker x ≠ 0 ∨ R.handler x = K.ntv

/-- **THE COUNTERPART CANNOT MISROUTE A VAULT TRIPLE'S ID.**  An L1 router `K1` and an L2
router `K2` share the encoding and `L2_NATIVE_TOKEN_VAULT_ADDR`, and the L2 vault sits at
that address.  The L1 trackers behave as `VaultApprovals` says.  Fix a vault triple `q`.
Suppose every counterpart write to `enc q` in an L2 run was sent by the L1 router from a
state its run reached from fresh storage, with the encoding injective on that L1 run's
logged triples plus `q`.  Then on L2 the route of `enc q` is always unset, tracked, or
pointed at the L2 vault. -/
def Properties.CounterpartCannotMisrouteVaultTriple : Prop :=
  ∀ (K1 K2 : Cfg) (approves : Approvals), K1.side = .l1 → K2.side = .l2 →
    K2.enc = K1.enc → K2.ntvAddr = K1.ntvAddr → K2.ntv = K2.ntvAddr →
    VaultApprovals K1 approves →
    ∀ (q : Chain × Address × AssetData), q.2.1 = K1.ntvAddr →
    ∀ (ops : List Op) (R : Router), ARun K2 empty ops R →
      (∀ h, Op.counterpartSet (K2.enc q.1 q.2.1 q.2.2) h ∈ ops →
        ∃ (ops1 : List Op) (R1 : Router), ARun K1 empty ops1 R1 ∧
          L1Emits approves R1 (K1.enc q.1 q.2.1 q.2.2) h ∧
          IdInjOn K1.enc (↑(loggedTriples K1 ops1) ∪ {q})) →
      TripleAccountable K2 R q

/-- **`CounterpartCannotMisrouteVaultTriple`'s PREMISES HOLD, WITH A COUNTERPART WRITE AND A
LIVE ROUTE.**  The L2 run is one counterpart write to a vault triple's id.  It was sent by
the L1 router after the L1 vault registered that token, and the route is live at the
end. -/
def Properties.CounterpartCannotMisrouteVaultTripleWitness : Prop :=
  ∃ (K1 K2 : Cfg) (approves : Approvals) (q : Chain × Address × AssetData) (ops : List Op)
    (R : Router),
    K1.side = .l1 ∧ K2.side = .l2 ∧ K2.enc = K1.enc ∧ K2.ntvAddr = K1.ntvAddr ∧
    K2.ntv = K2.ntvAddr ∧ VaultApprovals K1 approves ∧ q.2.1 = K1.ntvAddr ∧
    ARun K2 empty ops R ∧
    (∀ h, Op.counterpartSet (K2.enc q.1 q.2.1 q.2.2) h ∈ ops →
      ∃ (ops1 : List Op) (R1 : Router), ARun K1 empty ops1 R1 ∧
        L1Emits approves R1 (K1.enc q.1 q.2.1 q.2.2) h ∧
        IdInjOn K1.enc (↑(loggedTriples K1 ops1) ∪ {q})) ∧
    (∃ h, Op.counterpartSet (K2.enc q.1 q.2.1 q.2.2) h ∈ ops) ∧
    R.handler (K2.enc q.1 q.2.1 q.2.2) ≠ 0

end Contracts.AssetRouter.AllWriters
