import EraSpec.Contracts.AssetRouterBase.Specs.HandlerGateAtV35

/-!
# Properties: the L1 asset router's handler gate at `draft/v0.35.0`

Statements about `EraSpec.Contracts.AssetRouterBase.Specs.HandlerGateAtV35` (pinned at
`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`).  Proofs are in
`EraSpec.Contracts.AssetRouterBase.Proofs.HandlerGateAtV35`.  Only `GatedRunWeakValidOn` takes
a hash premise, `AllWriters`' run-local one.

"Has a step" is the model's: the handlers' own calls are taken to succeed, and the entry
points' other checks (modifiers, pause, `msg.value`, `receiveMessage`'s checks, the base-token
check of `_bridgehubDepositNonBaseTokenAsset`) are not modelled.  So a result that a call has a
step says that the gate and the handler-set check do not stop it, nothing more.  Where a call has
no step because the gate rejects it (a stranded `(c, a)`, whose handler is set), the code
reverts too: the gate's check is modelled as written.  A deposit of an asset with no handler is
different: the model logs the vault's on-the-fly registration as its own `register` event first
(see the Specs header).

## (a) What the gate lets through

* **One step** (`MovementEnabledIff`).  A gated entry point at `(c, a)` has a step exactly when
  `a`'s handler is set and `(c, a)` is not `Stranded`, and that step changes nothing.  The
  fallback has a step exactly when the handler is unset and the vault mints `a`, whatever the
  chain and the environment: the gate never stops it.
* **Along runs** (`MovementsUseExemptHandlerOrEnabledChain`).  Every event of a v35 run that
  moves an asset at chain `c` ran in a state where the handler it moved the asset through was
  the router's vault or the chain asset handler of that state, or `c` was interop-enabled.  So
  at a chain without interop, assets move only through those two handlers.  Witness:
  `CustomMovementAtEnabledChainWitness`.

## (b) What did not change

* **Every v35 run projects onto an `AllWriters` L1 run** of its router-writing calls
  (`RunProjectsToAllWriters`; witness `RunProjectsToAllWritersWitness`).  The gate adds no
  writer, and every `AllWriters` result about L1 runs applies to the router maps of v35 runs.
  For instance `WeakValid` holds along every v35 run from fresh router storage under
  `AllWriters`' run-local premise (`GatedRunWeakValidOn`; witness
  `GatedRunWeakValidOnWitness`).
* **Interop flags only turn on, as long as there is no `setAddresses`**
  (`InteropFlagsOneWayWithoutSetAddresses`; witness `InteropFlagsOneWayWitness`).  Along a run
  without `setAddresses`, the chain asset handler stays, every enabled chain stays enabled, and
  a chain's flag changes only through its own `enableInterop`.
* **Combined** (`MovementsAtDisabledChainUseExemptHandler`; witness
  `MovementsAtDisabledChainWitness`).  Along a run without `setAddresses`, every asset moved at a
  chain that is still without interop at the end moved through the router's vault or the chain
  asset handler of the start state.

## (c) Stranding, and what ends it

* **A stranded asset stays stranded until a listed call** (`StrandedUntilListedCall`; witness
  `StrandedUntilListedCallWitness`).  The listed calls (`Ev.MayUnstrand`) are
  `enableInterop(c)`, `setAddresses`, a registration whose derived id is `a`, and
  `setNativeTokenVault` when `a` is the seeded id.  Along a run with none of them, a stranded
  `(c, a)` stays stranded and no event of the run moves `a` at `c`.  With
  `MovementEnabledIff`, applied to each prefix of the run: in every state along it, deposits of
  `a` to `c`, their confirmations and refunds, and withdrawals of `a` from `c` have no step
  (`StrandedAlongRun`).
* **One step** (`UnstrandingCallIsListed`; witness `UnstrandingCallIsListedWitness`).  A step
  that ends a stranding is `enableInterop(c)`, `setAddresses`, `setNativeTokenVault` with `a`
  the seeded id, or a registration of `a` by the vault or by `a`'s recorded tracker.
* **An open gate stays open** (`OpenGateStaysOpen`; witness `OpenGateStaysOpenWitness`).  Once
  a gated entry point at `(c, a)` has a step in some state, along every later run with no
  `setAddresses` and no call that can rewrite `a`'s handler (`Ev.RewritesHandler`), `a` keeps
  its handler and every gated entry point at `(c, a)` keeps a step.
* **Both exclusions are needed.**  `setAddresses` can clear an interop flag and close an open
  gate (`SetAddressesClosesOpenGate`).  A tracker's re-registration of an asset routed to the
  chain asset handler can close the gate at a chain without interop
  (`RepointingClosesOpenGate`).
-/

namespace Contracts.AssetRouter.HandlerGateAtV35

open Contracts.AssetRouter.AllWriters (Cfg Op ARun MintsOnlyNtvIds IsNtvId WeakValid)

/-! ## (a) What the gate lets through -/

/-- **WHEN AN ASSET-MOVING CALL HAS A STEP.**  For every configuration, state `S`, chain `c`
and asset `a`: each gated entry point at `(c, a)` has a step from `S` exactly when `a`'s handler
is nonzero and `(c, a)` is not stranded in `S`, and every such step leaves `S` unchanged.  The
fallback `finalize` at `(c, a)` has a step exactly when `a`'s handler is zero and the vault
mints `a`: the gate never stops it. -/
def Properties.MovementEnabledIff : Prop :=
  ∀ (K : Cfg) (S : St) (c : Chain) (a : AssetId),
    (∀ g : Gated,
      ((∃ T, StepV35 K (.gated g c a) S T) ↔ S.router.handler a ≠ 0 ∧ ¬ Stranded K S c a) ∧
      ∀ T, StepV35 K (.gated g c a) S T → T = S) ∧
    ((∃ T, StepV35 K (.finalize c a) S T) ↔ S.router.handler a = 0 ∧ K.ntvMints a)

/-- **AT A CHAIN WITHOUT INTEROP, ASSETS MOVE ONLY THROUGH THE VAULT OR THE CHAIN ASSET
HANDLER.**  Take any v35 run and split its log around an event `e` that moves asset `a` at
chain `c` (a gated entry point, or the fallback).  Then `e` ran from the state `U` that the
log's prefix reached, and the handler it moved `a` through (`Ev.through`) is the router's
vault, or `U`'s chain asset handler, or `c` was interop-enabled in `U`.  No premise on the
run. -/
def Properties.MovementsUseExemptHandlerOrEnabledChain : Prop :=
  ∀ (K : Cfg) (S T : St) (evs₁ evs₂ : List Ev) (e : Ev),
    RunV35 K S (evs₁ ++ e :: evs₂) T →
    ∀ (c : Chain) (a : AssetId), e.gatedAt = some (c, a) →
      ∃ U V : St, RunV35 K S evs₁ U ∧ StepV35 K e U V ∧ RunV35 K V evs₂ T ∧
        ∃ h, e.through K U = some h ∧ (h = K.ntv ∨ h = U.env.cah ∨ U.env.ie c = true)

/-- **`MovementsUseExemptHandlerOrEnabledChain`'s PREMISE HOLDS WITH A CUSTOM HANDLER.**  An L1
run from fresh storage splits around an event that moves an asset at chain `c`, and further
events follow it.  The asset's handler, in the state the prefix reached, is custom.  `c` is not
interop-enabled at the start, and an `enableInterop(c)` in the prefix turned it on. -/
def Properties.CustomMovementAtEnabledChainWitness : Prop :=
  ∃ (K : Cfg) (E : Env) (T U : St) (evs₁ evs₂ : List Ev) (e : Ev) (c : Chain) (a : AssetId),
    K.side = .l1 ∧ RunV35 K ⟨empty, E⟩ (evs₁ ++ e :: evs₂) T ∧ evs₂ ≠ [] ∧
    e.gatedAt = some (c, a) ∧ RunV35 K ⟨empty, E⟩ evs₁ U ∧
    Custom K U.env (U.router.handler a) ∧ E.ie c = false ∧ Ev.enableInterop c ∈ evs₁

/-! ## (b) What did not change -/

/-- **EVERY v35 RUN IS AN `AllWriters` L1 RUN ON THE ROUTER'S MAPS.**  For an L1 configuration,
the router maps along any v35 run follow the `AllWriters` run of the log's router-writing calls
(`ops`), from the same start.  The gated entry points, the counterpart message,
`enableInterop` and `setAddresses` drop out of the log. -/
def Properties.RunProjectsToAllWriters : Prop :=
  ∀ (K : Cfg), K.side = .l1 → ∀ (S T : St) (evs : List Ev), RunV35 K S evs T →
    ARun K S.router (ops evs) T.router

/-- **`RunProjectsToAllWriters`' PREMISES HOLD ON A RUN WITH EVERY KIND OF EVENT.**  An L1 run
from fresh storage whose log holds a registration, the seed, a tracker write, a fallback, a
gated entry point, a counterpart message, an `enableInterop` and a `setAddresses`. -/
def Properties.RunProjectsToAllWritersWitness : Prop :=
  ∃ (K : Cfg) (E : Env) (T : St) (evs : List Ev),
    K.side = .l1 ∧ RunV35 K ⟨empty, E⟩ evs T ∧
    (∃ caller d h, Ev.register caller d h ∈ evs) ∧ Ev.seed ∈ evs ∧
    (∃ d t, Ev.setTracker d t ∈ evs) ∧ (∃ c a, Ev.finalize c a ∈ evs) ∧
    (∃ g c a, Ev.gated g c a ∈ evs) ∧ (∃ c a h, Ev.counterpartMsg c a h ∈ evs) ∧
    (∃ c, Ev.enableInterop c ∈ evs) ∧ (∃ cah ie, Ev.setAddresses cah ie ∈ evs)

/-- **`WeakValid` ALONG EVERY v35 RUN, UNDER `AllWriters`' RUN-LOCAL PREMISE.**  Take an L1
configuration whose vault mints only vault ids and whose seeded id is a vault id, with
`L2_NATIVE_TOKEN_VAULT_ADDR ≠ 0`.  Along every v35 run from fresh router storage (any
environment), if the encoding is injective on the triples that the log's registrations and
tracker writes hash, every live route has a nonzero tracker or is a vault route.  This is
`AllWriters.Properties.L1RunWeakValidOn` through `RunProjectsToAllWriters`. -/
def Properties.GatedRunWeakValidOn : Prop :=
  ∀ (K : Cfg), K.side = .l1 → K.ntvAddr ≠ 0 → MintsOnlyNtvIds K →
    IsNtvId K.enc K.ntvAddr K.seedId →
    ∀ (E : Env) (evs : List Ev) (T : St), RunV35 K ⟨empty, E⟩ evs T →
      IdInjOn K.enc ↑(AllWriters.loggedTriples K (ops evs)) → WeakValid K T.router

/-- **`GatedRunWeakValidOn`'s PREMISES HOLD, AND `Valid` FAILS AT THE END.**  An L1 configuration
whose vault mints only vault ids, and a v35 run from fresh storage with a gated movement, a
fallback and an `enableInterop`, on whose logged triples the encoding is injective.  At its end
`Valid` fails, so the weak invariant is the one that holds. -/
def Properties.GatedRunWeakValidOnWitness : Prop :=
  ∃ (K : Cfg) (E : Env) (evs : List Ev) (T : St),
    K.side = .l1 ∧ K.ntvAddr ≠ 0 ∧ MintsOnlyNtvIds K ∧ IsNtvId K.enc K.ntvAddr K.seedId ∧
    RunV35 K ⟨empty, E⟩ evs T ∧ IdInjOn K.enc ↑(AllWriters.loggedTriples K (ops evs)) ∧
    (∃ g c a, Ev.gated g c a ∈ evs) ∧ (∃ c a, Ev.finalize c a ∈ evs) ∧
    (∃ c, Ev.enableInterop c ∈ evs) ∧ ¬ Valid T.router

/-- **INTEROP FLAGS ONLY TURN ON, AS LONG AS THERE IS NO `setAddresses`.**  Along any v35 run
whose log has no `setAddresses`: the chain asset handler at the end is the one at the start,
every chain enabled at the start is enabled at the end, and the flag of every chain whose
`enableInterop` is not in the log is unchanged. -/
def Properties.InteropFlagsOneWayWithoutSetAddresses : Prop :=
  ∀ (K : Cfg) (S T : St) (evs : List Ev), RunV35 K S evs T →
    (∀ e ∈ evs, ¬ e.IsSetAddresses) →
      T.env.cah = S.env.cah ∧
      ∀ c, (S.env.ie c = true → T.env.ie c = true) ∧
        (Ev.enableInterop c ∉ evs → T.env.ie c = S.env.ie c)

/-- **`InteropFlagsOneWayWithoutSetAddresses`' PREMISES HOLD ON A RUN THAT ENABLES A CHAIN.**
From a state reachable from fresh storage in which one chain is enabled and another is not, a
run without `setAddresses` enables the second chain and moves an asset at the first. -/
def Properties.InteropFlagsOneWayWitness : Prop :=
  ∃ (K : Cfg) (E : Env) (evs₀ evs : List Ev) (S T : St) (c c' : Chain),
    K.side = .l1 ∧ RunV35 K ⟨empty, E⟩ evs₀ S ∧ RunV35 K S evs T ∧
    (∀ e ∈ evs, ¬ e.IsSetAddresses) ∧ S.env.ie c = true ∧ S.env.ie c' = false ∧
    Ev.enableInterop c' ∈ evs ∧ ∃ g a, Ev.gated g c a ∈ evs

/-- **A CHAIN STILL WITHOUT INTEROP AT THE END SAW ONLY THE VAULT AND THE CHAIN ASSET
HANDLER.**  Take a v35 run from `S` to `T` whose log has no `setAddresses`, and a chain `c`
that is not interop-enabled in `T`.  Every event of the log that moves an asset at `c` ran from
the state `U` that the log's prefix reached, and the handler it moved the asset through is the
router's vault or the chain asset handler of `S`.  This combines
`MovementsUseExemptHandlerOrEnabledChain` with `InteropFlagsOneWayWithoutSetAddresses`. -/
def Properties.MovementsAtDisabledChainUseExemptHandler : Prop :=
  ∀ (K : Cfg) (S T : St) (evs : List Ev), RunV35 K S evs T →
    (∀ e ∈ evs, ¬ e.IsSetAddresses) → ∀ c : Chain, T.env.ie c = false →
    ∀ (evs₁ evs₂ : List Ev) (e : Ev), evs = evs₁ ++ e :: evs₂ →
    ∀ a : AssetId, e.gatedAt = some (c, a) →
      ∃ U : St, RunV35 K S evs₁ U ∧
        ∃ h, e.through K U = some h ∧ (h = K.ntv ∨ h = S.env.cah)

/-- **`MovementsAtDisabledChainUseExemptHandler`'s PREMISES HOLD, NEXT TO A CUSTOM-HANDLER
MOVEMENT ELSEWHERE.**  An L1 run from fresh storage with no `setAddresses` ends with a chain `c`
not interop-enabled.  Its log moves a vault asset at `c` and takes a fallback at `c`, and it also
moves, at another chain, an asset whose handler in the state before that event is custom. -/
def Properties.MovementsAtDisabledChainWitness : Prop :=
  ∃ (K : Cfg) (E : Env) (evs : List Ev) (T : St) (c : Chain),
    K.side = .l1 ∧ RunV35 K ⟨empty, E⟩ evs T ∧ (∀ e ∈ evs, ¬ e.IsSetAddresses) ∧
    T.env.ie c = false ∧ (∃ g a, Ev.gated g c a ∈ evs) ∧ (∃ b, Ev.finalize c b ∈ evs) ∧
    ∃ (evs₁ evs₂ : List Ev) (g : Gated) (c' : Chain) (a : AssetId) (U : St),
      evs = evs₁ ++ Ev.gated g c' a :: evs₂ ∧ c' ≠ c ∧ RunV35 K ⟨empty, E⟩ evs₁ U ∧
      Custom K U.env (U.router.handler a)

/-! ## (c) Stranding, and what ends it -/

/-- **A STRANDED ASSET STAYS STRANDED UNTIL A LISTED CALL.**  Suppose `(c, a)` is stranded in
`S`: `a`'s handler is custom and `c` is not interop-enabled.  Take a v35 run from `S` whose log
has no call that `Ev.MayUnstrand` lists: `enableInterop(c)`, `setAddresses`, a registration whose
derived id is `a`, or `setNativeTokenVault` when `a` is the seeded id.  Then `(c, a)` is
stranded at the end, and no event of the log moves `a` at `c` (`gatedAt ≠ some (c, a)`). -/
def Properties.StrandedUntilListedCall : Prop :=
  ∀ (K : Cfg) (S T : St) (evs : List Ev) (c : Chain) (a : AssetId),
    Stranded K S c a → RunV35 K S evs T → (∀ e ∈ evs, ¬ e.MayUnstrand K c a) →
      Stranded K T c a ∧ ∀ e ∈ evs, e.gatedAt ≠ some (c, a)

/-- **A STRANDED ASSET HAS NO MOVEMENT STEP ANYWHERE ALONG SUCH A RUN.**  Under the premises of
`StrandedUntilListedCall`, for every split of the log into `evs₁ ++ evs₂` there is a state `U`
between the two parts, reached by `evs₁` and leading to `T` by `evs₂`, in which `(c, a)` is
stranded and no gated entry point at `(c, a)` has a step: deposits of `a` to `c`, their
confirmations and refunds, and withdrawals of `a` from `c` are all blocked there.  This is
`StrandedUntilListedCall` on the prefix, with `MovementEnabledIff`. -/
def Properties.StrandedAlongRun : Prop :=
  ∀ (K : Cfg) (S T : St) (evs₁ evs₂ : List Ev) (c : Chain) (a : AssetId),
    Stranded K S c a → RunV35 K S (evs₁ ++ evs₂) T →
    (∀ e ∈ evs₁ ++ evs₂, ¬ e.MayUnstrand K c a) →
      ∃ U, RunV35 K S evs₁ U ∧ RunV35 K U evs₂ T ∧ Stranded K U c a ∧
        ∀ g : Gated, ¬ ∃ U', StepV35 K (.gated g c a) U U'

/-- **`StrandedUntilListedCall`'s PREMISES HOLD ON A BUSY RUN.**  An L1 router reaches, from
fresh storage, a state where an asset is stranded at a chain.  A further run with no listed call
moves another asset at that chain, takes a fallback there, enables a second chain, and moves the
stranded asset at the second chain. -/
def Properties.StrandedUntilListedCallWitness : Prop :=
  ∃ (K : Cfg) (E : Env) (evs₀ evs : List Ev) (S T : St) (c c' : Chain) (a : AssetId),
    K.side = .l1 ∧ RunV35 K ⟨empty, E⟩ evs₀ S ∧ Stranded K S c a ∧ RunV35 K S evs T ∧
    (∀ e ∈ evs, ¬ e.MayUnstrand K c a) ∧ c' ≠ c ∧ Ev.enableInterop c' ∈ evs ∧
    (∃ g, Ev.gated g c' a ∈ evs) ∧ (∃ g b, b ≠ a ∧ Ev.gated g c b ∈ evs) ∧
    ∃ b, Ev.finalize c b ∈ evs

/-- **ONLY A LISTED CALL ENDS A STRANDING, IN ONE STEP.**  If `(c, a)` is stranded in `S` and a
step from `S` leaves it not stranded, the step is `enableInterop(c)`, `setAddresses`,
`setNativeTokenVault` with `a` the seeded id, or a registration whose derived id is `a`, by the
vault or by `a`'s tracker recorded in `S`. -/
def Properties.UnstrandingCallIsListed : Prop :=
  ∀ (K : Cfg) (S T : St) (e : Ev) (c : Chain) (a : AssetId),
    Stranded K S c a → StepV35 K e S T → ¬ Stranded K T c a →
      e = .enableInterop c ∨ e.IsSetAddresses ∨ (e = .seed ∧ K.seedId = a) ∨
        ∃ caller d h, e = .register caller d h ∧
          writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d = a ∧
          (caller = K.ntv ∨ caller = S.router.tracker a)

/-- **`UnstrandingCallIsListed`'s PREMISES HOLD, BY TWO DIFFERENT CALLS.**  From a state
reachable from fresh storage in which an asset is stranded at a chain, `enableInterop` of that
chain ends the stranding, and so does a registration call by the asset's recorded tracker. -/
def Properties.UnstrandingCallIsListedWitness : Prop :=
  ∃ (K : Cfg) (E : Env) (evs₀ : List Ev) (S T₁ T₂ : St) (e : Ev) (c : Chain) (a : AssetId),
    K.side = .l1 ∧ RunV35 K ⟨empty, E⟩ evs₀ S ∧ Stranded K S c a ∧
    StepV35 K (.enableInterop c) S T₁ ∧ ¬ Stranded K T₁ c a ∧
    StepV35 K e S T₂ ∧ ¬ Stranded K T₂ c a ∧
    ∃ d h, e = .register (S.router.tracker a) d h

/-- **AN OPEN GATE STAYS OPEN.**  Suppose a gated entry point at `(c, a)` has a step from `S`.
Then along every v35 run from `S` whose log has no `setAddresses` and no call that can rewrite
`a`'s handler (`Ev.RewritesHandler`), `a`'s handler at the end is its handler in `S`, and every
gated entry point at `(c, a)` has a step at the end.  So along such runs neither the gate nor
the handler-set check stops the confirmation or refund of a deposit of `a` to `c` that the gate
let through, or a later deposit or withdrawal of `a` at `c`. -/
def Properties.OpenGateStaysOpen : Prop :=
  ∀ (K : Cfg) (S T : St) (evs : List Ev) (g : Gated) (c : Chain) (a : AssetId),
    StepV35 K (.gated g c a) S S → RunV35 K S evs T →
    (∀ e ∈ evs, ¬ e.RewritesHandler K a ∧ ¬ e.IsSetAddresses) →
      T.router.handler a = S.router.handler a ∧ ∀ g' : Gated, StepV35 K (.gated g' c a) T T

/-- **`OpenGateStaysOpen`'s PREMISES HOLD WITH A CUSTOM HANDLER.**  In a state reachable from
fresh storage, a deposit of a custom-handler asset has a step.  The later run has a tracker
write, a registration and an `enableInterop`, with no `setAddresses` and no call that can
rewrite the first asset's handler. -/
def Properties.OpenGateStaysOpenWitness : Prop :=
  ∃ (K : Cfg) (E : Env) (evs₀ evs : List Ev) (S T : St) (c : Chain) (a : AssetId),
    K.side = .l1 ∧ RunV35 K ⟨empty, E⟩ evs₀ S ∧ StepV35 K (.gated .deposit c a) S S ∧
    Custom K S.env (S.router.handler a) ∧ RunV35 K S evs T ∧
    (∀ e ∈ evs, ¬ e.RewritesHandler K a ∧ ¬ e.IsSetAddresses) ∧
    (∃ d t, Ev.setTracker d t ∈ evs) ∧ (∃ caller d h, Ev.register caller d h ∈ evs) ∧
    ∃ c', Ev.enableInterop c' ∈ evs

/-- **`setAddresses` CAN CLOSE AN OPEN GATE.**  So `OpenGateStaysOpen` and
`InteropFlagsOneWayWithoutSetAddresses` must exclude it.  From a state reachable from fresh
storage in which a custom-handler deposit to an interop-enabled chain has a step, a
`setAddresses` installing a message root whose table does not enable that chain clears the
chain's flag, and the confirmation of that deposit then has no step.  `setAddresses` is
`onlyOwnerOrUpgrader` (`core/bridgehub/L1Bridgehub.sol:274`, `BridgehubBase.sol:146-151`): this is
a reconfiguration by the owner or the upgrader only (`OPS-CONFIG`). -/
def Properties.SetAddressesClosesOpenGate : Prop :=
  ∃ (K : Cfg) (E : Env) (evs₀ : List Ev) (S T : St) (c : Chain) (a : AssetId) (cah : Address)
    (ie : Chain → Bool),
    K.side = .l1 ∧ RunV35 K ⟨empty, E⟩ evs₀ S ∧ StepV35 K (.gated .deposit c a) S S ∧
    Custom K S.env (S.router.handler a) ∧ S.env.ie c = true ∧
    StepV35 K (.setAddresses cah ie) S T ∧ T.env.ie c = false ∧
    ¬ ∃ T', StepV35 K (.gated .confirm c a) T T'

/-- **A REGISTRATION CAN CLOSE AN OPEN GATE.**  So `OpenGateStaysOpen` must exclude the calls
that can rewrite the handler.  From a state reachable from fresh storage in which an asset routed
to the chain asset handler has a deposit step to a chain without interop, a registration call by
the asset's recorded tracker, which can rewrite the asset's handler and is not `setAddresses`,
leaves the asset with a custom handler, and the confirmation of that deposit then has no
step. -/
def Properties.RepointingClosesOpenGate : Prop :=
  ∃ (K : Cfg) (E : Env) (evs₀ : List Ev) (S T : St) (c : Chain) (a : AssetId) (e : Ev),
    K.side = .l1 ∧ RunV35 K ⟨empty, E⟩ evs₀ S ∧ StepV35 K (.gated .deposit c a) S S ∧
    S.router.handler a = S.env.cah ∧ S.env.ie c = false ∧
    StepV35 K e S T ∧ e.RewritesHandler K a ∧ ¬ e.IsSetAddresses ∧
    (∃ d h, e = .register (S.router.tracker a) d h) ∧ Custom K T.env (T.router.handler a) ∧
    ¬ ∃ T', StepV35 K (.gated .confirm c a) T T'

end Contracts.AssetRouter.HandlerGateAtV35
