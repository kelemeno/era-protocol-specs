import EraSpec.Contracts.ChainAssetHandler.Specs.Migration

/-!
# Properties: where a chain settles, its migration number, and recovery

Statements about `EraSpec.Contracts.ChainAssetHandler.Specs.Migration` (`draft/v0.35.0` at
`b17415d20`). Proofs are in `EraSpec.Contracts.ChainAssetHandler.Proofs.Migration`. Every
reachability statement is over `Reach`: any interleaving of every step of the model on every
hub, from a fresh deployment (`Init`), for one fixed `World`. `W.l1 ≠ 0` is
`block.chainid ≠ 0` on L1. "Field" below means a field of the model's `Sys`; storage the model
does not track (batch numbers, message-root records, the diamond's deposit-pause timestamp,
priority trees) is not covered by any statement.

* **One settlement layer.** Every chain registered on L1 has exactly one holder — one hub
  whose bridgehub says the chain settles there, or one live migration message — and a chain
  not registered on L1 has none (`ExactlyOneSettlementLayer`). On the hub where its diamond
  is registered, the bridgehub records that hub exactly when the diamond is not away
  (`BridgehubAgreesWithDiamond`). L1's bridgehub names the settlement layer that holds the
  chain, or the end other than L1 of the message that holds it
  (`L1SettlementLayerTracksHolder`).
* **Messages.** Every migration message runs between L1 and a settlement layer whitelisted on
  its source, never names its own chain as an endpoint, and carries number 1 out of L1 and 2
  into L1 (`MessagesRunBetweenL1AndALayer`).
* **The migration number.** On L1 it is at most 2 and mirrors where the chain is and what
  interval is recorded (`L1MigrationBookkeeping`); it changes only 0→1 (burn), 1→2 (return)
  and 1→0 (failed-deposit recovery) (`L1MigrationNumberTransitions`). A chain back on L1
  never moves again (`ReturnedChainStaysOnL1`), and a chain completes at most one round trip
  (`AtMostOneRoundTrip`).
* **Delivery is never blocked by the bookkeeping.** A pending message is executed at its
  destination whenever that hub's switches are off for the asset's CTM there, migrations are
  enabled, that CTM is not zero, and the version check of the branch taken passes
  (`GatewayAcceptsArrival` for a settlement layer, which deploys a fresh diamond;
  `L1AcceptsReturn` for L1, which reuses the chain's diamond).
* **Recovery.** Directly after any L1 burn, the deposit's failure and its confirmation are
  enabled and restore every field to its value before the burn
  (`FailedMigrationRecoveryRestoresSource`). From any reachable state, a failed deposit can be
  confirmed while L1's diamond of the chain is at the version the burn data carries, whatever
  the pauses say (`FailedDepositConfirmable`). `isMigrationInProgress` is set exactly while an
  L1-originated migration message is not yet confirmed (`InProgressTracksUnconfirmedDeparture`).
* **Versions.** A burn requires the diamond at its CTM's version and carries that version; a
  mint leaves the diamond at its own CTM's version, and a fresh deployment requires the
  carried version to be the CTM's (`VersionEqualityAtBurnAndMint`).
* **Production constant.** With `CHAIN_MIGRATIONS_ENABLED = false` nothing ever migrates
  (`MigrationsDisabledFreezeSettlement`).

Witnesses, in `cahWorld` from `cahInit` (`Specs/Migration.lean`, "Witness data"):
`CahRoundTripWitness` (a complete round trip), `CahInFlightWitness` (chain `3` held by a
message), `CahGatewayWitness` (chain `3` held by the gateway), `CahFailedAttemptWitness` (a
failed attempt, recovered, after which the chain can try again), `CahReturnedChainWitness` (a
run after the return), `CahDisabledWitness` (the production constant), `CahArrivalWitness`
(the gateway accepts chain `3` while L1 is paused), `CahReturnInFlightWitness` (chain `3` on
its way back, accepted by L1 after L1's CTM and diamond were upgraded), `CahRecoveryWitness`
(a failed deposit confirmed after a CTM upgrade and with L1 paused).
-/

namespace Contracts.ChainAssetHandler

/-- **EXACTLY ONE SETTLEMENT LAYER.** On every reachable state, a chain registered on L1 has
exactly one holder: a hub `h ≠ 0` with `settlementLayer[c] == h` on `h`'s own bridgehub, or a
live (pending, or failed and unrecovered) migration message for it. A chain not registered
on L1 has no holder. In particular no two hubs both treat the chain as settling on
themselves, and no hub does while the chain is in flight. -/
def Properties.ExactlyOneSettlementLayer : Prop :=
  ∀ (W : World) (s : Sys), W.l1 ≠ 0 → Reach W s → ∀ c : ChainId,
    (s.reg W.l1 c = true → ∃ x, ∀ y, Holds s c y ↔ y = x) ∧
    (s.reg W.l1 c = false → ∀ y, ¬ Holds s c y)

/-- **BRIDGEHUB AND DIAMOND AGREE.** On every reachable state, if chain `c` has a diamond
registered on hub `h`, then `h ≠ 0` and the bridgehub of `h` records `h` as the chain's
settlement layer exactly when the diamond's own `s.settlementLayer` is zero (not away); and a
diamond not registered on its hub is not away. So `registerAlreadyDeployedZKChain`, which
writes nothing to the diamond, registers one that agrees. -/
def Properties.BridgehubAgreesWithDiamond : Prop :=
  ∀ (W : World) (s : Sys), W.l1 ≠ 0 → Reach W s → ∀ h c : ChainId,
    (s.reg h c = true → h ≠ 0 ∧ (s.sl h c = h ↔ s.away h c = false)) ∧
    (s.reg h c = false → s.away h c = false)

/-- **L1 MIGRATION BOOKKEEPING.** On every reachable state, for every chain `c`, L1's
`migrationNumber[c]` is at most `MAX_ALLOWED_NUMBER_OF_MIGRATIONS` (so
`isValidSettlementLayer`'s `IteratedMigrationsNotSupported` check, `L1CAH:229`, never fires);
it is 0 for chains not registered on L1; at 0 the two modelled fields of interval 1 are
cleared (inactive, settlement layer 0) and a registered chain settles on L1; at 1 interval 1 is
active and names the settlement layer L1's bridgehub records, which is not L1; at 2 interval 1
is inactive and the chain settles on L1. Hence a registered chain settles on L1 exactly when its
number is not 1. -/
def Properties.L1MigrationBookkeeping : Prop :=
  ∀ (W : World) (s : Sys), W.l1 ≠ 0 → Reach W s → ∀ c : ChainId,
    s.migNum W.l1 c ≤ maxMigrations ∧
    (s.reg W.l1 c = false → s.migNum W.l1 c = 0) ∧
    (s.migNum W.l1 c = 0 → s.ivActive c = false ∧ s.ivSL c = 0) ∧
    (s.migNum W.l1 c = 0 → s.reg W.l1 c = true → s.sl W.l1 c = W.l1) ∧
    (s.migNum W.l1 c = numToSL →
      s.ivActive c = true ∧ s.ivSL c = s.sl W.l1 c ∧ s.sl W.l1 c ≠ W.l1) ∧
    (s.migNum W.l1 c = numToL1 → s.ivActive c = false ∧ s.sl W.l1 c = W.l1) ∧
    (s.reg W.l1 c = true → (Holds s c (.hub W.l1) ↔ s.migNum W.l1 c ≠ numToSL))

/-- **L1 MIGRATION NUMBER: THREE TRANSITIONS.** Any step that changes L1's
`migrationNumber[c]` is an L1 burn of `c` taking it 0 → 1, an L1 mint of `c` taking it
1 → 2, or a failed-deposit confirmation for `c` taking it 1 → 0. No other step, and no step
on another hub, writes it. This is a statement about single steps; it needs no
reachability premise. -/
def Properties.L1MigrationNumberTransitions : Prop :=
  ∀ (W : World) (s s' : Sys) (l : Label) (c : ChainId), Step W s l s' →
    s'.migNum W.l1 c ≠ s.migNum W.l1 c →
    (s.migNum W.l1 c = 0 ∧ s'.migNum W.l1 c = numToSL ∧ l.burnsOnL1 W c) ∨
    (s.migNum W.l1 c = numToSL ∧ s'.migNum W.l1 c = numToL1 ∧ l.mintsOnL1 W c = true) ∨
    (s.migNum W.l1 c = numToSL ∧ s'.migNum W.l1 c = 0 ∧ ∃ i, l = .confirm i c true)

/-- **A RETURNED CHAIN STAYS ON L1.** From a reachable state where L1's migration number of
`c` is 2 (the chain came back), along any run: the number stays 2, L1 is the chain's only
holder, and no step burns or mints `c` on any hub. -/
def Properties.ReturnedChainStaysOnL1 : Prop :=
  ∀ (W : World) (s s' : Sys) (ls : List Label) (c : ChainId), W.l1 ≠ 0 → Reach W s →
    Run W s ls s' → s.migNum W.l1 c = numToL1 →
    s'.migNum W.l1 c = numToL1 ∧ (∀ y, Holds s' c y ↔ y = .hub W.l1) ∧
    ∀ l ∈ ls, ¬ l.movesChain c

/-- **AT MOST ONE ROUND TRIP.** From a reachable state, along any run, the number of L1
mints of chain `c` plus one if `c` has already returned (L1 number 2) is at most one: a chain
completes at most one L1 → settlement layer → L1 round trip, however many failed attempts it
makes (the comment at `CAH:275-276`). -/
def Properties.AtMostOneRoundTrip : Prop :=
  ∀ (W : World) (s s' : Sys) (ls : List Label) (c : ChainId), W.l1 ≠ 0 → Reach W s →
    Run W s ls s' →
    countL1Mints W c ls + (if s.migNum W.l1 c = numToL1 then 1 else 0) ≤ 1

/-- **FAILED MIGRATION RECOVERY RESTORES THE SOURCE.** From a reachable state, directly after
any L1 burn of `c` (message id `s.nMsgs`), the deposit's failure (an environment step) and L1's
`bridgeConfirmTransferResult(Failure)` are both steps of the model, and the state they reach
is the state before the burn with only the message added, marked consumed: every other field
on every hub — bridgehub, handler and diamond — is back to its value before the burn. In the
source the confirmation also needs the L1 asset router and nullifier unpaused
(`bridge/asset-router/L1AssetRouter.sol:312`, `bridge/L1Nullifier.sol:220`) and a status
proof, which the model does not represent. -/
def Properties.FailedMigrationRecoveryRestoresSource : Prop :=
  ∀ (W : World) (s s1 : Sys) (c t : ChainId) (a : AssetId), W.l1 ≠ 0 →
    Reach W s → Step W s (.burn W.l1 c t a) s1 →
    ∃ s2 s3, Step W s1 (.failDeposit s.nMsgs) s2 ∧ Step W s2 (.confirm s.nMsgs c true) s3 ∧
      s3 = { s with
        msgs := upd s.msgs s.nMsgs (some { burnMsg s W.l1 c t a with status := .done })
        nMsgs := s.nMsgs + 1 }

/-- **IN PROGRESS EXACTLY WHILE UNCONFIRMED.** On every reachable state, L1's
`isMigrationInProgress[c]` — which pauses the chain's L1 deposits
(`state-transition/chain-deps/facets/Mailbox.sol:347-352`) — is set exactly when an
L1-originated migration message for `c` has not been consumed by
`bridgeConfirmTransferResult`, whatever happened to the chain since; there is at most one such
message per chain. -/
def Properties.InProgressTracksUnconfirmedDeparture : Prop :=
  ∀ (W : World) (s : Sys), W.l1 ≠ 0 → Reach W s → ∀ c : ChainId,
    (s.inProgress c = true ↔
      ∃ i m, s.msgs i = some m ∧ m.src = W.l1 ∧ m.chain = c ∧ m.status ≠ .done) ∧
    ∀ i j m m', s.msgs i = some m → s.msgs j = some m' → m.src = W.l1 → m'.src = W.l1 →
      m.chain = c → m'.chain = c → m.status ≠ .done → m'.status ≠ .done → i = j

/-- **VERSION EQUALITY AT BURN AND MINT.** A burn on hub `h` requires the chain's diamond at
the version of the CTM `h`'s bridgehub records for it, and sends that version. A mint on hub
`h` executes a message for its chain, records on `h`'s bridgehub the CTM `h`'s registry gives
the asset id, and leaves the diamond at the version of its own CTM (`s.chainTypeManager`);
when the chain was not registered on `h` (a fresh diamond), the diamond's CTM is that asset
id's CTM and the carried version equals that CTM's version. This is a statement about single
steps. (The returning branch, `Step.mintReturn`, does not read the carried version.) -/
def Properties.VersionEqualityAtBurnAndMint : Prop :=
  ∀ (W : World) (s s' : Sys) (l : Label), Step W s l s' →
    (∀ h c t a, l = .burn h c t a →
      s.dpv h c = s.ctmPV h (s.ctm h c) ∧
      ∃ m, s'.msgs s.nMsgs = some m ∧ m.chain = c ∧ m.pv = s.dpv h c) ∧
    (∀ h i c a, l = .mint h i c a → ∃ m, s.msgs i = some m ∧ m.chain = c ∧
      s'.ctm h c = W.ctmOfAsset h a ∧ s'.dpv h c = s'.ctmPV h (s'.dctm h c) ∧
      (s.reg h c = false →
        s'.dctm h c = W.ctmOfAsset h a ∧ m.pv = s.ctmPV h (W.ctmOfAsset h a)))

/-- **MIGRATIONS DISABLED: NOTHING MOVES.** With the production constant
`CHAIN_MIGRATIONS_ENABLED = false` (`CFG:320`), on every reachable state there is no
migration message, every migration number a hub keeps for another chain is 0, and every chain
registered on L1 has L1 as its only holder. A chain's own counter, kept by its own handler
(`migrationNumber[block.chainid]`, incremented by `setSettlementLayerChainId` when the system
context reports a change, `L2CAH:116-127`), is excluded. -/
def Properties.MigrationsDisabledFreezeSettlement : Prop :=
  ∀ (W : World) (s : Sys), W.l1 ≠ 0 → W.migrationsEnabled = false → Reach W s →
    (∀ i, s.msgs i = none) ∧ (∀ h c, h ≠ c → s.migNum h c = 0) ∧
    ∀ c, s.reg W.l1 c = true → ∀ y, Holds s c y ↔ y = .hub W.l1

/-- **MIGRATION MESSAGES RUN BETWEEN L1 AND A SETTLEMENT LAYER.** On every reachable state,
every migration message, whatever its status, has nonzero endpoints, one of them L1 and the
other not; its destination is whitelisted on its source's bridgehub; the migrating chain is
neither endpoint; a message out of L1 carries migration number 1
(`MIGRATION_NUMBER_L1_TO_SETTLEMENT_LAYER`) and a message into L1 carries 2
(`MIGRATION_NUMBER_SETTLEMENT_LAYER_TO_L1`), the numbers L1's `bridgeMint` requires
(`CAH:374-383`). -/
def Properties.MessagesRunBetweenL1AndALayer : Prop :=
  ∀ (W : World) (s : Sys), W.l1 ≠ 0 → Reach W s → ∀ (i : ℕ) (m : Msg), s.msgs i = some m →
    m.src ≠ 0 ∧ m.dst ≠ 0 ∧ W.wl m.src m.dst = true ∧ m.chain ≠ m.src ∧ m.chain ≠ m.dst ∧
    ((m.src = W.l1 ∧ m.dst ≠ W.l1 ∧ m.num = numToSL) ∨
      (m.dst = W.l1 ∧ m.src ≠ W.l1 ∧ m.num = numToL1))

/-- **L1'S BRIDGEHUB KNOWS WHERE THE CHAIN IS.** On every reachable state, for every chain `c`:
if a hub `g` other than L1 holds `c` (its own bridgehub says `c` settles there), L1's
`settlementLayer[c]` is `g`; if a live message holds `c`, L1's `settlementLayer[c]` is the
message's endpoint other than L1 (its destination if it left L1, its source if it is on its way
back). -/
def Properties.L1SettlementLayerTracksHolder : Prop :=
  ∀ (W : World) (s : Sys), W.l1 ≠ 0 → Reach W s → ∀ c : ChainId,
    (∀ g : ChainId, g ≠ W.l1 → Holds s c (.hub g) → s.sl W.l1 c = g) ∧
    (∀ (i : ℕ) (m : Msg), s.msgs i = some m → m.chain = c → m.Live →
      s.sl W.l1 c = if m.src = W.l1 then m.dst else m.src)

/-- **A SETTLEMENT LAYER ACCEPTS EVERY ARRIVAL.** On every reachable state, let message `i` be
pending and from L1, to hub `g = m.dst`. Suppose migrations are enabled, `g`'s `paused()`, its
ecosystem pause and the pause of the CTM `g`'s registry gives the asset id are off, that CTM is
not zero (`BH:437-440`), and the carried protocol version is that CTM's (`CTM:754-756`). Then
the chain is not registered on `g`, so `g`'s `bridgeMint` of message `i` deploys a fresh diamond,
it is a step, and after it `g` is the chain's only holder. So the fresh branch's other guards —
the chain does not already settle on `g` (`BH:441-443`), is not registered there
(`CAH:397-399`), and `g` is not L1 (`MIG:277-279`) — hold for every such message. -/
def Properties.GatewayAcceptsArrival : Prop :=
  ∀ (W : World) (s : Sys) (i : ℕ) (m : Msg), W.l1 ≠ 0 → Reach W s →
    s.msgs i = some m → m.status = .pending → m.src = W.l1 →
    W.migrationsEnabled = true → s.paused m.dst = false → s.ecoPaused m.dst = false →
    s.ctmPaused m.dst (W.ctmOfAsset m.dst m.asset) = false →
    W.ctmOfAsset m.dst m.asset ≠ 0 →
    m.pv = s.ctmPV m.dst (W.ctmOfAsset m.dst m.asset) →
    s.reg m.dst m.chain = false ∧
      ∃ s', Step W s (.mint m.dst i m.chain m.asset) s' ∧
        ∀ y, Holds s' m.chain y ↔ y = .hub m.dst

/-- **L1 ACCEPTS EVERY RETURN.** On every reachable state, let message `i` be pending and to L1.
Suppose migrations are enabled, L1's `paused()`, its ecosystem pause and the pause of the CTM
L1's registry gives the asset id are off, that CTM is not zero (`BH:437-440`), and L1's diamond
of the chain is at the version of its own CTM (`MIG:223-229`). Then L1's `bridgeMint` of
message `i` is a step, reusing the chain's L1 diamond; after it L1's migration number of the
chain is 2 and L1 is its only holder. So the returning branch's other guards — L1's checks of
the migration numbers (`CAH:374-383`) and of interval 1 (`L1CAH:309-314`), the chain not
settling on L1 already (`BH:441-443`), its registration on L1, and the diamond's away check
(`MIG:280-282`) — hold for every such message. -/
def Properties.L1AcceptsReturn : Prop :=
  ∀ (W : World) (s : Sys) (i : ℕ) (m : Msg), W.l1 ≠ 0 → Reach W s →
    s.msgs i = some m → m.status = .pending → m.dst = W.l1 →
    W.migrationsEnabled = true → s.paused W.l1 = false → s.ecoPaused W.l1 = false →
    s.ctmPaused W.l1 (W.ctmOfAsset W.l1 m.asset) = false →
    W.ctmOfAsset W.l1 m.asset ≠ 0 →
    s.dpv W.l1 m.chain = s.ctmPV W.l1 (s.dctm W.l1 m.chain) →
    ∃ s', Step W s (.mint W.l1 i m.chain m.asset) s' ∧
      s'.migNum W.l1 m.chain = numToL1 ∧ ∀ y, Holds s' m.chain y ↔ y = .hub W.l1

/-- **A FAILED DEPOSIT CAN BE CONFIRMED.** On every reachable state, let message `i` be from L1
with a failed L2 transaction. If L1's diamond of the chain is at the version the burn data
carries (the check `MIG:327-330`), L1's `bridgeConfirmTransferResult(Failure)` for message `i`
is a step of the model; it needs no pause switch, release flag or CTM version
(`RecoveryIgnoresPauses` in `Properties/Pause.lean`). After it L1 is the chain's only holder,
L1's migration number of the chain is 0, and the chain is not in progress. As in
`FailedMigrationRecoveryRestoresSource`, the L1 asset router's and nullifier's pauses and the
status proof are outside the model. -/
def Properties.FailedDepositConfirmable : Prop :=
  ∀ (W : World) (s : Sys) (i : ℕ) (m : Msg), W.l1 ≠ 0 → Reach W s →
    s.msgs i = some m → m.src = W.l1 → m.status = .failed →
    s.dpv W.l1 m.chain = m.pv →
    ∃ s', Step W s (.confirm i m.chain true) s' ∧
      (∀ y, Holds s' m.chain y ↔ y = .hub W.l1) ∧ s'.migNum W.l1 m.chain = 0 ∧
      s'.inProgress m.chain = false

/-! ## Witnesses -/

/-- **A COMPLETE ROUND TRIP.** From the fresh state `cahInit`, `cahRoundTrip` is a run of
`cahWorld`: chain `3` goes to the gateway by a fresh mint and returns to L1 by a returning
mint. It ends with one L1 mint of chain `3`, L1's number 2, chain `3` registered on both hubs,
and L1 its only holder. This instantiates the premises of `AtMostOneRoundTrip` (its bound is
reached), `L1MigrationNumberTransitions` (0 → 1 and 1 → 2), `VersionEqualityAtBurnAndMint`
(both mint branches) and, at the end state, `ReturnedChainStaysOnL1`. -/
def Properties.CahRoundTripWitness : Prop :=
  Init cahInit ∧ cahWorld.l1 ≠ 0 ∧
  ∃ s, Run cahWorld cahInit cahRoundTrip s ∧ Reach cahWorld s ∧
    countL1Mints cahWorld 3 cahRoundTrip = 1 ∧
    s.migNum cahWorld.l1 3 = numToL1 ∧ s.reg cahWorld.l1 3 = true ∧ s.reg 2 3 = true ∧
    (∀ y, Holds s 3 y ↔ y = .hub cahWorld.l1)

/-- **IN FLIGHT.** After the setup and L1's burn of chain `3` to the gateway, chain `3` is
registered on L1, its only holder is message `0`, L1's bridgehub records the gateway while the
L1 diamond is away, L1's number is 1 with interval 1 active for the gateway, and the chain is
in progress. This instantiates `ExactlyOneSettlementLayer` with a message holder,
`BridgehubAgreesWithDiamond` with both sides false, `L1MigrationBookkeeping` at 1, and
`InProgressTracksUnconfirmedDeparture` with the flag set. -/
def Properties.CahInFlightWitness : Prop :=
  ∃ s, Run cahWorld cahInit (cahSetup ++ [.burn 1 3 2 5]) s ∧ Reach cahWorld s ∧
    s.reg cahWorld.l1 3 = true ∧ (∀ y, Holds s 3 y ↔ y = .msg 0) ∧
    s.sl cahWorld.l1 3 = 2 ∧ s.away cahWorld.l1 3 = true ∧
    s.migNum cahWorld.l1 3 = numToSL ∧ s.ivActive 3 = true ∧ s.ivSL 3 = 2 ∧
    s.inProgress 3 = true

/-- **ON THE GATEWAY.** After the gateway mints chain `3` (fresh), its only holder is hub `2`,
which is not L1, and L1's bridgehub records `2`; the gateway's diamond is registered under CTM
`7` at that CTM's version, and the chain is still in progress on L1 (the deposit is not yet
confirmed). This instantiates `ExactlyOneSettlementLayer` with a hub other than L1 and the hub
clause of `L1SettlementLayerTracksHolder`. -/
def Properties.CahGatewayWitness : Prop :=
  ∃ s, Run cahWorld cahInit (cahSetup ++ [.burn 1 3 2 5, .mint 2 0 3 5]) s ∧
    Reach cahWorld s ∧ 2 ≠ cahWorld.l1 ∧
    (∀ y, Holds s 3 y ↔ y = .hub 2) ∧ s.sl cahWorld.l1 3 = 2 ∧
    s.reg 2 3 = true ∧ s.dctm 2 3 = 7 ∧ s.dpv 2 3 = s.ctmPV 2 7 ∧ s.inProgress 3 = true

/-- **A FAILED ATTEMPT, RECOVERED.** From the reachable setup state `s0`, L1's burn of chain
`3` is a step (the premises of `FailedMigrationRecoveryRestoresSource`); the attempt
`cahFailedAttempt` ends with L1's number back to 0, chain `3` on L1, not in progress, and a
second burn enabled. Its last step is a failed-deposit confirmation (L1's number goes
1 → 0). -/
def Properties.CahFailedAttemptWitness : Prop :=
  ∃ s0 s1, Run cahWorld cahInit cahSetup s0 ∧ Reach cahWorld s0 ∧
    Step cahWorld s0 (.burn cahWorld.l1 3 2 5) s1 ∧
    ∃ s, Run cahWorld cahInit cahFailedAttempt s ∧
      s.migNum cahWorld.l1 3 = 0 ∧ s.sl cahWorld.l1 3 = cahWorld.l1 ∧ s.inProgress 3 = false ∧
      ∃ s', Step cahWorld s (.burn cahWorld.l1 3 2 5) s'

/-- **AFTER THE RETURN.** From the end state of the round trip (reachable, L1's number 2), a
three-step run (a CTM upgrade, the diamond's catch-up upgrade, an ecosystem pause) is a run
of `cahWorld`, and a further burn of chain `3` is not a step. This instantiates every premise of
`ReturnedChainStaysOnL1` with a non-empty run. -/
def Properties.CahReturnedChainWitness : Prop :=
  ∃ s s', Run cahWorld cahInit cahRoundTrip s ∧ Reach cahWorld s ∧
    s.migNum cahWorld.l1 3 = numToL1 ∧
    Run cahWorld s [.ctmUpgrade 1 7 2, .diamondUpgrade 1 3 2, .pauseMigration 1 10] s' ∧
    ¬ ∃ s'', Step cahWorld s (.burn cahWorld.l1 3 2 5) s''

/-- **THE PRODUCTION CONSTANT.** In `cahWorldDisabled` (`CHAIN_MIGRATIONS_ENABLED = false`)
the setup is a run, so chain `3` is registered on L1 in a reachable state; there L1's burn of
chain `3` is not a step, while in `cahWorld`, which differs only in the constant, the same burn
from the same state is a step. This instantiates every premise of
`MigrationsDisabledFreezeSettlement`, with a chain registered on L1. -/
def Properties.CahDisabledWitness : Prop :=
  cahWorldDisabled.migrationsEnabled = false ∧ cahWorldDisabled.l1 ≠ 0 ∧
  ∃ s, Run cahWorldDisabled cahInit cahSetup s ∧ Reach cahWorldDisabled s ∧
    s.reg cahWorldDisabled.l1 3 = true ∧
    (¬ ∃ s', Step cahWorldDisabled s (.burn 1 3 2 5) s') ∧
    ∃ s', Step cahWorld s (.burn 1 3 2 5) s'

/-- **THE GATEWAY ACCEPTS AN ARRIVAL WHILE L1 IS PAUSED.** After the setup, L1's burn of chain
`3` to the gateway and L1's `pause()` (a reachable state), message `0` is pending, from L1 to
hub `2`, for chain `3` and asset id `5`, carrying the version of CTM `7` on the gateway; the
gateway's switches are off, chain `3` is not registered there, and the gateway's mint of
message `0` is a step. This instantiates every premise of `GatewayAcceptsArrival`, the mint
half of `PausedCTMChainsDoNotMove` (`Properties/Pause.lean`), and `L1SettlementLayerTracksHolder`
for a message out of L1 (L1's bridgehub records `2`). -/
def Properties.CahArrivalWitness : Prop :=
  cahWorld.l1 ≠ 0 ∧ cahWorld.migrationsEnabled = true ∧
  ∃ s, Run cahWorld cahInit (cahSetup ++ [.burn 1 3 2 5, .pause 1 10]) s ∧ Reach cahWorld s ∧
    s.paused 1 = true ∧ s.sl 1 3 = 2 ∧
    (∃ m, s.msgs 0 = some m ∧ m.status = .pending ∧ m.src = cahWorld.l1 ∧ m.dst = 2 ∧
      m.chain = 3 ∧
      m.asset = 5 ∧ m.Live ∧ m.pv = s.ctmPV 2 (cahWorld.ctmOfAsset 2 5)) ∧
    s.paused 2 = false ∧ s.ecoPaused 2 = false ∧ s.ctmPaused 2 (cahWorld.ctmOfAsset 2 5) = false ∧
    cahWorld.ctmOfAsset 2 5 ≠ 0 ∧ s.reg 2 3 = false ∧
    ∃ s', Step cahWorld s (.mint 2 0 3 5) s'

/-- **ON ITS WAY BACK, ACCEPTED AFTER UPGRADES.** After the round trip up to the gateway's burn
of chain `3` back to L1 (message `1`), CTM `7` on L1 moves to version `2`, the
gateway chain's L1 diamond and then chain `3`'s away L1 diamond are upgraded to `2`. In that
reachable state message `1` is the only holder of chain `3`; it is pending, from hub `2` to L1,
with number 2, while message `0` (consumed) went from L1 to `2` with number 1; L1's bridgehub
records `2`; L1's switches are off and its diamond of chain `3` is at its CTM's version; and L1's
mint of message `1` is a step. This instantiates both disjuncts of
`MessagesRunBetweenL1AndALayer`, the message clause of `L1SettlementLayerTracksHolder` for a
message into L1, and every premise of `L1AcceptsReturn` after the CTM's version changed. -/
def Properties.CahReturnInFlightWitness : Prop :=
  cahWorld.l1 ≠ 0 ∧ cahWorld.migrationsEnabled = true ∧
  ∃ s, Run cahWorld cahInit
      (cahSetup ++ [.burn 1 3 2 5, .mint 2 0 3 5, .confirm 0 3 false, .burn 2 3 1 5,
        .ctmUpgrade 1 7 2, .diamondUpgrade 1 2 2, .diamondUpgrade 1 3 2]) s ∧
    Reach cahWorld s ∧ (∀ y, Holds s 3 y ↔ y = .msg 1) ∧ s.sl 1 3 = 2 ∧
    (∃ m0, s.msgs 0 = some m0 ∧ m0.src = 1 ∧ m0.dst = 2 ∧ m0.num = numToSL ∧
      m0.status = .done) ∧
    (∃ m1, s.msgs 1 = some m1 ∧ m1.status = .pending ∧ m1.src = 2 ∧ m1.dst = cahWorld.l1 ∧
      m1.chain = 3 ∧ m1.asset = 5 ∧ m1.num = numToL1 ∧ m1.Live) ∧
    s.ctmPV 1 7 = 2 ∧ s.dpv 1 3 = s.ctmPV 1 (s.dctm 1 3) ∧
    s.paused 1 = false ∧ s.ecoPaused 1 = false ∧ s.ctmPaused 1 (cahWorld.ctmOfAsset 1 5) = false ∧
    cahWorld.ctmOfAsset 1 5 ≠ 0 ∧
    ∃ s', Step cahWorld s (.mint 1 1 3 5) s'

/-- **A FAILED DEPOSIT, CONFIRMED AFTER A CTM UPGRADE AND WITH L1 PAUSED.** After the setup,
L1's burn of chain `3`, an upgrade of CTM `7` on L1 to version `2`, L1's `pause()` and the
deposit's failure (a reachable state), message `0` is from L1 and failed, L1's diamond of chain
`3` is still at the version the message carries while CTM `7` is not, L1 is paused, and L1's
confirmation of the failure is a step. This instantiates every premise of
`FailedDepositConfirmable` and the premise of `RecoveryIgnoresPauses`. -/
def Properties.CahRecoveryWitness : Prop :=
  cahWorld.l1 ≠ 0 ∧
  ∃ s, Run cahWorld cahInit
      (cahSetup ++ [.burn 1 3 2 5, .ctmUpgrade 1 7 2, .pause 1 10, .failDeposit 0]) s ∧
    Reach cahWorld s ∧
    (∃ m, s.msgs 0 = some m ∧ m.src = cahWorld.l1 ∧ m.status = .failed ∧ m.chain = 3 ∧
      s.dpv 1 3 = m.pv ∧ s.ctmPV 1 7 ≠ m.pv) ∧
    s.paused 1 = true ∧
    ∃ s', Step cahWorld s (.confirm 0 3 true) s'

end Contracts.ChainAssetHandler
