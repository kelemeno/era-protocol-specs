import EraSpec.Contracts.ChainAssetHandler.Specs.Migration

/-!
# Properties: where a chain settles, its migration number, and recovery

Statements about `EraSpec.Contracts.ChainAssetHandler.Specs.Migration`. Proofs are in
`EraSpec.Contracts.ChainAssetHandler.Proofs.Migration`. Every reachability statement is over
`Reach`: any interleaving of every step of the model on every hub, from a fresh deployment.
`W.l1 ≠ 0` is `block.chainid ≠ 0` on L1.

* **One settlement layer.** Every chain registered on L1 has exactly one holder — one hub
  whose bridgehub says the chain settles there, or one live migration message — and a chain
  not registered on L1 has none (`ExactlyOneSettlementLayer`). The hub's bridgehub and the
  chain's diamond on that hub agree on it (`BridgehubAgreesWithDiamond`).
* **The migration number.** On L1 it is at most 2 and mirrors where the chain is and what
  interval is recorded (`L1MigrationBookkeeping`); it changes only 0→1 (burn), 1→2 (return)
  and 1→0 (failed-deposit recovery), so it is monotone except for that recovery
  (`L1MigrationNumberTransitions`). A chain back on L1 never moves again
  (`ReturnedChainStaysOnL1`), and a chain completes at most one round trip
  (`AtMostOneRoundTrip`).
* **Recovery.** After any L1 burn, the deposit's failure and its confirmation are enabled
  and restore every hub field to its value before the burn (`FailedMigrationRecoveryRestoresSource`).
  `isMigrationInProgress` is set exactly while an L1-originated migration message is not yet
  confirmed (`InProgressTracksUnconfirmedDeparture`).
* **Versions.** A burn requires the diamond at its CTM's version; a mint leaves the diamond at
  its CTM's version, and a fresh deployment requires the carried version to be the CTM's
  (`VersionEqualityAtBurnAndMint`).
* **Production constant.** With `CHAIN_MIGRATIONS_ENABLED = false` nothing ever migrates
  (`MigrationsDisabledFreezeSettlement`).
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
settlement layer exactly when the diamond's own `s.settlementLayer` is zero (not away). -/
def Properties.BridgehubAgreesWithDiamond : Prop :=
  ∀ (W : World) (s : Sys), W.l1 ≠ 0 → Reach W s → ∀ h c : ChainId, s.reg h c = true →
    h ≠ 0 ∧ (s.sl h c = h ↔ s.away h c = false)

/-- **L1 MIGRATION BOOKKEEPING.** On every reachable state, for every chain `c`, L1's
`migrationNumber[c]` is at most `MAX_ALLOWED_NUMBER_OF_MIGRATIONS` (so
`isValidSettlementLayer`'s `IteratedMigrationsNotSupported` check, `L1CAH:229`, never fires);
it is 0 for unregistered chains; at 0 interval 1 is empty and a registered chain settles on
L1; at 1 interval 1 is active and names the settlement layer L1's bridgehub records, which is
not L1; at 2 interval 1 is closed and the chain settles on L1. Hence a registered chain
settles on L1 exactly when its number is not 1. -/
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

/-- **L1 MIGRATION NUMBER: MONOTONE EXCEPT RECOVERY.** Any step that changes L1's
`migrationNumber[c]` is an L1 burn of `c` taking it 0 → 1, an L1 mint of `c` taking it
1 → 2, or a failed-deposit confirmation for `c` taking it 1 → 0. No other step, and no step
on another hub, writes it. -/
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
makes (the NatSpec of `CAH:275-276`). -/
def Properties.AtMostOneRoundTrip : Prop :=
  ∀ (W : World) (s s' : Sys) (ls : List Label) (c : ChainId), W.l1 ≠ 0 → Reach W s →
    Run W s ls s' →
    countL1Mints W c ls + (if s.migNum W.l1 c = numToL1 then 1 else 0) ≤ 1

/-- **FAILED MIGRATION RECOVERY RESTORES THE SOURCE.** From a reachable state, after any L1
burn of `c` (message id `s.nMsgs`), the deposit's failure and L1's
`bridgeConfirmTransferResult(Failure)` are both enabled, and the state they reach is the
state before the burn with only the message added, marked consumed: every bridgehub,
handler and diamond field on every hub is back to its value before the burn. -/
def Properties.FailedMigrationRecoveryRestoresSource : Prop :=
  ∀ (W : World) (s s1 : Sys) (c t : ChainId) (a : AssetId) (orig : Address), W.l1 ≠ 0 →
    Reach W s → Step W s (.burn W.l1 c t a orig) s1 →
    ∃ s2 s3, Step W s1 (.failDeposit s.nMsgs) s2 ∧ Step W s2 (.confirm s.nMsgs c true) s3 ∧
      s3 = { s with
        msgs := upd s.msgs s.nMsgs (some { burnMsg s W.l1 c t a with status := .done })
        nMsgs := s.nMsgs + 1 }

/-- **IN PROGRESS EXACTLY WHILE UNCONFIRMED.** On every reachable state, L1's
`isMigrationInProgress[c]` — which pauses the chain's L1 deposits (`Mailbox.depositsPaused`) —
is set exactly when an L1-originated migration message for `c` has not been consumed by
`bridgeConfirmTransferResult`; there is at most one such message per chain. -/
def Properties.InProgressTracksUnconfirmedDeparture : Prop :=
  ∀ (W : World) (s : Sys), W.l1 ≠ 0 → Reach W s → ∀ c : ChainId,
    (s.inProgress c = true ↔
      ∃ i m, s.msgs i = some m ∧ m.src = W.l1 ∧ m.chain = c ∧ m.status ≠ .done) ∧
    ∀ i j m m', s.msgs i = some m → s.msgs j = some m' → m.src = W.l1 → m'.src = W.l1 →
      m.chain = c → m'.chain = c → m.status ≠ .done → m'.status ≠ .done → i = j

/-- **VERSION EQUALITY AT BURN AND MINT.** A burn on hub `h` requires the chain's diamond at
its CTM's version and sends that version. A mint on hub `h` leaves the diamond at the version
of its CTM there, which is the asset id's CTM; when the diamond is freshly deployed, the
carried version must equal that CTM's. -/
def Properties.VersionEqualityAtBurnAndMint : Prop :=
  ∀ (W : World) (s s' : Sys) (l : Label), Step W s l s' →
    (∀ h c t a orig, l = .burn h c t a orig →
      s.dpv h c = s.ctmPV h (s.ctm h c) ∧
      ∃ m, s'.msgs s.nMsgs = some m ∧ m.chain = c ∧ m.pv = s.dpv h c) ∧
    (∀ h i c a, l = .mint h i c a → ∃ m, s.msgs i = some m ∧ m.chain = c ∧
      s'.ctm h c = W.ctmOfAsset a ∧ s'.dpv h c = s'.ctmPV h (s'.ctm h c) ∧
      (s.reg h c = false → m.pv = s.ctmPV h (W.ctmOfAsset a)))

/-- **MIGRATIONS DISABLED: NOTHING MOVES.** With the production constant
`CHAIN_MIGRATIONS_ENABLED = false` (`CFG:320`), on every reachable state there is no
migration message, every migration number is 0, and every chain registered on L1 has L1 as
its only holder. -/
def Properties.MigrationsDisabledFreezeSettlement : Prop :=
  ∀ (W : World) (s : Sys), W.l1 ≠ 0 → W.migrationsEnabled = false → Reach W s →
    (∀ i, s.msgs i = none) ∧ (∀ h c, s.migNum h c = 0) ∧
    ∀ c, s.reg W.l1 c = true → ∀ y, Holds s c y ↔ y = .hub W.l1

end Contracts.ChainAssetHandler
