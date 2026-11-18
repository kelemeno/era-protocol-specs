import EraSpec.Protocol.InteropPeerRegistry.Specs.PeerMirror

/-!
# Properties: the peer whitelist's mirror, and the `baseTokenAssetId` entries on each chain

Statements about `EraSpec.Protocol.InteropPeerRegistry.Specs.PeerMirror` (era-contracts `b17415d20`).
Proofs are in `EraSpec.Protocol.InteropPeerRegistry.Proofs.PeerMirror`. Every run starts from fresh
storage (`init`); `deployed` executes each chain's queue in order and has the full `_checkPeerPair`
in `deregisterInteropPairs`. Every step kind, the latent migration steps and the retired
registration included, is enabled for the whole run.

## (a) `isPeerAllowed` mirrors `interopPeerAllowed`

On chain `c`, `isPeerAllowed[p]` equals the sender's `interopPeerAllowed[c][p]` whenever no entry
writing it is pending in `c`'s queue and the last executed one succeeded
(`PeerFlagMirrorsWhenLastEntrySucceeded`). If every executed **service** entry succeeded, the
flags agree whenever none is pending, however many re-submissions failed
(`PeerFlagMirrorsWhenServiceEntriesSucceed`): a re-submission is only possible for an allowed pair,
so a failed one never leaves the flag behind. A failed service entry does
(`FailedServiceEntryLeavesPeerFlagBehind`); for a failed `allowInteropPeer` entry the re-submission
is then enabled and restores the flag (`ResubmissionRestoresPeerFlag`).

A failed `deregisterChainForInterop` entry leaves the flags disagreeing the other way: `c`'s flag
`true`, the sender's `false` (`FailedDeregLeavesPeerFlagOn`). Nothing re-sends a deregistration. A
repeated `deregisterInteropPairs(c, [p])`, which does not require the sender's flag, is enabled and
restores agreement wherever `_checkPeerPair` passes and `c`'s queue is empty
(`DeregistrationRepeatClearsPeerFlag`). While L1 records `p` as settling on `c`, `_checkPeerPair`
rejects it and `allowInteropPeer(c, p)`, and the re-submission needs the sender's flag
(`FailedDeregRepairBlockedWhileSettled`). From any state in which L1 records `p` on `c`, the
sender's flag is `false` and no entry writing `c`'s flag is pending, no step changes `c`'s flag,
and the last two conditions persist (`DisallowedPeerFlagFrozenWhileOnLayer`). For a created `p`,
L1 records a settlement layer other than L1 only after a migration, which is disabled at
`b17415d20`.

Executing the queue out of order breaks the mirror with every entry succeeding
(`WithoutFifoPeerFlagDesyncs`). Neither flag is ever set for the chain itself or for L1, although
the re-submission skips `_checkPeerPair` (`PeerFlagsOnlyForProperPeers`).

## (b) A chain's `baseTokenAssetId[p]` is `0` or L1's

On every chain, `baseTokenAssetId[p]` is `0` or the L1 Bridgehub's current `baseTokenAssetId[p]`
(`L2BaseTokenEntryIsZeroOrL1Value`). L1's entry never changes once nonzero, including through a
round trip of `p` to a settlement layer, whose return copies the layer's entry into L1
(`L1BaseTokenFixedOnceSet`). Hence after `p` is created with asset id `a`, every chain's entry for
`p` is `0` or `a` forever (`L2BaseTokenEntryIsZeroOrCreationValue`). That L1's
`baseTokenAssetId[p]` is fixed after creation is not assumed anywhere here: it is
`L1BaseTokenFixedOnceSet`.

## (c) Presence while `p` settles on `c` (latent: migrations are disabled at `b17415d20`)

While `c`'s `L2Bridgehub` records `p` as settling on `c`, `c`'s entry for `p` is L1's, which is
nonzero (`SettledChainEntryIsL1Value`); while `p`'s withdrawal from `c` is in flight, `c`'s entry and
the carried asset id are L1's (`ReturningChainEntryIsL1Value`, `ReturnCarriesL1BaseToken`). While `p`'s
arrival on `c` is queued, the queued data carries L1's value and no deregistration of `p` on `c` is
queued after it (`PendingArrivalCarriesL1Value`), but `c`'s entry itself may still be `0`
(`PendingArrivalEntryMayBeZero`): the presence claim does not extend to that window.
`_checkPeerPair`'s NatSpec (`CRS:170-171`) says such an entry must never change. `baseTokenAssetId[p]`
does not, through any step, the re-submission included, and a `true` `isPeerAllowed[p]` stays
`true` (`SettledEntryNeverChanges`). A `false` one can turn on: after a failed service entry, a
re-submission, which skips `_checkPeerPair`, sets it while `p` settles on `c`
(`SettledPeerFlagCanTurnOn`; with the re-submission and the failed entry stated,
`SettledPeerFlagTurnsOnByResubmission`). Both mechanisms are load-bearing. Without the
settlement clause in `deregisterInteropPairs`, a settled chain's entry is cleared
(`WithoutDeregSettlementCheckSettledEntryCleared`) and its return then writes `0` into L1
(`WithoutDeregSettlementCheckL1BaseTokenRewritten`). Without FIFO execution, a settled chain's
entry is cleared too (`WithoutFifoSettledEntryCleared`).

## (d) Deregistering a pair after `p` returned from `c`

Once `p` settles on L1 again, `deregisterInteropPairs(c, [p])` passes `_checkPeerPair`
(`ReturnedPeerDeregistrationAccepted`), and its execution clears `c`'s entry for `p`
(`ReturnedPeerEntryCanBeCleared`). That entry's readers on `c` are listed in the topic README. The
migration reader (`CAH:322`) is the start of a return, which the model enables only where `c`
records `p` as settling on `c` (`BB:411-413`); there the entry is L1's
(`SettledChainEntryIsL1Value`, `ReturnCarriesL1BaseToken`).

## Non-vacuity

`MirrorAfterFailedServiceEntryWitness` and `MirrorAfterFailedResubmissionWitness` meet the
premises of the two mirror statements with a failed entry in the log, and the first also the
premise of `PeerFlagsOnlyForProperPeers` (both flags `true`). `FailedServiceEntryLeavesPeerFlagBehind`
meets those of `ResubmissionRestoresPeerFlag`, with the chain's flag `false`.
`FailedDeregLeavesPeerFlagOn` meets those of `DeregistrationRepeatClearsPeerFlag`, with the chain's
flag `true` and the sender's `false`. `DisallowedPeerFlagFrozenWitness` meets those of
`DisallowedPeerFlagFrozenWhileOnLayer` with a nonempty queue, the chain's flag `true` and the
sender's `false`.
`BaseTokenEntryWitness`, `CreationValueWitness` and `L1BaseTokenRewriteWitness` meet those of (b).
`SettledEntryWitness` (the executed entry is a re-submission while `p` settles on `c`; it also meets
the premises of `SettledChainEntryIsL1Value`), `ReturnWitness` (for `ReturnCarriesL1BaseToken` and
`ReturningChainEntryIsL1Value`) and `PendingArrivalEntryMayBeZero` (for
`PendingArrivalCarriesL1Value`) meet those of (c). The state of `ReturnedPeerEntryCanBeCleared`
meets the premises of `ReturnedPeerDeregistrationAccepted`.
-/

namespace Contracts.InteropPeerRegistry

/-! ## (a) The mirror -/

/-- **HEADLINE (a): `isPeerAllowed` MIRRORS L1 ONCE ITS LAST ENTRY SUCCEEDED.** On every reachable
state, for every chain `c` and peer `p`: if no entry writing `isPeerAllowed[p]` is pending in `c`'s
queue, and the last executed one succeeded (or none was executed), then `c`'s
`isPeerAllowed[p]` equals the sender's `interopPeerAllowed[c][p]`. -/
def Properties.PeerFlagMirrorsWhenLastEntrySucceeded : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P S →
    ∀ c p : ChainId, NoPendingPeerEntry p (S.queue c) → lastPeerEntryOk p (S.done c) = true →
      (S.hub c).peer p = S.l1.allowed c p

/-- **(a), FAILED RE-SUBMISSIONS DO NOT MATTER.** On every reachable state: if no entry writing
`isPeerAllowed[p]` is pending in `c`'s queue, and every executed service entry of `c` writing it
succeeded, then `c`'s `isPeerAllowed[p]` equals `interopPeerAllowed[c][p]`, whatever happened to the
re-submissions. -/
def Properties.PeerFlagMirrorsWhenServiceEntriesSucceed : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P S →
    ∀ c p : ChainId, NoPendingPeerEntry p (S.queue c) →
      (∀ e ∈ S.done c, e.1.isService = true → (e.1.peerWrite p).isSome = true → e.2 = true) →
      (S.hub c).peer p = S.l1.allowed c p

/-- **A FAILED SERVICE ENTRY LEAVES THE FLAG BEHIND.** A reachable state in which `c`'s queue is
empty, the sender allows `(c, p)`, and `c`'s `isPeerAllowed[p]` is `false`. In the run behind it,
the service transaction of `allowInteropPeer(c, p)` failed. -/
def Properties.FailedServiceEntryLeavesPeerFlagBehind : Prop :=
  ∃ (P : Params) (S : State) (c p : ChainId), Reach deployed P S ∧ S.queue c = [] ∧
    S.l1.allowed c p = true ∧ (S.hub c).peer p = false

/-- **… WITH THE FAILED SERVICE ENTRY ON THE LOG.** `FailedServiceEntryLeavesPeerFlagBehind`, with
the failure stated: `c`'s executed entries include a failed service entry `allowInteropPeer(p, a)`
for some `a`. -/
def Properties.FailedServiceEntryLeavesPeerFlagBehindLogged : Prop :=
  ∃ (P : Params) (S : State) (c p : ChainId), Reach deployed P S ∧ S.queue c = [] ∧
    S.l1.allowed c p = true ∧ (S.hub c).peer p = false ∧
    ∃ a, (Msg.allow p a true, false) ∈ S.done c

/-- **THE RE-SUBMISSION REPAIRS IT.** On every reachable state where `c`'s queue is empty and the
sender allows `(c, p)`, the re-submission is enabled, its entry can execute successfully, and
afterwards the queue is empty and both flags are `true`. -/
def Properties.ResubmissionRestoresPeerFlag : Prop :=
  ∀ (P : Params) (S : State) (c p : ChainId), Reach deployed P S → S.queue c = [] →
    S.l1.allowed c p = true →
    ∃ S₁ S₂ : State, Step deployed P S (.resubmit c p) S₁ ∧
      Step deployed P S₁ (.execute c 0 true) S₂ ∧
      S₂.queue c = [] ∧ (S₂.hub c).peer p = true ∧ S₂.l1.allowed c p = true

/-- **A FAILED DEREGISTRATION LEAVES THE FLAG ON.** A reachable state in which `c` is registered,
`c`'s queue is empty, `p ≠ c`, `p` is not L1, L1 does not record `p` as settling on `c`, the sender
does not allow `(c, p)`, `c`'s `isPeerAllowed[p]` is `true`, and `c`'s log holds a failed
`deregisterChainForInterop(p)` entry. In the run behind it, the service transaction of
`allowInteropPeer(c, p)` succeeded and that of `deregisterInteropPairs(c, [p])` failed. -/
def Properties.FailedDeregLeavesPeerFlagOn : Prop :=
  ∃ (P : Params) (S : State) (c p : ChainId), Reach deployed P S ∧ S.l1.registered c = true ∧
    S.queue c = [] ∧ p ≠ c ∧ p ≠ P.l1 ∧ S.l1.sl p ≠ c ∧
    S.l1.allowed c p = false ∧ (S.hub c).peer p = true ∧ (Msg.dereg p, false) ∈ S.done c

/-- **A REPEATED DEREGISTRATION REPAIRS IT WHERE `_checkPeerPair` PASSES.** On every reachable
state where `c` is registered, `c`'s queue is empty, `p ≠ c`, `p` is not L1, and L1 does not record
`p` as settling on `c`: `deregisterInteropPairs(c, [p])` is enabled, whatever the sender's flag,
its entry can execute successfully, and afterwards `c`'s queue is empty and both `c`'s
`isPeerAllowed[p]` and the sender's `interopPeerAllowed[c][p]` are `false`. -/
def Properties.DeregistrationRepeatClearsPeerFlag : Prop :=
  ∀ (P : Params) (S : State) (c p : ChainId), Reach deployed P S → S.l1.registered c = true →
    S.queue c = [] → p ≠ c → p ≠ P.l1 → S.l1.sl p ≠ c →
    ∃ S₁ S₂ : State, Step deployed P S (.deregisterInteropPairs c [p]) S₁ ∧
      Step deployed P S₁ (.execute c 0 true) S₂ ∧
      S₂.queue c = [] ∧ (S₂.hub c).peer p = false ∧ S₂.l1.allowed c p = false

/-- **… BUT NOT WHILE `p` SETTLES ON `c`.** A reachable state in which `c` is registered, `c`'s queue
is empty, the sender does not allow `(c, p)`, `c`'s `isPeerAllowed[p]` is `true`, `c`'s log holds a
failed `deregisterChainForInterop(p)` entry, and both `c`'s `L2Bridgehub` and L1 record `p` as
settling on `c`. From it, no `deregisterInteropPairs(c, ps)` with `p ∈ ps` and no
`allowInteropPeer(c, p)` succeeds (both run `_checkPeerPair`), and no re-submission for `(c, p)`
succeeds (it requires the sender's flag). -/
def Properties.FailedDeregRepairBlockedWhileSettled : Prop :=
  ∃ (P : Params) (S : State) (c p : ChainId), Reach deployed P S ∧ S.l1.registered c = true ∧
    S.queue c = [] ∧ S.l1.allowed c p = false ∧ (S.hub c).peer p = true ∧
    (Msg.dereg p, false) ∈ S.done c ∧ (S.hub c).sl p = c ∧ S.l1.sl p = c ∧
    (∀ (ps : List ChainId) (S' : State), p ∈ ps →
      ¬ Step deployed P S (.deregisterInteropPairs c ps) S') ∧
    (∀ S' : State, ¬ Step deployed P S (.allowInteropPeer c p) S') ∧
    (∀ S' : State, ¬ Step deployed P S (.resubmit c p) S')

/-- **WHILE L1 RECORDS `p` ON `c` AND THE SENDER DOES NOT ALLOW `(c, p)`, `c`'S FLAG KEEPS ITS
VALUE.** For every step from any state in which L1's `settlementLayer[p]` is `c`, the sender does
not allow `(c, p)`, and no entry in `c`'s queue writes `isPeerAllowed[p]`: `c`'s
`isPeerAllowed[p]` is unchanged, the sender still does not allow `(c, p)`, and still no entry in
`c`'s queue writes it. The conclusion re-establishes every premise except L1's
`settlementLayer[p] = c`. -/
def Properties.DisallowedPeerFlagFrozenWhileOnLayer : Prop :=
  ∀ (P : Params) (S S' : State) (a : Action) (c p : ChainId), Step deployed P S a S' →
    S.l1.sl p = c → S.l1.allowed c p = false → NoPendingPeerEntry p (S.queue c) →
      (S'.hub c).peer p = (S.hub c).peer p ∧ S'.l1.allowed c p = false ∧
      NoPendingPeerEntry p (S'.queue c)

/-- **WITHOUT FIFO EXECUTION THE MIRROR BREAKS.** With the queue executed out of order, a reachable
state in which `c`'s queue is empty, every executed entry succeeded, and `c`'s `isPeerAllowed[p]`
differs from `interopPeerAllowed[c][p]`. -/
def Properties.WithoutFifoPeerFlagDesyncs : Prop :=
  ∃ (P : Params) (S : State) (c p : ChainId), Reach withoutFifo P S ∧ S.queue c = [] ∧
    (∀ e ∈ S.done c, e.2 = true) ∧ (S.hub c).peer p ≠ S.l1.allowed c p

/-- **NO FLAG FOR THE CHAIN ITSELF OR FOR L1.** On every reachable state, if the sender allows
`(c, p)` or `c`'s `isPeerAllowed[p]` is `true`, then `p ≠ c` and `p` is not L1. -/
def Properties.PeerFlagsOnlyForProperPeers : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P S → ∀ c p : ChainId,
    (S.l1.allowed c p = true ∨ (S.hub c).peer p = true) → p ≠ c ∧ p ≠ P.l1

/-! ## (b) The value of `baseTokenAssetId[p]` -/

/-- **HEADLINE (b): EVERY CHAIN'S ENTRY IS `0` OR L1'S.** On every reachable state, every chain's
`baseTokenAssetId[p]` is `0` or the L1 Bridgehub's `baseTokenAssetId[p]`. -/
def Properties.L2BaseTokenEntryIsZeroOrL1Value : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P S → ∀ c p : ChainId,
    (S.hub c).bta p = 0 ∨ (S.hub c).bta p = S.l1.bt p

/-- **L1'S ENTRY NEVER CHANGES ONCE NONZERO.** Every step from a reachable state leaves a nonzero
L1 `baseTokenAssetId[p]` unchanged. -/
def Properties.L1BaseTokenFixedOnceSet : Prop :=
  ∀ (P : Params) (S S' : State) (a : Action), Reach deployed P S → Step deployed P S a S' →
    ∀ p : ChainId, S.l1.bt p ≠ 0 → S'.l1.bt p = S.l1.bt p

/-- **(b) ALONG RUNS: `0` OR THE CREATION VALUE.** If L1's `baseTokenAssetId[p]` is nonzero on a
reachable state `S`, then on every later state every chain's entry for `p` is `0` or that value. -/
def Properties.L2BaseTokenEntryIsZeroOrCreationValue : Prop :=
  ∀ (P : Params) (S S' : State), Reach deployed P S → Steps deployed P S S' →
    ∀ c p : ChainId, S.l1.bt p ≠ 0 → (S'.hub c).bta p = 0 ∨ (S'.hub c).bta p = S.l1.bt p

/-! ## (c) Presence while `p` settles on `c` -/

/-- **HEADLINE (c): A SETTLED CHAIN'S ENTRY IS L1'S.** On every reachable state, if chain `c` is
registered and `c`'s `L2Bridgehub` records `p` as settling on `c`, then `c`'s `baseTokenAssetId[p]`
is L1's, and it is nonzero. -/
def Properties.SettledChainEntryIsL1Value : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P S → ∀ c p : ChainId,
    S.l1.registered c = true → (S.hub c).sl p = c →
      (S.hub c).bta p = S.l1.bt p ∧ S.l1.bt p ≠ 0

/-- **WHILE `p` RETURNS FROM `c`.** On every reachable state where `p`'s withdrawal from `c`
carrying `a` is in flight, `a` is L1's `baseTokenAssetId[p]`, it is nonzero, and `c`'s entry for `p`
is `a`. -/
def Properties.ReturningChainEntryIsL1Value : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P S → ∀ (p c : ChainId) (a : AssetId),
    S.mig p = .returning c a → a = S.l1.bt p ∧ a ≠ 0 ∧ (S.hub c).bta p = a

/-- **THE RETURN CARRIES L1'S VALUE.** Every start of a return of `p` from `c`, from a reachable
state, puts L1's (nonzero) `baseTokenAssetId[p]` into the withdrawal. -/
def Properties.ReturnCarriesL1BaseToken : Prop :=
  ∀ (P : Params) (S S' : State) (p c : ChainId), Reach deployed P S →
    Step deployed P S (.burnOnLayer p c) S' →
      S'.mig p = .returning c (S.l1.bt p) ∧ S.l1.bt p ≠ 0

/-- **WHILE `p`'S ARRIVAL ON `c` IS QUEUED.** On every reachable state where it is: L1 records `p`
as settling on `c`, and `c`'s queue holds the arrival, carrying L1's nonzero
`baseTokenAssetId[p]`, with no deregistration of `p` queued after it. -/
def Properties.PendingArrivalCarriesL1Value : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P S → ∀ p c : ChainId, S.mig p = .minting c →
    S.l1.sl p = c ∧ ∃ (pre post : List Msg) (a : AssetId),
      S.queue c = pre ++ .mint p a :: post ∧ a = S.l1.bt p ∧ a ≠ 0 ∧ Msg.dereg p ∉ post

/-- **THE LITERAL PRESENCE CLAIM FAILS WHILE THE ARRIVAL IS QUEUED.** A reachable state in which
L1 records `p` as settling on the registered chain `c`, `p`'s arrival on `c` is queued, and `c`'s
`baseTokenAssetId[p]` is `0`. -/
def Properties.PendingArrivalEntryMayBeZero : Prop :=
  ∃ (P : Params) (S : State) (p c : ChainId), Reach deployed P S ∧ S.l1.registered c = true ∧
    S.mig p = .minting c ∧ S.l1.sl p = c ∧ (S.hub c).bta p = 0

/-- **A SETTLED CHAIN'S ENTRY NEVER CHANGES** (`_checkPeerPair`'s NatSpec, `CRS:170-171`). For every
step from a reachable state that keeps `p` recorded as settling on the registered chain `c`, `c`'s
`baseTokenAssetId[p]` is unchanged, and a `true` `isPeerAllowed[p]` stays `true`. -/
def Properties.SettledEntryNeverChanges : Prop :=
  ∀ (P : Params) (S S' : State) (a : Action) (c p : ChainId), Reach deployed P S →
    Step deployed P S a S' → S.l1.registered c = true → (S.hub c).sl p = c → (S'.hub c).sl p = c →
      (S'.hub c).bta p = (S.hub c).bta p ∧ ((S.hub c).peer p = true → (S'.hub c).peer p = true)

/-- **… BUT ITS `isPeerAllowed` CAN TURN ON.** A step from a reachable state that keeps `p`
recorded as settling on the registered chain `c` and turns `c`'s `isPeerAllowed[p]` from `false`
to `true`. In the run behind it, the service transaction of `allowInteropPeer(c, p)` failed before
`p` migrated onto `c`, and the step executes a re-submission, which does not run
`_checkPeerPair`. -/
def Properties.SettledPeerFlagCanTurnOn : Prop :=
  ∃ (P : Params) (S S' : State) (a : Action) (c p : ChainId), Reach deployed P S ∧
    Step deployed P S a S' ∧ S.l1.registered c = true ∧ (S.hub c).sl p = c ∧ (S'.hub c).sl p = c ∧
    (S.hub c).peer p = false ∧ (S'.hub c).peer p = true

/-- **… AND THAT STEP EXECUTES A RE-SUBMISSION.** `SettledPeerFlagCanTurnOn`, with the step stated:
it is the successful execution of the head of `c`'s queue, and that queue holds exactly one entry,
a re-submission (a non-service `allowInteropPeer(p, a)`), after a failed service entry for `p` on
`c`'s log. -/
def Properties.SettledPeerFlagTurnsOnByResubmission : Prop :=
  ∃ (P : Params) (S S' : State) (c p : ChainId), Reach deployed P S ∧
    Step deployed P S (.execute c 0 true) S' ∧ S.l1.registered c = true ∧ (S.hub c).sl p = c ∧
    (S'.hub c).sl p = c ∧ (S.hub c).peer p = false ∧ (S'.hub c).peer p = true ∧
    (∃ a, S.queue c = [.allow p a false]) ∧ ∃ a, (Msg.allow p a true, false) ∈ S.done c

/-- **WITHOUT THE SETTLEMENT CLAUSE, A SETTLED CHAIN'S ENTRY IS CLEARED.** With
`deregisterInteropPairs` not checking `settlementLayer(p) == c`, a reachable state in which `c`
records `p` as settling on `c` and `c`'s `baseTokenAssetId[p]` is `0`. -/
def Properties.WithoutDeregSettlementCheckSettledEntryCleared : Prop :=
  ∃ (P : Params) (S : State) (c p : ChainId), Reach withoutDeregSettlementCheck P S ∧
    S.l1.registered c = true ∧ (S.hub c).sl p = c ∧ (S.hub c).bta p = 0

/-- **… AND L1'S ENTRY IS THEN OVERWRITTEN WITH `0`.** In the same variant, a step from a reachable
state that turns a nonzero L1 `baseTokenAssetId[p]` into `0`. -/
def Properties.WithoutDeregSettlementCheckL1BaseTokenRewritten : Prop :=
  ∃ (P : Params) (S S' : State) (a : Action) (p : ChainId),
    Reach withoutDeregSettlementCheck P S ∧ Step withoutDeregSettlementCheck P S a S' ∧
    S.l1.bt p ≠ 0 ∧ S'.l1.bt p = 0

/-- **WITHOUT FIFO EXECUTION, A SETTLED CHAIN'S ENTRY IS CLEARED.** With the queue executed out of
order, a reachable state in which `c` records `p` as settling on `c` and `c`'s
`baseTokenAssetId[p]` is `0`. In the run behind it, a deregistration queued before the arrival
executes after it. -/
def Properties.WithoutFifoSettledEntryCleared : Prop :=
  ∃ (P : Params) (S : State) (c p : ChainId), Reach withoutFifo P S ∧
    S.l1.registered c = true ∧ (S.hub c).sl p = c ∧ (S.hub c).bta p = 0

/-! ## (d) Deregistration after a return -/

/-- **ONCE `p` SETTLES ON L1, ITS PAIR WITH `c` CAN BE DEREGISTERED.** On every reachable state
where `c` and `p` are registered, `p ≠ c` and L1 records `p` as settling on L1,
`deregisterInteropPairs(c, [p])` succeeds. -/
def Properties.ReturnedPeerDeregistrationAccepted : Prop :=
  ∀ (P : Params) (S : State) (c p : ChainId), Reach deployed P S → S.l1.registered c = true →
    S.l1.registered p = true → p ≠ c → S.l1.sl p = P.l1 →
      ∃ S' : State, Step deployed P S (.deregisterInteropPairs c [p]) S'

/-- **AND IT CLEARS `c`'S ENTRY.** A reachable state in which `c` and `p ≠ c` are registered, `c`
records that `p` left it for L1 (`settlementLayer[p] = L1`, written only by the return), L1 records
`p` as settling on L1, and `c`'s `baseTokenAssetId[p]` is nonzero; `deregisterInteropPairs(c, [p])`
and the execution of its entry then leave `c`'s `baseTokenAssetId[p]` at `0` and `isPeerAllowed[p]`
`false`. -/
def Properties.ReturnedPeerEntryCanBeCleared : Prop :=
  ∃ (P : Params) (S S₁ S₂ : State) (c p : ChainId), Reach deployed P S ∧
    S.l1.registered c = true ∧ S.l1.registered p = true ∧ p ≠ c ∧
    (S.hub c).sl p = P.l1 ∧ S.l1.sl p = P.l1 ∧ (S.hub c).bta p ≠ 0 ∧
    Step deployed P S (.deregisterInteropPairs c [p]) S₁ ∧ Step deployed P S₁ (.execute c 0 true) S₂ ∧
    (S₂.hub c).bta p = 0 ∧ (S₂.hub c).peer p = false

/-! ## Non-vacuity -/

/-- **WITNESS FOR (a).** A reachable state meeting the premises of
`PeerFlagMirrorsWhenLastEntrySucceeded`: `c`'s queue is empty and its last entry for `p` succeeded,
after a failed service entry and a successful re-submission; both flags are `true`. -/
def Properties.MirrorAfterFailedServiceEntryWitness : Prop :=
  ∃ (P : Params) (S : State) (c p : ChainId), Reach deployed P S ∧ S.queue c = [] ∧
    lastPeerEntryOk p (S.done c) = true ∧
    (∃ e ∈ S.done c, e.1.isService = true ∧ (e.1.peerWrite p).isSome = true ∧ e.2 = false) ∧
    (∃ e ∈ S.done c, e.1.isService = false ∧ (e.1.peerWrite p).isSome = true ∧ e.2 = true) ∧
    S.l1.allowed c p = true ∧ (S.hub c).peer p = true

/-- **WITNESS FOR (a), FAILED RE-SUBMISSION.** A reachable state meeting the premises of
`PeerFlagMirrorsWhenServiceEntriesSucceed` but not those of
`PeerFlagMirrorsWhenLastEntrySucceeded`: the last executed entry for `p` is a failed
re-submission; both flags are `true`. -/
def Properties.MirrorAfterFailedResubmissionWitness : Prop :=
  ∃ (P : Params) (S : State) (c p : ChainId), Reach deployed P S ∧ S.queue c = [] ∧
    (∀ e ∈ S.done c, e.1.isService = true → (e.1.peerWrite p).isSome = true → e.2 = true) ∧
    lastPeerEntryOk p (S.done c) = false ∧
    S.l1.allowed c p = true ∧ (S.hub c).peer p = true

/-- **WITNESS FOR `DisallowedPeerFlagFrozenWhileOnLayer`.** A reachable state meeting its premises,
in which `c`'s queue holds exactly `p`'s arrival, `c`'s `isPeerAllowed[p]` is `true` while the
sender does not allow `(c, p)`, and `c`'s `L2Bridgehub` does not yet record `p` as settling on `c`;
executing the arrival is a step after which it does. -/
def Properties.DisallowedPeerFlagFrozenWitness : Prop :=
  ∃ (P : Params) (S S' : State) (c p : ChainId), Reach deployed P S ∧
    Step deployed P S (.execute c 0 true) S' ∧ S.l1.sl p = c ∧ S.l1.allowed c p = false ∧
    NoPendingPeerEntry p (S.queue c) ∧ S.queue c = [.mint p (S.l1.bt p)] ∧
    (S.hub c).peer p = true ∧ (S.hub c).sl p ≠ c ∧ (S'.hub c).sl p = c

/-- **WITNESS FOR (b).** A reachable state with a nonzero entry on a chain other than `p`. -/
def Properties.BaseTokenEntryWitness : Prop :=
  ∃ (P : Params) (S : State) (c p : ChainId), Reach deployed P S ∧ c ≠ p ∧
    (S.hub c).bta p ≠ 0 ∧ (S.hub c).bta p = S.l1.bt p

/-- **WITNESS FOR (b) ALONG RUNS.** Reachable `S` with L1's `baseTokenAssetId[p]` nonzero and
`c`'s entry `0`, and a later `S'`, after `p` arrives on `c` and starts back (its return is not
finalized; `L1BaseTokenRewriteWitness` finalizes it), with `c`'s entry nonzero. -/
def Properties.CreationValueWitness : Prop :=
  ∃ (P : Params) (S S' : State) (c p : ChainId), Reach deployed P S ∧ Steps deployed P S S' ∧
    S.l1.bt p ≠ 0 ∧ (S.hub c).bta p = 0 ∧ (S'.hub c).bta p ≠ 0 ∧ (S'.hub c).sl p = P.l1

/-- **WITNESS FOR `L1BaseTokenFixedOnceSet`.** A reachable state and a finalized return, the step
that writes L1's `baseTokenAssetId[p]` after creation, with that entry nonzero. -/
def Properties.L1BaseTokenRewriteWitness : Prop :=
  ∃ (P : Params) (S S' : State) (p : ChainId), Reach deployed P S ∧
    Step deployed P S (.finalizeReturn p) S' ∧ S.l1.bt p ≠ 0

/-- **WITNESS FOR (c), A RE-SUBMISSION WHILE `p` SETTLES ON `c`.** A reachable state in which `c`
records `p` as settling on `c`, `c`'s queue holds exactly a re-submitted `allowInteropPeer(p, …)`
(sent without `_checkPeerPair`), and a step executing it successfully keeps `p` settling on `c`. -/
def Properties.SettledEntryWitness : Prop :=
  ∃ (P : Params) (S S' : State) (c p : ChainId), Reach deployed P S ∧ S.l1.registered c = true ∧
    (S.hub c).sl p = c ∧ S.queue c = [.allow p (S.l1.bt p) false] ∧
    Step deployed P S (.execute c 0 true) S' ∧ (S'.hub c).sl p = c ∧ (S.hub c).peer p = true

/-- **WITNESS FOR THE RETURN.** A reachable state from which `p` starts back from `c`, and the
state after it. -/
def Properties.ReturnWitness : Prop :=
  ∃ (P : Params) (S S' : State) (p c : ChainId), Reach deployed P S ∧
    Step deployed P S (.burnOnLayer p c) S' ∧ Reach deployed P S' ∧
    ∃ a, S'.mig p = .returning c a

end Contracts.InteropPeerRegistry
