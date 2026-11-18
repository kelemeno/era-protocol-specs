import EraSpec.Protocol.L1WithdrawalProvenance.Specs.Provenance

/-!
# Properties: L1 withdrawal provenance, from the L1 gate to the modelled source chains

Statements about `EraSpec.Protocol.L1WithdrawalProvenance.Specs.Provenance` (era-contracts
`draft/v0.35.0` head `b17415d20`). Proofs are in
`EraSpec.Protocol.L1WithdrawalProvenance.Proofs.Provenance`.

All results take the four joining premises of the Specs header, each on the chains the L1 run's
committed verifications name: `InclusionSoundOn`, `ChainsRunTheModelOn`, `HooksAsDocumentedOn` and
`DispatchRoundTripOn`. None takes a hash premise.

What the source chains contribute is the model `Contracts.L1MessengerKeying`, in which the center's L1
dispatch is a `withdrawal` step guarded by `WithdrawalShape` (one zero-value call from
`L2_ASSET_ROUTER_ADDR`, to L1, with L1's ETH asset id). That shape is argued from the center's source in
`L1Messenger/Specs/SenderKeying.lean` (`InteropCenter.sol:262-264`, `:552-556`, `:629-658`,
`:782-822`); it is not derived from transcribed center code. The one-call conclusions below come from
that guard.

* `ProvenBundlesAreDispatchedOrCollide`: every committed verification checked the encoding of a bundle
  that its chain's modelled center dispatched to L1 (so of `WithdrawalShape`, in particular one call, by
  the guard above), or the queried message collides with a message the center sent. Under the four
  premises, this discharges the single-call evidence premise of `L1InteropHandler` `WithdrawalGate`'s
  `SingleCallEvidenceDeliversOneCall`, up to that message collision.
* `DeliveredWithdrawalWasDispatchedOrCollision` (headline): from fresh L1 storage, every committed
  delivery is `DispatchedWithdrawal` (call `0` of a one-call bundle that the modelled center of the
  sender's chain dispatched to L1, sent by `L2_ASSET_ROUTER_ADDR`, zero value, to `L1_ASSET_ROUTER`,
  unpaused), or one of two named keccak collisions.
* `ProvenanceEndToEndWitness`: every premise holds, non-vacuously (the run's one verification names
  chain `270`, whose run dispatched one bundle), on a run that delivers one call.
* `UngatedHookDeliversUndispatchedCalls` (countermodel): with a messenger hook that records for every
  caller (and is otherwise as documented), `ChainsRunTheModelOn`, `DispatchRoundTripOn` and
  `InclusionSoundOn` hold on a run in which L1 verifies and unbundles a two-call bundle no center
  dispatched, and `HooksAsDocumentedOn` fails; neither delivery satisfies any disjunct of the headline.
  With the documented hooks, the same L1 run fails `InclusionSoundOn`.
-/

namespace Contracts.L1WithdrawalProvenance

open Contracts.L1WithdrawalGate
open Contracts.L1MessengerKeying (HookSem ChainParams L2State WithdrawalShape wGatedHooks
  wUngatedHooks)

/-- **EVERY PROVEN BUNDLE WAS DISPATCHED BY ITS CHAIN'S CENTER, OR A MESSAGE HASH COLLIDES.** For every
deployment, every L2 run of every chain, and every sequence of L1 transactions from any state, under the
four joining premises (each on the chains the run's committed verifications name): every committed
verification `v` checked the encoding of a bundle `w` that the modelled center of chain
`v.proof.chainId` dispatched to L1 (`v.bytes = abi.encode(w)`, `v.bundle = w`, and `w` has
`WithdrawalShape`, the guard of the model's `withdrawal` step), or `BUNDLE_IDENTIFIER ++ v.bytes` and
`BUNDLE_IDENTIFIER ++ abi.encode(w)` differ and have the same keccak, for a dispatched `w` of that
chain. -/
def Properties.ProvenBundlesAreDispatchedOrCollide : Prop :=
  ∀ (P : Params) (Q : ℕ → ChainParams) (H : ℕ → HookSem) (runs : ℕ → L2State) (s : State)
    (txs : List Tx),
    ChainsRunTheModelOn P.codec Q H runs (submitAll P s txs).2 →
    HooksAsDocumentedOn P.codec H (submitAll P s txs).2 →
    DispatchRoundTripOn P.codec runs (submitAll P s txs).2 →
    InclusionSoundOn P.codec (fun c => (runs c).out) (submitAll P s txs).2 →
    ∀ v ∈ verifications (submitAll P s txs).2,
      (∃ w ∈ (runs v.proof.chainId).dispatched, v.bytes = P.codec.enc w.bundle ∧
          v.bundle = w.bundle ∧ WithdrawalShape P.codec (Q v.proof.chainId) w.bundle) ∨
        MessageClash P runs v

/-- **EVERY DELIVERED CALL IS A DISPATCHED WITHDRAWAL, OR A HASH COLLIDES.** For every deployment, every
L2 run of every chain, and every sequence of L1 transactions from fresh storage, under the four joining
premises (each on the chains the run's committed verifications name): every committed delivery `d` is
`DispatchedWithdrawal` (its one-call shape comes from `WithdrawalShape`, the guard of the model's
`withdrawal` step), or the delivered bytes collide under keccak with a committed verification's bytes,
or a committed verification's queried message collides with a message the center of its chain sent. -/
def Properties.DeliveredWithdrawalWasDispatchedOrCollision : Prop :=
  ∀ (P : Params) (Q : ℕ → ChainParams) (H : ℕ → HookSem) (runs : ℕ → L2State) (txs : List Tx),
    ChainsRunTheModelOn P.codec Q H runs (submitAll P init txs).2 →
    HooksAsDocumentedOn P.codec H (submitAll P init txs).2 →
    DispatchRoundTripOn P.codec runs (submitAll P init txs).2 →
    InclusionSoundOn P.codec (fun c => (runs c).out) (submitAll P init txs).2 →
    ∀ d ∈ deliveries (submitAll P init txs).2,
      DispatchedWithdrawal P runs d ∨
        (∃ v ∈ verifications (submitAll P init txs).2, KeccakClash P.codec v.bytes d.bytes) ∨
        ∃ v ∈ verifications (submitAll P init txs).2, MessageClash P runs v

/-- **THE PREMISES HOLD ON A DELIVERING RUN.** With `wCodec`, chains `wQ`, the documented hooks
`wGatedHooks` on every chain and the L2 runs `wRuns wGatedHooks` (chain `270` withdraws `wOne`, another
account sends a message, a direct hook call naming the center records nothing, a leaf is inserted): the
L1 run `[wExecOne]` from fresh storage commits one verification, naming chain `270`, whose run
dispatched one bundle; the four joining premises hold for that run; it delivers one call, and that call
is `DispatchedWithdrawal`. -/
def Properties.ProvenanceEndToEndWitness : Prop :=
  (verifications (submitAll wParams init [wExecOne]).2).map (·.proof.chainId) = [270] ∧
    (wRuns wGatedHooks 270).dispatched.length = 1 ∧
    ChainsRunTheModelOn wCodec wQ (fun _ => wGatedHooks) (wRuns wGatedHooks)
      (submitAll wParams init [wExecOne]).2 ∧
    HooksAsDocumentedOn wCodec (fun _ => wGatedHooks) (submitAll wParams init [wExecOne]).2 ∧
    DispatchRoundTripOn wCodec (wRuns wGatedHooks) (submitAll wParams init [wExecOne]).2 ∧
    InclusionSoundOn wCodec (fun c => (wRuns wGatedHooks c).out)
      (submitAll wParams init [wExecOne]).2 ∧
    (deliveries (submitAll wParams init [wExecOne]).2).length = 1 ∧
    ∀ d ∈ deliveries (submitAll wParams init [wExecOne]).2,
      DispatchedWithdrawal wParams (wRuns wGatedHooks) d

/-- **WITHOUT THE HOOK'S CALLER GATE, L1 DELIVERS CALLS NO CENTER DISPATCHED.** With `wUngatedHooks` on
every chain (only the messenger hook's caller gate fails, `L1Messenger`
`UngatedHookForgesACenterKeyedLog`), for the L1 run that verifies `[2]` with a proof of chain `270`'s
transaction `2` and then unbundles both of its calls: `ChainsRunTheModelOn`, `DispatchRoundTripOn` and
`InclusionSoundOn` hold, and `HooksAsDocumentedOn` fails. The run delivers two calls, and no delivery
satisfies any disjunct of `DeliveredWithdrawalWasDispatchedOrCollision`. With `wGatedHooks` the same L1
run fails `InclusionSoundOn`. -/
def Properties.UngatedHookDeliversUndispatchedCalls : Prop :=
  ChainsRunTheModelOn wCodec wQ (fun _ => wUngatedHooks) (wRuns wUngatedHooks)
      (submitAll wParams init [wVerifyTx2, wUnbundleTwo]).2 ∧
    DispatchRoundTripOn wCodec (wRuns wUngatedHooks)
      (submitAll wParams init [wVerifyTx2, wUnbundleTwo]).2 ∧
    InclusionSoundOn wCodec (fun c => (wRuns wUngatedHooks c).out)
      (submitAll wParams init [wVerifyTx2, wUnbundleTwo]).2 ∧
    ¬ HooksAsDocumentedOn wCodec (fun _ => wUngatedHooks)
      (submitAll wParams init [wVerifyTx2, wUnbundleTwo]).2 ∧
    (deliveries (submitAll wParams init [wVerifyTx2, wUnbundleTwo]).2).length = 2 ∧
    (∀ d ∈ deliveries (submitAll wParams init [wVerifyTx2, wUnbundleTwo]).2,
      ¬ (DispatchedWithdrawal wParams (wRuns wUngatedHooks) d ∨
        (∃ v ∈ verifications (submitAll wParams init [wVerifyTx2, wUnbundleTwo]).2,
          KeccakClash wCodec v.bytes d.bytes) ∨
        ∃ v ∈ verifications (submitAll wParams init [wVerifyTx2, wUnbundleTwo]).2,
          MessageClash wParams (wRuns wUngatedHooks) v)) ∧
    ¬ InclusionSoundOn wCodec (fun c => (wRuns wGatedHooks c).out)
      (submitAll wParams init [wVerifyTx2, wUnbundleTwo]).2

end Contracts.L1WithdrawalProvenance
