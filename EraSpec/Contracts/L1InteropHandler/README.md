# L1InteropHandler

## Headline guarantees

About `interop/interop-handler/L1InteropHandler.sol` and its base `InteropHandlerBase.sol` at era-contracts
`draft/v0.35.0` head `b17415d20`, the gate in front of L1 withdrawal finalization. Bundles are bytes,
decoded and hashed by an arbitrary codec; the inclusion oracle's verdict is an input of each call;
every delivered call's target may re-enter the handler arbitrarily. No headline takes a hash premise:
a collision appears only as a disjunct naming two byte strings of the run's own log. "Every run"
means every sequence of transactions, callers, oracle verdicts and target behaviours.

| Guarantee | Premises | Lean name |
|---|---|---|
| Every delivered call was proven: a committed verification of the same bytes checked an L1 inclusion proof of `BUNDLE_IDENTIFIER ++ bytes` sent by `L2_INTEROP_CENTER_ADDR`, with the call's source chain, destination L1 and L1's ETH asset id; or its bytes collide under keccak with verified bytes | the run starts from fresh storage | `Contracts.L1WithdrawalGate.Properties.DeliveredCallIsProvenOrKeccakClash` |
| Every delivery is a zero-value call to `L1_ASSET_ROUTER` of a call with `to = L1_ASSET_ROUTER`, value `0`, version `1` and no shadow account, with sender `(sourceChainId, from)` | none (any start state) | `Properties.DeliveriesAreCheckedRouterCalls` |
| A paused handler starts no `executeBundle` or `unbundleBundle` | the pause flag is set | `Properties.PausedHandlerStartsNoDelivery` |
| Every committed pause write is by the owner of that point of the log, re-entrant calls included | none | `Properties.CommittedPauseWritesAreOwnerCalls` |
| `initialize` commits at most once, and never once the guard slot is set | none | `Properties.InitializeRunsAtMostOnce` |
| No `(bundleHash, index)` is delivered twice, across `executeBundle` and `unbundleBundle`, in one transaction or several | none | `Properties.EachCallDeliveredAtMostOnce` |
| `callStatus[h][i]` is `Executed` exactly when call `i` of bundle `h` was delivered | fresh storage | `Properties.CallStatusRecordsDeliveries` |
| If every verified bundle has one call, every delivery is call `0` of a one-call bundle, made unpaused, or its bytes collide with verified bytes | fresh storage; every committed verification has a one-call bundle (discharged in `Protocol/L1WithdrawalProvenance` from the source chain's center) | `Properties.SingleCallEvidenceDeliversOneCall` |
| The leaf the gate's inclusion query proves is not an L1 → L2 status leaf, up to a keccak collision on the two named 88-byte preimages | the two leaves are equal | `Properties.GateQueryLeafIsStatusLeafOnlyByCollision` |

Witnesses (`@[witness]`): `ProvenanceWitness`, `PauseGateWitness`, `OwnerHandoverPauseWitness`,
`InitializeOnceWitness`, `SingleCallEvidenceWitness`, `ReentrantRedeliveryRefusedWitness`.
Countermodels (`@[countermodel]`): `CollisionDisjunctIsNeeded`; `OwnerPauseMidUnbundleWitness`
(the pause check runs once, at entry: a second call of a two-call bundle can be delivered after the
first target re-entered `pause()`); `VerifyThenUnbundleDeliversEveryCall` (`executeBundle`'s
single-call rule does not bound deliveries: a proven two-call bundle is delivered call by call by
`verifyBundle` then `unbundleBundle`).

## Source and scope

Source: `contracts/interop/interop-handler/L1InteropHandler.sol` and its base
`InteropHandlerBase.sol` at `b17415d20`. The handler is new in v0.35; `L1AssetRouter` accepts
withdrawal finalization only from its configured `l1InteropHandler`
(`bridge/asset-router/AssetRouterBase.sol:218`, `L1AssetRouter.sol:258-260`), which is this proxy
by configuration: a one-shot owner setter writes it (`L1AssetRouter.sol:126-130`, `OPS-CONFIG`).

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| WithdrawalGate | [Specs/WithdrawalGate.lean](Specs/WithdrawalGate.lean) | [Properties/WithdrawalGate.lean](Properties/WithdrawalGate.lean) | [Proofs/WithdrawalGate.lean](Proofs/WithdrawalGate.lean) |
| MessageLog | [Specs/MessageLog.lean](Specs/MessageLog.lean) | [Properties/MessageLog.lean](Properties/MessageLog.lean) | [Proofs/MessageLog.lean](Proofs/MessageLog.lean) |

Namespace `Contracts.L1WithdrawalGate`. Statements are `Contracts.L1WithdrawalGate.Properties.*`; each
certificate has the same name without the `Properties` segment.

`MessageLog` is a refinement lemma, not a second model: the gate's `msgToLog` is
`MessageHashing`'s `messageLog` (`MsgToLogIsMessageLog`), so both folders describe one
`_l2MessageToLog`, and MessageHashing's leaf separation applies to the gate's query.

## The model (`WithdrawalGate`)

The handler's replay mappings (reusing the pin model `InteropHandlerBase` `Reentrancy`), the pause
flag, owner, pending owner and reentrancy-guard slot. Entry points: `executeBundle`, `verifyBundle`,
`unbundleBundle` and the administrative functions, each with its caller. Bundles are bytes, decoded
and hashed by an abstract codec; the inclusion oracle's verdict is an input of each call. Every
delivered call's target is a tree of re-entrant calls, as in the pin model. The committed log records
each passing `_verifyBundle`, each delivered call (route, bytes, index, target, value, sender, payload,
pause flag), each `BundleExecuted` and the administrative writes. The permission gates are kept;
the returned-selector check and events are omitted.

## Results

None takes a hash premise; a collision appears only as a disjunct naming two byte strings of the
run's own log.

- **Provenance (a).** From fresh storage, every delivered call is `ProvenBy` a committed verification
  of the same bytes (sender `L2_INTEROP_CENTER_ADDR`, data `BUNDLE_IDENTIFIER ++ bytes`, source chain
  the proof's, destination L1, L1's ETH asset id, sender and payload the call's), or its bytes collide
  with verified bytes (`DeliveredCallIsProvenOrKeccakClash`). The collision disjunct is the `Verified`
  shortcut and is needed (`CollisionDisjunctIsNeeded`). `VerificationsAreChecked`,
  `ProvenanceWitness`.
- **Target pin and value (b).** Every delivery went to `L1_ASSET_ROUTER` with value `0`, from a call
  with `to = L1_ASSET_ROUTER`, value `0`, version `1` and no shadow account
  (`DeliveriesAreCheckedRouterCalls`).
- **Pause, owner, initialization (c).** A paused handler starts no `executeBundle` or
  `unbundleBundle` (`PausedHandlerStartsNoDelivery`); `verifyBundle` still commits while paused
  (`PauseGateWitness`). The pause flag is the last value `pause`/`unpause` wrote
  (`OnlyPauseAndUnpauseWritePaused`). One administrative call that writes it is `pause` or `unpause` by
  the owner (`PauseWritesAreOwnerCalls`); along whole runs, every committed pause write's caller is the
  owner the committed log gives at that point, at top level or re-entrantly
  (`CommittedPauseWritesAreOwnerCalls`, `OwnerHandoverPauseWitness`).
  `initialize` commits at most once (`InitializeRunsAtMostOnce`, `InitializeOnceWitness`). Boundary:
  the pause check runs once, at entry, so in an `unbundleBundle` of a two-call bundle whose first target
  re-enters `pause()` as the owner, the second call is delivered paused
  (`OwnerPauseMidUnbundleWitness`); a call of a one-call bundle is always delivered unpaused (b).
- **Single-call rule (d).** Only `executeBundle` checks it (`L1InteropHandler.sol:85`): a proven
  two-call bundle is refused
  there and delivered call by call by `verifyBundle` then `unbundleBundle`
  (`VerifyThenUnbundleDeliversEveryCall`). If every verified bundle has one call, every delivery is call
  `0` of a one-call bundle, unpaused, or collides (`SingleCallEvidenceDeliversOneCall`,
  `SingleCallEvidenceWitness`). `Protocol/L1WithdrawalProvenance` discharges that premise under
  `InclusionSoundOn`, `ChainsRunTheModelOn`, `HooksAsDocumentedOn` and `DispatchRoundTripOn`, from the
  modelled shape of the center's L1 branch (`WithdrawalShape`, argued from source in
  `L1Messenger/Specs/SenderKeying.lean`, not transcribed), up to a named message collision.
- **At most once (e).** Every run of this model projects to a run of the pin's re-entrant model with
  the same replay mappings, deliveries and completions (`L1RunsProjectToPinRuns`), so no `(bundleHash,
  index)` is delivered twice across routes and transactions (`EachCallDeliveredAtMostOnce`), and from
  fresh storage `callStatus` records exactly the deliveries (`CallStatusRecordsDeliveries`). A target
  re-entering both routes for its own call is refused (`ReentrantRedeliveryRefusedWitness`).

What the oracle's acceptance says about the source chain, and what the source chain's center sent, is
`Protocol/L1WithdrawalProvenance` together with `L1Messenger` `SenderKeying`.
