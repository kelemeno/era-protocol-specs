# Consolidation inventory: atomic-flow unit

Unit `atomic-flow`, branch `consol9/atomic-flow`, from `claude/proof-round-9` at `7cee115`. Contract:
AtomicFlowManager. Target commit: era-contracts `draft/v0.35.0` head `b17415d20`. Citations were
checked against an extracted `b17415d20` tree (`l1-contracts/contracts/atomic-interop/`).
`c67894b9` is not available locally, so claims about it are kept only where they already were.
The timeout-refund path (`authorizeRefund`, `claimRefund`) exists at `b17415d20` and is modelled;
the expiry-refund path of era-contracts PR 2642 is not at `b17415d20` and is not modelled.

Property counts at the branch point (104 in the folder): Model 17, ModelStrong 21, FlowCanonical 10,
FlowCanonicalAtHead 18, FlowCanonicalAtV35 29, RefundClosesAppend 17, RecoveryLimitsFaithful 27,
RecoveryLimitsStrong 8, RecoveryLimits 8, RecoveryTargets 14 (Model and ModelStrong share the
`Contracts.AtomicFlowManager` prefix with the four `Contracts.AtomicFlowManager.*` topics).

Concurrent wave-2 units: interop-center (InteropCenter) and handler-base (InteropHandlerBase). This
unit does not rename any declaration that their folders use (see "Kept in place" below).

## Topics

| Topic | Commit it models (checked) | Model types | Imported by (outside the folder) | Decision |
|---|---|---|---|---|
| Model | no header pin; the guards and writes are `c67894b9`'s and read the same at `b17415d20`: `append` `:162-166`, `authorizeRefund` loop `:238-246`, `claimRefund` `:254-260`, `_state` `:61`, `LegState` `IAtomicInterop.sol:10` | `LegState`, `rank`, `Manager`, `Step`, `Reach` | `Refinement.lean`, InteropCenter `Specs/Dispatch`, Protocol/InteropAtomicity `Refund`, `OncePerLeg` | **canonical** leg machine; **re-pin** to `b17415d20`. `FlowCanonicalAtV35.RunV35IsPinLegRun` (every transcribed v35 run is a `Reach` run) and `RefundClosesAppend.ChainRunLegsReach` are the refinement lemmas onto it |
| ModelStrong | header `c67894b9`, lines `:87-177`; the same writes and order at `b17415d20` (`:162-166`, `:241-244`, `:254-262`, comment `:258-259`) | `LegStep`, `LegRun`, `ClaimOrder`, `NestedRun` (over `Model`) | none | **re-pin**; keep (labelled runs and reentrancy over the shared machine) |
| FlowCanonical | the sort and length checks of `_checkFlowId` at `c67894b9`; the same neighbour loop and length check are `_validateAndComputeFlowId` `:370-377` at `b17415d20` | `Ascending`, `Flow`, `Valid` | none directly (the `FlowCanonicalAtHead` and `FlowCanonicalAtV35` specs build on it) | **re-pin**: order-theoretic facts about two checks that are unchanged. `Valid` is two of the four v35 checks (necessary, not sufficient: `AcceptedV35Iff`). Docstrings that call `Valid` "accepted" or pair it with `abiEncode_inj` are corrected |
| FlowCanonicalAtHead | `main` `3605e82` (`:346-365`, `:334-339`); the same text at `b17415d20` `:360-379`, `:348-353` (checked) | `FlowPreimage`, `AtomicFlow`, `validateAndComputeFlowId`, `CheckFlowId`, `PreimageAccepted`, `PreimageClash`, `PreimageHashInjOn` | Protocol/InteropAtomicity `FlowBindingAtHead` (Specs, Properties, Proofs; about 1500 lines that open the namespace) | **re-pin** to `b17415d20`; **refinement lemmas** onto `FlowCanonicalAtV35` (a field-by-field bijection of the preimage types under which `validateAndComputeFlowId`, `CheckFlowId` and `PreimageAccepted` are `validateV35`, `CheckFlowIdV35` and `AcceptedV35`). Not merged by type aliasing: the Protocol topic's proofs build on these types, and the Protocol unit comes later |
| FlowCanonicalAtV35 | `b17415d20` (every cited line of `AtomicFlowManager.sol` and `IAtomicInterop.sol` checked) | `PreimageV35`, `AtomicFlowV35`, `validateV35`, `CallV35`, `appendV35`, `authorizeRefundV35`, `claimRefundV35`, `runV35` (over `Model.Manager`) | Protocol/InteropAtomicity `SystemAtV35` (names in prose) | **canonical** entry-point model of the contract |
| RefundClosesAppend | `b17415d20` (A:, P:, R: lines spot-checked) | `ChainState`, `ChainCall`, `execCall`, `ChainRun`, `RootStore`, `Checks` (over `Model.Manager`) | Protocol/InteropAtomicity `SystemAtV35` | **keep**; current. Remove the sentence calling the other topics `c67894b9` models |
| RecoveryLimitsFaithful | mixed: the call and decoder model and the `draft/v0.35.0` loop at `b17415d20` (`:250-265`, `:292-325`); the loop over `c.to` with the `recovered == 0` revert at `c67894b9` | `SourceChain`, `probeAt`, `decodeBool`, `Conforms`, `v35Step`, `v35Loop`, `claimRefundV35`; pin: `pinnedProbe`, `recoverLoop`, `outcomes`, `claimRefundPinned` | none | **split**. Call model, decoder and v35 loop stay (re-cited). The pin loop, its statements and the pin-vs-v35 comparison go to **History** (`History/*/RecoveryLimitsFaithful.lean`, namespace `…RecoveryLimitsFaithful.History`) |
| RecoveryLimitsStrong | `c67894b9` (`claimRefund :165-180`, `_recoverBundle :219-230`), over AssetRouterBase `AtomicRecovery` (the pin loop) | `legClaimRefund`, `RetryStep` | none | **History** (whole topic) |
| RecoveryLimits | `c67894b9`: the loop over `c.to` with the `recovered == 0` revert. At `b17415d20` (`:292-325`) the loop calls only the router, discards its answer and counts nothing | `Outcome`, `LoopCompletes`, `ClaimAccepted`, a copy of `LegState` | AssetRouterBase (10 files), InteropCenter `Dispatch`, `SendAtHead` (4 files), Protocol/AssetBridgePreparation `FullRecovery` (3), DataEncoding `History/AssetIdRecovery` | **pin record, kept in place**: its names are used by InteropCenter (a concurrent unit) and AssetRouterBase. The header marks it as the `c67894b9` record; untagged; move to History once its importers move |
| RecoveryTargets | `c67894b9` (`:165-230`): `recoverAtomicCall` on each call's `to`, with the count | `Code`, `CallSem`, `VmCall`, `recoverStep`, `recoverBundle`, `claimRefund` | InteropCenter `AtomicRouting` (Specs, Properties, Proofs) | **pin record, kept in place** for the same reason (InteropCenter is concurrent). The header marks it; untagged |

## Step 2 (one model per contract)

- **Leg machine:** `Model` (`Manager`, `Step`, `Reach`) is the one state model. `ModelStrong` labels its
  runs; `FlowCanonicalAtV35.runV35` and `RefundClosesAppend.ChainRun` transcribe the entry points on
  the same `Manager` and are joined to it by `RunV35IsPinLegRun` and `ChainRunLegsReach`.
- **Flow preimage:** `FlowCanonicalAtV35` is canonical. `FlowCanonicalAtHead` gets refinement lemmas
  onto it (it stays because Protocol `FlowBindingAtHead` is built on its types). `FlowCanonical` is
  the shared neighbour-check vocabulary both import.
- **Refund loop:** `RecoveryLimitsFaithful`'s v35 loop is the current model; the pin loops
  (`RecoveryLimits`, `RecoveryTargets`, `RecoveryLimitsStrong`, the pin half of
  `RecoveryLimitsFaithful`) are records.

## Kept in place (follow-up)

`RecoveryLimits` and `RecoveryTargets` describe `c67894b9` only, but other folders (InteropCenter,
AssetRouterBase, Protocol/AssetBridgePreparation, DataEncoding History) use their names. Moving them
now would force edits in a concurrent unit's folder. Once those importers are History or re-pinned,
move both topics to `History/` (namespace segment `History`) and add their renames.

## Edits planned outside the folder

- `EraSpec.lean` (module list, for the History modules).
- `ASSUMPTIONS.md`: rows `MODEL-AFM-NESTED`, `MODEL-AFM-CALL`, `MODEL-FLOW-HEAD` and the summary rows
  for this folder, only where a statement moved or a commit claim became false; ids unchanged.

## Outcome

- **Step 1.** Model, ModelStrong, FlowCanonical, FlowCanonicalAtHead, FlowCanonicalAtV35 and
  RefundClosesAppend cite `b17415d20` only (FlowCanonicalAtHead notes once that it was first
  written at `main` `3605e82`, the same text). RecoveryLimitsStrong (8 statements) and the pin half
  of RecoveryLimitsFaithful (17 statements) are History; renames in `renames/atomic-flow.json`
  (25 entries, all `history`, checked with `ListProperties` before and after).
- **Step 2.** New refinement lemmas `FlowCanonicalAtHead.Properties.ToV35Bijective`,
  `ValidateAgreesWithV35`, `CheckFlowIdAgreesWithV35`, `AcceptedIffAcceptedV35`. No statement was
  weakened or removed.
- **Step 3.** 17 headlines, 11 witnesses, 9 countermodels (audit `FOLDER Contracts.AtomicFlowManager
  : 17 / 11 / 9 / 136`); the README lists the 17 headlines with their premises.
- **Outside the folder:** `EraSpec.lean` (two History modules), `ASSUMPTIONS.md` rows
  `MODEL-FLOW-HEAD`, `MODEL-AFM-NESTED`, `MODEL-AFM-CALL` and the two summary rows for ModelStrong /
  RecoveryLimitsStrong and RecoveryLimitsFaithful (commit claims and moved names only; ids unchanged).

## Not done

- RecoveryLimits and RecoveryTargets are `c67894b9` records kept in place (see above).
- FlowCanonicalAtHead is a second, bridged transcription, not merged into FlowCanonicalAtV35: the
  Protocol topic `FlowBindingAtHead` builds on its types. Merge it with the Protocol unit.
- Model, FlowCanonical and FlowCanonicalAtHead are untagged. Model's `Reach` results reach the
  deployed code through `RunV35IsPinLegRun`; the run-level forms over `runV35` are the headlines.
- AssetRouterBase `AtomicRecovery` and this folder's `RecoveryLimitsFaithful` still model the loop
  over different call types with no refinement between them (`MODEL-ATOMIC-RECOVERY`), now only
  for the pin loop.
