# Consolidation inventory: handler-base unit

Unit `handler-base`, branch `consol9/handler-base`, from `claude/proof-round-9` at `7cee115`.
Contract: InteropHandlerBase (`EraSpec/Contracts/InteropHandlerBase`, 10 topics, 113 properties).
Target commit: era-contracts `draft/v0.35.0` head `b17415d20`; citations checked against an
extracted `b17415d20` tree. The three handler files (`InteropHandlerBase.sol` = `IHB`,
`L2InteropHandler.sol` = `L2`, `L1InteropHandler.sol` = `L1`) are byte-identical at `d9f6789` and
`b17415d20` (checked). `c67894b9` and `e561b9cc2` are not in the local clone, so claims about them
are kept only where they already were.

Concurrent wave-2 units: interop-center (InteropCenter), atomic-flow (AtomicFlowManager). This unit
does not edit their folders.

## What changed in the handlers between the pin `c67894b9` and `b17415d20`

- Public L2→L2 interop is gone. L2 has `executeAtomicBundle` (`L2:61-78`) and the new
  `verifyAtomicBundle` (`L2:83-92`); L1 has `executeBundle` (`L1:81-98`) and `verifyBundle`
  (`L1:103-110`); `unbundleBundle` (`IHB:113-175`) is shared and unchanged apart from comments.
- `executeAtomicBundle` admits a `Verified` bundle and skips the flow gate for it (`IHB:282-287`,
  `L2:73-75`). An atomic bundle can be verified (`L2:83-92`), then unbundled. So the pin's
  "atomic sub-machine" (one edge `Unreceived → FullyExecuted`) does not describe `b17415d20`.
- `receiveMessage` (`IHB:188-213`) dispatches through per-layer hooks: on L2 the execute arm
  self-calls `executeAtomicBundle` after `_requireRescueExecutionAllowed` (`L2:109-131`,
  `IHB:261-278`), the verify arm `verifyAtomicBundle` (`L2:134-142`); on L1 `executeBundle`
  (`L1:127-149`) and `verifyBundle` (`L1:152-160`); the unbundle arm is shared (`IHB:413-433`).
- The bundle/call status edges (`Unreceived→Verified`, `Unreceived→FullyExecuted`,
  `Verified→FullyExecuted`, `Verified→Unbundled`, `Unbundled→Unbundled`; per call
  `Unprocessed→Executed`, `Unprocessed→Cancelled`, `Cancelled→Cancelled`) are the same set.

## Topics

| Topic | Commit it models (checked) | Model types | Imported by (outside the folder) | Duplicates | Decision |
|---|---|---|---|---|---|
| BundleStatusMachine | prose, no line cites; the guard list is the pin's. The edge set of `Step`/`CallStep` is the `b17415d20` edge set (above). `AtomicStep`/`AtomicReach` encode the pin premise that an atomic bundle is never `Verified`, which `verifyAtomicBundle` breaks at `b17415d20` | `Status`, `Step`, `Reach`, `CallStatus`, `CallStep`, `CallReach`, `Ledger`, `releasedSum`, `collectedSum`; pin-only `AtomicStep`, `AtomicReach` | Specs: InteropCenter/AtomicRouting, Protocol/InteropAtomicity/SystemAtV35 (vocabulary `Status`, `CallStatus`); Proofs: Protocol/DestinationCapstone | `Status`/`CallStatus` are the shared vocabulary of every handler model | **re-pin** the header to `b17415d20` (guards with lines). The atomic sub-machine (`AtomicStep`, `AtomicReach`) and its four statements (`atomic_ledger_trivial`, `atomic_reach_two_states`, `atomic_never_unbundled`, `atomic_delivery_terminal`) go to **History** |
| Reentrancy | `c67894b9`. Its `executeBundle`/`verifyBundle`/`unbundleBundle` are `b17415d20`'s L1 entry points (same guards and writes; line map in the folded `ReentrancyAtV35` header; `ExecMatchesPinAtV35` proves that a v35 frame of either layer runs as its translation, in the deployed order). Its fourth entry `executeAtomicBundle` is the pin's L2 entry (`Unreceived` only, gate always), with no own `b17415d20` counterpart | `State`, `Bundle`, `Effect`, `Entry`, `Callee`, `Frame`, `Tx`, `Variant`, `exec`, `submit`, `submitAll`, `commit` (the re-entrant engine) | Specs: L1InteropHandler/WithdrawalGate (canonical at `b17415d20`), Protocol/InteropAtomicity/ExecutionLiveness (through ReentrancyStrong). Proofs: L1InteropHandler/WithdrawalGate, ReentrancyAtV35 (its headlines are transported from the engine theorems) | ReentrancyAtV35 re-models the same code per layer | **canonical engine**, re-cited at `b17415d20`. The engine statements stay as untagged supporting lemmas: they quantify over every tree of the engine's four entries, hence over every translated v35 tree, plus the pin entry, which only adds runs. Not History: the canonical v35 layer and L1InteropHandler are proved from them |
| ReentrancyAtV35 | `b17415d20` (header cites checked; written at `d9f6789`, identical files) | `Layer`, `EntryAtV35`, `CalleeAtV35`, `FrameAtV35`, `execAtV35`, `submitAllAtV35`, translation `toPin` | none (Protocol/InteropAtomicity cites two names in prose) | per-layer re-model of the engine | **fold into Reentrancy**: its Specs/Properties/Proofs move into the Reentrancy files (names unchanged, namespace `Contracts.InteropHandlerAtV35`), so the topic is one stack: the engine and its `b17415d20` layer, linked by the refinement lemmas `ExecMatchesPinAtV35`/`SubmitAllMatchesPinAtV35`. The headlines are this layer's |
| ReentrancyStrong | `c67894b9` (two cites, both of `_executeCalls`' comment); statements are over the engine | `AlwaysReverts`, `Callee.endsInRevert`, witness trees | Protocol/InteropAtomicity/ExecutionLiveness (Specs, Proofs) | v35 forms are in the Reentrancy `b17415d20` layer (`…AtV35`) | **keep** as engine lemmas; re-cite at `b17415d20` |
| BundleStatusMachineFaithful | `c67894b9`. Two layers: (a) `AttackVectors.BundleStatusMachine.Faithful`, the labelled machine `LStep` over the pin's entry points (an inclusion-proof `executeBundle` on L2, an atomic entry admitting `Unreceived` only); `b17415d20` has a flow-gated `verifyAtomicBundle` edge `LStep` lacks. (b) `Contracts.InteropHandler.Faithful`, the gate predicates `ProvesInclusion`/`PassesFlowGate`/`TxAll` and their statements over the engine | (a) `Entry`, `Check`, `LStep`, `LReach`; (b) `ProvesInclusion`, `PassesFlowGate`, `CalleeAll`, `TxAll` | (b) is used by the v35 layer's proofs (`DeliveryNeedsTheGateAtV35`) and by ValueLedgerFaithful | — | **split**: (a) and its six statements go to **History** (namespace `AttackVectors.BundleStatusMachine.Faithful.History`); (b) stays as engine lemmas, re-cited at `b17415d20` |
| BundleStatusMachineStrong | `c67894b9`; composes the engine with InteropCenter `Dispatch` (pin) and the pin keccak layer of `BundleHashPinned` (History since smalls-enc). `VerifiedBundleNeverExecutesAtomically` and `NoProofKeepsBundleInAtomicMachine` are about the pin's atomic entry | `exec_atomicPart`, `submitAll_atomicPart`, `published_atomic_hash_clashes`, … | Protocol/InteropAtomicity/ExecutionLiveness (Specs, Proofs) | — | **History** (whole topic; namespace `Contracts.InteropHandler.History`). ExecutionLiveness gets a minimal import/name edit. The three engine statements in it (`WholeBundleWriteIgnoresCallStatus`, `CallStatusDoesNotStopWholeBundleRedelivery`, `AdmittedBundleHasOnlyUnprocessedCalls`) move with it; restating them on the v35 layer is a follow-up |
| ValueLedgerFaithful | `c67894b9` cites; the release site `_handleCallValue` in `_executeCalls` is the same at `b17415d20` (`IHB:371`; L2 `:149-154`); statements are over the engine | `val`, `NamesOnly`, the derived ledger | none (Protocol/NativeValueLegs README prose) | — | **keep** as engine lemmas, re-cited at `b17415d20` |
| SelfCallAuthority | abstract; three pin line cites | `Attr`, `attrAllows` | none | SelfCallAuthorityFaithful/Strong restate it | **re-pin** the cites to the `b17415d20` self-call sites |
| SelfCallAuthorityFaithful | pin table (`c67894b9`) and two "upgrade" tables cited at `e561b9cc2`. Every line the upgrade tables cite holds at `b17415d20` with the same content (`IHB:202-210`, `:261-278`, `:427-432`; `L2:99-142`; `L1:117-160`; checked). The pin table is, as a list, the `b17415d20` L1 table | `AddrField`, `GateAttrs`, `Gate`, `Entry`, `Table`, `Reaches`, `DelegationSound`, `Matched` | Protocol/InteropAtomicity/ExecutionLiveness (`pinnedTable`, `AtomicSelfDisjunctDeadAtPin`) | SelfCallAuthorityStrong models the same dispatch with a different `Branch` shape | **re-pin**: the upgrade tables are the `b17415d20` tables (`upgradeL2Table`→`l2TableAtV35`, `upgradeL1Table`→`l1TableAtV35`; properties `UpgradeDelegationSound`→`DelegationSoundAtV35`, `AtomicSelfDisjunctLiveAndCheckedAtUpgrade`→`AtomicSelfDisjunctLiveAndCheckedAtV35`, renamed). `pinnedTable` and its statements stay: the table equals the `b17415d20` L1 table, so they are also `b17415d20` facts |
| SelfCallAuthorityStrong | `c67894b9` cites; `deployedDispatch` (execute checked, verify unchecked, unbundle checked) is the `b17415d20` L1 dispatch (`L1:117-160`, `IHB:202-210`, `:413-433`) | `Gated`, `Branch`, `GateCall`, `Handler`, `RoundTripOn` | none | SelfCallAuthorityFaithful (`Reaches` vs `GateCall`) | **re-pin** to the `b17415d20` L1 dispatch. A refinement lemma onto SelfCallAuthorityFaithful's `Reaches` is a follow-up |

## Step 2 (one model per contract)

The contract's model is one stack:
1. `BundleStatusMachine`: the status vocabulary and the guard machine (abstract);
2. the `Reentrancy` engine `Contracts.InteropHandler`: re-entrant execution, every target, every
   depth; ReentrancyStrong, the gate predicates of BundleStatusMachineFaithful and
   ValueLedgerFaithful are statements over it;
3. `Reentrancy`'s `b17415d20` layer `Contracts.InteropHandlerAtV35` (folded in from ReentrancyAtV35),
   linked to the engine by the proved refinement `ExecMatchesPinAtV35`/`SubmitAllMatchesPinAtV35`;
4. the dispatch: SelfCallAuthorityFaithful (tables) and SelfCallAuthorityStrong (relay), both at
   `b17415d20`; they stay separate models of the same arm list (follow-up: a refinement lemma).

## Edits planned outside the unit's folder

- `EraSpec.lean` (module list).
- `Protocol/InteropAtomicity/{Specs,Properties,Proofs}/ExecutionLiveness.lean`: imports and names of
  the History moves only.
- `ASSUMPTIONS.md`: only rows naming moved statements, ids unchanged.
