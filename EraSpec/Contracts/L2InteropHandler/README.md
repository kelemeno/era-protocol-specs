# L2InteropHandler

Source: `contracts/interop/interop-handler/L2InteropHandler.sol` in the pinned
era-contracts tree.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| AtomicSourceBinding | [Specs/AtomicSourceBinding.lean](Specs/AtomicSourceBinding.lean) | [Properties/AtomicSourceBinding.lean](Properties/AtomicSourceBinding.lean) | [Proofs/AtomicSourceBinding.lean](Proofs/AtomicSourceBinding.lean) |
| AtomicSourceBindingStrong | [Specs/AtomicSourceBindingStrong.lean](Specs/AtomicSourceBindingStrong.lean) | [Properties/AtomicSourceBindingStrong.lean](Properties/AtomicSourceBindingStrong.lean) | [Proofs/AtomicSourceBindingStrong.lean](Proofs/AtomicSourceBindingStrong.lean) |
| SourceBindingReduced | [Specs/SourceBindingReduced.lean](Specs/SourceBindingReduced.lean) | [Properties/SourceBindingReduced.lean](Properties/SourceBindingReduced.lean) | [Proofs/SourceBindingReduced.lean](Proofs/SourceBindingReduced.lean) |

`AtomicSourceBinding.atomic_source_bound` restates its premise `HonestCommits`. Two topics derive
the binding instead:
- `SourceBindingReduced` (namespace `Contracts.SourceBinding`) derives it from a run of the
  pinned source code on the vouching chain (below).
- `AtomicSourceBindingStrong` (namespace `AttackVectors.AtomicSourceBinding`) derives it from the
  honest insertion of the one tree that vouched (`TreeHoldsOwnLegs`, discharged on a deployed
  center run by `CenterRunTreeHoldsOwnLegs`). It also models the validator by call site
  (`DestContextCheckBySite`: on the atomic site, check (1) compares the field with itself) and the
  flow gate (`ExecutingBundleSenderChainIsItsLegChainOrLoggedClash`).
Each holds up to the sentinel and keccak collisions on named preimages. In
`AtomicSourceBindingStrong`, a tree with one foreign commit value breaks the binding with no
collision (`ForeignCommitInTreeUnbindsSource`).

## Source binding from the vouching chain's code (`SourceBindingReduced`)

One source chain's send side in one state: the `InteropCenter` model of topic `Dispatch`
(salt flags, the manager's leg state, a ghost dispatch log) with the commitment tree's list
state, an atomic send being `_sendBundle`'s modelled checks plus the composed `append` of
`Protocol/InteropAtomicity` `OncePerLeg`. A run projects to both
(`SourceRunProjectsToCenterReach`, `SourceRunProjectsToAppendPath`), and every key of the
tree is `0` or the commit value of one of the chain's atomic dispatches
(`SourceKeysAreDispatchedCommitValues`: links 1 and 2 of `LocalHonesty.lean`, proved for this
model). Keccak, the encoder, the decoder and the commit value are universally quantified.
No result takes a hash premise. The one trust premise is that the vouching chain `c` runs
this code from genesis (`SourceReach deployed`, `PROTO-EVIDENCE` for that chain only); no
other chain is assumed.

| Result | Statement |
|---|---|
| `AtomicSourceBoundOrBreak` (headline) | Chain `c` runs the pinned code; the destination hashes the presented bytes `x` to `h` as `_getBundleData` does; the leg's commit value `cv f h` is a key of `c`'s tree. Then `x` declares source chain `c`, which is the chain `_executeCalls` hands every recipient, or a `SourceBindingBreak` holds: the commit value is the sentinel `0`, or it clashes with a leg `c` appended, or keccak collides on the handler's preimage of `x` and the center's preimage of the dispatch that committed `(f, h)`. |
| `ExecutedBytesAreDispatchedOrBreak` | Same premises: `x` is `abi.encode` of the bundle of an atomic dispatch of `c` that committed exactly `(f, h)`, formed by `_sendBundle` and validated, or a break. |
| `ExecutedCallersAreSourceSendersOrBreak` | Adding the decoder round trip on `c`'s own dispatched bundles (`SOL-ABI`): every executed call carries no value, and its `from` is the dispatch's sender or an indirect sender contract it called through, or a break. |
| `AtomicSourceBoundOn` | Bounded form: a nonzero commit value, `CommitValueInjOn` on the presented leg and `c`'s append log, and `KeccakInjOn` on the handler's preimage and `c`'s bundle-hash preimages; then the binding holds. |
| `CommitClashIsKeccakClash`, `BreakIsKeccakEvent`, `AtomicSourceBoundOrKeccakEvent` | For the commit value `keccak(abi.encode(TAG, flowId, bundleHash))`, every break is a keccak preimage of `0` or a keccak collision on two named preimages. |
| `CommitValueOnlyInItsSourceTreeOrBreak` | Two chains running the pinned code with one keccak, encoder, center address and commit value: if a dispatch of `c` has its commit value in `c'`'s tree, then `c' = c` or a break holds against `c'`'s run. |
| `GateBindsExecutingSourceOrBreak` | Gate form: a leg executes through `ExecutedViaBy` on a fixed history, and the tree of the batch its proof cites equals a state of a run of the pinned code on the leg's chain (a premise, the operational link). Then the bundle declares the leg's chain, or that proof carries an `InclusionBreak`, or a `SourceBindingBreak` holds. |

Witnesses: `SourceBindingWitness` (an honest run of chain `324` with the `keccak(abi.encode(TAG,
…))` commit-value shape meets every premise, including the bounded and round-trip ones, with
every break and keccak event false), `SentinelBreakFires`, `CommitClashBreakFires` and
`BundleClashBreakFires` (each break kind holding alone with a different declared source),
`CommitValueOnlyInItsSourceTreeWitness` (the firing case only: two chains, one commit value,
the break is a commit-value clash), and `GateSourceBindingWitness` (both breaks false, under
the constant commit value `1`, not the keccak shape). Countermodel:
`WithoutOnlyInteropCenterSourceUnbound` (without `onlyInteropCenter`, chain `324`'s tree
vouches for bytes declaring chain `325` with no break), so the trust premise is load-bearing.

Boundaries (`MODEL-SOURCE-BINDING`): only the executing bundle's own leg is bound, not the
other legs' chains; the `initL2` step cannot fire after genesis; the encoder, decoder and
keccak are abstract.

Bundle replay and self-call permission properties are under `../InteropHandlerBase/`.
The insertion authorization chain crosses contracts and is modeled in
`../../Protocol/LocalHonesty.lean`. In the model, up to the breaks above, the executed bytes
are the bytes the vouching chain dispatched (`ExecutedBytesAreDispatchedOrBreak`). A compiled
proof that successful `executeAtomicBundle` passed every flow gate and executed the committed
bytes remains a separate obligation.
