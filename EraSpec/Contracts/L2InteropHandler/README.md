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
| AtomicSourceBindingFaithful | [Specs/AtomicSourceBindingFaithful.lean](Specs/AtomicSourceBindingFaithful.lean) | [Properties/AtomicSourceBindingFaithful.lean](Properties/AtomicSourceBindingFaithful.lean) | [Proofs/AtomicSourceBindingFaithful.lean](Proofs/AtomicSourceBindingFaithful.lean) |

`AtomicSourceBinding.atomic_source_bound` restates its premise `HonestCommits`. Two topics derive
the binding instead:
- `SourceBindingReduced` (namespace `Contracts.SourceBinding`) derives it from the vouching
  chain's whole deployed source run.
- `AtomicSourceBindingStrong` (namespace `AttackVectors.AtomicSourceBinding`) derives it from the
  honest insertion of the one tree that vouched (`TreeHoldsOwnLegs`, discharged on a deployed
  center run by `CenterRunTreeHoldsOwnLegs`). It also models the validator by call site
  (`DestContextCheckBySite`: on the atomic site, check (1) compares the field with itself) and the
  flow gate (`ExecutingBundleSenderChainIsItsLegChainOrLoggedClash`).
Each holds up to the sentinel and keccak collisions on named preimages. In
`AtomicSourceBindingStrong`, a tree with one foreign commit value breaks the binding with no
collision (`ForeignCommitInTreeUnbindsSource`).

`AtomicSourceBindingFaithful` (namespace `Contracts.L2InteropHandler.AtomicSourceFaithful`, pin
`c67894b9`) states the binding over the entry point itself: every check of `executeAtomicBundle`,
every revert of `requireFlowFinalized`, and the calls `_executeCalls` makes (`ExecutesAtomic`). With
no premise, a successful execution locates its one vouching leg and delivers every call with the
bundle's own `sourceChainId` (`AtomicExecutionLocatesVouchingLeg`, `VouchingLegUnique`,
`DeliveriesCarryDeclaredSource`). If the leg's declared chain vouches honestly (`HonestVouching`),
every call is delivered with that chain, or the leg's commit value is the tree sentinel `0`, or
keccak collides on a named preimage pair (`AtomicSenderIsVouchingChainOrBreak`). Honest vouching is
derived from the vouching chain's deployed run in `SourceBindingReduced`'s model, with the
verifier's soundness for that run's tree as the remaining premise (`DeployedRunVouchesHonestly`).
On such a run, with the ABI decoder inverting the encoder, the executed bundle is a dispatched one
and every recipient sees a sender on the vouching chain that took part in the send and receives no
base-token value, up to the same breaks (`AtomicExecutionRunsTheDispatchedBundleOrBreak`). Without
honest vouching any chain impersonates any other, for every keccak
(`MisbehavingLegChainImpersonates`); each break disjunct can hold alone (`SentinelCommitFires`,
`CommitPreimageClashFires`, `BundlePreimageClashFires`).

Bundle replay and self-call permission properties are under `../InteropHandlerBase/`.
The insertion authorization chain crosses contracts and is modeled in
`../../Protocol/LocalHonesty.lean`. A compiled proof that successful
`executeAtomicBundle` passed every flow gate and executed the committed bytes
remains a separate obligation.
