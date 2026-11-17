# ProxyUpgradeExecutorBase

Source: `l1-contracts/contracts/upgrades/registry/executors/ProxyUpgradeExecutorBase.sol`, the
CTM-domain executor built on it (`executors/CTMUpgradeExecutor.sol`), and the `forward` it
inherits (`governance/UpgradeExecutorBase.sol`). That code is **not** in the pinned
era-contracts tree. It lives on era-contracts branch `draft/v0.35.0`. The topic below was first
written against commit `d9f6789` and is pinned to **`b17415d20`** (2026-11-16); its Specs header
lists what changed in the modelled code between the two. **The branch moves**: every
`file:line` quoted in the specs is at `b17415d20`. Re-check the source before relying on the
results.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact
named propositions, plus auxiliary lemmas.

| Topic | Source commit | Namespace | Specification | Property statements | Checked proofs |
|---|---|---|---|---|---|
| ExecutorOwnerCallsV35 | `b17415d20` (2026-11-16) | `Contracts.ExecutorOwnerCallsV35` | [Specs/ExecutorOwnerCallsV35.lean](Specs/ExecutorOwnerCallsV35.lean) | [Properties/ExecutorOwnerCallsV35.lean](Properties/ExecutorOwnerCallsV35.lean) | [Proofs/ExecutorOwnerCallsV35.lean](Proofs/ExecutorOwnerCallsV35.lean) |

Statements are `<namespace>.Properties.*`; each certificate has the same name without the
`Properties` segment.

## ExecutorOwnerCallsV35

Which frames of the CTM executor make the CTM's owner calls, and what the executor logs for
them, now that `applyInfrastructureUpgrade` delegatecalls the engine its transition pins. A
frame is one successful invocation of an executor entry point; its trace is what that
invocation's own code did, the engine included. The CTM's commit and replacement are
`../ChainTypeManager/` `VersionRegistry`'s `CStep`, unchanged at this commit.

What to check:

- `EntryFixesOwnerCallsAndLog`: in every frame, the CTM owner calls and the executor's log are
  read off the entry. A `forward` logs one `CallForwarded` per listed call, in order; an
  infrastructure leg makes exactly its engine's CTM calls and logs the engine's own logs, then
  `CTMInfrastructureUpgradeApplied`.
- `OwnerCallOrigins`: every owner call comes from `applyCTMUpgrade`, `upgradeChain` (the
  executor's owner or that chain's admin), a `forward`, or the pinned engine of an
  infrastructure leg. `OwnerCallOriginsEachOccur` realizes all four.
- `OwnerCallsOutsideEngineLegsAreLogged`: outside legs whose engine calls the CTM, the
  executor's log names every owner call. `EngineOwnerCallsNotLoggedByExecutor` and
  `EngineLegReplacesAndMovesDeadlineWithoutForward`: a leg whose engine replaces a committed
  transition and moves a deadline succeeds, and its log names neither call
  (`docs/registry-driven-upgrades.md:473-478` describes this route).
- `EngineLegKeepsHoldersOrCollides`, with `HoldersViewUnchangedIff`: a leg keeps the
  executor's ownership, its rows, and every holder the post-check reads, unless the holders
  hash collides on the leg's own two lists. The disjunction is the post-check split by cases;
  its content is which holders the list covers. `EngineNominationRefusedOnlyByHoldersHash`:
  a hash that reads the pending owner refuses an engine's nomination of a CTM owner, one that
  reads nothing lets it through; `ForwardNominatesCtmOwner`: through `forward` it passes for
  every hash. `EngineLegNominatesCtmAdmin`: the CTM's `pendingAdmin` is not among the holders,
  as `ProxyUpgradeExecutorBase.sol:114-116` states.
- `TameFramesKeepTheVersionInvariant`: a frame with no call or act whose effect the model
  leaves arbitrary keeps `CtmInv` and never lowers `protocolVersion`, whichever route carries
  the commits and replacements. `VersionInvariantPremisesMetAndNeeded`: the witness leg meets
  the premises, and one arbitrary engine act can break `CtmInv` while keeping every holder.

Model boundaries (details in the Specs header): a CTM owner call is a call whose owner gate
passes because the executor owns the CTM, and only `FwdCall.ctm` and `EngAct.ctm` are such
calls; every other forwarded call and engine act has an arbitrary effect. The CTM runs
`ChainTypeManager.sol` at this commit: a swap of the CTM's or the ServerNotifier's code is an
arbitrary-effect call or act, and so is every later call to a swapped CTM. Which act lists a
given engine contract can produce is not modelled, nor is governance's approval of a
transition. The holders hash `H` is an arbitrary function of the list `_domainHolders` reads,
and no statement assumes anything about it. Reverts are the absence of a frame; reject-only
checks that read nothing modelled are omitted. `value`, ETH, the OpenZeppelin ownership events,
the chains, and re-entrant frames inside a frame's calls (each is its own frame) are not part of
a trace.
