import EraSpec.Contracts.ChainBatchRootTree.Specs.MessageRootLink

/-!
# Properties: the canonical `MessageRoot` model refines the genesis-seed slice

Statements about `EraSpec.Contracts.ChainBatchRootTree.Specs.MessageRootLink`; proofs are in
`EraSpec.Contracts.ChainBatchRootTree.Proofs.MessageRootLink`.  No hash premise.

* `MessageRootCallIsSeedCall`: on storage satisfying the canonical invariant
  `Contracts.MessageRoot.Inv` (every reachable storage does, `Contracts.MessageRoot.ReachableInv`),
  a successful call of the canonical model leaves the slice of a chain `c ≠ block.chainid`
  unchanged or is one `seedExec` call on it, with `l2LogsRootHash(0)` read as the call's
  environment answers it.
* `InitializedSliceIsFresh`: right after `initialize` the slice of every chain other than
  `block.chainid` is the slice `seedFresh` starts from.
* `ReachableSliceIsSeedRun`: so the slice of every reachable storage, for a chain other than
  `block.chainid`, is reached from that fresh slice by `seedExec` calls.

So the slice-level transition `seedExec` of `GenesisSeed` covers every call of the canonical model.
-/

namespace Contracts.ChainBatchRootTree

/-- **EVERY CANONICAL CALL IS A SLICE CALL OR LEAVES THE SLICE ALONE.** -/
def Properties.MessageRootCallIsSeedCall : Prop :=
  ∀ (H : Contracts.MessageRoot.Hashes) (cfg : Contracts.MessageRoot.Config)
    (env : Contracts.MessageRoot.Env) (s t : Contracts.MessageRoot.State)
    (call : Contracts.MessageRoot.Call) (c : ℕ),
    Contracts.MessageRoot.Inv H cfg s → c ≠ cfg.selfChainId →
      Contracts.MessageRoot.exec H cfg env s call = some t →
        seedSlice cfg t c = seedSlice cfg s c
          ∨ ∃ sc, seedExec (seedSlice cfg s c) (some (env.l2LogsRootHash c 0)) sc
              = some (seedSlice cfg t c)

/-- **AFTER `initialize`, EVERY OTHER CHAIN'S SLICE IS FRESH.** -/
def Properties.InitializedSliceIsFresh : Prop :=
  ∀ (H : Contracts.MessageRoot.Hashes) (cfg : Contracts.MessageRoot.Config)
    (env : Contracts.MessageRoot.Env) (s : Contracts.MessageRoot.State) (c : ℕ),
    Contracts.MessageRoot.exec H cfg env Contracts.MessageRoot.fresh .initialize = some s →
      c ≠ cfg.selfChainId → seedSlice cfg s c = seedFresh.mr

/-- **EVERY REACHABLE SLICE IS A SLICE RUN.** For a chain other than `block.chainid`, the slice of
every storage the canonical model reaches is reached from the fresh slice by successful `seedExec`
calls. -/
def Properties.ReachableSliceIsSeedRun : Prop :=
  ∀ (H : Contracts.MessageRoot.Hashes) (cfg : Contracts.MessageRoot.Config)
    (s : Contracts.MessageRoot.State) (c : ℕ),
    Contracts.MessageRoot.Reachable H cfg s → c ≠ cfg.selfChainId →
      SeedCallsReach seedFresh.mr (seedSlice cfg s c)

end Contracts.ChainBatchRootTree
