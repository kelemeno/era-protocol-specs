import EraSpec.Contracts.ChainBatchRootTree.Specs.GenesisSeed
import EraSpec.Contracts.MessageRoot.Specs.Model

/-!
# Refinement: the canonical `MessageRoot` model and the genesis-seed slice

**This file is definitions only.**  Statements are in
`EraSpec.Contracts.ChainBatchRootTree.Properties.MessageRootLink`, proofs in
`EraSpec.Contracts.ChainBatchRootTree.Proofs.MessageRootLink`.

`Specs/GenesisSeed.lean` models one chain's slice of `MessageRootBase` storage
(`SeedChainState`: registered, `currentChainBatchNumber[c]`, `chainBatchRoots[c][·]`) with its own
transition function `seedExec`.  The canonical model of the contract is
`../../MessageRoot/Specs/Model.lean` (`Contracts.MessageRoot`, `b17415d20`).  This file names the
map from a canonical storage to chain `c`'s slice; `Properties/MessageRootLink.lean` proves that
every successful call of the canonical model moves the slice of a chain other than
`block.chainid` by one `seedExec` call or leaves it unchanged.

`SeedCallsReach` is any finite sequence of successful `seedExec` calls, each with its own answer
of `l2LogsRootHash(0)`: the slice's runs, without the diamond.
-/

namespace Contracts.ChainBatchRootTree

/-- **CHAIN `c`'S SLICE OF A CANONICAL `MessageRoot` STORAGE.** -/
def seedSlice (cfg : Contracts.MessageRoot.Config) (s : Contracts.MessageRoot.State) (c : ℕ) :
    SeedChainState where
  registered := Contracts.MessageRoot.chainRegistered cfg s c
  current := s.currentChainBatchNumber c
  roots := s.chainBatchRoots c

/-- Any finite sequence of successful message-root calls on the slice, each with its own read of
`l2LogsRootHash(0)`. -/
inductive SeedCallsReach : SeedChainState → SeedChainState → Prop
  | refl {m : SeedChainState} : SeedCallsReach m m
  | tail {m m' m'' : SeedChainState} (read0 : Option UInt256) (call : SeedCall) :
      SeedCallsReach m m' → seedExec m' read0 call = some m'' → SeedCallsReach m m''

end Contracts.ChainBatchRootTree
