import EraSpec.Contracts.L2InteropRootStorage.Specs.Model
import EraSpec.Contracts.L2InteropRootStorage.Specs.Storage

/-!
# Refinement: the canonical storage model and the `ok`-admitted model

**This file is definitions only.**  Statements are in
`EraSpec.Contracts.L2InteropRootStorage.Properties.Refinement`, proofs in
`EraSpec.Contracts.L2InteropRootStorage.Proofs.Refinement`.

`Specs/Storage.lean` (namespace `Contracts.InteropRootStorage`) is the canonical model of
`interop/L2InteropRootStorage.sol` at `b17415d20`: both mappings, the caller, `uint256` words.
`Specs/Model.lean` (namespace `Contracts.L2InteropRootStorage`) is the coarser view the protocol
topic `SettlementRoots` instantiates: `storedInteropRoots` alone, keys and timestamps in `ℕ`, and
an admission predicate `ok` on each import.  This file names the map between them:

* `toModel S` reads the canonical storage `S` as a model state: the entry at `(c, n)` is the
  stored pair at `(c, n)` with its timestamp as a natural number when `n < 2^256`, and `(0, 0)`
  (nothing imported) at keys the contract cannot address.  `latestInteropRootTimestamp` is
  dropped; no check of the contract reads it.
* `ofInteropRoot r` reads one calldata `InteropRoot` as the model's imported tuple.
-/

namespace Contracts.L2InteropRootStorage

/-- One calldata `InteropRoot` of the canonical model as the model's imported tuple. -/
def ofInteropRoot (r : Contracts.InteropRootStorage.InteropRoot) : RootIn where
  chainId := r.chainId
  blockOrBatchNumber := r.blockOrBatchNumber.val
  ts := r.timestamp.val
  sides := r.sides

/-- **THE CANONICAL STORAGE, READ AS A MODEL STATE.** `storedInteropRoots` with `ℕ` keys and
timestamps; keys at or above `2^256` hold `(0, 0)`. -/
def toModel (S : Contracts.InteropRootStorage.State) : State where
  entries := fun c n =>
    if h : n < UInt256.size then
      ⟨(S.storedInteropRoots c ⟨n, h⟩).root, (S.storedInteropRoots c ⟨n, h⟩).timestamp.val⟩
    else ⟨0, 0⟩

end Contracts.L2InteropRootStorage
