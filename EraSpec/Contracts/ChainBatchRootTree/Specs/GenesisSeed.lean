import EraSpec.Contracts.ChainBatchRootTree.Specs.Layout

/-!
# Spec: the genesis chain batch root, from `DiamondInit` to `MessageRoot.seedGenesisRoot`

Source: era-contracts `draft/v0.35.0` head `b17415d20`, `l1-contracts/contracts/` (cited without that
prefix).

    state-transition/chain-deps/DiamondInit.sol:138
        s.l2LogsRootHashes[0] = ChainBatchRootTree.genesisChainBatchRoot();
    state-transition/chain-deps/facets/Executor.sol
        :65-68    currentBatchNumber == s.totalBatchesExecuted + _executedBatchIdx + 1
        :101-103  s.l2LogsRootHashes[currentBatchNumber] = _storedBatch.l2LogsTreeRoot;
        :163-166  _appendMessageRoot: messageRoot.addChainBatchRootV32(s.chainId, n, root)
        :192-202  append every batch, then execute every batch, then totalBatchesExecuted += n
    state-transition/chain-deps/facets/Getters.sol:165-167
        l2LogsRootHash(n) = s.l2LogsRootHashes[n]
    core/bridgehub/L1Bridgehub.sol:108-139  createNewChain:
        CTM.createNewChain (the diamond, initialised by DiamondInit), _registerNewZKChain,
        messageRoot.addNewChain(_chainId, 0) (:134), messageRoot.seedGenesisRoot(_chainId) (:135)
    core/message-root/MessageRootBase.sol
        :145-150  addNewChain: onlyBridgehubOrChainAssetHandler; ChainExists if registered
        :153-157  setMigratingChainBatchNumber: onlyChainAssetHandler; require(current <= n)
        :159-161  chainRegistered(c) = (c == block.chainid || chainIndex[c] != 0)
        :164-180  addChainBatchRoot / addChainBatchRootV32: only getZKChain(c)
        :183-197  _recordChainBatchRoot: registered, root != 0, root[n] == 0, n == current + 1
        :275-293  _addNewChain: currentChainBatchNumber[c] = start
        :296-314  seedGenesisRoot: onlyBridgehub; read zkChain.l2LogsRootHash(0) != 0;
                  registered; current == 0; root[0] == 0; root[0] = read; push

Writers at `b17415d20` (by grep over `l1-contracts/contracts`): `l2LogsRootHashes` only at
`DiamondInit.sol:138` and `Executor.sol:103`; `chainBatchRoots` only at `MessageRootBase.sol:195`
and `:311`; `currentChainBatchNumber` only at `:156`, `:196`, `:282`. At main `70096e2ea` the same
code runs for ZKsync OS chains (`DiamondInit` writes the root and `seedGenesisRoot` seeds only when
`IS_ZKSYNC_OS` / `getZKsyncOS()`); at `b17415d20` every chain is a ZKsync OS chain
(`DiamondInit.sol:139`).

## Model

One chain id `c`, its slice of `MessageRootBase` storage (`SeedChainState`) and its diamond's two
fields (`SeedDiamond`). A revert is `none`.

* **Callers are not checked.** Every message-root call on `c` may come at any time, as if from an
  authorised caller. In particular `seedGenesisRoot` may run outside `createNewChain`, and
  `addChainBatchRoot` outside execution. This only adds steps, so the safety results below
  (`SeedAtMostOnce`, `NoSeedAfterRealBatch`, `GenesisRootStable`) cover the deployed callers.
* `addChainBatchRootV32`'s push into the chain and shared trees (`:199-220`) is omitted: it writes
  neither field of the slice and can only add a revert. The `++chainCount` overflow (`:279`) is
  omitted for the same reason. `chainRegistered(c)` is the field `registered`: `_addNewChain` gives
  `c` a nonzero index once the message root is initialised (`_initialize`, `:138-142`, puts
  `block.chainid` at index 0), and `c` is not the settlement layer's own chain id.
* `seedGenesisRoot` reads `IGetters(getZKChain(c)).l2LogsRootHash(0)`; with no chain contract for
  `c` the call to `address(0)` reverts (`read0 = none`).
* Diamond steps other than execution are `diamondOther`: they may change anything in
  `SeedDiamond` except `l2LogsRootHashes[0]`, which only `DiamondInit` writes (see above).
* `createNewChain` is one atomic step: `DiamondInit` on fresh diamond storage, `addNewChain(c, 0)`,
  `seedGenesisRoot(c)`. It needs no chain contract for `c` yet (`_registerNewZKChain` rejects a
  taken id). The CTM and bridgehub checks that can only reject are omitted.

**This file is definitions only.** Results: `../Properties/GenesisSeed.lean`.
-/

namespace Contracts.ChainBatchRootTree

/-- `MessageRootBase` storage for one chain `c`. -/
structure SeedChainState where
  /-- `chainRegistered(c)` (`MessageRootBase.sol:159-161`). -/
  registered : Bool
  /-- `currentChainBatchNumber[c]` (`:84`). -/
  current : ℕ
  /-- `chainBatchRoots[c][·]` (`:90`). -/
  roots : ℕ → UInt256

/-- The message-root calls on chain `c`. -/
inductive SeedCall where
  /-- `addNewChain(c, start)` (`:145-150`, `:275-293`). -/
  | addNewChain (start : ℕ)
  /-- `setMigratingChainBatchNumber(c, n)` (`:153-157`). -/
  | setMigratingChainBatchNumber (n : ℕ)
  /-- `addChainBatchRoot(c, n, r)` and `addChainBatchRootV32(c, n, r)` (`:164-180`), as far as
  `_recordChainBatchRoot` (`:183-197`). -/
  | addChainBatchRoot (n : ℕ) (r : UInt256)
  /-- `seedGenesisRoot(c)` (`:296-314`). -/
  | seedGenesisRoot

/-- **ONE MESSAGE-ROOT CALL ON `c`.** `read0` is what `IGetters(getZKChain(c)).l2LogsRootHash(0)`
returns, `none` when the bridgehub has no chain contract for `c`. -/
def seedExec (m : SeedChainState) (read0 : Option UInt256) : SeedCall → Option SeedChainState
  | .addNewChain start =>
      -- `if (chainRegistered(_chainId)) revert ChainExists()` (:146-148)
      if m.registered then none
      -- `currentChainBatchNumber[_chainId] = _startingBatchNumber` (:282)
      else some { m with registered := true, current := start }
  | .setMigratingChainBatchNumber n =>
      -- `require(currentChainBatchNumber[_chainId] <= _batchNumber)` (:155-156)
      if m.current ≤ n then some { m with current := n } else none
  | .addChainBatchRoot n r =>
      if m.registered = false then none                       -- :184-186
      else if r = 0 then none                                 -- :187
      else if m.roots n ≠ 0 then none                         -- :188-191
      else if UInt256.size ≤ m.current + 1 then none          -- :192, checked `+ 1`
      else if n ≠ m.current + 1 then none                     -- :193
      else some { m with roots := Function.update m.roots n r, current := m.current + 1 }  -- :195-196
  | .seedGenesisRoot =>
      match read0 with
      | none => none                                          -- :300-302, no chain contract
      | some g =>
          if g = 0 then none                                  -- :303
          else if m.registered = false then none              -- :304-306
          else if m.current ≠ 0 then none                     -- :308
          else if m.roots 0 ≠ 0 then none                     -- :309
          else some { m with roots := Function.update m.roots 0 g }  -- :311

/-- The chain's diamond, as far as the genesis root: `s.l2LogsRootHashes` and
`s.totalBatchesExecuted`. -/
structure SeedDiamond where
  /-- `l2LogsRootHashes` (`ZKChainStorage.sol:106`). -/
  logsRoots : ℕ → UInt256
  /-- `totalBatchesExecuted`. -/
  executed : ℕ

/-- **`DiamondInit.initialize` ON FRESH STORAGE**, as far as these two fields: `l2LogsRootHashes[0]`
is the genesis chain batch root (`DiamondInit.sol:138`), everything else zero. -/
def diamondInit (keccak : Keccak) : SeedDiamond where
  logsRoots := Function.update (fun _ => 0) 0 (genesisChainBatchRoot keccak)
  executed := 0

/-- The chain contract the bridgehub resolves for `c` (`none` before creation), and `c`'s slice of
the message root. -/
structure SeedSystem where
  diamond : Option SeedDiamond
  mr : SeedChainState

/-- Fresh storage: no chain contract for `c`, and `c` unregistered with zero storage. -/
def seedFresh : SeedSystem := ⟨none, ⟨false, 0, fun _ => 0⟩⟩

/-- The steps. -/
inductive SeedLabel where
  /-- `L1Bridgehub.createNewChain` for `c` (`L1Bridgehub.sol:108-139`). -/
  | createNewChain
  /-- One executed batch with chain batch root `r` (`Executor.sol:163-166`, `:192-202`, `:101-103`). -/
  | execute (r : UInt256)
  /-- Any message-root call on `c`, from any caller. -/
  | mrCall (call : SeedCall)
  /-- Any other diamond step, ending in `d'` (it must keep `l2LogsRootHashes[0]`). -/
  | diamondOther (d' : SeedDiamond)

/-- **ONE STEP.** `none` is a revert of the whole transaction. -/
def seedStep (keccak : Keccak) (s : SeedSystem) : SeedLabel → Option SeedSystem
  | .createNewChain =>
      match s.diamond with
      | some _ => none
      | none => do
          let mr₁ ← seedExec s.mr none (.addNewChain 0)                             -- :134
          let mr₂ ← seedExec mr₁ (some ((diamondInit keccak).logsRoots 0)) .seedGenesisRoot  -- :135
          pure ⟨some (diamondInit keccak), mr₂⟩
  | .execute r =>
      match s.diamond with
      | none => none
      | some d => do
          -- `addChainBatchRootV32(c, executed + 1, r)` from the diamond (Executor.sol:192-194)
          let mr' ← seedExec s.mr (some (d.logsRoots 0)) (.addChainBatchRoot (d.executed + 1) r)
          -- `l2LogsRootHashes[executed + 1] = r`, `totalBatchesExecuted += 1` (:103, :201-202)
          pure ⟨some ⟨Function.update d.logsRoots (d.executed + 1) r, d.executed + 1⟩, mr'⟩
  | .mrCall call => do
      let mr' ← seedExec s.mr (s.diamond.map (·.logsRoots 0)) call
      pure ⟨s.diamond, mr'⟩
  | .diamondOther d' =>
      match s.diamond with
      | none => none
      | some d => if d'.logsRoots 0 = d.logsRoots 0 then some ⟨some d', s.mr⟩ else none

/-- **A RUN**: the steps in order, each applied to the state the previous one left. `none` if any
step reverts; a successful run is one in which every step succeeded. -/
def seedRun (keccak : Keccak) : SeedSystem → List SeedLabel → Option SeedSystem
  | s, [] => some s
  | s, ℓ :: ls => (seedStep keccak s ℓ).bind (fun t => seedRun keccak t ls)

/-- The steps that run `seedGenesisRoot`: `createNewChain`, and a direct call. -/
def SeedLabel.IsSeed : SeedLabel → Prop
  | .createNewChain => True
  | .mrCall .seedGenesisRoot => True
  | _ => False

/-- The steps that record a real batch: execution, and a direct `addChainBatchRoot`. -/
def SeedLabel.IsRealBatch : SeedLabel → Prop
  | .execute _ => True
  | .mrCall (.addChainBatchRoot _ _) => True
  | _ => False

/-- How many steps of a run run `seedGenesisRoot`. -/
def seedCount : List SeedLabel → ℕ
  | [] => 0
  | .createNewChain :: ls => seedCount ls + 1
  | .mrCall .seedGenesisRoot :: ls => seedCount ls + 1
  | _ :: ls => seedCount ls

end Contracts.ChainBatchRootTree
