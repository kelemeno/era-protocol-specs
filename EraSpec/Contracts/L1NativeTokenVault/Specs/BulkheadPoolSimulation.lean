import EraSpec.Contracts.L1NativeTokenVault.Specs.BulkheadIsolation
import EraSpec.Contracts.L1NativeTokenVault.Specs.InteropPool

/-!
# The bulkhead model's calls as calls of the `InteropPool` model

`Contracts.L1NativeTokenVault.Bulkhead` (`Specs/BulkheadIsolation.lean`) and
`Contracts.L1NativeTokenVault.InteropPool` (`Specs/InteropPool.lean`) transcribe the same functions
of `l1-contracts/contracts/bridge/ntv/L1NativeTokenVault.sol` at era-contracts `draft/v0.35.0`
`b17415d20`, with `L1MessageRoot.enableInterop` and the Bridgehub's chain registration.  They were
written separately and frame the code differently:

* ids are naturals in the bulkhead model and words (`UInt256`) in `InteropPool`; storage values
  are naturals in both, and both check every `uint256` addition;
* the bulkhead model keeps `originChainId` in its state and writes it with `registerAsset`;
  `InteropPool` takes the origin as an input of each hook call and has no `registerAsset`;
* the bulkhead hooks require a registered chain; `InteropPool`'s take any chain;
* the bulkhead `populate` keeps `bridgedOutPopulated` and `legacyBridgedOut`'s L1-origin check;
  `InteropPool`'s `populateBridgedOut` has neither (both only reject);
* the bulkhead model records `initializeUpgrade` as a flag, `InteropPool` as the initializer
  version, and `InteropPool` has a ghost counter `directToPool`.

This file states how a bulkhead state and label are read in `InteropPool`.  `CapPoolCorr s p` says
that `p` holds `s`'s storage at every word index: every mapping the two models share agrees,
`upgraded` is "version at least 2", and the origin map's values are words.  A label is read with
its numbers as words (`CapLabel.toPoolCall`), the origin input of a hook being the origin map's
value in the state the call runs in.  `CapLabel.Words` says that every number the label carries
is below `2^256`, as calldata words are.

**This file is definitions only.**  The statements are in
`EraSpec.Contracts.L1NativeTokenVault.Properties.BulkheadPoolSimulation` and the proofs in
`EraSpec.Contracts.L1NativeTokenVault.Proofs.BulkheadPoolSimulation`.
-/

namespace Contracts.L1NativeTokenVault.Bulkhead

/-- `n mod 2^256` as a word.  For `n < 2^256` it is the `uint256` whose value is `n`. -/
def capWord (n : ℕ) : UInt256 := ⟨n % UInt256.size, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))⟩

/-- The numbers a label carries: chain and asset ids, amounts, origin values. -/
def CapLabel.nums : CapLabel → List ℕ
  | .toChain c a x => [c, a, x]
  | .fromChain c a x => [c, a, x]
  | .setBackfill c a v => [c, a, v]
  | .markBackfilled c => [c]
  | .moveToPool c a => [c, a]
  | .initializeUpgrade => []
  | .enableInterop c => [c]
  | .registerChain c => [c]
  | .registerAsset a o => [a, o]
  | .populate a L => [a, L]

/-- Every number the label carries is a `uint256`. -/
def CapLabel.Words (l : CapLabel) : Prop := ∀ n ∈ l.nums, n < capWordBound

instance (l : CapLabel) : Decidable l.Words := by unfold CapLabel.Words; infer_instance

/-- **THE `InteropPool` CALL A BULKHEAD CALL IS**, in the state `s` it runs in.  The numbers become
words; a hook's origin input is `s.origin asset`.  `registerAsset` writes only the origin map, which
`InteropPool` does not have, so it is no call there (`none`). -/
def CapLabel.toPoolCall (s : CapState) : CapLabel → Option InteropPool.PoolCall
  | .toChain c a x => some (.toChain (capWord c) (capWord a) (capWord x) (capWord (s.origin a)))
  | .fromChain c a x => some (.fromChain (capWord c) (capWord a) (capWord x) (capWord (s.origin a)))
  | .setBackfill c a v => some (.setBackfill (capWord c) (capWord a) (capWord v))
  | .markBackfilled c => some (.markBackfilled (capWord c))
  | .moveToPool c a => some (.move (capWord c) (capWord a))
  | .initializeUpgrade => some .initializeUpgrade
  | .enableInterop c => some (.enableInterop (capWord c))
  | .registerChain c => some (.register (capWord c))
  | .registerAsset _ _ => none
  | .populate a L => some (.populateBridgedOut (capWord a) (capWord L))

/-- The `InteropPool` calls of a bulkhead run, each label read in the state it runs in, with
`registerAsset` dropped.  It follows the run's states as `releasedUnderKey` does. -/
def capPoolCalls (cfg : CapConfig) : CapState → List CapLabel → List InteropPool.PoolCall
  | _, [] => []
  | s, l :: ls =>
    (l.toPoolCall s).toList ++
      (match capStep cfg l s with
        | some t => capPoolCalls cfg t ls
        | none => [])

/-- The bulkhead constants are `InteropPool`'s: L1's chain id is `l1`, and the pool key is
`InteropPool.interopPoolChainId` (the same `Config.sol:37` constant). -/
def CapConfig.MatchesPool (cfg : CapConfig) (l1 : UInt256) : Prop :=
  cfg.l1 = l1.val ∧ cfg.pool = InteropPool.interopPoolChainId.val

/-- **THE CORRESPONDENCE.**  The `InteropPool` state `p` holds the bulkhead state `s`'s storage at
every word index: `bridgedOut`, the four per-key mappings, the pending, interop and registration
flags.  `p`'s initializer version is at least `2` exactly when `s` has run `initializeUpgrade`, and
`s`'s origin values are words.  `bridgedOutPopulated`, the origin map and the ghost
`directToPool` are each in one model only and are not related. -/
structure CapPoolCorr (s : CapState) (p : InteropPool.PoolSys) : Prop where
  bridgedOut : ∀ a : UInt256, p.bridgedOut a = s.bridgedOut a.val
  deposited : ∀ c a : UInt256, p.deposited c a = s.deposited c.val a.val
  withdrawn : ∀ c a : UInt256, p.withdrawn c a = s.withdrawn c.val a.val
  backfill : ∀ c a : UInt256, p.backfill c a = s.backfill c.val a.val
  inPool : ∀ c a : UInt256, p.inPool c a = s.inPool c.val a.val
  pending : ∀ c : UInt256, p.pending c = s.pending c.val
  interop : ∀ c : UInt256, p.interop c = s.interop c.val
  registered : ∀ c : UInt256, p.registered c = s.registered c.val
  upgraded : 2 ≤ p.initVersion ↔ s.upgraded = true
  origin_lt : ∀ a, s.origin a < capWordBound

end Contracts.L1NativeTokenVault.Bulkhead
