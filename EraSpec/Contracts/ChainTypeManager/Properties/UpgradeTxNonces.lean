import EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTxNonces

/-!
# Properties: the L2 upgrade transaction's nonce along one chain's history

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTxNonces` (pin `b17415d20`).
Proofs are in `EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTxNonces`. Namespace
`Contracts.ChainTypeManager.EdgeChecks`.

## What holds

* **Per step.** A crossing on the settlement layer never changes a nonzero pending hash, and a
  patch crossing (equal minors) leaves `(h, b)` and the log as they were
  (`CrossingKeepsANonzeroPendingHash`, `PatchCrossingKeepsThePendingUpgrade`). A crossing that
  writes a transaction found nothing pending, raised the minor, and wrote nonce `minor(new)`
  (`WritingCrossingRaisesTheMinor`).
* **Along runs.** From `nonceInit` (a chain before `createNewChain`), or any state satisfying
  `NonceInv`, along every run in which each migration onto an existing diamond lands at a version
  no lower than the one it left (`MintLandsNotBehind`), the log only grows by appending and its
  nonces strictly increase (`UpgradeTxNoncesStrictlyIncrease`). So two logged transactions are
  different, and equal hashes for them are a collision on two transactions the run names, with
  different nonces (`LoggedUpgradeTxHashesDistinctOrCollide`). No hash premise.

## What it needs

* `LaggingReturnRepeatsNonce`: without `MintLandsNotBehind`, a migration back onto a diamond that
  stayed at `0.29.0` while the chain crossed to `0.30.0` elsewhere lets the chain write nonce `30`
  a second time, with the same transaction, so the same hash.

## Increasing nonces do not rule out a skipped transaction

* `ExactLandingRunsKeepTheActiveVersion`: when every migration onto an existing diamond lands at
  exactly the version it left with (`MintLandsExactly`), a run without genesis and without
  crossings on the settlement layer leaves the chain's live version (`ActiveVersion`) where it
  was. So the live version moves only at a genesis or a crossing on the settlement layer, the
  steps that run `_setL2SystemContractUpgrade` (for a constructed edge with an L2 side, that
  step writes its transaction: `ConstructedEdgePassesChainChecks`).
* `ReturnAheadSkipsAnL2Upgrade`: `MintLandsNotBehind` alone does not give that. A diamond that
  crossed `0.29.0 → 0.30.0` off its settlement layer, where no transaction is written, becomes
  the live diamond through a migration that satisfies `MintLandsNotBehind`. The chain is live at
  `0.30.0`, nothing with nonce `30` was written, and the constructed edge `wEdge`
  (`0.29.0 → 0.30.0`) has an L2 side. The nonces written still increase.

Every migration step of this model reverts at `b17415d20` (`CHAIN_MIGRATIONS_ENABLED = false`,
`common/Config.sol:320`), a check the model omits.
-/

namespace Contracts.ChainTypeManager.EdgeChecks

/-! ## Per step -/

/-- **A CROSSING NEVER OVERWRITES A NONZERO PENDING HASH.** If the diamond on its settlement layer
has a nonzero `l2SystemContractsUpgradeTxHash`, every successful crossing on it carries no
transaction (`txType == 0`) and leaves `(h, b)` and the log unchanged. -/
def Properties.CrossingKeepsANonzeroPendingHash : Prop :=
  ∀ (H : L2Tx → ℕ) (s s' : NonceSys) (d newV maxPubdata : ℕ) (tx : L2Tx) (c : ChainUpgradeState),
    NonceStep H s (.cross d newV maxPubdata tx) s' → s.dia d = some ⟨c, true⟩ → c.h ≠ 0 →
      tx.txType = 0 ∧ s'.log = s.log ∧
      ∃ c', s'.dia d = some ⟨c', true⟩ ∧ c'.h = c.h ∧ c'.b = c.b ∧ c'.pv = newV

/-- **A PATCH CROSSING KEEPS THE PENDING UPGRADE.** A successful crossing on the settlement layer
to a version with the same minor component leaves `(h, b)` and the log unchanged, and carries no
transaction. -/
def Properties.PatchCrossingKeepsThePendingUpgrade : Prop :=
  ∀ (H : L2Tx → ℕ) (s s' : NonceSys) (d newV maxPubdata : ℕ) (tx : L2Tx) (c : ChainUpgradeState),
    NonceStep H s (.cross d newV maxPubdata tx) s' → s.dia d = some ⟨c, true⟩ →
    minorOf newV = minorOf c.pv →
      tx.txType = 0 ∧ s'.log = s.log ∧
      ∃ c', s'.dia d = some ⟨c', true⟩ ∧ c'.h = c.h ∧ c'.b = c.b ∧ c'.pv = newV

/-- **A CROSSING THAT WRITES FOUND NOTHING PENDING AND RAISED THE MINOR.** A successful crossing on
the settlement layer carrying a transaction (`txType != 0`) started from `h = b = 0`, moved the
minor component strictly up, logged the transaction, and the transaction's nonce is the new minor;
the diamond's pending hash is the transaction's hash. -/
def Properties.WritingCrossingRaisesTheMinor : Prop :=
  ∀ (H : L2Tx → ℕ) (s s' : NonceSys) (d newV maxPubdata : ℕ) (tx : L2Tx) (c : ChainUpgradeState),
    NonceStep H s (.cross d newV maxPubdata tx) s' → s.dia d = some ⟨c, true⟩ → tx.txType ≠ 0 →
      c.h = 0 ∧ c.b = 0 ∧ minorOf c.pv < minorOf newV ∧ tx.nonce = minorOf newV ∧
      s'.log = s.log ++ [tx] ∧ s'.dia d = some ⟨⟨newV, H tx, 0⟩, true⟩

/-! ## Along runs -/

/-- **A CHAIN BEFORE `createNewChain` SATISFIES THE INVARIANT.** -/
def Properties.NonceInitSatisfiesInvariant : Prop := NonceInv nonceInit

/-- **EVERY STEP PRESERVES THE INVARIANT**, given `MintLandsNotBehind` for that step. -/
def Properties.NonceStepPreservesInvariant : Prop :=
  ∀ (H : L2Tx → ℕ) (s s' : NonceSys) (l : NonceLabel),
    NonceInv s → MintLandsNotBehind s l → NonceStep H s l s' → NonceInv s'

/-- **THE UPGRADE NONCES A CHAIN WRITES STRICTLY INCREASE.** Along every run from a state satisfying
`NonceInv` (for example `nonceInit`) whose every step satisfies `MintLandsNotBehind`, the log of
transactions written to `l2SystemContractsUpgradeTxHash` only grows by appending, and its nonces
strictly increase. The run covers genesis, crossings on and off the settlement layer, commits,
executions, reverts, and migrations with their copies. -/
def Properties.UpgradeTxNoncesStrictlyIncrease : Prop :=
  ∀ (H : L2Tx → ℕ) (s s' : NonceSys) (ls : List NonceLabel),
    NonceInv s → NonceRunWith H MintLandsNotBehind s ls s' →
      (∃ new, s'.log = s.log ++ new) ∧ s'.log.Pairwise (fun a b => a.nonce < b.nonce)

/-- **LOGGED HASHES ARE DISTINCT UP TO A NAMED COLLISION.** Along every such run, for any two
positions `i < j` of the final log, the transactions there have nonces `n_i < n_j`, and if
`keccak256(abi.encode(·))` gives them the same hash, that is a `TxHashCollision` on those two
logged transactions. -/
def Properties.LoggedUpgradeTxHashesDistinctOrCollide : Prop :=
  ∀ (H : L2Tx → ℕ) (s s' : NonceSys) (ls : List NonceLabel),
    NonceInv s → NonceRunWith H MintLandsNotBehind s ls s' →
    ∀ (i j : ℕ) (hi : i < j) (hj : j < s'.log.length),
      (s'.log[i]'(Nat.lt_trans hi hj)).nonce < (s'.log[j]'hj).nonce ∧
      (H (s'.log[i]'(Nat.lt_trans hi hj)) = H (s'.log[j]'hj) →
        TxHashCollision H (s'.log[i]'(Nat.lt_trans hi hj)) (s'.log[j]'hj))

/-! ## What it needs -/

/-- **WITHOUT `MintLandsNotBehind`, A CHAIN CAN WRITE THE SAME NONCE TWICE.** With the hash
`nonce + 1`, the run `wLaggingRun` from `nonceInit` succeeds. Its migration back lands on the
layer-`0` diamond at `0.29.0` while the version it left with is `0.30.0`, so that step does not
satisfy `MintLandsNotBehind`. The final log is genesis's `wUpgradeTx 29 [9]` followed by
`wUpgradeTx 30 [1]` twice: the same transaction, the same nonce and the same hash written twice
for one chain. -/
def Properties.LaggingReturnRepeatsNonce : Prop :=
  ∃ s', NonceRun (fun tx => tx.nonce + 1) nonceInit wLaggingRun s' ∧
    s'.log = [wUpgradeTx 29 [9], wUpgradeTx 30 [1], wUpgradeTx 30 [1]] ∧
    ¬ s'.log.Pairwise (fun a b => a.nonce < b.nonce) ∧
    ∃ s1 s2 ls1 ls2, wLaggingRun = ls1 ++ [.mint 0] ++ ls2 ∧
      NonceRun (fun tx => tx.nonce + 1) nonceInit ls1 s1 ∧
      ¬ MintLandsNotBehind s1 (.mint 0) ∧
      NonceStep (fun tx => tx.nonce + 1) s1 (.mint 0) s2

/-! ## Increasing nonces do not rule out a skipped transaction -/

/-- **WITH EXACT LANDINGS, ONLY A CROSSING ON THE SETTLEMENT LAYER MOVES THE LIVE VERSION.** Along
every run whose steps satisfy `MintLandsExactly` and are neither a genesis nor a crossing on the
settlement layer, a version that is live at the start is live at the end. -/
def Properties.ExactLandingRunsKeepTheActiveVersion : Prop :=
  ∀ (H : L2Tx → ℕ) (s s' : NonceSys) (ls : List NonceLabel),
    NonceRunWith H MintLandsExactly s ls s' → (∀ l ∈ ls, l.KeepsVersionLabel) →
      ∀ v, ActiveVersion s v → ActiveVersion s' v

/-- **A RUN WITH INCREASING NONCES CAN SKIP AN L2 UPGRADE.** The edge `wEdge` (`0.29.0 → 0.30.0`)
is constructed with `wPlan`, which has an L2 side. With the hash `nonce + 1`, the run `wSkipRun`
from `nonceInit` satisfies `MintLandsNotBehind` at every step (so `UpgradeTxNoncesStrictlyIncrease`
applies to it), and its only genesis or crossing on the settlement layer is the genesis at
`0.29.0`. At its end the chain is live at `0.30.0` on the layer-`0` diamond, and its log holds only
the genesis transaction: no transaction with nonce `30` was written. -/
def Properties.ReturnAheadSkipsAnL2Upgrade : Prop :=
  Constructed wEnv wEdge wPlan ∧ wPlan.deployments ≠ [] ∧ wEdge.old = v29 ∧ wEdge.new = v30 ∧
    ∃ s', NonceRunWith (fun tx => tx.nonce + 1) MintLandsNotBehind nonceInit wSkipRun s' ∧
      (∀ l ∈ wSkipRun, l = .genesis 0 v29 99000 (wUpgradeTx 29 [9]) ∨ l.KeepsVersionLabel) ∧
      s'.dia 0 = some ⟨⟨v30, 0, 0⟩, true⟩ ∧ ActiveVersion s' v30 ∧
      s'.log = [wUpgradeTx 29 [9]] ∧ ∀ tx ∈ s'.log, tx.nonce ≠ minorOf v30

/-- **EXACT LANDINGS ARE MET BY A RUN THAT MIGRATES OUT AND BACK.** After genesis at `0.29.0` on
layer `0` (with the hash `nonce + 1`), the run `wExactRun` (commit, revert, commit, execute, a
migration to a fresh diamond, a migration back onto the existing layer-`0` diamond at the version
it left with, a burn and a restore) satisfies `MintLandsExactly` at every step, has no genesis and
no crossing on the settlement layer, and `0.29.0` is live before and after it. -/
def Properties.ExactLandingWitness : Prop :=
  ∃ s1 s2, NonceRun (fun tx => tx.nonce + 1) nonceInit [.genesis 0 v29 99000 (wUpgradeTx 29 [9])] s1 ∧
    NonceRunWith (fun tx => tx.nonce + 1) MintLandsExactly s1 wExactRun s2 ∧
    (∀ l ∈ wExactRun, l.KeepsVersionLabel) ∧ ActiveVersion s1 v29 ∧ ActiveVersion s2 v29 ∧
    s2.dia 0 = some ⟨⟨v29, 0, 0⟩, true⟩

/-! ## Witness -/

/-- **THE RUN PREMISE IS MET BY A RUN THAT USES EVERY STEP.** With the hash `nonce + 1`, the run
`wNonceRun` from `nonceInit` uses every kind of step, every one satisfying `MintLandsNotBehind`
(the migration back lands on a diamond at the version it left with, `0.30.1`). Its log is
`[wUpgradeTx 29 [9], wUpgradeTx 30 [1], wUpgradeTx 31 [2]]`, nonces `29 < 30 < 31`. -/
def Properties.UpgradeTxNoncesWitness : Prop :=
  ∃ s', NonceRunWith (fun tx => tx.nonce + 1) MintLandsNotBehind nonceInit wNonceRun s' ∧
    s'.log = [wUpgradeTx 29 [9], wUpgradeTx 30 [1], wUpgradeTx 31 [2]] ∧
    s'.log.map L2Tx.nonce = [29, 30, 31]

end Contracts.ChainTypeManager.EdgeChecks
