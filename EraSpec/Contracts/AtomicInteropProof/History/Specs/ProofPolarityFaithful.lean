import EraSpec.Contracts.AtomicInteropProof.Specs.ProofPolarityFaithful

/-!
# Spec (History): the pinned `append`, with no declared-chain binding

**History.** This is the record of the H1 finding at era-contracts `c67894b9` (the forged refund of
a misdeclared leg), not a claim about `draft/v0.35.0` `b17415d20`. At the pin
`AtomicFlowManager.append` checked only that the leg was `Unset` before inserting its commit
value; it never compared the flow's `legSourceChainIds` with `block.chainid`. At `b17415d20`
`append` reverts with `ManagerCommittedLegSourceChainMismatch` unless
`legSourceChainIds[legIndex] == block.chainid` (`atomic-interop/AtomicFlowManager.sol:140-146`):
that binding `append` is `UpgradeReach` in `../../Specs/ProofPolarityFaithful.lean`.
-/

namespace AttackVectors.ProofPolarityFaithful.History

variable {Chain Value : Type}

/-- The states honest chains reach under the PINNED `append`: chain `c` inserts a
commit value whose bundle hash it computed with its own `block.chainid`
(`srcOf v = c`), under any sender-chosen flow, so with no condition on `decl v`. -/
inductive PinnedReach (srcOf : Value → Chain) : (Chain → Set Value) → Prop
  | genesis : PinnedReach srcOf (fun _ => ∅)
  | append {tree : Chain → Set Value} (c : Chain) (v : Value) :
      PinnedReach srcOf tree → srcOf v = c → PinnedReach srcOf (appendAt tree c v)

end AttackVectors.ProofPolarityFaithful.History
