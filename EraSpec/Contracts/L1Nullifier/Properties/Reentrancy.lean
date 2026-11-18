import EraSpec.Contracts.L1Nullifier.Specs.Reentrancy

/-!
# Properties: calls nested inside a claim

Statements about `EraSpec.Contracts.L1Nullifier.Specs.Reentrancy` (`draft/v0.35.0`, `b17415d20`).
Proofs are in `EraSpec.Contracts.L1Nullifier.Proofs.Reentrancy`.

* `NestedRunIsFlatRun`: in the source order (delete, then call), every nested execution, with any
  checks, is a run (`Reach`) of `Specs/Model.lean` between the same two states, logs included. So
  every run-level result of `Properties/Model.lean` also holds for executions in which a claim's
  callback calls the bridgehub, the router or the nullifier, to any depth. This needs no
  `nonReentrant`, which the model does not include.
* `NestedAtMostOneClearPerDeposit`: `AtMostOneClearPerDeposit` over nested executions, as one
  instance.
* `CallFirstClearsOneDepositTwice`: in the reversed order (call, then delete), with `nonReentrant`
  absent, a nested execution clears a key recorded once twice (in the proof, the second clear is a
  claim inside the first claim's callback). In the source order this cannot happen
  (`NestedAtMostOneClearPerDeposit`), and `nonReentrant` (`N:168`, `:190`) would also make such a
  nested claim revert.
* `NestedRunWitness`: a nested execution from fresh storage meeting the premises of
  `NestedAtMostOneClearPerDeposit` with one clear (in the proof, the claim's callback makes a new
  bridgehub deposit).
-/

namespace Contracts.L1Nullifier

/-- **HEADLINE: A NESTED EXECUTION IS A RUN.** In the source order, with any checks, every
`NestedRun` from `s` to `u` is a run of `Specs/Model.lean` from `s` to `u`: a claim whose callback
calls back into the modelled contracts, to any depth, is the claim's step followed by the
callback's steps. -/
def Properties.NestedRunIsFlatRun : Prop :=
  ∀ (chk : Checks) (env : Env) (cfg : Cfg) (s u : Sys),
    NestedRun .deleteFirst chk env cfg s u → Reach chk env cfg s u

/-- **A KEY RECORDED ONCE IS CLEARED AT MOST ONCE, WITH CALLBACKS.** The statement of
`AtMostOneClearPerDeposit` over nested executions of the source order with every source check. -/
def Properties.NestedAtMostOneClearPerDeposit : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s0 s : Sys) (c : ChainId) (h : Bytes32),
    s0.log = [] → NestedRun .deleteFirst Checks.source env cfg s0 s →
    s.log.countP (isNzWrite c h) + occupied s0.n c h ≤ 1 →
    s.log.countP (isZeroClear env c h) = 0 →
    s.log.countP (isClear c h) ≤ 1

/-- **IN THE REVERSED ORDER, A CALLBACK CLEARS THE SAME RECORD AGAIN.** With every source check but
the call placed before the delete, and with `nonReentrant` absent, a nested execution from fresh
storage records a key with a nonzero value at most once, has no zero-hash clear of it, and clears
it twice (in the proof, the second time from inside the first claim's callback). -/
def Properties.CallFirstClearsOneDepositTwice : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys) (c : ChainId) (h : Bytes32),
    s0.log = [] ∧ (∀ c' h', s0.n.depositHappened c' h' = 0) ∧
    NestedRun .callFirst Checks.source env cfg s0 s ∧
    s.log.countP (isNzWrite c h) + occupied s0.n c h ≤ 1 ∧
    s.log.countP (isZeroClear env c h) = 0 ∧ s.log.countP (isClear c h) = 2

/-- **A NESTED EXECUTION WITH A CALLBACK.** From fresh storage, with every source check, a nested
execution in the source order whose log is a deposit, a clear of it, and a second deposit at
another key (in the proof, made inside that claim's callback). At the first key the premises of
`NestedAtMostOneClearPerDeposit` hold with one clear. -/
def Properties.NestedRunWitness : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys) (cl : Claim) (t : Triple) (h' : Bytes32),
    s0.log = [] ∧ (∀ c' h'', s0.n.depositHappened c' h'' = 0) ∧
    NestedRun .deleteFirst Checks.source env cfg s0 s ∧
    s.log = [.write (.deposit cl.triple) cl.chainId cl.l2TxHash (env.txDataHash cl.triple),
      .clear cl cfg.router, .write (.deposit t) cl.chainId h' (env.txDataHash t)] ∧
    h' ≠ cl.l2TxHash ∧ env.txDataHash cl.triple ≠ 0 ∧ env.txDataHash t ≠ 0 ∧
    s.log.countP (isNzWrite cl.chainId cl.l2TxHash) + occupied s0.n cl.chainId cl.l2TxHash ≤ 1 ∧
    s.log.countP (isZeroClear env cl.chainId cl.l2TxHash) = 0 ∧
    s.log.countP (isClear cl.chainId cl.l2TxHash) = 1

end Contracts.L1Nullifier
