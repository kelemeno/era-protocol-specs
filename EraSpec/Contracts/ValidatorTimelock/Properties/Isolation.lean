import EraSpec.Contracts.ValidatorTimelock.Specs.Isolation

/-!
# Properties: other chains cannot interfere with a chain

Statements about `EraSpec.Contracts.ValidatorTimelock.Specs.Isolation` (source `b17415d20`).
Proofs are in `EraSpec.Contracts.ValidatorTimelock.Proofs.Isolation`.

* **A call on another chain leaves a chain's view alone** (`OtherChainCallsKeepAgreement`): a
  successful call that addresses some chain other than `c` changes neither the shared fields
  nor `c`'s storage.
* **A call on `c` reads only `c`'s view** (`StepRespectsAgreement`): if two states agree on
  the shared fields and on `c`'s storage, a call that addresses `c` or no chain succeeds on the
  first only if it succeeds on the second, and the two results agree again.
* **Other chains cannot enable or block anything on `c`** (`OtherChainsCannotInterfere`,
  headline). Removing from a successful run every call that addresses another chain leaves a
  successful run that ends in a state agreeing with the original on `c` and the shared fields.
  And a successful run of calls that concern `c` succeeds from every state agreeing with its
  start on `c`, ending in agreeing states. So the calls of other chains' admins and
  validators, and the owner's calls on other chains, change nothing that a call on `c` reads.
* `IsolationWitness` instantiates the premises with two states that differ on another chain.
-/

namespace Contracts.ValidatorTimelock

/-- **A CALL ON ANOTHER CHAIN LEAVES A CHAIN'S VIEW ALONE.** If a successful call does not
concern chain `c` (it addresses a chain other than `c`), the states before and after it agree
on the shared fields and on `c`'s storage. -/
def Properties.OtherChainCallsKeepAgreement : Prop :=
  ∀ (k : Call) (c : Address) (s s' : State), step k s = some s' → ¬ k.concerns c →
    AgreeOn c s s'

/-- **A CALL ON `c` READS ONLY `c`'S VIEW.** If `s` and `t` agree on the shared fields and on
chain `c`'s storage, and call `k` concerns `c` (it addresses `c` or no chain), then whenever
`k` succeeds from `s` it succeeds from `t`, and the two results agree on the shared fields and
on `c`'s storage. -/
def Properties.StepRespectsAgreement : Prop :=
  ∀ (k : Call) (c : Address) (s t s' : State), k.concerns c → AgreeOn c s t →
    step k s = some s' → ∃ t', step k t = some t' ∧ AgreeOn c s' t'

/-- **HEADLINE: OTHER CHAINS CANNOT ENABLE OR BLOCK ANYTHING ON A CHAIN.** (1) If a run of
successful calls goes from `s` to `s'`, the same run with every call that does not concern `c`
removed also succeeds from `s`, and ends in a state that agrees with `s'` on the shared fields
and on `c`'s storage. (2) If a run of successful calls that all concern `c` goes from `s` to
`s'`, then from any `t` agreeing with `s` on those, the same run succeeds and ends in a state
agreeing with `s'`. -/
def Properties.OtherChainsCannotInterfere : Prop :=
  ∀ (c : Address),
    (∀ (s s' : State) (ks : List Call), Run s ks s' →
      ∃ t', Run s (ks.filter (fun k => decide (k.concerns c))) t' ∧ AgreeOn c s' t') ∧
    (∀ (s t s' : State) (ks : List Call), (∀ k ∈ ks, k.concerns c) → AgreeOn c s t →
      Run s ks s' → ∃ t', Run t ks t' ∧ AgreeOn c s' t')

/-- **THE PREMISES ARE SATISFIABLE, ON GENUINELY DIFFERENT STATES.** After the witness setup
(state `s₀`), the owner's `setChainExecutionDelay(200, 50)` (`vtOtherChainCall`, which does
not concern chain `100`) gives `s₁`, which differs from `s₀` on chain `200` and agrees with it
on chain `100`. Validator `3`'s commit on chain `100` (which concerns it) succeeds from both,
and the results agree on chain `100`. The run of the setup's calls, `vtOtherChainCall` and the
commit is successful, and without `vtOtherChainCall` it is the run of the setup and the
commit. -/
def Properties.IsolationWitness : Prop :=
  ∃ s₀ s₁ s₂ s₃ : State,
    Run init vtSetupCalls s₀ ∧ step vtOtherChainCall s₀ = some s₁ ∧
    s₁.chainDelay vtFake ≠ s₀.chainDelay vtFake ∧ ¬ vtOtherChainCall.concerns vtChain ∧
    AgreeOn vtChain s₀ s₁ ∧
    (vtCall 1000 vtValidator (.commitBatches vtChain 1 1)).concerns vtChain ∧
    step (vtCall 1000 vtValidator (.commitBatches vtChain 1 1)) s₀ = some s₂ ∧
    step (vtCall 1000 vtValidator (.commitBatches vtChain 1 1)) s₁ = some s₃ ∧
    AgreeOn vtChain s₂ s₃ ∧
    (∃ s₄, Run init (vtSetupCalls ++ [vtOtherChainCall,
      vtCall 1000 vtValidator (.commitBatches vtChain 1 1)]) s₄) ∧
    (vtSetupCalls ++ [vtOtherChainCall, vtCall 1000 vtValidator (.commitBatches vtChain 1 1)]).filter
        (fun k => decide (k.concerns vtChain)) =
      vtSetupCalls ++ [vtCall 1000 vtValidator (.commitBatches vtChain 1 1)]

end Contracts.ValidatorTimelock
