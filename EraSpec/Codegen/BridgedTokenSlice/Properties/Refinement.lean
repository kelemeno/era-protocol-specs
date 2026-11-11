import EraSpec.Codegen.BridgedTokenSlice.Specs.Correspondence
import EraSpec.Core.Simulation

-- Preconditions are retained as statement parameters for the full-proof audit.
set_option linter.unusedVariables false

/-!
# The generated program refines the token model

Statements connecting `Codegen.BridgedTokenSlice.program` — the program that is
printed to Solidity — to `Contracts.BridgedStandardERC20`, the model whose
ledger properties are already proved.  Proofs: `../Proofs/Refinement.lean`.

## What the relation says

`Rel st s` is the whole claim about representation, and is the thing to review:
the vault slot holds the model's vault and it is nonzero; the supply slot's
value is the model's supply; and every *address-range* key of the balances
mapping holds that address's model balance.  Keys at or above `2^160` are
unconstrained — no ABI-valid call can name them.

## The two directions

A forward simulation alone would be satisfied by a contract that always
reverts (`ASSUMPTIONS.md`, "Composing proved boundaries").  The per-entry-point
results therefore state **both** directions: the model rejecting implies the
program reverts, and the model accepting implies the program succeeds, reaching
a related state, with the exact logs and return value.  The `Simulation` instance
and the transferred ledger invariant are corollaries.

## Scope

The interpreter is the semantics here; the Solidity printed from the same
program is related to it only by the `GEN-EMIT` boundary and by the tests in
`solidity/`.  Nothing here concerns the original `BridgedStandardERC20` bytecode.
-/

namespace Codegen.BridgedTokenSlice

open Codegen
open Contracts.BridgedStandardERC20 (Address State WellFormed Config empty)

/-! ## Deployment -/

/-- **DEPLOYMENT ESTABLISHES THE RELATION.**  A nonzero vault deploys to storage
representing the model's empty ledger for that vault — whatever origin token and
asset id the model's configuration carries, since the slice stores neither. -/
abbrev Properties.deploy_establishes (deployer : Address) (config : Config)
    (hv : config.vault ≠ 0) :=
  ∃ r, deploy program (addrWord deployer) [addrWord config.vault] = some (.ok r) ∧
    Rel r.st (empty config) ∧ r.logs = []

/-- A zero vault is refused with `ZeroAddress()`. -/
abbrev Properties.deploy_zero_vault_reverts (deployer : Address) :=
  deploy program (addrWord deployer) [addrWord 0] = some (.error (.custom "ZeroAddress" []))

/-! ## Entry points: exact agreement with the model -/

/-- **`bridgeMint` IS THE MODEL'S `mint`.** -/
abbrev Properties.mint_refines {st : Storage} {s : State} (hw : WellFormed s) (hr : Rel st s)
    (caller recipient : Address) (amount : Word) :=
  (Contracts.BridgedStandardERC20.mint s caller recipient amount = none →
      ∃ e, call program "bridgeMint" (addrWord caller) [addrWord recipient, amount] st = some (.error e)) ∧
  (∀ t, Contracts.BridgedStandardERC20.mint s caller recipient amount = some t →
      ∃ r, call program "bridgeMint" (addrWord caller) [addrWord recipient, amount] st = some (.ok r) ∧
        Rel r.st t ∧ r.logs = mintLogs recipient amount ∧ r.ret = none)

/-- **`bridgeBurn` IS THE MODEL'S `burn`.** -/
abbrev Properties.burn_refines {st : Storage} {s : State} (hw : WellFormed s) (hr : Rel st s)
    (caller account : Address) (amount : Word) :=
  (Contracts.BridgedStandardERC20.burn s caller account amount = none →
      ∃ e, call program "bridgeBurn" (addrWord caller) [addrWord account, amount] st = some (.error e)) ∧
  (∀ t, Contracts.BridgedStandardERC20.burn s caller account amount = some t →
      ∃ r, call program "bridgeBurn" (addrWord caller) [addrWord account, amount] st = some (.ok r) ∧
        Rel r.st t ∧ r.logs = burnLogs account amount ∧ r.ret = none)

/-- **`transfer` IS THE MODEL'S `transfer`**, with `owner = msg.sender`, returning `true`. -/
abbrev Properties.transfer_refines {st : Storage} {s : State} (hw : WellFormed s) (hr : Rel st s)
    (owner recipient : Address) (amount : Word) :=
  (Contracts.BridgedStandardERC20.transfer s owner recipient amount = none →
      ∃ e, call program "transfer" (addrWord owner) [addrWord recipient, amount] st = some (.error e)) ∧
  (∀ t, Contracts.BridgedStandardERC20.transfer s owner recipient amount = some t →
      ∃ r, call program "transfer" (addrWord owner) [addrWord recipient, amount] st = some (.ok r) ∧
        Rel r.st t ∧ r.logs = transferLogs owner recipient amount ∧ r.ret = some 1)

/-- The getters read the represented values and change nothing. -/
abbrev Properties.views_exact {st : Storage} {s : State} (hr : Rel st s) (caller a : Address) :=
  (∃ r, call program "balanceOf" (addrWord caller) [addrWord a] st = some (.ok r) ∧
      r.st = st ∧ r.logs = [] ∧ (r.ret.map Fin.val) = some (s.balances a)) ∧
  (∃ r, call program "totalSupply" (addrWord caller) [] st = some (.ok r) ∧
      r.st = st ∧ r.logs = [] ∧ (r.ret.map Fin.val) = some s.totalSupply) ∧
  (∃ r, call program "nativeTokenVault" (addrWord caller) [] st = some (.ok r) ∧
      r.st = st ∧ r.logs = [] ∧ r.ret = some (addrWord s.config.vault))

/-! ## Every call, and what follows -/

/-- **A FORWARD SIMULATION**, with the relation `Rel ∧ WellFormed`.  Every successful call,
mutating or not, to any function, with any ABI-valid arguments, is matched by a run of zero or
more model steps.  `LayeredVerification.Simulation` does not bound the length of a match, so
this statement does not either.  That every match is a stutter or a single model step is
`Properties.step_matched_by_at_most_one`.  The same bundled with a simulation is
`Properties.simulation_at_most_one` (`Properties/RefinementStrong.lean`). -/
abbrev Properties.simulation :=
  ∃ sim : LayeredVerification.Simulation Step Contracts.BridgedStandardERC20.Step,
    ∀ st s, sim.Rel st s ↔ Rel st s ∧ WellFormed s

/-- **THE MODEL'S LEDGER INVARIANT HOLDS OF THE DEPLOYED PROGRAM.**  In every
storage reachable from a deployment by any sequence of successful calls, the
balances of all `2^160` addresses sum to the supply slot, and the vault is the
one deployed with.  Obtained by `safety_transfer`, not reproved. -/
abbrev Properties.reachable_ledger (deployer vault : Address) (hv : vault ≠ 0) :=
  ∃ r, deploy program (addrWord deployer) [addrWord vault] = some (.ok r) ∧
    ∀ st, LayeredVerification.Run Step r.st st →
      (∑ a : Address, (st.maps "_balances" (addrWord a)).val) = (st.scalars "_totalSupply").val ∧
      st.scalars "_nativeTokenVault" = addrWord vault

end Codegen.BridgedTokenSlice
