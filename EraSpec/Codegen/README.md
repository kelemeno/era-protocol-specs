# Codegen: Lean-to-Solidity for the bridged-token slice

The first experiment of [CODE_GENERATION.md](../../CODE_GENERATION.md): a
restricted contract language with an executable semantics, a Solidity emitter,
and one program — the bridged-token mint/burn/transfer slice — proved to refine
the existing [`BridgedStandardERC20` model](../Contracts/BridgedStandardERC20/README.md).

| Review | File |
|---|---|
| The language and its interpreter: what each construct *means* | [Lang.lean](Lang.lean) |
| The emitter, with its construct-to-Solidity table and refused shapes | [Emit.lean](Emit.lean) |
| The program, transcribed from the pinned source and OZ v4 | [BridgedTokenSlice/Specs/Program.lean](BridgedTokenSlice/Specs/Program.lean) |
| The representation relation `Rel` and "any successful call" `Step` | [BridgedTokenSlice/Specs/Correspondence.lean](BridgedTokenSlice/Specs/Correspondence.lean) |
| The refinement statements | [BridgedTokenSlice/Properties/Refinement.lean](BridgedTokenSlice/Properties/Refinement.lean) |
| Proofs | [BridgedTokenSlice/Proofs/Refinement.lean](BridgedTokenSlice/Proofs/Refinement.lean) |
| The emitted contract | [solidity/src/generated/BridgedTokenSlice.sol](../../solidity/src/generated/BridgedTokenSlice.sol) |
| Tests against the original | [solidity/README.md](../../solidity/README.md) |

## What is proved

For the **interpreter**, with ABI-valid arguments:

* `deploy_establishes` / `deploy_zero_vault_reverts`: a nonzero vault deploys to
  storage representing the model's empty ledger; a zero vault reverts.
* `mint_refines`, `burn_refines`, `transfer_refines`: **both directions** — the
  model rejects iff the program reverts, and on acceptance the program reaches a
  related state with exactly the logs and return value stated. A forward
  simulation alone would admit an always-reverting implementation; this does not.
* `views_exact`: the getters return the represented values and change nothing.
* `simulation`: every successful call, to any function, by any caller, is
  matched by at most one model step — an instance of
  [`Core/Simulation.lean`](../Core/Simulation.lean).
* `reachable_ledger`: in every storage reachable from a deployment, the balances
  of all `2^160` addresses sum to the supply slot and the vault is unchanged.
  Obtained from the model's proof by `safety_transfer`, not reproved.

The model's `WellFormed` is what shows the source's `unchecked` arithmetic does
not wrap: the proofs are the place where `SOL-ARITH` is discharged for this
slice, at the level of the interpreter.

## What is not proved

* **`GEN-EMIT`.** That the printed Solidity behaves as the interpreter says is
  trusted, mitigated by the one-construct-one-line emitter, `solc` as its type
  checker, and the Lean-generated vectors in `solidity/`. There is no Solidity
  semantics in this package to prove it against.
* Anything about the **original** contract's bytecode. The tests compare it on
  the covered inputs; no theorem mentions it.
* `BUILD-*` and `VM-*` for either contract.
