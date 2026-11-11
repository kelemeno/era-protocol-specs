# Lean-to-Solidity generation and shared tests

Proposal from the manual review: write/prove executable contract behavior in Lean,
emit Solidity, and run the existing and generated Solidity implementations through
the same tests. This is a possible implementation path, not an existing compiler
or a completed verification result in this repository.

## What the route would establish

For newly generated contract code, a semantics-preserving generator could replace
repeated handwritten-source-to-model proofs for its supported constructs. A
generator implemented in Lean is still a program that needs a correctness proof
or per-output translation validation. Proofs of its input model do not
automatically become proofs of its emitted Solidity.

For the existing contracts, generated Solidity would supply a second
implementation for comparison. It would not retroactively establish that the
reviewed/deployed contract implements the Lean model. We need equivalence or
refinement evidence for that existing implementation as well.

There are two distinct obligations:

```text
existing Solidity -- correspondence proof --> contract model -- property proof

contract program in Lean -- generator preservation --> generated Solidity
```

Both concrete implementations still depend on the selected compiler/build and VM
profile. A deployment claim additionally identifies the actual code and
configuration. See the layers in [ASSUMPTIONS.md](ASSUMPTIONS.md).

## A restricted contract language inside Lean

The current behavioral specifications are not a storage/call intermediate
language. Token balances are functions `Address → Nat`; their sum over the finite
address space is a ghost invariant. Vault dependencies are arbitrary functions,
metadata is opaque bytes, and `Option` abstracts failure. These are useful proof
representations, but they do not specify an EVM storage layout, ABI dispatcher,
gas behavior, or external call implementation.

A practical prototype would define a small typed contract language inside Lean,
with an interpreter/transition semantics, and emit Solidity from that language.
Start with the nonlegacy token burn/mint slice. Represent fixed-width values,
storage reads/writes, caller identity, guards, checked/unchecked arithmetic, and
reverts explicitly. Extend ABI, calls, callbacks, deployment, and proxies only as
their semantics and preservation obligations are supplied. Relate the concrete
mapping representation to the mathematical ledger instead of executing its
whole-address-space sum.

The executable program and its proofs have different roles: emit program
operations and required runtime guards; keep proof terms and ghost invariants
as verification evidence. Lean's native executable compilation currently targets
C/native code; adding Solidity emission is a separate backend. See
[Lean's compilation pipeline](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/).

Solidity is a useful first output for human review and shared tests. Yul is a
possible later target because solc supports it as an intermediate/standalone
language; choosing it would require a corresponding semantics and target-profile
review. It does not supply compiler correctness for free. See
[Solidity's Yul documentation](https://docs.soliditylang.org/en/v0.8.28/yul.html).

## One suite, two implementations

Use the same interface-level assertions and transaction sequences for both
implementations. Parameterize deployment/fixture construction so each existing
test can run against either implementation without copying its assertions.
Every test in the declared comparison scope must run against both; unsupported
behavior is a scope gap, not a passing comparison. Report excluded existing tests
by name and reason, including legacy/proxy/permit behavior outside the initial
generated slice. Do not claim full-contract equivalence from a partial suite.

Add a differential runner that starts from related initialized fixtures, executes
each generated action on both, and compares observations after every action.
An adapter may normalize deployment addresses or proxy wrappers, but must not
erase differences in authority, value, amounts, or recipients. If CREATE2/address
behavior is part of the claim, compare that behavior under the exact target
profile rather than normalizing it away.

| Observation | Compare |
|---|---|
| Outcome | Success versus revert, and specified error data where compatibility requires it. |
| Token state | Balances of touched accounts, total supply, vault/origin/asset identity, and initializer state. Use ghost tracking for aggregate invariants. |
| Calls and returns | Return values/bytes, selected call targets, sender/value/calldata, dependency interactions, and callback order within the declared scope. |
| Events | Emitting contract, event signature, topics/data, and ordering for covered events. |
| Failed execution | Persistent state of the caller and all modeled dependencies, including late failures after accounting or burn. |
| Storage compatibility | Separate slot/layout checks when upgrade/proxy compatibility is required; identical logical behavior does not imply identical layout. |

Use examples, boundary inputs, fuzzed calls, and stateful sequences. The first
token cases should include authorization, zero addresses, zero amounts,
insufficient balance, supply limits, self-transfer, repeated initialization, and
interleaved mint/burn/transfer. Vault comparisons additionally need failing and
reentrant dependencies, paused/wrong-asset paths, and caught versus propagated
failures as those features enter the generated slice.

Tests must also assert independently reviewed intended properties: two
implementations can agree on the same bug. Preserve random seeds and minimize
failing traces into regression tests. Track gas/resource behavior separately;
semantic agreement on generously funded calls does not establish equal
enabledness under a production gas limit.

The pinned contract source already contains Foundry tests for bridged-token
initialization/authority and vault burn/mint paths under
`l1-contracts/test/foundry/`. Reuse the applicable existing tests as a single
parameterized suite, copying or adapting them locally with source/license
provenance once the generated implementation exists. The result report should
show the same test inventory and outcomes for each implementation, with every
coverage gap listed. No dependency on the old verification repository is
introduced by this proposal.

## Evidence and first experiment

The initial experiment is deliberately bounded:

1. Define the token slice in the typed contract language and connect it to the
   existing token model.
2. Emit a reviewable Solidity implementation and build both implementations with
   recorded compiler settings and VM profiles.
3. Run shared assertions and differential stateful sequences, including failures.
4. Prove the supported translation rules or validate each output with a checked
   correspondence certificate. Identify uncovered semantics explicitly.

Passing tests supplies useful empirical correspondence evidence. A checked
preservation/equivalence proof supplies universal guarantees within its stated
semantics and assumptions. Neither implies that the specification captures every
intended bridge property, so manual review of `Specs/` and `Properties/` remains
necessary.

## Status of the first experiment

The bounded experiment above has been run for the bridged-token slice. Review
guide: [EraSpec/Codegen/README.md](EraSpec/Codegen/README.md); test report:
[solidity/README.md](solidity/README.md).

| Step | Status |
|---|---|
| 1. Typed contract language; token slice in it; connection to the token model | Done. [`Codegen/Lang.lean`](EraSpec/Codegen/Lang.lean) is the language and its interpreter; the slice is transcribed from the pinned source and OZ v4 with the source's check order, revert data and `unchecked` placement. Proved: both-direction agreement with `Contracts.BridgedStandardERC20` for every entry point and deployment, a `Simulation` instance, and the model's ledger invariant transferred to every reachable concrete storage. |
| 2. Emit reviewable Solidity; build both with recorded settings | Done. [`Codegen/Emit.lean`](EraSpec/Codegen/Emit.lean) prints [`BridgedTokenSlice.sol`](solidity/src/generated/BridgedTokenSlice.sol); `scripts/emit-solidity.sh --check` keeps it current. Both implementations build with the pin's own settings (solc 0.8.28, `prague`, optimizer 9 999 999). |
| 3. Shared assertions and differential stateful sequences, including failures | Done, all passing: 28 shared tests × 2 implementations (upstream's in-scope tests ported, exclusions listed by name), a differential fuzzer comparing after every call, and Lean-interpreter-generated vectors replayed against both. A mutation check shows the suite fails on each of 8 planted bugs. |
| 4. Prove the translation rules or validate each output | **Open.** The emitter is a trusted pretty-printer (`GEN-EMIT` in ASSUMPTIONS.md): there is no Solidity semantics here to prove it against. The Lean-generated vectors test it on 960 calls; that is evidence, not a proof. |

What this does and does not establish:

* The **generated** contract has a proved meaning — up to `GEN-EMIT`, `BUILD-*`
  and `VM-*` — and that meaning provably satisfies every property already proved
  of the token model.
* The **original** contract agrees with it on every tested input. No theorem
  mentions the original; its correspondence (`REP-TOKEN`) remains open as a
  proof obligation, now with substantial test evidence.

## Status of the second slice: the vault's preparation path

Step 1 has been run for the registered bridged-token branch of
`NativeTokenVaultBase.bridgeBurn` (`REP-VAULT`). Steps 2–4 have not.
Files: [`Codegen/Calls.lean`](EraSpec/Codegen/Calls.lean) and
[`Codegen/VaultPreparationSlice/`](EraSpec/Codegen/VaultPreparationSlice/).

| Step | Status |
|---|---|
| 1. Language; vault slice in it; connection to the vault model | Done, at interpreter level. [`Calls.lean`](EraSpec/Codegen/Calls.lean) extends the language without changing `Lang.lean`: high-level external calls and bodiless `internal virtual` hooks, both given meaning by a `Machine`; `bytes`, the length check, `abi.decode` of static types, `abi.encode` of words and `bytes`; `msg.value`, `block.chainid`; logs tagged with their emitter. [`Specs/Program.lean`](EraSpec/Codegen/VaultPreparationSlice/Specs/Program.lean) transcribes `bridgeBurn` and its callees (`NativeTokenVaultBase.sol:315-479`) in source order with source revert data; the native and base-token branches revert with `OutsideSlice()`. The token it calls is the bridged-token slice plus `originToken()` and `assetId()`. Proved: `BridgeBurnRefines`, both directions against `Contracts.NativeTokenVaultBase.prepare` (the model rejects iff the call reverts; on acceptance vault storage is unchanged, the state is related, the returned bytes are exactly `encodeMintData out.data`, the logs are exactly `prepareLogs`); `BridgeBurnSuccessIsPreparation` (every successful call is a model request); `BridgeBurnBacked` (`preparation_backed` on storage words); `Simulation` of `AssetBridgePreparation.Step`; `ReachableJournalBacked` from `AssetBridgePreparation.reachable_conservation` by `safety_transfer`; `EncodeMintDataLayout` and `EncodeMintDataInjective`; the first four checks and both slice edges with exact revert data (`L2ValueCheckedFirst`, `RouterCheckedSecond`, `PauseCheckedThird`, `BurnDataLengthCheckedFourth`, `NativeAssetLeavesTheSlice`, `BaseAssetLeavesTheSlice`). Each premise has a witness ([`Properties/Witnesses.lean`](EraSpec/Codegen/VaultPreparationSlice/Properties/Witnesses.lean), `RevertOrderPremisesSatisfiable`). |
| 2. Emit reviewable Solidity | Not started. `Codegen.Emit` has no rules for the `Codegen.Calls` constructs, so there is no generated vault. |
| 3. Shared assertions and differential sequences | Not started. No shared suite, differential run or Lean-generated vectors against the original vault. |
| 4. Prove the translation rules or validate each output | Open, as for the first slice. |

What this does and does not establish:

* **Trusted: `MODEL-CALLS`, not `GEN-EMIT`.** Nothing is emitted, so `GEN-EMIT`
  does not apply. The meaning of the `Codegen.Calls` constructs is a definition
  reviewed against Solidity's documentation, not a proof (`MODEL-CALLS` in
  ASSUMPTIONS.md). It has no reentrancy: the only callee is a `Codegen.Lang`
  program, which makes no calls. Hooks cannot write the caller's storage.
  Address parameters and returned static words are not range-checked. The
  refinement and `Step` statements assume `oc.val < 2 ^ 160`; the six
  revert-order statements do not, so for an out-of-range `oc` they describe the
  interpreter, whereas solc's decoder reverts first. The returned
  `originToken()` word is an address because `Rel` makes it one.
* **Boundaries of the slice.** One token in the world. The accounting tracker
  and metadata getters are hooks under `HooksAgree` (`DEP-FRAME`/`DEP-RESULTS`).
  The vault has no constructor: theorems start from any storage related by
  `Rel` to a model state, and `EveryWellFormedStateIsRepresented` shows one
  exists. `bytes32` is carried as `uint256`, so selectors differ from the
  source. Registration, `bridgeMint`, recovery, pausing and ownership are not
  transcribed.
* **The original vault.** No theorem mentions its bytecode, and there is no test
  evidence for it yet. `REP-VAULT` remains open for it.

Transcribing the branch surfaced three NatSpec mismatches at the pin. They
are comment-only, and no behavioural difference was found in the transcribed
branch. They have been reported to the maintainer of this repo and are not yet
confirmed upstream:

* `NativeTokenVaultBase.sol:106`: `onlyAssetRouter` is documented as checking
  for the bridgehub; `:108` checks the asset router.
* `NativeTokenVaultBase.sol:313`: `bridgeBurn` is documented as letting the
  bridgehub acquire `mintValue`; the caller must be the asset router (`:326`).
* `NativeTokenVaultBase.sol:314` and `IAssetHandler.sol:33` describe `_data` as a
  two-field tuple. `DataEncoding.sol:54-59` requires exactly 96 bytes,
  `(amount, receiver, maybeTokenAddress)`. For the transcription,
  `BurnDataLengthCheckedFourth` proves that every other length reverts with
  `InvalidNTVBurnData()`.

Natural next steps: emitter rules for the `Codegen.Calls` constructs, then
steps 2–3 for the vault against the pin's vault tests; and replace `GEN-EMIT`
with translation validation once a Solidity or Yul semantics is chosen.
