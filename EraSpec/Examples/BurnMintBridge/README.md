# Reference burn/mint bridge — not a deployed contract model

This is an illustrative application of `../../Core/PreparedApplication.lean`.
It is not a specification or verification of L2AssetRouter, NativeTokenVaultBase,
or BridgedStandardERC20. Their intended properties are tracked in `../../../REVIEW.md`.

- `Model.lean`: a single-obligation burn/mint/recovery model, preparation laws,
  stable execution, immutable input, replay prevention, value accounting, and
  countermodels for unlocked balances and conflicting protocol evidence.
- `ProtocolComposition.lean`: conditional composition with source-bound,
  time-pinned commitment histories across the complete flow.

The model uses natural-number amounts, fixed token/endpoint identities, exact
full recovery, and a declared set of permitted interference steps. Concrete
amount bounds, access control, pauses, configuration changes, token behavior,
external calls, rollback, real encoding/root authentication, and the halted-chain
timeout branch require further work. Full recovery here must not be confused with
the real manager's best-effort recovery.
