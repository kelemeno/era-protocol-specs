# ChainAdminOwnable

`ChainAdminOwnable` at era-contracts `draft/v0.35.0` `b17415d20`: the calls it makes, who controls
it, and the diamond and Bridgehub admin roles it holds.

## Headline guarantees

The folder's real guarantees about `b17415d20`, each with every premise. They are meant to carry
`@[headline]` (the lists after the table: `@[witness]`, `@[countermodel]`) once the tag attributes
of `EraSpec.Core.Headline` are on this branch; they are not tagged yet. A "run"
is any derivation of the execution relation `Sem`: any calls, by any address other than the
`ChainAdminOwnable` and zero, with unknown code that may call anything at any depth, including
inside a `multicall`. "Well-formed configuration" (`Config.WF`) means the `ChainAdminOwnable` is
nonzero, is not the Bridgehub, and neither it nor the Bridgehub is a diamond. Diamonds keep the
`b17415d20` code (a cut only leaves the admin pair arbitrary); the Bridgehub's code is fixed.

| Guarantee | Premises | Statement |
|---|---|---|
| Every call the `ChainAdminOwnable` makes is an element of a `multicall` entered by the owner of that moment, or exactly `t.setTokenMultiplier(n, d)` with value zero entered by the setter of that moment | Any run | `CallsAreOwnersOrSetters` |
| Every successful call a diamond or the Bridgehub receives from the `ChainAdminOwnable` is one of those calls | Any run | `ReceivedCallsAreOwnersOrSetters` |
| The setter changes only by the owner's `setTokenMultiplierSetter` | Any run | `SetterChangesOnlyByOwner` |
| The owner changes only by the nominee's `acceptOwnership` or the owner's `renounceOwnership`; the nominee only by the owner's `transferOwnership` or to zero | Any run | `OwnerChangesOnlyByAcceptOrRenounce` |
| From a constructed contract, once the owner is zero no write commits again and every later call it makes is a `setTokenMultiplier` call for the frozen setter | Well-formed configuration; the runs start from the constructor's storage, and the owner is zero at a point between calls | `ConstructedThenOwnerlessIsPermanent` |
| A renounced `ChainAdminOwnable` that is a diamond's admin keeps exactly that admin pair | Well-formed configuration; no owner and no nominee; the diamond has no pending admin; the run cuts no diamond | `RenouncedCaoKeepsDiamondAdmin` |
| A renounced `ChainAdminOwnable` calls diamonds only with selector `0x235d9eb5` (`setTokenMultiplier`) and never calls the Bridgehub successfully | Well-formed configuration; no owner and no nominee | `RenouncedCaoReachesOnlySetTokenMultiplier` |
| Whatever the `ChainAdminOwnable`'s state, the Bridgehub's owner makes any actor the Bridgehub's admin in two transactions | The owner and the target are nonzero, not the `ChainAdminOwnable` and not the Bridgehub proxy's admin | `BridgehubAdminRecoverable` |
| No `setTokenMultiplier` call of the setter reaches the Bridgehub (it has no such function and no fallback) | Well-formed configuration | `NoSetterCallReachesBridgehub` |

Witnesses: `AuthorityWitness`, `ZeroSetterWitness`, `RenounceWitness`,
`AdminRolesWitness`, `SetterReachesDiamondNotBridgehub`. Countermodels:
`MulticallOutlivesRenounce`, `PendingDiamondAdminEscapes`, `CtmCutMovesRenouncedAdmin`,
`AdminRoleLiveBeforeRenounce`. The other statements are supporting lemmas.

## Source

`l1-contracts/contracts/governance/ChainAdminOwnable.sol` at era-contracts
`draft/v0.35.0` head **`b17415d20`**, with the OpenZeppelin v4.9 `Ownable2Step` it inherits, the
`Admin` facet functions that move a ZK chain's admin (`state-transition/chain-deps/facets/Admin.sol`)
and the Bridgehub's admin and ownership functions (`core/bridgehub/BridgehubBase.sol`). Every
`file:line` in the specs is at `b17415d20`.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the guarantees and
their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact named propositions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Authority | [Specs/Authority.lean](Specs/Authority.lean) | [Properties/Authority.lean](Properties/Authority.lean) | [Proofs/Authority.lean](Proofs/Authority.lean) |
| AdminRoles | [Specs/AdminRoles.lean](Specs/AdminRoles.lean) | [Properties/AdminRoles.lean](Properties/AdminRoles.lean) | [Proofs/AdminRoles.lean](Proofs/AdminRoles.lean) |

Namespace: `Contracts.ChainAdminOwnable`. Statements are `Contracts.ChainAdminOwnable.Properties.*`;
each certificate has the same name without the `Properties` segment.

## Why it matters

`ChainAdminOwnable` is the admin the code recommends for chains (`governance/ChainAdmin.sol:27-28`),
and the deploy scripts make one the Bridgehub's admin (`deploy-scripts/ecosystem/DeployL1CoreContracts.s.sol:86`),
which can call `createNewChain`. Its owner drives an unrestricted `multicall`. A second key, the
`tokenMultiplierSetter`, is meant for an automated service and may only adjust the base-token gas
price: `setTokenMultiplier(chain, n, d)` forwards `chain.setTokenMultiplier(n, d)` to any address
the setter names. OpenZeppelin's `renounceOwnership` is not disabled.

## The model (`Specs/Authority.lean`)

One execution relation `Sem cfg j S L S'` over the `ChainAdminOwnable`'s storage (owner, nominee,
setter), every diamond's admin pair and the Bridgehub's owner, nominee, admin and pending admin,
with a ghost log of the calls made. Unknown code (any callee, any
callback, any depth) may call anything as any address other than the `ChainAdminOwnable` and zero,
so the owner and the setter may act at any moment, including inside a `multicall`. A revert is the
absence of a derivation, and any call may fail with no effect. Only two rules make a call whose
`msg.sender` is the `ChainAdminOwnable`, a `multicall` iteration and `setTokenMultiplier`, and each
logs it with its origin: the frame's `msg.sender` and the storage that frame was entered with.

## What to check

- `CallsAreOwnersOrSetters` (a): every call the `ChainAdminOwnable` makes is a `multicall` element
  submitted by the owner of the moment the `multicall` was entered, or exactly
  `t.setTokenMultiplier(n, d)` with value zero, for the setter of that moment, at any `t`.
  `ReceivedCallsAreOwnersOrSetters` says the same from the callee's side: every successful call a
  diamond or the Bridgehub receives from the `ChainAdminOwnable` is one of those calls.
- `WritesAreGuarded`, `SetterChangesOnlyByOwner` (b), `OwnerChangesOnlyByAcceptOrRenounce` (c): the
  setter changes only through the owner; the owner only through the nominee's accept or a renounce.
- `RenounceIsPermanent`, `OwnerlessHasNoNominee`, `ConstructedThenOwnerlessIsPermanent` (c): from a
  constructed contract, once the owner is zero there is no nominee, no write ever commits again,
  and every later call is a `setTokenMultiplier` call for the frozen setter.
- **Boundary** `MulticallOutlivesRenounce`: those results speak of `multicall`s entered by the owner,
  and of runs that start after the renounce. A `multicall` whose first call makes the owner renounce
  still makes its next call, which here nominates a diamond's pending admin.
- `ZeroSetterIsInert`: constructed with setter zero, as the Bridgehub's is
  (`deploy-scripts/ecosystem/DeployL1CoreUtils.s.sol:117-118`), the contract makes no
  `setTokenMultiplier` call until the owner writes a setter.
- `RenouncedCaoKeepsDiamondAdmin`, `RenounceStrandsDiamondAdminRole`,
  `RenouncedCaoReachesOnlySetTokenMultiplier` (d): a renounced `ChainAdminOwnable` that is a
  diamond's admin **with no pending admin** keeps exactly that admin pair on every run that does
  not cut the diamond; on such a run no `setPendingAdmin`, `acceptAdmin` or `onlyAdmin` function of
  the diamond succeeds, and an `onlyAdminOrChainTypeManager` function succeeds only for the chain
  type manager or as the `ChainAdminOwnable`'s `setTokenMultiplier`; and the only diamond
  function the `ChainAdminOwnable` ever calls successfully has selector `0x235d9eb5`. Each premise
  is needed: `PendingDiamondAdminEscapes` (a pending admin, left for instance by the boundary run
  above, still takes the diamond), `CtmCutMovesRenouncedAdmin` (a cut by the chain type manager
  moves it), and `AdminRoleLiveBeforeRenounce` (before the renounce, an `onlyAdmin` function is
  reachable through the owner's `multicall`). The no-pending-admin premise is necessary
  (`PendingDiamondAdminEscapes`).
- `BridgehubAdminRecoverable` (e): whatever the `ChainAdminOwnable`'s state, the Bridgehub's owner
  can make any actor the Bridgehub's admin in two transactions (`setPendingAdmin` is
  `onlyOwnerOrAdmin`).
- `SetterCallToBridgehubReverts`, `SetTokenMultiplierOnBridgehubReverts`,
  `NoSetterCallReachesBridgehub` (f): `L1Bridgehub` has no function with selector `0x235d9eb5`
  (`BRIDGEHUB_SELECTORS`, the 51 entries of its committed ABI hashed with `cast sig`) and no
  `fallback`, so the setter's call to it reverts for every caller, value and state.
- Witnesses: `AuthorityWitness`, `ZeroSetterWitness`, `RenounceWitness`, `AdminRolesWitness`,
  `SetterReachesDiamondNotBridgehub`. Each property's premises are instantiated by one of them; the
  module docstrings of `Properties/Authority.lean` and `Properties/AdminRoles.lean` say which.

## Model boundaries

- Diamonds are fixed: diamond creation is not a step, and after a cut a diamond's functions are
  still the `b17415d20` ones (a cut only leaves the admin pair arbitrary). The results that admit
  cuts say nothing about the code a cut installs.
- The Bridgehub's code is fixed: its `ProxyAdmin`'s calls never reach the implementation and are
  not modelled beyond failing, so implementation upgrades are outside the model. `initialize`
  reverts (the proxy is initialized). Every other function of `BRIDGEHUB_SELECTORS` except the five
  ownership and admin writers is unknown code that writes none of the four modelled slots.
- On a diamond, every function gated on the admin (`onlyAdmin`: `ADMIN_ONLY_SELECTORS`;
  `onlyAdminOrChainTypeManager`: `ADMIN_OR_CTM_SELECTORS`, which includes `setTokenMultiplier`)
  keeps only its access check, followed by unknown code; its other checks (`onlyL1`,
  `onlySettlementLayer`, argument checks) and its writes are not modelled. Every other diamond
  function, including `setProofSystemStatus` (whose check also admits the Bridgehub's owner) and the
  `onlyChainTypeManager` functions, is unknown code with no access check.
  `upgradeChainFromVersion`'s validator set and timestamp gate are not modelled (any sender may run
  it).
- Not modelled: ETH balances, gas, events other than the ghost log, the extcodesize check before
  `ChainAdminOwnable.sol:69` (omitting it only adds runs), other `ChainAdminOwnable` instances (they
  are unknown code), and the chain type manager's own admin role, which the hub's
  `ChainAdminOwnable` also holds (`protocol-docs/ecosystem-deployment.md:249`; its
  `setPendingAdmin` is `onlyOwnerOrAdmin` too, `state-transition/ChainTypeManager.sol:354-375`).
- ABI decoding is a parameter of the configuration. The witnesses use a decoder that reads 32-byte
  words for `(address)` and `(address, uint128, uint128)` and maps two one-byte tags to the two
  witness call lists for `(Call[], bool)`.

## Relation to other work

`RegistryBootstrapMigration` `Forward` proves the analogous stranding for the CTM
(`RenouncedAuthorityIsStranded`).
