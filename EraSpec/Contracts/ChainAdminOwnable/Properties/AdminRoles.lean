import EraSpec.Contracts.ChainAdminOwnable.Specs.AdminRoles
import EraSpec.Core.Headline

/-!
# Properties: the admin roles a `ChainAdminOwnable` holds

Statements about `EraSpec.Contracts.ChainAdminOwnable.Specs.Authority`, read at the diamond and
the Bridgehub (`Specs/AdminRoles.lean`). Proofs are in
`EraSpec.Contracts.ChainAdminOwnable.Proofs.AdminRoles`.

## What holds

* **A renounced `ChainAdminOwnable` keeps a diamond's admin role**
  (`RenouncedCaoKeepsDiamondAdmin`). From storage with no owner and no nominee, a diamond whose
  admin is the `ChainAdminOwnable` with no pending admin keeps exactly that admin pair along every
  run that does not cut that diamond. No other actor can move it: the diamond has no owner role.
* **The role is stranded** (`RenounceStrandsDiamondAdminRole`). Along such a run, no
  `setPendingAdmin`, `acceptAdmin` or `onlyAdmin` function of that diamond succeeds, and an
  `onlyAdminOrChainTypeManager` function succeeds only for the chain type manager or as the
  `ChainAdminOwnable`'s `setTokenMultiplier`.
* **It reaches only `setTokenMultiplier`** (`RenouncedCaoReachesOnlySetTokenMultiplier`). Along
  any run from such storage, every diamond function the `ChainAdminOwnable` successfully calls has
  selector `0x235d9eb5`, `setTokenMultiplier(uint128,uint128)`, and it calls the Bridgehub
  successfully not at all.
* **As Bridgehub admin, a renounce is recoverable** (`BridgehubAdminRecoverable`). Whatever the
  `ChainAdminOwnable`'s storage, a Bridgehub owner that is an actor of its own can make any nonzero
  actor `x` the Bridgehub's admin in two transactions: `setPendingAdmin(x)`, then `x`'s
  `acceptAdmin()`.
* **No setter-originated call reaches the Bridgehub** (`SetterCallToBridgehubReverts`,
  `SetTokenMultiplierOnBridgehubReverts`, `NoSetterCallReachesBridgehub`). The call
  `setTokenMultiplier(n, d)` from the `ChainAdminOwnable` to the Bridgehub has no successful
  execution, whatever the state; so `setTokenMultiplier(bridgehub, n, d)` on the
  `ChainAdminOwnable` reverts for every caller; and along any run no logged setter call targets
  the Bridgehub.

## Which premises are needed

* `PendingDiamondAdminEscapes`: from renounced storage, a diamond whose admin is the
  `ChainAdminOwnable` but whose pending admin is `12` (as `MulticallOutlivesRenounce` leaves it)
  loses that admin to `12`, with no cut. The "no pending admin" premise is needed.
* `CtmCutMovesRenouncedAdmin`: a cut by the diamond's chain type manager moves the admin of a
  diamond held by a renounced `ChainAdminOwnable`. The "no cut" premise is needed.
* `AdminRoleLiveBeforeRenounce`: before the renounce, the owner's `multicall` makes the
  `ChainAdminOwnable` call an `onlyAdmin` function of the diamond it holds, which succeeds. The
  renounce premise of `RenounceStrandsDiamondAdminRole` is needed.

## Witnesses

* `AdminRolesWitness` (for `RenouncedCaoKeepsDiamondAdmin`, `RenounceStrandsDiamondAdminRole`,
  `RenouncedCaoReachesOnlySetTokenMultiplier`, `BridgehubAdminRecoverable`,
  `NoSetterCallReachesBridgehub`): from `wRenounced` (renounced storage, admin of diamond `4` with
  no pending admin, admin of the Bridgehub), one run commits in which the setter's
  `setTokenMultiplier` reaches diamond `4`, the chain type manager calls the diamond's
  `changeFeeParams`, and the Bridgehub's owner `9` hands the Bridgehub's admin role to `8`; the
  diamond's admin pair is unchanged and no cut is logged.
* `SetterReachesDiamondNotBridgehub` (for `SetterCallToBridgehubReverts`,
  `SetTokenMultiplierOnBridgehubReverts`): from the same state, the `ChainAdminOwnable`'s call
  `setTokenMultiplier(3, 2)` to diamond `4`, and the setter's `setTokenMultiplier(4, 3, 2)`, both
  have successful executions; the premises of the Bridgehub results hold in the witness
  configuration for the Bridgehub `2`.
-/

namespace Contracts.ChainAdminOwnable

/-! ## The diamond -/

/-- **(d) A RENOUNCED `ChainAdminOwnable` KEEPS A DIAMOND'S ADMIN ROLE.** In a well-formed
configuration, start from storage with no owner and no nominee, and a diamond `D` whose admin is
the `ChainAdminOwnable` and whose pending admin is zero. Along any run that logs no cut of `D`, `D`
ends with the same admin pair. -/
@[headline] def Properties.RenouncedCaoKeepsDiamondAdmin : Prop :=
  ∀ (cfg : Config) (S S' : State) (L : List Event) (D : Address), cfg.WF →
    S.cao.owner = 0 → S.cao.pending = 0 → S.chain D = ⟨cfg.cao, 0⟩ →
    Sem cfg .acts S L S' → Event.cut D ∉ L → S'.chain D = ⟨cfg.cao, 0⟩

/-- **(d) A RENOUNCE STRANDS THE DIAMOND'S ADMIN ROLE.** In a well-formed configuration, start
from storage with no owner and no nominee, and a diamond `D` whose admin is the
`ChainAdminOwnable` and whose pending admin is zero. Along any run that logs no cut of `D`, every
logged successful call into `D`:
* is none of `setPendingAdmin`, `acceptAdmin` and the `onlyAdmin` functions
  (`ADMIN_ONLY_SELECTORS`);
* if it is an `onlyAdminOrChainTypeManager` function (`ADMIN_OR_CTM_SELECTORS`), was made by `D`'s
  chain type manager, or is the `ChainAdminOwnable`'s call of `setTokenMultiplier`. -/
def Properties.RenounceStrandsDiamondAdminRole : Prop :=
  ∀ (cfg : Config) (S S' : State) (L : List Event) (D : Address), cfg.WF →
    S.cao.owner = 0 → S.cao.pending = 0 → S.chain D = ⟨cfg.cao, 0⟩ →
    Sem cfg .acts S L S' → Event.cut D ∉ L →
    ∀ s sel, Event.chainEntry D s sel ∈ L →
      sel ∉ SEL_SET_PENDING_ADMIN :: SEL_ACCEPT_ADMIN :: ADMIN_ONLY_SELECTORS ∧
        (sel ∈ ADMIN_OR_CTM_SELECTORS → s = cfg.ctmOf D ∨ (s = cfg.cao ∧ sel = SEL_SET_MULTIPLIER))

/-- **(d) A RENOUNCED `ChainAdminOwnable` REACHES ONLY `setTokenMultiplier`.** In a well-formed
configuration, start from storage with no owner and no nominee. Along any run, every logged
successful call by the `ChainAdminOwnable` into a diamond has selector `0x235d9eb5`
(`setTokenMultiplier(uint128,uint128)`), and none into the Bridgehub is logged. -/
@[headline] def Properties.RenouncedCaoReachesOnlySetTokenMultiplier : Prop :=
  ∀ (cfg : Config) (S S' : State) (L : List Event), cfg.WF →
    S.cao.owner = 0 → S.cao.pending = 0 → Sem cfg .acts S L S' →
    (∀ D sel, Event.chainEntry D cfg.cao sel ∈ L → sel = SEL_SET_MULTIPLIER) ∧
      ∀ sel, Event.hubEntry cfg.cao sel ∉ L

/-! ## The Bridgehub -/

/-- **(e) AS BRIDGEHUB ADMIN, A RENOUNCE IS RECOVERABLE.** From any state (in particular one where
the `ChainAdminOwnable` is the Bridgehub's admin and has renounced), take a Bridgehub owner that is
nonzero, not the `ChainAdminOwnable` and not the Bridgehub proxy's admin, a target `x` with the
same three properties, and an argument encoding `arg` that decodes to `x`. Then a run of two
transactions, the owner's `setPendingAdmin` with `arg` and `x`'s `acceptAdmin()`, commits and ends
with `x` as the Bridgehub's admin, no pending admin, and the `ChainAdminOwnable`'s storage and
every diamond's admin pair unchanged. -/
@[headline] def Properties.BridgehubAdminRecoverable : Prop :=
  ∀ (cfg : Config) (S : State) (x : Address) (arg : Bytes),
    S.hub.owner ≠ 0 → S.hub.owner ≠ cfg.cao → S.hub.owner ≠ cfg.hubProxyAdmin →
    x ≠ 0 → x ≠ cfg.cao → x ≠ cfg.hubProxyAdmin → cfg.abi.addr arg = some x →
    ∃ L S', Sem cfg .acts S L S' ∧ S'.hub.admin = x ∧ S'.hub.pendingAdmin = 0 ∧
      S'.cao = S.cao ∧ S'.chain = S.chain

/-- **(f) THE SETTER'S CALL TO THE BRIDGEHUB REVERTS.** In a well-formed configuration, the
`ChainAdminOwnable`'s call to the Bridgehub with calldata `setTokenMultiplier(n, d)`, with any value,
has no successful execution from any state. In the model the Bridgehub runs only the functions of
`BRIDGEHUB_SELECTORS`, for callers other than its proxy admin, and `0x235d9eb5` is not among them
(`L1Bridgehub` has no `fallback`); calls by the proxy admin run nothing (in the source they reach
only the proxy's admin interface, which has no function with that selector either). -/
def Properties.SetterCallToBridgehubReverts : Prop :=
  ∀ (cfg : Config) (S S' : State) (L : List Event) (v : UInt256) (n d : ℕ), cfg.WF →
    ¬ Sem cfg (.call cfg.cao ⟨cfg.hub, v, multiplierData n d⟩ true) S L S'

/-- **(f) `setTokenMultiplier(bridgehub, n, d)` REVERTS.** In a well-formed configuration, a call
of the `ChainAdminOwnable` whose calldata selects `setTokenMultiplier(address,uint128,uint128)` and
decodes to the Bridgehub as target has no successful execution, for any caller, value and state. -/
def Properties.SetTokenMultiplierOnBridgehubReverts : Prop :=
  ∀ (cfg : Config) (S S' : State) (L : List Event) (s : Address) (v : UInt256) (data : Bytes)
    (n d : ℕ), cfg.WF → data.take 4 = SEL_SET_MULTIPLIER_VIA →
    cfg.abi.multiplierArgs (data.drop 4) = some (cfg.hub, n, d) →
    ¬ Sem cfg (.call s ⟨cfg.cao, v, data⟩ true) S L S'

/-- **(f) NO SETTER CALL REACHES THE BRIDGEHUB.** In a well-formed configuration, along any run,
no logged `setTokenMultiplier` call of the `ChainAdminOwnable` targets the Bridgehub. -/
@[headline] def Properties.NoSetterCallReachesBridgehub : Prop :=
  ∀ (cfg : Config) (S S' : State) (L : List Event), cfg.WF → Sem cfg .acts S L S' →
    ∀ inv pre t n d c ok, Event.caoCall (.multiplier inv pre t n d) c ok ∈ L → t ≠ cfg.hub

/-! ## Which premises are needed -/

/-- **A PENDING ADMIN STILL TAKES THE DIAMOND.** In the witness configuration, the owner's
`multicall` of `MulticallOutlivesRenounce`, run from `wS1`, ends in `wNominated`: renounced
storage, and diamond `4`'s admin is the `ChainAdminOwnable` with pending admin `12`. From
`wNominated`, a run of `12`'s `acceptAdmin()` commits, logs no cut, and makes `12` the diamond's
admin. -/
@[countermodel] def Properties.PendingDiamondAdminEscapes : Prop :=
  (∃ L, Sem wCfg .acts wS1 L wNominated) ∧
    wNominated.cao.owner = 0 ∧ wNominated.cao.pending = 0 ∧ wNominated.chain 4 = ⟨wCfg.cao, 12⟩ ∧
    ∃ L S', Sem wCfg .acts wNominated L S' ∧ Event.cut 4 ∉ L ∧ S'.chain 4 = ⟨12, 0⟩

/-- **BEFORE THE RENOUNCE, THE ADMIN ROLE IS LIVE.** In the witness configuration, `wS1` has owner
`6`, and diamond `4`'s admin is the `ChainAdminOwnable` with no pending admin. From `wS1`, the
owner's `multicall(wCallsC, true)` commits, logs no cut, and makes the `ChainAdminOwnable` call the
diamond's `onlyAdmin` function `setTransactionFilterer(13)`, which the diamond logs. The conclusion
of `RenounceStrandsDiamondAdminRole` fails here: its renounce premise is needed. -/
@[countermodel] def Properties.AdminRoleLiveBeforeRenounce : Prop :=
  wS1.cao.owner ≠ 0 ∧ wS1.chain 4 = ⟨wCfg.cao, 0⟩ ∧
    SEL_SET_TRANSACTION_FILTERER ∈ ADMIN_ONLY_SELECTORS ∧
    ∃ L S', Sem wCfg .acts wS1 L S' ∧ Event.cut 4 ∉ L ∧
      Event.chainEntry 4 wCfg.cao SEL_SET_TRANSACTION_FILTERER ∈ L

/-- **A CUT MOVES THE DIAMOND'S ADMIN.** In the witness configuration, from `wRenounced` (renounced
storage; diamond `4`'s admin is the `ChainAdminOwnable` with no pending admin), the chain type
manager `5`'s `executeUpgrade`, whose initialization writes admin `13`, commits and makes `13` the
diamond's admin. Its log contains the cut. -/
@[countermodel] def Properties.CtmCutMovesRenouncedAdmin : Prop :=
  wRenounced.cao.owner = 0 ∧ wRenounced.cao.pending = 0 ∧ wRenounced.chain 4 = ⟨wCfg.cao, 0⟩ ∧
    ∃ L S', Sem wCfg .acts wRenounced L S' ∧ Event.cut 4 ∈ L ∧ S'.chain 4 = ⟨13, 0⟩

/-! ## Witnesses -/

/-- **THE ADMIN-ROLE RESULTS ARE NOT VACUOUS.** The witness configuration is well formed. In
`wRenounced`, the `ChainAdminOwnable`'s storage has no owner and no nominee, diamond `4`'s admin is
the `ChainAdminOwnable` with no pending admin, and the Bridgehub's owner is `9` (nonzero, neither
the `ChainAdminOwnable` nor the proxy admin `3`); `8` is nonzero, neither of those either, and its
encoding decodes to it. From `wRenounced`, one run commits: the setter's
`setTokenMultiplier(4, 3, 2)` makes the `ChainAdminOwnable` call diamond `4` (logged with selector
`0x235d9eb5`); the diamond's chain type manager `5` calls its `changeFeeParams` (an
`onlyAdminOrChainTypeManager` function, logged); then `9` nominates `8` on the Bridgehub and `8`
accepts. The run logs no cut, the diamond keeps its admin pair, and `8` is the Bridgehub's
admin. -/
@[witness] def Properties.AdminRolesWitness : Prop :=
  wCfg.WF ∧ wRenounced.cao.owner = 0 ∧ wRenounced.cao.pending = 0 ∧
    wRenounced.chain 4 = ⟨wCfg.cao, 0⟩ ∧
    wRenounced.hub.owner = 9 ∧ (9 : Address) ≠ 0 ∧ (9 : Address) ≠ wCfg.cao ∧
    (9 : Address) ≠ wCfg.hubProxyAdmin ∧
    (8 : Address) ≠ 0 ∧ (8 : Address) ≠ wCfg.cao ∧ (8 : Address) ≠ wCfg.hubProxyAdmin ∧
    wCfg.abi.addr (word32 8) = some 8 ∧
    ∃ L S', Sem wCfg .acts wRenounced L S' ∧
      Event.chainEntry 4 wCfg.cao SEL_SET_MULTIPLIER ∈ L ∧
      Event.chainEntry 4 (wCfg.ctmOf 4) SEL_CHANGE_FEE_PARAMS ∈ L ∧
      Event.caoCall (.multiplier 7 wRenounced.cao 4 3 2) ⟨4, 0, multiplierData 3 2⟩ true ∈ L ∧
      Event.cut 4 ∉ L ∧ S'.chain 4 = ⟨wCfg.cao, 0⟩ ∧ S'.hub.admin = 8

/-- **THE SETTER REACHES ITS DIAMOND.** In the witness configuration, from `wRenounced`:
* the `ChainAdminOwnable`'s call `setTokenMultiplier(3, 2)` (value zero) to diamond `4` has a
  successful execution, which `SetterCallToBridgehubReverts` rules out for the Bridgehub `2`;
* the setter `7`'s `setTokenMultiplier(4, 3, 2)` has a successful execution;
* the calldata `viaData 2 3 2` selects `setTokenMultiplier(address,uint128,uint128)` and decodes
  to the Bridgehub `2`, the premises of `SetTokenMultiplierOnBridgehubReverts`. -/
@[witness] def Properties.SetterReachesDiamondNotBridgehub : Prop :=
  wCfg.WF ∧
    (∃ L S', Sem wCfg (.call wCfg.cao ⟨4, 0, multiplierData 3 2⟩ true) wRenounced L S') ∧
    (∃ L S', Sem wCfg (.call 7 ⟨wCfg.cao, 0, viaData 4 3 2⟩ true) wRenounced L S') ∧
    (viaData 2 3 2).take 4 = SEL_SET_MULTIPLIER_VIA ∧
    wCfg.abi.multiplierArgs ((viaData 2 3 2).drop 4) = some (wCfg.hub, 3, 2)

end Contracts.ChainAdminOwnable
