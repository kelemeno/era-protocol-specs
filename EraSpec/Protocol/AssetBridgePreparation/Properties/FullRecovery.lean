import EraSpec.Protocol.AssetBridgePreparation.Specs.FullRecovery
import EraSpec.Contracts.NativeTokenVaultBase.Specs.ModelCorrespondence

/-!
# Properties: when an atomic refund restores a bundle in full

Statements about `EraSpec.Protocol.AssetBridgePreparation.Specs.FullRecovery`, on the manager,
router and vault model of `Contracts.AssetRouter.AtomicRecovery`.  Proofs are in
`EraSpec.Protocol.AssetBridgePreparation.Proofs.FullRecovery`.

## Terminality against full restoration

A successful `claimRefund` leaves the leg `Reverted` for good (`AtomicFlowManager.sol:175`).
`TerminalIsFullIffNoDecline` says exactly when that terminal state also means every call was
recovered: when no call of the loop returned `false`.  `FullAcceptanceIffAllRecovered` is the same
fact on `AttackVectors.RecoveryLimits`' outcome lists.  A router `finalizeDeposit` call never
returns `false`: it reverts or returns `true` (`L2AssetRouter.sol:293-295`).  So a bundle made only
of such calls never declines (`DepositBundleNeverDeclines`), and every successful claim of it is a
full restoration (`DepositBundleClaimIsFull`).  Neither statement takes a premise about the
hooks, the assets or the vault.  `DecliningCallMakesTerminalPartial` shows the router-only
premise is needed: one call to another target that returns `false` gives a terminal leg with a
call left unrestored.

## What the refund of a deposit bundle does, exactly

On assets the vault's registry has a token for, with tokens that behave as the local token model
and an unpaused vault, the manager's loop is exactly two runs side by side
(`DepositRefundIsCredits`):

* the tracker hook on each deposit, in order;
* the token-model credit of each deposit, in order: a re-mint for a bridged asset, a release from
  the vault's escrow for a native one, each of the data's `amount` to the data's `originalCaller`.

The loop succeeds when both runs do, counts every call, and changes nothing else.
`DepositClaimIffCredits` is the same at the level of the claim: it succeeds if and only if the
bundle is nonempty and both runs succeed.  `NonStandardTokenCountedButNotCredited` shows the token
model is needed for this.  With a mint hook that is not the token model's `mint`, the claim succeeds
and counts every call while crediting nothing: `recovered` counts `true` returns, not credits.

## When it is enabled, and what it restores

* `CreditsCoveredSucceedExactly` gives the exact result whenever `CreditsCovered` holds:
  - every touched token keeps its configuration;
  - its supply rises by exactly what is re-minted on it;
  - every account gains exactly what the bundle credits it on that token (the vault, in addition,
    loses what it releases from escrow);
  - untouched tokens are unchanged.

  `CreditsCovered` asks for a nonzero vault, nonzero original callers, the base-token exclusion,
  escrow covering each native token's releases, and the vault as minter of each bridged token
  with joint supply headroom.
* `CreditsPreserveLedgers`: every credit run keeps each ledger well-formed.
* `TrackerAlwaysReturnsRuns` is a sufficient condition for the tracker run.
* `JointHeadroomNeeded`: per-call headroom is not enough for a bundle, so the headroom in
  `CreditsCovered` is per token, over the whole bundle.
* **Headline (world level), `RegisteredDepositBundleFullyRecovered`.** Take a nonempty deposit
  bundle on registered assets, an unpaused vault, a tracker run that succeeds, and
  `CreditsCovered`.  Then:
  - the claim succeeds and recovers every call (`recovered = callsLen`);
  - the ledgers are exactly the credited ones and stay well-formed;
  - the router's maps, the registry and the pause flag are unchanged.

## Pause

* `PausedVaultBlocksDepositClaim`: while the vault is paused, every claim of a nonempty
  router-deposit bundle reverts, whatever the hooks, so the leg stays `Revertable`.
* `PauseOnlyDelaysFullRecovery`: under the headline's premises the paused world's claim reverts,
  and the same world unpaused recovers in full.  Pause delays the refund; it strands nothing.

## The preparation trace: deposits prepared on this chain

* `PendingObligationsSound`: from a well-formed vault with nothing pending, every obligation the
  preparation trace (`Specs/Model.lean`) has pending satisfies three things.  It is for the vault's
  tracked asset.  It names a nonzero depositor as `originalCaller`.  It was prepared under an
  in-scope configuration.
* **Headline, `PreparedBundleFullyRecovered`.** The bundle's deposit calls carry pending
  obligations of such a trace, a sub-multiset of the pending list.  The world's registry corresponds
  to the trace's vault (`NativeTokenVaultBase.Corr`), and its ledger of the tracked token is the
  trace's token.  The vault is unpaused and the tracker run succeeds.  Then:
  - the claim succeeds and recovers every call;
  - each depositor gains exactly the amounts the bundle owes it, and supply rises by exactly the
    bundle's pending total;
  - supply plus whatever is still pending is the supply before the trace, so a bundle carrying
    the whole pending list restores the starting supply exactly;
  - the router's maps, the registry, the pause flag and every other token's ledger are unchanged
    (the tracker state is the tracker run's).

  The supply headroom is not a premise: it follows from the trace's conservation.

## Non-vacuity

* `FullRecoverySatisfiable` meets, in one world, the premises of every world-level property above:
  - a two-call bundle, one native and one bridged deposit, with nonzero amounts;
  - a tracker that changes state;
  - the paused copy of the same world.
* `PreparedBundleFullyRecoveredSatisfiable` meets the premises of the two trace-level properties,
  on a trace of two preparations by two different depositors.  Its bundle carries both.

The countermodels are existence statements and are their own witnesses.  No property takes a
hash premise.
-/

namespace AssetBridgePreparation.FullRecovery

open Contracts
open Contracts.AssetRouter (Chain AssetId Address AssetIdOf)
open Contracts.AssetRouter.AtomicRecovery (Config Call CallData World Hooks MintData Addr160
  recoverCall recoverBundle claimRefund outcomes routerCall AtomicBundleValid)
open AttackVectors.RecoveryLimits (Outcome LegState ClaimAccepted recoveredCount)

/-! ## Terminality against full restoration -/

/-- **A TERMINAL CLAIM IS A FULL RESTORATION EXACTLY WHEN NO CALL DECLINED.**  For any per-call
behaviour: once `claimRefund` has succeeded, so the leg is `Reverted` and cannot be claimed again,
the loop recovered every call of the bundle if and only if none of its calls returned `false`. -/
def Properties.TerminalIsFullIffNoDecline : Prop :=
  ∀ (X : Type) (step : World X → Call → Option (World X × Bool)) (w w' : World X)
    (calls : List Call),
    claimRefund step LegState.Revertable w calls = some (LegState.Reverted, w') →
      (recoverBundle step w calls = some (w', calls.length) ↔
        Outcome.declined ∉ outcomes step w calls)

/-- **THE SAME, ON `RecoveryLimits`' OUTCOME LISTS.**  An outcome list is both accepted by the
manager's rule and fully recovered if and only if it is nonempty and every outcome is
`recovered`. -/
def Properties.FullAcceptanceIffAllRecovered : Prop :=
  ∀ os : List Outcome,
    ClaimAccepted os ∧ recoveredCount os = os.length ↔ os ≠ [] ∧ ∀ o ∈ os, o = Outcome.recovered

/-- **A ROUTER-DEPOSIT BUNDLE NEVER DECLINES.**  No premise on the hooks, the assets or the data.
If every call targets the router with `finalizeDeposit` data, no call of the loop returns `false`,
because the router returns `true` whenever the vault's refund returns
(`L2AssetRouter.sol:293-295`). -/
def Properties.DepositBundleNeverDeclines : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (other : OtherTargets X)
    (dest : Chain) (w : World X) (calls : List Call),
    (∀ c ∈ calls, RouterDepositShaped cfg c) →
      Outcome.declined ∉ outcomes (recoverCall enc cfg hk other dest) w calls

/-- **…SO EVERY SUCCESSFUL CLAIM OF IT IS A FULL RESTORATION.**  No premise on the hooks, the
assets or the data: a claim of a router-deposit bundle either reverts as a whole or recovers every
call. -/
def Properties.DepositBundleClaimIsFull : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (other : OtherTargets X)
    (dest : Chain) (w w' : World X) (calls : List Call),
    (∀ c ∈ calls, RouterDepositShaped cfg c) →
    claimRefund (recoverCall enc cfg hk other dest) LegState.Revertable w calls =
      some (LegState.Reverted, w') →
      recoverBundle (recoverCall enc cfg hk other dest) w calls = some (w', calls.length)

/-! ## What the refund of a deposit bundle does, exactly -/

/-- **THE REFUND OF A DEPOSIT BUNDLE IS EXACTLY ITS CREDITS.**  Tokens behave as the local token
model (`localHooks`), the vault is unpaused, and every deposit's asset has a token in the
registry.  Then the manager's loop is the tracker run and the credit run side by side.  It
succeeds when both do, counts every call, and changes only the ledgers and the tracker. -/
def Properties.DepositRefundIsCredits : Prop :=
  ∀ (A : Type) (enc : AssetIdOf) (cfg : Config) (vault : Addr160) (base : AssetId)
    (tr : TrackerHook A) (dep : DeployHook A) (other : OtherTargets (Ledgers A)) (dest : Chain)
    (w : World (Ledgers A)) (calls : List Call) (ds : List Deposit),
    w.paused = false → DepositBundle cfg calls ds → (∀ d ∈ ds, w.vault.token d.1 ≠ 0) →
      recoverBundle (recoverCall enc cfg (localHooks vault base tr dep) other dest) w calls =
        (trackerRun tr dest w.rest.tracker ds).bind fun t =>
          (creditRun vault base cfg.thisChain w.vault w.rest.token ds).map fun L =>
            ({ w with rest := ⟨L, t⟩ }, ds.length)

/-- **THE CLAIM SUCCEEDS EXACTLY WHEN THE BUNDLE IS NONEMPTY AND EVERY HOOK AND CREDIT DOES.**
Same setting as `DepositRefundIsCredits`.  The claim's world is then exactly the credited one. -/
def Properties.DepositClaimIffCredits : Prop :=
  ∀ (A : Type) (enc : AssetIdOf) (cfg : Config) (vault : Addr160) (base : AssetId)
    (tr : TrackerHook A) (dep : DeployHook A) (other : OtherTargets (Ledgers A)) (dest : Chain)
    (w w' : World (Ledgers A)) (calls : List Call) (ds : List Deposit),
    w.paused = false → DepositBundle cfg calls ds → (∀ d ∈ ds, w.vault.token d.1 ≠ 0) →
      (claimRefund (recoverCall enc cfg (localHooks vault base tr dep) other dest)
          LegState.Revertable w calls = some (LegState.Reverted, w') ↔
        ds ≠ [] ∧ ∃ t L, trackerRun tr dest w.rest.tracker ds = some t ∧
          creditRun vault base cfg.thisChain w.vault w.rest.token ds = some L ∧
          w' = { w with rest := ⟨L, t⟩ })

/-! ## When every credit succeeds, and what it gives -/

/-- **COVERED CREDITS SUCCEED, EXACTLY.**  Under `CreditsCovered`, the credit run succeeds and
its result is `ExactCredits`.  Untouched tokens are unchanged.  On each token the configuration
is kept, supply rises by what is re-minted, and each account gains what the bundle credits it, less
the vault's escrow releases for the vault itself. -/
def Properties.CreditsCoveredSucceedExactly : Prop :=
  ∀ (vault : Addr160) (base : AssetId) (thisChain : Chain) (V : NativeTokenVault.Vault)
    (L : Address → BridgedStandardERC20.State) (ds : List Deposit),
    CreditsCovered vault base thisChain V L ds →
      ∃ L', creditRun vault base thisChain V L ds = some L' ∧ ExactCredits vault thisChain V L L' ds

/-- **CREDITS KEEP EVERY LEDGER WELL-FORMED.**  Sum of balances equal to supply, supply below
`2^256`, nothing at the zero address. -/
def Properties.CreditsPreserveLedgers : Prop :=
  ∀ (vault : Addr160) (base : AssetId) (thisChain : Chain) (V : NativeTokenVault.Vault)
    (L L' : Address → BridgedStandardERC20.State) (ds : List Deposit),
    creditRun vault base thisChain V L ds = some L' →
      ∀ tok, BridgedStandardERC20.WellFormed (L tok) → BridgedStandardERC20.WellFormed (L' tok)

/-- **A TRACKER THAT NEVER REVERTS ON THE BUNDLE'S DEPOSITS LETS THE TRACKER RUN SUCCEED.**  This
is a sufficient condition for the tracker premise below.  On an asset the deployed L2 tracker has
already registered, its hook can revert only on a checked-add overflow
(`L2AssetTracker.sol:285-305`).  Its first-touch legacy registration (`:309-353`) has further
checks: a nonzero origin chain, a zero chain balance for a native asset, and token getters. -/
def Properties.TrackerAlwaysReturnsRuns : Prop :=
  ∀ (A : Type) (tr : TrackerHook A) (dest : Chain) (t : A) (ds : List Deposit),
    (∀ d ∈ ds, ∀ t', (tr t' dest d.1 d.2.amount).isSome) → (trackerRun tr dest t ds).isSome

/-- **HEADLINE (WORLD LEVEL): A COVERED DEPOSIT BUNDLE ON REGISTERED ASSETS IS RESTORED IN FULL.**

Premises:
* tokens behave as the local token model;
* the vault is unpaused;
* the bundle is a nonempty bundle of router deposits, each on an asset whose token is in the
  registry;
* the tracker run succeeds;
* the credits are covered (`CreditsCovered`).

Conclusions:
* the claim succeeds and the loop recovers every call (`recovered = callsLen`);
* the ledgers are exactly the credited ones (`ExactCredits`) and stay well-formed;
* the router's maps, the registry and the pause flag are unchanged.

Restoration is full, not best-effort. -/
def Properties.RegisteredDepositBundleFullyRecovered : Prop :=
  ∀ (A : Type) (enc : AssetIdOf) (cfg : Config) (vault : Addr160) (base : AssetId)
    (tr : TrackerHook A) (dep : DeployHook A) (other : OtherTargets (Ledgers A)) (dest : Chain)
    (w : World (Ledgers A)) (calls : List Call) (ds : List Deposit),
    w.paused = false → DepositBundle cfg calls ds → ds ≠ [] →
    (∀ d ∈ ds, w.vault.token d.1 ≠ 0) → (trackerRun tr dest w.rest.tracker ds).isSome →
    CreditsCovered vault base cfg.thisChain w.vault w.rest.token ds →
      ∃ w', claimRefund (recoverCall enc cfg (localHooks vault base tr dep) other dest)
          LegState.Revertable w calls = some (LegState.Reverted, w')
        ∧ recoverBundle (recoverCall enc cfg (localHooks vault base tr dep) other dest) w calls
            = some (w', calls.length)
        ∧ w'.router = w.router ∧ w'.vault = w.vault ∧ w'.paused = w.paused
        ∧ ExactCredits vault cfg.thisChain w.vault w.rest.token w'.rest.token ds
        ∧ ∀ tok, BridgedStandardERC20.WellFormed (w.rest.token tok) →
            BridgedStandardERC20.WellFormed (w'.rest.token tok)

/-! ## Pause -/

/-- **A PAUSED VAULT BLOCKS EVERY DEPOSIT REFUND.**  Whatever the hooks: while the vault is paused
(`whenNotPaused`, `NativeTokenVaultBase.sol:217`), the claim of a nonempty router-deposit bundle
reverts.  The leg stays `Revertable`. -/
def Properties.PausedVaultBlocksDepositClaim : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (other : OtherTargets X)
    (dest : Chain) (w : World X) (calls : List Call),
    w.paused = true → calls ≠ [] → (∀ c ∈ calls, RouterDepositShaped cfg c) →
      claimRefund (recoverCall enc cfg hk other dest) LegState.Revertable w calls = none

/-- **PAUSE ONLY DELAYS A FULL RECOVERY.**  Under the premises of
`RegisteredDepositBundleFullyRecovered`, the same world with the vault paused cannot be claimed:
the claim reverts and the leg stays `Revertable`.  Once unpaused, the claim succeeds and recovers
every call. -/
def Properties.PauseOnlyDelaysFullRecovery : Prop :=
  ∀ (A : Type) (enc : AssetIdOf) (cfg : Config) (vault : Addr160) (base : AssetId)
    (tr : TrackerHook A) (dep : DeployHook A) (other : OtherTargets (Ledgers A)) (dest : Chain)
    (w : World (Ledgers A)) (calls : List Call) (ds : List Deposit),
    w.paused = false → DepositBundle cfg calls ds → ds ≠ [] →
    (∀ d ∈ ds, w.vault.token d.1 ≠ 0) → (trackerRun tr dest w.rest.tracker ds).isSome →
    CreditsCovered vault base cfg.thisChain w.vault w.rest.token ds →
      claimRefund (recoverCall enc cfg (localHooks vault base tr dep) other dest)
          LegState.Revertable { w with paused := true } calls = none
      ∧ ∃ w', claimRefund (recoverCall enc cfg (localHooks vault base tr dep) other dest)
            LegState.Revertable w calls = some (LegState.Reverted, w')
          ∧ recoverBundle (recoverCall enc cfg (localHooks vault base tr dep) other dest) w calls
              = some (w', calls.length)

/-! ## The preparation trace -/

/-- **WHAT THE TRACE KEEPS TRUE OF PENDING OBLIGATIONS.**  From a well-formed vault with nothing
pending, after any preparation trace, every pending obligation:
* is for the vault's tracked asset;
* names a nonzero depositor as `originalCaller`;
* was prepared under a configuration in scope for preparation (`PendingSound`). -/
def Properties.PendingObligationsSound : Prop :=
  ∀ (Acc : Type) (hooks : NativeTokenVaultBase.Hooks Acc) (s t : Ledger Acc),
    NativeTokenVaultBase.WellFormed s.vault → s.pending = [] → Reach hooks s t → PendingSound t

/-- **HEADLINE: A BUNDLE OF DEPOSITS PREPARED ON THIS CHAIN IS RESTORED IN FULL.**

The setting.  A preparation trace (`Specs/Model.lean`: preparations and ordinary transfers) runs
from a well-formed vault with nothing pending to `t`.  The manager's world `w` matches it:
* its registry corresponds to `t`'s vault (`NativeTokenVaultBase.Corr`);
* its ledger of the tracked token is `t`'s token;
* its vault is unpaused;
* its token calls behave as the local token model, with `t`'s vault address as caller.

The premises:
* the bundle's calls are router deposits carrying the nonempty list `obs` of pending obligations,
  each at most as often as it is pending (`obs` is a sub-multiset of `t.pending`);
* the tracker run on them succeeds.

The conclusions:
* the claim succeeds and the loop recovers every call;
* the router's maps, the registry, the pause flag and every other token's ledger are unchanged;
* on the tracked token, the configuration is kept, each account `u` gains exactly
  `pendingAmountFor u obs`, and total supply rises by exactly `pendingAmount obs`;
* the token stays well-formed;
* the supply plus whatever remains pending equals the supply before the trace.  If `obs` is the
  whole pending list, the starting supply is restored exactly.

No supply-headroom premise is needed: the trace's conservation provides it. -/
def Properties.PreparedBundleFullyRecovered : Prop :=
  ∀ (Acc : Type) (hooks : NativeTokenVaultBase.Hooks Acc) (s t : Ledger Acc),
    NativeTokenVaultBase.WellFormed s.vault → s.pending = [] → Reach hooks s t →
  ∀ (A : Type) (enc : AssetIdOf) (cfg : Config) (base : AssetId) (tr : TrackerHook A)
    (dep : DeployHook A) (other : OtherTargets (Ledgers A)) (dest : Chain)
    (w : World (Ledgers A)) (calls : List Call) (obs : List Obligation),
    obs ≠ [] → obs.Subperm t.pending → DepositBundle cfg calls (obs.map obligationDeposit) →
    w.paused = false → NativeTokenVaultBase.Corr t.vault cfg.thisChain w.vault →
    w.rest.token (NativeTokenVaultBase.widen t.vault.config.tokenAddress) = t.vault.token →
    (trackerRun tr dest w.rest.tracker (obs.map obligationDeposit)).isSome →
      ∃ w', claimRefund (recoverCall enc cfg (localHooks t.vault.config.vault base tr dep) other dest)
          LegState.Revertable w calls = some (LegState.Reverted, w')
        ∧ recoverBundle (recoverCall enc cfg (localHooks t.vault.config.vault base tr dep) other
            dest) w calls = some (w', calls.length)
        ∧ w'.router = w.router ∧ w'.vault = w.vault ∧ w'.paused = w.paused
        ∧ (∀ tok, tok ≠ NativeTokenVaultBase.widen t.vault.config.tokenAddress →
            w'.rest.token tok = w.rest.token tok)
        ∧ (w'.rest.token (NativeTokenVaultBase.widen t.vault.config.tokenAddress)).config =
            t.vault.token.config
        ∧ (∀ u, (w'.rest.token (NativeTokenVaultBase.widen t.vault.config.tokenAddress)).balances u
            = t.vault.token.balances u + pendingAmountFor u obs)
        ∧ (w'.rest.token (NativeTokenVaultBase.widen t.vault.config.tokenAddress)).totalSupply
            = t.vault.token.totalSupply + pendingAmount obs
        ∧ BridgedStandardERC20.WellFormed
            (w'.rest.token (NativeTokenVaultBase.widen t.vault.config.tokenAddress))
        ∧ ∀ rest : List Obligation, (obs ++ rest).Perm t.pending →
            (w'.rest.token (NativeTokenVaultBase.widen t.vault.config.tokenAddress)).totalSupply
              + pendingAmount rest = s.vault.token.totalSupply

/-! ## Countermodels: why each premise is there -/

/-- **WITHOUT "ROUTER ONLY", A TERMINAL LEG CAN BE PARTIAL.**  In the local token model there is
an atomic bundle of two zero-value calls, which `_validateAtomicBundle` admits.  The first is a
router deposit that is refunded.  The second goes to another target that returns `false`, as a
call with nothing to reverse does (`AtomicFlowManager.sol:208-211`).  The claim succeeds, so the
leg is `Reverted` and terminal, but the loop recovered one call of two. -/
def Properties.DecliningCallMakesTerminalPartial : Prop :=
  ∃ (A : Type) (enc : AssetIdOf) (cfg : Config) (vault : Addr160) (base : AssetId)
    (tr : TrackerHook A) (dep : DeployHook A) (other : OtherTargets (Ledgers A)) (dest : Chain)
    (w w' : World (Ledgers A)) (calls : List Call),
    AtomicBundleValid calls ∧ calls.length = 2
    ∧ claimRefund (recoverCall enc cfg (localHooks vault base tr dep) other dest)
        LegState.Revertable w calls = some (LegState.Reverted, w')
    ∧ recoverBundle (recoverCall enc cfg (localHooks vault base tr dep) other dest) w calls
        = some (w', 1)
    ∧ outcomes (recoverCall enc cfg (localHooks vault base tr dep) other dest) w calls
        = [Outcome.recovered, Outcome.declined]

/-- **WITHOUT THE TOKEN MODEL, "RECOVERED" IS NOT "CREDITED".**  The setting is unpaused,
registered and bridged, and the tracker returns, but the token's `bridgeMint` returns without
crediting anyone.  The one-deposit claim succeeds and counts its call as recovered, while the
depositor's balance is unchanged although the amount is nonzero. -/
def Properties.NonStandardTokenCountedButNotCredited : Prop :=
  ∃ (enc : AssetIdOf) (cfg : Config) (hk : Hooks (Ledgers Unit)) (other : OtherTargets (Ledgers Unit))
    (dest : Chain) (w w' : World (Ledgers Unit)) (calls : List Call) (d : Deposit),
    w.paused = false ∧ DepositBundle cfg calls [d] ∧ w.vault.token d.1 ≠ 0
    ∧ w.vault.originChain d.1 ≠ cfg.thisChain ∧ d.2.amount ≠ 0 ∧ d.2.originalCaller ≠ 0
    ∧ claimRefund (recoverCall enc cfg hk other dest) LegState.Revertable w calls
        = some (LegState.Reverted, w')
    ∧ recoverBundle (recoverCall enc cfg hk other dest) w calls = some (w', calls.length)
    ∧ (w'.rest.token (w.vault.token d.1)).balances d.2.originalCaller
        = (w.rest.token (w.vault.token d.1)).balances d.2.originalCaller

/-- **PER-CALL HEADROOM IS NOT ENOUGH FOR A BUNDLE.**  Every deposit of a two-deposit bundle meets,
on its own and on the same well-formed starting ledger, the conditions under which a single
refund succeeds.  These are the conditions of `NativeTokenVaultBase.Properties.RecoverEnabled`,
restated on this model's ledgers:
* a bridged asset with a registered token whose minter is the vault;
* a nonzero original caller;
* `totalSupply + amount < 2^256`.

The vault is unpaused and the tracker returns, yet the bundle's claim reverts: the two re-mints on
the one token together pass `2^256`.  `CreditsCovered` therefore totals the headroom per token
over the whole bundle.  For deposits prepared on this chain, the trace's conservation provides
that total (`PreparedBundleFullyRecovered`). -/
def Properties.JointHeadroomNeeded : Prop :=
  ∃ (A : Type) (enc : AssetIdOf) (cfg : Config) (vault : Addr160) (base : AssetId)
    (tr : TrackerHook A) (dep : DeployHook A) (other : OtherTargets (Ledgers A)) (dest : Chain)
    (w : World (Ledgers A)) (calls : List Call) (ds : List Deposit),
    w.paused = false ∧ DepositBundle cfg calls ds ∧ ds.length = 2 ∧ vault ≠ 0
    ∧ (trackerRun tr dest w.rest.tracker ds).isSome
    ∧ (∀ d ∈ ds, w.vault.token d.1 ≠ 0 ∧ w.vault.originChain d.1 ≠ cfg.thisChain
        ∧ d.2.originalCaller ≠ 0 ∧ (w.rest.token (w.vault.token d.1)).config.vault = vault
        ∧ BridgedStandardERC20.WellFormed (w.rest.token (w.vault.token d.1))
        ∧ (w.rest.token (w.vault.token d.1)).totalSupply + d.2.amount.val < UInt256.size)
    ∧ claimRefund (recoverCall enc cfg (localHooks vault base tr dep) other dest)
        LegState.Revertable w calls = none

/-! ## Witnesses -/

/-- **THE WORLD-LEVEL PREMISES ARE JOINTLY SATISFIABLE, NONTRIVIALLY.**  One world meets every
premise of `RegisteredDepositBundleFullyRecovered`, and with them those of:
* `DepositRefundIsCredits` and `DepositClaimIffCredits`;
* `CreditsCoveredSucceedExactly`, `CreditsPreserveLedgers` and `TrackerAlwaysReturnsRuns`;
* `PauseOnlyDelaysFullRecovery`.

The bundle is a two-call atomic bundle of zero-value router calls (`_validateAtomicBundle` admits
it): one native and one bridged deposit, with nonzero amounts.  The tracker changes state.  Its
claim succeeds, which meets the premises of `TerminalIsFullIffNoDecline` and
`DepositBundleClaimIsFull`.  The same world with the vault paused (`{ w with paused := true }`)
meets those of `PausedVaultBlocksDepositClaim`: its calls are nonempty and router-deposit
shaped. -/
def Properties.FullRecoverySatisfiable : Prop :=
  ∃ (A : Type) (enc : AssetIdOf) (cfg : Config) (vault : Addr160) (base : AssetId)
    (tr : TrackerHook A) (dep : DeployHook A) (other : OtherTargets (Ledgers A)) (dest : Chain)
    (w w' : World (Ledgers A)) (calls : List Call) (ds : List Deposit),
    w.paused = false ∧ DepositBundle cfg calls ds ∧ ds ≠ [] ∧ (∀ d ∈ ds, w.vault.token d.1 ≠ 0)
    ∧ (trackerRun tr dest w.rest.tracker ds).isSome
    ∧ (∀ d ∈ ds, ∀ t, (tr t dest d.1 d.2.amount).isSome)
    ∧ CreditsCovered vault base cfg.thisChain w.vault w.rest.token ds
    ∧ (∀ tok, BridgedStandardERC20.WellFormed (w.rest.token tok))
    ∧ AtomicBundleValid calls ∧ ds.length = 2
    ∧ (∃ d ∈ ds, w.vault.originChain d.1 = cfg.thisChain)
    ∧ (∃ d ∈ ds, w.vault.originChain d.1 ≠ cfg.thisChain)
    ∧ (∀ d ∈ ds, d.2.amount ≠ 0)
    ∧ trackerRun tr dest w.rest.tracker ds ≠ some w.rest.tracker
    ∧ (∀ c ∈ calls, RouterDepositShaped cfg c)
    ∧ (creditRun vault base cfg.thisChain w.vault w.rest.token ds).isSome
    ∧ claimRefund (recoverCall enc cfg (localHooks vault base tr dep) other dest)
        LegState.Revertable w calls = some (LegState.Reverted, w')
    ∧ calls ≠ []

/-- **THE TRACE-LEVEL PREMISES ARE JOINTLY SATISFIABLE, NONTRIVIALLY.**  One trace and one world
meet every premise of `PreparedBundleFullyRecovered`, and with them those of
`PendingObligationsSound`:
* the trace has two preparations, by two different depositors;
* the bundle carries both obligations;
* the tracker changes state. -/
def Properties.PreparedBundleFullyRecoveredSatisfiable : Prop :=
  ∃ (Acc : Type) (hooks : NativeTokenVaultBase.Hooks Acc) (s t : Ledger Acc)
    (A : Type) (cfg : Config) (tr : TrackerHook A) (dest : Chain)
    (w : World (Ledgers A)) (calls : List Call) (obs : List Obligation),
    NativeTokenVaultBase.WellFormed s.vault ∧ s.pending = [] ∧ Reach hooks s t
    ∧ obs ≠ [] ∧ obs.Subperm t.pending ∧ DepositBundle cfg calls (obs.map obligationDeposit)
    ∧ w.paused = false ∧ NativeTokenVaultBase.Corr t.vault cfg.thisChain w.vault
    ∧ w.rest.token (NativeTokenVaultBase.widen t.vault.config.tokenAddress) = t.vault.token
    ∧ (trackerRun tr dest w.rest.tracker (obs.map obligationDeposit)).isSome
    ∧ obs.length = 2
    ∧ (∃ o₁ ∈ obs, ∃ o₂ ∈ obs, o₁.data.originalCaller ≠ o₂.data.originalCaller)
    ∧ trackerRun tr dest w.rest.tracker (obs.map obligationDeposit) ≠ some w.rest.tracker

end AssetBridgePreparation.FullRecovery
