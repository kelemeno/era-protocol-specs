import EraSpec.Codegen.VaultPreparationSlice.Specs.L1PerChainCapAtV35
import EraSpec.Codegen.VaultPreparationSlice.Properties.Refinement

/-!
# Properties: the vault slice on L1 at draft/v0.35.0, and the per-chain balance cap

Statements about `Specs/L1PerChainCapAtV35.lean` (pin `b17415d20`). Proofs:
`../Proofs/L1PerChainCapAtV35.lean`.

## The slice at v35

* `L1HooksAgreeAtV35`: the v35 L1 accounting hook, run on the cap storage, agrees with its
  model hook; the metadata hooks agree when `MetadataAgreesV35` says so. So each result of
  `Properties/Refinement.lean`, all of which quantify over hooks satisfying `HooksAgree`,
  applies at v35 on L1 with `l1HooksV35` under `MetadataAgreesV35`;
  `L1BridgeBurnRefinesAtV35` states the headline `BridgeBurnRefines` instance.
* `L1PrepareAtV35IsPinPlusCredit`: for an asset whose origin in the hook environment is not
  the environment's chain, the model's preparation with the v35 hook is the one with the pin's
  hook, with the accounting state replaced by the v35 hook's result, or rejected when that hook
  fails. `L1HookFailsOnlyOnDepositOverflowAtV35`: for such an asset the hook fails exactly when
  the tracked deposit counter would overflow, with `Panic(0x11)`.
* `L1BridgeBurnAtV35IsPinCallPlusCredit`: the same comparison for the program call itself,
  with no model state: the v35 call is the pin's call plus the v35 hook's credit, and reverts
  with exactly that hook's failure when it fails.
* `L1BridgeBurnCreditsJournalEntryAtV35`: a successful program `bridgeBurn` with the v35 hook
  changes the cap storage by exactly the deposit its journal entry stands for, and nothing
  else; no model state, no `Rel`, only `EnvMatchesV35`.
* `L1SliceStepIsCapStepAtV35`: every slice step leaves the cap storage alone or is one
  `CapStepV35` step, so the cap results below apply to slice runs interleaved with other cap
  steps.
* `L1SliceRunCreditsJournalAtV35`: along any slice run, the vault's storage never changes
  and the deposit counters grow by exactly the journal's deposits (`journalDepositsV35`).
* `L1SliceDepositsBackedByBurnsAtV35`: with the premises of `ReachableJournalBacked`, the
  deposits under any set of keys plus the token's supply slot never exceed their starting
  total, so the deposits credited along the run, summed over any set of keys, are at most the
  decrease of the supply slot.

## The cap's own runs (`CapStepV35`)

* `InteropPoolKeyOutsideChainIdsV35`: the pinned premise holds for the transcribed constant.
* `CappedWithdrawalWithinLimitV35`: a successful `_handleBridgeFromChain` on a tracked,
  non-pending key ends with that key's withdrawals at most its deposits plus backfill.
  `CappedWithdrawalSucceedsIffWithinLimitV35` is the exact condition for success, so the cap
  blocks nothing within the limit; `PendingWithdrawalUncappedV35` the condition while the key's
  backfill is pending, where only overflow (and `bridgedOut`) limits it.
* `CapCountersMonotoneV35`: no step lowers a deposit, withdrawal or backfill counter or clears
  a pool flag.
* `PoolNeverOverdrawnV35`: along every run, from any state satisfying `PoolInvV35` (fresh
  storage does), the pool is never pending, has no backfill, and has withdrawn at most what
  was deposited into it, per asset. No premise on the owner.
* `CoveredRunsKeepCapV35`: along runs whose `markBackfilled` steps close only covered chains,
  `CapInvV35` (with `PoolInvV35`) is kept.
* `UncoveredCloseBreaksCapV35` (countermodel): without that discipline `CapInvV35` fails on
  a run from fresh storage, so the premise of `CoveredRunsKeepCapV35` is needed.

## Not claimed

Nothing about the native-token and base-token branches of `bridgeBurn` beyond the hook step,
about `bridgeMint` or the recovery paths beyond their hook step, or about the routing that
decides which hook runs. Nothing that needs interop to be one-way: `CapStepV35` lets every
step choose its interop flags, so no statement here relates a chain's own counters to the
pool's after a move. `_trackedBalance`'s view calls are assumed to return (`DEP-RESULTS`).
-/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.BridgedStandardERC20 (Address)
open Contracts.NativeTokenVaultBase (State Request prepare WellFormed)

/-! ## The pool constant -/

/-- **THE POOL KEY IS NO CHAIN ID.** `PoolKeyOutsideChainIdsV35` holds for
`interopPoolChainIdV35`, the transcribed value of `INTEROP_POOL_CHAIN_ID`. -/
def Properties.InteropPoolKeyOutsideChainIdsV35 : Prop :=
  PoolKeyOutsideChainIdsV35 interopPoolChainIdV35

/-! ## The slice at v35 -/

/-- **THE V35 L1 HOOKS AGREE WITH THEIR MODEL.** The accounting halves are the same function
(`handleBridgeToChainV35`), so they agree on every input; with agreeing metadata
implementations the hooks satisfy `HooksAgree`. -/
def Properties.L1HooksAgreeAtV35 : Prop :=
  ∀ (env : CapEnvV35) (md : Storage → Word → Except XFailure Bytes)
    (mdm : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes),
    MetadataAgreesV35 md mdm → HooksAgree (l1HooksV35 env md) (l1ModelHooksV35 env mdm)

/-- **`bridgeBurn` IS THE MODEL'S `prepare` ON L1 AT V35.** `BridgeBurnRefines` with the v35
L1 hooks: under agreeing metadata, a well-formed model state and a storage representing it,
the model (with the cap's deposit credit) rejects iff the program reverts; on acceptance the
program succeeds without writing the vault's storage, reaches a related state (its cap storage
is the model's accounting state), returns exactly the encoded mint tuple, and emits exactly
`prepareLogs`. -/
def Properties.L1BridgeBurnRefinesAtV35 : Prop :=
  ∀ (d : Deployment) (env : CapEnvV35) (md : Storage → Word → Except XFailure Bytes)
    (mdm : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes) (st : Storage)
    (w : World CapStateV35) (s : State CapStateV35) (r : Request),
    MetadataAgreesV35 md mdm → WellFormed s → Rel d st w s →
    (prepare (l1ModelHooksV35 env mdm) s r = none →
      ∃ e, xcall (d.machine (l1HooksV35 env md)) vaultProgram "bridgeBurn"
        (d.env r.caller r.msgValue) (requestArgs r) st w = some (.error e)) ∧
    (∀ out, prepare (l1ModelHooksV35 env mdm) s r = some out →
      ∃ res, xcall (d.machine (l1HooksV35 env md)) vaultProgram "bridgeBurn"
          (d.env r.caller r.msgValue) (requestArgs r) st w = some (.ok res) ∧
        res.st = st ∧ Rel d res.st res.w out.state ∧
        res.ret = some (.bytes (encodeMintData out.data)) ∧ res.logs = prepareLogs d r)

/-- **V35 IS THE PIN PLUS THE DEPOSIT CREDIT.** For an asset whose origin chain in the hook
environment is not the environment's chain (L1), the model's preparation with the v35 hook is:
the preparation with the pin's hook (which leaves the accounting state alone for such an asset),
then the v35 hook on the pre-call accounting state; it fails if either fails, and on success
differs from the pin's only in the accounting state, which is the v35 hook's result. -/
def Properties.L1PrepareAtV35IsPinPlusCredit : Prop :=
  ∀ (env : CapEnvV35) (mdm : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes)
    (s : State CapStateV35) (r : Request),
    env.originChainId r.assetId ≠ env.chainId →
    prepare (l1ModelHooksV35 env mdm) s r =
      (prepare (l1ModelHooksPin env mdm) s r).bind fun out =>
        (handleBridgeToChainV35 env s.accounting r.destinationChain r.assetId
            r.data.amount).toOption.map
          fun acc => { out with state := { out.state with accounting := acc } }

/-- **THE V35 HOOK FAILS ONLY ON A DEPOSIT OVERFLOW.** For an asset whose origin in the hook
environment is not the environment's chain, `_handleBridgeToChain` fails iff the asset is
tracked for the destination and its deposit counter under the tracking key plus the amount
reaches `2^256` (in `ℕ`); every failure carries `Panic(0x11)`. -/
def Properties.L1HookFailsOnlyOnDepositOverflowAtV35 : Prop :=
  ∀ (env : CapEnvV35) (s : CapStateV35) (chain asset amount : Word),
    env.originChainId asset ≠ env.chainId →
    (∀ e, handleBridgeToChainV35 env s chain asset amount = .error e →
      e = .data (.panic panicOverflow)) ∧
    ((∃ e, handleBridgeToChainV35 env s chain asset amount = .error e) ↔
      (trackedBalanceV35 env chain (env.originChainId asset)).1 = true ∧
      UInt256.size ≤
        (s.deposited (trackedBalanceV35 env chain (env.originChainId asset)).2 asset).val +
          amount.val)

/-- **THE V35 CALL IS THE PIN'S CALL PLUS THE CREDIT**, for the program, with no model state and
no `Rel`. Compare a `bridgeBurn` call under the v35 L1 hooks with the same call, from the same
storages, under the pin's L1 hook (`l1HooksPin`, same metadata implementation). If the pin's
call succeeds, its returned amount word is some `amount`, and the v35 call reverts with exactly
the failure of `handleBridgeToChainV35` on the call's destination, asset and `amount` when that
fails, and otherwise succeeds with the pin's result except the cap storage, which is that
function's result. Conversely, when the hook environment is the deployment's, a successful v35
call has a successful pin call with the same result except the cap storage, which is the
starting one. -/
def Properties.L1BridgeBurnAtV35IsPinCallPlusCredit : Prop :=
  ∀ (d : Deployment) (env : CapEnvV35) (md : Storage → Word → Except XFailure Bytes)
    (st : Storage) (w : World CapStateV35) (caller : Address) (value c l2v a oc : Word)
    (data : Bytes),
    (∀ res, xcall (d.machine (l1HooksPin env md)) vaultProgram "bridgeBurn" (d.env caller value)
        [.word c, .word l2v, .word a, .word oc, .bytes data] st w = some (.ok res) →
      ∃ amount : Word, mintAmount res.ret = amount.val ∧
        (∀ err, handleBridgeToChainV35 env w.acct c a amount = .error err →
          xcall (d.machine (l1HooksV35 env md)) vaultProgram "bridgeBurn" (d.env caller value)
            [.word c, .word l2v, .word a, .word oc, .bytes data] st w = some (.error err)) ∧
        (∀ acc, handleBridgeToChainV35 env w.acct c a amount = .ok acc →
          xcall (d.machine (l1HooksV35 env md)) vaultProgram "bridgeBurn" (d.env caller value)
            [.word c, .word l2v, .word a, .word oc, .bytes data] st w =
              some (.ok { res with w := { res.w with acct := acc } }))) ∧
    (EnvMatchesV35 env d st →
      ∀ res, xcall (d.machine (l1HooksV35 env md)) vaultProgram "bridgeBurn" (d.env caller value)
          [.word c, .word l2v, .word a, .word oc, .bytes data] st w = some (.ok res) →
        xcall (d.machine (l1HooksPin env md)) vaultProgram "bridgeBurn" (d.env caller value)
          [.word c, .word l2v, .word a, .word oc, .bytes data] st w =
            some (.ok { res with w := { res.w with acct := w.acct } }))

/-- **A SUCCESSFUL `bridgeBurn` CREDITS EXACTLY ITS JOURNAL ENTRY.** Any successful program call
with the v35 L1 hooks, whose hook environment is the deployment's (`EnvMatchesV35`), leaves the
vault's storage unchanged, returns mint data of nonzero amount, leaves `bridgedOut`, the
withdrawals, the backfills, the pool flags and the pending flags unchanged, and adds to each
`chainTotalDeposited[key][asset]` exactly `entryDepositV35` of the entry the journal records
for the call: the returned amount at the key the destination is tracked under, for the call's
asset, and nothing elsewhere. The equation is in `ℕ`, so the counter did not wrap. -/
def Properties.L1BridgeBurnCreditsJournalEntryAtV35 : Prop :=
  ∀ (d : Deployment) (env : CapEnvV35) (md : Storage → Word → Except XFailure Bytes)
    (st : Storage) (w : World CapStateV35) (caller : Address) (value c l2v a oc : Word)
    (data : Bytes) (res : XSuccess (World CapStateV35)),
    EnvMatchesV35 env d st →
    xcall (d.machine (l1HooksV35 env md)) vaultProgram "bridgeBurn" (d.env caller value)
      [.word c, .word l2v, .word a, .word oc, .bytes data] st w = some (.ok res) →
    res.st = st ∧ 0 < mintAmount res.ret ∧
    res.w.acct.bridgedOut = w.acct.bridgedOut ∧ res.w.acct.withdrawn = w.acct.withdrawn ∧
    res.w.acct.backfill = w.acct.backfill ∧ res.w.acct.inPool = w.acct.inPool ∧
    res.w.acct.pending = w.acct.pending ∧
    ∀ key asset, (res.w.acct.deposited key asset).val =
      (w.acct.deposited key asset).val + entryDepositV35 env key asset ⟨c, a, res.ret⟩

/-- **EVERY SLICE STEP IS A CAP STEP OR LEAVES THE CAP ALONE.** With the v35 L1 hooks and an
environment matching the deployment and the current vault storage, a step of the slice's `Step`
either leaves the cap storage unchanged or moves it by one `CapStepV35 env.pool` step. -/
def Properties.L1SliceStepIsCapStepAtV35 : Prop :=
  ∀ (d : Deployment) (env : CapEnvV35) (md : Storage → Word → Except XFailure Bytes)
    (sys sys' : Sys CapStateV35),
    EnvMatchesV35 env d sys.vault → Step d (l1HooksV35 env md) sys sys' →
    sys'.world.acct = sys.world.acct ∨ CapStepV35 env.pool sys.world.acct sys'.world.acct

/-- **ALONG A SLICE RUN, THE DEPOSIT COUNTERS ARE THE JOURNAL.** With the v35 L1 hooks and an
environment matching the deployment and the starting vault storage, along any run of the
slice's `Step`: the vault's storage never changes, the journal only grows, `bridgedOut`, the
withdrawals, the backfills, the pool flags and the pending flags never change, and each
`chainTotalDeposited[key][asset]` grows by exactly `journalDepositsV35` of the entries
appended (in `ℕ`). -/
def Properties.L1SliceRunCreditsJournalAtV35 : Prop :=
  ∀ (d : Deployment) (env : CapEnvV35) (md : Storage → Word → Except XFailure Bytes)
    (sys₀ sys : Sys CapStateV35),
    EnvMatchesV35 env d sys₀.vault →
    LayeredVerification.Run (Step d (l1HooksV35 env md)) sys₀ sys →
    sys.vault = sys₀.vault ∧
    sys.world.acct.bridgedOut = sys₀.world.acct.bridgedOut ∧
    sys.world.acct.withdrawn = sys₀.world.acct.withdrawn ∧
    sys.world.acct.backfill = sys₀.world.acct.backfill ∧
    sys.world.acct.inPool = sys₀.world.acct.inPool ∧
    sys.world.acct.pending = sys₀.world.acct.pending ∧
    ∃ new, sys.journal = sys₀.journal ++ new ∧
      ∀ key asset, (sys.world.acct.deposited key asset).val =
        (sys₀.world.acct.deposited key asset).val + journalDepositsV35 env key asset new

/-- **THE CREDITED DEPOSITS ARE BACKED BY THE SUPPLY DECREASE.** With the premises of
`ReachableJournalBacked` at the v35 L1 hooks (agreeing metadata, a well-formed model state
represented by the starting storages, an empty journal) and an environment matching the
deployment: along any run, for any finite set of keys and any asset, the deposits the cap holds
under those keys plus the token's supply slot are at most their starting values' sum. -/
def Properties.L1SliceDepositsBackedByBurnsAtV35 : Prop :=
  ∀ (d : Deployment) (env : CapEnvV35) (md : Storage → Word → Except XFailure Bytes)
    (mdm : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes)
    (s₀ : State CapStateV35) (sys₀ sys : Sys CapStateV35),
    MetadataAgreesV35 md mdm → WellFormed s₀ → Rel d sys₀.vault sys₀.world s₀ →
    EnvMatchesV35 env d sys₀.vault → sys₀.journal = [] →
    LayeredVerification.Run (Step d (l1HooksV35 env md)) sys₀ sys →
    ∀ (keys : Finset Word) (asset : Word),
      (∑ k ∈ keys, (sys.world.acct.deposited k asset).val) +
          (sys.world.token.scalars "_totalSupply").val ≤
        (∑ k ∈ keys, (sys₀.world.acct.deposited k asset).val) +
          (sys₀.world.token.scalars "_totalSupply").val

/-! ## The cap's own runs -/

/-- **A CAPPED WITHDRAWAL STAYS WITHIN THE LIMIT.** If `_handleBridgeFromChain` succeeds and the
asset is tracked for the chain under a key whose backfill is not pending, the key's withdrawals
grew by exactly the amount (in `ℕ`) and are now at most its deposits plus backfill (in `ℕ`). -/
def Properties.CappedWithdrawalWithinLimitV35 : Prop :=
  ∀ (env : CapEnvV35) (s t : CapStateV35) (chain asset amount : Word),
    handleBridgeFromChainV35 env s chain asset amount = .ok t →
    (trackedBalanceV35 env chain (env.originChainId asset)).1 = true →
    s.pending (trackedBalanceV35 env chain (env.originChainId asset)).2 = false →
    (t.withdrawn (trackedBalanceV35 env chain (env.originChainId asset)).2 asset).val =
      (s.withdrawn (trackedBalanceV35 env chain (env.originChainId asset)).2 asset).val +
        amount.val ∧
    (t.withdrawn (trackedBalanceV35 env chain (env.originChainId asset)).2 asset).val ≤
      (t.deposited (trackedBalanceV35 env chain (env.originChainId asset)).2 asset).val +
        (t.backfill (trackedBalanceV35 env chain (env.originChainId asset)).2 asset).val

/-- **WHEN A CAPPED WITHDRAWAL SUCCEEDS, EXACTLY.** For an asset tracked for the chain under a
key whose backfill is not pending, `_handleBridgeFromChain` succeeds iff: for an asset native to
the environment's chain, the amount is at most `bridgedOut`; the key's withdrawals plus the amount
are at most its deposits plus backfill; and deposits plus backfill are below `2^256` (all in
`ℕ`). So the cap blocks nothing within the limit. -/
def Properties.CappedWithdrawalSucceedsIffWithinLimitV35 : Prop :=
  ∀ (env : CapEnvV35) (s : CapStateV35) (chain asset amount : Word),
    (trackedBalanceV35 env chain (env.originChainId asset)).1 = true →
    s.pending (trackedBalanceV35 env chain (env.originChainId asset)).2 = false →
    ((∃ t, handleBridgeFromChainV35 env s chain asset amount = .ok t) ↔
      (env.originChainId asset = env.chainId → amount.val ≤ (s.bridgedOut asset).val) ∧
      (s.withdrawn (trackedBalanceV35 env chain (env.originChainId asset)).2 asset).val +
          amount.val ≤
        (s.deposited (trackedBalanceV35 env chain (env.originChainId asset)).2 asset).val +
          (s.backfill (trackedBalanceV35 env chain (env.originChainId asset)).2 asset).val ∧
      (s.deposited (trackedBalanceV35 env chain (env.originChainId asset)).2 asset).val +
          (s.backfill (trackedBalanceV35 env chain (env.originChainId asset)).2 asset).val <
        UInt256.size)

/-- **WHILE PENDING, ONLY OVERFLOW LIMITS A WITHDRAWAL.** For an asset tracked for the chain under
a key whose backfill is pending, `_handleBridgeFromChain` succeeds iff: for an asset native to the
environment's chain, the amount is at most `bridgedOut`; and the key's withdrawals plus the amount
are below `2^256`. On success the withdrawals grew by exactly the amount (in `ℕ`). -/
def Properties.PendingWithdrawalUncappedV35 : Prop :=
  ∀ (env : CapEnvV35) (s : CapStateV35) (chain asset amount : Word),
    (trackedBalanceV35 env chain (env.originChainId asset)).1 = true →
    s.pending (trackedBalanceV35 env chain (env.originChainId asset)).2 = true →
    ((∃ t, handleBridgeFromChainV35 env s chain asset amount = .ok t) ↔
      (env.originChainId asset = env.chainId → amount.val ≤ (s.bridgedOut asset).val) ∧
      (s.withdrawn (trackedBalanceV35 env chain (env.originChainId asset)).2 asset).val +
          amount.val < UInt256.size) ∧
    ∀ t, handleBridgeFromChainV35 env s chain asset amount = .ok t →
      (t.withdrawn (trackedBalanceV35 env chain (env.originChainId asset)).2 asset).val =
        (s.withdrawn (trackedBalanceV35 env chain (env.originChainId asset)).2 asset).val +
          amount.val

/-- **THE COUNTERS ONLY GROW.** Along every run of `CapStepV35`, for every key and asset, the
deposits, the withdrawals and the backfill never decrease (in `ℕ`), and a balance once marked as
moved to the pool stays marked. -/
def Properties.CapCountersMonotoneV35 : Prop :=
  ∀ (pool : Word) (s t : CapStateV35), LayeredVerification.Run (CapStepV35 pool) s t →
    ∀ key asset, (s.deposited key asset).val ≤ (t.deposited key asset).val ∧
      (s.withdrawn key asset).val ≤ (t.withdrawn key asset).val ∧
      (s.backfill key asset).val ≤ (t.backfill key asset).val ∧
      (s.inPool key asset = true → t.inPool key asset = true)

/-- **THE POOL IS NEVER OVERDRAWN.** For a pool key outside the chain ids, `PoolInvV35` holds at
the end of every run of `CapStepV35` that starts in a state satisfying it: the pool is never
pending, never has a backfill, and for every asset its withdrawals are at most its deposits. -/
def Properties.PoolNeverOverdrawnV35 : Prop :=
  ∀ (pool : Word), PoolKeyOutsideChainIdsV35 pool →
    ∀ s t : CapStateV35, PoolInvV35 pool s →
      LayeredVerification.Run (CapStepV35 pool) s t → PoolInvV35 pool t

/-- **DISCIPLINED RUNS KEEP THE CAP.** For a pool key outside the chain ids, along every run of
`CoveredCapStepV35` (each `markBackfilled` closes only a covered chain) from a state satisfying
`CapInvV35` and `PoolInvV35`, both hold at the end: every non-pending key has withdrawn at most
its deposits plus backfill, per asset. -/
def Properties.CoveredRunsKeepCapV35 : Prop :=
  ∀ (pool : Word), PoolKeyOutsideChainIdsV35 pool →
    ∀ s t : CapStateV35, CapInvV35 s → PoolInvV35 pool s →
      LayeredVerification.Run (CoveredCapStepV35 pool) s t → CapInvV35 t ∧ PoolInvV35 pool t

/-- **WITHOUT THE DISCIPLINE THE CAP INVARIANT FAILS** (countermodel). With the real pool
constant: some run of `CapStepV35` from fresh storage ends in a state where some key whose
backfill is not pending has, for some asset, withdrawn more than its deposits plus backfill; so
`CoveredRunsKeepCapV35` with `CapStepV35` in place of `CoveredCapStepV35` is false. (The proof's
run: `initializeUpgrade` lists chain 5, chain 5 withdraws 3 units while pending, then
`markBackfilled(5)` with no backfill set.) -/
def Properties.UncoveredCloseBreaksCapV35 : Prop :=
  (∃ t : CapStateV35,
    LayeredVerification.Run (CapStepV35 interopPoolChainIdV35) CapStateV35.zero t ∧
      ¬ CapInvV35 t) ∧
  ¬ (∀ s t : CapStateV35, CapInvV35 s → PoolInvV35 interopPoolChainIdV35 s →
      LayeredVerification.Run (CapStepV35 interopPoolChainIdV35) s t → CapInvV35 t)

/-! ## Witnesses: the premises above are satisfiable, non-trivially -/

/-- **AGREEING METADATA EXISTS** for every model metadata hook (run it on the token state the
storage represents). -/
def Properties.L1MetadataAgreementSatisfiableAtV35 : Prop :=
  ∀ mdm : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes,
    ∃ md : Storage → Word → Except XFailure Bytes, MetadataAgreesV35 md mdm

/-- **A REPRESENTED STATE, A SUCCESSFUL CALL, A NONZERO CREDIT.** The premises of
`L1BridgeBurnRefinesAtV35` (with a request the model accepts), of
`L1BridgeBurnCreditsJournalEntryAtV35`, `L1SliceStepIsCapStepAtV35`,
`L1SliceRunCreditsJournalAtV35`, `L1SliceDepositsBackedByBurnsAtV35` and both halves of
`L1BridgeBurnAtV35IsPinCallPlusCredit` hold together, with the real pool key: a successful
`bridgeBurn` from the represented storage strictly raises a deposit counter, the same call with
the pin's hook succeeds, and the one-call run from an empty journal is a slice run. -/
def Properties.L1SliceCreditWitnessAtV35 : Prop :=
  ∃ (d : Deployment) (env : CapEnvV35) (md : Storage → Word → Except XFailure Bytes)
    (mdm : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes)
    (s : State CapStateV35) (r : Request) (out : Contracts.NativeTokenVaultBase.Result CapStateV35)
    (st : Storage) (w : World CapStateV35) (res : XSuccess (World CapStateV35)) (key : Word),
    MetadataAgreesV35 md mdm ∧ WellFormed s ∧ Rel d st w s ∧ EnvMatchesV35 env d st ∧
    env.pool = interopPoolChainIdV35 ∧
    prepare (l1ModelHooksV35 env mdm) s r = some out ∧
    xcall (d.machine (l1HooksV35 env md)) vaultProgram "bridgeBurn" (d.env r.caller r.msgValue)
      (requestArgs r) st w = some (.ok res) ∧
    (w.acct.deposited key r.assetId).val < (res.w.acct.deposited key r.assetId).val ∧
    (∃ res', xcall (d.machine (l1HooksPin env md)) vaultProgram "bridgeBurn"
      (d.env r.caller r.msgValue) (requestArgs r) st w = some (.ok res')) ∧
    LayeredVerification.Run (Step d (l1HooksV35 env md)) ⟨st, w, []⟩
      ⟨res.st, res.w, [⟨r.destinationChain, r.assetId, res.ret⟩]⟩

/-- **THE NEW REVERT IS REACHABLE.** The premises of `L1BridgeBurnRefinesAtV35`,
`L1PrepareAtV35IsPinPlusCredit`, `L1HookFailsOnlyOnDepositOverflowAtV35` and the first half of
`L1BridgeBurnAtV35IsPinCallPlusCredit` hold for a request that the model accepts with the pin's
hook and rejects with the v35 hook (so, by the first three, the destination's deposit counter
would overflow): the program call with the pin's hook succeeds, and with the v35 hook it reverts
with `Panic(0x11)`. -/
def Properties.L1DepositOverflowWitnessAtV35 : Prop :=
  ∃ (d : Deployment) (env : CapEnvV35) (md : Storage → Word → Except XFailure Bytes)
    (mdm : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes)
    (s : State CapStateV35) (r : Request) (st : Storage) (w : World CapStateV35),
    MetadataAgreesV35 md mdm ∧ WellFormed s ∧ Rel d st w s ∧ EnvMatchesV35 env d st ∧
    env.originChainId r.assetId ≠ env.chainId ∧
    (prepare (l1ModelHooksPin env mdm) s r).isSome ∧ prepare (l1ModelHooksV35 env mdm) s r = none ∧
    (∃ res, xcall (d.machine (l1HooksPin env md)) vaultProgram "bridgeBurn"
      (d.env r.caller r.msgValue) (requestArgs r) st w = some (.ok res)) ∧
    xcall (d.machine (l1HooksV35 env md)) vaultProgram "bridgeBurn"
      (d.env r.caller r.msgValue) (requestArgs r) st w =
        some (.error (.data (.panic panicOverflow)))

/-- **A CAPPED WITHDRAWAL, AND ONE OVER THE LIMIT.** The premises of
`CappedWithdrawalWithinLimitV35` hold with a nonzero amount, and the same call for one unit more
reverts with `ChainBalanceExceeded`. -/
def Properties.CappedWithdrawalWitnessV35 : Prop :=
  ∃ (env : CapEnvV35) (s t : CapStateV35) (chain asset amount limit : Word),
    handleBridgeFromChainV35 env s chain asset amount = .ok t ∧
    (trackedBalanceV35 env chain (env.originChainId asset)).1 = true ∧
    s.pending (trackedBalanceV35 env chain (env.originChainId asset)).2 = false ∧ amount ≠ 0 ∧
    handleBridgeFromChainV35 env s chain asset (amount + 1) =
      .error (.data (.custom "ChainBalanceExceeded" [chain, asset, amount + 1, limit]))

/-- **AN UNCAPPED WITHDRAWAL WHILE PENDING.** The premises of `PendingWithdrawalUncappedV35` hold
for a successful withdrawal after which the key has withdrawn more than its deposits plus
backfill. -/
def Properties.PendingWithdrawalWitnessV35 : Prop :=
  ∃ (env : CapEnvV35) (s t : CapStateV35) (chain asset amount : Word),
    (trackedBalanceV35 env chain (env.originChainId asset)).1 = true ∧
    s.pending (trackedBalanceV35 env chain (env.originChainId asset)).2 = true ∧
    handleBridgeFromChainV35 env s chain asset amount = .ok t ∧
    (t.deposited (trackedBalanceV35 env chain (env.originChainId asset)).2 asset).val +
        (t.backfill (trackedBalanceV35 env chain (env.originChainId asset)).2 asset).val <
      (t.withdrawn (trackedBalanceV35 env chain (env.originChainId asset)).2 asset).val

/-- **A POOL RUN THAT WITHDRAWS.** Fresh storage satisfies `PoolInvV35` for the real pool key, and
some run of `CapStepV35` from it ends with nonzero withdrawals from the pool. (The proof's run: a
deposit to a chain with interop, then a withdrawal from it.) -/
def Properties.PoolRunWitnessV35 : Prop :=
  PoolInvV35 interopPoolChainIdV35 CapStateV35.zero ∧
    ∃ (t : CapStateV35) (asset : Word),
      LayeredVerification.Run (CapStepV35 interopPoolChainIdV35) CapStateV35.zero t ∧
      0 < (t.withdrawn interopPoolChainIdV35 asset).val

/-- **A DISCIPLINED RUN THAT USES THE BACKFILL.** Fresh storage satisfies `CapInvV35` and
`PoolInvV35` for the real pool key, and some run of `CoveredCapStepV35` from it ends with a chain
that is not pending, has a nonzero backfill and has withdrawn more than its deposits, in some
asset (by `CoveredRunsKeepCapV35` the backfill covers the difference). (The proof's run: the
upgrade marks chain 5 pending, it withdraws, its backfill is set and its window closed, then a
deposit and a capped withdrawal.) -/
def Properties.CoveredRunWitnessV35 : Prop :=
  CapInvV35 CapStateV35.zero ∧ PoolInvV35 interopPoolChainIdV35 CapStateV35.zero ∧
    ∃ (t : CapStateV35) (chain asset : Word),
      LayeredVerification.Run (CoveredCapStepV35 interopPoolChainIdV35) CapStateV35.zero t ∧
      t.pending chain = false ∧ 0 < (t.backfill chain asset).val ∧
      (t.deposited chain asset).val < (t.withdrawn chain asset).val

end Codegen.VaultPreparationSlice
