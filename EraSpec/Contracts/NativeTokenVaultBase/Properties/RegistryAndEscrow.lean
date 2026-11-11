import EraSpec.Contracts.NativeTokenVaultBase.Specs.RegistryAndEscrow

/-!
# Properties: the native token vault

Statements about `EraSpec.Contracts.NativeTokenVaultBase.Specs.RegistryAndEscrow`.  Proofs are in
`EraSpec.Contracts.NativeTokenVaultBase.Proofs.RegistryAndEscrow`.

## The registry

The source states the registry's coherence as an assumption in a comment
("it is assumed, that `originChainId`, `tokenAddress` and `assetId` mappings are
always atomically populated").  `RunValid` makes it an inductive invariant of every
run from fresh storage.

The interesting step is `RegisterNativeIdFresh`.  `_registerToken` guards only on
the token being unregistered; it never checks that the asset id is free, so on the
face of it a registration could clobber a live asset.  It cannot, because the id is
`keccak(chainid, NTV, token)` — id-freshness follows from token-freshness through
injectivity.  The proof uses three invariant fields to get there (`idShape`,
`nativeToken`, `inverse`), which is a fair measure of how much the one-sided guard
is leaning on the rest of the registry.

## The escrow ledger

`Solvency` is the headline: at every point of every run, what is recorded as
bridged out never exceeds what the vault holds.  `GuardedInflowIsBacked` is the
consequence that matters at the moment of payout — an inbound flow that passes
`InsufficientChainBalance` is covered by escrow — and `UnguardedInflowUnbacked`
shows what that check is worth by exhibiting a reachable state where dropping it
pays out from an empty vault.

`SurplusMonotone` is the same fact from the other side: `escrowed - bridgedOut`
never decreases, so funds that were never bridged out — including direct transfers
into the vault — cannot be drained by bridge traffic.

`NoInflation` is the flow-level statement: for an asset native to this chain, the
total ever bridged in never exceeds the total ever bridged out.  It follows from
`LedgerIsNetFlow`, which says the ledger is exactly the difference.

## And what the ledger does not do

`PerChainIsolationFails` is the honest other half.  The outbound hook takes the
chain id as an unnamed parameter and the ledger is aggregated, so one chain can
withdraw against another chain's deposit: an explicit two-chain run where the books
balance in aggregate while chain `cA` takes out an asset it never deposited.  The
source is explicit that this is the design ("there is no on-chain per-chain balance
enforcement"; correctness of minted amounts rests on the sending chain's ZK proofs),
so this theorem is not a defect report — it is the boundary of what the vault's own
arithmetic protects, stated so a reader does not assume more.
-/

namespace Contracts.NativeTokenVault

/-! ## The registry -/

/-- Fresh storage satisfies the registry invariant. -/
def Properties.EmptyValid : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain), Valid e thisChain empty.vault

/-- **THE DERIVED ID IS FREE.**  In a valid vault, a token that is unregistered has
an unregistered asset id — so `_registerToken`'s one-sided guard cannot clobber a
live asset.  This is what the id being `keccak(chainid, NTV, token)` buys. -/
def Properties.RegisterNativeIdFresh : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain) (V : Vault),
    Valid e thisChain V → ∀ (t : Address), RegisterNativeGuard V t →
      ¬ Registered V (e thisChain t)

/-- Registering a token native to this chain preserves the registry invariant. -/
def Properties.RegisterNativePreservesValid : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (V : Vault), Valid e thisChain V → ∀ (t : Address), RegisterNativeGuard V t →
      Valid e thisChain (registerNative e thisChain V t)

/-- Registering a token native elsewhere preserves it too. -/
def Properties.RegisterBridgedPreservesValid : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (V : Vault), Valid e thisChain V →
    ∀ (a : AssetId) (t ot : Address) (origin : Chain),
      RegisterBridgedGuard e thisChain V a t ot origin →
      Valid e thisChain (registerBridged V a t ot origin)

/-- Every operation preserves it. -/
def Properties.StepPreservesValid : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W X : World), Step e thisChain W X → Valid e thisChain W.vault →
      Valid e thisChain X.vault

/-- **THE REGISTRY IS COHERENT ALONG EVERY RUN.**  The comment, as an invariant. -/
def Properties.RunValid : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W : World), Reach e thisChain empty W → Valid e thisChain W.vault

/-! ## Solvency -/

/-- **SOLVENCY.**  At every point of every run, the amount recorded as bridged out
never exceeds the amount the vault holds. -/
def Properties.Solvency : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W : World), Reach e thisChain empty W →
      ∀ a, W.vault.bridgedOut a ≤ W.vault.escrowed a

/-- **A PERMITTED PAYOUT IS COVERED.**  An inbound flow that passes
`InsufficientChainBalance` asks for no more than the vault holds. -/
def Properties.GuardedInflowIsBacked : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain) (V : Vault), Valid e thisChain V →
    ∀ (a : AssetId) (amt : ℕ), FlowInGuard thisChain V a amt → Native thisChain V a →
      amt ≤ V.escrowed a

/-- **THE SURPLUS NEVER SHRINKS.**  `escrowed - bridgedOut` is non-decreasing, so
funds that were never bridged out — direct transfers into the vault included —
cannot be taken by bridge traffic. -/
def Properties.SurplusMonotone : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W X : World), Step e thisChain W X → Valid e thisChain W.vault →
      ∀ a, W.vault.escrowed a - W.vault.bridgedOut a
        ≤ X.vault.escrowed a - X.vault.bridgedOut a

/-! ## The flow ledger -/

/-- The audit invariant holds along every run. -/
def Properties.RunAudited : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W : World), Reach e thisChain empty W → Audited thisChain W

/-- **THE LEDGER IS THE NET FLOW.**  For a native asset, `bridgedOut` is exactly
total-out minus total-in. -/
def Properties.LedgerIsNetFlow : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W : World), Reach e thisChain empty W → ∀ a, Native thisChain W.vault a →
      W.vault.bridgedOut a + W.audit.totalIn a = W.audit.totalOut a

/-- **NO INFLATION.**  For an asset native to this chain, no more was ever bridged
in than was bridged out. -/
def Properties.NoInflation : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W : World), Reach e thisChain empty W → ∀ a, Native thisChain W.vault a →
      W.audit.totalIn a ≤ W.audit.totalOut a

/-! ## The two boundaries -/

/-- **THE `InsufficientChainBalance` CHECK IS LOAD-BEARING.**  There is a reachable,
valid state — one native token registered, nothing yet bridged out — in which the
check rejects an inbound flow of one unit and, without it, the vault would release
a unit it never received. -/
def Properties.UnguardedInflowUnbacked : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (t : Address), t ≠ 0 →
      ∃ W : World, Reach e thisChain empty W ∧ Valid e thisChain W.vault
        ∧ Registered W.vault (e thisChain t)
        ∧ Native thisChain W.vault (e thisChain t)
        ∧ W.vault.escrowed (e thisChain t) = 0
        ∧ FlowInGuardUnchecked W.vault (e thisChain t) 1
        ∧ ¬ FlowInGuard thisChain W.vault (e thisChain t) 1

/-- **PER-CHAIN ISOLATION DOES NOT HOLD.**  A two-chain run in which the aggregate
books balance exactly, yet chain `cA` bridged in an asset that only chain `cB` ever
had bridged out to it.

The ledger carries no chain index — `_handleBridgeToChain`'s chain parameter is
unnamed — so this is by design, with the sending chain's ZK proof standing where a
per-chain balance would. Stated here so that `Solvency` is not read as more than it
is. -/
def Properties.PerChainIsolationFails : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain),
    ∀ (t : Address), t ≠ 0 → ∀ (cA cB : Chain), cA ≠ cB →
      ∃ W : World, Reach e thisChain empty W
        ∧ W.audit.totalIn (e thisChain t) = W.audit.totalOut (e thisChain t)
        ∧ W.audit.outTo cA (e thisChain t) = 0
        ∧ W.audit.innFrom cA (e thisChain t) = 1


/-! ## `IdAssumptions` is unsatisfiable

Added during the consolidation (ASSUMPTIONS `CRYPTO-ID`).  `inj` asks an encoding
into `UInt256` to be injective on all pairs of 256-bit words, which counting rules
out, so every property here taking `IdAssumptions` is vacuously true as stated. -/
def Properties.IdAssumptionsUnsatisfiable : Prop :=
  ∀ (e : NtvAssetId), ¬ IdAssumptions e

/-! ## Repaired forms: the hash assumption bounded to the run's own pairs

Every property above that takes `IdAssumptions` is restated here with
`IdAssumptionsOn e S` — injective and nonzero only on an explicit set `S` of
(chain, token) pairs — over runs whose registrations hash pairs of `S`
(`ReachIn`).  `IdAssumptionsOnSatisfiable` says any `S` smaller than the id space
admits such an encoding.  OPEN: that a given run is a `ReachIn` run for a SMALL `S`
(its own registered pairs) needs a trace-level statement; "some finite `S`" alone is
trivially true (`S := univ`), so it was not stated.  The satisfiability
of the full premise lists, on concrete nontrivial instances, is
`RunOnSatisfiable` / `RegisterNativeOnSatisfiable` / `RegisterBridgedOnSatisfiable`. -/

/-- **THE BOUNDED ASSUMPTION IS SATISFIABLE.**  For any finite set of pairs smaller
than the id space, some encoding is injective and nonzero on it. -/
def Properties.IdAssumptionsOnSatisfiable : Prop :=
  ∀ (S : Finset (Chain × Address)), S.card < UInt256.size →
    ∃ e : NtvAssetId, IdAssumptionsOn e ↑S

/-- A bounded run is a run. -/
def Properties.ReachInIsReach : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain) (S : Set (Chain × Address)) (W X : World),
    ReachIn e thisChain S W X → Reach e thisChain W X

/-- **THE DERIVED ID IS FREE, under injectivity on the pairs at hand.**  As
`RegisterNativeIdFresh`, with `e` injective and nonzero only on a set `S` holding
the new pair `(thisChain, t)` and the pairs of the already-registered assets. -/
def Properties.RegisterNativeIdFreshOn : Prop :=
  ∀ (e : NtvAssetId) (S : Set (Chain × Address)), IdAssumptionsOn e S →
    ∀ (thisChain : Chain) (V : Vault), Valid e thisChain V → PairsIn S V →
    ∀ (t : Address), (thisChain, t) ∈ S → RegisterNativeGuard V t →
      ¬ Registered V (e thisChain t)

/-- **THE DERIVED ID IS FREE, OR A PINNED COLLISION.**  No hash assumption at all:
either the id `_registerToken` computes for `t` is unregistered, or it hashed to the
unset sentinel, or it is already the id of an asset whose recorded
(origin chain, origin token) pair differs from `(thisChain, t)` yet hashes to the
same id.  All colliding inputs are named by the instance: the pair `(thisChain, t)`
and the recorded pair of the asset at `e thisChain t`. -/
def Properties.RegisterNativeIdFreshOrCollision : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain) (V : Vault), Valid e thisChain V →
    ∀ (t : Address), RegisterNativeGuard V t →
      ¬ Registered V (e thisChain t)
      ∨ e thisChain t = 0
      ∨ (Registered V (e thisChain t)
          ∧ (V.originChain (e thisChain t), V.originToken (e thisChain t)) ≠ (thisChain, t)
          ∧ e (V.originChain (e thisChain t)) (V.originToken (e thisChain t)) = e thisChain t)

/-- **THE COLLISION DISJUNCTS ARE NOT A TAUTOLOGY.**  A valid vault with one asset
registered, a second token passing the guard, and both collision disjuncts of
`RegisterNativeIdFreshOrCollision` false. -/
def Properties.RegisterNativeCollisionNotTautology : Prop :=
  ∃ (e : NtvAssetId) (thisChain : Chain) (V : Vault) (t : Address),
    Valid e thisChain V ∧ (∃ a, Registered V a) ∧ RegisterNativeGuard V t
    ∧ ¬ (e thisChain t = 0)
    ∧ ¬ (Registered V (e thisChain t)
          ∧ (V.originChain (e thisChain t), V.originToken (e thisChain t)) ≠ (thisChain, t)
          ∧ e (V.originChain (e thisChain t)) (V.originToken (e thisChain t)) = e thisChain t)

/-- **…AND THEY ARE NEEDED.**  With an encoding that collides, a valid vault and a
token passing the one-sided guard whose derived id is already taken — so the
`RegisterNativeIdFresh` conclusion fails without some assumption on `e`, and it is
the pinned-collision disjunct that holds. -/
def Properties.RegisterNativeCollisionReachable : Prop :=
  ∃ (e : NtvAssetId) (thisChain : Chain) (V : Vault) (t : Address),
    Valid e thisChain V ∧ RegisterNativeGuard V t ∧ Registered V (e thisChain t)
    ∧ (V.originChain (e thisChain t), V.originToken (e thisChain t)) ≠ (thisChain, t)
    ∧ e (V.originChain (e thisChain t)) (V.originToken (e thisChain t)) = e thisChain t

/-- Registering a native token preserves the registry invariant and the pair
bound, under injectivity on `S`. -/
def Properties.RegisterNativePreservesValidOn : Prop :=
  ∀ (e : NtvAssetId) (S : Set (Chain × Address)), IdAssumptionsOn e S →
    ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (V : Vault), Valid e thisChain V → PairsIn S V →
    ∀ (t : Address), (thisChain, t) ∈ S → RegisterNativeGuard V t →
      Valid e thisChain (registerNative e thisChain V t)
        ∧ PairsIn S (registerNative e thisChain V t)

/-- Registering a bridged token preserves them too. -/
def Properties.RegisterBridgedPreservesValidOn : Prop :=
  ∀ (e : NtvAssetId) (S : Set (Chain × Address)), IdAssumptionsOn e S →
    ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (V : Vault), Valid e thisChain V → PairsIn S V →
    ∀ (a : AssetId) (t ot : Address) (origin : Chain), (origin, ot) ∈ S →
      RegisterBridgedGuard e thisChain V a t ot origin →
      Valid e thisChain (registerBridged V a t ot origin)
        ∧ PairsIn S (registerBridged V a t ot origin)

/-- Every bounded step preserves them. -/
def Properties.StepInPreservesValidOn : Prop :=
  ∀ (e : NtvAssetId) (S : Set (Chain × Address)), IdAssumptionsOn e S →
    ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W X : World), StepIn e thisChain S W X →
      Valid e thisChain W.vault → PairsIn S W.vault →
      Valid e thisChain X.vault ∧ PairsIn S X.vault

/-- **THE REGISTRY IS COHERENT ALONG EVERY RUN**, with the id hash injective and
nonzero only on the pairs the run registers. -/
def Properties.RunValidOn : Prop :=
  ∀ (e : NtvAssetId) (S : Set (Chain × Address)), IdAssumptionsOn e S →
    ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W : World), ReachIn e thisChain S empty W → Valid e thisChain W.vault

/-- **SOLVENCY**, under injectivity on the run's own pairs. -/
def Properties.SolvencyOn : Prop :=
  ∀ (e : NtvAssetId) (S : Set (Chain × Address)), IdAssumptionsOn e S →
    ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W : World), ReachIn e thisChain S empty W →
      ∀ a, W.vault.bridgedOut a ≤ W.vault.escrowed a

/-- **THE SURPLUS NEVER SHRINKS**, with no hash assumption: `SurplusMonotone` never
used its `IdAssumptions` premise. -/
def Properties.SurplusMonotoneNoHash : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain) (W X : World), Step e thisChain W X →
    Valid e thisChain W.vault →
      ∀ a, W.vault.escrowed a - W.vault.bridgedOut a
        ≤ X.vault.escrowed a - X.vault.bridgedOut a

/-- The audit invariant along every bounded run. -/
def Properties.RunAuditedOn : Prop :=
  ∀ (e : NtvAssetId) (S : Set (Chain × Address)), IdAssumptionsOn e S →
    ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W : World), ReachIn e thisChain S empty W → Audited thisChain W

/-- **THE LEDGER IS THE NET FLOW**, under injectivity on the run's own pairs. -/
def Properties.LedgerIsNetFlowOn : Prop :=
  ∀ (e : NtvAssetId) (S : Set (Chain × Address)), IdAssumptionsOn e S →
    ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W : World), ReachIn e thisChain S empty W → ∀ a, Native thisChain W.vault a →
      W.vault.bridgedOut a + W.audit.totalIn a = W.audit.totalOut a

/-- **NO INFLATION**, under injectivity on the run's own pairs. -/
def Properties.NoInflationOn : Prop :=
  ∀ (e : NtvAssetId) (S : Set (Chain × Address)), IdAssumptionsOn e S →
    ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W : World), ReachIn e thisChain S empty W → ∀ a, Native thisChain W.vault a →
      W.audit.totalIn a ≤ W.audit.totalOut a

/-- **THE `InsufficientChainBalance` CHECK IS LOAD-BEARING**, with the only hash
fact the witness needs: the one id it registers is nonzero. -/
def Properties.UnguardedInflowUnbackedOn : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain), thisChain ≠ 0 →
    ∀ (t : Address), t ≠ 0 → e thisChain t ≠ 0 →
      ∃ W : World, ReachIn e thisChain {(thisChain, t)} empty W ∧ Valid e thisChain W.vault
        ∧ Registered W.vault (e thisChain t)
        ∧ Native thisChain W.vault (e thisChain t)
        ∧ W.vault.escrowed (e thisChain t) = 0
        ∧ FlowInGuardUnchecked W.vault (e thisChain t) 1
        ∧ ¬ FlowInGuard thisChain W.vault (e thisChain t) 1

/-! ### Anti-vacuity: the premises of the `…On` results hold on concrete instances -/

/-- **THE RUN-LEVEL PREMISES ARE SATISFIABLE, NONTRIVIALLY.**  An encoding, a pair
set and a run satisfying every premise of `RunValidOn` / `SolvencyOn` /
`RunAuditedOn` / `LedgerIsNetFlowOn` / `NoInflationOn`, in which a native asset is
registered and has been bridged both out and in. -/
def Properties.RunOnSatisfiable : Prop :=
  ∃ (e : NtvAssetId) (S : Set (Chain × Address)) (thisChain : Chain) (W : World),
    IdAssumptionsOn e S ∧ thisChain ≠ 0 ∧ ReachIn e thisChain S empty W
    ∧ ∃ a, Registered W.vault a ∧ Native thisChain W.vault a
      ∧ W.audit.totalOut a ≠ 0 ∧ W.audit.totalIn a ≠ 0

/-- **THE NATIVE-REGISTRATION PREMISES ARE SATISFIABLE**, on a vault that already
holds an asset — every premise of `RegisterNativeIdFreshOn` and
`RegisterNativePreservesValidOn`. -/
def Properties.RegisterNativeOnSatisfiable : Prop :=
  ∃ (e : NtvAssetId) (S : Set (Chain × Address)) (thisChain : Chain) (V : Vault)
    (t : Address),
    IdAssumptionsOn e S ∧ thisChain ≠ 0 ∧ Valid e thisChain V ∧ PairsIn S V
    ∧ (∃ a, Registered V a) ∧ (thisChain, t) ∈ S ∧ RegisterNativeGuard V t

/-- **THE BRIDGED-REGISTRATION PREMISES ARE SATISFIABLE** — every premise of
`RegisterBridgedPreservesValidOn`. -/
def Properties.RegisterBridgedOnSatisfiable : Prop :=
  ∃ (e : NtvAssetId) (S : Set (Chain × Address)) (thisChain : Chain) (V : Vault)
    (a : AssetId) (t ot : Address) (origin : Chain),
    IdAssumptionsOn e S ∧ thisChain ≠ 0 ∧ Valid e thisChain V ∧ PairsIn S V
    ∧ (origin, ot) ∈ S ∧ RegisterBridgedGuard e thisChain V a t ot origin

end Contracts.NativeTokenVault
