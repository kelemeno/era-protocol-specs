import EraSpec.Contracts.NativeTokenVault

/-!
# Properties: the native token vault

Statements about `EraSpec.Contracts.NativeTokenVault`.  Proofs are in
`EraSpec.Proofs.NativeTokenVault`.

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

namespace Properties.NativeTokenVault

open Contracts.NativeTokenVault

/-! ## The registry -/

/-- Fresh storage satisfies the registry invariant. -/
def EmptyValid : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain), Valid e thisChain empty.vault

/-- **THE DERIVED ID IS FREE.**  In a valid vault, a token that is unregistered has
an unregistered asset id — so `_registerToken`'s one-sided guard cannot clobber a
live asset.  This is what the id being `keccak(chainid, NTV, token)` buys. -/
def RegisterNativeIdFresh : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain) (V : Vault),
    Valid e thisChain V → ∀ (t : Address), RegisterNativeGuard V t →
      ¬ Registered V (e thisChain t)

/-- Registering a token native to this chain preserves the registry invariant. -/
def RegisterNativePreservesValid : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (V : Vault), Valid e thisChain V → ∀ (t : Address), RegisterNativeGuard V t →
      Valid e thisChain (registerNative e thisChain V t)

/-- Registering a token native elsewhere preserves it too. -/
def RegisterBridgedPreservesValid : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (V : Vault), Valid e thisChain V →
    ∀ (a : AssetId) (t ot : Address) (origin : Chain),
      RegisterBridgedGuard e thisChain V a t ot origin →
      Valid e thisChain (registerBridged V a t ot origin)

/-- Every operation preserves it. -/
def StepPreservesValid : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W X : World), Step e thisChain W X → Valid e thisChain W.vault →
      Valid e thisChain X.vault

/-- **THE REGISTRY IS COHERENT ALONG EVERY RUN.**  The comment, as an invariant. -/
def RunValid : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W : World), Reach e thisChain empty W → Valid e thisChain W.vault

/-! ## Solvency -/

/-- **SOLVENCY.**  At every point of every run, the amount recorded as bridged out
never exceeds the amount the vault holds. -/
def Solvency : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W : World), Reach e thisChain empty W →
      ∀ a, W.vault.bridgedOut a ≤ W.vault.escrowed a

/-- **A PERMITTED PAYOUT IS COVERED.**  An inbound flow that passes
`InsufficientChainBalance` asks for no more than the vault holds. -/
def GuardedInflowIsBacked : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain) (V : Vault), Valid e thisChain V →
    ∀ (a : AssetId) (amt : ℕ), FlowInGuard thisChain V a amt → Native thisChain V a →
      amt ≤ V.escrowed a

/-- **THE SURPLUS NEVER SHRINKS.**  `escrowed - bridgedOut` is non-decreasing, so
funds that were never bridged out — direct transfers into the vault included —
cannot be taken by bridge traffic. -/
def SurplusMonotone : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W X : World), Step e thisChain W X → Valid e thisChain W.vault →
      ∀ a, W.vault.escrowed a - W.vault.bridgedOut a
        ≤ X.vault.escrowed a - X.vault.bridgedOut a

/-! ## The flow ledger -/

/-- The audit invariant holds along every run. -/
def RunAudited : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W : World), Reach e thisChain empty W → Audited thisChain W

/-- **THE LEDGER IS THE NET FLOW.**  For a native asset, `bridgedOut` is exactly
total-out minus total-in. -/
def LedgerIsNetFlow : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W : World), Reach e thisChain empty W → ∀ a, Native thisChain W.vault a →
      W.vault.bridgedOut a + W.audit.totalIn a = W.audit.totalOut a

/-- **NO INFLATION.**  For an asset native to this chain, no more was ever bridged
in than was bridged out. -/
def NoInflation : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (W : World), Reach e thisChain empty W → ∀ a, Native thisChain W.vault a →
      W.audit.totalIn a ≤ W.audit.totalOut a

/-! ## The two boundaries -/

/-- **THE `InsufficientChainBalance` CHECK IS LOAD-BEARING.**  There is a reachable,
valid state — one native token registered, nothing yet bridged out — in which the
check rejects an inbound flow of one unit and, without it, the vault would release
a unit it never received. -/
def UnguardedInflowUnbacked : Prop :=
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
def PerChainIsolationFails : Prop :=
  ∀ (e : NtvAssetId), IdAssumptions e → ∀ (thisChain : Chain), thisChain ≠ 0 →
    ∀ (t : Address), t ≠ 0 → ∀ (cA cB : Chain), cA ≠ cB →
      ∃ W : World, Reach e thisChain empty W
        ∧ W.audit.totalIn (e thisChain t) = W.audit.totalOut (e thisChain t)
        ∧ W.audit.outTo cA (e thisChain t) = 0
        ∧ W.audit.innFrom cA (e thisChain t) = 1

end Properties.NativeTokenVault
