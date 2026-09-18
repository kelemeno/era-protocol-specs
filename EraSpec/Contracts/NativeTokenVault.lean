import Mathlib.Tactic
import EraSpec.Word

/-!
# Model: `NativeTokenVault` — the asset registry and the escrow ledger

The vault holds this chain's native tokens that have been bridged away, and mints
or burns local representations of tokens native elsewhere.  Two things in it are
worth stating precisely, and this file models both.

**This file is definitions only.**  The results are in
`EraSpec.Properties.NativeTokenVault` and proved in
`EraSpec.Proofs.NativeTokenVault`.

## 1. The registry, and a documented assumption

`NativeTokenVaultBase` carries three mappings and the same comment three times:

    /// @dev A mapping assetId => originChainId
    /// @dev It is assumed, that `originChainId`, `tokenAddress` and `assetId`
    /// mappings are always atomically populated

That is an assumption in a comment, and `_setNewTokenStorage` is the only writer.
`Valid` below states what the three maps must satisfy, and
`Properties.NativeTokenVault.RegisterNativePreservesValid` turns the comment into
an inductive invariant.

The load-bearing part is subtler than atomicity.  `_registerToken` guards only on
the TOKEN being unregistered (`assetId[_nativeToken] == 0`), not on the asset id
being free.  Nothing stops the write from clobbering an id that is already in use
— nothing, that is, except the id being derived from the token:

    newAssetId = DataEncoding.encodeNTVAssetId(block.chainid, _nativeToken)
               = keccak256(abi.encode(block.chainid, L2_NATIVE_TOKEN_VAULT_ADDR, _nativeToken))

So id-freshness is a *consequence* of token-freshness plus keccak injectivity, via
the `idShape` invariant.  That is what `RegisterNativePreservesValid` proves, and it
is why the one-sided guard is enough.

## 2. The escrow ledger, and what it does NOT guarantee

`bridgedOut[assetId]` is the net amount of a this-chain-native asset currently away.
`_handleBridgeToChain` increases it on the way out, `_handleBridgeFromChain`
decreases it on the way in and reverts with `InsufficientChainBalance` if the
inbound amount exceeds it.  Both are no-ops for assets native elsewhere, which are
minted and burned rather than escrowed.

Note the signature of the outbound hook:

    function _handleBridgeToChain(uint256, bytes32 _assetId, uint256 _amount) internal override

The chain id is **unnamed** — the ledger is aggregated over all chains.  The source
says so outright:

    /// - Correctness of the minted amounts is guaranteed by the ZK proofs of the sending chain
    /// (plus 2FA on ZKsync OS chains); there is no on-chain per-chain balance enforcement.

So the vault's own arithmetic guarantees *aggregate* solvency and not per-chain
isolation.  `Audit` below records the per-chain and total flows the contract does
**not** keep, purely so that both halves of that sentence can be stated:
`NoInflation` is what the ledger buys, and `PerChainIsolationFails` is what it does
not, with an explicit two-chain run.

## What is assumed about the token

`escrowed` is not vault storage — it is the token contract's balance of the vault.
Modelling it as an exact counter assumes the token moves exactly the requested
amount, which the vault enforces on the way in
(`_depositFunds` compares balances and reverts with `TokensWithFeesNotSupported`)
and relies on for the base token (`require(_depositAmount == msg.value)`).  A
fee-on-transfer or rebasing token is outside the model, and outside what the
contract supports.
-/

namespace Contracts.NativeTokenVault

open Clear

/-- Chain ids, asset ids and addresses, all as 256-bit words.  `0` is the zero
address and the unset value of every mapping, exactly as in Solidity. -/
abbrev Chain := UInt256
abbrev AssetId := UInt256
abbrev Address := UInt256

/-- Point update of a mapping. -/
def upd {β : Type} (f : AssetId → β) (a : AssetId) (v : β) : AssetId → β :=
  fun x => if x = a then v else f x

/-- Point update of an address-keyed mapping. -/
def updA {β : Type} (f : Address → β) (t : Address) (v : β) : Address → β :=
  fun x => if x = t then v else f x

/-- Point update of a chain-and-asset-keyed mapping. -/
def updCA (f : Chain → AssetId → ℕ) (c : Chain) (a : AssetId) (v : ℕ) : Chain → AssetId → ℕ :=
  fun x y => if x = c ∧ y = a then v else f x y

/-! ## The asset id -/

/-- `DataEncoding.encodeNTVAssetId(chainId, token)`, i.e.
`keccak256(abi.encode(chainId, L2_NATIVE_TOKEN_VAULT_ADDR, token))`.  The vault
address is a constant, so the id is a function of the chain and the token. -/
abbrev NtvAssetId := Chain → Address → AssetId

/-- What the asset-id hash is assumed to do.  Both fields are keccak idealizations,
of the same kind used for node and flow hashes elsewhere in this package. -/
structure IdAssumptions (e : NtvAssetId) : Prop where
  /-- Distinct (chain, token) pairs get distinct asset ids. -/
  inj : ∀ c₁ t₁ c₂ t₂, e c₁ t₁ = e c₂ t₂ → c₁ = c₂ ∧ t₁ = t₂
  /-- No asset id collides with the mappings' unset sentinel.  The vault reads
  `assetId[token] == bytes32(0)` as "unregistered", so an id that hashed to zero
  would be indistinguishable from an absent one — and its token would stay
  re-registerable forever. -/
  nonzero : ∀ c t, e c t ≠ 0

/-! ## State -/

/-- The vault's registry and ledger, plus the escrow it actually holds.

The first four fields are storage.  `originToken` and `escrowed` are not: the
origin token is `tokenAddress[assetId]` for a native asset and is read back from
the bridged token (`IBridgedStandardToken.originToken()`) otherwise, and `escrowed`
is the token contract's balance of the vault.  Both are carried because the
guarantees are about them — see the header. -/
structure Vault where
  /-- `originChainId[assetId]`; `0` means unregistered. -/
  originChain : AssetId → Chain
  /-- `tokenAddress[assetId]`; `0` means unregistered. -/
  token : AssetId → Address
  /-- `assetId[tokenAddress]`; `0` means unregistered. -/
  assetOf : Address → AssetId
  /-- `bridgedOut[assetId]`: net amount of a this-chain-native asset currently away. -/
  bridgedOut : AssetId → ℕ
  /-- The token on the asset's ORIGIN chain (see above). -/
  originToken : AssetId → Address
  /-- What the vault holds for the asset (see above). -/
  escrowed : AssetId → ℕ

/-- The per-chain and total flows the contract does **not** record.  Present only
so that `Properties.NativeTokenVault` can state what the aggregate ledger does and
does not guarantee. -/
structure Audit where
  /-- Total ever bridged out of this chain, per asset, all destinations. -/
  totalOut : AssetId → ℕ
  /-- Total ever bridged in, per asset, all sources. -/
  totalIn : AssetId → ℕ
  /-- Bridged out towards each destination chain. -/
  outTo : Chain → AssetId → ℕ
  /-- Bridged in from each source chain. -/
  innFrom : Chain → AssetId → ℕ

/-- The vault together with the flow audit. -/
structure World where
  vault : Vault
  audit : Audit

/-- Fresh storage: every mapping zero. -/
def empty : World where
  vault := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩
  audit := ⟨fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩

/-- An asset is registered once its `tokenAddress` entry is set.  The three maps are
written together, so any one of them could serve; this is the one the contract
itself tests (`_decodeBurnAndCheckAssetId`, `_bridgeMintToken`). -/
abbrev Registered (V : Vault) (a : AssetId) : Prop := V.token a ≠ 0

/-- `originChainId[_assetId] == block.chainid` — the test the vault branches on.  An
unregistered asset has `originChain = 0`, so it counts as non-native, matching
`_isBridgedToken`. -/
abbrev Native (thisChain : Chain) (V : Vault) (a : AssetId) : Prop := V.originChain a = thisChain

/-! ## The registry invariant

What the three mappings satisfy.  `idShape` is the field that makes the one-sided
registration guard sufficient; the rest is the atomic-population comment, spelled
out. -/
structure Valid (e : NtvAssetId) (thisChain : Chain) (V : Vault) : Prop where
  /-- A registered id's token maps back to it. -/
  inverse : ∀ a, Registered V a → V.assetOf (V.token a) = a
  /-- A registered token's id maps back to it. -/
  tokenOfAsset : ∀ t, V.assetOf t ≠ 0 → V.token (V.assetOf t) = t
  /-- The origin chain is set exactly for registered ids — the "atomically
  populated" comment, in one line. -/
  originIff : ∀ a, Registered V a ↔ V.originChain a ≠ 0
  /-- The zero asset id is never registered, and the zero address never carries an
  id.  Both hold because every id is a nonzero hash and every registered token is a
  nonzero address. -/
  zeroUnregistered : ¬ Registered V 0
  zeroTokenFree : V.assetOf 0 = 0
  /-- **Every registered id is the encoding of its origin chain and origin token.**
  `_unsafeRegisterNativeToken` computes the id this way; `assetIdCheck` enforces it
  on the bridged path. -/
  idShape : ∀ a, Registered V a → a = e (V.originChain a) (V.originToken a)
  /-- For a native asset the stored token *is* the origin token. -/
  nativeToken : ∀ a, Registered V a → Native thisChain V a → V.originToken a = V.token a
  /-- The ledger moves only for native assets, so it is zero elsewhere. -/
  ledgerNative : ∀ a, ¬ Native thisChain V a → V.bridgedOut a = 0
  /-- **SOLVENCY.**  What is out on loan never exceeds what is held. -/
  solvent : ∀ a, V.bridgedOut a ≤ V.escrowed a

/-! ## The flow audit invariant -/

/-- What ties the aggregate ledger to the flows that produced it. -/
structure Audited (thisChain : Chain) (W : World) : Prop where
  /-- For a native asset the ledger is exactly the net flow: out minus in. -/
  netFlow : ∀ a, Native thisChain W.vault a →
    W.vault.bridgedOut a + W.audit.totalIn a = W.audit.totalOut a
  /-- Nothing has flowed for an unregistered asset. -/
  unregisteredQuiet : ∀ a, ¬ Registered W.vault a →
    W.audit.totalIn a = 0 ∧ W.audit.totalOut a = 0

/-! ## Registration -/

/-- `_registerToken` / `_unsafeRegisterNativeToken`: the id is DERIVED from this
chain and the token.

The guard is one-sided by design — only the token is checked for freshness.  That
the id is therefore also fresh is `Properties.NativeTokenVault.RegisterNativeIdFresh`. -/
structure RegisterNativeGuard (V : Vault) (t : Address) : Prop where
  /-- `require(_nativeToken.code.length > 0, EmptyToken())` — in particular nonzero. -/
  nonzero : t ≠ 0
  /-- `require(assetId[_nativeToken] == bytes32(0), AssetIdAlreadyRegistered())`. -/
  fresh : V.assetOf t = 0

/-- `_setNewTokenStorage`: the single writer of the three registry mappings, called
by both registration paths. -/
def setNewTokenStorage (V : Vault) (a : AssetId) (t ot : Address) (origin : Chain) : Vault :=
  { V with
    originChain := upd V.originChain a origin
    token := upd V.token a t
    assetOf := updA V.assetOf t a
    originToken := upd V.originToken a ot }

/-- `_unsafeRegisterNativeToken`: derive the id from this chain and the token, then
write the registry.  The token is its own origin token. -/
def registerNative (e : NtvAssetId) (thisChain : Chain) (V : Vault) (t : Address) : Vault :=
  setNewTokenStorage V (e thisChain t) t t thisChain

/-- `_ensureAndSaveTokenDeployedInner`: registers a token native ELSEWHERE, whose
local representation `t` was just deployed.

`idChecked` is `DataEncoding.assetIdCheck`, `notNative` is
`DeployingBridgedTokenForNativeToken`, and `freshId` is the `token == address(0)`
test that gates the deploy branch.  `freshToken` is the CREATE2 address being new. -/
structure RegisterBridgedGuard (e : NtvAssetId) (thisChain : Chain) (V : Vault)
    (a : AssetId) (t ot : Address) (origin : Chain) : Prop where
  notNative : origin ≠ thisChain
  originNonzero : origin ≠ 0
  idChecked : a = e origin ot
  tokenNonzero : t ≠ 0
  freshToken : V.assetOf t = 0
  freshId : ¬ Registered V a

/-- `_ensureAndSaveTokenDeployedInner`: the id comes from the mint data and was
checked, the local token was just deployed, and the origin token is remote. -/
def registerBridged (V : Vault) (a : AssetId) (t ot : Address) (origin : Chain) : Vault :=
  setNewTokenStorage V a t ot origin

/-! ## Flows -/

/-- The guard on the way out: `_decodeBurnAndCheckAssetId` resolves and checks the
asset, and `_bridgeBurnToken` rejects a zero amount. -/
structure FlowOutGuard (V : Vault) (a : AssetId) (amt : ℕ) : Prop where
  registered : Registered V a
  nonzero : amt ≠ 0

/-- The guard on the way in.  `_handleBridgeFromChain` reverts with
`InsufficientChainBalance` when the inbound amount exceeds the outstanding
bridged-out amount — but only for assets native to this chain, since only those
have escrow to protect. -/
structure FlowInGuard (thisChain : Chain) (V : Vault) (a : AssetId) (amt : ℕ) : Prop where
  registered : Registered V a
  sufficient : Native thisChain V a → amt ≤ V.bridgedOut a

/-- The same guard with the `InsufficientChainBalance` check REMOVED, for
`Properties.NativeTokenVault.UnguardedInflowUnbacked`. -/
structure FlowInGuardUnchecked (V : Vault) (a : AssetId) (amt : ℕ) : Prop where
  registered : Registered V a

/-- `bridgeBurn` towards chain `c`: for a native asset the funds are escrowed and
the ledger grows; for one native elsewhere the local representation is burned and
neither moves.  The audit records the flow either way. -/
def bridgeOut (thisChain : Chain) (W : World) (c : Chain) (a : AssetId) (amt : ℕ) : World :=
  { vault :=
      if Native thisChain W.vault a then
        { W.vault with
          bridgedOut := upd W.vault.bridgedOut a (W.vault.bridgedOut a + amt)
          escrowed := upd W.vault.escrowed a (W.vault.escrowed a + amt) }
      else W.vault
    audit :=
      { W.audit with
        totalOut := upd W.audit.totalOut a (W.audit.totalOut a + amt)
        outTo := updCA W.audit.outTo c a (W.audit.outTo c a + amt) } }

/-- `bridgeMint` / `_disburseFailedTransfer` from chain `c`: for a native asset the
escrow is released and the ledger shrinks; for one native elsewhere the local
representation is minted. -/
def bridgeIn (thisChain : Chain) (W : World) (c : Chain) (a : AssetId) (amt : ℕ) : World :=
  { vault :=
      if Native thisChain W.vault a then
        { W.vault with
          bridgedOut := upd W.vault.bridgedOut a (W.vault.bridgedOut a - amt)
          escrowed := upd W.vault.escrowed a (W.vault.escrowed a - amt) }
      else W.vault
    audit :=
      { W.audit with
        totalIn := upd W.audit.totalIn a (W.audit.totalIn a + amt)
        innFrom := updCA W.audit.innFrom c a (W.audit.innFrom c a + amt) } }

/-- A direct transfer into the vault, which no accounting records.  Modelled because
the ledger's whole point is that it "cannot be skewed by direct transfers into the
vault", and an inequality rather than an equation is what expresses that. -/
def donate (W : World) (a : AssetId) (amt : ℕ) : World :=
  { W with vault := { W.vault with
      escrowed := upd W.vault.escrowed a (W.vault.escrowed a + amt) } }

/-! ## Runs -/

/-- One operation of the vault. -/
inductive Step (e : NtvAssetId) (thisChain : Chain) : World → World → Prop
  | registerNative {W t} : RegisterNativeGuard W.vault t →
      Step e thisChain W { W with vault := registerNative e thisChain W.vault t }
  | registerBridged {W a t ot origin} :
      RegisterBridgedGuard e thisChain W.vault a t ot origin →
      Step e thisChain W { W with vault := registerBridged W.vault a t ot origin }
  | bridgeOut {W c a amt} : FlowOutGuard W.vault a amt →
      Step e thisChain W (bridgeOut thisChain W c a amt)
  | bridgeIn {W c a amt} : FlowInGuard thisChain W.vault a amt →
      Step e thisChain W (bridgeIn thisChain W c a amt)
  | donate {W a amt} : Step e thisChain W (donate W a amt)

/-- Reachability over any number of operations. -/
inductive Reach (e : NtvAssetId) (thisChain : Chain) : World → World → Prop
  | refl {W} : Reach e thisChain W W
  | tail {W X Y} : Reach e thisChain W X → Step e thisChain X Y → Reach e thisChain W Y

end Contracts.NativeTokenVault
