import EraSpec.Contracts.NativeTokenVaultBase.Specs.LegacyFallback
import EraSpec.Contracts.NativeTokenVaultBase.Properties.RegistryAndEscrow
import EraSpec.Contracts.NativeTokenVaultBase.Properties.RepresentationPreparation

/-!
# Properties: the legacy fallback's asset id against the vault's registry

Statements about `EraSpec.Contracts.NativeTokenVaultBase.Specs.LegacyFallback`. Proofs are in
`EraSpec.Contracts.NativeTokenVaultBase.Proofs.LegacyFallback`.

## Agreement

The fallback writes `encodeNTVAssetId(L1_CHAIN_ID, originToken)` without reading the vault's
registry, so it agrees with the vault exactly when the vault happens to record that pair:

* `LegacyAssetIdAgreesIffRecordedOn` (headline): on a `Valid` vault, once the token's fallback
  has fired, the token's `assetId` is the vault's id for it **iff** the vault registered the
  token under origin chain `L1_CHAIN_ID` and the token's origin token. The hash premise is
  `IdAssumptionsOn` on the two pairs compared, the fallback's and the recorded one.
* `LegacyAssetIdAgreementOrBreak`: the same with no hash premise. The recorded legacy pair
  implies agreement; agreement implies the recorded legacy pair or a `LegacyIdBreak` pinned to
  those two pairs.
* `LegacyAssetIdAgreesIffL1OriginOn`: under the O9 reading of the registry model's origin
  token (the token's own `originToken()`), only the origin chain matters.

## Disagreement and permanence

* `LegacyAssetIdMismatch` (countermodel): a logged registry run whose vault records a legacy
  token as bridged from a chain other than `L1_CHAIN_ID`, with the vault's hash premise on every
  pair the run hashes and the fallback's pair. The vault would call the token
  (`VaultBridgesToken`), the L2 vault's mint succeeds, and the token's id is not the vault's.
* `RegisteredTokenIdFrozen`: no vault operation changes a token's nonzero id. With the token
  side's `legacy_run_config`, `LegacyAgreementPermanent`: once the fallback has fired and the
  vault has an id, agreement or disagreement is permanent. No hash premise in either.
* `UnregisteredLegacyTokenRegistersNative`: at the pin, the permissionless `registerToken` on a
  legacy token with no id records it as native to this chain, permanently. The vault then
  escrows it rather than calling it, so the fallback never fires through the vault, and the
  fallback's id would not be the vault's.

## Representation model and preparation

* `LegacyFallbackRepresentationIff`: in the representation model, a legacy tracked token
  fails `RepresentationConsistent`. After the fallback has fired it holds iff the vault's tracked
  id is the fallback's id and the two registry maps agree. The ledger invariant is carried.
* `LegacyPreparationConservative`, `LegacyPreparationIsPreparation`: `prepare` calls the
  nonlegacy `burn`, so it refuses every legacy token. The deployed preparation `prepareLegacy`
  is `prepare` on a nonlegacy token. On a legacy token it is `prepare` of the same state with the
  fallback-configured token, when the accounting hook does not read the token's configuration (as
  the deployed tracker does not). So every statement of `Properties/RepresentationPreparation.lean`
  and `Properties/PreparationGuards.lean` applies to the first preparation of a legacy token.
* `LegacyFirstPreparation`: that first preparation fires the fallback, burns exactly the amount,
  keeps the ledger invariant, and leaves `RepresentationConsistent` holding iff the vault's
  tracked id is the fallback's id and the maps agree. No premise on the hooks.
* `LegacyPreparationMismatch` (countermodel): with any other tracked id the preparation still
  succeeds and burns, but afterwards the token reports an asset id other than the one the vault
  has just burned it for.

## Anti-vacuity

`LegacyAssetIdAgreementWitness` meets every premise of the two `…On` headlines and of
`LegacyAssetIdAgreementOrBreak`, `RegisteredTokenIdFrozen` and `LegacyAgreementPermanent`, on a
logged registry run with the vault's hash premise, with agreement true and the break false (so
the break disjunct is not a tautology). `LegacyAssetIdMismatch` meets the same premises with both
sides of the headline's iff false. `LegacyIdCollisionAgreesWrongly` shows the break disjunct is
needed: with a colliding encoding the ids agree although the vault records another pair.
`UnregisteredLegacyTokenRegistersNativeSatisfiable`, `LegacyFallbackRepresentationWitness` and
`LegacyFirstPreparationWitness` meet the premises of the remaining statements; the last one also
shows `prepare` refusing a preparation that `prepareLegacy` makes.
-/

namespace Contracts.NativeTokenVaultBase

open NativeTokenVault (Chain Vault World NtvAssetId Valid IdAssumptionsOn Op ReachLog
  registeredPairs)

/-! ## Agreement -/

/-- **THE FALLBACK'S ID IS THE VAULT'S ID EXACTLY WHEN THE VAULT RECORDS
`(L1_CHAIN_ID, originToken)`.** Take a `Valid` registry-model vault `V`, a legacy token `s`
(vault slot zero) and any run of the token from `s` to a state `t` in which the fallback has
fired (`t`'s vault is nonzero). If the encoding is injective and nonzero on the two pairs
compared, the fallback's `(l1, originToken)` and the pair `V` records for `T`, then `t`'s
`assetId` is `V`'s id for the token at `T` iff `V` registered `T` under exactly
`(l1, originToken)`. -/
def Properties.LegacyAssetIdAgreesIffRecordedOn : Prop :=
  ∀ (e : NtvAssetId) (thisChain l1 : Chain) (V : Vault) (T : Address)
    (s t : BridgedStandardERC20.State),
    Valid e thisChain V → s.config.vault = 0 →
    BridgedStandardERC20.LegacyReach (legacyEnv e l1) s t → t.config.vault ≠ 0 →
    IdAssumptionsOn e {legacyPair l1 s.config.originToken, recordedPair V T} →
      (AssetIdAgrees V T t ↔ RecordsLegacyPair V T l1 s.config.originToken)

/-- **THE SAME, OR A PINNED BREAK.** No hash premise. On a `Valid` vault, after the fallback has
fired: if the vault records the legacy pair the ids agree; if the ids agree, the vault records
the legacy pair or a `LegacyIdBreak` holds on the two named pairs. -/
def Properties.LegacyAssetIdAgreementOrBreak : Prop :=
  ∀ (e : NtvAssetId) (thisChain l1 : Chain) (V : Vault) (T : Address)
    (s t : BridgedStandardERC20.State),
    Valid e thisChain V → s.config.vault = 0 →
    BridgedStandardERC20.LegacyReach (legacyEnv e l1) s t → t.config.vault ≠ 0 →
      (RecordsLegacyPair V T l1 s.config.originToken → AssetIdAgrees V T t) ∧
      (AssetIdAgrees V T t →
        RecordsLegacyPair V T l1 s.config.originToken ∨
        LegacyIdBreak e V T l1 s.config.originToken)

/-- **UNDER THE O9 READING, ONLY THE ORIGIN CHAIN MATTERS.** If the vault's recorded origin
token for the token's id is the token's own `originToken` (what `originToken()` returns,
`Refinement.lean` O9), then, with the hash premise on the two pairs, the ids agree iff the vault
has an id for the token whose recorded origin chain is `L1_CHAIN_ID`. -/
def Properties.LegacyAssetIdAgreesIffL1OriginOn : Prop :=
  ∀ (e : NtvAssetId) (thisChain l1 : Chain) (V : Vault) (T : Address)
    (s t : BridgedStandardERC20.State),
    Valid e thisChain V → s.config.vault = 0 →
    BridgedStandardERC20.LegacyReach (legacyEnv e l1) s t → t.config.vault ≠ 0 →
    V.originToken (vaultIdOf V T) = widen s.config.originToken →
    IdAssumptionsOn e {legacyPair l1 s.config.originToken, recordedPair V T} →
      (AssetIdAgrees V T t ↔ vaultIdOf V T ≠ 0 ∧ V.originChain (vaultIdOf V T) = l1)

/-! ## Disagreement -/

/-- **COUNTERMODEL: A LEGACY TOKEN THE VAULT RECORDS UNDER ANOTHER ORIGIN CHAIN GETS ANOTHER
ID.** A logged registry-model run from fresh storage on an L2 chain (`l1 ≠ thisChain`), with
the encoding injective and nonzero on every pair the run hashes and on the fallback's pair. Its
vault is `Valid`, bridges the token at `T` (so the vault's flows would call it), records the
token's own origin token (the O9 reading holds), and records an origin chain other than `l1`.
A well-formed legacy token's mint by the L2 vault succeeds and fires the fallback. Every premise
of `LegacyAssetIdAgreesIffRecordedOn` holds, both sides of its iff are false, and the token's
`assetId` is not the vault's id. -/
def Properties.LegacyAssetIdMismatch : Prop :=
  ∃ (e : NtvAssetId) (thisChain l1 : Chain) (W : World) (log : List Op) (T : Address)
    (s t : BridgedStandardERC20.State) (recipient : Address),
    thisChain ≠ 0 ∧ l1 ≠ thisChain ∧
    ReachLog e thisChain NativeTokenVault.empty W log ∧
    IdAssumptionsOn e ↑(insert (legacyPair l1 s.config.originToken)
      (registeredPairs thisChain log)) ∧
    Valid e thisChain W.vault ∧ VaultBridgesToken thisChain W.vault T ∧
    W.vault.originToken (vaultIdOf W.vault T) = widen s.config.originToken ∧
    W.vault.originChain (vaultIdOf W.vault T) ≠ l1 ∧
    BridgedStandardERC20.WellFormed s ∧ s.config.vault = 0 ∧
    BridgedStandardERC20.bridgeMint (legacyEnv e l1) s
      BridgedStandardERC20.l2NativeTokenVaultAddr recipient 1 = some t ∧
    BridgedStandardERC20.LegacyReach (legacyEnv e l1) s t ∧ t.config.vault ≠ 0 ∧
    IdAssumptionsOn e {legacyPair l1 s.config.originToken, recordedPair W.vault T} ∧
    ¬ RecordsLegacyPair W.vault T l1 s.config.originToken ∧
    ¬ AssetIdAgrees W.vault T t

/-! ## Permanence -/

/-- **THE VAULT'S ID FOR A REGISTERED TOKEN IS FROZEN.** No vault operation changes `assetId[T]`
once it is nonzero: both registration paths write only a key whose entry is zero
(`RegisterNativeGuard.fresh`, `RegisterBridgedGuard.freshToken`), and the flows do not write it.
No hash premise, no `Valid`. -/
def Properties.RegisteredTokenIdFrozen : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain) (W X : World) (T : NativeTokenVault.Address),
    NativeTokenVault.Reach e thisChain W X → W.vault.assetOf T ≠ 0 →
      X.vault.assetOf T = W.vault.assetOf T

/-- **AGREEMENT, OR DISAGREEMENT, IS PERMANENT.** Once a token's vault slot is nonzero (its
fallback, if any, has fired) and the vault has an id for it, no later run of the token and no
later run of the vault changes whether the two ids agree. In particular a mismatch cannot be
repaired by any modelled operation. No hash premise. -/
def Properties.LegacyAgreementPermanent : Prop :=
  ∀ (env : BridgedStandardERC20.LegacyEnv) (e : NtvAssetId) (thisChain : Chain) (W X : World)
    (T : Address) (t t' : BridgedStandardERC20.State),
    t.config.vault ≠ 0 → BridgedStandardERC20.LegacyReach env t t' →
    vaultIdOf W.vault T ≠ 0 → NativeTokenVault.Reach e thisChain W X →
      (AssetIdAgrees X.vault T t' ↔ AssetIdAgrees W.vault T t)

/-- **AN UNREGISTERED LEGACY TOKEN CAN BE REGISTERED AS NATIVE, PERMANENTLY.** At the pin
`registerToken` is permissionless and has no legacy-token check (`NativeTokenVaultBase.sol`
:129-142). On an L2 (`l1 ≠ thisChain`), take a nonzero token address with no id and an encoding
injective and nonzero on the pair it derives and the fallback's pair. Then there is a vault
step, `registerNative`, after which: the token's id is `encodeNTVAssetId(thisChain, T)` and is
native, so the vault escrows the token instead of calling it (no `VaultBridgesToken`, so the
fallback never fires through the vault); the vault does not record the legacy pair; the vault's
id is not the fallback's id; and no later vault operation changes the id. -/
def Properties.UnregisteredLegacyTokenRegistersNative : Prop :=
  ∀ (e : NtvAssetId) (thisChain l1 : Chain) (W : World) (T ot : Address),
    T ≠ 0 → vaultIdOf W.vault T = 0 → l1 ≠ thisChain →
    IdAssumptionsOn e {(thisChain, widen T), legacyPair l1 ot} →
      ∃ X : World, NativeTokenVault.Step e thisChain W X ∧
        vaultIdOf X.vault T = e thisChain (widen T) ∧
        NativeTokenVault.Native thisChain X.vault (vaultIdOf X.vault T) ∧
        ¬ VaultBridgesToken thisChain X.vault T ∧
        ¬ RecordsLegacyPair X.vault T l1 ot ∧
        vaultIdOf X.vault T ≠ e l1 (widen ot) ∧
        ∀ Y : World, NativeTokenVault.Reach e thisChain X Y →
          vaultIdOf Y.vault T = vaultIdOf X.vault T

/-! ## The representation model -/

/-- **THE FALLBACK REPAIRS THE REPRESENTATION INVARIANT EXACTLY WHEN THE VAULT'S TRACKED ID IS
THE FALLBACK'S.** A representation-model state whose vault is the L2 vault and whose tracked
token is legacy fails `RepresentationConsistent`. After any run of the token in which the
fallback fired, the state with the new token satisfies it iff the tracked id is
`encodeNTVAssetId(L1_CHAIN_ID, originToken)` and the two registry maps agree on the tracked
pair. `LedgerInvariant` is carried. -/
def Properties.LegacyFallbackRepresentationIff : Prop :=
  ∀ (Accounting : Type) (σ : State Accounting) (env : BridgedStandardERC20.LegacyEnv)
    (t : BridgedStandardERC20.State),
    σ.config.vault = BridgedStandardERC20.l2NativeTokenVaultAddr → σ.token.config.vault = 0 →
    BridgedStandardERC20.LegacyReach env σ.token t → t.config.vault ≠ 0 →
      ¬ RepresentationConsistent σ ∧
      (LedgerInvariant σ → LedgerInvariant { σ with token := t }) ∧
      (RepresentationConsistent { σ with token := t } ↔
        σ.config.assetId = env.assetIdFor env.l1ChainId σ.token.config.originToken ∧
        σ.registry.tokenForAsset σ.config.assetId = σ.config.tokenAddress ∧
        σ.registry.assetForToken σ.config.tokenAddress = σ.config.assetId)

/-! ## Preparation of a legacy token -/

/-- **ON A NONLEGACY TOKEN THE DEPLOYED PREPARATION IS THE MODEL'S.** -/
def Properties.LegacyPreparationConservative : Prop :=
  ∀ (Accounting : Type) (env : BridgedStandardERC20.LegacyEnv) (hooks : Hooks Accounting)
    (s : State Accounting) (r : Request),
    s.token.config.vault ≠ 0 → prepareLegacy env hooks s r = prepare hooks s r

/-- **ON A LEGACY TOKEN IT IS THE MODEL'S PREPARATION OF THE FALLBACK-CONFIGURED TOKEN.** With an
accounting hook that does not read the token's configuration, the deployed preparation of a
legacy token is `prepare` on the same state with the token's `onlyNTV` prologue applied. So every
statement of `Properties/RepresentationPreparation.lean` and `Properties/PreparationGuards.lean`
applies to it, on that state. -/
def Properties.LegacyPreparationIsPreparation : Prop :=
  ∀ (Accounting : Type) (env : BridgedStandardERC20.LegacyEnv) (hooks : Hooks Accounting)
    (s : State Accounting) (r : Request),
    s.token.config.vault = 0 → HookIgnoresTokenConfig hooks →
      prepareLegacy env hooks s r
        = prepare hooks { s with token := BridgedStandardERC20.legacyFallback env s.token } r

/-- **THE FIRST PREPARATION OF A LEGACY TOKEN.** On a legacy token tracked by the L2 vault, with a
well-formed ledger, a successful deployed preparation fires the fallback, burns exactly the
amount from the depositor and from the supply, keeps the ledger invariant, and leaves
`RepresentationConsistent` holding iff the vault's tracked id is the fallback's id and the two
registry maps agree. No premise on the hooks. -/
def Properties.LegacyFirstPreparation : Prop :=
  ∀ (Accounting : Type) (env : BridgedStandardERC20.LegacyEnv) (hooks : Hooks Accounting)
    (s : State Accounting) (r : Request) (out : Result Accounting),
    s.config.vault = BridgedStandardERC20.l2NativeTokenVaultAddr → s.token.config.vault = 0 →
    LedgerInvariant s → prepareLegacy env hooks s r = some out →
      out.state.token.config = BridgedStandardERC20.fallbackConfig env s.token.config ∧
      out.state.token.balances r.depositor + out.data.amount.val = s.token.balances r.depositor ∧
      out.state.token.totalSupply + out.data.amount.val = s.token.totalSupply ∧
      LedgerInvariant out.state ∧
      (RepresentationConsistent out.state ↔
        s.config.assetId = env.assetIdFor env.l1ChainId s.token.config.originToken ∧
        s.registry.tokenForAsset s.config.assetId = s.config.tokenAddress ∧
        s.registry.assetForToken s.config.tokenAddress = s.config.assetId)

/-! ## Anti-vacuity -/

/-- **THE NONLEGACY MODEL REFUSES THE FIRST PREPARATION OF A LEGACY TOKEN; THE DEPLOYED VAULT MAKES
IT.** For every fallback environment: a legacy token tracked by the L2 vault under the fallback's
id, with a well-formed ledger, and a request and hooks meeting every premise of
`LegacyFirstPreparation` and `LegacyPreparationIsPreparation`. `prepare` fails on it,
`prepareLegacy` succeeds, and the post-state is `WellFormed` with a nonlegacy token (the premise
of `LegacyPreparationConservative`). -/
def Properties.LegacyFirstPreparationWitness : Prop :=
  ∀ env : BridgedStandardERC20.LegacyEnv,
    ∃ (hooks : Hooks Unit) (s : State Unit) (r : Request) (out : Result Unit),
      s.config.vault = BridgedStandardERC20.l2NativeTokenVaultAddr ∧ s.token.config.vault = 0 ∧
      LedgerInvariant s ∧ HookIgnoresTokenConfig hooks ∧
      prepare hooks s r = none ∧ prepareLegacy env hooks s r = some out ∧
      WellFormed out.state ∧ out.state.token.config.vault ≠ 0

/-- **COUNTERMODEL: WITH A MISMATCHED ID THE PREPARATION STILL BURNS, BUT THE TOKEN THEN REPORTS
ANOTHER ASSET.** For every fallback environment: a legacy token tracked by the L2 vault under an
id other than the fallback's, with a well-formed ledger, both registry maps agreeing on the
tracked pair, and hooks meeting every premise of `LegacyFirstPreparation`. The deployed
preparation succeeds, but afterwards `RepresentationConsistent` fails: the token's `assetId` is
not the asset the vault has just burned it for. -/
def Properties.LegacyPreparationMismatch : Prop :=
  ∀ env : BridgedStandardERC20.LegacyEnv,
    ∃ (hooks : Hooks Unit) (s : State Unit) (r : Request) (out : Result Unit),
      s.config.vault = BridgedStandardERC20.l2NativeTokenVaultAddr ∧ s.token.config.vault = 0 ∧
      LedgerInvariant s ∧ HookIgnoresTokenConfig hooks ∧
      s.registry.tokenForAsset s.config.assetId = s.config.tokenAddress ∧
      s.registry.assetForToken s.config.tokenAddress = s.config.assetId ∧
      prepareLegacy env hooks s r = some out ∧
      ¬ RepresentationConsistent out.state ∧ out.state.token.config.assetId ≠ r.assetId

/-- **THE AGREEMENT PREMISES ARE SATISFIABLE, WITH AGREEMENT TRUE AND THE BREAK FALSE.** A logged
registry run from fresh storage on an L2 chain, with the encoding injective and nonzero on every
pair it hashes and on the fallback's pair, whose `Valid` vault bridges the token at `T` and
records exactly the legacy pair; a well-formed legacy token whose L2-vault mint succeeds and
fires the fallback. Every premise of `LegacyAssetIdAgreesIffRecordedOn` and
`LegacyAssetIdAgreesIffL1OriginOn` holds, both sides of the iff are true, and `LegacyIdBreak` is
false. -/
def Properties.LegacyAssetIdAgreementWitness : Prop :=
  ∃ (e : NtvAssetId) (thisChain l1 : Chain) (W : World) (log : List Op) (T : Address)
    (s t : BridgedStandardERC20.State) (recipient : Address),
    thisChain ≠ 0 ∧ l1 ≠ thisChain ∧
    ReachLog e thisChain NativeTokenVault.empty W log ∧
    IdAssumptionsOn e ↑(insert (legacyPair l1 s.config.originToken)
      (registeredPairs thisChain log)) ∧
    Valid e thisChain W.vault ∧ VaultBridgesToken thisChain W.vault T ∧
    W.vault.originToken (vaultIdOf W.vault T) = widen s.config.originToken ∧
    BridgedStandardERC20.WellFormed s ∧ s.config.vault = 0 ∧
    BridgedStandardERC20.bridgeMint (legacyEnv e l1) s
      BridgedStandardERC20.l2NativeTokenVaultAddr recipient 1 = some t ∧
    BridgedStandardERC20.LegacyReach (legacyEnv e l1) s t ∧ t.config.vault ≠ 0 ∧
    IdAssumptionsOn e {legacyPair l1 s.config.originToken, recordedPair W.vault T} ∧
    RecordsLegacyPair W.vault T l1 s.config.originToken ∧ AssetIdAgrees W.vault T t ∧
    ¬ LegacyIdBreak e W.vault T l1 s.config.originToken

/-- **…AND THE BREAK DISJUNCT IS NEEDED.** With an encoding that collides on the two pairs, a
`Valid` vault records the token under another origin chain, yet after the fallback the ids
agree: the vault does not record the legacy pair, and `LegacyIdBreak` holds. -/
def Properties.LegacyIdCollisionAgreesWrongly : Prop :=
  ∃ (e : NtvAssetId) (thisChain l1 : Chain) (V : Vault) (T : Address)
    (s t : BridgedStandardERC20.State),
    Valid e thisChain V ∧ s.config.vault = 0 ∧
    BridgedStandardERC20.LegacyReach (legacyEnv e l1) s t ∧ t.config.vault ≠ 0 ∧
    AssetIdAgrees V T t ∧ ¬ RecordsLegacyPair V T l1 s.config.originToken ∧
    LegacyIdBreak e V T l1 s.config.originToken

/-- The premises of `UnregisteredLegacyTokenRegistersNative` hold on a `Valid` fresh vault. -/
def Properties.UnregisteredLegacyTokenRegistersNativeSatisfiable : Prop :=
  ∃ (e : NtvAssetId) (thisChain l1 : Chain) (W : World) (T ot : Address),
    thisChain ≠ 0 ∧ Valid e thisChain W.vault ∧
    T ≠ 0 ∧ vaultIdOf W.vault T = 0 ∧ l1 ≠ thisChain ∧
    IdAssumptionsOn e {(thisChain, widen T), legacyPair l1 ot}

/-- **THE REPRESENTATION PREMISES ARE SATISFIABLE, WITH THE INVARIANT REPAIRED.** For every
fallback environment: a representation-model state with the L2 vault and a legacy tracked token,
a run of the token that fires the fallback, `LedgerInvariant` before, and
`RepresentationConsistent` after. -/
def Properties.LegacyFallbackRepresentationWitness : Prop :=
  ∀ env : BridgedStandardERC20.LegacyEnv,
    ∃ (σ : State Unit) (t : BridgedStandardERC20.State),
      σ.config.vault = BridgedStandardERC20.l2NativeTokenVaultAddr ∧
      σ.token.config.vault = 0 ∧ LedgerInvariant σ ∧
      BridgedStandardERC20.LegacyReach env σ.token t ∧ t.config.vault ≠ 0 ∧
      RepresentationConsistent { σ with token := t }

end Contracts.NativeTokenVaultBase
