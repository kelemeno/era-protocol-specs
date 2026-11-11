import EraSpec.Protocol.AssetBridgePreparation.Specs.Reinitialization

/-!
# Properties: reinitializations do not disturb the preparation trace

Statements about `EraSpec.Protocol.AssetBridgePreparation.Specs.Reinitialization`. Proofs are in
`EraSpec.Protocol.AssetBridgePreparation.Proofs.Reinitialization`.

* **A reinitialization step leaves the trace ledger exactly as it was** and raises the version;
  every other step is a step of the existing trace at the token's current metadata
  (`ReinitStepCases`). Conversely every run of the existing trace is a run here, at fixed
  version and metadata (`TraceRunsEmbed`), so nothing the existing trace admits is lost.
* **Conservation survives reinitializations** (`ReinitTraceConservation`): from a `WellFormed`
  vault state, along any run of preparations, transfers and reinitializations, the vault stays
  `WellFormed`, circulating supply plus total pending value is constant, and neither the vault's
  configuration nor the token's identity changes.
* **Prepared data persists** (`ReinitTracePreparedDataPersists`): runs only append to the pending
  list.
* **Pending obligations keep their asset** (`PendingObligationsKeepTheirAsset`): if every pending
  obligation names the token's asset id and origin token at the start, then every pending
  obligation, old or newly prepared, still does at the end, and those are the token's asset id
  and origin token at the start.
* **From registration** (`InitializedTraceWithReinitialization`): after a successful fresh
  registration, a funding phase of token calls (mints, burns, transfers and reinitializations),
  and a run of the extended trace, both vault invariants hold, supply plus pending equals the
  funded supply, every pending obligation names the registered asset and origin token, and the
  token's identity is the registered one. No input `WellFormed` or `RepresentationConsistent`.
* `ReinitTraceWitness` runs the whole pipeline concretely, with a reinitialization between two
  preparations whose metadata bytes differ.
-/

namespace AssetBridgePreparation

open Contracts

/-- **THE TWO KINDS OF STEP.** A step either leaves the trace ledger as it was and raises the
version (a reinitialization), or keeps the version and metadata and is a step of the existing
trace with the metadata read at the token's current metadata. -/
def Properties.ReinitStepCases : Prop :=
  ∀ {Accounting : Type} (hooks : NativeTokenVaultBase.MetaHooks Accounting)
    (s u : TokenTrace Accounting), ReinitStep hooks s u →
    (u.ledger = s.ledger ∧ s.version < u.version) ∨
    (u.version = s.version ∧ u.metadata = s.metadata ∧
      Step (hooks.toHooks s.metadata) s.ledger u.ledger)

/-- **THE EXISTING TRACE IS INCLUDED.** Every run of `Specs/Model.lean`'s trace, with the metadata
read at a fixed token metadata, is a run of the extended trace at that version and metadata. -/
def Properties.TraceRunsEmbed : Prop :=
  ∀ {Accounting : Type} (hooks : NativeTokenVaultBase.MetaHooks Accounting)
    (version : UInt8) (metadata : BridgedStandardERC20.Metadata) (s t : Ledger Accounting),
    Reach (hooks.toHooks metadata) s t →
    ReinitReach hooks ⟨s, version, metadata⟩ ⟨t, version, metadata⟩

/-- **CONSERVATION SURVIVES REINITIALIZATIONS.** From a `WellFormed` vault state, along any run of
preparations, transfers and reinitializations, the vault stays `WellFormed`, supply plus total
pending value is constant, and neither the vault's configuration nor the token's identity
changes. -/
def Properties.ReinitTraceConservation : Prop :=
  ∀ {Accounting : Type} (hooks : NativeTokenVaultBase.MetaHooks Accounting)
    (s t : TokenTrace Accounting),
    NativeTokenVaultBase.WellFormed s.ledger.vault → ReinitReach hooks s t →
    NativeTokenVaultBase.WellFormed t.ledger.vault ∧
    t.ledger.vault.token.totalSupply + pendingAmount t.ledger.pending =
      s.ledger.vault.token.totalSupply + pendingAmount s.ledger.pending ∧
    t.ledger.vault.config = s.ledger.vault.config ∧
    t.ledger.vault.token.config = s.ledger.vault.token.config

/-- **PREPARED DATA PERSISTS.** Along any run, the pending list only grows at its end: no
reinitialization, preparation or transfer replaces previously prepared data. -/
def Properties.ReinitTracePreparedDataPersists : Prop :=
  ∀ {Accounting : Type} (hooks : NativeTokenVaultBase.MetaHooks Accounting)
    (s t : TokenTrace Accounting), ReinitReach hooks s t →
    ∃ later, t.ledger.pending = s.ledger.pending ++ later

/-- **PENDING OBLIGATIONS KEEP THEIR ASSET.** From a `WellFormed` vault state in which every
pending obligation names the token's asset id and origin token, along any run, every pending
obligation still names the token's asset id and origin token, and those are the ones at the
start. -/
def Properties.PendingObligationsKeepTheirAsset : Prop :=
  ∀ {Accounting : Type} (hooks : NativeTokenVaultBase.MetaHooks Accounting)
    (s t : TokenTrace Accounting),
    NativeTokenVaultBase.WellFormed s.ledger.vault → PendingNamesToken s.ledger →
    ReinitReach hooks s t →
    PendingNamesToken t.ledger ∧
    ∀ o ∈ t.ledger.pending, o.assetId = s.ledger.vault.token.config.assetId ∧
      o.data.originToken = s.ledger.vault.token.config.originToken

/-- **FROM REGISTRATION, THROUGH FUNDING AND REINITIALIZATIONS, TO THE TRACE.** After a successful
fresh registration, any run of token calls on the registered token (at its registered version,
with any metadata), and any run of the extended trace from the funded vault with no pending
obligations: both vault invariants hold, supply plus pending equals the funded supply, every
pending obligation names the token's asset id and origin token, and the token's identity is the
registered one. -/
def Properties.InitializedTraceWithReinitialization : Prop :=
  ∀ {Accounting : Type} (initHooks : NativeTokenVaultBase.RegistrationHooks Accounting)
    (start : NativeTokenVaultBase.RegistrationState Accounting)
    (origin : NativeTokenVaultBase.Address)
    (registered : NativeTokenVaultBase.Registered Accounting)
    (metadata : BridgedStandardERC20.Metadata) (funded : BridgedStandardERC20.TokenStorage)
    (hooks : NativeTokenVaultBase.MetaHooks Accounting) (t : TokenTrace Accounting),
    NativeTokenVaultBase.registerFreshBranch initHooks start origin = some registered →
    BridgedStandardERC20.StorageReach
      ⟨registered.state.token, registered.tokenVersion, metadata⟩ funded →
    ReinitReach hooks
      ⟨⟨NativeTokenVaultBase.withTracked registered.state funded, []⟩, funded.version,
        funded.metadata⟩ t →
    NativeTokenVaultBase.LedgerInvariant t.ledger.vault ∧
    NativeTokenVaultBase.RepresentationConsistent t.ledger.vault ∧
    t.ledger.vault.token.totalSupply + pendingAmount t.ledger.pending = funded.token.totalSupply ∧
    PendingNamesToken t.ledger ∧
    t.ledger.vault.token.config = registered.state.token.config

/-- **THE PREMISES ARE SATISFIABLE, WITH A REINITIALIZATION BETWEEN TWO PREPARATIONS.** The
witness registration succeeds; a funding run mints ten units to account `4`, leaving a
`WellFormed` vault; then the trace prepares the witness request (three units), the beacon owner
`13` reinitializes the token to version 2 named `[0x42]`, and the same request prepares again. At
the end two obligations are pending, with metadata bytes the old name `[0x41]` and the new name
`[0x42]`, both naming asset `5` and origin token `9`; four units circulate and six are pending. -/
def Properties.ReinitTraceWitness : Prop :=
  ∃ (registered : NativeTokenVaultBase.Registered Unit)
    (funded : BridgedStandardERC20.TokenStorage) (t : TokenTrace Unit),
    NativeTokenVaultBase.registerFreshBranch wRegHooks wRegStart 9 = some registered ∧
    BridgedStandardERC20.StorageReach
      ⟨registered.state.token, registered.tokenVersion, NativeTokenVaultBase.wMetadata⟩
      funded ∧
    NativeTokenVaultBase.WellFormed (NativeTokenVaultBase.withTracked registered.state funded) ∧
    ReinitReach NativeTokenVaultBase.wHooks
      ⟨⟨NativeTokenVaultBase.withTracked registered.state funded, []⟩, funded.version,
        funded.metadata⟩ t ∧
    t.version = 2 ∧
    t.ledger.pending.map (fun o => o.data.metadata) = [[0x41], [0x42]] ∧
    (∀ o ∈ t.ledger.pending, o.assetId = 5 ∧ o.data.originToken = 9) ∧
    t.ledger.vault.token.totalSupply = 4 ∧ pendingAmount t.ledger.pending = 6

end AssetBridgePreparation
