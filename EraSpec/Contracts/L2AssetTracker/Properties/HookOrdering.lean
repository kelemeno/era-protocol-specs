import EraSpec.Contracts.L2AssetTracker.Specs.HookOrdering

/-!
# Properties: the tracker hook precedes the token effect, so first-touch snapshots are pre-call

Statements about `EraSpec.Contracts.L2AssetTracker.Specs.HookOrdering`.  Proofs are in
`EraSpec.Contracts.L2AssetTracker.Proofs.HookOrdering`.

* `HookPrecedesEffect`: the vault model's preparation, destination mint and recovery, with the L2
  hooks, ARE the source-order bridged paths: the tracker hook reads the token before the burn or
  the mint.
* `FirstTouchSnapshotIsPreOp`: on each of the four paths, a first touch registers the asset
  with the snapshot of the token as it was before the call.
* `SnapshotIndependentOfEntry`: whichever path makes the first touch, from the same storage and
  token, the snapshot is the same, so it does not depend on whether the first post-v31 operation
  is a deposit or a withdrawal.
* `HookAfterEffectSkews` (countermodel): with the effect first, the outbound and inbound
  snapshots of the same token differ, and neither is the pre-call one, for a bridged token and
  for a native one.
* `BaseNeverTakesLegacyPath`: once `initL2` has run and the base token is registered, every later
  state keeps the same base asset registered, and its first-touch registration is the identity
  whatever it would read: the base token's snapshot is never taken from `totalSupply()`.

Non-vacuity: `FirstTouchSatisfiable` (all four paths succeed on a first touch),
`HookPrecedesEffectSatisfiable` (a successful preparation with the vault as the tracker's caller),
`BaseNeverLegacySatisfiable` (a run with base-token flows from a post-genesis state).
-/

namespace Contracts.L2AssetTracker

open Contracts.NativeTokenVaultBase (State Request Result prepare bridgeMint
  bridgeRecoverFailedTransfer ResolutionCall L2Accounting l2Hooks l2ResolutionHooks WellFormed Bytes)

/-- **THE VAULT MODEL'S BRIDGED PATHS ARE HOOK-THEN-EFFECT.**  With the L2 hooks and the vault as
the tracker's caller: a successful preparation on a `WellFormed` state is the source-order
`bridgedOut` path for the depositor, and a successful destination mint (recovery) is the
source-order `bridgedIn` path for the remote receiver (the original caller); each reproduces the
resulting tracker storage and token exactly. -/
def Properties.HookPrecedesEffect : Prop :=
  ∀ (cfg : Config) (metadata : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes)
    (s : State L2Accounting),
    cfg.ntv = s.config.vault →
      (∀ (r : Request) (out : Result L2Accounting), WellFormed s →
        prepare (l2Hooks cfg metadata) s r = some out →
          runPath cfg .bridgedOut s.accounting.st s.accounting.sl s.token r.destinationChain
            r.assetId r.depositor r.data.amount = some (out.state.accounting.st, out.state.token)) ∧
      (∀ (c : ResolutionCall) (t : State L2Accounting),
        bridgeMint (l2ResolutionHooks cfg) s c = some t →
          runPath cfg .bridgedIn s.accounting.st s.accounting.sl s.token c.chain c.assetId
            c.data.remoteReceiver c.data.amount = some (t.accounting.st, t.token)) ∧
      (∀ (c : ResolutionCall) (t : State L2Accounting),
        bridgeRecoverFailedTransfer (l2ResolutionHooks cfg) s c = some t →
          runPath cfg .bridgedIn s.accounting.st s.accounting.sl s.token c.chain c.assetId
            c.data.originalCaller c.data.amount = some (t.accounting.st, t.token))

/-- **A FIRST TOUCH RECORDS THE PRE-CALL TOKEN.**  On every path in source order, for an asset the
tracker has not registered, a successful call leaves it registered with
`legacySnapshot cfg a tok`, computed from the token BEFORE the call. -/
def Properties.FirstTouchSnapshotIsPreOp : Prop :=
  ∀ (cfg : Config) (p : VaultPath) (st : Storage) (sl : ChainId)
    (tok : Contracts.BridgedStandardERC20.State) (chain : ChainId) (a : AssetId)
    (account : Address) (amount : UInt256) (st' : Storage)
    (tok' : Contracts.BridgedStandardERC20.State),
    st.isAssetRegistered a = false → runPath cfg p st sl tok chain a account amount = some (st', tok') →
      st'.isAssetRegistered a = true ∧ st'.totalPreV31TotalSupply a = legacySnapshot cfg a tok

/-- **THE SNAPSHOT DOES NOT DEPEND ON THE ENTRY.**  Two first touches of the same asset from the same
storage and token, by any two paths (any chains, accounts, amounts, settlement layers), record
the same snapshot. -/
def Properties.SnapshotIndependentOfEntry : Prop :=
  ∀ (cfg : Config) (p q : VaultPath) (st : Storage) (sl sl' : ChainId)
    (tok : Contracts.BridgedStandardERC20.State) (chain chain' : ChainId) (a : AssetId)
    (account account' : Address) (amount amount' : UInt256) (st₁ st₂ : Storage)
    (tok₁ tok₂ : Contracts.BridgedStandardERC20.State),
    st.isAssetRegistered a = false →
    runPath cfg p st sl tok chain a account amount = some (st₁, tok₁) →
    runPath cfg q st sl' tok chain' a account' amount' = some (st₂, tok₂) →
      st₁.totalPreV31TotalSupply a = st₂.totalPreV31TotalSupply a

/-- **COUNTERMODEL: EFFECT FIRST SKEWS THE SNAPSHOT.**  For a bridged legacy asset `a` (token
`tok`) and a native legacy asset `aN` (token `tokN`), all unregistered: in the reversed order the
outbound and the inbound path, from the same storage and token, both succeed and record different
snapshots, neither equal to the pre-call one; in source order both paths succeed (and record the
pre-call one, `FirstTouchSnapshotIsPreOp`). -/
def Properties.HookAfterEffectSkews : Prop :=
  ∃ (cfg : Config) (st : Storage) (sl : ChainId) (tok tokN : Contracts.BridgedStandardERC20.State)
    (chain : ChainId) (a aN : AssetId) (account : Address) (amount : UInt256)
    (st₁ st₂ st₃ st₄ : Storage) (tok₁ tok₂ tok₃ tok₄ : Contracts.BridgedStandardERC20.State),
    amount ≠ 0 ∧
    st.isAssetRegistered a = false ∧ ¬ Native cfg a ∧
    runPathEffectFirst cfg .bridgedOut st sl tok chain a account amount = some (st₁, tok₁) ∧
    runPathEffectFirst cfg .bridgedIn st sl tok chain a account amount = some (st₂, tok₂) ∧
    st₁.totalPreV31TotalSupply a ≠ st₂.totalPreV31TotalSupply a ∧
    st₁.totalPreV31TotalSupply a ≠ legacySnapshot cfg a tok ∧
    st₂.totalPreV31TotalSupply a ≠ legacySnapshot cfg a tok ∧
    (∃ x, runPath cfg .bridgedOut st sl tok chain a account amount = some x) ∧
    (∃ x, runPath cfg .bridgedIn st sl tok chain a account amount = some x) ∧
    st.isAssetRegistered aN = false ∧ Native cfg aN ∧
    runPathEffectFirst cfg .nativeOut st sl tokN chain aN account amount = some (st₃, tok₃) ∧
    runPathEffectFirst cfg .nativeIn st sl tokN chain aN account amount = some (st₄, tok₄) ∧
    st₃.totalPreV31TotalSupply aN ≠ st₄.totalPreV31TotalSupply aN ∧
    st₃.totalPreV31TotalSupply aN ≠ legacySnapshot cfg aN tokN ∧
    st₄.totalPreV31TotalSupply aN ≠ legacySnapshot cfg aN tokN ∧
    (∃ x, runPath cfg .nativeOut st sl tokN chain aN account amount = some x) ∧
    (∃ x, runPath cfg .nativeIn st sl tokN chain aN account amount = some x)

/-- **THE BASE TOKEN NEVER TAKES THE FIRST-TOUCH PATH.**  Along any run from a state where `initL2`
has run and the base token is registered: the base asset id never changes, it stays registered,
and its first-touch registration is the identity for every token read and token address. -/
def Properties.BaseNeverTakesLegacyPath : Prop :=
  ∀ (cfg : Config) (sys₀ sys : Sys), Reach cfg sys₀ sys →
    sys₀.st.guardInitialized = true →
    sys₀.st.isAssetRegistered sys₀.st.baseTokenAssetId = true →
      sys.st.baseTokenAssetId = sys₀.st.baseTokenAssetId ∧
      sys.st.isAssetRegistered sys.st.baseTokenAssetId = true ∧
      ∀ (reads : TokenReads) (token : Address),
        registerLegacyTokenIfNeeded cfg sys.st reads sys.st.baseTokenAssetId token = some sys.st

/-! ## Non-vacuity -/

/-- **ALL FOUR PATHS SUCCEED ON A FIRST TOUCH**, with a nonzero amount: a bridged legacy asset
through `bridgedOut` and `bridgedIn`, a native one through `nativeOut` and `nativeIn`. -/
def Properties.FirstTouchSatisfiable : Prop :=
  ∃ (cfg : Config) (st : Storage) (sl : ChainId) (tok tokN : Contracts.BridgedStandardERC20.State)
    (chain : ChainId) (a aN : AssetId) (account : Address) (amount : UInt256)
    (x₁ x₂ x₃ x₄ : Storage × Contracts.BridgedStandardERC20.State),
    amount ≠ 0 ∧ st.isAssetRegistered a = false ∧ st.isAssetRegistered aN = false ∧
    ¬ Native cfg a ∧ Native cfg aN ∧
    runPath cfg .bridgedOut st sl tok chain a account amount = some x₁ ∧
    runPath cfg .bridgedIn st sl tok chain a account amount = some x₂ ∧
    runPath cfg .nativeOut st sl tokN chain aN account amount = some x₃ ∧
    runPath cfg .nativeIn st sl tokN chain aN account amount = some x₄

/-- **THE PREMISES OF `HookPrecedesEffect` ARE SATISFIABLE**: the vault is the tracker's caller,
the state is `WellFormed`, and a preparation and a destination mint succeed. -/
def Properties.HookPrecedesEffectSatisfiable : Prop :=
  ∃ (cfg : Config) (metadata : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes)
    (s : State L2Accounting) (r : Request) (out : Result L2Accounting) (c : ResolutionCall)
    (t : State L2Accounting),
    cfg.ntv = s.config.vault ∧ WellFormed s ∧ prepare (l2Hooks cfg metadata) s r = some out ∧
    bridgeMint (l2ResolutionHooks cfg) s c = some t

/-- **A NONTRIVIAL RUN FROM A POST-GENESIS STATE**: `initL2` has run, the base token is
registered, and the run moves the base token out and back in. -/
def Properties.BaseNeverLegacySatisfiable : Prop :=
  ∃ (cfg : Config) (sys₀ sys₁ sys₂ : Sys) (reads : TokenReads) (c : ChainId),
    sys₀.st.guardInitialized = true ∧
    sys₀.st.isAssetRegistered sys₀.st.baseTokenAssetId = true ∧
    exec cfg sys₀ (.initiateBase reads c 1) = some sys₁ ∧
    exec cfg sys₁ (.finalizeBase reads cfg.baseTokenHolder c 1) = some sys₂ ∧
    Reach cfg sys₀ sys₂

end Contracts.L2AssetTracker
