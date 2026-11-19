import EraSpec.Contracts.BridgedStandardERC20.Specs.Model

/-!
# BridgedStandardERC20: the legacy zero-vault fallback in `onlyNTV`

Locally authored specification, reviewed against era-contracts `draft/v0.35.0` head `b17415d20`,
`l1-contracts/contracts/bridge/BridgedStandardERC20.sol` (the same code as at the old pin
`c67894b9`, where it was first reviewed, with rewritten comments). Line numbers below are in that
file at `b17415d20` unless another file is named; other paths are relative to
`l1-contracts/contracts/`.

## The source

`bridgeMint` (:158-161) and `bridgeBurn` (:164-167) are guarded by `onlyNTV` (:47-61):

    /// @dev Also lazily migrates legacy tokens (deployed before the NTV existed, only on L2s): sets
    /// `nativeTokenVault` to the canonical address and derives the asset ID on first use.
    modifier onlyNTV() {
        address ntv = nativeTokenVault;
        if (ntv == address(0)) {
            ntv = L2_NATIVE_TOKEN_VAULT_ADDR;
            nativeTokenVault = L2_NATIVE_TOKEN_VAULT_ADDR;
            assetId = DataEncoding.encodeNTVAssetId(
                L2NativeTokenVault(L2_NATIVE_TOKEN_VAULT_ADDR).L1_CHAIN_ID(),
                originToken
            );
        }
        require(msg.sender == ntv, Unauthorized(msg.sender));
        _;
    }

A *legacy* token is one whose `nativeTokenVault` slot (:42) is zero. The modifier's comment
says that happens only on L2s, for legacy tokens (:47-48); a token initialized by
`bridgeInitialize` has its caller as vault (:87). The prologue also writes the `assetId` slot
(:45), from the token's own `originToken` slot (:39).

## What this file adds

The nonlegacy model (`Specs/Model.lean`) covers only `nativeTokenVault ≠ 0`: its `mint` and
`burn` require `config.vault ≠ 0` and return `none` on a legacy state, which is not what the
deployed token does there. This file adds the legacy branch and leaves that model unchanged.

* `legacyFallback` is the modifier's prologue: on a zero vault it writes the vault slot to
  `L2_NATIVE_TOKEN_VAULT_ADDR` and the asset-id slot to
  `encodeNTVAssetId(L1_CHAIN_ID, originToken)`; on a nonzero vault it is the identity. It
  never touches balances, supply or the origin token.
* `bridgeMint` / `bridgeBurn` are the prologue followed by the nonlegacy `mint` / `burn` on
  its result. `require(msg.sender == ntv)` is the nonlegacy guard's `caller = config.vault`
  read on the post-prologue state, and OpenZeppelin's `_mint` / `_burn` checks are the rest
  of `MintAllowed` / `BurnAllowed`.
* A failure anywhere returns `none`, which commits nothing, the prologue's two writes
  included. The modifier writes before its `require`, in the same call frame, so a revert
  of the `require` or of `_mint` / `_burn` undoes them (`VM-REVERT`, `MODEL-COMMIT`).
* `LegacyStep` / `LegacyReach` are the token's runs with both branches: the two bridge
  calls and the nonlegacy `transfer`. Transfers do not pass through `onlyNTV`.

## Model boundaries

* `L2NativeTokenVault(L2_NATIVE_TOKEN_VAULT_ADDR).L1_CHAIN_ID()` is an external view call.
  `LegacyEnv.l1ChainId` is the value it returns. It is the L2 vault's `L1_CHAIN_ID` storage
  (`bridge/ntv/L2NativeTokenVault.sol:58`), which `updateL2` refuses to change once nonzero
  (`L2NativeTokenVault.sol:147-148`). It is fixed for a run here. Only a call that takes the
  fallback reads it (`Properties.nonlegacy_bridge_calls_unchanged`), and at most one call on a
  run does (`Properties.legacy_run_config`), so only its value at that call matters. The call
  is assumed not to revert (`DEP-RESULTS`).
* `LegacyEnv.assetIdFor` is `DataEncoding.encodeNTVAssetId(chainId, token)`
  (`common/libraries/DataEncoding.sol:150-152`), on 160-bit addresses. No hash property is
  assumed in this file.
* `l2NativeTokenVaultAddr` is the constant itself, `address(0x10000 + 0x04)`, not a
  parameter (`common/l2-helpers/L2ContractAddresses.sol:12, :89`).
* The deprecated `l2Bridge` slot (:34-36) is not modelled. Nothing reads it for
  authorization, so it confers no mint or burn authority on a legacy token.
* `bridgeInitialize` (an `initializer`, :82) and `reinitializeToken` (:139-155, which writes
  only the name, symbol, permit domain, getters and initializer version) are not steps here.
  `reinitializeToken` writes none of `nativeTokenVault`, `assetId` and `originToken`.
* Events, allowances/permit and metadata are not modelled, as in `Specs/Model.lean`.
-/

namespace Contracts.BridgedStandardERC20

/-- `L2_NATIVE_TOKEN_VAULT_ADDR = address(BUILT_IN_CONTRACTS_OFFSET + 0x04)`, with
`BUILT_IN_CONTRACTS_OFFSET = 0x10000` (`common/l2-helpers/L2ContractAddresses.sol:12, :89`).
The trustee the fallback installs. -/
def l2NativeTokenVaultAddr : Address := 0x10004

/-- What the fallback reads from outside the token's own storage. -/
structure LegacyEnv where
  /-- The value `L2NativeTokenVault(L2_NATIVE_TOKEN_VAULT_ADDR).L1_CHAIN_ID()` returns
  (:55): the L2 vault's `L1_CHAIN_ID` storage (`L2NativeTokenVault.sol:58`). -/
  l1ChainId : UInt256
  /-- `DataEncoding.encodeNTVAssetId(chainId, token)` (`DataEncoding.sol:150-152`). -/
  assetIdFor : UInt256 → Address → UInt256

/-- The configuration the fallback installs (:52-57): the L2 vault as trustee, the asset id
`encodeNTVAssetId(L1_CHAIN_ID, originToken)` computed from the stored origin token, and the
origin token unchanged. -/
def fallbackConfig (env : LegacyEnv) (c : Config) : Config :=
  ⟨l2NativeTokenVaultAddr, c.originToken, env.assetIdFor env.l1ChainId c.originToken⟩

/-- The `onlyNTV` prologue (:50-58) as a state update. On a zero vault it writes the vault
and asset-id slots; on a nonzero vault it writes nothing. Balances and supply are untouched.
On its own it is never committed: it is committed only as part of a successful
`bridgeMint` / `bridgeBurn`. -/
def legacyFallback (env : LegacyEnv) (s : State) : State :=
  if s.config.vault = 0 then { s with config := fallbackConfig env s.config } else s

/-- `bridgeMint(_to, _amount) external onlyNTV` (:158-161): the prologue, then the nonlegacy
`mint` on its result. `none` commits nothing, the prologue's writes included. -/
def bridgeMint (env : LegacyEnv) (s : State) (caller recipient : Address) (amount : UInt256) :
    Option State :=
  mint (legacyFallback env s) caller recipient amount

/-- `bridgeBurn(_from, _amount) external onlyNTV` (:164-167): the prologue, then the
nonlegacy `burn` on its result. `none` commits nothing, the prologue's writes included. -/
def bridgeBurn (env : LegacyEnv) (s : State) (caller owner : Address) (amount : UInt256) :
    Option State :=
  burn (legacyFallback env s) caller owner amount

/-- One successful call of the token with both `onlyNTV` branches. `transfer` is the
nonlegacy model's, since it does not pass through `onlyNTV`. -/
inductive LegacyStep (env : LegacyEnv) : State → State → Prop
  | bridgeMint {s t caller recipient amount} :
      bridgeMint env s caller recipient amount = some t → LegacyStep env s t
  | bridgeBurn {s t caller owner amount} :
      bridgeBurn env s caller owner amount = some t → LegacyStep env s t
  | transfer {s t owner recipient amount} :
      transfer s owner recipient amount = some t → LegacyStep env s t

/-- Any number of `LegacyStep`s. -/
inductive LegacyReach (env : LegacyEnv) : State → State → Prop
  | refl {s} : LegacyReach env s s
  | tail {s t u} : LegacyReach env s t → LegacyStep env t u → LegacyReach env s u

end Contracts.BridgedStandardERC20
