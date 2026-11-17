import EraSpec.Contracts.L2AssetTracker.Specs.HookOrdering

/-!
# Model: the tracker run together with a native token's ledger

Source: pin `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`, `TRK` =
`l1-contracts/contracts/bridge/asset-tracker/L2AssetTracker.sol`, `NTV` =
`bridge/ntv/NativeTokenVaultBase.sol`, `L2NTV` = `bridge/ntv/L2NativeTokenVault.sol`.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.L2AssetTracker.Properties.NativeEscrow` and proved in
`EraSpec.Contracts.L2AssetTracker.Proofs.NativeEscrow`.

`Specs/Accounting.lean` runs the tracker alone: the token reads of a first-touch registration
are free inputs, and a flow's token effect is not modelled.  `Specs/HookOrdering.lean` composes
ONE vault call with the token (`runPath`).  This file composes whole runs, for one asset `a`
and the ledger `tok` of its token (`L2_NATIVE_TOKEN_VAULT.tokenAddress(a)`).  A step is one of:

* the vault's outbound native path for `a` in source order (`runPath .nativeOut`): the tracker's
  `handleInitiateBridgingOnL2`, reading `tok`, then `_depositFunds` from the depositor with the
  vault's check on the balance increase (`NTV:469`, `:473-476`, `:490-497`);
* the vault's inbound native path for `a` (`runPath .nativeIn`): `handleFinalizeBridgingOnL2`,
  reading `tok`, then `_withdrawFunds` to the receiver (`NTV:260`, `:264-265`; recovery
  `:296-298`; `L2NTV:238-241`);
* anyone's `registerLegacyToken(a)`, reading `tok` as it is at that moment (`TRK:198-210`);
* any other successful tracker call (`Op.TouchesAsset` says which calls are excluded): those
  read no token of `a` and record no flow of `a`;
* any change of the ledger the vault does not make (`TokenMove`): transfers between other
  holders, transfers into the vault, mints and burns by the token's own logic.

The audit records the two vault paths' amounts as `Specs/Accounting.lean`'s `exec` does for the
vault's `.initiate` and `.finalize` calls.

## Model boundaries

* The vault's balance of the token is lowered only by its own `_withdrawFunds`, on the inbound
  path: at the pin the L2 vault moves tokens only through `_withdrawFunds` and `_depositFunds`
  and grants no allowance.  `TokenMove` therefore assumes that the ledger stays well-formed
  (`BridgedStandardERC20.WellFormed`: balances sum to the supply, supply below `2^256`) and that
  the vault's balance does not fall (`DEP-FRAME`).  A token that can lower the vault's balance on
  its own (a rebasing or fee-taking token, `MODEL-ESCROW`) is outside the model, and
  `Properties.EscrowNeedsVaultOnlyOutflow` shows that the conclusions fail for it.
* The vault's other checks around the hook (router, pause, nonzero amount, asset id, WETH,
  `msg.value`) are not modelled; neither are its bridged paths for `a`, which it does not take for
  an asset native here (`NTV:245`, `:389`).
* `Config` (the vault's maps, this chain, the system addresses) is fixed, as in
  `Specs/Accounting.lean`.
-/

namespace Contracts.L2AssetTracker

/-- The tracker calls that read the token of `a` or record a flow of `a`: the first-touch
`registerLegacyToken(a)` and the vault's two flow hooks for `a`.  In the composed run these
happen only as the `registerLegacy` step and inside the two vault paths. -/
def Op.TouchesAsset (a : AssetId) : Op → Prop
  | .registerLegacy _ b => b = a
  | .initiate _ _ b _ => b = a
  | .finalize _ _ b _ => b = a
  | _ => False

/-- The tracker, its settlement layer and audit, and the ledger of the token of the asset the run
follows. -/
structure EscrowSys where
  sys : Sys
  tok : Contracts.BridgedStandardERC20.State

/-- A change of the token's ledger that the vault does not make: it keeps the ledger well-formed
and does not lower the vault's balance.  The only assumptions made about it. -/
def TokenMove (cfg : Config) (tok tok' : Contracts.BridgedStandardERC20.State) : Prop :=
  Contracts.BridgedStandardERC20.WellFormed tok' ∧ tok.balances cfg.ntv ≤ tok'.balances cfg.ntv

/-- One step of the composed run for asset `a`. -/
inductive EscrowStep (cfg : Config) (a : AssetId) : EscrowSys → EscrowSys → Prop
  /-- The vault's outbound native path: the hook reading the token, then the deposit. -/
  | nativeOut {e : EscrowSys} {st' : Storage} {tok' : Contracts.BridgedStandardERC20.State}
      (chain : ChainId) (account : Address) (amount : UInt256) :
      runPath cfg .nativeOut e.sys.st e.sys.sl e.tok chain a account amount = some (st', tok') →
      EscrowStep cfg a e ⟨{ e.sys with st := st', audit := e.sys.audit.addOut a amount }, tok'⟩
  /-- The vault's inbound native path: the hook reading the token, then the withdrawal. -/
  | nativeIn {e : EscrowSys} {st' : Storage} {tok' : Contracts.BridgedStandardERC20.State}
      (chain : ChainId) (account : Address) (amount : UInt256) :
      runPath cfg .nativeIn e.sys.st e.sys.sl e.tok chain a account amount = some (st', tok') →
      EscrowStep cfg a e ⟨{ e.sys with st := st', audit := e.sys.audit.addIn a amount }, tok'⟩
  /-- Anyone's `registerLegacyToken(a)`, reading the token as it is. -/
  | registerLegacy {e : EscrowSys} {sys' : Sys} :
      exec cfg e.sys (.registerLegacy (tokenReads cfg e.tok) a) = some sys' →
      EscrowStep cfg a e ⟨sys', e.tok⟩
  /-- Any other successful tracker call. -/
  | tracker {e : EscrowSys} {sys' : Sys} (op : Op) :
      ¬ op.TouchesAsset a → exec cfg e.sys op = some sys' → EscrowStep cfg a e ⟨sys', e.tok⟩
  /-- A change of the ledger the vault does not make. -/
  | token {e : EscrowSys} {tok' : Contracts.BridgedStandardERC20.State} :
      TokenMove cfg e.tok tok' → EscrowStep cfg a e ⟨e.sys, tok'⟩

/-- Any number of composed steps. -/
abbrev EscrowReach (cfg : Config) (a : AssetId) : EscrowSys → EscrowSys → Prop :=
  Relation.ReflTransGen (EscrowStep cfg a)

/-- The invariant of the composed run: the tracker's `Inv`, a well-formed ledger, and, once `a`
is registered, `MAX - chainBalance` at most the vault's balance of the token. -/
structure EscrowInv (cfg : Config) (a : AssetId) (e : EscrowSys) : Prop where
  inv : Inv cfg e.sys
  ledger : Contracts.BridgedStandardERC20.WellFormed e.tok
  escrowed : e.sys.st.isAssetRegistered a = true →
    MAX_TOKEN_BALANCE.val - (e.sys.st.chainBalance cfg.thisChain a).val ≤ e.tok.balances cfg.ntv

end Contracts.L2AssetTracker
