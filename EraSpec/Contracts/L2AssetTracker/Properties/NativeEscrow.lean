import EraSpec.Contracts.L2AssetTracker.Specs.NativeEscrow

/-!
# Properties: the chain balance of a native token and the vault's escrow of it

Statements about `EraSpec.Contracts.L2AssetTracker.Specs.NativeEscrow`.  Proofs are in
`EraSpec.Contracts.L2AssetTracker.Proofs.NativeEscrow`.  `TRK` is
`bridge/asset-tracker/L2AssetTracker.sol` at `b17415d20`.

For a registered asset `a` native here, `Properties.NativeSentinel` says what the chain balance is
in the tracker alone: `chainBalance = MAX - (E + Σout - Σin)`, with `E = MAX - snapshot`.  Run
together with the token's ledger (the vault's two native paths, first-touch registrations
reading the token as it is, every other tracker call, and every ledger change the vault does not
make, `TokenMove`):

* `EscrowRunIsTrackerRun`: the tracker part of a composed run is a run of the tracker model, so
  every result of `Properties/Accounting.lean` applies to it.
* `EscrowInvariant`, `FreshEscrowSatisfiesInv`: `EscrowInv` holds along every composed run from a
  state satisfying it, and a fresh tracker next to any well-formed ledger satisfies it.
* `NativeReleasesAreEscrowed` (headline): for a registered asset native here, `E + Σout - Σin`,
  which is `MAX - chainBalance`, is at most the vault's balance of the token.
* `NativeInboundIffCap` (headline): for a registered asset whose inbound transfer touches no L1
  counter, with a nonzero vault address, the vault's inbound native path to a nonzero receiver
  succeeds iff `Σin + amount ≤ E + Σout`: inside the cap the vault's withdrawal does not fail.
  `NativeInboundFailsOnlyAtTheHook` is the general form: registered or not, and whatever the
  settlement layer, the path to a nonzero receiver fails only if the tracker's hook fails.
* `FundedNativeOutboundSucceeds` (headline): with a nonzero chain id, vault address and
  `tokenAddress` entry, a nonzero depositor other than the vault, holding at least `amount`, can
  always move `amount` out on the outbound native path, first touch included; the only exception
  is the `totalWithdrawalsToL1` counter overflowing on a transfer to L1 while the chain settles on
  L1.  So in a composed run the chain balance never refuses such a transfer.  Allowances are not
  modelled: the deposit is the depositor's transfer.
* `EscrowNeedsVaultOnlyOutflow` (countermodel): if the vault's balance can fall by a ledger change
  the vault does not make (outside `TokenMove`), the tracker's hook accepts an inbound transfer
  that the vault's withdrawal cannot pay.

Non-vacuity: `NativeEscrowSatisfiable` is a fresh tracker next to a well-formed ledger in which the
vault already holds a nonzero balance, and a composed run from it to a state where `initL2` has
run, the native asset is registered with nonzero outflow and inflow, and the vault's balance
strictly exceeds `MAX - chainBalance`; there, a funded outbound transfer and an inbound transfer
to a nonzero receiver both succeed.  It meets the premises of every result above.  The
countermodel is its own witness.
-/

namespace Contracts.L2AssetTracker

/-- **THE TRACKER PART OF A COMPOSED RUN IS A TRACKER RUN.**  Every composed run's tracker states
form a run of `Reach` (the vault paths are the tracker's `.initiate` and `.finalize` calls with
the token's reads, a ledger change is no tracker step). -/
def Properties.EscrowRunIsTrackerRun : Prop :=
  ∀ (cfg : Config) (a : AssetId) (e₀ e : EscrowSys), EscrowReach cfg a e₀ e → Reach cfg e₀.sys e.sys

/-- **THE ESCROW INVARIANT HOLDS ALONG EVERY COMPOSED RUN.**  For an asset `a` native here, from a
state satisfying `EscrowInv`, every state reachable by composed steps satisfies `EscrowInv`. -/
def Properties.EscrowInvariant : Prop :=
  ∀ (cfg : Config) (a : AssetId) (e₀ e : EscrowSys), Native cfg a →
    EscrowInv cfg a e₀ → EscrowReach cfg a e₀ e → EscrowInv cfg a e

/-- **THE STARTING POINT.**  A fresh tracker (empty audit, any settlement layer) next to any
well-formed ledger satisfies `EscrowInv`, under the premises of `FreshTrackerSatisfiesInv`. -/
def Properties.FreshEscrowSatisfiesInv : Prop :=
  ∀ (cfg : Config) (a : AssetId) (sl : ChainId) (tok : Contracts.BridgedStandardERC20.State),
    ¬ Native cfg cfg.initBaseAssetId → ¬ Native cfg 0 →
    Contracts.BridgedStandardERC20.WellFormed tok → EscrowInv cfg a ⟨Sys.fresh sl, tok⟩

/-- **WHAT THE TRACKER CAN LET IN IS IN THE VAULT** (headline).  Along every composed run from a
state satisfying `EscrowInv`, for a registered asset `a` native here, with
`E := MAX - snapshot`: `MAX - chainBalance` is at most the vault's balance of the token, and so is
`E + Σout - Σin`. -/
def Properties.NativeReleasesAreEscrowed : Prop :=
  ∀ (cfg : Config) (a : AssetId) (e₀ e : EscrowSys), Native cfg a →
    EscrowInv cfg a e₀ → EscrowReach cfg a e₀ e → e.sys.st.isAssetRegistered a = true →
      MAX_TOKEN_BALANCE.val - (e.sys.st.chainBalance cfg.thisChain a).val ≤
          e.tok.balances cfg.ntv ∧
      (MAX_TOKEN_BALANCE.val - (e.sys.st.totalPreV31TotalSupply a).amount.val) +
          e.sys.audit.outflow a - e.sys.audit.inflow a ≤ e.tok.balances cfg.ntv

/-- **AN INBOUND NATIVE TRANSFER SUCCEEDS EXACTLY WITHIN THE CAP** (headline).  Along every
composed run from a state satisfying `EscrowInv`, for a registered asset `a` native here, a
nonzero vault address and a nonzero receiver, and an inbound transfer touching no L1 counter (the
source chain is not L1, or the chain does not settle on L1): the vault's inbound native path
(hook, then withdrawal) succeeds iff `Σin + amount ≤ E + Σout`. This is relative to the modelled
path (`runPath`); the vault's other checks (amount, pause, base-token and `msg.value` checks) are
not modelled. -/
def Properties.NativeInboundIffCap : Prop :=
  ∀ (cfg : Config) (a : AssetId) (e₀ e : EscrowSys) (chain : ChainId) (account : Address)
    (amount : UInt256),
    Native cfg a → EscrowInv cfg a e₀ → EscrowReach cfg a e₀ e →
    e.sys.st.isAssetRegistered a = true → cfg.ntv ≠ 0 → account ≠ 0 →
    (chain ≠ e.sys.st.l1ChainId ∨ e.sys.sl ≠ e.sys.st.l1ChainId) →
      ((∃ x, runPath cfg .nativeIn e.sys.st e.sys.sl e.tok chain a account amount = some x) ↔
        e.sys.audit.inflow a + amount.val ≤
          (MAX_TOKEN_BALANCE.val - (e.sys.st.totalPreV31TotalSupply a).amount.val) +
            e.sys.audit.outflow a)

/-- **THE WITHDRAWAL NEVER FAILS AFTER THE HOOK ACCEPTS.**  Along every composed run from a state
satisfying `EscrowInv`, for an asset `a` native here (registered or not), a nonzero vault address
and a nonzero receiver: the vault's inbound native path succeeds iff the tracker's hook, reading
the token as it is, succeeds. -/
def Properties.NativeInboundFailsOnlyAtTheHook : Prop :=
  ∀ (cfg : Config) (a : AssetId) (e₀ e : EscrowSys) (chain : ChainId) (account : Address)
    (amount : UInt256),
    Native cfg a → EscrowInv cfg a e₀ → EscrowReach cfg a e₀ e → cfg.ntv ≠ 0 → account ≠ 0 →
      ((∃ x, runPath cfg .nativeIn e.sys.st e.sys.sl e.tok chain a account amount = some x) ↔
        ∃ st', pathHook cfg .nativeIn e.sys.st e.sys.sl (tokenReads cfg e.tok) chain a amount =
          some st')

/-- **A FUNDED OUTBOUND NATIVE TRANSFER GOES THROUGH** (headline).  Along every composed run from a
state satisfying `EscrowInv`, for an asset `a` native here (registered or not) whose token address
in the vault is set, on a chain with nonzero id and a nonzero vault address: for every depositor
other than the vault and the zero address that holds at least `amount`, the vault's outbound
native path (hook, then deposit) succeeds, provided that a transfer to L1 while the chain settles
on L1 does not raise `totalWithdrawalsToL1` past `2^256 - 1`.  The deposit is the token model's
transfer by the depositor: the allowance `safeTransferFrom` needs is not modelled. "Succeeds" is
relative to the modelled path (`runPath`); the vault's other checks (amount, pause, WETH and
`msg.value` checks) are not modelled. -/
def Properties.FundedNativeOutboundSucceeds : Prop :=
  ∀ (cfg : Config) (a : AssetId) (e₀ e : EscrowSys) (chain : ChainId) (account : Address)
    (amount : UInt256),
    Native cfg a → EscrowInv cfg a e₀ → EscrowReach cfg a e₀ e →
    cfg.thisChain ≠ 0 → cfg.ntvTokenAddress a ≠ 0 → cfg.ntv ≠ 0 →
    account ≠ 0 → account ≠ cfg.ntv → amount.val ≤ e.tok.balances account →
    (chain = e.sys.st.l1ChainId ∧ e.sys.sl = e.sys.st.l1ChainId →
      (e.sys.st.interopInfo a).totalWithdrawalsToL1.val + amount.val < UInt256.size) →
      ∃ x, runPath cfg .nativeOut e.sys.st e.sys.sl e.tok chain a account amount = some x

/-- **COUNTERMODEL: AN OUTSIDE FALL OF THE VAULT'S BALANCE BREAKS THE ESCROW.**  A composed run
from a state satisfying `EscrowInv` reaches a state where a native asset is registered; if the
ledger then changes, still well-formed, so that the vault's balance falls (not a `TokenMove`),
the tracker's hook accepts an inbound transfer of nonzero amount to a nonzero receiver that the
vault's withdrawal cannot pay, so the inbound path fails. -/
def Properties.EscrowNeedsVaultOnlyOutflow : Prop :=
  ∃ (cfg : Config) (a : AssetId) (e₀ e : EscrowSys) (tok' : Contracts.BridgedStandardERC20.State)
    (chain : ChainId) (account : Address) (amount : UInt256) (st' : Storage),
    Native cfg a ∧ EscrowInv cfg a e₀ ∧ EscrowReach cfg a e₀ e ∧
    e.sys.st.isAssetRegistered a = true ∧ cfg.ntv ≠ 0 ∧ account ≠ 0 ∧ amount ≠ 0 ∧
    Contracts.BridgedStandardERC20.WellFormed tok' ∧
    tok'.balances cfg.ntv < e.tok.balances cfg.ntv ∧
    pathHook cfg .nativeIn e.sys.st e.sys.sl (tokenReads cfg tok') chain a amount = some st' ∧
    runPath cfg .nativeIn e.sys.st e.sys.sl tok' chain a account amount = none

/-! ## Non-vacuity -/

/-- **A NONTRIVIAL COMPOSED RUN.**  A fresh tracker next to a well-formed ledger in which the vault
already holds a nonzero balance; a composed run to `e` in which the native asset `a` is
registered, with nonzero outflow and inflow, and in which the vault's balance strictly exceeds
`MAX - chainBalance`; at `e`, a depositor other than the vault holding a nonzero `amount` can
move it out to a chain that is not L1, and an inbound transfer of `amount` from that chain to a
nonzero receiver succeeds. -/
def Properties.NativeEscrowSatisfiable : Prop :=
  ∃ (cfg : Config) (a : AssetId) (sl : ChainId) (tok₀ : Contracts.BridgedStandardERC20.State)
    (e : EscrowSys) (chain : ChainId) (account receiver : Address) (amount : UInt256),
    Native cfg a ∧ cfg.thisChain ≠ 0 ∧ cfg.ntvTokenAddress a ≠ 0 ∧ cfg.ntv ≠ 0 ∧
    EscrowInv cfg a ⟨Sys.fresh sl, tok₀⟩ ∧ EscrowReach cfg a ⟨Sys.fresh sl, tok₀⟩ e ∧
    0 < tok₀.balances cfg.ntv ∧
    e.sys.st.guardInitialized = true ∧ e.sys.st.isAssetRegistered a = true ∧
    0 < e.sys.audit.outflow a ∧ 0 < e.sys.audit.inflow a ∧
    MAX_TOKEN_BALANCE.val - (e.sys.st.chainBalance cfg.thisChain a).val < e.tok.balances cfg.ntv ∧
    account ≠ 0 ∧ account ≠ cfg.ntv ∧ receiver ≠ 0 ∧ amount ≠ 0 ∧
    amount.val ≤ e.tok.balances account ∧ chain ≠ e.sys.st.l1ChainId ∧
    (∃ x, runPath cfg .nativeOut e.sys.st e.sys.sl e.tok chain a account amount = some x) ∧
    (∃ x, runPath cfg .nativeIn e.sys.st e.sys.sl e.tok chain a receiver amount = some x)

end Contracts.L2AssetTracker
