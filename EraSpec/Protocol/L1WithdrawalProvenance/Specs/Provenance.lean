import EraSpec.Contracts.L1InteropHandler.Specs.WithdrawalGate
import EraSpec.Contracts.L1Messenger.Specs.SenderKeying

/-!
# Model: L1 withdrawal provenance, from the L1 gate to the modelled source chains

Source: era-contracts branch `draft/v0.35.0` at head `b17415d20` (also main `70096e2ea`; see the two
component models). This file composes two models without adding steps:

* `Contracts.L1WithdrawalGate` (`L1InteropHandler/Specs/WithdrawalGate.lean`): the L1 handler, whose
  `_verifyBundle` asks the `MessageRoot` whether the message `{txNumberInBatch, L2_INTEROP_CENTER_ADDR,
  BUNDLE_IDENTIFIER ++ bytes}` of chain `proof.chainId` was included, and records each passing check as a
  `Verification`;
* `Contracts.L1MessengerKeying` (`L1Messenger/Specs/SenderKeying.lean`): one source chain's L2→L1
  output, written by its center's L1 dispatches, other accounts' messages, direct hook calls, leaf
  inserts and bootloader logs. The center's L1 dispatch is modelled by its shape (`WithdrawalShape`, the
  guard of the `withdrawal` step), argued from source in that file's header, not transcribed.

**This file is definitions only.** The results are in
`EraSpec.Protocol.L1WithdrawalProvenance.Properties.Provenance` and are proved in
`EraSpec.Protocol.L1WithdrawalProvenance.Proofs.Provenance`.

## The premises that join them

Each premise constrains only the chains that the L1 run's committed verifications name (as
`v.proof.chainId`); a chain no verification names is unconstrained.

* `InclusionSoundOn` (`PROTO-EVIDENCE`, on the run's own accepted queries): for every committed
  verification, the log `proveL2MessageInclusionShared` proves for the queried message
  (`MessageHashing._l2MessageToLog`, `common/libraries/MessageHashing.sol:27-37`) is in the output of the
  chain the proof names. This is what the settlement-layer roots and the Merkle path are trusted to give;
  it is not derived here.
* `ChainsRunTheModelOn`: the output of every chain a verification names is the output of a run from
  genesis of the modelled code as that chain (`PROTO-EVIDENCE` for the source chain's code; only ZKsync
  OS chains running the `b17415d20` center and messenger are modelled).
* `HooksAsDocumentedOn`: the VM premise `HooksAsDocumented` of `Contracts.L1MessengerKeying`, on every
  chain a verification names.
* `DispatchRoundTripOn` (`SOL-ABI`): `abi.decode` returns the bundle that `abi.encode` encoded, for the
  bundles dispatched by the chains the verifications name.

The conclusion names keccak collisions on two strings of the run: the bytes `executeBundle` or
`unbundleBundle` decoded and the bytes a verification checked (the `Verified` shortcut), or the
message the L1 verification queried and the message the center sent.
-/

namespace Contracts.L1WithdrawalProvenance

open Contracts.L1WithdrawalGate
open Contracts.L1MessengerKeying (HookSem HooksAsDocumented ChainParams L2State Reach
  l2AssetRouterAddr wGatedHooks wUngatedHooks wS₄)

/-- **The evidence premise**, on the run's own accepted queries: every committed verification's queried
message log is in the output of the chain its proof names. -/
def InclusionSoundOn (C : Codec) (out : ℕ → List L2Log) (l : List Effect) : Prop :=
  ∀ v ∈ verifications l, msgToLog C v.query ∈ out v.proof.chainId

instance (C : Codec) (out : ℕ → List L2Log) (l : List Effect) :
    Decidable (InclusionSoundOn C out l) := by
  unfold InclusionSoundOn; infer_instance

/-- Every chain named by a committed verification of `l` (as `v.proof.chainId`) has as its output that
of a run from genesis of the modelled L2 code, as that chain. -/
def ChainsRunTheModelOn (C : Codec) (Q : ℕ → ChainParams) (H : ℕ → HookSem) (runs : ℕ → L2State)
    (l : List Effect) : Prop :=
  ∀ v ∈ verifications l, (Q v.proof.chainId).chainId = v.proof.chainId ∧
    Reach C (Q v.proof.chainId) (H v.proof.chainId) L2State.init (runs v.proof.chainId)

/-- The VM premise `HooksAsDocumented`, on every chain named by a committed verification of `l`. -/
def HooksAsDocumentedOn (C : Codec) (H : ℕ → HookSem) (l : List Effect) : Prop :=
  ∀ v ∈ verifications l, HooksAsDocumented C (H v.proof.chainId)

/-- `abi.decode` inverts `abi.encode` on every bundle dispatched by a chain named by a committed
verification of `l`. -/
def DispatchRoundTripOn (C : Codec) (runs : ℕ → L2State) (l : List Effect) : Prop :=
  ∀ v ∈ verifications l, ∀ w ∈ (runs v.proof.chainId).dispatched,
    C.decode (C.enc w.bundle) = some w.bundle

/-- The delivery `d` is call `0` of a bundle that the center of chain `d.senderChain` dispatched to L1
(a `withdrawal` step of that chain's modelled run): the delivered bytes are that bundle's encoding, the
bundle has one call, the ERC-7786 sender is `L2_ASSET_ROUTER_ADDR`, the call went to `L1_ASSET_ROUTER`
with value zero, and the handler was not paused. -/
def DispatchedWithdrawal (P : Params) (runs : ℕ → L2State) (d : Delivery) : Prop :=
  ∃ w ∈ (runs d.senderChain).dispatched, d.bytes = P.codec.enc w.bundle ∧
    w.bundle.calls.length = 1 ∧ d.index = 0 ∧ d.senderAddr = l2AssetRouterAddr ∧ d.value = 0 ∧
    d.target = P.router ∧ d.pausedNow = false

instance (P : Params) (runs : ℕ → L2State) (d : Delivery) :
    Decidable (DispatchedWithdrawal P runs d) := by
  unfold DispatchedWithdrawal; infer_instance

/-- The message the L1 verification `v` queried and a message the center of its chain sent collide
under keccak. -/
def MessageClash (P : Params) (runs : ℕ → L2State) (v : Verification) : Prop :=
  ∃ w ∈ (runs v.proof.chainId).dispatched,
    KeccakClash P.codec (bundleIdentifier :: v.bytes) (bundleIdentifier :: P.codec.enc w.bundle)

instance (P : Params) (runs : ℕ → L2State) (v : Verification) :
    Decidable (MessageClash P runs v) := by
  unfold MessageClash; infer_instance

/-! ## Witness data -/

/-- Every chain `c` stores L1 chain id `1`. -/
def wQ (c : ℕ) : ChainParams := ⟨c, 1⟩

/-- Chain `270` ran `wS₄ H`; every other chain has no output. -/
def wRuns (H : HookSem) (c : ℕ) : L2State := if c = 270 then wS₄ H else L2State.init

/-- A proof of the message of chain `270` in transaction `2`, as sent by the center. -/
def wProofTx2 : InclusionProof := ⟨270, 5, 2, ⟨2, l2InteropCenterAddr, [0x99]⟩, []⟩

/-- `verifyBundle` of `[2]` (the two-call `wTwo`) with that proof, accepted. -/
def wVerifyTx2 : Tx := ⟨1, .verifyBundle wAnyone [2] wProofTx2 true, []⟩

end Contracts.L1WithdrawalProvenance
