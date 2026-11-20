import EraSpec.Contracts.InteropHandlerBase.Specs.BundleStatusMachineFaithful
import EraSpec.Contracts.InteropHandlerBase.History.Specs.BundleStatusMachine

/-! **History: a record of the interop pin `c67894b9`, not a claim about era-contracts `b17415d20`.**
The labelled machine `LStep` labels the pin's edges: an inclusion-proof `executeBundle`/`verifyBundle`
on both layers and an `executeAtomicBundle` that admits `Unreceived` only
(pin `L2InteropHandler.sol:79`). At `b17415d20` L2 has no inclusion-proof entry point; its
`verifyAtomicBundle` (`interop/interop-handler/L2InteropHandler.sol:83-92`) is a flow-gated
`Unreceived → Verified` edge `LStep` lacks, and `executeAtomicBundle` (`:61-78`) admits `Verified`
and skips the flow gate for it. The never-published statements rest on the pin's argument that an
atomic bundle never reaches `Verified`, and `VerifiedBundleRunsWithoutAnyGate` on the pin's atomic
entry refusing `Verified`. The `b17415d20` gate results are in topic `Reentrancy`
(`DeliveryNeedsTheGateAtV35`, `VerifiedBundleExecutesWithoutTheGateAtV35`). Namespaces carry a
`History` segment. -/

namespace AttackVectors.BundleStatusMachine.Faithful.History

open AttackVectors.BundleStatusMachine

/-- The four entry points, as edge labels. -/
inductive EntryPoint
  | verifyBundle
  | executeBundle
  | unbundleBundle
  | executeAtomicBundle
  deriving DecidableEq, Repr

/-- The authentication an edge consults before it is taken. -/
inductive Check
  /-- `_verifyBundle`'s L1 message-inclusion proof for the bundle's bytes (:296-316). -/
  | inclusionProof
  /-- `requireFlowFinalized`, the atomicity gate (`L2InteropHandler.sol:83`). -/
  | flowGate
  /-- Neither the inclusion proof nor the flow gate: the edge is admitted on the bundle's status and
  the reject-only checks (pause, caller permission, destination context) that the model omits. -/
  | noCheck
  deriving DecidableEq, Repr

/-- **The deployed edges**, each labelled by the entry point that takes it and the check it
consults. -/
inductive LStep : Status → EntryPoint → Check → Status → Prop
  /-- `verifyBundle` (:157-160). -/
  | verify : LStep .Unreceived .verifyBundle .inclusionProof .Verified
  /-- `executeBundle` of an `Unreceived` bundle: `_verifyBundle` first (:123). -/
  | executeFresh : LStep .Unreceived .executeBundle .inclusionProof .FullyExecuted
  /-- `executeBundle` of a `Verified` bundle: `:123` is skipped, so no inclusion proof and no flow
  gate is consulted (only the pause, destination-context and execution-address checks of :87-112,
  which `executeAtomicBundle` shares). -/
  | executeVerified : LStep .Verified .executeBundle .noCheck .FullyExecuted
  /-- `unbundleBundle` of a `Verified` bundle (:195-198). -/
  | unbundleFirst : LStep .Verified .unbundleBundle .noCheck .Unbundled
  /-- `unbundleBundle` of an `Unbundled` bundle. -/
  | unbundleAgain : LStep .Unbundled .unbundleBundle .noCheck .Unbundled
  /-- `executeAtomicBundle` (`L2InteropHandler.sol:79-86`). -/
  | executeAtomic : LStep .Unreceived .executeAtomicBundle .flowGate .FullyExecuted

/-- Labelled paths, recording the checks consulted along the way in order. -/
inductive LReach : Status → List Check → Status → Prop
  | refl (s : Status) : LReach s [] s
  | tail {a b d : Status} {cs : List Check} {e : EntryPoint} {c : Check} :
      LReach a cs b → LStep b e c d → LReach a (cs ++ [c]) d

end AttackVectors.BundleStatusMachine.Faithful.History
