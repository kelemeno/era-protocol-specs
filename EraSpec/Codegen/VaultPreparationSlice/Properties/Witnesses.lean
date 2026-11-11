import EraSpec.Codegen.VaultPreparationSlice.Specs.Correspondence
import EraSpec.Core.Simulation

/-!
# The refinement's premises are satisfiable

Non-vacuity of `Properties/Refinement.lean` and `Properties/MintDataBytes.lean`.  Each
premise is shown satisfiable on its own and jointly, on a concrete instance where the
model accepts a request, one where it rejects, and a run whose journal is not empty.
Proofs: `../Proofs/Witnesses.lean`.

* `HooksAgreeSatisfiable`: every pair of model hooks has implementations agreeing with
  it (the model hook run on the token state the storage represents).
* `EveryWellFormedStateIsRepresented`: every well-formed model state whose token has a
  nonzero vault has storages representing it.  `Rel` therefore constrains storage, not
  the model.
* `RefinementAcceptWitness`, `RefinementRejectWitness`: both directions of
  `BridgeBurnRefines` apply to some instance.
* `BridgeBurnSuccessWitness`: the premises of `BridgeBurnSuccessIsPreparation` and
  `BridgeBurnBacked` hold together, with returned mint data of nonzero amount.
* `JournalBackedNonTrivial`: the premises of `ReachableJournalBacked` hold with a run
  that journals a nonzero amount.
* `ViewCallWitness`: a view call succeeds (`VaultViewsChangeNothing`'s premise).
* `EncodeMintDataInjectiveWitness`: two mint tuples with metadata of different lengths
  have different encodings, so `EncodeMintDataInjective`'s premises are not merely
  `m = m'` in disguise.
-/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.BridgedStandardERC20 (Address)
open Contracts.NativeTokenVaultBase (State Hooks Request Result prepare WellFormed MintData)

/-- **THE HOOK PREMISE IS SATISFIABLE**, for every pair of model hooks. -/
def Properties.HooksAgreeSatisfiable : Prop :=
  ∀ {Acct : Type} (h : Hooks Acct), ∃ ch : CHooks Acct, HooksAgree ch h

/-- **EVERY WELL-FORMED MODEL STATE IS REPRESENTED** by some deployment and storages,
provided its token's vault is nonzero (`BridgedTokenSlice.Rel` requires it). -/
def Properties.EveryWellFormedStateIsRepresented : Prop :=
  ∀ {Acct : Type} (s : State Acct), WellFormed s → s.token.config.vault ≠ 0 →
    ∃ (d : Deployment) (st : Storage) (w : World Acct), Rel d st w s

/-- **THE REFINEMENT'S PREMISES, WITH A REQUEST THE MODEL ACCEPTS.** -/
def Properties.RefinementAcceptWitness : Prop :=
  ∃ (d : Deployment) (ch : CHooks Unit) (h : Hooks Unit) (st : Storage) (w : World Unit)
    (s : State Unit) (r : Request) (out : Result Unit),
    HooksAgree ch h ∧ WellFormed s ∧ Rel d st w s ∧ prepare h s r = some out

/-- **THE REFINEMENT'S PREMISES, WITH A REQUEST THE MODEL REJECTS.** -/
def Properties.RefinementRejectWitness : Prop :=
  ∃ (d : Deployment) (ch : CHooks Unit) (h : Hooks Unit) (st : Storage) (w : World Unit)
    (s : State Unit) (r : Request),
    HooksAgree ch h ∧ WellFormed s ∧ Rel d st w s ∧ prepare h s r = none

/-- **A SUCCESSFUL CALL FROM A REPRESENTED STATE**, returning mint data of nonzero
amount. -/
def Properties.BridgeBurnSuccessWitness : Prop :=
  ∃ (d : Deployment) (ch : CHooks Unit) (h : Hooks Unit) (st : Storage) (w : World Unit)
    (s : State Unit) (caller : Address) (value c l2v a oc : Word) (data : Bytes)
    (res : XSuccess (World Unit)),
    HooksAgree ch h ∧ WellFormed s ∧ Rel d st w s ∧ oc.val < 2 ^ 160 ∧
    xcall (d.machine ch) vaultProgram "bridgeBurn" (d.env caller value)
      [.word c, .word l2v, .word a, .word oc, .bytes data] st w = some (.ok res) ∧
    mintAmount res.ret ≠ 0

/-- **A RUN THAT JOURNALS A NONZERO AMOUNT**, from a state satisfying the premises of
`ReachableJournalBacked`. -/
def Properties.JournalBackedNonTrivial : Prop :=
  ∃ (d : Deployment) (ch : CHooks Unit) (h : Hooks Unit) (s₀ : State Unit) (sys₀ sys : Sys Unit),
    HooksAgree ch h ∧ WellFormed s₀ ∧ Rel d sys₀.vault sys₀.world s₀ ∧ sys₀.journal = [] ∧
    LayeredVerification.Run (Step d ch) sys₀ sys ∧ 0 < journalTotal sys.journal

/-- **A VIEW CALL SUCCEEDS**, from any storage. -/
def Properties.ViewCallWitness : Prop :=
  ∀ {Acct : Type} (d : Deployment) (ch : CHooks Acct) (caller : Address) (st : Storage)
    (w : World Acct),
    ∃ res, xcall (d.machine ch) vaultProgram "paused" (d.env caller 0) [] st w = some (.ok res)

/-- **DIFFERENT TUPLES, DIFFERENT BYTES, WITHIN THE PREMISES**: two tuples whose metadata
lengths are below `2^256` and differ have different encodings. -/
def Properties.EncodeMintDataInjectiveWitness : Prop :=
  ∃ m m' : MintData, m.metadata.length < 2 ^ 256 ∧ m'.metadata.length < 2 ^ 256 ∧
    m ≠ m' ∧ encodeMintData m ≠ encodeMintData m'

end Codegen.VaultPreparationSlice
