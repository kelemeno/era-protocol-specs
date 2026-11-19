import EraSpec.Contracts.L2InteropRootStorage.Specs.Refinement

/-!
# Properties: the canonical storage model refines the `ok`-admitted model

Statements about `EraSpec.Contracts.L2InteropRootStorage.Specs.Refinement`; proofs are in
`EraSpec.Contracts.L2InteropRootStorage.Proofs.Refinement`.  No hash premise.

* `ToModelReadsTheStorage`, `ToModelEmpty`: the map reads every addressable key exactly, and takes
  fresh storage to fresh storage.
* `CanonicalCallIsModelStep`: every successful call of the canonical model is one `Step ok` of the
  model, for every `ok` that admits the call's imports.
* `CanonicalRunIsModelRun`: so every logged run of the canonical model is a `Reach ok` run of the
  model, for every `ok` that admits all its imports.

With `ok := fun _ => True` the premise on `ok` is empty, so every result of `Properties/Model.lean`
about runs (`WriteOnce`, `TimestampNotRewritable`, `ZeroTimestampIffAbsent`,
`EntriesAreAdmittedImports`, …) applies to the canonical model's runs read through `toModel`.
-/

namespace Contracts.L2InteropRootStorage

/-- **THE MAP READS THE STORAGE.** At every key the contract can address, `toModel` holds the
stored root and the stored timestamp's value. -/
def Properties.ToModelReadsTheStorage : Prop :=
  ∀ (S : Contracts.InteropRootStorage.State) (c b : UInt256),
    (toModel S).entries c b.val =
      ⟨(S.storedInteropRoots c b).root, (S.storedInteropRoots c b).timestamp.val⟩

/-- **FRESH STORAGE MAPS TO FRESH STORAGE.** -/
def Properties.ToModelEmpty : Prop :=
  toModel Contracts.InteropRootStorage.empty = empty

/-- **EVERY CANONICAL CALL IS A MODEL STEP.** If a call of the canonical model succeeds from `S`
and ends in `S'`, and `ok` admits each `InteropRoot` the call imports, then the model steps from
`toModel S` to `toModel S'` under `ok`. -/
def Properties.CanonicalCallIsModelStep : Prop :=
  ∀ (ok : RootIn → Prop) (S S' : Contracts.InteropRootStorage.State)
    (caller : Contracts.InteropRootStorage.Address) (c : Contracts.InteropRootStorage.Call),
    Contracts.InteropRootStorage.exec S caller c = some S' →
      (∀ r ∈ c.roots, ok (ofInteropRoot r)) → Step ok (toModel S) (toModel S')

/-- **EVERY CANONICAL RUN IS A MODEL RUN.** If the canonical model runs from `S` to `S'` with log
`log`, and `ok` admits every `InteropRoot` the log imports, then the model reaches `toModel S'`
from `toModel S` under `ok`. -/
def Properties.CanonicalRunIsModelRun : Prop :=
  ∀ (ok : RootIn → Prop) (S S' : Contracts.InteropRootStorage.State)
    (log : List (Contracts.InteropRootStorage.Address × Contracts.InteropRootStorage.Call)),
    Contracts.InteropRootStorage.ReachLog S S' log →
      (∀ r ∈ Contracts.InteropRootStorage.imports log, ok (ofInteropRoot r)) →
        Reach ok (toModel S) (toModel S')

end Contracts.L2InteropRootStorage
