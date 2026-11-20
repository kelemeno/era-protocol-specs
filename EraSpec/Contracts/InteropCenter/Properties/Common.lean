import EraSpec.Contracts.InteropCenter.Specs.Common
import EraSpec.Core.Headline

/-!
# Properties: the run-local hash and encoder premises can hold

Statements about `EraSpec.Contracts.InteropCenter.Specs.Common`. Proofs are in
`EraSpec.Contracts.InteropCenter.Proofs.Common`. The send model's results take their hash and
encoder premises in run-local form (`KeccakInjOn`, `EncInjOn` on the run's own preimages and
bundles), never globally. These two statements show that such premises are satisfiable: for every
list of bundles some encoder separates them, and for every list of byte strings no longer than the
word space some function into words is injective on it.
-/

namespace Contracts.InteropCenter

/-- **THE ENCODER PREMISE IS SATISFIABLE FOR EVERY LIST OF BUNDLES.** -/
@[witness] def Properties.EncInjOnSatisfiable : Prop :=
  ∀ L : List Bundle, ∃ enc : Bundle → List UInt8, EncInjOn enc L

/-- **THE KECCAK PREMISE IS SATISFIABLE FOR EVERY LIST NO LONGER THAN THE WORD SPACE.** -/
@[witness] def Properties.KeccakInjOnSatisfiable : Prop :=
  ∀ L : List (List UInt8), L.length ≤ UInt256.size → ∃ k : List UInt8 → Word, KeccakInjOn k L

end Contracts.InteropCenter
