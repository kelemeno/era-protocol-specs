import Lake
open Lake DSL

/-
  era-protocol-specs — the PROTOCOL-LEVEL specification of ZKsync Era's atomic
  interop, with no EVM semantics in its trusted base.

  DEPENDENCY POLICY (load-bearing — do not relax):

    Mathlib and nothing else.

  This package must never depend on Clear, on solc output, or on any model of the
  EVM.  Every theorem here is a statement about the PROTOCOL: abstract states,
  guarded operations, and the invariants relating them.  The Mathlib revision is
  pinned to the selected Mathlib revision for reproducibility. This package has
  no dependency on the older `contracts-formal-verification` repository.

  `EraSpec.Core.Word` locally defines the 256-bit word type (a `Fin 2^256` wrapper).
  Its historical origin is described in that file's header; no Clear module is
  imported.
-/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "09d33efc68d3ad52db77b731d7253675395a14aa"

package «era-protocol-specs» {
  leanOptions := #[⟨`autoImplicit, false⟩]
}

@[default_target]
lean_lib «EraSpec» {
  roots := #[`EraSpec]
}
