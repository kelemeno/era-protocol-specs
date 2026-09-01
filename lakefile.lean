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
  pinned to the one `contracts-formal-verification` uses, so that repo can consume
  this one as a dependency without a toolchain conflict.

  `EraSpec.Word` vendors the 256-bit word type (a `Fin 2^256` wrapper) that Clear
  also defines.  It is vendored rather than imported precisely to keep this
  package Clear-free; see that file's header for the fidelity argument.
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
