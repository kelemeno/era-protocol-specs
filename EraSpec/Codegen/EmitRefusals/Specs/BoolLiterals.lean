import EraSpec.Codegen.Emit
import EraSpec.Codegen.BridgedTokenSlice.Specs.Program

/-!
# Bool literals and the emitter: vocabulary

`Codegen.evalExpr` gives `lit .bool n` the word `n` (modulo `2^256`), whatever `n` is.
Solidity has two Bool values, `false` and `true`, the words 0 and 1.  A Bool literal
other than 0 or 1 is either a word no Solidity Bool holds (`2`) or another name for 0
or 1 (`2^256`).  `Codegen.Emit.stmt` refuses any statement that contains one
(`Codegen.Emit.noncanonicalBool`), so only the literals 0 and 1 are printed.
Statements: `../Properties/BoolLiterals.lean`.

The definitions below say where a literal *occurs*.  They follow `Codegen.Lang`'s
syntax constructor by constructor and do not use the emitter's own traversal
(`Emit.stmtExprs`, `Emit.boolLits`), so the proofs also show that the traversal misses
no operand and no depth.

The regression inputs at the end are the review's counterexample and its neighbours.
-/

namespace Codegen.EmitRefusals

open Codegen

/-- `lit .bool n` occurs in `e`, at any depth. -/
inductive BoolLitIn (n : ℕ) : Expr → Prop
  | lit : BoolLitIn n (.lit .bool n)
  | mload {m : String} {k : Expr} : BoolLitIn n k → BoolLitIn n (.mload m k)
  | addLeft {c : Bool} {a b : Expr} : BoolLitIn n a → BoolLitIn n (.add c a b)
  | addRight {c : Bool} {a b : Expr} : BoolLitIn n b → BoolLitIn n (.add c a b)
  | subLeft {c : Bool} {a b : Expr} : BoolLitIn n a → BoolLitIn n (.sub c a b)
  | subRight {c : Bool} {a b : Expr} : BoolLitIn n b → BoolLitIn n (.sub c a b)

/-- `e` is one of the two operands of condition `c`. -/
def CondOperand : Cond → Expr → Prop
  | .eq a b, e | .ne a b, e | .ge a b, e => e = a ∨ e = b

/-- `e` is an expression of statement `s`: an operand of its condition, an argument of
its custom error or event, a mapping key, or the value it binds, stores or returns. -/
def StmtOperand : Stmt → Expr → Prop
  | .require c (.message _), e => CondOperand c e
  | .require c (.custom _ args), e => CondOperand c e ∨ e ∈ args
  | .local_ _ _ v, e | .sstore _ v, e | .ret v, e => e = v
  | .mstore _ k v, e => e = k ∨ e = v
  | .emit _ args, e => e ∈ args

/-- `s` is a statement of contract `c`: in its constructor or in one of its functions. -/
def ContractStmt (c : Contract) (s : Stmt) : Prop :=
  s ∈ c.ctorBody ∨ ∃ f ∈ c.fns, s ∈ f.body

/-! ## Regression inputs -/

/-- The review's counterexample: `require(lit .bool 2 == lit .bool 1, "different")`.  The
interpreter compares the words 2 and 1 and reverts.  Printed with both literals as
`true` it would read `require(true == true, "different");`, which passes. -/
def boolTwoEqOne : Stmt :=
  .require (.eq (.lit .bool 2) (.lit .bool 1)) (.message "different")

/-- Its canonical neighbour, `require(lit .bool 1 == lit .bool 1, "different")`. -/
def boolOneEqOne : Stmt :=
  .require (.eq (.lit .bool 1) (.lit .bool 1)) (.message "different")

/-- `return lit .bool (2^256)`.  The interpreter returns the word 0, because `n` is taken
modulo `2^256`, while a nonzero literal would be printed as `true`. -/
def boolWrapsToZero : Stmt := .ret (.lit .bool (2 ^ 256))

/-- A contract with one function whose body is `[s]`: the smallest context in which
`Emit.contract` prints a statement. -/
def boolProbe (s : Stmt) : Contract where
  name := "BoolProbe"
  scalars := []
  maps := []
  errors := []
  events := []
  ctorParams := []
  ctorBody := []
  fns := [⟨"probe", [], some .bool, .view, [s]⟩]

end Codegen.EmitRefusals
