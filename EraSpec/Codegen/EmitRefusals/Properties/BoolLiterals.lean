import EraSpec.Codegen.EmitRefusals.Specs.BoolLiterals

/-!
# Properties: the emitter prints only the Bool literals 0 and 1

`Codegen.evalExpr` gives `lit .bool n` the word `n` (modulo `2^256`).  Solidity's only
Bool values are `false` and `true`, the words 0 and 1.  `Codegen.Emit.stmt` therefore refuses a
statement that contains any other Bool literal.  These statements say the refusal is
complete, still lets the literals 0 and 1 through (shown on specific inputs, not for
every statement), and catches the review's counterexample.  Proofs:
`../Proofs/BoolLiterals.lean`.

* `AcceptedStmtBoolLiteralsCanonical`, `AcceptedBoolLiteralsCanonical`: every Bool
  literal in a statement or a contract that the emitter accepts is 0 or 1, in any
  operand and at any depth.
* `AcceptedBoolLiteralsPrintTheirWord`: such a literal is printed as the Solidity
  value of the word the interpreter gives it: `false` for 0 and `true` for 1.
* `NoncanonicalBoolLiteralRefused`: the same fact read as a refusal.  A statement or a
  contract containing a Bool literal above 1 is not printed.
* `BoolTwoEqOneRefused`, `BoolWrapsToZeroRefused`: the two regression inputs.  For each,
  the interpreter's result is stated, together with what the statement printer
  `stmtCore` spells for it.  The refusal stops that spelling from reaching a file.
* `CanonicalBoolLiteralsPrinted`: the literals 0 and 1 are still printed, exactly.
* `AcceptedBoolLiteralsWitness`: the premises of the acceptance statements are jointly
  satisfiable, for the literal 1 and for the literal 0.  The literal 1 comes from the
  committed token program.  `NoncanonicalBoolLiteralWitness` does the same for the
  refusal, with the review's counterexample.

What this does not prove: `GEN-EMIT`.  There is no Solidity semantics here.  That
Solidity's `false` and `true` are the words 0 and 1 is a fact about Solidity that the
statements rely on; it is not a theorem.
-/

namespace Codegen.EmitRefusals

open Codegen Codegen.Emit

/-- **EVERY BOOL LITERAL OF AN ACCEPTED STATEMENT IS 0 OR 1.** If `Emit.stmt` prints `s`,
every `lit .bool n` occurring in any expression of `s`, at any depth, has `n = 0` or
`n = 1`. -/
def Properties.AcceptedStmtBoolLiteralsCanonical : Prop :=
  ∀ (indent : String) (s : Stmt) (out : String), stmt indent s = .ok out →
    ∀ e, StmtOperand s e → ∀ n, BoolLitIn n e → n = 0 ∨ n = 1

/-- **EVERY BOOL LITERAL OF AN ACCEPTED CONTRACT IS 0 OR 1.** If `Emit.contract` prints `c`,
every `lit .bool n` occurring in its constructor or in any of its functions has `n = 0`
or `n = 1`. -/
def Properties.AcceptedBoolLiteralsCanonical : Prop :=
  ∀ (c : Contract) (origin src : String), contract c origin = .ok src →
    ∀ s, ContractStmt c s → ∀ e, StmtOperand s e → ∀ n, BoolLitIn n e → n = 0 ∨ n = 1

/-- **AN ACCEPTED BOOL LITERAL IS PRINTED AS ITS OWN WORD.** In a contract `Emit.contract`
prints, every Bool literal evaluates, in every storage and call context, to the word 0
and is printed `false`, or evaluates to the word 1 and is printed `true`. -/
def Properties.AcceptedBoolLiteralsPrintTheirWord : Prop :=
  ∀ (c : Contract) (origin src : String), contract c origin = .ok src →
    ∀ s, ContractStmt c s → ∀ e, StmtOperand s e → ∀ n, BoolLitIn n e →
      ∀ (st : Storage) (cx : Ctx),
        (evalExpr st cx (.lit .bool n) = .ok 0 ∧ expr (.lit .bool n) = "false") ∨
        (evalExpr st cx (.lit .bool n) = .ok 1 ∧ expr (.lit .bool n) = "true")

/-- **A BOOL LITERAL ABOVE 1 IS REFUSED, ANYWHERE.** A statement containing one is refused
at every indentation, and so is every contract with such a statement in its constructor
or in a function. -/
def Properties.NoncanonicalBoolLiteralRefused : Prop :=
  (∀ (indent : String) (s : Stmt) (e : Expr) (n : ℕ), StmtOperand s e → BoolLitIn n e →
      1 < n → ∃ msg, stmt indent s = .error msg) ∧
  (∀ (c : Contract) (origin : String) (s : Stmt) (e : Expr) (n : ℕ), ContractStmt c s →
      StmtOperand s e → BoolLitIn n e → 1 < n → ∃ msg, contract c origin = .error msg)

/-- **REGRESSION: THE REVIEW'S COUNTEREXAMPLE.** The interpreter reverts on
`boolTwoEqOne` with `"different"`, in every frame.  The statement printer spells it
`require(true == true, "different");`, which passes in Solidity.  The emitter refuses the
statement at every indentation, and refuses the contract `boolProbe boolTwoEqOne` that
contains it (every other such contract is covered by `NoncanonicalBoolLiteralRefused`). -/
def Properties.BoolTwoEqOneRefused : Prop :=
  (∀ f : Frame, execStmt f boolTwoEqOne = .error (.message "different")) ∧
  stmtCore boolTwoEqOne = "require(true == true, \"different\");" ∧
  (∀ indent, ∃ msg, stmt indent boolTwoEqOne = .error msg) ∧
  (∀ origin, ∃ msg, contract (boolProbe boolTwoEqOne) origin = .error msg)

/-- **REGRESSION: A BOOL LITERAL THAT WRAPS.** The interpreter returns the word 0 for
`return lit .bool (2^256)`, in every frame.  The statement printer spells it
`return true;`.  The emitter refuses the statement at every indentation, and refuses the
contract `boolProbe boolWrapsToZero` that contains it. -/
def Properties.BoolWrapsToZeroRefused : Prop :=
  (∀ f : Frame, execStmt f boolWrapsToZero = .ok (f, some 0)) ∧
  stmtCore boolWrapsToZero = "return true;" ∧
  (∀ indent, ∃ msg, stmt indent boolWrapsToZero = .error msg) ∧
  (∀ origin, ∃ msg, contract (boolProbe boolWrapsToZero) origin = .error msg)

/-- **THE LITERALS 0 AND 1 ARE STILL PRINTED, EXACTLY.** The canonical neighbour of the
counterexample passes in the interpreter, in every frame, and is printed
`require(true == true, "different");`.  `return lit .bool 1` and `return lit .bool 0` are
printed `return true;` and `return false;`. -/
def Properties.CanonicalBoolLiteralsPrinted : Prop :=
  (∀ f : Frame, execStmt f boolOneEqOne = .ok (f, none)) ∧
  stmt "" boolOneEqOne = .ok "require(true == true, \"different\");" ∧
  stmt "" (.ret (.lit .bool 1)) = .ok "return true;" ∧
  stmt "" (.ret (.lit .bool 0)) = .ok "return false;"

/-- **THE PREMISES ARE SATISFIABLE, FOR 1 AND FOR 0.** The committed token program is
accepted, and one of its statements, which the emitter also accepts on its own, contains
the literal 1.  Some accepted contract has an accepted statement containing the literal
0.  Neither disjunct of `AcceptedBoolLiteralsCanonical` can therefore be dropped. -/
def Properties.AcceptedBoolLiteralsWitness : Prop :=
  (∃ (src out : String) (s : Stmt) (e : Expr),
    contract BridgedTokenSlice.program "Codegen.BridgedTokenSlice.program" = .ok src ∧
    ContractStmt BridgedTokenSlice.program s ∧ stmt "        " s = .ok out ∧
    StmtOperand s e ∧ BoolLitIn 1 e) ∧
  (∃ (c : Contract) (origin src out : String) (s : Stmt) (e : Expr),
    contract c origin = .ok src ∧ ContractStmt c s ∧ stmt "        " s = .ok out ∧
    StmtOperand s e ∧ BoolLitIn 0 e)

/-- **THE REFUSAL'S PREMISES ARE SATISFIABLE.** Some contract has a statement containing a
Bool literal above 1: the review's counterexample, in `boolProbe boolTwoEqOne`. -/
def Properties.NoncanonicalBoolLiteralWitness : Prop :=
  ∃ (c : Contract) (s : Stmt) (e : Expr) (n : ℕ),
    ContractStmt c s ∧ StmtOperand s e ∧ BoolLitIn n e ∧ 1 < n

end Codegen.EmitRefusals
