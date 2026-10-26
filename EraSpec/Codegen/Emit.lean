import EraSpec.Codegen.Lang

/-!
# Solidity emission

A pretty-printer from `Codegen.Contract` to Solidity 0.8.28 source.  It is
**unverified**: that the printed source means what `Codegen.call` says is the
`GEN-EMIT` boundary in `ASSUMPTIONS.md`.  The printer is kept to a one-line
correspondence per construct so that boundary can be reviewed by reading the
table below next to `Lang.lean`:

| Construct | Printed as |
|---|---|
| `lit .address n` / `lit .uint256 n` / `lit .bool n` | `address(n)` / `n` / `true`·`false` |
| `var x`, `sender`, `sload s`, `mload m k` | `x`, `msg.sender`, `s`, `m[k]` |
| `add c a b`, `sub c a b` | `(a + b)`, `(a - b)`; a statement containing an unchecked one is wrapped in `unchecked { }` |
| `require c (message m)` / `(custom E args)` | `require(c, "m");` / `require(c, E(args));` |
| `local_ ty x e`, `sstore s e`, `mstore m k e` | `ty x = e;`, `s = e;`, `m[k] = e;` |
| `emit E args`, `ret e` | `emit E(args);`, `return e;` |

Two shapes are refused rather than printed, because Solidity's meaning would
differ from the interpreter's:

* a statement mixing checked and unchecked arithmetic — `unchecked` is a block,
  not an operator, so one of the two would be printed with the wrong flavour;
* a custom-error argument containing checked arithmetic — Solidity evaluates
  `require`'s error arguments even when the condition holds, so such an argument
  could panic where the interpreter succeeds.

Undeclared names and type errors are not checked here: `solc` rejects them, and
the build in `solidity/` compiles every emitted file.
-/

namespace Codegen.Emit

open Codegen

def ty : Ty → String
  | .uint256 => "uint256"
  | .address => "address"
  | .bool => "bool"

/-- Which arithmetic flavours an expression contains: `(checked, unchecked)`. -/
def flavours : Expr → Bool × Bool
  | .lit _ _ | .var _ | .sender | .sload _ => (false, false)
  | .mload _ k => flavours k
  | .add c a b | .sub c a b =>
      let (ca, ua) := flavours a
      let (cb, ub) := flavours b
      (c || ca || cb, !c || ua || ub)

def flavoursList (es : List Expr) : Bool × Bool :=
  es.foldr (fun e acc => let (c, u) := flavours e; (c || acc.1, u || acc.2)) (false, false)

def expr : Expr → String
  | .lit .address n => s!"address({n})"
  | .lit .uint256 n => toString n
  | .lit .bool n => if n = 0 then "false" else "true"
  | .var x => x
  | .sender => "msg.sender"
  | .sload s => s
  | .mload m k => s!"{m}[{expr k}]"
  | .add _ a b => s!"({expr a} + {expr b})"
  | .sub _ a b => s!"({expr a} - {expr b})"

def args (es : List Expr) : String := ", ".intercalate (es.map expr)

def cond : Cond → String
  | .eq a b => s!"{expr a} == {expr b}"
  | .ne a b => s!"{expr a} != {expr b}"
  | .ge a b => s!"{expr a} >= {expr b}"

def condExprs : Cond → List Expr
  | .eq a b | .ne a b | .ge a b => [a, b]

def stmtExprs : Stmt → List Expr
  | .require c (.message _) => condExprs c
  | .require c (.custom _ es) => condExprs c ++ es
  | .local_ _ _ e | .sstore _ e | .ret e => [e]
  | .mstore _ k e => [k, e]
  | .emit _ es => es

def stmtCore : Stmt → String
  | .require c (.message m) => s!"require({cond c}, \"{m}\");"
  | .require c (.custom n es) => s!"require({cond c}, {n}({args es}));"
  | .local_ t x e => s!"{ty t} {x} = {expr e};"
  | .sstore s e => s!"{s} = {expr e};"
  | .mstore m k e => s!"{m}[{expr k}] = {expr e};"
  | .emit ev es => s!"emit {ev}({args es});"
  | .ret e => s!"return {expr e};"

def stmt (indent : String) (s : Stmt) : Except String String := do
  if let .require _ (.custom n es) := s then
    if (flavoursList es).1 then
      throw s!"custom error {n}: checked arithmetic in an error argument"
  let (c, u) := flavoursList (stmtExprs s)
  if c && u then throw s!"statement mixes checked and unchecked arithmetic: {stmtCore s}"
  if u then pure s!"{indent}unchecked \{ {stmtCore s} }"
  else pure s!"{indent}{stmtCore s}"

def params (ps : List Param) : String := ", ".intercalate (ps.map fun p => s!"{ty p.ty} {p.name}")

def body (ss : List Stmt) : Except String String := do
  let lines ← ss.mapM (stmt "        ")
  pure ("\n".intercalate lines)

def fn (f : Fn) : Except String String := do
  let mut_ := match f.mutability with | .view => " view" | .nonpayable => ""
  let ret := match f.returns with | some t => s!" returns ({ty t})" | none => ""
  let b ← body f.body
  pure s!"    function {f.name}({params f.params}) external{mut_}{ret} \{\n{b}\n    }"

def eventDecl (e : EventDecl) : String :=
  let ps := e.params.map fun p => s!"{ty p.ty}{if p.indexed then " indexed" else ""} {p.name}"
  s!"    event {e.name}({", ".intercalate ps});"

def errorDecl (e : ErrorDecl) : String := s!"    error {e.name}({params e.params});"

/-- The whole source file. `origin` names the Lean declaration it came from. -/
def contract (c : Contract) (origin : String) : Except String String := do
  let ctor ← body c.ctorBody
  let fns ← c.fns.mapM fn
  let decls :=
    c.errors.map errorDecl ++ c.events.map eventDecl ++ [""] ++
    c.scalars.map (fun p => s!"    {ty p.ty} internal {p.name};") ++
    c.maps.map (fun (m, k, v) => s!"    mapping({ty k} => {ty v}) internal {m};")
  pure <| "\n".intercalate <|
    [ "// SPDX-License-Identifier: MIT",
      s!"// GENERATED from `{origin}` by EraSpec/Codegen/Emit.lean. Do not edit:",
      "// regenerate with scripts/emit-solidity.sh, which also checks this file is current.",
      "pragma solidity 0.8.28;",
      "",
      s!"contract {c.name} \{" ] ++ decls ++
    [ "",
      s!"    constructor({params c.ctorParams}) \{",
      ctor,
      "    }",
      "" ] ++
    ("\n\n".intercalate fns) :: ["}", ""]

end Codegen.Emit
