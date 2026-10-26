import EraSpec.Core.Word

/-!
# A restricted contract language with an executable semantics

The language `CODE_GENERATION.md` proposes: small enough to emit as reviewable
Solidity, explicit enough that its interpreter states the source-level behaviour
a proof relies on.  Everything an abstract model leaves implicit is a
construct here, with a meaning fixed by `call` / `deploy` below:

* storage is named 256-bit scalars and `word → word` mappings, zero on deploy;
* `msg.sender` is a value of the call context;
* `+`/`-` carry a `checked` flag: checked arithmetic fails with `Panic(0x11)` on
  overflow/underflow, unchecked arithmetic wraps modulo `2^256`;
* `require` fails with an `Error(string)` message or a custom error and its
  arguments, and a failure discards the whole call — storage *and* logs;
* events append to an ordered log.

**What this is not.**  It is not a Solidity semantics.  The claim that the
Solidity printed by `EraSpec.Codegen.Emit` behaves as this interpreter says is
the trusted emitter boundary `GEN-EMIT` in `ASSUMPTIONS.md`.  The construct set
is deliberately the minimum for which that boundary is easy to review line by
line, and the differential tests in `solidity/` exercise it.

Types are carried for emission only.  Addresses are words below `2^160`; the
interpreter does not range-check them, so theorems take well-typed arguments as
an explicit premise (`SOL-ABI`: the ABI decoder rejects dirty address words).
-/

namespace Codegen

/-- Solidity types the emitter can print. -/
inductive Ty
  | uint256
  | address
  | bool
deriving DecidableEq, Repr

abbrev Word := UInt256

inductive Expr
  /-- A typed literal; the type picks the Solidity spelling (`address(0)`, `true`). -/
  | lit (ty : Ty) (n : ℕ)
  /-- A parameter or local. -/
  | var (x : String)
  | sender
  | sload (slot : String)
  | mload (map : String) (key : Expr)
  /-- `a + b`; `checked = false` must be emitted inside `unchecked { }`. -/
  | add (checked : Bool) (a b : Expr)
  | sub (checked : Bool) (a b : Expr)
deriving Repr

inductive Cond
  | eq (a b : Expr)
  | ne (a b : Expr)
  | ge (a b : Expr)
deriving Repr

inductive Reason
  /-- `require(c, "msg")`: reverts with `Error(string)`. -/
  | message (msg : String)
  /-- `require(c, Err(args))`: reverts with the custom error. -/
  | custom (name : String) (args : List Expr)
deriving Repr

inductive Stmt
  | require (c : Cond) (r : Reason)
  | local_ (ty : Ty) (x : String) (e : Expr)
  | sstore (slot : String) (e : Expr)
  | mstore (map : String) (key value : Expr)
  | emit (event : String) (args : List Expr)
  | ret (e : Expr)
deriving Repr

structure Param where
  name : String
  ty : Ty
deriving Repr

structure EventParam where
  name : String
  ty : Ty
  indexed : Bool
deriving Repr

structure EventDecl where
  name : String
  params : List EventParam
deriving Repr

structure ErrorDecl where
  name : String
  params : List Param
deriving Repr

inductive Mutability
  | nonpayable
  | view
deriving DecidableEq, Repr

structure Fn where
  name : String
  params : List Param
  returns : Option Ty
  mutability : Mutability
  body : List Stmt
deriving Repr

structure Contract where
  name : String
  scalars : List Param
  /-- `(name, keyType, valueType)`. -/
  maps : List (String × Ty × Ty)
  errors : List ErrorDecl
  events : List EventDecl
  ctorParams : List Param
  ctorBody : List Stmt
  fns : List Fn
deriving Repr

/-! ## Semantics -/

structure Storage where
  scalars : String → Word
  maps : String → Word → Word

/-- Fresh contract storage (`VM-STORAGE`, `VM-DEPLOY`). -/
def Storage.zero : Storage := ⟨fun _ => 0, fun _ _ => 0⟩

/-- Revert data, before ABI encoding. -/
inductive Failure
  | message (msg : String)
  | custom (name : String) (args : List Word)
  | panic (code : ℕ)
deriving DecidableEq, Repr

structure Log where
  event : String
  args : List Word
deriving DecidableEq, Repr

structure Ctx where
  sender : Word
  env : String → Word

def upd {α : Type} (f : String → α) (k : String) (v : α) : String → α :=
  fun x => if x = k then v else f x

/-- Solidity's arithmetic-overflow panic code. -/
def panicOverflow : ℕ := 0x11

def evalExpr (st : Storage) (cx : Ctx) : Expr → Except Failure Word
  | .lit _ n => .ok (n : Word)
  | .var x => .ok (cx.env x)
  | .sender => .ok cx.sender
  | .sload s => .ok (st.scalars s)
  | .mload m k =>
      match evalExpr st cx k with
      | .ok kv => .ok (st.maps m kv)
      | .error e => .error e
  | .add c a b =>
      match evalExpr st cx a, evalExpr st cx b with
      | .ok x, .ok y =>
          if c = true ∧ UInt256.size ≤ x.val + y.val then .error (.panic panicOverflow)
          else .ok (x + y)
      | .error e, _ => .error e
      | .ok _, .error e => .error e
  | .sub c a b =>
      match evalExpr st cx a, evalExpr st cx b with
      | .ok x, .ok y =>
          if c = true ∧ x.val < y.val then .error (.panic panicOverflow)
          else .ok (x - y)
      | .error e, _ => .error e
      | .ok _, .error e => .error e

def evalList (st : Storage) (cx : Ctx) : List Expr → Except Failure (List Word)
  | [] => .ok []
  | e :: es =>
      match evalExpr st cx e, evalList st cx es with
      | .ok v, .ok vs => .ok (v :: vs)
      | .error err, _ => .error err
      | .ok _, .error err => .error err

def evalCond (st : Storage) (cx : Ctx) : Cond → Except Failure Bool
  | .eq a b => match evalExpr st cx a, evalExpr st cx b with
      | .ok x, .ok y => .ok (decide (x = y))
      | .error e, _ => .error e
      | .ok _, .error e => .error e
  | .ne a b => match evalExpr st cx a, evalExpr st cx b with
      | .ok x, .ok y => .ok (decide (x ≠ y))
      | .error e, _ => .error e
      | .ok _, .error e => .error e
  | .ge a b => match evalExpr st cx a, evalExpr st cx b with
      | .ok x, .ok y => .ok (decide (y.val ≤ x.val))
      | .error e, _ => .error e
      | .ok _, .error e => .error e

def reasonFailure (st : Storage) (cx : Ctx) : Reason → Failure
  | .message m => .message m
  | .custom n args =>
      match evalList st cx args with
      | .ok vs => .custom n vs
      | .error e => e

structure Frame where
  st : Storage
  cx : Ctx
  logs : List Log

/-- One statement.  `some v` in the result means the function returned `v`. -/
def execStmt (f : Frame) : Stmt → Except Failure (Frame × Option Word)
  | .require c r =>
      match evalCond f.st f.cx c with
      | .ok true => .ok (f, none)
      | .ok false => .error (reasonFailure f.st f.cx r)
      | .error e => .error e
  | .local_ _ x e =>
      match evalExpr f.st f.cx e with
      | .ok v => .ok ({ f with cx := { f.cx with env := upd f.cx.env x v } }, none)
      | .error err => .error err
  | .sstore s e =>
      match evalExpr f.st f.cx e with
      | .ok v => .ok ({ f with st := { f.st with scalars := upd f.st.scalars s v } }, none)
      | .error err => .error err
  | .mstore m k e =>
      match evalExpr f.st f.cx k, evalExpr f.st f.cx e with
      | .ok kv, .ok v =>
          .ok ({ f with st := { f.st with
            maps := upd f.st.maps m (fun w => if w = kv then v else f.st.maps m w) } }, none)
      | .error err, _ => .error err
      | .ok _, .error err => .error err
  | .emit ev args =>
      match evalList f.st f.cx args with
      | .ok vs => .ok ({ f with logs := f.logs ++ [⟨ev, vs⟩] }, none)
      | .error err => .error err
  | .ret e =>
      match evalExpr f.st f.cx e with
      | .ok v => .ok (f, some v)
      | .error err => .error err

def execBody (f : Frame) : List Stmt → Except Failure (Frame × Option Word)
  | [] => .ok (f, none)
  | s :: rest =>
      match execStmt f s with
      | .ok (f', none) => execBody f' rest
      | .ok (f', some v) => .ok (f', some v)
      | .error e => .error e

def bindParams : List Param → List Word → Option (String → Word)
  | [], [] => some (fun _ => 0)
  | p :: ps, v :: vs => (bindParams ps vs).map (fun env => upd env p.name v)
  | _, _ => none

def Contract.find (c : Contract) (name : String) : Option Fn :=
  c.fns.find? (fun fn => decide (fn.name = name))

/-- A successful call: final storage, logs in emission order, return value. -/
structure Success where
  st : Storage
  logs : List Log
  ret : Option Word

/-- An external call.  `none`: no such function, or wrong arity (the dispatcher
reverts with empty data; outside every claim here).  A failure carries no
storage — the call's writes and logs are discarded (`VM-REVERT`). -/
def call (c : Contract) (fname : String) (sender : Word) (args : List Word) (st : Storage) :
    Option (Except Failure Success) :=
  match c.find fname with
  | none => none
  | some fn =>
      match bindParams fn.params args with
      | none => none
      | some env =>
          some (match execBody ⟨st, ⟨sender, env⟩, []⟩ fn.body with
            | .ok (f, r) => .ok ⟨f.st, f.logs, r⟩
            | .error e => .error e)

/-- Deployment: the constructor body on fresh storage. -/
def deploy (c : Contract) (sender : Word) (args : List Word) :
    Option (Except Failure Success) :=
  match bindParams c.ctorParams args with
  | none => none
  | some env =>
      some (match execBody ⟨Storage.zero, ⟨sender, env⟩, []⟩ c.ctorBody with
        | .ok (f, r) => .ok ⟨f.st, f.logs, r⟩
        | .error e => .error e)

end Codegen
