import EraSpec.Codegen.Lang
import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashEncoding

/-!
# External calls, hooks and `bytes`: an extension of the contract language

`Codegen.Lang` has no way to call another contract, no `bytes`, no `msg.value` and
no `if`.  The vault's preparation path (`NativeTokenVaultBase.bridgeBurn`) needs all
of them.  This module adds them *on top of* `Codegen.Lang`, without changing it: every
`Codegen.Stmt` is a statement here (`XStmt.base`) and runs exactly as `Codegen.execStmt`
says.  What is new:

* `call target f args bind`: a high-level external call `target.f(args)`, sent by the
  running contract with no value.  What the callee does is **not** part of the
  language: a `Machine` supplies it (`VM-CALL`).  If the callee fails, the caller fails
  with the same revert data, Solidity's default for high-level calls.  A returned
  value is stored in a local; a value of the wrong kind (a call that returns nothing
  where a word is expected) fails with empty revert data, as the ABI decoder does.
* `hook name args bind`: an `internal virtual` function the contract declares without
  a body (`_handleBridgeToChain`, `_getERC20GettersInner`).  Its meaning is supplied by
  the `Machine` too.  A hook sees and changes only the machine's world `W`, never the
  running contract's own storage: that restriction is part of the interface
  (`DEP-FRAME`).
* `assign x e` (`x = e;`) and a one-statement `ifThen c s` (`if (c) { s }`).
* `bytes`: parameters and locals of type `bytes`; `requireLength x n r`
  (`require(x.length == n, r)`); `decode x outs`, `abi.decode` of static types with the
  decoder's range checks; `encode x args`, `abi.encode` of words and `bytes` in the
  standard head/tail layout (`abiEncode`); and `retBytes x`.
* `msg.value` and `block.chainid` are read as the variables `"msg.value"` and
  `"block.chainid"`, bound by `xcall` before the body runs.  No Solidity identifier
  contains a dot, so no parameter or local can shadow them, and `Codegen.Emit` prints
  `.var "msg.value"` as `msg.value`.
* A non-payable function called with value fails with empty revert data.
* Logs carry the address of the contract that emitted them, so a callee's logs and the
  caller's own logs interleave in emission order.

A failure discards everything the call did, to the contract's storage, the world and
the logs (`VM-REVERT`): `xcall` returns either the final state or revert data, never
both.

**What this is not.**  Not a Solidity semantics, and there is no emitter for these
constructs: programs written with them are compared with their source by review, not
by generated Solidity (`GEN-EMIT` covers only `Codegen.Emit`).  There is no reentrancy:
a `Machine`'s callee is a function of the world, and the callee this package uses
(`Codegen.call` of a `Codegen.Lang` contract) makes no calls back.
-/

namespace Codegen.Calls

open Codegen

abbrev Bytes := List UInt8

/-! ## `abi.encode` and `abi.decode` -/

/-- A value `abi.encode` takes, or a call passes: a static word, or a dynamic byte
string. -/
inductive AbiVal
  | word (w : Word)
  | bytes (b : Bytes)
deriving DecidableEq, Repr

/-- A 32-byte big-endian word: `AttackVectors.BundleHashEncoding.word`. -/
abbrev word32 (n : ℕ) : Bytes := AttackVectors.BundleHashEncoding.word n

/-- `b`, right-padded with zero bytes to a multiple of 32. -/
abbrev pad32 (b : Bytes) : Bytes := AttackVectors.BundleHashEncoding.pad32 b

/-- Reading big-endian bytes as a number. -/
abbrev fromBytes (b : Bytes) : ℕ := AttackVectors.BundleHashEncoding.fromBytesBE b

/-- An argument's tail: nothing for a word; for `bytes`, its length word followed by
its contents right-padded to a multiple of 32. -/
def AbiVal.tail : AbiVal → Bytes
  | .word _ => []
  | .bytes b => word32 b.length ++ pad32 b

/-- The heads.  `off` is the offset, from the start of the encoding, at which the next
tail begins: a word's head is the word, a `bytes` argument's head is its offset. -/
def heads (off : ℕ) : List AbiVal → Bytes
  | [] => []
  | .word w :: vs => word32 w.val ++ heads off vs
  | .bytes b :: vs => word32 off ++ heads (off + (AbiVal.bytes b).tail.length) vs

/-- **`abi.encode(v₁, …, vₙ)`**: `n` 32-byte heads, then the tails in argument order.
The first tail starts right after the heads, at `32 * n`. -/
def abiEncode (vs : List AbiVal) : Bytes :=
  heads (32 * vs.length) vs ++ (vs.map AbiVal.tail).flatten

/-- Whether a decoded word is in range for its static type: the ABI decoder reverts on
an address above `2^160` or a bool above `1`. -/
def fits : Ty → ℕ → Bool
  | .uint256, _ => true
  | .address, v => decide (v < 2 ^ 160)
  | .bool, v => decide (v < 2)

/-- `abi.decode(b, (T₁, …, Tₖ))` for static types, binding the words to `outs` in
`env`.  `none` if `b` is shorter than `32 k` bytes or a word does not fit its type.
Trailing bytes are ignored, as the decoder does. -/
def decodeInto (b : Bytes) (env : String → Word) : List Param → Option (String → Word)
  | [] => some env
  | p :: ps =>
      if 32 ≤ b.length ∧ fits p.ty (fromBytes (b.take 32)) = true then
        decodeInto (b.drop 32) (upd env p.name (fromBytes (b.take 32) : Word)) ps
      else none

/-! ## Syntax -/

/-- The language's types: a `Codegen.Ty`, or `bytes`. -/
inductive XTy
  | base (t : Ty)
  | bytes
deriving DecidableEq, Repr

structure XParam where
  name : String
  ty : XTy
deriving Repr

/-- What a function, an external call or a hook returns. -/
inductive Ret
  | none
  | word (w : Word)
  | bytes (b : Bytes)
deriving DecidableEq, Repr

/-- Where a returned value goes: discarded, a word local, or a `bytes` local. -/
inductive Bind
  | none
  | word (x : String)
  | bytes (x : String)
deriving DecidableEq, Repr

/-- An argument of `abi.encode`: a word-typed expression or a `bytes` local. -/
inductive AbiArg
  | word (ty : Ty) (e : Expr)
  | bytes (x : String)
deriving Repr

inductive XStmt
  /-- Any statement of `Codegen.Lang`, with its meaning there. -/
  | base (s : Stmt)
  /-- `x = e;` to a declared local or parameter. -/
  | assign (x : String) (e : Expr)
  /-- `if (c) { s }`. -/
  | ifThen (c : Cond) (s : XStmt)
  /-- `target.fname(args)`, storing the returned value as `bind` says. -/
  | call (target : Expr) (fname : String) (args : List Expr) (bind : Bind)
  /-- A call to the bodiless `internal virtual` function `name`. -/
  | hook (name : String) (args : List Expr) (bind : Bind)
  /-- `require(x.length == n, r);` for a `bytes` variable `x`. -/
  | requireLength (x : String) (n : ℕ) (r : Reason)
  /-- `(T₁ o₁, …, Tₖ oₖ) = abi.decode(x, (T₁, …, Tₖ));` for static types. -/
  | decode (x : String) (outs : List Param)
  /-- `bytes memory x = abi.encode(args);` -/
  | encode (x : String) (args : List AbiArg)
  /-- `return x;` for a `bytes` variable. -/
  | retBytes (x : String)
deriving Repr

structure XFn where
  name : String
  params : List XParam
  returns : Option XTy
  payable : Bool
  body : List XStmt
deriving Repr

/-- A contract.  No constructor: the programs written here are run from a given
storage, not deployed. -/
structure XContract where
  name : String
  scalars : List Param
  maps : List (String × Ty × Ty)
  errors : List ErrorDecl
  events : List EventDecl
  fns : List XFn
deriving Repr

def XContract.find (c : XContract) (name : String) : Option XFn :=
  c.fns.find? (fun fn => decide (fn.name = name))

/-! ## Semantics -/

/-- Revert data: the base language's, or empty (a call to an address without the
function, a value that does not decode, value sent to a non-payable function). -/
inductive XFailure
  | data (f : Failure)
  | empty
deriving DecidableEq, Repr

/-- A log entry and the address of the contract that emitted it. -/
structure XLog where
  emitter : Word
  log : Log
deriving DecidableEq, Repr

/-- The rest of the world, as the running contract sees it.  `W` is whatever state the
callees and hooks have. -/
structure Machine (W : Type) where
  /-- `call w self target fname args`: `self` calls `target.fname(args)` with no value.
  On success: the world afterwards, the returned value, and the callee's logs. -/
  call : W → Word → Word → String → List Word → Except XFailure (W × Ret × List XLog)
  /-- `hook w name args`: the bodiless internal function `name` on `args`. -/
  hook : W → String → List Word → Except XFailure (W × Ret)

/-- The name `msg.value` is read under. -/
def msgValue : String := "msg.value"

/-- The name `block.chainid` is read under. -/
def blockChainId : String := "block.chainid"

/-- The fixed context of one external call to the program. -/
structure Env where
  /-- The program's own address: the sender of its calls and the emitter of its logs. -/
  self : Word
  sender : Word
  value : Word
  chainId : Word

structure XFrame (W : Type) where
  st : Storage
  w : W
  cx : Ctx
  benv : String → Bytes
  logs : List XLog

variable {W : Type}

/-- Store a returned value. -/
def bindRet (f : XFrame W) : Bind → Ret → Except XFailure (XFrame W)
  | .none, _ => .ok f
  | .word x, .word v => .ok { f with cx := { f.cx with env := upd f.cx.env x v } }
  | .bytes x, .bytes b => .ok { f with benv := upd f.benv x b }
  | .word _, .none | .word _, .bytes _ | .bytes _, .none | .bytes _, .word _ => .error .empty

def evalAbiArg (f : XFrame W) : AbiArg → Except Failure AbiVal
  | .word _ e =>
      match evalExpr f.st f.cx e with
      | .ok v => .ok (.word v)
      | .error err => .error err
  | .bytes x => .ok (.bytes (f.benv x))

def evalAbiArgs (f : XFrame W) : List AbiArg → Except Failure (List AbiVal)
  | [] => .ok []
  | a :: as =>
      match evalAbiArg f a, evalAbiArgs f as with
      | .ok v, .ok vs => .ok (v :: vs)
      | .error err, _ => .error err
      | .ok _, .error err => .error err

/-- One statement.  `some r` in the result means the function returned `r`. -/
def execX (M : Machine W) (self : Word) (f : XFrame W) :
    XStmt → Except XFailure (XFrame W × Option Ret)
  | .base s =>
      match execStmt ⟨f.st, f.cx, []⟩ s with
      | .ok (g, r) =>
          .ok ({ f with st := g.st, cx := g.cx, logs := f.logs ++ g.logs.map (XLog.mk self) },
            r.map Ret.word)
      | .error err => .error (.data err)
  | .assign x e =>
      match evalExpr f.st f.cx e with
      | .ok v => .ok ({ f with cx := { f.cx with env := upd f.cx.env x v } }, none)
      | .error err => .error (.data err)
  | .ifThen c s =>
      match evalCond f.st f.cx c with
      | .ok true => execX M self f s
      | .ok false => .ok (f, none)
      | .error err => .error (.data err)
  | .call t fname args b =>
      match evalExpr f.st f.cx t, evalList f.st f.cx args with
      | .ok tv, .ok vs =>
          match M.call f.w self tv fname vs with
          | .ok (w', r, logs) =>
              match bindRet { f with w := w', logs := f.logs ++ logs } b r with
              | .ok g => .ok (g, none)
              | .error err => .error err
          | .error err => .error err
      | .error err, _ => .error (.data err)
      | .ok _, .error err => .error (.data err)
  | .hook name args b =>
      match evalList f.st f.cx args with
      | .ok vs =>
          match M.hook f.w name vs with
          | .ok (w', r) =>
              match bindRet { f with w := w' } b r with
              | .ok g => .ok (g, none)
              | .error err => .error err
          | .error err => .error err
      | .error err => .error (.data err)
  | .requireLength x n r =>
      if (f.benv x).length = n then .ok (f, none)
      else .error (.data (reasonFailure f.st f.cx r))
  | .decode x outs =>
      match decodeInto (f.benv x) f.cx.env outs with
      | some env => .ok ({ f with cx := { f.cx with env := env } }, none)
      | none => .error .empty
  | .encode x args =>
      match evalAbiArgs f args with
      | .ok vs => .ok ({ f with benv := upd f.benv x (abiEncode vs) }, none)
      | .error err => .error (.data err)
  | .retBytes x => .ok (f, some (.bytes (f.benv x)))

def execXBody (M : Machine W) (self : Word) (f : XFrame W) :
    List XStmt → Except XFailure (XFrame W × Option Ret)
  | [] => .ok (f, none)
  | s :: rest =>
      match execX M self f s with
      | .ok (f', none) => execXBody M self f' rest
      | .ok (f', some r) => .ok (f', some r)
      | .error err => .error err

/-- Bind ABI arguments to parameters: words to word parameters, byte strings to `bytes`
parameters.  `none` on a wrong arity or kind. -/
def bindXParams : List XParam → List AbiVal → Option ((String → Word) × (String → Bytes))
  | [], [] => some (fun _ => 0, fun _ => [])
  | ⟨x, .base _⟩ :: ps, .word v :: vs => (bindXParams ps vs).map fun e => (upd e.1 x v, e.2)
  | ⟨x, .bytes⟩ :: ps, .bytes v :: vs => (bindXParams ps vs).map fun e => (e.1, upd e.2 x v)
  | _, _ => none

/-- A successful call: the program's storage, the world, logs in emission order, and
the returned value. -/
structure XSuccess (W : Type) where
  st : Storage
  w : W
  logs : List XLog
  ret : Option Ret

/-- An external call to the program.  `none`: no such function, or wrong arity or
argument kinds (the dispatcher reverts with empty data; outside every claim here).  A
failure carries no state: every write, to the program's storage and to the world, is
discarded. -/
def xcall (M : Machine W) (c : XContract) (fname : String) (e : Env) (args : List AbiVal)
    (st : Storage) (w : W) : Option (Except XFailure (XSuccess W)) :=
  match c.find fname with
  | none => none
  | some fn =>
      match bindXParams fn.params args with
      | none => none
      | some (env, benv) =>
          some (if fn.payable = false ∧ e.value ≠ 0 then .error .empty
            else
              match execXBody M e.self
                  ⟨st, w, ⟨e.sender, upd (upd env msgValue e.value) blockChainId e.chainId⟩,
                    benv, []⟩ fn.body with
              | .ok (f, r) => .ok ⟨f.st, f.w, f.logs, r⟩
              | .error err => .error err)

end Codegen.Calls
