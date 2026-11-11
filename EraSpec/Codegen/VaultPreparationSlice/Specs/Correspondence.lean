import EraSpec.Codegen.VaultPreparationSlice.Specs.Program
import EraSpec.Codegen.BridgedTokenSlice.Specs.Correspondence
import EraSpec.Contracts.NativeTokenVaultBase.Specs.RepresentationPreparation
import EraSpec.Protocol.AssetBridgePreparation.Specs.Model

/-!
# The world the vault program runs in, and how it represents the vault model

The definitions the refinement statements are phrased in.  To review:

* `machine`: what the vault's calls and hooks do.  The token program runs at the
  deployment's token address and nothing else has code; the two hooks are a `CHooks`.
* `Rel`: when the vault's storage, the token's storage and the accounting state
  represent a model state of `Contracts.NativeTokenVaultBase`.
* `HooksAgree`: when the hooks agree with the model's `Hooks`.
* `requestArgs`, `encodeBurnData`, `encodeMintData`: the ABI bytes a model request and
  a model result stand for.
* `Step`: any successful call to either contract, the vault's journaled.

## The world

The vault calls two kinds of thing.  Its token (`IBridgedStandardToken(token).bridgeBurn`,
`.originToken()`) is `tokenProgram`, a `Codegen.Lang` program run by `Codegen.call`.  Its
two bodiless internal functions are hooks.  `_handleBridgeToChain` is, at the pin, a
no-op on L1 for a bridged token (`L1NativeTokenVault.sol:260-264` records `bridgedOut`
only for native ones) and the asset tracker's `handleInitiateBridgingOnL2` on L2
(`L2NativeTokenVault.sol:296-302`).  `_getERC20GettersInner` is the token's
`name`/`symbol`/`decimals` getters encoded by `BridgeHelper.getERC20Getters`
(`BridgeHelper.sol:20-50`).  As in the model (`Contracts.NativeTokenVaultBase.Hooks`),
each hook may fail, the accounting hook reads the token before the burn and the
metadata hook after it, and neither writes the vault's storage or the token's
(`DEP-FRAME`): what a real tracker does beyond its result is outside this slice.

**Only the token has code.**  A call to any other address fails with empty revert data.
For an address without code that is what the EVM does.  It is also what the vault
itself does: it has no `bridgeBurn(address,uint256)` or `originToken()`.  The world
has no other token, so a request naming one fails, as the model's `InScope` says.

## The journal

The concrete system keeps a ghost journal: for every successful `bridgeBurn`, its
destination chain, asset id and returned value.  These are observations of the call,
its arguments and its return, not vault storage.  The journal is what lets the protocol
trace's pending obligations (`AssetBridgePreparation.Ledger.pending`) be stated about
the concrete system: the trace pairs each preparation's returned tuple with the same
two outer fields (`REP-PUBLISH`).
-/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.BridgedStandardERC20 (Address)
open Codegen.BridgedTokenSlice (addrWord)

/-! ## The world and its machine -/

/-- What the vault's calls and hooks can change: the token's storage and the accounting
dependency's state. -/
structure World (Acct : Type) where
  token : Storage
  acct : Acct

/-- The hooks' implementations, over the token's storage.  `account acc token chain asset
amount` is `_handleBridgeToChain(chain, asset, amount)` with the token's storage at the
time of the call; `metadata token originChain` is `_getERC20GettersInner`. -/
structure CHooks (Acct : Type) where
  account : Acct → Storage → Word → Word → Word → Except XFailure Acct
  metadata : Storage → Word → Except XFailure Bytes

/-- Where the two contracts are, and the chain they run on. -/
structure Deployment where
  vault : Address
  token : Address
  chainId : Word

variable {Acct : Type}

/-- The returned value of a `Codegen.Lang` function. -/
def retOf : Option Word → Ret
  | none => .none
  | some v => .word v

/-- **THE WORLD'S MACHINE.**  `tokenProgram` runs at `token`, called by the vault, and its
logs carry `token` as their emitter; a call to any other address fails with empty data.
The hooks run `ch` on the token's current storage; a hook call with another name or
arity fails with empty data, and so does the metadata hook for an address other than
`token`, which the vault never reaches: it asks for metadata only after a successful
call to the same address. -/
def machine (token : Word) (ch : CHooks Acct) : Machine (World Acct) where
  call w self target fname args :=
    if target = token then
      match Codegen.call tokenProgram fname self args w.token with
      | some (.ok r) => .ok (⟨r.st, w.acct⟩, retOf r.ret, r.logs.map (XLog.mk token))
      | some (.error e) => .error (.data e)
      | none => .error .empty
    else .error .empty
  hook w name args :=
    if name = "_handleBridgeToChain" then
      match args with
      | [c, a, m] =>
          match ch.account w.acct w.token c a m with
          | .ok acc => .ok (⟨w.token, acc⟩, .none)
          | .error e => .error e
      | _ => .error .empty
    else if name = "_getERC20GettersInner" then
      match args with
      | [t, o] =>
          if t = token then
            match ch.metadata w.token o with
            | .ok b => .ok (w, .bytes b)
            | .error e => .error e
          else .error .empty
      | _ => .error .empty
    else .error .empty

/-- The machine of a deployment. -/
abbrev Deployment.machine (d : Deployment) (ch : CHooks Acct) : Machine (World Acct) :=
  VaultPreparationSlice.machine (addrWord d.token) ch

/-- The context of a call to the vault by `caller` with `value`. -/
def Deployment.env (d : Deployment) (caller : Address) (value : Word) : Env :=
  ⟨addrWord d.vault, addrWord caller, value, d.chainId⟩

/-! ## Representation -/

open Contracts.NativeTokenVaultBase (State Hooks Request BurnData MintData)

/-- The token's storage represents a model token: `BridgedTokenSlice.Rel` (vault slot,
supply, balances of every address) and the two added slots. -/
structure TokenRel (st : Storage) (t : Contracts.BridgedStandardERC20.State) : Prop where
  base : BridgedTokenSlice.Rel st t
  originToken : st.scalars "_originToken" = addrWord t.config.originToken
  assetId : st.scalars "_assetId" = t.config.assetId

/-- **THE REPRESENTATION RELATION.**  The deployment's addresses and chain are the
model's; each vault slot holds the model's value; the registry mappings agree with the
model's registry at every asset id and every address; the origin chain is stored at the
tracked asset; the token's storage represents the model's token; and the accounting
state is the model's.  Mapping keys at or above `2^160` in `_assetIdOf` are
unconstrained: no ABI-valid call can name them. -/
structure Rel (d : Deployment) (st : Storage) (w : World Acct) (s : State Acct) : Prop where
  vault : s.config.vault = d.vault
  token : s.config.tokenAddress = d.token
  chainId : s.config.chainId = d.chainId
  router : st.scalars "_assetRouter" = addrWord s.config.router
  paused : st.scalars "_paused" = if s.paused then 1 else 0
  baseAsset : st.scalars "_baseTokenAssetId" = s.config.baseAssetId
  tokenFor : ∀ id, st.maps "_tokenAddress" id = addrWord (s.registry.tokenForAsset id)
  assetFor : ∀ a : Address, st.maps "_assetIdOf" (addrWord a) = s.registry.assetForToken a
  origin : st.maps "_originChainId" s.config.assetId = s.config.originChainId
  tokenState : TokenRel w.token s.token
  acct : w.acct = s.accounting

/-- **THE HOOKS AGREE WITH THE MODEL'S.**  On every token storage representing a model
token, each hook succeeds exactly when the model's does, with the same result; the
revert data of a failure is unconstrained. -/
def HooksAgree (ch : CHooks Acct) (h : Hooks Acct) : Prop :=
  (∀ acc st t c a m, TokenRel st t →
      (ch.account acc st c a m).toOption = h.account acc t c a m) ∧
  (∀ st t o, TokenRel st t → (ch.metadata st o).toOption = h.metadata t o)

/-! ## Requests and results as bytes -/

/-- `DataEncoding.encodeBridgeBurnData` (`DataEncoding.sol:35-41`):
`abi.encode(amount, receiver, tokenHint)`. -/
def encodeBurnData (b : BurnData) : Bytes :=
  abiEncode [.word b.amount, .word (addrWord b.receiver), .word (addrWord b.tokenHint)]

/-- The arguments of the call a model request stands for:
`bridgeBurn(destinationChain, l2MsgValue, assetId, depositor, encodeBurnData data)`. -/
def requestArgs (r : Request) : List AbiVal :=
  [ .word r.destinationChain, .word r.l2MsgValue, .word r.assetId, .word (addrWord r.depositor),
    .bytes (encodeBurnData r.data) ]

/-- `DataEncoding.encodeBridgeMintData` (`DataEncoding.sol:84-93`) of the model's tuple:
`abi.encode(originalCaller, remoteReceiver, originToken, amount, metadata)`. -/
def encodeMintData (m : MintData) : Bytes :=
  abiEncode [ .word (addrWord m.originalCaller), .word (addrWord m.remoteReceiver),
    .word (addrWord m.originToken), .word m.amount, .bytes m.metadata ]

/-- The logs of a successful preparation, in emission order: the token's `Transfer` and
`BridgeBurn` (`BridgedTokenSlice.burnLogs`), then the vault's `BridgeBurn`. -/
def prepareLogs (d : Deployment) (r : Request) : List XLog :=
  (BridgedTokenSlice.burnLogs r.depositor r.data.amount).map (XLog.mk (addrWord d.token)) ++
    [⟨addrWord d.vault, ⟨"BridgeBurn", [r.destinationChain, r.assetId, addrWord r.depositor,
      addrWord r.data.receiver, r.data.amount]⟩⟩]

/-- The token burn data names: the hint, or the token registered for the asset when the
hint is zero (`NativeTokenVaultBase.sol:363-367`). -/
def hintedToken (st : Storage) (a : Word) (b : BurnData) : Word :=
  if b.tokenHint = 0 then st.maps "_tokenAddress" a else addrWord b.tokenHint

/-- The `amount` word of returned mint data: the fourth head word, bytes 96 to 127. -/
def mintAmount : Option Ret → ℕ
  | some (.bytes b) => fromBytes ((b.drop 96).take 32)
  | _ => 0

/-! ## Any successful call, and the journal -/

/-- A successful `bridgeBurn`'s destination chain, asset id and returned value. -/
structure Entry where
  destinationChain : Word
  assetId : Word
  ret : Option Ret

structure Sys (Acct : Type) where
  vault : Storage
  world : World Acct
  journal : List Entry

/-- The total amount the journal's returned mint data carries. -/
def journalTotal (j : List Entry) : ℕ := (j.map fun e => mintAmount e.ret).sum

/-- ABI-valid arguments of a vault function: kinds match the parameters and every
address argument is below `2^160` (`SOL-ABI`). -/
def ArgFits (p : XParam) (v : AbiVal) : Prop :=
  match p.ty, v with
  | .base .address, .word w => w.val < 2 ^ 160
  | .base _, .word _ => True
  | .bytes, .bytes _ => True
  | _, _ => False

def AbiValid (fname : String) (args : List AbiVal) : Prop :=
  ∃ fn, vaultProgram.find fname = some fn ∧ List.Forall₂ ArgFits fn.params args

/-- ABI-valid arguments of a token function. -/
def TokenAbiValid (fname : String) (args : List Word) : Prop :=
  ∃ fn, tokenProgram.find fname = some fn ∧
    List.Forall₂ (fun p (v : Word) => p.ty = .address → v.val < 2 ^ 160) fn.params args

/-- **ANY SUCCESSFUL CALL** to either contract.  A call to the vault may come from any
address, with any value; a successful `bridgeBurn` is journaled with its first and
third arguments and its returned value.  A call to the token may come from any address
but the vault's: only the vault's code sends calls as the vault, and it does so only
inside `bridgeBurn`. -/
inductive Step (d : Deployment) (ch : CHooks Acct) : Sys Acct → Sys Acct → Prop
  | bridgeBurn {sys : Sys Acct} {caller : Address} {value c l2v a oc : Word} {data : Bytes}
      {r : XSuccess (World Acct)} :
      oc.val < 2 ^ 160 →
      xcall (d.machine ch) vaultProgram "bridgeBurn" (d.env caller value)
        [.word c, .word l2v, .word a, .word oc, .bytes data] sys.vault sys.world = some (.ok r) →
      Step d ch sys ⟨r.st, r.w, sys.journal ++ [⟨c, a, r.ret⟩]⟩
  | vaultCall {sys : Sys Acct} {fname : String} {caller : Address} {value : Word}
      {args : List AbiVal} {r : XSuccess (World Acct)} :
      fname ≠ "bridgeBurn" → AbiValid fname args →
      xcall (d.machine ch) vaultProgram fname (d.env caller value) args sys.vault sys.world =
        some (.ok r) →
      Step d ch sys ⟨r.st, r.w, sys.journal⟩
  | tokenCall {sys : Sys Acct} {fname : String} {caller : Address} {args : List Word}
      {r : Success} :
      caller ≠ d.vault → TokenAbiValid fname args →
      Codegen.call tokenProgram fname (addrWord caller) args sys.world.token = some (.ok r) →
      Step d ch sys ⟨sys.vault, { sys.world with token := r.st }, sys.journal⟩

/-! ## The protocol trace's side -/

/-- The journal entry a pending obligation of the protocol trace stands for. -/
def entryOf (o : AssetBridgePreparation.Obligation) : Entry :=
  ⟨o.destinationChain, o.assetId, some (.bytes (encodeMintData o.data))⟩

/-- A concrete system represents a trace ledger: its storages and world represent the
ledger's vault state, which is well formed, and its journal is the ledger's pending
list, entry by entry. -/
structure SysRel (d : Deployment) (sys : Sys Acct) (L : AssetBridgePreparation.Ledger Acct) :
    Prop where
  rel : Rel d sys.vault sys.world L.vault
  wf : Contracts.NativeTokenVaultBase.WellFormed L.vault
  journal : sys.journal = L.pending.map entryOf

end Codegen.VaultPreparationSlice
