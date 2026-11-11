import EraSpec.Codegen.VaultPreparationSlice.Specs.Correspondence
import EraSpec.Core.Simulation

/-!
# The vault program refines the preparation model

Statements connecting `Codegen.VaultPreparationSlice.vaultProgram`, run with the token
program by `machine`, to `Contracts.NativeTokenVaultBase.prepare`, whose payload and
ledger properties are already proved.  Proofs: `../Proofs/Refinement.lean`.

## The two directions

`BridgeBurnRefines` is the headline.  For a model request `r` and the call it stands
for (`requestArgs r`: the same fields, the burn data ABI-encoded):

* the model rejecting implies the program reverts;
* the model accepting with result `out` implies the program succeeds, leaves the
  vault's storage unchanged, reaches a world related to `out.state`, emits exactly
  `prepareLogs`, and **returns exactly the bytes `encodeMintData out.data`**, the ABI
  encoding of the model's mint tuple.

A forward simulation alone would admit a program that always reverts; this does not.
`BridgeBurnSuccessIsPreparation` is the converse for *any* ABI-valid call, not only
one built from a request: a successful call decodes to a request that the model
accepts, with the same outcome.

## What follows

* `BridgeBurnBacked`: the model's `preparation_backed` at the level of storage words and
  returned bytes.  The amount word of the returned bytes is nonzero and is exactly what
  left the original caller's balance slot and the supply slot; no other balance moved.
* `Simulation`: every successful call to either contract is matched by at most one step
  of the protocol preparation trace `AssetBridgePreparation.Step`, the journal tracking
  the trace's pending obligations.
* `ReachableJournalBacked`: in every state reachable from a related one with an empty
  journal, the supply slot plus the amounts of all journaled mint data equals the
  initial supply; balances sum to supply; the identity slots stay consistent.  Obtained
  from the trace's `reachable_conservation` by `safety_transfer`, not reproved.

## Premises

`HooksAgree ch h` (the two hooks behave as the model's), `WellFormed s` (the model's
ledger invariant and representation consistency) and `Rel d st w s` (the storages
represent `s`).  `Witnesses.lean` shows them jointly satisfiable, with a request the
model accepts and one it rejects, and a run whose journal is not empty.

## Alongside

`MintDataBytes.lean` states what `encodeMintData` is, byte by byte, and that the returned
bytes determine the mint tuple.  `RevertOrder.lean` states which check fails first, with
what revert data, which the model's `Option` cannot say.

## Scope

The interpreter of `Codegen.Calls` is the semantics here.  No Solidity is generated
from `vaultProgram`; it is compared with the source by review.  Nothing here concerns
the original vault's bytecode (`REP-VAULT` stays open for it).
-/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.BridgedStandardERC20 (Address)
open Codegen.BridgedTokenSlice (addrWord)
open Contracts.NativeTokenVaultBase (State Hooks Request prepare WellFormed)

/-! ## `bridgeBurn` -/

/-- **`bridgeBurn` IS THE MODEL'S `prepare`, BYTE FOR BYTE.**  Under agreeing hooks, a
well-formed model state and a storage representing it: the model rejects iff the
program reverts; on acceptance the program succeeds without writing the vault's storage,
reaches a related state, returns exactly the ABI encoding of the model's mint tuple, and
emits the token's `Transfer` and `BridgeBurn` then the vault's `BridgeBurn`. -/
def Properties.BridgeBurnRefines : Prop :=
  ∀ {Acct : Type} (d : Deployment) (ch : CHooks Acct) (h : Hooks Acct) (st : Storage)
    (w : World Acct) (s : State Acct) (r : Request),
    HooksAgree ch h → WellFormed s → Rel d st w s →
    (prepare h s r = none →
      ∃ e, xcall (d.machine ch) vaultProgram "bridgeBurn" (d.env r.caller r.msgValue)
        (requestArgs r) st w = some (.error e)) ∧
    (∀ out, prepare h s r = some out →
      ∃ res, xcall (d.machine ch) vaultProgram "bridgeBurn" (d.env r.caller r.msgValue)
          (requestArgs r) st w = some (.ok res) ∧
        res.st = st ∧ Rel d res.st res.w out.state ∧
        res.ret = some (.bytes (encodeMintData out.data)) ∧ res.logs = prepareLogs d r)

/-- **EVERY SUCCESSFUL `bridgeBurn` IS A PREPARATION.**  Any successful call with an
ABI-valid original caller, from a related state, is the call of a request (same caller,
value and words; its burn data's encoding is exactly the bytes passed) that the model
accepts, with the related outcome, exactly the encoded mint tuple returned, and exactly
`prepareLogs` emitted. -/
def Properties.BridgeBurnSuccessIsPreparation : Prop :=
  ∀ {Acct : Type} (d : Deployment) (ch : CHooks Acct) (h : Hooks Acct) (st : Storage)
    (w : World Acct) (s : State Acct) (caller : Address) (value c l2v a oc : Word)
    (data : Bytes) (res : XSuccess (World Acct)),
    HooksAgree ch h → WellFormed s → Rel d st w s → oc.val < 2 ^ 160 →
    xcall (d.machine ch) vaultProgram "bridgeBurn" (d.env caller value)
      [.word c, .word l2v, .word a, .word oc, .bytes data] st w = some (.ok res) →
    ∃ r out, r.caller = caller ∧ r.msgValue = value ∧ r.destinationChain = c ∧
      r.l2MsgValue = l2v ∧ r.assetId = a ∧ addrWord r.depositor = oc ∧
      encodeBurnData r.data = data ∧ prepare h s r = some out ∧
      res.st = st ∧ Rel d res.st res.w out.state ∧
      res.ret = some (.bytes (encodeMintData out.data)) ∧ res.logs = prepareLogs d r

/-- **THE RETURNED BYTES ARE BACKED.**  The model's `preparation_backed`, as a statement
about storage words and returned bytes only: after any successful call, the amount word
of the returned mint data is nonzero, and exactly that amount left the original caller's
balance slot and the supply slot; every other address's balance slot is unchanged. -/
def Properties.BridgeBurnBacked : Prop :=
  ∀ {Acct : Type} (d : Deployment) (ch : CHooks Acct) (h : Hooks Acct) (st : Storage)
    (w : World Acct) (s : State Acct) (caller : Address) (value c l2v a oc : Word)
    (data : Bytes) (res : XSuccess (World Acct)),
    HooksAgree ch h → WellFormed s → Rel d st w s → oc.val < 2 ^ 160 →
    xcall (d.machine ch) vaultProgram "bridgeBurn" (d.env caller value)
      [.word c, .word l2v, .word a, .word oc, .bytes data] st w = some (.ok res) →
    ∃ amount : Word, amount ≠ 0 ∧ mintAmount res.ret = amount.val ∧
      (res.w.token.maps "_balances" oc).val + amount.val = (w.token.maps "_balances" oc).val ∧
      (res.w.token.scalars "_totalSupply").val + amount.val =
        (w.token.scalars "_totalSupply").val ∧
      ∀ k : Address, addrWord k ≠ oc →
        res.w.token.maps "_balances" (addrWord k) = w.token.maps "_balances" (addrWord k)

/-! ## The other functions -/

/-- **THE VIEWS CHANGE NOTHING.**  A successful call to any vault function other than
`bridgeBurn` leaves the vault's storage and the world unchanged and emits no log. -/
def Properties.VaultViewsChangeNothing : Prop :=
  ∀ {Acct : Type} (d : Deployment) (ch : CHooks Acct) (fname : String) (caller : Address)
    (value : Word) (args : List AbiVal) (st : Storage) (w : World Acct)
    (res : XSuccess (World Acct)),
    fname ≠ "bridgeBurn" →
    xcall (d.machine ch) vaultProgram fname (d.env caller value) args st w = some (.ok res) →
    res.st = st ∧ res.w = w ∧ res.logs = []

/-! ## Every call, and what follows -/

/-- **A FORWARD SIMULATION** of the protocol preparation trace.  Every successful call,
to either contract, is matched by at most one trace step; the relation is `SysRel`. -/
def Properties.Simulation : Prop :=
  ∀ {Acct : Type} (d : Deployment) (ch : CHooks Acct) (h : Hooks Acct), HooksAgree ch h →
    ∃ sim : LayeredVerification.Simulation (Step d ch) (AssetBridgePreparation.Step h),
      ∀ sys L, sim.Rel sys L ↔ SysRel d sys L

/-- **THE JOURNAL IS BACKED BY BURNED SUPPLY, IN EVERY REACHABLE STATE.**  From a state
representing a well-formed model state, with an empty journal, along any sequence of
successful calls: the supply slot plus the amounts of all mint data returned so far is
the initial supply; the balances of all `2^160` addresses sum to the supply slot; the
token's vault slot is the vault; and the vault's `assetId` mapping at the token is the
token's asset id slot.  Transferred from `AssetBridgePreparation.reachable_conservation`
by `safety_transfer`. -/
def Properties.ReachableJournalBacked : Prop :=
  ∀ {Acct : Type} (d : Deployment) (ch : CHooks Acct) (h : Hooks Acct) (s₀ : State Acct)
    (sys₀ : Sys Acct),
    HooksAgree ch h → WellFormed s₀ → Rel d sys₀.vault sys₀.world s₀ → sys₀.journal = [] →
    ∀ sys, LayeredVerification.Run (Step d ch) sys₀ sys →
      (sys.world.token.scalars "_totalSupply").val + journalTotal sys.journal =
        (sys₀.world.token.scalars "_totalSupply").val ∧
      (∑ a : Address, (sys.world.token.maps "_balances" (addrWord a)).val) =
        (sys.world.token.scalars "_totalSupply").val ∧
      sys.world.token.scalars "_nativeTokenVault" = addrWord d.vault ∧
      sys.vault.maps "_assetIdOf" (addrWord d.token) = sys.world.token.scalars "_assetId"

end Codegen.VaultPreparationSlice
