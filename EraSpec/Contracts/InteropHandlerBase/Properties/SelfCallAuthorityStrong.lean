import EraSpec.Contracts.InteropHandlerBase.Specs.SelfCallAuthorityStrong

/-!
# Properties: a self-call relays the original sender's authority, exactly when every branch checks

Statements about `EraSpec.Contracts.InteropHandlerBase.Specs.SelfCallAuthorityStrong`. Proofs
are in `EraSpec.Contracts.InteropHandlerBase.Proofs.SelfCallAuthorityStrong`.

These replace the content `Properties.selfCall_relays_authority` (topic `SelfCallAuthority`)
claims but does not state:

* **The pattern is sound exactly when every self-call site is preceded by the matching check**
  (`SelfCallRelaySoundIffEveryGatedBranchChecked`). For every dispatch table: every admitted call
  of a gated entry point is authorised for its principal — the direct caller, or the ORIGINAL
  sender of the outer message for a relayed call — if and only if every branch that self-calls
  a gated entry point checks its attribute against the parsed sender first. This is the
  sentence of the topic header, as a theorem over all tables.
* **The deployed table is such a table** (`DeployedSelfCallRelaysOriginalSenderAuthority`): an
  admitted relayed call's attribute names the original sender, `(sourceChainId, from)` of the
  delivered call.
* **What it rests on.** An `executeAtomicBundle` branch added without its check widens authority
  (`UncheckedAtomicBranchWidensAuthority`, the "inert disjunct" of the topic header). The relay
  also needs `parseEvmV1Calldata ∘ formatEvmV1` to be the identity on the relayed pair
  (`MisparsedSenderBreaksTheRelay`).
* `SelfCallRelayWitness`: the premises hold, the attributes involved are non-trivial, and the
  gate's own self-call disjunct passes for an attribute that authorises neither the handler nor
  the sender — only the check one frame up rejects that call.
-/

namespace AttackVectors.SelfCallAuthority

/-- **THE RELAY IS SOUND EXACTLY WHEN EVERY GATED BRANCH IS CHECKED.** For every dispatch table:
for all handlers, bundle attributes and calls reaching a gate, every admitted call whose relayed
pair (if any) survives the ERC-7930 round trip is authorised for its principal — if and only if
every branch of the table that self-calls a gated entry point checks that entry point's
attribute against the parsed sender. -/
def Properties.SelfCallRelaySoundIffEveryGatedBranchChecked : Prop :=
  ∀ dispatch : List Branch,
    (∀ (Sender : Type) (H : Handler Sender) (A : BundleAttrs) (c : GateCall),
        RelayRoundTrips H c → Admitted H dispatch A c → Authorized H A c) ↔
      ∀ br ∈ dispatch, br.target.isGated = true → br.checked = true

/-- **THE DEPLOYED RELAY HANDS ON THE ORIGINAL SENDER'S AUTHORITY.** For every handler, bundle
attributes and call admitted under the deployed dispatch (`InteropHandlerBase.sol:351-358`) —
direct, or relayed with the ERC-7930 round trip on its pair — the entry point's attribute allows
the call's principal. For a relayed call that principal is the original sender of the outer
message, the outer bundle's `sourceChainId` and the delivered call's `from` (`:284`): an
attribute `some (ch, addr)` admits the relayed call only if `addr` is that `from` and `ch` is
that chain or the wildcard `0`. -/
def Properties.DeployedSelfCallRelaysOriginalSenderAuthority : Prop :=
  (∀ (Sender : Type) (H : Handler Sender) (A : BundleAttrs) (c : GateCall),
      RelayRoundTrips H c → Admitted H deployedDispatch A c → Authorized H A c) ∧
  ∀ (Sender : Type) (H : Handler Sender) (A : BundleAttrs) (src fromAddr : ℕ) (br : Branch)
    (ch addr : ℕ),
    RoundTripOn H src fromAddr → Admitted H deployedDispatch A (.relayed src fromAddr br) →
    gateAttr br.target A = some (ch, addr) → addr = fromAddr ∧ (ch = src ∨ ch = 0)

/-- **AN `executeAtomicBundle` BRANCH ADDED WITHOUT ITS CHECK WOULD WIDEN AUTHORITY.** With the
deployed table plus an unchecked branch for `executeAtomicBundle` — whose gate has the same
self-call disjunct (`L2InteropHandler.sol:66-75`) — a relayed call from the original sender
`(1, 9)` reaches `executeAtomicBundle` of a bundle whose executor is `(1, 7)`: it is admitted,
its principal is not authorised, and the table fails the check of
`SelfCallRelaySoundIffEveryGatedBranchChecked`. -/
def Properties.UncheckedAtomicBranchWidensAuthority : Prop :=
  RoundTripOn wHandler 1 9 ∧
    Admitted wHandler withUncheckedAtomicBranch wAttrs7
      (.relayed 1 9 ⟨.executeAtomicBundle, false⟩) ∧
    ¬ Authorized wHandler wAttrs7 (.relayed 1 9 ⟨.executeAtomicBundle, false⟩) ∧
    ¬ (∀ br ∈ withUncheckedAtomicBranch, br.target.isGated = true → br.checked = true)

/-- **THE ROUND TRIP IS LOAD-BEARING.** With a parser that reads every sender as `(1, 7)`, the
deployed table admits a relayed `executeBundle` from the original sender `(1, 9)` of a bundle whose
executor is `(1, 7)`: the check passes against the misread pair, and the original sender is not
authorised. -/
def Properties.MisparsedSenderBreaksTheRelay : Prop :=
  ¬ RoundTripOn wMisparsingHandler 1 9 ∧
    Admitted wMisparsingHandler deployedDispatch wAttrs7 (.relayed 1 9 ⟨.executeBundle, true⟩) ∧
    ¬ Authorized wMisparsingHandler wAttrs7 (.relayed 1 9 ⟨.executeBundle, true⟩)

/-- **THE PREMISES ARE SATISFIABLE, AND ONLY THE CHECK ONE FRAME UP DECIDES A RELAYED CALL.** On
`wHandler` (chain `1`, address `99`, the round trip holding):
* relayed `executeBundle` and `unbundleBundle` calls from the original sender `(1, 7)` of a bundle
  naming `(1, 7)` are admitted, and so is a relayed `verifyBundle` for any attributes;
* a direct `executeAtomicBundle` by `7` is admitted; a "direct" call from the handler's own
  address is not a direct call;
* for a bundle naming `(0, 42)`, the gate's self-call disjunct passes although the attribute
  allows neither the handler nor `(1, 7)` — and the relayed call from `(1, 7)` is not admitted:
  `_handleExecuteBundle`'s check rejects it. -/
def Properties.SelfCallRelayWitness : Prop :=
  RoundTripOn wHandler 1 7 ∧
    Admitted wHandler deployedDispatch wAttrs7 (.relayed 1 7 ⟨.executeBundle, true⟩) ∧
    Admitted wHandler deployedDispatch wAttrs7 (.relayed 1 7 ⟨.unbundleBundle, true⟩) ∧
    Admitted wHandler deployedDispatch wAttrs42 (.relayed 5 9 ⟨.verifyBundle, false⟩) ∧
    Admitted wHandler deployedDispatch wAttrs7 (.direct .executeAtomicBundle 7) ∧
    ¬ Admitted wHandler deployedDispatch wAttrs7 (.direct .executeBundle wHandler.self) ∧
    innerGate (gateAttr .executeBundle wAttrs42) wHandler.chainId wHandler.chainId wHandler.self
      (wHandler.self = wHandler.self) ∧
    ¬ attrAllows (gateAttr .executeBundle wAttrs42) wHandler.chainId wHandler.chainId
      wHandler.self ∧
    ¬ Authorized wHandler wAttrs42 (.relayed 1 7 ⟨.executeBundle, true⟩) ∧
    ¬ Admitted wHandler deployedDispatch wAttrs42 (.relayed 1 7 ⟨.executeBundle, true⟩)

end AttackVectors.SelfCallAuthority
