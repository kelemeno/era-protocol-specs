import EraSpec.Contracts.InteropCommitmentTree
import EraSpec.Contracts.AtomicFlowManager
import EraSpec.Contracts.Protocol

/-!
# Refinement obligations

What `contracts-formal-verification` must prove about the compiled code for the
theorems in this package to say anything about the deployed system.

## Why this file is prose and not Lean

Every obligation below is a statement about SOLC OUTPUT — a Yul function, a
keccak-derived storage slot, a compiled guard.  None of it is expressible here:
this package has no EVM semantics, by design.  So the obligations are recorded as
named, checkable claims rather than as `theorem` statements with `sorry` bodies,
which would put `sorryAx` into this package's axiom profile and destroy the one
property that makes it useful — that every result in it is fully proved.

The division of labour is therefore:

| layer | repo | trusts |
|---|---|---|
| protocol operations are correct | **this package** | Mathlib, Lean kernel |
| compiled code implements those operations | `contracts-formal-verification` | + solc's Yul→EVM backend, Clear's EVM model, keccak idealization |

A reader who accepts both halves gets an end-to-end result.  A reader who accepts
only this half gets a verified *design*, which is worth stating plainly rather
than blurring.

## The obligations

### O1 — `Tree` is the compiled tree

`Contracts.InteropCommitmentTree.Tree` must correspond to `IMT`'s storage:
`leafCount` to `_imt.tree._leafNumber`, `leaf i` to the struct at
`keccak(i‖4)`-derived slots, `valueToIndex v` to the slot for `_imt.valueToIndex[v]`.

*Discharged by:* results `#39` (slot accessor closed form: `keccak(i‖4)`, struct
read/write) and `#41` (pointwise write effect against the real storage model,
`[propext, Quot.sound]` only) in `SECURITY_VERIFICATION.md`.

*Open sub-part:* the dispatcher-inlined insert glue → `Tree.insert`
correspondence is source-level inspection, not mechanized — the VC generator does
not extract dispatcher bodies. This is the one seam in the chain and is named as
such there too.

### O2 — `InsertGuard` is the compiled guard

Each field of `Contracts.InteropCommitmentTree.InsertGuard` must be exactly what
the compiled `insert` enforces before its first write, with no additional
condition and none missing.

*Note the direction that matters.* An obligation stated only as "the guard
implies the fields" would be satisfiable by a compiled guard that reverts always.
What is needed is the *success* direction: a successful call implies the fields
held. That is the shape the sibling repo's guard theorems already take (`#4`/`#19`
for chain registration, `#17`/`#18` for the modifiers): *a successful guard ⇒ the
precondition genuinely held.*

### O3 — `lowSearch` is the compiled loop

`lowSearch`'s fuel must be `MAX_LOW_INDEX_SEARCH_ATTEMPTS` and its `none` case
must be the `IMTLowLeafNextTooSmall` revert.

*Status:* the loop specs in `L2InteropCommitmentTree/Common` are the relevant
concrete artifacts. Per that repo's `loop-content-audit.sh`, most loop specs there
are still `AFor := True` — so this obligation is largely OPEN, and the honest
reading is that the compiled search loop is not yet tied to this model.

### O4 — `LegState` is the compiled state machine

`Contracts.AtomicFlowManager.Step`'s three constructors must be the only
transitions the compiled contract performs on `_state[flowId][bundleHash]`, and
each guard must be checked before its write.

*Partly blocked upstream:* the concrete counterparts (`fun_authorizeRefund`,
`fun_verifyTimeoutAbsence`, `fun_verifyInclusion`) cannot currently be built —
eight generated `AtomicFlowManager/Common` files emit `EVMCleanup_bool'`, a lemma
the pinned Clear never defined. Until that is fixed upstream, the CONCRETE side of
the timeout/refund protocol is unreachable and O4 rests on source inspection.

### O5 — access control

`append` is reachable only from `InteropCenter`, `requireFlowFinalized` only from
`InteropHandler`, `insert` only from the `AtomicFlowManager` address, `initL2`
only from the complex upgrader. Not modeled here (see the note in
`Contracts.AtomicFlowManager`): caller identity constrains *who* may step, not
what a step does.

*Discharged by:* `check-source-invariants.sh`'s call-site enumeration, plus
`#37`-style guard theorems. This is an enumeration, so it is the fragile kind —
an edit can break it while every proof stays green.

### O6 — the multi-chain binding is present in the code

`Contracts.Protocol.BoundGate` assumes `authorizeRefund` compares
`_absence.sourceChainId` against `_flow.legSourceChainIds[_missingLegIndex]`.
`unbound_gate_refunds_delivered_leg` shows what is lost if that comparison is
absent or reordered after the absence check.

*Discharged by:* source inspection only, today. **This is the obligation most
worth mechanizing next**, because it is the one whose failure mode is a live
double-spend rather than a weakened statement, and because
`check-source-invariants.sh` is the natural place for it: the check is a single
comparison whose presence a script can assert.

### O7 — the hash side

`Tree` carries list state only. Membership and non-inclusion proofs are checked
against a Merkle root, so `EraSpec.Core.Merkle` plus the concrete `updateWalk`
correspondence (`#31`, `#32`) must certify that the root authenticates exactly
the leaves this model talks about.

*Discharged by:* `#31` (`fun_updateLeaf` ≡ `updateWalk`), `#32` (the verifier's
fold replays that walk), and `root_pins_written_leaf`. These rest on the keccak
idealization axioms, or on the weaker `_of_config` pool-consistency assumptions —
a change of trusted base, not its elimination.

## Known model boundaries inherited from the concrete side

Recorded here so a reader of this package alone is not misled about what the
combined result covers:

* **`mcopy` is unmodelled** in Clear (empty stub, `A_mcopy := True`), so memory
  copies are invisible there. Nothing about copied *bytes* is proved — including
  `_verifyBundle`'s `_proof.message.data = bytes.concat(BUNDLE_IDENTIFIER, _bundle)`
  substitution.
* **`LOG` is a no-op**, so no property about emitted events is provable there.
  This is faithful for state reasoning (LOG cannot change state) but means
  "the contract announces X when it does Y" is out of scope, not merely unproven.
* **External calls are opaque** (`staticcall` returns no values in Clear), so the
  message-verification RESULT is inherently a hypothesis on that side.

None of these affect this package's theorems, which are about protocol
operations. They bound what the *combined* claim can be.
-/

namespace EraSpec.Refinement

/-! ## Machine-checkable summary of what IS proved here

The three statements below are the top of this package's dependency graph — the
protocol-level guarantees the obligations above are meant to transfer to the
compiled code. They are `abbrev`s rather than restatements so there is exactly
one proof of each, and `#print axioms` on them reports the real profile. -/

/-- The commitment tree: every run from `setup` keeps the reclaim gate firing on
exactly the never-delivered legs. -/
abbrev tree_guarantee := @Contracts.InteropCommitmentTree.genesis_run_reclaimable_iff_absent

/-- The flow manager: a refunded leg stays refunded, so no leg is refunded twice. -/
abbrev manager_guarantee := @Contracts.AtomicFlowManager.no_double_claim

/-- The multi-chain protocol: with the source-chain binding, delivery and refund
are mutually exclusive system-wide; without it, they are not. -/
abbrev protocol_guarantee := @Contracts.Protocol.chains_no_double_spend

/-- The countermodel that makes O6 necessary rather than advisory. -/
abbrev binding_necessity := @Contracts.Protocol.unbound_gate_refunds_delivered_leg

end EraSpec.Refinement
