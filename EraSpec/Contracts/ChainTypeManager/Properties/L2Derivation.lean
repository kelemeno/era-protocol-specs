import EraSpec.Contracts.ChainTypeManager.Specs.L2Derivation
import EraSpec.Core.Headline

/-!
# Properties: the L2 side a registry transition derives from its two releases

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.L2Derivation` (pin `b17415d20`).
Proofs are in `EraSpec.Contracts.ChainTypeManager.Proofs.L2Derivation`.

`ctmTransitionL2 kec rnd vFrom vNew Rf Rn e = some p` says the L2 part of `CTMTransition`'s
constructor returns, for departing release `Rf` at `vFrom` and target `Rn` at `vNew`, and stores
the plan `p`. Nothing is assumed about `kec`; where two hashes being equal is used as the two
values being equal, the result names the pair that would have to collide (`KeccakClash`).

## What a successful construction does

* Its system-proxy deployments are exactly the target table's new or changed rows (changed by
  keccak), each at its member's fixed address with the target release's shell, at pairwise
  distinct addresses; a new or changed row at a member with no fixed address makes the
  construction revert (`TransitionDeploysExactlyTheChangedRows`).
* It has an L2 side exactly when the manifest names a delegate. A new or changed row, an extra
  bytecode, or a composer each force a delegate (`HasL2SideIffDelegate`).
* An edge without an L2 side, every patch edge among them (`PatchEdgeHasNoL2Side`), stores the
  empty plan and keeps the L2 description: the tables agree member by member with padding, the
  shell and the blob agree, each up to a named keccak clash, and the genesis parameters are equal
  (`L1OnlyEdgeKeepsTheL2Description`).

## The two table comparisons

`changedL2Rows` and `_l2TableChanged` read a shorter table the same way. When `changedL2Rows`
returns, "no row changed" implies `_l2TableChanged` is false with no hash premise; the converse
holds unless an appended nonempty row hashes like the empty row (`TableComparisonsAgree`), and
such a clash does split them (`EmptyRowClashSplitsTheComparisons`). There is an L1-only patch edge
onto a release whose table only gained an empty row which the constructor before the OpenZeppelin
L-01 fix (`4e073f09b`) refuses for every injective table hash and the constructor at `b17415d20`
accepts for every hash (`AppendedEmptyRowKeepsAnL1OnlyEdge`).

## Boundaries

* A nonempty row never becomes empty (`NonemptyRowStaysNonempty`).
* A row at a member with no fixed address can be neither added nor changed
  (`NoFixedAddressRowCannotChange`), so once in a departing release it is frozen
  (`NoFixedAddressRowIsFrozen`), and no bootstrap plan onto a release holding one can be built
  (`BootstrapOntoNoFixedAddressRowReverts`). `CTMRelease`'s table checks can accept such a row
  (`FrozenRowWitness`).
-/

namespace Contracts.ChainTypeManager.L2Tables

/-! ## What a successful construction deploys -/

/-- **A TRANSITION DEPLOYS EXACTLY ITS NEW AND CHANGED ROWS.** For every successful construction:

* a system-proxy deployment is in the plan iff it is `(fixedAddress i, Rn's row i, Rn's shell)`
  for a member `i` with a fixed address whose row is new or changed by keccak (`RowChanged`);
* the system-proxy deployments target pairwise distinct addresses;
* every new or changed row is at a member with a fixed address. -/
@[headline] def Properties.TransitionDeploysExactlyTheChangedRows : Prop :=
  ∀ {H : Type} [DecidableEq H] (kec : Bytes → H) (rnd : Bytes → L2Addr) (vFrom vNew : ℕ)
    (Rf Rn : ReleaseL2) (e : EdgeInput) (p : L2Plan),
    ctmTransitionL2 kec rnd vFrom vNew Rf Rn e = some p →
    (∀ d, Deployment.proxy d ∈ p.deployments ↔
      ∃ i a, fixedAddress i = some a ∧ RowChanged kec Rf.table Rn.table i ∧
        d = ⟨a, rowAt Rn.table i, Rn.shell⟩) ∧
    ((p.deployments.filterMap Deployment.proxyPart).map ProxyDeployment.addr).Nodup ∧
    (∀ i, RowChanged kec Rf.table Rn.table i → fixedAddress i ≠ none)

/-- **AN L2 SIDE IFF A DELEGATE.** For every successful construction, `hasL2Side` holds iff the
manifest names a delegate, equivalently iff some row is new or changed or a delegate is named.
A new or changed row, an extra bytecode and a composer each force a delegate, and a composer is
named iff a delegate is. -/
def Properties.HasL2SideIffDelegate : Prop :=
  ∀ {H : Type} [DecidableEq H] (kec : Bytes → H) (rnd : Bytes → L2Addr) (vFrom vNew : ℕ)
    (Rf Rn : ReleaseL2) (e : EdgeInput) (p : L2Plan),
    ctmTransitionL2 kec rnd vFrom vNew Rf Rn e = some p →
    (hasL2Side p = true ↔ e.authored.delegate ≠ []) ∧
    (hasL2Side p = true ↔ (∃ i, RowChanged kec Rf.table Rn.table i) ∨ e.authored.delegate ≠ []) ∧
    ((∃ i, RowChanged kec Rf.table Rn.table i) → e.authored.delegate ≠ []) ∧
    (e.authored.extras ≠ [] → e.authored.delegate ≠ []) ∧
    (e.authored.composer ≠ 0 ↔ e.authored.delegate ≠ [])

/-- **AN EDGE WITHOUT AN L2 SIDE KEEPS THE RELEASE'S L2 DESCRIPTION.** For every successful
construction with `hasL2Side` false: the stored plan is empty (no deployment, no delegate, no
composer); `_l2TableChanged` is false; the target table is at least as long; member by member,
with rows past a table's end read as empty, the two rows are equal or are a named keccak clash;
the shells and the blobs are equal or a named keccak clash; the genesis parameters are equal. -/
def Properties.L1OnlyEdgeKeepsTheL2Description : Prop :=
  ∀ {H : Type} [DecidableEq H] (kec : Bytes → H) (rnd : Bytes → L2Addr) (vFrom vNew : ℕ)
    (Rf Rn : ReleaseL2) (e : EdgeInput) (p : L2Plan),
    ctmTransitionL2 kec rnd vFrom vNew Rf Rn e = some p → hasL2Side p = false →
    p = ⟨[], 0, 0⟩ ∧
    l2TableChanged kec Rf.table Rn.table = false ∧
    Rf.table.length ≤ Rn.table.length ∧
    (∀ i, rowAt Rf.table i = rowAt Rn.table i ∨
      KeccakClash kec (rowAt Rf.table i) (rowAt Rn.table i)) ∧
    (Rf.shell = Rn.shell ∨ KeccakClash kec Rf.shell Rn.shell) ∧
    (Rf.blob = Rn.blob ∨ KeccakClash kec Rf.blob Rn.blob) ∧
    Rf.genesis = Rn.genesis

/-- **A PATCH EDGE HAS NO L2 SIDE.** For every successful construction whose two versions have
the same minor component: no L2 side, no delegate, and no new or changed row. So
`L1OnlyEdgeKeepsTheL2Description` applies to it. -/
def Properties.PatchEdgeHasNoL2Side : Prop :=
  ∀ {H : Type} [DecidableEq H] (kec : Bytes → H) (rnd : Bytes → L2Addr) (vFrom vNew : ℕ)
    (Rf Rn : ReleaseL2) (e : EdgeInput) (p : L2Plan),
    ctmTransitionL2 kec rnd vFrom vNew Rf Rn e = some p → minorOf vFrom = minorOf vNew →
    hasL2Side p = false ∧ e.authored.delegate = [] ∧ ¬ ∃ i, RowChanged kec Rf.table Rn.table i

/-! ## The two table comparisons -/

/-- **THE TWO TABLE COMPARISONS AGREE, UP TO A CLASH WITH THE EMPTY ROW.** Whenever
`changedL2Rows` returns `changed`:

* if every entry of `changed` is empty, `_l2TableChanged` is false (no hash premise);
* if `_l2TableChanged` is false, every entry of `changed` is empty, or some row the target table
  appends past the departing table's end clashes with the empty row under `kec`. -/
def Properties.TableComparisonsAgree : Prop :=
  ∀ {H : Type} [DecidableEq H] (kec : Bytes → H) (fromT newT changed : List Bytes),
    changedL2Rows kec fromT newT = some changed →
    ((∀ x ∈ changed, x = []) → l2TableChanged kec fromT newT = false) ∧
    (l2TableChanged kec fromT newT = false →
      (∀ x ∈ changed, x = []) ∨
        ∃ i, fromT.length ≤ i ∧ i < newT.length ∧ KeccakClash kec (rowAt newT i) [])

/-- **COUNTERMODEL: A CLASH WITH THE EMPTY ROW SPLITS THE COMPARISONS.** With a hash under which
a nonempty row appended past the departing table's end hashes like the empty row, a construction
succeeds whose plan deploys that row while `_l2TableChanged` (which `releaseDiff()` reports,
`CTMTransition.sol:159`) is false. So the second half of `TableComparisonsAgree` needs its clash
disjunct. -/
@[countermodel] def Properties.EmptyRowClashSplitsTheComparisons : Prop :=
  ∃ (kec : Bytes → Bytes) (rnd : Bytes → L2Addr) (vFrom vNew : ℕ) (Rf Rn : ReleaseL2)
    (e : EdgeInput) (p : L2Plan),
    ctmTransitionL2 kec rnd vFrom vNew Rf Rn e = some p ∧
    l2TableChanged kec Rf.table Rn.table = false ∧
    (∃ d, Deployment.proxy d ∈ p.deployments) ∧
    ∃ i, Rf.table.length ≤ i ∧ KeccakClash kec (rowAt Rn.table i) []

/-- **OZ L-01: AN APPENDED EMPTY ROW NO LONGER REFUSES AN L1-ONLY EDGE.** There is a patch edge
whose target table is the departing table plus one empty row (a release built after an enum
append), such that:

* at `b17415d20` its construction succeeds with no L2 side, for **every** hash `kec`, storing the
  same plan;
* at `4e073f09b` (before the fix) its construction reverts for every table hash
  `kec ∘ encT` that is injective. -/
@[countermodel] def Properties.AppendedEmptyRowKeepsAnL1OnlyEdge : Prop :=
  ∃ (rnd : Bytes → L2Addr) (vFrom vNew : ℕ) (Rf Rn : ReleaseL2) (e : EdgeInput) (p : L2Plan),
    Rf.table ≠ [] ∧ Rn.table = Rf.table ++ [[]] ∧ minorOf vFrom = minorOf vNew ∧
    hasL2Side p = false ∧
    (∀ {H : Type} [DecidableEq H] (kec : Bytes → H),
      ctmTransitionL2 kec rnd vFrom vNew Rf Rn e = some p) ∧
    ∀ {H : Type} [DecidableEq H] (kec : Bytes → H) (encT : List Bytes → Bytes),
      Function.Injective (fun t => kec (encT t)) →
      ctmTransitionL2PreFix kec encT rnd vFrom vNew Rf Rn e = none

/-! ## Boundaries -/

/-- **A NONEMPTY ROW NEVER BECOMES EMPTY.** For every successful construction, every member with
a nonempty row in the departing table has a nonempty row in the target table. -/
def Properties.NonemptyRowStaysNonempty : Prop :=
  ∀ {H : Type} [DecidableEq H] (kec : Bytes → H) (rnd : Bytes → L2Addr) (vFrom vNew : ℕ)
    (Rf Rn : ReleaseL2) (e : EdgeInput) (p : L2Plan),
    ctmTransitionL2 kec rnd vFrom vNew Rf Rn e = some p →
    ∀ i, rowAt Rf.table i ≠ [] → rowAt Rn.table i ≠ []

/-- **A ROW AT A MEMBER WITH NO FIXED ADDRESS CAN BE NEITHER ADDED NOR CHANGED.** If member `i`
has no fixed address and its row in the target table is new or changed by keccak, the
construction reverts, whatever the versions and the authored input. -/
def Properties.NoFixedAddressRowCannotChange : Prop :=
  ∀ {H : Type} [DecidableEq H] (kec : Bytes → H) (rnd : Bytes → L2Addr) (vFrom vNew : ℕ)
    (Rf Rn : ReleaseL2) (e : EdgeInput) (i : ℕ),
    fixedAddress i = none → RowChanged kec Rf.table Rn.table i →
    ctmTransitionL2 kec rnd vFrom vNew Rf Rn e = none

/-- **SUCH A ROW, ONCE IN THE DEPARTING RELEASE, IS FROZEN.** For every successful construction
and every member `i` with no fixed address and a nonempty row in the departing table: the target
row is nonempty, and equal to the departing row or a named keccak clash with it. -/
def Properties.NoFixedAddressRowIsFrozen : Prop :=
  ∀ {H : Type} [DecidableEq H] (kec : Bytes → H) (rnd : Bytes → L2Addr) (vFrom vNew : ℕ)
    (Rf Rn : ReleaseL2) (e : EdgeInput) (p : L2Plan),
    ctmTransitionL2 kec rnd vFrom vNew Rf Rn e = some p →
    ∀ i, fixedAddress i = none → rowAt Rf.table i ≠ [] →
      rowAt Rn.table i ≠ [] ∧
        (rowAt Rn.table i = rowAt Rf.table i ∨ KeccakClash kec (rowAt Rf.table i) (rowAt Rn.table i))

/-- **NO BOOTSTRAP PLAN ONTO SUCH A RELEASE CAN BE BUILT.** If a release has a nonempty row at a
member with no fixed address, `RegistryBootstrapMigration._buildL2Plan` reverts for every
authored input, so the migration's constructor reverts (`RegistryBootstrapMigration.sol:83`). -/
def Properties.BootstrapOntoNoFixedAddressRowReverts : Prop :=
  ∀ (rnd : Bytes → L2Addr) (R : ReleaseL2) (a : AuthoredL2) (i : ℕ),
    fixedAddress i = none → rowAt R.table i ≠ [] → bootstrapPlanL2 rnd R a = none

/-! ## Witnesses -/

/-- **THE FROZEN ROW, END TO END.** There is a release `R` that passes every L2 check of
`CTMRelease`'s constructor (with an injective hash) and has a nonempty row at member 14
(`BeaconProxy`, no fixed address). From `R`: a minor edge onto `R'`, which keeps row 14 and
changes row 0, succeeds with an L2 side; an edge onto `R''`, which changes row 14 and nothing
else, reverts for every pair of versions and every authored input; and no bootstrap plan onto `R`
can be built. -/
@[witness] def Properties.FrozenRowWitness : Prop :=
  ∃ (enc : Bytes → Bytes → Bytes) (rnd : Bytes → L2Addr) (R R' R'' : ReleaseL2) (e : EdgeInput)
    (p : L2Plan),
    ReleaseL2Accepted (id : Bytes → Bytes) enc R ∧ ReleaseL2Accepted (id : Bytes → Bytes) enc R' ∧
    ReleaseL2Accepted (id : Bytes → Bytes) enc R'' ∧
    fixedAddress 14 = none ∧ rowAt R.table 14 ≠ [] ∧
    ctmTransitionL2 (id : Bytes → Bytes) rnd (2 ^ 32) (2 * 2 ^ 32) R R' e = some p ∧
    hasL2Side p = true ∧ RowChanged (id : Bytes → Bytes) R.table R'.table 0 ∧
    rowAt R'.table 14 = rowAt R.table 14 ∧
    RowChanged (id : Bytes → Bytes) R.table R''.table 14 ∧
    (∀ i, i ≠ 14 → rowAt R''.table i = rowAt R.table i) ∧
    (∀ (vFrom vNew : ℕ) (e' : EdgeInput),
      ctmTransitionL2 (id : Bytes → Bytes) rnd vFrom vNew R R'' e' = none) ∧
    ∀ a : AuthoredL2, bootstrapPlanL2 rnd R a = none

/-- **BOTH KINDS OF EDGE OCCUR.** With an injective hash: a minor edge `R1 → R2` (versions
`2^32 → 2·2^32`) with a delegate, one changed row (member 0) and one new row (member 2) succeeds
with an L2 side, deploying exactly those two rows; and a patch edge `R2 → R3`
(`2·2^32 → 2·2^32 + 1`) whose target has the same L2 description succeeds without one. The
`changedL2Rows` results of both are the premises of `TableComparisonsAgree`, one with a nonempty
entry and one with `_l2TableChanged` false. -/
@[witness] def Properties.L2DerivationWitness : Prop :=
  ∃ (rnd : Bytes → L2Addr) (R1 R2 R3 : ReleaseL2) (e12 e23 : EdgeInput) (p12 p23 : L2Plan)
    (c12 c23 : List Bytes),
    ctmTransitionL2 (id : Bytes → Bytes) rnd (2 ^ 32) (2 * 2 ^ 32) R1 R2 e12 = some p12 ∧
    hasL2Side p12 = true ∧
    RowChanged (id : Bytes → Bytes) R1.table R2.table 0 ∧ 0 < R1.table.length ∧
    RowChanged (id : Bytes → Bytes) R1.table R2.table 2 ∧ R1.table.length ≤ 2 ∧
    rowAt R1.table 1 ≠ [] ∧
    (p12.deployments.filterMap Deployment.proxyPart).length = 2 ∧
    ctmTransitionL2 (id : Bytes → Bytes) rnd (2 * 2 ^ 32) (2 * 2 ^ 32 + 1) R2 R3 e23 = some p23 ∧
    hasL2Side p23 = false ∧ minorOf (2 * 2 ^ 32) = minorOf (2 * 2 ^ 32 + 1) ∧
    changedL2Rows (id : Bytes → Bytes) R1.table R2.table = some c12 ∧ (∃ x ∈ c12, x ≠ []) ∧
    changedL2Rows (id : Bytes → Bytes) R2.table R3.table = some c23 ∧
    l2TableChanged (id : Bytes → Bytes) R2.table R3.table = false

end Contracts.ChainTypeManager.L2Tables
