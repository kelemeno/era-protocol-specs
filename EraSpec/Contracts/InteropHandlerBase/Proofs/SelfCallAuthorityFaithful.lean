import EraSpec.Contracts.InteropHandlerBase.Properties.SelfCallAuthorityFaithful
import Mathlib.Tactic

/-!
# Proofs: the self-call delegation relays authority

The headline is one argument in each direction. A matched table is sound: a direct call is gated
exactly (`DirectCallsAreGatedExactly`), and a relayed call was admitted by its arm's check, which is
its target's check (`dispatch_spec`). An unmatched table is not: an arm whose check differs from its
target's gate is defeated by an attribute pair that satisfies the check and not the gate, sent from
the principal the check admits. The deployed tables are matched by `decide`.
-/

namespace AttackVectors.SelfCallAuthority.Faithful

/-- The arm `branchFor` returns is in the table and matches the selector. -/
lemma branchFor_spec {tbl : Table} {sel : Entry} {br : Branch}
    (h : branchFor tbl sel = some br) : br ∈ tbl ∧ br.selector = sel := by
  unfold branchFor at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- What a successful dispatch did: the caller was the handler, the selector chose an arm, the
message's sender passed the arm's check, and the self-call is the arm's target, for that sender. -/
lemma dispatch_spec {tbl : Table} {handler caller : ℕ} {m : Message} {sc : SelfCall}
    (h : dispatch tbl handler caller m = some sc) :
    caller = handler ∧ ∃ (br : Branch) (p : Principal),
      m.selector = some (.entry br.selector) ∧ m.sender = some p ∧
        branchFor tbl br.selector = some br ∧ Admits br.check m.attrs p ∧
          sc = ⟨br.target, m.attrs, p⟩ := by
  obtain ⟨sender, selector, attrs⟩ := m
  unfold dispatch at h
  split_ifs at h with hc
  refine ⟨hc, ?_⟩
  rcases selector with _ | (sel | n)
  · simp at h
  · rcases sender with _ | p
    · simp at h
    · simp only at h
      cases hb : branchFor tbl sel with
      | none => rw [hb] at h; simp at h
      | some br =>
        rw [hb] at h
        simp only at h
        split_ifs at h with ha
        obtain ⟨-, hsel⟩ := branchFor_spec hb
        subst hsel
        exact ⟨br, p, rfl, rfl, hb, ha, (Option.some.inj h).symm⟩
  · simp at h

theorem DirectCallsAreGatedExactly : Properties.DirectCallsAreGatedExactly := by
  intro handler thisChain g a caller hne
  cases g with
  | permissionless => simp [InnerGate, Admits]
  | execution =>
    cases hx : a.execution with
    | empty => simp [InnerGate, Admits, hx]
    | malformed => simp [InnerGate, Admits, hx, AddrField.Names]
    | evm ch addr => simp [InnerGate, Admits, hx, AddrField.Names, hne]
  | unbundler =>
    cases hx : a.unbundler with
    | empty => simp [InnerGate, Admits, hx, AddrField.Names]
    | malformed => simp [InnerGate, Admits, hx, AddrField.Names]
    | evm ch addr => simp [InnerGate, Admits, hx, AddrField.Names, hne]

theorem DelegationSoundIffMatched : Properties.DelegationSoundIffMatched := by
  intro tbl
  constructor
  · -- An unmatched arm, sent from the principal its check admits, defeats the target's gate.
    intro hs br hbr hfirst
    by_contra hne
    obtain ⟨hck, htg⟩ := not_or.1 hne
    cases hg : br.target.gate with
    | permissionless => exact htg hg
    | execution =>
      have hm : Admits br.check wAttrs (1, 9) := by
        cases hc : br.check with
        | execution => exact absurd (hc.trans hg.symm) hck
        | unbundler => decide
        | permissionless => trivial
      have hd : dispatch tbl 0 0 ⟨some (1, 9), some (.entry br.selector), wAttrs⟩ =
          some ⟨br.target, wAttrs, (1, 9)⟩ := by
        simp [dispatch, hfirst, hm]
      have hgate : InnerGate 0 1 (GateCall.entry ⟨br.target, wAttrs, 0, (1, 9)⟩).gate
          (GateCall.attrs ⟨br.target, wAttrs, 0, (1, 9)⟩)
          (GateCall.sender ⟨br.target, wAttrs, 0, (1, 9)⟩) := by
        simp [hg, InnerGate, wAttrs]
      have := hs 0 1 _ (Reaches.relayed 0 _ _ hd) hgate
      simp [hg, Admits, wAttrs, AddrField.Names] at this
    | unbundler =>
      have hm : Admits br.check ⟨.empty, .evm 1 7⟩ (1, 9) := by
        cases hc : br.check with
        | execution => exact Or.inl rfl
        | unbundler => exact absurd (hc.trans hg.symm) hck
        | permissionless => trivial
      have hd : dispatch tbl 0 0 ⟨some (1, 9), some (.entry br.selector), ⟨.empty, .evm 1 7⟩⟩ =
          some ⟨br.target, ⟨.empty, .evm 1 7⟩, (1, 9)⟩ := by
        simp [dispatch, hfirst, hm]
      have hgate : InnerGate 0 1 (GateCall.entry ⟨br.target, ⟨.empty, .evm 1 7⟩, 0, (1, 9)⟩).gate
          (GateCall.attrs ⟨br.target, ⟨.empty, .evm 1 7⟩, 0, (1, 9)⟩)
          (GateCall.sender ⟨br.target, ⟨.empty, .evm 1 7⟩, 0, (1, 9)⟩) := by
        simp [hg, InnerGate]
      have := hs 0 1 _ (Reaches.relayed 0 _ _ hd) hgate
      simp [hg, Admits, AddrField.Names] at this
  · -- A matched table: direct calls are gated exactly, relayed ones were checked for the target.
    intro hm handler thisChain gc hr hgate
    cases hr with
    | direct e a caller hne =>
      exact (DirectCallsAreGatedExactly handler thisChain e.gate a caller hne).1 hgate
    | relayed caller m sc hd =>
      obtain ⟨_, br, p, _, _, hb, hadm, rfl⟩ := dispatch_spec hd
      obtain ⟨hmem, -⟩ := branchFor_spec hb
      rcases hm br hmem hb with heq | hperm
      · show Admits br.target.gate m.attrs p
        rw [← heq]; exact hadm
      · show Admits br.target.gate m.attrs p
        rw [hperm]; trivial

lemma pinnedTable_matched : Matched pinnedTable := by decide

theorem PinnedDelegationSound : Properties.PinnedDelegationSound :=
  (DelegationSoundIffMatched pinnedTable).2 pinnedTable_matched

theorem UpgradeDelegationSound : Properties.UpgradeDelegationSound :=
  ⟨(DelegationSoundIffMatched upgradeL2Table).2 (by decide),
    (DelegationSoundIffMatched upgradeL1Table).2 (by decide)⟩

theorem SelfDisjunctPassesWhateverTheAttribute :
    Properties.SelfDisjunctPassesWhateverTheAttribute := by
  intro handler thisChain a
  refine ⟨fun hne => ?_, fun ch addr hu => ?_⟩
  · cases hx : a.execution with
    | empty => simp [InnerGate, hx]
    | malformed => exact absurd hx hne
    | evm ch addr => simp [InnerGate, hx]
  · simp [InnerGate, hu]

theorem RelayedCallActsForTheMessageSender :
    Properties.RelayedCallActsForTheMessageSender := by
  intro tbl handler caller m sc hd
  obtain ⟨hc, br, p, hsel, hsend, hb, hadm, rfl⟩ := dispatch_spec hd
  exact ⟨hc, hsend, rfl, br, hsel, hb, rfl, hadm⟩

/-- `Admits` on the execution gate is the original `attrAllows`, at the rescue path's chain. -/
lemma admits_execution_iff (a : GateAttrs) (p : Principal) :
    Admits .execution a p ↔
      ∃ at' : Attr, a.execution.toAttr = some at' ∧ attrAllows at' p.1 p.1 p.2 := by
  obtain ⟨pc, pa⟩ := p
  cases hx : a.execution with
  | empty => simp [Admits, hx, AddrField.toAttr, attrAllows]
  | malformed => simp [Admits, hx, AddrField.toAttr, AddrField.Names]
  | evm ch addr => simp [Admits, hx, AddrField.toAttr, AddrField.Names, attrAllows]

/-- `Admits` on the unbundler gate is the original `attrAllows` of a parsed attribute. -/
lemma admits_unbundler_iff (a : GateAttrs) (p : Principal) :
    Admits .unbundler a p ↔
      ∃ ch addr, a.unbundler = .evm ch addr ∧ attrAllows (some (ch, addr)) p.1 p.1 p.2 := by
  obtain ⟨pc, pa⟩ := p
  cases hx : a.unbundler with
  | empty => simp [Admits, hx, AddrField.Names]
  | malformed => simp [Admits, hx, AddrField.Names]
  | evm ch addr =>
    show AddrField.Names a.unbundler (pc, pa) ↔ _
    rw [hx]
    constructor
    · intro h
      exact ⟨ch, addr, rfl, h.1, h.2, rfl⟩
    · rintro ⟨ch', addr', he, h₁, h₂, -⟩
      cases he
      exact ⟨h₁, h₂⟩

theorem RelayEstablishesTheOriginalHypothesis :
    Properties.RelayEstablishesTheOriginalHypothesis := by
  intro handler caller m sc hd
  obtain ⟨_, br, p, _, _, hb, hadm, rfl⟩ := dispatch_spec hd
  obtain ⟨hmem, -⟩ := branchFor_spec hb
  have hA : Admits br.target.gate m.attrs p := by
    rcases pinnedTable_matched br hmem hb with heq | hperm
    · rw [← heq]; exact hadm
    · rw [hperm]; trivial
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · have hA' : Admits .execution m.attrs p := hg ▸ hA
    exact (admits_execution_iff m.attrs p).1 hA'
  · have hA' : Admits .unbundler m.attrs p := hg ▸ hA
    exact (admits_unbundler_iff m.attrs p).1 hA'

theorem AtomicSelfDisjunctDeadAtPin : Properties.AtomicSelfDisjunctDeadAtPin := by
  intro handler thisChain gc hr hatomic
  cases hr with
  | direct e a caller hne => exact hne
  | relayed caller m sc hd =>
    exfalso
    obtain ⟨_, br, p, _, _, hb, _, rfl⟩ := dispatch_spec hd
    obtain ⟨hmem, -⟩ := branchFor_spec hb
    have hno : ∀ b ∈ pinnedTable, b.target ≠ .executeAtomicBundle := by decide
    exact hno br hmem hatomic

theorem AtomicSelfDisjunctLiveAndCheckedAtUpgrade :
    Properties.AtomicSelfDisjunctLiveAndCheckedAtUpgrade := by
  have hd : dispatch upgradeL2Table 0 0 wAtomicMsgOk = some ⟨.executeAtomicBundle, wAttrs, (1, 7)⟩ :=
    by decide
  exact ⟨Reaches.relayed 0 wAtomicMsgOk _ hd, hd, by decide⟩

theorem UncheckedAtomicArmWidensAuthority : Properties.UncheckedAtomicArmWidensAuthority := by
  have hd : dispatch uncheckedAtomicTable 0 0 wAtomicMsg =
      some ⟨.executeAtomicBundle, wAttrs, (1, 9)⟩ := by decide
  refine ⟨fun hs => ?_, Reaches.relayed 0 wAtomicMsg _ hd, Or.inl rfl, by decide⟩
  exact absurd ((DelegationSoundIffMatched uncheckedAtomicTable).1 hs) (by decide)

theorem MiswiredCheckWidensAuthority : Properties.MiswiredCheckWidensAuthority := by
  have hd : dispatch miswiredTable 0 0 wExecMsg = some ⟨.executeBundle, wAttrs, (1, 9)⟩ := by
    decide
  refine ⟨fun hs => ?_, Reaches.relayed 0 wExecMsg _ hd, Or.inl rfl, by decide⟩
  exact absurd ((DelegationSoundIffMatched miswiredTable).1 hs) (by decide)

/-- **Why `SelfCallAuthority.selfCall_relays_authority` says nothing.** Its conclusion
`∃ ch addr, attrAllows a ch ch addr` holds for every attribute, with no hypothesis: an empty
attribute allows everyone, and `some (ch, addr)` allows `addr` on `ch`. -/
theorem selfCall_relays_authority_conclusion_always_holds (a : Attr) :
    ∃ ch addr, attrAllows a ch ch addr := by
  rcases a with _ | ⟨ch, addr⟩
  · exact ⟨0, 0, trivial⟩
  · exact ⟨ch, addr, Or.inl rfl, rfl, rfl⟩

end AttackVectors.SelfCallAuthority.Faithful
