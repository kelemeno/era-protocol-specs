import EraSpec.Codegen.EmitRefusals.Properties.BoolLiterals

/-! # Proofs: the emitter prints only the Bool literals 0 and 1 -/

namespace Codegen.EmitRefusals

open Codegen Codegen.Emit

/-! ## The emitter's traversal reaches every operand and every depth -/

theorem mem_boolLits_of_boolLitIn {n : ℕ} {e : Expr} (h : BoolLitIn n e) :
    n ∈ boolLits e := by
  induction h <;> simp_all [boolLits]

theorem mem_stmtExprs_of_stmtOperand {s : Stmt} {e : Expr} (h : StmtOperand s e) :
    e ∈ stmtExprs s := by
  cases s with
  | require c r =>
      cases c <;> cases r <;> simp only [StmtOperand, CondOperand] at h <;>
        simp only [stmtExprs, condExprs, List.mem_cons, List.mem_append, List.not_mem_nil] <;>
        tauto
  | local_ => simp_all [StmtOperand, stmtExprs]
  | sstore => simp_all [StmtOperand, stmtExprs]
  | mstore => simp_all [StmtOperand, stmtExprs]
  | emit => simp_all [StmtOperand, stmtExprs]
  | ret => simp_all [StmtOperand, stmtExprs]

/-! ## Acceptance, from a contract down to its statements -/

/-- The Bool check is the first thing `Emit.stmt` does: an accepted statement has no
noncanonical Bool literal. -/
theorem noncanonicalBool_eq_none_of_stmt_ok {indent out : String} {s : Stmt}
    (h : stmt indent s = .ok out) : noncanonicalBool s = none := by
  cases hb : noncanonicalBool s with
  | none => rfl
  | some b =>
      unfold stmt at h
      rw [hb] at h
      cases h

theorem boolLits_le_one_of_stmt_ok {indent out : String} {s : Stmt}
    (h : stmt indent s = .ok out) : ∀ e ∈ stmtExprs s, ∀ n ∈ boolLits e, n ≤ 1 := by
  have h0 := noncanonicalBool_eq_none_of_stmt_ok h
  rw [noncanonicalBool, List.find?_eq_none] at h0
  intro e he n hn
  have : ¬ 1 < n := by simpa using h0 n (List.mem_flatMap.mpr ⟨e, he, hn⟩)
  omega

/-- In `Except`, a successful `mapM` succeeded on every element. -/
theorem mapM_except_ok_mem {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → ∀ x ∈ l, ∃ y, f x = .ok y
  | [], _, _, x, hx => by simp at hx
  | a :: l, l', h, x, hx => by
      rw [List.mapM_cons] at h
      cases ha : f a with
      | error e => rw [ha] at h; cases h
      | ok b =>
          cases hl : l.mapM f with
          | error e => rw [ha, hl] at h; cases h
          | ok bs =>
              rcases List.mem_cons.mp hx with rfl | hx
              · exact ⟨b, ha⟩
              · exact mapM_except_ok_mem hl x hx

theorem stmt_ok_of_body_ok {ss : List Stmt} {out : String} (h : body ss = .ok out) :
    ∀ s ∈ ss, ∃ out', stmt "        " s = .ok out' := by
  unfold body at h
  cases hm : ss.mapM (stmt "        ") with
  | error e => rw [hm] at h; cases h
  | ok lines => exact mapM_except_ok_mem hm

theorem body_ok_of_fn_ok {f : Fn} {out : String} (h : fn f = .ok out) :
    ∃ b, body f.body = .ok b := by
  unfold fn at h
  cases hb : body f.body with
  | error e => rw [hb] at h; cases h
  | ok b => exact ⟨b, rfl⟩

/-- Every statement of an accepted contract is accepted, at the indentation `body` uses. -/
theorem stmt_ok_of_contract_ok {c : Contract} {origin src : String}
    (h : contract c origin = .ok src) :
    ∀ s, ContractStmt c s → ∃ out, stmt "        " s = .ok out := by
  unfold contract at h
  cases hc : body c.ctorBody with
  | error e => rw [hc] at h; cases h
  | ok ctor =>
      cases hf : c.fns.mapM fn with
      | error e => rw [hc, hf] at h; cases h
      | ok fns =>
          rintro s (hs | ⟨f, hf', hs⟩)
          · exact stmt_ok_of_body_ok hc s hs
          · obtain ⟨out, hout⟩ := mapM_except_ok_mem hf f hf'
            obtain ⟨b, hb⟩ := body_ok_of_fn_ok hout
            exact stmt_ok_of_body_ok hb s hs

/-! ## The properties -/

theorem AcceptedStmtBoolLiteralsCanonical : Properties.AcceptedStmtBoolLiteralsCanonical := by
  intro indent s out h e he n hn
  have := boolLits_le_one_of_stmt_ok h e (mem_stmtExprs_of_stmtOperand he) n
    (mem_boolLits_of_boolLitIn hn)
  omega

theorem AcceptedBoolLiteralsCanonical : Properties.AcceptedBoolLiteralsCanonical := by
  intro c origin src h s hs e he n hn
  obtain ⟨out, hout⟩ := stmt_ok_of_contract_ok h s hs
  exact AcceptedStmtBoolLiteralsCanonical _ s out hout e he n hn

theorem AcceptedBoolLiteralsPrintTheirWord : Properties.AcceptedBoolLiteralsPrintTheirWord := by
  intro c origin src h s hs e he n hn st cx
  rcases AcceptedBoolLiteralsCanonical c origin src h s hs e he n hn with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

theorem NoncanonicalBoolLiteralRefused : Properties.NoncanonicalBoolLiteralRefused := by
  constructor
  · intro indent s e n he hn h1
    cases h : stmt indent s with
    | error msg => exact ⟨msg, rfl⟩
    | ok out =>
        rcases AcceptedStmtBoolLiteralsCanonical indent s out h e he n hn with rfl | rfl <;>
          omega
  · intro c origin s e n hs he hn h1
    cases h : contract c origin with
    | error msg => exact ⟨msg, rfl⟩
    | ok src =>
        rcases AcceptedBoolLiteralsCanonical c origin src h s hs e he n hn with rfl | rfl <;>
          omega

/-! ## Regression inputs, run through the emitter and the interpreter -/

theorem BoolTwoEqOneRefused : Properties.BoolTwoEqOneRefused :=
  ⟨fun _ => rfl, by decide, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩

theorem BoolWrapsToZeroRefused : Properties.BoolWrapsToZeroRefused :=
  ⟨fun _ => rfl, by decide, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩

theorem CanonicalBoolLiteralsPrinted : Properties.CanonicalBoolLiteralsPrinted :=
  ⟨fun _ => rfl, rfl, rfl, rfl⟩

/-! ## Witnesses -/

theorem AcceptedBoolLiteralsWitness : Properties.AcceptedBoolLiteralsWitness :=
  ⟨⟨_, _, .ret (.lit .bool 1), .lit .bool 1, rfl,
      Or.inr ⟨BridgedTokenSlice.transfer, by simp [BridgedTokenSlice.program],
        by simp [BridgedTokenSlice.transfer]⟩,
      rfl, rfl, .lit⟩,
    ⟨boolProbe (.ret (.lit .bool 0)), "", _, _, .ret (.lit .bool 0), .lit .bool 0, rfl,
      Or.inr ⟨_, List.mem_singleton_self _, List.mem_singleton_self _⟩, rfl, rfl, .lit⟩⟩

theorem NoncanonicalBoolLiteralWitness : Properties.NoncanonicalBoolLiteralWitness :=
  ⟨boolProbe boolTwoEqOne, boolTwoEqOne, .lit .bool 2, 2,
    Or.inr ⟨_, List.mem_singleton_self _, List.mem_singleton_self _⟩, Or.inl rfl, .lit,
    by decide⟩

end Codegen.EmitRefusals
