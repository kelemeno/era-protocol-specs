import Mathlib.Tactic
import EraSpec.Contracts.AdminFacet.Specs.AdminFacet

/-!
# Auxiliary lemmas for the `AdminFacet` model

No property statements live here. These are the one-step frame facts every run-level proof uses:
which entries can change which fields, read off `exec` entry by entry.

`Holds P o` says every successful outcome of `o` satisfies `P`; `simp` pushes it through the
`req` chains of `exec`, so each frame lemma is one case split over the 25 entries.
-/

namespace Contracts.AdminFacet

/-- Every successful outcome of `o` satisfies `P`. -/
def Holds (P : State → Prop) (o : Option State) : Prop := ∀ s', o = some s' → P s'

@[simp] theorem holds_none (P : State → Prop) : Holds P none := by simp [Holds]

@[simp] theorem holds_some (P : State → Prop) (x : State) : Holds P (some x) ↔ P x := by
  simp [Holds]

@[simp] theorem holds_req (P : State → Prop) (c : Prop) [Decidable c] (k : Option State) :
    Holds P (req c k) ↔ (c → Holds P k) := by
  unfold req; split <;> simp_all [Holds]

theorem req_eq_some {c : Prop} [Decidable c] {k : Option State} {s : State} :
    req c k = some s ↔ c ∧ k = some s := by
  unfold req; split <;> simp_all

theorem req_eq_none {c : Prop} [Decidable c] {k : Option State} :
    req c k = none ↔ (¬ c ∨ k = none) := by
  unfold req; split <;> simp_all

theorem call_exec {K : Config} {e : Env} {s s' : State} {c : Call}
    (h : call K e s c = some s') : exec K e s c = some s' := by
  unfold call at h; exact (req_eq_some.1 h).2

theorem call_not_blocked {K : Config} {e : Env} {s s' : State} {c : Call}
    (h : call K e s c = some s') : ¬ (s.frozen = true ∧ s.freezable c.entry.sel = true) := by
  unfold call at h; exact (req_eq_some.1 h).1

/-- The simp set that unfolds a non-cut entry. -/
macro "exec_simp" : tactic =>
  `(tactic| simp (config := { contextual := true })
      [exec, onlyL1, onlySettlementLayer, noUnverifiedBatches, revertBatches, Entry.runsCut])

/-! ## One-step frame lemmas for non-cut calls -/

section Frame

variable {K : Config} {e : Env} {s s' : State} {c : Call}

/-- A non-cut call changes the admin only as `acceptAdmin` by the pending admin. -/
theorem exec_admin (h : exec K e s c = some s') (hc : c.entry.runsCut = false) :
    s'.admin = s.admin ∨
      (c.entry = .acceptAdmin ∧ c.sender = s.pendingAdmin ∧ s'.admin = s.pendingAdmin) := by
  suffices H : Holds (fun s' => s'.admin = s.admin ∨
      (c.entry = .acceptAdmin ∧ c.sender = s.pendingAdmin ∧ s'.admin = s.pendingAdmin))
      (exec K e s c) from H s' h
  rcases c with ⟨snd, τ, en⟩
  cases en <;> simp [Entry.runsCut] at hc <;> exec_simp

/-- A non-cut call changes the pending admin only by `setPendingAdmin` (to its argument) or
`acceptAdmin` (to zero). -/
theorem exec_pending (h : exec K e s c = some s') (hc : c.entry.runsCut = false) :
    s'.pendingAdmin = s.pendingAdmin ∨
      (c.entry = .setPendingAdmin s'.pendingAdmin) ∨
      (c.entry = .acceptAdmin ∧ s'.pendingAdmin = 0) := by
  suffices H : Holds (fun s' => s'.pendingAdmin = s.pendingAdmin ∨
      (c.entry = .setPendingAdmin s'.pendingAdmin) ∨
      (c.entry = .acceptAdmin ∧ s'.pendingAdmin = 0)) (exec K e s c) from H s' h
  rcases c with ⟨snd, τ, en⟩
  cases en <;> simp [Entry.runsCut] at hc <;> exec_simp

/-- A non-cut call writes none of: the CTM address, the protocol version, the verifier, the
freezability table, the L2 upgrade transaction's hash. -/
theorem exec_fixed (h : exec K e s c = some s') (hc : c.entry.runsCut = false) :
    s'.chainTypeManager = s.chainTypeManager ∧ s'.protocolVersion = s.protocolVersion ∧
      s'.verifier = s.verifier ∧ s'.freezable = s.freezable ∧
      s'.upgradeTxHash = s.upgradeTxHash := by
  suffices H : Holds (fun s' => s'.chainTypeManager = s.chainTypeManager ∧
      s'.protocolVersion = s.protocolVersion ∧ s'.verifier = s.verifier ∧
      s'.freezable = s.freezable ∧ s'.upgradeTxHash = s.upgradeTxHash) (exec K e s c) from H s' h
  rcases c with ⟨snd, τ, en⟩
  cases en <;> simp [Entry.runsCut] at hc <;> exec_simp

/-- A non-cut call changes a validator bit only as `setValidator` by the CTM. -/
theorem exec_validators (h : exec K e s c = some s') (hc : c.entry.runsCut = false) (x : Address) :
    s'.validators x = s.validators x ∨
      (c.entry = .setValidator x (s'.validators x) ∧ c.sender = s.chainTypeManager) := by
  suffices H : Holds (fun s' => s'.validators x = s.validators x ∨
      (c.entry = .setValidator x (s'.validators x) ∧ c.sender = s.chainTypeManager))
      (exec K e s c) from H s' h
  rcases c with ⟨snd, τ, en⟩
  cases en <;> simp [Entry.runsCut] at hc <;> exec_simp
  case setValidator v b =>
    intro hs
    by_cases hx : x = v <;> simp [hx]

/-- A non-cut call changes the freeze flag only as `freezeDiamond`/`unfreezeDiamond` by the CTM,
each in its own direction. -/
theorem exec_frozen (h : exec K e s c = some s') (hc : c.entry.runsCut = false) :
    s'.frozen = s.frozen ∨
      (c.entry = .freezeDiamond ∧ c.sender = s.chainTypeManager ∧ s.frozen = false ∧
        s'.frozen = true) ∨
      (c.entry = .unfreezeDiamond ∧ c.sender = s.chainTypeManager ∧ s.frozen = true ∧
        s'.frozen = false) := by
  suffices H : Holds (fun s' => s'.frozen = s.frozen ∨
      (c.entry = .freezeDiamond ∧ c.sender = s.chainTypeManager ∧ s.frozen = false ∧
        s'.frozen = true) ∨
      (c.entry = .unfreezeDiamond ∧ c.sender = s.chainTypeManager ∧ s.frozen = true ∧
        s'.frozen = false)) (exec K e s c) from H s' h
  rcases c with ⟨snd, τ, en⟩
  cases en <;> simp [Entry.runsCut] at hc <;> exec_simp

/-- A non-cut call changes the priority-mode `activated` bit only as `activatePriorityMode`
(false to true) or `deactivatePriorityMode` by the CTM (true to false). -/
theorem exec_activated (h : exec K e s c = some s') (hc : c.entry.runsCut = false) :
    s'.priorityMode.activated = s.priorityMode.activated ∨
      (c.entry = .activatePriorityMode ∧ s'.priorityMode.activated = true) ∨
      (c.entry = .deactivatePriorityMode ∧ c.sender = s.chainTypeManager ∧
        s'.priorityMode.activated = false) := by
  suffices H : Holds (fun s' => s'.priorityMode.activated = s.priorityMode.activated ∨
      (c.entry = .activatePriorityMode ∧ s'.priorityMode.activated = true) ∨
      (c.entry = .deactivatePriorityMode ∧ c.sender = s.chainTypeManager ∧
        s'.priorityMode.activated = false)) (exec K e s c) from H s' h
  rcases c with ⟨snd, τ, en⟩
  cases en <;> simp [Entry.runsCut] at hc <;> exec_simp

/-- A non-cut call never clears `isPermanentRollup`, `secondProofSystemRequired` or
`canBeActivated`, and while `canBeActivated` holds it changes neither the pricing mode nor the
three capacity fields of the fee parameters. -/
theorem exec_oneWay (h : exec K e s c = some s') (hc : c.entry.runsCut = false) :
    (s.isPermanentRollup = true → s'.isPermanentRollup = true) ∧
    (s.secondProofSystemRequired = true → s'.secondProofSystemRequired = true) ∧
    (s.priorityMode.canBeActivated = true →
      s'.priorityMode.canBeActivated = true ∧
      s'.feeParams.pricingMode = s.feeParams.pricingMode ∧
      s'.feeParams.priorityTxMaxPubdata = s.feeParams.priorityTxMaxPubdata ∧
      s'.feeParams.maxPubdataPerBatch = s.feeParams.maxPubdataPerBatch ∧
      s'.feeParams.maxL2GasPerBatch = s.feeParams.maxL2GasPerBatch) := by
  suffices H : Holds (fun s' =>
      (s.isPermanentRollup = true → s'.isPermanentRollup = true) ∧
      (s.secondProofSystemRequired = true → s'.secondProofSystemRequired = true) ∧
      (s.priorityMode.canBeActivated = true →
        s'.priorityMode.canBeActivated = true ∧
        s'.feeParams.pricingMode = s.feeParams.pricingMode ∧
        s'.feeParams.priorityTxMaxPubdata = s.feeParams.priorityTxMaxPubdata ∧
        s'.feeParams.maxPubdataPerBatch = s.feeParams.maxPubdataPerBatch ∧
        s'.feeParams.maxL2GasPerBatch = s.feeParams.maxL2GasPerBatch)) (exec K e s c)
    from H s' h
  rcases c with ⟨snd, τ, en⟩
  cases en <;> simp [Entry.runsCut] at hc <;> exec_simp

/-- A non-cut call preserves `Stage1Inv`. -/
theorem exec_stage1 (h : exec K e s c = some s') (hc : c.entry.runsCut = false)
    (hi : Stage1Inv s) : Stage1Inv s' := by
  suffices H : Holds Stage1Inv (exec K e s c) from H s' h
  obtain ⟨h1, h2⟩ := hi
  rcases c with ⟨snd, τ, en⟩
  cases en <;> simp [Entry.runsCut] at hc <;>
    simp (config := { contextual := true }) [exec, onlyL1, onlySettlementLayer,
      noUnverifiedBatches, revertBatches, Stage1Inv, h1, h2] <;> intros <;> simp_all

end Frame

/-! ## Foreign writes -/

section Foreign

variable {s s' : State}

theorem Foreign.owned_eq (h : Foreign s s') : s'.owned = s.owned := h.1

theorem Foreign.admin (h : Foreign s s') : s'.admin = s.admin := by
  simpa [State.owned] using congrArg Owned.admin h.1
theorem Foreign.pendingAdmin (h : Foreign s s') : s'.pendingAdmin = s.pendingAdmin := by
  simpa [State.owned] using congrArg Owned.pendingAdmin h.1
theorem Foreign.chainTypeManager (h : Foreign s s') : s'.chainTypeManager = s.chainTypeManager :=
  by simpa [State.owned] using congrArg Owned.chainTypeManager h.1
theorem Foreign.validators (h : Foreign s s') : s'.validators = s.validators := by
  simpa [State.owned] using congrArg Owned.validators h.1
theorem Foreign.frozen (h : Foreign s s') : s'.frozen = s.frozen := by
  simpa [State.owned] using congrArg Owned.frozen h.1
theorem Foreign.freezable (h : Foreign s s') : s'.freezable = s.freezable := by
  simpa [State.owned] using congrArg Owned.freezable h.1
theorem Foreign.protocolVersion (h : Foreign s s') : s'.protocolVersion = s.protocolVersion := by
  simpa [State.owned] using congrArg Owned.protocolVersion h.1
theorem Foreign.l1TxFiltering (h : Foreign s s') : s'.l1TxFiltering = s.l1TxFiltering := by
  simpa [State.owned] using congrArg Owned.l1TxFiltering h.1
theorem Foreign.feeParams (h : Foreign s s') : s'.feeParams = s.feeParams := by
  simpa [State.owned] using congrArg Owned.feeParams h.1
theorem Foreign.transactionFilterer (h : Foreign s s') :
    s'.transactionFilterer = s.transactionFilterer := by
  simpa [State.owned] using congrArg Owned.transactionFilterer h.1
theorem Foreign.secondProofSystemRequired (h : Foreign s s') :
    s'.secondProofSystemRequired = s.secondProofSystemRequired := by
  simpa [State.owned] using congrArg Owned.secondProofSystemRequired h.1
theorem Foreign.priorityMode (h : Foreign s s') : s'.priorityMode = s.priorityMode := by
  simpa [State.owned] using congrArg Owned.priorityMode h.1

theorem Foreign.stage1 (h : Foreign s s') (hi : Stage1Inv s) : Stage1Inv s' := by
  obtain ⟨h1, h2⟩ := hi
  refine ⟨?_, ?_⟩
  · rw [h.priorityMode]; intro ha
    obtain ⟨hc, hp⟩ := h1 ha
    exact ⟨hc, h.2 hp⟩
  · rw [h.priorityMode, h.l1TxFiltering, h.transactionFilterer]; exact h2

end Foreign

/-! ## Runs -/

theorem Run.append {K : Config} {w₁ w₂ w₃ : World} {l₁ l₂ : List Label}
    (h₁ : Run K w₁ l₁ w₂) (h₂ : Run K w₂ l₂ w₃) : Run K w₁ (l₁ ++ l₂) w₃ := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hs _ ih => exact Run.cons hs (ih h₂)

theorem Run.single {K : Config} {w w' : World} {l : Label} (h : Step K w l w') :
    Run K w [l] w' := Run.cons h (Run.nil _)

/-- Any predicate preserved by every non-cut step holds along a run without cuts. -/
theorem Run.preserve {K : Config} (P : World → Prop)
    (hstep : ∀ w l w', Step K w l w' → l.runsCut = false → P w → P w')
    {w w' : World} {ls : List Label} (hr : Run K w ls w')
    (hnc : ∀ l ∈ ls, l.runsCut = false) (hw : P w) : P w' := by
  induction hr with
  | nil => exact hw
  | cons hs _ ih =>
    exact ih (fun l hl => hnc l (List.mem_cons_of_mem _ hl))
      (hstep _ _ _ hs (hnc _ List.mem_cons_self) hw)

end Contracts.AdminFacet
