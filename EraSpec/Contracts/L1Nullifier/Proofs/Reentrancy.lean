import EraSpec.Contracts.L1Nullifier.Properties.Reentrancy
import EraSpec.Contracts.L1Nullifier.Proofs.Model

/-!
# Proofs: calls nested inside a claim

`NestedRunIsFlatRun` is an induction over `NestedRun`: in the source order a claim's step already
leaves the post-delete state that its callback starts from, so the claim followed by its callback
and the rest is a `Reach` run, glued by transitivity. The countermodel and the witness are
concrete nested executions from fresh storage.
-/

namespace Contracts.L1Nullifier

private lemma nested_reach_trans {chk : Checks} {env : Env} {cfg : Cfg} {s t u : Sys}
    (h1 : Reach chk env cfg s t) (h2 : Reach chk env cfg t u) : Reach chk env cfg s u := by
  induction h2 with
  | refl => exact h1
  | step _ hs ih => exact .step ih hs

private lemma nested_reach_cons {chk : Checks} {env : Env} {cfg : Cfg} {s t u : Sys} {l : Label}
    (hs : Step chk env cfg s l t) (hr : Reach chk env cfg t u) : Reach chk env cfg s u :=
  nested_reach_trans (.step (.refl _) hs) hr

theorem NestedRunIsFlatRun : Properties.NestedRunIsFlatRun := by
  intro chk env cfg s u hn
  induction hn with
  | nil => exact .refl _
  | step hs _ ih => exact nested_reach_cons hs ih
  | claimDeleteFirst _ ha hok _ _ ih₁ ih₂ =>
    exact nested_reach_cons (Step.confirm ha hok) (nested_reach_trans ih₁ ih₂)
  | claimCallFirst ho => exact absurd ho (by decide)

theorem NestedAtMostOneClearPerDeposit : Properties.NestedAtMostOneClearPerDeposit := by
  intro env cfg s0 s c h h0 hn hw hz
  exact AtMostOneClearPerDeposit env cfg s0 s c h h0 (NestedRunIsFlatRun _ _ _ _ _ hn) hw hz

/-! ## Concrete nested executions -/

private def nestedZeroDeprecated : Deprecated :=
  ⟨0, 0, 0, 0, 0, fun _ => 0, fun _ _ _ => false, fun _ => false, fun _ _ => 0, 0, 0⟩

/-- Fresh proxy storage. -/
private def nestedFresh : Sys :=
  ⟨⟨false, 0, 0, false, fun _ _ => 0, 0, 0, 0, nestedZeroDeprecated⟩, false, []⟩

/-- Nullifier `1`, router `2`, bridgehub `3`. -/
private def nestedCfg : Cfg := ⟨1, 2, 3⟩

/-- Deposit A by `10`; deposit B by `12`, made inside A's claim's callback. -/
private def nestedTripleA : Triple := ⟨10, 11, [1]⟩
private def nestedTripleB : Triple := ⟨12, 11, [2]⟩

/-- Never zero, separates A and B. -/
private def nestedHash (t : Triple) : Bytes32 :=
  if t = nestedTripleA then 7 else if t = nestedTripleB then 8 else 9

/-- The prover accepts the failure of transaction `9` on chain `5` and nothing else. -/
private def nestedEnv : Env :=
  ⟨nestedHash, fun q => q.chainId = 5 ∧ q.l2TxHash = 9 ∧ q.status = .failure⟩

/-- A's claim, with status failure. -/
private def nestedClaimA : Claim := ⟨5, 10, 3, .failure, 11, [1], 9, 1, 4, [6]⟩

private lemma nested_ext10 : ExternalSender nestedCfg 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- After `initialize(10)`, `setL1AssetRouter(2)` and deposit A at `(5, 9)`. -/
private def nestedDeposited : Sys :=
  afterWrite ⟨⟨true, 10, 0, false, fun _ _ => 0, 2, 0, 0, nestedZeroDeprecated⟩, false, []⟩
    (.deposit nestedTripleA) 5 9 (nestedHash nestedTripleA)

private lemma nested_prefix (o : ClaimOrder) {u : Sys}
    (hrest : NestedRun o Checks.source nestedEnv nestedCfg nestedDeposited u) :
    NestedRun o Checks.source nestedEnv nestedCfg nestedFresh u :=
  .step (Step.initialize nested_ext10 rfl (by decide))
    (.step (Step.setL1AssetRouter nested_ext10 rfl rfl (by decide))
      (.step (Step.twoBridges (caller := 10) (c := 5) (h := 9) (req := .deposit 11 [1])
        rfl rfl rfl (fun _ => rfl)) hrest))

private lemma nestedHash_A : nestedHash nestedTripleA = 7 := by simp [nestedHash]
private lemma nestedHash_B : nestedHash nestedTripleB = 8 := by
  simp [nestedHash, nestedTripleA, nestedTripleB]

private lemma nested_claimA_ok (s : Sys) (hp : s.n.paused = false) (hr : s.routerPaused = false)
    (hd : s.n.depositHappened 5 9 = 7) :
    ClaimOk Checks.source nestedEnv nestedCfg s nestedClaimA :=
  ⟨hp, fun _ => by simp [nestedEnv, nestedClaimA, Claim.query],
    fun _ => by
      simp only [nestedClaimA, Claim.triple, nestedEnv]
      rw [hd]; exact nestedHash_A.symm,
    fun _ => hr⟩

private lemma nestedDeposited_slot : nestedDeposited.n.depositHappened 5 9 = 7 := by
  simp [nestedDeposited, afterWrite, nestedHash_A]

theorem CallFirstClearsOneDepositTwice : Properties.CallFirstClearsOneDepositTwice := by
  -- A's claim; inside its call, before the delete, a second claim of A.
  have inner : NestedRun .callFirst Checks.source nestedEnv nestedCfg
      (logClear nestedDeposited nestedClaimA)
      (deleteSlot (logClear (logClear nestedDeposited nestedClaimA) nestedClaimA) nestedClaimA) :=
    .claimCallFirst rfl nested_ext10
      (nested_claimA_ok _ rfl rfl (by simpa [logClear] using nestedDeposited_slot))
      (.nil _) (.nil _)
  have run := nested_prefix .callFirst
    (.claimCallFirst rfl nested_ext10 (nested_claimA_ok _ rfl rfl nestedDeposited_slot) inner (.nil _))
  refine ⟨nestedEnv, nestedCfg, nestedFresh, _, 5, 9, rfl, fun _ _ => rfl, run, ?_, ?_, ?_⟩
  · simp [deleteSlot, logClear, nestedDeposited, afterWrite, isNzWrite, occupied, nestedFresh,
      nestedHash_A]
  · simp [deleteSlot, logClear, nestedDeposited, afterWrite, isZeroClear, nestedEnv, nestedClaimA,
      Claim.triple, nestedHash, nestedTripleA]
  · simp [deleteSlot, logClear, nestedDeposited, afterWrite, isClear, nestedClaimA]

theorem NestedRunWitness : Properties.NestedRunWitness := by
  -- A's claim, whose callback makes deposit B at `(5, 13)`.
  have callback : NestedRun .deleteFirst Checks.source nestedEnv nestedCfg
      (afterClaim nestedDeposited nestedClaimA)
      (afterWrite (afterClaim nestedDeposited nestedClaimA) (.deposit nestedTripleB) 5 13
        (nestedHash nestedTripleB)) :=
    .step (Step.twoBridges (caller := 12) (c := 5) (h := 13) (req := .deposit 11 [2])
      rfl rfl rfl (fun _ => by simp [afterClaim, nestedDeposited, afterWrite, setSlot])) (.nil _)
  have run := nested_prefix .deleteFirst
    (.claimDeleteFirst rfl nested_ext10 (nested_claimA_ok _ rfl rfl nestedDeposited_slot)
      callback (.nil _))
  refine ⟨nestedEnv, nestedCfg, nestedFresh, _, nestedClaimA, nestedTripleB, 13, rfl,
    fun _ _ => rfl, run, ?_, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [nestedEnv, nestedClaimA, Claim.triple, nestedHash, nestedTripleA]
  · simp [nestedEnv, nestedHash_B]
  · simp [afterWrite, afterClaim, nestedDeposited, isNzWrite, occupied, nestedFresh, nestedClaimA,
      nestedHash_A]
  · simp [afterWrite, afterClaim, nestedDeposited, isZeroClear, nestedEnv, nestedClaimA,
      Claim.triple, nestedHash, nestedTripleA]
  · simp [afterWrite, afterClaim, nestedDeposited, isClear, nestedClaimA]

end Contracts.L1Nullifier
