import EraSpec.Protocol.NativeValueLegs.Properties.LegConservationRuns
import EraSpec.Protocol.NativeValueLegs.Proofs.LegConservation

/-!
# Proofs: along every run, each refund is bound to the send that committed its leg

Every function of the model only ever sets tracker registrations (`registerIfNeeded_regMono` and
the lemmas after it), so with `CodeFrames` an asset a send collected through the holder or the
vault stays registered for the rest of the run (`sentRegistered_reach`).  The premise-free
invariant `Inv` (`inv_reach`) says every leg that is not `Unset` was committed by a logged send,
every claimed leg is `Reverted`, and both logs have distinct keys.  A new claim's leg was
`Revertable`, so `Inv` names the send that committed it; when the claimant passed that send's bytes,
the decoder round trip identifies the decoded bundle with the sent one, and `claim_shifted_gen` from
`LegConservation` gives the exact refund, its registration premise discharged by
`sentRegistered_reach` for a send through the holder or the vault (`matches_reach`).
-/

namespace Contracts.NativeValueLegs

/-! ## Registrations only grow -/

theorem RegMono.refl (w : World) : RegMono w w := fun _ h => h

theorem RegMono.trans {w₁ w₂ w₃ : World} (h₁ : RegMono w₁ w₂) (h₂ : RegMono w₂ w₃) :
    RegMono w₁ w₃ := fun a h => h₂ a (h₁ a h)

theorem RegMono.of_eq {w w' : World} (h : w'.registered = w.registered) : RegMono w w' :=
  fun a ha => by rw [h]; exact ha

theorem registerIfNeeded_regMono {cfg : Config} {w w' : World} {a : AssetId}
    (h : registerIfNeeded cfg w a = some w') : RegMono w w' := by
  unfold registerIfNeeded at h
  intro b hb
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h
  · exact hb
  · simp only [Function.update_apply]
    split_ifs <;> simp_all
  · simp only [Function.update_apply]
    split_ifs <;> simp_all

theorem trackerInitiate_regMono {cfg : Config} {w w' : World} {d : Chain} {a : AssetId}
    {amount : ℕ} (h : trackerInitiate cfg w d a amount = some w') : RegMono w w' := by
  unfold trackerInitiate at h
  by_cases htok : cfg.tokenOf a = 0
  · simp [htok] at h
  rw [ite_eq_right htok] at h
  obtain ⟨w₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
  refine (registerIfNeeded_regMono h₁).trans (RegMono.of_eq ?_)
  split_ifs at h₂ <;> simp at h₂ <;> subst h₂ <;> rfl

theorem trackerFinalize_regMono {cfg : Config} {w w' : World} {d : Chain} {a : AssetId}
    {amount : ℕ} (h : trackerFinalize cfg w d a amount = some w') : RegMono w w' := by
  unfold trackerFinalize at h
  obtain ⟨w₁, h₁, h₂⟩ := Option.map_eq_some_iff.mp h
  refine (registerIfNeeded_regMono h₁).trans (RegMono.of_eq ?_)
  subst h₂
  split_ifs <;> rfl

theorem routerRecoverBase_regMono {cfg : Config} {w w' : World} {d : Chain} {a : AssetId}
    {u : Address} {v : ℕ} (h : routerRecoverBase cfg w d a u v = some w') : RegMono w w' := by
  unfold routerRecoverBase vaultRefund holderRecover sendValue at h
  split_ifs at h <;> (try simp only [Option.some.injEq] at h)
  all_goals first
    | (subst h; exact RegMono.refl _)
    | (obtain ⟨w₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
       refine (trackerFinalize_regMono h₁).trans (RegMono.of_eq ?_)
       (try split_ifs at h₂)
       all_goals first
         | simp only [reduceCtorEq] at h₂
         | (simp only [Option.some.injEq] at h₂; subst h₂; rfl))

theorem vaultBurn_regMono {cfg : Config} {w w' : World} {d : Chain} {a : AssetId} {u : Address}
    {v : ℕ} (h : vaultBurn cfg w d a u v = some w') : RegMono w w' := by
  unfold vaultBurn at h
  split_ifs at h
  all_goals
    obtain ⟨w₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    refine (trackerInitiate_regMono h₁).trans (RegMono.of_eq ?_)
    first
    | simp only [reduceCtorEq] at h₂
    | split_ifs at h₂
      simp only [Option.some.injEq] at h₂
      subst h₂
      rfl

theorem collect_regMono {P : Params} (hc : CodeFrames P) {w w' : World} {u : Address} {d : Chain}
    {a : AssetId} {v : ℕ} (h : collect P w u d a v = some w') : RegMono w w' := by
  unfold collect routerDepositBase holderBurn at h
  split_ifs at h <;> (try simp only [Option.some.injEq] at h)
  all_goals first
    | (subst h; exact RegMono.refl _)
    | exact RegMono.trans (w₂ := moveNative w u P.cfg.holder v) (RegMono.of_eq rfl)
        (trackerInitiate_regMono h)
    | exact vaultBurn_regMono h
    | exact hc.customMono _ _ _ _ _ _ _ h

theorem recoverBundle_regMono {P : Params} (hc : CodeFrames P) {d : Chain} {A : AssetId} :
    ∀ (calls : List Call) (w w' : World), recoverBundle P d A w calls = some w' → RegMono w w'
  | [], w, w', h => by
    simp only [recoverBundle, Option.some.injEq] at h
    subst h
    exact RegMono.refl _
  | c :: cs, w, w', h => by
    simp only [recoverBundle] at h
    obtain ⟨w₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    refine RegMono.trans ?_ (recoverBundle_regMono hc cs w₁ w' h₂)
    unfold recoverCall at h₁
    split_ifs at h₁
    · exact hc.recoverMono _ _ _ _ h₁
    · exact routerRecoverBase_regMono h₁
    · simp only [Option.some.injEq] at h₁
      subst h₁
      exact RegMono.refl _

theorem claimRefund_regMono {P : Params} (hc : CodeFrames P) {w w' : World} {B : Bundle}
    (h : claimRefund P w B = some w') : RegMono w w' := by
  unfold claimRefund at h
  split_ifs at h
  exact recoverBundle_regMono hc _ _ _ h


/-! ## Structural invariants of runs -/

theorem setLeg_self (legs : Word → Word → LegState) (f h : Word) (s : LegState) :
    setLeg legs f h s f h = s := by
  simp [setLeg]

theorem setLeg_other (legs : Word → Word → LegState) {f h f' h' : Word} (s : LegState)
    (hne : ¬ (f' = f ∧ h' = h)) : setLeg legs f h s f' h' = legs f' h' := by
  simp only [setLeg, hne, ↓reduceIte]

/-- What every reachable state satisfies, with no premise. -/
structure Inv (R : RunParams) (S : State) : Prop where
  /-- Every leg that is not `Unset` was committed by a logged send. -/
  legsLogged : ∀ F h, S.legs F h ≠ .Unset →
    ∃ s ∈ S.sent, s.flowId = F ∧ R.keccak (R.enc s.bundle) = h
  /-- Every logged send's leg is not `Unset`. -/
  sentSet : ∀ s ∈ S.sent, S.legs s.flowId (R.keccak (R.enc s.bundle)) ≠ .Unset
  /-- The logged sends' keys are distinct. -/
  sentNodup : (S.sent.map (Sent.key R)).Nodup
  /-- Every logged claim's leg is `Reverted`. -/
  claimedReverted : ∀ r ∈ S.claimed, S.legs r.flowId (R.keccak r.bytes) = .Reverted
  /-- The logged claims' keys are distinct. -/
  claimedNodup : (S.claimed.map (Claimed.key R)).Nodup
  /-- Every logged send passed the send step's guards. -/
  sentOk : ∀ s ∈ S.sent, s.bundle.destChain ≠ R.cfg.l1Chain ∧
    (∀ st ∈ s.starters, StarterPasses deployed R.cfg st) ∧
    List.Forall₂ (FormsCall R.cfg s.bundle.destBaseAsset s.sender) s.starters s.bundle.calls
  /-- Every logged claim decoded its bytes and its refund succeeded. -/
  claimRecord : ∀ r ∈ S.claimed, R.dec r.bytes = some r.bundle ∧
    claimRefund R.toParams r.before r.bundle = some r.after

theorem inv_init (R : RunParams) (w : World) : Inv R (State.init w) where
  legsLogged := fun _ _ h => absurd rfl h
  sentSet := fun _ h => absurd h List.not_mem_nil
  sentNodup := List.nodup_nil
  claimedReverted := fun _ h => absurd h List.not_mem_nil
  claimedNodup := List.nodup_nil
  sentOk := fun _ h => absurd h List.not_mem_nil
  claimRecord := fun _ h => absurd h List.not_mem_nil

theorem inv_step {R : RunParams} {S S' : State} (hI : Inv R S) (hs : Step R S S') : Inv R S' := by
  cases hs with
  | send u starters B F w₁ w₂ w₃ hd hp hf _ _ _ hU =>
    set k := R.keccak (R.enc B) with hk
    refine ⟨?_, ?_, ?_, ?_, hI.claimedNodup, ?_, hI.claimRecord⟩
    · intro F' h' hne
      dsimp only at hne ⊢
      by_cases hkey : F' = F ∧ h' = k
      · exact ⟨⟨u, starters, B, F, routeOf R.cfg w₁ B.destBaseAsset⟩, by simp, hkey.1.symm,
          hkey.2.symm⟩
      · rw [setLeg_other _ _ hkey] at hne
        obtain ⟨s, hs, h1, h2⟩ := hI.legsLogged F' h' hne
        exact ⟨s, List.mem_append_left _ hs, h1, h2⟩
    · intro s hs
      dsimp only at hs ⊢
      by_cases hkey : s.flowId = F ∧ R.keccak (R.enc s.bundle) = k
      · rw [hkey.1, hkey.2, setLeg_self]
        exact LegState.noConfusion
      · rw [setLeg_other _ _ hkey]
        rcases List.mem_append.mp hs with hs | hs
        · exact hI.sentSet s hs
        · simp only [List.mem_singleton] at hs
          subst hs
          exact absurd ⟨rfl, rfl⟩ hkey
    · rw [List.map_append, List.nodup_append]
      refine ⟨hI.sentNodup, List.nodup_singleton _, ?_⟩
      intro a ha b hb hab
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
      subst hb
      simp only [Sent.key, Prod.mk.injEq] at hab
      have := hI.sentSet s hs
      rw [hab.1, hab.2] at this
      exact this hU
    · intro r hr
      dsimp only at hr ⊢
      have hrev := hI.claimedReverted r hr
      by_cases hkey : r.flowId = F ∧ R.keccak r.bytes = k
      · rw [hkey.1, hkey.2] at hrev
        rw [hU] at hrev
        exact absurd hrev LegState.noConfusion
      · rw [setLeg_other _ _ hkey]
        exact hrev
    · intro s hs
      dsimp only at hs ⊢
      rcases List.mem_append.mp hs with hs | hs
      · exact hI.sentOk s hs
      · simp only [List.mem_singleton] at hs
        subst hs
        exact ⟨hd, hp, hf⟩
  | authorize F h hC =>
    refine ⟨?_, ?_, hI.sentNodup, ?_, hI.claimedNodup, hI.sentOk, hI.claimRecord⟩
    · intro F' h' hne
      dsimp only at hne ⊢
      by_cases hkey : F' = F ∧ h' = h
      · rw [hkey.1, hkey.2]
        exact hI.legsLogged F h (by rw [hC]; exact LegState.noConfusion)
      · rw [setLeg_other _ _ hkey] at hne
        exact hI.legsLogged F' h' hne
    · intro s hs
      dsimp only at hs ⊢
      by_cases hkey : s.flowId = F ∧ R.keccak (R.enc s.bundle) = h
      · rw [hkey.1, hkey.2, setLeg_self]
        exact LegState.noConfusion
      · rw [setLeg_other _ _ hkey]
        exact hI.sentSet s hs
    · intro r hr
      dsimp only at hr ⊢
      have hrev := hI.claimedReverted r hr
      by_cases hkey : r.flowId = F ∧ R.keccak r.bytes = h
      · rw [hkey.1, hkey.2, hC] at hrev
        exact absurd hrev LegState.noConfusion
      · rw [setLeg_other _ _ hkey]
        exact hrev
  | claim F x B w' hR hdec hclaim =>
    refine ⟨?_, ?_, hI.sentNodup, ?_, ?_, hI.sentOk, ?_⟩
    · intro F' h' hne
      dsimp only at hne ⊢
      by_cases hkey : F' = F ∧ h' = R.keccak x
      · rw [hkey.1, hkey.2]
        exact hI.legsLogged F (R.keccak x) (by rw [hR]; exact LegState.noConfusion)
      · rw [setLeg_other _ _ hkey] at hne
        exact hI.legsLogged F' h' hne
    · intro s hs
      dsimp only at hs ⊢
      by_cases hkey : s.flowId = F ∧ R.keccak (R.enc s.bundle) = R.keccak x
      · rw [hkey.1, hkey.2, setLeg_self]
        exact LegState.noConfusion
      · rw [setLeg_other _ _ hkey]
        exact hI.sentSet s hs
    · intro r hr
      dsimp only at hr ⊢
      rcases List.mem_append.mp hr with hr | hr
      · have hrev := hI.claimedReverted r hr
        by_cases hkey : r.flowId = F ∧ R.keccak r.bytes = R.keccak x
        · rw [hkey.1, hkey.2, hR] at hrev
          exact absurd hrev LegState.noConfusion
        · rw [setLeg_other _ _ hkey]
          exact hrev
      · simp only [List.mem_singleton] at hr
        subst hr
        exact setLeg_self _ _ _ _
    · rw [List.map_append, List.nodup_append]
      refine ⟨hI.claimedNodup, List.nodup_singleton _, ?_⟩
      intro a ha b hb hab
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
      subst hb
      simp only [Claimed.key, Prod.mk.injEq] at hab
      have := hI.claimedReverted r hr
      rw [hab.1, hab.2, hR] at this
      exact LegState.noConfusion this
    · intro r hr
      dsimp only at hr ⊢
      rcases List.mem_append.mp hr with hr | hr
      · exact hI.claimRecord r hr
      · simp only [List.mem_singleton] at hr
        subst hr
        exact ⟨hdec, hclaim⟩
  | other w' _ =>
    exact ⟨hI.legsLogged, hI.sentSet, hI.sentNodup, hI.claimedReverted, hI.claimedNodup,
      hI.sentOk, hI.claimRecord⟩

theorem inv_reach {R : RunParams} {w₀ : World} {S : State} (h : Reach R (State.init w₀) S) :
    Inv R S := by
  induction h with
  | refl => exact inv_init R w₀
  | tail _ hs ih => exact inv_step ih hs

theorem step_sent_sub {R : RunParams} {S S' : State} (hs : Step R S S') : S.sent ⊆ S'.sent := by
  cases hs with
  | send => exact List.subset_append_left _ _
  | authorize => exact List.Subset.refl _
  | claim => exact List.Subset.refl _
  | other => exact List.Subset.refl _

/-! ## Registrations of sent assets persist -/

theorem routeOf_not_custom {cfg : Config} {w : World} {A : AssetId}
    (h : ¬ (routeOf cfg w A).IsCustom) : A = cfg.baseAsset ∨ w.handler A = cfg.ntv := by
  unfold routeOf at h
  by_cases hA : A = cfg.baseAsset
  · exact Or.inl hA
  · by_cases hH : w.handler A = cfg.ntv
    · exact Or.inr hH
    · simp [hA, hH, Route.IsCustom] at h

/-- Every sent asset collected through the holder or the vault stays registered. -/
def SentRegistered (S : State) : Prop :=
  ∀ s ∈ S.sent, ¬ s.route.IsCustom → 0 < collected s.starters →
    S.world.registered s.bundle.destBaseAsset = true

theorem sentRegistered_reach {R : RunParams} (hc : CodeFrames R.toParams) {w₀ : World}
    {S : State} (h : Reach R (State.init w₀) S) : SentRegistered S := by
  induction h with
  | refl => intro s hs; exact absurd hs List.not_mem_nil
  | tail _ hs ih =>
    cases hs with
    | send u starters B F w₁ w₂ w₃ hd hp hf h₁ hcol h₃ hU =>
      intro s hs' hnc hpos
      rcases List.mem_append.mp hs' with hs' | hs'
      · exact h₃ _ (collect_regMono hc hcol _ (h₁ _ (ih s hs' hnc hpos)))
      · simp only [List.mem_singleton] at hs'
        subst hs'
        exact h₃ _ (collect_registers hpos (routeOf_not_custom hnc) hcol)
    | authorize => exact ih
    | claim F x B w' _ _ hclaim =>
      intro s hs' hnc hpos
      exact claimRefund_regMono hc hclaim _ (ih s hs' hnc hpos)
    | other w' hmono =>
      intro s hs' hnc hpos
      exact hmono _ (ih s hs' hnc hpos)

/-! ## The headline -/

theorem ClaimMatches.mono {R : RunParams} {sent sent' : List Sent} {r : Claimed}
    (hsub : sent ⊆ sent') (h : ClaimMatches R sent r) : ClaimMatches R sent' r := by
  obtain ⟨s, hs, rest⟩ := h
  exact ⟨s, hsub hs, rest⟩

theorem matches_reach {R : RunParams} (hc : CodeFrames R.toParams) {w₀ : World} {S : State}
    (h : Reach R (State.init w₀) S) :
    (∀ s ∈ S.sent, s.sender ≠ R.cfg.router) →
    (∀ s ∈ S.sent, R.dec (R.enc s.bundle) = some s.bundle) →
    ∀ r ∈ S.claimed, ClaimMatches R S.sent r := by
  induction h with
  | refl => intro _ _ r hr; exact absurd hr List.not_mem_nil
  | @tail T U hreach hstep ih =>
    intro hu hdec r hr
    have hsub := step_sent_sub hstep
    have ih' := ih (fun s hs => hu s (hsub hs)) (fun s hs => hdec s (hsub hs))
    have hinv := inv_reach hreach
    have hregs := sentRegistered_reach hc hreach
    cases hstep with
    | send => exact (ih' r hr).mono hsub
    | authorize => exact ih' r hr
    | other => exact ih' r hr
    | claim F x B w' hR hdecx hclaim =>
      rcases List.mem_append.mp hr with hr | hr
      · exact ih' r hr
      · simp only [List.mem_singleton] at hr
        subst hr
        obtain ⟨s, hs, hsF, hsk⟩ :=
          hinv.legsLogged F (R.keccak x) (by rw [hR]; exact LegState.noConfusion)
        refine ⟨s, hs, hsF, hsk, ?_⟩
        by_cases hx : x = R.enc s.bundle
        · left
          have hB : B = s.bundle := by
            rw [hx, hdec s hs] at hdecx
            exact (Option.some.inj hdecx).symm
          refine ⟨hx, hB, fun hcase => ?_⟩
          obtain ⟨-, hpass, hforms⟩ := hinv.sentOk s hs
          subst hB
          refine claim_shifted_gen (hu s hs) hpass hforms (hc.recover _) (fun hpos => ?_) hclaim
          rcases hcase with h0 | hnc | hreg | hnat
          · exact absurd h0 (Nat.pos_iff_ne_zero.mp hpos)
          · exact Or.inr (Or.inl (hregs s hs hnc hpos))
          · exact Or.inr (Or.inl hreg)
          · exact Or.inr (Or.inr hnat)
        · exact Or.inr hx

theorem EveryClaimRefundsItsSenderOrCollision :
    Properties.EveryClaimRefundsItsSenderOrCollision := by
  intro R w₀ S h hc hu hdec
  exact matches_reach hc h hu hdec

theorem EachLegSentOnce : Properties.EachLegSentOnce := by
  intro R w₀ S h
  exact (inv_reach h).sentNodup

theorem EachLegClaimedAtMostOnce : Properties.EachLegClaimedAtMostOnce := by
  intro R w₀ S h
  exact (inv_reach h).claimedNodup

/-! ## Witnesses -/

theorem wParams_codeFrames : CodeFrames wParams where
  recover := wRecover_frames
  recoverMono := by
    intro w d cd w' h
    cases cd with
    | finalizeDeposit src a m =>
      simp only [wParams, wRecover, Option.some.injEq] at h
      subst h
      exact RegMono.of_eq rfl
    | other raw =>
      simp only [wParams, wRecover, Option.some.injEq] at h
      subst h
      exact RegMono.refl _
  customMono := by
    intro h w d a u v w' hb
    simp only [wParams, wCustomBurn] at hb
    split_ifs at hb
    simp only [Option.some.injEq] at hb
    subst hb
    exact RegMono.of_eq rfl

/-- The bundle the witness run sends: a direct call of value `6` and a router-produced call on asset
`300`, to chain `20`, whose base-token asset `200` is native to the source chain. -/
def wRunBundle : Bundle := wBundle 200 [wDirectCall 5 6, wRouterCall 300 0]

/-- The world after the witness run's collection. -/
def wRunW₂ : World := (collect wParams wWorld 5 20 200 6).get (by decide)

/-- The world after the witness run's refund. -/
def wRunW₃ : World := (claimRefund wParams wRunW₂ wRunBundle).get (by decide)

theorem RunClaimWitness : Properties.RunClaimWitness := by
  have hcol : collect (wRun wRunBundle).toParams wWorld 5 wRunBundle.destChain
      wRunBundle.destBaseAsset (collected [wDirect 6, wIndirect 0]) = some wRunW₂ :=
    (Option.some_get _).symm
  have hclaim : claimRefund (wRun wRunBundle).toParams wRunW₂ wRunBundle = some wRunW₃ :=
    (Option.some_get _).symm
  have hforms : List.Forall₂ (FormsCall (wRun wRunBundle).cfg wRunBundle.destBaseAsset 5)
      [wDirect 6, wIndirect 0] wRunBundle.calls :=
    .cons (wDirect_forms 200 5 6) (.cons (wIndirect_forms 200 300 5 0 (by decide)) .nil)
  refine ⟨wRun wRunBundle, wWorld, _,
    Reach.tail (Reach.tail (Reach.tail Reach.refl
      (Step.send 5 [wDirect 6, wIndirect 0] wRunBundle 1 wWorld wRunW₂ wRunW₂ (by decide)
        wPair_passes hforms (RegMono.refl _) hcol (RegMono.refl _) rfl))
      (Step.authorize 1 (wKeccak [7]) (by decide)))
      (Step.claim 1 [7] wRunBundle wRunW₃ (by decide) (by decide) hclaim),
    wParams_codeFrames, ?_, ?_, ?_⟩
  · intro s hs
    simp only [State.init, List.nil_append, List.mem_singleton] at hs
    subst hs
    decide
  · intro s hs
    simp only [State.init, List.nil_append, List.mem_singleton] at hs
    subst hs
    decide
  · refine ⟨⟨1, [7], wRunBundle, wRunW₂, wRunW₃⟩, by simp [State.init],
      ⟨5, [wDirect 6, wIndirect 0], wRunBundle, 1,
        routeOf (wRun wRunBundle).cfg wWorld wRunBundle.destBaseAsset⟩, by simp [State.init],
      rfl, by decide, by decide⟩

end Contracts.NativeValueLegs
