import EraSpec.Contracts.NativeTokenVaultBase.Properties.Pause
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.Resolution
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.PreparationGuards

/-!
# Proofs: a vault pause freezes the vault, and unpausing returns it exactly

Proofs of `EraSpec.Contracts.NativeTokenVaultBase.Properties.Pause`.  Every entry point rejects a
paused vault (`paused_preparation_rejected`, `ResolutionPausedRejected`), and the commit interfaces
keep the state on a rejection, so each attempt is the identity.  The pause and unpause calls touch
only the flag.  The round trip is then B2's `PrepareThenRecoverRoundTrip`.
-/

namespace Contracts.NativeTokenVaultBase

variable {Accounting : Type}

theorem vaultPause_of_unpaused {s : State Accounting} (hp : s.paused = false) :
    vaultPause s = some { s with paused := true } := by
  unfold vaultPause; rw [hp]; rfl

theorem vaultPause_eq_some {s p : State Accounting} (h : vaultPause s = some p) :
    s.paused = false ∧ p = { s with paused := true } := by
  unfold vaultPause at h
  cases hs : s.paused
  · rw [hs] at h
    exact ⟨rfl, (Option.some.inj h).symm⟩
  · rw [hs] at h
    cases h

theorem vaultUnpause_of_pause {s : State Accounting} (hp : s.paused = false) :
    vaultUnpause { s with paused := true } = some s := by
  unfold vaultUnpause
  dsimp only
  rw [ite_eq_left rfl]
  cases s
  simp_all

/-- On a paused vault, each attempted call commits nothing. -/
theorem VaultEntryCall.commit_paused (hooks : Hooks Accounting) (rh : ResolutionHooks Accounting)
    {s : State Accounting} (hp : s.paused = true) (c : VaultEntryCall) :
    c.commit hooks rh s = s := by
  cases c with
  | burn r =>
    show (transact hooks s r).1 = s
    unfold transact
    rw [show prepare hooks s r = none from paused_preparation_rejected hp]
  | mint c =>
    show (commitResolution s (bridgeMint rh s c)).1 = s
    rw [(ResolutionPausedRejected _ rh s c hp).1]
    rfl
  | recover c =>
    show (commitResolution s (bridgeRecoverFailedTransfer rh s c)).1 = s
    rw [(ResolutionPausedRejected _ rh s c hp).2]
    rfl

/-- **A PAUSED VAULT COMMITS NOTHING.** -/
theorem commitVaultCalls_paused (hooks : Hooks Accounting) (rh : ResolutionHooks Accounting)
    {s : State Accounting} (hp : s.paused = true) :
    ∀ calls : List VaultEntryCall, commitVaultCalls hooks rh s calls = s
  | [] => rfl
  | c :: cs => by
    unfold commitVaultCalls
    rw [List.foldl_cons, VaultEntryCall.commit_paused hooks rh hp c]
    exact commitVaultCalls_paused hooks rh hp cs

/-- **PAUSE AND UNPAUSE CHANGE ONLY THE FLAG.** -/
theorem vault_pause_toggles_only_the_flag (s : State Accounting) :
    (s.paused = false → vaultPause s = some { s with paused := true }
        ∧ vaultUnpause { s with paused := true } = some s ∧ vaultUnpause s = none)
    ∧ (s.paused = true → vaultPause s = none) := by
  refine ⟨fun hp => ⟨vaultPause_of_unpaused hp, vaultUnpause_of_pause hp, ?_⟩, fun hp => ?_⟩
  · unfold vaultUnpause; rw [hp]; rfl
  · unfold vaultPause; rw [hp]; rfl

/-- After any attempts on the paused vault `p` obtained by pausing `d`, unpausing returns `d`. -/
theorem vaultUnpause_after_attempts (hooks : Hooks Accounting) (rh : ResolutionHooks Accounting)
    {d p : State Accounting} (h : vaultPause d = some p) (calls : List VaultEntryCall) :
    vaultUnpause (commitVaultCalls hooks rh p calls) = some d := by
  obtain ⟨hd, rfl⟩ := vaultPause_eq_some h
  rw [commitVaultCalls_paused hooks rh rfl calls]
  exact vaultUnpause_of_pause hd

/-- **A PAUSE DELAYS A RECOVERY AND DOES NOT CHANGE IT.** -/
theorem recovery_delayed_not_lost {hooks : Hooks Accounting} {rh : ResolutionHooks Accounting}
    {s : State Accounting} {r : Request} {out : Result Accounting} {p : State Accounting}
    (hc : HooksCancel hooks rh) (hw : WellFormed s) (hprep : prepare hooks s r = some out)
    (hpause : vaultPause out.state = some p) (calls : List VaultEntryCall) :
    recoverTransact rh p (recoveryCall s.config.router r out.data) = (p, false)
    ∧ vaultUnpause (commitVaultCalls hooks rh p calls) = some out.state
    ∧ bridgeRecoverFailedTransfer rh out.state (recoveryCall s.config.router r out.data) = some s := by
  obtain ⟨_, rfl⟩ := vaultPause_eq_some hpause
  refine ⟨?_, vaultUnpause_after_attempts hooks rh hpause calls,
    (PrepareThenRecoverRoundTrip _ hooks rh s r out hc hw hprep).1⟩
  unfold recoverTransact
  rw [(ResolutionPausedRejected _ rh _ _ rfl).2]
  rfl

/-- **…AND THE SAME FOR DELIVERY.** -/
theorem delivery_delayed_not_lost (hooks : Hooks Accounting) (rh : ResolutionHooks Accounting)
    {d p : State Accounting} (c : ResolutionCall) (h : vaultPause d = some p)
    (calls : List VaultEntryCall) :
    bridgeMint rh p c = none ∧ vaultUnpause (commitVaultCalls hooks rh p calls) = some d := by
  refine ⟨?_, vaultUnpause_after_attempts hooks rh h calls⟩
  obtain ⟨_, rfl⟩ := vaultPause_eq_some h
  exact (ResolutionPausedRejected _ rh _ c rfl).1

theorem vault_pause_witness : Properties.VaultPauseWitness := by
  obtain ⟨hooks, rh, s, r, out, c, t, hc, hw, hprep, hamt, hacc, hround, hmint, _, _, _⟩ :=
    ResolutionExample.resolutionSatisfiable
  have hsp : s.paused = false := by
    cases h : s.paused
    · rfl
    · exact absurd (show prepare hooks s r = none from paused_preparation_rejected h)
        (by rw [hprep]; exact Option.some_ne_none _)
  have hop : out.state.paused = false := by
    rw [(preparation_preserves_ledger hw hprep).2.2.2.1]; exact hsp
  have hpause := vaultPause_of_unpaused hop
  refine ⟨hooks, rh, s, r, out, _, c, t, hc, hw, hprep, hamt, hacc, hpause,
    (recovery_delayed_not_lost hc hw hprep hpause []).1, hround, hmint,
    _, vaultPause_of_unpaused hsp, (ResolutionPausedRejected _ rh _ c rfl).1⟩

end Contracts.NativeTokenVaultBase

/-! ## Certificates -/

namespace Contracts.NativeTokenVaultBase

theorem VaultPauseTogglesOnlyTheFlag : Properties.VaultPauseTogglesOnlyTheFlag :=
  fun _ s => vault_pause_toggles_only_the_flag s

theorem PausedVaultCommitsNothing : Properties.PausedVaultCommitsNothing :=
  fun _ hooks rh _ calls hp => commitVaultCalls_paused hooks rh hp calls

theorem RecoveryDelayedNotLost : Properties.RecoveryDelayedNotLost :=
  fun _ _ _ _ _ _ _ calls hc hw hprep hpause => recovery_delayed_not_lost hc hw hprep hpause calls

theorem DeliveryDelayedNotLost : Properties.DeliveryDelayedNotLost :=
  fun _ hooks rh _ _ c calls h => delivery_delayed_not_lost hooks rh c h calls

theorem VaultPauseWitness : Properties.VaultPauseWitness := vault_pause_witness

end Contracts.NativeTokenVaultBase
