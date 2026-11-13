import EraSpec.Contracts.NativeTokenVaultBase.Specs.Pause

/-!
# Properties: a vault pause freezes the vault, and unpausing returns it exactly

Statements about `EraSpec.Contracts.NativeTokenVaultBase.Specs.Pause`.  Proofs are in
`EraSpec.Contracts.NativeTokenVaultBase.Proofs.Pause`.

* `VaultPauseTogglesOnlyTheFlag`: pausing writes the flag and nothing else, and unpausing undoes it.
* `PausedVaultCommitsNothing`: while paused, every attempted burn, mint and recovery reverts and
  commits nothing.  Any sequence of attempts leaves the vault exactly as it was, accounting
  included.
* `RecoveryDelayedNotLost` (headline): after a preparation, a pause of any length with any attempts
  in it, the recovery of the prepared data among them, leaves the vault exactly as it was.  After
  the unpause, the router's recovery of that data restores the state before the preparation
  exactly (`PrepareThenRecoverRoundTrip`).
* `DeliveryDelayedNotLost`: the destination side of the same.  A paused destination vault rejects
  `bridgeMint`.  After the pause interval the vault is exactly as before it, so the mint behaves
  exactly as it would have.

The witness is `VaultPauseWitness`.
-/

namespace Contracts.NativeTokenVaultBase

/-- **PAUSE AND UNPAUSE CHANGE ONLY THE FLAG.**  Pausing an unpaused vault sets the flag and
nothing else.  Unpausing it then returns exactly the original state.  Neither call succeeds from
the wrong state (OpenZeppelin's `whenNotPaused` and `whenPaused`). -/
def Properties.VaultPauseTogglesOnlyTheFlag : Prop :=
  ∀ (Accounting : Type) (s : State Accounting),
    (s.paused = false → vaultPause s = some { s with paused := true }
        ∧ vaultUnpause { s with paused := true } = some s ∧ vaultUnpause s = none)
    ∧ (s.paused = true → vaultPause s = none)

/-- **A PAUSED VAULT COMMITS NOTHING.**  On a paused vault, every attempted `bridgeBurn`,
`bridgeMint` and `bridgeRecoverFailedTransfer` reverts.  So any sequence of attempts leaves the
whole state unchanged: token, accounting, registry, configuration and flag. -/
def Properties.PausedVaultCommitsNothing : Prop :=
  ∀ (Accounting : Type) (hooks : Hooks Accounting) (rh : ResolutionHooks Accounting)
    (s : State Accounting) (calls : List VaultEntryCall),
    s.paused = true → commitVaultCalls hooks rh s calls = s

/-- **HEADLINE: A PAUSE DELAYS A RECOVERY AND DOES NOT CHANGE IT.**  Premises: hooks satisfying
`HooksCancel`, a `WellFormed` state, a successful preparation, and then a pause
(`vaultPause out.state = some p`).  For any attempts during the pause:

* the router's recovery of the prepared data, attempted while paused, reverts and commits nothing;
* unpausing after the attempts returns exactly the post-preparation state `out.state`;
* from there, the recovery restores the pre-preparation state `s` exactly. -/
def Properties.RecoveryDelayedNotLost : Prop :=
  ∀ (Accounting : Type) (hooks : Hooks Accounting) (rh : ResolutionHooks Accounting)
    (s : State Accounting) (r : Request) (out : Result Accounting) (p : State Accounting)
    (calls : List VaultEntryCall),
    HooksCancel hooks rh → WellFormed s → prepare hooks s r = some out →
    vaultPause out.state = some p →
      recoverTransact rh p (recoveryCall s.config.router r out.data) = (p, false)
      ∧ vaultUnpause (commitVaultCalls hooks rh p calls) = some out.state
      ∧ bridgeRecoverFailedTransfer rh out.state (recoveryCall s.config.router r out.data)
          = some s

/-- **…AND THE SAME FOR DELIVERY.**  Pausing a destination vault `d` makes every `bridgeMint`
revert.  After any attempts during the pause, unpausing returns exactly `d`, so the mint is
exactly what it would have been without the pause. -/
def Properties.DeliveryDelayedNotLost : Prop :=
  ∀ (Accounting : Type) (hooks : Hooks Accounting) (rh : ResolutionHooks Accounting)
    (d p : State Accounting) (c : ResolutionCall) (calls : List VaultEntryCall),
    vaultPause d = some p →
      bridgeMint rh p c = none ∧ vaultUnpause (commitVaultCalls hooks rh p calls) = some d

/-- **THE PREMISES ARE JOINTLY SATISFIABLE, NONTRIVIALLY.**  B2's counter hooks and witness state
(`countOut`, `countIn`).  A `WellFormed` state with a preparation of a nonzero amount that changes
the accounting can be paused.  The recovery of its data then fails while paused, and after the
unpause it restores the state exactly.  A destination mint that succeeds on the same unpaused
state fails once it is paused. -/
def Properties.VaultPauseWitness : Prop :=
  ∃ (hooks : Hooks ℕ) (rh : ResolutionHooks ℕ) (s : State ℕ) (r : Request) (out : Result ℕ)
    (p : State ℕ) (c : ResolutionCall) (t : State ℕ),
    HooksCancel hooks rh ∧ WellFormed s ∧ prepare hooks s r = some out ∧ r.data.amount ≠ 0
      ∧ out.state.accounting ≠ s.accounting ∧ vaultPause out.state = some p
      ∧ recoverTransact rh p (recoveryCall s.config.router r out.data) = (p, false)
      ∧ bridgeRecoverFailedTransfer rh out.state (recoveryCall s.config.router r out.data)
          = some s
      ∧ bridgeMint rh s c = some t
      ∧ ∃ q, vaultPause s = some q ∧ bridgeMint rh q c = none

end Contracts.NativeTokenVaultBase
