import EraSpec.Contracts.NativeTokenVaultBase.Specs.EscrowLedgerAtHead
import EraSpec.Core.Headline

/-!
# Properties: the escrow ledger at head, with `populateBridgedOut`

Statements about `EraSpec.Contracts.NativeTokenVaultBase.Specs.EscrowLedgerAtHead`
(`main` `70096e2` and `draft/v0.35.0` `b17415d`; the cited files are unchanged since `3605e82`
and `d9f6789`; for `draft/v0.35.0` see the spec's last section).  Proofs in
`EraSpec.Contracts.NativeTokenVaultBase.Proofs.EscrowLedgerAtHead`.

## What the pin's headlines become

* **Solvency needs a legacy premise now.**  The pin's `Solvency`/`LoggedRunSound` hold for
  runs from fresh storage.  At head a permissionless call adds an amount read from legacy
  storage to `bridgedOut`, with no comparison against the escrow.  What still holds, with no
  hash premise: if the ledger plus the legacy amounts still to be populated is backed at the
  start, it stays backed along every run (`SolvencyAtHead`), so every native inflow that
  passes `InsufficientChainBalance` on such a state asks for no more than the vault holds
  (`GuardedInflowIsBackedAtHead`).  The in-place upgrade start meets the premise
  (`UpgradeStartIsLedgerBacked`), because its `legacyBacked` field is that premise there.
  Without it, one population makes the ledger exceed the escrow, and the guard admits an
  inflow larger than the vault holds (`UnbackedLegacyBreaksSolvencyAtHead`).
* **The net-flow identity gains the populated legacy amount.**  `LoggedRunSoundAtHead`
  restates `LoggedRunSound` for logged runs from the in-place upgrade, with the id hash
  injective and nonzero on the start's recorded pairs and the run's own pairs.  For a native
  asset, `bridgedOut` plus inflow equals outflow plus the populated legacy amount, so inflow
  never exceeds outflow plus that amount.  `LoggedRunSoundAtHeadSatisfiable` meets its
  premises with a population, an outflow and an inflow larger than that outflow.
* **Each asset's legacy amount is folded in at most once** (`PopulateEffectAtHead`,
  `PopulatedFlagsPersistAtHead`).
* **The pin's runs are head runs** with nothing populated (`PinReachLogIsReachLogAtHead`).

## Enabledness

These are about the modelled checks (`FlowInGuard`, the population step), not about a
transaction succeeding.  At an in-place upgrade whose whole escrow is legacy, an inflow of
that escrow fails `InsufficientChainBalance`, and after the asset's population it passes
(`PopulateRestoresLegacyWithdrawalAtHead`).  The ledger has one entry per asset, so before
population an inflow from any chain is checked against what all chains bridged out after the
upgrade: after an outflow towards one chain and an equal inflow from another, an inflow of
that amount fails the check, and after the asset's population it passes
(`PrePopulationHeadroomIsSharedAtHead`).

## Witnesses

`EscrowLedgerAtHeadWitness` meets the premises of the hash-free results on one run, with a
population of a nonzero legacy amount and a later passing inflow.
`LoggedRunSoundAtHeadSatisfiable` meets those of `LoggedRunSoundAtHead`.  The two pin-embedding
results take a pin step or run, which the pin's own witnesses supply.  The two enabledness
results and the countermodel are about the concrete vault `upgradedVaultAtHead`; their
premises are side conditions on its parameters (nonzero chain, token and id, positive
amounts).
-/

namespace Contracts.NativeTokenVault

/-! ## The pin's runs embed -/

/-- **EVERY PIN STEP IS A HEAD STEP**, with no asset populated. -/
def Properties.PinStepOpIsStepOpAtHead : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain) (legacy : LegacyAmounts) (o : Op) (W X : World),
    StepOp e thisChain o W X →
      StepOpAtHead e thisChain legacy (.pin o) (WorldAtHead.ofWorld W) (WorldAtHead.ofWorld X)

/-- **EVERY PIN RUN IS A HEAD RUN**, logging the same operations, with no asset populated. -/
def Properties.PinReachLogIsReachLogAtHead : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain) (legacy : LegacyAmounts) (W X : World) (log : List Op),
    ReachLog e thisChain W X log →
      ReachLogAtHead e thisChain legacy (WorldAtHead.ofWorld W) (WorldAtHead.ofWorld X)
        (log.map OpAtHead.pin)

/-! ## Solvency, with no hash premise -/

/-- **EVERY STEP KEEPS THE LEDGER BACKED.**  With no hash premise and no registry
invariant. -/
def Properties.StepAtHeadPreservesLedgerBacked : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain) (legacy : LegacyAmounts) (o : OpAtHead)
    (W X : WorldAtHead),
    StepOpAtHead e thisChain legacy o W X → LedgerBackedAtHead legacy W →
      LedgerBackedAtHead legacy X

/-- **SOLVENCY AT HEAD (HEADLINE).**  Along every run from a state whose ledger, legacy
amounts included, is backed, it stays backed, so `bridgedOut` never exceeds the escrow.  No
hash premise, no registry invariant: the legacy backing is the only premise. -/
@[headline] def Properties.SolvencyAtHead : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain) (legacy : LegacyAmounts) (W₀ W : WorldAtHead)
    (log : List OpAtHead),
    LedgerBackedAtHead legacy W₀ → ReachLogAtHead e thisChain legacy W₀ W log →
      LedgerBackedAtHead legacy W ∧ ∀ a, W.world.vault.bridgedOut a ≤ W.world.vault.escrowed a

/-- **THE IN-PLACE UPGRADE IS A BACKED START.** -/
def Properties.UpgradeStartIsLedgerBacked : Prop :=
  ∀ (legacy : LegacyAmounts) (W : WorldAtHead), UpgradeStartAtHead legacy W →
    LedgerBackedAtHead legacy W

/-- **A PERMITTED PAYOUT IS COVERED, AT HEAD.**  On a backed state, an inflow of a native
asset that passes `InsufficientChainBalance` asks for no more than the vault holds. -/
def Properties.GuardedInflowIsBackedAtHead : Prop :=
  ∀ (legacy : LegacyAmounts) (thisChain : Chain) (W : WorldAtHead),
    LedgerBackedAtHead legacy W → ∀ (a : AssetId) (amt : ℕ),
      FlowInGuard thisChain W.world.vault a amt → Native thisChain W.world.vault a →
        amt ≤ W.world.vault.escrowed a

/-- **WITHOUT THE LEGACY BACKING, ONE POPULATION BREAKS SOLVENCY.**  Take the vault of an
in-place upgrade that registered the native token `t` and holds `held` of it, and legacy
amounts that give `held + 1` for its asset.  Every field of `UpgradeStartAtHead` except the
backing holds, and so does the registry invariant `Valid`.  Populating the asset is a step.
Afterwards `bridgedOut` exceeds the escrow, and an inflow of `held + 1` passes
`InsufficientChainBalance` although the vault holds only `held`.  So the model's solvency
needs `SolvencyAtHead`'s premise, which `populateBridgedOut` does not check. -/
@[countermodel] def Properties.UnbackedLegacyBreaksSolvencyAtHead : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain), thisChain ≠ 0 →
    ∀ (t : Address), t ≠ 0 → e thisChain t ≠ 0 → ∀ held : ℕ,
      let W := upgradedVaultAtHead e thisChain t held
      let legacy := legacyOfAtHead e thisChain t (held + 1)
      Valid e thisChain W.world.vault
        ∧ (∀ a, W.world.vault.bridgedOut a = 0) ∧ (∀ a, W.populated a = false)
        ∧ (∀ a, W.world.audit.totalIn a = 0 ∧ W.world.audit.totalOut a = 0)
        ∧ ¬ UpgradeStartAtHead legacy W
        ∧ ∃ X, StepOpAtHead e thisChain legacy (.populate (e thisChain t)) W X
          ∧ X.world.vault.escrowed (e thisChain t) < X.world.vault.bridgedOut (e thisChain t)
          ∧ FlowInGuard thisChain X.world.vault (e thisChain t) (held + 1)
          ∧ X.world.vault.escrowed (e thisChain t) < held + 1

/-! ## Population -/

/-- **WHAT ONE POPULATION DOES.**  On an already-populated asset nothing changes.  On an
unpopulated one, its flag is set and exactly its legacy amount is added to its `bridgedOut`.
No other asset's ledger or flag moves, and neither does any escrow or the flow audit. -/
def Properties.PopulateEffectAtHead : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain) (legacy : LegacyAmounts) (W X : WorldAtHead)
    (a : AssetId),
    StepOpAtHead e thisChain legacy (.populate a) W X →
      (W.populated a = true → X = W)
        ∧ (W.populated a = false →
            X.world.vault.bridgedOut a = W.world.vault.bridgedOut a + legacy a
              ∧ X.populated a = true)
        ∧ (∀ a', a' ≠ a →
            X.world.vault.bridgedOut a' = W.world.vault.bridgedOut a'
              ∧ X.populated a' = W.populated a')
        ∧ X.world.vault.escrowed = W.world.vault.escrowed
        ∧ X.world.audit = W.world.audit

/-- **A POPULATED ASSET STAYS POPULATED.**  Along every run, so each asset's legacy amount is
added at most once. -/
def Properties.PopulatedFlagsPersistAtHead : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain) (legacy : LegacyAmounts) (W X : WorldAtHead)
    (log : List OpAtHead),
    ReachLogAtHead e thisChain legacy W X log → ∀ a, W.populated a = true → X.populated a = true

/-! ## The flow audit, under the run-local hash premise -/

/-- **THE HEADLINE AT HEAD, RUN-LOCAL.**  Take a logged run from the vault right after the
in-place upgrade, whose registry was coherent (`Valid`) with every registered asset's
recorded pair in `S₀`.  Assume the id hash is injective and nonzero on `S₀` and the pairs the
run's own registrations hash.  At the end, the registry is coherent, the head audit holds,
the ledger (legacy included) is backed, and for every native asset the post-upgrade inflow
never exceeds the post-upgrade outflow plus the legacy amount already populated. -/
def Properties.LoggedRunSoundAtHead : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain) (legacy : LegacyAmounts), thisChain ≠ 0 →
    ∀ (S₀ : Set (Chain × Address)) (W₀ W : WorldAtHead) (log : List OpAtHead),
      UpgradeStartAtHead legacy W₀ → Valid e thisChain W₀.world.vault →
      PairsIn S₀ W₀.world.vault → ReachLogAtHead e thisChain legacy W₀ W log →
      IdAssumptionsOn e (S₀ ∪ ↑(registeredPairsAtHead thisChain log)) →
        Valid e thisChain W.world.vault ∧ AuditedAtHead legacy thisChain W
          ∧ LedgerBackedAtHead legacy W
          ∧ (∀ a, W.world.vault.bridgedOut a ≤ W.world.vault.escrowed a)
          ∧ (∀ a, Native thisChain W.world.vault a →
              W.world.audit.totalIn a ≤ W.world.audit.totalOut a + populatedLegacy legacy W a)

/-- **THE HEADLINE'S PREMISES HOLD ON A NONTRIVIAL RUN.**  An encoding, an in-place upgrade
start, a pair set and a logged run meeting every premise of `LoggedRunSoundAtHead`.  The run
populates a native asset whose legacy amount is nonzero, bridges it out after the upgrade,
and withdraws it, the withdrawal exceeding what was bridged out after the upgrade.  So the
populated legacy term of the conclusion carries weight. -/
@[witness] def Properties.LoggedRunSoundAtHeadSatisfiable : Prop :=
  ∃ (e : NtvAssetId) (thisChain : Chain) (legacy : LegacyAmounts) (S₀ : Set (Chain × Address))
    (W₀ W : WorldAtHead) (log : List OpAtHead),
    thisChain ≠ 0 ∧ UpgradeStartAtHead legacy W₀ ∧ Valid e thisChain W₀.world.vault
      ∧ PairsIn S₀ W₀.world.vault ∧ ReachLogAtHead e thisChain legacy W₀ W log
      ∧ IdAssumptionsOn e (S₀ ∪ ↑(registeredPairsAtHead thisChain log))
      ∧ ∃ a, Native thisChain W.world.vault a ∧ W.populated a = true ∧ legacy a ≠ 0
        ∧ W.world.audit.totalOut a ≠ 0
        ∧ W.world.audit.totalOut a < W.world.audit.totalIn a

/-- **THE HASH-FREE RESULTS' PREMISES HOLD ON A NONTRIVIAL RUN.**  A backed start `W₀`, a
population step of an unpopulated native asset `a` with a nonzero legacy amount (also a
one-step logged run), and a nonempty logged continuation to a state `W`, still backed, where a
native inflow of `a` passes `InsufficientChainBalance`.  So the premises of `SolvencyAtHead`,
`StepAtHeadPreservesLedgerBacked`, `PopulateEffectAtHead` (the population step),
`PopulatedFlagsPersistAtHead` (the continuation, from a state where `a` is populated) and
`GuardedInflowIsBackedAtHead` (at `W`) are met together.  The final inflow of `1` would pass
the guard with or without the population; the case where the population matters for the
guard (an inflow larger than the post-upgrade outflow) is carried by
`LoggedRunSoundAtHeadSatisfiable` and `PopulateRestoresLegacyWithdrawalAtHead`. -/
@[witness] def Properties.EscrowLedgerAtHeadWitness : Prop :=
  ∃ (e : NtvAssetId) (thisChain : Chain) (legacy : LegacyAmounts) (W₀ X W : WorldAtHead)
    (log : List OpAtHead) (a : AssetId),
    LedgerBackedAtHead legacy W₀ ∧ StepOpAtHead e thisChain legacy (.populate a) W₀ X
      ∧ ReachLogAtHead e thisChain legacy W₀ X [.populate a]
      ∧ ReachLogAtHead e thisChain legacy X W log ∧ log ≠ []
      ∧ W₀.populated a = false ∧ X.populated a = true ∧ legacy a ≠ 0
      ∧ Native thisChain W₀.world.vault a ∧ LedgerBackedAtHead legacy W
      ∧ Native thisChain W.world.vault a ∧ FlowInGuard thisChain W.world.vault a 1

/-! ## Enabledness: the modelled checks -/

/-- **POPULATION RESTORES THE LEGACY WITHDRAWALS.**  Take the vault of an in-place upgrade that
registered the native token `t` and holds `L > 0` of it, with legacy amount `L`.  It is an
upgrade start (`UpgradeStartAtHead`, so a backed one) with a coherent registry.  There an
inflow of `L` fails `InsufficientChainBalance`.  Populating the asset is a step, after which
an inflow of `L` passes the check, and once it is paid out (from any chain `c`) the vault has
nothing outstanding and holds nothing of the asset. -/
def Properties.PopulateRestoresLegacyWithdrawalAtHead : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain), thisChain ≠ 0 →
    ∀ (t : Address), t ≠ 0 → e thisChain t ≠ 0 → ∀ (L : ℕ), 0 < L → ∀ c : Chain,
      let W := upgradedVaultAtHead e thisChain t L
      let legacy := legacyOfAtHead e thisChain t L
      UpgradeStartAtHead legacy W ∧ Valid e thisChain W.world.vault
        ∧ ¬ FlowInGuard thisChain W.world.vault (e thisChain t) L
        ∧ ∃ X, StepOpAtHead e thisChain legacy (.populate (e thisChain t)) W X
          ∧ FlowInGuard thisChain X.world.vault (e thisChain t) L
          ∧ (bridgeIn thisChain X.world c (e thisChain t) L).vault.bridgedOut (e thisChain t) = 0
          ∧ (bridgeIn thisChain X.world c (e thisChain t) L).vault.escrowed (e thisChain t) = 0

/-- **BEFORE POPULATION, ONE ENTRY FOR ALL CHAINS.**  From the same upgraded vault (escrow `L`,
legacy amount `L`, unpopulated) and for any `0 < d ≤ L` and chains `cA`, `cB`: an outflow of
`d` towards `cA` is a step, then an inflow of `d` from `cB` is a step (it passes
`InsufficientChainBalance` against `cA`'s outflow).  In the state after them an inflow of `d`
fails the check, whichever chain it comes from; populating the asset is a step, after which
that inflow passes. -/
def Properties.PrePopulationHeadroomIsSharedAtHead : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain) (t : Address), t ≠ 0 → ∀ (L d : ℕ), d ≤ L → 0 < d →
      ∀ (cA cB : Chain),
      let W := upgradedVaultAtHead e thisChain t L
      let legacy := legacyOfAtHead e thisChain t L
      let a := e thisChain t
      ∃ X Y : WorldAtHead,
        StepOpAtHead e thisChain legacy (.pin (.bridgeOut cA a d)) W X
          ∧ StepOpAtHead e thisChain legacy (.pin (.bridgeIn cB a d)) X Y
          ∧ ¬ FlowInGuard thisChain Y.world.vault a d
          ∧ ∃ Z, StepOpAtHead e thisChain legacy (.populate a) Y Z
            ∧ FlowInGuard thisChain Z.world.vault a d

end Contracts.NativeTokenVault
