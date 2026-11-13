import EraSpec.Contracts.L1InteropFeeManager.Specs.Model

/-!
# Properties: the interop fee ledger balances, and who can move what

Statements about `EraSpec.Contracts.L1InteropFeeManager.Specs.Model`; proofs in
`EraSpec.Contracts.L1InteropFeeManager.Proofs.Model`.

* `LedgerBalanced` (run-level): per chain and token, deposits = withdrawals + charges +
  balance; per token, charges = sweeps + accrued; per token, received = sent out + accrued +
  the sum of all chain balances.
* `DebitAuthority`: a chain's balance goes down only by a withdrawal sent by the chain's
  admin, or by a charge sent by the chain's diamond in the fee token, and by exactly the
  amount that goes out or is accrued.
* `CreditOnlyByDeposit`: a chain's balance goes up only by a deposit of the fee token for a
  registered chain, by the deposited amount.
* `AccruedLeavesOnlyBySweep`: accrued fees go down only by a sweep, which pays the whole
  amount to `feeRecipient`.
* `FeeConfigOnlyByOwner`: `feeToken`, `feePerUnit` and `feeRecipient` change only in
  `initialize` or by the owner's setters.
* `ConfigNonzeroOnceInitialized` (run-level): from a fresh proxy, an initialized contract
  has a nonzero fee token and recipient; before initialization nothing is accrued and nothing
  is charged.
* `SweepNeverPaysZeroAddress` (run-level): from a fresh proxy, a sweep that pays out pays a
  nonzero recipient.
* `InitializeOnce` (run-level).
* `ZeroFeeChargeOpenToAnyone` (observation): while `feePerUnit * units = 0` anyone can call
  `chargeInteropFee` for any chain id; nothing changes.
* `RenouncedOwnerFreezesConfig` (observation, run-level): `renounceOwnership` is not
  disabled; after it, fee token, fee and recipient never change again.
* `UncheckedChargeDrains` (countermodel): without the caller check of `chargeInteropFee`, a
  third party moves a chain's balance to the fee recipient's side.
* `FeeFlowWitness`: initialize, set a fee, deposit, charge, sweep, withdraw.
-/

namespace Contracts.L1InteropFeeManager

/-- **THE LEDGERS BALANCE.** The fresh proxy's ledgers balance, and along any interleaving of
transactions in any environments from any state whose ledgers balance: for every chain and token,
`deposited = withdrawn + charged + chainBalance`; for every token,
`charged = swept + accruedFees`; and for every token, the amount received by deposits equals
the amount sent out by withdrawals and sweeps plus `accruedFees` plus the sum of
`chainBalance` over all chain ids. -/
def Properties.LedgerBalanced : Prop :=
  Balanced fresh ∧ ∀ (s₀ s : State), Balanced s₀ → Reach s₀ s → Balanced s

/-- **WHO CAN DEBIT A CHAIN'S BALANCE.** If one transaction lowers `chainBalance[c][t]`, it is
either `withdraw(c, t, dst, a)` sent by `getAdmin()` of the registered chain's diamond, with
`dst ≠ 0` and the balance lowered by exactly `a`; or `chargeInteropFee(c, _, u)` sent by the
registered chain's diamond with `t` the fee token, the balance lowered by exactly
`feePerUnit * u` and `accruedFees[t]` raised by the same amount. -/
def Properties.DebitAuthority : Prop :=
  ∀ (E : Env) (s s' : State) (l : Label) (c : UInt256) (t : Address),
    Step E s l s' → s'.bal c t < s.bal c t →
      (∃ dst a, l = .withdraw (E.adminOf (E.zkChain c)) c t dst a ∧ E.zkChain c ≠ 0 ∧ dst ≠ 0 ∧
          s'.bal c t + a = s.bal c t ∧ E.payOk t dst a = true) ∨
      (∃ b u, l = .charge (E.zkChain c) c b u ∧ E.zkChain c ≠ 0 ∧ t = s.feeToken ∧
          s'.bal c t + s.feePerUnit * u = s.bal c t ∧
          s'.accrued t = s.accrued t + s.feePerUnit * u)

/-- **A BALANCE GROWS ONLY BY A DEPOSIT.** If one transaction raises `chainBalance[c][t]`, it
is `deposit(c, t, a)` with `t` the fee token and `c` a registered chain, and the balance grows
by exactly `a`. -/
def Properties.CreditOnlyByDeposit : Prop :=
  ∀ (E : Env) (s s' : State) (l : Label) (c : UInt256) (t : Address),
    Step E s l s' → s.bal c t < s'.bal c t →
      ∃ caller a v, l = .deposit caller c t a v ∧ t = s.feeToken ∧ E.zkChain c ≠ 0 ∧
        s'.bal c t = s.bal c t + a

/-- **ACCRUED FEES LEAVE ONLY BY A SWEEP TO THE RECIPIENT.** If one transaction lowers
`accruedFees[t]`, it is `sweep(t)`; the entry becomes zero and the whole amount was sent to
the `feeRecipient` of the pre-state. -/
def Properties.AccruedLeavesOnlyBySweep : Prop :=
  ∀ (E : Env) (s s' : State) (l : Label) (t : Address),
    Step E s l s' → s'.accrued t < s.accrued t →
      (∃ caller, l = .sweep caller t) ∧ s'.accrued t = 0 ∧
        E.payOk t s.feeRecipient (s.accrued t) = true ∧
        s'.outflow t = s.outflow t + s.accrued t

/-- **ONLY THE OWNER CONFIGURES THE FEE.** If one transaction changes `feeToken`,
`feePerUnit` or `feeRecipient`, it is `initialize`, or `setFee` / `setFeeRecipient` sent by
the owner. -/
def Properties.FeeConfigOnlyByOwner : Prop :=
  ∀ (E : Env) (s s' : State) (l : Label), Step E s l s' →
    (s'.feeToken ≠ s.feeToken ∨ s'.feePerUnit ≠ s.feePerUnit ∨ s'.feeRecipient ≠ s.feeRecipient) →
      (∃ caller o r, l = .init caller o r) ∨ (∃ tok f, l = .setFee s.owner tok f) ∨
        (∃ r, l = .setFeeRecipient s.owner r)

/-- **CONFIGURATION IS NONZERO ONCE INITIALIZED.** In every state reachable from the fresh
proxy: if initialized, `feeToken ≠ 0`, `feeRecipient ≠ 0` and the reentrancy slot is set; if
not, there is no owner or nominee, the fee is zero and nothing is accrued in any token. -/
def Properties.ConfigNonzeroOnceInitialized : Prop :=
  ∀ s : State, Reach fresh s →
    (s.initialized = true → s.feeToken ≠ 0 ∧ s.feeRecipient ≠ 0 ∧ s.guard = true) ∧
    (s.initialized = false →
      s.owner = 0 ∧ s.pending = 0 ∧ s.feePerUnit = 0 ∧ ∀ t, s.accrued t = 0)

/-- **A SWEEP NEVER PAYS THE ZERO ADDRESS.** From the fresh proxy, along any run, a `sweep`
that sends anything out sends it to a nonzero `feeRecipient`. -/
def Properties.SweepNeverPaysZeroAddress : Prop :=
  ∀ (E : Env) (s s' : State) (caller t : Address), Reach fresh s →
    Step E s (.sweep caller t) s' → s'.outflow t ≠ s.outflow t → s.feeRecipient ≠ 0

/-- **`initialize` RUNS AT MOST ONCE.** After a successful `initialize`, along any run, no
`initialize` succeeds. -/
def Properties.InitializeOnce : Prop :=
  ∀ (E E' : Env) (s s' s'' s''' : State) (c o r c' o' r' : Address),
    Step E s (.init c o r) s' → Reach s' s'' → ¬ Step E' s'' (.init c' o' r') s'''

/-- **OBSERVATION: A ZERO-FEE CHARGE IS OPEN TO ANYONE.** `chargeInteropFee` returns at :112-114
before the caller check at :115. While `feePerUnit * units = 0`, any nonzero caller's call
for any chain id, registered or not, succeeds, and the state is unchanged. -/
def Properties.ZeroFeeChargeOpenToAnyone : Prop :=
  ∀ (E : Env) (s : State) (caller : Address) (c : UInt256) (b u : ℕ),
    caller ≠ 0 → s.feePerUnit * u = 0 →
      Step E s (.charge caller c b u) s ∧ ∀ s', Step E s (.charge caller c b u) s' → s' = s

/-- **OBSERVATION: `renounceOwnership` FREEZES THE FEE CONFIGURATION.** The contract inherits
`renounceOwnership` unchanged. In a state with no owner and no nominee that is initialized,
along any run, `feeToken`, `feePerUnit` and `feeRecipient` never change and the owner stays
zero. -/
def Properties.RenouncedOwnerFreezesConfig : Prop :=
  ∀ (s s' : State), s.initialized = true → s.owner = 0 → s.pending = 0 → Reach s s' →
    s'.owner = 0 ∧ s'.pending = 0 ∧ s'.feeToken = s.feeToken ∧ s'.feePerUnit = s.feePerUnit ∧
      s'.feeRecipient = s.feeRecipient

/-- **COUNTERMODEL: THE CALLER CHECK OF `chargeInteropFee` IS LOAD-BEARING.** With
`msg.sender == zkChain` (:115) removed, there is a state and a caller different from the
chain's diamond and from its admin whose call lowers the chain's balance, which
`DebitAuthority` excludes for the real contract. -/
def Properties.UncheckedChargeDrains : Prop :=
  ∃ (E : Env) (s s' : State) (caller : Address) (c : UInt256) (b u : ℕ),
    ChargeNoCallerCheck E s (.charge caller c b u) s' ∧ caller ≠ E.zkChain c ∧
      caller ≠ E.adminOf (E.zkChain c) ∧ s'.bal c s.feeToken < s.bal c s.feeToken ∧
      ¬ Step E s (.charge caller c b u) s'

/-- **WITNESS.** From the fresh proxy: `initialize(owner 5, recipient 6)`, the owner sets a fee
of `3` per unit in ether, `100` is deposited for chain `7`, the chain's diamond is charged for
`10` units, the fees are swept, and the chain's admin withdraws the remaining `70`. At the end
`100` came in, `100` went out, `30` was swept, and nothing is held. -/
def Properties.FeeFlowWitness : Prop :=
  ∃ s : State, Reach fresh s ∧ s.inflow ETH = 100 ∧ s.outflow ETH = 100 ∧ s.swept ETH = 30 ∧
    s.wd 7 ETH = 70 ∧ s.bal 7 ETH = 0 ∧ s.accrued ETH = 0

end Contracts.L1InteropFeeManager
