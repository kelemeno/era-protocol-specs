import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: `L1InteropFeeManager`, every state-changing entry point

Source: era-contracts `draft/v0.35.0`, commit `d9f678900e1bc8286412b78f56d4a9f443983c29`,
`l1-contracts/contracts/core/interop-fee/L1InteropFeeManager.sol` (162 lines), with
OpenZeppelin v4 `Ownable2StepUpgradeable`, `Initializable` and `common/ReentrancyGuard.sol`
(`reentrancyGuardInitializer` :43-63, `nonReentrant` :72-98).

**This file is definitions only.** Statements are in
`EraSpec.Contracts.L1InteropFeeManager.Properties.Model`, proofs in
`EraSpec.Contracts.L1InteropFeeManager.Proofs.Model`.

## The source (guards in order)

    function initialize(address _owner, address _feeRecipient) external reentrancyGuardInitializer initializer {
        require(_owner != address(0), ZeroAddress());                                   // :61
        require(_feeRecipient != address(0), ZeroAddress());                            // :62
        _transferOwnership(_owner); _setFee(ETH_TOKEN_ADDRESS, 0);                      // :63-64
        feeRecipient = _feeRecipient; ... }                                             // :65
    function setFee(address _feeToken, uint256 _feePerUnit) external onlyOwner {        // :70-72
        _setFee(_feeToken, _feePerUnit); }       // require(_feeToken != address(0))      :138
    function setFeeRecipient(address _feeRecipient) external onlyOwner {
        require(_feeRecipient != address(0), ZeroAddress()); feeRecipient = ...; }      // :75-80
    function deposit(uint256 _chainId, address _token, uint256 _amount) external payable nonReentrant {
        require(_token == feeToken, TokenNotSupported(_token));                         // :84
        require(_amount != 0, AmountMustBeGreaterThanZero());                           // :85
        uint256 expectedMsgValue = _token == ETH_TOKEN_ADDRESS ? _amount : 0;           // :86
        require(msg.value == expectedMsgValue, ...);                                    // :87
        _getZKChain(_chainId);                    // BRIDGE_HUB.getZKChain != 0           :89
        chainBalance[_chainId][_token] += _amount;                                      // :90
        if (_token != ETH_TOKEN_ADDRESS) IERC20(_token).safeTransferFrom(msg.sender, address(this), _amount); } // :92-94
    function withdraw(uint256 _chainId, address _token, address _to, uint256 _amount) external nonReentrant {
        require(msg.sender == IGetters(_getZKChain(_chainId)).getAdmin(), Unauthorized(msg.sender)); // :99
        require(_to != address(0), ZeroAddress());                                      // :100
        require(_amount != 0, AmountMustBeGreaterThanZero());                           // :101
        uint256 balance = chainBalance[_chainId][_token];
        require(_amount <= balance, InsufficientInteropFeeBalance(...));                // :102-103
        chainBalance[_chainId][_token] = balance - _amount;                             // :104
        _transferOut(_token, _to, _amount); }                                           // :106
    function chargeInteropFee(uint256 _chainId, uint256 _batchNumber, uint256 _units) external {
        uint256 fee = feePerUnit * _units;                                              // :111
        if (fee == 0) { return; }                                                       // :112-114
        require(msg.sender == _getZKChain(_chainId), Unauthorized(msg.sender));         // :115
        address token = feeToken; uint256 balance = chainBalance[_chainId][token];      // :116-117
        require(fee <= balance, InsufficientInteropFeeBalance(...));                    // :118
        chainBalance[_chainId][token] = balance - fee;                                  // :119
        accruedFees[token] += fee; ... }                                                // :120
    function sweep(address _token) external nonReentrant {
        uint256 amount = accruedFees[_token];
        if (amount == 0) { return; }                                                    // :126-129
        accruedFees[_token] = 0;                                                        // :130
        address recipient = feeRecipient; ...
        _transferOut(_token, recipient, amount); }                                      // :131-133

`ETH_TOKEN_ADDRESS = address(1)` (`common/Config.sol:203`).

## Modelling choices

* **Amounts are natural numbers below `MAX = 2^256`.** Solidity 0.8 checked arithmetic reverts
  on overflow; the model has the matching guard on `feePerUnit * _units` (:111), on
  `chainBalance += _amount` (:90) and on `accruedFees += fee` (:120). `MAX` is never unfolded.
* **The environment of one transaction** (`Env`) answers the calls into other contracts:
  `BRIDGE_HUB.getZKChain`, the diamond's `getAdmin()` (a reverting `getAdmin` is the answer `0`,
  which no caller equals), whether the ERC20 pull succeeds, and whether `_transferOut` succeeds.
  A failing call reverts the transaction, which is the absence of a step. Each transaction may
  run in a different environment.
* **Token movements are counted, not modelled.** `inflow t` adds `_amount` for each successful
  deposit of `t` (the `msg.value` received, or the amount passed to `safeTransferFrom`);
  `outflow t` adds each amount passed to a successful `_transferOut`. Whether the token
  contract moved exactly that amount (fee-on-transfer, rebasing) is outside the model.
* **Reentrancy.** `deposit`, `withdraw` and `sweep` are `nonReentrant`; `chargeInteropFee`,
  the setters and the ownership functions are not. In every function the external transfer is
  the last action, after all storage writes, so a call made from inside the transfer sees the
  final storage and is the same as a later transaction. The model has no nested calls.
* **Ghost counters** (not contract storage): per chain and token `dep`, `wd`, `chg` (amounts
  deposited, withdrawn, charged); per token `inflow`, `outflow`, `charged`, `swept`.
* **`guard`** is the reentrancy slot being nonzero; `nonReentrant` reverts while it is zero
  (`ReentrancyGuard.sol:78-80`). `initialized` is `Initializable._initialized ≠ 0`.
* `msg.sender` is never the zero address.
* **Not modelled:** events; proxy implementation swaps; the `Executor` facet that calls
  `chargeInteropFee` (`state-transition/chain-deps/facets/Executor.sol:108`).
-/

namespace Contracts.L1InteropFeeManager

open Clear

/-- Addresses as 256-bit words; `0` is the zero address. -/
abbrev Address := UInt256

/-- `2^256`, kept opaque to arithmetic: results only use that amounts stay below it. -/
def MAX : ℕ := UInt256.size

/-- `ETH_TOKEN_ADDRESS` (`common/Config.sol:203`). -/
def ETH : Address := 1

/-- What other contracts answer during one transaction. -/
structure Env where
  /-- `BRIDGE_HUB.getZKChain(chainId)`; `0` for an unregistered chain. -/
  zkChain : UInt256 → Address
  /-- `IGetters(diamond).getAdmin()`; `0` when the call reverts. -/
  adminOf : Address → Address
  /-- `IERC20(token).safeTransferFrom(from, this, amount)` succeeds. -/
  pullOk : Address → Address → ℕ → Bool
  /-- `_transferOut(token, to, amount)` succeeds (:153-161). -/
  payOk : Address → Address → ℕ → Bool

/-- Storage plus ghost counters. -/
structure State where
  /-- `Initializable._initialized ≠ 0`. -/
  initialized : Bool
  /-- The reentrancy slot is nonzero. -/
  guard : Bool
  owner : Address
  pending : Address
  /-- `feeToken` (:36). -/
  feeToken : Address
  /-- `feePerUnit` (:39). -/
  feePerUnit : ℕ
  /-- `feeRecipient` (:42). -/
  feeRecipient : Address
  /-- `accruedFees[token]` (:45). -/
  accrued : Address → ℕ
  /-- `chainBalance[chainId][token]` (:48). -/
  bal : UInt256 → Address → ℕ
  /-- Ghost: total deposited for a chain in a token. -/
  dep : UInt256 → Address → ℕ
  /-- Ghost: total withdrawn from a chain's balance in a token. -/
  wd : UInt256 → Address → ℕ
  /-- Ghost: total charged from a chain's balance in a token. -/
  chg : UInt256 → Address → ℕ
  /-- Ghost: total amount of a token received by deposits. -/
  inflow : Address → ℕ
  /-- Ghost: total amount of a token sent out by `_transferOut`. -/
  outflow : Address → ℕ
  /-- Ghost: total fees charged in a token. -/
  charged : Address → ℕ
  /-- Ghost: total fees swept in a token. -/
  swept : Address → ℕ

/-- Transactions. -/
inductive Label where
  | init (caller owner recipient : Address)
  | setFee (caller token : Address) (feePerUnit : ℕ)
  | setFeeRecipient (caller recipient : Address)
  | deposit (caller : Address) (chain : UInt256) (token : Address) (amount value : ℕ)
  | withdraw (caller : Address) (chain : UInt256) (token dst : Address) (amount : ℕ)
  | charge (caller : Address) (chain : UInt256) (batch units : ℕ)
  | sweep (caller token : Address)
  | transferOwnership (caller newOwner : Address)
  | acceptOwnership (caller : Address)
  | renounceOwnership (caller : Address)

/-- Write one entry of a two-key table. -/
def setBal (b : UInt256 → Address → ℕ) (c : UInt256) (t : Address) (v : ℕ) :
    UInt256 → Address → ℕ :=
  fun c' t' => if c' = c ∧ t' = t then v else b c' t'

/-- Add to one entry of a one-key table. -/
def bump (f : Address → ℕ) (t : Address) (a : ℕ) : Address → ℕ :=
  fun t' => if t' = t then f t' + a else f t'

/-- Zero one entry of a one-key table. -/
def clear (f : Address → ℕ) (t : Address) : Address → ℕ :=
  fun t' => if t' = t then 0 else f t'

/-- The sum of a token's prepaid balances over all chain ids. -/
def total (b : UInt256 → Address → ℕ) (t : Address) : ℕ :=
  Finset.univ.sum fun c => b c t

/-- One successful transaction in environment `E`. -/
inductive Step (E : Env) : State → Label → State → Prop where
  /-- `initialize` (:60-67). -/
  | init {s : State} {caller o r : Address} :
      caller ≠ 0 → s.guard = false → s.initialized = false → o ≠ 0 → r ≠ 0 →
      Step E s (.init caller o r)
        { s with initialized := true, guard := true, owner := o, pending := 0,
                 feeToken := ETH, feePerUnit := 0, feeRecipient := r }
  /-- `setFee` (:70-72, :137-144). -/
  | setFee {s : State} {caller tok : Address} {f : ℕ} :
      caller ≠ 0 → caller = s.owner → tok ≠ 0 → f < MAX →
      Step E s (.setFee caller tok f) { s with feeToken := tok, feePerUnit := f }
  /-- `setFeeRecipient` (:75-80). -/
  | setFeeRecipient {s : State} {caller r : Address} :
      caller ≠ 0 → caller = s.owner → r ≠ 0 →
      Step E s (.setFeeRecipient caller r) { s with feeRecipient := r }
  /-- `deposit` (:83-95). -/
  | deposit {s : State} {caller : Address} {c : UInt256} {tok : Address} {a v : ℕ} :
      caller ≠ 0 → s.guard = true →
      tok = s.feeToken →                                         -- :84
      a ≠ 0 → a < MAX →                                          -- :85
      v = (if tok = ETH then a else 0) →                         -- :86-87
      E.zkChain c ≠ 0 →                                          -- :89
      s.bal c tok + a < MAX →                                    -- :90, checked
      (tok ≠ ETH → E.pullOk tok caller a = true) →               -- :92-94
      Step E s (.deposit caller c tok a v)
        { s with bal := setBal s.bal c tok (s.bal c tok + a),
                 dep := setBal s.dep c tok (s.dep c tok + a),
                 inflow := bump s.inflow tok a }
  /-- `withdraw` (:98-107). -/
  | withdraw {s : State} {caller : Address} {c : UInt256} {tok dst : Address} {a : ℕ} :
      caller ≠ 0 → s.guard = true →
      E.zkChain c ≠ 0 → caller = E.adminOf (E.zkChain c) →       -- :99
      dst ≠ 0 →                                                   -- :100
      a ≠ 0 →                                                    -- :101
      a ≤ s.bal c tok →                                          -- :102-103
      E.payOk tok dst a = true →                                  -- :106
      Step E s (.withdraw caller c tok dst a)
        { s with bal := setBal s.bal c tok (s.bal c tok - a),
                 wd := setBal s.wd c tok (s.wd c tok + a),
                 outflow := bump s.outflow tok a }
  /-- `chargeInteropFee` with `feePerUnit * _units == 0` (:111-114): returns before the caller
  check; nothing changes. -/
  | chargeZero {s : State} {caller : Address} {c : UInt256} {b u : ℕ} :
      caller ≠ 0 → s.feePerUnit * u = 0 →
      Step E s (.charge caller c b u) s
  /-- `chargeInteropFee` with a nonzero fee (:111-122). -/
  | charge {s : State} {caller : Address} {c : UInt256} {b u : ℕ} :
      caller ≠ 0 →
      s.feePerUnit * u < MAX →                                   -- :111, checked
      s.feePerUnit * u ≠ 0 →                                     -- :112
      E.zkChain c ≠ 0 → caller = E.zkChain c →                   -- :115
      s.feePerUnit * u ≤ s.bal c s.feeToken →                    -- :118
      s.accrued s.feeToken + s.feePerUnit * u < MAX →            -- :120, checked
      Step E s (.charge caller c b u)
        { s with bal := setBal s.bal c s.feeToken (s.bal c s.feeToken - s.feePerUnit * u),
                 accrued := bump s.accrued s.feeToken (s.feePerUnit * u),
                 chg := setBal s.chg c s.feeToken (s.chg c s.feeToken + s.feePerUnit * u),
                 charged := bump s.charged s.feeToken (s.feePerUnit * u) }
  /-- `sweep` with nothing accrued (:126-129): nothing changes. -/
  | sweepZero {s : State} {caller tok : Address} :
      caller ≠ 0 → s.guard = true → s.accrued tok = 0 →
      Step E s (.sweep caller tok) s
  /-- `sweep` (:125-134): everything accrued in the token goes to `feeRecipient`. -/
  | sweep {s : State} {caller tok : Address} :
      caller ≠ 0 → s.guard = true → s.accrued tok ≠ 0 →
      E.payOk tok s.feeRecipient (s.accrued tok) = true →        -- :133
      Step E s (.sweep caller tok)
        { s with accrued := clear s.accrued tok,
                 swept := bump s.swept tok (s.accrued tok),
                 outflow := bump s.outflow tok (s.accrued tok) }
  /-- `Ownable2Step.transferOwnership`, `onlyOwner`. -/
  | transferOwnership {s : State} {caller a : Address} :
      caller ≠ 0 → caller = s.owner →
      Step E s (.transferOwnership caller a) { s with pending := a }
  /-- `Ownable2Step.acceptOwnership`. -/
  | acceptOwnership {s : State} {caller : Address} :
      caller ≠ 0 → s.pending = caller →
      Step E s (.acceptOwnership caller) { s with owner := caller, pending := 0 }
  /-- `Ownable.renounceOwnership`, `onlyOwner` (not overridden by the contract). -/
  | renounceOwnership {s : State} {caller : Address} :
      caller ≠ 0 → caller = s.owner →
      Step E s (.renounceOwnership caller) { s with owner := 0, pending := 0 }

/-- Reachability: any interleaving of transactions, each in any environment. -/
inductive Reach (s₀ : State) : State → Prop where
  | refl : Reach s₀ s₀
  | step {E : Env} {s s' : State} {l : Label} : Reach s₀ s → Step E s l s' → Reach s₀ s'

/-- The proxy's storage before `initialize`, ghost counters at zero. -/
def fresh : State :=
  { initialized := false, guard := false, owner := 0, pending := 0, feeToken := 0,
    feePerUnit := 0, feeRecipient := 0, accrued := fun _ => 0, bal := fun _ _ => 0,
    dep := fun _ _ => 0, wd := fun _ _ => 0, chg := fun _ _ => 0, inflow := fun _ => 0,
    outflow := fun _ => 0, charged := fun _ => 0, swept := fun _ => 0 }

/-- The ledgers of a state balance: per chain and token, deposits equal withdrawals plus
charges plus the remaining balance; per token, charges equal sweeps plus accrued fees, and
the amount received equals the amount sent out plus accrued fees plus all chain balances. -/
structure Balanced (s : State) : Prop where
  chain : ∀ c t, s.dep c t = s.wd c t + s.chg c t + s.bal c t
  fees : ∀ t, s.charged t = s.swept t + s.accrued t
  held : ∀ t, s.inflow t = s.outflow t + s.accrued t + total s.bal t

/-! ## Countermodel: `chargeInteropFee` without the caller check -/

/-- `chargeInteropFee` with `require(msg.sender == _getZKChain(_chainId))` (:115) replaced by
the registration check alone. -/
inductive ChargeNoCallerCheck (E : Env) : State → Label → State → Prop where
  | charge {s : State} {caller : Address} {c : UInt256} {b u : ℕ} :
      caller ≠ 0 → s.feePerUnit * u < MAX → s.feePerUnit * u ≠ 0 →
      E.zkChain c ≠ 0 →
      s.feePerUnit * u ≤ s.bal c s.feeToken →
      s.accrued s.feeToken + s.feePerUnit * u < MAX →
      ChargeNoCallerCheck E s (.charge caller c b u)
        { s with bal := setBal s.bal c s.feeToken (s.bal c s.feeToken - s.feePerUnit * u),
                 accrued := bump s.accrued s.feeToken (s.feePerUnit * u),
                 chg := setBal s.chg c s.feeToken (s.chg c s.feeToken + s.feePerUnit * u),
                 charged := bump s.charged s.feeToken (s.feePerUnit * u) }

end Contracts.L1InteropFeeManager
