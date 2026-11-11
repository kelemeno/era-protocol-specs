import EraSpec.Core.Word

/-!
# BridgedStandardERC20: initialized representation-token ledger

Locally authored behavioral specification, reviewed against era-contracts
`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`, `bridge/BridgedStandardERC20.sol`
and inherited OpenZeppelin v4 `ERC20Upgradeable` mint/burn/transfer logic.

Scope: the nonzero configured-vault branch of `onlyNTV`, empty inherited hooks,
and token-ledger effects. This is not a compiled-code proof. Legacy zero-vault
fallback, initialization/reinitialization, allowances/permit, events, metadata,
and upgrades are not transitions in this first slice.

Amounts are UInt256 inputs. Ledger values use naturals with an explicit supply
bound and sum-of-balances invariant; these justify the source's unchecked
subtractions/additions without silently assuming modular arithmetic conserves
value. A failed operation returns `none`, with no successor state committed.
-/

namespace Contracts.BridgedStandardERC20

abbrev Address := Fin (2 ^ 160)

structure Config where
  vault : Address
  originToken : Address
  assetId : UInt256
deriving DecidableEq

structure State where
  config : Config
  balances : Address → ℕ
  totalSupply : ℕ

def empty (config : Config) : State := ⟨config, fun _ => 0, 0⟩

/-- The whole ledger, not merely the balance of the account being burned. -/
def WellFormed (s : State) : Prop :=
  (∑ a : Address, s.balances a) = s.totalSupply ∧
  s.totalSupply < UInt256.size ∧ s.balances 0 = 0

def BurnAllowed (s : State) (caller owner : Address) (amount : UInt256) : Prop :=
  s.config.vault ≠ 0 ∧ caller = s.config.vault ∧ owner ≠ 0 ∧
  amount.val ≤ s.balances owner

def MintAllowed (s : State) (caller recipient : Address) (amount : UInt256) : Prop :=
  s.config.vault ≠ 0 ∧ caller = s.config.vault ∧ recipient ≠ 0 ∧
  s.totalSupply + amount.val < UInt256.size

def TransferAllowed (s : State) (owner recipient : Address) (amount : UInt256) : Prop :=
  owner ≠ 0 ∧ recipient ≠ 0 ∧ amount.val ≤ s.balances owner

instance (s : State) (caller owner : Address) (amount : UInt256) :
    Decidable (BurnAllowed s caller owner amount) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

instance (s : State) (caller recipient : Address) (amount : UInt256) :
    Decidable (MintAllowed s caller recipient amount) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

instance (s : State) (owner recipient : Address) (amount : UInt256) :
    Decidable (TransferAllowed s owner recipient amount) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def burnEffect (s : State) (owner : Address) (amount : UInt256) : State :=
  { s with balances := Function.update s.balances owner (s.balances owner - amount.val)
           totalSupply := s.totalSupply - amount.val }

def mintEffect (s : State) (recipient : Address) (amount : UInt256) : State :=
  { s with balances := Function.update s.balances recipient (s.balances recipient + amount.val)
           totalSupply := s.totalSupply + amount.val }

/-- Debit first, then read the recipient balance: self-transfer is handled exactly. -/
def transferEffect (s : State) (owner recipient : Address) (amount : UInt256) : State :=
  let debited := Function.update s.balances owner (s.balances owner - amount.val)
  { s with balances := Function.update debited recipient (debited recipient + amount.val) }

def burn (s : State) (caller owner : Address) (amount : UInt256) : Option State :=
  if BurnAllowed s caller owner amount then some (burnEffect s owner amount) else none

def mint (s : State) (caller recipient : Address) (amount : UInt256) : Option State :=
  if MintAllowed s caller recipient amount then some (mintEffect s recipient amount) else none

def transfer (s : State) (owner recipient : Address) (amount : UInt256) : Option State :=
  if TransferAllowed s owner recipient amount then some (transferEffect s owner recipient amount) else none

inductive Step : State → State → Prop
  | burn {s t caller owner amount} : burn s caller owner amount = some t → Step s t
  | mint {s t caller recipient amount} : mint s caller recipient amount = some t → Step s t
  | transfer {s t owner recipient amount} : transfer s owner recipient amount = some t → Step s t

inductive Reach : State → State → Prop
  | refl {s} : Reach s s
  | tail {s t u} : Reach s t → Step t u → Reach s u

end Contracts.BridgedStandardERC20
