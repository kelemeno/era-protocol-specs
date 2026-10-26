import EraSpec.Contracts.BridgedStandardERC20.Specs.Model

/-!
# Registered representation-token preparation

Local specification of the non-native, non-base ERC20 branch of
`NativeTokenVaultBase.bridgeBurn` at source pin
`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`.

One already registered token is modeled. `InScope` selects this branch, not an
extra guard purported to reject all other production routes. Typed burn/mint
data stands for decoded fields; no ABI or hash correspondence is claimed.
Registry consistency and the selected token's real implementation are explicit
model assumptions. The reverse token→asset check is modeled separately from
selecting the one token whose implementation this slice represents. Explicit
hints for other tokens are outside this slice, not claimed to fail in production.

The hook runs on the pre-burn token state; its accounting implementation is an
explicit dependency. It may fail. Its interface confines writes to accounting;
arbitrary reentrancy or mutation of other contracts is not silently included.
Origin and metadata checks happen after burning. `transact` commits a successor
only on complete success, modeling atomic rollback rather than proving EVM
semantics. The vault stores no pending-obligation flag in this model or source.
-/

namespace Contracts.NativeTokenVaultBase

abbrev Address := BridgedStandardERC20.Address
abbrev Bytes := List UInt8

structure Config where
  vault : Address
  router : Address
  tokenAddress : Address
  assetId : UInt256
  baseAssetId : UInt256
  chainId : UInt256
  originChainId : UInt256

structure BurnData where
  amount : UInt256
  receiver : Address
  tokenHint : Address

structure Request where
  caller : Address
  destinationChain : UInt256
  assetId : UInt256
  depositor : Address
  l2MsgValue : UInt256
  msgValue : UInt256
  data : BurnData

/-- Fields of DataEncoding.encodeBridgeMintData, without pretending the
outer asset ID or destination chain is encoded inside this tuple. -/
structure MintData where
  originalCaller : Address
  remoteReceiver : Address
  originToken : Address
  amount : UInt256
  metadata : Bytes

structure Registry where
  tokenForAsset : UInt256 → Address
  assetForToken : Address → UInt256

structure State (Accounting : Type) where
  config : Config
  registry : Registry
  paused : Bool
  token : BridgedStandardERC20.State
  accounting : Accounting

structure Hooks (Accounting : Type) where
  /-- Return the accounting successor, or fail, using the PRE-burn snapshot. -/
  account : Accounting → BridgedStandardERC20.State → UInt256 → UInt256 → UInt256 → Option Accounting
  /-- Metadata/getter/encoding success is a visible dependency. -/
  metadata : BridgedStandardERC20.State → UInt256 → Option Bytes

structure Result (Accounting : Type) where
  state : State Accounting
  data : MintData

variable {Accounting : Type}

def selectedToken (s : State Accounting) (r : Request) : Address :=
  if r.data.tokenHint = 0 then s.registry.tokenForAsset r.assetId else r.data.tokenHint

def InScope (s : State Accounting) (r : Request) : Prop :=
  s.config.vault ≠ 0 ∧ s.config.tokenAddress ≠ 0 ∧
  s.config.assetId ≠ s.config.baseAssetId ∧ s.config.originChainId ≠ s.config.chainId ∧
  selectedToken s r = s.config.tokenAddress

def EntryAllowed (s : State Accounting) (r : Request) : Prop :=
  r.caller = s.config.router ∧ s.paused = false ∧ r.l2MsgValue = 0 ∧
  selectedToken s r ≠ 0 ∧
  s.registry.assetForToken (selectedToken s r) = r.assetId ∧ r.data.amount ≠ 0

instance (s : State Accounting) (r : Request) : Decidable (InScope s r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

instance (s : State Accounting) (r : Request) : Decidable (EntryAllowed s r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Economic accounting, independently of how identity is stored. -/
def LedgerInvariant (s : State Accounting) : Prop :=
  BridgedStandardERC20.WellFormed s.token

/-- The independently stored representations agree for the tracked token/asset.
This is a state invariant to establish and preserve, not an extra prepare guard. -/
def RepresentationConsistent (s : State Accounting) : Prop :=
  s.token.config.vault = s.config.vault ∧
  s.token.config.assetId = s.config.assetId ∧
  s.registry.tokenForAsset s.config.assetId = s.config.tokenAddress ∧
  s.registry.assetForToken s.config.tokenAddress = s.config.assetId

/-- Compatibility bundle: definitionally the same five conditions as before. -/
def WellFormed (s : State Accounting) : Prop :=
  LedgerInvariant s ∧ RepresentationConsistent s

def mintData (r : Request) (burned : BridgedStandardERC20.State) (metadata : Bytes) : MintData :=
  ⟨r.depositor, r.data.receiver, burned.config.originToken, r.data.amount, metadata⟩

/-- Source order: entry checks, accounting, zero native value, token burn,
then origin/metadata validation and returned mint data. -/
def prepare (hooks : Hooks Accounting) (s : State Accounting) (r : Request) :
    Option (Result Accounting) :=
  if InScope s r ∧ EntryAllowed s r then
    match hooks.account s.accounting s.token r.destinationChain r.assetId r.data.amount with
    | none => none
    | some accounted =>
      if r.msgValue = 0 then
        match BridgedStandardERC20.burn s.token s.config.vault r.depositor r.data.amount with
        | none => none
        | some burned =>
          if burned.config.originToken ≠ 0 ∧ s.config.originChainId ≠ 0 then
            match hooks.metadata burned s.config.originChainId with
            | none => none
            | some metadata =>
              some ⟨{ s with token := burned, accounting := accounted }, mintData r burned metadata⟩
          else none
      else none
  else none

/-- Atomic commit interface. Failure leaves the entire modeled state unchanged,
including accounting updates tentatively performed before token burning. -/
def transact (hooks : Hooks Accounting) (s : State Accounting) (r : Request) :
    State Accounting × Option MintData :=
  match prepare hooks s r with
  | none => (s, none)
  | some result => (result.state, some result.data)

end Contracts.NativeTokenVaultBase
