import EraSpec.Contracts.DataAvailability.Specs.RollupL1DAValidator

/-!
# Spec: `ValidiumL1DAValidator` and `RelayedSLDAValidator`

Source: era-contracts `d9f678900e1bc8286412b78f56d4a9f443983c29`, under
`l1-contracts/contracts/state-transition/data-availability/`:

* `ValidiumL1DAValidator.sol` (29 lines). `checkDA` is `pure`; it ignores the chain id, the batch
  number and the L2 output hash, requires a 32-byte input and returns it as the state diff hash with
  all-zero blob arrays.
* `RelayedSLDAValidator.sol` (111 lines), the DA validator of chains settling on a gateway. `checkDA`
  first requires `msg.sender` to be the chain's diamond as the L2 bridgehub reports it (`:27-33`),
  parses the operator input like the rollup validator (`CalldataDA`), supports only the calldata
  source, processes it with `CalldataDAGateway._processCalldataDA`, relays the pubdata to L1 through
  the L2-to-L1 messenger (`:39-45`), and runs the pair sanity loop (`:102-109`).

## Model boundaries

* `IL2Bridgehub(L2_BRIDGEHUB_ADDR).getZKChain` is an arbitrary function `UInt256 → Address`
  (`GatewayEnv.getZKChain`); the call is assumed not to revert.
* `L2_TO_L1_MESSENGER_SYSTEM_CONTRACT.sendToL1` is assumed to succeed; its effect is recorded as the
  returned `RelayMessage`, the four ABI fields of `abi.encode(RELAYED_SL_DA_VALIDATOR_VERSION,
  _chainId, _batchNumber, _pubdata)` (`:42-44`). The ABI encoding itself is not modelled. Because the
  sanity loop runs after the relay, a revert there also undoes the message (`VM-REVERT`).
-/

namespace Contracts.DataAvailability

/-- **`ValidiumL1DAValidator.checkDA`** (`ValidiumL1DAValidator.sol:9-28`). The chain id, batch
number and `_l2DAValidatorOutputHash` are accepted and ignored. -/
def validiumCheckDA (_chainId _batchNumber _h : UInt256) (input : Bytes) (max : ℕ) :
    Option Output :=
  -- `:18-20`
  if input.length ≠ 32 then none
  -- `:21-27`
  else some { stateDiffHash := b32At input 0, blobsLinearHashes := List.replicate max 0,
              blobsOpeningCommitments := List.replicate max 0 }

/-- What the gateway validator reads from its environment. -/
structure GatewayEnv where
  /-- `IL2Bridgehub(L2_BRIDGEHUB_ADDR).getZKChain(chainId)` (`RelayedSLDAValidator.sol:30`). -/
  getZKChain : UInt256 → Address

/-- The message relayed to L1: the fields of
`abi.encode(RELAYED_SL_DA_VALIDATOR_VERSION, _chainId, _batchNumber, _pubdata)` (`:42-44`). -/
structure RelayMessage where
  version : ℕ
  chainId : UInt256
  batchNumber : UInt256
  pubdata : Bytes
deriving DecidableEq

/-- `RELAYED_SL_DA_VALIDATOR_VERSION = 0` (`RelayedSLDAValidator.sol:18`). -/
def RELAYED_SL_DA_VALIDATOR_VERSION : ℕ := 0

/-- The sanity predicate of `RelayedSLDAValidator.sol:103-106`, as written there (a different
Boolean expression from the rollup validator's; `Properties.SanityChecksAgree` shows they agree). -/
def relayedPairMismatch (lin com : UInt256) : Bool :=
  (lin != 0 || com != 0) && (lin == 0 || com == 0)

/-- **`RelayedSLDAValidator.checkDA`** (`:48-110`). Returns the output and the relayed message.
`checkSender = false` deletes `_ensureOnlyChainSender` (`:57`); it exists only for the countermodel
`Properties.RelayedSenderCheckLoadBearing`. The source is `relayedCheckDA`. -/
def relayedCheckDAWith (checkSender : Bool) (K : Crypto) (G : GatewayEnv) (caller : Address)
    (chainId batchNumber h : UInt256) (input : Bytes) (max : ℕ) : Option (Output × RelayMessage) :=
  -- `:57`, `:27-33`
  if checkSender = true ∧ G.getZKChain chainId ≠ caller then none
  -- `:66-72`
  else match processL2 K.keccak h max input with
  | none => none
  | some p =>
    -- `:78`: `l1DaInput[0]` panics on an empty slice
    match p.l1DaInput with
    | [] => none
    | src :: rest =>
      -- `:81`, `PubdataSource.Calldata = 0`; otherwise `:95-97`
      if src.toNat ≠ 0 then none
      else match processCalldataDAGateway K.keccak p.blobsProvided p.fullPubdataHash max rest with
      | none => none
      | some (cs, pub) =>
        -- `:102-109`
        if (List.range max).any (fun i =>
            relayedPairMismatch (p.blobsLinearHashes.getD i 0) (cs.getD i 0)) then none
        else some
          ({ stateDiffHash := p.stateDiffHash, blobsLinearHashes := p.blobsLinearHashes,
             blobsOpeningCommitments := cs },
           -- `:92`, `:39-45`
           { version := RELAYED_SL_DA_VALIDATOR_VERSION, chainId := chainId,
             batchNumber := batchNumber, pubdata := pub })

/-- The source's `RelayedSLDAValidator.checkDA`. -/
def relayedCheckDA (K : Crypto) (G : GatewayEnv) (caller : Address) (chainId batchNumber h : UInt256)
    (input : Bytes) (max : ℕ) : Option (Output × RelayMessage) :=
  relayedCheckDAWith true K G caller chainId batchNumber h input max

end Contracts.DataAvailability
