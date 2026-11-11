import EraSpec.Codegen.VaultPreparationSlice.Specs.Correspondence

/-!
# The bytes `bridgeBurn` takes and returns

`BridgeBurnRefines` says the program returns exactly `encodeMintData out.data`.  These
statements say what those bytes are, independently of `Codegen.Calls.abiEncode`'s
definition, so a reviewer can check them against the Solidity ABI specification without
reading the encoder: the layout of `abi.encode(address, address, address, uint256,
bytes)` and of `abi.encode(uint256, address, address)`, and that the returned bytes
determine the model's mint tuple.  Proofs: `../Proofs/MintDataBytes.lean`.
-/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.NativeTokenVaultBase (BurnData MintData)

/-- **THE RETURNED BYTES ARE THE STANDARD ABI LAYOUT** of
`(address, address, address, uint256, bytes)`: four 32-byte big-endian heads, the head of
the `bytes` argument (its offset, `160 = 5 * 32`), then its length word and its contents
right-padded with zeros to a multiple of 32. -/
def Properties.EncodeMintDataLayout : Prop :=
  ∀ m : MintData, encodeMintData m =
    word32 m.originalCaller.val ++ word32 m.remoteReceiver.val ++ word32 m.originToken.val ++
      word32 m.amount.val ++ word32 160 ++ word32 m.metadata.length ++ pad32 m.metadata

/-- **THE BURN DATA IS THREE WORDS**: `abi.encode(amount, receiver, tokenHint)` is 96 bytes,
the three values as 32-byte big-endian words. -/
def Properties.EncodeBurnDataLayout : Prop :=
  ∀ b : BurnData, encodeBurnData b =
    word32 b.amount.val ++ word32 b.receiver.val ++ word32 b.tokenHint.val

/-- **THE RETURNED BYTES DETERMINE THE MINT TUPLE.**  Two mint tuples with the same
encoding are equal, for metadata shorter than `2^256` bytes. -/
def Properties.EncodeMintDataInjective : Prop :=
  ∀ m m' : MintData, m.metadata.length < 2 ^ 256 → m'.metadata.length < 2 ^ 256 →
    encodeMintData m = encodeMintData m' → m = m'

end Codegen.VaultPreparationSlice
