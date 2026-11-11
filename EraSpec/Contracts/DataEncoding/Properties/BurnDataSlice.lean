import EraSpec.Contracts.DataEncoding.Specs.BurnDataSlice

/-!
# Properties: the burn data here and in the vault's codegen slice

Statements about `EraSpec.Contracts.DataEncoding.Specs.BurnDataSlice`. Proofs are in
`EraSpec.Contracts.DataEncoding.Proofs.BurnDataSlice`.

The two transcriptions of `encodeBridgeBurnData` produce the same bytes, and on 96-byte input
the slice's `abi.decode(_data, (uint256, address, address))` succeeds exactly when
`decodeBridgeBurnData` does, binding the same three values.
-/

namespace Contracts.DataEncoding

/-- **THE TWO ENCODERS AGREE.** The codegen slice's `encodeBurnData` (generic `abiEncode` of three
words) and `encodeBridgeBurnData` (type-directed heads) are the same bytes on every burn tuple. -/
def Properties.EncodeBurnDataAgreesWithSlice : Prop :=
  ∀ b : NativeTokenVaultBase.BurnData,
    Codegen.VaultPreparationSlice.encodeBurnData b = encodeBridgeBurnData b

/-- **THE TWO DECODERS AGREE ON 96 BYTES.** For data of the length both accept, the slice's
`decode "_data" [amount : uint256, receiver : address, parsedTokenAddress : address]` fails iff
`decodeBridgeBurnData` reverts; when the latter returns `b`, the slice binds `amount`, `receiver`
and `parsedTokenAddress` to `b`'s three fields (addresses as zero-extended words). (For any
other length the slice's preceding `requireLength "_data" 96` reverts, as `decodeBridgeBurnData`
does.) -/
def Properties.DecodeBurnDataAgreesWithSlice : Prop :=
  ∀ (data : List UInt8) (env : String → Codegen.Word), data.length = 96 →
    (Codegen.Calls.decodeInto data env
        [⟨"amount", .uint256⟩, ⟨"receiver", .address⟩, ⟨"parsedTokenAddress", .address⟩] = none
      ↔ decodeBridgeBurnData data = none)
    ∧ ∀ b, decodeBridgeBurnData data = some b →
      Codegen.Calls.decodeInto data env
          [⟨"amount", .uint256⟩, ⟨"receiver", .address⟩, ⟨"parsedTokenAddress", .address⟩]
        = some (Codegen.upd (Codegen.upd (Codegen.upd env "amount" b.amount) "receiver"
            (Codegen.BridgedTokenSlice.addrWord b.receiver)) "parsedTokenAddress"
            (Codegen.BridgedTokenSlice.addrWord b.tokenHint))

end Contracts.DataEncoding
