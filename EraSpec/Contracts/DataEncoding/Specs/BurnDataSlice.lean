import EraSpec.Contracts.DataEncoding.Specs.TxDataHash
import EraSpec.Codegen.VaultPreparationSlice.Specs.Correspondence

/-!
# Spec: the burn data here and in the vault's codegen slice

This topic adds no definitions. It compares two independently written transcriptions of the
same two library functions (`common/libraries/DataEncoding.sol:35-60`):

* here (`Specs/TxDataHash.lean`): `encodeBridgeBurnData`, built from the type-directed ABI heads
  `encWord` / `encAddr`, and `decodeBridgeBurnData`, the length check plus the address range
  checks of `abi.decode`;
* in the vault's codegen slice (backlog item O4, `Codegen/VaultPreparationSlice`):
  `encodeBurnData`, built from the generic `Codegen.Calls.abiEncode` with `addrWord`, and the
  program's `requireLength "_data" 96` followed by `decode "_data" [uint256, address, address]`,
  interpreted by `Codegen.Calls.decodeInto` with its `fits` range checks.

Statements are in `EraSpec.Contracts.DataEncoding.Properties.BurnDataSlice`, proofs in
`EraSpec.Contracts.DataEncoding.Proofs.BurnDataSlice`. Agreement of two transcriptions is
evidence about both, not a proof about solc's output (`SOL-ABI`).
-/
