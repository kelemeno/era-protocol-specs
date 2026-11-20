# MultichainGate

The multi-chain model of the refund gate's source-chain check (`authorizeRefund`): the abstract
gate over every chain's commitment-tree leaf set ([Model](Properties/Model.lean)), and the deployed
gate over `FullMerkle` paths with its padding constant ([DeployedGate](Properties/DeployedGate.lean)).
The protocol-level overview is in the [Protocol README](../README.md).

## Pin

Both topics cite era-contracts `c67894b9`, the round-5 interop pin, and are kept as the record of
that pin. `Model` is the abstract gate as `c67894b9`'s `authorizeRefund` ran it; `DeployedGate`
records the `c67894b9` padding behaviour (fixed upstream before `b17415d20`; see the Specs header).
`b17415d20` has a different `AtomicFlowManager`, and neither topic has been re-modelled against it.
The commitment-tree models they import (`IndexedMerkleTree`, `L2InteropCommitmentTree`) are the
consolidated ones. These results build on `c67894b9` records and are not claims about `b17415d20`.

## Headline guarantees

None. Nothing in this area is a `@[headline]`, because the area models `c67894b9`, not
`b17415d20`. Its statements stay untagged supporting results until the area is re-modelled at
`b17415d20`.
