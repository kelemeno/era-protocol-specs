import EraSpec.Contracts.MessageVerification.Specs.StatusProof
import EraSpec.Contracts.ChainBatchRootTree.Specs.Layout
import EraSpec.Contracts.MessageRoot.Specs.Model

/-!
# Refinement: the status proof against the canonical chain-batch-root and `MessageRoot` models

This module adds no definitions.  `Specs/StatusProof.lean` writes the chain batch root as its own
`chainBatchRoot` over an abstract node hash with the reserved node by its documented definition,
and compares the walk with an abstract stored root `R`.  The canonical models of the two are
`../../ChainBatchRootTree/Specs/Layout.lean` (`compute`, with the reserved node as its hex
literal) and `../../MessageRoot/Specs/Model.lean` (`finalNodeAccepts` over the contract's
`chainBatchRoots`).  `Properties/Refinement.lean` states how they agree.
-/
