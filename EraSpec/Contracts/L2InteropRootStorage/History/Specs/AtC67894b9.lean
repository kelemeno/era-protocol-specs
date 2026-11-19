import EraSpec.Contracts.L2InteropRootStorage.Specs.Storage
import EraSpec.Protocol.InteropAtomicity.Specs.RootImport

/-!
# History: `L2InteropRootStorage` at the interop pin `c67894b9`

**This is a record of an older commit, not a claim about `b17415d20`.** The canonical model is
`../../Specs/Storage.lean` (`b17415d20`). This file keeps the transcription of the contract at
`c67894b9`, where it has no `latestInteropRootTimestamp`, and the reading of
`Contracts.RootImport`'s imports (`Protocol/InteropAtomicity/Specs/RootImport.lean`, written at
`c67894b9`) off that version's storage. The `c67894b9` source was not available when this file was
moved here; its line numbers are as first written.

**This file is definitions only.** Statements: `../Properties/AtC67894b9.lean`.
-/

namespace Contracts.InteropRootStorage.History

/-! ## The contract at `c67894b9`

`interop/L2InteropRootStorage.sol` at `c67894b970a0dac6fe9144d8ebf4b0806e15a9af` (107 lines): the
storage is `storedInteropRoots` alone (`:40`); the modifier is `:20-25`, `addSingleInteropRoot`
`:58-60`, `addInteropRootsInBatch` `:64-76`, and `_addInteropRoot` (`:78-106`) has the same four
checks in the same order (`:85-87`, `:88-90`, `:93-95`, `:98-100`) and the same write (`:103`),
with no `latestInteropRootTimestamp` update.  Apart from comments and the `Unauthorized` import,
that is the only difference from the code above. -/

/-- The storage at `c67894b9`: `storedInteropRoots` (`:40` there). -/
abbrev RootsAtC67 := UInt256 → UInt256 → StoredInteropRoot

/-- `_addInteropRoot` at `c67894b9` (`:78-106` there); `none` is a revert. -/
def addInteropRootAtC67 (R : RootsAtC67) (chainId blockOrBatchNumber timestamp : UInt256)
    (sides : List UInt256) : Option RootsAtC67 :=
  if sides.length ≠ 1 then none                                                     -- :85 SidesLengthNotOne
  else if sides.headD 0 = 0 then none                                               -- :88 MessageRootIsZero
  else if timestamp = 0 then none                                                   -- :93 InteropRootTimestampIsZero
  else if (R chainId blockOrBatchNumber).root ≠ 0 then none                         -- :98 InteropRootAlreadyExists
  else some (fun c b =>                                                             -- :103
    if c = chainId ∧ b = blockOrBatchNumber then ⟨sides.headD 0, timestamp⟩ else R c b)

/-- The loop of `addInteropRootsInBatch` at `c67894b9` (`:67-74` there), all or nothing; a single
import is the one-element case. -/
def addRootsAtC67 (R : RootsAtC67) : List InteropRoot → Option RootsAtC67
  | [] => some R
  | r :: rs =>
    match addInteropRootAtC67 R r.chainId r.blockOrBatchNumber r.timestamp r.sides with
    | none => none
    | some R' => addRootsAtC67 R' rs

/-- Either writer at `c67894b9`, called by `caller`: the modifier (`:20-25`), then
`_addInteropRoot` on the call's roots in order. -/
def execAtC67 (R : RootsAtC67) (caller : Address) (c : Call) : Option RootsAtC67 :=
  if caller ≠ L2_BOOTLOADER_ADDRESS then none else addRootsAtC67 R c.roots

/-- Any finite sequence of successful calls of the `c67894b9` contract. -/
inductive ReachAtC67 : RootsAtC67 → RootsAtC67 → Prop
  | refl {R : RootsAtC67} : ReachAtC67 R R
  | tail {R T U : RootsAtC67} (caller : Address) (c : Call) :
      ReachAtC67 R T → execAtC67 T caller c = some U → ReachAtC67 R U

/-! ## `Contracts.RootImport`'s imports read off the `c67894b9` storage

`World` numbers blocks in `ℕ`; the storage key read for block `k` is `Nat.toUInt256 k`, so blocks
that agree modulo `2^256` read the same slot. -/

/-- The destination side of `Contracts.RootImport` whose imports are read off each destination's
`c67894b9` storage: `imported d sl k` holds when `R d` holds a nonzero root at
`(sl, Nat.toUInt256 k)`.  The settlement-layer roots and `L1_CHAIN_ID`s are given. -/
def importWorldAtC67 (slRoot : Contracts.Atomicity.Chain → ℕ → Contracts.Timeout.SlRoot)
    (l1 : Contracts.RootImport.Dest → Contracts.Atomicity.Chain)
    (R : Contracts.RootImport.Dest → RootsAtC67) : Contracts.RootImport.World where
  slRoot := slRoot
  imported := fun d sl k => (R d sl (Nat.toUInt256 k)).root ≠ 0
  l1 := l1

end Contracts.InteropRootStorage.History
