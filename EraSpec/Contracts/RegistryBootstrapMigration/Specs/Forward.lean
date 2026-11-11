import EraSpec.Contracts.RegistryBootstrapMigration.Specs.Authority

/-!
# Model: forwarded calls, seen by the authority model

Source: branch `feat/upgrade-simplification` of the zksync-era `contracts` repository at
commit `e561b9cc2` (2026-10-19), as for `Specs/Authority.lean`. Paths are relative to
`l1-contracts/contracts/`. The OpenZeppelin v4.9 files are the two submodules that commit
pins: `lib/openzeppelin-contracts-upgradeable-v4` at `2d081f2` (`OZU/` below) and
`lib/openzeppelin-contracts-v4` at `dc44c9f` (`OZ/` below). Every `file:line` is at those
commits.

**This file is definitions only.** The results are in
`EraSpec.Contracts.RegistryBootstrapMigration.Properties.Forward` and are proved in
`EraSpec.Contracts.RegistryBootstrapMigration.Proofs.Forward`.

## Why this is modelled

`Specs/Authority.lean` lists the transactions of the actors other than the migration as
four labels: nominate on the CTM, accept a nomination, transfer the `ProxyAdmin`, move the
CTM's version. It does not model the CTM executor's `forward`. The folder README argued that
a `forward` is a sequence of those four steps, so every result that holds "along any run"
covers it. That was an argument about the label set, not a theorem. This file models the
calls a `forward` can make, so the argument can be checked.

## `forward` (`governance/UpgradeExecutorBase.sol:32-46`)

    function forward(Call[] calldata _calls) external payable onlyOwner {
        for (uint256 i = 0; i < _calls.length; ++i) {
            (bool success, bytes memory returnData) = _calls[i].target.call{value: _calls[i].value}(_calls[i].data);
            if (!success) { assembly { revert(add(returnData, 0x20), mload(returnData)) } }
            emit CallForwarded(_calls[i].target, _calls[i].value, _calls[i].data);
        }
    }

Each call is a `CALL` with the executor as `msg.sender`. A failing call reverts the whole
forward. Targets and calldata are arbitrary. The executor's NatSpec (:14-17) says
`forward` exists "so the authority the executor holds never becomes unreachable".
`CTMUpgradeExecutor.sol:25-29` says every CTM owner operation without a fixed entry point
goes through it. The authority matrix (`docs/registry-driven-upgrades.md:413`, from the
repository root) routes "CTM / ProxyAdmin `transferOwnership` (executor succession)" through
`forward` only.

## The writers of the state `AState` tracks

`AState` has six slots: the CTM's `_owner`, `_pendingOwner`, `protocolVersion` and
`currentRelease`; the CTM-domain `ProxyAdmin`'s `_owner`; and the migration's `executed`.
Their writers at the pin:

* **The CTM** (`state-transition/ChainTypeManager.sol:58`) is `Ownable2StepUpgradeable`. It
  does not override `renounceOwnership`.
  * `transferOwnership(x)` is `onlyOwner` (`OZU/access/OwnableUpgradeable.sol:40-43, 55-57`)
    and sets `_pendingOwner = x`, with no zero check (`OZU/access/Ownable2StepUpgradeable.sol:42-45`).
  * `acceptOwnership()` requires `pendingOwner() == msg.sender`, then
    `_transferOwnership(msg.sender)`, which deletes the nomination and sets the owner
    (`OZU/access/Ownable2StepUpgradeable.sol:51-54, 59-63`).
  * `renounceOwnership()` is `onlyOwner` and calls `_transferOwnership(address(0))`
    (`OZU/access/OwnableUpgradeable.sol:66-68`). The owner and the nomination both become zero.
  * The version writers are `setNewVersionUpgradeFromTransition` (:408-423) and the legacy
    `setNewVersionUpgrade` (:799-818). Both are `onlyOwner`, and both go through
    `_commitVersionEdge` (:528-542) and `_setCurrentRelease` (:305-323). `initialize`
    (:275-298) writes them too, but it is `reentrancyGuardInitializer` and reverts once the
    CTM is initialized (`common/ReentrancyGuard.sol:43-63`).
* **The CTM-domain `ProxyAdmin`** is OpenZeppelin's `ProxyAdmin is Ownable`
  (`OZ/proxy/transparent/ProxyAdmin.sol:13`).
  * `transferOwnership(x)` is `onlyOwner` and requires `x != 0` (`OZ/access/Ownable.sol:35-38, 69-72`).
  * `renounceOwnership()` is `onlyOwner` and sets the owner to zero (`OZ/access/Ownable.sol:61-63`).
  * `upgrade` and `upgradeAndCall` (`OZ/proxy/transparent/ProxyAdmin.sol:62-64, 74-80`) are
    `onlyOwner`. On the CTM proxy, which this `ProxyAdmin` administers
    (`CTMUpgradeExecutor.sol:38-40`), they replace the CTM's code. `upgradeAndCall` also
    runs `data` on the new code in the CTM's storage, so any of the CTM's slots can end up
    holding anything.
* **The migration** writes `executed` in `migrate()` only (`RegistryBootstrapMigration.sol:262-304`).
  `migrate()` is permissionless (:257-261) and is the contract's only state-changing entry
  point. Its other functions are `view`, and it has "no arbitrary-call surface" (:43-47).
  So the migration sends calls only from inside `migrate()`, and those calls are part of
  `MigrateStep`.

## Modelling choices

* **A transaction is a list of calls** (`Call`). Each call is an entry point (`Op`) and its
  `msg.sender`. `FRun` executes the list in order. The list for a `forward` holds, in
  execution order:
  * the calls `forward` makes itself, each with the executor as sender;
  * every call those calls make in turn, each with its own sender.

  For example, a forwarded `X.acceptCTMOwnership()` is an `untracked` call by the executor,
  followed by `X`'s own `acceptOwnership()` on the CTM, sent by `X`. Calls that write
  nothing tracked may be listed as `untracked` or left out.
* **A revert is the absence of a step.** A call whose guard fails has no `OpStep`, so its
  transaction has no `FRun`. Reject-only checks that read nothing tracked are omitted, which
  only adds runs. The version writers are over-approximated: the owner may set any version
  and release, exactly as `Label.legacyMove` lets any non-migration owner do.
* **No premise on the executor's code.** Whatever code a contract runs, the calls it makes
  have it as `msg.sender`. The coverage results need only that no call is sent by the
  migration (whose code makes none outside `migrate()`) or by the zero address. So they hold
  for a genuine executor, a non-genuine one, governance, or any other contract.
* **`Op.untracked`** is a call that writes none of the six slots, and that leaves the CTM
  proxy's code and its admin alone. Examples:
  * the CTM owner functions that touch no tracked slot (`replaceUpgradeTransition`,
    `setProtocolVersionDeadline`, `executeUpgrade`, `freezeChain`, `setValidator`, ...);
  * `ProxyAdmin.upgrade`/`upgradeAndCall` on a proxy other than the CTM (calls its
    reinitializer makes are listed on their own);
  * view calls (`validate()`, `validateApplied()`);
  * calls to other contracts.

  It may change configuration that the authority model fixes (the executors' own ownership,
  the notifier handover, the core domain), as before.
* **`Op.ctmCodeSwap o p v r`** is `upgrade`/`upgradeAndCall` on the CTM proxy, after which
  the CTM's owner, nominee, version and release are `o`, `p`, `v`, `r`. The CTM afterwards
  runs code the model does not know, so the values are arbitrary. This is the authority-side
  counterpart of `FCall.swapCtm` in `Contracts.ChainTypeManager`'s `ExecutorForward`, whose
  `ForwardCtmSwapBreaksInvariants` shows what it does to the CTM's version state. The swap
  inside `migrate()`, applied by the bootstrap rows, stays under the existing assumption that
  it keeps the `Ownable2Step` storage.
* **Not modelled.**
  * `ProxyAdmin.changeProxyAdmin(ctm, x)` (`OZ/proxy/transparent/ProxyAdmin.sol:51-53`). It
    moves the power to replace the CTM's code to `x`; who administers the CTM proxy is fixed
    configuration here.
  * ETH value, events, and `CallForwarded`.
-/

namespace Contracts.RegistryBootstrapMigration

/-- An entry point that writes a slot the authority model tracks, or a call that writes none. -/
inductive Op
  /-- `Ownable2Step(m.ctm).transferOwnership(x)`: nominate `x` (zero cancels a nomination). -/
  | ctmTransferOwnership (x : Address)
  /-- `Ownable2Step(m.ctm).acceptOwnership()`. -/
  | ctmAcceptOwnership
  /-- `Ownable2Step(m.ctm).renounceOwnership()`: owner and nomination become zero. -/
  | ctmRenounceOwnership
  /-- An owner-only CTM version writer (`setNewVersionUpgradeFromTransition`,
  `setNewVersionUpgrade`, or the pre-registry implementation's counterparts) leaving the CTM
  at version `v` with release `r`. -/
  | ctmSetVersion (v : ℕ) (r : Address)
  /-- `m.ctmProxyAdmin.transferOwnership(x)`. -/
  | paTransferOwnership (x : Address)
  /-- `m.ctmProxyAdmin.renounceOwnership()`. -/
  | paRenounceOwnership
  /-- `m.ctmProxyAdmin.upgrade(ctm, impl)` or `upgradeAndCall(ctm, impl, data)`: the CTM runs
  new code, which leaves its owner, nominee, version and release at `o`, `p`, `v`, `r`. -/
  | ctmCodeSwap (o p : Address) (v : ℕ) (r : Address)
  /-- `RegistryBootstrapMigration(M).migrate()`. -/
  | migrate
  /-- A call that writes none of the tracked slots. -/
  | untracked
deriving DecidableEq

/-- One call of a transaction: its `msg.sender` and its entry point. -/
structure Call where
  /-- `msg.sender`. -/
  sender : Address
  /-- The entry point and its arguments. -/
  op : Op
deriving DecidableEq

/-- One successful call by `a`. -/
inductive OpStep (K : Config) (a : Address) : AState → Op → AState → Prop
  /-- `onlyOwner`, then `_pendingOwner = x` (`OZU/access/Ownable2StepUpgradeable.sol:42-45`). -/
  | ctmTransferOwnership {s : AState} {x : Address} :
      s.ctmOwner = a → OpStep K a s (.ctmTransferOwnership x) { s with ctmPending := x }
  /-- `pendingOwner() == msg.sender`, then the caller is the owner and the nomination is
  deleted (`OZU/access/Ownable2StepUpgradeable.sol:51-54, 59-63`). -/
  | ctmAcceptOwnership {s : AState} :
      s.ctmPending = a →
      OpStep K a s .ctmAcceptOwnership { s with ctmOwner := a, ctmPending := 0 }
  /-- `onlyOwner`, then `_transferOwnership(address(0))` (`OZU/access/OwnableUpgradeable.sol:66-68`),
  which also deletes the nomination. -/
  | ctmRenounceOwnership {s : AState} :
      s.ctmOwner = a →
      OpStep K a s .ctmRenounceOwnership { s with ctmOwner := 0, ctmPending := 0 }
  /-- `onlyOwner` (`ChainTypeManager.sol:408, 804`), then the version and release move. -/
  | ctmSetVersion {s : AState} {v : ℕ} {r : Address} :
      s.ctmOwner = a → OpStep K a s (.ctmSetVersion v r) { s with ctmPv := v, ctmRel := r }
  /-- `onlyOwner` and `newOwner != address(0)` (`OZ/access/Ownable.sol:69-72`). -/
  | paTransferOwnership {s : AState} {x : Address} :
      s.paOwner = a → x ≠ 0 → OpStep K a s (.paTransferOwnership x) { s with paOwner := x }
  /-- `onlyOwner`, then the owner is zero (`OZ/access/Ownable.sol:61-63`). -/
  | paRenounceOwnership {s : AState} :
      s.paOwner = a → OpStep K a s .paRenounceOwnership { s with paOwner := 0 }
  /-- `onlyOwner` on the `ProxyAdmin` (`OZ/proxy/transparent/ProxyAdmin.sol:62-64, 74-80`);
  the new code's effect on the CTM's slots is arbitrary. -/
  | ctmCodeSwap {s : AState} {o p : Address} {v : ℕ} {r : Address} :
      s.paOwner = a →
      OpStep K a s (.ctmCodeSwap o p v r)
        { s with ctmOwner := o, ctmPending := p, ctmPv := v, ctmRel := r }
  /-- Permissionless (`RegistryBootstrapMigration.sol:257-262`): one successful `migrate()`. -/
  | migrate {s s' : AState} : MigrateStep K s s' → OpStep K a s .migrate s'
  /-- Writes nothing tracked. -/
  | untracked {s : AState} : OpStep K a s .untracked s

/-- The calls of one transaction (a `forward`, and the calls its targets make in turn), in
execution order; a failing call reverts them all. Several transactions in a row are one
`FRun` of their concatenated calls. -/
inductive FRun (K : Config) : AState → List Call → AState → Prop
  | nil {s : AState} : FRun K s [] s
  | cons {s s' s'' : AState} {c : Call} {cs : List Call} :
      OpStep K c.sender s c.op s' → FRun K s' cs s'' → FRun K s (c :: cs) s''

/-! ## The label set -/

/-- The labels of `Specs/Authority.lean` that the actors other than the migration use. -/
def Label.OtherActor : Label → Prop
  | .nominate _ => True
  | .accept => True
  | .transferPA _ => True
  | .legacyMove _ _ => True
  | _ => False

/-- The model's own transactions that a call is: an ownership or version call is the
matching other-actor label, `migrate()` is `migrate`, and a call that writes nothing tracked
is no transaction. A renounce or a CTM code swap has no label (`Op.InLabelSet`). -/
def Op.labels : Op → List Label
  | .ctmTransferOwnership x => [.nominate x]
  | .ctmAcceptOwnership => [.accept]
  | .ctmSetVersion v r => [.legacyMove v r]
  | .paTransferOwnership x => [.transferPA x]
  | .migrate => [.migrate]
  | .untracked => []
  | .ctmRenounceOwnership => []
  | .paRenounceOwnership => []
  | .ctmCodeSwap _ _ _ _ => []

/-- The call has a counterpart among the model's labels: it is not a renounce and not a CTM
code swap. -/
def Op.InLabelSet : Op → Prop
  | .ctmRenounceOwnership => False
  | .paRenounceOwnership => False
  | .ctmCodeSwap _ _ _ _ => False
  | _ => True

/-- The call hands authority to the migration by an ownership call: it nominates the
migration on the CTM, or transfers it the `ProxyAdmin`. As for `Label.handsToMigration`. A
CTM code swap is not an ownership call: what the new code writes is not visible in the call
(`ForwardCtmSwapReparks` is the consequence). -/
def Op.handsToMigration (K : Config) : Op → Prop
  | .ctmTransferOwnership x => x = K.M
  | .paTransferOwnership x => x = K.M
  | _ => False

/-- The call replaces the CTM's code. -/
def Op.swapsCtmCode : Op → Prop
  | .ctmCodeSwap _ _ _ _ => True
  | _ => False

/-- The labels of a call. -/
def Call.labels (c : Call) : List Label := c.op.labels

/-- A call the model's labels cover: it is sent neither by the migration nor by the zero
address, and it is in the label set. -/
def Call.Covered (K : Config) (c : Call) : Prop :=
  c.sender ≠ K.M ∧ c.sender ≠ 0 ∧ c.op.InLabelSet

/-! ## Runs with forwards -/

/-- A transaction of the extended model: one of `Specs/Authority.lean`'s, or a `forward`. -/
inductive XLabel
  /-- An `AStep` transaction. -/
  | tx (l : Label)
  /-- A `forward`, as the list of its calls. -/
  | forward (cs : List Call)

/-- One successful transaction of the extended model. -/
inductive XStep (K : Config) : AState → XLabel → AState → Prop
  | tx {s s' : AState} {l : Label} : AStep K s l s' → XStep K s (.tx l) s'
  | forward {s s' : AState} {cs : List Call} : FRun K s cs s' → XStep K s (.forward cs) s'

/-- A sequence of successful transactions of the extended model. -/
inductive XRun (K : Config) : AState → List XLabel → AState → Prop
  | nil {s : AState} : XRun K s [] s
  | cons {s s' s'' : AState} {x : XLabel} {xs : List XLabel} :
      XStep K s x s' → XRun K s' xs s'' → XRun K s (x :: xs) s''

/-- The labels of a transaction: itself, or those of a forward's calls. -/
def XLabel.labels : XLabel → List Label
  | .tx l => [l]
  | .forward cs => cs.flatMap Call.labels

/-- Every call of the transaction is covered. -/
def XLabel.Covered (K : Config) : XLabel → Prop
  | .tx _ => True
  | .forward cs => ∀ c ∈ cs, c.Covered K

/-- The transaction hands authority to the migration by an ownership call. -/
def XLabel.handsToMigration (K : Config) : XLabel → Prop
  | .tx l => l.handsToMigration K
  | .forward cs => ∃ c ∈ cs, c.op.handsToMigration K

/-- The transaction replaces the CTM's code. -/
def XLabel.swapsCtmCode : XLabel → Prop
  | .tx _ => False
  | .forward cs => ∃ c ∈ cs, c.op.swapsCtmCode

/-! ## Witness data

The configuration and states of `Specs/Authority.lean`'s witnesses: migration `50`, CTM
executor `3`, governance `9`. Address `7` is a successor executor. -/

/-- What the witness bundle leaves (`BundleWitness`): executor `3` owns the CTM and the
`ProxyAdmin`, at version 35 on release 60, the edge spent. -/
def wPost : AState := ⟨3, 0, 3, 35, 60, true⟩

/-- What the non-genuine executor's `migrate()` leaves (`NonGenuineExecutorParksTheCTM`): the
CTM owned by the migration with executor `3` nominated, the `ProxyAdmin` with `3`. -/
def wParked : AState := ⟨50, 3, 3, 35, 60, true⟩

/-- Governance's hand-over before `migrate()`: the migration nominated and owning the
`ProxyAdmin`. -/
def wHanded : AState := { wPre with ctmPending := 50, paOwner := 50 }

/-- Executor succession through `forward` by executor `3`:
* move the CTM to version 36 on release 61;
* nominate `7` on the CTM;
* hand `7` the `ProxyAdmin`;
* call `7.acceptCTMOwnership()`, which makes `7` call the CTM's `acceptOwnership()`. -/
def wSuccession : List Call :=
  [⟨3, .ctmSetVersion 36 61⟩, ⟨3, .ctmTransferOwnership 7⟩, ⟨3, .paTransferOwnership 7⟩,
    ⟨3, .untracked⟩, ⟨7, .ctmAcceptOwnership⟩]

end Contracts.RegistryBootstrapMigration
