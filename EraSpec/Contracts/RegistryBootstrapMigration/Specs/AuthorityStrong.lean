import EraSpec.Contracts.RegistryBootstrapMigration.Specs.Forward

/-!
# Model: who can move a CTM parked on the spent migration

Source: branch `feat/upgrade-simplification` of the zksync-era `contracts` repository at
commit `e561b9cc2`, as for `Specs/Authority.lean` and `Specs/Forward.lean`.

**This file adds no new operation.** It reuses the label model of `Specs/Authority.lean` and
the call model of `Specs/Forward.lean` unchanged (`AStep`, `ARun`, `OpStep`, `FRun`, `Call`,
...) and adds witness data. The results are in
`EraSpec.Contracts.RegistryBootstrapMigration.Properties.AuthorityStrong` and are proved in
`EraSpec.Contracts.RegistryBootstrapMigration.Proofs.AuthorityStrong`.

## Why

`ParkedCTMLeavesOnlyByNomineeAccept` (`Properties/Authority.lean`) is stated over the label
model, which leaves out one writer of the CTM's owner slot: a code swap on the CTM proxy by the
CTM-domain `ProxyAdmin`'s owner (`upgrade`/`upgradeAndCall`, `Op.ctmCodeSwap` in
`Specs/Forward.lean`; the `ProxyAdmin` administers the CTM proxy,
`executors/CTMUpgradeExecutor.sol:38-39`). Its docstring used to excuse the omission by
saying that in the parked states the model reaches, that owner is the nominee too. In the
state the non-genuine executor's `migrate()` leaves (`wParked`), the `ProxyAdmin`'s owner and the nominee
are both executor `3`. But the `ProxyAdmin` is plain `Ownable`, so its owner can hand it on
with one `transferPA` while the CTM stays parked. The data below is that run.
-/

namespace Contracts.RegistryBootstrapMigration

/-- `wParked` after the `ProxyAdmin`'s owner, executor `3`, hands the `ProxyAdmin` to `7`. The
CTM is still owned by the spent migration `50`, with `3` nominated. The `ProxyAdmin` is `7`'s. -/
def wParkedHandedOn : AState := ⟨50, 3, 7, 35, 60, true⟩

/-- What a CTM code swap by `7` leaves from `wParkedHandedOn`, when the new code writes `7` as
the owner and no nominee. -/
def wParkedSwapped : AState := ⟨7, 0, 7, 35, 60, true⟩

/-- From `wParked`, executor `3` hands `7` the `ProxyAdmin`, then `7` swaps the CTM's code. -/
def wHandOnThenSwap : List Call :=
  [⟨3, .paTransferOwnership 7⟩, ⟨7, .ctmCodeSwap 7 0 35 60⟩]

end Contracts.RegistryBootstrapMigration
