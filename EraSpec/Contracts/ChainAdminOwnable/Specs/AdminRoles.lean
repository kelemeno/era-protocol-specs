import EraSpec.Contracts.ChainAdminOwnable.Specs.Authority

/-!
# Model: the admin roles a `ChainAdminOwnable` holds, after a renounce

Source and model: `Specs/Authority.lean` (`b17415d20`); this topic adds no rule. It reads that
model at the two places where the deployment puts a `ChainAdminOwnable` in an admin role:

* **A ZK chain's diamond.** The admin pair `(s.admin, s.pendingAdmin)` moves only through
  `setPendingAdmin`, which only the admin can call (`facets/Admin.sol:131-137`), and
  `acceptAdmin`, which only the pending admin can call (`:140-153`), or through a cut
  (`:559-609`). No owner or other role can reassign it. The admin's powers are the `onlyAdmin`
  and `onlyAdminOrChainTypeManager` functions (`ADMIN_ONLY_SELECTORS`, `ADMIN_OR_CTM_SELECTORS`),
  `setProofSystemStatus` (`:416-432`, modelled without its check), `upgradeChainFromVersion` (a
  cut, `:559-590`), and the initiation of a migration: `Migrator.forwardedBridgeBurn` requires the original caller of the Bridgehub request
  to be the admin (`facets/Migrator.sol:165-166`), and a renounced `ChainAdminOwnable` never calls
  the Bridgehub successfully (`RenouncedCaoReachesOnlySetTokenMultiplier`); the function itself is
  modelled as unknown code.
* **The Bridgehub.** `setPendingAdmin` is `onlyOwnerOrAdmin` (`BridgehubBase.sol:139-144,
  179-188`), so the Bridgehub's owner can nominate a new admin whatever the admin does; the nominee
  then accepts (`:191-204`).

The `ChainAdminOwnable`'s calls carry the selector `0x235d9eb5` once it is renounced
(`Properties/Authority.lean`, `RenounceIsPermanent`). The Bridgehub has no function with that
selector and no `fallback` (`BRIDGEHUB_SELECTORS`), so those calls revert there.

**This file is definitions only**: one witness state. The results are in
`EraSpec.Contracts.ChainAdminOwnable.Properties.AdminRoles`.
-/

namespace Contracts.ChainAdminOwnable

/-- `wRenounced` with diamond `4`'s pending admin set to `12`: the storage and admin pair
`MulticallOutlivesRenounce` ends with. -/
def wNominated : State := wRenounced.setChain 4 ⟨1, 12⟩

end Contracts.ChainAdminOwnable
