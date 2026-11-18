import EraSpec.Protocol.NativeValueLegs.Specs.LegConservation

/-!
# Properties: a native-value atomic leg returns exactly what it collected, to its payer, in its asset

Statements about `EraSpec.Protocol.NativeValueLegs.Specs.LegConservation` (head `b17415d20`).
Proofs are in `EraSpec.Protocol.NativeValueLegs.Proofs.LegConservation`.

* **(1) Bundle shape.**  Under both indirect-starter checks, and for a sender other than the router,
  every call sent from the router carries no value and router data naming another asset, every other
  call is the sender's, and the base-token refunds `_recoverBundle` requests are `(sender, v)` pairs
  whose values sum to `totalBurnedCallsValue` (`ValueCallsComeFromTheSender`).  The sender premise
  stands for an inventory fact, not a check: the router's code makes no call to the center's send
  entry points (at `b17415d20`, `L2AssetRouter.sol` uses the center's address only in its
  `onlyL2InteropCenter` gate, `:83-86, :129-132`, and `AssetRouterBase.sol` not at all; the
  router's external calls go to asset handlers, the vault, the Bridgehub and itself).  It is
  load-bearing (`RouterSenderValueIsNotRefunded`).
* **(2) The refund.**  A successful refund of such a bundle moves exactly `totalBurnedCallsValue` of
  the destination base-token asset to the sender, out of the holder (same base token), out of the
  vault's escrow (a token native here) or by minting (a bridged token), with the tracker's
  `chainBalance` of a native token credited by the same amount and the L1 counters unchanged
  (`ClaimReturnsCollected`).  Premises: the frame premise `RecoveryFramesOthers` on the code that
  recovers router-produced calls, and, when something was collected, the asset registered in the
  tracker unless it is the base token.  The registration premise is needed only for a token native to
  the source chain (`ClaimReturnsCollectedIfNativeRegistered`): a refund of a bridged token the
  tracker has not registered registers it and mints the same amount.  For a native token it is
  load-bearing: the first registration also sets the token's `chainBalance`
  (`UnregisteredNativeRefundSetsChainBalance`).
* **The collection.**  Through the holder or the vault, the send moves the same amount the other way
  (`CollectionTakesCollected`), and leaves the asset registered in the tracker
  (`CollectionRegistersAsset`), which discharges the registration premise of (2).  So the refund's
  footprint change is the exact negation of the collection's (`RefundIsCollectionInverse`), and a
  refund right after the collection restores the footprint (`RefundRestoresFootprint`).
* **Countermodel.**  Without `IndirectCallCannotCarryValue`, an indirect call's value is
  collected and the refund returns nothing of it (`WithoutIndirectValueBanValueIsNotRefunded`).

Every result about the refund is about a refund that succeeds; none states when a refund succeeds.
No statement takes a hash premise.  The full execution at the destination and the exclusion of
"executed and refunded" are not restated here (see the folder README).
-/

namespace Contracts.NativeValueLegs

/-! ## (1) Bundle shape -/

/-- **(1) THE VALUE CALLS ARE THE SENDER'S, AND THEIR VALUES ARE `totalBurnedCallsValue`.**  For a
bundle formed by sender `u` under the deployed checks, with `u` not the router: every call from the
router carries value `0` and `finalizeDeposit` data on an asset other than the bundle's
destination base-token asset `A`; every call not from the router is from `u`; every base-token
refund `_recoverBundle` requests is to `u`; and their amounts sum to `collected starters`, the
`totalBurnedCallsValue` the send collected. -/
def Properties.ValueCallsComeFromTheSender : Prop :=
  ∀ (cfg : Config) (A : AssetId) (u : Address) (starters : List Starter) (calls : List Call),
    u ≠ cfg.router →
    (∀ s ∈ starters, StarterPasses deployed cfg s) →
    List.Forall₂ (FormsCall cfg A u) starters calls →
    (∀ c ∈ calls, c.fromAddr = cfg.router →
        c.value = 0 ∧ ∃ a m, c.data = .finalizeDeposit cfg.thisChain a m ∧ a ≠ A) ∧
      (∀ c ∈ calls, c.fromAddr ≠ cfg.router → c.fromAddr = u) ∧
      (∀ p ∈ valueRefunds cfg calls, p.1 = u) ∧
      ((valueRefunds cfg calls).map Prod.snd).sum = collected starters

/-- **WITNESS FOR (1).**  A bundle with a direct value call and a router-produced call, formed by a
sender other than the router under the deployed checks, requests one refund, of `collected > 0`, to
its sender. -/
def Properties.ValueCallsWitness : Prop :=
  ∃ (cfg : Config) (A : AssetId) (u : Address) (starters : List Starter) (calls : List Call),
    u ≠ cfg.router ∧ (∀ s ∈ starters, StarterPasses deployed cfg s) ∧
      List.Forall₂ (FormsCall cfg A u) starters calls ∧
      (∃ c ∈ calls, c.fromAddr = cfg.router) ∧ 0 < collected starters ∧
      valueRefunds cfg calls = [(u, collected starters)]

/-- **THE SENDER PREMISE IS LOAD-BEARING.**  If the router itself were the sender, its direct value
call would be dispatched to `recoverAtomicCall` and refund nothing: the value is collected from the
router, and a successful refund leaves the leg's footprint unchanged. -/
def Properties.RouterSenderValueIsNotRefunded : Prop :=
  ∃ (P : Params) (u : Address) (starters : List Starter) (B : Bundle) (w₀ w₁ w₂ : World),
    u = P.cfg.router ∧ (∀ s ∈ starters, StarterPasses deployed P.cfg s) ∧
      List.Forall₂ (FormsCall P.cfg B.destBaseAsset u) starters B.calls ∧
      RecoveryFramesOthers P B.destBaseAsset ∧ 0 < collected starters ∧
      collect P w₀ u B.destChain B.destBaseAsset (collected starters) = some w₁ ∧
      Shifted P.cfg B.destBaseAsset u (-(collected starters : ℤ)) w₀ w₁ ∧
      claimRefund P w₁ B = some w₂ ∧ Frames P.cfg B.destBaseAsset w₁ w₂

/-! ## (2) The refund -/

/-- **(2) A SUCCESSFUL REFUND RETURNS EXACTLY WHAT WAS COLLECTED, TO THE PAYER, IN THE COLLECTED
ASSET.**  Take a bundle formed by sender `u` (not the router) under the deployed checks, with
destination base-token asset `A`.  If the code recovering router-produced calls leaves `A` alone
(`RecoveryFramesOthers`), and, if anything was collected, `A` is the base token or already registered
in the tracker, then every successful `claimRefund` of the bundle moves `collected starters` of `A`
to `u` (`Shifted … u (collected starters)`): out of the holder for the base token, out of the
vault's escrow for a token native here (crediting the tracker's `chainBalance` by the same amount),
or minted for a bridged token; the L1 counters do not move. -/
def Properties.ClaimReturnsCollected : Prop :=
  ∀ (P : Params) (u : Address) (starters : List Starter) (B : Bundle) (w w' : World),
    u ≠ P.cfg.router →
    (∀ s ∈ starters, StarterPasses deployed P.cfg s) →
    List.Forall₂ (FormsCall P.cfg B.destBaseAsset u) starters B.calls →
    RecoveryFramesOthers P B.destBaseAsset →
    (0 < collected starters →
      B.destBaseAsset = P.cfg.baseAsset ∨ w.registered B.destBaseAsset = true) →
    claimRefund P w B = some w' →
    Shifted P.cfg B.destBaseAsset u (collected starters) w w'

/-- **WITNESS FOR (2), DIFFERENT BASE TOKEN.**  Every premise of `ClaimReturnsCollected` holds, with a
router-produced call recovered by code that mints another asset, a value call of `collected > 0` in a
token native to the source chain, and the refund succeeds. -/
def Properties.ClaimWitnessNativeToken : Prop :=
  ∃ (P : Params) (u : Address) (starters : List Starter) (B : Bundle) (w : World),
    u ≠ P.cfg.router ∧ (∀ s ∈ starters, StarterPasses deployed P.cfg s) ∧
      List.Forall₂ (FormsCall P.cfg B.destBaseAsset u) starters B.calls ∧
      RecoveryFramesOthers P B.destBaseAsset ∧ w.registered B.destBaseAsset = true ∧
      B.destBaseAsset ≠ P.cfg.baseAsset ∧ NativeHere P.cfg B.destBaseAsset ∧
      (∃ c ∈ B.calls, c.fromAddr = P.cfg.router) ∧ 0 < collected starters ∧
      (claimRefund P w B).isSome

/-- **WITNESS FOR (2), SAME BASE TOKEN.**  Every premise of `ClaimReturnsCollected` holds with the
source chain's base token as the asset, a value call of `collected > 0`, and the refund succeeds. -/
def Properties.ClaimWitnessBaseToken : Prop :=
  ∃ (P : Params) (u : Address) (starters : List Starter) (B : Bundle) (w : World),
    u ≠ P.cfg.router ∧ (∀ s ∈ starters, StarterPasses deployed P.cfg s) ∧
      List.Forall₂ (FormsCall P.cfg B.destBaseAsset u) starters B.calls ∧
      RecoveryFramesOthers P B.destBaseAsset ∧ B.destBaseAsset = P.cfg.baseAsset ∧
      (∃ c ∈ B.calls, c.fromAddr = P.cfg.router) ∧ 0 < collected starters ∧
      (claimRefund P w B).isSome

/-- **(2) WITH THE REGISTRATION PREMISE ONLY FOR A TOKEN NATIVE HERE.**  `ClaimReturnsCollected` with
its registration premise weakened: if anything was collected, the asset is the base token, is
registered in the tracker, or does not originate on the source chain.  A successful refund of a
bridged token the tracker has not registered registers it (`_registerLegacyToken`,
`L2AssetTracker.sol:233-262`, whose supply snapshot is not modelled) and mints, so it moves
`collected starters` of the asset to `u` as in `ClaimReturnsCollected`. -/
def Properties.ClaimReturnsCollectedIfNativeRegistered : Prop :=
  ∀ (P : Params) (u : Address) (starters : List Starter) (B : Bundle) (w w' : World),
    u ≠ P.cfg.router →
    (∀ s ∈ starters, StarterPasses deployed P.cfg s) →
    List.Forall₂ (FormsCall P.cfg B.destBaseAsset u) starters B.calls →
    RecoveryFramesOthers P B.destBaseAsset →
    (0 < collected starters →
      B.destBaseAsset = P.cfg.baseAsset ∨ w.registered B.destBaseAsset = true ∨
        ¬ NativeHere P.cfg B.destBaseAsset) →
    claimRefund P w B = some w' →
    Shifted P.cfg B.destBaseAsset u (collected starters) w w'

/-- **WITNESS FOR THE WEAKER PREMISE.**  Every premise of `ClaimReturnsCollectedIfNativeRegistered`
holds for a token that does not originate on the source chain and that the tracker has not
registered (in the proof, a token bridged from L1), with a router-produced call recovered by code
that mints another asset and a value call of `collected > 0`, and the refund succeeds. -/
def Properties.ClaimWitnessUnregisteredBridged : Prop :=
  ∃ (P : Params) (u : Address) (starters : List Starter) (B : Bundle) (w : World),
    u ≠ P.cfg.router ∧ (∀ s ∈ starters, StarterPasses deployed P.cfg s) ∧
      List.Forall₂ (FormsCall P.cfg B.destBaseAsset u) starters B.calls ∧
      RecoveryFramesOthers P B.destBaseAsset ∧ B.destBaseAsset ≠ P.cfg.baseAsset ∧
      w.registered B.destBaseAsset = false ∧ ¬ NativeHere P.cfg B.destBaseAsset ∧
      (∃ c ∈ B.calls, c.fromAddr = P.cfg.router) ∧ 0 < collected starters ∧
      (claimRefund P w B).isSome

/-- **THE REGISTRATION PREMISE IS LOAD-BEARING FOR A TOKEN NATIVE HERE.**  A bundle formed by a sender
other than the router under the deployed checks, with a value call of `collected > 0` in a token
native to the source chain that the tracker has not registered, under the frame premise, whose
refund succeeds and is not `Shifted … u (collected starters)`: the tracker's first registration of
the token sets its `chainBalance` to `MAX_TOKEN_BALANCE` minus the vault's holding
(`L2AssetTracker.sol:246-251`), and the refund then credits `collected starters`. -/
def Properties.UnregisteredNativeRefundSetsChainBalance : Prop :=
  ∃ (P : Params) (u : Address) (starters : List Starter) (B : Bundle) (w w' : World),
    u ≠ P.cfg.router ∧ (∀ s ∈ starters, StarterPasses deployed P.cfg s) ∧
      List.Forall₂ (FormsCall P.cfg B.destBaseAsset u) starters B.calls ∧
      RecoveryFramesOthers P B.destBaseAsset ∧ B.destBaseAsset ≠ P.cfg.baseAsset ∧
      NativeHere P.cfg B.destBaseAsset ∧ w.registered B.destBaseAsset = false ∧
      0 < collected starters ∧ claimRefund P w B = some w' ∧
      w'.chainBalance B.destBaseAsset =
        maxTokenBalance - ntvHolding P.cfg w B.destBaseAsset + collected starters ∧
      ¬ Shifted P.cfg B.destBaseAsset u (collected starters) w w'

/-! ## The collection -/

/-- **THE COLLECTION TAKES `v` FROM THE PAYER.**  For a destination other than L1, an asset that is
the base token or routed to the vault, an asset already registered in the tracker, and a
token ledger whose supply covers every balance (`SupplyCovers`, the ERC20 invariant), a successful
collection of `v` by sender `u` moves `v` of the asset from `u` into the holder, into the vault's
escrow, or out of the supply (`Shifted … u (-v)`). -/
def Properties.CollectionTakesCollected : Prop :=
  ∀ (P : Params) (u : Address) (d : Chain) (A : AssetId) (v : ℕ) (w w' : World),
    d ≠ P.cfg.l1Chain →
    (A = P.cfg.baseAsset ∨ w.handler A = P.cfg.ntv) →
    w.registered A = true → SupplyCovers w A →
    collect P w u d A v = some w' →
    Shifted P.cfg A u (-(v : ℤ)) w w'

/-- **THE COLLECTION REGISTERS THE ASSET.**  A successful collection of `v > 0` through the holder or
the vault leaves the asset registered in the tracker. -/
def Properties.CollectionRegistersAsset : Prop :=
  ∀ (P : Params) (u : Address) (d : Chain) (A : AssetId) (v : ℕ) (w w' : World),
    0 < v → (A = P.cfg.baseAsset ∨ w.handler A = P.cfg.ntv) →
    collect P w u d A v = some w' → w'.registered A = true

/-- **WITNESS FOR THE REGISTRATION.**  Every premise of `CollectionRegistersAsset` holds for a token
bridged from L1, routed to the vault and not yet registered in the tracker, and the collection
succeeds. -/
def Properties.CollectionRegistersWitness : Prop :=
  ∃ (P : Params) (u : Address) (d : Chain) (A : AssetId) (v : ℕ) (w : World),
    0 < v ∧ A ≠ P.cfg.baseAsset ∧ w.handler A = P.cfg.ntv ∧ w.registered A = false ∧
      (collect P w u d A v).isSome

/-- **WITNESS FOR THE COLLECTION.**  Every premise of `CollectionTakesCollected` holds for a token
native to the source chain routed to the vault, with `v > 0`, and the collection succeeds. -/
def Properties.CollectionWitness : Prop :=
  ∃ (P : Params) (u : Address) (d : Chain) (A : AssetId) (v : ℕ) (w : World),
    d ≠ P.cfg.l1Chain ∧ A ≠ P.cfg.baseAsset ∧ w.handler A = P.cfg.ntv ∧ w.registered A = true ∧
      SupplyCovers w A ∧ 0 < v ∧ (collect P w u d A v).isSome

/-! ## The round trip -/

/-- **THE REFUND UNDOES THE COLLECTION.**  For a bundle formed by sender `u` (not the router) under
the deployed checks: if its collection from `w₀` to `w₁` went through the holder or the vault, with
the asset registered and its supply covering every balance, and a later refund of it from `w₂` to
`w₃` succeeds, with the asset the base token or registered at `w₂` if anything was collected, under
the frame premise, then the refund's change of the asset's footprint is the negation of the
collection's, account by account.  (The refund's success implies the destination is not L1.) -/
def Properties.RefundIsCollectionInverse : Prop :=
  ∀ (P : Params) (u : Address) (starters : List Starter) (B : Bundle) (w₀ w₁ w₂ w₃ : World),
    u ≠ P.cfg.router →
    (∀ s ∈ starters, StarterPasses deployed P.cfg s) →
    List.Forall₂ (FormsCall P.cfg B.destBaseAsset u) starters B.calls →
    RecoveryFramesOthers P B.destBaseAsset →
    (B.destBaseAsset = P.cfg.baseAsset ∨ w₀.handler B.destBaseAsset = P.cfg.ntv) →
    w₀.registered B.destBaseAsset = true → SupplyCovers w₀ B.destBaseAsset →
    collect P w₀ u B.destChain B.destBaseAsset (collected starters) = some w₁ →
    (0 < collected starters →
      B.destBaseAsset = P.cfg.baseAsset ∨ w₂.registered B.destBaseAsset = true) →
    claimRefund P w₂ B = some w₃ →
    DeltasCancel P.cfg B.destBaseAsset w₀ w₁ w₂ w₃

/-- **A REFUND RIGHT AFTER THE COLLECTION RESTORES THE FOOTPRINT.**  Under the premises of
`RefundIsCollectionInverse` with the refund starting where the collection ended, the asset's
footprint and registration after the refund are those before the collection. -/
def Properties.RefundRestoresFootprint : Prop :=
  ∀ (P : Params) (u : Address) (starters : List Starter) (B : Bundle) (w₀ w₁ w₂ : World),
    u ≠ P.cfg.router →
    (∀ s ∈ starters, StarterPasses deployed P.cfg s) →
    List.Forall₂ (FormsCall P.cfg B.destBaseAsset u) starters B.calls →
    RecoveryFramesOthers P B.destBaseAsset →
    (B.destBaseAsset = P.cfg.baseAsset ∨ w₀.handler B.destBaseAsset = P.cfg.ntv) →
    w₀.registered B.destBaseAsset = true → SupplyCovers w₀ B.destBaseAsset →
    collect P w₀ u B.destChain B.destBaseAsset (collected starters) = some w₁ →
    claimRefund P w₁ B = some w₂ →
    Frames P.cfg B.destBaseAsset w₀ w₂

/-- **WITNESS FOR THE ROUND TRIP.**  Every premise of `RefundRestoresFootprint` holds with a value
call of `collected > 0` in a token bridged from L1 and a router-produced call, and both the collection
and the refund succeed.  With `w₂ = w₁` these are also the premises of `RefundIsCollectionInverse`
(the registration at `w₁` is `CollectionRegistersAsset`). -/
def Properties.RoundTripWitness : Prop :=
  ∃ (P : Params) (u : Address) (starters : List Starter) (B : Bundle) (w₀ w₁ : World),
    u ≠ P.cfg.router ∧ (∀ s ∈ starters, StarterPasses deployed P.cfg s) ∧
      List.Forall₂ (FormsCall P.cfg B.destBaseAsset u) starters B.calls ∧
      RecoveryFramesOthers P B.destBaseAsset ∧
      (B.destBaseAsset = P.cfg.baseAsset ∨ w₀.handler B.destBaseAsset = P.cfg.ntv) ∧
      w₀.registered B.destBaseAsset = true ∧ SupplyCovers w₀ B.destBaseAsset ∧
      0 < collected starters ∧
      (∃ c ∈ B.calls, c.fromAddr = P.cfg.router) ∧
      collect P w₀ u B.destChain B.destBaseAsset (collected starters) = some w₁ ∧
      (claimRefund P w₁ B).isSome

/-! ## Countermodel: an indirect call carrying value -/

/-- **WITHOUT `IndirectCallCannotCarryValue`, THE VALUE IS COLLECTED AND NOT REFUNDED.**  With the
check off, a bundle with one indirect starter carrying value `v > 0`, formed by a sender other than
the router, collects `v` from the sender, and a successful refund returns nothing of the asset:
the call's `from` is the router, so it is dispatched to `recoverAtomicCall`. -/
def Properties.WithoutIndirectValueBanValueIsNotRefunded : Prop :=
  ∃ (P : Params) (u : Address) (starters : List Starter) (B : Bundle) (w₀ w₁ w₂ : World),
    u ≠ P.cfg.router ∧ (∀ s ∈ starters, StarterPasses withoutIndirectValueBan P.cfg s) ∧
      List.Forall₂ (FormsCall P.cfg B.destBaseAsset u) starters B.calls ∧
      RecoveryFramesOthers P B.destBaseAsset ∧ 0 < collected starters ∧
      collect P w₀ u B.destChain B.destBaseAsset (collected starters) = some w₁ ∧
      Shifted P.cfg B.destBaseAsset u (-(collected starters : ℤ)) w₀ w₁ ∧
      claimRefund P w₁ B = some w₂ ∧ Frames P.cfg B.destBaseAsset w₁ w₂

end Contracts.NativeValueLegs
