import EraSpec.Contracts.DataEncoding.Specs.AssetIdRuns

/-!
# Properties: the router's and the vault's results with keccak as the id hash

Statements about `EraSpec.Contracts.DataEncoding.Specs.AssetIdRuns`. Proofs are in
`EraSpec.Contracts.DataEncoding.Proofs.AssetIdRuns`.

Every result here takes NO premise on keccak. Each has the form "the model's conclusion, or a
keccak event on byte strings the instance names":

* for one call (`NoHijackOrKeccakCollision`, `NtvTouchesOnlyItsOwnIdsOrKeccakCollision`,
  `RegisterNativeIdFreshOrKeccakEvent`), the event is on exactly the two preimages the call
  compares;
* for a logged run (`LoggedRunNoHijackOrKeccakCollision`,
  `LoggedRunKeepsVaultRoutesOrKeccakCollision`, `LoggedRunSoundOrKeccakEvent`), it is among
  the preimages of the triples or pairs the run's own calls hashed (plus the watched triple).

So a failure of the conclusion hands over a keccak collision (or a zero preimage) on inputs the
run names: a reduction, not an assumption.

For each, a witness shows the event disjunct false on a nontrivial instance. Countermodels show
that when the event holds the conclusion really fails: for one call (`KeccakCollisionHijacks`),
for a logged router run (`KeccakCollisionOnLogTakesOverLiveRoute`), for native registration
(`RegisterNativeIdTakenByKeccakCollision`) and for a logged vault run
(`LoggedRunSoundEventNeeded`). The witnesses are the existing abstract witnesses carried to
byte level by `Properties.RouterEncodingsAreKeccakInstances` and
`Properties.VaultEncodingsAreKeccakInstances` (topic `AssetId`).
-/

namespace Contracts.DataEncoding

open AttackVectors.BundleHashEncoding (HashCollision)

/-! ## One router call -/

/-- **NO HIJACK, OR A KECCAK COLLISION ON THE TWO NAMED PREIMAGES.** With the byte-level id
hash, a call by a caller other than the vault leaves the handler of the id hashed from any
other sender `s` unchanged, unless keccak collides on the two 96-byte preimages
`abi.encode(thisChain, s, d')` and `abi.encode(thisChain, caller, d)`. This is
`Contracts.AssetRouter.Properties.NoHijackOrCollision` with its id-equality disjunct turned
into a keccak collision on named inputs. -/
def Properties.NoHijackOrKeccakCollision : Prop :=
  ∀ (keccak : Keccak) (thisChain : AssetRouter.Chain) (ntv ntvAddr : AssetRouter.Address)
    (R : AssetRouter.Router) (caller : AssetRouter.Address) (d : AssetRouter.AssetData)
    (h : AssetRouter.Address), caller ≠ ntv →
    ∀ (s : AssetRouter.Address) (d' : AssetRouter.AssetData), s ≠ caller →
      (AssetRouter.setHandler (routerEnc keccak) thisChain ntv ntvAddr R caller d h).handler
          (routerEnc keccak thisChain s d')
        = R.handler (routerEnc keccak thisChain s d')
      ∨ HashCollision keccak (routerPreimage thisChain s d') (routerPreimage thisChain caller d)

/-- **THE VAULT IS NO EXCEPTION, OR A KECCAK COLLISION ON THE TWO NAMED PREIMAGES.** The vault's
call hashes the normalised sender `ntvAddr`; it leaves the id of any other sender `s` alone
unless keccak collides on `abi.encode(thisChain, s, d')` and `abi.encode(thisChain, ntvAddr, d)`. -/
def Properties.NtvTouchesOnlyItsOwnIdsOrKeccakCollision : Prop :=
  ∀ (keccak : Keccak) (thisChain : AssetRouter.Chain) (ntv ntvAddr : AssetRouter.Address)
    (R : AssetRouter.Router) (d : AssetRouter.AssetData) (h : AssetRouter.Address),
    ∀ (s : AssetRouter.Address) (d' : AssetRouter.AssetData), s ≠ ntvAddr →
      (AssetRouter.setHandler (routerEnc keccak) thisChain ntv ntvAddr R ntv d h).handler
          (routerEnc keccak thisChain s d')
        = R.handler (routerEnc keccak thisChain s d')
      ∨ HashCollision keccak (routerPreimage thisChain s d') (routerPreimage thisChain ntvAddr d)

/-- **THE COLLISION DISJUNCT IS NOT A TAUTOLOGY.** An authorised non-vault call and another
sender's triple on whose preimage keccak does not collide with the written one. -/
def Properties.NoHijackOrKeccakCollisionWitness : Prop :=
  ∃ (keccak : Keccak) (thisChain : AssetRouter.Chain) (ntv ntvAddr : AssetRouter.Address)
    (R : AssetRouter.Router) (caller : AssetRouter.Address) (d : AssetRouter.AssetData)
    (s : AssetRouter.Address) (d' : AssetRouter.AssetData),
    AssetRouter.SetGuard (routerEnc keccak) thisChain ntv ntvAddr R caller d ∧ caller ≠ ntv
    ∧ s ≠ caller
    ∧ ¬ HashCollision keccak (routerPreimage thisChain s d') (routerPreimage thisChain caller d)

/-- **THE VAULT FORM'S COLLISION DISJUNCT IS NOT A TAUTOLOGY EITHER.** An authorised vault call and a
sender `s ≠ ntvAddr` on whose preimage keccak does not collide with the vault's written one. -/
def Properties.NtvTouchesOnlyItsOwnIdsOrKeccakCollisionWitness : Prop :=
  ∃ (keccak : Keccak) (thisChain : AssetRouter.Chain) (ntv ntvAddr : AssetRouter.Address)
    (R : AssetRouter.Router) (d : AssetRouter.AssetData) (s : AssetRouter.Address)
    (d' : AssetRouter.AssetData),
    AssetRouter.SetGuard (routerEnc keccak) thisChain ntv ntvAddr R ntv d ∧ s ≠ ntvAddr
    ∧ ¬ HashCollision keccak (routerPreimage thisChain s d') (routerPreimage thisChain ntvAddr d)

/-- **UNDER A KECCAK COLLISION ON THE TWO PREIMAGES, AN AUTHORISED CALL RE-POINTS ANOTHER
SENDER'S ID.** A keccak, an authorised non-vault call, and a sender `s ≠ caller` whose id's
handler the call changes; keccak then collides on exactly the two named preimages. So the
collision disjunct cannot be dropped. -/
def Properties.KeccakCollisionHijacks : Prop :=
  ∃ (keccak : Keccak) (thisChain : AssetRouter.Chain) (ntv ntvAddr : AssetRouter.Address)
    (R : AssetRouter.Router) (caller : AssetRouter.Address) (d : AssetRouter.AssetData)
    (h : AssetRouter.Address) (s : AssetRouter.Address) (d' : AssetRouter.AssetData),
    AssetRouter.SetGuard (routerEnc keccak) thisChain ntv ntvAddr R caller d ∧ caller ≠ ntv
    ∧ s ≠ caller
    ∧ (AssetRouter.setHandler (routerEnc keccak) thisChain ntv ntvAddr R caller d h).handler
          (routerEnc keccak thisChain s d')
        ≠ R.handler (routerEnc keccak thisChain s d')
    ∧ HashCollision keccak (routerPreimage thisChain s d') (routerPreimage thisChain caller d)

/-! ## Logged router runs -/

/-- **RUN-LEVEL NO HIJACK, OR A KECCAK COLLISION AMONG THE RUN'S OWN PREIMAGES.**
`Contracts.AssetRouter.Properties.LoggedRunNoHijack` with its premise
`IdInjOn enc (insert (thisChain, s, d') (loggedTriples log))` dropped. At byte level its failure
is a keccak collision among the preimages of the triples the logged run hashed and the watched
triple: a non-vault call in the run leaves the watched route alone, or keccak collides there. -/
def Properties.LoggedRunNoHijackOrKeccakCollision : Prop :=
  ∀ (keccak : Keccak) (thisChain : AssetRouter.Chain) (ntv ntvAddr : AssetRouter.Address)
    (R₀ R : AssetRouter.Router) (log : List AssetRouter.Call),
    AssetRouter.ReachLog (routerEnc keccak) thisChain ntv ntvAddr R₀ R log →
    ∀ (pre post : List AssetRouter.Call) (c : AssetRouter.Call) (S T : AssetRouter.Router),
      log = pre ++ c :: post →
      AssetRouter.ReachLog (routerEnc keccak) thisChain ntv ntvAddr R₀ S pre →
      AssetRouter.StepCall (routerEnc keccak) thisChain ntv ntvAddr c S T → c.caller ≠ ntv →
    ∀ (s : AssetRouter.Address) (d' : AssetRouter.AssetData), s ≠ c.caller →
      T.handler (routerEnc keccak thisChain s d') = S.handler (routerEnc keccak thisChain s d')
      ∨ RouterIdBreakOn keccak
          ↑(insert (thisChain, s, d') (AssetRouter.loggedTriples thisChain ntv ntvAddr log))

/-- **THE VAULT'S ROUTES SURVIVE THE RUN, OR A KECCAK COLLISION AMONG ITS OWN PREIMAGES.**
`Contracts.AssetRouter.Properties.LoggedRunKeepsVaultRoutes` with its premise
`IdInjOn enc (loggedTriples log)` dropped: a vault registration in a logged run still
holds its handler and tracker at the end (when no later vault call re-registers the same
data), or keccak collides among the preimages of the triples the run's calls hashed. -/
def Properties.LoggedRunKeepsVaultRoutesOrKeccakCollision : Prop :=
  ∀ (keccak : Keccak) (thisChain : AssetRouter.Chain) (ntv ntvAddr : AssetRouter.Address)
    (R₀ R : AssetRouter.Router) (log : List AssetRouter.Call),
    AssetRouter.ReachLog (routerEnc keccak) thisChain ntv ntvAddr R₀ R log →
    ∀ (pre post : List AssetRouter.Call) (c : AssetRouter.Call), log = pre ++ c :: post →
      c.caller = ntv → (∀ c' ∈ post, c'.caller = ntv → c'.data ≠ c.data) →
      (R.handler (routerEnc keccak thisChain ntvAddr c.data) = c.handler
        ∧ R.tracker (routerEnc keccak thisChain ntvAddr c.data) = ntv)
      ∨ RouterIdBreakOn keccak ↑(AssetRouter.loggedTriples thisChain ntv ntvAddr log)

/-- **`LoggedRunNoHijackOrKeccakCollision`'S BREAK IS FALSE ON A NONTRIVIAL RUN.** A logged run
from the owner's whitelisting state, a non-vault call in it while the watched route is the
vault's and live, and no keccak collision among the run's preimages and the watched one, while
keccak does collide on a preimage of the log and one off it. So only collisions among the
named inputs matter. -/
def Properties.LoggedRunNoHijackOrKeccakCollisionWitness : Prop :=
  ∃ (keccak : Keccak) (thisChain : AssetRouter.Chain) (ntv ntvAddr : AssetRouter.Address)
    (R₀ R : AssetRouter.Router) (log pre post : List AssetRouter.Call) (c : AssetRouter.Call)
    (S T : AssetRouter.Router) (s : AssetRouter.Address) (d' : AssetRouter.AssetData),
    AssetRouter.ReachLog (routerEnc keccak) thisChain ntv ntvAddr R₀ R log
    ∧ log = pre ++ c :: post
    ∧ AssetRouter.ReachLog (routerEnc keccak) thisChain ntv ntvAddr R₀ S pre
    ∧ AssetRouter.StepCall (routerEnc keccak) thisChain ntv ntvAddr c S T
    ∧ c.caller ≠ ntv ∧ s ≠ c.caller
    ∧ ¬ RouterIdBreakOn keccak
        ↑(insert (thisChain, s, d') (AssetRouter.loggedTriples thisChain ntv ntvAddr log))
    ∧ (∃ d t, R₀ = AssetRouter.afterSetDeploymentTracker (routerEnc keccak) thisChain
        AssetRouter.empty d t)
    ∧ s = ntvAddr ∧ S.tracker (routerEnc keccak thisChain s d') = ntv
    ∧ S.handler (routerEnc keccak thisChain s d') ≠ 0
    ∧ ∃ p ∈ AssetRouter.loggedTriples thisChain ntv ntvAddr log, ∃ p',
        p' ∉ insert (thisChain, s, d') (AssetRouter.loggedTriples thisChain ntv ntvAddr log)
        ∧ HashCollision keccak (routerPreimage p.1 p.2.1 p.2.2) (routerPreimage p'.1 p'.2.1 p'.2.2)

/-- **`LoggedRunKeepsVaultRoutesOrKeccakCollision`'S BREAK IS FALSE ON A NONTRIVIAL RUN.** After
the vault's call come both a non-vault call and a vault call for other data, and keccak has no
collision among the run's preimages, while it collides on a preimage of the log and one off
it. -/
def Properties.LoggedRunKeepsVaultRoutesOrKeccakCollisionWitness : Prop :=
  ∃ (keccak : Keccak) (thisChain : AssetRouter.Chain) (ntv ntvAddr : AssetRouter.Address)
    (R₀ R : AssetRouter.Router) (log pre post : List AssetRouter.Call) (c : AssetRouter.Call),
    AssetRouter.ReachLog (routerEnc keccak) thisChain ntv ntvAddr R₀ R log
    ∧ ¬ RouterIdBreakOn keccak ↑(AssetRouter.loggedTriples thisChain ntv ntvAddr log)
    ∧ log = pre ++ c :: post ∧ c.caller = ntv
    ∧ (∀ c' ∈ post, c'.caller = ntv → c'.data ≠ c.data)
    ∧ (∃ d t, R₀ = AssetRouter.afterSetDeploymentTracker (routerEnc keccak) thisChain
        AssetRouter.empty d t)
    ∧ (∃ c' ∈ post, c'.caller = ntv) ∧ (∃ c' ∈ post, c'.caller ≠ ntv)
    ∧ ∃ p ∈ AssetRouter.loggedTriples thisChain ntv ntvAddr log, ∃ p',
        p' ∉ AssetRouter.loggedTriples thisChain ntv ntvAddr log
        ∧ HashCollision keccak (routerPreimage p.1 p.2.1 p.2.2) (routerPreimage p'.1 p'.2.1 p'.2.2)

/-- **ONE KECCAK COLLISION ON THE LOG TAKES A LIVE ROUTE OVER.** From the state the owner's
`setAssetDeploymentTracker(d', s)` leaves on fresh storage: `s` points its asset at a live
handler `h`, then the vault registers token data `d` (anyone can make it, through
`registerToken`), and keccak collides on the two preimages the run hashed:
`abi.encode(thisChain, ntvAddr, d)` and `abi.encode(thisChain, s, d')`. The vault's call
re-points `s`'s live route at the vault and records the vault as its tracker, so `s` can no
longer re-point its own asset. The collision is exactly the run's `RouterIdBreakOn` (last
conjunct), so the break disjunct of the run-level results describes a real takeover. -/
def Properties.KeccakCollisionOnLogTakesOverLiveRoute : Prop :=
  ∃ (keccak : Keccak) (thisChain : AssetRouter.Chain) (ntv ntvAddr s : AssetRouter.Address)
    (d d' : AssetRouter.AssetData) (h : AssetRouter.Address) (R₀ S R : AssetRouter.Router),
    s ≠ ntv ∧ s ≠ ntvAddr ∧ h ≠ 0 ∧ h ≠ ntv
    ∧ R₀ = AssetRouter.afterSetDeploymentTracker (routerEnc keccak) thisChain AssetRouter.empty d' s
    ∧ AssetRouter.ReachLog (routerEnc keccak) thisChain ntv ntvAddr R₀ S [⟨s, d', h⟩]
    ∧ S.handler (routerEnc keccak thisChain s d') = h
    ∧ AssetRouter.StepCall (routerEnc keccak) thisChain ntv ntvAddr ⟨ntv, d, ntv⟩ S R
    ∧ R.handler (routerEnc keccak thisChain s d') = ntv
    ∧ R.tracker (routerEnc keccak thisChain s d') = ntv
    ∧ ¬ AssetRouter.SetGuard (routerEnc keccak) thisChain ntv ntvAddr R s d'
    ∧ HashCollision keccak (routerPreimage thisChain ntvAddr d) (routerPreimage thisChain s d')
    ∧ RouterIdBreakOn keccak
        ↑(AssetRouter.loggedTriples thisChain ntv ntvAddr [⟨s, d', h⟩, ⟨ntv, d, ntv⟩])

/-! ## The vault registry -/

/-- **THE DERIVED ID IS FREE, OR A KECCAK EVENT ON NAMED PREIMAGES.**
`Contracts.NativeTokenVault.Properties.RegisterNativeIdFreshOrCollision` at byte level. Either
the id `_registerToken` computes for `t`, `encodeNTVAssetId(thisChain, t)`, is unregistered;
or keccak sends its preimage to zero; or the id is already registered and keccak collides on
the preimage of that asset's recorded (origin chain, origin token) pair and the preimage of
`(thisChain, t)`. -/
def Properties.RegisterNativeIdFreshOrKeccakEvent : Prop :=
  ∀ (keccak : Keccak) (thisChain : NativeTokenVault.Chain) (V : NativeTokenVault.Vault),
    NativeTokenVault.Valid (vaultEnc keccak) thisChain V →
    ∀ (t : NativeTokenVault.Address), NativeTokenVault.RegisterNativeGuard V t →
      ¬ NativeTokenVault.Registered V (vaultEnc keccak thisChain t)
      ∨ ZeroPreimage keccak (vaultPreimage thisChain t)
      ∨ (NativeTokenVault.Registered V (vaultEnc keccak thisChain t)
          ∧ HashCollision keccak
              (vaultPreimage (V.originChain (vaultEnc keccak thisChain t))
                (V.originToken (vaultEnc keccak thisChain t)))
              (vaultPreimage thisChain t))

/-- **ITS EVENT DISJUNCTS ARE NOT A TAUTOLOGY.** A valid vault with an asset registered, a second
token passing the guard, and both keccak-event disjuncts false. -/
def Properties.RegisterNativeIdFreshOrKeccakEventWitness : Prop :=
  ∃ (keccak : Keccak) (thisChain : NativeTokenVault.Chain) (V : NativeTokenVault.Vault)
    (t : NativeTokenVault.Address),
    NativeTokenVault.Valid (vaultEnc keccak) thisChain V
    ∧ (∃ a, NativeTokenVault.Registered V a) ∧ NativeTokenVault.RegisterNativeGuard V t
    ∧ ¬ ZeroPreimage keccak (vaultPreimage thisChain t)
    ∧ ¬ (NativeTokenVault.Registered V (vaultEnc keccak thisChain t)
          ∧ HashCollision keccak
              (vaultPreimage (V.originChain (vaultEnc keccak thisChain t))
                (V.originToken (vaultEnc keccak thisChain t)))
              (vaultPreimage thisChain t))

/-- **UNDER A KECCAK COLLISION THE DERIVED ID IS TAKEN.** A keccak, a valid vault and a token
passing the one-sided guard whose derived id is already registered, with keccak colliding on
the two named preimages. So without the event disjunct the freshness conclusion fails. -/
def Properties.RegisterNativeIdTakenByKeccakCollision : Prop :=
  ∃ (keccak : Keccak) (thisChain : NativeTokenVault.Chain) (V : NativeTokenVault.Vault)
    (t : NativeTokenVault.Address),
    NativeTokenVault.Valid (vaultEnc keccak) thisChain V
    ∧ NativeTokenVault.RegisterNativeGuard V t
    ∧ NativeTokenVault.Registered V (vaultEnc keccak thisChain t)
    ∧ HashCollision keccak
        (vaultPreimage (V.originChain (vaultEnc keccak thisChain t))
          (V.originToken (vaultEnc keccak thisChain t)))
        (vaultPreimage thisChain t)

/-- **THE VAULT'S RUN-LEVEL HEADLINE, OR A KECCAK EVENT AMONG ITS OWN PREIMAGES.**
`Contracts.NativeTokenVault.Properties.LoggedRunSound` with its premise
`IdAssumptionsOn e (registeredPairs log)` dropped. Every logged run from fresh storage ends in
a state where:

* the registry is `Valid`, and the audit is consistent;
* the vault is solvent for every asset;
* for a native asset, the total bridged in never exceeds the total bridged out;
* every registered asset's pair is one the run hashed.

Otherwise keccak collides on two preimages of pairs the run's registrations hashed, or sends
one of them to zero. -/
def Properties.LoggedRunSoundOrKeccakEvent : Prop :=
  ∀ (keccak : Keccak) (thisChain : NativeTokenVault.Chain), thisChain ≠ 0 →
    ∀ (W : NativeTokenVault.World) (log : List NativeTokenVault.Op),
      NativeTokenVault.ReachLog (vaultEnc keccak) thisChain NativeTokenVault.empty W log →
        (NativeTokenVault.Valid (vaultEnc keccak) thisChain W.vault
          ∧ NativeTokenVault.Audited thisChain W
          ∧ (∀ a, W.vault.bridgedOut a ≤ W.vault.escrowed a)
          ∧ (∀ a, NativeTokenVault.Native thisChain W.vault a → W.audit.totalIn a ≤ W.audit.totalOut a)
          ∧ NativeTokenVault.PairsIn ↑(NativeTokenVault.registeredPairs thisChain log) W.vault)
        ∨ VaultIdBreakOn keccak ↑(NativeTokenVault.registeredPairs thisChain log)

/-- **ITS EVENT DISJUNCT IS FALSE ON A NONTRIVIAL RUN.** A logged run from fresh storage that
registers two pairs, with a native asset that was bridged both out and in, and no keccak event
among the run's preimages. -/
def Properties.LoggedRunSoundOrKeccakEventWitness : Prop :=
  ∃ (keccak : Keccak) (thisChain : NativeTokenVault.Chain) (W : NativeTokenVault.World)
    (log : List NativeTokenVault.Op),
    thisChain ≠ 0
    ∧ NativeTokenVault.ReachLog (vaultEnc keccak) thisChain NativeTokenVault.empty W log
    ∧ ¬ VaultIdBreakOn keccak ↑(NativeTokenVault.registeredPairs thisChain log)
    ∧ 2 ≤ (NativeTokenVault.registeredPairs thisChain log).card
    ∧ ∃ a, NativeTokenVault.Registered W.vault a ∧ NativeTokenVault.Native thisChain W.vault a
      ∧ W.audit.totalOut a ≠ 0 ∧ W.audit.totalIn a ≠ 0

/-- **UNDER A KECCAK COLLISION ON THE RUN'S PREIMAGES THE REGISTRY BREAKS.** A keccak that collides
on the preimages of the pairs `(1, 1)` and `(1, 2)`, and the logged run that registers token `1`
and then token `2` natively on chain `1`. The second registration passes the one-sided guard
(`assetId[token] == 0` for the new token only) and overwrites the first's `tokenAddress` entry.
So the registry is not `Valid` at the end: token `1` still maps to the shared id, which now
maps to token `2`. The run's `VaultIdBreakOn` holds, so `LoggedRunSoundOrKeccakEvent`'s event
disjunct cannot be dropped. -/
def Properties.LoggedRunSoundEventNeeded : Prop :=
  ∃ (keccak : Keccak) (W : NativeTokenVault.World),
    NativeTokenVault.ReachLog (vaultEnc keccak) 1 NativeTokenVault.empty W
      [.registerNative 1, .registerNative 2]
    ∧ ¬ NativeTokenVault.Valid (vaultEnc keccak) 1 W.vault
    ∧ HashCollision keccak (vaultPreimage 1 1) (vaultPreimage 1 2)
    ∧ VaultIdBreakOn keccak
        ↑(NativeTokenVault.registeredPairs 1 [.registerNative 1, .registerNative 2])

end Contracts.DataEncoding
