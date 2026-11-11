import EraSpec.Contracts.DataEncoding.Specs.AssetId
import EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecovery

/-!
# Properties: asset ids at byte level

Statements about `EraSpec.Contracts.DataEncoding.Specs.AssetId`. Proofs are in
`EraSpec.Contracts.DataEncoding.Proofs.AssetId`.

None of these takes a premise on keccak. Groups, in order:

* **Bytes.** The ABI head of an address is the word of its zero extension
  (`AddressWordIsWidenedWord`), and every preimage is 96 bytes.
* **(a) Injectivity of the preimages.** The encoding contributes no collision of its own.
* **(c) The overloads coincide, by byte equality.** Both `encodeAssetId` overloads, both
  `encodeNTVAssetId` overloads and the router's registration of a vault token compute the
  same keccak input, so they agree for EVERY keccak, not up to collision. The model
  instances are the library on real addresses, and the vault's instance is the router's with
  the vault as sender, which is the identity `AtomicRecovery.ntvId` builds in.
* **(b), (d) The bounded premises at byte level.** `IdInjOn (routerEnc keccak) S` is exactly
  the absence of a keccak collision among the preimages of `S`. `IdAssumptionsOn
  (vaultEnc keccak) S` is exactly the absence of such a collision and of a zero preimage.
  Each failure names its inputs.
* **(e) `assetIdCheck`.** It passes exactly on the vault id of the origin pair, which is
  the registry model's `idChecked` guard; two passing checks for one id name the same origin
  pair or a keccak collision on the two named preimages.
* **Non-vacuity.** Every abstract router or vault encoding is `routerEnc keccak` or
  `vaultEnc keccak` for some keccak, so nothing is lost by specialising; the no-break
  premises are satisfiable on every set the id space can hold; and the breaks are contingent
  (some keccak has them, some does not).
-/

namespace Contracts.DataEncoding

open AttackVectors.BundleHashEncoding (HashCollision)

/-! ## Bytes -/

/-- **THE ABI HEAD OF AN ADDRESS IS THE WORD OF ITS ZERO EXTENSION.** Twelve zero bytes and
the 20 address bytes are the 32 big-endian bytes of `bytes32(uint256(uint160(t)))`. Every
overload identity below rests on this. -/
def Properties.AddressWordIsWidenedWord : Prop :=
  ∀ t : Addr, encAddr t = encWord (addrAsBytes32 t)

/-- **EVERY ASSET-ID PREIMAGE IS 96 BYTES**: three 32-byte heads and no tail, for the library's
two preimages and for the two model instances. -/
def Properties.AssetIdPreimageLength : Prop :=
  (∀ (c : UInt256) (s : Addr) (d : UInt256), (assetIdPreimage c s d).length = 96)
  ∧ (∀ (c : UInt256) (s t : Addr), (assetIdPreimageOfToken c s t).length = 96)
  ∧ (∀ c s d : UInt256, (routerPreimage c s d).length = 96)
  ∧ (∀ c t : UInt256, (vaultPreimage c t).length = 96)

/-! ## (a) The preimages determine their arguments -/

/-- **(a) THE ASSET-ID PREIMAGE DETERMINES CHAIN, SENDER AND DATA.** Equal
`abi.encode(_chainId, _sender, _assetData)` bytes force equal arguments. So two distinct
argument triples get distinct ids unless keccak collides on two distinct byte strings; the
encoding adds no collision. No premise: every argument is a fixed-width value of its type. -/
def Properties.AssetIdPreimageInjective : Prop :=
  ∀ (c c' : UInt256) (s s' : Addr) (d d' : UInt256),
    assetIdPreimage c s d = assetIdPreimage c' s' d' → c = c' ∧ s = s' ∧ d = d'

/-- **(a) THE SAME FOR THE `address` OVERLOAD**, `abi.encode(_chainId, _sender, _tokenAddress)`. -/
def Properties.AssetIdPreimageOfTokenInjective : Prop :=
  ∀ (c c' : UInt256) (s s' t t' : Addr),
    assetIdPreimageOfToken c s t = assetIdPreimageOfToken c' s' t' → c = c' ∧ s = s' ∧ t = t'

/-- **(a) THE ROUTER MODEL'S PREIMAGE DETERMINES ITS TRIPLE**, for every triple of words,
including model "addresses" above `2^160`. -/
def Properties.RouterPreimageInjective : Prop :=
  ∀ c c' s s' d d' : UInt256,
    routerPreimage c s d = routerPreimage c' s' d' → c = c' ∧ s = s' ∧ d = d'

/-- **(a) THE VAULT MODEL'S PREIMAGE DETERMINES ITS PAIR.** -/
def Properties.VaultPreimageInjective : Prop :=
  ∀ c c' t t' : UInt256, vaultPreimage c t = vaultPreimage c' t' → c = c' ∧ t = t'

/-! ## (c) The overloads coincide, by byte equality -/

/-- **(c) THE TWO PREIMAGES ARE THE SAME BYTES.** `abi.encode(c, s, t)` with `t : address`
and `abi.encode(c, s, bytes32(uint256(uint160(t))))` are one byte string. -/
def Properties.OverloadPreimagesCoincide : Prop :=
  ∀ (c : UInt256) (s t : Addr), assetIdPreimageOfToken c s t = assetIdPreimage c s (addrAsBytes32 t)

/-- **(c) THE TWO `encodeAssetId` OVERLOADS COINCIDE** (`DataEncoding.sol:126-128` and
`:135-137`): `encodeAssetId(c, t, s) = encodeAssetId(c, bytes32(uint256(uint160(t))), s)` for
every keccak, because the keccak inputs are equal. -/
def Properties.EncodeAssetIdOverloadsCoincide : Prop :=
  ∀ (keccak : Keccak) (c : UInt256) (t s : Addr),
    encodeAssetIdOfToken keccak c t s = encodeAssetId keccak c (addrAsBytes32 t) s

/-- **(c) THE VAULT'S ID IS THE ROUTER'S ID WITH THE VAULT AS SENDER.** Both
`encodeNTVAssetId` overloads (`DataEncoding.sol:143-145`, `:151-153`) are `encodeAssetId`
with sender `L2_NATIVE_TOKEN_VAULT_ADDR`:

* `encodeNTVAssetId(c, t) = encodeAssetId(c, bytes32(uint256(uint160(t))), L2_NTV)` for an
  `address t`;
* `encodeNTVAssetId(c, d) = encodeAssetId(c, d, L2_NTV)` for a `bytes32 d`.

For every keccak: an identity of bytes, not an equality up to collision. -/
def Properties.OverloadsCoincide : Prop :=
  ∀ (keccak : Keccak) (c : UInt256),
    (∀ t : Addr, encodeNTVAssetIdOfToken keccak c t = encodeAssetId keccak c (addrAsBytes32 t) l2NtvAddr)
    ∧ (∀ d : UInt256, encodeNTVAssetId keccak c d = encodeAssetId keccak c d l2NtvAddr)

/-- **NATIVE REGISTRATION KEYS THE VAULT AND THE ROUTER BY ONE ID.** On chain `c`,
`_unsafeRegisterNativeToken(t)` (`NativeTokenVaultBase.sol:515-522`) stores the token under
`encodeNTVAssetId(c, t)` and calls the router with data `bytes32(uint256(uint160(t)))`. The
router's caller is the vault `ntv`, so it hashes the sender as `L2_NATIVE_TOKEN_VAULT_ADDR`
(`AssetRouterBase.sol:78-80`). Here that is the router model's `writtenId` for the caller
`ntv`, with `routerEnc keccak` and the normalised vault address `widen L2_NTV`. The two ids
are equal for every keccak and every vault address `ntv`. -/
def Properties.NativeRegistrationIdsAgree : Prop :=
  ∀ (keccak : Keccak) (c : UInt256) (ntv : AssetRouter.Address) (t : Addr),
    AssetRouter.writtenId (routerEnc keccak) c ntv (addrAsBytes32 l2NtvAddr) ntv (addrAsBytes32 t)
      = encodeNTVAssetIdOfToken keccak c t

/-- **THE ROUTER MODEL'S INSTANCE IS THE LIBRARY ON REAL ADDRESSES.** For a 160-bit sender,
`routerEnc keccak c (widen s) d` is `encodeAssetId(c, d, s)` (`DataEncoding.sol:126-128`). -/
def Properties.RouterModelIsLibrary : Prop :=
  ∀ (keccak : Keccak) (c : UInt256) (s : Addr) (d : UInt256),
    routerEnc keccak c (addrAsBytes32 s) d = encodeAssetId keccak c d s

/-- **THE VAULT MODEL'S INSTANCE IS THE LIBRARY ON REAL TOKENS.** For a 160-bit token,
`vaultEnc keccak c (widen t)` is `encodeNTVAssetId(c, t)` (`DataEncoding.sol:151-153`), the id
`_unsafeRegisterNativeToken` and `assetIdCheck` compute. -/
def Properties.VaultModelIsLibrary : Prop :=
  ∀ (keccak : Keccak) (c : UInt256) (t : Addr),
    vaultEnc keccak c (addrAsBytes32 t) = encodeNTVAssetIdOfToken keccak c t

/-- **THE `ntvId` IDENTITY HOLDS AT BYTE LEVEL.** `AssetRouterBase/Specs/AtomicRecovery.lean`
defines the vault's id from the router's encoding, `ntvId enc cfg c t = enc c cfg.ntv t`, as a
model choice. At byte level it is a theorem: with the vault's configured address the
normalised `L2_NATIVE_TOKEN_VAULT_ADDR` (`L2AssetRouter.sol:72-74` on an L2),
`ntvId (routerEnc keccak) cfg` is the vault model's instance `vaultEnc keccak`, on every pair of
words. -/
def Properties.VaultModelIsRouterModelAtNtv : Prop :=
  ∀ (keccak : Keccak) (cfg : AssetRouter.AtomicRecovery.Config),
    cfg.ntv = addrAsBytes32 l2NtvAddr →
      AssetRouter.AtomicRecovery.ntvId (routerEnc keccak) cfg = vaultEnc keccak

/-- **ITS PREMISE IS SATISFIABLE**: a configuration whose vault address is the normalised
`L2_NATIVE_TOKEN_VAULT_ADDR`, as on every L2. -/
def Properties.VaultModelIsRouterModelAtNtvWitness : Prop :=
  ∃ cfg : AssetRouter.AtomicRecovery.Config, cfg.ntv = addrAsBytes32 l2NtvAddr

/-! ## (b), (d) The bounded premises at byte level -/

/-- **(b) THE ROUTER'S BOUNDED PREMISE IS "NO NAMED KECCAK COLLISION".** At byte level,
`IdInjOn (routerEnc keccak) S`, the premise of `NoHijackOn`, `NtvTouchesOnlyItsOwnIdsOn` and
the logged-run results, holds exactly when keccak has no collision among the preimages of
the triples of `S`. -/
def Properties.RouterIdInjOnIffNoCollision : Prop :=
  ∀ (keccak : Keccak) (S : Set (AssetRouter.Chain × AssetRouter.Address × AssetRouter.AssetData)),
    AssetRouter.IdInjOn (routerEnc keccak) S ↔ ¬ RouterIdBreakOn keccak S

/-- **(b) NO NAMED COLLISION GIVES `IdInjOn`.** The direction a caller of the router's bounded
results needs: to discharge `IdInjOn (routerEnc keccak) S` it suffices that keccak does not
collide on the preimages of `S`. -/
def Properties.IdInjOnOfNoCollision : Prop :=
  ∀ (keccak : Keccak) (S : Set (AssetRouter.Chain × AssetRouter.Address × AssetRouter.AssetData)),
    ¬ RouterIdBreakOn keccak S → AssetRouter.IdInjOn (routerEnc keccak) S

/-- **(b), CONVERSE, PER PAIR: A ROUTER ID CLASH IS A NAMED KECCAK COLLISION.** Two distinct
triples with one id give a keccak collision on exactly their two preimages. -/
def Properties.RouterIdClashIsNamedCollision : Prop :=
  ∀ (keccak : Keccak) (p q : AssetRouter.Chain × AssetRouter.Address × AssetRouter.AssetData),
    p ≠ q → routerEnc keccak p.1 p.2.1 p.2.2 = routerEnc keccak q.1 q.2.1 q.2.2 →
      HashCollision keccak (routerPreimage p.1 p.2.1 p.2.2) (routerPreimage q.1 q.2.1 q.2.2)

/-- **(b), (d) THE VAULT'S BOUNDED PREMISE IS "NO NAMED KECCAK EVENT".** At byte level,
`IdAssumptionsOn (vaultEnc keccak) S`, the premise of `RunValidOn`, `SolvencyOn`,
`NoInflationOn` and `LoggedRunSound`, holds exactly when keccak neither collides on two
preimages of pairs of `S` nor sends one of them to zero. -/
def Properties.VaultIdAssumptionsOnIffNoKeccakEvent : Prop :=
  ∀ (keccak : Keccak) (S : Set (NativeTokenVault.Chain × NativeTokenVault.Address)),
    NativeTokenVault.IdAssumptionsOn (vaultEnc keccak) S ↔ ¬ VaultIdBreakOn keccak S

/-- **(b), CONVERSE, PER PAIR: A VAULT ID CLASH IS A NAMED KECCAK COLLISION.** -/
def Properties.VaultIdClashIsNamedCollision : Prop :=
  ∀ (keccak : Keccak) (p q : NativeTokenVault.Chain × NativeTokenVault.Address),
    p ≠ q → vaultEnc keccak p.1 p.2 = vaultEnc keccak q.1 q.2 →
      HashCollision keccak (vaultPreimage p.1 p.2) (vaultPreimage q.1 q.2)

/-- **(d) A ZERO ID IS A PREIMAGE EVENT ON THE NAMED PREIMAGE.** The `nonzero` fields of the
router's and the vault's assumptions fail at an argument exactly when keccak sends that
argument's 96-byte preimage to the zero word. Finding such a preimage is a preimage attack on a
fixed value, a different event from a collision. -/
def Properties.NonzeroIsPreimageEvent : Prop :=
  ∀ (keccak : Keccak),
    (∀ c t : UInt256, vaultEnc keccak c t = 0 ↔ ZeroPreimage keccak (vaultPreimage c t))
    ∧ (∀ c s d : UInt256, routerEnc keccak c s d = 0 ↔ ZeroPreimage keccak (routerPreimage c s d))

/-- **(d) NO COLLISION DOES NOT GIVE NONZERO.** There is a keccak and a two-pair set on which
the vault id is injective (keccak has no collision among the two preimages) while one id is
zero, so `IdAssumptionsOn` fails. So the zero-preimage disjunct of `VaultIdBreakOn` cannot
be dropped: `nonzero` is a separate, preimage-type premise. -/
def Properties.ZeroPreimageIndependentOfCollisions : Prop :=
  ∃ (keccak : Keccak) (S : Set (NativeTokenVault.Chain × NativeTokenVault.Address)),
    (¬ ∃ p ∈ S, ∃ q ∈ S, HashCollision keccak (vaultPreimage p.1 p.2) (vaultPreimage q.1 q.2))
    ∧ (∀ p ∈ S, ∀ q ∈ S, vaultEnc keccak p.1 p.2 = vaultEnc keccak q.1 q.2 → p = q)
    ∧ (∃ p ∈ S, ZeroPreimage keccak (vaultPreimage p.1 p.2))
    ∧ ¬ NativeTokenVault.IdAssumptionsOn (vaultEnc keccak) S

/-! ## (e) `assetIdCheck` -/

/-- **(e) `assetIdCheck` PASSES EXACTLY ON THE VAULT ID OF THE ORIGIN PAIR.**
`assetIdCheck(c, a, t)` returns iff `a = encodeNTVAssetId(c, t)`, and reverts otherwise. -/
def Properties.AssetIdCheckPassesIff : Prop :=
  ∀ (keccak : Keccak) (c a : UInt256) (t : Addr),
    assetIdCheck keccak c a t = some () ↔ a = encodeNTVAssetIdOfToken keccak c t

/-- **(e) `assetIdCheck` IS THE REGISTRY MODEL'S `idChecked` GUARD.** With the byte-level vault
encoding, the check passes iff `a = vaultEnc keccak c (widen t)`, which is
`RegisterBridgedGuard.idChecked` (`Specs/RegistryAndEscrow.lean`) for origin chain `c` and
origin token `widen t`. -/
def Properties.AssetIdCheckIsRegistryIdCheck : Prop :=
  ∀ (keccak : Keccak) (c a : UInt256) (t : Addr),
    assetIdCheck keccak c a t = some () ↔ a = vaultEnc keccak c (addrAsBytes32 t)

/-- **(e) THE ID `assetIdCheck` ACCEPTS IS THE ONE THE ORIGIN CHAIN'S ROUTER KEYED.** The check
on a destination passes for `(c, a, t)` iff `a` is the id the router of chain `c` writes when
that chain's vault registers `t` natively: `encodeAssetId(c, bytes32(uint256(uint160(t))),
L2_NATIVE_TOKEN_VAULT_ADDR)`. -/
def Properties.AssetIdCheckPassesIffRouterId : Prop :=
  ∀ (keccak : Keccak) (c a : UInt256) (t : Addr),
    assetIdCheck keccak c a t = some () ↔ a = encodeAssetId keccak c (addrAsBytes32 t) l2NtvAddr

/-- **(e) ONE ID, ONE ORIGIN PAIR, OR A NAMED COLLISION.** If `assetIdCheck` passes for one id
`a` with origin pairs `(c, t)` and `(c', t')`, the pairs are equal, or keccak collides on their
two preimages. So a bridged registration's id determines its origin chain and token unless
keccak collides on those two named byte strings. -/
def Properties.AssetIdCheckPinsOriginOrCollision : Prop :=
  ∀ (keccak : Keccak) (a c c' : UInt256) (t t' : Addr),
    assetIdCheck keccak c a t = some () → assetIdCheck keccak c' a t' = some () →
      (c = c' ∧ t = t')
      ∨ HashCollision keccak (assetIdPreimageOfToken c l2NtvAddr t)
          (assetIdPreimageOfToken c' l2NtvAddr t')

/-- **(e) THE PIN IS NOT A TAUTOLOGY, AND THE COLLISION DISJUNCT CANNOT BE DROPPED.**
* There is a keccak and two distinct origin pairs on whose preimages keccak does not collide,
  and `assetIdCheck` accepts the first pair's id for the first pair and rejects it for the
  second.
* There is a keccak and two distinct origin pairs for which `assetIdCheck` accepts one id for
  both; keccak then collides on the two named preimages. -/
def Properties.AssetIdCheckPinWitness : Prop :=
  (∃ (keccak : Keccak) (c c' : UInt256) (t t' : Addr),
      ¬ (c = c' ∧ t = t')
      ∧ ¬ HashCollision keccak (assetIdPreimageOfToken c l2NtvAddr t)
            (assetIdPreimageOfToken c' l2NtvAddr t')
      ∧ assetIdCheck keccak c (encodeNTVAssetIdOfToken keccak c t) t = some ()
      ∧ assetIdCheck keccak c' (encodeNTVAssetIdOfToken keccak c t) t' = none)
  ∧ (∃ (keccak : Keccak) (a c c' : UInt256) (t t' : Addr),
      ¬ (c = c' ∧ t = t')
      ∧ assetIdCheck keccak c a t = some () ∧ assetIdCheck keccak c' a t' = some ()
      ∧ HashCollision keccak (assetIdPreimageOfToken c l2NtvAddr t)
          (assetIdPreimageOfToken c' l2NtvAddr t'))

/-! ## Non-vacuity -/

/-- **EVERY ABSTRACT ROUTER ENCODING IS A KECCAK INSTANCE.** For every `enc : AssetIdOf` there
is a keccak with `routerEnc keccak = enc`. So specialising the router model to byte level
loses no generality: each abstract result and countermodel applies to some keccak. (The
preimage has a left inverse, so any function of the triple factors through it.) -/
def Properties.RouterEncodingsAreKeccakInstances : Prop :=
  ∀ enc : AssetRouter.AssetIdOf, ∃ keccak : Keccak, routerEnc keccak = enc

/-- **EVERY ABSTRACT VAULT ENCODING IS A KECCAK INSTANCE.** -/
def Properties.VaultEncodingsAreKeccakInstances : Prop :=
  ∀ e : NativeTokenVault.NtvAssetId, ∃ keccak : Keccak, vaultEnc keccak = e

/-- **NO ROUTER BREAK IS SATISFIABLE ON ANY SET THE ID SPACE CAN HOLD.** For every finite set of
at most `2^256` triples some keccak has no collision among their preimages. -/
def Properties.RouterNoBreakSatisfiable : Prop :=
  ∀ S : Finset (AssetRouter.Chain × AssetRouter.Address × AssetRouter.AssetData),
    S.card ≤ UInt256.size → ∃ keccak : Keccak, ¬ RouterIdBreakOn keccak ↑S

/-- **NO VAULT EVENT IS SATISFIABLE ON ANY SET THE NONZERO IDS CAN HOLD.** For every finite set of
fewer than `2^256` pairs some keccak neither collides on their preimages nor sends one to
zero. -/
def Properties.VaultNoBreakSatisfiable : Prop :=
  ∀ S : Finset (NativeTokenVault.Chain × NativeTokenVault.Address),
    S.card < UInt256.size → ∃ keccak : Keccak, ¬ VaultIdBreakOn keccak ↑S

/-- **THE BREAKS ARE CONTINGENT.** For any two distinct router triples, some keccak collides on
their preimages and some does not; for any vault pair, some keccak sends its preimage to zero
and some keccak has no event on it. So neither predicate is a tautology or a contradiction on
a named set. -/
def Properties.IdBreaksAreContingent : Prop :=
  (∀ p q : AssetRouter.Chain × AssetRouter.Address × AssetRouter.AssetData, p ≠ q →
      (∃ keccak : Keccak, RouterIdBreakOn keccak {p, q})
      ∧ ∃ keccak : Keccak, ¬ RouterIdBreakOn keccak {p, q})
  ∧ (∀ p : NativeTokenVault.Chain × NativeTokenVault.Address,
      (∃ keccak : Keccak, VaultIdBreakOn keccak {p})
      ∧ ∃ keccak : Keccak, ¬ VaultIdBreakOn keccak {p})

end Contracts.DataEncoding
