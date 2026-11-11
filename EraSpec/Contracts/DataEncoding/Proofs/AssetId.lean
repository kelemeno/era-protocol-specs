import EraSpec.Contracts.DataEncoding.Properties.AssetId
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashPinned
import EraSpec.Contracts.AssetRouterBase.Proofs.HandlerRegistration
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.RegistryAndEscrow

/-!
# Proofs: asset ids at byte level

One byte fact carries the overload results: `toBytesBE 32 t` is 12 zero bytes followed by
`toBytesBE 20 t` when `t < 2^160` (`assetId_toBytesBE_add`, `assetId_toBytesBE_zero`). The
injectivity results split a preimage into its three 32-byte words with `List.append_inj` and
read each word back (`word_val_inj`). The bounded-premise results are the usual case split: two
ids are equal and the triples differ, so the preimages differ, which is a collision on those
two named byte strings. The instance results build keccak from the abstract encoding and a
left inverse of the preimage (`assetIdReadWord`).
-/

namespace Contracts.DataEncoding

open AttackVectors.BundleHashEncoding (toBytesBE fromBytesBE word HashCollision word_length
  word_val_inj uint256_val_lt toUInt256_val length_toBytesBE fromBytesBE_toBytesBE
  injOn_pair_iff_no_collision)

/-! ## Byte-level facts -/

/-- Splitting a big-endian string: the high `m` bytes hold `n / 256^k`, the low `k` bytes `n`. -/
theorem assetId_toBytesBE_add (m : ℕ) : ∀ (k n : ℕ),
    toBytesBE (m + k) n = toBytesBE m (n / 256 ^ k) ++ toBytesBE k n
  | 0, n => by simp [toBytesBE]
  | k + 1, n => by
      rw [← Nat.add_assoc, toBytesBE, assetId_toBytesBE_add m k (n / 256), toBytesBE,
        Nat.div_div_eq_div_mul, ← pow_succ', List.append_assoc]

/-- Zero is all zero bytes. -/
theorem assetId_toBytesBE_zero : ∀ m : ℕ, toBytesBE m 0 = List.replicate m 0
  | 0 => rfl
  | m + 1 => by
      rw [toBytesBE, Nat.zero_div, assetId_toBytesBE_zero m, List.replicate_succ']
      rfl

theorem encWord_length (w : UInt256) : (encWord w).length = 32 := word_length _

theorem encAddr_length (a : Addr) : (encAddr a).length = 32 := by
  simp [encAddr, length_toBytesBE]

theorem addrAsBytes32_val (t : Addr) : (addrAsBytes32 t).val = t.val := rfl

/-- **The ABI head of an address is the word of its zero extension.** -/
theorem encAddr_eq_encWord (t : Addr) : encAddr t = encWord (addrAsBytes32 t) := by
  have ht : t.val / 256 ^ 20 = 0 := Nat.div_eq_of_lt (lt_of_lt_of_eq t.isLt (by norm_num))
  show List.replicate 12 0 ++ toBytesBE 20 t.val = toBytesBE (12 + 20) t.val
  rw [assetId_toBytesBE_add, ht, assetId_toBytesBE_zero]

theorem encWord_inj {x y : UInt256} (h : encWord x = encWord y) : x = y := word_val_inj h

theorem addrAsBytes32_inj {a b : Addr} (h : addrAsBytes32 a = addrAsBytes32 b) : a = b :=
  Fin.ext (by simpa [addrAsBytes32_val] using congrArg Fin.val h)

theorem encAddr_inj {a b : Addr} (h : encAddr a = encAddr b) : a = b := by
  rw [encAddr_eq_encWord, encAddr_eq_encWord] at h
  exact addrAsBytes32_inj (encWord_inj h)

/-- Split three 32-byte heads. -/
theorem assetId_three_heads {x y z x' y' z' : List UInt8} (hx : x.length = 32)
    (hy : y.length = 32) (hx' : x'.length = 32) (hy' : y'.length = 32)
    (h : x ++ y ++ z = x' ++ y' ++ z') : x = x' ∧ y = y' ∧ z = z' := by
  obtain ⟨hxy, hz⟩ := List.append_inj h (by simp [hx, hy, hx', hy'])
  obtain ⟨hx2, hy2⟩ := List.append_inj hxy (by rw [hx, hx'])
  exact ⟨hx2, hy2, hz⟩

/-! ## Lengths and injectivity -/

theorem assetIdPreimage_length (c : UInt256) (s : Addr) (d : UInt256) :
    (assetIdPreimage c s d).length = 96 := by
  simp [assetIdPreimage, encWord_length, encAddr_length]

theorem assetIdPreimageOfToken_length (c : UInt256) (s t : Addr) :
    (assetIdPreimageOfToken c s t).length = 96 := by
  simp [assetIdPreimageOfToken, encWord_length, encAddr_length]

theorem routerPreimage_length (c s d : UInt256) : (routerPreimage c s d).length = 96 := by
  simp [routerPreimage, encWord_length]

theorem vaultPreimage_length (c t : UInt256) : (vaultPreimage c t).length = 96 := by
  simp [vaultPreimage, encWord_length, encAddr_length]

theorem assetIdPreimage_inj {c c' : UInt256} {s s' : Addr} {d d' : UInt256}
    (h : assetIdPreimage c s d = assetIdPreimage c' s' d') : c = c' ∧ s = s' ∧ d = d' := by
  obtain ⟨h1, h2, h3⟩ := assetId_three_heads (encWord_length _) (encAddr_length _)
    (encWord_length _) (encAddr_length _) h
  exact ⟨encWord_inj h1, encAddr_inj h2, encWord_inj h3⟩

theorem assetIdPreimageOfToken_inj {c c' : UInt256} {s s' t t' : Addr}
    (h : assetIdPreimageOfToken c s t = assetIdPreimageOfToken c' s' t') :
    c = c' ∧ s = s' ∧ t = t' := by
  obtain ⟨h1, h2, h3⟩ := assetId_three_heads (encWord_length _) (encAddr_length _)
    (encWord_length _) (encAddr_length _) h
  exact ⟨encWord_inj h1, encAddr_inj h2, encAddr_inj h3⟩

theorem routerPreimage_inj {c c' s s' d d' : UInt256}
    (h : routerPreimage c s d = routerPreimage c' s' d') : c = c' ∧ s = s' ∧ d = d' := by
  obtain ⟨h1, h2, h3⟩ := assetId_three_heads (encWord_length _) (encWord_length _)
    (encWord_length _) (encWord_length _) h
  exact ⟨encWord_inj h1, encWord_inj h2, encWord_inj h3⟩

theorem vaultPreimage_inj {c c' t t' : UInt256} (h : vaultPreimage c t = vaultPreimage c' t') :
    c = c' ∧ t = t' := by
  obtain ⟨h1, -, h3⟩ := assetId_three_heads (encWord_length _) (encAddr_length _)
    (encWord_length _) (encAddr_length _) h
  exact ⟨encWord_inj h1, encWord_inj h3⟩

/-- The router preimage as a function of the triple is injective. -/
theorem routerPreimage_triple_inj {p q : AssetRouter.Chain × AssetRouter.Address × AssetRouter.AssetData}
    (h : routerPreimage p.1 p.2.1 p.2.2 = routerPreimage q.1 q.2.1 q.2.2) : p = q := by
  obtain ⟨h1, h2, h3⟩ := routerPreimage_inj h
  obtain ⟨p1, p2, p3⟩ := p
  obtain ⟨q1, q2, q3⟩ := q
  simp only at h1 h2 h3
  rw [h1, h2, h3]

theorem vaultPreimage_pair_inj {p q : NativeTokenVault.Chain × NativeTokenVault.Address}
    (h : vaultPreimage p.1 p.2 = vaultPreimage q.1 q.2) : p = q := by
  obtain ⟨h1, h2⟩ := vaultPreimage_inj h
  exact Prod.ext h1 h2

/-! ## The overloads -/

theorem overloadPreimages (c : UInt256) (s t : Addr) :
    assetIdPreimageOfToken c s t = assetIdPreimage c s (addrAsBytes32 t) := by
  rw [assetIdPreimageOfToken, assetIdPreimage, encAddr_eq_encWord t]

theorem routerPreimage_widen (c : UInt256) (s : Addr) (d : UInt256) :
    routerPreimage c (addrAsBytes32 s) d = assetIdPreimage c s d := by
  rw [routerPreimage, assetIdPreimage, encAddr_eq_encWord s]

theorem vaultPreimage_widen (c : UInt256) (t : Addr) :
    vaultPreimage c (addrAsBytes32 t) = assetIdPreimageOfToken c l2NtvAddr t := by
  rw [vaultPreimage, assetIdPreimageOfToken, encAddr_eq_encWord t]

theorem vaultPreimage_eq_routerPreimage (c t : UInt256) :
    vaultPreimage c t = routerPreimage c (addrAsBytes32 l2NtvAddr) t := by
  rw [vaultPreimage, routerPreimage, encAddr_eq_encWord l2NtvAddr]

/-! ## The bounded premises -/

theorem routerId_clash {keccak : Keccak}
    {p q : AssetRouter.Chain × AssetRouter.Address × AssetRouter.AssetData} (hpq : p ≠ q)
    (h : routerEnc keccak p.1 p.2.1 p.2.2 = routerEnc keccak q.1 q.2.1 q.2.2) :
    HashCollision keccak (routerPreimage p.1 p.2.1 p.2.2) (routerPreimage q.1 q.2.1 q.2.2) :=
  ⟨fun he => hpq (routerPreimage_triple_inj he), h⟩

theorem vaultId_clash {keccak : Keccak} {p q : NativeTokenVault.Chain × NativeTokenVault.Address}
    (hpq : p ≠ q) (h : vaultEnc keccak p.1 p.2 = vaultEnc keccak q.1 q.2) :
    HashCollision keccak (vaultPreimage p.1 p.2) (vaultPreimage q.1 q.2) :=
  ⟨fun he => hpq (vaultPreimage_pair_inj he), h⟩

theorem routerIdInjOn_iff (keccak : Keccak)
    (S : Set (AssetRouter.Chain × AssetRouter.Address × AssetRouter.AssetData)) :
    AssetRouter.IdInjOn (routerEnc keccak) S ↔ ¬ RouterIdBreakOn keccak S := by
  constructor
  · rintro hinj ⟨p, hp, q, hq, hne, heq⟩
    have hpq : p = q := hinj p hp q hq heq
    subst hpq
    exact hne rfl
  · intro hno p hp q hq heq
    by_contra hpq
    exact hno ⟨p, hp, q, hq, routerId_clash hpq heq⟩

theorem vaultIdAssumptionsOn_iff (keccak : Keccak)
    (S : Set (NativeTokenVault.Chain × NativeTokenVault.Address)) :
    NativeTokenVault.IdAssumptionsOn (vaultEnc keccak) S ↔ ¬ VaultIdBreakOn keccak S := by
  constructor
  · rintro ⟨hinj, hnz⟩ (⟨p, hp, q, hq, hne, heq⟩ | ⟨p, hp, hz⟩)
    · have hpq : p = q := hinj p hp q hq heq
      subst hpq
      exact hne rfl
    · exact hnz p hp hz
  · intro hno
    refine ⟨fun p hp q hq heq => ?_, fun p hp hz => hno (Or.inr ⟨p, hp, hz⟩)⟩
    by_contra hpq
    exact hno (Or.inl ⟨p, hp, q, hq, vaultId_clash hpq heq⟩)

/-! ## `assetIdCheck` -/

theorem assetIdCheck_some_iff (keccak : Keccak) (c a : UInt256) (t : Addr) :
    assetIdCheck keccak c a t = some () ↔ a = encodeNTVAssetIdOfToken keccak c t := by
  unfold assetIdCheck
  split_ifs with h <;> simp [h]

theorem assetIdCheck_none_iff (keccak : Keccak) (c a : UInt256) (t : Addr) :
    assetIdCheck keccak c a t = none ↔ a ≠ encodeNTVAssetIdOfToken keccak c t := by
  unfold assetIdCheck
  split_ifs with h <;> simp [h]

theorem assetIdCheck_pins (keccak : Keccak) {a c c' : UInt256} {t t' : Addr}
    (h : assetIdCheck keccak c a t = some ()) (h' : assetIdCheck keccak c' a t' = some ()) :
    (c = c' ∧ t = t')
    ∨ HashCollision keccak (assetIdPreimageOfToken c l2NtvAddr t)
        (assetIdPreimageOfToken c' l2NtvAddr t') := by
  rw [assetIdCheck_some_iff] at h h'
  by_cases hpre : assetIdPreimageOfToken c l2NtvAddr t = assetIdPreimageOfToken c' l2NtvAddr t'
  · obtain ⟨hc, -, ht⟩ := assetIdPreimageOfToken_inj hpre
    exact Or.inl ⟨hc, ht⟩
  · exact Or.inr ⟨hpre, h.symm.trans h'⟩

/-! ## Keccak instances of the abstract encodings -/

/-- Reading the leading 32-byte word back as a `uint256`. -/
def assetIdReadWord (l : List UInt8) : UInt256 := Nat.toUInt256 (fromBytesBE (l.take 32))

theorem assetIdReadWord_encWord (w : UInt256) (l : List UInt8) :
    assetIdReadWord (encWord w ++ l) = w := by
  rw [assetIdReadWord, List.take_left' (encWord_length w), encWord,
    fromBytesBE_toBytesBE (uint256_val_lt w), toUInt256_val]

theorem routerPreimage_fields (c s d : UInt256) :
    assetIdReadWord (routerPreimage c s d) = c
    ∧ assetIdReadWord ((routerPreimage c s d).drop 32) = s
    ∧ assetIdReadWord ((routerPreimage c s d).drop 64) = d := by
  have h64 : (encWord c ++ encWord s).length = 64 := by simp [encWord_length]
  refine ⟨?_, ?_, ?_⟩
  · rw [routerPreimage, List.append_assoc, assetIdReadWord_encWord]
  · rw [routerPreimage, List.append_assoc, List.drop_left' (encWord_length c),
      assetIdReadWord_encWord]
  · rw [routerPreimage, List.drop_left' h64]
    simpa using assetIdReadWord_encWord d []

theorem vaultPreimage_fields (c t : UInt256) :
    assetIdReadWord (vaultPreimage c t) = c ∧ assetIdReadWord ((vaultPreimage c t).drop 64) = t := by
  have h64 : (encWord c ++ encAddr l2NtvAddr).length = 64 := by
    simp [encWord_length, encAddr_length]
  refine ⟨?_, ?_⟩
  · rw [vaultPreimage, List.append_assoc, assetIdReadWord_encWord]
  · rw [vaultPreimage, List.drop_left' h64]
    simpa using assetIdReadWord_encWord t []

/-- The keccak that realises a given router encoding: read the triple back, apply `enc`. -/
def keccakOfRouterEnc (enc : AssetRouter.AssetIdOf) : Keccak :=
  fun x => enc (assetIdReadWord x) (assetIdReadWord (x.drop 32)) (assetIdReadWord (x.drop 64))

/-- The keccak that realises a given vault encoding. -/
def keccakOfVaultEnc (e : NativeTokenVault.NtvAssetId) : Keccak :=
  fun x => e (assetIdReadWord x) (assetIdReadWord (x.drop 64))

theorem routerEnc_keccakOfRouterEnc (enc : AssetRouter.AssetIdOf) :
    routerEnc (keccakOfRouterEnc enc) = enc := by
  funext c s d
  obtain ⟨h1, h2, h3⟩ := routerPreimage_fields c s d
  simp only [routerEnc, keccakOfRouterEnc, h1, h2, h3]

theorem vaultEnc_keccakOfVaultEnc (e : NativeTokenVault.NtvAssetId) :
    vaultEnc (keccakOfVaultEnc e) = e := by
  funext c t
  obtain ⟨h1, h2⟩ := vaultPreimage_fields c t
  simp only [vaultEnc, keccakOfVaultEnc, h1, h2]

/-! ## Contingency of the breaks -/

/-- A keccak separating one named input from everything else. -/
def assetIdSeparatingKeccak (x₀ : List UInt8) : Keccak := fun x => if x = x₀ then 0 else 1

theorem assetIdSeparating_no_collision (x₀ y : List UInt8) :
    ¬ HashCollision (assetIdSeparatingKeccak x₀) x₀ y
    ∧ ¬ HashCollision (assetIdSeparatingKeccak x₀) y x₀ := by
  have h01 : (0 : UInt256) ≠ 1 := by decide
  refine ⟨?_, ?_⟩
  · rintro ⟨hne, heq⟩
    simp only [assetIdSeparatingKeccak, ite_true, Ne.symm hne, ite_false] at heq
    exact h01 heq
  · rintro ⟨hne, heq⟩
    simp only [assetIdSeparatingKeccak, ite_true, hne, ite_false] at heq
    exact h01 heq.symm

theorem routerBreak_contingent (p q : AssetRouter.Chain × AssetRouter.Address × AssetRouter.AssetData)
    (hpq : p ≠ q) :
    (∃ keccak : Keccak, RouterIdBreakOn keccak {p, q})
    ∧ ∃ keccak : Keccak, ¬ RouterIdBreakOn keccak {p, q} := by
  refine ⟨⟨fun _ => 0, p, Set.mem_insert _ _, q, Set.mem_insert_of_mem _ rfl,
    fun he => hpq (routerPreimage_triple_inj he), rfl⟩, ?_⟩
  refine ⟨assetIdSeparatingKeccak (routerPreimage p.1 p.2.1 p.2.2), ?_⟩
  rintro ⟨x, hx, y, hy, hcoll⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact hcoll.1 rfl
  · exact (assetIdSeparating_no_collision _ _).1 hcoll
  · exact (assetIdSeparating_no_collision _ _).2 hcoll
  · exact hcoll.1 rfl

theorem vaultBreak_contingent (p : NativeTokenVault.Chain × NativeTokenVault.Address) :
    (∃ keccak : Keccak, VaultIdBreakOn keccak {p})
    ∧ ∃ keccak : Keccak, ¬ VaultIdBreakOn keccak {p} := by
  have h10 : (1 : UInt256) ≠ 0 := by decide
  refine ⟨⟨fun _ => 0, Or.inr ⟨p, rfl, rfl⟩⟩, ⟨fun _ => 1, ?_⟩⟩
  rintro (⟨x, hx, y, hy, hcoll⟩ | ⟨x, -, hz⟩)
  · rw [Set.mem_singleton_iff] at hx hy
    subst hx; subst hy
    exact hcoll.1 rfl
  · exact h10 hz

/-- The two-pair set of `ZeroPreimageIndependentOfCollisions`: two tokens on chain `0`. -/
def assetIdZeroWitnessSet : Set (NativeTokenVault.Chain × NativeTokenVault.Address) :=
  {((0 : UInt256), (0 : UInt256)), ((0 : UInt256), (1 : UInt256))}

theorem zero_preimage_independent :
    ∃ (keccak : Keccak) (S : Set (NativeTokenVault.Chain × NativeTokenVault.Address)),
      (¬ ∃ p ∈ S, ∃ q ∈ S, HashCollision keccak (vaultPreimage p.1 p.2) (vaultPreimage q.1 q.2))
      ∧ (∀ p ∈ S, ∀ q ∈ S, vaultEnc keccak p.1 p.2 = vaultEnc keccak q.1 q.2 → p = q)
      ∧ (∃ p ∈ S, ZeroPreimage keccak (vaultPreimage p.1 p.2))
      ∧ ¬ NativeTokenVault.IdAssumptionsOn (vaultEnc keccak) S := by
  have h01 : ((0 : UInt256), (0 : UInt256)) ≠ ((0 : UInt256), (1 : UInt256)) := by decide
  set keccak := assetIdSeparatingKeccak (vaultPreimage 0 0) with hk
  have hnocoll : ¬ ∃ p ∈ assetIdZeroWitnessSet, ∃ q ∈ assetIdZeroWitnessSet,
      HashCollision keccak (vaultPreimage p.1 p.2) (vaultPreimage q.1 q.2) := by
    rintro ⟨x, hx, y, hy, hcoll⟩
    simp only [assetIdZeroWitnessSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact hcoll.1 rfl
    · exact (assetIdSeparating_no_collision _ _).1 hcoll
    · exact (assetIdSeparating_no_collision _ _).2 hcoll
    · exact hcoll.1 rfl
  refine ⟨keccak, assetIdZeroWitnessSet, hnocoll, ?_, ⟨(0, 0), Set.mem_insert _ _, ?_⟩, ?_⟩
  · intro p hp q hq heq
    by_contra hpq
    exact hnocoll ⟨p, hp, q, hq, vaultId_clash hpq heq⟩
  · simp [ZeroPreimage, keccak, assetIdSeparatingKeccak]
  · rintro ⟨-, hnz⟩
    exact hnz (0, 0) (Set.mem_insert _ _) (by simp [vaultEnc, keccak, assetIdSeparatingKeccak])

/-! ## Certificates -/

theorem AddressWordIsWidenedWord : Properties.AddressWordIsWidenedWord := encAddr_eq_encWord

theorem AssetIdPreimageLength : Properties.AssetIdPreimageLength :=
  ⟨assetIdPreimage_length, assetIdPreimageOfToken_length, routerPreimage_length,
    vaultPreimage_length⟩

theorem AssetIdPreimageInjective : Properties.AssetIdPreimageInjective :=
  fun _ _ _ _ _ _ h => assetIdPreimage_inj h

theorem AssetIdPreimageOfTokenInjective : Properties.AssetIdPreimageOfTokenInjective :=
  fun _ _ _ _ _ _ h => assetIdPreimageOfToken_inj h

theorem RouterPreimageInjective : Properties.RouterPreimageInjective :=
  fun _ _ _ _ _ _ h => routerPreimage_inj h

theorem VaultPreimageInjective : Properties.VaultPreimageInjective :=
  fun _ _ _ _ h => vaultPreimage_inj h

theorem OverloadPreimagesCoincide : Properties.OverloadPreimagesCoincide := overloadPreimages

theorem EncodeAssetIdOverloadsCoincide : Properties.EncodeAssetIdOverloadsCoincide :=
  fun keccak c t s => by rw [encodeAssetIdOfToken, encodeAssetId, overloadPreimages]

theorem OverloadsCoincide : Properties.OverloadsCoincide :=
  fun keccak c => ⟨fun t => by rw [encodeNTVAssetIdOfToken, encodeAssetId, overloadPreimages],
    fun _ => rfl⟩

theorem NativeRegistrationIdsAgree : Properties.NativeRegistrationIdsAgree := by
  intro keccak c ntv t
  have hs : AssetRouter.senderOf ntv (addrAsBytes32 l2NtvAddr) ntv = addrAsBytes32 l2NtvAddr := by
    simp [AssetRouter.senderOf]
  unfold AssetRouter.writtenId
  rw [hs]
  show keccak (routerPreimage c (addrAsBytes32 l2NtvAddr) (addrAsBytes32 t))
    = keccak (assetIdPreimageOfToken c l2NtvAddr t)
  rw [← vaultPreimage_eq_routerPreimage, vaultPreimage_widen]

theorem RouterModelIsLibrary : Properties.RouterModelIsLibrary :=
  fun keccak c s d => by rw [routerEnc, encodeAssetId, routerPreimage_widen]

theorem VaultModelIsLibrary : Properties.VaultModelIsLibrary :=
  fun keccak c t => by rw [vaultEnc, encodeNTVAssetIdOfToken, vaultPreimage_widen]

theorem VaultModelIsRouterModelAtNtv : Properties.VaultModelIsRouterModelAtNtv := by
  intro keccak cfg hcfg
  funext c t
  simp only [AssetRouter.AtomicRecovery.ntvId, routerEnc, vaultEnc, hcfg,
    vaultPreimage_eq_routerPreimage]

theorem VaultModelIsRouterModelAtNtvWitness : Properties.VaultModelIsRouterModelAtNtvWitness :=
  ⟨⟨0, 0, addrAsBytes32 l2NtvAddr, 0, fun _ => none⟩, rfl⟩

theorem RouterIdInjOnIffNoCollision : Properties.RouterIdInjOnIffNoCollision := routerIdInjOn_iff

theorem IdInjOnOfNoCollision : Properties.IdInjOnOfNoCollision :=
  fun keccak S h => (routerIdInjOn_iff keccak S).mpr h

theorem RouterIdClashIsNamedCollision : Properties.RouterIdClashIsNamedCollision :=
  fun _ _ _ hpq h => routerId_clash hpq h

theorem VaultIdAssumptionsOnIffNoKeccakEvent : Properties.VaultIdAssumptionsOnIffNoKeccakEvent :=
  vaultIdAssumptionsOn_iff

theorem VaultIdClashIsNamedCollision : Properties.VaultIdClashIsNamedCollision :=
  fun _ _ _ hpq h => vaultId_clash hpq h

theorem NonzeroIsPreimageEvent : Properties.NonzeroIsPreimageEvent :=
  fun _ => ⟨fun _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩

theorem ZeroPreimageIndependentOfCollisions : Properties.ZeroPreimageIndependentOfCollisions :=
  zero_preimage_independent

theorem AssetIdCheckPassesIff : Properties.AssetIdCheckPassesIff := assetIdCheck_some_iff

theorem AssetIdCheckIsRegistryIdCheck : Properties.AssetIdCheckIsRegistryIdCheck := by
  intro keccak c a t
  rw [assetIdCheck_some_iff, VaultModelIsLibrary]

theorem AssetIdCheckPassesIffRouterId : Properties.AssetIdCheckPassesIffRouterId := by
  intro keccak c a t
  rw [assetIdCheck_some_iff, (OverloadsCoincide keccak c).1 t]

theorem AssetIdCheckPinsOriginOrCollision : Properties.AssetIdCheckPinsOriginOrCollision :=
  fun keccak _ _ _ _ _ h h' => assetIdCheck_pins keccak h h'

theorem AssetIdCheckPinWitness : Properties.AssetIdCheckPinWitness := by
  have hne : ¬ ((0 : UInt256) = 1 ∧ (0 : Addr) = 0) := by decide
  have hpre : assetIdPreimageOfToken 0 l2NtvAddr 0 ≠ assetIdPreimageOfToken 1 l2NtvAddr 0 :=
    fun h => hne ⟨(assetIdPreimageOfToken_inj h).1, rfl⟩
  refine ⟨⟨assetIdSeparatingKeccak (assetIdPreimageOfToken 0 l2NtvAddr 0), 0, 1, 0, 0, hne,
    (assetIdSeparating_no_collision _ _).1, ?_, ?_⟩,
    ⟨fun _ => 0, 0, 0, 1, 0, 0, hne, ?_, ?_, hpre, rfl⟩⟩
  · rw [assetIdCheck_some_iff]
  · rw [assetIdCheck_none_iff]
    simp only [encodeNTVAssetIdOfToken, assetIdSeparatingKeccak, ite_true, hpre.symm, ite_false]
    decide
  · rw [assetIdCheck_some_iff]; rfl
  · rw [assetIdCheck_some_iff]; rfl

theorem RouterEncodingsAreKeccakInstances : Properties.RouterEncodingsAreKeccakInstances :=
  fun enc => ⟨keccakOfRouterEnc enc, routerEnc_keccakOfRouterEnc enc⟩

theorem VaultEncodingsAreKeccakInstances : Properties.VaultEncodingsAreKeccakInstances :=
  fun e => ⟨keccakOfVaultEnc e, vaultEnc_keccakOfVaultEnc e⟩

theorem RouterNoBreakSatisfiable : Properties.RouterNoBreakSatisfiable := by
  intro S hS
  obtain ⟨enc, henc⟩ := AssetRouter.IdInjOnSatisfiable S hS
  refine ⟨keccakOfRouterEnc enc, ?_⟩
  rw [← routerIdInjOn_iff, routerEnc_keccakOfRouterEnc]
  exact henc

theorem VaultNoBreakSatisfiable : Properties.VaultNoBreakSatisfiable := by
  intro S hS
  obtain ⟨e, he⟩ := NativeTokenVault.IdAssumptionsOnSatisfiable S hS
  refine ⟨keccakOfVaultEnc e, ?_⟩
  rw [← vaultIdAssumptionsOn_iff, vaultEnc_keccakOfVaultEnc]
  exact he

theorem IdBreaksAreContingent : Properties.IdBreaksAreContingent :=
  ⟨routerBreak_contingent, vaultBreak_contingent⟩

/-! ## Model validation

Byte positions checked on concrete arguments, so a reviewer can compare them with the ABI
specification without reading the encoder: the address head is left-padded, the vault address
`0x10004` sits in the last three bytes of its head, and the preimage is 96 bytes. -/

example : encAddr l2NtvAddr = List.replicate 29 0 ++ [0x01, 0x00, 0x04] := by decide
example : (assetIdPreimage 324 l2NtvAddr 7).length = 96 := by decide
example : (assetIdPreimage 324 l2NtvAddr 7)[31]! = 0x44 := by decide   -- 324 = 0x0144
example : (assetIdPreimage 324 l2NtvAddr 7)[30]! = 0x01 := by decide
example : (assetIdPreimage 324 l2NtvAddr 7)[63]! = 0x04 := by decide   -- sender's low byte
example : (assetIdPreimage 324 l2NtvAddr 7)[95]! = 0x07 := by decide   -- data's low byte
example : (assetIdPreimage 324 l2NtvAddr 7)[32]! = 0 := by decide      -- address left padding

end Contracts.DataEncoding
