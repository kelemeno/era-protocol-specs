import EraSpec.Contracts.MultiProofVerifier.Specs.Routing

/-!
# Properties: what a ZKsync OS verifier accepts

Statements about `EraSpec.Contracts.MultiProofVerifier.Specs.Routing` (era-contracts
`d9f678900e1bc8286412b78f56d4a9f443983c29`). Proofs are in
`EraSpec.Contracts.MultiProofVerifier.Proofs.Routing`. Cryptographic checks are abstract
(`Crypto`); "attested" means some proof is accepted by that abstract check
(`AirbenderAttested`, `ZiskAttested`).

## Mode selection

* `GetProofModeExact`: on a `uint8` mask, `getProofMode` returns multi-proof (`5`) exactly
  at `0`, Airbender-only (`2`) exactly at `4`, and reverts on every other mask.

## `MultiProofVerifier`, any wiring

* `NeverReturnsFalse`: `verifyForChain` rejects only by reverting.
* `AcceptIff`: exact acceptance condition, for any sub-verifiers: the chain's getter
  answers, Boojum and Airbender are not disabled, and either ZiSK is disabled, the proof
  starts with `2` and the Airbender verifier accepts the **whole** proof; or ZiSK is
  enabled, the proof is `5 :: 0 :: c :: ab ++ zk ++ rest` with `|ab| = c`, `|zk| = 24`, the
  Airbender verifier accepts `ab` and the range verifier accepts `zk`, both against the
  same, unmodified public inputs.
* `NoDowngrade`: a chain whose ZiSK lane is enabled rejects every proof starting with `2`,
  and a chain whose ZiSK lane is disabled rejects every proof starting with `5`.
* `TrailingWordsIgnored`: words after the ZiSK slice are not read (a multi-proof is
  malleable in its tail; nothing is bound to the proof bytes, so this is harmless).
* `ShiftCheckRedundant`: the `_proof[0] >> 8 != 0` check never changes the outcome.

## `ZKsyncOSVerifier`

* `ZkosAcceptIff`: exact acceptance for both flavours: `pi ≠ []` and either the proof is
  `2 :: 0 :: w` with `plonk [batchInput pi] w`, or the flavour is testnet and the proof is
  exactly `[3, 0, 13, batchInput pi]`. A production verifier accepts no mock proof.

## Production wiring (`ZKsyncOSVerifier` + `ZiskVerifier`)

* `ProductionAcceptsOnlyIfAllRequired` (**headline**): if the production
  `MultiProofVerifier` accepts, the Airbender lane is attested for `pi` and, unless the
  chain has disabled ZiSK, the ZiSK lane is attested for the same `pi`.
* `ProductionAcceptIff`: the exact envelope in both modes (so the headline is not vacuous,
  and nothing else is accepted).
* `MultiModeWitness`: a concrete accepted multi-proof under a `Crypto` whose checks each
  accept exactly one proof.

## Which check carries the safety (countermodels)

* `SubmittedDispatchDowngrades`: if the dispatch at `:86` read the submitted type (and the
  equality check were gone), a ZiSK-enabled chain would accept an Airbender-only proof
  while no ZiSK proof verifies at all. The source dispatches on `requiredType`.
* `NoTypeCheckStillSafe`: removing only the `proofType != requiredType` check keeps the
  headline guarantee; that check is a format check, the dispatch on the chain's mode is
  what enforces the lanes.
* `AirbenderLaneMockLoadBearing`: the production `mockVerify` revert is load-bearing: with
  a `ZKsyncOSTestnetVerifier` as Airbender lane, a multi-proof is accepted although no
  PLONK proof verifies at all.

## Testnet wrappers (boundary)

* `TestnetAcceptIff`: `MultiProofTestnetVerifier` accepts in exactly three ways: the empty
  proof; a proof whose first word has low byte `3` and that reads
  `_ :: 0 :: 13 :: batchInput pi :: _`; or a proof whose first word has another low byte and
  that the inner verifier accepts for the original caller.
* `TestnetAcceptsFalseProof` (**boundary countermodel**): when no proof verifies at all,
  the testnet wrapper over the production verifier still accepts the empty proof and the
  mock proof for any `pi` and any caller, and the production verifier rejects both.
* `TestnetMockTypeIsLowByte`: the mock path is selected by the low byte of `_proof[0]`
  (the NatSpec says "type 3" and "all other proofs: delegated"): `[259, 0, 13, batchInput
  pi]` is accepted for any inner verifier, while `MultiProofVerifier` rejects a proof with
  that first word.
* `ZiskTestnetAcceptIff`: `ZiskTestnetVerifier` accepts exactly the canonical mock
  `3 :: 0 :: 13 :: batchInput pi :: 0^20` and the non-mock proofs its inner verifier accepts.
-/

namespace Contracts.MultiProofVerifier

/-- **MODE SELECTION.** For every `uint8` mask `m`: `getProofMode m` is `5` iff `m = 0`, is
`2` iff `m = 4`, and reverts iff `m ∉ {0, 4}`. -/
def Properties.GetProofModeExact : Prop :=
  ∀ m : ℕ, m < 256 →
    (getProofMode m = some MULTI_TYPE ↔ m = 0) ∧
    (getProofMode m = some PLONK_TYPE ↔ m = 4) ∧
    (getProofMode m = none ↔ (m ≠ 0 ∧ m ≠ 4))

/-- **NO `false`.** For any wiring, policy, caller, inputs and proof, `verifyForChain`
never returns `false`: it returns `true` or reverts. -/
def Properties.NeverReturnsFalse : Prop :=
  ∀ (W : Wiring) (P : Policy) (chain : Address) (pi proof : List Word),
    verifyForChain W P chain pi proof ≠ some false

/-- **EXACT ACCEPTANCE, ANY WIRING.** `verifyForChain W P chain pi proof = some true` iff the
chain's getter returns some `d` with Boojum and Airbender not disabled, and either
(ZiSK disabled) the proof's first word is `2` and the Airbender verifier accepts the whole
proof with `pi`, or (ZiSK enabled) the proof is `5 :: 0 :: c :: ab ++ zk ++ rest` with
`|ab| = c`, `|zk| = 24`, the Airbender verifier accepts `(pi, ab)` and the range verifier
accepts `(pi, zk)`. -/
def Properties.AcceptIff : Prop :=
  ∀ (W : Wiring) (P : Policy) (chain : Address) (pi proof : List Word),
    verifyForChain W P chain pi proof = some true ↔
      ∃ d, P chain = some d ∧ d.boojum = false ∧ d.airbender = false ∧
        ((d.zisk = true ∧ proof.head? = some PLONK_TYPE ∧ W.airbender pi proof = some true) ∨
         (d.zisk = false ∧ ∃ (c : Word) (ab zk rest : List Word),
            proof = MULTI_TYPE :: 0 :: c :: (ab ++ zk ++ rest) ∧ ab.length = c.val ∧
            zk.length = ZISK_LEN ∧ W.airbender pi ab = some true ∧
            W.ziskRange pi zk = some true))

/-- **NO DOWNGRADE.** For any wiring: if the chain's ZiSK lane is enabled, every proof whose
first word is `2` is rejected (reverts); if it is disabled, every proof whose first word
is `5` is rejected. -/
def Properties.NoDowngrade : Prop :=
  ∀ (W : Wiring) (P : Policy) (chain : Address) (pi proof : List Word)
    (d : DisabledProofSystems), P chain = some d →
      (d.zisk = false → proof.head? = some PLONK_TYPE → verifyForChain W P chain pi proof = none) ∧
      (d.zisk = true → proof.head? = some MULTI_TYPE → verifyForChain W P chain pi proof = none)

/-- **TAIL NOT READ.** For any wiring: if a chain in multi-proof mode (getter returns `d` with
`d.zisk = false`) accepts `proof`, it accepts `proof ++ extra` for every `extra`. -/
def Properties.TrailingWordsIgnored : Prop :=
  ∀ (W : Wiring) (P : Policy) (chain : Address) (pi proof extra : List Word)
    (d : DisabledProofSystems), P chain = some d → d.zisk = false →
      verifyForChain W P chain pi proof = some true →
      verifyForChain W P chain pi (proof ++ extra) = some true

/-- **DEAD FORMAT CHECK.** For any wiring and inputs, removing `_proof[0] >> 8 != 0`
(`MultiProofVerifier.sol:74-76`) yields the same verdict. -/
def Properties.ShiftCheckRedundant : Prop :=
  ∀ (W : Wiring) (P : Policy) (chain : Address) (pi proof : List Word),
    verifyForChainNoShiftCheck W P chain pi proof = verifyForChain W P chain pi proof

/-- **`ZKsyncOSVerifier`, BOTH FLAVOURS.** It returns `true` iff `pi ≠ []` and either the
proof is `2 :: 0 :: w` with `plonk [batchInput pi] w`, or the flavour is testnet and the
proof is exactly `[3, 0, 13, batchInput pi]`. -/
def Properties.ZkosAcceptIff : Prop :=
  ∀ (K : Crypto) (fl : Flavour) (pi proof : List Word),
    zkosVerify K fl pi proof = some true ↔
      pi ≠ [] ∧
        ((∃ w, proof = PLONK_TYPE :: 0 :: w ∧ K.plonk [batchInput K pi] w = true) ∨
         (fl = .testnet ∧ proof = [MOCK_TYPE, 0, MOCK_MAGIC, batchInput K pi]))

/-- **HEADLINE: ALL REQUIRED LANES.** If the production `MultiProofVerifier` (Airbender lane a
production `ZKsyncOSVerifier`, range verifier `ZiskVerifier`) accepts `(pi, proof)` for
`chain`, then the chain's getter returned some `d` with Boojum and Airbender not disabled,
the Airbender lane is attested for `pi`, and if `d.zisk = false` the ZiSK lane is attested
for the same `pi`. -/
def Properties.ProductionAcceptsOnlyIfAllRequired : Prop :=
  ∀ (K : Crypto) (P : Policy) (chain : Address) (pi proof : List Word),
    verifyForChain (productionWiring K) P chain pi proof = some true →
      ∃ d, P chain = some d ∧ d.boojum = false ∧ d.airbender = false ∧
        AirbenderAttested K pi ∧ (d.zisk = false → ZiskAttested K pi)

/-- **EXACT ENVELOPE, PRODUCTION.** The production `MultiProofVerifier` accepts
`(pi, proof)` for `chain` iff the getter returns `d` with Boojum and Airbender not
disabled, `pi ≠ []`, and either (ZiSK disabled) `proof = 2 :: 0 :: w` with
`plonk [batchInput pi] w`, or (ZiSK enabled)
`proof = 5 :: 0 :: c :: (2 :: 0 :: w) ++ zk ++ rest` with `c = |w| + 2`, `|zk| = 24`,
`plonk [batchInput pi] w` and `zisk pi zk`. -/
def Properties.ProductionAcceptIff : Prop :=
  ∀ (K : Crypto) (P : Policy) (chain : Address) (pi proof : List Word),
    verifyForChain (productionWiring K) P chain pi proof = some true ↔
      ∃ d, P chain = some d ∧ d.boojum = false ∧ d.airbender = false ∧ pi ≠ [] ∧
        ((d.zisk = true ∧ ∃ w, proof = PLONK_TYPE :: 0 :: w ∧
            K.plonk [batchInput K pi] w = true) ∨
         (d.zisk = false ∧ ∃ (c : Word) (w zk rest : List Word),
            proof = MULTI_TYPE :: 0 :: c :: ((PLONK_TYPE :: 0 :: w) ++ zk ++ rest) ∧
            c.val = w.length + 2 ∧ zk.length = ZISK_LEN ∧
            K.plonk [batchInput K pi] w = true ∧ K.zisk pi zk = true))

/-- **WITNESS.** There are a `Crypto` whose PLONK check accepts only `[7]` and whose ZiSK
check accepts only 24 nines, a policy with all lanes enabled, and a multi-proof the
production verifier accepts; the same chain rejects the Airbender part alone. -/
def Properties.MultiModeWitness : Prop :=
  ∃ (K : Crypto) (P : Policy) (chain : Address) (pi proof : List Word),
    (∀ a w, K.plonk a w = true → w = [7]) ∧ (∀ p w, K.zisk p w = true → w = List.replicate 24 9) ∧
    P chain = some ⟨false, false, false⟩ ∧
    verifyForChain (productionWiring K) P chain pi proof = some true ∧
    verifyForChain (productionWiring K) P chain pi [PLONK_TYPE, 0, 7] = none

/-- **COUNTERMODEL: DISPATCH ON THE SUBMITTED TYPE.** There are a `Crypto` under which no
ZiSK proof verifies, inputs `pi` and a chain with every lane enabled, such that the variant
dispatching on the submitted type accepts a proof the source rejects, and `pi` is not
ZiSK-attested. -/
def Properties.SubmittedDispatchDowngrades : Prop :=
  ∃ (K : Crypto) (P : Policy) (chain : Address) (pi proof : List Word),
    (∀ p w, K.zisk p w = false) ∧ P chain = some ⟨false, false, false⟩ ∧
    verifyForChainSubmittedDispatch (productionWiring K) P chain pi proof = some true ∧
    verifyForChain (productionWiring K) P chain pi proof = none ∧
    ¬ ZiskAttested K pi

/-- **TYPE EQUALITY IS NOT THE GUARD.** The variant without `proofType != requiredType`
still satisfies the headline: acceptance implies the getter's `d` has Boojum and Airbender
enabled, the Airbender lane is attested, and ZiSK is attested unless disabled. -/
def Properties.NoTypeCheckStillSafe : Prop :=
  ∀ (K : Crypto) (P : Policy) (chain : Address) (pi proof : List Word),
    verifyForChainNoTypeCheck (productionWiring K) P chain pi proof = some true →
      ∃ d, P chain = some d ∧ d.boojum = false ∧ d.airbender = false ∧
        AirbenderAttested K pi ∧ (d.zisk = false → ZiskAttested K pi)

/-- **COUNTERMODEL: TESTNET AIRBENDER LANE.** With a `ZKsyncOSTestnetVerifier` as the
Airbender lane, there are a `Crypto` under which no PLONK proof verifies, a chain with every
lane enabled, and `pi` with a multi-proof that is accepted although `pi` is not
Airbender-attested. -/
def Properties.AirbenderLaneMockLoadBearing : Prop :=
  ∃ (K : Crypto) (P : Policy) (chain : Address) (pi proof : List Word),
    (∀ a w, K.plonk a w = false) ∧ P chain = some ⟨false, false, false⟩ ∧
    verifyForChain ⟨zkosVerify K .testnet, fun p w => some (K.zisk p w)⟩ P chain pi proof
      = some true ∧
    ¬ AirbenderAttested K pi

/-- **TESTNET WRAPPER, EXACT.** `MultiProofTestnetVerifier.verify` returns `true` iff the
proof is empty; or its first word has low byte `3` and it is
`p0 :: 0 :: 13 :: batchInput pi :: rest`; or its first word has a low byte other than `3`
and `inner sender` (the wrapped `verifyForChain(msg.sender, ·, ·)`) returns `true`. -/
def Properties.TestnetAcceptIff : Prop :=
  ∀ (K : Crypto) (inner : Address → Verifier) (sender : Address) (pi proof : List Word),
    testnetVerify K inner sender pi proof = some true ↔
      proof = [] ∨
      (∃ p0 rest, proof = p0 :: 0 :: MOCK_MAGIC :: batchInput K pi :: rest ∧
        p0.val &&& 255 = MOCK_TYPE.val) ∨
      (∃ p0 rest, proof = p0 :: rest ∧ p0.val &&& 255 ≠ MOCK_TYPE.val ∧
        inner sender pi proof = some true)

/-- **BOUNDARY COUNTERMODEL: THE TESTNET VERIFIER ACCEPTS A FALSE PROOF.** For every `Crypto`
under which nothing verifies, every policy, caller and `pi`: the `MultiProofTestnetVerifier`
over the production verifier accepts the empty proof and the mock proof
`[3, 0, 13, batchInput pi]`; `pi` is attested by neither lane; and the production verifier
rejects both proofs. -/
def Properties.TestnetAcceptsFalseProof : Prop :=
  ∀ (K : Crypto), NothingVerifies K → ∀ (P : Policy) (sender : Address) (pi : List Word),
    testnetVerify K (verifyForChain (productionWiring K) P) sender pi [] = some true ∧
    testnetVerify K (verifyForChain (productionWiring K) P) sender pi
      [MOCK_TYPE, 0, MOCK_MAGIC, batchInput K pi] = some true ∧
    ¬ AirbenderAttested K pi ∧ ¬ ZiskAttested K pi ∧
    verifyForChain (productionWiring K) P sender pi [] = none ∧
    verifyForChain (productionWiring K) P sender pi
      [MOCK_TYPE, 0, MOCK_MAGIC, batchInput K pi] = none

/-- **TESTNET: MOCK SELECTED BY THE LOW BYTE.** For every `Crypto`, inner verifier, caller
and `pi`: the testnet wrapper accepts `[259, 0, 13, batchInput pi]` (first word `0x103`,
not `3`) without consulting the inner verifier, and `MultiProofVerifier` with any wiring
and policy rejects that proof. -/
def Properties.TestnetMockTypeIsLowByte : Prop :=
  ∀ (K : Crypto) (inner : Address → Verifier) (sender : Address) (pi : List Word),
    testnetVerify K inner sender pi [259, 0, MOCK_MAGIC, batchInput K pi] = some true ∧
    ∀ (W : Wiring) (P : Policy),
      verifyForChain W P sender pi [259, 0, MOCK_MAGIC, batchInput K pi] = none

/-- **ZISK TESTNET WRAPPER, EXACT.** `ZiskTestnetVerifier.verify` returns `true` iff the proof
is `3 :: 0 :: 13 :: batchInput pi :: 0^20`, or it is not a mock marker (`isZiskMock` false)
and the inner verifier returns `true` on the unchanged arguments. -/
def Properties.ZiskTestnetAcceptIff : Prop :=
  ∀ (K : Crypto) (inner : Verifier) (pi proof : List Word),
    ziskTestnetVerify K inner pi proof = some true ↔
      proof = MOCK_TYPE :: 0 :: MOCK_MAGIC :: batchInput K pi :: List.replicate 20 0 ∨
      (isZiskMock proof = false ∧ inner pi proof = some true)

end Contracts.MultiProofVerifier
