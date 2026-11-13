import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: proof routing in the ZKsync OS verifiers (`MultiProofVerifier` and its wrappers)

**Source.** era-contracts `draft/v0.35.0`, commit
`d9f678900e1bc8286412b78f56d4a9f443983c29`. Paths are relative to `l1-contracts/contracts/`;
every `file:line` below is at that commit.

**This file is definitions only.** Statements are in
`EraSpec.Contracts.MultiProofVerifier.Properties.Routing`, proofs in
`EraSpec.Contracts.MultiProofVerifier.Proofs.Routing`.

## What is modelled

Only routing and combination: which sub-verifier calls a proof must pass, on which slices
of the proof and with which public inputs. Every cryptographic check is an abstract
predicate in `Crypto`:

* `Crypto.plonk args w` — `ZKsyncOSVerifierPlonk.verify(args, w)` (the Airbender PLONK
  verifier, `PLONK_VERIFIER` of `ZKsyncOSVerifier`);
* `Crypto.zisk pi w` — `ZiskVerifier.verify(pi, w)` as a whole (its on-chain reconstruction
  of the ZiSK public values and the snarkJS backend are not modelled);
* `Crypto.keccakPacked pi` — `uint256(keccak256(abi.encodePacked(pi)))`.

A `view` call returns a `Verdict`: `none` is a revert, `some b` is a return of `b`. An
abstract sub-verifier returning `false` and one reverting are identified (`Crypto.plonk`
and `Crypto.zisk` are `Bool`): every caller in this file turns both into a revert or a
`false`, never into acceptance.

### `ZKsyncOSVerifier.verify` (`state-transition/verifiers/ZKsyncOSVerifier.sol:43-72`)

    if (_proof.length < ZKSYNC_OS_PROOF_METADATA_LENGTH) revert EmptyProofLength();    // :45-47
    if (_publicInputs.length == 0) revert EmptyPublicInputsLength();                    // :50-52
    uint256 verifierType = _proof[0];                                                   // :55
    if (verifierType == ZKSYNC_OS_PLONK_VERIFICATION_TYPE) {                            // :57
        args[0] = computeZKsyncOSHash(_proof[1], _publicInputs);                        // :59
        return PLONK_VERIFIER.verify(args, _extractZKsyncOSProof(_proof));              // :61
    } else if (verifierType == ZKSYNC_OS_MOCK_VERIFICATION_TYPE) {                      // :62
        args[0] = computeZKsyncOSHash(_proof[1], _publicInputs);                        // :64
        return mockVerify(args, _extractZKsyncOSProof(_proof));                         // :66
    } else { revert UnknownVerifierType(); }                                            // :69-71

`mockVerify` reverts in production (`:75-77`, `MockVerifierNotSupported`); the testnet
override (`ZKsyncOSTestnetVerifier.sol:26-37`) checks `length == 2`, `[0] == 13`,
`[1] == args[0]`. `_extractZKsyncOSProof` (`:108-118`) drops the two metadata words.
`computeZKsyncOSHash` (`:120-133`) reverts on a nonzero carried hash, folds
(`length == 1 ? pi[0] : keccak(pi)`) and shifts right by `PUBLIC_INPUT_SHIFT = 32`.

### `MultiProofVerifier.verifyForChain` (`state-transition/verifiers/MultiProofVerifier.sol:66-93`)

    if (_proof.length == 0) revert EmptyProof();                                        // :71-73
    if (_proof[0] >> 8 != 0) revert InvalidProofFormat();                               // :74-76
    uint256 proofType = _proof[0];                                                      // :77
    DisabledProofSystems memory disabled = IGetters(_chain).disabledProofSystems();     // :78
    uint8 disabledMask = (boojum ? 1 : 0) | (airbender ? 2 : 0) | (zisk ? 4 : 0);       // :79-81
    uint256 requiredType = getProofMode(disabledMask);                                  // :82
    if (proofType != requiredType) revert UnknownProofType(proofType);                  // :83-85
    if (requiredType == ZKSYNC_OS_PLONK_VERIFICATION_TYPE) {                            // :86
        if (!AIRBENDER_VERIFIER.verify(_publicInputs, _proof)) revert ...;              // :87-89
        return true; }                                                                  // :90
    return _verifyMultiProof(_publicInputs, _proof);                                    // :92

`verify` (`:53-58`) is `verifyForChain(msg.sender, ...)`. `getProofMode` (`:101-109`) reverts
unless the mask is a subset of the ZiSK bit `4`, and returns `5` (multi-proof) when the ZiSK
bit is clear, `2` (Airbender only) when set. `_verifyMultiProof` (`:126-181`):

    if (_proof.length < 3) revert ProofTooShort();                                      // :131-133
    if (_proof[1] != 0) revert NonZeroCarriedHash();                                    // :137-139
    uint256 airbenderLen = _proof[2];                                                   // :141
    if (_proof.length < 3 + airbenderLen + ZISK_SNARK_PROOF_LENGTH) revert ...;         // :144-146
    airbenderProof = _proof[3 .. 3+airbenderLen];                                       // :154-157
    if (!AIRBENDER_VERIFIER.verify(_publicInputs, airbenderProof)) revert ...;          // :158-160
    ziskProof = _proof[3+airbenderLen .. 3+airbenderLen+24];                            // :171-175
    if (!ZISK_RANGE_VERIFIER.verify(_publicInputs, ziskProof)) revert ...;              // :176-178
    return true;                                                                        // :180

Checked `3 + airbenderLen + 24` overflow reverts; with `ℕ` the length test fails instead,
which is the same outcome because a calldata length is below `2^256`.

### `MultiProofTestnetVerifier.verify` (`state-transition/verifiers/MultiProofTestnetVerifier.sol:31-44`)

    if (_proof.length == 0) return true;                                                // :33-35
    if ((_proof[0] & 255) == MOCK_PROOF_TYPE) return _mockVerify(...);                  // :38-40
    return MultiProofVerifier(INNER_VERIFIER).verifyForChain(msg.sender, ...);          // :43

`_mockVerify` (`:76-98`): `length < 4` reverts, `[1] != 0` reverts, the expected value is
the folded and shifted public input, and `[2] == 13 && [3] == expected` is required.

### `ZiskTestnetVerifier.verify` (`state-transition/verifiers/ZiskTestnetVerifier.sol:31-37`)

A proof of length 24 starting `[3, 0, 13]` (`_isMockProof`, `:44-50`) takes the mock path
(`_mockVerify`, `:52-68`: word 3 equals the folded and shifted input, words 4..23 are zero);
every other proof goes to `INNER_VERIFIER.verify` unchanged.

### Constructors

The two testnet wrappers and `ZKsyncOSTestnetVerifier` `assert(block.chainid != 1)`
(`MultiProofTestnetVerifier.sol:26`, `ZKsyncOSTestnetVerifier.sol:17`,
`ZiskTestnetVerifier.sol:26`); `MultiProofVerifier`'s two sub-verifiers are immutable
(`MultiProofVerifier.sol:41-50`). Wiring is a parameter here (`Wiring`); the production
wiring (`productionWiring`) is `ZKsyncOSVerifier` as Airbender lane and `ZiskVerifier` as
range verifier, which is what `DeployCTM` does with `multi_proof_verifier = true`
(`verifiers/README.md:124-140`).

## Modelling choices

* Words are `UInt256`; arrays are lists, `length` is `List.length`, `_proof[i]` is
  `List.getD i 0` behind a length check that makes the index valid (or, for the ZiSK mock
  path, behind `length == 24`).
* The chain's `disabledProofSystems()` getter is `Policy`: `none` when the call reverts
  (the caller is not a chain), else the struct. What a chain stores and how it changes is in
  `EraSpec.Protocol.ProofSystemGate.Specs.Run`.
* Which compositions of these contracts exist (and on which chain id their constructors
  succeed) is in `EraSpec.Contracts.MultiProofVerifier.Specs.Deployments`.
* Variants exist only for countermodels and redundancy statements:
  `verifyForChainSubmittedDispatch`, `verifyForChainNoTypeCheck` and
  `verifyForChainNoShiftCheck` (one check removed or changed each, see their docstrings).
-/

namespace Contracts.MultiProofVerifier

/-- A calldata/memory word. -/
abbrev Word := UInt256
/-- Addresses as 256-bit words. -/
abbrev Address := UInt256

/-- Outcome of a `view` verifier call: `none` reverts, `some b` returns `b`. -/
abbrev Verdict := Option Bool

/-- An `IVerifier.verify(publicInputs, proof)` as a function. -/
abbrev Verifier := List Word → List Word → Verdict

/-! ## Constants (`common/Config.sol:86-123`) -/

/-- `ZKSYNC_OS_PLONK_VERIFICATION_TYPE` (`Config.sol:105`). -/
def PLONK_TYPE : Word := 2
/-- `ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE` (`Config.sol:108`). -/
def MULTI_TYPE : Word := 5
/-- `ZKSYNC_OS_MOCK_VERIFICATION_TYPE` (`Config.sol:111`), also `MOCK_PROOF_TYPE`
(`MultiProofTestnetVerifier.sol:21`). -/
def MOCK_TYPE : Word := 3
/-- `ZKSYNC_OS_MOCK_PROOF_MAGIC` (`Config.sol:120`). -/
def MOCK_MAGIC : Word := 13
/-- `ZKSYNC_OS_PROOF_METADATA_LENGTH` (`Config.sol:114`). -/
def METADATA_LENGTH : ℕ := 2
/-- `ZKSYNC_OS_MOCK_PROOF_LENGTH` (`Config.sol:117`). -/
def MOCK_PROOF_LENGTH : ℕ := 2
/-- `ZISK_SNARK_PROOF_LENGTH` (`Config.sol:123`). -/
def ZISK_LEN : ℕ := 24
/-- `PUBLIC_INPUT_SHIFT` (`Config.sol:102`). -/
def SHIFT : ℕ := 32
/-- `MAINNET_CHAIN_ID` (`Config.sol:86`). -/
def MAINNET_CHAIN_ID : ℕ := 1

/-! ## Abstract cryptography -/

/-- The abstract cryptographic checks. See the module docstring. -/
structure Crypto where
  /-- `uint256(keccak256(abi.encodePacked(pi)))`. -/
  keccakPacked : List Word → Word
  /-- `ZKsyncOSVerifierPlonk.verify(args, w)` accepts. -/
  plonk : List Word → List Word → Bool
  /-- `ZiskVerifier.verify(pi, w)` accepts. -/
  zisk : List Word → List Word → Bool

/-- `x >> PUBLIC_INPUT_SHIFT`. -/
def shiftPI (x : Word) : Word :=
  ⟨x.val >>> SHIFT,
    lt_of_le_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _) x.isLt⟩

/-- `_publicInputs.length == 1 ? _publicInputs[0] : uint256(keccak256(abi.encodePacked(_publicInputs)))`. -/
def foldPI (K : Crypto) : List Word → Word
  | [x] => x
  | pi => K.keccakPacked pi

/-- The value the settlement layer proves against: folded, then shifted. -/
def batchInput (K : Crypto) (pi : List Word) : Word := shiftPI (foldPI K pi)

/-- `ZKsyncOSVerifier.computeZKsyncOSHash` (`ZKsyncOSVerifier.sol:120-133`). -/
def computeZKsyncOSHash (K : Crypto) (initialHash : Word) (pi : List Word) : Option Word :=
  if initialHash ≠ 0 then none else some (batchInput K pi)

/-! ## `ZKsyncOSVerifier` and its testnet subclass -/

/-- Which `mockVerify` the deployed `ZKsyncOSVerifier` code has. -/
inductive Flavour
  | production
  | testnet
  deriving DecidableEq, Repr

/-- `ZKsyncOSTestnetVerifier.mockVerify` (`ZKsyncOSTestnetVerifier.sol:26-37`). -/
def zkosMockVerify (args proof : List Word) : Verdict :=
  if proof.length ≠ MOCK_PROOF_LENGTH then none
  else if proof.getD 0 0 ≠ MOCK_MAGIC then none
  else if proof.getD 1 0 ≠ args.getD 0 0 then none
  else some true

/-- `ZKsyncOSVerifier.verify` (`ZKsyncOSVerifier.sol:43-72`), with the production
`mockVerify` (reverts, `:75-77`) or the testnet one. -/
def zkosVerify (K : Crypto) (fl : Flavour) : Verifier := fun pi proof =>
  if proof.length < METADATA_LENGTH then none
  else if pi.length = 0 then none
  else if proof.getD 0 0 = PLONK_TYPE then
    match computeZKsyncOSHash K (proof.getD 1 0) pi with
    | none => none
    | some a => some (K.plonk [a] (proof.drop METADATA_LENGTH))
  else if proof.getD 0 0 = MOCK_TYPE then
    match computeZKsyncOSHash K (proof.getD 1 0) pi with
    | none => none
    | some a =>
      match fl with
      | .production => none
      | .testnet => zkosMockVerify [a] (proof.drop METADATA_LENGTH)
  else none

/-! ## `MultiProofVerifier` -/

/-- `DisabledProofSystems` (`Config.sol:132-136`). -/
structure DisabledProofSystems where
  boojum : Bool
  airbender : Bool
  zisk : Bool
  deriving DecidableEq, Repr

/-- The mask `verifyForChain` rebuilds from the struct (`MultiProofVerifier.sol:79-81`);
`ProofSystem` ordinals are `Boojum = 0, Airbender = 1, Zisk = 2` (`Config.sol:126-130`). -/
def DisabledProofSystems.mask (d : DisabledProofSystems) : ℕ :=
  (if d.boojum then 1 else 0) ||| (if d.airbender then 2 else 0) ||| (if d.zisk then 4 else 0)

/-- `MultiProofVerifier.getProofMode` (`MultiProofVerifier.sol:101-109`). `~uint8(4) = 251`. -/
def getProofMode (m : ℕ) : Option Word :=
  if m &&& 251 ≠ 0 then none
  else if m &&& 4 = 0 then some MULTI_TYPE else some PLONK_TYPE

/-- `IGetters(_chain).disabledProofSystems()`: `none` when that call reverts. -/
abbrev Policy := Address → Option DisabledProofSystems

/-- The two immutable sub-verifiers (`MultiProofVerifier.sol:41-50`). -/
structure Wiring where
  airbender : Verifier
  ziskRange : Verifier

/-- `_verifyMultiProof` (`MultiProofVerifier.sol:126-181`). -/
def verifyMultiProof (W : Wiring) (pi proof : List Word) : Verdict :=
  if proof.length < 3 then none
  else if proof.getD 1 0 ≠ 0 then none
  else if proof.length < 3 + (proof.getD 2 0).val + ZISK_LEN then none
  else if W.airbender pi ((proof.drop 3).take (proof.getD 2 0).val) ≠ some true then none
  else if W.ziskRange pi ((proof.drop (3 + (proof.getD 2 0).val)).take ZISK_LEN) ≠ some true
    then none
  else some true

/-- `MultiProofVerifier.verifyForChain` (`MultiProofVerifier.sol:66-93`). -/
def verifyForChain (W : Wiring) (P : Policy) (chain : Address) (pi proof : List Word) : Verdict :=
  match proof with
  | [] => none
  | p0 :: _ =>
    if p0.val >>> 8 ≠ 0 then none
    else match P chain with
      | none => none
      | some d =>
        match getProofMode d.mask with
        | none => none
        | some req =>
          if p0 ≠ req then none
          else if req = PLONK_TYPE then
            (if W.airbender pi proof = some true then some true else none)
          else verifyMultiProof W pi proof

/-- `MultiProofVerifier.verify` (`MultiProofVerifier.sol:53-58`): the chain is the caller. -/
def verify (W : Wiring) (P : Policy) (msgSender : Address) (pi proof : List Word) : Verdict :=
  verifyForChain W P msgSender pi proof

/-- The production wiring: the Airbender lane is a production `ZKsyncOSVerifier`, the range
verifier is `ZiskVerifier` (abstract). -/
def productionWiring (K : Crypto) : Wiring where
  airbender := zkosVerify K .production
  ziskRange := fun pi w => some (K.zisk pi w)

/-! ## Testnet wrappers -/

/-- `MultiProofTestnetVerifier._mockVerify` (`MultiProofTestnetVerifier.sol:76-98`). -/
def multiMockVerify (K : Crypto) (pi proof : List Word) : Verdict :=
  if proof.length < 4 then none
  else if proof.getD 1 0 ≠ 0 then none
  else if proof.getD 2 0 ≠ MOCK_MAGIC ∨ proof.getD 3 0 ≠ batchInput K pi then none
  else some true

/-- `MultiProofTestnetVerifier.verify` (`MultiProofTestnetVerifier.sol:31-44`), with
`inner chain` standing for `INNER_VERIFIER.verifyForChain(chain, ·, ·)`. -/
def testnetVerify (K : Crypto) (inner : Address → Verifier) (msgSender : Address)
    (pi proof : List Word) : Verdict :=
  match proof with
  | [] => some true
  | p0 :: _ =>
    if p0.val &&& 255 = MOCK_TYPE.val then multiMockVerify K pi proof
    else inner msgSender pi proof

/-- `ZiskTestnetVerifier._isMockProof` (`ZiskTestnetVerifier.sol:44-50`). -/
def isZiskMock (proof : List Word) : Bool :=
  decide (proof.length = ZISK_LEN) && decide (proof.getD 0 0 = MOCK_TYPE) &&
    decide (proof.getD 1 0 = 0) && decide (proof.getD 2 0 = MOCK_MAGIC)

/-- `ZiskTestnetVerifier._mockVerify` (`ZiskTestnetVerifier.sol:52-68`). -/
def ziskMockVerify (K : Crypto) (pi proof : List Word) : Verdict :=
  if proof.getD 3 0 ≠ batchInput K pi then none
  else if !((proof.drop 4).all (fun x => decide (x = 0))) then none
  else some true

/-- `ZiskTestnetVerifier.verify` (`ZiskTestnetVerifier.sol:31-37`). -/
def ziskTestnetVerify (K : Crypto) (inner : Verifier) : Verifier := fun pi proof =>
  if isZiskMock proof then ziskMockVerify K pi proof else inner pi proof

/-- The testnet constructors' only guard, `assert(block.chainid != MAINNET_CHAIN_ID)`. -/
def testnetConstructorAccepts (chainid : ℕ) : Prop := chainid ≠ MAINNET_CHAIN_ID

/-! ## Attestations -/

/-- `pi` is nonempty and some PLONK proof is accepted by the Airbender verifier for its
batch input. -/
def AirbenderAttested (K : Crypto) (pi : List Word) : Prop :=
  pi ≠ [] ∧ ∃ w, K.plonk [batchInput K pi] w = true

/-- Some 24-word proof is accepted by the ZiSK range verifier for `pi`. -/
def ZiskAttested (K : Crypto) (pi : List Word) : Prop :=
  ∃ w : List Word, w.length = ZISK_LEN ∧ K.zisk pi w = true

/-- A `Crypto` under which no proof verifies at all. -/
def NothingVerifies (K : Crypto) : Prop :=
  (∀ a w, K.plonk a w = false) ∧ (∀ pi w, K.zisk pi w = false)

/-! ## Variants used only for countermodels and redundancy statements -/

/-- `verifyForChain` with the `proofType != requiredType` check (`:83-85`) removed and the
dispatch at `:86` reading the **submitted** type: `proofType == PLONK ? Airbender-only :
multi-proof`. -/
def verifyForChainSubmittedDispatch (W : Wiring) (P : Policy) (chain : Address)
    (pi proof : List Word) : Verdict :=
  match proof with
  | [] => none
  | p0 :: _ =>
    if p0.val >>> 8 ≠ 0 then none
    else match P chain with
      | none => none
      | some d =>
        match getProofMode d.mask with
        | none => none
        | some _ =>
          if p0 = PLONK_TYPE then
            (if W.airbender pi proof = some true then some true else none)
          else verifyMultiProof W pi proof

/-- `verifyForChain` with only the `proofType != requiredType` check (`:83-85`) removed;
the dispatch still reads `requiredType`. -/
def verifyForChainNoTypeCheck (W : Wiring) (P : Policy) (chain : Address)
    (pi proof : List Word) : Verdict :=
  match proof with
  | [] => none
  | p0 :: _ =>
    if p0.val >>> 8 ≠ 0 then none
    else match P chain with
      | none => none
      | some d =>
        match getProofMode d.mask with
        | none => none
        | some req =>
          if req = PLONK_TYPE then
            (if W.airbender pi proof = some true then some true else none)
          else verifyMultiProof W pi proof

/-- `verifyForChain` with the `_proof[0] >> 8 != 0` check (`:74-76`) removed. -/
def verifyForChainNoShiftCheck (W : Wiring) (P : Policy) (chain : Address)
    (pi proof : List Word) : Verdict :=
  match proof with
  | [] => none
  | p0 :: _ =>
    match P chain with
    | none => none
    | some d =>
      match getProofMode d.mask with
      | none => none
      | some req =>
        if p0 ≠ req then none
        else if req = PLONK_TYPE then
          (if W.airbender pi proof = some true then some true else none)
        else verifyMultiProof W pi proof

end Contracts.MultiProofVerifier
