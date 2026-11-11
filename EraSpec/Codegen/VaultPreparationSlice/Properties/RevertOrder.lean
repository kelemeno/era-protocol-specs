import EraSpec.Codegen.VaultPreparationSlice.Specs.Correspondence

/-!
# Which check fails first, and with what revert data

`Contracts.NativeTokenVaultBase.prepare` returns `none` for every rejection, so the
refinement cannot say *which* check rejects or with what data.  The program can: these
statements fix the first checks of `bridgeBurn` and their exact revert data, in the
source's order (`requireZeroValue`, `onlyAssetRouter`, `whenNotPaused`, then the 96-byte
check of `decodeBridgeBurnData`), and the two edges of the transcribed branch.  They
are about the program alone: they hold for every machine, whatever the token and hooks
do.  Proofs: `../Proofs/RevertOrder.lean`.

The two edges matter for what the slice claims.  A native or base-token request is
refused with `OutsideSlice()` *before* the accounting hook and before any call, so the
slice's edge adds no effect the source's other branches would not have.
-/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.NativeTokenVaultBase (BurnData)

/-- **FIRST: `requireZeroValue(_l2MsgValue)`** (`AssetHandlerModifiers.sol:12-14`).  A
nonzero `_l2MsgValue` reverts with `NonEmptyMsgValue()`, whatever else holds. -/
def Properties.L2ValueCheckedFirst : Prop :=
  ∀ {W : Type} (M : Machine W) (e : Env) (c l2v a oc : Word) (data : Bytes) (st : Storage)
    (w : W), l2v ≠ 0 →
    xcall M vaultProgram "bridgeBurn" e [.word c, .word l2v, .word a, .word oc, .bytes data]
      st w = some (.error (.data (.custom "NonEmptyMsgValue" [])))

/-- **SECOND: `onlyAssetRouter`** (`NativeTokenVaultBase.sol:108`): a caller other than
the stored router reverts with `Unauthorized(caller)`. -/
def Properties.RouterCheckedSecond : Prop :=
  ∀ {W : Type} (M : Machine W) (e : Env) (c a oc : Word) (data : Bytes) (st : Storage)
    (w : W), e.sender ≠ st.scalars "_assetRouter" →
    xcall M vaultProgram "bridgeBurn" e [.word c, .word 0, .word a, .word oc, .bytes data]
      st w = some (.error (.data (.custom "Unauthorized" [e.sender])))

/-- **THIRD: `whenNotPaused`** (`PausableUpgradeable.sol:77`): a paused vault reverts with
`"Pausable: paused"` for the router. -/
def Properties.PauseCheckedThird : Prop :=
  ∀ {W : Type} (M : Machine W) (e : Env) (c a oc : Word) (data : Bytes) (st : Storage)
    (w : W), e.sender = st.scalars "_assetRouter" → st.scalars "_paused" ≠ 0 →
    xcall M vaultProgram "bridgeBurn" e [.word c, .word 0, .word a, .word oc, .bytes data]
      st w = some (.error (.data (.message "Pausable: paused")))

/-- **FOURTH: the burn data's length** (`DataEncoding.sol:54-57`): burn data that is not
96 bytes long reverts with `InvalidNTVBurnData()`, for the router of an unpaused vault. -/
def Properties.BurnDataLengthCheckedFourth : Prop :=
  ∀ {W : Type} (M : Machine W) (e : Env) (c a oc : Word) (data : Bytes) (st : Storage)
    (w : W), e.sender = st.scalars "_assetRouter" → st.scalars "_paused" = 0 →
    data.length ≠ 96 →
    xcall M vaultProgram "bridgeBurn" e [.word c, .word 0, .word a, .word oc, .bytes data]
      st w = some (.error (.data (.custom "InvalidNTVBurnData" [])))

/-- **THE NATIVE-TOKEN EDGE**: a request from the router of an unpaused vault, with
well-formed burn data naming a token whose stored asset id is the request's, a nonzero
amount, and an asset whose origin chain is this chain, reverts with `OutsideSlice()`,
before the accounting hook and any call. -/
def Properties.NativeAssetLeavesTheSlice : Prop :=
  ∀ {W : Type} (M : Machine W) (e : Env) (c a oc : Word) (b : BurnData) (st : Storage)
    (w : W), e.sender = st.scalars "_assetRouter" → st.scalars "_paused" = 0 →
    hintedToken st a b ≠ 0 → st.maps "_assetIdOf" (hintedToken st a b) = a →
    b.amount ≠ 0 → st.maps "_originChainId" a = e.chainId →
    xcall M vaultProgram "bridgeBurn" e
      [.word c, .word 0, .word a, .word oc, .bytes (encodeBurnData b)] st w =
      some (.error (.data (.custom "OutsideSlice" [])))

/-- **THE BASE-TOKEN EDGE**: as above, for a bridged asset that is the base token. -/
def Properties.BaseAssetLeavesTheSlice : Prop :=
  ∀ {W : Type} (M : Machine W) (e : Env) (c a oc : Word) (b : BurnData) (st : Storage)
    (w : W), e.sender = st.scalars "_assetRouter" → st.scalars "_paused" = 0 →
    hintedToken st a b ≠ 0 → st.maps "_assetIdOf" (hintedToken st a b) = a →
    b.amount ≠ 0 → st.maps "_originChainId" a ≠ e.chainId →
    st.scalars "_baseTokenAssetId" = a →
    xcall M vaultProgram "bridgeBurn" e
      [.word c, .word 0, .word a, .word oc, .bytes (encodeBurnData b)] st w =
      some (.error (.data (.custom "OutsideSlice" [])))

/-- **EACH STATEMENT ABOVE APPLIES TO SOME CALL**: their premises are satisfiable, one
existential per statement. -/
def Properties.RevertOrderPremisesSatisfiable : Prop :=
  (∃ l2v : Word, l2v ≠ 0) ∧
  (∃ (e : Env) (st : Storage), e.sender ≠ st.scalars "_assetRouter") ∧
  (∃ (e : Env) (st : Storage), e.sender = st.scalars "_assetRouter" ∧ st.scalars "_paused" ≠ 0) ∧
  (∃ (e : Env) (st : Storage) (data : Bytes), e.sender = st.scalars "_assetRouter" ∧
    st.scalars "_paused" = 0 ∧ data.length ≠ 96) ∧
  (∃ (e : Env) (st : Storage) (a : Word) (b : BurnData), e.sender = st.scalars "_assetRouter" ∧
    st.scalars "_paused" = 0 ∧ hintedToken st a b ≠ 0 ∧
    st.maps "_assetIdOf" (hintedToken st a b) = a ∧ b.amount ≠ 0 ∧
    st.maps "_originChainId" a = e.chainId) ∧
  (∃ (e : Env) (st : Storage) (a : Word) (b : BurnData), e.sender = st.scalars "_assetRouter" ∧
    st.scalars "_paused" = 0 ∧ hintedToken st a b ≠ 0 ∧
    st.maps "_assetIdOf" (hintedToken st a b) = a ∧ b.amount ≠ 0 ∧
    st.maps "_originChainId" a ≠ e.chainId ∧ st.scalars "_baseTokenAssetId" = a)

end Codegen.VaultPreparationSlice
