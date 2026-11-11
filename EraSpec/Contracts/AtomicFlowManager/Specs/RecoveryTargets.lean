import EraSpec.Contracts.AtomicFlowManager.Specs.Model
import EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecovery

/-!
# Model: `AtomicFlowManager._recoverBundle` — what is deployed at each call's `to`

Source: `l1-contracts/contracts/atomic-interop/AtomicFlowManager.sol` in the pinned era-contracts
tree (`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`), with `atomic-interop/IAtomicRecoverable.sol`,
`interop/InteropCenter.sol` and `bridge/asset-router/L2AssetRouter.sol` from the same tree. A bare
`:N` is a line of `AtomicFlowManager.sol`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.AtomicFlowManager.Properties.RecoveryTargets` and are proved in
`EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryTargets`.

## The code

    function claimRefund(bytes32 _flowId, bytes calldata _bundle) external {              // :165
        InteropBundle memory bundle = abi.decode(_bundle, (InteropBundle));                // :166
        bytes32 bundleHash = InteropDataEncoding.encodeInteropBundleHash(bundle.sourceChainId, _bundle);
        LegState s = _state[_flowId][bundleHash];                                          // :169
        if (s != LegState.Revertable) revert ManagerLegNotRevertable(_flowId, bundleHash, s);  // :170
        _state[_flowId][bundleHash] = LegState.Reverted;                                   // :175
        _recoverBundle(_flowId, bundleHash, bundle);                                       // :177
    }

    function _recoverBundle(bytes32 _flowId, bytes32 _bundleHash, InteropBundle memory _bundle) internal {
        uint256 destChainId = _bundle.destinationChainId;                                  // :220
        uint256 callsLen = _bundle.calls.length;
        uint256 recovered = 0;
        for (uint256 i = 0; i < callsLen; ++i) {
            InteropCall memory c = _bundle.calls[i];
            if (IAtomicRecoverable(c.to).recoverAtomicCall(destChainId, c.data)) {         // :225
                ++recovered;
            }
        }
        if (recovered == 0) revert ManagerNoRecoverableCalls(_flowId, _bundleHash);        // :229
    }

`claimRefund` runs on the leg's **source** chain: the manager whose `_state` holds the leg is the
one the source chain's `InteropCenter` appended to (`InteropCenter.sol:650`). But `InteropCall.to`
is the address the call targets on the **destination** chain:

* a direct call's `to` is the sender's recipient on the destination (`InteropCenter.sol:742-749`);
* an indirect call's `to` is what the indirect sender returned (`InteropCenter.sol:714-716, :733-740`):
  for the L2 asset router, the destination's router (`L2AssetRouter.sol:336`), which for an L2
  destination is `L2_ASSET_ROUTER_ADDR`, the source chain's own router too, and for an L1
  destination is the L1 asset router, an L1 address.

So `_recoverBundle` calls, **on the source chain**, whatever happens to be deployed there at a
destination-side address. `IAtomicRecoverable.sol:6-7` says the interface is "Implemented by any
contract that can be the target (`InteropCall.to`) of an atomic-interop bundle call"; it does not
say the target must exist on the source chain. `AtomicFlowManager.sol:208-211` and
`atomic-interop/README.md:63-66` say that calls which "move no funds and have nothing to reverse
(e.g. flipping a flag on some contract)" "legitimately return `false`". Such a call's `to` is the
destination contract; where nothing is deployed at that address on the source chain, the call
reverts instead of returning `false`, and takes the whole claim with it.

The call that took the funds on the source chain is the indirect sender, `InteropCall.from`
(`InteropCenter.sol:739`), which the manager never reads. At `feat/upgrade-simplification`
(`e561b9cc2`), `atomic-interop/AtomicFlowManager.sol:308-310` calls `c.from` instead, and only when
it is the asset router.

## What is modelled

* **The code at an address** is one of three kinds (`Code`): nothing deployed; code implementing
  `recoverAtomicCall` (or a fallback returning a 32-byte word), which may read and write the rest
  of the world and returns a `bool` or reverts (`recoverer f`); and code that has neither
  (`other`). The classification is total.
* **How the call resolves** is a parameter `sem : CallSem`, constrained by the named premise
  `VmCall` (`VM-CALL`, `SOL-CONTROL`): with no code, or with `other` code, the high-level call
  reverts; with `recoverer f`, it is `f`. The pinned compiler is solc 0.8.28
  (`AtomicFlowManager.sol:2`); since 0.8.10 a high-level call that expects return data skips the
  `extcodesize` check, and then the ABI decoder rejects return data shorter than 32 bytes, which is
  what an account without code returns (on EraVM, an address without code runs the default account,
  which returns no data for a non-system call). Code without the selector and without a fallback
  reverts in its dispatcher. `vmCall` is the semantics `VmCall` describes.
* **The loop** (`recoverBundle`) is `_recoverBundle`'s: the calls in order, each on the world the
  previous one left, no `try/catch`, counting the calls that returned `true`. `claimRefund` is the
  one-leg transaction: enabled only on a `Revertable` leg, and reverting as a whole when the loop
  reverts or counts zero. A revert is `none` (`VM-REVERT`): the leg stays `Revertable` and nothing
  the loop did persists. The world `W`, the data `D`, the address type `A` and the call type `C` are
  generic; `to` and `data` are the two fields the manager reads.
* **The router model of `EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecovery`** is an instance:
  `routerRecoverer` is the router's `recoverAtomicCall` as the manager calls it, and `routerCodeMap`
  puts it at the router's address and B1's arbitrary `other` targets everywhere else.
-/

namespace Contracts.AtomicFlowManager.RecoveryTargets

open Contracts.AtomicFlowManager (LegState)

/-! ## The code at an address, and how the call resolves -/

/-- What is deployed at an address of the chain running `claimRefund` (the leg's source chain), as
the call `IAtomicRecoverable(c.to).recoverAtomicCall(destChainId, c.data)` (:225) sees it. -/
inductive Code (W D : Type) where
  /-- No code at the address. -/
  | none
  /-- Code implementing `recoverAtomicCall(uint256,bytes)` (or a fallback returning a 32-byte
  word): `f w destChainId data` is what it does when the manager calls it in world `w`;
  `some (w', b)` returns `b` and leaves world `w'`, `none` reverts. -/
  | recoverer (f : W → UInt256 → D → Option (W × Bool))
  /-- Code with neither that function nor a fallback returning data. -/
  | other

/-- How the call resolves, given the code at `c.to`, the world, `destChainId` and `c.data`. -/
abbrev CallSem (W D : Type) := Code W D → W → UInt256 → D → Option (W × Bool)

/-- **`VM-CALL` FOR THE CALL AT :225** (a named premise). A call to an address without code reverts
(the ABI decoder rejects the empty return data); a call to code without the function or a returning
fallback reverts; a call to a recoverer is that recoverer. -/
structure VmCall {W D : Type} (sem : CallSem W D) : Prop where
  noCode : ∀ w dest d, sem .none w dest d = Option.none
  noEntry : ∀ w dest d, sem .other w dest d = Option.none
  recoverer : ∀ f w dest d, sem (.recoverer f) w dest d = f w dest d

/-- The semantics `VmCall` describes. -/
def vmCall {W D : Type} : CallSem W D
  | .none, _, _, _ => Option.none
  | .recoverer f, w, dest, d => f w dest d
  | .other, _, _, _ => Option.none

/-- **NO RECOVERER AT `a`.** Nothing, or code without `recoverAtomicCall`, is deployed at `a` on the
chain running the refund. -/
def NoRecovererAt {W D A : Type} (code : A → Code W D) (a : A) : Prop :=
  code a = .none ∨ code a = .other

/-! ## The loop -/

/-- One iteration of the loop body (:224-227): the manager reads only `c.to` and `c.data`, and
passes the bundle's `destChainId`. -/
def recoverStep {W D A C : Type} (sem : CallSem W D) (code : A → Code W D) (target : C → A)
    (data : C → D) (dest : UInt256) (w : W) (c : C) : Option (W × Bool) :=
  sem (code (target c)) w dest (data c)

/-- `_recoverBundle`'s loop (:219-230): the calls in order, each on the world the previous one
left, no `try/catch`; `some (w, n)` counts the calls that returned `true`. -/
def recoverBundle {W C : Type} (step : W → C → Option (W × Bool)) : W → List C → Option (W × ℕ)
  | w, [] => some (w, 0)
  | w, c :: cs =>
    match step w c with
    | Option.none => Option.none
    | some (w', b) =>
      match recoverBundle step w' cs with
      | Option.none => Option.none
      | some (w'', n) => some (w'', (if b then 1 else 0) + n)

/-- `claimRefund` for one leg in state `s` (:165-180): enabled only on a `Revertable` leg (:170);
the leg is set `Reverted` before the loop (:175), and the loop must count at least one `true`
(:229). `none` is a revert of the whole transaction. -/
def claimRefund {W C : Type} (step : W → C → Option (W × Bool)) (s : LegState) (w : W)
    (calls : List C) : Option (LegState × W) :=
  if s ≠ LegState.Revertable then Option.none else
  match recoverBundle step w calls with
  | Option.none => Option.none
  | some (w', n) => if n = 0 then Option.none else some (LegState.Reverted, w')

/-- **THE RECOVERERS RETURN, IN TURN.** Every call's target has recoverer code, and each recoverer
returns on the world the previous one left: `bs` are the returned booleans and `w'` the final
world. -/
inductive RecoverersReturn {W D A C : Type} (code : A → Code W D) (target : C → A) (data : C → D)
    (dest : UInt256) : W → List C → List Bool → W → Prop
  | nil {w : W} : RecoverersReturn code target data dest w [] [] w
  | cons {w w' w'' : W} {c : C} {cs : List C} {b : Bool} {bs : List Bool}
      (f : W → UInt256 → D → Option (W × Bool)) :
      code (target c) = .recoverer f → f w dest (data c) = some (w', b) →
      RecoverersReturn code target data dest w' cs bs w'' →
      RecoverersReturn code target data dest w (c :: cs) (b :: bs) w''

/-- A recoverer that returns `true` and changes nothing, on any call. -/
def trueNoOp {W D : Type} : W → UInt256 → D → Option (W × Bool) := fun w _ _ => some (w, true)

/-! ## The router model of `AssetRouterBase/Specs/AtomicRecovery.lean` as a code map -/

section RouterInstance

open Contracts.AssetRouter Contracts.AssetRouter.AtomicRecovery

variable {X : Type}

/-- The router's `recoverAtomicCall` (`L2AssetRouter.sol:281-296`) as the manager calls it: caller
the manager. -/
def routerRecoverer (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) :
    World X → Chain → CallData → Option (World X × Bool) :=
  fun w dest d => recoverAtomicCall enc cfg hk w cfg.manager dest d

/-- B1's world as a code map: the router at `cfg.router`, B1's arbitrary `other target` at every
other address. -/
def routerCodeMap (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool)) :
    Address → Code (World X) CallData :=
  fun a => if a = cfg.router then .recoverer (routerRecoverer enc cfg hk) else .recoverer (other a)

/-- A code map with the router at `cfg.router`, a destination-only application `app` (nothing
deployed at its address on this chain), and B1's arbitrary `other` targets elsewhere. -/
def routerAndAppCodeMap (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (app : Address)
    (other : Address → World X → Chain → CallData → Option (World X × Bool)) :
    Address → Code (World X) CallData :=
  fun a => if a = cfg.router then .recoverer (routerRecoverer enc cfg hk)
    else if a = app then .none else .recoverer (other a)

end RouterInstance

/-! ## Witness data -/

/-- A call as the witnesses use it: `(to, from, data)`; the manager reads `to` and `data`. -/
abbrev TriCall := ℕ × ℕ × Unit

/-- Its `to`, the target. -/
def TriCall.target (c : TriCall) : ℕ := c.1

/-- Its `data`. -/
def TriCall.data (c : TriCall) : Unit := c.2.2

/-- The escrow witness: the world is the amount the indirect sender `1` holds for the depositor;
its own recoverer would release it. The destination-side address `2` holds unrelated code that
answers `true` and does nothing, address `3` code that answers `false` and does nothing, and every
other address holds nothing. -/
def escrowCode : ℕ → Code ℕ Unit :=
  fun a => if a = 1 then .recoverer (fun _ _ _ => some (0, true))
    else if a = 2 then .recoverer trueNoOp
    else if a = 3 then .recoverer (fun w _ _ => some (w, false)) else .none

end Contracts.AtomicFlowManager.RecoveryTargets
