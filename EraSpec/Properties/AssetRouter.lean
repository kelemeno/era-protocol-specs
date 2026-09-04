import EraSpec.Contracts.AssetRouter

/-!
# Properties: the asset router's routing table

Statements about `EraSpec.Contracts.AssetRouter`.  Proofs are in
`EraSpec.Proofs.AssetRouter`.

Two separate protections, stated separately because they fail differently:

* `NoHijack` is structural.  The asset id is hashed from the caller, so a caller
  leaves untouched every handler whose id encodes anybody else — no matter what
  registration data it supplies, and regardless of the `require`.  If the guard
  were deleted tomorrow this would still hold.
* `OnlyTrackerOrNtvWrites` is the guard.  Among the ids a caller *can* name, only
  one whose recorded deployment tracker is already itself may be re-pointed.

`FreshIdNeedsNtv` is the consequence of putting them together: a non-vault caller
cannot make the first registration even for its own id, because the tracker starts
at zero and `msg.sender` never is.  So a custom deployment tracker has to be
bootstrapped through the native token vault or the L1-to-L2 counterpart path, not
by calling the router directly.
-/

namespace Properties.AssetRouter

open Contracts.AssetRouter

/-! ## The structural protection -/

/-- **A REGISTRATION TOUCHES ONE ID.**  Every handler except the one the call
computes is left alone. -/
def HandlerFrame : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R : Router)
    (caller : Address) (d : AssetData) (h : Address) (a : AssetId),
    a ≠ writtenId enc thisChain ntv ntvAddr caller d →
      (setHandler enc thisChain ntv ntvAddr R caller d h).handler a = R.handler a

/-- **NO HIJACK.**  A caller other than the native token vault cannot change the
handler of an asset whose id encodes a different registrant — whatever registration
data it passes.

This is the caller-in-the-key mechanism, and it does not depend on the `require`:
the id a call writes is a hash of the caller's own address, so an id hashed from
someone else is simply a different key. -/
def NoHijack : Prop :=
  ∀ (enc : AssetIdOf), IdAssumptions enc →
    ∀ (thisChain : Chain) (ntv ntvAddr : Address) (R : Router) (caller : Address)
      (d : AssetData) (h : Address), caller ≠ ntv →
    ∀ (s : Address) (d' : AssetData), s ≠ caller →
      (setHandler enc thisChain ntv ntvAddr R caller d h).handler (enc thisChain s d')
        = R.handler (enc thisChain s d')

/-- **THE VAULT IS NO EXCEPTION.**  The native token vault writes only ids hashed
from the fixed `L2_NATIVE_TOKEN_VAULT_ADDR`, so it cannot reach a custom
registrant's asset either — its privilege is bypassing the tracker check on its own
ids, not reaching other ids. -/
def NtvTouchesOnlyItsOwnIds : Prop :=
  ∀ (enc : AssetIdOf), IdAssumptions enc →
    ∀ (thisChain : Chain) (ntv ntvAddr : Address) (R : Router) (d : AssetData) (h : Address),
    ∀ (s : Address) (d' : AssetData), s ≠ ntvAddr →
      (setHandler enc thisChain ntv ntvAddr R ntv d h).handler (enc thisChain s d')
        = R.handler (enc thisChain s d')

/-! ## The guard -/

/-- **EVERY HANDLER CHANGE IS BY THE VAULT OR BY THE ASSET'S OWN TRACKER.**  If a
registration changed the handler of any asset, the caller was the native token vault
or the deployment tracker recorded for that very asset. -/
def OnlyTrackerOrNtvWrites : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R : Router)
    (caller : Address) (d : AssetData) (h : Address),
    SetGuard enc thisChain ntv ntvAddr R caller d →
    ∀ (a : AssetId),
      (setHandler enc thisChain ntv ntvAddr R caller d h).handler a ≠ R.handler a →
        caller = ntv ∨ caller = R.tracker a

/-- The tracker of the written id becomes the caller, which is what makes the guard
a fixed point: the same caller can re-register, nobody else can. -/
def TrackerRecordsCaller : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R : Router)
    (caller : Address) (d : AssetData) (h : Address),
    (setHandler enc thisChain ntv ntvAddr R caller d h).tracker
        (writtenId enc thisChain ntv ntvAddr caller d) = caller

/-- **A NON-VAULT CALLER CANNOT REGISTER A FRESH ID.**  The guard requires the
caller to be the recorded tracker, an unregistered id has tracker zero, and
`msg.sender` is never zero.  So the first registration for any id must come from
the native token vault (or, on an L2, from the L1 counterpart path). -/
def FreshIdNeedsNtv : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R : Router)
    (caller : Address) (d : AssetData), caller ≠ ntv →
    R.tracker (writtenId enc thisChain ntv ntvAddr caller d) = 0 →
      ¬ SetGuard enc thisChain ntv ntvAddr R caller d

/-! ## The run-level invariant -/

/-- Fresh storage is valid. -/
def EmptyValid : Prop := Valid empty

/-- **A LIVE ROUTE ALWAYS HAS AN ACCOUNTABLE TRACKER.**  At every point of every
run, an asset with a nonzero handler has a nonzero deployment tracker. -/
def RunValid : Prop :=
  ∀ (enc : AssetIdOf) (thisChain : Chain) (ntv ntvAddr : Address) (R : Router),
    Reach enc thisChain ntv ntvAddr empty R → Valid R

end Properties.AssetRouter
