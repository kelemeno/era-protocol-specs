import EraSpec.Protocol.NativeValueLegs.Specs.LegConservationRuns

/-!
# Properties: along every run, each refund is bound to the send that committed its leg

Statements about `EraSpec.Protocol.NativeValueLegs.Specs.LegConservationRuns` (head `b17415d20`).
Proofs are in `EraSpec.Protocol.NativeValueLegs.Proofs.LegConservationRuns`.

* **Headline.**  Along every run from fresh manager storage, every successful claim consumed the
  leg of a logged send `s`, and either decoded `s`'s own bundle and moved exactly
  `collected s.starters` of `s`'s destination base-token asset to `s.sender` (whenever `s` collected
  nothing, or collected through the holder or the vault, or the asset was registered in the tracker
  before the claim, or it does not originate on the source chain), or passed other bytes with the
  same keccak, a collision on two named byte strings (`EveryClaimRefundsItsSenderOrCollision`).
  The case left out is a claim that is the tracker's first registration of a token native to the
  source chain (see `ClaimMatches`).  Premises: the
  frame premise on the abstract code (`CodeFrames`), no logged send from the router, and the
  decoder round trip on the run's own bundles.  No hash premise.
* **Once.**  Each leg is committed by one send (`EachLegSentOnce`) and consumed by at most one claim
  (`EachLegClaimedAtMostOnce`), with no premise.  With the headline: a leg pays out its collected
  value at most once on the source chain.

The headline is about the claims that succeed; it does not state that a claim succeeds.
-/

namespace Contracts.NativeValueLegs

/-- **EVERY SUCCESSFUL REFUND IS BOUND TO ITS SEND, OR TO A PINNED KECCAK COLLISION.**  Along every run
from fresh manager storage over any world: if the abstract code satisfies `CodeFrames`, no logged
send is from the router, and the decoder inverts the encoder on every logged bundle, then every
logged claim satisfies `ClaimMatches` against the run's sends. -/
def Properties.EveryClaimRefundsItsSenderOrCollision : Prop :=
  ∀ (R : RunParams) (w₀ : World) (S : State),
    Reach R (State.init w₀) S → CodeFrames R.toParams →
    (∀ s ∈ S.sent, s.sender ≠ R.cfg.router) →
    (∀ s ∈ S.sent, R.dec (R.enc s.bundle) = some s.bundle) →
    ∀ r ∈ S.claimed, ClaimMatches R S.sent r

/-- **WITNESS FOR THE HEADLINE.**  A run satisfying every premise in which a claim passes the bytes of
a logged send that collected `collected > 0` through the vault. -/
def Properties.RunClaimWitness : Prop :=
  ∃ (R : RunParams) (w₀ : World) (S : State),
    Reach R (State.init w₀) S ∧ CodeFrames R.toParams ∧
      (∀ s ∈ S.sent, s.sender ≠ R.cfg.router) ∧
      (∀ s ∈ S.sent, R.dec (R.enc s.bundle) = some s.bundle) ∧
      ∃ r ∈ S.claimed, ∃ s ∈ S.sent, r.bytes = R.enc s.bundle ∧ s.route = .vault ∧
        0 < collected s.starters

/-- **EACH LEG IS COMMITTED BY ONE SEND.**  Along every run, the leg keys of the logged sends are
pairwise distinct. -/
def Properties.EachLegSentOnce : Prop :=
  ∀ (R : RunParams) (w₀ : World) (S : State),
    Reach R (State.init w₀) S → (S.sent.map (Sent.key R)).Nodup

/-- **EACH LEG IS CONSUMED BY AT MOST ONE CLAIM.**  Along every run, the leg keys of the logged
claims are pairwise distinct. -/
def Properties.EachLegClaimedAtMostOnce : Prop :=
  ∀ (R : RunParams) (w₀ : World) (S : State),
    Reach R (State.init w₀) S → (S.claimed.map (Claimed.key R)).Nodup

end Contracts.NativeValueLegs
