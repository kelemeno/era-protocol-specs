import EraSpec.Contracts.InteropCenter.Properties.AtomicRouting
import EraSpec.Contracts.InteropCenter.Proofs.Dispatch
import EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryTargets

/-!
# Proofs: where an atomic leg's calls point, and an atomic leg sent to L1

The source component of every system run is a run of `Specs/Dispatch.lean`'s deployed code
(`sysReach_src`), so `Dispatch`'s invariants and `AtomicBytesNeverPublished` apply. One more
invariant, `SysInv`, carries the rest: the ghost send log matches the dispatch log and every
logged send has its shape; every handler status other than `Unreceived` is explained by bytes the
handler's `_verifyBundle` accepted, or by `executeAtomicBundle` where it exists; every `Reverted`
leg is explained by a logged successful claim. The headlines are then case splits on whether the
bytes behind a status or a claim have the dispatched bundle's own preimage (`abiEncode_right_inj`):
if so they are its bytes, otherwise there is a pinned keccak collision.
-/

namespace Contracts.InteropCenter.AtomicRouting

open Contracts.AtomicFlowManager (LegState Manager AppendGuard AuthorizeGuard ClaimGuard)
open Contracts.AtomicFlowManager.RecoveryTargets (Code CallSem VmCall NoRecovererAt recoverStep
  claimRefund recoverBundle vmCall vmCall_holds trueNoOp recoverStep_noRecoverer
  recoverBundle_none_of_noRecoverer claimRefund_none_of_loop claimRefund_revertable
  NonRecovererTargetBlocksClaim)
open AttackVectors.BundleStatusMachine (Status)

variable {W : Type}

/-! ## Lists -/

theorem forall₂_singleton_left {α β : Type} {R : α → β → Prop} {a : α} {l : List β}
    (h : List.Forall₂ R [a] l) : ∃ b, l = [b] ∧ R a b := by
  cases h with
  | cons hab hrest => cases hrest; exact ⟨_, rfl, hab⟩

theorem forall₂_and {α β : Type} {R Q : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ Q l₁ l₂ →
      List.Forall₂ (fun a b => R a b ∧ Q a b) l₁ l₂
  | _, _, .nil, _ => .nil
  | _, _, .cons hr hrs, hq => by
    cases hq with
    | cons hq hqs => exact .cons ⟨hr, hq⟩ (forall₂_and hrs hqs)

/-! ## The source chain is a `Dispatch` run -/

theorem sysStep_src {K : Guards} {E : Env W} {S S' : Sys W} (h : SysStep K E S S') :
    S'.src = S.src ∨ Step deployed E.P S.src S'.src := by
  cases h with
  | send s ok =>
    exact Or.inr (Step.send s.dispatch (fun _ => ok.salt) ok.shape.formed
      (fun hat _ => ok.shape.validated hat) ok.append)
  | authorize f h hg _ _ => exact Or.inr (Step.authorize f h hg)
  | claim f x w' hcl => exact Or.inr (Step.claim f _ (claimRefund_revertable hcl))
  | handler c H _ => exact Or.inl rfl
  | env w' => exact Or.inl rfl

theorem sysReach_src {K : Guards} {E : Env W} {w₀ : W} {S : Sys W}
    (h : SysReach K E (sysInit w₀) S) : Reach deployed E.P init S.src := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    rcases sysStep_src hs with heq | hstep
    · rw [heq]; exact ih
    · exact .tail ih hstep

/-! ## Handlers -/

/-- What every handler state satisfies. -/
structure HInv (E : Env W) (c : Word) (H : Handler) : Prop where
  verified : ∀ x ∈ H.verified, E.included (E.dec x).sourceChainId x ∧ (E.dec x).destinationChainId = c
  status : ∀ h, H.status h ≠ .Unreceived →
    (∃ x ∈ H.verified, handlerHash E x = h) ∨ (atomicEntry (destKind E c) = true ∧ E.finalized c h)

theorem hInv_init (E : Env W) (c : Word) : HInv E c Handler.init where
  verified := by simp [Handler.init]
  status := by intro h hne; exact absurd rfl hne

theorem setStatus_apply (st : Word → Status) (h h' : Word) (s : Status) :
    setStatus st h s h' = if h' = h then s else st h' := rfl

theorem hInv_step {E : Env W} {c : Word} {H H' : Handler} (hs : HandlerStep E c H H')
    (hI : HInv E c H) : HInv E c H' := by
  cases hs with
  | verify x hinc hdst hU =>
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hI.verified y hy
      · rw [List.mem_singleton] at hy; subst hy; exact ⟨hinc, hdst⟩
    · intro h hne
      dsimp only at hne ⊢
      rw [setStatus_apply] at hne
      by_cases hh : h = handlerHash E x
      · exact Or.inl ⟨x, by simp, hh.symm⟩
      · rw [ite_eq_right hh] at hne
        rcases hI.status h hne with ⟨y, hy, hyh⟩ | hat
        · exact Or.inl ⟨y, List.mem_append_left _ hy, hyh⟩
        · exact Or.inr hat
  | executeFresh x hinc hdst hU =>
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hI.verified y hy
      · rw [List.mem_singleton] at hy; subst hy; exact ⟨hinc, hdst⟩
    · intro h hne
      dsimp only at hne ⊢
      rw [setStatus_apply] at hne
      by_cases hh : h = handlerHash E x
      · exact Or.inl ⟨x, by simp, hh.symm⟩
      · rw [ite_eq_right hh] at hne
        rcases hI.status h hne with ⟨y, hy, hyh⟩ | hat
        · exact Or.inl ⟨y, List.mem_append_left _ hy, hyh⟩
        · exact Or.inr hat
  | executeVerified x hV =>
    refine ⟨hI.verified, ?_⟩
    intro h hne
    dsimp only at hne ⊢
    rw [setStatus_apply] at hne
    by_cases hh : h = handlerHash E x
    · subst hh
      exact hI.status _ (by rw [hV]; exact Status.noConfusion)
    · rw [ite_eq_right hh] at hne
      exact hI.status h hne
  | unbundle x hV =>
    refine ⟨hI.verified, ?_⟩
    intro h hne
    dsimp only at hne ⊢
    rw [setStatus_apply] at hne
    by_cases hh : h = handlerHash E x
    · subst hh
      refine hI.status _ ?_
      rcases hV with hV | hV <;> rw [hV] <;> exact Status.noConfusion
    · rw [ite_eq_right hh] at hne
      exact hI.status h hne
  | executeAtomic x hent hfin hdst hU =>
    refine ⟨hI.verified, ?_⟩
    intro h hne
    dsimp only at hne ⊢
    rw [setStatus_apply] at hne
    by_cases hh : h = handlerHash E x
    · subst hh; exact Or.inr ⟨hent, hfin⟩
    · rw [ite_eq_right hh] at hne
      exact hI.status h hne

/-! ## The system invariant -/

/-- What every reachable system state satisfies. -/
structure SysInv (K : Guards) (E : Env W) (S : Sys W) : Prop where
  log : S.src.log = S.sends.map Send.dispatch
  shape : ∀ s ∈ S.sends, SendShape K E s
  handlers : ∀ c, HInv E c (S.dst c)
  reverted : ∀ f h, S.src.manager.legState f h = .Reverted →
    ∃ x, (f, x) ∈ S.claims ∧ handlerHash E x = h
  claims : ∀ p ∈ S.claims, ∃ w w',
    claimRefund (refundStep E p.2) .Revertable w (E.dec p.2).calls = some (.Reverted, w')

theorem sysInv_init (K : Guards) (E : Env W) (w₀ : W) : SysInv K E (sysInit w₀) where
  log := rfl
  shape := by simp [sysInit]
  handlers := fun c => hInv_init E c
  reverted := by
    intro f h hR
    exact absurd hR (by simp [sysInit, init])
  claims := by simp [sysInit]

theorem sysInv_step {K : Guards} {E : Env W} {S S' : Sys W} (hs : SysStep K E S S')
    (hI : SysInv K E S) : SysInv K E S' := by
  cases hs with
  | send s ok =>
    refine ⟨?_, ?_, hI.handlers, ?_, hI.claims⟩
    · show S.src.log ++ [s.dispatch] = (S.sends ++ [s]).map Send.dispatch
      rw [hI.log, List.map_append, List.map_singleton]
    · intro s' hs'
      rcases List.mem_append.mp hs' with hs' | hs'
      · exact hI.shape s' hs'
      · rw [List.mem_singleton] at hs'; subst hs'; exact ok.shape
    · intro f h hR
      have hR' : (S.src.afterSend E.P s.dispatch).manager.legState f h = .Reverted := hR
      rw [afterSend_legState] at hR'
      split_ifs at hR' with hc
      exact hI.reverted f h hR'
  | authorize f₀ h₀ hg _ _ =>
    refine ⟨hI.log, hI.shape, hI.handlers, ?_, hI.claims⟩
    intro f h hR
    have hR' : (S.src.manager.set f₀ h₀ .Revertable).legState f h = .Reverted := hR
    rw [legState_set] at hR'
    split_ifs at hR' with hc
    exact hI.reverted f h hR'
  | claim f₀ x₀ w' hcl =>
    refine ⟨hI.log, hI.shape, hI.handlers, ?_, ?_⟩
    · intro f h hR
      have hR' : (S.src.manager.set f₀ (handlerHash E x₀) .Reverted).legState f h = .Reverted := hR
      rw [legState_set] at hR'
      by_cases hc : f = f₀ ∧ h = handlerHash E x₀
      · obtain ⟨rfl, rfl⟩ := hc
        exact ⟨x₀, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
      · rw [ite_eq_right hc] at hR'
        obtain ⟨x, hx, hxh⟩ := hI.reverted f h hR'
        exact ⟨x, List.mem_append_left _ hx, hxh⟩
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hI.claims p hp
      · rw [List.mem_singleton] at hp
        subst hp
        have hst := claimRefund_revertable hcl
        rw [hst] at hcl
        exact ⟨S.world, w', hcl⟩
  | handler c H hstep =>
    refine ⟨hI.log, hI.shape, ?_, hI.reverted, hI.claims⟩
    intro c'
    show HInv E c' (if c' = c then H else S.dst c')
    by_cases hc : c' = c
    · rw [ite_eq_left hc]; subst hc; exact hInv_step hstep (hI.handlers c')
    · rw [ite_eq_right hc]; exact hI.handlers c'
  | env w' => exact ⟨hI.log, hI.shape, hI.handlers, hI.reverted, hI.claims⟩

theorem sysInv_reach {K : Guards} {E : Env W} {w₀ : W} {S : Sys W}
    (h : SysReach K E (sysInit w₀) S) : SysInv K E S := by
  induction h with
  | refl => exact sysInv_init K E w₀
  | tail _ hs ih => exact sysInv_step hs ih

/-- A logged dispatch is a logged send's. -/
theorem send_of_dispatch {K : Guards} {E : Env W} {S : Sys W} (hI : SysInv K E S) {d : Dispatch}
    (hd : d ∈ S.src.log) : ∃ s ∈ S.sends, s.dispatch = d := by
  rw [hI.log] at hd
  exact List.mem_map.mp hd

/-! ## (a) Routing -/

/-- The shape of an L1-destined send. -/
theorem l1_send_call {K : Guards} {E : Env W} {s : Send} (sh : SendShape K E s)
    (hdest : s.dest = E.l1ChainId) :
    ∃ c, s.dispatch.bundle.calls = [c] ∧ c.target = E.l1Router ∧ c.fromAddr = E.l2Router ∧
      c.value = 0 ∧ ∃ (assetId : Word) (mintData : List UInt8),
        c.data = E.depositCalldata E.P.chainId assetId mintData := by
  obtain ⟨cs, hcs⟩ := List.length_eq_one_iff.mp (sh.l1OneCall hdest)
  have hF := sh.formed.calls
  have hR := sh.routed
  rw [hcs] at hF hR
  obtain ⟨c, hcalls, hc⟩ := forall₂_singleton_left hF
  rw [hcalls] at hR
  obtain ⟨hind, htgt, hval⟩ := sh.l1Withdrawal hdest cs (by rw [hcs]; exact List.mem_singleton_self _)
  obtain ⟨_, _, hRc⟩ := forall₂_singleton_left hR
  have hRc' := hRc
  obtain ⟨hto, hdata⟩ := (List.forall₂_cons.mp hR).1 hind htgt
  rw [ite_eq_left hdest] at hto
  exact ⟨c, hcalls, hto, (hc.indirect hind).trans htgt, hc.value.trans hval, hdata⟩

theorem AtomicL1BundleCarriesL1RouterTarget : Properties.AtomicL1BundleCarriesL1RouterTarget := by
  intro W K E w₀ S hr s hs hdest
  obtain ⟨c, hcalls, hto, hfrom, hval, hdata⟩ := l1_send_call ((sysInv_reach hr).shape s hs) hdest
  refine ⟨c, hcalls, hto, hfrom, hval, hdata, fun w => ?_⟩
  unfold recoverStep
  rw [hto]

/-- `atomicSendOf`'s atomic flag, by cases. -/
theorem atomicSendOf_isAtomic (K : Guards) (e : EntryPoint) (a : Option AtomicAttr) :
    (atomicSendOf K e a).isAtomic = true ↔
      a.isSome = true ∧ (e = .sendBundle ∨ K.messageHonoursAtomic = true) := by
  rcases K with ⟨k₁, _ | _⟩ <;> rcases e with _ | _ <;> rcases a with _ | a <;> simp [atomicSendOf]

theorem AttributeRoutingByEntryPoint : Properties.AttributeRoutingByEntryPoint := by
  intro W K E w₀ S hr s hs
  have ha := ((sysInv_reach hr).shape s hs).atomicSend
  have hat : s.dispatch.isAtomic = (atomicSendOf K s.entry s.attr).isAtomic := by
    show s.dispatch.atomicSend.isAtomic = _
    rw [ha]
  rw [hat]
  exact atomicSendOf_isAtomic K s.entry s.attr

/-! ## (b)–(d) -/

/-- The run-local encoding premise follows from the decoding premise. -/
theorem encInjOn_of_decodes {E : Env W} {S : Sys W} (h : DecodesRunBundles E S) :
    EncInjOn E.P.enc (S.src.log.map Dispatch.bundle) := by
  intro b hb b' hb' he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
  obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hb'
  rw [← h d hd, ← h d' hd', he]

theorem AtomicToL1NeverExecuted : Properties.AtomicToL1NeverExecuted := by
  intro W K E w₀ S hr hhon hdec d hd hat
  have henc := encInjOn_of_decodes hdec
  have hsrc := sysReach_src hr
  have hI := sysInv_reach hr
  by_cases hU : (S.dst E.l1ChainId).status (bundleHash E.P d.bundle) = .Unreceived
  · exact Or.inl hU
  right
  rcases (hI.handlers E.l1ChainId).status _ hU with ⟨x, hx, hxh⟩ | ⟨hent, _⟩
  · by_cases hpre : claimPreimage E.dec x = bundlePreimage E.P d.bundle
    · left
      have hxe : x = E.P.enc d.bundle := abiEncode_right_inj hpre
      have hinc := ((hI.handlers E.l1ChainId).verified x hx).1
      rw [hxe, hdec d hd, ((inv_reach hsrc).formed d hd).source] at hinc
      obtain ⟨d', hd', hpub, hbytes⟩ := hhon _ hinc
      rcases AtomicBytesNeverPublished E.P S.src hsrc henc d hd hat d' hd' hpub with hne | hc
      · exact absurd hbytes.symm hne
      · exact ⟨d', hd', hpub, hc⟩
    · exact Or.inr ⟨x, hx, hpre, hxh⟩
  · exact absurd hent (by simp [destKind, atomicEntry])

theorem AtomicToL1ClaimReverts : Properties.AtomicToL1ClaimReverts := by
  intro W K E w₀ S hr hvm hno hdec d hd hat hdest x hxh
  by_cases hpre : claimPreimage E.dec x = bundlePreimage E.P d.bundle
  · left
    have hI := sysInv_reach hr
    have hxe : x = E.P.enc d.bundle := abiEncode_right_inj hpre
    obtain ⟨s, hs, rfl⟩ := send_of_dispatch hI hd
    obtain ⟨c, hcalls, hto, -⟩ := l1_send_call (hI.shape s hs) hdest
    intro st w
    rw [hxe]
    unfold refundStep
    rw [hdec _ hd, hcalls]
    exact claimRefund_none_of_loop
      (recoverBundle_none_of_noRecoverer hvm _ w ⟨c, List.mem_singleton_self _, by rw [hto]; exact hno⟩)
  · exact Or.inr hpre

theorem NonRecovererLegNeverRefunded : Properties.NonRecovererLegNeverRefunded := by
  intro W K E w₀ S hr hvm hdec d hd hat hex
  have hI := sysInv_reach hr
  by_cases hR : S.src.manager.legState d.atomicSend.flowId (bundleHash E.P d.bundle) = .Reverted
  · right
    obtain ⟨x, hmem, hxh⟩ := hI.reverted _ _ hR
    by_cases hpre : claimPreimage E.dec x = bundlePreimage E.P d.bundle
    · exfalso
      obtain ⟨w, w', hcl⟩ := hI.claims _ hmem
      have hxe : x = E.P.enc d.bundle := abiEncode_right_inj hpre
      simp only at hcl
      rw [hxe] at hcl
      unfold refundStep at hcl
      rw [hdec _ hd] at hcl
      rw [claimRefund_none_of_loop (recoverBundle_none_of_noRecoverer hvm _ w hex)] at hcl
      cases hcl
    · exact ⟨(d.atomicSend.flowId, x), hmem, hpre, hxh⟩
  · exact Or.inl hR

theorem AtomicToL1Stranded : Properties.AtomicToL1Stranded := by
  intro W K E w₀ S hr hvm hno hhon hdec d hd hat hdest
  refine ⟨AtomicToL1NeverExecuted W K E w₀ S hr hhon hdec d hd hat,
    NonRecovererLegNeverRefunded W K E w₀ S hr hvm hdec d hd hat ?_⟩
  have hI := sysInv_reach hr
  obtain ⟨s, hs, rfl⟩ := send_of_dispatch hI hd
  obtain ⟨c, hcalls, hto, -⟩ := l1_send_call (hI.shape s hs) hdest
  exact ⟨c, by rw [hcalls]; exact List.mem_singleton_self _, by rw [hto]; exact hno⟩

/-! ## (f) -/

theorem IndirectL2RouterLegsReachSourceRouter :
    Properties.IndirectL2RouterLegsReachSourceRouter := by
  intro W K E w₀ S hr s hs hdest
  have sh := (sysInv_reach hr).shape s hs
  refine (forall₂_and sh.formed.calls sh.routed).imp ?_
  rintro cs c ⟨hform, hroute⟩ hind htgt
  obtain ⟨hto, hdata⟩ := hroute hind htgt
  rw [ite_eq_right hdest] at hto
  refine ⟨hto, (hform.indirect hind).trans htgt, hdata, fun w => ?_⟩
  unfold recoverStep
  rw [hto]

/-! ## (i) -/

theorem AttributeHonouredOrRejected : Properties.AttributeHonouredOrRejected := by
  intro W E w₀ S hr s hs
  refine ⟨?_, fun ha => ?_⟩
  · rw [AttributeRoutingByEntryPoint W upgradeTree E w₀ S hr s hs]
    simp [upgradeTree]
  · have hne := ((sysInv_reach hr).shape s hs).atomicNotToL1 rfl ha
    simp [destKind, hne, atomicEntry]

theorem GuardKeepsAtomicLegsOffL1 : Properties.GuardKeepsAtomicLegsOffL1 := by
  intro W K E w₀ S hK hr d hd hat
  have hI := sysInv_reach hr
  obtain ⟨s, hs, rfl⟩ := send_of_dispatch hI hd
  exact (hI.shape s hs).atomicNotToL1 hK hat


/-! ## Witness runs

One pinned run carries every pinned witness: a public withdrawal `sW` and an atomic withdrawal
`sL` to L1; the `sendMessage` `s1` carrying the attribute of flow `9` and the other leg `s2` of that
flow; the atomic leg `sG` of a router call and a direct call to an address with nothing deployed on
the source chain. L1 then executes `sW`, chain `325` executes `s1`, the three atomic legs are
authorized, and `s2` is claimed. The `upgradeTree` run sends `sW`, `sG`, `sM` and `sMA`. -/

/-- A system send. -/
def Sys.sendS (E : Env W) (S : Sys W) (s : Send) : Sys W :=
  { S with src := S.src.afterSend E.P s.dispatch, sends := S.sends ++ [s] }

/-- A system `authorizeRefund`. -/
def Sys.authS (S : Sys W) (f h : Word) : Sys W :=
  { S with src := { S.src with manager := S.src.manager.set f h .Revertable } }

/-- A system `claimRefund`. -/
def Sys.claimS (E : Env W) (S : Sys W) (f : Word) (x : List UInt8) (w' : W) : Sys W :=
  { S with
    src := { S.src with manager := S.src.manager.set f (handlerHash E x) .Reverted },
    world := w', claims := S.claims ++ [(f, x)] }

/-- A system handler transaction. -/
def Sys.handlerS (S : Sys W) (c : Word) (H : Handler) : Sys W :=
  { S with dst := fun c' => if c' = c then H else S.dst c' }

theorem lastWord_saltWordsEncoder (b : Bundle) :
    lastWord (saltWordsEncoder b) = b.bundleAttributes.salt := by
  unfold saltWordsEncoder
  rw [lastWord_append_word, ofNat_val]

theorem arEnv_dec : arEnv.dec = arDec := rfl

theorem arEnv_P : arEnv.P = wParams := rfl

theorem arDec_enc (b : Bundle) : arDec (wParams.enc b) =
    if b.bundleAttributes.salt = 1 then arSL.dispatch.bundle
    else if b.bundleAttributes.salt = 2 then arSW.dispatch.bundle
    else if b.bundleAttributes.salt = 3 then arS1.dispatch.bundle
    else if b.bundleAttributes.salt = 4 then arS2.dispatch.bundle
    else if b.bundleAttributes.salt = 5 then arSG.dispatch.bundle
    else arSM.dispatch.bundle := by
  unfold arDec
  rw [show wParams.enc b = saltWordsEncoder b from rfl, lastWord_saltWordsEncoder]

theorem arDec_SW : arEnv.dec (arEnv.P.enc arSW.dispatch.bundle) = arSW.dispatch.bundle := by
  rw [arEnv_dec, arEnv_P, arDec_enc]; rfl
theorem arDec_SL : arEnv.dec (arEnv.P.enc arSL.dispatch.bundle) = arSL.dispatch.bundle := by
  rw [arEnv_dec, arEnv_P, arDec_enc]; rfl
theorem arDec_S1 : arEnv.dec (arEnv.P.enc arS1.dispatch.bundle) = arS1.dispatch.bundle := by
  rw [arEnv_dec, arEnv_P, arDec_enc]; rfl
theorem arDec_S2 : arEnv.dec (arEnv.P.enc arS2.dispatch.bundle) = arS2.dispatch.bundle := by
  rw [arEnv_dec, arEnv_P, arDec_enc]; rfl
theorem arDec_SG : arEnv.dec (arEnv.P.enc arSG.dispatch.bundle) = arSG.dispatch.bundle := by
  rw [arEnv_dec, arEnv_P, arDec_enc]; rfl
theorem arDec_SM : arEnv.dec (arEnv.P.enc arSM.dispatch.bundle) = arSM.dispatch.bundle := by
  rw [arEnv_dec, arEnv_P, arDec_enc]; rfl

theorem claimPreimage_enc {E : Env W} {b : Bundle} (hdec : E.dec (E.P.enc b) = b)
    (hsrc : b.sourceChainId = E.P.chainId) :
    claimPreimage E.dec (E.P.enc b) = bundlePreimage E.P b := by
  unfold claimPreimage bundlePreimage
  rw [hdec, hsrc]

theorem handlerHash_enc {E : Env W} {b : Bundle} (hdec : E.dec (E.P.enc b) = b)
    (hsrc : b.sourceChainId = E.P.chainId) :
    handlerHash E (E.P.enc b) = bundleHash E.P b := by
  unfold handlerHash bundleHash
  rw [claimPreimage_enc hdec hsrc]


theorem afterSend_saltUsed (P : Params) (S : State) (d : Dispatch) (a : Address) (s : Word) :
    (S.afterSend P d).saltUsed a s = if a = d.sender ∧ s = d.salt then true else S.saltUsed a s := rfl

theorem arHash (b : Bundle) : bundleHash arEnv.P b = b.bundleAttributes.salt := bundleHash_wParams b

/-! ### The shapes of the witness sends -/

theorem arShape_SW (K : Guards) : SendShape K arEnv arSW where
  atomicSend := rfl
  sourceNotL1 := by decide
  notSelf := by decide
  messageNotToL1 := fun h => absurd h (by decide)
  messageOneCall := fun h => absurd h (by decide)
  l1OneCall := fun _ => rfl
  l1Withdrawal := by
    intro _ cs hcs
    rw [show arSW.dispatch.starters = [arRouterStarter] from rfl, List.mem_singleton] at hcs
    subst hcs
    exact ⟨rfl, rfl, rfl⟩
  formed := ⟨rfl, rfl, .cons ⟨rfl, fun _ => rfl, fun h => absurd h (by decide)⟩ .nil⟩
  routed := .cons (fun _ _ => ⟨rfl, 0, [], rfl⟩) .nil
  validated := fun h => absurd h (by decide)
  atomicNotToL1 := fun _ h => absurd h (by decide)

theorem arShape_SL : SendShape pin arEnv arSL where
  atomicSend := rfl
  sourceNotL1 := by decide
  notSelf := by decide
  messageNotToL1 := fun h => absurd h (by decide)
  messageOneCall := fun h => absurd h (by decide)
  l1OneCall := fun _ => rfl
  l1Withdrawal := by
    intro _ cs hcs
    rw [show arSL.dispatch.starters = [arRouterStarter] from rfl, List.mem_singleton] at hcs
    subst hcs
    exact ⟨rfl, rfl, rfl⟩
  formed := ⟨rfl, rfl, .cons ⟨rfl, fun _ => rfl, fun h => absurd h (by decide)⟩ .nil⟩
  routed := .cons (fun _ _ => ⟨rfl, 0, [], rfl⟩) .nil
  validated := by
    intro _ c hc
    rw [show arSL.dispatch.bundle.calls = [arL1Call] from rfl, List.mem_singleton] at hc
    subst hc; rfl
  atomicNotToL1 := fun h => absurd h (by decide)

theorem arShape_S1 : SendShape pin arEnv arS1 where
  atomicSend := rfl
  sourceNotL1 := by decide
  notSelf := by decide
  messageNotToL1 := fun _ => by decide
  messageOneCall := fun _ => rfl
  l1OneCall := fun h => absurd h (by decide)
  l1Withdrawal := fun h => absurd h (by decide)
  formed := ⟨rfl, rfl, .cons ⟨rfl, fun h => absurd h (by decide), fun _ => ⟨rfl, rfl, rfl⟩⟩ .nil⟩
  routed := .cons (fun h _ => absurd h (by decide)) .nil
  validated := fun h => absurd h (by decide)
  atomicNotToL1 := fun h => absurd h (by decide)

theorem arShape_S2 (K : Guards) : SendShape K arEnv arS2 where
  atomicSend := rfl
  sourceNotL1 := by decide
  notSelf := by decide
  messageNotToL1 := fun h => absurd h (by decide)
  messageOneCall := fun h => absurd h (by decide)
  l1OneCall := fun h => absurd h (by decide)
  l1Withdrawal := fun h => absurd h (by decide)
  formed := ⟨rfl, rfl, .cons ⟨rfl, fun _ => rfl, fun h => absurd h (by decide)⟩ .nil⟩
  routed := .cons (fun _ _ => ⟨rfl, 0, [], rfl⟩) .nil
  validated := by
    intro _ c hc
    rw [show arS2.dispatch.bundle.calls = [arL2Call] from rfl, List.mem_singleton] at hc
    subst hc; rfl
  atomicNotToL1 := fun _ _ => by decide

theorem arShape_SG (K : Guards) : SendShape K arEnv arSG where
  atomicSend := rfl
  sourceNotL1 := by decide
  notSelf := by decide
  messageNotToL1 := fun h => absurd h (by decide)
  messageOneCall := fun h => absurd h (by decide)
  l1OneCall := fun h => absurd h (by decide)
  l1Withdrawal := fun h => absurd h (by decide)
  formed := ⟨rfl, rfl, .cons ⟨rfl, fun _ => rfl, fun h => absurd h (by decide)⟩
    (.cons ⟨rfl, fun h => absurd h (by decide), fun _ => ⟨rfl, rfl, rfl⟩⟩ .nil)⟩
  routed := .cons (fun _ _ => ⟨rfl, 0, [], rfl⟩) (.cons (fun h _ => absurd h (by decide)) .nil)
  validated := by
    intro _ c hc
    rw [show arSG.dispatch.bundle.calls = [arL2Call, arAppCall 1] from rfl] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> rfl
  atomicNotToL1 := fun _ _ => by decide

theorem arShape_SM (K : Guards) : SendShape K arEnv arSM where
  atomicSend := rfl
  sourceNotL1 := by decide
  notSelf := by decide
  messageNotToL1 := fun _ => by decide
  messageOneCall := fun _ => rfl
  l1OneCall := fun h => absurd h (by decide)
  l1Withdrawal := fun h => absurd h (by decide)
  formed := ⟨rfl, rfl, .cons ⟨rfl, fun h => absurd h (by decide), fun _ => ⟨rfl, rfl, rfl⟩⟩ .nil⟩
  routed := .cons (fun h _ => absurd h (by decide)) .nil
  validated := fun h => absurd h (by decide)
  atomicNotToL1 := fun _ h => absurd h (by decide)

theorem arShape_SMA : SendShape upgradeTree arEnv arSMA where
  atomicSend := rfl
  sourceNotL1 := by decide
  notSelf := by decide
  messageNotToL1 := fun _ => by decide
  messageOneCall := fun _ => rfl
  l1OneCall := fun h => absurd h (by decide)
  l1Withdrawal := fun h => absurd h (by decide)
  formed := ⟨rfl, rfl, .cons ⟨rfl, fun h => absurd h (by decide), fun _ => ⟨rfl, rfl, rfl⟩⟩ .nil⟩
  routed := .cons (fun h _ => absurd h (by decide)) .nil
  validated := by
    intro _ c hc
    rw [show arSMA.dispatch.bundle.calls = [arAppCall 2] from rfl, List.mem_singleton] at hc
    subst hc; rfl
  atomicNotToL1 := fun _ _ => by decide


/-! ### The pinned run -/

/-- The bytes of the witness bundles. -/
abbrev arX (s : Send) : List UInt8 := arEnv.P.enc s.dispatch.bundle

def arR1 : Sys Unit := (sysInit ()).sendS arEnv arSW
def arR2 : Sys Unit := arR1.sendS arEnv arSL
def arR3 : Sys Unit := arR2.sendS arEnv arS1
def arR4 : Sys Unit := arR3.sendS arEnv arS2
def arR5 : Sys Unit := arR4.sendS arEnv arSG

/-- L1 executes the public withdrawal. -/
def arH6 : Handler :=
  ⟨setStatus (arR5.dst 1).status (handlerHash arEnv (arX arSW)) .FullyExecuted,
    (arR5.dst 1).verified ++ [arX arSW]⟩
def arR6 : Sys Unit := arR5.handlerS 1 arH6

/-- Chain `325` executes the `sendMessage` bundle `s1`. -/
def arH7 : Handler :=
  ⟨setStatus (arR6.dst 325).status (handlerHash arEnv (arX arS1)) .FullyExecuted,
    (arR6.dst 325).verified ++ [arX arS1]⟩
def arR7 : Sys Unit := arR6.handlerS 325 arH7

def arR8 : Sys Unit := arR7.authS 7 1
def arR9 : Sys Unit := arR8.authS 9 4
def arR10 : Sys Unit := arR9.authS 8 5
def arR11 : Sys Unit := arR10.claimS arEnv 9 (arX arS2) ()

theorem arLog : arR11.src.log = [arSW.dispatch, arSL.dispatch, arS1.dispatch, arS2.dispatch,
    arSG.dispatch] := rfl

theorem arSends : arR11.sends = [arSW, arSL, arS1, arS2, arSG] := rfl

theorem arClaims : arR11.claims = [(9, arX arS2)] := rfl

/-- The manager after the five sends. -/
theorem arR5_leg (f h : Word) : arR5.src.manager.legState f h =
    if f = 8 ∧ h = 5 then .Committed else if f = 9 ∧ h = 4 then .Committed
    else if f = 7 ∧ h = 1 then .Committed else .Unset := by
  show ((((((init.afterSend wParams arSW.dispatch).afterSend wParams arSL.dispatch).afterSend
    wParams arS1.dispatch).afterSend wParams arS2.dispatch).afterSend wParams arSG.dispatch)).manager.legState f h = _
  simp only [afterSend_legState, bundleHash_wParams]
  simp [arSW, arSL, arS1, arS2, arSG, arBundle, wAttrs, init]

theorem arDec_bundles : DecodesRunBundles arEnv arR11 := by
  unfold DecodesRunBundles
  rw [arLog]
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl
  · exact arDec_SW
  · exact arDec_SL
  · exact arDec_S1
  · exact arDec_S2
  · exact arDec_SG

theorem arHH (s : Send) (hd : arEnv.dec (arEnv.P.enc s.dispatch.bundle) = s.dispatch.bundle)
    (hsrc : s.dispatch.bundle.sourceChainId = arEnv.P.chainId) :
    handlerHash arEnv (arX s) = s.dispatch.bundle.bundleAttributes.salt := by
  rw [show arX s = arEnv.P.enc s.dispatch.bundle from rfl, handlerHash_enc hd hsrc, arHash]

theorem arHH_SW : handlerHash arEnv (arX arSW) = 2 := arHH arSW arDec_SW rfl
theorem arHH_SL : handlerHash arEnv (arX arSL) = 1 := arHH arSL arDec_SL rfl
theorem arHH_S1 : handlerHash arEnv (arX arS1) = 3 := arHH arS1 arDec_S1 rfl
theorem arHH_S2 : handlerHash arEnv (arX arS2) = 4 := arHH arS2 arDec_S2 rfl
theorem arHH_SG : handlerHash arEnv (arX arSG) = 5 := arHH arSG arDec_SG rfl

theorem arStep1 : SysStep pin arEnv (sysInit ()) arR1 :=
  SysStep.send arSW ⟨arShape_SW pin, rfl, fun h => absurd h (by decide)⟩

theorem arStep2 : SysStep pin arEnv arR1 arR2 := by
  refine SysStep.send arSL ⟨arShape_SL, ?_, fun _ => ?_⟩
  · show (init.afterSend wParams arSW.dispatch).saltUsed 1 1 = false
    rw [afterSend_saltUsed]; rfl
  · show (init.afterSend wParams arSW.dispatch).manager.legState 7 (bundleHash wParams arSL.dispatch.bundle) = .Unset
    rw [afterSend_legState]; rfl


theorem arStep3 : SysStep pin arEnv arR2 arR3 := by
  refine SysStep.send arS1 ⟨arShape_S1, ?_, fun h => absurd h (by decide)⟩
  show ((init.afterSend wParams arSW.dispatch).afterSend wParams arSL.dispatch).saltUsed 1 3 = false
  rw [afterSend_saltUsed, afterSend_saltUsed]; rfl

theorem arStep4 : SysStep pin arEnv arR3 arR4 := by
  refine SysStep.send arS2 ⟨arShape_S2 pin, ?_, fun _ => ?_⟩
  · show (((init.afterSend wParams arSW.dispatch).afterSend wParams arSL.dispatch).afterSend wParams
      arS1.dispatch).saltUsed 1 4 = false
    rw [afterSend_saltUsed, afterSend_saltUsed, afterSend_saltUsed]; rfl
  · show (((init.afterSend wParams arSW.dispatch).afterSend wParams arSL.dispatch).afterSend wParams
      arS1.dispatch).manager.legState 9 (bundleHash wParams arS2.dispatch.bundle) = .Unset
    simp only [afterSend_legState, bundleHash_wParams]
    simp [arSW, arSL, arS1, arS2, arBundle, wAttrs, init]

theorem arStep5 : SysStep pin arEnv arR4 arR5 := by
  refine SysStep.send arSG ⟨arShape_SG pin, ?_, fun _ => ?_⟩
  · show ((((init.afterSend wParams arSW.dispatch).afterSend wParams arSL.dispatch).afterSend wParams
      arS1.dispatch).afterSend wParams arS2.dispatch).saltUsed 1 5 = false
    rw [afterSend_saltUsed, afterSend_saltUsed, afterSend_saltUsed, afterSend_saltUsed]; rfl
  · show ((((init.afterSend wParams arSW.dispatch).afterSend wParams arSL.dispatch).afterSend wParams
      arS1.dispatch).afterSend wParams arS2.dispatch).manager.legState 8
        (bundleHash wParams arSG.dispatch.bundle) = .Unset
    simp only [afterSend_legState, bundleHash_wParams]
    simp [arSW, arSL, arS1, arS2, arSG, arBundle, wAttrs, init]

theorem arStep6 : SysStep pin arEnv arR5 arR6 := by
  refine SysStep.handler 1 arH6 (HandlerStep.executeFresh (arX arSW) ?_ ?_ ?_)
  · rw [arDec_SW]; exact ⟨rfl, Or.inl rfl⟩
  · rw [arDec_SW]; rfl
  · rfl

theorem arStep7 : SysStep pin arEnv arR6 arR7 := by
  refine SysStep.handler 325 arH7 (HandlerStep.executeFresh (arX arS1) ?_ ?_ ?_)
  · rw [arDec_S1]; exact ⟨rfl, Or.inr rfl⟩
  · rw [arDec_S1]; rfl
  · rfl

theorem arR7_leg (f h : Word) : arR7.src.manager.legState f h = arR5.src.manager.legState f h := rfl

theorem arStep8 : SysStep pin arEnv arR7 arR8 := by
  refine SysStep.authorize 7 1 ?_ (by decide) ⟨(99, 324), by decide, Or.inl ⟨rfl, ?_⟩⟩
  · show arR7.src.manager.legState 7 1 = .Committed
    rw [arR7_leg, arR5_leg]; rfl
  · show arR7.src.manager.legState 7 99 = .Unset
    rw [arR7_leg, arR5_leg]; rfl

theorem arR8_leg (f h : Word) : arR8.src.manager.legState f h =
    if f = 7 ∧ h = 1 then .Revertable else arR5.src.manager.legState f h := by
  show (arR5.src.manager.set 7 1 .Revertable).legState f h = _
  rw [legState_set]

theorem arStep9 : SysStep pin arEnv arR8 arR9 := by
  refine SysStep.authorize 9 4 ?_ (by decide) ⟨(3, 324), by decide, Or.inl ⟨rfl, ?_⟩⟩
  · show arR8.src.manager.legState 9 4 = .Committed
    rw [arR8_leg, arR5_leg]; rfl
  · show arR8.src.manager.legState 9 3 = .Unset
    rw [arR8_leg, arR5_leg]; rfl

theorem arR10_leg (f h : Word) : arR10.src.manager.legState f h =
    if f = 8 ∧ h = 5 then .Revertable else if f = 9 ∧ h = 4 then .Revertable
    else arR8.src.manager.legState f h := by
  show ((arR8.src.manager.set 9 4 .Revertable).set 8 5 .Revertable).legState f h = _
  rw [legState_set, legState_set]

theorem arStep10 : SysStep pin arEnv arR9 arR10 := by
  refine SysStep.authorize 8 5 ?_ (by decide) ⟨(98, 324), by decide, Or.inl ⟨rfl, ?_⟩⟩
  · show (arR8.src.manager.set 9 4 .Revertable).legState 8 5 = .Committed
    rw [legState_set, arR8_leg, arR5_leg]; rfl
  · show (arR8.src.manager.set 9 4 .Revertable).legState 8 98 = .Unset
    rw [legState_set, arR8_leg, arR5_leg]; rfl

theorem arStep11 : SysStep pin arEnv arR10 arR11 := by
  refine SysStep.claim 9 (arX arS2) () ?_
  rw [arHH_S2, arR10_leg]
  unfold refundStep
  rw [arDec_S2]
  rfl

theorem arReach : SysReach pin arEnv (sysInit ()) arR11 :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail .refl arStep1)
    arStep2) arStep3) arStep4) arStep5) arStep6) arStep7) arStep8) arStep9) arStep10) arStep11

theorem arR11_leg (f h : Word) : arR11.src.manager.legState f h =
    if f = 9 ∧ h = 4 then .Reverted else arR10.src.manager.legState f h := by
  show (arR10.src.manager.set 9 (handlerHash arEnv (arX arS2)) .Reverted).legState f h = _
  rw [legState_set, arHH_S2]

theorem arR11_dst1 : arR11.dst arEnv.l1ChainId = arH6 := rfl
theorem arR11_dst325 : arR11.dst 325 = arH7 := rfl

theorem arH6_status (h : Word) : arH6.status h = if h = 2 then .FullyExecuted else .Unreceived := by
  show setStatus (arR5.dst 1).status (handlerHash arEnv (arX arSW)) .FullyExecuted h = _
  rw [setStatus_apply, arHH_SW]
  rfl

theorem arH6_verified : arH6.verified = [arX arSW] := rfl

theorem arH7_status (h : Word) : arH7.status h = if h = 3 then .FullyExecuted else .Unreceived := by
  show setStatus (arR6.dst 325).status (handlerHash arEnv (arX arS1)) .FullyExecuted h = _
  rw [setStatus_apply, arHH_S1]
  rfl


/-! ### The pinned witnesses -/

theorem arPublishes : CenterPublishesOnlyPublicDispatches arEnv arR11 := by
  rintro x ⟨-, hx | hx⟩
  · exact ⟨arSW.dispatch, by rw [arLog]; exact List.mem_cons_self, rfl, hx.symm⟩
  · exact ⟨arS1.dispatch, by rw [arLog]; simp, rfl, hx.symm⟩

theorem arVmCall : VmCall arEnv.sem := vmCall_holds _ _

theorem arNoRecovererAtL1 : NoRecovererAt arEnv.code arEnv.l1Router := Or.inl rfl

theorem AtomicToL1StrandedWitness : Properties.AtomicToL1StrandedWitness := by
  refine ⟨Unit, arEnv, (), arR11, arReach, arVmCall, arNoRecovererAtL1, arPublishes,
    arDec_bundles, arSL.dispatch,
    by rw [arLog]; simp, rfl, rfl, ⟨arSL, by rw [arSends]; simp, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    handlerHash_enc arDec_SL rfl, claimPreimage_enc arDec_SL rfl, ?_⟩
  · rw [arHash, arR11_leg, arR10_leg, arR8_leg]; rfl
  · rw [arHash, arR11_dst1, arH6_status]; rfl
  · refine ⟨arSW.dispatch, by rw [arLog]; exact List.mem_cons_self, rfl, rfl, ?_⟩
    rw [arHash, arR11_dst1, arH6_status]; rfl
  · rintro ⟨d', hd', hpub, hsalt, -⟩
    rw [arLog] at hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with rfl | rfl | rfl | rfl | rfl
    · exact absurd hsalt (by decide)
    · exact absurd hpub (by decide)
    · exact absurd hsalt (by decide)
    · exact absurd hpub (by decide)
    · exact absurd hpub (by decide)
  · intro x hx
    rw [arR11_dst1, arH6_verified, List.mem_singleton] at hx
    rw [hx, arHH_SW, arHash]
    decide
  · intro p hp
    rw [arClaims, List.mem_singleton] at hp
    subst hp
    rw [arHH_S2, arHash]
    decide
  · intro st w
    unfold refundStep
    rw [arDec_SL]
    exact claimRefund_none_of_loop (recoverBundle_none_of_noRecoverer arVmCall _ w
      ⟨arL1Call, by simp [arSL, arBundle], Or.inl rfl⟩)

theorem SendMessageAtomicMisrouted : Properties.SendMessageAtomicMisrouted := by
  refine ⟨Unit, arEnv, (), arR11, arReach, arVmCall, arPublishes, arDec_bundles,
    fun _ _ h => h, arS1, arS2,
    ⟨9, 100, 0⟩, by rw [arSends]; simp, by rw [arSends]; simp, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [arHash]; decide
  · rw [arHash]; decide
  · rw [arHash, arHash]; decide
  · rw [arHash, arR11_leg, arR10_leg, arR8_leg, arR5_leg]; rfl
  · rw [arHash, show arS1.dest = 325 from rfl, arR11_dst325, arH7_status]; rfl
  · rw [arHash, arR11_leg]; rfl

theorem NonRecovererLegNeverRefundedWitness :
    Properties.NonRecovererLegNeverRefundedWitness := by
  refine ⟨Unit, arEnv, (), arR11, arReach, arVmCall, arDec_bundles, arSG.dispatch,
    by rw [arLog]; simp, rfl, by decide, ⟨arAppCall 1, by simp [arSG, arBundle], Or.inl rfl⟩,
    ⟨arL2Call, by simp [arSG, arBundle], ?_⟩, ?_, ?_⟩
  · unfold refundStep
    rw [arDec_SG]
    rfl
  · rw [arHash, arR11_leg, arR10_leg]; rfl
  · intro p hp
    rw [arClaims, List.mem_singleton] at hp
    subst hp
    rw [arHH_S2, arHash]
    decide

theorem IndirectL2RouterLegsReachSourceRouterWitness :
    Properties.IndirectL2RouterLegsReachSourceRouterWitness :=
  ⟨Unit, arEnv, (), arR11, arReach, arSG, by rw [arSends]; simp, by decide, arRouterStarter,
    by simp [arSG], rfl, rfl⟩

theorem PinBreaksAttributeHonoured : Properties.PinBreaksAttributeHonoured :=
  ⟨Unit, arEnv, (), arR11, arReach, ⟨arS1, by rw [arSends]; simp, rfl, rfl⟩,
    ⟨arSL, by rw [arSends]; simp, rfl, rfl⟩⟩

/-! ### The premises of (d) are needed

Two pinned runs with the one atomic withdrawal `sL`. `arEnvLeaky` differs from `arEnv` only in its
inclusion verdict, which accepts `sL`'s bytes; `arEnvL1Code` deploys code that returns `true` at
the L1 router's address `26`, and its inclusion verdict accepts nothing. -/

/-- A send's shape reads the environment only through `P`, `L1_CHAIN_ID`, the two routers and
`depositCalldata`. -/
theorem sendShape_transport {K : Guards} {E E' : Env W} {s : Send} (h : SendShape K E s)
    (hP : E'.P = E.P) (h1 : E'.l1ChainId = E.l1ChainId) (h2 : E'.l2Router = E.l2Router)
    (h3 : E'.l1Router = E.l1Router) (h4 : E'.depositCalldata = E.depositCalldata) :
    SendShape K E' s := by
  rcases E' with ⟨P, l1, l2, r1, dc, dec, code, sem, inc, fin, fl, ae⟩
  dsimp only at hP h1 h2 h3 h4
  subst hP h1 h2 h3 h4
  exact ⟨h.atomicSend, h.sourceNotL1, h.notSelf, h.messageNotToL1, h.messageOneCall, h.l1OneCall,
    h.l1Withdrawal, h.formed, h.routed, h.validated, h.atomicNotToL1⟩

/-- `arEnv`, with an inclusion verdict that accepts exactly the bytes of `sL` from chain `324`. -/
def arEnvLeaky : Env Unit :=
  { arEnv with included := fun c x => c = 324 ∧ x = wParams.enc arSL.dispatch.bundle }

/-- `arEnv`, with code at the L1 router's address `26` that returns `true` and changes nothing, and
an inclusion verdict that accepts nothing. -/
def arEnvL1Code : Env Unit :=
  { arEnv with
    code := fun a => if a = 9 ∨ a = 26 then .recoverer Contracts.AtomicFlowManager.RecoveryTargets.trueNoOp
      else .none
    included := fun _ _ => False }

theorem arEnvLeaky_dec : arEnvLeaky.dec = arDec := rfl
theorem arEnvLeaky_P : arEnvLeaky.P = wParams := rfl
theorem arEnvL1Code_dec : arEnvL1Code.dec = arDec := rfl
theorem arEnvL1Code_P : arEnvL1Code.P = wParams := rfl

theorem arDec_SL_leaky :
    arEnvLeaky.dec (arEnvLeaky.P.enc arSL.dispatch.bundle) = arSL.dispatch.bundle := by
  rw [arEnvLeaky_dec, arEnvLeaky_P, arDec_enc]; rfl

theorem arDec_SL_l1Code :
    arEnvL1Code.dec (arEnvL1Code.P.enc arSL.dispatch.bundle) = arSL.dispatch.bundle := by
  rw [arEnvL1Code_dec, arEnvL1Code_P, arDec_enc]; rfl

/-- `sL` is the first send of a fresh pinned system, in any environment with `arEnv`'s send fields. -/
theorem arStepSL_fresh (E : Env Unit) (hP : E.P = arEnv.P) (h1 : E.l1ChainId = arEnv.l1ChainId)
    (h2 : E.l2Router = arEnv.l2Router) (h3 : E.l1Router = arEnv.l1Router)
    (h4 : E.depositCalldata = arEnv.depositCalldata) :
    SysStep pin E (sysInit ()) ((sysInit ()).sendS E arSL) :=
  SysStep.send arSL ⟨sendShape_transport arShape_SL hP h1 h2 h3 h4, rfl, fun _ => rfl⟩

/-- L1 executes `sL` in the leaky environment. -/
def arLeakyH : Handler :=
  ⟨setStatus Handler.init.status (handlerHash arEnvLeaky (arEnvLeaky.P.enc arSL.dispatch.bundle))
      .FullyExecuted, [arEnvLeaky.P.enc arSL.dispatch.bundle]⟩

def arLeaky1 : Sys Unit := (sysInit ()).sendS arEnvLeaky arSL
def arLeaky2 : Sys Unit := arLeaky1.handlerS 1 arLeakyH

theorem arLeaky_hash :
    handlerHash arEnvLeaky (arEnvLeaky.P.enc arSL.dispatch.bundle) = 1 := by
  rw [handlerHash_enc arDec_SL_leaky rfl, arEnvLeaky_P, bundleHash_wParams]
  rfl

theorem arLeaky2_dst1 : arLeaky2.dst arEnvLeaky.l1ChainId = arLeakyH := rfl

theorem arLeakyH_status (h : Word) :
    arLeakyH.status h = if h = 1 then .FullyExecuted else .Unreceived := by
  show setStatus Handler.init.status (handlerHash arEnvLeaky (arEnvLeaky.P.enc arSL.dispatch.bundle))
    .FullyExecuted h = _
  rw [setStatus_apply, arLeaky_hash]
  rfl

theorem arLeakyH_verified : arLeakyH.verified = [arEnvLeaky.P.enc arSL.dispatch.bundle] := rfl

theorem arLeakyReach : SysReach pin arEnvLeaky (sysInit ()) arLeaky2 := by
  have h1 := arStepSL_fresh arEnvLeaky rfl rfl rfl rfl rfl
  have h2 : SysStep pin arEnvLeaky arLeaky1 arLeaky2 := by
    refine SysStep.handler 1 arLeakyH
      (HandlerStep.executeFresh (arEnvLeaky.P.enc arSL.dispatch.bundle) ?_ ?_ rfl)
    · rw [arDec_SL_leaky]; exact ⟨rfl, rfl⟩
    · rw [arDec_SL_leaky]; rfl
  exact .tail (.tail .refl h1) h2

theorem AtomicToL1StrandedNeedsPublicationPremise :
    Properties.AtomicToL1StrandedNeedsPublicationPremise := by
  have hlog : arLeaky2.src.log = [arSL.dispatch] := rfl
  refine ⟨Unit, arEnvLeaky, (), arLeaky2, arLeakyReach, vmCall_holds _ _, Or.inl rfl, ?_,
    arSL.dispatch, by rw [hlog]; exact List.mem_singleton_self _, rfl, rfl, ?_, ?_, ?_⟩
  · intro d hd
    rw [hlog, List.mem_singleton] at hd
    subst hd
    exact arDec_SL_leaky
  · rw [arLeaky2_dst1, arLeakyH_status, arEnvLeaky_P, bundleHash_wParams]
    rfl
  · rintro ⟨d', hd', hpub, -⟩
    rw [hlog, List.mem_singleton] at hd'
    subst hd'
    exact absurd hpub (by decide)
  · intro x hx
    rw [arLeaky2_dst1, arLeakyH_verified, List.mem_singleton] at hx
    rw [hx]
    exact claimPreimage_enc arDec_SL_leaky rfl

def arL1Code1 : Sys Unit := (sysInit ()).sendS arEnvL1Code arSL
def arL1Code2 : Sys Unit := arL1Code1.authS 7 1
def arL1Code3 : Sys Unit :=
  arL1Code2.claimS arEnvL1Code 7 (arEnvL1Code.P.enc arSL.dispatch.bundle) ()

theorem arL1Code_hash :
    handlerHash arEnvL1Code (arEnvL1Code.P.enc arSL.dispatch.bundle) = 1 := by
  rw [handlerHash_enc arDec_SL_l1Code rfl, arEnvL1Code_P, bundleHash_wParams]
  rfl

theorem arL1Code1_leg (f h : Word) : arL1Code1.src.manager.legState f h =
    if f = 7 ∧ h = 1 then .Committed else .Unset := by
  show (init.afterSend wParams arSL.dispatch).manager.legState f h = _
  simp only [afterSend_legState, bundleHash_wParams]
  simp [arSL, arBundle, wAttrs, init]

theorem arL1Code2_leg : arL1Code2.src.manager.legState 7 1 = .Revertable := by
  show (arL1Code1.src.manager.set 7 1 .Revertable).legState 7 1 = _
  rw [legState_set]
  rfl

theorem arL1Code3_leg : arL1Code3.src.manager.legState 7 1 = .Reverted := by
  show (arL1Code2.src.manager.set 7 (handlerHash arEnvL1Code
    (arEnvL1Code.P.enc arSL.dispatch.bundle)) .Reverted).legState 7 1 = _
  rw [legState_set, arL1Code_hash]
  rfl

theorem arL1CodeReach : SysReach pin arEnvL1Code (sysInit ()) arL1Code3 := by
  have h1 := arStepSL_fresh arEnvL1Code rfl rfl rfl rfl rfl
  have h2 : SysStep pin arEnvL1Code arL1Code1 arL1Code2 := by
    refine SysStep.authorize 7 1 ?_ (by decide) ⟨(99, 324), by decide, Or.inl ⟨rfl, ?_⟩⟩
    · show arL1Code1.src.manager.legState 7 1 = .Committed
      rw [arL1Code1_leg]; rfl
    · show arL1Code1.src.manager.legState 7 99 = .Unset
      rw [arL1Code1_leg]; rfl
  have h3 : SysStep pin arEnvL1Code arL1Code2 arL1Code3 := by
    refine SysStep.claim 7 (arEnvL1Code.P.enc arSL.dispatch.bundle) () ?_
    rw [arL1Code_hash, arL1Code2_leg]
    unfold refundStep
    rw [arDec_SL_l1Code]
    rfl
  exact .tail (.tail (.tail .refl h1) h2) h3

theorem AtomicToL1StrandedNeedsNoRecoverer : Properties.AtomicToL1StrandedNeedsNoRecoverer := by
  have hlog : arL1Code3.src.log = [arSL.dispatch] := rfl
  have hclaims : arL1Code3.claims = [(7, arEnvL1Code.P.enc arSL.dispatch.bundle)] := rfl
  refine ⟨Unit, arEnvL1Code, (), arL1Code3, arL1CodeReach, vmCall_holds _ _,
    fun _ h => False.elim h, ?_,
    ⟨Contracts.AtomicFlowManager.RecoveryTargets.trueNoOp, rfl, fun _ _ _ => rfl⟩,
    arSL.dispatch, by rw [hlog]; exact List.mem_singleton_self _, rfl, rfl, ?_, ?_⟩
  · intro d hd
    rw [hlog, List.mem_singleton] at hd
    subst hd
    exact arDec_SL_l1Code
  · rw [arEnvL1Code_P, bundleHash_wParams]
    exact arL1Code3_leg
  · intro p hp
    rw [hclaims, List.mem_singleton] at hp
    subst hp
    exact claimPreimage_enc arDec_SL_l1Code rfl

/-! ### The `upgradeTree` witness -/

def arQ1 : Sys Unit := (sysInit ()).sendS arEnv arSW
def arQ2 : Sys Unit := arQ1.sendS arEnv arSG
def arQ3 : Sys Unit := arQ2.sendS arEnv arSM
def arQ4 : Sys Unit := arQ3.sendS arEnv arSMA

theorem arQReach : SysReach upgradeTree arEnv (sysInit ()) arQ4 := by
  have h1 : SysStep upgradeTree arEnv (sysInit ()) arQ1 :=
    SysStep.send arSW ⟨arShape_SW upgradeTree, rfl, fun h => absurd h (by decide)⟩
  have h2 : SysStep upgradeTree arEnv arQ1 arQ2 := by
    refine SysStep.send arSG ⟨arShape_SG upgradeTree, ?_, fun _ => ?_⟩
    · show (init.afterSend wParams arSW.dispatch).saltUsed 1 5 = false
      rw [afterSend_saltUsed]; rfl
    · show (init.afterSend wParams arSW.dispatch).manager.legState 8
        (bundleHash wParams arSG.dispatch.bundle) = .Unset
      rw [afterSend_legState]; rfl
  have h3 : SysStep upgradeTree arEnv arQ2 arQ3 := by
    refine SysStep.send arSM ⟨arShape_SM upgradeTree, ?_, fun h => absurd h (by decide)⟩
    show ((init.afterSend wParams arSW.dispatch).afterSend wParams arSG.dispatch).saltUsed 2 6 = false
    rw [afterSend_saltUsed, afterSend_saltUsed]; rfl
  have h4 : SysStep upgradeTree arEnv arQ3 arQ4 := by
    refine SysStep.send arSMA ⟨arShape_SMA, ?_, fun _ => ?_⟩
    · show (((init.afterSend wParams arSW.dispatch).afterSend wParams arSG.dispatch).afterSend
        wParams arSM.dispatch).saltUsed 2 7 = false
      rw [afterSend_saltUsed, afterSend_saltUsed, afterSend_saltUsed]; rfl
    · show (((init.afterSend wParams arSW.dispatch).afterSend wParams arSG.dispatch).afterSend
        wParams arSM.dispatch).manager.legState 10 (bundleHash wParams arSMA.dispatch.bundle) = .Unset
      simp only [afterSend_legState, bundleHash_wParams]
      simp [arSW, arSG, arSM, arSMA, arBundle, wAttrs, init]
  exact .tail (.tail (.tail (.tail .refl h1) h2) h3) h4

theorem arQSends : arQ4.sends = [arSW, arSG, arSM, arSMA] := rfl

theorem AttributeHonouredOrRejectedWitness : Properties.AttributeHonouredOrRejectedWitness :=
  ⟨Unit, arEnv, (), arQ4, arQReach, ⟨arSG, by rw [arQSends]; simp, rfl, rfl, rfl⟩,
    ⟨arSMA, by rw [arQSends]; simp, rfl, rfl, rfl⟩, ⟨arSM, by rw [arQSends]; simp, rfl, rfl⟩,
    ⟨arSW, by rw [arQSends]; simp, rfl⟩⟩

theorem AttributeRoutingByEntryPointWitness : Properties.AttributeRoutingByEntryPointWitness :=
  ⟨Unit, arEnv, (), arR11, arQ4, arReach, arQReach,
    ⟨arS1, by rw [arSends]; simp, rfl, rfl, rfl⟩, ⟨arSL, by rw [arSends]; simp, rfl, rfl, rfl⟩,
    ⟨arSW, by rw [arSends]; simp, rfl, rfl, rfl⟩, ⟨arSMA, by rw [arQSends]; simp, rfl, rfl, rfl⟩⟩

end Contracts.InteropCenter.AtomicRouting
