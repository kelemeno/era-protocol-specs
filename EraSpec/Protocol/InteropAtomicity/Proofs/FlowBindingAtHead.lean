import EraSpec.Protocol.InteropAtomicity.Properties.FlowBindingAtHead
import EraSpec.Protocol.InteropAtomicity.Proofs.OncePerLeg
import EraSpec.Protocol.InteropAtomicity.Proofs.FlowBinding
import EraSpec.Contracts.AtomicFlowManager.Proofs.FlowCanonicalAtHead

/-!
# Proofs: the committed leg is bound to a logged preimage, at head (`3605e82`)

Three pieces carry everything.

* **The pin view.** A checked head flow settling on `l1` is a checked pin flow for
  `pinFlowHash enc l1` (`headCheck_pinCheck`), because an accepted preimage is rebuilt from
  its pin legs and deadline (`rebuild_eq`). So the pin's no-hash-premise gate and refund
  results (`none_or_all_or_break_pinned`, `executed_excludes_any_refund_or_break`) apply to
  logged head calls.
* **The chain projection.** Each chain of a head run is a pin `Contracts.AppendPath.Steps`
  run (`runAtHead_chain`): a head insert is the pin insert with the landing hint
  (`InsertGuard.pinInsert`). So the pin's one-chain invariant `Contracts.AppendPath.Inv`
  applies.
* **The log.** Every logged call passed its checks (`logged_calls_checked`); in particular
  every logged `append`'s preimage is accepted and declares the committed leg on the
  committing chain. With `declared_source_chain_unique` this binds the declared chain.
-/

namespace Contracts.FlowBindingAtHead

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund Contracts.AppendPath
open Contracts.FlowCanonicalAtHead

/-! ## The pin view of a head flow -/

theorem mem_pinLegs_iff {P : FlowPreimage} {leg : FlowLeg} :
    leg ∈ pinLegs P ↔ P.Declares leg.bundleHash leg.chain := by
  unfold pinLegs FlowPreimage.Declares
  constructor
  · intro h
    obtain ⟨⟨b', c'⟩, hmem, heq⟩ := List.mem_map.mp h
    subst heq
    exact hmem
  · intro h
    exact List.mem_map.mpr ⟨(leg.bundleHash, leg.chain), h, rfl⟩

theorem mk_mem_pinLegs_iff {P : FlowPreimage} {c b : UInt256} :
    (⟨c, b⟩ : FlowLeg) ∈ pinLegs P ↔ P.Declares b c :=
  mem_pinLegs_iff

theorem pinLegs_map_bundleHash {P : FlowPreimage}
    (hl : P.legSourceChainIds.length = P.legBundleHashes.length) :
    (pinLegs P).map FlowLeg.bundleHash = P.legBundleHashes := by
  unfold pinLegs
  rw [List.map_map]
  exact legPairs_map_fst hl

theorem pinLegs_map_chain {P : FlowPreimage}
    (hl : P.legSourceChainIds.length = P.legBundleHashes.length) :
    (pinLegs P).map FlowLeg.chain = P.legSourceChainIds := by
  unfold pinLegs
  rw [List.map_map]
  exact legPairs_map_snd hl

/-- An accepted preimage settling on `l1` is rebuilt from its pin legs and deadline. -/
theorem rebuild_eq {P : FlowPreimage} {l1 : UInt256} (hP : PreimageAccepted P)
    (hsl : P.settlementLayerChainId = l1) :
    (⟨ATOMIC_FLOW_PREIMAGE_VERSION, P.deadline, l1, (pinLegs P).map FlowLeg.bundleHash,
      (pinLegs P).map FlowLeg.chain⟩ : FlowPreimage) = P := by
  rw [pinLegs_map_bundleHash hP.lengths, pinLegs_map_chain hP.lengths]
  obtain ⟨v, d, sl, hs, cs⟩ := P
  simp only at hsl
  subst hsl
  have hv : v = ATOMIC_FLOW_PREIMAGE_VERSION := hP.version
  subst hv
  rfl

/-- The pin flow hash of an accepted preimage settling on `l1` is its head hash. -/
theorem pinFlowHash_eq {enc : PreimageHash} {P : FlowPreimage} {l1 : UInt256}
    (hP : PreimageAccepted P) (hsl : P.settlementLayerChainId = l1) :
    pinFlowHash enc l1 (pinLegs P) P.deadline = enc P := by
  unfold pinFlowHash
  rw [rebuild_eq hP hsl]

/-- **A CHECKED HEAD FLOW IS A CHECKED PIN FLOW.** -/
theorem headCheck_pinCheck {enc : PreimageHash} {l1 : UInt256} {F : AtomicFlow}
    (hF : CheckFlowId enc F) (hsl : F.preimage.settlementLayerChainId = l1) :
    FlowIdChecked (pinFlowHash enc l1) (pinFlow F) := by
  show pinFlowHash enc l1 (pinLegs F.preimage) F.preimage.deadline = F.flowId
  rw [pinFlowHash_eq hF.accepted hsl]
  exact hF.id_eq

/-- Two accepted preimages settling on `l1` with the same pin legs and deadline are equal. -/
theorem preimage_eq_of_pin {P Q : FlowPreimage} {l1 : UInt256} (hP : PreimageAccepted P)
    (hPs : P.settlementLayerChainId = l1) (hQ : PreimageAccepted Q)
    (hQs : Q.settlementLayerChainId = l1) (hl : pinLegs P = pinLegs Q)
    (hd : P.deadline = Q.deadline) : P = Q := by
  rw [← rebuild_eq hP hPs, ← rebuild_eq hQ hQs, hl, hd]

theorem pin_clash_iff {enc : PreimageHash} {l1 : UInt256} {F G : AtomicFlow}
    (hF : CheckFlowId enc F) (hFs : F.preimage.settlementLayerChainId = l1)
    (hG : CheckFlowId enc G) (hGs : G.preimage.settlementLayerChainId = l1) :
    FlowIdClash (pinFlowHash enc l1) (pinFlow F) (pinFlow G)
      ↔ PreimageClash enc F.preimage G.preimage := by
  have eF := pinFlowHash_eq (enc := enc) hF.accepted hFs
  have eG := pinFlowHash_eq (enc := enc) hG.accepted hGs
  constructor
  · rintro ⟨hne, heq⟩
    refine ⟨?_, ?_⟩
    · intro hp
      apply hne
      show (pinLegs F.preimage, F.preimage.deadline) = (pinLegs G.preimage, G.preimage.deadline)
      rw [hp]
    · have heq' : pinFlowHash enc l1 (pinLegs F.preimage) F.preimage.deadline
          = pinFlowHash enc l1 (pinLegs G.preimage) G.preimage.deadline := heq
      rw [eF, eG] at heq'
      exact heq'
  · rintro ⟨hne, heq⟩
    refine ⟨?_, ?_⟩
    · intro hp
      obtain ⟨hl, hd⟩ := Prod.mk.inj hp
      exact hne (preimage_eq_of_pin hF.accepted hFs hG.accepted hGs hl hd)
    · show pinFlowHash enc l1 (pinLegs F.preimage) F.preimage.deadline
          = pinFlowHash enc l1 (pinLegs G.preimage) G.preimage.deadline
      rw [eF, eG]
      exact heq

/-! ## The head insert -/

/-- On a valid tree, the head insert's checks are the guarded insert at the landing leaf. -/
theorem InsertSucceedsAtHead.guard {T : Tree} (hV : Valid T) {v : UInt256} {hint low : ℕ}
    (h : InsertSucceedsAtHead T v hint low) : InsertGuard T v low := by
  obtain ⟨hops, hs⟩ := h.search
  exact search_yields_guard hV h.initialized h.nonzero h.fresh h.hintInBounds h.hintBelow hs

/-- The guarded insert at `low` is the pin's insert with hint `low`: the walk does not hop. -/
theorem InsertGuard.pinInsert {T : Tree} {v : UInt256} {low : ℕ} (hg : InsertGuard T v low) :
    InsertSucceeds T v low low := by
  refine ⟨hg.initialized, hg.nonzero, hg.fresh, hg.inBounds, hg.lowBelow, ?_⟩
  apply lowSearch_stop
  rintro ⟨hne, hlt⟩
  rcases hg.window with h0 | hle
  · exact hne h0
  · exact absurd hlt (not_lt.mpr hle)

/-- The pin's bounded insert is a head insert. -/
theorem InsertSucceeds.atHead {T : Tree} {v : UInt256} {hint low : ℕ}
    (h : InsertSucceeds T v hint low) : InsertSucceedsAtHead T v hint low :=
  ⟨h.initialized, h.nonzero, h.fresh, h.hintInBounds, h.hintBelow, ⟨_, h.search⟩⟩

/-- A head `append` is a pin `append` of its obligation, with the landing hint. -/
theorem AppendSucceedsAtHead.pinAppend {enc : PreimageHash} {cv : CommitValue} {l1 : UInt256}
    {env : AppendEnv} {c : Chain} {s : ChainState} {b : UInt256} {P : FlowPreimage}
    {hint low : ℕ} (hV : Valid s.tree) (h : AppendSucceedsAtHead enc cv l1 env c s b P hint low) :
    AppendSucceeds cv s (enc P) b low low :=
  ⟨h.legUnset, InsertGuard.pinInsert (h.treeInsert.guard hV)⟩

/-- A head `append`'s preimage is accepted. -/
theorem AppendSucceedsAtHead.accepted {enc : PreimageHash} {cv : CommitValue} {l1 : UInt256}
    {env : AppendEnv} {c : Chain} {s : ChainState} {b : UInt256} {P : FlowPreimage}
    {hint low : ℕ} (h : AppendSucceedsAtHead enc cv l1 env c s b P hint low) :
    PreimageAccepted P :=
  (validate_eq_some_iff.mp h.flowId).1

/-- A head `append` declares the committed bundle on the committing chain. -/
theorem AppendSucceedsAtHead.declares {enc : PreimageHash} {cv : CommitValue} {l1 : UInt256}
    {env : AppendEnv} {c : Chain} {s : ChainState} {b : UInt256} {P : FlowPreimage}
    {hint low : ℕ} (h : AppendSucceedsAtHead enc cv l1 env c s b P hint low) :
    P.Declares b c := by
  obtain ⟨i, hidx, hci⟩ := h.isLegHere
  obtain ⟨hi, hbi, _⟩ := List.idxOf?_eq_some_iff.mp hidx
  have hlen := h.accepted.lengths
  have hi' : i < P.legSourceChainIds.length := by rw [hlen]; exact hi
  have hci' : P.legSourceChainIds[i] = c := by
    rw [List.getElem?_eq_getElem hi'] at hci
    exact Option.some.inj hci
  have hmem : (P.legBundleHashes[i], P.legSourceChainIds[i]) ∈ P.legPairs := by
    unfold FlowPreimage.legPairs
    have hzi : i < (P.legBundleHashes.zip P.legSourceChainIds).length := by
      rw [List.length_zip]; exact lt_min hi hi'
    have := List.getElem_mem hzi
    rw [List.getElem_zip] at this
    exact this
  rw [hbi, hci'] at hmem
  exact hmem

/-! ## The log -/

@[simp] theorem appendCalls_nil : appendCalls [] = [] := rfl

@[simp] theorem appendCalls_append (a : AppendCall) (log : List CallAtHead) :
    appendCalls (.append a :: log) = a :: appendCalls log := rfl

@[simp] theorem appendCalls_execute (e : ExecCallAtHead) (log : List CallAtHead) :
    appendCalls (.execute e :: log) = appendCalls log := rfl

@[simp] theorem appendCalls_authorize (a : AuthCallAtHead) (log : List CallAtHead) :
    appendCalls (.authorize a :: log) = appendCalls log := rfl

@[simp] theorem appendLog_nil (enc : PreimageHash) : appendLog enc [] = [] := rfl

@[simp] theorem appendLog_append (enc : PreimageHash) (a : AppendCall) (log : List CallAtHead) :
    appendLog enc (.append a :: log) = a.obligation enc :: appendLog enc log := rfl

@[simp] theorem appendLog_execute (enc : PreimageHash) (e : ExecCallAtHead)
    (log : List CallAtHead) : appendLog enc (.execute e :: log) = appendLog enc log := rfl

@[simp] theorem appendLog_authorize (enc : PreimageHash) (a : AuthCallAtHead)
    (log : List CallAtHead) : appendLog enc (.authorize a :: log) = appendLog enc log := rfl

theorem mem_appendCalls {a : AppendCall} {log : List CallAtHead} :
    a ∈ appendCalls log ↔ CallAtHead.append a ∈ log := by
  unfold appendCalls
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨k, hk, hka⟩
    cases k with
    | append a' =>
      simp only [CallAtHead.appendCall?, Option.some.injEq] at hka
      rw [← hka]; exact hk
    | execute _ => simp [CallAtHead.appendCall?] at hka
    | authorize _ => simp [CallAtHead.appendCall?] at hka
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_appendLog {o : Obligation} {enc : PreimageHash} {log : List CallAtHead} :
    o ∈ appendLog enc log ↔ ∃ a ∈ appendCalls log, a.obligation enc = o := by
  unfold appendLog
  exact List.mem_map

@[simp] theorem AppendCall.obligation_flowId (enc : PreimageHash) (a : AppendCall) :
    (a.obligation enc).flowId = enc a.preimage := rfl

@[simp] theorem AppendCall.obligation_bundleHash (enc : PreimageHash) (a : AppendCall) :
    (a.obligation enc).bundleHash = a.bundleHash := rfl

@[simp] theorem AppendCall.obligation_chain (enc : PreimageHash) (a : AppendCall) :
    (a.obligation enc).chain = a.chain := rfl

theorem AppendCall.obligation_eq_iff {enc : PreimageHash} {a : AppendCall} {f b c : UInt256} :
    a.obligation enc = ⟨f, b, c⟩ ↔ enc a.preimage = f ∧ a.bundleHash = b ∧ a.chain = c := by
  unfold AppendCall.obligation
  simp only [Obligation.mk.injEq]

/-- The facts a logged `append` carries. -/
structure AppendCall.Checked (enc : PreimageHash) (l1 : UInt256) (a : AppendCall) : Prop where
  accepted : PreimageAccepted a.preimage
  slIsL1 : a.preimage.settlementLayerChainId = l1
  notExpired : a.env.latestRootTimestamp l1 ≤ a.preimage.deadline
  declares : a.preimage.Declares a.bundleHash a.chain
  othersRegistered : ∀ src ∈ a.preimage.legSourceChainIds, src ≠ a.chain → a.env.registered src

/-- A logged `append`'s flow passes `_checkFlowId`. -/
theorem AppendCall.Checked.check {enc : PreimageHash} {l1 : UInt256} {a : AppendCall}
    (h : a.Checked enc l1) : CheckFlowId enc (committedFlow enc a.preimage) :=
  checkFlowId_of_accepted enc h.accepted

/-- **EVERY LOGGED CALL PASSED ITS CHECKS.** -/
theorem logged_calls_checked {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {enc : PreimageHash} {l1 : UInt256} {S : System} {X Y : Chains} {log : List CallAtHead}
    (hr : RunAtHead h z0 hl cv enc l1 S X Y log) :
    (∀ a ∈ appendCalls log, a.Checked enc l1)
      ∧ (∀ e, CallAtHead.execute e ∈ log → e.Verified h z0 hl cv enc l1 S)
      ∧ (∀ a, CallAtHead.authorize a ∈ log → a.Verified h z0 hl cv enc l1 S) := by
  induction hr with
  | refl => exact ⟨by simp, by simp, by simp⟩
  | @append Y log a hint low _ ha ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro a' ha'
      rw [appendCalls_append] at ha'
      rcases List.mem_cons.mp ha' with rfl | ha'
      · refine ⟨ha.accepted, ha.slIsL1, ?_, ha.declares, ha.othersRegistered⟩
        have := ha.notExpired
        rw [ha.slIsL1] at this
        exact this
      · exact ih1 a' ha'
    · intro e he
      rcases List.mem_cons.mp he with he | he
      · cases he
      · exact ih2 e he
    · intro a' ha'
      rcases List.mem_cons.mp ha' with ha' | ha'
      · cases ha'
      · exact ih3 a' ha'
  | @execute Y log e _ hv ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    refine ⟨by rw [appendCalls_execute]; exact ih1, ?_, ?_⟩
    · intro e' he'
      rcases List.mem_cons.mp he' with he' | he'
      · cases he'; exact hv
      · exact ih2 e' he'
    · intro a' ha'
      rcases List.mem_cons.mp ha' with ha' | ha'
      · cases ha'
      · exact ih3 a' ha'
  | @authorize Y log a _ hv _ ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    refine ⟨by rw [appendCalls_authorize]; exact ih1, ?_, ?_⟩
    · intro e' he'
      rcases List.mem_cons.mp he' with he' | he'
      · cases he'
      · exact ih2 e' he'
    · intro a' ha'
      rcases List.mem_cons.mp ha' with ha' | ha'
      · cases ha'; exact hv
      · exact ih3 a' ha'
  | claim _ _ ih => exact ih
  | initL2 _ _ ih => exact ih

/-- A logged call's preimage hashes to its flow id. -/
theorem logged_call_id {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {enc : PreimageHash} {l1 : UInt256} {S : System} {X Y : Chains} {log : List CallAtHead}
    (hr : RunAtHead h z0 hl cv enc l1 S X Y log) {k : CallAtHead} (hk : k ∈ log) :
    enc k.preimage = k.flowId enc ∧ PreimageAccepted k.preimage
      ∧ k.preimage.settlementLayerChainId = l1 := by
  obtain ⟨h1, h2, h3⟩ := logged_calls_checked hr
  cases k with
  | append a =>
    have ha := h1 a (mem_appendCalls.mpr hk)
    exact ⟨rfl, ha.accepted, ha.slIsL1⟩
  | execute e =>
    have he := h2 e hk
    exact ⟨he.1.id_eq, he.1.accepted, he.2.1⟩
  | authorize a =>
    have ha := h3 a hk
    exact ⟨ha.1.id_eq, ha.1.accepted, ha.2.1⟩

/-! ## The chain projection -/

/-- **EACH CHAIN OF A HEAD RUN FROM GENESIS IS A PIN CHAIN RUN.** -/
theorem runAtHead_chain {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {enc : PreimageHash} {l1 : UInt256} {S : System} {Y : Chains} {log : List CallAtHead}
    (hr : RunAtHead h z0 hl cv enc l1 S genesisAll Y log) :
    ∀ c, Steps cv c genesis (Y c) ((appendLog enc log).filter (fun o => o.chain = c)) := by
  induction hr with
  | refl => exact fun _ => Steps.refl
  | @append Y log a hint low _ ha ih =>
    intro c
    by_cases hc : c = a.chain
    · subst hc
      rw [update_self, appendLog_append, List.filter_cons_of_pos (by simp)]
      have hV : Valid (Y a.chain).tree := (inv_of_steps (ih a.chain)).valid
      exact Steps.append (ih a.chain) (ha.pinAppend hV)
    · rw [update_other _ _ hc, appendLog_append,
        List.filter_cons_of_neg (by simp [AppendCall.obligation, Ne.symm hc])]
      exact ih c
  | execute _ _ _ ih => intro c; rw [appendLog_execute]; exact ih c
  | @authorize Y log a _ _ hg ih =>
    intro c
    rw [appendLog_authorize]
    by_cases hc : c = a.chain
    · subst hc
      rw [update_self]
      exact Steps.authorize (ih a.chain) hg
    · rw [update_other _ _ hc]
      exact ih c
  | @claim Y log c' f b _ hg ih =>
    intro c
    by_cases hc : c = c'
    · subst hc
      rw [update_self]
      exact Steps.claim (ih c) hg
    · rw [update_other _ _ hc]
      exact ih c
  | @initL2 Y log c' _ h0 ih =>
    intro c
    by_cases hc : c = c'
    · subst hc
      rw [update_self]
      exact Steps.initL2 (ih c) h0
    · rw [update_other _ _ hc]
      exact ih c

/-- The pin invariant, on chain `c` of a head run. -/
theorem runAtHead_inv {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {enc : PreimageHash} {l1 : UInt256} {S : System} {Y : Chains} {log : List CallAtHead}
    (hr : RunAtHead h z0 hl cv enc l1 S genesisAll Y log) (c : Chain) :
    Inv cv c (Y c) ((appendLog enc log).filter (fun o => o.chain = c)) :=
  inv_of_steps (runAtHead_chain hr c)

/-- An obligation is in chain `c`'s filtered log iff a logged `append` on `c` committed it. -/
theorem mem_chainLog {enc : PreimageHash} {log : List CallAtHead} {f b c : UInt256} :
    (⟨f, b, c⟩ : Obligation) ∈ (appendLog enc log).filter (fun o => o.chain = c)
      ↔ ∃ a ∈ appendCalls log, a.obligation enc = ⟨f, b, c⟩ := by
  rw [mem_filter_chain, mem_appendLog]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

/-- On a head run from genesis, a leg is `Unset` iff no logged `append` committed it. -/
theorem unset_iff_not_appended {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {enc : PreimageHash} {l1 : UInt256} {S : System} {Y : Chains} {log : List CallAtHead}
    (hr : RunAtHead h z0 hl cv enc l1 S genesisAll Y log) (c f b : UInt256) :
    (Y c).mgr.legState f b = .Unset ↔ ∀ a ∈ appendCalls log, a.obligation enc ≠ ⟨f, b, c⟩ := by
  rw [(runAtHead_inv hr c).mgrUnset f b, mem_chainLog]
  constructor
  · intro hnot a ha heq
    exact hnot ⟨a, ha, heq⟩
  · rintro hall ⟨a, ha, heq⟩
    exact hall a ha heq

/-- On a head run from genesis, a leg that is not `Unset` was committed by a logged `append`. -/
theorem appended_of_not_unset {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {enc : PreimageHash} {l1 : UInt256} {S : System} {Y : Chains} {log : List CallAtHead}
    (hr : RunAtHead h z0 hl cv enc l1 S genesisAll Y log) {c f b : UInt256}
    (hne : (Y c).mgr.legState f b ≠ .Unset) :
    ∃ a ∈ appendCalls log, a.obligation enc = ⟨f, b, c⟩ := by
  by_contra hno
  apply hne
  rw [unset_iff_not_appended hr]
  intro a ha heq
  exact hno ⟨a, ha, heq⟩

/-- No obligation is appended twice, across all chains. -/
theorem appendLog_nodup {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {enc : PreimageHash} {l1 : UInt256} {S : System} {Y : Chains} {log : List CallAtHead}
    (hr : RunAtHead h z0 hl cv enc l1 S genesisAll Y log) : (appendLog enc log).Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro o
  rw [← count_filter_chain (appendLog enc log) o]
  exact List.nodup_iff_count_le_one.mp
    (AppendedAtMostOnce cv _ _ _ (runAtHead_chain hr o.chain)) o

/-- Two logged `append`s that committed one obligation are the same call. -/
theorem appendCall_unique {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {enc : PreimageHash} {l1 : UInt256} {S : System} {Y : Chains} {log : List CallAtHead}
    (hr : RunAtHead h z0 hl cv enc l1 S genesisAll Y log) {a a' : AppendCall}
    (ha : a ∈ appendCalls log) (ha' : a' ∈ appendCalls log)
    (he : a.obligation enc = a'.obligation enc) : a = a' :=
  List.inj_on_of_nodup_map (appendLog_nodup hr) ha ha' he

/-! ## The declared chain -/

/-- **THE BINDING LEMMA.** A logged `append` and a logged call with its flow id: the call's
preimage declares the appended bundle on the committing chain, or the two logged preimages
clash. -/
theorem declared_source_or_clash {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {enc : PreimageHash} {l1 : UInt256} {S : System} {X Y : Chains} {log : List CallAtHead}
    (hr : RunAtHead h z0 hl cv enc l1 S X Y log) {a : AppendCall} (ha : a ∈ appendCalls log)
    {k : CallAtHead} (hk : k ∈ log) (hid : k.flowId enc = enc a.preimage) {c' : UInt256}
    (hd : k.preimage.Declares a.bundleHash c') :
    c' = a.chain ∨ PreimageClash enc k.preimage a.preimage := by
  obtain ⟨hidk, _, _⟩ := logged_call_id hr hk
  have hca := (logged_calls_checked hr).1 a ha
  by_cases hp : k.preimage = a.preimage
  · left
    rw [hp] at hd
    exact declared_source_chain_unique hca.accepted hd hca.declares
  · right
    exact ⟨hp, hidk.trans hid⟩

/-- The same key appended on two chains is a logged preimage clash. -/
theorem same_key_two_chains_clash {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {enc : PreimageHash} {l1 : UInt256} {S : System} {X Y : Chains} {log : List CallAtHead}
    (hr : RunAtHead h z0 hl cv enc l1 S X Y log) {a a' : AppendCall} (ha : a ∈ appendCalls log)
    (ha' : a' ∈ appendCalls log) (hid : enc a.preimage = enc a'.preimage)
    (hb : a.bundleHash = a'.bundleHash) (hc : a.chain ≠ a'.chain) :
    PreimageClash enc a.preimage a'.preimage := by
  have hca' := (logged_calls_checked hr).1 a' ha'
  have hd : (CallAtHead.append a').preimage.Declares a.bundleHash a'.chain := by
    rw [hb]; exact hca'.declares
  rcases declared_source_or_clash hr ha (mem_appendCalls.mp ha') hid.symm hd with heq | hcl
  · exact absurd heq.symm hc
  · exact ⟨fun hp => hcl.1 hp.symm, hcl.2.symm⟩

/-- Every logged `authorizeRefund` marked a leg that a logged `append` committed on the chain
running it. -/
theorem authorized_was_appended {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {enc : PreimageHash} {l1 : UInt256} {S : System} {Y : Chains} {log : List CallAtHead}
    (hr : RunAtHead h z0 hl cv enc l1 S genesisAll Y log) :
    ∀ a, CallAtHead.authorize a ∈ log →
      ∃ ap ∈ appendCalls log, ap.obligation enc = ⟨a.flow.flowId, a.marked, a.chain⟩ := by
  induction hr with
  | refl => intro a ha; cases ha
  | append _ _ _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with hk | hk
    · cases hk
    · obtain ⟨ap, hap, he⟩ := ih a hk
      exact ⟨ap, by rw [appendCalls_append]; exact List.mem_cons_of_mem _ hap, he⟩
  | execute _ _ _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with hk | hk
    · cases hk
    · obtain ⟨ap, hap, he⟩ := ih a hk
      exact ⟨ap, by rw [appendCalls_execute]; exact hap, he⟩
  | @authorize Y log a' hprev _ hg ih =>
    intro a ha
    rcases List.mem_cons.mp ha with hk | hk
    · rw [CallAtHead.authorize.inj hk]
      have hne : (Y a'.chain).mgr.legState a'.flow.flowId a'.marked ≠ .Unset := by
        rw [show (Y a'.chain).mgr.legState a'.flow.flowId a'.marked = .Committed from hg]
        decide
      obtain ⟨ap, hap, he⟩ := appended_of_not_unset hprev hne
      exact ⟨ap, by rw [appendCalls_authorize]; exact hap, he⟩
    · obtain ⟨ap, hap, he⟩ := ih a hk
      exact ⟨ap, by rw [appendCalls_authorize]; exact hap, he⟩
  | claim _ _ ih => exact ih
  | initL2 _ _ ih => exact ih

/-- **`authorizeRefund` MARKS DECLARED LEGS, OR TWO LOGGED PREIMAGES CLASH.** -/
theorem authorize_marks_declared_or_clash {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {enc : PreimageHash} {l1 : UInt256} {S : System} {Y : Chains}
    {log : List CallAtHead} (hr : RunAtHead h z0 hl cv enc l1 S genesisAll Y log)
    {a : AuthCallAtHead} (ha : CallAtHead.authorize a ∈ log) :
    a.flow.preimage.Declares a.marked a.chain
      ∨ ∃ ap ∈ appendCalls log, ap.obligation enc = ⟨a.flow.flowId, a.marked, a.chain⟩
          ∧ PreimageClash enc a.flow.preimage ap.preimage := by
  obtain ⟨ap, hap, he⟩ := authorized_was_appended hr a ha
  obtain ⟨hf, hb, hc⟩ := AppendCall.obligation_eq_iff.mp he
  have hav := (logged_calls_checked hr).2.2 a ha
  obtain ⟨c', hc'⟩ := listed_leg_is_declared hav.1.accepted.lengths hav.2.2.2.2
  have hd : (CallAtHead.authorize a).preimage.Declares ap.bundleHash c' := by
    rw [hb]; exact hc'
  rcases declared_source_or_clash hr hap ha hf.symm hd with heq | hcl
  · left
    rw [heq, hc] at hc'
    exact hc'
  · right
    exact ⟨ap, hap, he, hcl⟩

/-! ## Refunds -/

/-- A leg past `Committed` on chain `c` was marked by a logged `authorizeRefund` on `c`. -/
theorem authorized_of_refunded {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {enc : PreimageHash} {l1 : UInt256} {S : System} {Y : Chains} {log : List CallAtHead}
    (hr : RunAtHead h z0 hl cv enc l1 S genesisAll Y log) :
    ∀ (c f b : UInt256), 2 ≤ rank ((Y c).mgr.legState f b) →
      ∃ r, CallAtHead.authorize r ∈ log ∧ r.chain = c ∧ r.flow.flowId = f ∧ r.marked = b := by
  induction hr with
  | refl =>
    intro c f b hrk
    simp [genesisAll, genesis, Contracts.AtomicFlowManager.empty, rank] at hrk
  | @append Y log a hint low _ ha ih =>
    intro c f b hrk
    have key : 2 ≤ rank ((Y c).mgr.legState f b) := by
      by_cases hc : c = a.chain
      · subst hc
        rw [update_self, appended_mgr] at hrk
        by_cases hk : f = enc a.preimage ∧ b = a.bundleHash
        · obtain ⟨rfl, rfl⟩ := hk
          rw [set_same] at hrk
          simp [rank] at hrk
        · rw [set_other hk] at hrk
          exact hrk
      · rw [update_other _ _ hc] at hrk
        exact hrk
    obtain ⟨r, hr', h1, h2, h3⟩ := ih c f b key
    exact ⟨r, List.mem_cons_of_mem _ hr', h1, h2, h3⟩
  | execute _ _ _ ih =>
    intro c f b hrk
    obtain ⟨r, hr', h1, h2, h3⟩ := ih c f b hrk
    exact ⟨r, List.mem_cons_of_mem _ hr', h1, h2, h3⟩
  | @authorize Y log a _ _ _ ih =>
    intro c f b hrk
    by_cases hk : c = a.chain ∧ f = a.flow.flowId ∧ b = a.marked
    · obtain ⟨rfl, rfl, rfl⟩ := hk
      exact ⟨a, List.mem_cons_self, rfl, rfl, rfl⟩
    · have key : 2 ≤ rank ((Y c).mgr.legState f b) := by
        by_cases hc : c = a.chain
        · subst hc
          rw [update_self] at hrk
          dsimp only at hrk
          have hk' : ¬ (f = a.flow.flowId ∧ b = a.marked) := fun h' => hk ⟨rfl, h'⟩
          rw [set_other hk'] at hrk
          exact hrk
        · rw [update_other _ _ hc] at hrk
          exact hrk
      obtain ⟨r, hr', h1, h2, h3⟩ := ih c f b key
      exact ⟨r, List.mem_cons_of_mem _ hr', h1, h2, h3⟩
  | @claim Y log c' f' b' _ hg ih =>
    intro c f b hrk
    apply ih c f b
    by_cases hk : c = c' ∧ f = f' ∧ b = b'
    · obtain ⟨rfl, rfl, rfl⟩ := hk
      rw [show (Y c).mgr.legState f b = .Revertable from hg]
      decide
    · by_cases hc : c = c'
      · subst hc
        rw [update_self] at hrk
        dsimp only at hrk
        have hk' : ¬ (f = f' ∧ b = b') := fun h' => hk ⟨rfl, h'⟩
        rw [set_other hk'] at hrk
        exact hrk
      · rw [update_other _ _ hc] at hrk
        exact hrk
  | @initL2 Y log c' _ _ ih =>
    intro c f b hrk
    apply ih c f b
    by_cases hc : c = c'
    · subst hc
      rw [update_self] at hrk
      exact hrk
    · rw [update_other _ _ hc] at hrk
      exact hrk

/-! ## The gate, through the pin view -/

/-- A logged execution is a pin execution of its pin flow, for the induced pin hash. -/
theorem logged_execution_pin {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {enc : PreimageHash} {l1 : UInt256} {S : System} {X Y : Chains} {log : List CallAtHead}
    (hr : RunAtHead h z0 hl cv enc l1 S X Y log) {e : ExecCallAtHead}
    (he : CallAtHead.execute e ∈ log) :
    ∃ leg, ExecutedViaBy h z0 hl cv (pinFlowHash enc l1) S (pinFlow e.flow) e.evidence leg := by
  have hev := (logged_calls_checked hr).2.1 e he
  obtain ⟨ce, hce⟩ := listed_leg_is_declared hev.1.accepted.lengths hev.2.2.1
  exact ⟨⟨ce, e.executing⟩, mk_mem_pinLegs_iff.mpr hce, headCheck_pinCheck hev.1 hev.2.1,
    hev.2.2.2⟩

/-- A head flow is its own committed-under flow when its preimage is the `append`'s and the
ids agree. -/
theorem committedFlow_eq {enc : PreimageHash} {F : AtomicFlow} {P : FlowPreimage}
    (hp : F.preimage = P) (hid : enc P = F.flowId) : committedFlow enc P = F := by
  obtain ⟨fid, Q⟩ := F
  simp only at hp hid
  subst hp hid
  rfl

/-- Two head flows with one id and one preimage are equal. -/
theorem atomicFlow_eq {F G : AtomicFlow} (h1 : F.flowId = G.flowId)
    (h2 : F.preimage = G.preimage) : F = G := by
  obtain ⟨f, P⟩ := F
  obtain ⟨g, Q⟩ := G
  simp only at h1 h2
  rw [h1, h2]

theorem executed_implies_committed_flow_finalizable_or_logged_clash {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {enc : PreimageHash} {l1 : UInt256} {S : System}
    (hS : Wf S) {A : Access} (hDA : DataAvailable h z0 hl S A) {X Y : Chains}
    {log : List CallAtHead} (hr : RunAtHead h z0 hl cv enc l1 S X Y log) {e : ExecCallAtHead}
    (he : CallAtHead.execute e ∈ log) {a : AppendCall} (_ha : a ∈ appendCalls log)
    (hid : enc a.preimage = e.flow.flowId) :
    FlowFinalizableBy h z0 hl cv S A (pinFlow (committedFlow enc a.preimage))
      ∨ PinnedGateBreak h z0 hl cv S A (pinFlow e.flow) e.evidence
      ∨ PreimageClash enc e.flow.preimage a.preimage := by
  have hev := (logged_calls_checked hr).2.1 e he
  obtain ⟨leg, hex⟩ := logged_execution_pin hr he
  by_cases hp : e.flow.preimage = a.preimage
  · rw [committedFlow_eq hp hid]
    rcases none_or_all_or_break_pinned (fh := pinFlowHash enc l1) hS hDA (pinFlow e.flow)
      e.evidence with hfin | hnex | hpin
    · exact Or.inl hfin
    · exact absurd hex (hnex leg)
    · exact Or.inr (Or.inl hpin)
  · exact Or.inr (Or.inr ⟨hp, hev.1.id_eq.trans hid.symm⟩)

theorem executed_implies_committed_leg_finalizable_or_logged_clash {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {enc : PreimageHash} {l1 : UInt256} {S : System}
    (hS : Wf S) {A : Access} (hDA : DataAvailable h z0 hl S A) {X Y : Chains}
    {log : List CallAtHead} (hr : RunAtHead h z0 hl cv enc l1 S X Y log) {e : ExecCallAtHead}
    (he : CallAtHead.execute e ∈ log) {a : AppendCall} (_ha : a ∈ appendCalls log)
    (hid : enc a.preimage = e.flow.flowId) {other : FlowLeg} (hother : other ∈ pinLegs a.preimage) :
    LegFinalizableBy h z0 hl cv S A (pinFlow (committedFlow enc a.preimage)) other
      ∨ InclusionBreak h z0 hl S other.chain (e.evidence other).1 (e.evidence other).2
      ∨ PreimageClash enc e.flow.preimage a.preimage := by
  have hev := (logged_calls_checked hr).2.1 e he
  obtain ⟨leg, hex⟩ := logged_execution_pin hr he
  by_cases hp : e.flow.preimage = a.preimage
  · rw [committedFlow_eq hp hid]
    have hother' : other ∈ (pinFlow e.flow).legs := by
      show other ∈ pinLegs e.flow.preimage
      rw [hp]; exact hother
    rcases executed_implies_all_finalizable_or_break hS hDA hex other hother' with hf | hb
    · exact Or.inl hf
    · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr ⟨hp, hev.1.id_eq.trans hid.symm⟩)

theorem logged_execution_excludes_logged_refund_or_break_at_head {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {enc : PreimageHash} {l1 : UInt256} {S : System}
    (hS : Wf S) {X Y : Chains} {log : List CallAtHead}
    (hr : RunAtHead h z0 hl cv enc l1 S X Y log) {e : ExecCallAtHead}
    (he : CallAtHead.execute e ∈ log) {r : AuthCallAtHead} (hr' : CallAtHead.authorize r ∈ log)
    (hid : r.flow.flowId = e.flow.flowId) :
    InclusionBreak h z0 hl S r.missing.chain (e.evidence r.missing).1 (e.evidence r.missing).2
      ∨ AbsenceBreak h z0 hl S r.flow.preimage.deadline r.missing.chain r.batch r.proof
      ∨ PreimageClash enc e.flow.preimage r.flow.preimage := by
  have hev := (logged_calls_checked hr).2.1 e he
  have hrv := (logged_calls_checked hr).2.2 r hr'
  obtain ⟨leg, hex⟩ := logged_execution_pin hr he
  by_cases hp : e.flow.preimage = r.flow.preimage
  · have hflow : r.flow = e.flow := atomicFlow_eq hid hp.symm
    have hmiss : r.missing ∈ (pinFlow e.flow).legs := by
      rw [← hflow]; exact hrv.2.2.1
    have href : LegRefundableBy h z0 hl cv S (pinFlow e.flow) r.missing r.batch r.proof := by
      rw [← hflow]; exact hrv.2.2.2.1
    rcases executed_excludes_any_refund_or_break hS hex r.missing hmiss r.batch r.proof
      with hn | hb | hb
    · exact absurd href hn
    · exact Or.inl hb
    · right; left
      rw [hflow]
      exact hb
  · exact Or.inr (Or.inr ⟨hp, hev.1.id_eq.trans (hid.symm.trans hrv.1.id_eq.symm)⟩)

end Contracts.FlowBindingAtHead

/-! ## Certificates -/

namespace Contracts.FlowBindingAtHead

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund Contracts.AppendPath
open Contracts.FlowCanonicalAtHead

theorem HeadCheckIsPinCheck : Properties.HeadCheckIsPinCheck :=
  fun _ _ _ hF hsl => headCheck_pinCheck hF hsl

theorem PinClashIsPreimageClash : Properties.PinClashIsPreimageClash :=
  fun _ _ _ _ hF hFs hG hGs => pin_clash_iff hF hFs hG hGs

theorem PinLegIffDeclares : Properties.PinLegIffDeclares :=
  fun _ _ _ => mk_mem_pinLegs_iff

theorem HeadInsertLandsWherePinInsertLands : Properties.HeadInsertLandsWherePinInsertLands := by
  intro T v low hV
  constructor
  · rintro ⟨hint, hins⟩
    exact ⟨low, InsertGuard.pinInsert (hins.guard hV)⟩
  · rintro ⟨hint, hins⟩
    exact ⟨hint, InsertSucceeds.atHead hins⟩

theorem HeadWalkAcceptsHintPinRejects : Properties.HeadWalkAcceptsHintPinRejects := by
  obtain ⟨_, hcount, hval0, hnone, hsome, hguard⟩ := HonestInsertRevertsAtDeployedFuel
  refine ⟨⟨hguard.initialized, hguard.nonzero, hguard.fresh, by rw [hcount]; decide, hval0,
    ⟨_, hsome⟩⟩, ?_⟩
  intro low hins
  have := hins.search
  rw [hnone] at this
  cases this

theorem RunAtHeadProjectsToChainRuns : Properties.RunAtHeadProjectsToChainRuns :=
  fun _ _ _ _ _ _ _ _ _ hr => runAtHead_chain hr

theorem LoggedCallsPassedTheirChecks : Properties.LoggedCallsPassedTheirChecks := by
  intro h z0 hl cv enc l1 S X Y log hr
  obtain ⟨h1, h2, h3⟩ := logged_calls_checked hr
  refine ⟨fun a ha => ?_, h2, h3⟩
  have hca := h1 a ha
  exact ⟨hca.check, hca.slIsL1, hca.notExpired, hca.declares, hca.othersRegistered⟩

theorem CommittedLegHasLoggedPreimage : Properties.CommittedLegHasLoggedPreimage := by
  intro h z0 hl cv enc l1 S Y log hr c f b hne
  obtain ⟨a, ha, he⟩ := appended_of_not_unset hr hne
  have hca := (logged_calls_checked hr).1 a ha
  obtain ⟨hf, hb, hc⟩ := AppendCall.obligation_eq_iff.mp he
  refine ⟨a, ⟨ha, he, ?_, hca.slIsL1, ?_⟩, ?_⟩
  · rw [← hf]; exact hca.check
  · rw [← hb, ← hc]; exact hca.declares
  · rintro a' ⟨ha', he', _, _, _⟩
    exact appendCall_unique hr ha' ha (he'.trans he.symm)

theorem UnsetIffNotAppended : Properties.UnsetIffNotAppended :=
  fun _ _ _ _ _ _ _ _ _ hr c f b => unset_iff_not_appended hr c f b

theorem CommittedLegIsInACheckedPinFlow : Properties.CommittedLegIsInACheckedPinFlow := by
  intro h z0 hl cv enc l1 S Y log hr c f b hne
  obtain ⟨a, ha, he⟩ := appended_of_not_unset hr hne
  have hca := (logged_calls_checked hr).1 a ha
  obtain ⟨hf, hb, hc⟩ := AppendCall.obligation_eq_iff.mp he
  refine ⟨pinFlow (committedFlow enc a.preimage), headCheck_pinCheck hca.check hca.slIsL1, hf, ?_⟩
  show (⟨c, b⟩ : FlowLeg) ∈ pinLegs a.preimage
  rw [mk_mem_pinLegs_iff, ← hb, ← hc]
  exact hca.declares

theorem DeclaredSourceIsCommittingChainOrLoggedClash :
    Properties.DeclaredSourceIsCommittingChainOrLoggedClash :=
  fun _ _ _ _ _ _ _ _ _ _ hr _ ha _ hk hid _ hd => declared_source_or_clash hr ha hk hid hd

theorem SameKeyAppendedOnTwoChainsIsLoggedClash :
    Properties.SameKeyAppendedOnTwoChainsIsLoggedClash :=
  fun _ _ _ _ _ _ _ _ _ _ hr _ ha _ ha' hid hb hc => same_key_two_chains_clash hr ha ha' hid hb hc

theorem AuthorizeMarksDeclaredLegOrLoggedClash :
    Properties.AuthorizeMarksDeclaredLegOrLoggedClash :=
  fun _ _ _ _ _ _ _ _ _ hr _ ha => authorize_marks_declared_or_clash hr ha

theorem KeyIsDeclaredOnItsChainOrLoggedClash : Properties.KeyIsDeclaredOnItsChainOrLoggedClash := by
  intro h z0 hl cv enc l1 S Y log hr k hk c c' b hd hv0 hkey
  obtain ⟨h1, _⟩ := KeyPinsAppendedLegOrClash cv c (Y c) _ (runAtHead_chain hr c)
    (k.flowId enc) b hv0 hkey
  rcases h1 with hmem | ⟨o, ho, hcl⟩
  · obtain ⟨ap, hap, he⟩ := mem_chainLog.mp hmem
    obtain ⟨hf, hb, hc⟩ := AppendCall.obligation_eq_iff.mp he
    have hd' : k.preimage.Declares ap.bundleHash c' := by rw [hb]; exact hd
    rcases declared_source_or_clash hr hap hk hf.symm hd' with heq | hcl
    · left; rw [heq, hc]
    · right; right; exact ⟨ap, hap, hc, hcl⟩
  · right; left
    exact ⟨o, (mem_filter_chain.mp ho).1, (mem_filter_chain.mp ho).2, hcl⟩

theorem SystemOncePerLegAtHead : Properties.SystemOncePerLegAtHead := by
  intro h z0 hl cv enc l1 S Y log hr
  have hc := runAtHead_chain hr
  have hown : ∀ {o : Obligation}, o ∈ appendLog enc log →
      o ∈ (appendLog enc log).filter (fun o' => o'.chain = o.chain) :=
    fun ho => mem_filter_chain.mpr ⟨ho, rfl⟩
  refine ⟨appendLog_nodup hr, ?_, ?_⟩
  · intro o ho
    exact ((OncePerLeg cv _ _ _ (hc o.chain)).2.1 o (hown ho)).2
  · intro a ha a' ha' heq
    have hoa : a.obligation enc ∈ appendLog enc log := mem_appendLog.mpr ⟨a, ha, rfl⟩
    have hoa' : a'.obligation enc ∈ appendLog enc log := mem_appendLog.mpr ⟨a', ha', rfl⟩
    by_cases hch : a.chain = a'.chain
    · left
      have hoa'' : a'.obligation enc ∈ (appendLog enc log).filter
          (fun x => x.chain = (a.obligation enc).chain) :=
        mem_filter_chain.mpr ⟨hoa', hch.symm⟩
      exact commitment_pins_logged_leg (hc (a.obligation enc).chain) (hown hoa) hoa'' heq
    · by_cases hkey : enc a.preimage = enc a'.preimage ∧ a.bundleHash = a'.bundleHash
      · right; right
        exact same_key_two_chains_clash hr ha ha' hkey.1 hkey.2 hch
      · right; left
        refine ⟨hch, ?_, heq⟩
        intro hp
        exact hkey (Prod.mk.inj hp)

theorem ExecutedImpliesCommittedFlowFinalizableOrLoggedClash :
    Properties.ExecutedImpliesCommittedFlowFinalizableOrLoggedClash :=
  fun _ _ _ _ _ _ _ hS _ hDA _ _ _ hr _ he _ ha hid =>
    executed_implies_committed_flow_finalizable_or_logged_clash hS hDA hr he ha hid

theorem ExecutedImpliesCommittedLegFinalizableOrLoggedClash :
    Properties.ExecutedImpliesCommittedLegFinalizableOrLoggedClash :=
  fun _ _ _ _ _ _ _ hS _ hDA _ _ _ hr _ he _ ha hid _ hother =>
    executed_implies_committed_leg_finalizable_or_logged_clash hS hDA hr he ha hid hother

theorem LoggedExecutionExcludesLoggedRefundOrBreakAtHead :
    Properties.LoggedExecutionExcludesLoggedRefundOrBreakAtHead :=
  fun _ _ _ _ _ _ _ hS _ _ _ hr _ he _ hr' hid =>
    logged_execution_excludes_logged_refund_or_break_at_head hS hr he hr' hid

theorem ExecutionFreezesItsFlowOrLoggedBreakAtHead :
    Properties.ExecutionFreezesItsFlowOrLoggedBreakAtHead := by
  intro h z0 hl cv enc l1 S hS Y log hr e he c b
  by_cases hrf : Refunded Y.mgrs ⟨e.flow.flowId, b, c⟩
  · right
    obtain ⟨r, hr', h1, h2, h3⟩ := authorized_of_refunded hr c e.flow.flowId b hrf
    exact ⟨r, hr', h1, h2, h3, logged_execution_excludes_logged_refund_or_break_at_head hS hr he hr' h2⟩
  · exact Or.inl hrf

theorem RefundedLegWasAuthorizedOnItsChain : Properties.RefundedLegWasAuthorizedOnItsChain :=
  fun _ _ _ _ _ _ _ _ _ hr c f b hrk => authorized_of_refunded hr c f b hrk

theorem PinUnboundLegIsStranded : Properties.PinUnboundLegIsStranded := by
  intro h z0 hl cv fh S Ms Ns alog o hrun hunbound hcom
  refine ⟨?_, ?_⟩
  · induction hrun with
    | refl => exact hcom
    | @append Ns log c f b _ hg ih =>
      by_cases ho : o = ⟨f, b, c⟩
      · subst ho
        exact stateOf_setAt_self _ _ _ _ _
      · rw [stateOf_setAt_other ho]
        exact ih
    | @authorize Ns log a _ hv _ ih =>
      have ho : o ≠ ⟨a.flow.flowId, a.leg.bundleHash, a.leg.chain⟩ := by
        intro ho
        obtain ⟨hchk, hleg, _, _⟩ := hv
        exact hunbound a.flow hchk (by rw [ho]) a.leg hleg (by rw [ho])
      rw [stateOf_setAt_other ho]
      exact ih
    | @claim Ns log c f b _ hg ih =>
      by_cases ho : o = ⟨f, b, c⟩
      · subst ho
        have hrev : stateOf Ns ⟨f, b, c⟩ = .Revertable := hg
        rw [ih] at hrev
        cases hrev
      · rw [stateOf_setAt_other ho]
        exact ih
  · intro F ev leg hex hid hb
    exact hunbound F hex.2.1 hid leg hex.1 hb

theorem PinUnboundLegRejectedAtHead : Properties.PinUnboundLegRejectedAtHead := by
  intro enc cv l1 env c s b P hint low hunbound happ
  have hacc := happ.accepted
  have hchk : CheckFlowId enc (committedFlow enc P) := checkFlowId_of_accepted enc hacc
  have hleg : (⟨c, b⟩ : FlowLeg) ∈ (pinFlow (committedFlow enc P)).legs :=
    mk_mem_pinLegs_iff.mpr happ.declares
  exact hunbound _ (headCheck_pinCheck hchk happ.slIsL1) rfl _ hleg rfl

theorem CommittedLegRefundableOnTimeout : Properties.CommittedLegRefundableOnTimeout := by
  intro h z0 hl cv enc l1 S Y log hr c f b hcom
  have hne : (Y c).mgr.legState f b ≠ .Unset := by rw [hcom]; decide
  obtain ⟨a, ha, he⟩ := appended_of_not_unset hr hne
  have hca := (logged_calls_checked hr).1 a ha
  obtain ⟨hf, hb, hc⟩ := AppendCall.obligation_eq_iff.mp he
  subst hf hb hc
  refine ⟨a, ha, he, ?_⟩
  intro m N q hm href
  have hv : AuthCallAtHead.Verified h z0 hl cv enc l1 S
      ⟨a.chain, committedFlow enc a.preimage, a.bundleHash, m, N, q⟩ :=
    ⟨hca.check, hca.slIsL1, hm, href, hca.declares.mem.1⟩
  exact RunAtHead.authorize _ hr hv hcom

end Contracts.FlowBindingAtHead

/-! ## Witnesses -/

namespace Contracts.FlowBindingAtHead

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund Contracts.AppendPath
open Contracts.FlowCanonicalAtHead Contracts.FlowBinding

/-! ### The pin countermodel -/

/-- The one-leg flow whose timeout the pin witness proves: id `0`, bundle `1` on chain `1`. -/
def pinBoundFlow : Flow := ⟨0, [⟨1, 1⟩], 0⟩

/-- The refund authorization of `pinBoundFlow`, on the honest absence proof at batch 1. -/
def pinBoundAuth (h : Hash) (z0 : UInt256) (hl : LeafHash) : AuthCall :=
  ⟨pinBoundFlow, ⟨1, 1⟩, ⟨1, 1⟩, 1, setupAbsence h z0 hl⟩

/-- Chain `1` has appended `(0, 1)`. -/
def pinM1 : Managers := setAt emptyManagers 1 ((emptyManagers 1).set 0 1 .Committed)

/-- Then `(0, 2)`, under the same id, which `pinBoundFlow` does not list. -/
def pinM2 : Managers := setAt pinM1 1 ((pinM1 1).set 0 2 .Committed)

/-- Then the timeout of `pinBoundFlow` marks `(0, 1)` `Revertable`. -/
def pinMs : Managers := setAt pinM2 1 ((pinM2 1).set 0 1 .Revertable)

theorem pin_unbound_run (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ReachLog h z0 hl (fun _ b => b) (honestFlowHash pinBoundFlow) (mixedSystem 5) emptyManagers
      pinMs [pinBoundAuth h z0 hl] := by
  have r1 : ReachLog h z0 hl (fun _ b => b) (honestFlowHash pinBoundFlow) (mixedSystem 5)
      emptyManagers pinM1 [] := ReachLog.append (c := 1) (f := 0) (b := 1) ReachLog.refl rfl
  have r2 : ReachLog h z0 hl (fun _ b => b) (honestFlowHash pinBoundFlow) (mixedSystem 5)
      emptyManagers pinM2 [] := by
    refine ReachLog.append (c := 1) (f := 0) (b := 2) r1 ?_
    show (pinM1 1).legState 0 2 = .Unset
    decide
  have h10 : (1 : Chain) ≠ 0 := by decide
  have hmem : (⟨1, 1⟩ : FlowLeg) ∈ pinBoundFlow.legs := List.mem_singleton_self _
  have hv : (pinBoundAuth h z0 hl).Verified h z0 hl (fun _ b => b) (honestFlowHash pinBoundFlow)
      (mixedSystem 5) := by
    refine ⟨(honest_flowHash_no_clash pinBoundFlow).1, hmem, hmem, ?_⟩
    exact setupAbsence_refundable (F := pinBoundFlow) (leg := ⟨1, 1⟩) (N := 0)
      (by show (0 : ℕ) < 1; norm_num) (mixedSystem_tree_other h10 0)
      (mixedSystem_height_other h10 0) (by show (0 : UInt256) < 1; decide)
  have hg : AuthorizeGuard (pinM2 1) 0 1 := by
    show (pinM2 1).legState 0 1 = .Committed
    decide
  exact ReachLog.authorize (pinBoundAuth h z0 hl) r2 hv hg

theorem PinUnboundLegWitness : Properties.PinUnboundLegWitness := by
  intro h z0 hl
  refine ⟨fun _ b => b, honestFlowHash pinBoundFlow, mixedSystem 5, pinMs, [pinBoundAuth h z0 hl],
    ⟨0, 2, 1⟩, pin_unbound_run h z0 hl, ?_, by decide,
    ⟨pinBoundAuth h z0 hl, List.mem_singleton_self _, rfl, rfl⟩, ?_⟩
  · intro F hF hid leg hleg hb
    by_cases hp : (F.legs, F.deadline) = (pinBoundFlow.legs, pinBoundFlow.deadline)
    · have hl' : F.legs = [⟨1, 1⟩] := congrArg Prod.fst hp
      rw [hl', List.mem_singleton] at hleg
      rw [hleg] at hb
      exact absurd hb (by decide)
    · have hval : honestFlowHash pinBoundFlow F.legs F.deadline = pinBoundFlow.flowId + 1 := by
        simp only [honestFlowHash, ite_eq_right hp]
      have h1 : F.flowId = 1 := by
        rw [← hF, hval]
        rfl
      rw [h1] at hid
      exact absurd hid (by decide)
  · show 2 ≤ rank ((pinMs 1).legState 0 1)
    decide

/-! ### The honest head run -/

/-- The L1 chain id of the witnesses. -/
def witnessL1 : UInt256 := 9

/-- The two-leg flow: bundle `1` on chain `0`, bundle `2` on chain `1`. -/
def pairPreimage : FlowPreimage := ⟨0x01, 0, witnessL1, [1, 2], [0, 1]⟩

/-- The one-leg flow: bundle `3` on chain `2`. -/
def singlePreimage : FlowPreimage := ⟨0x01, 0, witnessL1, [3], [2]⟩

/-- A preimage hash with `pairPreimage ↦ 1` and everything else `↦ 0`. -/
def witnessEnc : PreimageHash := fun P => if P = pairPreimage then 1 else 0

theorem witnessEnc_pair : witnessEnc pairPreimage = 1 := by
  unfold witnessEnc
  exact ite_eq_left rfl

theorem witnessEnc_single : witnessEnc singlePreimage = 0 := by
  unfold witnessEnc
  exact ite_eq_right (by decide)

theorem pairPreimage_accepted : PreimageAccepted pairPreimage :=
  ⟨rfl, by decide, by decide, rfl⟩

theorem singlePreimage_accepted : PreimageAccepted singlePreimage :=
  ⟨rfl, by decide, by decide, rfl⟩

/-- An environment in which no root has been imported and every chain is registered. -/
def witnessEnv : AppendEnv := ⟨fun _ => 0, fun _ => True⟩

/-- A head `append` at genesis, for an accepted preimage that declares the leg here. -/
theorem append_at_genesis {enc : PreimageHash} {cv : CommitValue} {l1 : UInt256}
    {c b : UInt256} {P : FlowPreimage} (hP : PreimageAccepted P)
    (hsl : P.settlementLayerChainId = l1)
    (hleg : ∃ i, P.legBundleHashes.idxOf? b = some i ∧ P.legSourceChainIds[i]? = some c)
    (hv : 0 < cv (enc P) b) :
    AppendSucceedsAtHead enc cv l1 witnessEnv c genesis b P 0 0 :=
  ⟨validate_of_accepted enc hP, hsl, Nat.zero_le _, hleg, fun _ _ _ => trivial, rfl,
    InsertSucceeds.atHead (InsertGuard.pinInsert (setup_insertGuard hv))⟩

def wa0 : AppendCall := ⟨0, 1, pairPreimage, witnessEnv⟩
def wa1 : AppendCall := ⟨1, 2, pairPreimage, witnessEnv⟩
def wa2 : AppendCall := ⟨2, 3, singlePreimage, witnessEnv⟩

/-- The refund authorization of the one-leg flow, on chain `2`. -/
def wr (h : Hash) (z0 : UInt256) (hl : LeafHash) : AuthCallAtHead :=
  ⟨2, ⟨0, singlePreimage⟩, 3, ⟨2, 3⟩, 1, setupAbsence h z0 hl⟩

/-- The execution of the two-leg flow's first leg, on honest evidence. -/
def we (h : Hash) (z0 : UInt256) (hl : LeafHash) : ExecCallAtHead :=
  ⟨⟨1, pairPreimage⟩, pairEvidence h z0 hl, 1⟩

/-- The states. -/
def wY1 : Chains :=
  genesisAll.update 0 ((genesisAll 0).appended (fun _ b => b) (witnessEnc pairPreimage) 1 0)
def wY2 : Chains := wY1.update 1 ((wY1 1).appended (fun _ b => b) (witnessEnc pairPreimage) 2 0)
def wY3 : Chains := wY2.update 2 ((wY2 2).appended (fun _ b => b) (witnessEnc singlePreimage) 3 0)
def wY4 : Chains := wY3.update 2 ⟨(wY3 2).mgr.set 0 3 .Revertable, (wY3 2).tree⟩

/-- The log, most recent first. -/
def wLog (h : Hash) (z0 : UInt256) (hl : LeafHash) : List CallAtHead :=
  [.execute (we h z0 hl), .authorize (wr h z0 hl), .append wa2, .append wa1, .append wa0]

theorem wY1_one : wY1 1 = genesis := update_other _ _ (by decide)
theorem wY2_two : wY2 2 = genesis := by
  rw [wY2, update_other _ _ (by decide), wY1, update_other _ _ (by decide)]
  rfl

theorem wY3_two_mgr :
    (wY3 2).mgr = Contracts.AtomicFlowManager.empty.set 0 3 .Committed := by
  rw [wY3, update_self, appended_mgr, wY2_two, witnessEnc_single]
  rfl

theorem pinFlow_pair : pinFlow ⟨1, pairPreimage⟩ = mixedFlow 1 1 2 := rfl

theorem pinFlow_single : pinFlow ⟨0, singlePreimage⟩ = strandedFlow := rfl

theorem witness_run (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    RunAtHead h z0 hl (fun _ b => b) witnessEnc witnessL1 (pairSystem 1 2) genesisAll wY4
      (wLog h z0 hl) := by
  have r1 : RunAtHead h z0 hl (fun _ b => b) witnessEnc witnessL1 (pairSystem 1 2) genesisAll
      wY1 [.append wa0] := by
    refine RunAtHead.append (hint := 0) (low := 0) wa0 RunAtHead.refl ?_
    exact append_at_genesis pairPreimage_accepted rfl ⟨0, by decide, rfl⟩
      (by show (0 : UInt256) < 1; decide)
  have r2 : RunAtHead h z0 hl (fun _ b => b) witnessEnc witnessL1 (pairSystem 1 2) genesisAll
      wY2 [.append wa1, .append wa0] := by
    refine RunAtHead.append (hint := 0) (low := 0) wa1 r1 ?_
    show AppendSucceedsAtHead witnessEnc (fun _ b => b) witnessL1 witnessEnv 1 (wY1 1) 2
      pairPreimage 0 0
    rw [wY1_one]
    exact append_at_genesis pairPreimage_accepted rfl ⟨1, by decide, rfl⟩
      (by show (0 : UInt256) < 2; decide)
  have r3 : RunAtHead h z0 hl (fun _ b => b) witnessEnc witnessL1 (pairSystem 1 2) genesisAll
      wY3 [.append wa2, .append wa1, .append wa0] := by
    refine RunAtHead.append (hint := 0) (low := 0) wa2 r2 ?_
    show AppendSucceedsAtHead witnessEnc (fun _ b => b) witnessL1 witnessEnv 2 (wY2 2) 3
      singlePreimage 0 0
    rw [wY2_two]
    exact append_at_genesis singlePreimage_accepted rfl ⟨0, by decide, rfl⟩
      (by show (0 : UInt256) < 3; decide)
  have h20 : (2 : Chain) ≠ 0 := by decide
  have h21 : (2 : Chain) ≠ 1 := by decide
  have hchk1 : CheckFlowId witnessEnc ⟨0, singlePreimage⟩ := by
    have := checkFlowId_of_accepted witnessEnc singlePreimage_accepted
    rw [witnessEnc_single] at this
    exact this
  have hrv : (wr h z0 hl).Verified h z0 hl (fun _ b => b) witnessEnc witnessL1 (pairSystem 1 2) := by
    refine ⟨hchk1, rfl, (by show (⟨2, 3⟩ : FlowLeg) ∈ pinLegs singlePreimage; decide), ?_,
      (by show (3 : UInt256) ∈ singlePreimage.legBundleHashes; decide)⟩
    rw [show (wr h z0 hl).flow = ⟨0, singlePreimage⟩ from rfl, pinFlow_single]
    exact setupAbsence_refundable (F := strandedFlow) (leg := ⟨2, 3⟩) (N := 0)
      (by show (0 : ℕ) < 1; norm_num) (pairSystem_tree_other h20 h21 0)
      (pairSystem_height_other h20 h21 0) (by show (0 : UInt256) < 3; decide)
  have hg : AuthorizeGuard (wY3 2).mgr 0 3 := by
    show (wY3 2).mgr.legState 0 3 = .Committed
    rw [wY3_two_mgr]
    decide
  have r4 := RunAtHead.authorize (wr h z0 hl) r3 hrv hg
  have hchk0 : CheckFlowId witnessEnc ⟨1, pairPreimage⟩ := by
    have := checkFlowId_of_accepted witnessEnc pairPreimage_accepted
    rw [witnessEnc_pair] at this
    exact this
  have hev : (we h z0 hl).Verified h z0 hl (fun _ b => b) witnessEnc witnessL1 (pairSystem 1 2) := by
    refine ⟨hchk0, rfl, (by show (1 : UInt256) ∈ pairPreimage.legBundleHashes; decide), ?_⟩
    rw [show (we h z0 hl).flow = ⟨1, pairPreimage⟩ from rfl, pinFlow_pair]
    exact fun _ hl' => pair_leg_finalizedBy h z0 hl hl'
  exact RunAtHead.execute (we h z0 hl) r4 hev

/-- Every preimage of the witness log is one of the two. -/
theorem wLog_preimages (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∀ k ∈ wLog h z0 hl, k.preimage = pairPreimage ∨ k.preimage = singlePreimage := by
  intro k hk
  simp only [wLog, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

theorem witness_no_logged_clash (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ¬ LoggedPreimageClash witnessEnc (wLog h z0 hl) := by
  rintro ⟨k, hk, k', hk', hne, heq⟩
  rcases wLog_preimages h z0 hl k hk with hp | hp <;>
    rcases wLog_preimages h z0 hl k' hk' with hp' | hp' <;>
    rw [hp, hp'] at hne heq
  · exact hne rfl
  · rw [witnessEnc_pair, witnessEnc_single] at heq
    exact absurd heq (by decide)
  · rw [witnessEnc_pair, witnessEnc_single] at heq
    exact absurd heq (by decide)
  · exact hne rfl

/-- The one-leg flow is not finalizable: chain `2` commits nothing in `pairSystem 1 2`. -/
theorem stranded_not_finalizable (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ¬ FlowFinalizableBy h z0 hl (fun _ b => b) (pairSystem 1 2)
      (honestAccess h z0 hl (pairSystem 1 2)) strandedFlow := by
  have h20 : (2 : Chain) ≠ 0 := by decide
  have h21 : (2 : Chain) ≠ 1 := by decide
  intro hall
  obtain ⟨n, p, _, ⟨i, _, rfl⟩, hacc⟩ := hall ⟨2, 3⟩ (List.mem_singleton_self _)
  have hv := hacc.valueMatch
  change (((pairSystem 1 2).tree 2 n).leaf i).value = 3 at hv
  rw [pairSystem_tree_other h20 h21] at hv
  change (0 : UInt256) = 3 at hv
  exact absurd hv (by decide)

theorem FlowBindingAtHeadWitness : Properties.FlowBindingAtHeadWitness := by
  intro h z0 hl
  have hfin := pair_flow_finalizable h z0 hl
  have hnp : ¬ PinnedGateBreak h z0 hl (fun _ b => b) (pairSystem 1 2)
      (honestAccess h z0 hl (pairSystem 1 2)) (pinFlow (we h z0 hl).flow) (we h z0 hl).evidence :=
    no_pinned_break_of_finalizable _ hfin
  have hcf0 : pinFlow (committedFlow witnessEnc wa0.preimage) = mixedFlow 1 1 2 := by
    show pinFlow ⟨witnessEnc pairPreimage, pairPreimage⟩ = _
    rw [witnessEnc_pair]
    rfl
  have hcf2 : pinFlow (committedFlow witnessEnc wa2.preimage) = strandedFlow := by
    show pinFlow ⟨witnessEnc singlePreimage, singlePreimage⟩ = _
    rw [witnessEnc_single]
    rfl
  have hmem0 : wa0 ∈ appendCalls (wLog h z0 hl) :=
    mem_appendCalls.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  have hkey : (fun _ b => b : CommitValue) (witnessEnc wa0.preimage) wa0.bundleHash
      ∈ keys (toAbs (wY4 wa0.chain).tree) :=
    (runAtHead_inv (witness_run h z0 hl) wa0.chain).key_of_mem
      (mem_chainLog.mpr ⟨wa0, hmem0, rfl⟩)
  have hcom : (wY4 wa0.chain).mgr.legState (witnessEnc wa0.preimage) wa0.bundleHash = .Committed := by
    show (wY4 0).mgr.legState (witnessEnc pairPreimage) 1 = .Committed
    rw [wY4, update_other _ _ (by decide), wY3, update_other _ _ (by decide), wY2,
      update_other _ _ (by decide), wY1, update_self, appended_mgr, set_same]
  refine ⟨fun _ b => b, witnessEnc, witnessL1, pairSystem 1 2, honestAccess h z0 hl (pairSystem 1 2),
    wY4, wLog h z0 hl, we h z0 hl, wr h z0 hl, wa0, wa2,
    pairSystem_wf (by decide) (by decide), honestAccess_dataAvailable h z0 hl _, witness_run h z0 hl,
    List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self, hmem0, ?_, rfl,
    witness_no_logged_clash h z0 hl, hcom, (by show (1 : UInt256) ≠ 0; decide), hkey,
    witnessEnc_pair, ?_, hnp, ?_, ?_,
    (by show singlePreimage.Declares 3 2; decide), ?_⟩
  · exact mem_appendCalls.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · rw [hcf0]; exact hfin
  · show witnessEnc singlePreimage ≠ 1
    rw [witnessEnc_single]
    decide
  · rintro (hf | hp | hcl)
    · rw [hcf2] at hf
      exact stranded_not_finalizable h z0 hl hf
    · exact hnp hp
    · have heq := hcl.2
      change witnessEnc pairPreimage = witnessEnc singlePreimage at heq
      rw [witnessEnc_pair, witnessEnc_single] at heq
      exact absurd heq (by decide)
  · show 2 ≤ rank ((wY4 2).mgr.legState 0 3)
    rw [wY4, update_self]
    show 2 ≤ rank (((wY3 2).mgr.set 0 3 .Revertable).legState 0 3)
    rw [set_same]
    decide

/-! ### One key on two chains -/

/-- Bundle `5`, declared on chain `0`. -/
def keyPreimage0 : FlowPreimage := ⟨0x01, 0, witnessL1, [5], [0]⟩

/-- Bundle `5`, declared on chain `1`. -/
def keyPreimage1 : FlowPreimage := ⟨0x01, 0, witnessL1, [5], [1]⟩

def ka0 : AppendCall := ⟨0, 5, keyPreimage0, witnessEnv⟩
def ka1 : AppendCall := ⟨1, 5, keyPreimage1, witnessEnv⟩

theorem SameKeyOnTwoChainsWitness : Properties.SameKeyOnTwoChainsWitness := by
  intro h z0 hl
  have hacc0 : PreimageAccepted keyPreimage0 := ⟨rfl, by decide, by decide, rfl⟩
  have hacc1 : PreimageAccepted keyPreimage1 := ⟨rfl, by decide, by decide, rfl⟩
  let enc : PreimageHash := fun _ => 0
  let Y1 : Chains := genesisAll.update 0 ((genesisAll 0).appended (fun _ b => b) (enc keyPreimage0) 5 0)
  have r1 : RunAtHead h z0 hl (fun _ b => b) enc witnessL1 (pairSystem 1 2) genesisAll Y1
      [.append ka0] := by
    refine RunAtHead.append (hint := 0) (low := 0) ka0 RunAtHead.refl ?_
    exact append_at_genesis hacc0 rfl ⟨0, by decide, rfl⟩ (by show (0 : UInt256) < 5; decide)
  have hY1 : Y1 1 = genesis := update_other _ _ (by decide)
  have r2 := RunAtHead.append (hint := 0) (low := 0) ka1 r1 (by
    show AppendSucceedsAtHead enc (fun _ b => b) witnessL1 witnessEnv 1 (Y1 1) 5 keyPreimage1 0 0
    rw [hY1]
    exact append_at_genesis hacc1 rfl ⟨0, by decide, rfl⟩ (by show (0 : UInt256) < 5; decide))
  refine ⟨fun _ b => b, enc, witnessL1, pairSystem 1 2, _, _, ka0, ka1, r2, ?_, ?_, rfl, rfl,
    by decide, by decide, ⟨by decide, rfl⟩⟩
  · exact mem_appendCalls.mpr (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact mem_appendCalls.mpr List.mem_cons_self

/-! ### Once per leg on each chain -/

theorem OncePerLegAtHead : Properties.OncePerLegAtHead := by
  intro h z0 hl cv enc l1 S Y log hr c
  obtain ⟨h1, h2, h3⟩ := Contracts.AppendPath.OncePerLeg cv c (Y c) (chainLog enc c log)
    (runAtHead_chain hr c)
  refine ⟨h1, h2, h3, ?_⟩
  intro a ha hc
  have hd := ((logged_calls_checked hr).1 a ha).declares
  rw [hc] at hd
  exact hd

/-! ### The pin instance's premise, at head -/

/-- The truncation of `pairPreimage`: bundle `1` on chain `0` only. -/
def subsetPreimage : FlowPreimage := ⟨0x01, 0, witnessL1, [1], [0]⟩

theorem subsetPreimage_accepted : PreimageAccepted subsetPreimage :=
  ⟨rfl, by decide, by decide, rfl⟩

theorem PinUnboundLegRejectedAtHeadWitness : Properties.PinUnboundLegRejectedAtHeadWitness := by
  refine ⟨honestPreimageHash subsetPreimage 0, witnessL1, subsetPreimage, subsetPreimage_accepted,
    rfl, ?_, by decide⟩
  intro F hF hid leg hleg hb
  have hencP : honestPreimageHash subsetPreimage 0 subsetPreimage = 0 := ite_eq_left rfl
  rw [hencP] at hid
  have hval : pinFlowHash (honestPreimageHash subsetPreimage 0) witnessL1 F.legs F.deadline = 0 := by
    rw [hF, hid]
  unfold pinFlowHash honestPreimageHash at hval
  by_cases hq : (⟨ATOMIC_FLOW_PREIMAGE_VERSION, F.deadline, witnessL1, F.legs.map FlowLeg.bundleHash,
      F.legs.map FlowLeg.chain⟩ : FlowPreimage) = subsetPreimage
  · have hm : F.legs.map FlowLeg.bundleHash = [1] := congrArg FlowPreimage.legBundleHashes hq
    have hin : leg.bundleHash ∈ F.legs.map FlowLeg.bundleHash := List.mem_map_of_mem hleg
    rw [hm, List.mem_singleton, hb] at hin
    exact absurd hin (by decide)
  · rw [ite_eq_right hq] at hval
    exact absurd hval (by decide)

/-! ### The subset-flow attack, at head -/

theorem SubsetFlowAttackAtHeadLandsInLoggedClash :
    Properties.SubsetFlowAttackAtHeadLandsInLoggedClash := by
  intro h z0 hl
  have h10 : (1 : Chain) ≠ 0 := by decide
  let cv : CommitValue := fun _ b => b
  let enc : PreimageHash := fun _ => 7
  let S : System := mixedSystem 1
  have hS : Wf S := mixedSystem_wf (by decide)
  -- the real flow's leg `2` is appended on chain `1`
  let sa : AppendCall := ⟨1, 2, pairPreimage, witnessEnv⟩
  let Y1 : Chains := genesisAll.update 1 ((genesisAll 1).appended cv (enc pairPreimage) 2 0)
  have r1 : RunAtHead h z0 hl cv enc witnessL1 S genesisAll Y1 [.append sa] := by
    refine RunAtHead.append (hint := 0) (low := 0) sa RunAtHead.refl ?_
    exact append_at_genesis pairPreimage_accepted rfl ⟨1, by decide, rfl⟩
      (by show (0 : UInt256) < 2; decide)
  -- leg `1` executes through the truncated preimage
  have hcountA : (S.tree 0 0).leafCount = 2 := by
    show ((mixedSystem 1).tree 0 0).leafCount = 2
    rw [mixedSystem_tree_zero]; rfl
  have accA : Accepts h z0 hl S 0 0 1 (honestProof h z0 hl S 0 0 1) :=
    honestProof_accepts hS (by rw [hcountA]; norm_num)
      (by show (((mixedSystem 1).tree 0 0).leaf 1).value = 1
          rw [mixedSystem_tree_zero, insertSetup_leaf_one_value])
  let se : ExecCallAtHead := ⟨⟨7, subsetPreimage⟩, subsetEvidence h z0 hl S 1, 1⟩
  have hev : se.Verified h z0 hl cv enc witnessL1 S := by
    refine ⟨checkFlowId_of_accepted enc subsetPreimage_accepted, rfl,
      (by show (1 : UInt256) ∈ subsetPreimage.legBundleHashes; decide), ?_⟩
    intro l hl'
    have hl'' : l = ⟨0, 1⟩ := by
      have : l ∈ [(⟨0, 1⟩ : FlowLeg)] := hl'
      exact List.mem_singleton.mp this
    subst hl''
    show LegFinalizedBy h z0 hl cv S (pinFlow se.flow) ⟨0, 1⟩
      (subsetEvidence h z0 hl S 1 ⟨0, 1⟩).1 (subsetEvidence h z0 hl S 1 ⟨0, 1⟩).2
    rw [subsetEvidence_legA]
    exact ⟨le_refl _, accA⟩
  have r2 := RunAtHead.execute se r1 hev
  -- the real flow's refund is authorized on chain `1`
  let sr : AuthCallAtHead := ⟨1, ⟨7, pairPreimage⟩, 2, ⟨1, 2⟩, 1, setupAbsence h z0 hl⟩
  have hrv : sr.Verified h z0 hl cv enc witnessL1 S := by
    refine ⟨checkFlowId_of_accepted enc pairPreimage_accepted, rfl,
      (by show (⟨1, 2⟩ : FlowLeg) ∈ pinLegs pairPreimage; decide), ?_,
      (by show (2 : UInt256) ∈ pairPreimage.legBundleHashes; decide)⟩
    exact setupAbsence_refundable (F := pinFlow sr.flow) (leg := ⟨1, 2⟩) (N := 0)
      (by show (0 : ℕ) < 1; norm_num) (mixedSystem_tree_other h10 0)
      (mixedSystem_height_other h10 0) (by show (0 : UInt256) < 2; decide)
  have hg : AuthorizeGuard (Y1 sr.chain).mgr sr.flow.flowId sr.marked := by
    show (Y1 1).mgr.legState 7 2 = .Committed
    show ((genesisAll.update 1 ((genesisAll 1).appended cv (enc pairPreimage) 2 0)) 1).mgr.legState
      7 2 = .Committed
    rw [update_self, appended_mgr]
    exact set_same
  have r3 := RunAtHead.authorize sr r2 hrv hg
  -- what holds of the logged pair
  have hnleg : ¬ LegFinalizableBy h z0 hl cv S (honestAccess h z0 hl S)
      (pinFlow (committedFlow enc sa.preimage)) ⟨1, 2⟩ := by
    rintro ⟨n, p, _, ⟨i, _, rfl⟩, hacc⟩
    have hv := hacc.valueMatch
    change (((mixedSystem 1).tree 1 n).leaf i).value = 2 at hv
    rw [mixedSystem_tree_other h10] at hv
    change (0 : UInt256) = 2 at hv
    exact absurd hv (by decide)
  have hfinSub : FlowFinalizableBy h z0 hl cv S (honestAccess h z0 hl S) (pinFlow se.flow) := by
    intro l hl'
    have hl'' : l = ⟨0, 1⟩ := by
      have : l ∈ [(⟨0, 1⟩ : FlowLeg)] := hl'
      exact List.mem_singleton.mp this
    subst hl''
    exact ⟨0, _, le_refl _, ⟨1, by rw [hcountA]; norm_num, rfl⟩, accA⟩
  have hnb : ¬ InclusionBreak h z0 hl S sr.missing.chain (se.evidence sr.missing).1
      (se.evidence sr.missing).2 := by
    show ¬ InclusionBreak h z0 hl S 1 (subsetEvidence h z0 hl S 1 ⟨1, 2⟩).1
      (subsetEvidence h z0 hl S 1 ⟨1, 2⟩).2
    rw [subsetEvidence_chain_one]
    exact honestProof_no_break h z0 hl _ 1 0 0
      (by show 0 < ((mixedSystem 1).tree 1 0).leafCount
          rw [mixedSystem_tree_other h10]; norm_num [setup])
  have hclash : PreimageClash enc subsetPreimage pairPreimage := ⟨by decide, rfl⟩
  refine ⟨cv, enc, witnessL1, S, honestAccess h z0 hl S, _, _, se, sr, sa, hS,
    honestAccess_dataAvailable h z0 hl _, r3, List.mem_cons_of_mem _ List.mem_cons_self,
    List.mem_cons_self,
    mem_appendCalls.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    rfl, rfl, fun hall => hnleg (hall _ (by show (⟨1, 2⟩ : FlowLeg) ∈ pinLegs pairPreimage; decide)),
    no_pinned_break_of_finalizable _ hfinSub, hclash, hnb,
    setupAbsence_no_break (N := 0) (by show (0 : ℕ) < 1; norm_num)
      (mixedSystem_tree_other h10 0) (mixedSystem_height_other h10 0), hclash⟩

end Contracts.FlowBindingAtHead
