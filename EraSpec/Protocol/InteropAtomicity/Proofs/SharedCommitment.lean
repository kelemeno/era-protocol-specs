import EraSpec.Protocol.InteropAtomicity.Properties.SharedCommitment
import EraSpec.Protocol.InteropAtomicity.Proofs.OncePerLeg
import EraSpec.Protocol.InteropAtomicity.Proofs.Refund
import EraSpec.Protocol.InteropAtomicity.Proofs.Atomicity
import EraSpec.Protocol.InteropAtomicity.Proofs.Timeout
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.TreeRoot

/-!
# Proofs: what a shared commitment means, on a run, at the gate and at the timeout check

The run-level results rest on topic `OncePerLeg`'s invariant (`Contracts.AppendPath.inv_of_steps`)
and on `Contracts.AppendPath.AppendEnabledIff`: on a reachable state, an `append` can succeed iff the
commit value is nonzero and not yet a key.  The converse directions append the list one entry at a
time, oldest first.  The gate results compose `inclusion_sound_or_break` (an accepted inclusion
proof names a key of the tree, or a located break) with
`Contracts.AppendPath.KeyPinsAppendedLegOrClash` (a nonzero key is a logged leg or clashes with
one).  The timeout result composes `verified_absence_excludes_delivered_or_break` (an accepted
absence proof against a valid tree means the value is not a key, or a located break) with the
invariant's "every logged commit value is a key".
-/

namespace Contracts.SharedCommitment

open MerkleSpec MerkleSpec.Verifier IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund Contracts.AppendPath

/-! ## Appendable logs -/

lemma appendable_sublist {cv : CommitValue} {c : Chain} {l₁ l₂ : List Obligation}
    (hA : AppendableLog cv c l₂) (hs : l₁.Sublist l₂) : AppendableLog cv c l₁ := by
  obtain ⟨hc, hv, hnd, hinj⟩ := hA
  refine ⟨fun o ho => hc o (hs.subset ho), fun o ho => hv o (hs.subset ho),
    List.Nodup.sublist hs hnd, ?_⟩
  intro o ho o' ho'
  exact hinj o (hs.subset ho) o' (hs.subset ho')

/-- On one chain, a clash-free duplicate-free log has pairwise distinct commit values. -/
lemma appendable_map_nodup {cv : CommitValue} {c : Chain} {log : List Obligation}
    (hA : AppendableLog cv c log) : (log.map (commitOf cv)).Nodup := by
  obtain ⟨hc, _, hnd, hinj⟩ := hA
  refine List.Nodup.map_on ?_ hnd
  intro o ho o' ho' heq
  by_contra hne
  apply hinj o ho o' ho'
  refine ⟨?_, heq⟩
  intro hp
  apply hne
  obtain ⟨hf, hb⟩ := Prod.mk.inj hp
  have hch : o.chain = o'.chain := (hc o ho).trans (hc o' ho').symm
  cases o
  cases o'
  simp_all

/-- Every run's log is appendable. -/
lemma appendable_of_steps {cv : CommitValue} {c : Chain} {s : ChainState} {log : List Obligation}
    (h : Steps cv c genesis s log) : AppendableLog cv c log := by
  have hI := inv_of_steps h
  exact ⟨hI.chainEq, hI.valsNe, List.Nodup.of_map (commitOf cv) hI.valsNodup,
    run_refutes_logged_commit_clash h⟩

/-- On a reachable state, an obligation whose commit value is nonzero and differs from every
logged one can be appended. -/
lemma append_fresh_succeeds {cv : CommitValue} {c : Chain} {s : ChainState}
    {log : List Obligation} (h : Steps cv c genesis s log) {o : Obligation}
    (hv : commitOf cv o ≠ 0) (hfresh : commitOf cv o ∉ log.map (commitOf cv)) :
    ∃ hint low, AppendSucceeds cv s o.flowId o.bundleHash hint low := by
  have hI := inv_of_steps h
  have hkey : cv o.flowId o.bundleHash ∉ keys (toAbs s.tree) := by
    rw [hI.keysEq, Finset.mem_insert, not_or]
    exact ⟨hv, fun hm => hfresh (List.mem_toFinset.mp hm)⟩
  exact (AppendEnabledIff cv c s log h o.flowId o.bundleHash).mpr ⟨hv, hkey⟩

/-- Every appendable log is the log of a run. -/
theorem chain_log_of_appendable {cv : CommitValue} {c : Chain} {log : List Obligation}
    (hA : AppendableLog cv c log) : ∃ s, Steps cv c genesis s log := by
  induction log with
  | nil => exact ⟨genesis, Steps.refl⟩
  | cons o l ih =>
    obtain ⟨s, hs⟩ := ih (appendable_sublist hA (List.sublist_cons_self o l))
    have hnd := appendable_map_nodup hA
    rw [List.map_cons, List.nodup_cons] at hnd
    have hoc : o.chain = c := hA.1 o List.mem_cons_self
    obtain ⟨hint, low, happ⟩ := append_fresh_succeeds hs (hA.2.1 o List.mem_cons_self) hnd.1
    subst hoc
    exact ⟨_, Steps.append hs happ⟩

/-- Every log that is appendable chain by chain is the log of a system run with no
authorizations. -/
theorem system_log_of_appendable {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {log : List Obligation}
    (hA : ∀ c, AppendableLog cv c (log.filter (fun o => o.chain = c))) :
    ∃ Y, SysSteps h z0 hl cv fh S genesisAll Y log [] := by
  induction log with
  | nil => exact ⟨genesisAll, SysSteps.refl⟩
  | cons o l ih =>
    obtain ⟨Y, hY⟩ := ih (fun c => appendable_sublist (hA c)
      ((List.sublist_cons_self o l).filter _))
    have hrun := sysSteps_chain hY o.chain
    have hAo := hA o.chain
    rw [List.filter_cons_of_pos (by simp)] at hAo
    have hnd := appendable_map_nodup hAo
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hint, low, happ⟩ := append_fresh_succeeds hrun (hAo.2.1 o List.mem_cons_self) hnd.1
    exact ⟨_, SysSteps.append hY happ⟩

theorem ChainLogIffAppendable : Properties.ChainLogIffAppendable := by
  intro cv c log
  constructor
  · rintro ⟨s, hs⟩
    exact appendable_of_steps hs
  · exact chain_log_of_appendable

theorem SystemLogIffAppendablePerChain : Properties.SystemLogIffAppendablePerChain := by
  intro h z0 hl cv fh S log
  constructor
  · rintro ⟨Y, alog, hr⟩ c
    exact appendable_of_steps (sysSteps_chain hr c)
  · intro hA
    obtain ⟨Y, hY⟩ := system_log_of_appendable (h := h) (z0 := z0) (hl := hl) (fh := fh) (S := S) hA
    exact ⟨Y, [], hY⟩

/-! ## An honest commit value for a finite list -/

/-- The `k`-th distinct `(flowId, bundleHash)` pair of `os` (counting from `0`) gets `k + 1`, and
every other pair gets `0`. -/
def indexCommitValue (os : List Obligation) : CommitValue := fun f b =>
  if hk : (os.map fun o => (o.flowId, o.bundleHash)).idxOf (f, b) + 1 < UInt256.size then
    ⟨(os.map fun o => (o.flowId, o.bundleHash)).idxOf (f, b) + 1, hk⟩
  else 0

lemma indexCommitValue_val {os : List Obligation} (hlen : os.length < UInt256.size)
    {o : Obligation} (ho : o ∈ os) :
    ((indexCommitValue os o.flowId o.bundleHash : UInt256) : ℕ)
      = (os.map fun o => (o.flowId, o.bundleHash)).idxOf (o.flowId, o.bundleHash) + 1 := by
  have hmem : (o.flowId, o.bundleHash) ∈ os.map (fun o => (o.flowId, o.bundleHash)) :=
    List.mem_map_of_mem ho
  have hlt := List.idxOf_lt_length_iff.mpr hmem
  rw [List.length_map] at hlt
  have hk : (os.map fun o => (o.flowId, o.bundleHash)).idxOf (o.flowId, o.bundleHash) + 1
      < UInt256.size := by omega
  simp only [indexCommitValue, hk, dite_true]

theorem HonestCommitValueRealizesChainLog : Properties.HonestCommitValueRealizesChainLog := by
  intro c os hc hnd hlen
  have hinj : CommitValueInjOn (indexCommitValue os) os := by
    rintro o ho o' ho' ⟨hne, heq⟩
    apply hne
    have h1 := indexCommitValue_val hlen ho
    have h2 := indexCommitValue_val hlen ho'
    have hval := congrArg Fin.val heq
    have hidx : (os.map fun o => (o.flowId, o.bundleHash)).idxOf (o.flowId, o.bundleHash)
        = (os.map fun o => (o.flowId, o.bundleHash)).idxOf (o'.flowId, o'.bundleHash) := by
      omega
    exact (List.idxOf_inj
      (List.mem_map_of_mem (f := fun o : Obligation => (o.flowId, o.bundleHash)) ho)).mp hidx
  refine ⟨indexCommitValue os, hinj, chain_log_of_appendable ⟨hc, ?_, hnd, hinj⟩⟩
  intro o ho h0
  have h1 := indexCommitValue_val hlen ho
  have h0' : ((indexCommitValue os o.flowId o.bundleHash : UInt256) : ℕ) = 0 := by
    have : indexCommitValue os o.flowId o.bundleHash = 0 := h0
    rw [this]
    rfl
  omega

theorem HonestCommitValueRealizesChainLogWitness :
    Properties.HonestCommitValueRealizesChainLogWitness := by
  refine ⟨0, [⟨0, 1, 0⟩, ⟨0, 2, 0⟩], by simp, by decide, by decide, rfl, ?_⟩
  intro hinj
  exact hinj ⟨0, 1, 0⟩ List.mem_cons_self ⟨0, 2, 0⟩ (List.mem_cons_of_mem _ List.mem_cons_self)
    ⟨by decide, rfl⟩

/-! ## What a shared commitment means in a run -/

/-- Every obligation drawn from a system run's logs was appended. -/
lemma runObligations_appended {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {Y : Chains} {log : List Obligation} {alog : List AuthCall}
    (hr : SysSteps h z0 hl cv fh S genesisAll Y log alog) {o : Obligation}
    (ho : o ∈ runObligations log alog) : o ∈ log := by
  rcases List.mem_append.mp ho with ho | ho
  · exact ho
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
    exact (SystemAuthorizedWereAppended h z0 hl cv fh S Y log alog hr).1 a ha

theorem SharedCommitmentPinnedToRun : Properties.SharedCommitmentPinnedToRun := by
  intro h z0 hl cv fh S Y log alog hr o ho o' ho' heq
  by_cases hch : o.chain = o'.chain
  · exact Or.inl ((SystemOncePerLeg h z0 hl cv fh S Y log alog hr).2.2 o
      (runObligations_appended hr ho) o' (runObligations_appended hr ho') hch heq)
  · refine Or.inr ⟨hch, ?_⟩
    by_cases hp : (o.flowId, o.bundleHash) = (o'.flowId, o'.bundleHash)
    · exact Or.inl (Prod.mk.inj hp)
    · exact Or.inr ⟨hp, heq⟩

/-- A single obligation on its own chain, with a nonzero commit value, is an appendable log. -/
lemma appendable_singleton {cv : CommitValue} {c : Chain} {o : Obligation} (hc : o.chain = c)
    (hv : commitOf cv o ≠ 0) : AppendableLog cv c [o] := by
  refine ⟨?_, ?_, List.nodup_singleton o, ?_⟩
  · intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact hc
  · intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact hv
  · rintro x hx y hy ⟨hne, _⟩
    rw [List.mem_singleton] at hx hy
    subst hx
    subst hy
    exact hne rfl

lemma appendable_nil (cv : CommitValue) (c : Chain) : AppendableLog cv c [] :=
  ⟨by simp, by simp, List.nodup_nil, by simp [CommitValueInjOn]⟩

theorem SharedCommitmentCoexistsIffCrossChain : Properties.SharedCommitmentCoexistsIffCrossChain := by
  intro h z0 hl cv fh S o o' hne heq hv0
  constructor
  · rintro ⟨Y, log, alog, hr, ho, ho'⟩ hch
    exact hne ((SystemOncePerLeg h z0 hl cv fh S Y log alog hr).2.2 o ho o' ho' hch heq)
  · intro hch
    have hv0' : commitOf cv o' ≠ 0 := heq ▸ hv0
    have hA : ∀ c, AppendableLog cv c ([o', o].filter (fun x => x.chain = c)) := by
      intro c
      by_cases hc : o.chain = c
      · have hc' : ¬ o'.chain = c := fun h' => hch (hc.trans h'.symm)
        simp only [List.filter_cons, hc, hc', decide_true, decide_false, List.filter_nil]
        exact appendable_singleton hc hv0
      · by_cases hc' : o'.chain = c
        · simp only [List.filter_cons, hc, hc', decide_true, decide_false, List.filter_nil]
          exact appendable_singleton hc' hv0'
        · simp only [List.filter_cons, hc, hc', decide_false, List.filter_nil]
          exact appendable_nil cv c
    obtain ⟨Y, hY⟩ := system_log_of_appendable (h := h) (z0 := z0) (hl := hl) (fh := fh) (S := S) hA
    exact ⟨Y, [o', o], [], hY, by simp, by simp⟩

theorem SharedCommitmentCoexistsIffCrossChainWitness :
    Properties.SharedCommitmentCoexistsIffCrossChainWitness := by
  intro h z0 hl
  have hiff := SharedCommitmentCoexistsIffCrossChain h z0 hl constCv lengthFlowHash (mixedSystem 1)
  refine ⟨constCv, lengthFlowHash, mixedSystem 1, ⟨0, 1, 0⟩, ⟨1, 2, 1⟩, ⟨0, 2, 0⟩, by decide,
    by decide, rfl, rfl, by decide, ?_, ?_⟩
  · exact (hiff ⟨0, 1, 0⟩ ⟨1, 2, 1⟩ (by decide) rfl (by decide)).mpr (by decide)
  · intro hco
    exact (hiff ⟨0, 1, 0⟩ ⟨0, 2, 0⟩ (by decide) rfl (by decide)).mp hco rfl

/-! ## The run-level witnesses -/

/-- At genesis, `append(f, b, _, 0)` succeeds through the sentinel for every nonzero commit
value. -/
lemma append_genesis_zero {cv : CommitValue} {f b : UInt256} (hv : cv f b ≠ 0) :
    AppendSucceeds cv genesis f b 0 0 := by
  refine ⟨rfl, by unfold Initialized; decide, hv, rfl, by decide, ?_, ?_⟩
  · show (0 : UInt256) < cv f b
    exact Fin.pos_iff_ne_zero.mpr hv
  · apply lowSearch_stop
    rintro ⟨hne, _⟩
    exact hne rfl

/-- Chain `1` appends `⟨1, 2, 1⟩` (leg `⟨1, 2⟩` of `mixedFlow 1 1 2`) under `bundleCv`. -/
def sameLegY1 : Chains := genesisAll.update 1 (genesis.appended bundleCv 1 2 0)

/-- Then chain `0` appends the same `(flowId, bundleHash)`, as `⟨1, 2, 0⟩`. -/
def sameLegY2 : Chains := sameLegY1.update 0 ((sameLegY1 0).appended bundleCv 1 2 0)

lemma sameLegY1_zero : sameLegY1 0 = genesis := update_other _ _ (by decide)

lemma sameLegY2_one : sameLegY2 1 = genesis.appended bundleCv 1 2 0 := by
  rw [sameLegY2, update_other _ _ (by decide : (1 : Chain) ≠ 0), sameLegY1, update_self]

theorem SharedCommitmentSameLegTwoChainsWitness :
    Properties.SharedCommitmentSameLegTwoChainsWitness := by
  intro h z0 hl
  have h1 : (0 : UInt256) < 1 := by decide
  have h2 : (0 : UInt256) < 2 := by decide
  have r1 : SysSteps h z0 hl bundleCv lengthFlowHash (mixedSystem 1) genesisAll sameLegY1
      [⟨1, 2, 1⟩] [] :=
    SysSteps.append (c := 1) (f := 1) (b := 2) (hint := 0) (low := 0) SysSteps.refl
      (append_genesis_zero (by decide))
  have happ₂ : AppendSucceeds bundleCv (sameLegY1 0) 1 2 0 0 := by
    rw [sameLegY1_zero]
    exact append_genesis_zero (by decide)
  have r2 : SysSteps h z0 hl bundleCv lengthFlowHash (mixedSystem 1) genesisAll sameLegY2
      [⟨1, 2, 0⟩, ⟨1, 2, 1⟩] [] :=
    SysSteps.append (c := 0) (f := 1) (b := 2) (hint := 0) (low := 0) r1 happ₂
  -- the timeout that authorizes leg `⟨1, 2⟩` of `mixedFlow 1 1 2`, on chain `1`
  obtain ⟨N, p, href⟩ := (subset_flow_passes_unchecked_gate (h := h) (z0 := z0) (hl := hl)
    (cv := bundleCv) (id := 1) (hA := 1) (hB := 2) h1 h2).2.2
  have hmem : (⟨1, 2⟩ : FlowLeg) ∈ (mixedFlow 1 1 2).legs := by simp [mixedFlow]
  have hv : AuthCall.Verified h z0 hl bundleCv lengthFlowHash (mixedSystem 1)
      ⟨mixedFlow 1 1 2, ⟨1, 2⟩, ⟨1, 2⟩, N, p⟩ :=
    ⟨lengthFlowHash_checks_mixed, hmem, hmem, href⟩
  have hg : AuthorizeGuard (sameLegY2 1).mgr 1 2 := by
    rw [sameLegY2_one]
    unfold AuthorizeGuard
    simp [Manager.set]
  have r3 := SysSteps.authorize ⟨mixedFlow 1 1 2, ⟨1, 2⟩, ⟨1, 2⟩, N, p⟩ r2 hv hg
  have hall : ∀ x ∈ runObligations [⟨1, 2, 0⟩, ⟨1, 2, 1⟩]
      [(⟨mixedFlow 1 1 2, ⟨1, 2⟩, ⟨1, 2⟩, N, p⟩ : AuthCall)], x.flowId = 1 ∧ x.bundleHash = 2 := by
    intro x hx
    simp only [runObligations, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  refine ⟨bundleCv, lengthFlowHash, mixedSystem 1, _, _, _, ⟨1, 2, 0⟩, ⟨1, 2, 1⟩, r3,
    List.cons_ne_nil _ _, List.cons_ne_nil _ _, by simp [runObligations],
    by simp [runObligations], rfl, by decide, ⟨rfl, rfl⟩, ?_⟩
  rintro x hx y hy ⟨hne, _⟩
  obtain ⟨hx1, hx2⟩ := hall x hx
  obtain ⟨hy1, hy2⟩ := hall y hy
  exact hne (by rw [hx1, hx2, hy1, hy2])

theorem SharedCommitmentCrossChainClashWitness :
    Properties.SharedCommitmentCrossChainClashWitness := by
  intro h z0 hl
  exact ⟨constCv, lengthFlowHash, mixedSystem 1, sysY2, [⟨1, 2, 1⟩, ⟨0, 1, 0⟩], [], ⟨0, 1, 0⟩,
    ⟨1, 2, 1⟩, sys_r2 h z0 hl, by simp [runObligations], by simp [runObligations],
    ⟨by decide, rfl⟩, by decide⟩

/-! ## The managers alone -/

/-- The honest absence proof against `setup`: the sentinel at index 0, at height 0. -/
def scSetupAbsence (h : Hash) (z0 : UInt256) (hl : LeafHash) : ImtProof :=
  ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩

/-- `authorizeRefund(mixedFlow 1 1 b, ⟨1, b⟩, ·)` on the BEGIN root of chain `1`'s late batch 1,
marking leg `⟨1, b⟩`. -/
def scCall (h : Hash) (z0 : UInt256) (hl : LeafHash) (b : UInt256) : AuthCall :=
  ⟨mixedFlow 1 1 b, ⟨1, b⟩, ⟨1, b⟩, 1, scSetupAbsence h z0 hl⟩

lemma scCall_verified (h : Hash) (z0 : UInt256) (hl : LeafHash) (b : UInt256) :
    (scCall h z0 hl b).Verified h z0 hl constCv lengthFlowHash (mixedSystem 1) := by
  have h1 : (0 : UInt256) < 1 := by decide
  have hne : (1 : Chain) ≠ 0 := by decide
  have hbegin : beginTree (mixedSystem 1) 1 1 = setup := mixedSystem_tree_other hne 0
  have hbeginH : beginHeight (mixedSystem 1) 1 1 = 0 := mixedSystem_height_other hne 0
  have hmem : (⟨1, b⟩ : FlowLeg) ∈ (mixedFlow 1 1 b).legs := by simp [mixedFlow]
  refine ⟨by simp [scCall, FlowIdChecked, lengthFlowHash, mixedFlow], hmem, hmem,
    Or.inl ⟨by norm_num [scCall, mixedFlow], ?_⟩⟩
  show AbsenceAccepted h z0 hl (beginTree (mixedSystem 1) 1 1) (beginHeight (mixedSystem 1) 1 1)
    1 (scSetupAbsence h z0 hl)
  rw [hbegin, hbeginH]
  exact Contracts.Timeout.setup_absence_accepted h z0 hl h1

/-- The managers after appending `(1, 2)` on chain `1`. -/
def scM1 : Managers := setAt emptyManagers 1 ((emptyManagers 1).set 1 2 .Committed)
/-- Then `(1, 3)` on chain `1`: the manager's guard does not look at the commit value. -/
def scM2 : Managers := setAt scM1 1 ((scM1 1).set 1 3 .Committed)
/-- Then `(1, 2)` authorized. -/
def scM3 : Managers := setAt scM2 1 ((scM2 1).set 1 2 .Revertable)
/-- Then `(1, 3)` authorized. -/
def scM4 : Managers := setAt scM3 1 ((scM3 1).set 1 3 .Revertable)

theorem SharedCommitmentManagersAloneAdmitSameChainClash :
    Properties.SharedCommitmentManagersAloneAdmitSameChainClash := by
  intro h z0 hl
  have r1 : ReachLog h z0 hl constCv lengthFlowHash (mixedSystem 1) emptyManagers scM1 [] :=
    ReachLog.append (c := 1) (f := 1) (b := 2) ReachLog.refl rfl
  have g2 : AppendGuard (scM1 1) 1 3 := by
    show (scM1 1).legState 1 3 = .Unset
    decide
  have r2 : ReachLog h z0 hl constCv lengthFlowHash (mixedSystem 1) emptyManagers scM2 [] :=
    ReachLog.append (c := 1) (f := 1) (b := 3) r1 g2
  have g3 : AuthorizeGuard (scM2 1) 1 2 := by
    show (scM2 1).legState 1 2 = .Committed
    decide
  have r3 : ReachLog h z0 hl constCv lengthFlowHash (mixedSystem 1) emptyManagers scM3
      [scCall h z0 hl 2] :=
    ReachLog.authorize (scCall h z0 hl 2) r2 (scCall_verified h z0 hl 2) g3
  have g4 : AuthorizeGuard (scM3 1) 1 3 := by
    show (scM3 1).legState 1 3 = .Committed
    decide
  have r4 : ReachLog h z0 hl constCv lengthFlowHash (mixedSystem 1) emptyManagers scM4
      [scCall h z0 hl 3, scCall h z0 hl 2] :=
    ReachLog.authorize (scCall h z0 hl 3) r3 (scCall_verified h z0 hl 3) g4
  have hcl : CommitClash constCv (⟨1, 3, 1⟩ : Obligation) ⟨1, 2, 1⟩ := ⟨by decide, rfl⟩
  refine ⟨constCv, lengthFlowHash, mixedSystem 1, scM4, [scCall h z0 hl 3, scCall h z0 hl 2],
    scCall h z0 hl 3, scCall h z0 hl 2, r4, List.mem_cons_self,
    List.mem_cons_of_mem _ List.mem_cons_self, rfl, hcl, ?_⟩
  intro Y log hsys
  exact (SystemAuthorizedWereAppended h z0 hl constCv lengthFlowHash (mixedSystem 1) Y log _
    hsys).2 (scCall h z0 hl 3) List.mem_cons_self (scCall h z0 hl 2)
    (List.mem_cons_of_mem _ List.mem_cons_self) rfl hcl

/-! ## What a shared commitment means at the gate -/

theorem gate_leg_was_appended_or_clash {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {F : Flow} {leg : FlowLeg} {n : ℕ} {p : ImtProof}
    {s : ChainState} {l : List Obligation} (hrun : Steps cv leg.chain genesis s l)
    (htree : S.tree leg.chain n = s.tree) (hfin : LegFinalizedBy h z0 hl cv S F leg n p) :
    (obligationOf F leg ∈ l ∨ (∃ o ∈ l, CommitClash cv (obligationOf F leg) o)
        ∨ legValue cv F leg = 0 ∨ InclusionBreak h z0 hl S leg.chain n p)
      ∧ ¬ (obligationOf F leg ∈ l ∧ ∃ o ∈ l, CommitClash cv (obligationOf F leg) o) := by
  refine ⟨?_, ?_⟩
  · have hacc : InclusionAccepted h hl (root h z0 hl (S.tree leg.chain n) (S.height leg.chain n))
        (legValue cv F leg) p.leaf p.index p.sibs p.pathLen := hfin.2
    rcases inclusion_sound_or_break hacc with hkey | hb
    · by_cases hv0 : legValue cv F leg = 0
      · exact Or.inr (Or.inr (Or.inl hv0))
      · rw [htree] at hkey
        rcases (KeyPinsAppendedLegOrClash cv leg.chain s l hrun F.flowId leg.bundleHash hv0
          hkey).1 with hm | hcl
        · exact Or.inl hm
        · exact Or.inr (Or.inl hcl)
    · exact Or.inr (Or.inr (Or.inr hb))
  · rintro ⟨hm, o, ho, hne, heq⟩
    exact hne (congrArg (fun x : Obligation => (x.flowId, x.bundleHash))
      (commitment_pins_logged_leg hrun hm ho heq))

theorem GateLegWasAppendedOrClash : Properties.GateLegWasAppendedOrClash :=
  fun _ _ _ _ _ _ _ _ _ _ _ hrun htree hfin => gate_leg_was_appended_or_clash hrun htree hfin

theorem ExecutedFlowLegsWereAppendedOrClash : Properties.ExecutedFlowLegsWereAppendedOrClash := by
  intro h z0 hl cv fh S snap logAt hH F ev leg hex other hother
  obtain ⟨hrun, htree⟩ := hH other.chain (ev other).1
  exact (gate_leg_was_appended_or_clash hrun htree (hex.2.2 other hother)).1

theorem SystemHistoryIsHistoryFromRuns : Properties.SystemHistoryIsHistoryFromRuns := by
  intro h z0 hl cv fh S' S snapY logs alogs hH c n
  obtain ⟨hr, htree⟩ := hH n
  exact ⟨sysSteps_chain hr c, htree c⟩

theorem ExecutedFlowLegsWereAppendedInSystemOrClash :
    Properties.ExecutedFlowLegsWereAppendedInSystemOrClash := by
  intro h z0 hl cv fh S' S snapY logs alogs hH F ev leg hex other hother
  rcases ExecutedFlowLegsWereAppendedOrClash h z0 hl cv fh S _ _
      (SystemHistoryIsHistoryFromRuns h z0 hl cv fh S' S snapY logs alogs hH) F ev leg hex
      other hother with hm | ⟨o, ho, hcl⟩ | h0 | hb
  · exact Or.inl (mem_filter_chain.mp hm).1
  · exact Or.inr (Or.inl ⟨o, (mem_filter_chain.mp ho).1, (mem_filter_chain.mp ho).2, hcl⟩)
  · exact Or.inr (Or.inr (Or.inl h0))
  · exact Or.inr (Or.inr (Or.inr hb))

/-! ## The gate-level witnesses -/

/-- In `mixedSystem 1`, a one-leg flow on chain `0` whose commit value is the value of leaf `i`
of chain `0`'s tree executes on the honest proof of leaf `i`, and that proof carries no break. -/
lemma sc_subsetFlow_executes (h : Hash) (z0 : UInt256) (hl : LeafHash) {cv : CommitValue}
    {fh : FlowHash} {id b : UInt256} {i : ℕ} (hi : i < 2)
    (hchk : FlowIdChecked fh (subsetFlow id b))
    (hv : cv id b = (((mixedSystem 1).tree 0 0).leaf i).value) :
    ExecutedViaBy h z0 hl cv fh (mixedSystem 1) (subsetFlow id b)
        (fun _ => (0, honestProof h z0 hl (mixedSystem 1) 0 0 i)) ⟨0, b⟩
      ∧ ¬ InclusionBreak h z0 hl (mixedSystem 1) 0 0
          (honestProof h z0 hl (mixedSystem 1) 0 0 i) := by
  have h1 : (0 : UInt256) < 1 := by decide
  have hS := mixedSystem_wf h1
  have hcount : ((mixedSystem 1).tree 0 0).leafCount = 2 := by
    rw [mixedSystem_tree_zero]; rfl
  have hacc : Accepts h z0 hl (mixedSystem 1) 0 0 (cv id b)
      (honestProof h z0 hl (mixedSystem 1) 0 0 i) := by
    have := inclusion_complete (h := h) (z0 := z0) (hl := hl) (T := (mixedSystem 1).tree 0 0)
      (height := (mixedSystem 1).height 0 0) (hS.capacity 0 0) (i := i) (by rw [hcount]; exact hi)
    rw [← hv] at this
    exact this
  refine ⟨⟨List.mem_singleton_self _, hchk, ?_⟩,
    honestProof_no_break h z0 hl _ 0 0 i (by rw [hcount]; exact hi)⟩
  intro l hl'
  obtain rfl : l = ⟨0, b⟩ := List.mem_singleton.mp hl'
  exact ⟨by simp [subsetFlow], hacc⟩

/-- Chain `0` has appended `⟨0, 1, 0⟩` from batch 0 on; every other chain is at genesis. -/
def scSnap (cv : CommitValue) : Chain → ℕ → ChainState :=
  fun c _ => if c = 0 then genesis.appended cv 0 1 0 else genesis

/-- The matching logs. -/
def scLogAt : Chain → ℕ → List Obligation := fun c _ => if c = 0 then [⟨0, 1, 0⟩] else []

/-- `mixedSystem 1` is read off those runs, whenever `cv 0 1 = 1`. -/
lemma sc_history {cv : CommitValue} (h1 : cv 0 1 = 1) :
    HistoryFromRuns cv (mixedSystem 1) (scSnap cv) scLogAt := by
  intro c n
  by_cases hc : c = 0
  · subst hc
    have e1 : scSnap cv 0 n = genesis.appended cv 0 1 0 := by simp [scSnap]
    have e2 : scLogAt 0 n = [⟨0, 1, 0⟩] := by simp [scLogAt]
    rw [e1, e2]
    refine ⟨steps_01 h1, ?_⟩
    rw [mixedSystem_tree_zero, appended_tree, h1]
    rfl
  · have e1 : scSnap cv c n = genesis := by simp [scSnap, hc]
    have e2 : scLogAt c n = [] := by simp [scLogAt, hc]
    rw [e1, e2]
    exact ⟨Steps.refl, mixedSystem_tree_other hc n⟩

/-- Chain `0`'s log at every batch, and every other chain's. -/
lemma scLogAt_zero (n : ℕ) : scLogAt 0 n = [⟨0, 1, 0⟩] := by simp [scLogAt]

lemma scLogAt_other {c : Chain} (hc : c ≠ 0) (n : ℕ) : scLogAt c n = [] := by simp [scLogAt, hc]

/-- An obligation other than `⟨0, 1, 0⟩` is in no log of `scLogAt`. -/
lemma not_mem_scLogAt {o : Obligation} (ho : o ≠ ⟨0, 1, 0⟩) (c : Chain) (n : ℕ) :
    o ∉ scLogAt c n := by
  by_cases hc : c = 0
  · subst hc
    rw [scLogAt_zero, List.mem_singleton]
    exact ho
  · rw [scLogAt_other hc]
    exact List.not_mem_nil

theorem SharedCommitmentGateWitness : Properties.SharedCommitmentGateWitness := by
  intro h z0 hl
  have h1 : (0 : UInt256) < 1 := by decide
  have hv : bundleCv 0 1 = (((mixedSystem 1).tree 0 0).leaf 1).value := by
    rw [mixedSystem_tree_zero, insertSetup_leaf_one_value]; rfl
  obtain ⟨hex, hnb⟩ := sc_subsetFlow_executes h z0 hl (cv := bundleCv) (fh := lengthFlowHash)
    (id := 0) (b := 1) (i := 1) (by norm_num) lengthFlowHash_checks_subset hv
  refine ⟨bundleCv, lengthFlowHash, mixedSystem 1, scSnap bundleCv, scLogAt, subsetFlow 0 1, _,
    ⟨0, 1⟩, mixedSystem_wf h1, sc_history rfl, hex, ?_⟩
  intro other hother
  obtain rfl : other = ⟨0, 1⟩ := List.mem_singleton.mp hother
  refine ⟨?_, ?_, by decide, hnb⟩
  · show obligationOf (subsetFlow 0 1) ⟨0, 1⟩ ∈ scLogAt 0 0
    rw [scLogAt_zero]
    exact List.mem_singleton_self _
  · rintro ⟨o, ho, hne, _⟩
    have ho' : o ∈ scLogAt 0 0 := ho
    rw [scLogAt_zero, List.mem_singleton] at ho'
    subst ho'
    exact hne rfl

theorem SharedCommitmentClashLetsUnappendedLegExecute :
    Properties.SharedCommitmentClashLetsUnappendedLegExecute := by
  intro h z0 hl
  have h1 : (0 : UInt256) < 1 := by decide
  have hv : constCv 0 2 = (((mixedSystem 1).tree 0 0).leaf 1).value := by
    rw [mixedSystem_tree_zero, insertSetup_leaf_one_value]; rfl
  have hchk : FlowIdChecked lengthFlowHash (subsetFlow 0 2) := by
    simp [FlowIdChecked, lengthFlowHash, subsetFlow]
  obtain ⟨hex, hnb⟩ := sc_subsetFlow_executes h z0 hl (cv := constCv) (fh := lengthFlowHash)
    (id := 0) (b := 2) (i := 1) (by norm_num) hchk hv
  refine ⟨constCv, lengthFlowHash, mixedSystem 1, scSnap constCv, scLogAt, subsetFlow 0 2, _,
    ⟨0, 2⟩, mixedSystem_wf h1, sc_history rfl, hex,
    fun c n => not_mem_scLogAt (by decide) c n, ?_, by decide, hnb⟩
  refine ⟨⟨0, 1, 0⟩, ?_, by decide, rfl⟩
  show (⟨0, 1, 0⟩ : Obligation) ∈ scLogAt 0 0
  rw [scLogAt_zero]
  exact List.mem_singleton_self _

/-- Commit value `1` on bundle hash `1`, and `0` everywhere else. -/
def zeroOffOneCv : CommitValue := fun _ b => if b = 1 then 1 else 0

theorem SharedCommitmentZeroLetsUnappendedLegExecute :
    Properties.SharedCommitmentZeroLetsUnappendedLegExecute := by
  intro h z0 hl
  have h1 : (0 : UInt256) < 1 := by decide
  have hv : zeroOffOneCv 0 2 = (((mixedSystem 1).tree 0 0).leaf 0).value := by
    rw [mixedSystem_tree_zero]
    decide
  have hchk : FlowIdChecked lengthFlowHash (subsetFlow 0 2) := by
    simp [FlowIdChecked, lengthFlowHash, subsetFlow]
  obtain ⟨hex, hnb⟩ := sc_subsetFlow_executes h z0 hl (cv := zeroOffOneCv) (fh := lengthFlowHash)
    (id := 0) (b := 2) (i := 0) (by norm_num) hchk hv
  refine ⟨zeroOffOneCv, lengthFlowHash, mixedSystem 1, scSnap zeroOffOneCv, scLogAt,
    subsetFlow 0 2, _, ⟨0, 2⟩, mixedSystem_wf h1, sc_history (by decide), hex,
    fun c n => not_mem_scLogAt (by decide) c n, ?_, by decide, hnb⟩
  rintro ⟨o, ho, _, heq⟩
  have ho' : o ∈ scLogAt 0 0 := ho
  rw [scLogAt_zero, List.mem_singleton] at ho'
  subst ho'
  exact absurd heq (by decide)

/-- Every chain's tree is `setup` at every batch, at height 1; batch numbers are timestamps. -/
def scSetupSystem : System := ⟨fun _ _ => setup, fun _ n => n, fun _ _ => 1⟩

lemma scSetupSystem_wf : Wf scSetupSystem := by
  refine ⟨fun _ => Reaches.refl, fun _ _ => Reaches.refl, fun _ => monotone_id, ?_⟩
  intro c n
  show setup.leafCount ≤ 2 ^ 1
  decide

/-- The forged inclusion proof: the honest path for the sentinel's index 0, presenting a leaf
`⟨1, 0, 1⟩` whose toy leaf hash equals the sentinel's. -/
def scForgedProof (h : Hash) (z0 : UInt256) : ImtProof :=
  ⟨⟨1, 0, 1⟩, 0, honestSibs h z0 (leafHashes toyLeafHash setup) 0, 1⟩

theorem SharedCommitmentForgedProofLetsUnappendedLegExecute :
    Properties.SharedCommitmentForgedProofLetsUnappendedLegExecute := by
  intro h z0
  have hv : (⟨1, 0, 1⟩ : Leaf).value ≠ 0 := by decide
  have he : toyLeafHash ⟨1, 0, 1⟩ = toyLeafHash ⟨0, 0, 0⟩ := by decide
  obtain ⟨_, _, hI, _, _⟩ := leaf_collision_forges_inclusion h z0 toyLeafHash ⟨1, 0, 1⟩ hv he
  have hex : ExecutedViaBy h z0 toyLeafHash constCv lengthFlowHash scSetupSystem (subsetFlow 0 1)
      (fun _ => (0, scForgedProof h z0)) ⟨0, 1⟩ := by
    refine ⟨List.mem_singleton_self _, lengthFlowHash_checks_subset, ?_⟩
    intro l hl'
    obtain rfl : l = ⟨0, 1⟩ := List.mem_singleton.mp hl'
    exact ⟨by simp [scSetupSystem, subsetFlow], hI⟩
  refine ⟨toyLeafHash, constCv, lengthFlowHash, scSetupSystem, fun _ _ => genesis, fun _ _ => [],
    subsetFlow 0 1, fun _ => (0, scForgedProof h z0), ⟨0, 1⟩, scSetupSystem_wf,
    fun _ _ => ⟨Steps.refl, rfl⟩, hex, fun _ _ => List.not_mem_nil, ?_, by decide, ?_⟩
  · rintro ⟨o, ho, _⟩
    exact List.not_mem_nil ho
  · exact TreeRootBreak.leafCollision (show (0 : ℕ) < 1 by decide)
      (show (⟨0, 0, 0⟩ : Leaf) ≠ ⟨1, 0, 1⟩ by decide) he.symm

/-- `mixedSystem 1` is cut from the system run `sys_r1` of topic `OncePerLeg` (chain `0` appends
`⟨0, 1, 0⟩` under the constant commit value `1`), at every batch. -/
lemma sc_mixed_history_from_system (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    HistoryFromSystemRun h z0 hl constCv lengthFlowHash (mixedSystem 1) (mixedSystem 1)
      (fun _ => sysY1) (fun _ => [⟨0, 1, 0⟩]) (fun _ => []) := by
  intro n
  refine ⟨sys_r1 h z0 hl, fun c => ?_⟩
  show (mixedSystem 1).tree c n = (sysY1 c).tree
  by_cases hc : c = 0
  · subst hc
    rw [mixedSystem_tree_zero, show sysY1 0 = genesis.appended constCv 0 1 0 from update_self _ _ _]
    rfl
  · rw [mixedSystem_tree_other hc, show sysY1 c = genesis from update_other _ _ hc]
    rfl

/-! ## The timeout check -/

/-- An absence proof accepted against the tree of a run excludes every logged commit value, or
carries a located break. -/
lemma absence_on_run_excludes_logged {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {c : Chain} {s : ChainState} {l : List Obligation} {height : ℕ}
    {v : UInt256} {p : ImtProof} (hrun : Steps cv c genesis s l)
    (hacc : AbsenceAccepted h z0 hl s.tree height v p) :
    (∀ o ∈ l, commitOf cv o ≠ v) ∨ ImtProofBreak h z0 hl s.tree height p := by
  have hI := inv_of_steps hrun
  have hN : NonInclusionAccepted h hl (root h z0 hl s.tree height) v p.leaf p.index p.sibs
      p.pathLen := hacc
  rcases verified_absence_excludes_delivered_or_break hI.valid hN with hnk | hb
  · left
    intro o ho heq
    exact hnk (heq ▸ hI.key_of_mem ho)
  · exact Or.inr hb

theorem timeout_absence_excludes_shared_commitment_or_break {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {S : System} {snap : Chain → ℕ → ChainState}
    {logAt : Chain → ℕ → List Obligation} (hH : HistoryFromRuns cv S snap logAt) {F : Flow}
    {m : FlowLeg} {N : ℕ} {p : ImtProof} (href : LegRefundableBy h z0 hl cv S F m N p) :
    (∀ o ∈ absenceLog logAt S F.deadline m.chain N, commitOf cv o ≠ legValue cv F m)
      ∨ AbsenceBreak h z0 hl S F.deadline m.chain N p := by
  rcases href with ⟨hlt, hacc⟩ | ⟨hlast, hacc⟩
  · -- BEGIN branch: the root is the end of the previous batch, or genesis
    cases N with
    | zero =>
      left
      intro o ho
      simp [absenceLog, hlt] at ho
    | succ k =>
      obtain ⟨hrun, htree⟩ := hH m.chain k
      have hacc' : AbsenceAccepted h z0 hl (snap m.chain k).tree (S.height m.chain k)
          (legValue cv F m) p := by
        rw [← htree]
        exact hacc
      have hlog : absenceLog logAt S F.deadline m.chain (k + 1) = logAt m.chain k := by
        simp [absenceLog, hlt]
      rcases absence_on_run_excludes_logged hrun hacc' with hno | hb
      · left
        rw [hlog]
        exact hno
      · right
        left
        refine ⟨hlt, ?_⟩
        show ImtProofBreak h z0 hl (S.tree m.chain k) (S.height m.chain k) p
        rw [htree]
        exact hb
  · -- END branch: the root is the end of this on-time batch
    have hle : S.time m.chain N ≤ F.deadline := hlast.1
    obtain ⟨hrun, htree⟩ := hH m.chain N
    have hacc' : AbsenceAccepted h z0 hl (snap m.chain N).tree (S.height m.chain N)
        (legValue cv F m) p := by
      rw [← htree]
      exact hacc
    have hlog : absenceLog logAt S F.deadline m.chain N = logAt m.chain N := by
      cases N with
      | zero => simp [absenceLog, not_lt.mpr hle]
      | succ k => simp [absenceLog, not_lt.mpr hle]
    rcases absence_on_run_excludes_logged hrun hacc' with hno | hb
    · left
      rw [hlog]
      exact hno
    · right
      right
      refine ⟨hle, ?_⟩
      show ImtProofBreak h z0 hl (S.tree m.chain N) (S.height m.chain N) p
      rw [htree]
      exact hb

theorem TimeoutAbsenceExcludesSharedCommitmentOrBreak :
    Properties.TimeoutAbsenceExcludesSharedCommitmentOrBreak :=
  fun _ _ _ _ _ _ _ hH _ _ _ _ href => timeout_absence_excludes_shared_commitment_or_break hH href

theorem TimeoutAbsenceWitness : Properties.TimeoutAbsenceWitness := by
  intro h z0 hl
  have h1 : (0 : UInt256) < 1 := by decide
  have hS := mixedSystem_wf h1
  have hcount : ((mixedSystem 1).tree 0 0).leafCount = 2 := by
    rw [mixedSystem_tree_zero]; rfl
  have hinc := inclusion_complete (h := h) (z0 := z0) (hl := hl)
    (T := (mixedSystem 1).tree 0 0) (height := (mixedSystem 1).height 0 0) (hS.capacity 0 0)
    (i := 1) (by rw [hcount]; norm_num)
  have hleaf : ((mixedSystem 1).tree 0 0).leaf 1 = ⟨1, 0, 0⟩ := by
    rw [mixedSystem_tree_zero]
    decide
  -- the honest proof of leaf 1 (value 1, next 0) is an absence proof for the value 2
  have habs : AbsenceAccepted h z0 hl (beginTree (mixedSystem 1) 0 1)
      (beginHeight (mixedSystem 1) 0 1) (legValue bundleCv (subsetFlow 0 2) ⟨0, 2⟩)
      (honestProof h z0 hl (mixedSystem 1) 0 0 1) := by
    refine ⟨by decide, ?_, ?_, hinc.path⟩
    · show (((mixedSystem 1).tree 0 0).leaf 1).value < (2 : UInt256)
      rw [hleaf]
      decide
    · show (((mixedSystem 1).tree 0 0).leaf 1).nextValue = 0
        ∨ (2 : UInt256) < (((mixedSystem 1).tree 0 0).leaf 1).nextValue
      rw [hleaf]
      exact Or.inl rfl
  have hnb := honestProof_no_break h z0 hl (mixedSystem 1) 0 0 1 (by rw [hcount]; norm_num)
  have hlog : absenceLog scLogAt (mixedSystem 1) (subsetFlow 0 2).deadline
      (⟨0, 2⟩ : FlowLeg).chain 1 = [⟨0, 1, 0⟩] := by
    simp [absenceLog, scLogAt, subsetFlow]
  refine ⟨bundleCv, mixedSystem 1, scSnap bundleCv, scLogAt, subsetFlow 0 2, ⟨0, 2⟩, 1,
    honestProof h z0 hl (mixedSystem 1) 0 0 1, hS, sc_history rfl,
    Or.inl ⟨by simp [subsetFlow], habs⟩, by rw [hlog]; exact List.cons_ne_nil _ _, ?_, ?_⟩
  · intro o ho
    rw [hlog, List.mem_singleton] at ho
    subst ho
    decide
  · rintro (⟨_, hb⟩ | ⟨hle, _⟩)
    · exact hnb hb
    · simp [subsetFlow] at hle

theorem SharedCommitmentClashBlocksTimeout : Properties.SharedCommitmentClashBlocksTimeout := by
  intro h z0 hl
  have h1 : (0 : UInt256) < 1 := by decide
  have hv : constCv 0 2 = (((mixedSystem 1).tree 0 0).leaf 1).value := by
    rw [mixedSystem_tree_zero, insertSetup_leaf_one_value]; rfl
  have hchk : FlowIdChecked lengthFlowHash (subsetFlow 0 2) := by
    simp [FlowIdChecked, lengthFlowHash, subsetFlow]
  obtain ⟨hex, _⟩ := sc_subsetFlow_executes h z0 hl (cv := constCv) (fh := lengthFlowHash)
    (id := 0) (b := 2) (i := 1) (by norm_num) hchk hv
  have hH := sc_history (cv := constCv) rfl
  refine ⟨constCv, lengthFlowHash, mixedSystem 1, scSnap constCv, scLogAt, subsetFlow 0 2, ⟨0, 2⟩,
    _, mixedSystem_wf h1, hH, List.mem_singleton_self _,
    fun c n => not_mem_scLogAt (by decide) c n, hex, ?_⟩
  intro N p href
  rcases timeout_absence_excludes_shared_commitment_or_break hH href with hno | hb
  · -- the appended `⟨0, 1, 0⟩` sits behind every root the check can use
    have hmem : (⟨0, 1, 0⟩ : Obligation)
        ∈ absenceLog scLogAt (mixedSystem 1) (subsetFlow 0 2).deadline (⟨0, 2⟩ : FlowLeg).chain N := by
      cases N with
      | zero => simp [absenceLog, scLogAt, subsetFlow]
      | succ k => simp [absenceLog, scLogAt, subsetFlow]
    exact absurd rfl (hno _ hmem)
  · exact hb

theorem SystemHistoryWitness : Properties.SystemHistoryWitness := by
  intro h z0 hl
  have h1 : (0 : UInt256) < 1 := by decide
  obtain ⟨hex, hnb⟩ := subsetFlow_executes h z0 hl lengthFlowHash lengthFlowHash_checks_subset
  refine ⟨constCv, lengthFlowHash, mixedSystem 1, fun _ => sysY1, fun _ => [⟨0, 1, 0⟩],
    fun _ => [], subsetFlow 0 1, _, ⟨0, 1⟩, mixedSystem_wf h1, sc_mixed_history_from_system h z0 hl,
    hex, ?_⟩
  intro other hother
  obtain rfl : other = ⟨0, 1⟩ := List.mem_singleton.mp hother
  refine ⟨List.mem_singleton_self _, ?_, by decide, hnb⟩
  rintro ⟨o, ho, _, hne, _⟩
  rw [List.mem_singleton] at ho
  subst ho
  exact hne rfl

end Contracts.SharedCommitment
