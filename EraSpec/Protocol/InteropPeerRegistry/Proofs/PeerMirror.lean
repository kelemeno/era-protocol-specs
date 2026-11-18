import EraSpec.Protocol.InteropPeerRegistry.Properties.PeerMirror

/-!
# Proofs: the peer whitelist's mirror, and the `baseTokenAssetId` entries on each chain

One run invariant, `Inv`, carries everything for `deployed`. Its mirror half says that the
sender's flag is the value of the last entry ever queued for the pair (`allowedSeq`) and the
chain's flag the value of the last one that succeeded (`peerDone`), and that every re-submission
was queued behind an entry that allowed the pair (`resub`). Its migration half pins down, per
chain `p`, the one migration message in flight (`mig`): the arrival is queued exactly once
(`mintCount`), the layer records `p` exactly while it settles there (`hubSettled`), L1's
`settlementLayer[p]` names the layer of the message (`l1Layer`), and no deregistration of `p` on
the layer is queued behind the arrival or while `p` settles there or returns
(`mintingQueue`, `settledEntry`, `returningEntry`). Its value half says every queued value and
every entry is `0` or L1's (`queueVal`, `hubVal`, `retVal`). `inv_step` proves one step for
`deployed`: the FIFO order is used where an executed entry is the head of the queue (`allowedSeq`,
`mintingQueue`), and the settlement clause of `deregisterInteropPairs` where a deregistration is
queued for a chain whose migration message names that layer (`inv_deregisterInteropPairs`).

`DeregistrationRepeatClearsPeerFlag`, `DisallowedPeerFlagFrozenWhileOnLayer` and the three
`not_step_*` lemmas need no invariant: they read the guards and writes of `Step` directly.

Witness runs, the countermodels included, are computed by `stepFn`, an executable version of
`Step` proved sound (`step_of_stepFn`), and checked by `decide`.
-/

namespace Contracts.InteropPeerRegistry

/-! ## Lists of entries -/

theorem lastPeerWrite_snoc (p : ChainId) (l : List Msg) (m : Msg) :
    lastPeerWrite p (l ++ [m]) = (m.peerWrite p).or (lastPeerWrite p l) := by
  simp [lastPeerWrite, List.foldl_append]

theorem foldl_peerWrite_of_none (p : ChainId) (l : List Msg) (acc : Option Bool)
    (h : ∀ m ∈ l, m.peerWrite p = none) :
    l.foldl (fun acc m => (m.peerWrite p).or acc) acc = acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    rw [h x List.mem_cons_self, Option.none_or]
    exact ih acc (fun m hm => h m (List.mem_cons_of_mem _ hm))

theorem lastPeerWrite_append_of_none (p : ChainId) (l l' : List Msg)
    (h : ∀ m ∈ l', m.peerWrite p = none) :
    lastPeerWrite p (l ++ l') = lastPeerWrite p l := by
  simp only [lastPeerWrite, List.foldl_append]
  exact foldl_peerWrite_of_none p l' _ h

theorem foldl_peerWrite_deregs (p : ChainId) (ps : List ChainId) (acc : Option Bool) :
    (ps.map Msg.dereg).foldl (fun acc m => (m.peerWrite p).or acc) acc =
      if p ∈ ps then some false else acc := by
  induction ps generalizing acc with
  | nil => simp
  | cons q ps ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ih]
    by_cases hq : q = p
    · subst hq; simp [Msg.peerWrite]
    · simp [Msg.peerWrite, hq, Ne.symm hq]

theorem lastPeerWrite_append_deregs (p : ChainId) (l : List Msg) (ps : List ChainId) :
    lastPeerWrite p (l ++ ps.map Msg.dereg) = if p ∈ ps then some false else lastPeerWrite p l := by
  simp only [lastPeerWrite, List.foldl_append]
  exact foldl_peerWrite_deregs p ps _

/-- The value of the last successful executed entry writing `isPeerAllowed[p]`. -/
def lastOkPeerWrite (p : ChainId) (d : List (Msg × Bool)) : Option Bool :=
  d.foldl (fun acc e => if e.2 then (e.1.peerWrite p).or acc else acc) none

theorem lastOkPeerWrite_snoc (p : ChainId) (d : List (Msg × Bool)) (e : Msg × Bool) :
    lastOkPeerWrite p (d ++ [e]) =
      if e.2 then (e.1.peerWrite p).or (lastOkPeerWrite p d) else lastOkPeerWrite p d := by
  simp [lastOkPeerWrite, List.foldl_append]

theorem lastPeerEntryOk_snoc (p : ChainId) (d : List (Msg × Bool)) (e : Msg × Bool) :
    lastPeerEntryOk p (d ++ [e]) = if (e.1.peerWrite p).isSome then e.2 else lastPeerEntryOk p d := by
  simp [lastPeerEntryOk, List.foldl_append]

theorem peerWrite_eq_some {p : ChainId} {m : Msg} {v : Bool} (h : m.peerWrite p = some v) :
    (∃ a s, m = .allow p a s ∧ v = true) ∨ (m = .dereg p ∧ v = false) := by
  cases m with
  | allow q a s =>
    simp only [Msg.peerWrite] at h
    split_ifs at h with hq
    · subst hq; cases h; exact Or.inl ⟨a, s, rfl, rfl⟩
  | dereg q =>
    simp only [Msg.peerWrite] at h
    split_ifs at h with hq
    · subst hq; cases h; exact Or.inr ⟨rfl, rfl⟩
  | legacy q a => simp [Msg.peerWrite] at h
  | mint q a => simp [Msg.peerWrite] at h
  | other => simp [Msg.peerWrite] at h

/-- If the last executed entry for `p` succeeded, the last successful value is the last value. -/
theorem lastOkPeerWrite_eq_of_lastOk (p : ChainId) (d : List (Msg × Bool))
    (h : lastPeerEntryOk p d = true) :
    lastOkPeerWrite p d = lastPeerWrite p (d.map Prod.fst) := by
  induction d using List.reverseRecOn with
  | nil => rfl
  | append_singleton d e ih =>
    rw [lastPeerEntryOk_snoc] at h
    rw [lastOkPeerWrite_snoc, List.map_append, List.map_singleton, lastPeerWrite_snoc]
    cases hw : e.1.peerWrite p with
    | none =>
      simp only [hw, Option.isSome_none, Bool.false_eq_true, ite_false] at h
      simp [ih h]
    | some v =>
      simp only [hw, Option.isSome_some, ite_true] at h
      simp [h]

/-! ## Re-submissions are queued behind an allowing entry -/

/-- Every re-submission entry of `l` follows a prefix whose last entry for its pair allows it. -/
def ResubBacked (l : List Msg) : Prop :=
  ∀ (l₁ l₂ : List Msg) (q : ChainId) (a : AssetId),
    l = l₁ ++ Msg.allow q a false :: l₂ → lastPeerWrite q l₁ = some true

theorem resubBacked_nil : ResubBacked [] := by
  intro l₁ l₂ q a h
  cases l₁ <;> simp at h

theorem resubBacked_prefix {l l' : List Msg} (h : ResubBacked (l ++ l')) : ResubBacked l := by
  intro l₁ l₂ q a hl
  exact h l₁ (l₂ ++ l') q a (by rw [hl]; simp)

theorem resubBacked_append {l ms : List Msg} (h : ResubBacked l)
    (hms : ∀ m ∈ ms, ∀ q a, m ≠ Msg.allow q a false) : ResubBacked (l ++ ms) := by
  intro l₁ l₂ q a hl
  rcases List.append_eq_append_iff.mp hl with ⟨as, h1, h2⟩ | ⟨bs, h1, h2⟩
  · -- the entry lies in `ms`
    exfalso
    cases as with
    | nil =>
      simp only [List.nil_append] at h2
      exact hms _ (by rw [h2]; exact List.mem_cons_self) q a rfl
    | cons x as =>
      have hmem : Msg.allow q a false ∈ ms := by
        rw [h2]; simp
      exact hms _ hmem q a rfl
  · -- the entry lies in `l`
    cases bs with
    | nil =>
      simp only [List.nil_append] at h2
      exfalso
      exact hms _ (by rw [← h2]; exact List.mem_cons_self) q a rfl
    | cons x bs =>
      simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact h l₁ bs q a (by rw [h1])

theorem resubBacked_snoc_resub {l : List Msg} {q : ChainId} {a : AssetId} (h : ResubBacked l)
    (hq : lastPeerWrite q l = some true) : ResubBacked (l ++ [Msg.allow q a false]) := by
  intro l₁ l₂ q' a' hl
  rcases List.eq_nil_or_concat l₂ with rfl | ⟨l₂', b, rfl⟩
  · have : l = l₁ ∧ Msg.allow q a false = Msg.allow q' a' false := by
      simpa using hl
    obtain ⟨rfl, he⟩ := this
    cases he
    exact hq
  · have hl' : l ++ [Msg.allow q a false] = (l₁ ++ Msg.allow q' a' false :: l₂') ++ [b] := by
      rw [hl]; simp
    have := List.append_inj_left' hl' rfl
    exact h l₁ l₂' q' a' this

/-- With every failed entry for `p` a re-submission, the last successful value is the last value. -/
theorem lastOkPeerWrite_eq_of_service (p : ChainId) (d : List (Msg × Bool))
    (hr : ResubBacked (d.map Prod.fst))
    (hs : ∀ e ∈ d, e.1.isService = true → (e.1.peerWrite p).isSome = true → e.2 = true) :
    lastOkPeerWrite p d = lastPeerWrite p (d.map Prod.fst) := by
  induction d using List.reverseRecOn with
  | nil => rfl
  | append_singleton d e ih =>
    rw [List.map_append, List.map_singleton] at hr
    have hd : lastOkPeerWrite p d = lastPeerWrite p (d.map Prod.fst) :=
      ih (resubBacked_prefix hr) (fun x hx => hs x (List.mem_append_left _ hx))
    rw [lastOkPeerWrite_snoc, List.map_append, List.map_singleton, lastPeerWrite_snoc]
    cases hw : e.1.peerWrite p with
    | none => simp [hd]
    | some v =>
      cases he : e.2 with
      | true => simp
      | false =>
        simp only [Bool.false_eq_true, ite_false, Option.some_or]
        rcases peerWrite_eq_some hw with ⟨a, s, hm, rfl⟩ | ⟨hm, rfl⟩
        · cases s with
          | true =>
            have := hs e (List.mem_append_right _ List.mem_cons_self) (by rw [hm]; rfl)
              (by rw [hw]; rfl)
            rw [he] at this; cases this
          | false =>
            have hback := hr (d.map Prod.fst) [] p a (by rw [hm])
            rw [hd, hback]
        · have := hs e (List.mem_append_right _ List.mem_cons_self) (by rw [hm]; rfl)
            (by rw [hw]; rfl)
          rw [he] at this; cases this

/-! ## The invariant -/

/-- `m` is an arrival of `p`. -/
def isMintOf (p : ChainId) : Msg → Bool
  | .mint q _ => decide (q = p)
  | _ => false

/-- A queued entry carries L1's current, nonzero value for its chain. -/
def Carries (L : L1State) : Msg → Prop
  | .allow p a _ => a = L.bt p ∧ a ≠ 0
  | .legacy p a => a = L.bt p ∧ a ≠ 0
  | .mint p a => a = L.bt p ∧ a ≠ 0
  | .dereg _ => True
  | .other => True

/-- Every entry chain `c` was ever sent, oldest first: the executed ones, then the pending ones. -/
def State.sent (S : State) (c : ChainId) : List Msg := (S.done c).map Prod.fst ++ S.queue c

/-- The run invariant of `deployed`. -/
structure Inv (P : Params) (S : State) : Prop where
  regNe : ∀ p, S.l1.registered p = true → p ≠ 0 ∧ p ≠ P.l1
  regBt : ∀ p, S.l1.registered p = true → S.l1.bt p ≠ 0
  unregBt : ∀ p, S.l1.registered p = false → S.l1.bt p = 0
  unregMig : ∀ p, S.l1.registered p = false → S.mig p = .home
  unregQueue : ∀ c, S.l1.registered c = false → S.queue c = []
  unregHub : ∀ c, S.l1.registered c = false → ∀ q, (S.hub c).sl q = 0
  mintCount : ∀ c p, (S.queue c).countP (isMintOf p) = if S.mig p = .minting c then 1 else 0
  hubSettled : ∀ c p, S.l1.registered c = true → ((S.hub c).sl p = c ↔ S.mig p = .settled c)
  l1Layer : ∀ p, S.l1.registered p = true → S.l1.sl p = (S.mig p).layer.getD P.l1
  layerReg : ∀ p c, (S.mig p).layer = some c →
    S.l1.registered c = true ∧ c ≠ p ∧ S.l1.registered p = true
  queueVal : ∀ c, ∀ m ∈ S.queue c, Carries S.l1 m
  hubVal : ∀ c p, (S.hub c).bta p = 0 ∨ (S.hub c).bta p = S.l1.bt p
  retVal : ∀ p c a, S.mig p = .returning c a → a = S.l1.bt p
  settledEntry : ∀ p c, S.mig p = .settled c →
    (S.hub c).bta p = S.l1.bt p ∧ Msg.dereg p ∉ S.queue c
  returningEntry : ∀ p c a, S.mig p = .returning c a →
    (S.hub c).bta p = S.l1.bt p ∧ Msg.dereg p ∉ S.queue c
  mintingQueue : ∀ p c, S.mig p = .minting c →
    ∃ pre a post, S.queue c = pre ++ Msg.mint p a :: post ∧ Msg.dereg p ∉ post
  allowedSeq : ∀ c p, S.l1.allowed c p = (lastPeerWrite p (S.sent c)).getD false
  peerDone : ∀ c p, (S.hub c).peer p = (lastOkPeerWrite p (S.done c)).getD false
  resub : ∀ c, ResubBacked (S.sent c)
  allowedOk : ∀ c p, S.l1.allowed c p = true →
    S.l1.registered c = true ∧ S.l1.bt p ≠ 0 ∧ S.l1.hasBatch p = true ∧ p ≠ c ∧ p ≠ P.l1
  properAllow : ∀ c, ∀ m ∈ S.sent c, ∀ p a s, m = Msg.allow p a s → p ≠ c ∧ p ≠ P.l1

theorem inv_init (P : Params) : Inv P init where
  regNe := by intro p h; simp [init, L1State.fresh] at h
  regBt := by intro p h; simp [init, L1State.fresh] at h
  unregBt := by intro p _; rfl
  unregMig := by intro p _; rfl
  unregQueue := by intro c _; rfl
  unregHub := by intro c _ q; rfl
  mintCount := by intro c p; simp [init]
  hubSettled := by intro c p h; simp [init, L1State.fresh] at h
  l1Layer := by intro p h; simp [init, L1State.fresh] at h
  layerReg := by intro p c h; simp [init, Mig.layer] at h
  queueVal := by intro c m hm; simp [init] at hm
  hubVal := by intro c p; exact Or.inl rfl
  retVal := by intro p c a h; simp [init] at h
  settledEntry := by intro p c h; simp [init] at h
  returningEntry := by intro p c a h; simp [init] at h
  mintingQueue := by intro p c h; simp [init] at h
  allowedSeq := by intro c p; rfl
  peerDone := by intro c p; rfl
  resub := by intro c; exact resubBacked_nil
  allowedOk := by intro c p h; simp [init, L1State.fresh] at h
  properAllow := by intro c m hm; simp [init, State.sent] at hm

/-! ### Helpers -/

/-- `L'` keeps every nonzero `baseTokenAssetId` of `L`. -/
def BtStable (L L' : L1State) : Prop := ∀ q, L.bt q ≠ 0 → L'.bt q = L.bt q

theorem carries_of_btStable {L L' : L1State} (h : BtStable L L') {m : Msg} (hm : Carries L m) :
    Carries L' m := by
  cases m with
  | allow q a s => exact ⟨by rw [h q (hm.1 ▸ hm.2)]; exact hm.1, hm.2⟩
  | legacy q a => exact ⟨by rw [h q (hm.1 ▸ hm.2)]; exact hm.1, hm.2⟩
  | mint q a => exact ⟨by rw [h q (hm.1 ▸ hm.2)]; exact hm.1, hm.2⟩
  | dereg q => trivial
  | other => trivial

theorem zeroOr_of_btStable {L L' : L1State} (h : BtStable L L') {x : AssetId} {q : ChainId}
    (hx : x = 0 ∨ x = L.bt q) : x = 0 ∨ x = L'.bt q := by
  rcases hx with hx | hx
  · exact Or.inl hx
  · by_cases hq : L.bt q = 0
    · exact Or.inl (hx.trans hq)
    · exact Or.inr (by rw [h q hq]; exact hx)

theorem countP_isMintOf_deregs (p : ChainId) (ps : List ChainId) :
    (ps.map Msg.dereg).countP (isMintOf p) = 0 := by
  induction ps with
  | nil => rfl
  | cons q ps ih => simp [ih, isMintOf]

theorem shift_decomp {x y : Msg} {l pre post : List Msg} (h : x :: l = pre ++ y :: post)
    (hxy : x ≠ y) : ∃ pre', l = pre' ++ y :: post := by
  cases pre with
  | nil => simp only [List.nil_append, List.cons.injEq] at h; exact absurd h.1 hxy
  | cons z pre' => simp only [List.cons_append, List.cons.injEq] at h; exact ⟨pre', h.2⟩

theorem decomp_head_of_count {p : ChainId} {a a' : AssetId} {l pre post : List Msg}
    (h : Msg.mint p a :: l = pre ++ Msg.mint p a' :: post)
    (hc : (Msg.mint p a :: l).countP (isMintOf p) = 1) : l = post := by
  cases pre with
  | nil => simp only [List.nil_append, List.cons.injEq] at h; exact h.2
  | cons z pre' =>
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [List.countP_append, isMintOf] at hc

theorem layer_eq_none_iff {m : Mig} : m.layer = none ↔ m = .home := by
  cases m <;> simp [Mig.layer]

/-- With `l1Layer` and `layerReg`, a registered chain whose L1 settlement layer is L1 is at home. -/
theorem home_of_sl {P : Params} {S : State} (hI : Inv P S) {p : ChainId}
    (hr : S.l1.registered p = true) (hsl : S.l1.sl p = P.l1) : S.mig p = .home := by
  have h := hI.l1Layer p hr
  cases hm : (S.mig p).layer with
  | none => exact layer_eq_none_iff.mp hm
  | some c =>
    rw [hm] at h
    simp only [Option.getD_some] at h
    obtain ⟨hc, -, -⟩ := hI.layerReg p c hm
    exact absurd (h.symm.trans hsl) (hI.regNe c hc).2

/-- A migration status with a layer `c` means L1 records `p` on `c`. -/
theorem sl_of_layer {P : Params} {S : State} (hI : Inv P S) {p c : ChainId}
    (h : (S.mig p).layer = some c) : S.l1.sl p = c := by
  obtain ⟨-, -, hp⟩ := hI.layerReg p c h
  rw [hI.l1Layer p hp, h]; rfl

theorem registered_of_queue {P : Params} {S : State} (hI : Inv P S) {c : ChainId} {m : Msg}
    {l : List Msg} (h : S.queue c = m :: l) : S.l1.registered c = true := by
  cases hr : S.l1.registered c
  · rw [hI.unregQueue c hr] at h; cases h
  · rfl

/-! ### One step, per entry point -/

theorem inv_createChain {P : Params} {S S' : State} {p : ChainId} {a : AssetId}
    (hI : Inv P S) (hs : Step deployed P S (.createChain p a) S') : Inv P S' := by
  cases hs with
  | createChain h1 h2 h3 h4 =>
  have hbt : BtStable S.l1 { S.l1 with
      registered := Function.update S.l1.registered p true
      bt := Function.update S.l1.bt p a
      sl := Function.update S.l1.sl p P.l1 } := by
    intro q hq
    show Function.update S.l1.bt p a q = S.l1.bt q
    rw [Function.update_of_ne]
    rintro rfl
    exact hq (hI.unregBt _ h1)
  have hbt' : ∀ q, S.l1.bt q ≠ 0 → Function.update S.l1.bt p a q = S.l1.bt q := hbt
  have regMono : ∀ q, S.l1.registered q = true →
      Function.update S.l1.registered p true q = true := by
    intro q hq; rw [Function.update_apply]; split_ifs <;> simp [hq]
  have unreg : ∀ q, Function.update S.l1.registered p true q = false →
      q ≠ p ∧ S.l1.registered q = false := by
    intro q hq
    by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [Function.update_of_ne hqp] at hq; exact ⟨hqp, hq⟩
  refine ⟨?regNe, ?regBt, ?unregBt, ?unregMig, ?unregQueue, ?unregHub, hI.mintCount, ?hubSettled,
    ?l1Layer, ?layerReg, ?queueVal, ?hubVal, ?retVal, ?settledEntry, ?returningEntry,
    hI.mintingQueue, hI.allowedSeq, hI.peerDone, hI.resub, ?allowedOk, hI.properAllow⟩
  all_goals (try dsimp only)
  case regNe =>
    intro q hq
    simp only [Function.update_apply] at hq
    split_ifs at hq with hqp
    · subst hqp; exact ⟨h2, h3⟩
    · exact hI.regNe q hq
  case regBt =>
    intro q hq
    simp only [Function.update_apply] at hq ⊢
    split_ifs at hq ⊢ with hqp
    · exact h4
    · exact hI.regBt q hq
  case unregBt =>
    intro q hq
    obtain ⟨hqp, hq⟩ := unreg q hq
    simp only [Function.update_of_ne hqp]
    exact hI.unregBt q hq
  case unregMig => intro q hq; exact hI.unregMig q (unreg q hq).2
  case unregQueue => intro q hq; exact hI.unregQueue q (unreg q hq).2
  case unregHub => intro q hq; exact hI.unregHub q (unreg q hq).2
  case hubSettled =>
    intro c q hc
    by_cases hcp : c = p
    · subst hcp
      simp only [hI.unregHub c h1 q]
      constructor
      · intro h; exact absurd h.symm h2
      · intro h
        have := hI.layerReg q c (by rw [h]; rfl)
        rw [h1] at this; simp at this
    · rw [Function.update_of_ne hcp] at hc
      exact hI.hubSettled c q hc
  case l1Layer =>
    intro q hq
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, hI.unregMig q h1, Mig.layer, Option.getD_none]
    · rw [Function.update_of_ne hqp] at hq
      simp only [Function.update_of_ne hqp]
      exact hI.l1Layer q hq
  case layerReg =>
    intro q c hq
    obtain ⟨h5, h6, h7⟩ := hI.layerReg q c hq
    exact ⟨regMono c h5, h6, regMono q h7⟩
  case queueVal => intro c m hm; exact carries_of_btStable hbt (hI.queueVal c m hm)
  case hubVal => intro c q; exact zeroOr_of_btStable hbt (hI.hubVal c q)
  case retVal =>
    intro q c a' hq
    obtain ⟨-, -, hr⟩ := hI.layerReg q c (by rw [hq]; rfl)
    rw [hbt' q (hI.regBt q hr)]
    exact hI.retVal q c a' hq
  case settledEntry =>
    intro q c hq
    obtain ⟨-, -, hr⟩ := hI.layerReg q c (by rw [hq]; rfl)
    rw [hbt' q (hI.regBt q hr)]
    exact hI.settledEntry q c hq
  case returningEntry =>
    intro q c a' hq
    obtain ⟨-, -, hr⟩ := hI.layerReg q c (by rw [hq]; rfl)
    rw [hbt' q (hI.regBt q hr)]
    exact hI.returningEntry q c a' hq
  case allowedOk =>
    intro c q hq
    obtain ⟨h5, h6, h7, h8, h9⟩ := hI.allowedOk c q hq
    exact ⟨regMono c h5, by rw [hbt' q h6]; exact h6, h7, h8, h9⟩

theorem inv_enableInterop {P : Params} {S S' : State} {c : ChainId}
    (hI : Inv P S) (hs : Step deployed P S (.enableInterop c) S') : Inv P S' := by
  cases hs with
  | enableInterop _ =>
  exact ⟨hI.regNe, hI.regBt, hI.unregBt, hI.unregMig, hI.unregQueue, hI.unregHub, hI.mintCount,
    hI.hubSettled, hI.l1Layer, hI.layerReg, hI.queueVal, hI.hubVal, hI.retVal, hI.settledEntry,
    hI.returningEntry, hI.mintingQueue, hI.allowedSeq, hI.peerDone, hI.resub, hI.allowedOk,
    hI.properAllow⟩

theorem inv_pushBatch {P : Params} {S S' : State} {c : ChainId}
    (hI : Inv P S) (hs : Step deployed P S (.pushBatch c) S') : Inv P S' := by
  cases hs with
  | pushBatch _ =>
  refine ⟨hI.regNe, hI.regBt, hI.unregBt, hI.unregMig, hI.unregQueue, hI.unregHub, hI.mintCount,
    hI.hubSettled, hI.l1Layer, hI.layerReg, hI.queueVal, hI.hubVal, hI.retVal, hI.settledEntry,
    hI.returningEntry, hI.mintingQueue, hI.allowedSeq, hI.peerDone, hI.resub, ?_,
    hI.properAllow⟩
  intro c' q hq
  obtain ⟨h1, h2, h3, h4, h5⟩ := hI.allowedOk c' q hq
  refine ⟨h1, h2, ?_, h4, h5⟩
  show Function.update S.l1.hasBatch c true q = true
  rw [Function.update_apply]; split_ifs <;> simp [h3]

theorem getD_false_eq_true {o : Option Bool} (h : o.getD false = true) : o = some true := by
  cases o with
  | none => simp at h
  | some b => simp at h; rw [h]

/-- The steps that only append entries to one chain's queue, and possibly rewrite the sender's
map. -/
theorem inv_enqueue {P : Params} {S : State} (hI : Inv P S) {c : ChainId} {ms : List Msg}
    {A : ChainId → ChainId → Bool} (hc : S.l1.registered c = true)
    (hval : ∀ m ∈ ms, Carries S.l1 m) (hmint : ∀ q, ms.countP (isMintOf q) = 0)
    (hdereg : ∀ q, Msg.dereg q ∈ ms → (S.mig q).layer ≠ some c)
    (hA : ∀ c' q, A c' q =
      (lastPeerWrite q (if c' = c then S.sent c ++ ms else S.sent c')).getD false)
    (hres : ResubBacked (S.sent c ++ ms))
    (hok : ∀ c' q, A c' q = true →
      S.l1.registered c' = true ∧ S.l1.bt q ≠ 0 ∧ S.l1.hasBatch q = true ∧ q ≠ c' ∧ q ≠ P.l1)
    (hprop : ∀ m ∈ ms, ∀ q a s, m = Msg.allow q a s → q ≠ c ∧ q ≠ P.l1) :
    Inv P { S with l1 := { S.l1 with allowed := A },
                   queue := Function.update S.queue c (S.queue c ++ ms) } := by
  have hsent : ∀ c', (S.done c').map Prod.fst ++ Function.update S.queue c (S.queue c ++ ms) c' =
      if c' = c then S.sent c ++ ms else S.sent c' := by
    intro c'
    rw [Function.update_apply]
    split_ifs with h
    · subst h; simp [State.sent]
    · rfl
  have hmem : ∀ c' m, m ∈ Function.update S.queue c (S.queue c ++ ms) c' →
      m ∈ S.queue c' ∨ (c' = c ∧ m ∈ ms) := by
    intro c' m hm
    rw [Function.update_apply] at hm
    split_ifs at hm with h
    · subst h
      rcases List.mem_append.mp hm with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨rfl, h1⟩
    · exact Or.inl hm
  have hnotin : ∀ q c', (S.mig q).layer = some c' → Msg.dereg q ∉ S.queue c' →
      Msg.dereg q ∉ Function.update S.queue c (S.queue c ++ ms) c' := by
    intro q c' hl hq hmem'
    rcases hmem c' _ hmem' with h1 | ⟨rfl, h1⟩
    · exact hq h1
    · exact hdereg q h1 hl
  refine ⟨hI.regNe, hI.regBt, hI.unregBt, hI.unregMig, ?unregQueue, hI.unregHub, ?mintCount,
    hI.hubSettled, hI.l1Layer, hI.layerReg, ?queueVal, hI.hubVal, hI.retVal, ?settledEntry,
    ?returningEntry, ?mintingQueue, ?allowedSeq, hI.peerDone, ?resub, hok, ?properAllow⟩
  all_goals (try dsimp only)
  case unregQueue =>
    intro c' hc'
    have hne : c' ≠ c := by rintro rfl; rw [hc] at hc'; cases hc'
    rw [Function.update_of_ne hne]; exact hI.unregQueue c' hc'
  case mintCount =>
    intro c' q
    by_cases h : c' = c
    · subst h
      rw [Function.update_self, List.countP_append, hmint q, add_zero]
      exact hI.mintCount c' q
    · rw [Function.update_of_ne h]; exact hI.mintCount c' q
  case queueVal =>
    intro c' m hm
    rcases hmem c' m hm with h1 | ⟨-, h1⟩
    · exact hI.queueVal c' m h1
    · exact hval m h1
  case settledEntry =>
    intro q c' hq
    obtain ⟨h1, h2⟩ := hI.settledEntry q c' hq
    exact ⟨h1, hnotin q c' (by rw [hq]; rfl) h2⟩
  case returningEntry =>
    intro q c' a hq
    obtain ⟨h1, h2⟩ := hI.returningEntry q c' a hq
    exact ⟨h1, hnotin q c' (by rw [hq]; rfl) h2⟩
  case mintingQueue =>
    intro q c' hq
    obtain ⟨pre, a, post, h1, h2⟩ := hI.mintingQueue q c' hq
    rw [Function.update_apply]
    split_ifs with h
    · subst h
      refine ⟨pre, a, post ++ ms, by rw [h1]; simp, ?_⟩
      intro hm
      rcases List.mem_append.mp hm with h3 | h3
      · exact h2 h3
      · exact hdereg q h3 (by rw [hq]; rfl)
    · exact ⟨pre, a, post, h1, h2⟩
  case allowedSeq =>
    intro c' q
    show A c' q = (lastPeerWrite q ((S.done c').map Prod.fst ++
      Function.update S.queue c (S.queue c ++ ms) c')).getD false
    rw [hsent c']
    exact hA c' q
  case resub =>
    intro c'
    show ResubBacked ((S.done c').map Prod.fst ++ Function.update S.queue c (S.queue c ++ ms) c')
    rw [hsent c']
    split_ifs with h
    · exact hres
    · exact hI.resub c'
  case properAllow =>
    intro c' m hm q a s hms
    have hm' : m ∈ (if c' = c then S.sent c ++ ms else S.sent c') := by
      rw [← hsent c']; exact hm
    split_ifs at hm' with h
    · subst h
      rcases List.mem_append.mp hm' with h1 | h1
      · exact hI.properAllow c' m h1 q a s hms
      · exact hprop m h1 q a s hms
    · exact hI.properAllow c' m hm' q a s hms

theorem inv_allowInteropPeer {P : Params} {S S' : State} {c p : ChainId}
    (hI : Inv P S) (hs : Step deployed P S (.allowInteropPeer c p) S') : Inv P S' := by
  cases hs with
  | allowInteropPeer h1 h2 h3 h4 h5 h6 h7 h8 =>
  obtain ⟨hpc, hpl1, -⟩ := h2
  apply inv_enqueue hI h1
  · intro m hm
    simp only [List.mem_singleton] at hm
    subst hm
    exact ⟨rfl, h7⟩
  · intro q; simp [isMintOf]
  · intro q hq; simp at hq
  · intro c' q
    unfold setAllowed
    by_cases hc' : c' = c
    · subst hc'
      simp only [true_and, ite_true]
      rw [lastPeerWrite_snoc]
      by_cases hq : q = p
      · subst hq; simp [Msg.peerWrite]
      · simp [Msg.peerWrite, hq, Ne.symm hq, hI.allowedSeq c' q]
    · simp only [hc', false_and, ite_false]
      exact hI.allowedSeq c' q
  · exact resubBacked_append (hI.resub c) (by simp)
  · intro c' q hq
    unfold setAllowed at hq
    split_ifs at hq with h
    · obtain ⟨rfl, rfl⟩ := h
      exact ⟨h1, h7, h8, hpc, hpl1⟩
    · exact hI.allowedOk c' q hq
  · intro m hm q a s hms
    simp only [List.mem_singleton] at hm
    subst hm
    cases hms
    exact ⟨hpc, hpl1⟩

theorem inv_deregisterInteropPairs {P : Params} {S S' : State} {c : ChainId} {ps : List ChainId}
    (hI : Inv P S) (hs : Step deployed P S (.deregisterInteropPairs c ps) S') : Inv P S' := by
  cases hs with
  | deregisterInteropPairs h1 h2 =>
  apply inv_enqueue hI h1
  · intro m hm
    simp only [List.mem_map] at hm
    obtain ⟨q, -, rfl⟩ := hm
    trivial
  · intro q; exact countP_isMintOf_deregs q ps
  · intro q hq hl
    simp only [List.mem_map, Msg.dereg.injEq, exists_eq_right] at hq
    obtain ⟨-, -, h3⟩ := h2 q hq
    exact h3 rfl (sl_of_layer hI hl)
  · intro c' q
    unfold clearAllowed
    by_cases hc' : c' = c
    · subst hc'
      simp only [true_and, ite_true]
      rw [lastPeerWrite_append_deregs]
      split_ifs with hq
      · rfl
      · exact hI.allowedSeq c' q
    · simp only [hc', false_and, ite_false]
      exact hI.allowedSeq c' q
  · refine resubBacked_append (hI.resub c) ?_
    intro m hm q a
    simp only [List.mem_map] at hm
    obtain ⟨q', -, rfl⟩ := hm
    simp
  · intro c' q hq
    unfold clearAllowed at hq
    split_ifs at hq with h
    exact hI.allowedOk c' q hq
  · intro m hm q a s hms
    simp only [List.mem_map] at hm
    obtain ⟨q', -, rfl⟩ := hm
    cases hms

theorem inv_resubmit {P : Params} {S S' : State} {c p : ChainId}
    (hI : Inv P S) (hs : Step deployed P S (.resubmit c p) S') : Inv P S' := by
  cases hs with
  | resubmit h1 h2 h3 h4 =>
  obtain ⟨-, -, -, hpc, hpl1⟩ := hI.allowedOk c p h2
  have hback : lastPeerWrite p (S.sent c) = some true :=
    getD_false_eq_true (by rw [← hI.allowedSeq c p]; exact h2)
  refine inv_enqueue (A := S.l1.allowed) hI h1 ?_ ?_ ?_ ?_ ?_ (fun c' q hq => hI.allowedOk c' q hq) ?_
  · intro m hm
    simp only [List.mem_singleton] at hm
    subst hm
    exact ⟨rfl, h3⟩
  · intro q; simp [isMintOf]
  · intro q hq; simp at hq
  · intro c' q
    by_cases hc' : c' = c
    · subst hc'
      simp only [ite_true]
      rw [lastPeerWrite_snoc]
      by_cases hq : q = p
      · subst hq; simp [Msg.peerWrite, h2]
      · simp [Msg.peerWrite, Ne.symm hq, hI.allowedSeq c' q]
    · simp only [hc', ite_false]
      exact hI.allowedSeq c' q
  · exact resubBacked_snoc_resub (hI.resub c) hback
  · intro m hm q a s hms
    simp only [List.mem_singleton] at hm
    subst hm
    cases hms
    exact ⟨hpc, hpl1⟩

theorem inv_legacyRegister {P : Params} {S S' : State} {c p : ChainId}
    (hI : Inv P S) (hs : Step deployed P S (.legacyRegister c p) S') : Inv P S' := by
  cases hs with
  | legacyRegister h1 h2 h3 =>
  refine inv_enqueue (A := S.l1.allowed) hI h1 ?_ ?_ ?_ ?_ ?_ (fun c' q hq => hI.allowedOk c' q hq) ?_
  · intro m hm
    simp only [List.mem_singleton] at hm
    subst hm
    exact ⟨rfl, h2⟩
  · intro q; simp [isMintOf]
  · intro q hq; simp at hq
  · intro c' q
    split_ifs with hc'
    · subst hc'
      rw [lastPeerWrite_append_of_none _ _ _ (by simp [Msg.peerWrite])]
      exact hI.allowedSeq c' q
    · exact hI.allowedSeq c' q
  · exact resubBacked_append (hI.resub c) (by simp)
  · intro m hm q a s hms
    simp only [List.mem_singleton] at hm
    subst hm
    cases hms

theorem inv_otherRequest {P : Params} {S S' : State} {c : ChainId}
    (hI : Inv P S) (hs : Step deployed P S (.otherRequest c) S') : Inv P S' := by
  cases hs with
  | otherRequest h1 =>
  refine inv_enqueue (A := S.l1.allowed) hI h1 ?_ ?_ ?_ ?_ ?_ (fun c' q hq => hI.allowedOk c' q hq) ?_
  · intro m hm
    simp only [List.mem_singleton] at hm
    subst hm
    trivial
  · intro q; simp [isMintOf]
  · intro q hq; simp at hq
  · intro c' q
    split_ifs with hc'
    · subst hc'
      rw [lastPeerWrite_append_of_none _ _ _ (by simp [Msg.peerWrite])]
      exact hI.allowedSeq c' q
    · exact hI.allowedSeq c' q
  · exact resubBacked_append (hI.resub c) (by simp)
  · intro m hm q a s hms
    simp only [List.mem_singleton] at hm
    subst hm
    cases hms

/-! ### Executing the head of a queue -/

theorem sent_pop {S : State} {c : ChainId} {m : Msg} {post : List Msg}
    (hq : S.queue c = m :: post) (ok : Bool) (c' : ChainId) :
    (Function.update S.done c (S.done c ++ [(m, ok)]) c').map Prod.fst ++
      Function.update S.queue c post c' = S.sent c' := by
  by_cases h : c' = c
  · subst h; simp [State.sent, hq]
  · simp [Function.update_of_ne h, State.sent]

theorem mem_pop {S : State} {c c' : ChainId} {m m' : Msg} {post : List Msg}
    (hq : S.queue c = m :: post) (hm : m' ∈ Function.update S.queue c post c') :
    m' ∈ S.queue c' := by
  by_cases h : c' = c
  · subst h; rw [Function.update_self] at hm; rw [hq]; exact List.mem_cons_of_mem _ hm
  · rwa [Function.update_of_ne h] at hm

/-- Executing a head entry that is not an arrival. -/
theorem inv_pop {P : Params} {S : State} {c : ChainId} {m : Msg} {post : List Msg} {ok : Bool}
    {H : ChainId → Hub} (hI : Inv P S) (hq : S.queue c = m :: post)
    (hm : ∀ p a, m ≠ .mint p a)
    (hother : ∀ c', c' ≠ c → H c' = S.hub c')
    (hsl : (H c).sl = (S.hub c).sl)
    (hbta : ∀ q, (H c).bta q = 0 ∨ (H c).bta q = S.l1.bt q)
    (hkeep : ∀ q, (S.mig q = .settled c ∨ ∃ a, S.mig q = .returning c a) →
      (H c).bta q = S.l1.bt q)
    (hpeer : ∀ q, (H c).peer q = (lastOkPeerWrite q (S.done c ++ [(m, ok)])).getD false) :
    Inv P { S with hub := H, queue := Function.update S.queue c post,
                   done := Function.update S.done c (S.done c ++ [(m, ok)]) } := by
  have hc : S.l1.registered c = true := registered_of_queue hI hq
  have hmint : ∀ q, isMintOf q m = false := by
    intro q
    cases m with
    | mint p a => exact absurd rfl (hm p a)
    | _ => rfl
  have hsent := sent_pop hq ok
  refine ⟨hI.regNe, hI.regBt, hI.unregBt, hI.unregMig, ?unregQueue, ?unregHub, ?mintCount,
    ?hubSettled, hI.l1Layer, hI.layerReg, ?queueVal, ?hubVal, hI.retVal, ?settledEntry,
    ?returningEntry, ?mintingQueue, ?allowedSeq, ?peerDone, ?resub, hI.allowedOk, ?properAllow⟩
  all_goals (try dsimp only)
  case unregQueue =>
    intro c' hc'
    have hne : c' ≠ c := by rintro rfl; rw [hc] at hc'; cases hc'
    rw [Function.update_of_ne hne]; exact hI.unregQueue c' hc'
  case unregHub =>
    intro c' hc' q
    have hne : c' ≠ c := by rintro rfl; rw [hc] at hc'; cases hc'
    rw [hother c' hne]; exact hI.unregHub c' hc' q
  case mintCount =>
    intro c' q
    by_cases h : c' = c
    · subst h
      rw [Function.update_self, ← hI.mintCount c' q, hq, List.countP_cons, hmint q]
      simp
    · rw [Function.update_of_ne h]; exact hI.mintCount c' q
  case hubSettled =>
    intro c' q hc'
    by_cases h : c' = c
    · subst h; rw [hsl]; exact hI.hubSettled c' q hc'
    · rw [hother c' h]; exact hI.hubSettled c' q hc'
  case queueVal =>
    intro c' m' hm'
    exact hI.queueVal c' m' (mem_pop hq hm')
  case hubVal =>
    intro c' q
    by_cases h : c' = c
    · subst h; exact hbta q
    · rw [hother c' h]; exact hI.hubVal c' q
  case settledEntry =>
    intro q c' hq'
    obtain ⟨h1, h2⟩ := hI.settledEntry q c' hq'
    refine ⟨?_, fun hm' => h2 (mem_pop hq hm')⟩
    by_cases h : c' = c
    · subst h; exact hkeep q (Or.inl hq')
    · rw [hother c' h]; exact h1
  case returningEntry =>
    intro q c' a hq'
    obtain ⟨h1, h2⟩ := hI.returningEntry q c' a hq'
    refine ⟨?_, fun hm' => h2 (mem_pop hq hm')⟩
    by_cases h : c' = c
    · subst h; exact hkeep q (Or.inr ⟨a, hq'⟩)
    · rw [hother c' h]; exact h1
  case mintingQueue =>
    intro q c' hq'
    obtain ⟨pre, a, post', h1, h2⟩ := hI.mintingQueue q c' hq'
    by_cases h : c' = c
    · subst h
      rw [Function.update_self]
      rw [hq] at h1
      obtain ⟨pre', h3⟩ := shift_decomp h1 (hm q a)
      exact ⟨pre', a, post', h3, h2⟩
    · rw [Function.update_of_ne h]; exact ⟨pre, a, post', h1, h2⟩
  case allowedSeq =>
    intro c' q
    show S.l1.allowed c' q = (lastPeerWrite q ((Function.update S.done c
      (S.done c ++ [(m, ok)]) c').map Prod.fst ++ Function.update S.queue c post c')).getD false
    rw [hsent c']; exact hI.allowedSeq c' q
  case peerDone =>
    intro c' q
    by_cases h : c' = c
    · subst h; rw [Function.update_self]; exact hpeer q
    · rw [hother c' h, Function.update_of_ne h]; exact hI.peerDone c' q
  case resub =>
    intro c'
    show ResubBacked ((Function.update S.done c (S.done c ++ [(m, ok)]) c').map Prod.fst ++
      Function.update S.queue c post c')
    rw [hsent c']; exact hI.resub c'
  case properAllow =>
    intro c' m' hm'
    have hm'' : m' ∈ S.sent c' := by rw [← hsent c']; exact hm'
    exact hI.properAllow c' m' hm''

/-- The arrival of `p` on `c`, from the head of `c`'s queue, succeeds. -/
theorem inv_executeMintOk {P : Params} {S : State} {c p : ChainId} {a : AssetId}
    {post : List Msg} (hI : Inv P S) (hq : S.queue c = .mint p a :: post) :
    Inv P { S with
      hub := Function.update S.hub c { S.hub c with
        sl := Function.update (S.hub c).sl p c, bta := Function.update (S.hub c).bta p a }
      queue := Function.update S.queue c post
      done := Function.update S.done c (S.done c ++ [(.mint p a, true)])
      mig := Function.update S.mig p (.settled c) } := by
  have hmig : S.mig p = .minting c := by
    have h := hI.mintCount c p
    rw [hq, List.countP_cons] at h
    by_contra hne
    simp [isMintOf, hne] at h
  have hcnt : (S.queue c).countP (isMintOf p) = 1 := by rw [hI.mintCount c p]; simp [hmig]
  have hpost : Msg.dereg p ∉ post := by
    obtain ⟨pre, a', post', h1, h2⟩ := hI.mintingQueue p c hmig
    rw [hq] at h1
    have := decomp_head_of_count h1 (by rw [← hq]; exact hcnt)
    rw [this]; exact h2
  have hcar : a = S.l1.bt p ∧ a ≠ 0 :=
    hI.queueVal c (.mint p a) (by rw [hq]; exact List.mem_cons_self)
  obtain ⟨hcr, hcp, hpr⟩ := hI.layerReg p c (by rw [hmig]; rfl)
  have hsent := sent_pop hq true
  have hcntq : ∀ q, q ≠ p → post.countP (isMintOf q) = (S.queue c).countP (isMintOf q) := by
    intro q hqp
    rw [hq, List.countP_cons]
    simp [isMintOf, Ne.symm hqp]
  have hcntp : post.countP (isMintOf p) = 0 := by
    rw [hq, List.countP_cons] at hcnt
    simpa [isMintOf] using hcnt
  refine ⟨hI.regNe, hI.regBt, hI.unregBt, ?unregMig, ?unregQueue, ?unregHub, ?mintCount,
    ?hubSettled, ?l1Layer, ?layerReg, ?queueVal, ?hubVal, ?retVal, ?settledEntry,
    ?returningEntry, ?mintingQueue, ?allowedSeq, ?peerDone, ?resub, hI.allowedOk, ?properAllow⟩
  all_goals (try dsimp only)
  case unregMig =>
    intro q hq'
    have hne : q ≠ p := by rintro rfl; rw [hpr] at hq'; cases hq'
    rw [Function.update_of_ne hne]; exact hI.unregMig q hq'
  case unregQueue =>
    intro c' hc'
    have hne : c' ≠ c := by rintro rfl; rw [hcr] at hc'; cases hc'
    rw [Function.update_of_ne hne]; exact hI.unregQueue c' hc'
  case unregHub =>
    intro c' hc' q
    have hne : c' ≠ c := by rintro rfl; rw [hcr] at hc'; cases hc'
    rw [Function.update_of_ne hne]; exact hI.unregHub c' hc' q
  case mintCount =>
    intro c' q
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, reduceCtorEq, ite_false]
      by_cases hcc : c' = c
      · subst hcc; simp only [Function.update_self, hcntp]
      · simp only [Function.update_of_ne hcc, hI.mintCount c' q, hmig, Mig.minting.injEq]
        simp [Ne.symm hcc]
    · simp only [Function.update_of_ne hqp]
      by_cases hcc : c' = c
      · subst hcc; simp only [Function.update_self, hcntq q hqp]; exact hI.mintCount c' q
      · simp only [Function.update_of_ne hcc]; exact hI.mintCount c' q
  case hubSettled =>
    intro c' q hc'
    by_cases hcc : c' = c
    · subst hcc
      rw [Function.update_self]
      dsimp only
      by_cases hqp : q = p
      · subst hqp; simp
      · simp only [Function.update_of_ne hqp]
        exact hI.hubSettled c' q hc'
    · rw [Function.update_of_ne hcc]
      by_cases hqp : q = p
      · subst hqp
        rw [Function.update_self]
        have h := hI.hubSettled c' q hc'
        rw [hmig] at h
        simp only [reduceCtorEq, iff_false] at h
        simp only [h, false_iff, Mig.settled.injEq]
        exact Ne.symm hcc
      · rw [Function.update_of_ne hqp]; exact hI.hubSettled c' q hc'
  case l1Layer =>
    intro q hq'
    by_cases hqp : q = p
    · subst hqp
      rw [Function.update_self, hI.l1Layer q hq', hmig]
      rfl
    · rw [Function.update_of_ne hqp]; exact hI.l1Layer q hq'
  case layerReg =>
    intro q c'' hl
    by_cases hqp : q = p
    · subst hqp
      rw [Function.update_self] at hl
      simp only [Mig.layer, Option.some.injEq] at hl
      subst hl
      exact ⟨hcr, hcp, hpr⟩
    · rw [Function.update_of_ne hqp] at hl; exact hI.layerReg q c'' hl
  case queueVal =>
    intro c' m' hm'
    exact hI.queueVal c' m' (mem_pop hq hm')
  case hubVal =>
    intro c' q
    by_cases hcc : c' = c
    · subst hcc
      rw [Function.update_self]
      dsimp only
      by_cases hqp : q = p
      · subst hqp; rw [Function.update_self]; exact Or.inr hcar.1
      · rw [Function.update_of_ne hqp]; exact hI.hubVal c' q
    · rw [Function.update_of_ne hcc]; exact hI.hubVal c' q
  case retVal =>
    intro q c'' a' hq'
    have hne : q ≠ p := by rintro rfl; rw [Function.update_self] at hq'; cases hq'
    rw [Function.update_of_ne hne] at hq'
    exact hI.retVal q c'' a' hq'
  case settledEntry =>
    intro q c'' hq'
    by_cases hqp : q = p
    · subst hqp
      rw [Function.update_self] at hq'
      cases hq'
      rw [Function.update_self, Function.update_self]
      exact ⟨by dsimp only; rw [Function.update_self]; exact hcar.1, hpost⟩
    · rw [Function.update_of_ne hqp] at hq'
      obtain ⟨h1, h2⟩ := hI.settledEntry q c'' hq'
      by_cases hcc : c'' = c
      · subst hcc
        rw [Function.update_self, Function.update_self]
        refine ⟨?_, fun hm => h2 (by rw [hq]; exact List.mem_cons_of_mem _ hm)⟩
        dsimp only
        rw [Function.update_of_ne hqp]; exact h1
      · rw [Function.update_of_ne hcc, Function.update_of_ne hcc]; exact ⟨h1, h2⟩
  case returningEntry =>
    intro q c'' a' hq'
    have hqp : q ≠ p := by rintro rfl; rw [Function.update_self] at hq'; cases hq'
    rw [Function.update_of_ne hqp] at hq'
    obtain ⟨h1, h2⟩ := hI.returningEntry q c'' a' hq'
    by_cases hcc : c'' = c
    · subst hcc
      rw [Function.update_self, Function.update_self]
      refine ⟨?_, fun hm => h2 (by rw [hq]; exact List.mem_cons_of_mem _ hm)⟩
      dsimp only
      rw [Function.update_of_ne hqp]; exact h1
    · rw [Function.update_of_ne hcc, Function.update_of_ne hcc]; exact ⟨h1, h2⟩
  case mintingQueue =>
    intro q c'' hq'
    have hqp : q ≠ p := by rintro rfl; rw [Function.update_self] at hq'; cases hq'
    rw [Function.update_of_ne hqp] at hq'
    obtain ⟨pre, a', post', h1, h2⟩ := hI.mintingQueue q c'' hq'
    by_cases hcc : c'' = c
    · subst hcc
      rw [Function.update_self]
      rw [hq] at h1
      obtain ⟨pre', h3⟩ := shift_decomp h1 (by intro h; cases h; exact hqp rfl)
      exact ⟨pre', a', post', h3, h2⟩
    · rw [Function.update_of_ne hcc]; exact ⟨pre, a', post', h1, h2⟩
  case allowedSeq =>
    intro c' q
    show S.l1.allowed c' q = (lastPeerWrite q ((Function.update S.done c
      (S.done c ++ [(.mint p a, true)]) c').map Prod.fst ++
        Function.update S.queue c post c')).getD false
    rw [hsent c']; exact hI.allowedSeq c' q
  case peerDone =>
    intro c' q
    by_cases hcc : c' = c
    · subst hcc
      rw [Function.update_self, Function.update_self, lastOkPeerWrite_snoc]
      simp only [ite_true, Msg.peerWrite, Option.none_or]
      exact hI.peerDone c' q
    · rw [Function.update_of_ne hcc, Function.update_of_ne hcc]; exact hI.peerDone c' q
  case resub =>
    intro c'
    show ResubBacked ((Function.update S.done c (S.done c ++ [(.mint p a, true)]) c').map
      Prod.fst ++ Function.update S.queue c post c')
    rw [hsent c']; exact hI.resub c'
  case properAllow =>
    intro c' m' hm'
    have hm'' : m' ∈ S.sent c' := by rw [← hsent c']; exact hm'
    exact hI.properAllow c' m' hm''

/-- The arrival of `p` on `c`, from the head of `c`'s queue, fails. -/
theorem inv_executeMintFail {P : Params} {S : State} {c p : ChainId} {a : AssetId}
    {post : List Msg} (hI : Inv P S) (hq : S.queue c = .mint p a :: post) :
    Inv P { S with
      queue := Function.update S.queue c post
      done := Function.update S.done c (S.done c ++ [(.mint p a, false)])
      mig := Function.update S.mig p (.failed c) } := by
  have hmig : S.mig p = .minting c := by
    have h := hI.mintCount c p
    rw [hq, List.countP_cons] at h
    by_contra hne
    simp [isMintOf, hne] at h
  have hcnt : (S.queue c).countP (isMintOf p) = 1 := by rw [hI.mintCount c p]; simp [hmig]
  obtain ⟨hcr, hcp, hpr⟩ := hI.layerReg p c (by rw [hmig]; rfl)
  have hsent := sent_pop hq false
  have hcntq : ∀ q, q ≠ p → post.countP (isMintOf q) = (S.queue c).countP (isMintOf q) := by
    intro q hqp
    rw [hq, List.countP_cons]
    simp [isMintOf, Ne.symm hqp]
  have hcntp : post.countP (isMintOf p) = 0 := by
    rw [hq, List.countP_cons] at hcnt
    simpa [isMintOf] using hcnt
  refine ⟨hI.regNe, hI.regBt, hI.unregBt, ?unregMig, ?unregQueue, hI.unregHub, ?mintCount,
    ?hubSettled, ?l1Layer, ?layerReg, ?queueVal, hI.hubVal, ?retVal, ?settledEntry,
    ?returningEntry, ?mintingQueue, ?allowedSeq, ?peerDone, ?resub, hI.allowedOk, ?properAllow⟩
  all_goals (try dsimp only)
  case unregMig =>
    intro q hq'
    have hne : q ≠ p := by rintro rfl; rw [hpr] at hq'; cases hq'
    rw [Function.update_of_ne hne]; exact hI.unregMig q hq'
  case unregQueue =>
    intro c' hc'
    have hne : c' ≠ c := by rintro rfl; rw [hcr] at hc'; cases hc'
    rw [Function.update_of_ne hne]; exact hI.unregQueue c' hc'
  case mintCount =>
    intro c' q
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, reduceCtorEq, ite_false]
      by_cases hcc : c' = c
      · subst hcc; simp only [Function.update_self, hcntp]
      · simp only [Function.update_of_ne hcc, hI.mintCount c' q, hmig, Mig.minting.injEq]
        simp [Ne.symm hcc]
    · simp only [Function.update_of_ne hqp]
      by_cases hcc : c' = c
      · subst hcc; simp only [Function.update_self, hcntq q hqp]; exact hI.mintCount c' q
      · simp only [Function.update_of_ne hcc]; exact hI.mintCount c' q
  case hubSettled =>
    intro c' q hc'
    by_cases hqp : q = p
    · subst hqp
      rw [Function.update_self]
      have h := hI.hubSettled c' q hc'
      rw [hmig] at h
      simp only [reduceCtorEq, iff_false] at h
      simp only [h, reduceCtorEq]
    · rw [Function.update_of_ne hqp]; exact hI.hubSettled c' q hc'
  case l1Layer =>
    intro q hq'
    by_cases hqp : q = p
    · subst hqp
      rw [Function.update_self, hI.l1Layer q hq', hmig]
      rfl
    · rw [Function.update_of_ne hqp]; exact hI.l1Layer q hq'
  case layerReg =>
    intro q c'' hl
    by_cases hqp : q = p
    · subst hqp
      rw [Function.update_self] at hl
      simp only [Mig.layer, Option.some.injEq] at hl
      subst hl
      exact ⟨hcr, hcp, hpr⟩
    · rw [Function.update_of_ne hqp] at hl; exact hI.layerReg q c'' hl
  case queueVal =>
    intro c' m' hm'
    exact hI.queueVal c' m' (mem_pop hq hm')
  case retVal =>
    intro q c'' a' hq'
    have hne : q ≠ p := by rintro rfl; rw [Function.update_self] at hq'; cases hq'
    rw [Function.update_of_ne hne] at hq'
    exact hI.retVal q c'' a' hq'
  case settledEntry =>
    intro q c'' hq'
    have hqp : q ≠ p := by rintro rfl; rw [Function.update_self] at hq'; cases hq'
    rw [Function.update_of_ne hqp] at hq'
    obtain ⟨h1, h2⟩ := hI.settledEntry q c'' hq'
    exact ⟨h1, fun hm => h2 (mem_pop hq hm)⟩
  case returningEntry =>
    intro q c'' a' hq'
    have hqp : q ≠ p := by rintro rfl; rw [Function.update_self] at hq'; cases hq'
    rw [Function.update_of_ne hqp] at hq'
    obtain ⟨h1, h2⟩ := hI.returningEntry q c'' a' hq'
    exact ⟨h1, fun hm => h2 (mem_pop hq hm)⟩
  case mintingQueue =>
    intro q c'' hq'
    have hqp : q ≠ p := by rintro rfl; rw [Function.update_self] at hq'; cases hq'
    rw [Function.update_of_ne hqp] at hq'
    obtain ⟨pre, a', post', h1, h2⟩ := hI.mintingQueue q c'' hq'
    by_cases hcc : c'' = c
    · subst hcc
      rw [Function.update_self]
      rw [hq] at h1
      obtain ⟨pre', h3⟩ := shift_decomp h1 (by intro h; cases h; exact hqp rfl)
      exact ⟨pre', a', post', h3, h2⟩
    · rw [Function.update_of_ne hcc]; exact ⟨pre, a', post', h1, h2⟩
  case allowedSeq =>
    intro c' q
    show S.l1.allowed c' q = (lastPeerWrite q ((Function.update S.done c
      (S.done c ++ [(.mint p a, false)]) c').map Prod.fst ++
        Function.update S.queue c post c')).getD false
    rw [hsent c']; exact hI.allowedSeq c' q
  case peerDone =>
    intro c' q
    by_cases hcc : c' = c
    · subst hcc
      rw [Function.update_self, lastOkPeerWrite_snoc]
      simp only [Bool.false_eq_true, ite_false]
      exact hI.peerDone c' q
    · rw [Function.update_of_ne hcc]; exact hI.peerDone c' q
  case resub =>
    intro c'
    show ResubBacked ((Function.update S.done c (S.done c ++ [(.mint p a, false)]) c').map
      Prod.fst ++ Function.update S.queue c post c')
    rw [hsent c']; exact hI.resub c'
  case properAllow =>
    intro c' m' hm'
    have hm'' : m' ∈ S.sent c' := by rw [← hsent c']; exact hm'
    exact hI.properAllow c' m' hm''

theorem keep_of_inv {P : Params} {S : State} (hI : Inv P S) (c q : ChainId)
    (hq : S.mig q = .settled c ∨ ∃ a, S.mig q = .returning c a) : (S.hub c).bta q = S.l1.bt q := by
  rcases hq with hq | ⟨a', hq⟩
  · exact (hI.settledEntry q c hq).1
  · exact (hI.returningEntry q c a' hq).1

theorem inv_executeOk {P : Params} {S S' : State} {c : ChainId} {i : ℕ}
    (hI : Inv P S) (hs : Step deployed P S (.execute c i true) S') : Inv P S' := by
  cases hs with
  | executeOk hq hfifo hrun =>
  rename_i pre post m h
  obtain rfl : pre = [] := hfifo rfl
  simp only [List.nil_append] at hq
  cases m with
  | allow p a s =>
    have hcar : a = S.l1.bt p ∧ a ≠ 0 :=
      hI.queueVal c (.allow p a s) (by rw [hq]; exact List.mem_cons_self)
    simp only [Msg.run, hcar.2, ite_false, Option.some.injEq] at hrun
    subst hrun
    refine inv_pop (ok := true) hI hq (fun _ _ h => by cases h)
      (fun c' h => Function.update_of_ne h _ _) ?_ ?_ ?_ ?_
    · rw [Function.update_self]
    · intro q
      rw [Function.update_self]
      dsimp only
      by_cases hqp : q = p
      · subst hqp; rw [Function.update_self]; exact Or.inr hcar.1
      · rw [Function.update_of_ne hqp]; exact hI.hubVal c q
    · intro q hq'
      rw [Function.update_self]
      dsimp only
      by_cases hqp : q = p
      · subst hqp; rw [Function.update_self]; exact hcar.1
      · rw [Function.update_of_ne hqp]; exact keep_of_inv hI c q hq'
    · intro q
      rw [Function.update_self, lastOkPeerWrite_snoc]
      dsimp only
      by_cases hqp : q = p
      · subst hqp; simp [Msg.peerWrite]
      · rw [Function.update_of_ne hqp]; simp [Msg.peerWrite, Ne.symm hqp, hI.peerDone c q]
  | dereg p =>
    simp only [Msg.run, Option.some.injEq] at hrun
    subst hrun
    refine inv_pop (ok := true) hI hq (fun _ _ h => by cases h)
      (fun c' h => Function.update_of_ne h _ _) ?_ ?_ ?_ ?_
    · rw [Function.update_self]
    · intro q
      rw [Function.update_self]
      dsimp only
      by_cases hqp : q = p
      · subst hqp; rw [Function.update_self]; exact Or.inl rfl
      · rw [Function.update_of_ne hqp]; exact hI.hubVal c q
    · intro q hq'
      rw [Function.update_self]
      dsimp only
      by_cases hqp : q = p
      · subst hqp
        exfalso
        have hin : Msg.dereg q ∈ S.queue c := by rw [hq]; exact List.mem_cons_self
        rcases hq' with hq' | ⟨a', hq'⟩
        · exact (hI.settledEntry q c hq').2 hin
        · exact (hI.returningEntry q c a' hq').2 hin
      · rw [Function.update_of_ne hqp]; exact keep_of_inv hI c q hq'
    · intro q
      rw [Function.update_self, lastOkPeerWrite_snoc]
      dsimp only
      by_cases hqp : q = p
      · subst hqp; simp [Msg.peerWrite]
      · rw [Function.update_of_ne hqp]; simp [Msg.peerWrite, Ne.symm hqp, hI.peerDone c q]
  | legacy p a =>
    have hcar : a = S.l1.bt p ∧ a ≠ 0 :=
      hI.queueVal c (.legacy p a) (by rw [hq]; exact List.mem_cons_self)
    simp only [Msg.run, Option.some.injEq] at hrun
    subst hrun
    refine inv_pop (ok := true) hI hq (fun _ _ h => by cases h)
      (fun c' h => Function.update_of_ne h _ _) ?_ ?_ ?_ ?_
    · rw [Function.update_self]
    · intro q
      rw [Function.update_self]
      dsimp only
      by_cases hqp : q = p
      · subst hqp; rw [Function.update_self]; exact Or.inr hcar.1
      · rw [Function.update_of_ne hqp]; exact hI.hubVal c q
    · intro q hq'
      rw [Function.update_self]
      dsimp only
      by_cases hqp : q = p
      · subst hqp; rw [Function.update_self]; exact hcar.1
      · rw [Function.update_of_ne hqp]; exact keep_of_inv hI c q hq'
    · intro q
      rw [Function.update_self, lastOkPeerWrite_snoc]
      simp [Msg.peerWrite, hI.peerDone c q]
  | mint p a =>
    simp only [Msg.run] at hrun
    split_ifs at hrun with hsl
    simp only [Option.some.injEq] at hrun
    subst hrun
    exact inv_executeMintOk hI hq
  | other =>
    simp only [Msg.run, Option.some.injEq] at hrun
    subst hrun
    refine inv_pop (ok := true) hI hq (fun _ _ h => by cases h)
      (fun c' h => Function.update_of_ne h _ _) ?_ ?_ ?_ ?_
    · rw [Function.update_self]
    · intro q; rw [Function.update_self]; exact hI.hubVal c q
    · intro q hq'; rw [Function.update_self]; exact keep_of_inv hI c q hq'
    · intro q
      rw [Function.update_self, lastOkPeerWrite_snoc]
      simp [Msg.peerWrite, hI.peerDone c q]

theorem inv_executeFail {P : Params} {S S' : State} {c : ChainId} {i : ℕ}
    (hI : Inv P S) (hs : Step deployed P S (.execute c i false) S') : Inv P S' := by
  cases hs with
  | executeFail hq hfifo =>
  rename_i pre post m
  obtain rfl : pre = [] := hfifo rfl
  simp only [List.nil_append] at hq
  have hpeer : ∀ q, (S.hub c).peer q =
      (lastOkPeerWrite q (S.done c ++ [(m, false)])).getD false := by
    intro q
    rw [lastOkPeerWrite_snoc]
    simp only [Bool.false_eq_true, ite_false]
    exact hI.peerDone c q
  cases m with
  | mint p a => exact inv_executeMintFail hI hq
  | allow p a s =>
    exact inv_pop (H := S.hub) (ok := false) hI hq (fun _ _ h => by cases h) (fun _ _ => rfl) rfl
      (hI.hubVal c) (keep_of_inv hI c) hpeer
  | dereg p =>
    exact inv_pop (H := S.hub) (ok := false) hI hq (fun _ _ h => by cases h) (fun _ _ => rfl) rfl
      (hI.hubVal c) (keep_of_inv hI c) hpeer
  | legacy p a =>
    exact inv_pop (H := S.hub) (ok := false) hI hq (fun _ _ h => by cases h) (fun _ _ => rfl) rfl
      (hI.hubVal c) (keep_of_inv hI c) hpeer
  | other =>
    exact inv_pop (H := S.hub) (ok := false) hI hq (fun _ _ h => by cases h) (fun _ _ => rfl) rfl
      (hI.hubVal c) (keep_of_inv hI c) hpeer

/-! ### Migrations -/

theorem inv_migrateToLayer {P : Params} {S S' : State} {p c : ChainId}
    (hI : Inv P S) (hs : Step deployed P S (.migrateToLayer p c) S') : Inv P S' := by
  cases hs with
  | migrateToLayer h1 h2 h3 h4 h5 =>
  have hhome : S.mig p = .home := home_of_sl hI h1 h5
  have hbt : S.l1.bt p ≠ 0 := hI.regBt p h1
  have hsent : ∀ c', (S.done c').map Prod.fst ++
      Function.update S.queue c (S.queue c ++ [Msg.mint p (S.l1.bt p)]) c' =
      if c' = c then S.sent c ++ [Msg.mint p (S.l1.bt p)] else S.sent c' := by
    intro c'
    by_cases h : c' = c
    · subst h; simp [State.sent]
    · simp [h, State.sent]
  have hmem : ∀ c' m, m ∈ Function.update S.queue c (S.queue c ++ [Msg.mint p (S.l1.bt p)]) c' →
      m ∈ S.queue c' ∨ m = Msg.mint p (S.l1.bt p) := by
    intro c' m hm
    by_cases h : c' = c
    · subst h
      rw [Function.update_self] at hm
      simpa using hm
    · rw [Function.update_of_ne h] at hm; exact Or.inl hm
  refine ⟨hI.regNe, hI.regBt, hI.unregBt, ?unregMig, ?unregQueue, hI.unregHub, ?mintCount,
    ?hubSettled, ?l1Layer, ?layerReg, ?queueVal, hI.hubVal, ?retVal, ?settledEntry,
    ?returningEntry, ?mintingQueue, ?allowedSeq, hI.peerDone, ?resub, hI.allowedOk, ?properAllow⟩
  all_goals (try dsimp only)
  case unregMig =>
    intro q hq
    have hne : q ≠ p := by rintro rfl; rw [h1] at hq; cases hq
    simp only [Function.update_of_ne hne]; exact hI.unregMig q hq
  case unregQueue =>
    intro c' hc'
    have hne : c' ≠ c := by rintro rfl; rw [h2] at hc'; cases hc'
    simp only [Function.update_of_ne hne]; exact hI.unregQueue c' hc'
  case mintCount =>
    intro c' q
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self]
      by_cases hcc : c' = c
      · subst hcc
        simp only [Function.update_self, List.countP_append, hI.mintCount c' q, hhome]
        simp [isMintOf]
      · simp only [Function.update_of_ne hcc, hI.mintCount c' q, hhome]
        simp [Ne.symm hcc]
    · simp only [Function.update_of_ne hqp]
      by_cases hcc : c' = c
      · subst hcc
        simp only [Function.update_self, List.countP_append, hI.mintCount c' q]
        simp [isMintOf, Ne.symm hqp]
      · simp only [Function.update_of_ne hcc]; exact hI.mintCount c' q
  case hubSettled =>
    intro c' q hc'
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, reduceCtorEq, iff_false]
      intro h
      have := (hI.hubSettled c' q hc').mp h
      rw [hhome] at this; cases this
    · simp only [Function.update_of_ne hqp]; exact hI.hubSettled c' q hc'
  case l1Layer =>
    intro q hq
    by_cases hqp : q = p
    · subst hqp; simp only [Function.update_self]; rfl
    · simp only [Function.update_of_ne hqp]; exact hI.l1Layer q hq
  case layerReg =>
    intro q c'' hl
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, Mig.layer, Option.some.injEq] at hl
      subst hl
      exact ⟨h2, h3, h1⟩
    · simp only [Function.update_of_ne hqp] at hl; exact hI.layerReg q c'' hl
  case queueVal =>
    intro c' m hm
    rcases hmem c' m hm with h | rfl
    · exact hI.queueVal c' m h
    · exact ⟨rfl, hbt⟩
  case retVal =>
    intro q c'' a hq
    have hqp : q ≠ p := by rintro rfl; simp at hq
    simp only [Function.update_of_ne hqp] at hq
    exact hI.retVal q c'' a hq
  case settledEntry =>
    intro q c'' hq
    have hqp : q ≠ p := by rintro rfl; simp at hq
    simp only [Function.update_of_ne hqp] at hq
    obtain ⟨h6, h7⟩ := hI.settledEntry q c'' hq
    refine ⟨h6, fun hm => ?_⟩
    rcases hmem c'' _ hm with h | h
    · exact h7 h
    · cases h
  case returningEntry =>
    intro q c'' a hq
    have hqp : q ≠ p := by rintro rfl; simp at hq
    simp only [Function.update_of_ne hqp] at hq
    obtain ⟨h6, h7⟩ := hI.returningEntry q c'' a hq
    refine ⟨h6, fun hm => ?_⟩
    rcases hmem c'' _ hm with h | h
    · exact h7 h
    · cases h
  case mintingQueue =>
    intro q c'' hq
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, Mig.minting.injEq] at hq
      subst hq
      simp only [Function.update_self]
      exact ⟨S.queue c, S.l1.bt q, [], rfl, by simp⟩
    · simp only [Function.update_of_ne hqp] at hq
      obtain ⟨pre, a, post, h6, h7⟩ := hI.mintingQueue q c'' hq
      by_cases hcc : c'' = c
      · subst hcc
        simp only [Function.update_self]
        refine ⟨pre, a, post ++ [Msg.mint p (S.l1.bt p)], by rw [h6]; simp, ?_⟩
        simp [h7]
      · simp only [Function.update_of_ne hcc]; exact ⟨pre, a, post, h6, h7⟩
  case allowedSeq =>
    intro c' q
    show S.l1.allowed c' q = (lastPeerWrite q ((S.done c').map Prod.fst ++
      Function.update S.queue c (S.queue c ++ [Msg.mint p (S.l1.bt p)]) c')).getD false
    rw [hsent c']
    split_ifs with hcc
    · subst hcc
      rw [lastPeerWrite_append_of_none _ _ _ (by simp [Msg.peerWrite])]
      exact hI.allowedSeq c' q
    · exact hI.allowedSeq c' q
  case resub =>
    intro c'
    show ResubBacked ((S.done c').map Prod.fst ++
      Function.update S.queue c (S.queue c ++ [Msg.mint p (S.l1.bt p)]) c')
    rw [hsent c']
    split_ifs
    · exact resubBacked_append (hI.resub c) (by simp)
    · exact hI.resub c'
  case properAllow =>
    intro c' m hm q a s hms
    have hm' : m ∈ (if c' = c then S.sent c ++ [Msg.mint p (S.l1.bt p)] else S.sent c') := by
      rw [← hsent c']; exact hm
    split_ifs at hm' with hcc
    · subst hcc
      rcases List.mem_append.mp hm' with h | h
      · exact hI.properAllow c' m h q a s hms
      · simp only [List.mem_singleton] at h; subst h; cases hms
    · exact hI.properAllow c' m hm' q a s hms

theorem inv_burnOnLayer {P : Params} {S S' : State} {p c : ChainId}
    (hI : Inv P S) (hs : Step deployed P S (.burnOnLayer p c) S') : Inv P S' := by
  cases hs with
  | burnOnLayer h1 h2 =>
  have hmig : S.mig p = .settled c := (hI.hubSettled c p h1).mp h2
  obtain ⟨-, -, hpr⟩ := hI.layerReg p c (by rw [hmig]; rfl)
  obtain ⟨hbta, hdereg⟩ := hI.settledEntry p c hmig
  have hcl1 : c ≠ P.l1 := (hI.regNe c h1).2
  refine ⟨hI.regNe, hI.regBt, hI.unregBt, ?unregMig, hI.unregQueue, ?unregHub, ?mintCount,
    ?hubSettled, ?l1Layer, ?layerReg, hI.queueVal, ?hubVal, ?retVal, ?settledEntry,
    ?returningEntry, ?mintingQueue, hI.allowedSeq, ?peerDone, hI.resub, hI.allowedOk,
    hI.properAllow⟩
  all_goals (try dsimp only)
  case unregMig =>
    intro q hq
    have hne : q ≠ p := by rintro rfl; rw [hpr] at hq; cases hq
    simp only [Function.update_of_ne hne]; exact hI.unregMig q hq
  case unregHub =>
    intro c' hc' q
    have hne : c' ≠ c := by rintro rfl; rw [h1] at hc'; cases hc'
    simp only [Function.update_of_ne hne]; exact hI.unregHub c' hc' q
  case mintCount =>
    intro c' q
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, reduceCtorEq, ite_false]
      rw [hI.mintCount c' q, hmig]
      simp
    · simp only [Function.update_of_ne hqp]; exact hI.mintCount c' q
  case hubSettled =>
    intro c' q hc'
    by_cases hcc : c' = c
    · subst hcc
      simp only [Function.update_self]
      by_cases hqp : q = p
      · subst hqp
        simp only [Function.update_self, reduceCtorEq, iff_false]
        exact Ne.symm hcl1
      · simp only [Function.update_of_ne hqp]; exact hI.hubSettled c' q hc'
    · simp only [Function.update_of_ne hcc]
      by_cases hqp : q = p
      · subst hqp
        simp only [Function.update_self, reduceCtorEq, iff_false]
        intro h
        have := (hI.hubSettled c' q hc').mp h
        rw [hmig] at this
        cases this
        exact hcc rfl
      · simp only [Function.update_of_ne hqp]; exact hI.hubSettled c' q hc'
  case l1Layer =>
    intro q hq
    by_cases hqp : q = p
    · subst hqp; simp only [Function.update_self]; rw [hI.l1Layer q hq, hmig]; rfl
    · simp only [Function.update_of_ne hqp]; exact hI.l1Layer q hq
  case layerReg =>
    intro q c'' hl
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, Mig.layer, Option.some.injEq] at hl
      subst hl
      exact hI.layerReg q c (by rw [hmig]; rfl)
    · simp only [Function.update_of_ne hqp] at hl; exact hI.layerReg q c'' hl
  case hubVal =>
    intro c' q
    by_cases hcc : c' = c
    · subst hcc; simp only [Function.update_self]; exact hI.hubVal c' q
    · simp only [Function.update_of_ne hcc]; exact hI.hubVal c' q
  case retVal =>
    intro q c'' a hq
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, Mig.returning.injEq] at hq
      obtain ⟨-, rfl⟩ := hq
      exact hbta
    · simp only [Function.update_of_ne hqp] at hq; exact hI.retVal q c'' a hq
  case settledEntry =>
    intro q c'' hq
    have hqp : q ≠ p := by rintro rfl; simp at hq
    simp only [Function.update_of_ne hqp] at hq
    obtain ⟨h3, h4⟩ := hI.settledEntry q c'' hq
    refine ⟨?_, h4⟩
    by_cases hcc : c'' = c
    · subst hcc; simp only [Function.update_self]; exact h3
    · simp only [Function.update_of_ne hcc]; exact h3
  case returningEntry =>
    intro q c'' a hq
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, Mig.returning.injEq] at hq
      obtain ⟨rfl, -⟩ := hq
      simp only [Function.update_self]
      exact ⟨hbta, hdereg⟩
    · simp only [Function.update_of_ne hqp] at hq
      obtain ⟨h3, h4⟩ := hI.returningEntry q c'' a hq
      refine ⟨?_, h4⟩
      by_cases hcc : c'' = c
      · subst hcc; simp only [Function.update_self]; exact h3
      · simp only [Function.update_of_ne hcc]; exact h3
  case mintingQueue =>
    intro q c'' hq
    have hqp : q ≠ p := by rintro rfl; simp at hq
    simp only [Function.update_of_ne hqp] at hq
    exact hI.mintingQueue q c'' hq
  case peerDone =>
    intro c' q
    by_cases hcc : c' = c
    · subst hcc; simp only [Function.update_self]; exact hI.peerDone c' q
    · simp only [Function.update_of_ne hcc]; exact hI.peerDone c' q

theorem inv_finalizeReturn {P : Params} {S S' : State} {p : ChainId}
    (hI : Inv P S) (hs : Step deployed P S (.finalizeReturn p) S') : Inv P S' := by
  cases hs with
  | finalizeReturn h1 h2 =>
  rename_i c a
  have ha : a = S.l1.bt p := hI.retVal p c a h1
  obtain ⟨-, -, hpr⟩ := hI.layerReg p c (by rw [h1]; rfl)
  have hbteq : Function.update S.l1.bt p a = S.l1.bt := by
    rw [ha]; exact Function.update_eq_self p S.l1.bt
  rw [hbteq]
  refine ⟨hI.regNe, hI.regBt, hI.unregBt, ?unregMig, hI.unregQueue, hI.unregHub, ?mintCount,
    ?hubSettled, ?l1Layer, ?layerReg, hI.queueVal, hI.hubVal, ?retVal, ?settledEntry,
    ?returningEntry, ?mintingQueue, hI.allowedSeq, hI.peerDone, hI.resub, hI.allowedOk,
    hI.properAllow⟩
  all_goals (try dsimp only)
  case unregMig =>
    intro q hq
    have hne : q ≠ p := by rintro rfl; rw [hpr] at hq; cases hq
    simp only [Function.update_of_ne hne]; exact hI.unregMig q hq
  case mintCount =>
    intro c' q
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, reduceCtorEq, ite_false]
      rw [hI.mintCount c' q, h1]
      simp
    · simp only [Function.update_of_ne hqp]; exact hI.mintCount c' q
  case hubSettled =>
    intro c' q hc'
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, reduceCtorEq, iff_false]
      intro h
      have := (hI.hubSettled c' q hc').mp h
      rw [h1] at this; cases this
    · simp only [Function.update_of_ne hqp]; exact hI.hubSettled c' q hc'
  case l1Layer =>
    intro q hq
    by_cases hqp : q = p
    · subst hqp; simp only [Function.update_self]; rfl
    · simp only [Function.update_of_ne hqp]; exact hI.l1Layer q hq
  case layerReg =>
    intro q c'' hl
    by_cases hqp : q = p
    · subst hqp; simp [Mig.layer] at hl
    · simp only [Function.update_of_ne hqp] at hl; exact hI.layerReg q c'' hl
  case retVal =>
    intro q c'' a' hq
    have hqp : q ≠ p := by rintro rfl; simp at hq
    simp only [Function.update_of_ne hqp] at hq
    exact hI.retVal q c'' a' hq
  case settledEntry =>
    intro q c'' hq
    have hqp : q ≠ p := by rintro rfl; simp at hq
    simp only [Function.update_of_ne hqp] at hq
    exact hI.settledEntry q c'' hq
  case returningEntry =>
    intro q c'' a' hq
    have hqp : q ≠ p := by rintro rfl; simp at hq
    simp only [Function.update_of_ne hqp] at hq
    exact hI.returningEntry q c'' a' hq
  case mintingQueue =>
    intro q c'' hq
    have hqp : q ≠ p := by rintro rfl; simp at hq
    simp only [Function.update_of_ne hqp] at hq
    exact hI.mintingQueue q c'' hq

theorem inv_confirmFailedMigration {P : Params} {S S' : State} {p : ChainId}
    (hI : Inv P S) (hs : Step deployed P S (.confirmFailedMigration p) S') : Inv P S' := by
  cases hs with
  | confirmFailedMigration h1 =>
  rename_i c
  obtain ⟨-, -, hpr⟩ := hI.layerReg p c (by rw [h1]; rfl)
  refine ⟨hI.regNe, hI.regBt, hI.unregBt, ?unregMig, hI.unregQueue, hI.unregHub, ?mintCount,
    ?hubSettled, ?l1Layer, ?layerReg, hI.queueVal, hI.hubVal, ?retVal, ?settledEntry,
    ?returningEntry, ?mintingQueue, hI.allowedSeq, hI.peerDone, hI.resub, hI.allowedOk,
    hI.properAllow⟩
  all_goals (try dsimp only)
  case unregMig =>
    intro q hq
    have hne : q ≠ p := by rintro rfl; rw [hpr] at hq; cases hq
    simp only [Function.update_of_ne hne]; exact hI.unregMig q hq
  case mintCount =>
    intro c' q
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, reduceCtorEq, ite_false]
      rw [hI.mintCount c' q, h1]
      simp
    · simp only [Function.update_of_ne hqp]; exact hI.mintCount c' q
  case hubSettled =>
    intro c' q hc'
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, reduceCtorEq, iff_false]
      intro h
      have := (hI.hubSettled c' q hc').mp h
      rw [h1] at this; cases this
    · simp only [Function.update_of_ne hqp]; exact hI.hubSettled c' q hc'
  case l1Layer =>
    intro q hq
    by_cases hqp : q = p
    · subst hqp; simp only [Function.update_self]; rfl
    · simp only [Function.update_of_ne hqp]; exact hI.l1Layer q hq
  case layerReg =>
    intro q c'' hl
    by_cases hqp : q = p
    · subst hqp; simp [Mig.layer] at hl
    · simp only [Function.update_of_ne hqp] at hl; exact hI.layerReg q c'' hl
  case retVal =>
    intro q c'' a' hq
    have hqp : q ≠ p := by rintro rfl; simp at hq
    simp only [Function.update_of_ne hqp] at hq
    exact hI.retVal q c'' a' hq
  case settledEntry =>
    intro q c'' hq
    have hqp : q ≠ p := by rintro rfl; simp at hq
    simp only [Function.update_of_ne hqp] at hq
    exact hI.settledEntry q c'' hq
  case returningEntry =>
    intro q c'' a' hq
    have hqp : q ≠ p := by rintro rfl; simp at hq
    simp only [Function.update_of_ne hqp] at hq
    exact hI.returningEntry q c'' a' hq
  case mintingQueue =>
    intro q c'' hq
    have hqp : q ≠ p := by rintro rfl; simp at hq
    simp only [Function.update_of_ne hqp] at hq
    exact hI.mintingQueue q c'' hq

/-! ### The induction -/

theorem inv_step {P : Params} {S S' : State} {a : Action} (hI : Inv P S)
    (hs : Step deployed P S a S') : Inv P S' := by
  cases a with
  | createChain p a => exact inv_createChain hI hs
  | enableInterop c => exact inv_enableInterop hI hs
  | pushBatch c => exact inv_pushBatch hI hs
  | allowInteropPeer c p => exact inv_allowInteropPeer hI hs
  | deregisterInteropPairs c ps => exact inv_deregisterInteropPairs hI hs
  | resubmit c p => exact inv_resubmit hI hs
  | legacyRegister c p => exact inv_legacyRegister hI hs
  | otherRequest c => exact inv_otherRequest hI hs
  | execute c i ok =>
    cases ok with
    | true => exact inv_executeOk hI hs
    | false => exact inv_executeFail hI hs
  | migrateToLayer p c => exact inv_migrateToLayer hI hs
  | burnOnLayer p c => exact inv_burnOnLayer hI hs
  | finalizeReturn p => exact inv_finalizeReturn hI hs
  | confirmFailedMigration p => exact inv_confirmFailedMigration hI hs

theorem inv_reach {P : Params} {S : State} (h : Reach deployed P S) : Inv P S := by
  induction h with
  | init => exact inv_init P
  | step _ hs ih => exact inv_step ih hs

/-! ## Runs -/

theorem steps_trans {K : Config} {P : Params} {S S' S'' : State} (h1 : Steps K P S S')
    (h2 : Steps K P S' S'') : Steps K P S S'' := by
  induction h2 with
  | refl => exact h1
  | step _ hs ih => exact Steps.step ih hs

theorem steps_head {K : Config} {P : Params} {S S' S'' : State} {a : Action}
    (h1 : Step K P S a S') (h2 : Steps K P S' S'') : Steps K P S S'' :=
  steps_trans (Steps.step (Steps.refl S) h1) h2

theorem reach_of_steps {K : Config} {P : Params} {S S' : State} (h1 : Reach K P S)
    (h2 : Steps K P S S') : Reach K P S' := by
  induction h2 with
  | refl => exact h1
  | step _ hs ih => exact Reach.step ih hs

theorem registered_step {K : Config} {P : Params} {S S' : State} {a : Action}
    (hs : Step K P S a S') {c : ChainId} (hc : S.l1.registered c = true) :
    S'.l1.registered c = true := by
  cases hs with
  | createChain =>
    show Function.update S.l1.registered _ true c = true
    rw [Function.update_apply]; split_ifs <;> simp [hc]
  | _ => exact hc

theorem bt_step {P : Params} {S S' : State} {a : Action} (hI : Inv P S)
    (hs : Step deployed P S a S') (q : ChainId) (hq : S.l1.bt q ≠ 0) :
    S'.l1.bt q = S.l1.bt q := by
  cases hs with
  | createChain h1 =>
    show Function.update _ _ _ q = _
    rw [Function.update_of_ne]
    rintro rfl
    exact hq (hI.unregBt _ h1)
  | finalizeReturn h1 h2 =>
    rename_i p c a
    show Function.update S.l1.bt p a q = S.l1.bt q
    by_cases hqp : q = p
    · subst hqp; rw [Function.update_self]; exact hI.retVal q c a h1
    · rw [Function.update_of_ne hqp]
  | _ => rfl

theorem bt_steps {P : Params} {S S' : State} (hR : Reach deployed P S)
    (h : Steps deployed P S S') (q : ChainId) (hq : S.l1.bt q ≠ 0) :
    S'.l1.bt q = S.l1.bt q := by
  induction h with
  | refl => rfl
  | step h1 hs ih =>
    rw [← ih]
    exact bt_step (inv_reach (reach_of_steps hR h1)) hs q (by rw [ih]; exact hq)

/-! ## (a) The mirror -/

theorem PeerFlagMirrorsWhenLastEntrySucceeded :
    Properties.PeerFlagMirrorsWhenLastEntrySucceeded := by
  intro P S hR c p hnone hok
  have hI := inv_reach hR
  rw [hI.peerDone c p, hI.allowedSeq c p, lastOkPeerWrite_eq_of_lastOk p _ hok]
  unfold State.sent
  rw [lastPeerWrite_append_of_none p _ _ hnone]

theorem PeerFlagMirrorsWhenServiceEntriesSucceed :
    Properties.PeerFlagMirrorsWhenServiceEntriesSucceed := by
  intro P S hR c p hnone hserv
  have hI := inv_reach hR
  have hres : ResubBacked ((S.done c).map Prod.fst) := resubBacked_prefix (hI.resub c)
  rw [hI.peerDone c p, hI.allowedSeq c p, lastOkPeerWrite_eq_of_service p _ hres hserv]
  unfold State.sent
  rw [lastPeerWrite_append_of_none p _ _ hnone]

theorem ResubmissionRestoresPeerFlag : Properties.ResubmissionRestoresPeerFlag := by
  intro P S c p hR hq hallowed
  have hI := inv_reach hR
  obtain ⟨hc, hbt, hbatch, -, -⟩ := hI.allowedOk c p hallowed
  refine ⟨_, _, Step.resubmit hc hallowed hbt hbatch,
    Step.executeOk (pre := []) (post := []) (m := .allow p (S.l1.bt p) false)
      (h := { S.hub c with peer := Function.update (S.hub c).peer p true,
                           bta := Function.update (S.hub c).bta p (S.l1.bt p) })
      ?_ (fun _ => rfl) ?_, ?_, ?_, ?_⟩
  · simp [hq]
  · simp [Msg.run, hbt]
  · simp
  · simp
  · exact hallowed

theorem exists_allow_of_lastOkPeerWrite {p : ChainId} {d : List (Msg × Bool)}
    (h : lastOkPeerWrite p d = some true) : ∃ a s, (Msg.allow p a s, true) ∈ d := by
  induction d using List.reverseRecOn with
  | nil => simp [lastOkPeerWrite] at h
  | append_singleton d e ih =>
    rw [lastOkPeerWrite_snoc] at h
    obtain ⟨m, ok⟩ := e
    cases ok with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at h
      obtain ⟨a, s, hm⟩ := ih h
      exact ⟨a, s, List.mem_append_left _ hm⟩
    | true =>
      simp only [ite_true] at h
      cases hw : m.peerWrite p with
      | none =>
        rw [hw, Option.none_or] at h
        obtain ⟨a, s, hm⟩ := ih h
        exact ⟨a, s, List.mem_append_left _ hm⟩
      | some v =>
        rcases peerWrite_eq_some hw with ⟨a, s, rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨a, s, List.mem_append_right _ List.mem_cons_self⟩
        · rw [hw] at h; simp at h

theorem PeerFlagsOnlyForProperPeers : Properties.PeerFlagsOnlyForProperPeers := by
  intro P S hR c p h
  have hI := inv_reach hR
  rcases h with h | h
  · obtain ⟨-, -, -, h1, h2⟩ := hI.allowedOk c p h
    exact ⟨h1, h2⟩
  · rw [hI.peerDone c p] at h
    obtain ⟨a, s, hm⟩ := exists_allow_of_lastOkPeerWrite (getD_false_eq_true h)
    have hm' : Msg.allow p a s ∈ S.sent c :=
      List.mem_append_left _ (List.mem_map.mpr ⟨_, hm, rfl⟩)
    exact hI.properAllow c _ hm' p a s rfl

/-! ### A failed deregistration -/

theorem DeregistrationRepeatClearsPeerFlag : Properties.DeregistrationRepeatClearsPeerFlag := by
  intro P S c p _ hc hq hpc hpl hsl
  refine ⟨_, _, Step.deregisterInteropPairs (ps := [p]) hc ?_,
    Step.executeOk (pre := []) (post := []) (m := .dereg p)
      (h := { S.hub c with peer := Function.update (S.hub c).peer p false,
                           bta := Function.update (S.hub c).bta p 0 })
      ?_ (fun _ => rfl) rfl, ?_, ?_, ?_⟩
  · intro q hq'
    simp only [List.mem_singleton] at hq'
    subst hq'
    exact ⟨hpc, hpl, fun _ => hsl⟩
  · simp [hq]
  · simp
  · simp
  · simp [clearAllowed]

/-- An entry that does not write `isPeerAllowed[p]` leaves it as it is. -/
theorem run_peer_of_peerWrite_none {c p : ChainId} {m : Msg} {h h' : Hub}
    (hrun : m.run c h = some h') (hw : m.peerWrite p = none) : h'.peer p = h.peer p := by
  cases m with
  | allow q a s =>
    simp only [Msg.run] at hrun
    split_ifs at hrun
    simp only [Option.some.injEq] at hrun
    subst hrun
    have hqp : p ≠ q := by
      rintro rfl; simp [Msg.peerWrite] at hw
    simp [Function.update_of_ne hqp]
  | dereg q =>
    simp only [Msg.run, Option.some.injEq] at hrun
    subst hrun
    have hqp : p ≠ q := by
      rintro rfl; simp [Msg.peerWrite] at hw
    simp [Function.update_of_ne hqp]
  | legacy q a =>
    simp only [Msg.run, Option.some.injEq] at hrun
    subst hrun; rfl
  | mint q a =>
    simp only [Msg.run] at hrun
    split_ifs at hrun
    simp only [Option.some.injEq] at hrun
    subst hrun; rfl
  | other =>
    simp only [Msg.run, Option.some.injEq] at hrun
    subst hrun; rfl

/-- Appending entries that do not write `isPeerAllowed[p]` keeps a queue free of such entries. -/
theorem noPending_enqueue {Q : ChainId → List Msg} {c c' p : ChainId} {ms : List Msg}
    (h : NoPendingPeerEntry p (Q c)) (hms : c = c' → ∀ m ∈ ms, m.peerWrite p = none) :
    NoPendingPeerEntry p (Function.update Q c' (Q c' ++ ms) c) := by
  intro m hm
  by_cases hcc : c = c'
  · subst hcc
    rw [Function.update_self] at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h m hm
    · exact hms rfl m hm
  · rw [Function.update_of_ne hcc] at hm
    exact h m hm

/-- Removing an entry keeps a queue free of entries writing `isPeerAllowed[p]`. -/
theorem noPending_pop {Q : ChainId → List Msg} {c c' p : ChainId} {pre post : List Msg} {m : Msg}
    (hq : Q c' = pre ++ m :: post) (h : NoPendingPeerEntry p (Q c)) :
    NoPendingPeerEntry p (Function.update Q c' (pre ++ post) c) := by
  intro m' hm'
  by_cases hcc : c = c'
  · subst hcc
    rw [Function.update_self] at hm'
    apply h m'
    rw [hq]
    rcases List.mem_append.mp hm' with h1 | h1
    · exact List.mem_append_left _ h1
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h1)
  · rw [Function.update_of_ne hcc] at hm'
    exact h m' hm'

theorem DisallowedPeerFlagFrozenWhileOnLayer :
    Properties.DisallowedPeerFlagFrozenWhileOnLayer := by
  intro P S S' a c p hs hsl hal hnone
  cases hs with
  | createChain => exact ⟨rfl, hal, hnone⟩
  | enableInterop => exact ⟨rfl, hal, hnone⟩
  | pushBatch => exact ⟨rfl, hal, hnone⟩
  | allowInteropPeer h1 h2 h3 h4 h5 h6 h7 h8 =>
    rename_i c' q
    have hne : ¬ (c = c' ∧ p = q) := by
      rintro ⟨rfl, rfl⟩; exact h2.2.2 hsl
    refine ⟨rfl, ?_, noPending_enqueue hnone ?_⟩
    · show setAllowed S.l1.allowed c' q c p = false
      simp [setAllowed, hne, hal]
    · intro hcc m hm
      simp only [List.mem_singleton] at hm
      subst hm
      have hqp : q ≠ p := fun h => hne ⟨hcc, h.symm⟩
      simp [Msg.peerWrite, hqp]
  | deregisterInteropPairs h1 h2 =>
    rename_i c' ps
    have hp : c = c' → p ∉ ps := by
      intro hcc hp
      exact (h2 p hp).2.2 rfl (hcc ▸ hsl)
    refine ⟨rfl, ?_, noPending_enqueue hnone ?_⟩
    · show clearAllowed S.l1.allowed c' ps c p = false
      simp only [clearAllowed]; split_ifs <;> simp [hal]
    · intro hcc m hm
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
      have hqp : q ≠ p := fun h => hp hcc (h ▸ hq)
      simp [Msg.peerWrite, hqp]
  | resubmit h1 h2 h3 h4 =>
    rename_i c' q
    refine ⟨rfl, hal, noPending_enqueue hnone ?_⟩
    intro hcc m hm
    simp only [List.mem_singleton] at hm
    subst hm
    have hqp : q ≠ p := by
      rintro rfl; rw [← hcc, hal] at h2; cases h2
    simp [Msg.peerWrite, hqp]
  | legacyRegister =>
    refine ⟨rfl, hal, noPending_enqueue hnone ?_⟩
    intro _ m hm
    simp only [List.mem_singleton] at hm
    subst hm; rfl
  | otherRequest =>
    refine ⟨rfl, hal, noPending_enqueue hnone ?_⟩
    intro _ m hm
    simp only [List.mem_singleton] at hm
    subst hm; rfl
  | executeOk hq hfifo hrun =>
    rename_i c' pre post m h
    refine ⟨?_, hal, noPending_pop hq hnone⟩
    show (Function.update S.hub c' h c).peer p = (S.hub c).peer p
    by_cases hcc : c = c'
    · subst hcc
      rw [Function.update_self]
      exact run_peer_of_peerWrite_none hrun (hnone m (by rw [hq]; simp))
    · rw [Function.update_of_ne hcc]
  | executeFail hq hfifo => exact ⟨rfl, hal, noPending_pop hq hnone⟩
  | migrateToLayer =>
    refine ⟨rfl, hal, noPending_enqueue hnone ?_⟩
    intro _ m hm
    simp only [List.mem_singleton] at hm
    subst hm; rfl
  | burnOnLayer hb1 hb2 =>
    rename_i q c'
    refine ⟨?_, hal, hnone⟩
    show (Function.update S.hub c' _ c).peer p = (S.hub c).peer p
    by_cases hcc : c = c'
    · subst hcc; rw [Function.update_self]
    · rw [Function.update_of_ne hcc]
  | finalizeReturn => exact ⟨rfl, hal, hnone⟩
  | confirmFailedMigration => exact ⟨rfl, hal, hnone⟩

/-- While L1 records `p` on `c`, `deregisterInteropPairs(c, ps)` with `p ∈ ps` reverts
(`_checkPeerPair`, `CRS:108`, `:178`). -/
theorem not_step_deregisterInteropPairs_of_layer {P : Params} {S S' : State} {c p : ChainId}
    {ps : List ChainId} (hsl : S.l1.sl p = c) (hp : p ∈ ps) :
    ¬ Step deployed P S (.deregisterInteropPairs c ps) S' := by
  intro hs
  cases hs with
  | deregisterInteropPairs _ hok => exact (hok p hp).2.2 rfl hsl

/-- While L1 records `p` on `c`, `allowInteropPeer(c, p)` reverts (`_checkPeerPair`, `CRS:81`,
`:178`). -/
theorem not_step_allowInteropPeer_of_layer {K : Config} {P : Params} {S S' : State}
    {c p : ChainId} (hsl : S.l1.sl p = c) : ¬ Step K P S (.allowInteropPeer c p) S' := by
  intro hs
  cases hs with
  | allowInteropPeer _ hpp => exact hpp.2.2 hsl

/-- Without the sender's flag, the re-submission reverts (`CRS:139-142`). -/
theorem not_step_resubmit_of_disallowed {K : Config} {P : Params} {S S' : State}
    {c p : ChainId} (ha : S.l1.allowed c p = false) : ¬ Step K P S (.resubmit c p) S' := by
  intro hs
  cases hs with
  | resubmit _ h2 => rw [ha] at h2; cases h2

/-! ## (b) The value of `baseTokenAssetId[p]` -/

theorem L2BaseTokenEntryIsZeroOrL1Value : Properties.L2BaseTokenEntryIsZeroOrL1Value := by
  intro P S hR c p
  exact (inv_reach hR).hubVal c p

theorem L1BaseTokenFixedOnceSet : Properties.L1BaseTokenFixedOnceSet := by
  intro P S S' a hR hs p hp
  exact bt_step (inv_reach hR) hs p hp

theorem L2BaseTokenEntryIsZeroOrCreationValue :
    Properties.L2BaseTokenEntryIsZeroOrCreationValue := by
  intro P S S' hR h c p hp
  rw [← bt_steps hR h p hp]
  exact (inv_reach (reach_of_steps hR h)).hubVal c p

/-! ## (c) Presence -/

theorem SettledChainEntryIsL1Value : Properties.SettledChainEntryIsL1Value := by
  intro P S hR c p hc hsl
  have hI := inv_reach hR
  have hmig := (hI.hubSettled c p hc).mp hsl
  obtain ⟨-, -, hpr⟩ := hI.layerReg p c (by rw [hmig]; rfl)
  exact ⟨(hI.settledEntry p c hmig).1, hI.regBt p hpr⟩

theorem ReturningChainEntryIsL1Value : Properties.ReturningChainEntryIsL1Value := by
  intro P S hR p c a hm
  have hI := inv_reach hR
  have ha := hI.retVal p c a hm
  obtain ⟨-, -, hpr⟩ := hI.layerReg p c (by rw [hm]; rfl)
  refine ⟨ha, ha ▸ hI.regBt p hpr, ?_⟩
  rw [(hI.returningEntry p c a hm).1, ha]

theorem ReturnCarriesL1BaseToken : Properties.ReturnCarriesL1BaseToken := by
  intro P S S' p c hR hs
  have hI := inv_reach hR
  cases hs with
  | burnOnLayer h1 h2 =>
  have hmig := (hI.hubSettled c p h1).mp h2
  obtain ⟨-, -, hpr⟩ := hI.layerReg p c (by rw [hmig]; rfl)
  refine ⟨?_, hI.regBt p hpr⟩
  show Function.update S.mig p (.returning c ((S.hub c).bta p)) p = .returning c (S.l1.bt p)
  rw [Function.update_self, (hI.settledEntry p c hmig).1]

theorem PendingArrivalCarriesL1Value : Properties.PendingArrivalCarriesL1Value := by
  intro P S hR p c hm
  have hI := inv_reach hR
  refine ⟨sl_of_layer hI (by rw [hm]; rfl), ?_⟩
  obtain ⟨pre, a, post, h1, h2⟩ := hI.mintingQueue p c hm
  have hcar : Carries S.l1 (.mint p a) := hI.queueVal c _ (by rw [h1]; simp)
  exact ⟨pre, post, a, h1, hcar.1, hcar.2, h2⟩

/-- Only an executed `deregisterChainForInterop(p)` turns `isPeerAllowed[p]` off. -/
theorem dereg_queued_of_peer_cleared {P : Params} {S S' : State} {a : Action}
    (hs : Step deployed P S a S') {c p : ChainId} (h1 : (S.hub c).peer p = true)
    (h2 : (S'.hub c).peer p = false) : Msg.dereg p ∈ S.queue c := by
  cases hs with
  | executeOk hq hfifo hrun =>
    rename_i c' pre post m h
    obtain rfl : pre = [] := hfifo rfl
    simp only [List.nil_append] at hq
    by_cases hcc : c = c'
    · subst hcc
      have h2' : h.peer p = false := by
        have := h2; simp only [Function.update_self] at this; exact this
      cases m with
      | allow q a s =>
        simp only [Msg.run] at hrun
        split_ifs at hrun
        simp only [Option.some.injEq] at hrun
        subst hrun
        by_cases hqp : p = q
        · subst hqp; simp at h2'
        · simp [Function.update_of_ne hqp, h1] at h2'
      | dereg q =>
        simp only [Msg.run, Option.some.injEq] at hrun
        subst hrun
        by_cases hqp : p = q
        · subst hqp; rw [hq]; exact List.mem_cons_self
        · simp [Function.update_of_ne hqp, h1] at h2'
      | legacy q a =>
        simp only [Msg.run, Option.some.injEq] at hrun
        subst hrun
        simp [h1] at h2'
      | mint q a =>
        simp only [Msg.run] at hrun
        split_ifs at hrun
        simp only [Option.some.injEq] at hrun
        subst hrun
        simp [h1] at h2'
      | other =>
        simp only [Msg.run, Option.some.injEq] at hrun
        subst hrun
        simp [h1] at h2'
    · have := h2
      simp only [Function.update_of_ne hcc] at this
      rw [h1] at this; cases this
  | burnOnLayer hb1 hb2 =>
    rename_i q c'
    by_cases hcc : c = c'
    · subst hcc
      have := h2
      simp only [Function.update_self] at this
      rw [h1] at this; cases this
    · have := h2
      simp only [Function.update_of_ne hcc] at this
      rw [h1] at this; cases this
  | _ => exact absurd (h1.symm.trans h2) (by simp)

theorem SettledEntryNeverChanges : Properties.SettledEntryNeverChanges := by
  intro P S S' a c p hR hs hc hsl hsl'
  have hI := inv_reach hR
  have hR' : Reach deployed P S' := Reach.step hR hs
  obtain ⟨e1, hbt⟩ := SettledChainEntryIsL1Value P S hR c p hc hsl
  obtain ⟨e2, -⟩ := SettledChainEntryIsL1Value P S' hR' c p (registered_step hs hc) hsl'
  refine ⟨by rw [e2, e1, bt_step hI hs p hbt], ?_⟩
  intro hpeer
  cases h : (S'.hub c).peer p with
  | true => rfl
  | false =>
    exfalso
    have hmig := (hI.hubSettled c p hc).mp hsl
    exact (hI.settledEntry p c hmig).2 (dereg_queued_of_peer_cleared hs hpeer h)

/-! ## (d) Deregistration after a return -/

theorem ReturnedPeerDeregistrationAccepted : Properties.ReturnedPeerDeregistrationAccepted := by
  intro P S c p hR hc hp hpc hsl
  have hI := inv_reach hR
  refine ⟨_, Step.deregisterInteropPairs hc ?_⟩
  intro q hq
  simp only [List.mem_singleton] at hq
  subst hq
  refine ⟨hpc, (hI.regNe q hp).2, fun _ => ?_⟩
  rw [hsl]
  exact Ne.symm (hI.regNe c hc).2

/-! ## An executable step, for the witness runs -/

/-- `Step` as a function: the post-state, or `none` if a guard fails. Proved sound by
`step_of_stepFn`. -/
def stepFn (K : Config) (P : Params) (S : State) : Action → Option State
  | .createChain p a =>
    if S.l1.registered p = false ∧ p ≠ 0 ∧ p ≠ P.l1 ∧ a ≠ 0 then
      some { S with l1 := { S.l1 with
        registered := Function.update S.l1.registered p true
        bt := Function.update S.l1.bt p a
        sl := Function.update S.l1.sl p P.l1 } }
    else none
  | .enableInterop c =>
    if S.l1.registered c = true then
      some { S with l1 := { S.l1 with
        interopEnabled := Function.update S.l1.interopEnabled c true } }
    else none
  | .pushBatch c =>
    if S.l1.registered c = true then
      some { S with l1 := { S.l1 with hasBatch := Function.update S.l1.hasBatch c true } }
    else none
  | .allowInteropPeer c p =>
    if S.l1.registered c = true ∧ (p ≠ c ∧ p ≠ P.l1 ∧ S.l1.sl p ≠ c) ∧
        S.l1.registered p = true ∧ S.l1.allowed c p = false ∧ S.l1.interopEnabled c = true ∧
        S.l1.interopEnabled p = true ∧ S.l1.bt p ≠ 0 ∧ S.l1.hasBatch p = true then
      some { S with
        l1 := { S.l1 with allowed := setAllowed S.l1.allowed c p }
        queue := Function.update S.queue c (S.queue c ++ [.allow p (S.l1.bt p) true]) }
    else none
  | .deregisterInteropPairs c ps =>
    if S.l1.registered c = true ∧ ps.all (fun p => decide (p ≠ c ∧ p ≠ P.l1 ∧
        (K.deregChecksSettlement = true → S.l1.sl p ≠ c))) = true then
      some { S with
        l1 := { S.l1 with allowed := clearAllowed S.l1.allowed c ps }
        queue := Function.update S.queue c (S.queue c ++ ps.map Msg.dereg) }
    else none
  | .resubmit c p =>
    if S.l1.registered c = true ∧ S.l1.allowed c p = true ∧ S.l1.bt p ≠ 0 ∧
        S.l1.hasBatch p = true then
      some { S with queue := Function.update S.queue c (S.queue c ++ [.allow p (S.l1.bt p) false]) }
    else none
  | .legacyRegister c p =>
    if S.l1.registered c = true ∧ S.l1.bt p ≠ 0 ∧ S.l1.hasBatch p = true then
      some { S with queue := Function.update S.queue c (S.queue c ++ [.legacy p (S.l1.bt p)]) }
    else none
  | .otherRequest c =>
    if S.l1.registered c = true then
      some { S with queue := Function.update S.queue c (S.queue c ++ [.other]) }
    else none
  | .execute c i ok =>
    if hg : i < (S.queue c).length ∧ (K.fifo = true → i = 0) then
      if ok then
        match ((S.queue c)[i]'hg.1).run c (S.hub c) with
        | some hb => some { S with
            hub := Function.update S.hub c hb
            queue := Function.update S.queue c ((S.queue c).take i ++ (S.queue c).drop (i + 1))
            done := Function.update S.done c (S.done c ++ [((S.queue c)[i]'hg.1, true)])
            mig := ((S.queue c)[i]'hg.1).migAfter c true S.mig }
        | none => none
      else some { S with
            queue := Function.update S.queue c ((S.queue c).take i ++ (S.queue c).drop (i + 1))
            done := Function.update S.done c (S.done c ++ [((S.queue c)[i]'hg.1, false)])
            mig := ((S.queue c)[i]'hg.1).migAfter c false S.mig }
    else none
  | .migrateToLayer p c =>
    if S.l1.registered p = true ∧ S.l1.registered c = true ∧ c ≠ p ∧ c ≠ P.l1 ∧
        S.l1.sl p = P.l1 then
      some { S with
        l1 := { S.l1 with sl := Function.update S.l1.sl p c }
        queue := Function.update S.queue c (S.queue c ++ [.mint p (S.l1.bt p)])
        mig := Function.update S.mig p (.minting c) }
    else none
  | .burnOnLayer p c =>
    if S.l1.registered c = true ∧ (S.hub c).sl p = c then
      some { S with
        hub := Function.update S.hub c { S.hub c with sl := Function.update (S.hub c).sl p P.l1 }
        mig := Function.update S.mig p (.returning c ((S.hub c).bta p)) }
    else none
  | .finalizeReturn p =>
    match S.mig p with
    | .returning _ a =>
      if S.l1.sl p ≠ P.l1 then
        some { S with
          l1 := { S.l1 with sl := Function.update S.l1.sl p P.l1, bt := Function.update S.l1.bt p a }
          mig := Function.update S.mig p .home }
      else none
    | _ => none
  | .confirmFailedMigration p =>
    match S.mig p with
    | .failed _ =>
      some { S with
        l1 := { S.l1 with sl := Function.update S.l1.sl p P.l1 }
        mig := Function.update S.mig p .home }
    | _ => none

theorem step_of_stepFn {K : Config} {P : Params} {S S' : State} {a : Action}
    (h : stepFn K P S a = some S') : Step K P S a S' := by
  cases a with
  | createChain p a =>
    simp only [stepFn] at h
    split_ifs at h with hg
    obtain rfl := Option.some.inj h
    exact Step.createChain hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
  | enableInterop c =>
    simp only [stepFn] at h
    split_ifs at h with hg
    obtain rfl := Option.some.inj h
    exact Step.enableInterop hg
  | pushBatch c =>
    simp only [stepFn] at h
    split_ifs at h with hg
    obtain rfl := Option.some.inj h
    exact Step.pushBatch hg
  | allowInteropPeer c p =>
    simp only [stepFn] at h
    split_ifs at h with hg
    obtain rfl := Option.some.inj h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hg
    exact Step.allowInteropPeer h1 h2 h3 h4 h5 h6 h7 h8
  | deregisterInteropPairs c ps =>
    simp only [stepFn] at h
    split_ifs at h with hg
    obtain rfl := Option.some.inj h
    refine Step.deregisterInteropPairs hg.1 ?_
    intro p hp
    have := List.all_eq_true.mp hg.2 p hp
    exact (of_decide_eq_true this : p ≠ c ∧ p ≠ P.l1 ∧ _)
  | resubmit c p =>
    simp only [stepFn] at h
    split_ifs at h with hg
    obtain rfl := Option.some.inj h
    exact Step.resubmit hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
  | legacyRegister c p =>
    simp only [stepFn] at h
    split_ifs at h with hg
    obtain rfl := Option.some.inj h
    exact Step.legacyRegister hg.1 hg.2.1 hg.2.2
  | otherRequest c =>
    simp only [stepFn] at h
    split_ifs at h with hg
    obtain rfl := Option.some.inj h
    exact Step.otherRequest hg
  | execute c i ok =>
    simp only [stepFn] at h
    by_cases hg : i < (S.queue c).length ∧ (K.fifo = true → i = 0)
    · rw [dite_eq_left hg] at h
      have hlen : ((S.queue c).take i).length = i := by
        simp [Nat.min_eq_left (le_of_lt hg.1)]
      have hq : S.queue c =
          (S.queue c).take i ++ (S.queue c)[i]'hg.1 :: (S.queue c).drop (i + 1) := by
        rw [← List.drop_eq_getElem_cons hg.1, List.take_append_drop]
      have hf : K.fifo = true → (S.queue c).take i = [] := by
        intro hk; rw [hg.2 hk]; simp
      cases ok with
      | true =>
        simp only [ite_true] at h
        cases hr : ((S.queue c)[i]'hg.1).run c (S.hub c) with
        | none => rw [hr] at h; cases h
        | some hb =>
          rw [hr] at h
          obtain rfl := Option.some.inj h
          have := Step.executeOk (K := K) (P := P) (h := hb) hq hf hr
          rwa [hlen] at this
      | false =>
        simp only [Bool.false_eq_true, ite_false] at h
        obtain rfl := Option.some.inj h
        have := Step.executeFail (K := K) (P := P) hq hf
        rwa [hlen] at this
    · simp [hg] at h
  | migrateToLayer p c =>
    simp only [stepFn] at h
    split_ifs at h with hg
    obtain rfl := Option.some.inj h
    obtain ⟨h1, h2, h3, h4, h5⟩ := hg
    exact Step.migrateToLayer h1 h2 h3 h4 h5
  | burnOnLayer p c =>
    simp only [stepFn] at h
    split_ifs at h with hg
    obtain rfl := Option.some.inj h
    exact Step.burnOnLayer hg.1 hg.2
  | finalizeReturn p =>
    simp only [stepFn] at h
    cases hm : S.mig p with
    | returning c a =>
      rw [hm] at h
      dsimp only at h
      split_ifs at h with hg
      obtain rfl := Option.some.inj h
      exact Step.finalizeReturn hm hg
    | home => rw [hm] at h; cases h
    | minting c => rw [hm] at h; cases h
    | settled c => rw [hm] at h; cases h
    | failed c => rw [hm] at h; cases h
  | confirmFailedMigration p =>
    simp only [stepFn] at h
    cases hm : S.mig p with
    | failed c =>
      rw [hm] at h
      dsimp only at h
      obtain rfl := Option.some.inj h
      exact Step.confirmFailedMigration hm
    | home => rw [hm] at h; cases h
    | minting c => rw [hm] at h; cases h
    | settled c => rw [hm] at h; cases h
    | returning c a => rw [hm] at h; cases h

/-- A list of transactions run from `S`, or `none` if one of them reverts. -/
def runFrom (K : Config) (P : Params) : State → List Action → Option State
  | S, [] => some S
  | S, a :: as => match stepFn K P S a with
    | some S' => runFrom K P S' as
    | none => none

theorem steps_of_runFrom {K : Config} {P : Params} :
    ∀ {S S' : State} {as : List Action}, runFrom K P S as = some S' → Steps K P S S'
  | S, S', [], h => by
    simp only [runFrom, Option.some.injEq] at h
    subst h
    exact Steps.refl S
  | S, S', a :: as, h => by
    simp only [runFrom] at h
    cases h1 : stepFn K P S a with
    | none => rw [h1] at h; cases h
    | some S₁ =>
      rw [h1] at h
      exact steps_head (step_of_stepFn h1) (steps_of_runFrom h)

theorem reach_of_runFrom {K : Config} {P : Params} {S : State} {as : List Action}
    (h : runFrom K P init as = some S) : Reach K P S :=
  reach_of_steps Reach.init (steps_of_runFrom h)

/-! ## Witness runs

L1 is chain `1`. Chain `2` (base-token asset id `10`) hosts the entries and is the settlement
layer of the migration runs; chain `3` (asset id `20`) is the peer. -/

/-- L1's chain id in the witnesses. -/
def wP : Params := ⟨1⟩

/-- Create chains `2` and `3`, enable both, give `3` a batch. -/
def runSetup : List Action :=
  [.createChain 2 10, .createChain 3 20, .enableInterop 2, .enableInterop 3, .pushBatch 3]

/-- The state a run of `K` from fresh storage ends in (`init` if a transaction reverts; each use
below proves that none does). -/
def runState (K : Config) (as : List Action) : State := (runFrom K wP init as).getD init

/-- `allowInteropPeer(2, 3)`, whose service transaction fails on chain `2`. -/
def runDesync : List Action := runSetup ++ [.allowInteropPeer 2 3, .execute 2 0 false]

/-- Then the re-submission, which succeeds. -/
def runRepaired : List Action := runDesync ++ [.resubmit 2 3, .execute 2 0 true]

/-- The service transaction succeeds; a later re-submission fails. -/
def runFailedResub : List Action :=
  runSetup ++ [.allowInteropPeer 2 3, .execute 2 0 true, .resubmit 2 3, .execute 2 0 false]

/-- Allow, then deregister; chain `2` executes the deregistration first. -/
def runOutOfOrder : List Action :=
  runSetup ++ [.allowInteropPeer 2 3, .deregisterInteropPairs 2 [3], .execute 2 1 true,
    .execute 2 0 true]

/-- Allow `(2, 3)`; then `3` migrates onto `2` and arrives. -/
def runArrived : List Action :=
  runSetup ++ [.allowInteropPeer 2 3, .execute 2 0 true, .migrateToLayer 3 2, .execute 2 0 true]

/-- While `3` settles on `2`, the pair is re-submitted. -/
def runResubSettled : List Action := runArrived ++ [.resubmit 2 3]

/-- `3` starts back to L1. -/
def runReturning : List Action := runArrived ++ [.burnOnLayer 3 2]

/-- `3`'s return is finalized on L1. -/
def runReturned : List Action := runReturning ++ [.finalizeReturn 3]

/-- `3` migrates onto `2`; the arrival is still queued. -/
def runPending : List Action := [.createChain 2 10, .createChain 3 20, .migrateToLayer 3 2]

/-- Without the settlement clause: `3` arrives on `2`, then the pair is deregistered. -/
def runNoCheck : List Action :=
  runPending ++ [.execute 2 0 true, .deregisterInteropPairs 2 [3], .execute 2 0 true]

/-- … and `3` starts back to L1. -/
def runNoCheckReturning : List Action := runNoCheck ++ [.burnOnLayer 3 2]

/-- Without FIFO: a deregistration queued before the arrival executes after it. -/
def runNoFifoSettled : List Action :=
  [.createChain 2 10, .createChain 3 20, .deregisterInteropPairs 2 [3], .migrateToLayer 3 2,
    .execute 2 1 true, .execute 2 0 true]

/-- The re-submission executes while `3` settles on `2`. -/
def runResubExecuted : List Action := runResubSettled ++ [.execute 2 0 true]

/-- Without the settlement clause, the return with a cleared entry is finalized. -/
def runNoCheckReturned : List Action := runNoCheckReturning ++ [.finalizeReturn 3]

/-- After `3` returned, the pair `(2, 3)` is deregistered … -/
def runDeregistered : List Action := runReturned ++ [.deregisterInteropPairs 2 [3]]

/-- … and chain `2` executes the deregistration. -/
def runCleared : List Action := runDeregistered ++ [.execute 2 0 true]

/-- The service transaction of `allowInteropPeer(2, 3)` fails; `3` then migrates onto `2` and
arrives; the pair is re-submitted. -/
def runLateResub : List Action :=
  runDesync ++ [.migrateToLayer 3 2, .execute 2 0 true, .resubmit 2 3]

/-- … and the re-submission executes. -/
def runLateResubExecuted : List Action := runLateResub ++ [.execute 2 0 true]

/-- `allowInteropPeer(2, 3)` succeeds on chain `2`; `deregisterInteropPairs(2, [3])` fails there. -/
def runFailedDereg : List Action :=
  runSetup ++ [.allowInteropPeer 2 3, .execute 2 0 true, .deregisterInteropPairs 2 [3],
    .execute 2 0 false]

/-- `allowInteropPeer(2, 3)` succeeds on chain `2`; `deregisterInteropPairs(2, [3])` is queued, `3`
migrates onto `2`, and the deregistration fails; the arrival is still queued. -/
def runFailedDeregArriving : List Action :=
  runSetup ++ [.allowInteropPeer 2 3, .execute 2 0 true, .deregisterInteropPairs 2 [3],
    .migrateToLayer 3 2, .execute 2 0 false]

/-- … and `3` arrives on `2`. -/
def runFailedDeregSettled : List Action := runFailedDeregArriving ++ [.execute 2 0 true]

theorem SettledPeerFlagCanTurnOn : Properties.SettledPeerFlagCanTurnOn :=
  ⟨wP, runState deployed runLateResub, runState deployed runLateResubExecuted, .execute 2 0 true,
    2, 3,
    reach_of_runFrom
      (rfl : runFrom deployed wP init runLateResub = some (runState deployed runLateResub)),
    step_of_stepFn (rfl : stepFn deployed wP (runState deployed runLateResub) (.execute 2 0 true) =
      some (runState deployed runLateResubExecuted)),
    by decide, by decide, by decide, by decide, by decide⟩

theorem FailedServiceEntryLeavesPeerFlagBehind :
    Properties.FailedServiceEntryLeavesPeerFlagBehind :=
  ⟨wP, runState deployed runDesync, 2, 3,
    reach_of_runFrom (rfl : runFrom deployed wP init runDesync = some (runState deployed runDesync)),
    by decide, by decide, by decide⟩

theorem FailedDeregLeavesPeerFlagOn : Properties.FailedDeregLeavesPeerFlagOn :=
  ⟨wP, runState deployed runFailedDereg, 2, 3,
    reach_of_runFrom
      (rfl : runFrom deployed wP init runFailedDereg = some (runState deployed runFailedDereg)),
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem FailedDeregRepairBlockedWhileSettled : Properties.FailedDeregRepairBlockedWhileSettled :=
  have hsl : (runState deployed runFailedDeregSettled).l1.sl 3 = 2 := by decide
  have hal : (runState deployed runFailedDeregSettled).l1.allowed 2 3 = false := by decide
  ⟨wP, runState deployed runFailedDeregSettled, 2, 3,
    reach_of_runFrom (rfl : runFrom deployed wP init runFailedDeregSettled =
      some (runState deployed runFailedDeregSettled)),
    by decide, by decide, hal, by decide, by decide, by decide, hsl,
    fun _ _ hp => not_step_deregisterInteropPairs_of_layer hsl hp,
    fun _ => not_step_allowInteropPeer_of_layer hsl,
    fun _ => not_step_resubmit_of_disallowed hal⟩

theorem DisallowedPeerFlagFrozenWitness : Properties.DisallowedPeerFlagFrozenWitness :=
  ⟨wP, runState deployed runFailedDeregArriving, runState deployed runFailedDeregSettled, 2, 3,
    reach_of_runFrom (rfl : runFrom deployed wP init runFailedDeregArriving =
      some (runState deployed runFailedDeregArriving)),
    step_of_stepFn (rfl : stepFn deployed wP (runState deployed runFailedDeregArriving)
      (.execute 2 0 true) = some (runState deployed runFailedDeregSettled)),
    by decide, by decide, by unfold NoPendingPeerEntry; decide, by decide, by decide, by decide,
    by decide⟩

theorem WithoutFifoPeerFlagDesyncs : Properties.WithoutFifoPeerFlagDesyncs :=
  ⟨wP, runState withoutFifo runOutOfOrder, 2, 3,
    reach_of_runFrom
      (rfl : runFrom withoutFifo wP init runOutOfOrder = some (runState withoutFifo runOutOfOrder)),
    by decide, by decide, by decide⟩

theorem MirrorAfterFailedServiceEntryWitness : Properties.MirrorAfterFailedServiceEntryWitness :=
  ⟨wP, runState deployed runRepaired, 2, 3,
    reach_of_runFrom
      (rfl : runFrom deployed wP init runRepaired = some (runState deployed runRepaired)),
    by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem MirrorAfterFailedResubmissionWitness :
    Properties.MirrorAfterFailedResubmissionWitness :=
  ⟨wP, runState deployed runFailedResub, 2, 3,
    reach_of_runFrom
      (rfl : runFrom deployed wP init runFailedResub = some (runState deployed runFailedResub)),
    by decide, by decide, by decide, by decide, by decide⟩

theorem BaseTokenEntryWitness : Properties.BaseTokenEntryWitness :=
  ⟨wP, runState deployed runRepaired, 2, 3,
    reach_of_runFrom
      (rfl : runFrom deployed wP init runRepaired = some (runState deployed runRepaired)),
    by decide, by decide, by decide⟩

theorem CreationValueWitness : Properties.CreationValueWitness :=
  ⟨wP, runState deployed [.createChain 2 10, .createChain 3 20], runState deployed runReturning,
    2, 3,
    reach_of_runFrom (rfl : runFrom deployed wP init [.createChain 2 10, .createChain 3 20] =
      some (runState deployed [.createChain 2 10, .createChain 3 20])),
    steps_of_runFrom (rfl : runFrom deployed wP
      (runState deployed [.createChain 2 10, .createChain 3 20])
      [.enableInterop 2, .enableInterop 3, .pushBatch 3, .allowInteropPeer 2 3, .execute 2 0 true,
        .migrateToLayer 3 2, .execute 2 0 true, .burnOnLayer 3 2] =
      some (runState deployed runReturning)),
    by decide, by decide, by decide, by decide⟩

theorem L1BaseTokenRewriteWitness : Properties.L1BaseTokenRewriteWitness :=
  ⟨wP, runState deployed runReturning, runState deployed runReturned, 3,
    reach_of_runFrom
      (rfl : runFrom deployed wP init runReturning = some (runState deployed runReturning)),
    step_of_stepFn (rfl : stepFn deployed wP (runState deployed runReturning) (.finalizeReturn 3) =
      some (runState deployed runReturned)),
    by decide⟩

theorem SettledEntryWitness : Properties.SettledEntryWitness :=
  ⟨wP, runState deployed runResubSettled,
    runState deployed runResubExecuted, 2, 3,
    reach_of_runFrom
      (rfl : runFrom deployed wP init runResubSettled = some (runState deployed runResubSettled)),
    by decide, by decide, by decide,
    step_of_stepFn (rfl : stepFn deployed wP (runState deployed runResubSettled)
      (.execute 2 0 true) = some (runState deployed runResubExecuted)),
    by decide, by decide⟩

theorem ReturnWitness : Properties.ReturnWitness :=
  have h1 : Reach deployed wP (runState deployed runArrived) :=
    reach_of_runFrom
      (rfl : runFrom deployed wP init runArrived = some (runState deployed runArrived))
  have h2 : Step deployed wP (runState deployed runArrived) (.burnOnLayer 3 2)
      (runState deployed runReturning) :=
    step_of_stepFn (rfl : stepFn deployed wP (runState deployed runArrived) (.burnOnLayer 3 2) =
      some (runState deployed runReturning))
  ⟨wP, _, _, 3, 2, h1, h2, Reach.step h1 h2, 20, by decide⟩

theorem PendingArrivalEntryMayBeZero : Properties.PendingArrivalEntryMayBeZero :=
  ⟨wP, runState deployed runPending, 3, 2,
    reach_of_runFrom
      (rfl : runFrom deployed wP init runPending = some (runState deployed runPending)),
    by decide, by decide, by decide, by decide⟩

theorem WithoutDeregSettlementCheckSettledEntryCleared :
    Properties.WithoutDeregSettlementCheckSettledEntryCleared :=
  ⟨wP, runState withoutDeregSettlementCheck runNoCheck, 2, 3,
    reach_of_runFrom (rfl : runFrom withoutDeregSettlementCheck wP init runNoCheck =
      some (runState withoutDeregSettlementCheck runNoCheck)),
    by decide, by decide, by decide⟩

theorem WithoutDeregSettlementCheckL1BaseTokenRewritten :
    Properties.WithoutDeregSettlementCheckL1BaseTokenRewritten :=
  ⟨wP, runState withoutDeregSettlementCheck runNoCheckReturning,
    runState withoutDeregSettlementCheck runNoCheckReturned,
    .finalizeReturn 3, 3,
    reach_of_runFrom (rfl : runFrom withoutDeregSettlementCheck wP init runNoCheckReturning =
      some (runState withoutDeregSettlementCheck runNoCheckReturning)),
    step_of_stepFn (rfl : stepFn withoutDeregSettlementCheck wP
      (runState withoutDeregSettlementCheck runNoCheckReturning) (.finalizeReturn 3) =
      some (runState withoutDeregSettlementCheck runNoCheckReturned)),
    by decide, by decide⟩

theorem WithoutFifoSettledEntryCleared : Properties.WithoutFifoSettledEntryCleared :=
  ⟨wP, runState withoutFifo runNoFifoSettled, 2, 3,
    reach_of_runFrom (rfl : runFrom withoutFifo wP init runNoFifoSettled =
      some (runState withoutFifo runNoFifoSettled)),
    by decide, by decide, by decide⟩

theorem ReturnedPeerEntryCanBeCleared : Properties.ReturnedPeerEntryCanBeCleared :=
  ⟨wP, runState deployed runReturned,
    runState deployed runDeregistered,
    runState deployed runCleared, 2, 3,
    reach_of_runFrom
      (rfl : runFrom deployed wP init runReturned = some (runState deployed runReturned)),
    by decide, by decide, by decide, by decide, by decide, by decide,
    step_of_stepFn (rfl : stepFn deployed wP (runState deployed runReturned)
      (.deregisterInteropPairs 2 [3]) =
      some (runState deployed runDeregistered)),
    step_of_stepFn (rfl : stepFn deployed wP
      (runState deployed runDeregistered) (.execute 2 0 true) =
      some (runState deployed runCleared)),
    by decide, by decide⟩

end Contracts.InteropPeerRegistry
