import EraSpec.Protocol.PriorityRequests.Properties.PrivilegedSenders
import EraSpec.Contracts.MailboxFacet.Proofs.RequestPaths

/-!
# Proofs: who appends priority operations on L1, and the two privileged senders

The run invariant `Inv` says the roles are genuine, `SysWF` holds, and every logged push satisfies
`PushOk` relative to the pushes before it. `PushOk` bundles the four run-level headlines. Each
composed Mailbox operation (`relayCall`, `serviceCall`, `userCall`) preserves the log part given what
its caller guarantees (`relayCall_logOk`, `serviceCall_logOk`, `userCall_logOk`), and keeps the
Bridgehub and the diamonds' chain ids (`OpFrame`). Each step then discharges those guarantees: the
user steps from the account premises (`l2Sender_ne_of_unreachable`, `l2Sender_ne_alias_crs`), the
service steps from the three fixed calldata, and the direct calls by actors are impossible under
the genuine roles, `SysWF` and the account premises (`step_inv`).

The facts at the time of a push are per step. `userCall_new` and `serviceCall_new` list what one
request appends (its own push, then relay pushes only), `PushFrame` says pushes keep the flags and
pause timestamps, and `RelayCtx` carries the relay context through the operations of one step.
The witness run is evaluated by the kernel (`rfl`, `decide`).
-/

namespace Contracts.PriorityRequests

open Contracts.MailboxFacet.RequestPaths

/-! ## Operation destructors -/

theorem relayCall_some {P : SysParams} {S : System} {env : Env} {held : Option Address}
    {G caller : Address} {c : ℕ} {h : Word} {e : ℕ} {S' : System}
    (H : relayCall P S env held G caller c h e = some S') :
    ∃ dG tx h', S.diamonds G = some dG ∧ env.onL1 P.mb ∧ S.whitelistedSL dG.chainId = true ∧
      S.zkChain c = caller ∧ e = 0 ∧ held ≠ some G ∧
      requestL2TransactionFree P.mb dG env (wrapRequest P.mb c h e) =
        some (dG.pushLeaf h' env.timestamp, tx, h') ∧
      S' = (S.withDiamond G (dG.pushLeaf h' env.timestamp)).appendPush
        (mkPush S G dG (some tx) h' .free) := by
  unfold relayCall at H
  split at H
  · contradiction
  · rename_i dG hG
    split_ifs at H with h1 h2 h3 h4 h5
    split at H
    · contradiction
    · rename_i dG' tx h' hF
      cases H
      have hd := (requestL2TransactionFree_some hF).2.2.2
      subst hd
      refine ⟨dG, tx, h', hG, by simpa using h1, by simpa using h2, by simpa using h3,
        by simpa using h4, h5, hF, rfl⟩

theorem relayIfSettled_some {P : SysParams} {S : System} {env : Env} {held : Option Address}
    {D : Address} {dD : Diamond} {h : Word} {S' : System}
    (H : relayIfSettled P S env held D dD h = some S') :
    (dD.settlementLayer = 0 ∧ S' = S) ∨
      (dD.settlementLayer ≠ 0 ∧
        relayCall P S env held dD.settlementLayer D dD.chainId h 0 = some S') := by
  unfold relayIfSettled at H
  split_ifs at H with h1
  · cases H; exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr ⟨h1, H⟩

theorem serviceCall_some {P : SysParams} {S : System} {env : Env} {G caller target : Address}
    {data : Bytes} {S' : System}
    (H : serviceCall P S env G caller target data = some S') :
    ∃ dG tx h, S.diamonds G = some dG ∧ (caller = S.crsRole ∨ caller = S.cahRole) ∧
      env.onL1 P.mb ∧
      requestL2TransactionFree P.mb dG env (serviceRequest target data) =
        some (dG.pushLeaf h env.timestamp, tx, h) ∧
      relayIfSettled P ((S.withDiamond G (dG.pushLeaf h env.timestamp)).appendPush
        (mkPush S G dG (some tx) h .free)) env none G dG h = some S' := by
  unfold serviceCall at H
  split at H
  · contradiction
  · rename_i dG hG
    split_ifs at H with h1 h2
    split at H
    · contradiction
    · rename_i dG' tx h hF
      have hd := (requestL2TransactionFree_some hF).2.2.2
      subst hd
      refine ⟨dG, tx, h, hG, ?_, by simpa using h2, hF, H⟩
      by_contra hc
      exact h1 ⟨fun e => hc (Or.inl e), fun e => hc (Or.inr e)⟩

theorem userCall_some {P : SysParams} {S : System} {env : Env} {D : Address} {req : Request}
    {S' : System} (H : userCall P S env D req = some S') :
    ∃ dD tx h, S.diamonds D = some dD ∧
      requestL2TransactionSender P.mb dD env req = some (dD.pushLeaf h env.timestamp, tx, h) ∧
      relayIfSettled P ((S.withDiamond D (dD.pushLeaf h env.timestamp)).appendPush
        (mkPush S D dD (some tx) h .user)) env (some D) D dD h = some S' := by
  unfold userCall at H
  split at H
  · contradiction
  · rename_i dD hD
    split at H
    · contradiction
    · rename_i dD' tx h hF
      have hd := (requestL2TransactionSender_some hF).2.2.choose_spec.2.2.2.2
      subst hd
      exact ⟨dD, tx, h, hD, hF, H⟩

theorem onGatewayCall_caller {S : System} {env : Env} {caller D : Address} {h : Word}
    {S' : System} (H : onGatewayCall S env caller D h = some S') :
    caller = l2InteropCenterAddr := by
  unfold onGatewayCall at H
  split_ifs at H with h1
  simpa using h1

theorem cahPause_some {P : SysParams} {S : System} {env : Env} {caller : Address} {c : ℕ}
    {S' : System} (H : cahPause P S env caller c = some S') :
    caller = S.zkChain c ∧ S.settlementLayerOf c ≠ env.chainId ∧
      serviceCall P S env (S.zkChain (S.settlementLayerOf c)) P.cah l2ChainAssetHandlerAddr
        (P.encPause c) = some S' := by
  unfold cahPause at H
  split_ifs at H with h1 h2
  exact ⟨by simpa using h1, h2, H⟩

/-! ## The frame of an operation -/

/-- What an operation keeps: the Bridgehub, the step counter, the set of diamonds and their chain
ids; the log only grows. -/
structure OpFrame (S S' : System) : Prop where
  zkChain : S'.zkChain = S.zkChain
  bt : S'.baseTokenAssetId = S.baseTokenAssetId
  sl : S'.settlementLayerOf = S.settlementLayerOf
  wl : S'.whitelistedSL = S.whitelistedSL
  crsRole : S'.crsRole = S.crsRole
  cahRole : S'.cahRole = S.cahRole
  txNo : S'.txNo = S.txNo
  dom : ∀ a, S'.diamonds a = none ↔ S.diamonds a = none
  chainIds : ∀ a d, S.diamonds a = some d → ∃ d', S'.diamonds a = some d' ∧ d'.chainId = d.chainId
  prefix_ : S.log <+: S'.log

theorem OpFrame.refl (S : System) : OpFrame S S :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => Iff.rfl, fun _ d h => ⟨d, h, rfl⟩,
    List.prefix_refl _⟩

theorem OpFrame.trans {S T U : System} (h1 : OpFrame S T) (h2 : OpFrame T U) : OpFrame S U where
  zkChain := h2.zkChain.trans h1.zkChain
  bt := h2.bt.trans h1.bt
  sl := h2.sl.trans h1.sl
  wl := h2.wl.trans h1.wl
  crsRole := h2.crsRole.trans h1.crsRole
  cahRole := h2.cahRole.trans h1.cahRole
  txNo := h2.txNo.trans h1.txNo
  dom := fun a => (h2.dom a).trans (h1.dom a)
  chainIds := fun a d hd => by
    obtain ⟨d1, hd1, hc1⟩ := h1.chainIds a d hd
    obtain ⟨d2, hd2, hc2⟩ := h2.chainIds a d1 hd1
    exact ⟨d2, hd2, hc2.trans hc1⟩
  prefix_ := h1.prefix_.trans h2.prefix_

theorem opFrame_withDiamond {S : System} {a : Address} {d d' : Diamond}
    (hd : S.diamonds a = some d) (hc : d'.chainId = d.chainId) :
    OpFrame S (S.withDiamond a d') where
  zkChain := rfl
  bt := rfl
  sl := rfl
  wl := rfl
  crsRole := rfl
  cahRole := rfl
  txNo := rfl
  dom := fun b => by
    by_cases hb : b = a
    · subst hb; simp [System.withDiamond, hd]
    · simp [System.withDiamond, Function.update_of_ne hb]
  chainIds := fun b e he => by
    by_cases hb : b = a
    · subst hb; rw [hd] at he; cases he
      exact ⟨d', by simp [System.withDiamond], hc⟩
    · exact ⟨e, by simp [System.withDiamond, Function.update_of_ne hb, he], rfl⟩
  prefix_ := List.prefix_refl _

theorem opFrame_appendPush (S : System) (p : Push) : OpFrame S (S.appendPush p) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => Iff.rfl, fun _ d h => ⟨d, h, rfl⟩,
    List.prefix_append _ _⟩

theorem opFrame_peers (S : System) (f : ℕ → ℕ → Bool) :
    OpFrame S { S with interopPeerAllowed := f } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => Iff.rfl, fun _ d h => ⟨d, h, rfl⟩,
    List.prefix_refl _⟩

theorem opFrame_push {S : System} {a : Address} {d : Diamond} (hd : S.diamonds a = some d)
    (h : Word) (t : ℕ) (p : Push) :
    OpFrame S ((S.withDiamond a (d.pushLeaf h t)).appendPush p) :=
  (opFrame_withDiamond (d' := d.pushLeaf h t) hd rfl).trans (opFrame_appendPush _ p)

theorem relayCall_frame {P : SysParams} {S : System} {env : Env} {held : Option Address}
    {G caller : Address} {c : ℕ} {h : Word} {e : ℕ} {S' : System}
    (H : relayCall P S env held G caller c h e = some S') : OpFrame S S' := by
  obtain ⟨dG, tx, h', hG, -, -, -, -, -, -, rfl⟩ := relayCall_some H
  exact opFrame_push hG _ _ _

theorem relayIfSettled_frame {P : SysParams} {S : System} {env : Env} {held : Option Address}
    {D : Address} {dD : Diamond} {h : Word} {S' : System}
    (H : relayIfSettled P S env held D dD h = some S') : OpFrame S S' := by
  rcases relayIfSettled_some H with ⟨-, rfl⟩ | ⟨-, H'⟩
  · exact OpFrame.refl _
  · exact relayCall_frame H'

theorem serviceCall_frame {P : SysParams} {S : System} {env : Env} {G caller target : Address}
    {data : Bytes} {S' : System} (H : serviceCall P S env G caller target data = some S') :
    OpFrame S S' := by
  obtain ⟨dG, tx, h, hG, -, -, -, hR⟩ := serviceCall_some H
  exact (opFrame_push hG _ _ _).trans (relayIfSettled_frame hR)

theorem userCall_frame {P : SysParams} {S : System} {env : Env} {D : Address} {req : Request}
    {S' : System} (H : userCall P S env D req = some S') : OpFrame S S' := by
  obtain ⟨dD, tx, h, hD, -, hR⟩ := userCall_some H
  exact (opFrame_push hD _ _ _).trans (relayIfSettled_frame hR)

theorem cahPause_frame {P : SysParams} {S : System} {env : Env} {caller : Address} {c : ℕ}
    {S' : System} (H : cahPause P S env caller c = some S') : OpFrame S S' :=
  serviceCall_frame (cahPause_some H).2.2

theorem OpFrame.wf {S S' : System} (F : OpFrame S S') (W : SysWF S) : SysWF S' where
  noDiamondAtZero := (F.dom 0).mpr W.noDiamondAtZero
  registered := fun c hc => by
    rw [F.zkChain] at hc ⊢
    obtain ⟨d, hd, hdc⟩ := W.registered c hc
    obtain ⟨d', hd', hc'⟩ := F.chainIds _ d hd
    exact ⟨d', hd', hc'.trans hdc⟩

/-! ## The log invariant -/

/-- A service call's target and calldata are one of the three fixed purposes. -/
def ServicePurpose (P : SysParams) (target : Address) (data : Bytes) : Prop :=
  (target = l2BridgehubAddr ∧
      ((∃ p a, a ≠ 0 ∧ data = P.encAllowPeer p a) ∨ ∃ p, data = P.encDeregister p)) ∨
    (target = l2ChainAssetHandlerAddr ∧ ∃ c, data = P.encPause c)

/-- What every logged push satisfies, given the pushes before it. -/
def PushOk (P : SysParams) (pre : List Push) (p : Push) : Prop :=
  ∃ tx, p.tx = some tx ∧ p.leaf = P.mb.txHash tx ∧ tx.nonce = p.index ∧
    tx.gasPerPubdataByteLimit = requiredGasPerPubdata ∧ tx.factoryDeps = [] ∧ p.kind ≠ .gateway ∧
    (tx.fromAddr = relaySender → p.kind = .free ∧ RelayShape P pre p tx) ∧
    (tx.fromAddr = serviceSender → p.kind = .free ∧ ServiceShape P tx) ∧
    (tx.fromAddr = applyL1ToL2Alias P.crs → p.kind = .user ∧ RegistrationShape P tx) ∧
    (p.kind = .user → tx.fromAddr ≠ relaySender ∧ tx.fromAddr ≠ serviceSender)

/-- Every push of the log satisfies `PushOk` relative to the pushes before it. -/
def LogOk (P : SysParams) (log : List Push) : Prop :=
  ∀ i (hi : i < log.length), PushOk P (log.take i) log[i]

theorem logOk_nil (P : SysParams) : LogOk P [] := by
  intro i hi; simp at hi

theorem logOk_append {P : SysParams} {l : List Push} {p : Push} :
    LogOk P (l ++ [p]) ↔ LogOk P l ∧ PushOk P l p := by
  constructor
  · intro H
    refine ⟨fun i hi => ?_, ?_⟩
    · have := H i (by simp; omega)
      rwa [List.take_append_of_le_length (by omega), List.getElem_append_left hi] at this
    · have := H l.length (by simp)
      rw [List.take_left' rfl, List.getElem_append_right (by omega)] at this
      simpa using this
  · rintro ⟨H, hp⟩ i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < l.length
    · rw [List.take_append_of_le_length (by omega), List.getElem_append_left hlt]
      exact H i hlt
    · have hi' : i = l.length := by omega
      subst hi'
      rw [List.take_left' rfl, List.getElem_append_right (by omega)]
      simpa using hp

/-- The two privileged senders differ. -/
theorem relaySender_ne_serviceSender : relaySender ≠ serviceSender := by decide

/-- The alias of a contract at a reachable position is not an unreachable address. -/
theorem alias_ne_of_contract {A : Accounts} {a C : Address} (hc : A.contract a)
    (hC : Unreachable A C) : applyL1ToL2Alias a ≠ C := by
  intro h
  apply hC.2
  rw [← h, undo_apply]
  exact hc

theorem appendPush_log (S : System) (a : Address) (d : Diamond) (p : Push) :
    ((S.withDiamond a d).appendPush p).log = S.log ++ [p] := rfl

/-- The relay push satisfies `PushOk` after a push `q` with leaf `h` by chain `c`. -/
theorem relayCall_logOk {P : SysParams} {S : System} {env : Env} {held : Option Address}
    {G caller : Address} {c : ℕ} {h : Word} {S' : System}
    (H : relayCall P S env held G caller c h 0 = some S') (hL : LogOk P S.log)
    (hq : ∃ q, S.log.getLast? = some q ∧ q.txNo = S.txNo ∧ q.kind ≠ .gateway ∧ q.chainId = c ∧
      q.leaf = h)
    (hrc : relaySender ≠ applyL1ToL2Alias P.crs) : LogOk P S'.log := by
  obtain ⟨dG, tx, h', hG, -, -, -, -, -, hF, rfl⟩ := relayCall_some H
  obtain ⟨-, rfl, hn, hfrom, hto, hdata, hr0, hv, hfee, -, -, hgpp⟩ :=
    RelayRequestShape P.mb dG env c h 0 _ tx h' hF
  have hfd := (FreeRequestExact P.mb dG env _ _ tx _ hF).2.2.2.2.1
  rw [appendPush_log]
  refine logOk_append.mpr ⟨hL, tx, rfl, rfl, hn, hgpp, hfd, by simp [mkPush], ?_, ?_, ?_, ?_⟩
  · intro _
    obtain ⟨q, hq1, hq2, hq3, hq4, hq5⟩ := hq
    refine ⟨rfl, ⟨hr0, hv, hfee⟩, hto, q, hq1, hq2, hq3, ?_⟩
    rw [hdata, hq4, hq5]
  · intro hs; exact absurd (hfrom.symm.trans hs) relaySender_ne_serviceSender
  · intro hs; exact absurd (hfrom.symm.trans hs) hrc
  · intro hk; simp [mkPush] at hk

/-- After a push `q` by `D` with leaf `h`, the optional relay keeps the invariant. -/
theorem relayIfSettled_logOk {P : SysParams} {S : System} {env : Env} {held : Option Address}
    {D : Address} {dD : Diamond} {h : Word} {S' : System}
    (H : relayIfSettled P S env held D dD h = some S') (hL : LogOk P S.log)
    (hq : ∃ q, S.log.getLast? = some q ∧ q.txNo = S.txNo ∧ q.kind ≠ .gateway ∧
      q.chainId = dD.chainId ∧ q.leaf = h)
    (hrc : relaySender ≠ applyL1ToL2Alias P.crs) : LogOk P S'.log := by
  rcases relayIfSettled_some H with ⟨-, rfl⟩ | ⟨-, H'⟩
  · exact hL
  · exact relayCall_logOk H' hL hq hrc

/-- A service call with one of the fixed purposes keeps the invariant. -/
theorem serviceCall_logOk {P : SysParams} {S : System} {env : Env} {G caller target : Address}
    {data : Bytes} {S' : System} (H : serviceCall P S env G caller target data = some S')
    (hL : LogOk P S.log) (hpur : ServicePurpose P target data)
    (hrc : relaySender ≠ applyL1ToL2Alias P.crs) (hsc : serviceSender ≠ applyL1ToL2Alias P.crs) :
    LogOk P S'.log := by
  obtain ⟨dG, tx, h, hG, -, -, hF, hR⟩ := serviceCall_some H
  obtain ⟨-, rfl, hn, hfrom, hto, hdata, hr0, hv, hfee, -, -, hgpp⟩ :=
    ServiceRequestShape P.mb dG env target data _ tx h hF
  have hfd := (FreeRequestExact P.mb dG env _ _ tx _ hF).2.2.2.2.1
  have hL1 : LogOk P (S.log ++ [mkPush S G dG (some tx) (P.mb.txHash tx) .free]) := by
    refine logOk_append.mpr ⟨hL, tx, rfl, rfl, hn, hgpp, hfd, by simp [mkPush], ?_, ?_, ?_, ?_⟩
    · intro hs; exact absurd (hfrom.symm.trans hs) relaySender_ne_serviceSender.symm
    · intro _
      refine ⟨rfl, ⟨hr0, hv, hfee⟩, ?_⟩
      rcases hpur with ⟨ht, hd⟩ | ⟨ht, hd⟩
      · exact Or.inl ⟨hto.trans ht, hdata ▸ hd⟩
      · exact Or.inr ⟨hto.trans ht, hdata ▸ hd⟩
    · intro hs; exact absurd (hfrom.symm.trans hs) hsc
    · intro hk; simp [mkPush] at hk
  refine relayIfSettled_logOk hR hL1
    ⟨mkPush S G dG (some tx) (P.mb.txHash tx) .free, ?_, rfl, by simp [mkPush], rfl, rfl⟩ hrc
  simp [System.appendPush, System.withDiamond]

/-- A user call whose `from` is neither privileged sender, and whose `from` is the aliased
registration sender only for a registration, keeps the invariant. -/
theorem userCall_logOk {P : SysParams} {S : System} {env : Env} {D : Address} {req : Request}
    {S' : System} (H : userCall P S env D req = some S') (hL : LogOk P S.log)
    (hs : l2Sender P.mb env req.sender ≠ relaySender ∧
      l2Sender P.mb env req.sender ≠ serviceSender)
    (hreg : l2Sender P.mb env req.sender = applyL1ToL2Alias P.crs →
      req.contractL2 = l2BridgehubAddr ∧ ∃ p a, a ≠ 0 ∧ req.l2Calldata = P.encAllowPeer p a)
    (hrc : relaySender ≠ applyL1ToL2Alias P.crs) : LogOk P S'.log := by
  obtain ⟨dD, tx, h, hD, hF, hR⟩ := userCall_some H
  obtain ⟨-, rfl, hn, hgpp, hfd, -, hto, hdata, -, -, -, -⟩ :=
    UserRequestExact P.mb dD env req _ tx h hF
  have hfrom := userRequest_from hF
  have hL1 : LogOk P (S.log ++ [mkPush S D dD (some tx) (P.mb.txHash tx) .user]) := by
    refine logOk_append.mpr ⟨hL, tx, rfl, rfl, hn, hgpp, hfd, by simp [mkPush], ?_, ?_, ?_, ?_⟩
    · intro hr; exact absurd (hfrom.symm.trans hr) hs.1
    · intro hr; exact absurd (hfrom.symm.trans hr) hs.2
    · intro hr
      obtain ⟨ht, hd⟩ := hreg (hfrom.symm.trans hr)
      exact ⟨rfl, hto.trans ht, hdata ▸ hd⟩
    · intro _; exact ⟨hfrom ▸ hs.1, hfrom ▸ hs.2⟩
  refine relayIfSettled_logOk hR hL1
    ⟨mkPush S D dD (some tx) (P.mb.txHash tx) .user, ?_, rfl, by simp [mkPush], rfl, rfl⟩ hrc
  simp [System.appendPush, System.withDiamond]

/-! ## Senders and actors -/

theorem AccountPremises.relay_ne_alias {P : SysParams} {A : Accounts} (h : AccountPremises P A) :
    relaySender ≠ applyL1ToL2Alias P.crs :=
  fun e => alias_ne_of_contract h.crsContract h.relay e.symm

theorem AccountPremises.service_ne_alias {P : SysParams} {A : Accounts}
    (h : AccountPremises P A) : serviceSender ≠ applyL1ToL2Alias P.crs :=
  fun e => alias_ne_of_contract h.crsContract h.service e.symm

/-- The user path gives the alias of the registration sender only to the registration sender
itself, unless someone holds a key for that alias. -/
theorem l2Sender_ne_alias_crs {P : SysParams} {A : Accounts} {env : Env} {s : Address}
    (hA : EnvAgrees A env) (hne : s ≠ P.crs) (hk : ¬ A.keyed (applyL1ToL2Alias P.crs)) :
    l2Sender P.mb env s ≠ applyL1ToL2Alias P.crs := by
  intro hEq
  unfold l2Sender at hEq
  split_ifs at hEq with ha
  · apply hne
    have := congrArg undoL1ToL2Alias hEq
    rwa [undo_apply, undo_apply] at this
  · exact hk (hEq ▸ keyed_of_l2Sender_eq_self hA ha)

theorem Actor.ne_bridgehub {P : SysParams} {A : Accounts} {env : Env} {S : System} {a : Address}
    (h : Actor P A env S a) : a ≠ P.bridgehub := fun e => h.2.2 (Or.inl e)

theorem Actor.ne_crs {P : SysParams} {A : Accounts} {env : Env} {S : System} {a : Address}
    (h : Actor P A env S a) : a ≠ P.crs := fun e => h.2.2 (Or.inr (Or.inl e))

theorem Actor.ne_cah {P : SysParams} {A : Accounts} {env : Env} {S : System} {a : Address}
    (h : Actor P A env S a) : a ≠ P.cah := fun e => h.2.2 (Or.inr (Or.inr (Or.inl e)))

/-- An actor is no chain's registered diamond. -/
theorem Actor.ne_zkChain {P : SysParams} {A : Accounts} {env : Env} {S : System} {a : Address}
    (h : Actor P A env S a) (W : SysWF S) (c : ℕ) : S.zkChain c ≠ a := by
  intro e
  by_cases hz : S.zkChain c = 0
  · exact h.2.1 (e ▸ hz)
  · obtain ⟨d, hd, -⟩ := W.registered c hz
    rw [e] at hd
    exact h.2.2 (Or.inr (Or.inr (Or.inr (by rw [hd]; simp))))

/-- No actor is `L2_INTEROP_CENTER_ADDR`. -/
theorem Actor.ne_interopCenter {P : SysParams} {A : Accounts} {env : Env} {S : System}
    {a : Address} (h : Actor P A env S a) (hA : EnvAgrees A env) (hP : AccountPremises P A) :
    a ≠ l2InteropCenterAddr := by
  intro e
  subst e
  rcases h.1 with ho | h7 | hc
  · exact hP.interopCenterKey (ho ▸ hA.1)
  · exact hP.interopCenterKey (hA.2 _ h7)
  · exact hP.interopCenterCode hc

/-! ## The run invariant -/

/-- The run invariant: genuine roles, `SysWF`, and `LogOk`. -/
structure Inv (P : SysParams) (S : System) : Prop where
  crs : S.crsRole = P.crs
  cah : S.cahRole = P.cah
  wf : SysWF S
  log : LogOk P S.log

theorem Inv.of_frame {P : SysParams} {S S' : System} (I : Inv P S) (F : OpFrame S S')
    (hL : LogOk P S'.log) : Inv P S' :=
  ⟨F.crsRole.trans I.crs, F.cahRole.trans I.cah, F.wf I.wf, hL⟩

theorem Inv.tick {P : SysParams} {S : System} (I : Inv P S) : Inv P S.tick :=
  ⟨I.crs, I.cah, ⟨I.wf.1, I.wf.2⟩, I.log⟩

theorem Inv.peers {P : SysParams} {S : System} (I : Inv P S) (f : ℕ → ℕ → Bool) :
    Inv P { S with interopPeerAllowed := f } :=
  I.of_frame (opFrame_peers S f) I.log

theorem init_inv {P : SysParams} {S : System} (h : Init P S) : Inv P S :=
  ⟨h.crsRole, h.cahRole, h.wf, h.log ▸ logOk_nil P⟩

theorem serviceCall_inv {P : SysParams} {A : Accounts} {S : System} {env : Env}
    {G caller target : Address} {data : Bytes} {S' : System} (I : Inv P S)
    (hP : AccountPremises P A) (H : serviceCall P S env G caller target data = some S')
    (hpur : ServicePurpose P target data) : Inv P S' :=
  I.of_frame (serviceCall_frame H)
    (serviceCall_logOk H I.log hpur hP.relay_ne_alias hP.service_ne_alias)

/-- A Bridgehub request whose sender can reach the Bridgehub keeps the invariant, given what a
leaf from the aliased registration sender carries. -/
theorem sendRequest_inv {P : SysParams} {A : Accounts} {S : System} {env : Env}
    {bhCaller : Address} {chainId : ℕ} {rr : Address} {req : Request} {S' : System}
    (I : Inv P S) (hP : AccountPremises P A) (hl : env.onL1 P.mb) (hA : EnvAgrees A env)
    (H : sendRequest P S env bhCaller chainId rr req = some S') (hs : CanSend A env req.sender)
    (hreg : l2Sender P.mb env req.sender = applyL1ToL2Alias P.crs →
      req.contractL2 = l2BridgehubAddr ∧ ∃ p a, a ≠ 0 ∧ req.l2Calldata = P.encAllowPeer p a) :
    Inv P S' := by
  unfold sendRequest at H
  exact I.of_frame (userCall_frame H)
    (userCall_logOk H I.log ⟨l2Sender_ne_of_unreachable hl hA hs hP.relay,
      l2Sender_ne_of_unreachable hl hA hs hP.service⟩ hreg hP.relay_ne_alias)

theorem registrationCalldata_some {P : SysParams} {S : System} {peer : ℕ} {data : Bytes}
    (H : registrationCalldata P S peer = some data) :
    S.baseTokenAssetId peer ≠ 0 ∧ data = P.encAllowPeer peer (S.baseTokenAssetId peer) := by
  unfold registrationCalldata at H
  split_ifs at H with h1
  cases H
  exact ⟨h1, rfl⟩

theorem crsDepositOutput_some {P : SysParams} {S : System} {c peer : ℕ} {out : BridgeOutput}
    (H : crsDepositOutput P S c peer = some out) :
    S.interopPeerAllowed c peer = true ∧ S.baseTokenAssetId peer ≠ 0 ∧
      out = ⟨l2BridgehubAddr, P.encAllowPeer peer (S.baseTokenAssetId peer), []⟩ := by
  unfold crsDepositOutput at H
  split_ifs at H with h1
  split at H
  · contradiction
  · rename_i data hd
    cases H
    obtain ⟨hb, rfl⟩ := registrationCalldata_some hd
    exact ⟨by simpa using h1, hb, rfl⟩

theorem crsAllow_some {P : SysParams} {S : System} {env : Env} {c p : ℕ} {S' : System}
    (H : crsAllow P S env c p = some S') :
    S.baseTokenAssetId p ≠ 0 ∧
      serviceCall P { S with interopPeerAllowed := setPeer S.interopPeerAllowed c p true } env
        (S.zkChain c) P.crs l2BridgehubAddr (P.encAllowPeer p (S.baseTokenAssetId p)) = some S' := by
  unfold crsAllow at H
  dsimp only at H
  split_ifs at H with h1 h2 h3 h4
  split at H
  · contradiction
  · rename_i data hd
    obtain ⟨hb, rfl⟩ := registrationCalldata_some hd
    exact ⟨hb, H⟩

theorem crsDeregisterLoop_inv {P : SysParams} {A : Accounts} {env : Env} {c : ℕ} {D : Address}
    (hP : AccountPremises P A) :
    ∀ (ps : List ℕ) (S S' : System), Inv P S → crsDeregisterLoop P env c D S ps = some S' →
      Inv P S'
  | [], S, S', I, H => by
    simp only [crsDeregisterLoop, Option.some.injEq] at H
    exact H ▸ I
  | p :: ps, S, S', I, H => by
    simp only [crsDeregisterLoop] at H
    split_ifs at H with h1
    split at H
    · contradiction
    · rename_i S2 hS2
      exact crsDeregisterLoop_inv hP ps S2 S' (serviceCall_inv (I.peers _) hP hS2
        (Or.inl ⟨rfl, Or.inr ⟨p, rfl⟩⟩)) H

/-- A successful `pauseDepositsBeforeInitiatingMigration` on `D`: `D` was unpaused, its
timestamp is written, and either nothing else happens or the genuine chain asset handler is
called by `D` for `D`'s chain. -/
theorem migratorPause_some {P : SysParams} {S : System} {env : Env} {D : Address} {S' : System}
    (H : migratorPause P S env D = some S') :
    ∃ dD, S.diamonds D = some dD ∧ dD.pausedDepositsTimestamp = 0 ∧
      (S' = S.withDiamond D { dD with pausedDepositsTimestamp := env.timestamp } ∨
        (dD.settlementLayer ≠ 0 ∧ S.cahRole = P.cah ∧
          cahPause P (S.withDiamond D { dD with pausedDepositsTimestamp := env.timestamp }) env D
            dD.chainId = some S')) := by
  unfold migratorPause at H
  rcases hdd : S.diamonds D with _ | dD
  · simp [hdd] at H
  · simp only [hdd] at H
    by_cases h1 : env.onL1 P.mb
    swap
    · simp [h1] at H
    by_cases h2 : dD.pausedDepositsTimestamp = 0
    swap
    · simp [h2] at H
    rcases hc : checkedWord dD.total with _ | total
    · simp [h1, h2, hc] at H
    · simp only [h1, h2, hc, not_true_eq_false, ↓reduceIte, ne_eq] at H
      refine ⟨dD, rfl, h2, ?_⟩
      by_cases h3 : dD.settlementLayer = 0
      · rw [ite_eq_left h3, Option.some.injEq] at H
        exact Or.inl H.symm
      · rw [ite_eq_right h3] at H
        by_cases h4 : total = 0
        · simp [h4] at H
        · rw [ite_eq_right h4] at H
          by_cases h5 : S.cahRole = P.cah
          · rw [ite_eq_left h5] at H
            exact Or.inr ⟨h3, h5, H⟩
          · rw [ite_eq_right h5, Option.some.injEq] at H
            exact Or.inl H.symm

theorem migratorPause_inv {P : SysParams} {A : Accounts} {S : System} {env : Env} {D : Address}
    {S' : System} (I : Inv P S) (hP : AccountPremises P A)
    (H : migratorPause P S env D = some S') : Inv P S' := by
  obtain ⟨dD, hD, -, hS⟩ := migratorPause_some H
  have F1 : OpFrame S (S.withDiamond D { dD with pausedDepositsTimestamp := env.timestamp }) :=
    opFrame_withDiamond hD rfl
  have I1 := I.of_frame F1 I.log
  rcases hS with rfl | ⟨-, -, hC⟩
  · exact I1
  · obtain ⟨-, -, hS⟩ := cahPause_some hC
    exact serviceCall_inv I1 hP hS (Or.inr ⟨rfl, _, rfl⟩)

/-- **One step keeps the invariant.** -/
theorem step_inv {P : SysParams} {A : Accounts} {env : Env} {S S' : System} (I : Inv P S)
    (hP : AccountPremises P A) (hl : env.onL1 P.mb) (hA : EnvAgrees A env)
    (s : Step P A false env S S') : Inv P S' := by
  cases s with
  | bridgehubDirect caller a hAct H =>
    refine (sendRequest_inv I hP hl hA H hAct.1 ?_).tick
    intro e; exact absurd e (l2Sender_ne_alias_crs hA hAct.ne_crs hP.crsAliasKey)
  | bridgehubTwoBridges caller a out hAct hB H =>
    unfold bridgehubTwoBridges at H
    split_ifs at H with h1
    refine (sendRequest_inv I hP hl hA H hB.1 ?_).tick
    intro e; exact absurd e (l2Sender_ne_alias_crs hA hB.ne_crs hP.crsAliasKey)
  | bridgehubTwoBridgesCrs caller a peer out hAct hcrs hout H =>
    unfold bridgehubTwoBridges at H
    split_ifs at H with h1
    obtain ⟨-, hb, rfl⟩ := crsDepositOutput_some hout
    refine (sendRequest_inv I hP hl hA H ?_ ?_).tick
    · exact Or.inr (Or.inr (hcrs ▸ hP.crsContract))
    · intro _; exact ⟨rfl, _, _, hb, rfl⟩
  | crsAllow c p H =>
    obtain ⟨hb, hS⟩ := crsAllow_some H
    exact (serviceCall_inv (I.peers _) hP hS (Or.inl ⟨rfl, Or.inl ⟨p, _, hb, rfl⟩⟩)).tick
  | crsDeregister c ps H =>
    unfold crsDeregister at H
    split_ifs at H with h1
    exact (crsDeregisterLoop_inv hP ps S _ I H).tick
  | migratorPause D H => exact (migratorPause_inv I hP H).tick
  | directUser caller D req hAct heq H => exact absurd heq hAct.ne_bridgehub
  | directService caller G target data hAct H =>
    obtain ⟨-, -, -, -, hc, -⟩ := serviceCall_some H
    rcases hc with hc | hc
    · exact absurd (hc.trans I.crs) hAct.ne_crs
    · exact absurd (hc.trans I.cah) hAct.ne_cah
  | directRelay caller G c h e hAct H =>
    obtain ⟨-, -, -, -, -, -, hz, -⟩ := relayCall_some H
    exact absurd hz (hAct.ne_zkChain I.wf c)
  | directOnGateway caller D h hAct H =>
    exact absurd (onGatewayCall_caller H) (hAct.ne_interopCenter hA hP)
  | directCahPause caller c hAct H =>
    exact absurd (cahPause_some H).1.symm (hAct.ne_zkChain I.wf c)
  | config hC =>
    refine Inv.tick ⟨hC.crsRole.trans I.crs, hC.cahRole.trans I.cah, hC.wf, ?_⟩
    rw [hC.log]; exact I.log
  | setRoles crs cah hR => exact absurd hR (by decide)

theorem reach_inv {P : SysParams} {A : Accounts} {S0 S : System} (h0 : Init P S0)
    (hP : AccountPremises P A) (R : Reach P A false S0 S) : Inv P S := by
  induction R with
  | refl => exact init_inv h0
  | tail env _ hl hA s ih => exact step_inv ih hP hl hA s

/-! ## Roles and well-formedness need no account premise -/

theorem onGatewayCall_frame {S : System} {env : Env} {caller D : Address} {h : Word}
    {S' : System} (H : onGatewayCall S env caller D h = some S') : OpFrame S S' := by
  unfold onGatewayCall at H
  split_ifs at H with h1
  split at H
  · contradiction
  · rename_i dD hD
    split at H
    · contradiction
    · rename_i dD' hG
      cases H
      rw [OnGatewayRequestExact dD env h dD' hG]
      exact opFrame_push hD _ _ _

theorem crsAllow_frame {P : SysParams} {S : System} {env : Env} {c p : ℕ} {S' : System}
    (H : crsAllow P S env c p = some S') : OpFrame S S' :=
  (opFrame_peers S _).trans (serviceCall_frame (crsAllow_some H).2)

theorem crsDeregisterLoop_frame {P : SysParams} {env : Env} {c : ℕ} {D : Address} :
    ∀ (ps : List ℕ) (S S' : System), crsDeregisterLoop P env c D S ps = some S' → OpFrame S S'
  | [], S, S', H => by
    simp only [crsDeregisterLoop, Option.some.injEq] at H
    exact H ▸ OpFrame.refl S
  | p :: ps, S, S', H => by
    simp only [crsDeregisterLoop] at H
    split_ifs at H with h1
    split at H
    · contradiction
    · rename_i S2 hS2
      exact ((opFrame_peers S _).trans (serviceCall_frame hS2)).trans
        (crsDeregisterLoop_frame ps S2 S' H)

theorem migratorPause_frame {P : SysParams} {S : System} {env : Env} {D : Address}
    {S' : System} (H : migratorPause P S env D = some S') : OpFrame S S' := by
  obtain ⟨dD, hD, -, hS⟩ := migratorPause_some H
  have F1 : OpFrame S (S.withDiamond D { dD with pausedDepositsTimestamp := env.timestamp }) :=
    opFrame_withDiamond hD rfl
  rcases hS with rfl | ⟨-, -, hC⟩
  · exact F1
  · exact F1.trans (cahPause_frame hC)

/-- Roles and `SysWF`, the part of `Inv` that needs no account premise. -/
theorem step_rolesWF {P : SysParams} {A : Accounts} {env : Env} {S S' : System}
    (I : S.crsRole = P.crs ∧ S.cahRole = P.cah ∧ SysWF S) (s : Step P A false env S S') :
    S'.crsRole = P.crs ∧ S'.cahRole = P.cah ∧ SysWF S' := by
  have of : ∀ {T : System}, OpFrame S T → T.tick.crsRole = P.crs ∧ T.tick.cahRole = P.cah ∧
      SysWF T.tick := fun F => ⟨F.crsRole.trans I.1, F.cahRole.trans I.2.1,
        ⟨(F.wf I.2.2).1, (F.wf I.2.2).2⟩⟩
  cases s with
  | bridgehubDirect caller a hAct H => exact of (userCall_frame H)
  | bridgehubTwoBridges caller a out hAct hB H =>
    unfold bridgehubTwoBridges at H
    split_ifs at H with h1
    exact of (userCall_frame H)
  | bridgehubTwoBridgesCrs caller a peer out hAct hcrs hout H =>
    unfold bridgehubTwoBridges at H
    split_ifs at H with h1
    exact of (userCall_frame H)
  | crsAllow c p H => exact of (crsAllow_frame H)
  | crsDeregister c ps H =>
    unfold crsDeregister at H
    split_ifs at H with h1
    exact of (crsDeregisterLoop_frame ps S _ H)
  | migratorPause D H => exact of (migratorPause_frame H)
  | directUser caller D req hAct heq H => exact of (userCall_frame H)
  | directService caller G target data hAct H => exact of (serviceCall_frame H)
  | directRelay caller G c h e hAct H => exact of (relayCall_frame H)
  | directOnGateway caller D h hAct H => exact of (onGatewayCall_frame H)
  | directCahPause caller c hAct H => exact of (cahPause_frame H)
  | config hC =>
    exact ⟨hC.crsRole.trans I.1, hC.cahRole.trans I.2.1, ⟨hC.wf.1, hC.wf.2⟩⟩
  | setRoles crs cah hR => exact absurd hR (by decide)

theorem RolesStayGenuine : Properties.RolesStayGenuine := by
  intro P A S0 S h0 R
  induction R with
  | refl => exact ⟨h0.crsRole, h0.cahRole, h0.wf⟩
  | tail env _ hl hA s ih => exact step_rolesWF ih s

/-! ## (B) The run-level headlines -/

theorem LogOk.mem {P : SysParams} {log : List Push} (L : LogOk P log) {p : Push}
    (hp : p ∈ log) : ∃ pre, PushOk P pre p := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  exact ⟨_, L i hi⟩

theorem EveryLeafIsASerializedTransaction : Properties.EveryLeafIsASerializedTransaction := by
  intro P A S0 S h0 hP R p hp
  obtain ⟨pre, tx, htx, hleaf, hn, hgpp, hfd, hk, -⟩ := (reach_inv h0 hP R).log.mem hp
  exact ⟨tx, htx, hleaf, hn, hgpp, hfd, hk⟩

theorem RelayLeavesForwardTheirHash : Properties.RelayLeavesForwardTheirHash := by
  intro P A S0 S h0 hP R i hi tx htx hfrom
  obtain ⟨tx', htx', -, -, -, -, -, hrel, -⟩ := (reach_inv h0 hP R).log i hi
  rw [htx] at htx'
  cases htx'
  exact hrel hfrom

theorem ServiceLeavesHaveFixedPurpose : Properties.ServiceLeavesHaveFixedPurpose := by
  intro P A S0 S h0 hP R p hp tx htx hfrom
  obtain ⟨pre, tx', htx', -, -, -, -, -, -, hsvc, -⟩ := (reach_inv h0 hP R).log.mem hp
  rw [htx] at htx'
  cases htx'
  exact hsvc hfrom

theorem AliasedRegistrationLeavesRegister : Properties.AliasedRegistrationLeavesRegister := by
  intro P A S0 S h0 hP R p hp tx htx hfrom
  obtain ⟨pre, tx', htx', -, -, -, -, -, -, -, hreg, -⟩ := (reach_inv h0 hP R).log.mem hp
  rw [htx] at htx'
  cases htx'
  exact hreg hfrom

theorem UserLeavesNeverPrivileged : Properties.UserLeavesNeverPrivileged := by
  intro P A S0 S h0 hP R p hp hk tx htx
  obtain ⟨pre, tx', htx', -, -, -, -, -, -, -, -, huser⟩ := (reach_inv h0 hP R).log.mem hp
  rw [htx] at htx'
  cases htx'
  exact huser hk

/-! ## (A) Relay: one leaf in the settlement layer's tree iff the chain settles there -/

theorem withDiamond_other {S : System} {a b : Address} {d : Diamond} (h : b ≠ a) :
    (S.withDiamond a d).diamonds b = S.diamonds b := by
  simp [System.withDiamond, Function.update_of_ne h]

theorem withDiamond_self (S : System) (a : Address) (d : Diamond) :
    (S.withDiamond a d).diamonds a = some d := by
  simp [System.withDiamond]

@[simp] theorem appendPush_diamonds (S : System) (p : Push) :
    (S.appendPush p).diamonds = S.diamonds := rfl

theorem UserCallRelaysIffSettled : Properties.UserCallRelaysIffSettled := by
  intro P S env D req S' H
  obtain ⟨dD, tx, h, hD, hF, hR⟩ := userCall_some H
  refine ⟨dD, hD, ?_, ?_⟩
  · intro h0
    rcases relayIfSettled_some hR with ⟨-, rfl⟩ | ⟨h1, -⟩
    · exact ⟨_, rfl, rfl, rfl, fun a ha => withDiamond_other ha⟩
    · exact absurd h0 h1
  · intro h0
    rcases relayIfSettled_some hR with ⟨h1, -⟩ | ⟨-, H'⟩
    · exact absurd h1 h0
    obtain ⟨dG, tx', h', hG, -, -, -, -, hheld, hF', rfl⟩ := relayCall_some H'
    have hne : dD.settlementLayer ≠ D := fun e => hheld (by rw [e])
    rw [appendPush_diamonds, withDiamond_other hne] at hG
    obtain ⟨-, -, -, hfrom, hto, hdata, -⟩ := RelayRequestShape P.mb dG env _ _ 0 _ tx' h' hF'
    refine ⟨hne, mkPush S D dD (some tx) h .user,
      mkPush ((S.withDiamond D (dD.pushLeaf h env.timestamp)).appendPush
        (mkPush S D dD (some tx) h .user)) dD.settlementLayer dG (some tx') h' .free,
      by simp [System.appendPush, System.withDiamond], rfl, rfl, rfl, rfl,
      ⟨tx', rfl, hfrom, hto, hdata⟩,
      ⟨dG, dG.pushLeaf h' env.timestamp, hG, by rw [appendPush_diamonds, withDiamond_self],
        (PushLeafFrame dG h' env.timestamp).1⟩, fun a ha1 ha2 => ?_⟩
    rw [appendPush_diamonds, withDiamond_other ha2, appendPush_diamonds, withDiamond_other ha1]

theorem ServiceCallRelaysIffSettled : Properties.ServiceCallRelaysIffSettled := by
  intro P S env G caller target data S' H
  obtain ⟨dG, tx, h, hG, -, -, hF, hR⟩ := serviceCall_some H
  refine ⟨dG, hG, ?_, ?_⟩
  · intro h0
    rcases relayIfSettled_some hR with ⟨-, rfl⟩ | ⟨h1, -⟩
    · exact ⟨_, rfl, rfl, rfl, fun a ha => withDiamond_other ha⟩
    · exact absurd h0 h1
  · intro h0
    rcases relayIfSettled_some hR with ⟨h1, -⟩ | ⟨-, H'⟩
    · exact absurd h1 h0
    obtain ⟨dL, tx', h', hL, -, -, -, -, -, hF', rfl⟩ := relayCall_some H'
    obtain ⟨-, -, -, hfrom, hto, hdata, -⟩ := RelayRequestShape P.mb dL env _ _ 0 _ tx' h' hF'
    refine ⟨mkPush S G dG (some tx) h .free,
      mkPush ((S.withDiamond G (dG.pushLeaf h env.timestamp)).appendPush
        (mkPush S G dG (some tx) h .free)) dG.settlementLayer dL (some tx') h' .free,
      by simp [System.appendPush, System.withDiamond], rfl, rfl, rfl, rfl,
      ⟨tx', rfl, hfrom, hto, hdata⟩, fun a ha1 ha2 => ?_⟩
    rw [appendPush_diamonds, withDiamond_other ha2, appendPush_diamonds, withDiamond_other ha1]

/-! ## Pushes, flags and pause timestamps within one step -/

/-- A relay push: made by the free path with a transaction from the relay sender. -/
def IsRelayPush (p : Push) : Prop := p.kind = .free ∧ ∃ tx, p.tx = some tx ∧ tx.fromAddr = relaySender

/-- What a push-only operation keeps besides `OpFrame`: the registration flags, every diamond, and
its pause timestamp. -/
structure PushFrame (S S' : System) : Prop where
  peers : S'.interopPeerAllowed = S.interopPeerAllowed
  paused : ∀ a d, S.diamonds a = some d →
    ∃ d', S'.diamonds a = some d' ∧ d'.pausedDepositsTimestamp = d.pausedDepositsTimestamp

theorem PushFrame.refl (S : System) : PushFrame S S := ⟨rfl, fun _ d h => ⟨d, h, rfl⟩⟩

theorem PushFrame.trans {S T U : System} (h1 : PushFrame S T) (h2 : PushFrame T U) :
    PushFrame S U where
  peers := h2.peers.trans h1.peers
  paused := fun a d hd => by
    obtain ⟨d1, hd1, hp1⟩ := h1.paused a d hd
    obtain ⟨d2, hd2, hp2⟩ := h2.paused a d1 hd1
    exact ⟨d2, hd2, hp2.trans hp1⟩

theorem pushFrame_push {S : System} {a : Address} {d : Diamond} (hd : S.diamonds a = some d)
    (h : Word) (t : ℕ) (p : Push) :
    PushFrame S ((S.withDiamond a (d.pushLeaf h t)).appendPush p) where
  peers := rfl
  paused := fun b e he => by
    by_cases hb : b = a
    · subst hb; rw [hd] at he; cases he
      exact ⟨_, withDiamond_self _ _ _, rfl⟩
    · exact ⟨e, by simp only [System.appendPush]; rw [withDiamond_other hb, he], rfl⟩

theorem relayCall_new {P : SysParams} {S : System} {env : Env} {held : Option Address}
    {G caller : Address} {c : ℕ} {h : Word} {e : ℕ} {S' : System}
    (H : relayCall P S env held G caller c h e = some S') :
    PushFrame S S' ∧ ∃ p, S'.log = S.log ++ [p] ∧ IsRelayPush p := by
  obtain ⟨dG, tx, h', hG, -, -, -, -, -, hF, rfl⟩ := relayCall_some H
  obtain ⟨-, -, -, hfrom, -⟩ := RelayRequestShape P.mb dG env _ _ _ _ tx h' hF
  exact ⟨pushFrame_push hG _ _ _, _, rfl, rfl, tx, rfl, hfrom⟩

theorem relayIfSettled_new {P : SysParams} {S : System} {env : Env} {held : Option Address}
    {D : Address} {dD : Diamond} {h : Word} {S' : System}
    (H : relayIfSettled P S env held D dD h = some S') :
    PushFrame S S' ∧ ∃ rest, S'.log = S.log ++ rest ∧ ∀ p ∈ rest, IsRelayPush p := by
  rcases relayIfSettled_some H with ⟨-, rfl⟩ | ⟨-, H'⟩
  · exact ⟨PushFrame.refl _, [], by simp, by simp⟩
  · obtain ⟨F, p, hlog, hp⟩ := relayCall_new H'
    exact ⟨F, [p], hlog, by simpa using hp⟩

theorem serviceCall_new {P : SysParams} {S : System} {env : Env} {G caller target : Address}
    {data : Bytes} {S' : System} (H : serviceCall P S env G caller target data = some S') :
    PushFrame S S' ∧ ∃ dG tx h rest, S.diamonds G = some dG ∧ tx.fromAddr = serviceSender ∧
      tx.toAddr = target ∧ tx.data = data ∧
      S'.log = S.log ++ mkPush S G dG (some tx) h .free :: rest ∧ ∀ p ∈ rest, IsRelayPush p := by
  obtain ⟨dG, tx, h, hG, -, -, hF, hR⟩ := serviceCall_some H
  obtain ⟨-, -, -, hfrom, hto, hdata, -⟩ := ServiceRequestShape P.mb dG env _ _ _ tx h hF
  obtain ⟨F, rest, hlog, hrest⟩ := relayIfSettled_new hR
  refine ⟨(pushFrame_push hG _ _ _).trans F, dG, tx, h, rest, hG, hfrom, hto, hdata, ?_, hrest⟩
  rw [hlog]; simp [System.appendPush, System.withDiamond]

theorem userCall_new {P : SysParams} {S : System} {env : Env} {D : Address} {req : Request}
    {S' : System} (H : userCall P S env D req = some S') :
    PushFrame S S' ∧ ∃ dD tx h rest, S.diamonds D = some dD ∧
      tx.fromAddr = l2Sender P.mb env req.sender ∧ tx.toAddr = req.contractL2 ∧
      tx.data = req.l2Calldata ∧
      S'.log = S.log ++ mkPush S D dD (some tx) h .user :: rest ∧ ∀ p ∈ rest, IsRelayPush p := by
  obtain ⟨dD, tx, h, hD, hF, hR⟩ := userCall_some H
  obtain ⟨-, -, -, -, -, -, hto, hdata, -⟩ := UserRequestExact P.mb dD env req _ tx h hF
  obtain ⟨F, rest, hlog, hrest⟩ := relayIfSettled_new hR
  refine ⟨(pushFrame_push hD _ _ _).trans F, dD, tx, h, rest, hD, userRequest_from hF, hto,
    hdata, ?_, hrest⟩
  rw [hlog]; simp [System.appendPush, System.withDiamond]

theorem drop_of_log {l new : List Push} : (l ++ new).drop l.length = new := List.drop_left

@[simp] theorem tick_log (S : System) : S.tick.log = S.log := rfl
@[simp] theorem tick_peers (S : System) : S.tick.interopPeerAllowed = S.interopPeerAllowed := rfl
@[simp] theorem tick_diamonds (S : System) : S.tick.diamonds = S.diamonds := rfl
@[simp] theorem withDiamond_log (S : System) (a : Address) (d : Diamond) :
    (S.withDiamond a d).log = S.log := rfl

/-- The deregistration loop: every service push it appends deregisters a peer whose flag is clear
at the end, and is in `D`'s tree with `D`'s chain id; every other push is a relay push. The flags it
finds clear stay clear. -/
theorem crsDeregisterLoop_new {P : SysParams} {env : Env} {c : ℕ} {D : Address} :
    ∀ (ps : List ℕ) (S S' : System), crsDeregisterLoop P env c D S ps = some S' →
      OpFrame S S' ∧ (∀ x y, S.interopPeerAllowed x y = false → S'.interopPeerAllowed x y = false) ∧
      ∃ new, S'.log = S.log ++ new ∧ ∀ p ∈ new, IsRelayPush p ∨
        (p.diamond = D ∧ (∃ dD, S.diamonds D = some dD ∧ p.chainId = dD.chainId) ∧
          ∃ tx peer, p.tx = some tx ∧ tx.fromAddr = serviceSender ∧
            tx.data = P.encDeregister peer ∧ S'.interopPeerAllowed c peer = false)
  | [], S, S', H => by
    simp only [crsDeregisterLoop, Option.some.injEq] at H
    subst H
    exact ⟨OpFrame.refl _, fun _ _ h => h, [], by simp, by simp⟩
  | p :: ps, S, S', H => by
    simp only [crsDeregisterLoop] at H
    split_ifs at H with h1
    split at H
    · contradiction
    · rename_i S2 hS2
      obtain ⟨F2, dG, tx, h, rest, hG, hfrom, -, hdata, hlog2, hrest⟩ := serviceCall_new hS2
      have O2 := (opFrame_peers S _).trans (serviceCall_frame hS2)
      obtain ⟨O3, hfl3, new3, hlog3, hnew3⟩ := crsDeregisterLoop_new ps S2 S' H
      refine ⟨O2.trans O3, fun x y hxy => hfl3 x y ?_,
        (mkPush S D dG (some tx) h .free :: rest) ++ new3, ?_, ?_⟩
      · rw [F2.peers]; simp only [setPeer]; split_ifs <;> simp_all
      · rw [hlog3, hlog2]; simp [mkPush]
      · intro q hq
        simp only [List.mem_cons, List.mem_append] at hq
        rcases hq with (rfl | hq) | hq
        · refine Or.inr ⟨rfl, ⟨dG, hG, rfl⟩, tx, p, rfl, hfrom, hdata, hfl3 c p ?_⟩
          rw [F2.peers]; simp [setPeer]
        · exact Or.inl (hrest q hq)
        · rcases hnew3 q hq with hr | ⟨hd, ⟨dD2, hD2, hc2⟩, rest3⟩
          · exact Or.inl hr
          · refine Or.inr ⟨hd, ⟨dG, hG, ?_⟩, rest3⟩
            obtain ⟨d', hd', hc'⟩ := O2.chainIds D dG hG
            rw [hd'] at hD2
            cases hD2
            exact hc2.trans hc'

/-- The pushes of a step whose only service push is `pS`: either it or a relay push. -/
theorem mem_cons_relay {p q : Push} {rest : List Push} (hp : p ∈ q :: rest)
    (hrest : ∀ r ∈ rest, IsRelayPush r) : p = q ∨ IsRelayPush p := by
  rcases List.mem_cons.mp hp with rfl | hp
  · exact Or.inl rfl
  · exact Or.inr (hrest p hp)

theorem IsRelayPush.from {p : Push} (h : IsRelayPush p) {tx : L2Tx} (htx : p.tx = some tx) :
    tx.fromAddr = relaySender := by
  obtain ⟨-, tx', htx', hf⟩ := h
  rw [htx] at htx'
  cases htx'
  exact hf

theorem ServiceLeafStepFacts : Properties.ServiceLeafStepFacts := by
  intro P A S0 S S' env h0 hP R hl hA s
  have I := reach_inv h0 hP R
  -- the user steps append no service push
  have userNo : ∀ {D : Address} {req : Request} {S'' : System}, CanSend A env req.sender →
      userCall P S env D req = some S'' →
      ∀ p ∈ S''.log.drop S.log.length, ∀ tx, p.tx = some tx → tx.fromAddr ≠ serviceSender := by
    intro D req S'' hs H p hp tx htx hfs
    obtain ⟨-, dD, tx', h, rest, -, hfrom, -, -, hlog, hrest⟩ := userCall_new H
    rw [hlog, drop_of_log] at hp
    rcases mem_cons_relay hp hrest with rfl | hr
    · simp only [mkPush, Option.some.injEq] at htx
      subst htx
      exact l2Sender_ne_of_unreachable hl hA hs hP.service (hfrom.symm.trans hfs)
    · exact relaySender_ne_serviceSender ((hr.from htx).symm.trans hfs)
  cases s with
  | bridgehubDirect caller a hAct H =>
    unfold bridgehubDirect sendRequest at H
    intro p hp tx htx hfs
    exact absurd hfs (userNo hAct.1 H p hp tx htx)
  | bridgehubTwoBridges caller a out hAct hB H =>
    unfold bridgehubTwoBridges sendRequest at H
    split_ifs at H with h1
    intro p hp tx htx hfs
    exact absurd hfs (userNo hB.1 H p hp tx htx)
  | bridgehubTwoBridgesCrs caller a peer out hAct hcrs hout H =>
    unfold bridgehubTwoBridges sendRequest at H
    split_ifs at H with h1
    intro p hp tx htx hfs
    exact absurd hfs (userNo (Or.inr (Or.inr (hcrs ▸ hP.crsContract))) H p hp tx htx)
  | crsAllow c q H =>
    obtain ⟨hb, hS⟩ := crsAllow_some H
    obtain ⟨F, dG, tx, h, rest, hG, hfrom, hto, hdata, hlog, hrest⟩ := serviceCall_new hS
    have hz : S.zkChain c ≠ 0 := fun e => by rw [e, I.wf.noDiamondAtZero] at hG; cases hG
    obtain ⟨d, hd, hdc⟩ := I.wf.registered c hz
    have hdG : dG = d := by
      have : S.diamonds (S.zkChain c) = some dG := hG
      rw [hd] at this; cases this; rfl
    subst hdG
    intro p hp tx' htx' hfs
    rw [tick_log, hlog, List.drop_left' rfl] at hp
    rcases mem_cons_relay hp hrest with rfl | hr
    · simp only [mkPush, Option.some.injEq] at htx'
      subst htx'
      refine ⟨by simp [mkPush, hdc], Or.inl ⟨q, hdata, hb, ?_⟩⟩
      rw [tick_peers, F.peers]; simp [setPeer, mkPush, hdc]
    · exact absurd ((hr.from htx').symm.trans hfs) relaySender_ne_serviceSender
  | crsDeregister c ps H =>
    unfold crsDeregister at H
    split_ifs at H with hz
    obtain ⟨-, -, new, hlog, hnew⟩ := crsDeregisterLoop_new ps S _ H
    obtain ⟨d, hd, hdc⟩ := I.wf.registered c hz
    intro p hp tx htx hfs
    rw [tick_log, hlog, drop_of_log] at hp
    rcases hnew p hp with hr | ⟨hpd, ⟨dD, hD, hpc⟩, tx', peer, htx', hfs', hdata, hfl⟩
    · exact absurd ((hr.from htx).symm.trans hfs) relaySender_ne_serviceSender
    · rw [htx] at htx'
      cases htx'
      rw [hd] at hD
      cases hD
      refine ⟨by rw [hpc, hdc, hpd], Or.inr (Or.inl ⟨peer, hdata, ?_⟩)⟩
      rw [tick_peers, hpc, hdc]; exact hfl
  | migratorPause D H =>
    obtain ⟨dD, hD, hp0, hS⟩ := migratorPause_some H
    rcases hS with rfl | ⟨-, -, hC⟩
    · intro p hp
      rw [tick_log] at hp
      change p ∈ (S.log).drop S.log.length at hp
      simp at hp
    obtain ⟨hcaller, hsl, hS⟩ := cahPause_some hC
    obtain ⟨F, dG, tx, h, rest, hG, hfrom, hto, hdata, hlog, hrest⟩ := serviceCall_new hS
    have O1 : OpFrame S (S.withDiamond D { dD with pausedDepositsTimestamp := env.timestamp }) :=
      opFrame_withDiamond hD rfl
    -- `S1` has `S`'s Bridgehub
    change D = S.zkChain dD.chainId at hcaller
    change S.settlementLayerOf dD.chainId ≠ env.chainId at hsl
    intro p hp tx' htx' hfs
    rw [tick_log, hlog, withDiamond_log, drop_of_log] at hp
    rcases mem_cons_relay hp hrest with rfl | hr
    · simp only [mkPush, Option.some.injEq] at htx'
      subst htx'
      -- the receiving diamond is the settlement layer's registered diamond
      have hG' : (S.withDiamond D { dD with pausedDepositsTimestamp := env.timestamp }).diamonds
          (S.zkChain (S.settlementLayerOf dD.chainId)) = some dG := hG
      have hz : S.zkChain (S.settlementLayerOf dD.chainId) ≠ 0 := by
        intro e
        rw [e] at hG'
        have h0' := (O1.dom 0).mpr I.wf.noDiamondAtZero
        rw [h0'] at hG'
        cases hG'
      obtain ⟨d, hd, hdc⟩ := I.wf.registered _ hz
      obtain ⟨d', hd', hdc'⟩ := O1.chainIds _ d hd
      rw [hG'] at hd'
      cases hd'
      refine ⟨by simp [mkPush, hdc', hdc]; rfl, Or.inr (Or.inr ⟨dD.chainId, hdata, ?_, rfl, ?_⟩)⟩
      · rw [← hl]; exact hsl
      · obtain ⟨d'', hd'', hp''⟩ := F.paused D _ (withDiamond_self _ _ _)
        refine ⟨dD, d'', by rw [← hcaller]; exact hD, hp0, ?_, hp''⟩
        rw [tick_diamonds, ← hcaller]
        exact hd''
    · exact absurd ((hr.from htx').symm.trans hfs) relaySender_ne_serviceSender
  | directUser caller D req hAct heq H => exact absurd heq hAct.ne_bridgehub
  | directService caller G target data hAct H =>
    obtain ⟨-, -, -, -, hc, -⟩ := serviceCall_some H
    rcases hc with hc | hc
    · exact absurd (hc.trans I.crs) hAct.ne_crs
    · exact absurd (hc.trans I.cah) hAct.ne_cah
  | directRelay caller G c h e hAct H =>
    obtain ⟨-, -, -, -, -, -, hz, -⟩ := relayCall_some H
    exact absurd hz (hAct.ne_zkChain I.wf c)
  | directOnGateway caller D h hAct H =>
    exact absurd (onGatewayCall_caller H) (hAct.ne_interopCenter hA hP)
  | directCahPause caller c hAct H =>
    exact absurd (cahPause_some H).1.symm (hAct.ne_zkChain I.wf c)
  | config hC =>
    intro p hp
    rw [tick_log, hC.log] at hp
    simp at hp
  | setRoles crs cah hR => exact absurd hR (by decide)

/-- A service-type operation appends no push from the aliased registration sender. -/
theorem serviceCall_noAlias {P : SysParams} {A : Accounts} {S S' : System} {env : Env}
    {G caller target : Address} {data : Bytes} (hP : AccountPremises P A)
    (H : serviceCall P S env G caller target data = some S') :
    ∀ p ∈ S'.log.drop S.log.length, ∀ tx, p.tx = some tx →
      tx.fromAddr ≠ applyL1ToL2Alias P.crs := by
  obtain ⟨-, dG, tx, h, rest, -, hfrom, -, -, hlog, hrest⟩ := serviceCall_new H
  intro p hp tx' htx' hf
  rw [hlog, drop_of_log] at hp
  rcases mem_cons_relay hp hrest with rfl | hr
  · simp only [mkPush, Option.some.injEq] at htx'
    subst htx'
    exact hP.service_ne_alias (hfrom.symm.trans hf)
  · exact hP.relay_ne_alias ((hr.from htx').symm.trans hf)

theorem RegistrationLeafStepFacts : Properties.RegistrationLeafStepFacts := by
  intro P A S0 S S' env h0 hP R hl hA s
  have I := reach_inv h0 hP R
  -- a user step whose sender is not the registration sender appends no such push
  have userNo : ∀ {D : Address} {req : Request} {S'' : System}, req.sender ≠ P.crs →
      userCall P S env D req = some S'' →
      ∀ p ∈ S''.log.drop S.log.length, ∀ tx, p.tx = some tx →
        tx.fromAddr ≠ applyL1ToL2Alias P.crs := by
    intro D req S'' hne H p hp tx htx hf
    obtain ⟨-, dD, tx', h, rest, -, hfrom, -, -, hlog, hrest⟩ := userCall_new H
    rw [hlog, drop_of_log] at hp
    rcases mem_cons_relay hp hrest with rfl | hr
    · simp only [mkPush, Option.some.injEq] at htx
      subst htx
      exact l2Sender_ne_alias_crs hA hne hP.crsAliasKey (hfrom.symm.trans hf)
    · exact hP.relay_ne_alias ((hr.from htx).symm.trans hf)
  cases s with
  | bridgehubDirect caller a hAct H =>
    unfold bridgehubDirect sendRequest at H
    intro p hp tx htx hf
    exact absurd hf (userNo hAct.ne_crs H p hp tx htx)
  | bridgehubTwoBridges caller a out hAct hB H =>
    unfold bridgehubTwoBridges sendRequest at H
    split_ifs at H with h1
    intro p hp tx htx hf
    exact absurd hf (userNo hB.ne_crs H p hp tx htx)
  | bridgehubTwoBridgesCrs caller a peer out hAct hcrs hout H =>
    unfold bridgehubTwoBridges sendRequest at H
    split_ifs at H with h1
    obtain ⟨hal, hb, rfl⟩ := crsDepositOutput_some hout
    obtain ⟨-, dD, tx, h, rest, hD, hfrom, hto, hdata, hlog, hrest⟩ := userCall_new H
    intro p hp tx' htx' hf
    rw [tick_log, hlog, drop_of_log] at hp
    rcases mem_cons_relay hp hrest with rfl | hr
    · simp only [mkPush, Option.some.injEq] at htx'
      subst htx'
      have hz : S.zkChain a.chainId ≠ 0 := fun e => by
        rw [e, I.wf.noDiamondAtZero] at hD; cases hD
      obtain ⟨d, hd, hdc⟩ := I.wf.registered _ hz
      rw [hd] at hD
      cases hD
      refine ⟨by simp [mkPush, hdc], peer, hdata, hb, ?_⟩
      simp only [mkPush, hdc]
      exact hal
    · exact absurd hf (hP.relay_ne_alias ∘ fun e => ((hr.from htx').symm.trans e))
  | crsAllow c q H =>
    obtain ⟨-, hS⟩ := crsAllow_some H
    intro p hp tx htx hf
    exact absurd hf (serviceCall_noAlias hP hS p hp tx htx)
  | crsDeregister c ps H =>
    unfold crsDeregister at H
    split_ifs at H with hz
    obtain ⟨-, -, new, hlog, hnew⟩ := crsDeregisterLoop_new ps S _ H
    intro p hp tx htx hf
    rw [tick_log, hlog, drop_of_log] at hp
    rcases hnew p hp with hr | ⟨-, -, tx', peer, htx', hfs, -⟩
    · exact absurd ((hr.from htx).symm.trans hf) hP.relay_ne_alias
    · rw [htx] at htx'
      cases htx'
      exact absurd (hfs.symm.trans hf) hP.service_ne_alias
  | migratorPause D H =>
    obtain ⟨dD, hD, -, hS⟩ := migratorPause_some H
    rcases hS with rfl | ⟨-, -, hC⟩
    · intro p hp
      rw [tick_log] at hp
      change p ∈ (S.log).drop S.log.length at hp
      simp at hp
    obtain ⟨-, -, hS⟩ := cahPause_some hC
    intro p hp tx htx hf
    exact absurd hf (serviceCall_noAlias hP hS p hp tx htx)
  | directUser caller D req hAct heq H => exact absurd heq hAct.ne_bridgehub
  | directService caller G target data hAct H =>
    obtain ⟨-, -, -, -, hc, -⟩ := serviceCall_some H
    rcases hc with hc | hc
    · exact absurd (hc.trans I.crs) hAct.ne_crs
    · exact absurd (hc.trans I.cah) hAct.ne_cah
  | directRelay caller G c h e hAct H =>
    obtain ⟨-, -, -, -, -, -, hz, -⟩ := relayCall_some H
    exact absurd hz (hAct.ne_zkChain I.wf c)
  | directOnGateway caller D h hAct H =>
    exact absurd (onGatewayCall_caller H) (hAct.ne_interopCenter hA hP)
  | directCahPause caller c hAct H =>
    exact absurd (cahPause_some H).1.symm (hAct.ne_zkChain I.wf c)
  | config hC =>
    intro p hp
    rw [tick_log, hC.log] at hp
    simp at hp
  | setRoles crs cah hR => exact absurd hR (by decide)

/-! ## Relay leaves within one step -/

/-- The relay pushes of `log` from position `n0` on: each went into a diamond whose chain `S`
whitelists as a settlement layer, is not at `n0`, and follows a push by the diamond `S` registers
for that push's chain. -/
def RelayCtx (S : System) (n0 : ℕ) (log : List Push) : Prop :=
  ∀ (i : ℕ) (hi : i < log.length) (tx : L2Tx), n0 ≤ i → log[i].tx = some tx →
    tx.fromAddr = relaySender →
      S.whitelistedSL log[i].chainId = true ∧ n0 < i ∧
      ∃ q, (log.take i).getLast? = some q ∧ S.zkChain q.chainId = q.diamond

theorem relayCtx_base (S : System) (l : List Push) : RelayCtx S l.length l := by
  intro i hi tx h; omega

theorem relayCtx_append {S : System} {n0 : ℕ} {l : List Push} {p : Push} (H : RelayCtx S n0 l)
    (hp : n0 ≤ l.length → ∀ tx, p.tx = some tx → tx.fromAddr = relaySender →
      S.whitelistedSL p.chainId = true ∧ n0 < l.length ∧
      ∃ q, l.getLast? = some q ∧ S.zkChain q.chainId = q.diamond) :
    RelayCtx S n0 (l ++ [p]) := by
  intro i hi tx hn htx hf
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hlt : i < l.length
  · rw [List.getElem_append_left hlt] at htx ⊢
    rw [List.take_append_of_le_length (by omega)]
    exact H i hlt tx hn htx hf
  · have hi' : i = l.length := by omega
    subst hi'
    rw [List.getElem_append_right (by omega)] at htx ⊢
    simp only [Nat.sub_self, List.getElem_cons_zero] at htx ⊢
    rw [List.take_left' rfl]
    exact hp hn tx htx hf

/-- What a relay call needs of the push before it. -/
theorem relayCall_relayCtx {P : SysParams} {S S1 : System} {env : Env} {held : Option Address}
    {G caller : Address} {c : ℕ} {h : Word} {n0 : ℕ} {S2 : System}
    (H : relayCall P S1 env held G caller c h 0 = some S2) (C : RelayCtx S n0 S1.log)
    (hz : S1.zkChain = S.zkChain) (hw : S1.whitelistedSL = S.whitelistedSL)
    (hn : n0 < S1.log.length)
    (hq : ∃ q, S1.log.getLast? = some q ∧ q.diamond = caller ∧ q.chainId = c) :
    RelayCtx S n0 S2.log := by
  obtain ⟨dG, tx, h', hG, -, hwl, hzc, -, -, -, rfl⟩ := relayCall_some H
  rw [appendPush_log]
  refine relayCtx_append C fun _ _ _ _ => ⟨by rw [← hw]; exact hwl, hn, ?_⟩
  obtain ⟨q, hq1, hq2, hq3⟩ := hq
  exact ⟨q, hq1, by rw [← hz, hq3, hq2]; exact hzc⟩

theorem serviceCall_relayCtx {P : SysParams} {S S1 : System} {env : Env}
    {G caller target : Address} {data : Bytes} {n0 : ℕ} {S2 : System}
    (H : serviceCall P S1 env G caller target data = some S2) (C : RelayCtx S n0 S1.log)
    (hz : S1.zkChain = S.zkChain) (hw : S1.whitelistedSL = S.whitelistedSL)
    (hn : n0 ≤ S1.log.length) : RelayCtx S n0 S2.log := by
  obtain ⟨dG, tx, h, hG, -, -, hF, hR⟩ := serviceCall_some H
  obtain ⟨-, -, -, hfrom, -⟩ := ServiceRequestShape P.mb dG env target data _ tx h hF
  have C1 : RelayCtx S n0 (S1.log ++ [mkPush S1 G dG (some tx) h .free]) :=
    relayCtx_append C fun _ tx' htx' hf => by
      simp only [mkPush, Option.some.injEq] at htx'
      subst htx'
      exact absurd (hfrom.symm.trans hf) relaySender_ne_serviceSender.symm
  rcases relayIfSettled_some hR with ⟨-, rfl⟩ | ⟨-, H'⟩
  · exact C1
  · refine relayCall_relayCtx H' C1 hz hw
      (by rw [appendPush_log, List.length_append, List.length_singleton]; omega)
      ⟨mkPush S1 G dG (some tx) h .free, ?_, rfl, rfl⟩
    simp [System.appendPush, System.withDiamond]

theorem userCall_relayCtx {P : SysParams} {S S1 : System} {env : Env} {D : Address}
    {req : Request} {n0 : ℕ} {S2 : System}
    (H : userCall P S1 env D req = some S2) (C : RelayCtx S n0 S1.log)
    (hz : S1.zkChain = S.zkChain) (hw : S1.whitelistedSL = S.whitelistedSL)
    (hn : n0 ≤ S1.log.length) (hs : l2Sender P.mb env req.sender ≠ relaySender) :
    RelayCtx S n0 S2.log := by
  obtain ⟨dD, tx, h, hD, hF, hR⟩ := userCall_some H
  have hfrom := userRequest_from hF
  have C1 : RelayCtx S n0 (S1.log ++ [mkPush S1 D dD (some tx) h .user]) :=
    relayCtx_append C fun _ tx' htx' hf => by
      simp only [mkPush, Option.some.injEq] at htx'
      subst htx'
      exact absurd (hfrom.symm.trans hf) hs
  rcases relayIfSettled_some hR with ⟨-, rfl⟩ | ⟨-, H'⟩
  · exact C1
  · refine relayCall_relayCtx H' C1 hz hw
      (by rw [appendPush_log, List.length_append, List.length_singleton]; omega)
      ⟨mkPush S1 D dD (some tx) h .user, ?_, rfl, rfl⟩
    simp [System.appendPush, System.withDiamond]

theorem crsDeregisterLoop_relayCtx {P : SysParams} {S : System} {env : Env} {c : ℕ}
    {D : Address} {n0 : ℕ} :
    ∀ (ps : List ℕ) (S1 S2 : System), crsDeregisterLoop P env c D S1 ps = some S2 →
      RelayCtx S n0 S1.log → S1.zkChain = S.zkChain → S1.whitelistedSL = S.whitelistedSL →
      n0 ≤ S1.log.length → RelayCtx S n0 S2.log
  | [], S1, S2, H, C, _, _, _ => by
    simp only [crsDeregisterLoop, Option.some.injEq] at H
    exact H ▸ C
  | p :: ps, S1, S2, H, C, hz, hw, hn => by
    simp only [crsDeregisterLoop] at H
    split_ifs at H with h1
    split at H
    · contradiction
    · rename_i S3 hS3
      have F := serviceCall_frame hS3
      exact crsDeregisterLoop_relayCtx ps S3 S2 H (serviceCall_relayCtx hS3 C hz hw hn)
        (F.zkChain.trans hz) (F.wl.trans hw) (hn.trans (List.IsPrefix.length_le F.prefix_))

theorem RelayLeafStepFacts : Properties.RelayLeafStepFacts := by
  intro P A S0 S S' env h0 hP R hl hA s
  have I := reach_inv h0 hP R
  suffices RelayCtx S S.log.length S'.log by exact this
  have C0 := relayCtx_base S S.log
  cases s with
  | bridgehubDirect caller a hAct H =>
    unfold bridgehubDirect sendRequest at H
    have := userCall_relayCtx H C0 rfl rfl le_rfl
      (l2Sender_ne_of_unreachable hl hA hAct.1 hP.relay)
    exact this
  | bridgehubTwoBridges caller a out hAct hB H =>
    unfold bridgehubTwoBridges sendRequest at H
    split_ifs at H with h1
    have := userCall_relayCtx H C0 rfl rfl le_rfl
      (l2Sender_ne_of_unreachable hl hA hB.1 hP.relay)
    exact this
  | bridgehubTwoBridgesCrs caller a peer out hAct hcrs hout H =>
    unfold bridgehubTwoBridges sendRequest at H
    split_ifs at H with h1
    have hs : CanSend A env a.secondBridge := Or.inr (Or.inr (hcrs ▸ hP.crsContract))
    have := userCall_relayCtx H C0 rfl rfl le_rfl (l2Sender_ne_of_unreachable hl hA hs hP.relay)
    exact this
  | crsAllow c q H =>
    obtain ⟨-, hS⟩ := crsAllow_some H
    have := serviceCall_relayCtx hS C0 rfl rfl le_rfl
    exact this
  | crsDeregister c ps H =>
    unfold crsDeregister at H
    split_ifs at H with hz
    have := crsDeregisterLoop_relayCtx ps S _ H C0 rfl rfl le_rfl
    exact this
  | migratorPause D H =>
    obtain ⟨dD, hD, -, hS⟩ := migratorPause_some H
    rcases hS with rfl | ⟨-, -, hC⟩
    · exact C0
    · obtain ⟨-, -, hS⟩ := cahPause_some hC
      have := serviceCall_relayCtx hS C0 rfl rfl le_rfl
      exact this
  | directUser caller D req hAct heq H => exact absurd heq hAct.ne_bridgehub
  | directService caller G target data hAct H =>
    obtain ⟨-, -, -, -, hc, -⟩ := serviceCall_some H
    rcases hc with hc | hc
    · exact absurd (hc.trans I.crs) hAct.ne_crs
    · exact absurd (hc.trans I.cah) hAct.ne_cah
  | directRelay caller G c h e hAct H =>
    obtain ⟨-, -, -, -, -, -, hz, -⟩ := relayCall_some H
    exact absurd hz (hAct.ne_zkChain I.wf c)
  | directOnGateway caller D h hAct H =>
    exact absurd (onGatewayCall_caller H) (hAct.ne_interopCenter hA hP)
  | directCahPause caller c hAct H =>
    exact absurd (cahPause_some H).1.symm (hAct.ne_zkChain I.wf c)
  | config hC =>
    show RelayCtx S S.log.length _
    rw [tick_log, hC.log]; exact C0
  | setRoles crs cah hR => exact absurd hR (by decide)

/-! ## Non-vacuity and the countermodel -/

theorem wsInit_init : Init wsParams wsInit := by
  refine ⟨rfl, rfl, rfl, ⟨rfl, ?_⟩⟩
  intro c hc
  by_cases h10 : c = 10
  · subst h10; exact ⟨wsDiamond 10 0, rfl, rfl⟩
  by_cases h20 : c = 20
  · subst h20; exact ⟨wsDiamond 20 wsGateway, rfl, rfl⟩
  by_cases h30 : c = 30
  · subst h30; exact ⟨wsDiamond 30 0, rfl, rfl⟩
  · simp [wsInit, h10, h20, h30] at hc

theorem wsAccounts_premises : AccountPremises wsParams wsAccounts where
  relay := by
    show ¬ (relaySender = wOrigin) ∧ ¬ (undoL1ToL2Alias relaySender = wContract ∨
      undoL1ToL2Alias relaySender = wsCrs)
    decide
  service := by
    show ¬ (serviceSender = wOrigin) ∧ ¬ (undoL1ToL2Alias serviceSender = wContract ∨
      undoL1ToL2Alias serviceSender = wsCrs)
    decide
  interopCenterKey := by show ¬ (l2InteropCenterAddr = wOrigin); decide
  interopCenterCode := by
    show ¬ (l2InteropCenterAddr = wContract ∨ l2InteropCenterAddr = wsCrs); decide
  crsContract := Or.inr rfl
  crsAliasKey := by show ¬ (applyL1ToL2Alias wsCrs = wOrigin); decide

theorem wEnv_agrees : EnvAgrees wsAccounts wEnv :=
  ⟨rfl, fun a h => by simp [wEnv] at h⟩

/-- `wContract` is an actor in a state whose only diamonds are the witness ones. -/
theorem wContract_actor {S : System} (hS : S.diamonds wContract = none) :
    Actor wsParams wsAccounts wEnv S wContract := by
  refine ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, ?_⟩
  rintro (h | h | h | h)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact h hS

theorem ws_step1 : Step wsParams wsAccounts false wEnv wsInit wsRun1 :=
  .bridgehubDirect wContract wsDirect (wContract_actor rfl) rfl

theorem ws_step2 : Step wsParams wsAccounts false wEnv wsRun1 wsRun2 := .crsAllow 20 30 rfl

theorem ws_step3 : Step wsParams wsAccounts false wEnv wsRun2 wsRun3 :=
  .bridgehubTwoBridgesCrs wContract wsTwoBridges 30 ⟨l2BridgehubAddr, [2], []⟩
    (wContract_actor rfl) rfl rfl rfl

theorem ws_step4 : Step wsParams wsAccounts false wEnv wsRun3 wsRun4 := .crsDeregister 20 [30] rfl

theorem ws_step5 : Step wsParams wsAccounts false wEnv wsRun4 wsRun5 := .migratorPause wsD20 rfl

theorem ws_reach1 : Reach wsParams wsAccounts false wsInit wsRun1 :=
  .tail wEnv .refl rfl wEnv_agrees ws_step1

theorem ws_reach2 : Reach wsParams wsAccounts false wsInit wsRun2 :=
  .tail wEnv ws_reach1 rfl wEnv_agrees ws_step2

theorem ws_reach3 : Reach wsParams wsAccounts false wsInit wsRun3 :=
  .tail wEnv ws_reach2 rfl wEnv_agrees ws_step3

theorem ws_reach4 : Reach wsParams wsAccounts false wsInit wsRun4 :=
  .tail wEnv ws_reach3 rfl wEnv_agrees ws_step4

theorem wsRun_reach : Reach wsParams wsAccounts false wsInit wsRun5 :=
  .tail wEnv ws_reach4 rfl wEnv_agrees ws_step5

theorem PrivilegedSendersWitness : Properties.PrivilegedSendersWitness :=
  ⟨wsParams, wsAccounts, wsInit, wsRun5, wsInit_init, wsAccounts_premises, wsRun_reach,
    by decide, by decide, by decide, by decide⟩

theorem RelayWitness : Properties.RelayWitness :=
  ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl, rfl⟩

theorem StepFactsWitness : Properties.StepFactsWitness :=
  ⟨wsInit_init, wsAccounts_premises, rfl, wEnv_agrees,
    ⟨ws_reach1, ws_step2, by decide, by decide⟩, ⟨ws_reach2, ws_step3, by decide⟩,
    ⟨ws_reach3, ws_step4, by decide⟩, ⟨ws_reach4, ws_step5, by decide⟩⟩

/-- The countermodel's service transaction. -/
private def wsBadTx : L2Tx := serializedTx (serviceRequest l2BridgehubAddr [9]) 7 0

theorem RedirectedRoleBreaksServicePurpose : Properties.RedirectedRoleBreaksServicePurpose := by
  have s1 : Step wsParams wsAccounts true wEnv wsInit wsBad1 := .setRoles wContract wsCah rfl
  have s2 : Step wsParams wsAccounts true wEnv wsBad1 wsBad2 :=
    .directService wContract wsD30 l2BridgehubAddr [9] (wContract_actor rfl) rfl
  have hlog : wsBad2.log =
      [mkPush wsBad1 wsD30 (wsDiamond 30 0) (some wsBadTx) (wParams.txHash wsBadTx) .free] := rfl
  refine ⟨wsParams, wsAccounts, wsInit, wsBad2, wsInit_init, wsAccounts_premises,
    .tail wEnv (.tail wEnv .refl rfl wEnv_agrees s1) rfl wEnv_agrees s2, _,
    hlog ▸ List.mem_singleton_self _, wsBadTx, rfl, rfl, ?_⟩
  simp [ServiceShape, wsBadTx, serializedTx, serviceRequest, wsParams]

end Contracts.PriorityRequests
