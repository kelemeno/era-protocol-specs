import EraSpec.Contracts.MailboxFacet.Properties.RequestPaths

/-!
# Proofs: what one request does to one diamond

Each request function is a chain of guards ending in `writePriorityOp`; the destructor lemmas
below (`requestL2TransactionSender_some`, `requestL2TransactionFree_some`) read a successful result
back into its guards and its closed form. The timestamp result is an induction over the run.
-/

namespace Contracts.MailboxFacet.RequestPaths

/-! ## Destructors -/

theorem checkedWord_eq_some {n m : ℕ} :
    checkedWord n = some m ↔ n < requestWordLimit ∧ m = n := by
  unfold checkedWord
  split_ifs with h <;> simp [h, eq_comm]

theorem writePriorityOpHash_some {d : Diamond} {t : ℕ} {h : Word} {d' : Diamond}
    (H : writePriorityOpHash d t h = some d') :
    d.total + 1 < requestWordLimit ∧ d' = d.pushLeaf h t := by
  unfold writePriorityOpHash at H
  split_ifs at H with hc
  cases H
  exact ⟨by omega, rfl⟩

theorem writePriorityOp_some {P : Params} {d : Diamond} {env : Env} {h : Word} {d' : Diamond}
    (H : writePriorityOp P d env h = some d') :
    d.total + 1 < requestWordLimit ∧ d' = d.pushLeaf h env.timestamp ∧
      ¬ (env.onL1 P ∧ depositsPaused P (d.pushLeaf h env.timestamp) env = true) := by
  unfold writePriorityOp at H
  split at H
  · contradiction
  · rename_i e he
    obtain ⟨hlt, rfl⟩ := writePriorityOpHash_some he
    split_ifs at H with hp
    cases H
    exact ⟨hlt, rfl, hp⟩

/-- The transaction `_serializeL2Transaction` builds from a request, an id and a price. -/
def serializedTx (req : Request) (txId price : ℕ) : L2Tx where
  txType := priorityOpTxType
  fromAddr := req.sender
  toAddr := req.contractL2
  gasLimit := req.l2GasLimit
  gasPerPubdataByteLimit := req.l2GasPerPubdataByteLimit
  maxFeePerGas := price
  maxPriorityFeePerGas := 0
  paymaster := 0
  nonce := txId
  value := req.l2Value
  reserved0 := req.mintValue
  reserved1 := req.refundRecipient
  reserved2 := 0
  reserved3 := 0
  data := req.l2Calldata
  signature := []
  factoryDeps := []
  paymasterInput := []
  reservedDynamic := []

theorem serializeL2Transaction_some {req : Request} {txId price : ℕ} {tx : L2Tx}
    (H : serializeL2Transaction req txId price = some tx) :
    req.factoryDeps = [] ∧ tx = serializedTx req txId price := by
  unfold serializeL2Transaction at H
  split_ifs at H with hf
  cases H
  simp only [ne_eq, not_not] at hf
  exact ⟨hf, rfl⟩

theorem validateTx_some {P : Params} {d : Diamond} {req : Request} {txId price : ℕ}
    {tx : L2Tx} {h : Word} (H : validateTx P d req txId price = some (tx, h)) :
    req.factoryDeps = [] ∧ tx = serializedTx req txId price ∧
      ValidL1ToL2 tx d.priorityTxMaxGasLimit d.feeParams.priorityTxMaxPubdata ∧ h = P.txHash tx := by
  unfold validateTx at H
  split at H
  · contradiction
  · rename_i t ht
    split_ifs at H with hv
    cases H
    obtain ⟨hf, rfl⟩ := serializeL2Transaction_some ht
    exact ⟨hf, rfl, hv, rfl⟩

theorem requestL2TransactionFree_some {P : Params} {d : Diamond} {env : Env} {req : Request}
    {d' : Diamond} {tx : L2Tx} {h : Word}
    (H : requestL2TransactionFree P d env req = some (d', tx, h)) :
    req.factoryDeps = [] ∧ tx = serializedTx req d.total 0 ∧ h = P.txHash tx ∧
      d' = d.pushLeaf h env.timestamp := by
  unfold requestL2TransactionFree at H
  split at H
  · contradiction
  · rename_i txId hc
    obtain ⟨-, rfl⟩ := checkedWord_eq_some.mp hc
    split at H
    · contradiction
    · rename_i p t k hv
      split at H
      · contradiction
      · rename_i e hw
        cases H
        obtain ⟨hf, rfl, -, rfl⟩ := validateTx_some hv
        exact ⟨hf, rfl, rfl, (writePriorityOp_some hw).2.1⟩

theorem requestL2TransactionSender_some {P : Params} {d : Diamond} {env : Env} {req : Request}
    {d' : Diamond} {tx : L2Tx} {h : Word}
    (H : requestL2TransactionSender P d env req = some (d', tx, h)) :
    req.l2GasPerPubdataByteLimit = requiredGasPerPubdata ∧ (rewriteRequest P env req).factoryDeps = [] ∧
      ∃ price, deriveL2GasPrice d env.gasPrice requiredGasPerPubdata = some price ∧
        price * req.l2GasLimit ≤ req.mintValue ∧
        tx = serializedTx (rewriteRequest P env req) d.total price ∧ h = P.txHash tx ∧
        d' = d.pushLeaf h env.timestamp := by
  unfold requestL2TransactionSender at H
  split_ifs at H with hf hg
  simp only [ne_eq, not_not] at hg
  split at H
  · contradiction
  · rename_i txId hc
    obtain ⟨-, rfl⟩ := checkedWord_eq_some.mp hc
    split at H
    · contradiction
    · rename_i price hp
      split at H
      · contradiction
      · rename_i baseCost hb
        obtain ⟨-, rfl⟩ := checkedWord_eq_some.mp hb
        split_ifs at H with hm
        split at H
        · contradiction
        · rename_i p t k hv
          split at H
          · contradiction
          · rename_i e hw
            cases H
            rw [hg] at hp
            obtain ⟨hfd, rfl, -, rfl⟩ := validateTx_some hv
            exact ⟨hg, hfd, price, hp, by omega, rfl, rfl, (writePriorityOp_some hw).2.1⟩

/-! ## (a) One leaf, at the old total -/

theorem PushLeafFrame : Properties.PushLeafFrame := by
  intro d h t
  refine ⟨?_, rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [Diamond.pushLeaf, Diamond.total]; omega
  · simp [Diamond.pushLeaf]
  · simp [Diamond.pushLeaf]
  · intro i hi
    simp [Diamond.pushLeaf, Function.update_of_ne hi]

theorem UserRequestExact : Properties.UserRequestExact := by
  intro P d env req d' tx h H
  obtain ⟨hg, hfd, price, -, -, rfl, rfl, rfl⟩ := requestL2TransactionSender_some H
  exact ⟨rfl, rfl, rfl, hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hfd⟩

theorem FreeRequestExact : Properties.FreeRequestExact := by
  intro P d env req d' tx h H
  obtain ⟨-, rfl, rfl, rfl⟩ := requestL2TransactionFree_some H
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ServiceRequestShape : Properties.ServiceRequestShape := by
  intro P d env target data d' tx h H
  obtain ⟨-, rfl, rfl, rfl⟩ := requestL2TransactionFree_some H
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem RelayRequestShape : Properties.RelayRequestShape := by
  intro P d env c h₀ e d' tx h H
  obtain ⟨-, rfl, rfl, rfl⟩ := requestL2TransactionFree_some H
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem OnGatewayRequestExact : Properties.OnGatewayRequestExact := by
  intro d env h d' H
  exact (writePriorityOpHash_some H).2

/-! ## (b) The user path: fee floor and sender -/

theorem UserRequestFeeFloor : Properties.UserRequestFeeFloor := by
  intro P d env req d' tx h H
  obtain ⟨-, -, price, hp, hm, rfl, -, -⟩ := requestL2TransactionSender_some H
  exact ⟨price, hp, rfl, hm⟩

/-- The `from` of a successful user request is `l2Sender` of its sender. -/
theorem userRequest_from {P : Params} {d : Diamond} {env : Env} {req : Request} {d' : Diamond}
    {tx : L2Tx} {h : Word} (H : requestL2TransactionSender P d env req = some (d', tx, h)) :
    tx.fromAddr = l2Sender P env req.sender := by
  obtain ⟨-, -, price, -, -, rfl, -, -⟩ := requestL2TransactionSender_some H
  rfl

theorem UserRequestSender : Properties.UserRequestSender := by
  intro P d env req d' tx h H
  rw [userRequest_from H]
  unfold l2Sender senderIs7702
  by_cases ho : req.sender = env.origin
  · simp [ho]
  · by_cases hl : env.onL1 P
    · cases env.is7702 req.sender <;> simp [ho, hl]
    · simp [ho, hl]

theorem undo_apply (a : Address) : undoL1ToL2Alias (applyL1ToL2Alias a) = a := by
  unfold undoL1ToL2Alias applyL1ToL2Alias; abel

/-- An address the user path keeps unaliased is keyed: it is `tx.origin` or a 7702 account. -/
theorem keyed_of_l2Sender_eq_self {P : Params} {A : Accounts} {env : Env} {s : Address}
    (hA : EnvAgrees A env)
    (ha : ¬ (s ≠ env.origin ∧ senderIs7702 P env s = false)) : A.keyed s := by
  by_cases ho : s = env.origin
  · exact ho ▸ hA.1
  · have h7 : senderIs7702 P env s = true := by
      by_contra hc
      exact ha ⟨ho, by simpa using hc⟩
    simp only [senderIs7702, Bool.and_eq_true] at h7
    exact hA.2 _ h7.2

/-- The user path's `from` is never an unreachable address. -/
theorem l2Sender_ne_of_unreachable {P : Params} {A : Accounts} {env : Env} {s C : Address}
    (hl : env.onL1 P) (hA : EnvAgrees A env) (hs : CanSend A env s) (hC : Unreachable A C) :
    l2Sender P env s ≠ C := by
  intro hEq
  obtain ⟨hkC, hcC⟩ := hC
  unfold l2Sender at hEq
  split_ifs at hEq with ha
  · -- aliased: the sender is the alias preimage of `C`
    obtain ⟨hno, hn7⟩ := ha
    have hpre : s = undoL1ToL2Alias C := by rw [← hEq, undo_apply]
    rcases hs with ho | h7 | hc
    · exact hno ho
    · simp [senderIs7702, hl, h7] at hn7
    · exact hcC (hpre ▸ hc)
  · -- not aliased: the sender is `C` itself, which is keyed
    exact hkC (hEq ▸ keyed_of_l2Sender_eq_self hA ha)

theorem UserRequestNeverReachesUnreachableSender :
    Properties.UserRequestNeverReachesUnreachableSender := by
  intro P A d env req d' tx h C hl hA hs hC H
  rw [userRequest_from H]
  exact l2Sender_ne_of_unreachable hl hA hs hC

theorem AliasPreimageYieldsServiceSender : Properties.AliasPreimageYieldsServiceSender := by
  have hfrom : applyL1ToL2Alias wServicePreimage = serviceSender := by
    unfold wServicePreimage undoL1ToL2Alias applyL1ToL2Alias; abel
  refine ⟨_, serializedTx (rewriteRequest wParams wEnvPreimage (wRequest wServicePreimage)) 7 5, _,
    rfl, ?_, rfl, ⟨rfl, fun a ha => by simp [wEnvPreimage, wEnv] at ha⟩,
    Or.inr (Or.inr (Or.inr rfl)), ?_, Or.inr rfl⟩
  · show l2Sender wParams wEnvPreimage wServicePreimage = serviceSender
    have hno : wServicePreimage ≠ wOrigin := by decide
    simp [l2Sender, senderIs7702, hno, wEnvPreimage, wEnv, hfrom]
  · show ¬ (serviceSender = wOrigin)
    decide

theorem RelayAndServiceUnreachableIff : Properties.RelayAndServiceUnreachableIff := by
  intro A
  have h1 : undoL1ToL2Alias relaySender = ⟨0x0000111111111111111111111111111111110000, by decide⟩ := by
    decide
  have h2 : undoL1ToL2Alias serviceSender = ⟨0xEEEEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEEEE, by decide⟩ := by
    decide
  unfold Unreachable
  rw [h1, h2]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-! ## (c) Request timestamps on an L1 diamond -/

/-- The invariant of a run from `d`: same start, total does not decrease, timestamps present on
`[d.total, current total)`. -/
private def TsInv (d e : Diamond) : Prop :=
  e.startIndex = d.startIndex ∧ d.total ≤ e.total ∧
    ∀ i, d.total ≤ i → i < e.total → e.requestTimestamp i ≠ 0

private theorem tsInv_push {d e : Diamond} {h : Word} {t : ℕ} (ht : 0 < t) (I : TsInv d e) :
    TsInv d (e.pushLeaf h t) := by
  obtain ⟨hs, hle, hts⟩ := I
  obtain ⟨htot, hst, -, -, hat, hother, -⟩ := PushLeafFrame e h t
  refine ⟨hst.trans hs, by omega, ?_⟩
  intro i hi hlt
  by_cases hik : i = e.total
  · subst hik; rw [hat]; omega
  · rw [(hother i hik).2]
    exact hts i hi (by omega)

private theorem tsInv_step {P : Params} {d e f : Diamond}
    (s : TreeStepL1 P (fun env => 0 < env.timestamp) e f) (I : TsInv d e) : TsInv d f := by
  cases s with
  | userRequest env req tx h _ hpos H =>
    rw [(requestL2TransactionSender_some H).2.2.choose_spec.2.2.2.2]
    exact tsInv_push hpos I
  | freeRequest env req tx h _ hpos H =>
    rw [(requestL2TransactionFree_some H).2.2.2]
    exact tsInv_push hpos I
  | onGatewayRequest env h hpos H =>
    rw [OnGatewayRequestExact e env h f H]
    exact tsInv_push hpos I
  | processBatch n =>
    obtain ⟨hs, hle, hts⟩ := I
    exact ⟨hs, hle, hts⟩
  | l1Reinit a b c _ _ _ =>
    obtain ⟨hs, hle, hts⟩ := I
    exact ⟨hs, hle, hts⟩
  | other hs' hn' ht' =>
    obtain ⟨hs, hle, hts⟩ := I
    have htot : f.total = e.total := by simp [Diamond.total, hs', hn']
    refine ⟨hs'.trans hs, htot ▸ hle, ?_⟩
    intro i hi hlt
    rw [ht']
    exact hts i hi (htot ▸ hlt)

theorem L1RequestTimestampsNonzero : Properties.L1RequestTimestampsNonzero := by
  intro P d d' R
  induction R with
  | refl => exact ⟨rfl, le_rfl, fun i h1 h2 => absurd h2 (by omega)⟩
  | tail _ s ih => exact tsInv_step s ih

theorem FirstUnprocessedTimestampNonzero : Properties.FirstUnprocessedTimestampNonzero := by
  intro P d d' R h1 h2
  exact (L1RequestTimestampsNonzero P d d' R).2.2 _ h1 h2

/-! ## Non-vacuity -/

/-- The witness user transaction from `wContract`. -/
private def wTxContract : L2Tx :=
  serializedTx (rewriteRequest wParams wEnv (wRequest wContract)) 7 5

theorem UserRequestWitness : Properties.UserRequestWitness := by
  refine ⟨wDiamond.pushLeaf (wParams.txHash wTxContract) 1000, wTxContract,
    wParams.txHash wTxContract, rfl, rfl, rfl, rfl, by decide, rfl, rfl, rfl, rfl, by decide,
    rfl, ⟨rfl, ?_⟩, Or.inr (Or.inr rfl), ?_, ?_⟩
  · intro a ha; simp [wEnv] at ha
  · show ¬ (relaySender = wOrigin) ∧ ¬ (undoL1ToL2Alias relaySender = wContract)
    decide
  · show ¬ (serviceSender = wOrigin) ∧ ¬ (undoL1ToL2Alias serviceSender = wContract)
    decide

theorem UserRequestOriginWitness : Properties.UserRequestOriginWitness := by
  refine ⟨wDiamond.pushLeaf
      (wParams.txHash (serializedTx (rewriteRequest wParams wEnv (wRequest wOrigin)) 7 5)) 1000,
    serializedTx (rewriteRequest wParams wEnv (wRequest wOrigin)) 7 5,
    wParams.txHash (serializedTx (rewriteRequest wParams wEnv (wRequest wOrigin)) 7 5),
    rfl, rfl, Or.inl rfl⟩

theorem UserRequest7702Witness : Properties.UserRequest7702Witness := by
  refine ⟨_, serializedTx (rewriteRequest wParams wEnv7702 (wRequest w7702)) 7 5, _, rfl, ?_,
    by decide, by simp [wEnv7702], rfl⟩
  show l2Sender wParams wEnv7702 w7702 = w7702
  simp [l2Sender, senderIs7702, wEnv7702, Env.onL1, wParams, wEnv]

theorem OnGatewayRequestWitness : Properties.OnGatewayRequestWitness :=
  ⟨wDiamond.pushLeaf 77 1000, rfl, rfl, rfl⟩

theorem FreeRequestWitness : Properties.FreeRequestWitness := by
  refine ⟨⟨wDiamond.pushLeaf (wParams.txHash (serializedTx (serviceRequest l2BridgehubAddr [0xCD]) 7 0)) 1000,
      serializedTx (serviceRequest l2BridgehubAddr [0xCD]) 7 0,
      wParams.txHash (serializedTx (serviceRequest l2BridgehubAddr [0xCD]) 7 0), rfl, rfl⟩,
    ⟨wDiamond.pushLeaf (wParams.txHash (serializedTx (wrapRequest wParams 325 77 0) 7 0)) 1000,
      serializedTx (wrapRequest wParams 325 77 0) 7 0,
      wParams.txHash (serializedTx (wrapRequest wParams 325 77 0) 7 0), rfl, rfl⟩⟩

/-- The witness diamond after the user request. -/
private def wD1 : Diamond := wDiamond.pushLeaf (wParams.txHash wTxContract) 1000

/-- The service transaction of the witness run, at index `8`. -/
private def wTxService : L2Tx := serializedTx (serviceRequest l2BridgehubAddr [0xCD]) 8 0

/-- The witness diamond after the service request. -/
private def wD2 : Diamond := wD1.pushLeaf (wParams.txHash wTxService) 1000

theorem L1TimestampWitness : Properties.L1TimestampWitness := by
  have s1 : TreeStepL1 wParams (fun env => 0 < env.timestamp) wDiamond wD1 :=
    .userRequest wEnv (wRequest wContract) wTxContract (wParams.txHash wTxContract)
      rfl (by decide) rfl
  have s2 : TreeStepL1 wParams (fun env => 0 < env.timestamp) wD1 wD2 :=
    .freeRequest wEnv (serviceRequest l2BridgehubAddr [0xCD]) wTxService
      (wParams.txHash wTxService) rfl (by decide) rfl
  exact ⟨{ wD2 with unprocessedIndex := wD2.unprocessedIndex + 2 },
    .tail (.tail (.tail .refl s1) s2) (.processBatch 2), rfl, rfl, by decide⟩

end Contracts.MailboxFacet.RequestPaths
