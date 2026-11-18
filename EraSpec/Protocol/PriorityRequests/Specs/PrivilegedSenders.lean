import EraSpec.Contracts.MailboxFacet.Specs.RequestPaths

/-!
# Model: every L1 entry that appends a priority operation, and who sends the privileged ones

Source: era-contracts `draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5` (label
`head-v35-b17415d`), paths relative to `l1-contracts/contracts/`:

* `MB` — `state-transition/chain-deps/facets/Mailbox.sol`,
* `ZB` — `state-transition/chain-deps/facets/ZKChainBase.sol`,
* `MIG` — `state-transition/chain-deps/facets/Migrator.sol`,
* `BH` — `core/bridgehub/BridgehubBase.sol`, `L1BH` — `core/bridgehub/L1Bridgehub.sol`,
* `CRS` — `core/chain-registration/ChainRegistrationSender.sol`,
* `CAH` — `core/chain-asset-handler/L1ChainAssetHandler.sol`,
* `CFG` — `common/Config.sol`.

**This file is definitions only.** Statements are in
`EraSpec.Protocol.PriorityRequests.Properties.PrivilegedSenders`, proofs in
`EraSpec.Protocol.PriorityRequests.Proofs.PrivilegedSenders`. One diamond's request functions are
`Contracts.MailboxFacet.RequestPaths` (`EraSpec.Contracts.MailboxFacet.Specs.RequestPaths`).

## The privileged senders

Two constant `from` addresses are written by the Mailbox itself:

* `SETTLEMENT_LAYER_RELAY_SENDER = 0x1111…1111` (`CFG:219`), by `_wrapRequest` (`MB:142-166`) inside
  `requestL2TransactionToGatewayMailbox` (`MB:110-130`). On L2 the interop center accepts
  `forwardTransactionOnGateway` only from it (`interop/InteropCenter.sol:130-133`, `:839-850`).
* `SERVICE_TRANSACTION_SENDER = 0xFFFF…FFFF` (`CFG:264`), by `requestL2ServiceTransaction`
  (`MB:169-196`), which only the Bridgehub's `chainRegistrationSender` and `chainAssetHandler` may
  call (`onlyServiceTransaction`, `ZB:155-167`). On L2, `L2Bridgehub.allowInteropPeer` and
  `deregisterChainForInterop` accept the aliased chain registration sender or any service
  transaction (`core/bridgehub/L2Bridgehub.sol:45-53`, `:95-105`), and
  `L2ChainAssetHandler.requestPauseDepositsForChainOnGateway` accepts any service transaction
  (`core/chain-asset-handler/L2ChainAssetHandler.sol:80-85`, `:130-134`).

## Every L1 entry that reaches a Mailbox (a source search at the pin)

    bridgehubRequestL2Transaction      ← only BH._sendRequest (BH:366-381), from
                                         requestL2TransactionDirect (L1BH:146-187, sender = msg.sender)
                                         requestL2TransactionTwoBridges (L1BH:200-265, sender = second bridge)
    requestL2ServiceTransaction        ← CRS.allowInteropPeer (CRS:77-93), CRS.deregisterInteropPairs
                                         (CRS:98-118), CAH.requestPauseDepositsForChainOnGateway (CAH:193-202)
    requestL2TransactionToGatewayMailbox ← MB:190 and MB:279 (a diamond, after its own push)
    bridgehubRequestL2TransactionOnGateway ← only interop/InteropCenter.sol:849, an L2 contract

`CAH.requestPauseDepositsForChainOnGateway` is called by a chain's diamond from
`pauseDepositsBeforeInitiatingMigration` (`MIG:105-130`). The `L2Bridgehub` has no request entry
(`grep -rn '_sendRequest' contracts/`), so on L1 the only Bridgehub is `L1Bridgehub`.

## Modelling choices (`MODEL-PRIORITY-SENDERS` in `ASSUMPTIONS.md`)

* **One step is one L1 transaction.** `Step` lists the successful top-level calls; a revert is the
  absence of a step. `txNo` numbers the steps, and every push records the step that made it.
* **A ghost log of pushes.** `System.log` records, in order, every leaf appended to any modelled
  diamond during the run: the diamond, its chain id, the global index, the transaction the
  Mailbox serialized (none for a hash-only push), the leaf, the step and the entry point that
  pushed it. It is not storage.
* **System contracts run their source; everyone else is arbitrary.** The Bridgehub, the chain
  registration sender `P.crs`, the chain asset handler `P.cah` and every modelled diamond make
  exactly the calls of their code. Any other account (`Actor`) may call each modelled entry with any
  arguments; such a call is a step only when the entry's own checks pass. Neither the diamonds nor
  the three system contracts are upgraded during the run (`OPS-CONFIG`): a delegatecalled upgrade
  initializer could, for example, call `requestL2TransactionToGatewayMailbox` with any hash.
* **External calls.** View calls (filterer, 7702 checker, `isMigrationInProgress`, code size) are
  `Env` values, as in `RequestPaths`. The non-view external calls inside a request are the asset
  router's base-token deposit (`L1BH:164-169`, `:223-228`) and the second bridge's
  `bridgehubDeposit` and `bridgehubConfirmL2Transaction` (`L1BH:232-238`, `:260-264`); the
  second bridge's output is free unless it is the registration sender. Of the modelled system
  contracts only the registration sender implements `bridgehubDeposit` (a source search finds it in
  `ChainRegistrationSender`, `CTMDeploymentTracker` and the asset routers), so the Bridgehub, the
  chain asset handler and the diamonds are never second bridges. The Bridgehub entries are
  `nonReentrant` (`L1BH:148`, `:202`). What such a callee does inside the transaction is modelled
  as `Actor` steps of their own, before or after the request step: the request reads the
  registry and the diamonds only after the deposit and `bridgehubDeposit` return
  (`L1BH:172-186`, `:244-258`), and between a diamond's push and its relay call there is no
  external call that can write (`MB:276-284`, `MB:173-195`). Those steps get their own `txNo`.
* **Relays.** `s.settlementLayer` is written only by `Migrator.forwardedBridgeBurn` (`MIG:207`),
  which accepts only the registered diamond of a chain under the same chain type manager or, off L1,
  a virtual L1 address (`MIG:181-189`), and by the two migrations back (`MIG:299`, `:332`), which
  write `0`. A relay into an address that is not a modelled diamond reverts in the model. The relay
  of a user request runs while the requesting diamond's reentrancy lock is held (`MB:198-200`),
  so a relay into that same diamond reverts; the lock of a service request is released before its
  relay (`MB:173-195`).
* **Reject-only checks that read nothing modelled are omitted**: `whenNotPaused`, the `msg.value`
  checks (`L1BH:153-161`, `:210-220`), the magic value (`L1BH:240-242`), the chain-admin checks of
  the registration sender (`CRS:80`, `:104`), its interop-enabled and message-root checks
  (`CRS:84-86`, `:164-166`), its encoding-version byte (`CRS:133-136`), and the priority-mode check
  of `pauseDepositsBeforeInitiatingMigration` (`MIG:106-108`). Omitting a check only adds runs.
* **Configuration is free but well formed** (`ConfigStep`): registry entries, base token asset
  ids, settlement layers, the whitelist and every diamond field the request paths only read may
  change arbitrarily between transactions, and new diamonds may appear. The well-formedness kept
  is `SysWF`: every registered chain id maps to a modelled diamond with that chain id. The two
  Bridgehub roles change only by `setRoles` (`L1BH:268-280`, `BH:219-221`, owner or upgrader), and
  only when the model's switch allows it (`RoleWrites`).
* **The redirected role.** If `chainAssetHandler` is not `P.cah`, a diamond's
  `pauseDepositsBeforeInitiatingMigration` calls that other contract (`MIG:124`); the model keeps
  the diamond's own write and nothing else. Whatever the contract then does is an `Actor` step.
-/

namespace Contracts.PriorityRequests

open Contracts.MailboxFacet.RequestPaths

/-! ## Deployment and state -/

/-- The deployment: the Mailbox's parameters, the three L1 system contracts, and the encoders of the
fixed calldata. The encoders are `abi.encodeCall` of the L2 functions; nothing is assumed about
them. -/
structure SysParams where
  /-- The Mailbox facet's immutables and abstract functions. -/
  mb : Params
  /-- The `L1Bridgehub`, every diamond's `s.bridgehub`. -/
  bridgehub : Address
  /-- The genuine `ChainRegistrationSender` proxy. -/
  crs : Address
  /-- The genuine `L1ChainAssetHandler` proxy. -/
  cah : Address
  /-- `abi.encodeCall(IL2Bridgehub.allowInteropPeer, (peer, baseTokenAssetId))` (`CRS:167`). -/
  encAllowPeer : ℕ → Word → Bytes
  /-- `abi.encodeCall(IL2Bridgehub.deregisterChainForInterop, (peer))` (`CRS:115`). -/
  encDeregister : ℕ → Bytes
  /-- `abi.encodeCall(IL2ChainAssetHandler.requestPauseDepositsForChainOnGateway, (chainId))`
  (`CAH:200`). -/
  encPause : ℕ → Bytes

/-- Which Mailbox function made a push. -/
inductive PushKind where
  /-- `_writePriorityOp` in `_requestL2Transaction` (the user path, `MB:276`). -/
  | user
  /-- `_writePriorityOp` in `_requestL2TransactionFree` (`MB:302`). -/
  | free
  /-- `_writePriorityOpHash` in `bridgehubRequestL2TransactionOnGateway` (`MB:137`). -/
  | gateway
deriving DecidableEq

/-- One ghost record of the log. -/
structure Push where
  /-- The diamond whose tree received the leaf. -/
  diamond : Address
  /-- That diamond's `s.chainId`. -/
  chainId : ℕ
  /-- The global index of the leaf: the diamond's total before the push. -/
  index : ℕ
  /-- The transaction the Mailbox serialized and hashed; `none` for a hash-only push. -/
  tx : Option L2Tx
  /-- The leaf. -/
  leaf : Word
  /-- The step (L1 transaction) that made the push. -/
  txNo : ℕ
  /-- The function that made the push. -/
  kind : PushKind

/-- The modelled L1 state. -/
structure System where
  /-- The storage of every modelled diamond; `none` where there is none. -/
  diamonds : Address → Option Diamond
  /-- `Bridgehub.getZKChain` (`BH:344-346`): `0` when unregistered. -/
  zkChain : ℕ → Address
  /-- `Bridgehub.baseTokenAssetId`. -/
  baseTokenAssetId : ℕ → Word
  /-- `Bridgehub.settlementLayer`: a chain id. -/
  settlementLayerOf : ℕ → ℕ
  /-- `Bridgehub.whitelistedSettlementLayers` (`BH:115`). -/
  whitelistedSL : ℕ → Bool
  /-- `Bridgehub.chainRegistrationSender` (`BH:130`). -/
  crsRole : Address
  /-- `Bridgehub.chainAssetHandler` (`BH:124`). -/
  cahRole : Address
  /-- `ChainRegistrationSender.interopPeerAllowed` (`CRS:52`). -/
  interopPeerAllowed : ℕ → ℕ → Bool
  /-- Ghost: every push of the run, oldest first. -/
  log : List Push
  /-- Ghost: the number of steps so far. -/
  txNo : ℕ

/-- Replace one diamond's storage. -/
def System.withDiamond (S : System) (a : Address) (d : Diamond) : System :=
  { S with diamonds := Function.update S.diamonds a (some d) }

/-- Append one push to the log. -/
def System.appendPush (S : System) (p : Push) : System :=
  { S with log := S.log ++ [p] }

/-- The record of a push into `a`, whose storage before the push is `d`. -/
def mkPush (S : System) (a : Address) (d : Diamond) (tx : Option L2Tx) (h : Word)
    (k : PushKind) : Push :=
  ⟨a, d.chainId, d.total, tx, h, S.txNo, k⟩

/-- `interopPeerAllowed[c][p] = v`. -/
def setPeer (f : ℕ → ℕ → Bool) (c p : ℕ) (v : Bool) : ℕ → ℕ → Bool :=
  fun c' p' => if c' = c ∧ p' = p then v else f c' p'

/-! ## The Mailbox entries, composed -/

/-- `G.requestL2TransactionToGatewayMailbox(c, h, e)` called by `caller` (`MB:110-130`). `held` is the
diamond whose reentrancy lock the enclosing call holds: `_requestL2TransactionFree` is
`nonReentrant` (`MB:293`), so calling it on that diamond reverts. -/
def relayCall (P : SysParams) (S : System) (env : Env) (held : Option Address) (G caller : Address)
    (c : ℕ) (h : Word) (e : ℕ) : Option System :=
  match S.diamonds G with
  | none => none
  | some dG =>
    if ¬ env.onL1 P.mb then none else
    if S.whitelistedSL dG.chainId = false then none else
    if S.zkChain c ≠ caller then none else
    if e ≠ 0 then none else
    if held = some G then none else
    match requestL2TransactionFree P.mb dG env (wrapRequest P.mb c h e) with
    | none => none
    | some (dG', tx, h') =>
      some ((S.withDiamond G dG').appendPush (mkPush S G dG (some tx) h' .free))

/-- After diamond `D` (storage `dD` before its push) pushed `h`: the relay into its settlement layer
when `s.settlementLayer != address(0)` (`MB:188-195`, `MB:277-284`), with `_chainId: s.chainId`. -/
def relayIfSettled (P : SysParams) (S : System) (env : Env) (held : Option Address) (D : Address)
    (dD : Diamond) (h : Word) : Option System :=
  if dD.settlementLayer = 0 then some S
  else relayCall P S env held dD.settlementLayer D dD.chainId h 0

/-- `G.requestL2ServiceTransaction(target, data)` called by `caller` (`MB:169-196`): the free path,
then the relay. The lock of `_requestL2TransactionFree` is released before the relay. -/
def serviceCall (P : SysParams) (S : System) (env : Env) (G caller target : Address) (data : Bytes) :
    Option System :=
  match S.diamonds G with
  | none => none
  | some dG =>
    if caller ≠ S.crsRole ∧ caller ≠ S.cahRole then none else
    if ¬ env.onL1 P.mb then none else
    match requestL2TransactionFree P.mb dG env (serviceRequest target data) with
    | none => none
    | some (dG', tx, h) =>
      relayIfSettled P ((S.withDiamond G dG').appendPush (mkPush S G dG (some tx) h .free))
        env none G dG h

/-- `D.bridgehubRequestL2Transaction(req)` after `onlyBridgehub` (`MB:92-96`): the user path, then
the relay while `D`'s lock is held (`MB:198-200`, `:277-284`). -/
def userCall (P : SysParams) (S : System) (env : Env) (D : Address) (req : Request) :
    Option System :=
  match S.diamonds D with
  | none => none
  | some dD =>
    match requestL2TransactionSender P.mb dD env req with
    | none => none
    | some (dD', tx, h) =>
      relayIfSettled P ((S.withDiamond D dD').appendPush (mkPush S D dD (some tx) h .user))
        env (some D) D dD h

/-- `D.bridgehubRequestL2TransactionOnGateway(h, _)` called by `caller` (`MB:133-140`): the hash is
pushed without a transaction. -/
def onGatewayCall (S : System) (env : Env) (caller D : Address) (h : Word) : Option System :=
  if caller ≠ l2InteropCenterAddr then none else
  match S.diamonds D with
  | none => none
  | some dD =>
    match requestOnGateway dD env h with
    | none => none
    | some dD' => some ((S.withDiamond D dD').appendPush (mkPush S D dD none h .gateway))

/-! ## The Bridgehub -/

/-- `_sendRequest(chainId, refundRecipient, request)` with Bridgehub caller `bhCaller` (`BH:366-381`):
the refund recipient resolved against `msg.sender` (dropping the finality flag), then the chain's
diamond. `zkChainMap.get` reverts on an unregistered chain; in the model the lookup of address `0`
finds no diamond (`SysWF`). -/
def sendRequest (P : SysParams) (S : System) (env : Env) (bhCaller : Address) (chainId : ℕ)
    (rr : Address) (req : Request) : Option System :=
  userCall P S env (S.zkChain chainId)
    { req with refundRecipient := (actualRefundRecipient env rr bhCaller).1 }

/-- The fields of `L2TransactionRequestDirect` the model keeps. -/
structure DirectArgs where
  chainId : ℕ
  l2Contract : Address
  mintValue : ℕ
  l2Value : ℕ
  l2Calldata : Bytes
  l2GasLimit : ℕ
  l2GasPerPubdataByteLimit : ℕ
  factoryDeps : List Bytes
  refundRecipient : Address

/-- `requestL2TransactionDirect` by `caller` (`L1BH:146-187`): `sender: msg.sender` (`:176`). -/
def bridgehubDirect (P : SysParams) (S : System) (env : Env) (caller : Address) (a : DirectArgs) :
    Option System :=
  sendRequest P S env caller a.chainId a.refundRecipient
    { sender := caller, contractL2 := a.l2Contract, mintValue := a.mintValue, l2Value := a.l2Value,
      l2Calldata := a.l2Calldata, l2GasLimit := a.l2GasLimit,
      l2GasPerPubdataByteLimit := a.l2GasPerPubdataByteLimit, factoryDeps := a.factoryDeps,
      refundRecipient := 0 }

/-- The fields of `L2TransactionRequestTwoBridgesOuter` the model keeps. -/
structure TwoBridgesArgs where
  chainId : ℕ
  mintValue : ℕ
  l2Value : ℕ
  l2GasLimit : ℕ
  l2GasPerPubdataByteLimit : ℕ
  refundRecipient : Address
  secondBridge : Address

/-- What the second bridge's `bridgehubDeposit` returns, without the magic value and `txDataHash`. -/
structure BridgeOutput where
  l2Contract : Address
  l2Calldata : Bytes
  factoryDeps : List Bytes

/-- `requestL2TransactionTwoBridges` by `caller` with the second bridge's output `out`
(`L1BH:200-265`): the bridge address must exceed `BRIDGEHUB_MIN_SECOND_BRIDGE_ADDRESS = 0xFFFF`
(`L1BH:203-205`, `CFG:209`), and `sender: _request.secondBridgeAddress` (`:248`). -/
def bridgehubTwoBridges (P : SysParams) (S : System) (env : Env) (caller : Address)
    (a : TwoBridgesArgs) (out : BridgeOutput) : Option System :=
  if a.secondBridge.val ≤ 0xFFFF then none else
  sendRequest P S env caller a.chainId a.refundRecipient
    { sender := a.secondBridge, contractL2 := out.l2Contract, mintValue := a.mintValue,
      l2Value := a.l2Value, l2Calldata := out.l2Calldata, l2GasLimit := a.l2GasLimit,
      l2GasPerPubdataByteLimit := a.l2GasPerPubdataByteLimit, factoryDeps := out.factoryDeps,
      refundRecipient := 0 }

/-! ## The chain registration sender and the chain asset handler -/

/-- `_getL2RegistrationCalldata(peer)` (`CRS:159-168`): a revert on a zero base token asset id; the
message-root leaf count check only rejects and is omitted. -/
def registrationCalldata (P : SysParams) (S : System) (peer : ℕ) : Option Bytes :=
  if S.baseTokenAssetId peer = 0 then none else some (P.encAllowPeer peer (S.baseTokenAssetId peer))

/-- `_checkPeerPair(c, p)` passes (`CRS:174-182`), with `block.chainid` the L1 chain id. -/
def PeerPairOk (P : SysParams) (S : System) (c p : ℕ) : Prop :=
  p ≠ c ∧ p ≠ P.mb.l1ChainId ∧ S.settlementLayerOf p ≠ c

instance (P : SysParams) (S : System) (c p : ℕ) : Decidable (PeerPairOk P S c p) := by
  unfold PeerPairOk; infer_instance

/-- The genuine registration sender's `bridgehubDeposit(c, _, _, data)` with `data` decoding to
`peer` (`CRS:124-153`): the pair must be allowed. -/
def crsDepositOutput (P : SysParams) (S : System) (c peer : ℕ) : Option BridgeOutput :=
  if S.interopPeerAllowed c peer = false then none else
  match registrationCalldata P S peer with
  | none => none
  | some data => some ⟨l2BridgehubAddr, data, []⟩

/-- `allowInteropPeer(c, p)` (`CRS:77-93`): set the flag, then the service transaction to the L2
Bridgehub on `c`'s diamond. -/
def crsAllow (P : SysParams) (S : System) (env : Env) (c p : ℕ) : Option System :=
  if S.zkChain c = 0 then none else
  if ¬ PeerPairOk P S c p then none else
  if S.zkChain p = 0 then none else
  if S.interopPeerAllowed c p = true then none else
  let S1 := { S with interopPeerAllowed := setPeer S.interopPeerAllowed c p true }
  match registrationCalldata P S1 p with
  | none => none
  | some data => serviceCall P S1 env (S.zkChain c) P.crs l2BridgehubAddr data

/-- The loop of `deregisterInteropPairs` (`CRS:105-117`) on the diamond `D` read once at `CRS:102`. -/
def crsDeregisterLoop (P : SysParams) (env : Env) (c : ℕ) (D : Address) :
    System → List ℕ → Option System
  | S, [] => some S
  | S, p :: ps =>
    if ¬ PeerPairOk P S c p then none else
    match serviceCall P { S with interopPeerAllowed := setPeer S.interopPeerAllowed c p false } env
        D P.crs l2BridgehubAddr (P.encDeregister p) with
    | none => none
    | some S2 => crsDeregisterLoop P env c D S2 ps

/-- `deregisterInteropPairs(c, ps)` (`CRS:98-118`). -/
def crsDeregister (P : SysParams) (S : System) (env : Env) (c : ℕ) (ps : List ℕ) : Option System :=
  if S.zkChain c = 0 then none else crsDeregisterLoop P env c (S.zkChain c) S ps

/-- The genuine `requestPauseDepositsForChainOnGateway(c)` called by `caller` (`CAH:193-202`):
the caller must be `c`'s diamond, `c` must settle off L1, and the service transaction goes to the
diamond of `c`'s settlement layer. -/
def cahPause (P : SysParams) (S : System) (env : Env) (caller : Address) (c : ℕ) :
    Option System :=
  if caller ≠ S.zkChain c then none else
  if S.settlementLayerOf c = env.chainId then none else
  serviceCall P S env (S.zkChain (S.settlementLayerOf c)) P.cah l2ChainAssetHandlerAddr
    (P.encPause c)

/-- `D.pauseDepositsBeforeInitiatingMigration()` (`MIG:105-130`), by `D`'s admin or chain type
manager: write `pausedDepositsTimestamp = block.timestamp` (`PAUSE_DEPOSITS_TIME_WINDOW_START = 0`,
so both branches of `MIG:113-120`), then, if the chain settles elsewhere and has operations, call
the chain asset handler the Bridgehub names (`MIG:122-127`). -/
def migratorPause (P : SysParams) (S : System) (env : Env) (D : Address) : Option System :=
  match S.diamonds D with
  | none => none
  | some dD =>
    if ¬ env.onL1 P.mb then none else
    if dD.pausedDepositsTimestamp ≠ 0 then none else
    match checkedWord dD.total with
    | none => none
    | some total =>
    let S1 := S.withDiamond D { dD with pausedDepositsTimestamp := env.timestamp }
    if dD.settlementLayer = 0 then some S1 else
    if total = 0 then none else
    if S.cahRole = P.cah then cahPause P S1 env D dD.chainId else some S1

/-! ## Steps -/

/-- A system contract or a modelled diamond. Their calls are the steps their code makes. -/
def IsSystem (P : SysParams) (S : System) (a : Address) : Prop :=
  a = P.bridgehub ∨ a = P.crs ∨ a = P.cah ∨ S.diamonds a ≠ none

/-- An account other than the system contracts that can make a call: `tx.origin`, an EIP-7702
account, or a contract; never `address(0)`. -/
def Actor (P : SysParams) (A : Accounts) (env : Env) (S : System) (a : Address) : Prop :=
  CanSend A env a ∧ a ≠ 0 ∧ ¬ IsSystem P S a

/-- The well-formedness configuration keeps: no diamond at address `0`, and every registered chain id
maps to a modelled diamond with that chain id (chains are created by the chain type manager or
registered by the Bridgehub owner, `L1BH:108-139`, `:285-300`). -/
structure SysWF (S : System) : Prop where
  noDiamondAtZero : S.diamonds 0 = none
  registered : ∀ c, S.zkChain c ≠ 0 → ∃ d, S.diamonds (S.zkChain c) = some d ∧ d.chainId = c

/-- A configuration change between requests: the Bridgehub's registry, base token asset ids,
settlement layers and whitelist, and the diamonds' other fields, change arbitrarily; new diamonds may
appear. Kept: the log, the step counter, the roles, the registration sender's flags (only its own
entries write them), each existing diamond's chain id, tree counters, leaves and request timestamps,
and `SysWF`. -/
structure ConfigStep (S S' : System) : Prop where
  log : S'.log = S.log
  txNo : S'.txNo = S.txNo
  crsRole : S'.crsRole = S.crsRole
  cahRole : S'.cahRole = S.cahRole
  peers : S'.interopPeerAllowed = S.interopPeerAllowed
  keep : ∀ a d, S.diamonds a = some d → ∃ d', S'.diamonds a = some d' ∧ d'.chainId = d.chainId ∧
    d'.startIndex = d.startIndex ∧ d'.nextLeafIndex = d.nextLeafIndex ∧ d'.leafAt = d.leafAt ∧
    d'.requestTimestamp = d.requestTimestamp
  wf : SysWF S'

/-- Whether the Bridgehub owner or upgrader may rewrite the two roles during the run. -/
abbrev RoleWrites := Bool

/-- Advance the step counter. -/
def System.tick (S : System) : System := { S with txNo := S.txNo + 1 }

/-- One L1 transaction with environment `env` that changes the modelled state. -/
inductive Step (P : SysParams) (A : Accounts) (R : RoleWrites) (env : Env) : System → System → Prop
  /-- `requestL2TransactionDirect` by an actor. -/
  | bridgehubDirect {S S' : System} (caller : Address) (a : DirectArgs) :
      Actor P A env S caller → bridgehubDirect P S env caller a = some S' →
      Step P A R env S S'.tick
  /-- `requestL2TransactionTwoBridges` by an actor, with any second bridge that is not a system
  contract; its output is free. -/
  | bridgehubTwoBridges {S S' : System} (caller : Address) (a : TwoBridgesArgs) (out : BridgeOutput) :
      Actor P A env S caller → Actor P A env S a.secondBridge →
      bridgehubTwoBridges P S env caller a out = some S' → Step P A R env S S'.tick
  /-- `requestL2TransactionTwoBridges` by an actor with the genuine registration sender as second
  bridge, whose output is its `bridgehubDeposit` for `peer`. -/
  | bridgehubTwoBridgesCrs {S S' : System} (caller : Address) (a : TwoBridgesArgs) (peer : ℕ)
      (out : BridgeOutput) :
      Actor P A env S caller → a.secondBridge = P.crs → crsDepositOutput P S a.chainId peer = some out →
      bridgehubTwoBridges P S env caller a out = some S' → Step P A R env S S'.tick
  /-- `allowInteropPeer(c, p)` on the genuine registration sender. -/
  | crsAllow {S S' : System} (c p : ℕ) : crsAllow P S env c p = some S' → Step P A R env S S'.tick
  /-- `deregisterInteropPairs(c, ps)` on the genuine registration sender. -/
  | crsDeregister {S S' : System} (c : ℕ) (ps : List ℕ) :
      crsDeregister P S env c ps = some S' → Step P A R env S S'.tick
  /-- `pauseDepositsBeforeInitiatingMigration()` on diamond `D`. -/
  | migratorPause {S S' : System} (D : Address) :
      migratorPause P S env D = some S' → Step P A R env S S'.tick
  /-- An actor calls `bridgehubRequestL2Transaction` on a diamond: `onlyBridgehub` (`ZB:92-97`). -/
  | directUser {S S' : System} (caller D : Address) (req : Request) :
      Actor P A env S caller → caller = P.bridgehub → userCall P S env D req = some S' →
      Step P A R env S S'.tick
  /-- An actor calls `requestL2ServiceTransaction` on a diamond. -/
  | directService {S S' : System} (caller G target : Address) (data : Bytes) :
      Actor P A env S caller → serviceCall P S env G caller target data = some S' →
      Step P A R env S S'.tick
  /-- An actor calls `requestL2TransactionToGatewayMailbox` on a diamond. -/
  | directRelay {S S' : System} (caller G : Address) (c : ℕ) (h : Word) (e : ℕ) :
      Actor P A env S caller → relayCall P S env none G caller c h e = some S' →
      Step P A R env S S'.tick
  /-- An actor calls `bridgehubRequestL2TransactionOnGateway` on a diamond. -/
  | directOnGateway {S S' : System} (caller D : Address) (h : Word) :
      Actor P A env S caller → onGatewayCall S env caller D h = some S' →
      Step P A R env S S'.tick
  /-- An actor calls the chain asset handler's `requestPauseDepositsForChainOnGateway`. -/
  | directCahPause {S S' : System} (caller : Address) (c : ℕ) :
      Actor P A env S caller → cahPause P S env caller c = some S' → Step P A R env S S'.tick
  /-- A configuration change. -/
  | config {S S' : System} : ConfigStep S S' → Step P A R env S S'.tick
  /-- `setAddresses` / `setAddressesV31` by the Bridgehub owner or upgrader (`L1BH:268-280`,
  `BH:219-221`), when the switch allows it. -/
  | setRoles {S : System} (crs cah : Address) :
      R = true → Step P A R env S { S with crsRole := crs, cahRole := cah }.tick

/-- Reachability over L1 transactions whose environments agree with the accounts. -/
inductive Reach (P : SysParams) (A : Accounts) (R : RoleWrites) : System → System → Prop
  | refl {S : System} : Reach P A R S S
  | tail {S T U : System} (env : Env) :
      Reach P A R S T → env.onL1 P.mb → EnvAgrees A env → Step P A R env T U → Reach P A R S U

/-- A start state: no push logged yet, the two roles are the genuine contracts, well formed. -/
structure Init (P : SysParams) (S : System) : Prop where
  log : S.log = []
  crsRole : S.crsRole = P.crs
  cahRole : S.cahRole = P.cah
  wf : SysWF S

/-- The account premises of the results. Both privileged senders are `Unreachable`; no account acts
at `L2_INTEROP_CENTER_ADDR = 0x1000d` on L1; the registration sender is a contract and nobody holds
a key for its alias. -/
structure AccountPremises (P : SysParams) (A : Accounts) : Prop where
  relay : Unreachable A relaySender
  service : Unreachable A serviceSender
  interopCenterKey : ¬ A.keyed l2InteropCenterAddr
  interopCenterCode : ¬ A.contract l2InteropCenterAddr
  crsContract : A.contract P.crs
  crsAliasKey : ¬ A.keyed (applyL1ToL2Alias P.crs)

/-! ## The shapes of privileged leaves -/

/-- A free transaction: no mint, no L2 value, no fee. -/
def FreeFields (tx : L2Tx) : Prop := tx.reserved0 = 0 ∧ tx.value = 0 ∧ tx.maxFeePerGas = 0

/-- A service transaction carries one of the three fixed calls: `allowInteropPeer(p, a)` with
`a ≠ 0` or `deregisterChainForInterop(p)` to the L2 Bridgehub, or
`requestPauseDepositsForChainOnGateway(c)` to the L2 chain asset handler. -/
def ServiceShape (P : SysParams) (tx : L2Tx) : Prop :=
  FreeFields tx ∧
    ((tx.toAddr = l2BridgehubAddr ∧
        ((∃ p a, a ≠ 0 ∧ tx.data = P.encAllowPeer p a) ∨ ∃ p, tx.data = P.encDeregister p)) ∨
      (tx.toAddr = l2ChainAssetHandlerAddr ∧ ∃ c, tx.data = P.encPause c))

/-- A relay transaction calls `forwardTransactionOnGateway(c, h, 0)` on the L2 interop center, where
the push just before it in the log was made in the same step, by a diamond of chain `c`, with leaf
`h`. -/
def RelayShape (P : SysParams) (pre : List Push) (p : Push) (tx : L2Tx) : Prop :=
  FreeFields tx ∧ tx.toAddr = l2InteropCenterAddr ∧
    ∃ q, pre.getLast? = some q ∧ q.txNo = p.txNo ∧ q.kind ≠ .gateway ∧
      tx.data = P.mb.encForward q.chainId q.leaf 0

/-- A transaction from the aliased registration sender calls `allowInteropPeer(p, a)` with `a ≠ 0` on
the L2 Bridgehub. -/
def RegistrationShape (P : SysParams) (tx : L2Tx) : Prop :=
  tx.toAddr = l2BridgehubAddr ∧ ∃ p a, a ≠ 0 ∧ tx.data = P.encAllowPeer p a

/-! ## Witness data

L1 is chain `1`. Chain `10` is a gateway settling on L1 and whitelisted as a settlement layer;
chain `20` settles on it; chain `30` settles on L1. The diamonds reuse the fee and tree fields of
`Contracts.MailboxFacet.RequestPaths.wDiamond`. The toy encoders write one distinct byte each. -/

/-- The witness Bridgehub. -/
def wsBridgehub : Address := ⟨0xB0B0000000000000000000000000000000000001, by decide⟩

/-- The witness chain registration sender. -/
def wsCrs : Address := ⟨0xC125000000000000000000000000000000000002, by decide⟩

/-- The witness chain asset handler. -/
def wsCah : Address := ⟨0xCA40000000000000000000000000000000000003, by decide⟩

/-- The witness deployment. -/
def wsParams : SysParams where
  mb := wParams
  bridgehub := wsBridgehub
  crs := wsCrs
  cah := wsCah
  encAllowPeer := fun _ _ => [2]
  encDeregister := fun _ => [3]
  encPause := fun _ => [4]

/-- The gateway's diamond. -/
def wsGateway : Address := ⟨0xD10, by decide⟩

/-- Chain `20`'s diamond. -/
def wsD20 : Address := ⟨0xD20, by decide⟩

/-- Chain `30`'s diamond. -/
def wsD30 : Address := ⟨0xD30, by decide⟩

/-- A witness diamond for chain `cid` with settlement layer `sl`. -/
def wsDiamond (cid : ℕ) (sl : Address) : Diamond :=
  { wDiamond with chainId := cid, settlementLayer := sl }

/-- The witness start state. -/
def wsInit : System where
  diamonds := fun a =>
    if a = wsGateway then some (wsDiamond 10 0)
    else if a = wsD20 then some (wsDiamond 20 wsGateway)
    else if a = wsD30 then some (wsDiamond 30 0)
    else none
  zkChain := fun c => if c = 10 then wsGateway else if c = 20 then wsD20 else if c = 30 then wsD30 else 0
  baseTokenAssetId := fun c => (c : Word) + 7
  settlementLayerOf := fun c => if c = 20 then 10 else 1
  whitelistedSL := fun c => decide (c = 10)
  crsRole := wsCrs
  cahRole := wsCah
  interopPeerAllowed := fun _ _ => false
  log := []
  txNo := 0

/-- The witness accounts: `wOrigin` is the only keyed address; `wContract` and the registration
sender are the contracts. -/
def wsAccounts : Accounts where
  keyed := fun a => a = wOrigin
  contract := fun a => a = wContract ∨ a = wsCrs

/-- A deposit from `wContract` to chain `20`. -/
def wsDirect : DirectArgs where
  chainId := 20
  l2Contract := ⟨0x1234, by decide⟩
  mintValue := 2000000
  l2Value := 7
  l2Calldata := [0xAB]
  l2GasLimit := 300000
  l2GasPerPubdataByteLimit := requiredGasPerPubdata
  factoryDeps := []
  refundRecipient := 0

/-- The re-submission of the registration of chain `30` on chain `20` through the Bridgehub. -/
def wsTwoBridges : TwoBridgesArgs where
  chainId := 20
  mintValue := 2000000
  l2Value := 0
  l2GasLimit := 300000
  l2GasPerPubdataByteLimit := requiredGasPerPubdata
  refundRecipient := 0
  secondBridge := wsCrs

/-! The witness run has one state per step. A failing step would leave the state unchanged
(`getD`); the proofs show that none fails. -/

/-- After step 1: the deposit from `wContract` to chain `20`. -/
def wsRun1 : System := ((bridgehubDirect wsParams wsInit wEnv wContract wsDirect).getD wsInit).tick

/-- After step 2: the registration sender's `allowInteropPeer(20, 30)`. -/
def wsRun2 : System := ((crsAllow wsParams wsRun1 wEnv 20 30).getD wsRun1).tick

/-- After step 3: the re-submission of `(20, 30)` with the registration sender as second bridge. -/
def wsRun3 : System :=
  ((bridgehubTwoBridges wsParams wsRun2 wEnv wContract wsTwoBridges
    ⟨l2BridgehubAddr, [2], []⟩).getD wsRun2).tick

/-- After step 4: `deregisterInteropPairs(20, [30])`. -/
def wsRun4 : System := ((crsDeregister wsParams wsRun3 wEnv 20 [30]).getD wsRun3).tick

/-- After step 5: chain `20`'s `pauseDepositsBeforeInitiatingMigration`. -/
def wsRun5 : System := ((migratorPause wsParams wsRun4 wEnv wsD20).getD wsRun4).tick

/-- The countermodel's first step: the Bridgehub owner points `chainRegistrationSender` at
`wContract`. -/
def wsBad1 : System := { wsInit with crsRole := wContract, cahRole := wsCah }.tick

/-- The countermodel's second step: `wContract` requests a service transaction with calldata `[9]`
to the L2 Bridgehub on chain `30`. -/
def wsBad2 : System :=
  ((serviceCall wsParams wsBad1 wEnv wsD30 wContract l2BridgehubAddr [9]).getD wsBad1).tick

end Contracts.PriorityRequests
