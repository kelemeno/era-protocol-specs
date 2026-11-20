import EraSpec.Protocol.PriorityRequests.Specs.PrivilegedSenders
import EraSpec.Core.Headline

/-!
# Properties: who appends priority operations on L1, and the two privileged senders

Statements about `EraSpec.Protocol.PriorityRequests.Specs.PrivilegedSenders` (pin `b17415d20`).
Proofs are in `EraSpec.Protocol.PriorityRequests.Proofs.PrivilegedSenders`. No statement takes a
hash or encoding premise.

Every run starts from an `Init` state (empty log, the Bridgehub's two roles are the genuine
`ChainRegistrationSender` and `L1ChainAssetHandler`, `SysWF`) and is a `Reach` over L1
transactions whose environments agree with the accounts. The run-level results take the account
premises `AccountPremises` and forbid role writes (`R = false`).

## (A) Relay: one leaf in the settlement layer's tree iff the chain settles there

A successful user request on diamond `D` appends exactly one push, by `D`, to the log when
`s.settlementLayer = 0`, and changes no other diamond. Otherwise it appends, in the same
transaction, that push and then one relay push into the settlement layer's diamond, which is not `D`
and whose total grows by one; the relay transaction calls `forwardTransactionOnGateway(D.chainId, h,
0)` with `h` the leaf `D` just pushed, and no third diamond changes (`UserCallRelaysIffSettled`). A
service request does the same, except that the settlement layer may be the requesting diamond
itself, and the statement leaves out how the settlement layer's total grows (by one, or by two
when it is the requesting diamond) (`ServiceCallRelaysIffSettled`).

## (B) The privileged senders

Along every run:

1. **Relay leaves** (`from = SETTLEMENT_LAYER_RELAY_SENDER`) are free transactions to the L2
   interop center calling `forwardTransactionOnGateway(c, h, 0)`, where the push just before
   them in the log was made in the same L1 transaction, by a request (not the hash-only path) of a
   diamond of chain `c`, with leaf `h` (`RelayLeavesForwardTheirHash`). At that time the
   receiving diamond's chain was a whitelisted settlement layer and the pushing diamond was chain
   `c`'s registered diamond (`RelayLeafStepFacts`).
2. **Service leaves** (`from = SERVICE_TRANSACTION_SENDER`) are free transactions with one of three
   (target, calldata) pairs: `allowInteropPeer(p, a)` with `a ≠ 0` or
   `deregisterChainForInterop(p)` to the L2 Bridgehub, or `requestPauseDepositsForChainOnGateway(c)`
   to the L2 chain asset handler (`ServiceLeavesHaveFixedPurpose`). Both L2 receivers accept any
   service sender (`L2Bridgehub.sol:45-53`, `L2ChainAssetHandler.sol:80-85`); along these runs the
   L2 Bridgehub is sent only the two registration calls and the L2 chain asset handler only the
   pause call. At the time of the push, the leaf is in the tree of its chain's registered diamond,
   and: a registration of `p` carries the Bridgehub's nonzero base token asset id of `p` and the
   pair is allowed after the step; or a deregistration of `p` leaves the pair disallowed after the
   step; or a pause request for `c` is in the tree of the registered diamond of `c`'s settlement
   layer, which is not L1, and `c`'s registered diamond had pause timestamp `0` before the step and
   the step's `block.timestamp` after it (`ServiceLeafStepFacts`).
3. **Leaves from the aliased registration sender** call `allowInteropPeer(p, a)` with `a ≠ 0` on
   the L2 Bridgehub (`AliasedRegistrationLeavesRegister`), with `a` the Bridgehub's value and the
   pair allowed at the time (`RegistrationLeafStepFacts`).
4. **No user request** has either privileged sender (`UserLeavesNeverPrivileged`), and every leaf
   of the run is the hash of a transaction the Mailbox serialized, with the leaf's index as nonce
   (`EveryLeafIsASerializedTransaction`): no hash-only push happens on L1.

The roles stay the genuine contracts and `SysWF` is kept (`RolesStayGenuine`, which needs no
account premise).

## Countermodel

With role writes allowed, the Bridgehub owner points `chainRegistrationSender` at an ordinary
contract, which then appends a service leaf whose calldata is none of the three
(`RedirectedRoleBreaksServicePurpose`). So the role premise of `Init` and the switch `R = false`
are load-bearing. `Contracts.MailboxFacet.RequestPaths.AliasPreimageYieldsServiceSender` shows the
account premise is needed for the user path.

## Non-vacuity

`PrivilegedSendersWitness` is one run from an `Init` state under `AccountPremises`, with a
gateway (chain `10`) and a chain settling on it (chain `20`): a user deposit from a contract, an
interop-peer registration of chain `30`, its re-submission through the Bridgehub with the
registration sender as second bridge, the deregistration, and a deposit pause. Its log has relay,
service and aliased-registration leaves and a user leaf from an aliased contract, so every
run-level premise holds non-trivially and every conclusion is about present leaves.
`StepFactsWitness` gives, for each of the three step-fact results, steps from reachable states that
append the leaves they speak about, and `RelayWitness` reaches both branches of (A) for both
paths.
-/

namespace Contracts.PriorityRequests

open Contracts.MailboxFacet.RequestPaths

/-! ## (A) Relay -/

/-- **HEADLINE (A), USER PATH.** A successful `bridgehubRequestL2Transaction` on `D` appends one push
by `D` when `D` settles here, and otherwise that push followed by one relay push into the settlement
layer's diamond, which is a different diamond whose total grows by one; the relay transaction calls
`forwardTransactionOnGateway(D.chainId, h, 0)` for `D`'s leaf `h`. Every other diamond is
unchanged. -/
@[headline] def Properties.UserCallRelaysIffSettled : Prop :=
  ∀ (P : SysParams) (S : System) (env : Env) (D : Address) (req : Request) (S' : System),
    userCall P S env D req = some S' →
      ∃ dD, S.diamonds D = some dD ∧
        (dD.settlementLayer = 0 → ∃ p, S'.log = S.log ++ [p] ∧ p.diamond = D ∧ p.kind = .user ∧
          ∀ a, a ≠ D → S'.diamonds a = S.diamonds a) ∧
        (dD.settlementLayer ≠ 0 → dD.settlementLayer ≠ D ∧
          ∃ p q, S'.log = S.log ++ [p, q] ∧ p.diamond = D ∧ p.kind = .user ∧
            q.diamond = dD.settlementLayer ∧ q.kind = .free ∧
            (∃ tx, q.tx = some tx ∧ tx.fromAddr = relaySender ∧ tx.toAddr = l2InteropCenterAddr ∧
              tx.data = P.mb.encForward dD.chainId p.leaf 0) ∧
            (∃ dG dG', S.diamonds dD.settlementLayer = some dG ∧
              S'.diamonds dD.settlementLayer = some dG' ∧ dG'.total = dG.total + 1) ∧
            ∀ a, a ≠ D → a ≠ dD.settlementLayer → S'.diamonds a = S.diamonds a)

/-- **HEADLINE (A), SERVICE PATH.** A successful `requestL2ServiceTransaction` on `G` appends one push
by `G` when `G` settles here, and otherwise that push followed by one relay push into the
settlement layer's diamond calling `forwardTransactionOnGateway(G.chainId, h, 0)` for `G`'s leaf
`h`. Every diamond other than `G` and its settlement layer is unchanged. -/
@[headline] def Properties.ServiceCallRelaysIffSettled : Prop :=
  ∀ (P : SysParams) (S : System) (env : Env) (G caller target : Address) (data : Bytes)
    (S' : System),
    serviceCall P S env G caller target data = some S' →
      ∃ dG, S.diamonds G = some dG ∧
        (dG.settlementLayer = 0 → ∃ p, S'.log = S.log ++ [p] ∧ p.diamond = G ∧ p.kind = .free ∧
          ∀ a, a ≠ G → S'.diamonds a = S.diamonds a) ∧
        (dG.settlementLayer ≠ 0 →
          ∃ p q, S'.log = S.log ++ [p, q] ∧ p.diamond = G ∧ p.kind = .free ∧
            q.diamond = dG.settlementLayer ∧ q.kind = .free ∧
            (∃ tx, q.tx = some tx ∧ tx.fromAddr = relaySender ∧ tx.toAddr = l2InteropCenterAddr ∧
              tx.data = P.mb.encForward dG.chainId p.leaf 0) ∧
            ∀ a, a ≠ G → a ≠ dG.settlementLayer → S'.diamonds a = S.diamonds a)

/-! ## (B) The privileged senders: run-level -/

/-- **THE ROLES STAY GENUINE.** Without role writes, every state reached from an `Init` state has the
genuine registration sender and chain asset handler as the Bridgehub's roles, and is `SysWF`. -/
def Properties.RolesStayGenuine : Prop :=
  ∀ (P : SysParams) (A : Accounts) (S0 S : System), Init P S0 → Reach P A false S0 S →
    S.crsRole = P.crs ∧ S.cahRole = P.cah ∧ SysWF S

/-- **EVERY L1 LEAF IS A SERIALIZED TRANSACTION.** Along every run under the account premises, every
logged push carries the transaction the Mailbox serialized, its leaf is that transaction's hash, the
nonce is the leaf's index, `gasPerPubdataByteLimit = 800`, `factoryDeps` is empty, and it is not a
hash-only push. -/
def Properties.EveryLeafIsASerializedTransaction : Prop :=
  ∀ (P : SysParams) (A : Accounts) (S0 S : System), Init P S0 → AccountPremises P A →
    Reach P A false S0 S →
      ∀ p ∈ S.log, ∃ tx, p.tx = some tx ∧ p.leaf = P.mb.txHash tx ∧ tx.nonce = p.index ∧
        tx.gasPerPubdataByteLimit = requiredGasPerPubdata ∧ tx.factoryDeps = [] ∧
        p.kind ≠ .gateway

/-- **HEADLINE (B1): RELAY LEAVES FORWARD THE HASH PUSHED JUST BEFORE THEM.** Along every run under
the account premises, a logged push whose transaction is from `SETTLEMENT_LAYER_RELAY_SENDER` was
made by the free path, and is a free transaction to `L2_INTEROP_CENTER_ADDR` calling
`forwardTransactionOnGateway(c, h, 0)`, where the push immediately before it in the log was made in
the same L1 transaction, not by the hash-only path, by a diamond of chain `c`, with leaf `h`.
The premises: the run starts from a start state (`Init`: no push logged yet, the Bridgehub's
registration-sender and chain-asset-handler roles are the genuine contracts, the state is well
formed); no role write occurs in it; every step is an L1 transaction whose sender agrees with the
accounts; and the account premises hold (`AccountPremises`: nobody can act as
`SETTLEMENT_LAYER_RELAY_SENDER` or `SERVICE_TRANSACTION_SENDER`, no account acts at
`L2_INTEROP_CENTER_ADDR` on L1, and the registration sender is a contract whose alias nobody holds a
key for). -/
@[headline] def Properties.RelayLeavesForwardTheirHash : Prop :=
  ∀ (P : SysParams) (A : Accounts) (S0 S : System), Init P S0 → AccountPremises P A →
    Reach P A false S0 S →
      ∀ (i : ℕ) (hi : i < S.log.length) (tx : L2Tx), S.log[i].tx = some tx →
        tx.fromAddr = relaySender → S.log[i].kind = .free ∧ RelayShape P (S.log.take i) S.log[i] tx

/-- **HEADLINE (B2): SERVICE LEAVES HAVE ONE OF THREE PURPOSES.** Along every run under the account
premises, a logged push whose transaction is from `SERVICE_TRANSACTION_SENDER` was made by the free
path and is a free transaction calling `allowInteropPeer(p, a)` with `a ≠ 0` or
`deregisterChainForInterop(p)` on the L2 Bridgehub, or `requestPauseDepositsForChainOnGateway(c)` on
the L2 chain asset handler.
The premises: the run starts from a start state (`Init`: no push logged yet, the Bridgehub's
registration-sender and chain-asset-handler roles are the genuine contracts, the state is well
formed); no role write occurs in it; every step is an L1 transaction whose sender agrees with the
accounts; and the account premises hold (`AccountPremises`: nobody can act as
`SETTLEMENT_LAYER_RELAY_SENDER` or `SERVICE_TRANSACTION_SENDER`, no account acts at
`L2_INTEROP_CENTER_ADDR` on L1, and the registration sender is a contract whose alias nobody holds a
key for). -/
@[headline] def Properties.ServiceLeavesHaveFixedPurpose : Prop :=
  ∀ (P : SysParams) (A : Accounts) (S0 S : System), Init P S0 → AccountPremises P A →
    Reach P A false S0 S →
      ∀ p ∈ S.log, ∀ tx, p.tx = some tx → tx.fromAddr = serviceSender →
        p.kind = .free ∧ ServiceShape P tx

/-- **HEADLINE (B3): LEAVES FROM THE ALIASED REGISTRATION SENDER REGISTER A PEER.** Along every run
under the account premises, a logged push whose transaction is from the alias of the genuine
`ChainRegistrationSender` was made by the user path and calls `allowInteropPeer(p, a)` with `a ≠ 0`
on the L2 Bridgehub.
The premises: the run starts from a start state (`Init`: no push logged yet, the Bridgehub's
registration-sender and chain-asset-handler roles are the genuine contracts, the state is well
formed); no role write occurs in it; every step is an L1 transaction whose sender agrees with the
accounts; and the account premises hold (`AccountPremises`: nobody can act as
`SETTLEMENT_LAYER_RELAY_SENDER` or `SERVICE_TRANSACTION_SENDER`, no account acts at
`L2_INTEROP_CENTER_ADDR` on L1, and the registration sender is a contract whose alias nobody holds a
key for). -/
@[headline] def Properties.AliasedRegistrationLeavesRegister : Prop :=
  ∀ (P : SysParams) (A : Accounts) (S0 S : System), Init P S0 → AccountPremises P A →
    Reach P A false S0 S →
      ∀ p ∈ S.log, ∀ tx, p.tx = some tx → tx.fromAddr = applyL1ToL2Alias P.crs →
        p.kind = .user ∧ RegistrationShape P tx

/-- **HEADLINE (B4): NO USER REQUEST HAS A PRIVILEGED SENDER.** Along every run under the account
premises, no push made by the user path has a transaction from `SETTLEMENT_LAYER_RELAY_SENDER` or
`SERVICE_TRANSACTION_SENDER`.
The premises: the run starts from a start state (`Init`: no push logged yet, the Bridgehub's
registration-sender and chain-asset-handler roles are the genuine contracts, the state is well
formed); no role write occurs in it; every step is an L1 transaction whose sender agrees with the
accounts; and the account premises hold (`AccountPremises`: nobody can act as
`SETTLEMENT_LAYER_RELAY_SENDER` or `SERVICE_TRANSACTION_SENDER`, no account acts at
`L2_INTEROP_CENTER_ADDR` on L1, and the registration sender is a contract whose alias nobody holds a
key for). -/
@[headline] def Properties.UserLeavesNeverPrivileged : Prop :=
  ∀ (P : SysParams) (A : Accounts) (S0 S : System), Init P S0 → AccountPremises P A →
    Reach P A false S0 S →
      ∀ p ∈ S.log, p.kind = .user → ∀ tx, p.tx = some tx →
        tx.fromAddr ≠ relaySender ∧ tx.fromAddr ≠ serviceSender

/-! ## (B) The privileged senders: facts at the time of the push -/

/-- **A RELAY LEAF'S CONTEXT.** In a step from a reachable state `S` to `S'`, every push the step
appended whose transaction is from `SETTLEMENT_LAYER_RELAY_SENDER` went into the tree of a diamond
whose chain the Bridgehub listed as a whitelisted settlement layer in `S`; the push before it was
appended by the same step, by the diamond the Bridgehub registered in `S` for that push's chain. -/
def Properties.RelayLeafStepFacts : Prop :=
  ∀ (P : SysParams) (A : Accounts) (S0 S S' : System) (env : Env), Init P S0 →
    AccountPremises P A → Reach P A false S0 S → env.onL1 P.mb → EnvAgrees A env →
    Step P A false env S S' →
      ∀ (i : ℕ) (hi : i < S'.log.length) (tx : L2Tx), S.log.length ≤ i → S'.log[i].tx = some tx →
        tx.fromAddr = relaySender →
          S.whitelistedSL S'.log[i].chainId = true ∧ S.log.length < i ∧
          ∃ q, (S'.log.take i).getLast? = some q ∧ S.zkChain q.chainId = q.diamond

/-- **A SERVICE LEAF'S CONTEXT.** In a step from a reachable state `S` to `S'`, every appended push
from `SERVICE_TRANSACTION_SENDER` went into the tree of the diamond registered in `S` for its chain,
and is one of: a registration of `peer` with the base token asset id the Bridgehub holds for `peer`
in `S`, which is nonzero, the pair being allowed after the step; a deregistration of `peer`, the pair
being disallowed after the step; or a pause request for a chain `c` whose settlement layer in `S` is
not L1 and has the receiving diamond as its registered diamond in `S`, where `c`'s registered
diamond had `pausedDepositsTimestamp = 0` in `S` and has the step's `block.timestamp` after it. The
three cases are a disjunction: the encoders are arbitrary, so the calldata alone need not tell them
apart. -/
def Properties.ServiceLeafStepFacts : Prop :=
  ∀ (P : SysParams) (A : Accounts) (S0 S S' : System) (env : Env), Init P S0 →
    AccountPremises P A → Reach P A false S0 S → env.onL1 P.mb → EnvAgrees A env →
    Step P A false env S S' →
      ∀ p ∈ S'.log.drop S.log.length, ∀ tx, p.tx = some tx → tx.fromAddr = serviceSender →
        S.zkChain p.chainId = p.diamond ∧
        ((∃ peer, tx.data = P.encAllowPeer peer (S.baseTokenAssetId peer) ∧
            S.baseTokenAssetId peer ≠ 0 ∧ S'.interopPeerAllowed p.chainId peer = true) ∨
          (∃ peer, tx.data = P.encDeregister peer ∧
            S'.interopPeerAllowed p.chainId peer = false) ∨
          (∃ c, tx.data = P.encPause c ∧ S.settlementLayerOf c ≠ P.mb.l1ChainId ∧
            S.zkChain (S.settlementLayerOf c) = p.diamond ∧
            ∃ dc dc', S.diamonds (S.zkChain c) = some dc ∧ dc.pausedDepositsTimestamp = 0 ∧
              S'.diamonds (S.zkChain c) = some dc' ∧ dc'.pausedDepositsTimestamp = env.timestamp))

/-- **A REGISTRATION LEAF'S CONTEXT.** In a step from a reachable state `S` to `S'`, every appended
push from the alias of the genuine `ChainRegistrationSender` went into the tree of the diamond
registered in `S` for its chain and registers a `peer` whose pair with that chain is allowed in `S`,
with the nonzero base token asset id the Bridgehub holds for `peer` in `S`. -/
def Properties.RegistrationLeafStepFacts : Prop :=
  ∀ (P : SysParams) (A : Accounts) (S0 S S' : System) (env : Env), Init P S0 →
    AccountPremises P A → Reach P A false S0 S → env.onL1 P.mb → EnvAgrees A env →
    Step P A false env S S' →
      ∀ p ∈ S'.log.drop S.log.length, ∀ tx, p.tx = some tx →
        tx.fromAddr = applyL1ToL2Alias P.crs →
          S.zkChain p.chainId = p.diamond ∧
          ∃ peer, tx.data = P.encAllowPeer peer (S.baseTokenAssetId peer) ∧
            S.baseTokenAssetId peer ≠ 0 ∧ S.interopPeerAllowed p.chainId peer = true

/-! ## Countermodel -/

/-- **A REDIRECTED ROLE BREAKS THE SERVICE PURPOSES.** With role writes allowed, there is a run from
an `Init` state under the account premises in which a service leaf does not have `ServiceShape` (in
the proof: the owner sets `chainRegistrationSender` to an ordinary contract, which sends calldata
`[9]` to the L2 Bridgehub, a byte string none of the witness encoders produces). -/
@[countermodel] def Properties.RedirectedRoleBreaksServicePurpose : Prop :=
  ∃ (P : SysParams) (A : Accounts) (S0 S : System), Init P S0 ∧ AccountPremises P A ∧
    Reach P A true S0 S ∧
      ∃ p ∈ S.log, ∃ tx, p.tx = some tx ∧ tx.fromAddr = serviceSender ∧ ¬ ServiceShape P tx

/-! ## Non-vacuity -/

/-- **WITNESS FOR (A).** From the witness start state, a user request and a service request both
succeed on chain `20`'s diamond, which settles on the gateway (two pushes each), and on chain
`30`'s diamond, which settles here (one push each). -/
@[witness] def Properties.RelayWitness : Prop :=
  (∃ S', userCall wsParams wsInit wEnv wsD20 (wRequest wContract) = some S' ∧ S'.log.length = 2) ∧
  (∃ S', userCall wsParams wsInit wEnv wsD30 (wRequest wContract) = some S' ∧ S'.log.length = 1) ∧
  (∃ S', serviceCall wsParams wsInit wEnv wsD20 wsCrs l2BridgehubAddr [2] = some S' ∧
    S'.log.length = 2) ∧
  (∃ S', serviceCall wsParams wsInit wEnv wsD30 wsCrs l2BridgehubAddr [2] = some S' ∧
    S'.log.length = 1) ∧
  (wsInit.diamonds wsD20).map Diamond.settlementLayer = some wsGateway ∧
  (wsInit.diamonds wsD30).map Diamond.settlementLayer = some 0

/-- **WITNESS FOR THE STEP FACTS.** The witness start state is an `Init` state, the account premises
hold, `wEnv` is an L1 environment agreeing with the accounts, and in the witness run: the
registration step (from a reachable state) appends a service leaf and a relay leaf, the
re-submission step appends a leaf from the aliased registration sender, the deregistration step
appends a service leaf, and the pause step appends a service leaf. -/
def Properties.StepFactsWitness : Prop :=
  Init wsParams wsInit ∧ AccountPremises wsParams wsAccounts ∧ wEnv.onL1 wsParams.mb ∧
  EnvAgrees wsAccounts wEnv ∧
  (Reach wsParams wsAccounts false wsInit wsRun1 ∧ Step wsParams wsAccounts false wEnv wsRun1 wsRun2 ∧
    (∃ p ∈ wsRun2.log.drop wsRun1.log.length, (p.tx.map L2Tx.fromAddr) = some serviceSender) ∧
    (∃ p ∈ wsRun2.log.drop wsRun1.log.length, (p.tx.map L2Tx.fromAddr) = some relaySender)) ∧
  (Reach wsParams wsAccounts false wsInit wsRun2 ∧ Step wsParams wsAccounts false wEnv wsRun2 wsRun3 ∧
    ∃ p ∈ wsRun3.log.drop wsRun2.log.length,
      (p.tx.map L2Tx.fromAddr) = some (applyL1ToL2Alias wsCrs)) ∧
  (Reach wsParams wsAccounts false wsInit wsRun3 ∧ Step wsParams wsAccounts false wEnv wsRun3 wsRun4 ∧
    ∃ p ∈ wsRun4.log.drop wsRun3.log.length, (p.tx.map L2Tx.fromAddr) = some serviceSender) ∧
  (Reach wsParams wsAccounts false wsInit wsRun4 ∧ Step wsParams wsAccounts false wEnv wsRun4 wsRun5 ∧
    ∃ p ∈ wsRun5.log.drop wsRun4.log.length, (p.tx.map L2Tx.fromAddr) = some serviceSender)

/-- **WITNESS.** A run from an `Init` state under the account premises, without role writes, whose
log holds at least two relay leaves, three service leaves (a registration, a deregistration and a
pause request), one leaf from the aliased registration sender and one user leaf from an aliased
contract. -/
@[witness] def Properties.PrivilegedSendersWitness : Prop :=
  ∃ (P : SysParams) (A : Accounts) (S0 S : System), Init P S0 ∧ AccountPremises P A ∧
    Reach P A false S0 S ∧
    2 ≤ (S.log.filter fun p => (p.tx.map L2Tx.fromAddr) = some relaySender).length ∧
    3 ≤ (S.log.filter fun p => (p.tx.map L2Tx.fromAddr) = some serviceSender).length ∧
    (∃ p ∈ S.log, (p.tx.map L2Tx.fromAddr) = some (applyL1ToL2Alias P.crs)) ∧
    (∃ p ∈ S.log, p.kind = .user ∧ p.tx.isSome ∧
      (p.tx.map L2Tx.fromAddr) ≠ some relaySender ∧
      (p.tx.map L2Tx.fromAddr) ≠ some serviceSender ∧
      (p.tx.map L2Tx.fromAddr) ≠ some (applyL1ToL2Alias P.crs))

end Contracts.PriorityRequests
