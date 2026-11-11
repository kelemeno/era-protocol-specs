import EraSpec.Contracts.NativeTokenVaultBase.Specs.RegistrationUnified

/-!
# The representation model's life, logged, and its registry image

`RepReach` (`Specs/RegistrationUnified.lean`) records states, not the operations that
produced them.  A statement about the registry run that simulates it can therefore
only say that SOME registry run exists, and `Properties.UnifiedLifecycleCorresponds`
does so.  Its supply/flow identity is then implied by its other conjuncts: the
registry run is not tied to the representation run, and one more flow step of the
tracked asset makes the identity hold for any number in place of the supply
(`Properties.UnifiedLifecycleSupplyConjunctFree`).

This file writes the operations down, so that the registry run can be named:

* `LifecycleStepOp` / `LifecycleReachLog` is `RepStep` / `RepReach` with every
  operation logged, oldest first, with its arguments (`LifecycleOp`).  Logging loses
  no run (`Properties.LifecycleRepReachIffReachLog`).
* `LifecycleOp.registryOp a c` is the registry-model operation a logged operation is
  matched with, for the tracked asset `a`.  A preparation is the `bridgeOut` of its
  own amount towards its own destination chain; a nonzero token-model burn is a
  `bridgeOut` and a token-model mint a `bridgeIn` of its amount; transfers and zero
  burns are no operation.  The token model's mint and burn carry no chain id, so they
  are attributed to a chain `c` chosen by the statement (every result quantifies over
  it).  `lifecycleRegistryLog a c trace` is the image of a whole log.
* `lifecycleOutTotal trace` / `lifecycleInTotal trace` are the amounts a log sends
  out (preparations and burns) and brings in (mints).

`Properties.UnifiedLifecycleTraced` states the lifecycle correspondence for the
registry run whose log is `lifecycleRegistryLog` of the logged representation run.
`Contracts.NativeTokenVault.ReachLog` is deterministic, so that run is unique.

## Model boundaries

As in `Specs/RegistrationUnified.lean`.  Mapping a token-model mint to a `bridgeIn` and
a burn to a `bridgeOut` is the matching of `Properties.LifecycleRelIsSimulation`.  The
token model's mint and burn require the caller to be the token's configured vault
(`onlyNTV`, `REP-TOKEN`); which vault entry point made the call, and so which chain the
flow came from or went to, is not modelled, hence the chain parameter `c`.  The logged
run is the same run as the unlogged one; only the labels are new.

**This file is definitions only.**  Statements are in
`EraSpec.Contracts.NativeTokenVaultBase.Properties.RegistrationUnifiedStrong`.
-/

namespace Contracts.NativeTokenVaultBase

variable {Accounting : Type}

/-! ## The logged run -/

/-- One operation on the tracked token after its registration, with the arguments it
was called with: `RepStep`'s two constructors, with the token model's three operations
told apart. -/
inductive LifecycleOp where
  /-- A successful `prepare` of request `r` (the `bridgeBurn` branch). -/
  | prepared (r : Request)
  /-- The token model's `bridgeBurn(owner, amount)` (`BridgedStandardERC20.sol:179-182`),
  called by `caller`. -/
  | burn (caller owner : Address) (amount : UInt256)
  /-- The token model's `bridgeMint(recipient, amount)` (`BridgedStandardERC20.sol:170-173`),
  called by `caller`. -/
  | mint (caller recipient : Address) (amount : UInt256)
  /-- An ordinary transfer of `amount` from `owner` to `recipient`. -/
  | transfer (owner recipient : Address) (amount : UInt256)

/-- `RepStep`, labelled by the operation taken. -/
inductive LifecycleStepOp (hooks : Hooks Accounting) :
    LifecycleOp → State Accounting → State Accounting → Prop
  /-- A successful `prepare`. -/
  | prepared {s : State Accounting} {r : Request} {out : Result Accounting} :
      prepare hooks s r = some out → LifecycleStepOp hooks (.prepared r) s out.state
  /-- A successful token-model burn on the tracked token. -/
  | burn {s : State Accounting} {t : BridgedStandardERC20.State} {caller owner : Address}
      {amount : UInt256} :
      BridgedStandardERC20.burn s.token caller owner amount = some t →
      LifecycleStepOp hooks (.burn caller owner amount) s { s with token := t }
  /-- A successful token-model mint on the tracked token. -/
  | mint {s : State Accounting} {t : BridgedStandardERC20.State} {caller recipient : Address}
      {amount : UInt256} :
      BridgedStandardERC20.mint s.token caller recipient amount = some t →
      LifecycleStepOp hooks (.mint caller recipient amount) s { s with token := t }
  /-- A successful transfer of the tracked token. -/
  | transfer {s : State Accounting} {t : BridgedStandardERC20.State} {owner recipient : Address}
      {amount : UInt256} :
      BridgedStandardERC20.transfer s.token owner recipient amount = some t →
      LifecycleStepOp hooks (.transfer owner recipient amount) s { s with token := t }

/-- `RepReach`, with every operation logged, oldest first. -/
inductive LifecycleReachLog (hooks : Hooks Accounting) :
    State Accounting → State Accounting → List LifecycleOp → Prop
  | refl {s : State Accounting} : LifecycleReachLog hooks s s []
  | tail {s t u : State Accounting} {trace : List LifecycleOp} {o : LifecycleOp} :
      LifecycleReachLog hooks s t trace → LifecycleStepOp hooks o t u →
      LifecycleReachLog hooks s u (trace ++ [o])

/-! ## The registry image of a logged run -/

/-- **The registry operation a logged operation is matched with**, for the tracked asset
`a`.  A preparation is the `bridgeOut` of its request's amount towards the request's
destination chain.  A token-model burn of a nonzero amount is a `bridgeOut` of that
amount, and a token-model mint a `bridgeIn`, both attributed to chain `c` (the token
model records no chain).  A transfer, and a burn of `0` (the registry's `FlowOutGuard`
rejects a zero amount), are no operation. -/
def LifecycleOp.registryOp (a : NativeTokenVault.AssetId) (c : NativeTokenVault.Chain) :
    LifecycleOp → Option NativeTokenVault.Op
  | .prepared r => some (.bridgeOut r.destinationChain a r.data.amount.val)
  | .burn _ _ amount => if amount.val = 0 then none else some (.bridgeOut c a amount.val)
  | .mint _ _ amount => some (.bridgeIn c a amount.val)
  | .transfer .. => none

/-- **The registry log matched with a logged representation run**: each logged
operation's `registryOp`, in order. -/
def lifecycleRegistryLog (a : NativeTokenVault.AssetId) (c : NativeTokenVault.Chain)
    (trace : List LifecycleOp) : List NativeTokenVault.Op :=
  trace.filterMap (LifecycleOp.registryOp a c)

/-! ## What a logged run moves -/

/-- The amount a logged operation takes out of the tracked token's supply: a
preparation's requested amount, or a burn's amount. -/
def LifecycleOp.outAmount : LifecycleOp → ℕ
  | .prepared r => r.data.amount.val
  | .burn _ _ amount => amount.val
  | .mint .. => 0
  | .transfer .. => 0

/-- The amount a logged operation adds to the tracked token's supply: a mint's amount. -/
def LifecycleOp.inAmount : LifecycleOp → ℕ
  | .prepared _ => 0
  | .burn .. => 0
  | .mint _ _ amount => amount.val
  | .transfer .. => 0

/-- Everything a logged run prepared or burned. -/
def lifecycleOutTotal (trace : List LifecycleOp) : ℕ :=
  (trace.map LifecycleOp.outAmount).sum

/-- Everything a logged run minted. -/
def lifecycleInTotal (trace : List LifecycleOp) : ℕ :=
  (trace.map LifecycleOp.inAmount).sum

end Contracts.NativeTokenVaultBase
