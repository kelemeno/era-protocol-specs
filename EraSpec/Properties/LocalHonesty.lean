import Mathlib.Tactic

/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/LocalHonesty.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  WHAT `HonestInsertion` ACTUALLY COSTS.

  `ProofPolarity` shows the inclusion path's chain binding rests on `HonestInsertion`: every chain's
  tree holds only the commit values of legs originating on that chain.  Stated globally that sounds
  like a large assumption.  This file locates it precisely, and the answer is better than it looks:
  for THIS chain it is enforced by code, and for foreign chains it reduces to running the same code.

  The local enforcement is a three-link authorisation chain, each link a separate contract:

    1. L2InteropCommitmentTree.sol:54    insert(): `if (msg.sender != appender()) revert CommitmentTreeNotAppender`
    2. AtomicFlowManager.sol:76,92       append() is `onlyInteropCenter`: `msg.sender != interopCenter()` reverts
    3. InteropCenter.sol:644,650         the sole `append` call site, in `_dispatchBundle`:
                                             bundleHash = encodeInteropBundleHash(block.chainid, bytes);
                                             ... IAtomicFlowManager(...).append({_bundleHash: bundleHash, ...})

  Two whole-program facts hold the chain together, and both were checked rather than assumed:

    * The tree's MUTATING surface is exactly two functions — `insert` (link 1) and `initL2`
      (`onlyUpgrader`, i.e. governance, which is out of scope by standing exception).  `root`,
      `leafCount`, `leafAt` and `merklePath` are views.  So link 1 has no sibling to bypass it.
    * `append` has exactly ONE call site in the tree (`InteropCenter.sol:650`), so link 3 covers every
      value that can reach link 2.  This is the fragile one: it is a property of the whole program,
      not a guard, so it is exactly what a future contract calling `append` from a second site would
      silently break -- and nothing in the type system would complain.

  The composition itself is trivial, and this file does not pretend otherwise.  Its content is the
  ENUMERATION above and the REDUCTION below: `HonestInsertion` is not a fresh trust assumption layered
  on the protocol, it is precisely "every chain in the leg set runs an unmodified deployment".  That is
  the standard elastic-chain premise, and now it is stated rather than implied.
-/

namespace AttackVectors.LocalHonesty

variable {Chain Value : Type*}

/-! ## The three links, as extracted facts

Each predicate names a stage a value must have passed through.  They are parameters rather than
definitions because their content lives in the Solidity, not here; what this file checks is that the
three compose to the property `ProofPolarity` needs, and that nothing else is required. -/

variable (srcOf : Value → Chain) (thisChain : Chain)
variable (InTree InsertedByAppender AppendedByCenter : Value → Prop)

/-- The deployment's guards, one field per link.  `sole_call_site` is the whole-program fact. -/
structure Guards : Prop where
  /-- Link 1 — `insert` reverts unless `msg.sender == appender()`, and no other mutator exists. -/
  insert_guarded : ∀ v, InTree v → InsertedByAppender v
  /-- Link 2 — the appender is the flow manager, whose `append` is `onlyInteropCenter`. -/
  append_guarded : ∀ v, InsertedByAppender v → AppendedByCenter v
  /-- Link 3 — the sole `append` call site builds its bundle hash with `block.chainid`. -/
  sole_call_site : ∀ v, AppendedByCenter v → srcOf v = thisChain

/-- **THE LOCAL HALF IS CODE-ENFORCED.**  Every value in this chain's tree originates on this chain --
not by assumption, but by the three guards composing.  This is `HonestInsertion` restricted to the
chain running the code. -/
theorem local_honest_insertion (g : Guards srcOf thisChain InTree InsertedByAppender AppendedByCenter)
    {v : Value} (h : InTree v) : srcOf v = thisChain :=
  g.sole_call_site v (g.append_guarded v (g.insert_guarded v h))

/-! ## The reduction

`HonestInsertion` quantifies over every chain.  Instantiating the guards at each chain shows the global
assumption is exactly the conjunction of the local, enforced ones -- so it buys no extra trust beyond
"the other chains run this deployment". -/

/-! Per-chain data: each chain has its own tree and its own copy of the guards. -/

variable (tree : Chain → Set Value) (Inserted Appended : Chain → Value → Prop)

/-- **`HonestInsertion` IS "EVERY CHAIN RUNS THIS CODE".**  Given the guards at every chain, the global
hypothesis `ProofPolarity.inclusion_self_binds` needs follows -- with nothing added.  The premise is
the standard elastic-chain one, not a new assumption introduced by the atomic-interop layer. -/
theorem honestInsertion_of_guards_everywhere
    (g : ∀ c : Chain, Guards srcOf c (· ∈ tree c) (Inserted c) (Appended c)) :
    ∀ c v, v ∈ tree c → srcOf v = c :=
  fun c v h => local_honest_insertion srcOf c (· ∈ tree c) (Inserted c) (Appended c) (g c) h

/-- Conversely the guards are not stronger than needed: `HonestInsertion` is exactly what they give,
so a chain satisfying it vacuously (an empty tree, say) needs no guards at all.  Recorded so the
reduction is read as an equivalence in substance and not as a one-way sufficiency claim. -/
theorem guards_give_exactly_honestInsertion
    (h : ∀ c v, v ∈ tree c → srcOf v = c) (c : Chain) :
    Guards srcOf c (· ∈ tree c) (· ∈ tree c) (· ∈ tree c) :=
  { insert_guarded := fun _ hv => hv
    append_guarded := fun _ hv => hv
    sole_call_site := fun v hv => h c v hv }

/-! ## Where this leaves the polarity result

Combining with `ProofPolarity`:

* Inclusion's self-binding holds for legs on chains running an unmodified deployment -- which is what
  the "defense-in-depth" label was tacitly claiming, now with the claim visible.
* A leg whose declared source chain is NOT running one loses that self-binding, and the explicit
  `sourceChainId` equality check is what still stands between it and a forged finality proof.
* Absence never self-binds regardless, so the refund path's check is unconditional.

The practical upshot for a reviewer is narrow and checkable: the inclusion-side redundancy claim is
only as strong as `sole_call_site`, and that is the one link no compiler enforces. -/

end AttackVectors.LocalHonesty
