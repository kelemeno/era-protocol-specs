import EraSpec

/-!
# The axiom audit, driven from the ENVIRONMENT rather than from source text

An earlier version of this audit reconstructed declaration names by regex over the
`.lean` files and fed them to `#print axioms`.  It reported "327 clean, 0 unclean"
while silently failing to resolve 25 declarations — every `private lemma`, plus
anything whose enclosing namespace the regex guessed wrongly.  A clean result with
a hidden hole is the exact failure mode this repo's sibling documents at length:
*every one of these failures reads as success.*

So this version asks the Lean environment which theorems exist, which cannot miss
a `private` declaration, cannot mis-resolve a namespace, and does not care how
`#print axioms` formats or wraps its output.

It also counts `axiom` declarations in the package. That number must be zero:
proofs may use only the admitted logical principles. This does not eliminate
theorem hypotheses, modeling restrictions, or unproved implementation links;
those are recorded separately in ASSUMPTIONS.md.

Separated contract and protocol property propositions are checked for complete proof coverage as well:
the named theorem must reference the proposition and prove its full universally
quantified statement. Missing proofs, special-case-only proofs, and independently
restated theorem conclusions are rejected.
-/

open Lean Elab Command

/-- Lean's three standard axioms.  Anything else — above all `sorryAx` — is a
finding. -/
private def isStandard (a : Name) : Bool :=
  a == ``propext || a == ``Quot.sound || a == ``Classical.choice

/-- The axiom set a declaration actually depends on.

This reuses the *same* traversal `#print axioms` uses
(`Lean.Elab.Command.CollectAxioms`), so the audit and the command a reviewer would
type by hand cannot disagree — but it returns the set as data instead of as
formatted text, which is what removes the print-order and line-wrapping hazards. -/
private def axiomsOf (env : Environment) (n : Name) : Array Name :=
  (((CollectAxioms.collect n).run env).run {}).2.axioms

private def hasPart (part : String) : Name → Bool
  | .anonymous => false
  | .str parentName s => s == part || hasPart part parentName
  | .num parentName _ => hasPart part parentName

/-- Statements add a `Properties` namespace segment; their public proofs keep
the original name. Removing that segment gives the required proof declaration. -/
private def proofName : Name → Name
  | .anonymous => .anonymous
  | .str parentName "Properties" => parentName
  | .str parentName s => .str (proofName parentName) s
  | .num parentName i => .num (proofName parentName) i

private def returnsProp : Expr → Bool
  | .forallE _ _ body _ => returnsProp body
  | .sort .zero => true
  | _ => false

run_cmd do
  let env ← getEnv
  let mut thms := 0
  let mut axFree := 0
  let mut unclean : Array (Name × Array Name) := #[]
  let mut declaredAxioms : Array Name := #[]
  let mut internalStubs := 0
  let mut properties := 0
  for (n, ci) in env.constants.toList do
    -- Restrict to constants that came from this package's modules.
    let some modIdx := env.getModuleIdxFor? n | continue
    let some modName := env.header.moduleNames[modIdx.toNat]? | continue
    unless (`EraSpec).isPrefixOf modName do continue
    if hasPart "Properties" modName then
      if let .defnInfo statement := ci then
        unless n.isInternal do
          properties := properties + 1
          unless returnsProp statement.type do
            throwError "property {n} is not a proposition"
          let expectedProof := proofName n
          let some (.thmInfo proof) := env.find? expectedProof
            | throwError "property {n} has no theorem {expectedProof}"
          unless proof.type.getUsedConstants.contains n do
            throwError "theorem {expectedProof} does not reference statement {n}"
          -- Check the WHOLE universally quantified property, not one special
          -- case or a theorem that merely mentions the statement as a premise.
          let fullProof ← liftTermElabM do
            let property ← Lean.Meta.mkConstWithFreshMVarLevels n
            let proof ← Lean.Meta.mkConstWithFreshMVarLevels expectedProof
            let propertyType ← Lean.Meta.inferType property
            Lean.Meta.forallTelescope propertyType fun args _ => do
              let expected ← Lean.Meta.mkForallFVars args (mkAppN property args)
              Lean.Meta.isDefEq expected (← Lean.Meta.inferType proof)
          unless fullProof do
            throwError "theorem {expectedProof} does not prove the full property {n}"
    match ci with
    | .axiomInfo _ =>
      -- Lean's compiler emits `axiomInfo` stubs for specialized/erased code paths
      -- (`_elambda_N`, `._at._spec_N`, `npowRec._at…`).  Those are code-generation
      -- artifacts with internal names, not logical assumptions, and no proof term
      -- can mention them — the `unclean` tally is what would catch it if one did.
      -- Only NON-internal names would be a real `axiom` declaration.
      if n.isInternal then
        internalStubs := internalStubs + 1
      else
        declaredAxioms := declaredAxioms.push n
    | .thmInfo _ =>
      thms := thms + 1
      let axs := axiomsOf env n
      if axs.isEmpty then axFree := axFree + 1
      unless axs.all isStandard do
        unclean := unclean.push (n, axs)
    | _ => pure ()
  logInfo m!"theorems audited     : {thms}"
  logInfo m!"properties proved    : {properties}   (each has its full named theorem)"
  logInfo m!"axiom-free           : {axFree}"
  logInfo m!"axioms declared      : {declaredAxioms.size}   (must be 0)"
  logInfo m!"compiler stubs       : {internalStubs}   (internal names; no proof can use them)"
  logInfo m!"NOT clean            : {unclean.size}   (must be 0)"
  for n in declaredAxioms do
    logInfo m!"  DECLARED AXIOM {n}"
  for (n, axs) in unclean do
    logInfo m!"  UNCLEAN {n} : {axs}"
  if unclean.size > 0 then
    throwError "audit failed: {unclean.size} result(s) depend on non-standard axioms"
  if declaredAxioms.size > 0 then
    throwError "audit failed: {declaredAxioms.size} axiom(s) declared in EraSpec"
