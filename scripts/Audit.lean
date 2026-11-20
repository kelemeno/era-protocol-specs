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

Every other declaration of the package is checked the same way. A `def`, `opaque`
constant, inductive type, constructor or recursor that depends on a non-standard
axiom, above all `sorryAx`, is a finding even when no theorem uses it. Lean only
warns about `sorry`, so an unused `def hiddenFalse : False := by sorry` would
otherwise pass.

It also counts `axiom` declarations in the package. That number must be zero:
proofs may use only the admitted logical principles. This does not eliminate
theorem hypotheses, modeling restrictions, or unproved implementation links;
those are recorded separately in ASSUMPTIONS.md.

Separated contract and protocol property propositions are checked for complete proof coverage as well:
the named theorem must reference the proposition and prove its full universally
quantified statement, at every universe level. Missing proofs, special-case-only
proofs (a proof of one universe instance among them), and independently restated
theorem conclusions are rejected. A Properties module may declare only `def`
property statements: an `opaque` property, or a theorem, axiom or inductive type
there, is an error, never a declaration the coverage check skips. So is a `private`
declaration of any kind there: `Name.isInternal` takes a private name's `_private`
prefix for a Lean auxiliary, so the check strips that prefix first (`isUserDecl`).

Property statements may carry one of the tags of `EraSpec.Core.Headline`: `@[headline]` (a real
guarantee about era-contracts `b17415d20`), `@[witness]` (a non-vacuity witness for a headline) or
`@[countermodel]` (a stronger reading or a dropped premise fails). The audit counts each kind
separately, with the untagged properties (supporting lemmas), in total and per contract folder
(`EraSpec.Contracts.<C>`) and protocol area (`EraSpec.Protocol.<A>`), so that the README headline
indexes can be checked against it. It rejects a tag on anything but a property statement (a `def` in
a Properties module), a statement carrying two of the tags, and a `@[headline]` in a `History` module
or namespace (History is the record of an older commit, not a claim about `b17415d20`), and a
`@[headline]` without a docstring (its docstring states every premise; that it states ALL of them,
and that each headline with premises has a witness, stay review items). If the
environment variable `ERASPEC_HEADLINES_OUT` names a file, the audit writes every tagged property to
it, one per line: tag, folder, statement name and module, separated by tabs.

The axiom findings and the tag findings are all printed before the audit fails on any of them.

`scripts/audit-selftest.sh` runs this file against planted defects
(`scripts/audit-selftest/`) and requires each to be rejected for its own reason.
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
private def axiomsOf (n : Name) : CommandElabM (Array Name) :=
  Lean.collectAxioms n

open EraSpec.Headline (hasNamePart isPropertiesModule isUserDecl)

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

/-- The declaration kind, as findings name it. -/
private def kindName : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient primitive"
  | .inductInfo _ => "inductive type"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- The three classification tags of `EraSpec.Core.Headline`, with the names findings use. -/
private def classificationTags : List (String × TagAttribute) :=
  [("headline", EraSpec.Headline.headlineAttr), ("witness", EraSpec.Headline.witnessAttr),
   ("countermodel", EraSpec.Headline.countermodelAttr)]

/-- Every declaration carrying tag `attr`, in any imported module or in this file. -/
private def taggedWith (env : Environment) (attr : TagAttribute) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for i in [0:env.header.moduleNames.size] do
    out := out ++ attr.ext.getModuleEntries env i
  return out ++ (attr.ext.getState env).toArray

/-- The folder a package module reports under: the two name components after `EraSpec`
(`Contracts.<C>`, `Protocol.<A>`; a top-level module reports under its own name). -/
private def folderOf (modName : Name) : String :=
  match modName.components with
  | _ :: a :: b :: _ :: _ => s!"{a}.{b}"
  | _ :: a :: b :: [] => s!"{a}.{b}"
  | _ :: a :: [] => s!"{a}"
  | _ => s!"{modName}"

run_cmd do
  let env ← getEnv
  let mut thms : Nat := 0
  let mut axFree : Nat := 0
  let mut unclean : Array (Name × Array Name) := #[]
  let mut others : Nat := 0
  let mut uncleanOthers : Array (String × Name × Array Name) := #[]
  let mut declaredAxioms : Array Name := #[]
  let mut internalStubs : Nat := 0
  let mut properties : Nat := 0
  -- Every property statement, with its module.
  let mut propertyModules : NameMap Name := {}
  for (n, ci) in env.constants.toList do
    -- Restrict to constants that came from this package's modules.
    let some modIdx := env.getModuleIdxFor? n | continue
    let some modName := env.header.moduleNames[modIdx.toNat]? | continue
    unless (`EraSpec).isPrefixOf modName do continue
    -- A Properties module holds `def` property statements and nothing else. Every
    -- declaration kind is handled here, so none can bypass the coverage check by
    -- being a kind it does not look at. Internal names (`_proof_1`, …) are the
    -- auxiliaries Lean generates for a statement; the axiom check below covers them.
    -- A `private` declaration is not internal (`isUserDecl` strips its `_private`
    -- prefix first), and it is rejected: a property statement is public, so that its
    -- name can be cited and its proof found.
    if isPropertiesModule modName && isUserDecl n then
      if isPrivateName n then
        throwError "{privateToUserName n} in {modName} ({kindName ci}) is private: a Properties module may declare only public `def` property statements"
      match ci with
      | .defnInfo statement =>
        properties := properties + 1
        propertyModules := propertyModules.insert n modName
        unless returnsProp statement.type do
          throwError "property {n} is not a proposition"
        let expectedProof := proofName n
        let some (.thmInfo proof) := env.find? expectedProof
          | throwError "property {n} has no theorem {expectedProof}"
        unless proof.type.getUsedConstants.contains n do
          throwError "theorem {expectedProof} does not reference statement {n}"
        -- Check the WHOLE universally quantified property, not one special
        -- case or a theorem that merely mentions the statement as a premise.
        -- That includes its universes. The property is instantiated at its own
        -- level parameters, which unification never assigns, and only the
        -- proof's levels are metavariables. With metavariables on both sides,
        -- `isDefEq` could specialize the PROPERTY to the proof's universe, and a
        -- proof of `Properties.P.{0}` would pass for `∀ α : Sort u, …`.
        let fullProof ← liftTermElabM do
          let property := mkConst n (statement.levelParams.map mkLevelParam)
          let proof ← Lean.Meta.mkConstWithFreshMVarLevels expectedProof
          let propertyType ← Lean.Meta.inferType property
          Lean.Meta.forallTelescope propertyType fun args _ => do
            let expected ← Lean.Meta.mkForallFVars args (mkAppN property args)
            unless (← Lean.Meta.isDefEq expected (← Lean.Meta.inferType proof)) do
              return false
            -- `isDefEq` can report success with a universe constraint it could
            -- not solve left postponed: `u =?= max ?v 1`, from a proof of
            -- `Properties.P.{max v 1}`, which misses `u = 0`. Every constraint
            -- must actually be solved.
            Lean.Meta.processPostponed (mayPostpone := false)
        unless fullProof do
          throwError "theorem {expectedProof} does not prove the full property {n}"
      | .opaqueInfo _ =>
        throwError "{n} in {modName} is opaque: a property must be a transparent `def`, which the audit checks for a full named proof"
      | _ =>
        throwError "{n} in {modName} ({kindName ci}): a Properties module may declare only `def` property statements"
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
      let axs ← axiomsOf n
      if axs.isEmpty then axFree := axFree + 1
      unless axs.all isStandard do
        unclean := unclean.push (n, axs)
    | _ =>
      -- Every other declaration: def, opaque, inductive type, constructor,
      -- recursor. Its `sorry` is a finding even if no theorem depends on it.
      others := others + 1
      let axs ← axiomsOf n
      unless axs.all isStandard do
        uncleanOthers := uncleanOthers.push (kindName ci, n, axs)
  logInfo m!"theorems audited     : {thms}"
  logInfo m!"other decls audited  : {others}   (defs, opaques, inductive types, constructors, recursors)"
  logInfo m!"properties proved    : {properties}   (each has its full named theorem)"
  logInfo m!"axiom-free           : {axFree}"
  logInfo m!"axioms declared      : {declaredAxioms.size}   (must be 0)"
  logInfo m!"compiler stubs       : {internalStubs}   (internal names; no proof can use them)"
  logInfo m!"NOT clean            : {unclean.size}   (must be 0)"
  logInfo m!"NOT clean, other     : {uncleanOthers.size}   (must be 0)"
  -- Classification tags. A tag sits on a property statement, at most one per statement, and a
  -- `@[headline]` is never a History record.
  let mut tagsOf : NameMap (Array String) := {}
  for (tag, attr) in classificationTags do
    for n in taggedWith env attr do
      tagsOf := tagsOf.insert n (((tagsOf.find? n).getD #[]).push tag)
  let mut tagFindings : Array MessageData := #[]
  let mut counts : Std.HashMap String Nat := {}
  -- folder ↦ (headline, witness, countermodel, untagged)
  let mut byFolder : Std.HashMap String (Nat × Nat × Nat × Nat) := {}
  let mut listing : Array String := #[]
  for (n, tags) in tagsOf.toList do
    match propertyModules.find? n with
    | none =>
      let kind := match env.find? n with
        | some ci => kindName ci
        | none => "unknown declaration"
      let modName := match env.getModuleIdxFor? n with
        | some i => s!"{env.header.moduleNames[i.toNat]?.getD .anonymous}"
        | none => "this file"
      tagFindings := tagFindings.push
        m!"  MISPLACED TAG {n} ({kind} in {modName}) carries @[{tags[0]!}]: only a property statement, a `def` in a Properties module, may carry @[headline], @[witness] or @[countermodel]"
    | some modName =>
      if tags.size > 1 then
        tagFindings := tagFindings.push
          m!"  DOUBLE TAG {n} carries {tags.size} of @[headline], @[witness], @[countermodel]: {", ".intercalate (tags.toList.map (s!"@[{·}]"))}"
      if tags.contains "headline" && (hasNamePart "History" modName || hasNamePart "History" n) then
        tagFindings := tagFindings.push
          m!"  HISTORY HEADLINE {n} in {modName}: a History record is not a guarantee about b17415d20 and may not carry @[headline]"
      if tags.contains "headline" then
        let doc := (← findDocString? env n).getD ""
        if doc.all Char.isWhitespace then
          tagFindings := tagFindings.push
            m!"  HEADLINE WITHOUT DOCSTRING {n} in {modName}: a @[headline] states every premise in its docstring"
      for tag in tags do
        listing := listing.push s!"{tag}\t{folderOf modName}\t{n}\t{modName}"
  for (n, modName) in propertyModules.toList do
    let tags := (tagsOf.find? n).getD #[]
    let (h, w, c, u) := (byFolder.get? (folderOf modName)).getD (0, 0, 0, 0)
    let entry :=
      if tags.size != 1 then (h, w, c, u + (if tags.isEmpty then 1 else 0))
      else match tags[0]! with
        | "headline" => (h + 1, w, c, u)
        | "witness" => (h, w + 1, c, u)
        | _ => (h, w, c + 1, u)
    byFolder := byFolder.insert (folderOf modName) entry
    let key := if tags.isEmpty then "untagged" else if tags.size == 1 then tags[0]! else "multiple"
    counts := counts.insert key ((counts.getD key 0) + 1)
  logInfo m!"headline properties  : {counts.getD "headline" 0}   (real guarantees about b17415d20)"
  logInfo m!"witness properties   : {counts.getD "witness" 0}   (non-vacuity witnesses)"
  logInfo m!"countermodel props   : {counts.getD "countermodel" 0}   (a stronger reading or a dropped premise fails)"
  logInfo m!"untagged properties  : {counts.getD "untagged" 0}   (supporting lemmas)"
  logInfo m!"tag findings         : {tagFindings.size}   (must be 0)"
  logInfo m!"per folder           : headline / witness / countermodel / untagged"
  let folders := byFolder.toArray.qsort (fun a b => a.1 < b.1)
  for (folder, (h, w, c, u)) in folders do
    logInfo m!"  FOLDER {folder} : {h} / {w} / {c} / {u}"
  if let some path ← IO.getEnv "ERASPEC_HEADLINES_OUT" then
    unless path.isEmpty do
      let header := "tag\tfolder\tstatement\tmodule"
      let lines := listing.qsort (· < ·)
      IO.FS.writeFile path (String.intercalate "\n" (header :: lines.toList) ++ "\n")
      logInfo m!"tagged properties written to {path}"
  for f in tagFindings do
    logInfo f
  for n in declaredAxioms do
    logInfo m!"  DECLARED AXIOM {n}"
  for (n, axs) in unclean do
    logInfo m!"  UNCLEAN {n} : {axs}"
  for (kind, n, axs) in uncleanOthers do
    logInfo m!"  UNCLEAN {kind} {n} : {axs}"
  if unclean.size > 0 then
    throwError "audit failed: {unclean.size} result(s) depend on non-standard axioms"
  if uncleanOthers.size > 0 then
    throwError "audit failed: {uncleanOthers.size} other declaration(s) depend on non-standard axioms"
  if declaredAxioms.size > 0 then
    throwError "audit failed: {declaredAxioms.size} axiom(s) declared in EraSpec"
  if tagFindings.size > 0 then
    throwError "audit failed: {tagFindings.size} misplaced, doubled, History or undocumented headline tag(s)"
