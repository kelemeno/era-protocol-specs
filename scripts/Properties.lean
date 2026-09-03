import EraSpec

/-!
# The property checker

Every `def … : Prop` under `EraSpec.Properties.*` is a stated property.  Every
theorem anywhere in the environment whose type is EXACTLY that constant is a
certificate for it.  This command lists each property as `PROVED` (naming its
certificate) or `OPEN`.

Like `scripts/Audit.lean`, this reads the ENVIRONMENT, not source text: a
property cannot be missed by a regex, and a certificate counts only if the kernel
accepted a theorem of precisely the property's type — a proof of something
merely similar does not.

Self-test in the failing direction: add `def Bogus : Prop := False` to any
`Properties/*.lean`, rebuild, and it must appear as `OPEN`.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  -- Stated properties: Prop-valued definitions in the Properties modules.
  let mut props : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let some modIdx := env.getModuleIdxFor? n | continue
    let some modName := env.header.moduleNames[modIdx.toNat]? | continue
    unless (`EraSpec.Properties).isPrefixOf modName do continue
    if n.isInternal then continue
    match ci with
    | .defnInfo d => if d.type.isProp then props := props.push n
    | _ => pure ()
  -- Certificates: theorems whose type is exactly a property constant.
  let mut certs : Array (Name × Name) := #[]
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo t =>
      match t.type with
      | .const p [] => if props.contains p then certs := certs.push (p, n)
      | _ => pure ()
    | _ => pure ()
  let sorted := props.qsort (fun a b => a.toString < b.toString)
  let mut nOpen := 0
  logInfo m!"properties stated : {props.size}"
  for p in sorted do
    match certs.find? (fun c => c.1 == p) with
    | some (_, c) => logInfo m!"  PROVED  {p}  ⟵  {c}"
    | none =>
      nOpen := nOpen + 1
      logInfo m!"  OPEN    {p}"
  logInfo m!"proved            : {props.size - nOpen}"
  logInfo m!"open              : {nOpen}"
