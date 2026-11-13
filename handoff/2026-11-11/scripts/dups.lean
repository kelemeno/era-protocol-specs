import Lean
open Lean
def main (mods : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let mut owner : Std.HashMap Name Name := {}
  let mut base : Std.HashSet Name := {}
  -- names already in the pre-round-5 library
  let env0 ← importModules #[{module := `EraSpec}] {} (loadExts := false)
  for (n, _) in env0.constants.toList do base := base.insert n
  for m in mods do
    let mn := m.toName
    let env ← importModules #[{module := mn}] {} (loadExts := false)
    for (n, _) in env.constants.toList do
      if n.isInternal then continue
      let some idx := env.getModuleIdxFor? n | continue
      let some modName := env.header.moduleNames[idx.toNat]? | continue
      unless modName == mn || (mods.contains modName.toString) do continue
      if base.contains n && modName == mn then IO.println s!"CLASH-WITH-BASE {n} in {modName}"
      match owner.get? n with
      | some o => if o != modName then IO.println s!"DUP {n}: {o} vs {modName}"
      | none => owner := owner.insert n modName
