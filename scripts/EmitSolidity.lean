import EraSpec.Codegen.Emit
import EraSpec.Codegen.BridgedTokenSlice.Specs.Program

/-! Prints the emitted Solidity for the bridged-token slice to stdout. -/

def main : IO UInt32 := do
  match Codegen.Emit.contract Codegen.BridgedTokenSlice.program
      "Codegen.BridgedTokenSlice.program" with
  | .ok src => IO.print src; pure 0
  | .error e => IO.eprintln s!"emission refused: {e}"; pure 1
