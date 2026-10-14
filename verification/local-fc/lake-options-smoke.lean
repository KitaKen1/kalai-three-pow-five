import Lean
open Lean Elab Command
run_cmd do
  let opts ← getOptions
  if opts.getBool `debug.skipKernelTC true then
    throwError "Kernel checking was not explicitly enabled"
  if opts.getBool `Elab.async true then
    throwError "Asynchronous elaboration was not explicitly disabled"
theorem checked_arithmetic : (1 : Nat) + 1 = 2 := by decide
#print axioms checked_arithmetic
