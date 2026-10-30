import Counting.ComplexityInclusions

/-! Small kernel-checked regressions for the concrete class-inclusion
machines. The general correctness and cost statements are proved in the
imported modules; these cover empty, malformed and nonempty-witness paths. -/
namespace Counting.Machine

def firstBitProgram : Program where
  states := 2
  code state symbol := if state.val = 0 then
    some (if symbol = .one then 1 else 2, .write symbol) else none
  accept state := state == 1

def runAcceptance (program : Program) (input : List Bool) (steps : Nat) : Option Bool :=
  (run (step program) steps (initial program input)).map (fun output =>
    (step program output).isNone && program.accept output.control)

example : runAcceptance (framedVerifier firstBitProgram) (Encoding.frame []) 9 = some false := by decide
example : runAcceptance (framedVerifier firstBitProgram) (Encoding.frame [true]) 13 = some true := by decide
example : runAcceptance (framedVerifier firstBitProgram) (Encoding.frame [false, true]) 17 = some false := by decide
example : runAcceptance (framedVerifier firstBitProgram) (Encoding.pairWords [true] [false]) 4 = some false := by decide
example : runAcceptance (framedVerifier firstBitProgram) [] 0 = some false := by decide
example : runAcceptance (framedVerifier firstBitProgram) [true] 1 = some false := by decide
example : runAcceptance (framedVerifier firstBitProgram) [true, true] 2 = some false := by decide

end Counting.Machine
