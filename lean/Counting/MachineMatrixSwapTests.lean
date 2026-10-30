import Counting.MachineMatrixSwapGaussian
import Counting.MachineTestMemo

namespace Counting.Machine.MatrixSwapTests
open StackMachine.MatrixSwap

private def stackFinish (program : StackMachine.Program) : Nat → Nat → StackMachine.Config program →
    Option (Nat×StackMachine.Config program)
  | 0,_,_ => none
  | fuel+1,steps,config => match StackMachine.step program config with
    | none => some (steps,config)
    | some next => stackFinish program fuel (steps+1) next

private def stackTest (rows : List (List Rat)) (first second : Fin rows.length) : IO Unit := do
  let code := Encoding.rationalMatrix.encode rows
  let expected := Encoding.rationalMatrix.encode ((rows.set first.val rows[second.val]).set second.val rows[first.val])
  let store := file code (List.replicate (first.val+1) true) (List.replicate (second.val+1) true) [] [] []
  match stackFinish swapRoutine.program 1000000 0 ⟨0,store⟩ with
  | none => throw (IO.userError "Matrix swap exhausted stack budget")
  | some (steps,finish) =>
      unless (List.finRange 10).all (fun r => finish.store r==file expected [] [] [] [] [] r) &&
          steps≤100*(code.length+1) do
        throw (IO.userError "Matrix swap full-store or cost mismatch")

private def physicalTest (rows : List (List Rat)) (first second : Fin rows.length) : IO Unit := do
  let input := inputWord rows first.val second.val
  let expected := Encoding.rationalMatrix.encode ((rows.set first.val rows[second.val]).set second.val rows[first.val])
  match TestMemo.finishWithin matrixSwapProgram 10000000 0 (TestMemo.empty matrixSwapProgram)
      (initial matrixSwapProgram input) with
  | none => throw (IO.userError "Matrix swap exhausted physical test budget")
  | some (steps,finish) =>
      let right := finish.tape.head::finish.tape.right
      unless finish.tape.left.all (· == .blank) && right.take expected.length==expected.map bitSymbol &&
          (right.drop expected.length).all (· == .blank) && steps≤(20*513^2)*(input.length+1)^2 do
        throw (IO.userError "Matrix swap dirty tape, wrong result or cost failure")
      IO.println s!"Matrix swap {first.val}/{second.val}: {steps} physical transitions, clean tape."

def tests : IO Unit := do
  let matrices : List (List (List Rat)) := [[[1]],[[],[]],[[1],[2]],[[-1,0],[1/2,3]],
    [[1],[2],[3]],[[2^128],[0]],[[1,2],[],[-3]]]
  for rows in matrices do
    for first in List.finRange rows.length do
      for second in List.finRange rows.length do stackTest rows first second
  physicalTest [[],[]] ⟨0,by decide⟩ ⟨1,by decide⟩
  physicalTest [[1],[2]] ⟨0,by decide⟩ ⟨1,by decide⟩
  physicalTest [[0]] ⟨0,by decide⟩ ⟨0,by decide⟩
  IO.println "Matrix swap passed 35 full-store and 3 physical-machine cases."

#eval tests
end Counting.Machine.MatrixSwapTests
