import Counting.StackFrameReplaceArray

namespace Counting.StackMachine.FieldAccess.ReplaceTests

def roles : Fin 5 ↪ Fin 7 where
  toFun i := ![4,0,6,2,5] i
  inj' := by decide

def testStore (input index replacement : List Bool) : Fin 7 → List Bool := fun r =>
  if r=roles 0 then input else if r=roles 1 then index else if r=roles 2 then replacement else
  if r=1 then [false,true,false] else if r=3 then [true,true] else []

private def requireRun (input index replacement : List Bool) : IO Unit := do
  let routine := replaceRoutine 2 roles
  let store := testStore input index replacement
  let expected := Function.update (Function.update store (roles 1) []) (roles 0)
    (replaceFieldWord input index.length replacement)
  let cost := replaceCost input index replacement
  match Machine.run (step routine.program) cost ⟨0,store⟩ with
  | none => throw (IO.userError "Field replacement stopped before exact cost")
  | some finish =>
      unless (step routine.program finish).isNone do
        throw (IO.userError "Field replacement exceeded exact cost")
      unless (List.finRange 7).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "Field replacement changed an unrelated register or returned wrong bytes")
      unless cost ≤ 5*input.length+3*index.length+5*replacement.length+8 do
        throw (IO.userError "Field replacement exceeded the proved linear bound")
      unless (finish.store (roles 0)).length ≤ input.length+replacement.length do
        throw (IO.userError "Field replacement exceeded its proved output-size bound")

def tests : IO Unit := do
  for values in [[0],[1,0],[3,0,7],[2^128,0,2^64]] do
    let array := values.toArray
    let input := (Encoding.array Encoding.natural).encode array
    for index in List.range array.size do
      for replacement in [0,1,2^130] do
        let field := Encoding.natural.encode replacement
        unless replaceFieldWord input (index+1) field ==
            (Encoding.array Encoding.natural).encode (array.setIfInBounds index replacement) do
          throw (IO.userError "Array setter disagrees with the exact encoded-array specification")
        requireRun input (List.replicate (index+1) false) field
  for input in [[],[true],[false],[true,false],[true,true,true],[false,false,true],
      Encoding.frame [false,true]++[true],Encoding.frame [false,false]++Encoding.frame []] do
    for index in [[],[false],[true,false],List.replicate 12 true] do
      for replacement in [[],[true],Encoding.natural.encode 0,Encoding.natural.encode (2^80)] do
        requireRun input index replacement
  IO.println "Field replacement passed 155 exact-cost full-store cases: actual arrays, 131-bit values, malformed frames, total out-of-range extension, scratch and operand preservation."

#eval tests
end Counting.StackMachine.FieldAccess.ReplaceTests
