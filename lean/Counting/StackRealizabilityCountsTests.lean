import Counting.StackRealizabilityCountsSpec
import Counting.StackDagTestRun

namespace Counting.StackMachine.RealizabilityCheck.Tests
open Routine

private def requireCounts (values : List Nat) (total expected : Nat) (accepted : Bool) : IO Unit:=do
  let suffix:=[false,true,true,false]
  let tail:=[false,true]
  let store : Store 20:=fun r=>
    if r=17 then (Encoding.list Encoding.natural).encode values++suffix
    else if r=1 then accepted::tail
    else if r=19 then total.bits
    else if r=21 then List.replicate expected true else []
  let actual:=(accepted && values.all (fun value=>decide (0<value))) && decide (values.length=expected)
  match DagValidation.TestRun.run countsShape.program 3000000 0 ⟨0,store⟩ with
  | none=>throw (IO.userError "Compact count scan exceeded test fuel")
  | some (steps,result)=>
    let wanted:=countsShapeStore store accepted tail suffix total expected values
    unless (List.finRange 22).all (fun r=>result.store r==wanted r) do
      throw (IO.userError "Compact count scan failed its full-store contract")
    unless result.store 19==(total+values.sum).bits && result.store 1==actual::tail &&
        result.store 0==List.replicate values.length true do
      throw (IO.userError "Compact count scan returned wrong sum, length or positivity")
    unless steps≤2030*((store 17).length+total.size+expected+1)^3 do
      throw (IO.userError "Compact count scan exceeded its proved polynomial")
    IO.println s!"Compact counts: {values.length} entries, {steps} stack instructions, result {actual}."

def tests : IO Unit:=do
  requireCounts [] 0 0 true
  requireCounts [] 7 1 true
  requireCounts [1] 0 1 true
  requireCounts [0] 0 1 true
  requireCounts [2] 0 1 true
  requireCounts [1,2,3] 4 3 true
  requireCounts [1,0,3] 4 3 true
  requireCounts [1,2,3] 4 2 true
  requireCounts [1,2,3] 4 4 true
  requireCounts [1,2,3] 4 3 false
  requireCounts [1] (2^128-1) 1 true
  requireCounts [2^128,2^128,2^128] (2^129) 3 true
  IO.println "Compact certificate counts passed 12 full-store cases, including large binary values, even values, zero, carries and length mismatch."

#eval tests
end Counting.StackMachine.RealizabilityCheck.Tests
