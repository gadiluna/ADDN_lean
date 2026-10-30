import Counting.ExternalMatchingClauseLoop
import Counting.StackMachineTestMemo

namespace Counting.External.MatchingMachine.ClauseTests
open StackMachine
private def workspace : LiteralWorkspace 2 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 50=>i.val) h)⟩

def tests : IO Unit := do
  let program := TestRun.tabulate (generateClauseLoop 2 workspace).program
  let mut maximum := 0
  for n in [1,3] do
    for count in [0,1,2] do
      for offset in [0,3] do
        let clause : List (Nat×Bool) := [(0,false),(n-1,true),(0,true)]
        let clauses := List.replicate count clause
        let width := 3*count+1
        let shift := n*width
        let first := shift+2
        let suffix := [false,true,false]
        let store : Fin 50 → List Bool := fun r=>
          if r=0 then Encoding.sequence (Encoding.list (Encoding.product Encoding.natural Encoding.boolean)) clauses++suffix
          else if r=1 then [true,false] else if r=17 then List.replicate n true
          else if r=23 then List.replicate count true else if r=32 then List.replicate width true
          else if r=33 then List.replicate shift true else if r=34 then List.replicate offset true
          else if r=35 then List.replicate first true else if r=36 then [true,false]
          else if r=48 then [false,true,true] else if r=49 then [false,false] else []
        let expected := clauseLoopResult 2 workspace store first width shift offset clauses suffix
        match TestRun.finishWithin program 2000000 ⟨0,store⟩ with
        | none => throw (IO.userError "matching clause loop exceeded test fuel")
        | some (steps,finish) =>
          unless (List.finRange 50).all (fun r=>finish.store r==expected r) do
            throw (IO.userError "matching clause loop disagrees with full-store contract")
          maximum := max maximum steps
  IO.println s!"Matching clause loops: 12 full-store cases passed, including both signs, boundary variable indices, empty formulas, nonzero occurrence offsets and suffix/sentinel preservation; maximum {maximum} stack transitions."
#eval tests
end Counting.External.MatchingMachine.ClauseTests
