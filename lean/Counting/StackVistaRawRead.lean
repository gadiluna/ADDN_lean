import Counting.StackEncodingDagParser
import Counting.StackEncodingParserRelabel
import Counting.StackRoutineLists

namespace Counting.StackMachine.DagUpdate.Raw
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def nodesRoles : Fin 17 ↪ Fin 96 := ⟨![0,71,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],by decide⟩

def readNodes : Routine 94 := sequence (mapRegisters nodesRoles DagParser.nodes.routine)
  (ofProgram (ListPrograms.reverseProgram 94 2 64))

theorem readNodes_executes (store : Store 94) (nodes : Array Executable.Node)
    (suffix : List Bool) (source : store 0=(Encoding.list Encoding.node).encode nodes.toList++suffix)
    (flag : store 71=[true]) (target : store 64=[])
    (empty : ∀ r:Fin 96,2≤r.val → r.val≤16 → store r=[]) :
    ∃ time ≤ Complexity.polynomial DagParser.nodes.coefficient DagParser.nodes.exponent (store 0).length+
        2*((Encoding.list Encoding.node).encode nodes.toList).length+2,
      Executes readNodes store time
        (Function.update (Function.update store 0 suffix) 64 ((Encoding.list Encoding.node).encode nodes.toList)) := by
  let parser := DagParser.nodes.relabel nodesRoles
  have work (r : Fin 96) (member : r∈parser.work) : store r=[] := by
    change r∈DagParser.nodes.work.map nodesRoles at member
    obtain ⟨i,mem,rfl⟩ := Finset.mem_map.mp member
    obtain ⟨a,b,c⟩ := DagParser.nodes.separate i mem
    fin_cases i <;> simp_all [nodesRoles]
  obtain ⟨time,bound,parsing⟩ := parser.executes store true [] flag work
  change time ≤ Complexity.polynomial DagParser.nodes.coefficient DagParser.nodes.exponent (store 0).length at bound
  change Executes (mapRegisters nodesRoles DagParser.nodes.routine) store time
    (parseStore (0:Fin 96) 71 2 store true [] (DagParser.nodes.effect (store 0))) at parsing
  rw [source,DagParser.nodes.roundtrip] at parsing
  let parsed := Function.update (Function.update store 0 suffix) 2
    ((Encoding.list Encoding.node).encode nodes.toList).reverse
  have parsedEq : parseStore (0:Fin 96) 71 2 store true []
      ⟨suffix,(Encoding.list Encoding.node).encode nodes.toList,true⟩=parsed := by
    funext r
    by_cases a:r=0 <;> by_cases b:r=71 <;> by_cases c:r=2 <;>
      simp_all [parseStore,parsed]
  rw [parsedEq] at parsing
  have reversed := reverse_executes 94 (2:Fin 96) 64 (by decide) parsed
  rw [show parsed 2=((Encoding.list Encoding.node).encode nodes.toList).reverse by simp [parsed],
    show parsed 64=[] by simp [parsed,target],List.reverse_reverse,List.append_nil,List.length_reverse] at reversed
  have final : Function.update (Function.update parsed 2 []) 64 ((Encoding.list Encoding.node).encode nodes.toList)=
      Function.update (Function.update store 0 suffix) 64 ((Encoding.list Encoding.node).encode nodes.toList) := by
    funext r
    by_cases a:r=0 <;> by_cases b:r=2 <;> by_cases c:r=64 <;> simp_all [parsed]
  rw [final] at reversed
  exact ⟨_,by omega,parsing.sequence reversed⟩

end Counting.StackMachine.DagUpdate.Raw
