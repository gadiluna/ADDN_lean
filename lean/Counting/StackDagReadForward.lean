import Counting.StackEncodingDagReadPreserving

namespace Counting.StackMachine.DagUpdate
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def readForward : Routine 18 := sequence DagParser.wideNode.routine
  (ofProgram (ListPrograms.reverseProgram 18 2 17))

/-- Consume one canonical node, retaining its forward compact encoding.
The source suffix and caller's status tail are preserved exactly. -/
theorem readForward_executes (store : Store 18) (node : Executable.Node) (suffix : List Bool)
    (accepted : Bool) (tail : List Bool)
    (source : store 0=Encoding.node.encode node++suffix)
    (status : store 1=accepted::tail)
    (empty : ∀ r : Fin 20,2 ≤ r.val → r.val ≤ 17 → store r=[]) :
    ∃ time ≤ 2100*((store 0).length+1)^3,
      Executes readForward store time
        (Function.update (Function.update store 0 suffix) 17 (Encoding.node.encode node)) := by
  have work (r : Fin 20) (member : r∈DagParser.wideNode.work) : store r=[] := by
    change r∈DagParser.node.work.map DagParser.nodeRoles at member
    obtain ⟨small,inside,rfl⟩ := Finset.mem_map.mp member
    obtain ⟨n0,n1,_⟩ := DagParser.node.separate small inside
    apply empty
    · have zero : small.val≠0 := by intro eq;apply n0;exact Fin.ext eq
      have one : small.val≠1 := by intro eq;apply n1;exact Fin.ext eq
      change 2 ≤ small.val
      omega
    · change small.val ≤ 17
      have := small.isLt
      omega
  obtain ⟨time,bound,ran⟩ := DagParser.wideNode.executes store accepted tail status work
  rw [source,DagParser.wideNode.roundtrip] at ran
  let parsed := Function.update (Function.update store 0 suffix) 2 (Encoding.node.encode node).reverse
  have parsedResult : parseStore 0 1 2 store accepted tail ⟨suffix,Encoding.node.encode node,true⟩=parsed := by
    funext r
    by_cases r0 : r=0 <;> by_cases r1 : r=1 <;> by_cases r2 : r=2 <;>
      simp_all [parseStore,parsed]
  rw [parsedResult] at ran
  have reversed := reverse_executes 18 (2:Fin 20) 17 (by decide) parsed
  have codeAt : parsed 2=(Encoding.node.encode node).reverse := by simp [parsed]
  have outputAt : parsed 17=[] := by simp [parsed,empty]
  rw [codeAt,outputAt,List.length_reverse,List.reverse_reverse,List.append_nil] at reversed
  have final : Function.update (Function.update parsed 2 []) 17 (Encoding.node.encode node)=
      Function.update (Function.update store 0 suffix) 17 (Encoding.node.encode node) := by
    funext r
    by_cases r0 : r=0 <;> by_cases r2 : r=2 <;> by_cases r17 : r=17 <;>
      simp [parsed,r0,r2,r17,empty]
  rw [final] at reversed
  refine ⟨time+1+(2*(Encoding.node.encode node).length+1),?_,ran.sequence reversed⟩
  change time ≤ 2029*((store 0).length+1)^3 at bound
  have codeLength : (Encoding.node.encode node).length ≤ (store 0).length := by
    rw [source,List.length_append]
    omega
  have linear : (store 0).length+1 ≤ ((store 0).length+1)^3 := Nat.le_self_pow (by decide) _
  omega

end Counting.StackMachine.DagUpdate
