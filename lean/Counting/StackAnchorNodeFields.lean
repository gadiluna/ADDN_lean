import Counting.StackDagHeader
import Counting.StackNaturalPayloadRead

namespace Counting.StackMachine.AnchorNode
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def file (input level parent leader degree flag : List Bool) : Store 7 :=
  ![input,level,parent,leader,degree,flag,[],[],[]]
def headerRoles : Fin 6 ↪ Fin 9 := ⟨![0,1,2,3,5,6],by decide⟩
abbrev fields : Routine 7 := sequence (DagValidation.headerRoutine 3 headerRoles)
  (sequence (readNaturalPayload 5 0 4 6 5) (clear 5))

theorem fields_executes (node : Executable.Node) (suffix : List Bool) :
    ∃ time  ≤  10*(Encoding.node.encode node++suffix).length+30,
      Executes fields (file (Encoding.node.encode node++suffix) [] [] [] [] []) time
        (file ((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming++suffix)
          node.level.bits (DagValidation.parentCode node).bits [node.leader] node.degree.bits []) := by
  let rest := (Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming++suffix
  let start := file (Encoding.node.encode node++suffix) [] [] [] [] []
  obtain ⟨headerTime,headerBound,headerRun⟩ := DagValidation.header_executes 3 headerRoles start rfl
  have header := DagValidation.header_node node suffix
  let parsed := file (Encoding.natural.encode node.degree++rest) node.level.bits
    (DagValidation.parentCode node).bits [node.leader] [] [true]
  have headerStore : DagValidation.headerStore 3 headerRoles start=parsed := by
    funext r;fin_cases r <;> simp [DagValidation.headerStore,start,file,headerRoles,header,parsed,rest,List.append_assoc]
  rw [headerStore] at headerRun
  obtain ⟨degreeTime,degreeBound,degreeRun⟩ := readNaturalPayload_executes 5 (0:Fin 9) 4 6 5
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    parsed node.degree rest true [] rfl rfl rfl rfl
  let extracted := file rest node.level.bits (DagValidation.parentCode node).bits [node.leader] node.degree.bits [true]
  have degreeStore : Function.update (Function.update parsed 0 rest) 4 node.degree.bits=extracted := by
    funext r;fin_cases r <;> simp [parsed,extracted,file]
  rw [degreeStore] at degreeRun
  have cleared := clear_executes (5:Fin 9) extracted
  have clearStore : Function.update extracted 5 []=
      file rest node.level.bits (DagValidation.parentCode node).bits [node.leader] node.degree.bits [] := by
    funext r;fin_cases r <;> simp [extracted,file]
  rw [clearStore] at cleared
  refine ⟨_,?_,headerRun.sequence (degreeRun.sequence cleared)⟩
  change headerTime ≤ 6*(Encoding.node.encode node++suffix).length+17 at headerBound
  change degreeTime ≤ 3*(Encoding.natural.encode node.degree++rest).length+8 at degreeBound
  have suffixBound := DagValidation.header_suffix_le (Encoding.node.encode node++suffix)
  rw [header] at suffixBound
  simp only [List.append_assoc] at suffixBound
  change (Encoding.natural.encode node.degree++rest).length ≤ (Encoding.node.encode node++suffix).length at suffixBound
  change headerTime+1+(degreeTime+1+2) ≤  _
  omega

end Counting.StackMachine.AnchorNode
