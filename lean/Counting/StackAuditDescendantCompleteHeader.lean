import Counting.StackAuditDescendantCompleteNodes
import Counting.StackEncodingListReadHeader
import Counting.EncodingVerifier

namespace Counting.StackMachine.AuditDescendant
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def completeHeaderRoles : FullListWorkspace 31 :=
  ⟨![17,1,2,3,44,4,5,6,7,8,9,10,11,12,13,14,15],by decide⟩

abbrev readCompleteHeader : Routine 46 := sequence (ofProgram (ListPrograms.copyProgram 45 46 17 47))
  (sequence (pushBit 1 true) (sequence (readListHeader 31 completeHeaderRoles)
    (sequence (clear 17) (clear 1))))

def completeHeaderFile (vista : Executable.Vista) (weights : Array Nat) (anchor last : Nat) : Store 46 :=
  Function.update (completeNodesFile vista weights anchor last) 44 (List.replicate vista.nodes.size true)

/-- The exact outer-loop budget is read from the serialized node array.
Its canonical content bounds the header's unary conversion. -/
theorem readCompleteHeader_executes (vista : Executable.Vista) (weights : Array Nat) (anchor last : Nat) :
    ∃ time ≤ 2000*(((Encoding.array Encoding.node).encode vista.nodes).length+1)^3,
      Executes readCompleteHeader (completeNodesFile vista weights anchor last) time
        (completeHeaderFile vista weights anchor last) := by
  let initial:=completeNodesFile vista weights anchor last
  have a:=copy_executes 45 (46:Fin 48) 17 47 (by decide) (by decide) (by decide) initial
    (by simp [initial,completeNodesFile,completeInputFile])
  have source : initial 46=(Encoding.array Encoding.node).encode vista.nodes := by simp [initial,completeNodesFile]
  have vacant : initial 17=[] := by simp [initial,completeNodesFile,completeInputFile]
  rw [source,vacant,List.append_nil] at a
  let copied:=Function.update initial 17 ((Encoding.array Encoding.node).encode vista.nodes)
  have b:=pushBit_executes (1:Fin 48) true copied
  have e1 : copied 1=[] := by simp [copied,initial,completeNodesFile,completeInputFile]
  rw [e1] at b
  let flagged:=Function.update copied 1 [true]
  obtain ⟨headerTime,headerBound,c⟩:=readListHeader_canonical 31 completeHeaderRoles flagged true []
    (by simp [flagged,completeHeaderRoles]) (by
      intro i member
      fin_cases i <;> simp_all [flagged,copied,initial,completeNodesFile,completeInputFile,completeHeaderRoles])
    Encoding.node Encoding.node_positive_length vista.nodes.toList []
    (by simp [flagged,copied,completeHeaderRoles];rfl)
  let parsed:=Function.update (Function.update flagged 17 (Encoding.sequence Encoding.node vista.nodes.toList))
    44 (List.replicate vista.nodes.size true)
  have parsedStore : Function.update (Function.update flagged (completeHeaderRoles 0)
      (Encoding.sequence Encoding.node vista.nodes.toList++[])) (completeHeaderRoles 4)
        (List.replicate vista.nodes.toList.length true)=parsed := by simp [parsed,completeHeaderRoles]
  rw [parsedStore] at c
  have d:=clear_executes (17:Fin 48) parsed
  have table : parsed 17=Encoding.sequence Encoding.node vista.nodes.toList := by simp [parsed]
  rw [table] at d
  let erased:=Function.update parsed 17 []
  have e:=clear_executes (1:Fin 48) erased
  have status : erased 1=[true] := by simp [erased,parsed,flagged]
  rw [status,List.length_singleton] at e
  have final : Function.update erased 1 []=completeHeaderFile vista weights anchor last := by
    funext r
    fin_cases r <;> simp [erased,parsed,flagged,copied,initial,completeHeaderFile,completeNodesFile,completeInputFile]
  rw [final] at e
  have input : flagged (completeHeaderRoles 0)=(Encoding.array Encoding.node).encode vista.nodes := by
    simp [flagged,copied,completeHeaderRoles]
  rw [input] at headerBound
  have bare : (Encoding.sequence Encoding.node vista.nodes.toList).length≤
      ((Encoding.array Encoding.node).encode vista.nodes).length := by
    change _≤(Encoding.natural.encode vista.nodes.size++Encoding.sequence Encoding.node vista.nodes.toList).length
    simp only [List.length_append];omega
  have linear : ((Encoding.array Encoding.node).encode vista.nodes).length+1≤
      (((Encoding.array Encoding.node).encode vista.nodes).length+1)^3:=Nat.le_self_pow (by decide) _
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence e)))⟩
  change 5*((Encoding.array Encoding.node).encode vista.nodes).length+2+1+
    (1+1+(headerTime+1+((Encoding.sequence Encoding.node vista.nodes.toList).length+1+1+2)))≤
      2000*(((Encoding.array Encoding.node).encode vista.nodes).length+1)^3
  omega

end Counting.StackMachine.AuditDescendant
