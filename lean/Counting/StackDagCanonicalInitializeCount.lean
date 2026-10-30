import Counting.StackDagCanonicalInitializeRead
import Counting.StackEncodingListReadHeader

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def initializeCountRoles : FullListWorkspace 113 :=
  ⟨![126,104,0,1,123,2,3,4,5,6,7,8,9,10,11,12,13],by decide⟩

def initializeCount : Routine 128 := sequence (copyExternal 20 26)
  (sequence (readListHeader 113 initializeCountRoles)
    (sequence (clearExternal 26) (copyExternal 23 24)))

def initializeCountData (data : Fin 30→List Bool) (nodes : Array Executable.Node) : Fin 30→List Bool :=
  Function.update (Function.update data 23 (List.replicate nodes.size true)) 24 (List.replicate nodes.size true)

theorem initializeCount_executes (data : Fin 30→List Bool) (nodes : Array Executable.Node)
    (encoded : data 20=(Encoding.array Encoding.node).encode nodes) (flag : data 4=[true])
    (e23 : data 23=[]) (e24 : data 24=[]) (e26 : data 26=[]) :
    ∃ time ≤ 1900*((data 20).length+1)^3,
      Executes initializeCount (file data) time (file (initializeCountData data nodes)) := by
  have copied := copyExternal_executes data 20 26 (by decide)
  rw [e26,List.append_nil] at copied
  let a := Function.update data 26 (data 20)
  obtain ⟨th,bh,rh⟩ := readListHeader_canonical 113 initializeCountRoles (file a) true []
    (by simp [initializeCountRoles,file,a,flag])
    (by intro i member;fin_cases i <;> simp_all [initializeCountRoles,file,a])
    Encoding.node Encoding.node_positive_length nodes.toList []
    (by simp [initializeCountRoles,file,a,encoded,Encoding.array,Encoding.transport])
  have source : file a (initializeCountRoles 0)=data 20 := by simp [initializeCountRoles,file,a]
  rw [source] at bh
  let b := Function.update (Function.update a 26 (Encoding.sequence Encoding.node nodes.toList))
    23 (List.replicate nodes.size true)
  have readOutput : Function.update (Function.update (file a) (initializeCountRoles 0)
      (Encoding.sequence Encoding.node nodes.toList++[]))
      (initializeCountRoles 4) (List.replicate nodes.toList.length true)=file b := by
    change Function.update (Function.update (file a) (context 26) _) (context 23) _=_
    simp only [List.append_nil,Array.length_toList,file_update,b]
  rw [readOutput] at rh
  have cleared := clearExternal_executes b 26
  have payload : b 26=Encoding.sequence Encoding.node nodes.toList := by simp [b]
  rw [payload] at cleared
  let c := Function.update b 26 []
  have duplicated := copyExternal_executes c 23 24 (by decide)
  rw [show c 23=List.replicate nodes.size true by simp [c,b],
    show c 24=[] by simp [c,b,a,e24],List.append_nil,List.length_replicate] at duplicated
  have final : Function.update c 24 (List.replicate nodes.size true)=initializeCountData data nodes := by
    funext r
    fin_cases r <;> simp [initializeCountData,c,b,a,e26]
  rw [final] at duplicated
  refine ⟨_,?_,copied.sequence (rh.sequence (cleared.sequence duplicated))⟩
  have count := Encoding.array_size_le_length Encoding.node nodes (fun node _=>Encoding.node_positive_length node)
  have payloadLength : (Encoding.sequence Encoding.node nodes.toList).length ≤ (data 20).length := by
    rw [encoded]
    simp only [Encoding.array,Encoding.transport,Encoding.list,List.length_append]
    omega
  rw [←encoded] at count
  have linear : (data 20).length+1 ≤ ((data 20).length+1)^3 := Nat.le_self_pow (by decide) _
  omega

end Counting.StackMachine.DagUpdate.Canonical
