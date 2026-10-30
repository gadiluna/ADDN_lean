import Counting.StackRealizabilityDepthRead
import Counting.StackDagClean
import Counting.StackEncodingFrameStore

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def depthMetadataWork : List (Fin 100) := [70,73,75,76,77]
def depthFrame : Routine 98 := sequence (clearRegisters depthMetadataWork) (frameRoutine 97 74 72 0)

def depthFramedStore (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (status : List Bool) : Store 98 :=
  Function.update (inputCountStore vista values ell order status) 72
    (Encoding.natural.encode (vista.node vista.bottom).level)

theorem depthFrame_executes (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (valid : vista.valid=true) (status : List Bool) :
    ∃ time ≤ 30*(((Encoding.list Encoding.node).encode vista.nodes.toList).length+vista.nodes.size+1),
      Executes depthFrame (depthMetadataStore vista values ell order status) time
        (depthFramedStore vista values ell order status) := by
  let node := vista.node vista.bottom
  let word := (Encoding.list Encoding.node).encode vista.nodes.toList
  let S := word.length+vista.nodes.size+1
  have last := valid_bottom_last vista valid
  have inside : vista.bottom<vista.nodes.size := by omega
  have member : node∈vista.nodes.toList := by
    apply Array.mem_toList_iff.mpr
    simp only [node,Executable.Vista.node,Array.getElem?_eq_getElem inside,Option.getD_some]
    exact Array.getElem_mem inside
  have small := DagValidation.node_sequence_member_le vista.nodes.toList node member
  have sequenceSmall : (Encoding.sequence Encoding.node vista.nodes.toList).length ≤ word.length := by
    change _ ≤ (Encoding.natural.encode vista.nodes.toList.length++Encoding.sequence Encoding.node vista.nodes.toList).length
    rw [List.length_append];omega
  have metadata := DagValidation.node_metadata_size_le node
  have suffix := DagValidation.nodeSuffix_length_le node
  dsimp only [node] at small metadata suffix
  have bounded (i : Fin 100) (member : i∈depthMetadataWork) :
      (depthMetadataStore vista values ell order status i).length ≤ S := by
    simp [depthMetadataWork] at member
    rcases member with rfl|rfl|rfl|rfl|rfl
    all_goals simp [depthMetadataStore,depthPreparedStore,Encoding.bits_length]
    all_goals dsimp only [S]
    all_goals omega
  obtain ⟨time,bound,clearing⟩ := DagValidation.clear_selected_executes depthMetadataWork
    (depthMetadataStore vista values ell order status) S bounded
  let cleared := Function.update (inputCountStore vista values ell order status) 74 node.level.bits
  have clearedEq : clearedStore depthMetadataWork (depthMetadataStore vista values ell order status)=cleared := by
    funext i
    by_cases a:i=70 <;> by_cases b:i=73 <;> by_cases c:i=75 <;> by_cases d:i=76 <;> by_cases e:i=77 <;> by_cases f:i=74 <;>
      simp_all [clearedStore,depthMetadataWork,depthMetadataStore,depthPreparedStore,cleared,node,
        inputCountStore,inputNodesStore,inputFieldsStore]
  rw [clearedEq] at clearing
  have framing := frame_executes_updates 97 (74:Fin 100) 72 0 (by decide) (by decide) (by decide)
    cleared (by simp [cleared,inputCountStore,inputNodesStore,inputFieldsStore])
  have payloadAt : cleared 74=node.level.bits := by simp [cleared]
  have targetAt : cleared 72=[] := by simp [cleared,inputCountStore,inputNodesStore,inputFieldsStore]
  rw [payloadAt,targetAt,List.append_nil,Encoding.bits_length] at framing
  have final : Function.update (Function.update cleared 74 []) 72 (Encoding.frame node.level.bits)=
      depthFramedStore vista values ell order status := by
    funext i
    by_cases a:i=74 <;> by_cases b:i=72 <;>
      simp_all [cleared,depthFramedStore,inputCountStore,inputNodesStore,inputFieldsStore,Encoding.natural,node]
  rw [final] at framing
  have levelSmall : node.level.size ≤ S := by dsimp only [S,node];omega
  change time ≤ 5*(S+2) at bound
  have positive : 1 ≤ S := by dsimp only [S];omega
  exact ⟨_,by change time+1+(5*node.level.size+4) ≤ 30*S;omega,clearing.sequence framing⟩

end Counting.StackMachine.RealizabilityCheck
