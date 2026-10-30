import Counting.StackRealizabilityInputNodes
import Counting.StackEncodingListReadHeader

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def inputCountRoles : FullListWorkspace 83 :=
  ⟨![70,85,0,2,87,3,4,5,6,7,8,9,10,11,12,13,14],by decide⟩

def inputCount : Routine 98 := sequence (ofProgram (ListPrograms.copyProgram 97 80 70 0))
  (sequence (readListHeader 83 inputCountRoles) (clear 70))

def inputCountStore (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (status : List Bool) : Store 98 :=
  Function.update (inputNodesStore vista values ell order status) 87 (List.replicate vista.nodes.size true)

/-- The only unary quantity introduced here is the number of explicitly
serialized nodes, bounded by the input word length. -/
theorem inputCount_executes (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (accepted : Bool) (tail : List Bool) :
    ∃ time ≤ 1900*(((Encoding.list Encoding.node).encode vista.nodes.toList).length+1)^3,
      Executes inputCount (inputNodesStore vista values ell order (accepted::tail)) time
        (inputCountStore vista values ell order (accepted::tail)) := by
  let start := inputNodesStore vista values ell order (accepted::tail)
  let word := (Encoding.list Encoding.node).encode vista.nodes.toList
  have copying := copy_executes 97 (80:Fin 100) 70 0 (by decide) (by decide) (by decide)
    start (by simp [start,inputNodesStore,inputFieldsStore])
  have sourceAt : start 80=word := by simp [start,inputNodesStore,word]
  have emptyAt : start 70=[] := by simp [start,inputNodesStore,inputFieldsStore]
  rw [sourceAt,emptyAt,List.append_nil] at copying
  let copied := Function.update start 70 word
  obtain ⟨time,bound,reading⟩ := readListHeader_canonical 83 inputCountRoles copied accepted tail
    (by simp [copied,start,inputNodesStore,inputFieldsStore,inputCountRoles])
    (by intro i member;fin_cases i <;> simp_all [copied,start,inputNodesStore,inputFieldsStore,inputCountRoles])
    Encoding.node (by intro node;rw [Encoding.node_length];unfold Encoding.nodeBits;omega)
    vista.nodes.toList [] (by simp [copied,word,inputCountRoles])
  let parsed := Function.update (Function.update copied 70 (Encoding.sequence Encoding.node vista.nodes.toList))
    87 (List.replicate vista.nodes.size true)
  change Executes (readListHeader 83 inputCountRoles) copied time
    (Function.update (Function.update copied 70 (Encoding.sequence Encoding.node vista.nodes.toList++[]))
      87 (List.replicate vista.nodes.toList.length true)) at reading
  simp only [List.append_nil,Array.length_toList] at reading
  have clearing := clear_executes (70:Fin 100) parsed
  have suffixAt : parsed 70=Encoding.sequence Encoding.node vista.nodes.toList := by simp [parsed]
  rw [suffixAt] at clearing
  have final : Function.update parsed 70 []=inputCountStore vista values ell order (accepted::tail) := by
    funext r
    by_cases a:r=70 <;> by_cases b:r=87 <;>
      simp_all [parsed,copied,start,inputCountStore,inputNodesStore,inputFieldsStore]
  rw [final] at clearing
  change time ≤ 1820*(word.length+1)^3 at bound
  have sequenceSmall : (Encoding.sequence Encoding.node vista.nodes.toList).length ≤ word.length := by
    change _ ≤ (Encoding.natural.encode vista.nodes.toList.length++Encoding.sequence Encoding.node vista.nodes.toList).length
    rw [List.length_append];omega
  have linear := Nat.le_self_pow (by decide : 3≠0) (word.length+1)
  have one := Nat.one_le_pow 3 (word.length+1) (by omega)
  exact ⟨_,by change 5*word.length+2+1+(time+1+((Encoding.sequence Encoding.node vista.nodes.toList).length+1)) ≤ 1900*(word.length+1)^3;omega,
    copying.sequence (reading.sequence clearing)⟩

end Counting.StackMachine.RealizabilityCheck
