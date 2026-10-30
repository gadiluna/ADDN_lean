import Counting.StackRealizabilityInputCount
import Counting.StackRealizabilityInitialChecked

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def inputInitialRoles : Fin 28 ↪ Fin 100 :=
  ⟨![0,85,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,70,18,19,71,73,74,23,24,25,98,82],by decide⟩
def inputInitial : Routine 98 := sequence (ofProgram (ListPrograms.copyProgram 97 80 70 0))
  (sequence (ofProgram (ListPrograms.copyProgram 97 81 71 0))
    (sequence (mapRegisters inputInitialRoles initialCheck)
      (sequence (clear 70) (sequence (clear 73) (clear 74)))))

/-- The initial leader/nonleader sums and all four capacity guards are
computed from copied encoded inputs. Every copy and erasure is charged. -/
theorem inputInitial_executes (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (length : values.length=vista.nodes.size) (accepted : Bool) (tail : List Bool) :
    ∃ time ≤ 15000*((((Encoding.list Encoding.node).encode vista.nodes.toList).length+
        ((Encoding.list Encoding.natural).encode values).length)+ell.size+order.size+1)^5,
      Executes inputInitial (inputCountStore vista values ell order (accepted::tail)) time
        (inputCountStore vista values ell order
          ((accepted && initialScanCheck vista.nodes.toList values ell order)::tail)) := by
  let start := inputCountStore vista values ell order (accepted::tail)
  let nodesWord := (Encoding.list Encoding.node).encode vista.nodes.toList
  let valuesWord := (Encoding.list Encoding.natural).encode values
  have copyNodes := copy_executes 97 (80:Fin 100) 70 0 (by decide) (by decide) (by decide)
    start (by simp [start,inputCountStore,inputNodesStore,inputFieldsStore])
  have nodesAt : start 80=nodesWord := by simp [start,inputCountStore,inputNodesStore,nodesWord]
  have empty70 : start 70=[] := by simp [start,inputCountStore,inputNodesStore,inputFieldsStore]
  rw [nodesAt,empty70,List.append_nil] at copyNodes
  let copiedNodes := Function.update start 70 nodesWord
  have copyValues := copy_executes 97 (81:Fin 100) 71 0 (by decide) (by decide) (by decide)
    copiedNodes (by simp [copiedNodes,start,inputCountStore,inputNodesStore,inputFieldsStore])
  have valuesAt : copiedNodes 81=valuesWord := by
    simp [copiedNodes,start,inputCountStore,inputNodesStore,inputFieldsStore,valuesWord]
  have empty71 : copiedNodes 71=[] := by
    simp [copiedNodes,start,inputCountStore,inputNodesStore,inputFieldsStore]
  rw [valuesAt,empty71,List.append_nil] at copyValues
  let copied := Function.update copiedNodes 71 valuesWord
  let localStore : Store 26 := copied ∘ inputInitialRoles
  have localEmpty (i : Fin 28) (outside : i∉({1,17,20,26,27}:Finset (Fin 28))) : localStore i=[] := by
    fin_cases i <;> simp_all [localStore,copied,copiedNodes,start,inputInitialRoles,inputCountStore,inputNodesStore,inputFieldsStore]
  obtain ⟨time,bound,checking⟩ := initialCheck_executes localStore accepted tail
    (by simp [localStore,copied,copiedNodes,start,inputInitialRoles,inputCountStore,inputNodesStore,inputFieldsStore])
    (by intro i small different;apply localEmpty;fin_cases i <;> simp_all)
    (localEmpty 18 (by decide)) (localEmpty 19 (by decide)) (localEmpty 21 (by decide)) (localEmpty 22 (by decide))
    (localEmpty 23 (by decide)) (localEmpty 24 (by decide)) (localEmpty 25 (by decide))
    vista.nodes.toList values (by simpa only [Array.length_toList] using length) [] []
    (by simp [localStore,copied,copiedNodes,inputInitialRoles,nodesWord])
    (by simp [localStore,copied,inputInitialRoles,valuesWord]) ell order
    (by simp [localStore,copied,copiedNodes,start,inputInitialRoles,inputCountStore,inputNodesStore,inputFieldsStore])
    (by simp [localStore,copied,copiedNodes,start,inputInitialRoles,inputCountStore,inputNodesStore,inputFieldsStore])
  let next := (accepted && initialScanCheck vista.nodes.toList values ell order)::tail
  let leaders := initialRangeSum vista.nodes.toList true 0 values
  let nonleaders := initialRangeSum vista.nodes.toList false 0 values
  let scanned := Function.update (Function.update (Function.update (inputCountStore vista values ell order next)
    70 (Encoding.sequence Encoding.node vista.nodes.toList)) 73 leaders.bits) 74 nonleaders.bits
  have scanning : Executes (mapRegisters inputInitialRoles initialCheck) copied time scanned := by
    apply relocate_executes_frame initialCheck inputInitialRoles copied scanned localStore
      (initialCheckStore localStore accepted tail vista.nodes.toList values ell order [] []) time rfl _ _ checking
    · intro i
      fin_cases i <;> simp [scanned,localStore,copied,copiedNodes,start,inputInitialRoles,inputCountStore,
        inputNodesStore,inputFieldsStore,initialCheckStore,next,leaders,nonleaders]
    · intro i outside
      have n70:i≠70 := by intro same;subst i;exact outside 17 rfl
      have n71:i≠71 := by intro same;subst i;exact outside 20 rfl
      have n73:i≠73 := by intro same;subst i;exact outside 21 rfl
      have n74:i≠74 := by intro same;subst i;exact outside 22 rfl
      have n85:i≠85 := by intro same;subst i;exact outside 1 rfl
      by_cases a:i=87 <;> by_cases b:i=80 <;>
        simp_all [scanned,copied,copiedNodes,start,inputCountStore,inputNodesStore,inputFieldsStore]
  have c0 := clear_executes (70:Fin 100) scanned
  have a0 : scanned 70=Encoding.sequence Encoding.node vista.nodes.toList := by simp [scanned]
  rw [a0] at c0
  let cleared0 := Function.update scanned 70 []
  have c1 := clear_executes (73:Fin 100) cleared0
  have a1 : cleared0 73=leaders.bits := by simp [cleared0,scanned]
  rw [a1,Encoding.bits_length] at c1
  let cleared1 := Function.update cleared0 73 []
  have c2 := clear_executes (74:Fin 100) cleared1
  have a2 : cleared1 74=nonleaders.bits := by simp [cleared1,cleared0,scanned]
  rw [a2,Encoding.bits_length] at c2
  have final : Function.update cleared1 74 []=inputCountStore vista values ell order next := by
    funext i
    by_cases a:i=70 <;> by_cases b:i=73 <;> by_cases c:i=74 <;>
      simp_all [cleared1,cleared0,scanned,inputCountStore,inputNodesStore,inputFieldsStore]
  rw [final] at c2
  change time ≤ 13200*(nodesWord.length+valuesWord.length+ell.size+order.size+1)^5 at bound
  have sums := initialRangeSum_size vista.nodes.toList 0 values 0 0
  simp only [Nat.zero_add,Nat.size_zero,Nat.add_zero] at sums
  have sumSmall : leaders.size+nonleaders.size ≤ valuesWord.length := by
    change _ ≤ (Encoding.natural.encode values.length++Encoding.sequence Encoding.natural values).length
    rw [List.length_append]
    change leaders.size+nonleaders.size ≤ (Encoding.sequence Encoding.natural values).length at sums
    omega
  have sequenceSmall : (Encoding.sequence Encoding.node vista.nodes.toList).length ≤ nodesWord.length := by
    change _ ≤ (Encoding.natural.encode vista.nodes.toList.length++Encoding.sequence Encoding.node vista.nodes.toList).length
    rw [List.length_append];omega
  let S := nodesWord.length+valuesWord.length+ell.size+order.size+1
  change time ≤ 13200*S^5 at bound
  have linear : S ≤ S^5 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^5 := Nat.one_le_pow _ _ (by dsimp only [S];omega)
  have wordSmall : nodesWord.length+valuesWord.length ≤ S := by dsimp only [S];omega
  exact ⟨_,by change 5*nodesWord.length+2+1+(5*valuesWord.length+2+1+
      (time+1+((Encoding.sequence Encoding.node vista.nodes.toList).length+1+1+
        (leaders.size+1+1+(nonleaders.size+1))))) ≤ 15000*S^5;omega,
    copyNodes.sequence (copyValues.sequence (scanning.sequence (c0.sequence (c1.sequence c2))))⟩

end Counting.StackMachine.RealizabilityCheck
