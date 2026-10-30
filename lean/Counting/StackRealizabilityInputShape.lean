import Counting.StackRealizabilityInputCount
import Counting.StackRealizabilityCountsSpec

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def inputShapeRoles : Fin 22 ↪ Fin 100 :=
  ⟨![73,85,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,70,18,74,20,87],by decide⟩
def inputShape : Routine 98 := sequence (ofProgram (ListPrograms.copyProgram 97 81 70 0))
  (sequence (mapRegisters inputShapeRoles countsShape) (sequence (clear 73) (clear 74)))

theorem inputNaturalSum_size (values : List Nat) :
    values.sum.size ≤ (Encoding.sequence Encoding.natural values).length := by
  induction values with
  | nil => decide
  | cons value values ih =>
    have bounded := nat_add_size_le value values.sum
    simp only [List.sum_cons,Encoding.sequence,List.length_append,Encoding.natural_length]
    omega

/-- Positivity and exact count-array dimension are checked by a concrete
binary arithmetic pass. The explicit unary node count is preserved for
the subsequent bottom and depth readers. -/
theorem inputShape_executes (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (accepted : Bool) (tail : List Bool) :
    ∃ time ≤ 5000*((((Encoding.list Encoding.node).encode vista.nodes.toList).length+
        ((Encoding.list Encoding.natural).encode values).length)+1)^3,
      Executes inputShape (inputCountStore vista values ell order (accepted::tail)) time
        (inputCountStore vista values ell order
          ((accepted && countsShapeCheck values.toArray vista.nodes.size)::tail)) := by
  let start := inputCountStore vista values ell order (accepted::tail)
  let word := (Encoding.list Encoding.natural).encode values
  have copying := copy_executes 97 (81:Fin 100) 70 0 (by decide) (by decide) (by decide)
    start (by simp [start,inputCountStore,inputNodesStore,inputFieldsStore])
  have sourceAt : start 81=word := by simp [start,inputCountStore,inputNodesStore,inputFieldsStore,word]
  have emptyAt : start 70=[] := by simp [start,inputCountStore,inputNodesStore,inputFieldsStore]
  rw [sourceAt,emptyAt,List.append_nil] at copying
  let copied := Function.update start 70 word
  let localStore : Store 20 := copied ∘ inputShapeRoles
  obtain ⟨time,bound,checking⟩ := countsShape_executes localStore accepted tail
    (by simp [localStore,copied,start,inputShapeRoles,inputCountStore,inputNodesStore,inputFieldsStore])
    (by intro i small different;fin_cases i <;> simp_all [localStore,copied,start,inputShapeRoles,inputCountStore,inputNodesStore,inputFieldsStore])
    (by simp [localStore,copied,start,inputShapeRoles,inputCountStore,inputNodesStore,inputFieldsStore])
    (by simp [localStore,copied,start,inputShapeRoles,inputCountStore,inputNodesStore,inputFieldsStore])
    0 vista.nodes.size
    (by simp [localStore,copied,start,inputShapeRoles,inputCountStore,inputNodesStore,inputFieldsStore])
    (by simp [localStore,copied,start,inputShapeRoles,inputCountStore])
    values [] (by simp [localStore,copied,inputShapeRoles,word])
  let next := (accepted && countsShapeCheck values.toArray vista.nodes.size)::tail
  let scanned := Function.update (Function.update (inputCountStore vista values ell order next)
    73 (List.replicate values.length true)) 74 values.sum.bits
  have scanning : Executes (mapRegisters inputShapeRoles countsShape) copied time scanned := by
    apply relocate_executes_frame countsShape inputShapeRoles copied scanned localStore
      (countsShapeStore localStore accepted tail [] 0 vista.nodes.size values) time rfl _ _ checking
    · intro i
      fin_cases i <;> simp [scanned,localStore,copied,start,inputShapeRoles,inputCountStore,inputNodesStore,
        inputFieldsStore,countsShapeStore,next,countsShapeCheck,Bool.and_assoc]
    · intro i outside
      have n70:i≠70 := by intro same;subst i;exact outside 17 rfl
      have n73:i≠73 := by intro same;subst i;exact outside 0 rfl
      have n74:i≠74 := by intro same;subst i;exact outside 19 rfl
      have n85:i≠85 := by intro same;subst i;exact outside 1 rfl
      by_cases a:i=87 <;> by_cases b:i=80 <;>
        simp_all [scanned,copied,start,inputCountStore,inputNodesStore,inputFieldsStore]
  have clearCount := clear_executes (73:Fin 100) scanned
  have countAt : scanned 73=List.replicate values.length true := by simp [scanned]
  rw [countAt,List.length_replicate] at clearCount
  let cleared := Function.update scanned 73 []
  have clearSum := clear_executes (74:Fin 100) cleared
  have sumAt : cleared 74=values.sum.bits := by simp [cleared,scanned]
  rw [sumAt,Encoding.bits_length] at clearSum
  have final : Function.update cleared 74 []=inputCountStore vista values ell order next := by
    funext i
    by_cases a:i=73 <;> by_cases b:i=74 <;>
      simp_all [cleared,scanned,inputCountStore,inputNodesStore,inputFieldsStore]
  rw [final] at clearSum
  change time ≤ 2030*(word.length+0+vista.nodes.size+1)^3 at bound
  simp only [Nat.add_zero] at bound
  have nodeCount : vista.nodes.size ≤ ((Encoding.list Encoding.node).encode vista.nodes.toList).length := by
    have small := EncodingPrograms.VerifiedParser.sequence_count_le (codec:=Encoding.node)
      (by intro node;rw [Encoding.node_length];unfold Encoding.nodeBits;omega) vista.nodes.toList
    change vista.nodes.size ≤ (Encoding.natural.encode vista.nodes.toList.length++Encoding.sequence Encoding.node vista.nodes.toList).length
    simp only [Array.length_toList,List.length_append] at small ⊢
    omega
  have valueCount : values.length ≤ word.length := by
    have small := EncodingPrograms.VerifiedParser.sequence_count_le (codec:=Encoding.natural)
      (by intro value;rw [Encoding.natural_length];omega) values
    change values.length ≤ (Encoding.natural.encode values.length++Encoding.sequence Encoding.natural values).length
    rw [List.length_append];omega
  have sumSmall : values.sum.size ≤ word.length := by
    have small := inputNaturalSum_size values
    change values.sum.size ≤ (Encoding.natural.encode values.length++Encoding.sequence Encoding.natural values).length
    rw [List.length_append];omega
  let S := ((Encoding.list Encoding.node).encode vista.nodes.toList).length+word.length+1
  have limit : time ≤ 2030*S^3 := bound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 3))
  have linear : S ≤ S^3 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^3 := Nat.one_le_pow _ _ (by dsimp only [S];omega)
  have wordSmall : word.length ≤ S := by dsimp only [S];omega
  exact ⟨_,by change 5*word.length+2+1+(time+1+(values.length+1+1+(values.sum.size+1))) ≤ 5000*S^3;omega,
    copying.sequence (scanning.sequence (clearCount.sequence clearSum))⟩

end Counting.StackMachine.RealizabilityCheck
