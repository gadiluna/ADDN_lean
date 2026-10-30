import Counting.StackAnchorCoefficientSelect
import Counting.EncodingRecognitionBounds

namespace Counting.StackMachine.AnchorCoefficient
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev cleanup : Routine 32 := sequence (clear 24) (sequence (clear 25) (clear 28))
abbrev arithmetic : Routine 32 := sequence prepareQuery (sequence retainDegree (sequence subtract cleanup))
abbrev routine : Routine 32 := sequence readNode (sequence findCount arithmetic)

theorem cleanup_executes (input query result level parent leader successor : List Bool) :
    Executes cleanup (file input query result level parent leader [] [] successor [])
      (parent.length+leader.length+successor.length+5)
      (file input query result level [] [] [] [] [] []) := by
  have a := clear_executes (24:Fin 34) (file input query result level parent leader [] [] successor [])
  have ea : Function.update (file input query result level parent leader [] [] successor []) 24 []=
      file input query result level [] leader [] [] successor [] := by funext r;fin_cases r <;> simp [file]
  rw [ea] at a
  have b := clear_executes (25:Fin 34) (file input query result level [] leader [] [] successor [])
  have eb : Function.update (file input query result level [] leader [] [] successor []) 25 []=
      file input query result level [] [] [] [] successor [] := by funext r;fin_cases r <;> simp [file]
  rw [eb] at b
  have c := clear_executes (28:Fin 34) (file input query result level [] [] [] [] successor [])
  have ec : Function.update (file input query result level [] [] [] [] successor []) 28 []=
      file input query result level [] [] [] [] [] [] := by funext r;fin_cases r <;> simp [file]
  rw [ec] at c
  have combined := a.sequence (b.sequence c)
  convert combined using 1
  simp [file]
  omega

def arithmeticCost (node : Executable.Node) (query : Nat) : Nat :=
  9*query.size+10+1+(6*((DagValidation.parentCode node).size+(query+1).size)+node.degree.size+14+1+
    (10000*((Executable.countFrom node query).size+(chargedDegree node query).size+1)+1+
      ((DagValidation.parentCode node).size+(query+1).size+6)))

theorem arithmetic_executes (node : Executable.Node) (query : Nat) (input result : List Bool) :
    ∃ time  ≤  arithmeticCost node query,
      Executes arithmetic
        (file input query.bits result node.level.bits (DagValidation.parentCode node).bits [node.leader]
          node.degree.bits (Executable.countFrom node query).bits [] []) time
        (file input query.bits (Encoding.rational.encode (coefficient node query)++result)
          node.level.bits [] [] [] [] [] []) := by
  let start := file input query.bits result node.level.bits (DagValidation.parentCode node).bits [node.leader]
    node.degree.bits (Executable.countFrom node query).bits [] []
  obtain ⟨queryTime,queryBound,queryRun⟩ := prepareQuery_executes start query rfl rfl rfl rfl
  let prepared := file input query.bits result node.level.bits (DagValidation.parentCode node).bits [node.leader]
    node.degree.bits (Executable.countFrom node query).bits (query+1).bits []
  have queryStore : Function.update start 28 (query+1).bits=prepared := by
    funext r;fin_cases r <;> simp [start,prepared,file]
  rw [queryStore] at queryRun
  obtain ⟨retainTime,retainBound,retained⟩ := retainDegree_executes prepared rfl rfl rfl rfl
  let selected := file input query.bits result node.level.bits (DagValidation.parentCode node).bits [node.leader]
    (chargedDegree node query).bits (Executable.countFrom node query).bits (query+1).bits []
  have selectedStore : Function.update prepared 26 (if prepared 24=prepared 28 then prepared 26 else [])=selected := by
    change Function.update prepared 26
      (if (DagValidation.parentCode node).bits=(query+1).bits then node.degree.bits else [])=selected
    rw [degree_choice]
    funext r;fin_cases r <;> simp [prepared,selected,file]
  rw [selectedStore] at retained
  obtain ⟨subtractTime,subtractBound,subtracted⟩ := subtract_executes (Executable.countFrom node query)
    (chargedDegree node query) input query.bits result node.level.bits (DagValidation.parentCode node).bits
    [node.leader] (query+1).bits []
  have cleared := cleanup_executes input query.bits (Encoding.rational.encode (coefficient node query)++result)
    node.level.bits (DagValidation.parentCode node).bits [node.leader] (query+1).bits
  have composed := queryRun.sequence (retained.sequence (subtracted.sequence cleared))
  refine ⟨_,?_,composed⟩
  change retainTime ≤ 6*((DagValidation.parentCode node).bits.length+(query+1).bits.length)+node.degree.bits.length+14 at retainBound
  simp only [Encoding.bits_length,List.length_singleton] at retainBound ⊢
  dsimp only [arithmeticCost]
  omega

theorem arithmeticCost_bound (node : Executable.Node) (query : Nat) :
    arithmeticCost node query ≤ 50000*((Encoding.node.encode node).length+query.size+1) := by
  have degree := Encoding.degreeBits_le_node node
  have count := Encoding.redBits_le_node node query
  have parent : (DagValidation.parentCode node).size ≤ Encoding.nodeBits node := by
    unfold Encoding.nodeBits DagValidation.parentCode
    omega
  have selected : (chargedDegree node query).size ≤ node.degree.size := by
    unfold chargedDegree;split <;> simp
  have successor : (query+1).size ≤ query.size+1 :=
    (Nat.size_le_size (Nat.succ_le_of_lt (Nat.lt_size_self query))).trans_eq Nat.size_pow
  rw [Encoding.node_length]
  unfold arithmeticCost
  omega

/-- One coefficient of the actual anchor system, computed from the full
serialized node and a binary predecessor index. The node level and query
are retained, the unread suffix and previous output are preserved, and
all other cells are empty. -/
theorem coefficient_executes (node : Executable.Node) (query : Nat) (suffix result : List Bool) :
    ∃ time  ≤ 100000*((Encoding.node.encode node++suffix).length+query.size+1)^3,
      Executes routine (file (Encoding.node.encode node++suffix) query.bits result [] [] [] [] [] [] []) time
        (file suffix query.bits (Encoding.rational.encode (coefficient node query)++result)
          node.level.bits [] [] [] [] [] []) := by
  obtain ⟨readTime,readBound,readRun⟩ := readNode_executes node query suffix result
  obtain ⟨findTime,findBound,findRun⟩ := findCount_executes node query suffix result
  obtain ⟨arithmeticTime,arithmeticBound,arithmeticRun⟩ := arithmetic_executes node query suffix result
  have composed := readRun.sequence (findRun.sequence arithmeticRun)
  refine ⟨readTime+1+(findTime+1+arithmeticTime),?_,composed⟩
  have code := arithmeticCost_bound node query
  have incoming : ((Encoding.list AnchorFind.edgeCodec).encode node.incoming++suffix).length ≤ 
      (Encoding.node.encode node++suffix).length := by
    change ((Encoding.list AnchorFind.edgeCodec).encode node.incoming++suffix).length ≤ 
      ((Encoding.natural.encode node.level++(Encoding.natural.encode (DagValidation.parentCode node)++
        ([node.leader]++(Encoding.natural.encode node.degree++
          (Encoding.list AnchorFind.edgeCodec).encode node.incoming))))++suffix).length
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega
  let size := (Encoding.node.encode node++suffix).length+query.size+1
  have findRaised : findTime ≤ 5000*size^3 := findBound.trans (by dsimp only [size];gcongr)
  have linear : size ≤ size^3 := Nat.le_self_pow (by decide) _
  have positive : 1 ≤ size^3 := Nat.one_le_pow _ _ (by dsimp only [size];omega)
  change _ ≤ 100000*size^3
  dsimp only [size] at findRaised linear positive ⊢
  simp only [List.length_append] at *
  omega

end Counting.StackMachine.AnchorCoefficient
