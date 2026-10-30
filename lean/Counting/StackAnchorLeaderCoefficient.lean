import Counting.StackAnchorCoefficient

namespace Counting.StackMachine.AnchorLeader
open Routine EncodingPrograms AnchorCoefficient
set_option backward.isDefEq.respectTransparency false

abbrev choose : Routine 32 := branchRoutine 25
  (prepend 22 (Encoding.rational.encode 1)) (prepend 22 (Encoding.rational.encode 0))
abbrev cleanup : Routine 32 := sequence (clear 24) (sequence (clear 26) (clear 27))
abbrev arithmetic : Routine 32 := sequence choose cleanup
abbrev calculate : Routine 32 := sequence readNode (sequence findCount arithmetic)

def value (node : Executable.Node) : Rat := if node.leader then 1 else 0

theorem choose_executes (input query level parent degree count : List Bool) (leader : Bool) :
    ∃ time ≤ 15,
      Executes choose (file input query [] level parent [leader] degree count [] []) time
        (file input query (Encoding.rational.encode (if leader then 1 else 0)) level parent [] degree count [] []) := by
  let before := file input query [] level parent [leader] degree count [] []
  let ready := file input query [] level parent [] degree count [] []
  have reset : Function.update before 25 []=ready := by funext r;fin_cases r <;> simp [before,ready,file]
  have emit (number : Rat) := prepend_executes (22:Fin 34) (Encoding.rational.encode number) ready
  have output (number : Rat) : Function.update ready 22 (Encoding.rational.encode number++ready 22)=
      file input query (Encoding.rational.encode number) level parent [] degree count [] [] := by
    funext r;fin_cases r <;> simp [ready,file]
  cases leader with
  | true =>
    have emitted := emit 1
    rw [output] at emitted
    have run := branch_executes_true (25:Fin 34) (prepend 22 (Encoding.rational.encode 1))
      (prepend 22 (Encoding.rational.encode 0)) before _ [] _ rfl (by rw [reset];exact emitted)
    exact ⟨15,by rfl,run⟩
  | false =>
    have emitted := emit 0
    rw [output] at emitted
    have run := branch_executes_false (25:Fin 34) (prepend 22 (Encoding.rational.encode 1))
      (prepend 22 (Encoding.rational.encode 0)) before _ [] _ rfl (by rw [reset];exact emitted)
    exact ⟨11,by decide,run⟩

theorem cleanup_executes (input query result level parent degree count : List Bool) :
    Executes cleanup (file input query result level parent [] degree count [] [])
      (parent.length+degree.length+count.length+5)
      (file input query result level [] [] [] [] [] []) := by
  have a := clear_executes (24:Fin 34) (file input query result level parent [] degree count [] [])
  have as' : Function.update (file input query result level parent [] degree count [] []) 24 []=
      file input query result level [] [] degree count [] [] := by funext r;fin_cases r <;> simp [file]
  rw [as'] at a
  have b := clear_executes (26:Fin 34) (file input query result level [] [] degree count [] [])
  have bs : Function.update (file input query result level [] [] degree count [] []) 26 []=
      file input query result level [] [] [] count [] [] := by funext r;fin_cases r <;> simp [file]
  rw [bs] at b
  have c := clear_executes (27:Fin 34) (file input query result level [] [] [] count [] [])
  have cs : Function.update (file input query result level [] [] [] count [] []) 27 []=
      file input query result level [] [] [] [] [] [] := by funext r;fin_cases r <;> simp [file]
  rw [cs] at c
  change Executes _ _ (parent.length+1) _ at a
  change Executes _ _ (degree.length+1) _ at b
  change Executes _ _ (count.length+1) _ at c
  convert a.sequence (b.sequence c) using 1
  omega

theorem calculate_executes (node : Executable.Node) (query : Nat) (suffix : List Bool) :
    ∃ time ≤ 10000*((Encoding.node.encode node++suffix).length+query.size+1)^3,
      Executes calculate (file (Encoding.node.encode node++suffix) query.bits [] [] [] [] [] [] [] []) time
        (file suffix query.bits (Encoding.rational.encode (value node)) node.level.bits [] [] [] [] [] []) := by
  obtain ⟨readTime,readBound,a⟩ := readNode_executes node query suffix []
  obtain ⟨findTime,findBound,b⟩ := findCount_executes node query suffix []
  obtain ⟨chooseTime,chooseBound,c⟩ := choose_executes suffix query.bits node.level.bits
    (DagValidation.parentCode node).bits node.degree.bits (Executable.countFrom node query).bits node.leader
  have d := cleanup_executes suffix query.bits (Encoding.rational.encode (value node)) node.level.bits
    (DagValidation.parentCode node).bits node.degree.bits (Executable.countFrom node query).bits
  have composed := a.sequence (b.sequence (c.sequence d))
  refine ⟨_,?_,composed⟩
  have incoming : ((Encoding.list AnchorFind.edgeCodec).encode node.incoming++suffix).length ≤
      (Encoding.node.encode node++suffix).length := by
    change ((Encoding.list AnchorFind.edgeCodec).encode node.incoming++suffix).length ≤
      ((Encoding.natural.encode node.level++(Encoding.natural.encode (DagValidation.parentCode node)++
        ([node.leader]++(Encoding.natural.encode node.degree++
          (Encoding.list AnchorFind.edgeCodec).encode node.incoming))))++suffix).length
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega
  have parent : (DagValidation.parentCode node).size ≤ (Encoding.node.encode node).length := by
    rw [Encoding.node_length];unfold Encoding.nodeBits DagValidation.parentCode;omega
  have degree := Encoding.degreeBits_le_node node
  have count := Encoding.redBits_le_node node query
  rw [←Encoding.node_length] at degree count
  let size := (Encoding.node.encode node++suffix).length+query.size+1
  have findRaised : findTime ≤ 5000*size^3 := findBound.trans (by dsimp only [size];gcongr)
  have linear : size ≤ size^3 := Nat.le_self_pow (by decide) _
  have positive : 1 ≤ size^3 := Nat.one_le_pow _ _ (by dsimp only [size];omega)
  change _ ≤ 10000*size^3
  dsimp only [size] at findRaised linear positive ⊢
  simp only [Encoding.bits_length,List.length_append] at *
  omega

end Counting.StackMachine.AnchorLeader
