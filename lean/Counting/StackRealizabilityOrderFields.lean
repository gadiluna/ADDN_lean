import Counting.StackRealizabilityVistaRead
import Counting.StackRealizabilityVistaBudget

namespace Counting.StackMachine.VistaComplement
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def orderFields (orderField countsField : Fin 30) : Routine 128 :=
  sequence (readField DagParser.natural orderField) (readField DagParser.naturals countsField)

def orderFieldsData (data : Fin 30→List Bool) (orderField countsField : Fin 30)
    (order : Nat) (values : List Nat) (suffix : List Bool) : Fin 30→List Bool :=
  Function.update (Function.update (Function.update (Function.update data 5
    ((Encoding.list Encoding.natural).encode values++suffix)) orderField (Encoding.natural.encode order))
      5 suffix) countsField ((Encoding.list Encoding.natural).encode values)

theorem orderFields_executes (data : Fin 30→List Bool) (orderField countsField : Fin 30)
    (orderSource : orderField≠5) (orderStatus : orderField≠4)
    (countsSource : countsField≠5) (countsStatus : countsField≠4) (distinct : countsField≠orderField)
    (order : Nat) (values : List Nat) (suffix : List Bool) (accepted : Bool) (tail : List Bool)
    (status : data 4=accepted::tail) (source : data 5=Encoding.orderWitness.encode (order,values)++suffix)
    (emptyOrder : data orderField=[]) (emptyCounts : data countsField=[]) :
    ∃ time ≤ 8100*((data 5).length+1)^4,
      Executes (orderFields orderField countsField) (file data) time
        (file (orderFieldsData data orderField countsField order values suffix)) := by
  obtain ⟨t0,b0,r0⟩ := readField_executes DagParser.natural data orderField orderSource orderStatus
    order ((Encoding.list Encoding.natural).encode values++suffix) accepted tail
      (by simpa only [Encoding.orderWitness,Encoding.product,List.append_assoc] using source) status emptyOrder
  let middle := Function.update (Function.update data 5 ((Encoding.list Encoding.natural).encode values++suffix))
    orderField (Encoding.natural.encode order)
  obtain ⟨t1,b1,r1⟩ := readField_executes DagParser.naturals middle countsField countsSource countsStatus
    values suffix accepted tail (by simp [middle,Ne.symm orderSource])
      (by simp [middle,Ne.symm orderStatus,status]) (by simp [middle,distinct,countsSource,emptyCounts])
  let L := (data 5).length
  have lengths : L=(Encoding.natural.encode order).length+
      ((Encoding.list Encoding.natural).encode values).length+suffix.length := by
    rw [show L=(data 5).length by rfl,source]
    simp only [Encoding.orderWitness,Encoding.product,List.length_append]
  have firstCost := fieldReaderCost_le DagParser.natural.coefficient DagParser.natural.exponent
    (data 5).length (Encoding.natural.encode order).length L naturalParser_coefficient naturalParser_degree
      (by rfl) (by omega)
  have secondCost := fieldReaderCost_le DagParser.naturals.coefficient DagParser.naturals.exponent
    (middle 5).length ((Encoding.list Encoding.natural).encode values).length L
      naturalsParser_coefficient naturalsParser_degree
      (by simp only [middle,Function.update_of_ne (Ne.symm orderSource),Function.update_self,List.length_append];omega)
      (by omega)
  have bound0 := b0.trans firstCost
  have bound1 := b1.trans secondCost
  have one : 1 ≤ (L+1)^4 := Nat.one_le_pow _ _ (by omega)
  refine ⟨_,?_,r0.sequence r1⟩
  change t0+1+t1 ≤ 8100*(L+1)^4
  omega

end Counting.StackMachine.VistaComplement
