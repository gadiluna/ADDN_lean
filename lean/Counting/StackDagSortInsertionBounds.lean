import Counting.StackDagSortInsertion

namespace Counting.StackMachine.DagUpdate.Sort
open Routine

theorem records_length_le_sequence (records : List Record) :
    records.length≤(Encoding.sequence recordCodec records).length := by
  induction records with
  | nil => simp [Encoding.sequence]
  | cons head tail ih =>
    simp only [Encoding.sequence,List.length_cons,List.length_append]
    have positive : 1≤(recordCodec.encode head).length := by
      simp only [recordCodec,Encoding.product,List.length_append,Encoding.natural_length]
      omega
    omega

theorem insertionBudget_polynomial (query : Record) (records : List Record) (sourceLength : Nat)
    (sourceBound : (Encoding.sequence recordCodec records).length ≤ sourceLength) :
    insertionBudget query records sourceLength≤
      20000*(sourceLength+(recordCodec.encode query).length+1)^4 := by
  let K := sourceLength+(recordCodec.encode query).length+1
  have positive : 1≤K := by omega
  have countBound : records.length≤K := (records_length_le_sequence records).trans (by omega)
  have product : records.length*(15000*K^3+2)≤15000*K^4+2*K := by
    calc
      _≤K*(15000*K^3+2) := Nat.mul_le_mul_right _ countBound
      _=15000*K^4+2*K := by ring
  have linear : K≤K^4 := Nat.le_self_pow (by decide) _
  have onePower : 1≤K^4 := one_le_pow₀ positive
  unfold insertionBudget
  change records.length*(15000*K^3+2)+11*(recordCodec.encode query).length+2*sourceLength+22≤20000*K^4
  have extraBound : 11*(recordCodec.encode query).length+2*sourceLength+22≤13*K+22 := by omega
  omega

theorem insertCore_executes_polynomial (store : Store 94) (query : Record) (records : List Record) (suffix : List Bool)
    (source : store 80=Encoding.sequence recordCodec records++suffix)
    (queryAt : store 64=Encoding.node.encode query.2) (recordAt : store 82=recordCodec.encode query)
    (status : store 81=[true]) (flagAt : store 84=[false])
    (counter : store 90=List.replicate records.length true) (outputEmpty : store 83=[] ∧ store 91=[])
    (empty : ∀ r : Fin 96,r.val≤14 ∨ (40≤r.val ∧ r.val≤44) ∨ (49≤r.val ∧ r.val≤51) ∨
      r=65 ∨ r=66 ∨ r=67 ∨ r=86 ∨ r=88 ∨ r=89 → store r=[]) :
    ∃ time≤20000*((store 80).length+(store 82).length+1)^4,
      Executes insertCore store time (insertCoreResult store query records suffix) := by
  obtain ⟨time,bounded,run⟩ := insertCore_executes store query records suffix source queryAt recordAt status flagAt counter outputEmpty empty
  refine ⟨time,bounded.trans ?_,run⟩
  rw [recordAt]
  exact insertionBudget_polynomial query records (store 80).length (by rw [source,List.length_append];omega)

end Counting.StackMachine.DagUpdate.Sort
