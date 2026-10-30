import Counting.StackDagSortBank
import Counting.StackUnframeCanonical

namespace Counting.StackMachine.DagUpdate.Sort
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

def readCompare : Routine 94 := sequence readSortedRecord
  (sequence (ofProgram (unframeProgram 93 65 88 89)) compareSortedNodes)

def comparedRecord (store : Store 94) (query : Executable.Node) (record : Record) (suffix : List Bool) : Store 94 :=
  Function.update (Function.update (Function.update (Function.update store 80 suffix)
    65 (Encoding.node.encode record.2)) 88 record.1.bits)
    66 [Executable.lexLE query.key record.2.key]

theorem readCompare_executes (store : Store 94) (query : Executable.Node) (record : Record) (suffix : List Bool)
    (source : store 80=recordCodec.encode record++suffix)
    (queryAt : store 64=Encoding.node.encode query) (status : store 81=[true])
    (empty : ∀ r : Fin 96,r.val≤14 ∨ (40≤r.val ∧ r.val≤44) ∨ (49≤r.val ∧ r.val≤51) ∨
      r=65 ∨ r=66 ∨ r=67 ∨ r=88 ∨ r=89 → store r=[]) :
    ∃ time≤14000*((store 80).length+(store 64).length+1)^3,
      Executes readCompare store time (comparedRecord store query record suffix) := by
  obtain ⟨readTime,readBound,reading⟩ := readSortedRecord_executes store record suffix source status
    (empty 65 (by simp)) (fun r lower=>empty r (Or.inl lower))
  let read := Function.update (Function.update store 80 suffix) 65 (recordCodec.encode record)
  have split := unframe_canonical_executes 93 (65:Fin 96) 88 89 (by decide) (by decide) (by decide)
    read record.1.bits (Encoding.node.encode record.2)
    (by simp [read,recordCodec,Encoding.product,Encoding.natural]) (by simp [read,empty])
  have indexEmpty : read 88=[] := by simp [read,empty]
  rw [indexEmpty,List.append_nil] at split
  let separated := Function.update (Function.update read 65 (Encoding.node.encode record.2)) 88 record.1.bits
  obtain ⟨compareTime,compareBound,compared⟩ := compareSortedNodes_executes separated query record.2
    (by simp [separated,read,queryAt]) (by simp [separated]) (by
      intro r allowed
      fin_cases r <;> simp_all [separated,read])
  have flagEmpty : separated 66=[] := by simp [separated,read,empty]
  rw [flagEmpty] at compared
  have final : Function.update separated 66 [Executable.lexLE query.key record.2.key]=
      comparedRecord store query record suffix := by
    simp only [separated,read,Function.update_idem,comparedRecord]
  rw [final] at compared
  refine ⟨readTime+1+((5*record.1.bits.length+2)+1+compareTime),?_,reading.sequence (split.sequence compared)⟩
  have nodeSize : (Encoding.node.encode record.2).length≤(store 80).length := by
    rw [source]
    simp only [recordCodec,Encoding.product,List.length_append]
    omega
  have indexSize : record.1.bits.length≤(store 80).length := by
    rw [source]
    simp only [recordCodec,Encoding.product,List.length_append,Encoding.natural_length,Encoding.bits_length]
    omega
  have querySize : separated 64=store 64 := by simp [separated,read]
  have currentSize : separated 65=Encoding.node.encode record.2 := by simp [separated]
  rw [querySize,currentSize] at compareBound
  let K := (store 80).length+(store 64).length+1
  have one : 1≤K := by omega
  have readPower : ((store 80).length+1)^3≤K^3 := by gcongr;omega
  have comparePower : ((store 64).length+(Encoding.node.encode record.2).length+1)^2≤K^3 := by
    calc
      _≤K^2 := by gcongr;omega
      _≤K^3 := Nat.pow_le_pow_right one (by decide)
  have linear : K≤K^3 := Nat.le_self_pow (by decide) _
  change _≤14000*K^3
  have indexK : record.1.bits.length≤K := by omega
  have onePower : 1≤K^3 := one_le_pow₀ one
  have readFinal := readBound.trans (Nat.mul_le_mul_left 2100 readPower)
  have compareFinal := compareBound.trans (Nat.mul_le_mul_left 11000 comparePower)
  omega

end Counting.StackMachine.DagUpdate.Sort
