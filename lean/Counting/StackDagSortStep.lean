import Counting.StackDagSortReadCompare
import Counting.StackDagSortSelect
import Counting.StackDagSortEmit

namespace Counting.StackMachine.DagUpdate.Sort
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

def insertionStep : Routine 94 := sequence readCompare (sequence selectInsertion emitCurrent)

def insertionStepResult (store : Store 94) (query current : Record) (suffix : List Bool) (inserted : Bool) : Store 94 :=
  let before := Executable.lexLE query.2.key current.2.key
  Function.update (Function.update (Function.update store 80 suffix) 84 [inserted || before])
    83 ((recordCodec.encode current).reverse++
      (if !inserted && before then (recordCodec.encode query).reverse++store 83 else store 83))

/-- One physical insertion scan retains both original local indices and
emits the query before the first greater-or-equal signature. -/
theorem insertionStep_executes (store : Store 94) (query current : Record) (suffix : List Bool) (inserted : Bool)
    (source : store 80=recordCodec.encode current++suffix)
    (queryAt : store 64=Encoding.node.encode query.2) (recordAt : store 82=recordCodec.encode query)
    (status : store 81=[true]) (flagAt : store 84=[inserted])
    (empty : ∀ r : Fin 96,r.val≤14 ∨ (40≤r.val ∧ r.val≤44) ∨ (49≤r.val ∧ r.val≤51) ∨
      r=65 ∨ r=66 ∨ r=67 ∨ r=86 ∨ r=88 ∨ r=89 → store r=[]) :
    ∃ time≤15000*((store 80).length+(store 82).length+1)^3,
      Executes insertionStep store time (insertionStepResult store query current suffix inserted) := by
  obtain ⟨readTime,readBound,readRun⟩ := readCompare_executes store query.2 current suffix source queryAt status (by
    intro r allowed
    apply empty r
    tauto)
  let read := comparedRecord store query.2 current suffix
  let before := Executable.lexLE query.2.key current.2.key
  have selectRun := selectInsertion_executes read inserted before
    (by simp [read,comparedRecord,flagAt]) (by simp [read,comparedRecord,before])
    (by simp [read,comparedRecord,empty]) (by simp [read,comparedRecord,empty])
  let selected := selectedStore read inserted before
  have emitRun := emitCurrent_executes selected current
    (by simp [selected,selectedStore,read,comparedRecord])
    (by simp [selected,selectedStore,read,comparedRecord])
    (by simp [selected,selectedStore,read,comparedRecord,empty])
  have final : Function.update (Function.update (Function.update selected 65 []) 88 [])
      83 ((recordCodec.encode current).reverse++selected 83)=
      insertionStepResult store query current suffix inserted := by
    funext r
    fin_cases r <;> simp [selected,selectedStore,read,comparedRecord,insertionStepResult,before,recordAt,empty]
  rw [final] at emitRun
  refine ⟨readTime+1+(selectionCost read inserted before+1+emitCurrentCost current),?_,
    readRun.sequence (selectRun.sequence emitRun)⟩
  have nodeQuery : (store 64).length≤(store 82).length := by
    rw [queryAt,recordAt]
    simp only [recordCodec,Encoding.product,List.length_append]
    omega
  have currentSize : (recordCodec.encode current).length≤(store 80).length := by
    rw [source,List.length_append]
    omega
  have indexSize : current.1.bits.length≤(store 80).length := by
    rw [source]
    simp only [recordCodec,Encoding.product,List.length_append,Encoding.natural_length,Encoding.bits_length]
    omega
  have selectBound : selectionCost read inserted before≤7*(store 82).length+13 := by
    cases inserted <;> cases before <;> simp [selectionCost,read,comparedRecord]
  have emitBound : emitCurrentCost current≤7*(store 80).length+6 := by
    unfold emitCurrentCost
    omega
  let K := (store 80).length+(store 82).length+1
  have sizePower : ((store 80).length+(store 64).length+1)^3≤K^3 := by gcongr;omega
  have linear : K≤K^3 := Nat.le_self_pow (by decide) _
  have positive : 1≤K := by omega
  change _≤15000*K^3
  have readFinal := readBound.trans (Nat.mul_le_mul_left 14000 sizePower)
  have extraBound : selectionCost read inserted before+emitCurrentCost current+2≤7*K+14 := by omega
  have onePower : 1≤K^3 := one_le_pow₀ positive
  omega

end Counting.StackMachine.DagUpdate.Sort
