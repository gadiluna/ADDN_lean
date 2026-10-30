import Counting.StackRealizabilityReachRowPrepare
import Counting.StackEncodingGuards

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def rowLookupRoles : Fin 7 ↪ Fin 24:=⟨![18,17,22,6,9,10,11],by decide⟩
def rowFinish : Routine 22:=sequence (bitLookup 17 rowLookupRoles)
  (sequence (negateFlag 22 22)
    (sequence (BooleanFold.single .disjunction 22 21)
      (sequence (BooleanFold.single .conjunction 21 19) (pushBit 17 true))))

def rowFinishStore (store : Store 22) (value row : Bool) (tail : List Bool) : Store 22:=
  Function.update (Function.update (Function.update (Function.update store 21 []) 22 [])
    19 ((value && (!RealizabilityVerifier.BitGraph.bitAt (store 18) (store 17).length || row))::tail))
    17 (true::store 17)

theorem rowFinish_executes (store : Store 22) (value row : Bool) (tail : List Bool)
    (globalFlag : store 19=value::tail) (rowFlag : store 21=[row]) (e22 : store 22=[])
    (e9 : store 9=[]) (e10 : store 10=[]) (e11 : store 11=[]) :
    ∃ time ≤ 40*((store 18).length+(store 17).length+1),
      Executes rowFinish store time (rowFinishStore store value row tail):=by
  obtain ⟨readTime,readBound,reading⟩:=bitLookup_executes 17 rowLookupRoles store e9 e10 e11
  change readTime ≤ 6*(store 18).length+7*(store 17).length+16 at readBound
  let bit:=RealizabilityVerifier.BitGraph.bitAt (store 18) (store 17).length
  change Executes (bitLookup 17 rowLookupRoles) store readTime
    (Function.update store 22 (bit::store 22)) at reading
  rw [e22] at reading
  let read:=Function.update store 22 [bit]
  have negating:=negateFlag_executes 22 22 read bit [] (by simp [read])
  let negated:=Function.update read 22 [!bit]
  have disjoining:=BooleanFold.single_executes .disjunction (22:Fin 24) 21 (by decide) negated
    (!bit) row [] [] (by simp [negated]) (by simp [negated,read,rowFlag])
  let disjoined:=BooleanFold.updated (22:Fin 24) 21 negated [] (BooleanFold.operation .disjunction row (!bit)) []
  have conjoining:=BooleanFold.single_executes .conjunction (21:Fin 24) 19 (by decide) disjoined
    (row || !bit) value [] tail (by simp [disjoined,BooleanFold.updated,BooleanFold.operation])
    (by simp [disjoined,BooleanFold.updated,negated,read,globalFlag])
  let conjoined:=BooleanFold.updated (21:Fin 24) 19 disjoined []
    (BooleanFold.operation .conjunction value (row || !bit)) tail
  have increment:=pushBit_executes (17:Fin 24) true conjoined
  have sourceAt : conjoined 17=store 17:=by
    simp [conjoined,disjoined,BooleanFold.updated,negated,read]
  rw [sourceAt] at increment
  have final : Function.update conjoined 17 (true::store 17)=rowFinishStore store value row tail:=by
    funext r
    by_cases n17 : r=17 <;> by_cases n19 : r=19 <;> by_cases n21 : r=21 <;> by_cases n22 : r=22 <;>
      simp [conjoined,disjoined,BooleanFold.updated,BooleanFold.operation,negated,read,bit,
        rowFinishStore,n17,n19,n21,n22,Bool.or_comm]
  rw [final] at increment
  exact ⟨_,by omega,reading.sequence (negating.sequence (disjoining.sequence (conjoining.sequence increment)))⟩

def rowValue (store : Store 22) : Bool:=
  !RealizabilityVerifier.BitGraph.bitAt (store 18) (store 17).length || rowReachable store

def rowItemStore (store : Store 22) (value : Bool) (tail : List Bool) : Store 22:=
  Function.update (Function.update store 19 ((value && rowValue store)::tail)) 17 (true::store 17)

def rowItem : Routine 22:=sequence rowPrepare rowFinish

theorem rowItem_executes (store : Store 22) (value : Bool) (tail : List Bool)
    (accumulated : store 19=value::tail) (empty : RowEmpty store) :
    ∃ time ≤ 202000*((store 0).length+(store 18).length+(store 2).length+(store 17).length+1)^5,
      Executes rowItem store time (rowItemStore store value tail):=by
  obtain ⟨prepareTime,prepareBound,preparing⟩:=rowPrepare_executes store empty
  let prepared:=Function.update store 21 [rowReachable store]
  obtain ⟨finishTime,finishBound,finishing⟩:=rowFinish_executes prepared value (rowReachable store) tail
    (by simp [prepared,accumulated]) (by simp [prepared])
    (by simp [prepared,empty 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by simp [prepared,empty 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by simp [prepared,empty 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by simp [prepared,empty 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
  have final : rowFinishStore prepared value (rowReachable store) tail=rowItemStore store value tail:=by
    funext r
    by_cases n17 : r=17 <;> by_cases n19 : r=19 <;> by_cases n21 : r=21 <;> by_cases n22 : r=22 <;>
      simp [prepared,rowFinishStore,rowItemStore,rowValue,n17,n19,n21,n22,
        empty 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        empty 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [final] at finishing
  have finishLimit : finishTime ≤ 40*((store 18).length+(store 17).length+1):=by
    simpa [prepared] using finishBound
  let S:=(store 0).length+(store 18).length+(store 2).length+(store 17).length+1
  have linear : S ≤ S^5:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^5:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  exact ⟨_,by change _ ≤ 202000*S^5;dsimp only [S] at linear one ⊢;omega,
    preparing.sequence finishing⟩

end Counting.StackMachine.RealizabilityCheck
