import Counting.StackRealizabilityAccumulate
import Counting.StackDagEmptyGuard
import Counting.StackEncodingGuards

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def countAccumulatorRoles : Fin 4 ↪ Fin 21:=⟨![19,20,2,3],by decide⟩

def countItem : Routine 19:=sequence (ofProgram (unframeProgram 18 17 20 4))
  (sequence (DagValidation.emptyFlag 20 1)
    (sequence (negateFlag 19 1)
      (sequence (ofProgram (combineFlagsProgram 19 1)) (accumulateAt countAccumulatorRoles))))

def countItemStore (store : Store 19) (accepted : Bool) (tail suffix : List Bool) (total value : Nat) : Store 19:=
  Function.update (Function.update (Function.update store 17 suffix) 19 (total+value).bits)
    1 ((accepted && decide (0<value))::tail)

theorem countItem_executes (store : Store 19) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (e2 : store 2=[]) (e3 : store 3=[]) (e4 : store 4=[]) (e20 : store 20=[])
    (total value : Nat) (accumulator : store 19=total.bits) (suffix : List Bool)
    (input : store 17=Encoding.natural.encode value++suffix) :
    ∃ time ≤ 40*((store 17).length+total.size+1),
      Executes countItem store time (countItemStore store accepted tail suffix total value):=by
  have parsing:=unframe_canonical_executes 18 17 20 4 (by decide) (by decide) (by decide)
    store value.bits suffix input e4
  rw [e20,List.append_nil] at parsing
  let parsed:=Function.update (Function.update store 17 suffix) 20 value.bits
  have checking:=DagValidation.emptyFlag_executes (20:Fin 21) 1 parsed
  have valueAt : parsed 20=value.bits:=by simp [parsed]
  have statusAt : parsed 1=accepted::tail:=by simp [parsed,status]
  rw [valueAt,statusAt] at checking
  let flagged:=Function.update parsed 1 (decide (value.bits=[])::accepted::tail)
  have negating:=negateFlag_executes 19 1 flagged (decide (value.bits=[])) (accepted::tail)
    (by simp [flagged])
  let inverted:=Function.update flagged 1 ((!decide (value.bits=[]))::accepted::tail)
  have combining:=combineFlags_executes 19 1 inverted accepted (!decide (value.bits=[])) tail
    (by simp [inverted])
  have emptyIff : value.bits=[] ↔ value=0:=by
    constructor
    · intro empty
      have evaluated:=congrArg Encoding.value empty
      simpa only [Encoding.value_bits,Encoding.value] using evaluated
    · intro zero;subst value;rfl
  have positivity : (!decide (value.bits=[]))=decide (0<value):=by
    simp [emptyIff,Nat.pos_iff_ne_zero]
  have joined : Function.update inverted 1 ((accepted && !decide (value.bits=[]))::tail)=
      Function.update parsed 1 ((accepted && decide (0<value))::tail):=by
    simp only [inverted,flagged,Function.update_idem,positivity]
  rw [joined] at combining
  let checked:=Function.update parsed 1 ((accepted && decide (0<value))::tail)
  obtain ⟨sumTime,sumBound,adding⟩:=accumulateAt_executes countAccumulatorRoles checked
    (by simp [countAccumulatorRoles,checked,parsed,e2])
    (by simp [countAccumulatorRoles,checked,parsed,e3])
  have first : checked (countAccumulatorRoles 0)=total.bits:=by
    simp [countAccumulatorRoles,checked,parsed,accumulator]
  have second : checked (countAccumulatorRoles 1)=value.bits:=by
    simp [countAccumulatorRoles,checked,parsed]
  rw [first,second,Encoding.value_bits,Encoding.value_bits] at adding
  rw [first,second,Encoding.bits_length,Encoding.bits_length] at sumBound
  have final : Function.update (Function.update checked (countAccumulatorRoles 0) (total+value).bits)
      (countAccumulatorRoles 1) []=countItemStore store accepted tail suffix total value:=by
    funext r
    by_cases r1 : r=1 <;> by_cases r17 : r=17 <;> by_cases r19 : r=19 <;> by_cases r20 : r=20 <;>
      simp [countAccumulatorRoles,checked,parsed,countItemStore,r1,r17,r19,r20,e20]
  rw [final] at adding
  have valueLength : value.size≤(store 17).length:=by
    rw [input,List.length_append,Encoding.natural_length]
    omega
  have emptyCost : DagValidation.emptyFlagCost value.bits≤3:=by
    unfold DagValidation.emptyFlagCost;split_ifs <;> omega
  refine ⟨_,?_,parsing.sequence (checking.sequence (negating.sequence (combining.sequence adding)))⟩
  rw [Encoding.bits_length]
  omega

end Counting.StackMachine.RealizabilityCheck
