import Counting.StackRealizabilityCountItem

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def positiveCounts (values : List Nat) : Bool:=values.all (fun value=>decide (0<value))

theorem nat_add_size_le (first second : Nat) : (first+second).size≤first.size+second.size+1:=by
  simpa only [Encoding.value_bits,Encoding.bits_length] using sum_bits_length first.bits second.bits

def countValuesStore (store : Store 19) (accepted : Bool) (tail suffix : List Bool)
    (total : Nat) (values : List Nat) : Store 19:=
  Function.update (Function.update (Function.update (Function.update store 18 []) 17 suffix)
    19 (total+values.sum).bits) 1 ((accepted && positiveCounts values)::tail)

theorem countValues_executes (store : Store 19) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (e2 : store 2=[]) (e3 : store 3=[]) (e4 : store 4=[]) (e20 : store 20=[])
    (total : Nat) (accumulator : store 19=total.bits) (values : List Nat) (suffix : List Bool)
    (input : store 17=Encoding.sequence Encoding.natural values++suffix)
    (bits : List Bool) (counter : store 18=bits) (countEq : bits.length=values.length) :
    ∃ time ≤ values.length*(40*((store 17).length+total.size+1)+2)+1,
      Executes (forEach 18 countItem) store time (countValuesStore store accepted tail suffix total values):=by
  induction values generalizing store accepted total bits with
  | nil=>
    have emptyBits : bits=[]:=List.length_eq_zero_iff.mp countEq
    have empty : store 18=[]:=counter.trans emptyBits
    have source : store 17=suffix:=by simpa only [Encoding.sequence,List.nil_append] using input
    obtain ⟨ran,halted⟩:=repeat_empty (18:Fin 21) countItem store empty
    have final : countValuesStore store accepted tail suffix total []=store:=by
      funext r
      by_cases r1 : r=1 <;> by_cases r17 : r=17 <;> by_cases r18 : r=18 <;> by_cases r19 : r=19 <;>
        simp [countValuesStore,positiveCounts,r1,r17,r18,r19,status,empty,source,accumulator]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons value values ih=>
    cases bits with
    | nil=>simp at countEq
    | cons bit bits=>
      let consumed:=Function.update store 18 bits
      let remaining:=Encoding.sequence Encoding.natural values++suffix
      have headInput : consumed 17=Encoding.natural.encode value++remaining:=by
        simpa only [consumed,Function.update_of_ne (by decide : (17:Fin 21)≠18),
          Encoding.sequence,List.append_assoc] using input
      obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩:=countItem_executes consumed accepted tail
        (by simp [consumed,status]) (by simp [consumed,e2]) (by simp [consumed,e3])
        (by simp [consumed,e4]) (by simp [consumed,e20]) total value (by simp [consumed,accumulator])
        remaining headInput
      let middle:=countItemStore consumed accepted tail remaining total value
      let nextAccepted:=accepted && decide (0<value)
      obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩:=ih middle nextAccepted
        (by simp [middle,countItemStore,nextAccepted])
        (by simp [middle,countItemStore,consumed,e2]) (by simp [middle,countItemStore,consumed,e3])
        (by simp [middle,countItemStore,consumed,e4]) (by simp [middle,countItemStore,consumed,e20])
        (total+value) (by simp [middle,countItemStore]) (by simp [middle,countItemStore,remaining])
        bits (by simp [middle,countItemStore,consumed]) (by simpa using countEq)
      have firstRun:=repeat_iteration (18:Fin 21) countItem store bit bits counter bodyTime finishBody bodyRun bodyHalt
      have final : countValuesStore middle nextAccepted tail suffix (total+value) values=
          countValuesStore store accepted tail suffix total (value::values):=by
        funext r
        by_cases r1 : r=1 <;> by_cases r17 : r=17 <;> by_cases r18 : r=18 <;> by_cases r19 : r=19 <;>
          simp [countValuesStore,positiveCounts,middle,countItemStore,consumed,nextAccepted,
            r1,r17,r18,r19,Bool.and_assoc,Nat.add_assoc]
      refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalt,tailStore.trans final⟩
      · have sourceSame : consumed 17=store 17:=by simp [consumed]
        rw [sourceSame] at bodyBound
        have sourceSize : (middle 17).length+(total+value).size≤(store 17).length+total.size:=by
          have addedSize:=nat_add_size_le total value
          rw [input]
          simp only [middle,countItemStore,Function.update_of_ne (by decide : (17:Fin 21)≠1),
            Function.update_of_ne (by decide : (17:Fin 21)≠19),Function.update_self]
          simp only [remaining,Encoding.sequence,List.length_append,Encoding.natural_length]
          omega
        have tailLimit : tailTime≤values.length*(40*((store 17).length+total.size+1)+2)+1:=by
          apply tailBound.trans
          gcongr
        simp only [List.length_cons]
        nlinarith
      · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
        exact tailRun

end Counting.StackMachine.RealizabilityCheck
