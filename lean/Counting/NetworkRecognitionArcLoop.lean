import Counting.NetworkRecognitionArc
import Counting.StackRegisterFrames

namespace Counting.StackMachine.NetworkRecognition
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def arcRoles : Fin 4 ↪ Fin 21 := ⟨![17,19,2,4],by decide⟩
def arcItem : Routine 19 := relocate arcBit arcRoles

def arcItemStore (store : Store 19) (value : Nat) (suffix : List Bool) : Store 19 :=
  Function.update (Function.update store 17 suffix) 19 (decide (0<value)::store 19)

theorem arcItem_executes (store : Store 19) (value : Nat) (suffix : List Bool)
    (input : store 17=Encoding.natural.encode value++suffix) (e2 : store 2=[]) (e4 : store 4=[]) :
    ∃time ≤ 6*value.size+11, Executes arcItem store time (arcItemStore store value suffix) := by
  obtain ⟨time,bound,executed⟩ := arcBit_executes (store ∘ arcRoles) value suffix
    (by simpa [arcRoles] using input) (by simpa [arcRoles] using e2) (by simpa [arcRoles] using e4)
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame arcBit arcRoles store (arcItemStore store value suffix)
    (store ∘ arcRoles) (arcBitStore (store ∘ arcRoles) value suffix) time rfl
  · intro i;fin_cases i <;> simp [arcRoles,arcItemStore,arcBitStore]
  · intro r outside
    have n17 := (outside 0).symm
    have n19 := (outside 1).symm
    change r≠17 at n17
    change r≠19 at n19
    simp [arcItemStore,n17,n19]
  · exact executed

def arcValuesStore (store : Store 19) (values : List Nat) (suffix : List Bool) : Store 19 :=
  Function.update (Function.update (Function.update store 17 suffix) 18 [])
    19 ((values.map (fun value=>decide (0<value))).reverse++store 19)

theorem arcValues_executes (store : Store 19) (values : List Nat) (suffix : List Bool)
    (input : store 17=Encoding.sequence Encoding.natural values++suffix)
    (counter : store 18=List.replicate values.length true) (e2 : store 2=[]) (e4 : store 4=[]) :
    ∃time ≤ values.length*(6*(store 17).length+13)+1,
      Executes (forEach 18 arcItem) store time (arcValuesStore store values suffix) := by
  induction values generalizing store with
  | nil =>
    obtain ⟨ran,halted⟩ := repeat_empty (18:Fin 21) arcItem store (by simpa using counter)
    have final : arcValuesStore store [] suffix=store := by
      funext r
      by_cases r17:r=17 <;> by_cases r18:r=18 <;> by_cases r19:r=19 <;>
        simp_all [arcValuesStore,Encoding.sequence]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons value values ih =>
    let consumed := Function.update store 18 (List.replicate values.length true)
    let remaining := Encoding.sequence Encoding.natural values++suffix
    obtain ⟨bodyTime,bodyBound,body,bodyRun,bodyHalted,bodyStore⟩ := arcItem_executes consumed value remaining
      (by simpa [consumed,remaining,Encoding.sequence,List.append_assoc] using input)
      (by simp [consumed,e2]) (by simp [consumed,e4])
    let middle := arcItemStore consumed value remaining
    obtain ⟨tailTime,tailBound,finish,tailRun,tailHalted,tailStore⟩ := ih middle
      (by simp [middle,arcItemStore,remaining]) (by simp [middle,arcItemStore,consumed])
      (by simp [middle,arcItemStore,consumed,e2]) (by simp [middle,arcItemStore,consumed,e4])
    have firstRun := repeat_iteration (18:Fin 21) arcItem store true (List.replicate values.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter) bodyTime body bodyRun bodyHalted
    have final : arcValuesStore middle values suffix=arcValuesStore store (value::values) suffix := by
      funext r
      by_cases r17:r=17 <;> by_cases r18:r=18 <;> by_cases r19:r=19 <;>
        simp [arcValuesStore,middle,arcItemStore,consumed,r17,r18,r19,List.append_assoc]
    have sourceLength : (middle 17).length ≤ (store 17).length := by
      rw [input]
      simp only [middle,arcItemStore,Function.update_of_ne (by decide : (17:Fin 21)≠19),Function.update_self,
        remaining,Encoding.sequence,List.length_append]
      omega
    have valueLength : value.size ≤ (store 17).length := by
      rw [input]
      simp only [Encoding.sequence,List.length_append,Encoding.natural_length]
      omega
    have tailLimit : tailTime ≤ values.length*(6*(store 17).length+13)+1 := by
      apply tailBound.trans
      gcongr
    refine ⟨bodyTime+2+tailTime,?_,finish,?_,tailHalted,tailStore.trans final⟩
    · simp only [List.length_cons]
      nlinarith
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.NetworkRecognition
