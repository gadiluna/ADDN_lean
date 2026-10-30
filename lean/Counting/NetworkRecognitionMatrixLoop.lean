import Counting.NetworkRecognitionRow

namespace Counting.StackMachine.NetworkRecognition
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def rowLengths (width : Nat) (rows : List (List Nat)) : Bool := rows.all (fun row=>decide (width=row.length))
def adjacencyBits (rows : List (List Nat)) : List Bool := rows.flatMap (fun row=>row.map (fun value=>decide (0<value)))

def rowsStore (store : Store 19) (accepted : Bool) (tail : List Bool)
    (rows : List (List Nat)) (suffix : List Bool) : Store 19 :=
  Function.update (Function.update (Function.update (Function.update store 17 suffix) 20 [])
    1 ((accepted && rowLengths (store 0).length rows)::tail)) 19 ((adjacencyBits rows).reverse++store 19)

theorem rows_executes (store : Store 19) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀r:Fin 21,r.val<17 → r≠0 → r≠1 → store r=[])
    (e18 : store 18=[]) (rows : List (List Nat)) (suffix : List Bool)
    (input : store 17=Encoding.sequence (Encoding.list Encoding.natural) rows++suffix)
    (counter : store 20=List.replicate rows.length true) :
    ∃time ≤ rows.length*(1900*((store 17).length+(store 0).length+1)^3+2)+1,
      Executes (forEach 20 rowPrefix) store time (rowsStore store accepted tail rows suffix) := by
  induction rows generalizing store accepted with
  | nil =>
    obtain ⟨ran,halted⟩ := repeat_empty (20:Fin 21) rowPrefix store (by simpa using counter)
    have final : rowsStore store accepted tail [] suffix=store := by
      funext r
      by_cases r1:r=1 <;> by_cases r17:r=17 <;> by_cases r19:r=19 <;> by_cases r20:r=20 <;>
        simp_all [rowsStore,rowLengths,adjacencyBits,Encoding.sequence]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons row rows ih =>
    let consumed := Function.update store 20 (List.replicate rows.length true)
    let remaining := Encoding.sequence (Encoding.list Encoding.natural) rows++suffix
    obtain ⟨bodyTime,bodyBound,body,bodyRun,bodyHalted,bodyStore⟩ := rowPrefix_executes consumed accepted tail
      (by simp [consumed,status])
      (by intro r h n0 n1
          have n20:r≠20:=by intro eq;subst r;norm_num at h
          simpa [consumed,n20] using work r h n0 n1)
      (by simp [consumed,e18]) row remaining
      (by simpa [consumed,remaining,Encoding.sequence,List.append_assoc] using input)
    let middle := rowPrefixStore consumed accepted tail row remaining
    let next := accepted && decide ((store 0).length=row.length)
    obtain ⟨tailTime,tailBound,finish,tailRun,tailHalted,tailStore⟩ := ih middle next
      (by simp [middle,rowPrefixStore,consumed,next])
      (by intro r h n0 n1
          have n17:r≠17:=by intro eq;subst r;norm_num at h
          have n19:r≠19:=by intro eq;subst r;norm_num at h
          have n20:r≠20:=by intro eq;subst r;norm_num at h
          simpa [middle,rowPrefixStore,consumed,n1,n17,n19,n20] using work r h n0 n1)
      (by simp [middle,rowPrefixStore,consumed,e18])
      (by simp [middle,rowPrefixStore,remaining]) (by simp [middle,rowPrefixStore,consumed])
    have firstRun := repeat_iteration (20:Fin 21) rowPrefix store true (List.replicate rows.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter) bodyTime body bodyRun bodyHalted
    have final : rowsStore middle next tail rows suffix=rowsStore store accepted tail (row::rows) suffix := by
      funext r
      by_cases r1:r=1 <;> by_cases r17:r=17 <;> by_cases r19:r=19 <;> by_cases r20:r=20 <;>
        simp [rowsStore,rowLengths,adjacencyBits,middle,rowPrefixStore,consumed,next,
          r1,r17,r19,r20,Bool.and_assoc,List.append_assoc]
    have sourceLength : (middle 17).length ≤ (store 17).length := by
      rw [input]
      simp only [middle,rowPrefixStore,Function.update_of_ne (by decide : (17:Fin 21)≠19),
        Function.update_of_ne (by decide : (17:Fin 21)≠1),Function.update_self,
        remaining,Encoding.sequence,List.length_append]
      omega
    have width : middle 0=store 0 := by simp [middle,rowPrefixStore,consumed]
    rw [width] at tailBound
    have tailLimit : tailTime ≤ rows.length*(1900*((store 17).length+(store 0).length+1)^3+2)+1 := by
      apply tailBound.trans;gcongr
    simp only [consumed,Function.update_of_ne (by decide : (17:Fin 21)≠20),
      Function.update_of_ne (by decide : (0:Fin 21)≠20)] at bodyBound
    refine ⟨bodyTime+2+tailTime,?_,finish,?_,tailHalted,tailStore.trans final⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.NetworkRecognition
