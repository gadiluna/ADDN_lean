import Counting.StackRowAddStep
import Counting.StackLoop

namespace Counting.StackMachine.RowAdd
open Routine

abbrev loop : Routine 34 := forEach 3 body

theorem loop_executes (pairs : List (Rat×Rat)) (leftSuffix rightSuffix reversed header status : List Bool)
    (limit : Nat) (bounded : ∀ pair∈pairs,
      (Encoding.rational.encode pair.1).length+(Encoding.rational.encode pair.2).length≤limit) :
    ∃ time ≤ pairs.length*(700000000*(limit+1)^3+2)+1,
      Executes loop
        (file (Encoding.sequence (Encoding.framed Encoding.rational) (pairs.map Prod.fst)++leftSuffix)
          (Encoding.sequence (Encoding.framed Encoding.rational) (pairs.map Prod.snd)++rightSuffix)
          reversed (List.replicate pairs.length true) [] [] [] [] header status []) time
        (file leftSuffix rightSuffix
          ((Encoding.sequence (Encoding.framed Encoding.rational) (pairs.map (fun pair => pair.1+pair.2))).reverse++reversed)
          [] [] [] [] [] header status []) := by
  induction pairs generalizing reversed with
  | nil =>
    have ran := repeat_empty 3 body (file leftSuffix rightSuffix reversed [] [] [] [] [] header status []) rfl
    exact ⟨1,by simp,⟨⟨1,_⟩,ran.1,ran.2,rfl⟩⟩
  | cons pair rest ih =>
    let first := Encoding.rational.encode pair.1
    let second := Encoding.rational.encode pair.2
    let left := Encoding.frame first++(Encoding.sequence (Encoding.framed Encoding.rational) (rest.map Prod.fst)++leftSuffix)
    let right := Encoding.frame second++(Encoding.sequence (Encoding.framed Encoding.rational) (rest.map Prod.snd)++rightSuffix)
    let count := List.replicate rest.length true
    let nextReversed := (Encoding.frame (Encoding.rational.encode (pair.1+pair.2))).reverse++reversed
    let start := file left right reversed (true::count) [] [] [] [] header status []
    have counterUpdate : Function.update start 3 count = file left right reversed count [] [] [] [] header status [] := by
      funext r; fin_cases r <;> simp [start,file]
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩ := body_executes first second
      (Encoding.sequence (Encoding.framed Encoding.rational) (rest.map Prod.fst)++leftSuffix)
      (Encoding.sequence (Encoding.framed Encoding.rational) (rest.map Prod.snd)++rightSuffix)
      reversed count header status
    have exactSum : RationalArithmetic.Addition.additionFunction (first++second) =
        Encoding.rational.encode (pair.1+pair.2) := RationalArithmetic.Addition.additionFunction_rationals pair.1 pair.2
    rw [exactSum] at bodyStore
    have firstRun := repeat_iteration 3 body start true count rfl bodyTime finishBody
      (by rw [counterUpdate]; exact bodyRun) bodyHalt
    change Machine.run (step loop.program) (bodyTime+2) ⟨0,start⟩ = some ⟨0,finishBody.store⟩ at firstRun
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩ := ih nextReversed
      (by intro x member; exact bounded x (List.mem_cons_of_mem pair member))
    have currentBound := bounded pair (List.mem_cons_self)
    change bodyTime ≤ 700000000*((Encoding.rational.encode pair.1).length+(Encoding.rational.encode pair.2).length+1)^3 at bodyBound
    have power := Nat.pow_le_pow_left
      (show (Encoding.rational.encode pair.1).length+(Encoding.rational.encode pair.2).length+1 ≤ limit+1 by omega) 3
    refine ⟨bodyTime+2+tailTime,?_,⟨finishTail,?_,tailHalt,?_⟩⟩
    · simp only [List.length_cons]
      nlinarith
    · have combined := Machine.run_add (step loop.program) (bodyTime+2) tailTime ⟨0,start⟩
      rw [firstRun,Option.bind_some,bodyStore] at combined
      rw [tailRun] at combined
      simpa only [start,left,right,count,first,second,Encoding.sequence,Encoding.framed,
        List.map_cons,List.length_cons,List.replicate_succ,List.append_assoc] using combined
    · rw [tailStore]
      simp only [List.map_cons,Encoding.sequence,Encoding.framed,List.reverse_append,List.append_assoc]
      rfl

end Counting.StackMachine.RowAdd
