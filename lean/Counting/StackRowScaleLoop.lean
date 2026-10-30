import Counting.StackRowScaleStep
import Counting.StackLoop

namespace Counting.StackMachine.RowScale
open Routine

abbrev loop : Routine 30 := forEach 3 body

theorem loop_executes (factor : Rat) (row : List Rat) (suffix reversed header status : List Bool)
    (limit : Nat) (bounded : ∀ value∈row,(Encoding.rational.encode value).length≤limit) :
    ∃ time ≤ row.length*(150000000*((Encoding.rational.encode factor).length+limit+1)^3+2)+1,
      Executes loop
        (file (Encoding.rational.encode factor) (Encoding.sequence (Encoding.framed Encoding.rational) row++suffix)
          reversed (List.replicate row.length true) [] [] header status []) time
        (file (Encoding.rational.encode factor) suffix
          ((Encoding.sequence (Encoding.framed Encoding.rational) (row.map (factor*·))).reverse++reversed)
          [] [] [] header status []) := by
  induction row generalizing reversed with
  | nil =>
    have ran := repeat_empty 3 body (file (Encoding.rational.encode factor) suffix reversed [] [] [] header status []) rfl
    exact ⟨1,by simp,⟨⟨1,_⟩,ran.1,ran.2,rfl⟩⟩
  | cons value rest ih =>
    let factorCode := Encoding.rational.encode factor
    let valueCode := Encoding.rational.encode value
    let input := Encoding.frame valueCode++(Encoding.sequence (Encoding.framed Encoding.rational) rest++suffix)
    let count := List.replicate rest.length true
    let nextReversed := (Encoding.frame (Encoding.rational.encode (factor*value))).reverse++reversed
    let start := file factorCode input reversed (true::count) [] [] header status []
    have counterUpdate : Function.update start 3 count = file factorCode input reversed count [] [] header status [] := by
      funext r; fin_cases r <;> simp [start,file]
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩ := body_executes factorCode valueCode
      (Encoding.sequence (Encoding.framed Encoding.rational) rest++suffix) reversed count header status
    have exactProduct : RationalArithmetic.Product.productFunction (factorCode++valueCode) =
        Encoding.rational.encode (factor*value) := RationalArithmetic.Product.productFunction_rationals factor value
    rw [exactProduct] at bodyStore
    have firstRun := repeat_iteration 3 body start true count rfl bodyTime finishBody
      (by rw [counterUpdate]; exact bodyRun) bodyHalt
    change Machine.run (step loop.program) (bodyTime+2) ⟨0,start⟩ = some ⟨0,finishBody.store⟩ at firstRun
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩ := ih nextReversed
      (by intro x member; exact bounded x (List.mem_cons_of_mem value member))
    have currentBound := bounded value (List.mem_cons_self)
    change bodyTime ≤ 150000000*((Encoding.rational.encode factor).length+(Encoding.rational.encode value).length+1)^3 at bodyBound
    have power := Nat.pow_le_pow_left
      (show (Encoding.rational.encode factor).length+(Encoding.rational.encode value).length+1 ≤
        (Encoding.rational.encode factor).length+limit+1 by omega) 3
    refine ⟨bodyTime+2+tailTime,?_,⟨finishTail,?_,tailHalt,?_⟩⟩
    · simp only [List.length_cons]
      nlinarith
    · have combined := Machine.run_add (step loop.program) (bodyTime+2) tailTime ⟨0,start⟩
      rw [firstRun,Option.bind_some,bodyStore] at combined
      rw [tailRun] at combined
      simpa only [start,input,count,factorCode,valueCode,Encoding.sequence,Encoding.framed,
        List.length_cons,List.replicate_succ,List.append_assoc] using combined
    · rw [tailStore]
      simp only [List.map_cons,Encoding.sequence,Encoding.framed,List.reverse_append,List.append_assoc]
      rfl

end Counting.StackMachine.RowScale
