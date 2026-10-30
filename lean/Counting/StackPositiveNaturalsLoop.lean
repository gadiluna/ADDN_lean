import Counting.StackPositiveNaturalsStep
import Counting.StackRowScaleHeader

namespace Counting.StackMachine.PositiveNaturals
open Routine

abbrev loop : Routine 30 := forEach 3 body

theorem loop_executes (row : List Rat) (suffix reversed header : List Bool) (accepted : Bool)
    (limit : Nat) (bounded : ∀ value∈row,(Encoding.rational.encode value).length≤limit) :
    ∃ time ≤ row.length*(5000*(limit+1)+2)+1,
      Executes loop
        (RowScale.file [] (Encoding.sequence (Encoding.framed Encoding.rational) row++suffix)
          reversed (List.replicate row.length true) [] [] header [accepted] []) time
        (RowScale.file [] suffix
          ((Encoding.sequence Encoding.natural (row.map (fun value => value.num.toNat))).reverse++reversed)
          [] [] [] header [accepted && row.all Counting.PositiveNaturals.guard] []) := by
  induction row generalizing reversed accepted with
  | nil =>
      have ran := repeat_empty 3 body (RowScale.file [] suffix reversed [] [] [] header [accepted] []) rfl
      refine ⟨1,by simp,⟨⟨1,_⟩,ran.1,ran.2,?_⟩⟩
      simp [Encoding.sequence]
  | cons value rest ih =>
      let input := Encoding.frame (Encoding.rational.encode value)++
        (Encoding.sequence (Encoding.framed Encoding.rational) rest++suffix)
      let count := List.replicate rest.length true
      let nextReversed := (Encoding.natural.encode value.num.toNat).reverse++reversed
      let nextAccepted := accepted && Counting.PositiveNaturals.guard value
      let start := RowScale.file [] input reversed (true::count) [] [] header [accepted] []
      have counterUpdate : Function.update start 3 count = RowScale.file [] input reversed count [] [] header [accepted] [] := by
        funext r; fin_cases r <;> simp [start,RowScale.file]
      obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩ := body_executes value
        (Encoding.sequence (Encoding.framed Encoding.rational) rest++suffix) reversed count header accepted
      have firstRun := repeat_iteration 3 body start true count rfl bodyTime finishBody
        (by rw [counterUpdate]; exact bodyRun) bodyHalt
      change Machine.run (step loop.program) (bodyTime+2) ⟨0,start⟩=some ⟨0,finishBody.store⟩ at firstRun
      obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩ := ih nextReversed nextAccepted
        (by intro x member; exact bounded x (List.mem_cons_of_mem value member))
      have currentBound := bounded value (List.mem_cons_self)
      refine ⟨bodyTime+2+tailTime,?_,⟨finishTail,?_,tailHalt,?_⟩⟩
      · simp only [List.length_cons]
        nlinarith
      · have combined := Machine.run_add (step loop.program) (bodyTime+2) tailTime ⟨0,start⟩
        rw [firstRun,Option.bind_some,bodyStore,tailRun] at combined
        simpa only [start,input,count,Encoding.sequence,Encoding.framed,List.length_cons,
          List.replicate_succ,List.append_assoc] using combined
      · rw [tailStore]
        simp only [List.map_cons,Encoding.sequence,List.reverse_append,List.append_assoc,
          List.all_cons,Bool.and_assoc,nextAccepted,nextReversed]

end Counting.StackMachine.PositiveNaturals
