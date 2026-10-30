import Counting.StackGaussianPivotStep
import Counting.StackLoop

namespace Counting.StackMachine.GaussianPivot
open Routine

/-- Result flag `true` means the bounded search exhausted all candidates. -/
def search (value : Nat → Rat) : Nat → Nat → Nat × Bool
  | 0,row => (row,true)
  | count+1,row => if value row=0 then search value count (row+1) else (row,false)

abbrev loop : Routine 29 := forEach 29 body

theorem loop_inactive (matrix : List Bool) (row column count : Nat) :
    Executes loop (state matrix row column (List.replicate count true) false)
      (5*count+1) (state matrix row column [] false) := by
  induction count with
  | zero =>
    have ran := repeat_empty 29 body (state matrix row column [] false) rfl
    exact ⟨⟨1,_⟩,ran.1,ran.2,rfl⟩
  | succ count ih =>
    let start := state matrix row column (true::List.replicate count true) false
    have updated : Function.update start 29 (List.replicate count true)=
        state matrix row column (List.replicate count true) false := by
      funext r;fin_cases r <;> simp [start,state,file]
    obtain ⟨finishBody,bodyRun,bodyHalt,bodyStore⟩ := body_inactive matrix row column (List.replicate count true)
    have first := repeat_iteration 29 body start true (List.replicate count true) rfl 3 finishBody
      (by rw [updated];exact bodyRun) bodyHalt
    obtain ⟨finishTail,tailRun,tailHalt,tailStore⟩ := ih
    refine ⟨finishTail,?_,tailHalt,tailStore⟩
    have combined := Machine.run_add (step loop.program) 5 (5*count+1) ⟨0,start⟩
    rw [first,Option.bind_some,bodyStore,tailRun] at combined
    simpa only [start,List.replicate_succ,show 5+ (5*count+1)=5*(count+1)+1 by omega] using combined

/-- The implemented finite loop searches precisely the supplied consecutive
rows. Matrix lookup and scalar testing are executed only until the first
nonzero entry; later loop iterations still pay their control-flow steps. -/
theorem loop_executes (rows : List (List Rat)) (column : Nat) (value : Nat → Rat)
    (entries : ∀ row : Fin rows.length, rows[row.val][column]?=some (value row.val))
    (count start : Nat) (inside : start+count≤rows.length) :
    ∃ time ≤ count*(5000*((Encoding.rationalMatrix.encode rows).length+rows.length+column+count+7)+2)+1,
      Executes loop (state (Encoding.rationalMatrix.encode rows) start column (List.replicate count true) true) time
        (state (Encoding.rationalMatrix.encode rows) (search value count start).1 column [] (search value count start).2) := by
  induction count generalizing start with
  | zero =>
    have ran := repeat_empty 29 body (state (Encoding.rationalMatrix.encode rows) start column [] true) rfl
    exact ⟨1,by simp,⟨⟨1,_⟩,ran.1,ran.2,rfl⟩⟩
  | succ count ih =>
    let row : Fin rows.length := ⟨start,by omega⟩
    let matrix := Encoding.rationalMatrix.encode rows
    let initial := state matrix start column (true::List.replicate count true) true
    have updated : Function.update initial 29 (List.replicate count true)=
        state matrix start column (List.replicate count true) true := by
      funext r; fin_cases r <;> simp [initial,state,file]
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩ := body_active rows row column (value start)
      (entries row) (List.replicate count true)
    have first := repeat_iteration 29 body initial true (List.replicate count true) rfl bodyTime finishBody
      (by rw [updated];exact bodyRun) bodyHalt
    change Machine.run (step loop.program) (bodyTime+2) ⟨0,initial⟩=some ⟨0,finishBody.store⟩ at first
    simp only [List.length_replicate] at bodyBound
    change bodyTime≤5000*(matrix.length+start+column+count+7) at bodyBound
    by_cases zero : value start=0
    · simp only [show row.val=start from rfl,if_pos zero] at bodyStore
      obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩ := ih (start+1) (by omega)
      refine ⟨bodyTime+2+tailTime,?_,⟨finishTail,?_,tailHalt,?_⟩⟩
      · dsimp [matrix] at bodyBound
        nlinarith
      · have combined := Machine.run_add (step loop.program) (bodyTime+2) tailTime ⟨0,initial⟩
        rw [first,Option.bind_some,bodyStore,tailRun] at combined
        simpa only [initial,List.replicate_succ] using combined
      · simpa only [search,if_pos zero] using tailStore
    · simp only [show row.val=start from rfl,if_neg zero] at bodyStore
      obtain ⟨finishTail,tailRun,tailHalt,tailStore⟩ := loop_inactive matrix start column count
      refine ⟨bodyTime+2+(5*count+1),?_,⟨finishTail,?_,tailHalt,?_⟩⟩
      · dsimp [matrix] at bodyBound
        nlinarith
      · have combined := Machine.run_add (step loop.program) (bodyTime+2) (5*count+1) ⟨0,initial⟩
        rw [first,Option.bind_some,bodyStore,tailRun] at combined
        simpa only [initial,List.replicate_succ] using combined
      · simpa only [search,if_neg zero] using tailStore

end Counting.StackMachine.GaussianPivot
