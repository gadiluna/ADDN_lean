import Counting.StackScaleLength
import Counting.StackRoutineLists

namespace Counting.StackMachine.Routine

/-- Replace a register by a unary multiple of its length. Both scratch
registers are restored, and clearing/reversal transitions are charged. -/
def scaleInPlace (extra : Nat) (source temporary work : Fin (extra+3)) (scale : Nat) : Routine (extra+1) :=
  sequence (scaleLength extra source temporary work scale)
    (sequence (clear source) (ofProgram (ListPrograms.reverseProgram (extra+1) temporary source)))

theorem scaleInPlace_executes (extra : Nat) (source temporary work : Fin (extra+3)) (scale : Nat)
    (st : source ≠ temporary) (sw : source ≠ work) (tw : temporary ≠ work)
    (store : Fin (extra+3) → List Bool) (temporaryEmpty : store temporary=[]) (workEmpty : store work=[]) :
    Executes (scaleInPlace extra source temporary work scale) store
      (7*scale*(store source).length+3*scale+(store source).length+4)
      (Function.update store source (List.replicate (scale*(store source).length) true)) := by
  let filled := Function.update store temporary (List.replicate (scale*(store source).length) true)
  have scaled : Executes (scaleLength extra source temporary work scale) store
      (scale*(5*(store source).length+3)) filled := by
    simpa only [filled,temporaryEmpty,List.append_nil] using
      scaleLength_executes extra source temporary work st sw tw scale store workEmpty
  let emptied := Function.update filled source []
  have cleared : Executes (clear source) filled ((store source).length+1) emptied := by
    simpa only [filled,Function.update_of_ne st,emptied] using clear_executes source filled
  have reverse : Executes (ofProgram (ListPrograms.reverseProgram (extra+1) temporary source)) emptied
      (2*(scale*(store source).length)+1)
      (Function.update store source (List.replicate (scale*(store source).length) true)) := by
    have run := reverse_executes (extra+1) temporary source st.symm emptied
    have temp : emptied temporary=List.replicate (scale*(store source).length) true := by simp [emptied,filled,st.symm]
    have empty : emptied source=[] := by simp [emptied]
    have result : Function.update (Function.update emptied temporary []) source
        (List.replicate (scale*(store source).length) true)=
        Function.update store source (List.replicate (scale*(store source).length) true) := by
      funext r
      by_cases a : r=source
      · subst r; simp
      · by_cases b : r=temporary
        · subst r; simp [emptied,filled,a,temporaryEmpty]
        · simp [emptied,filled,a,b]
    simpa +instances only [ListPrograms.reverseProgram,temp,empty,List.length_replicate,
      List.reverse_replicate,List.append_nil,result] using run
  have combined := scaled.sequence (cleared.sequence reverse)
  have cost : scale*(5*(store source).length+3)+1+((store source).length+1+1+(2*(scale*(store source).length)+1))=
      7*scale*(store source).length+3*scale+(store source).length+4 := by ring
  simpa +instances only [scaleInPlace,cost,ListPrograms.reverseProgram] using combined

end Counting.StackMachine.Routine
