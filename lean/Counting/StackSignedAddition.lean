import Counting.StackSignedMagnitude

namespace Counting.StackMachine.Signed
open Routine Binary EncodingPrograms

theorem branch_bit {registers : Nat} (flag : Fin (registers+2))
    (yes no : Routine registers) (store result : Store registers) (bit : Bool) (time : Nat)
    (condition : store flag = [bit])
    (executed : Executes (if bit then yes else no) (Function.update store flag []) time result) :
    Executes (branchRoutine flag yes no) store (1+time) result := by
  cases bit
  · exact branch_executes_false flag yes no store result [] time condition executed
  · exact branch_executes_true flag yes no store result [] time condition executed

abbrev signedSum (sign : Bool) : Routine 10 := sequence sumPart (pushBit 10 sign)
abbrev signedDifference (reverse sign : Bool) : Routine 10 :=
  sequence (differencePart reverse) (pushBit 10 sign)
abbrev mixed (firstSign secondSign : Bool) : Routine 10 :=
  sequence comparePart (branchRoutine 11 (signedDifference true secondSign) (signedDifference false firstSign))

def signCase (firstSign secondSign : Bool) : Routine 10 :=
  if firstSign = secondSign then signedSum firstSign else mixed firstSign secondSign

abbrev dispatch (firstSign : Bool) : Routine 10 :=
  branchRoutine 9 (signCase firstSign true) (signCase firstSign false)

abbrev additionRoutine : Routine 10 := branchRoutine 8 (dispatch true) (dispatch false)

theorem mixed_executes (firstSign secondSign : Bool) (input first second : List Bool) :
    ∃ time ≤ 12*(first.length+second.length)+17,
      Executes (mixed firstSign secondSign) (file input first second [] [] [] [] [] []) time
        (file input [] [] [] []
          (if compareBits true first second then (subtractBits false second first).1 else (subtractBits false first second).1)
          [if compareBits true first second then secondSign else firstSign] [] []) := by
  have compared := compare_executes input first second
  have reset : Function.update
      (file input first second [] [] [] [] [] [compareBits true first second]) 11 [] =
      file input first second [] [] [] [] [] [] := by
    funext r; fin_cases r <;> rfl
  have selected : Executes
      (if compareBits true first second then signedDifference true secondSign else signedDifference false firstSign)
      (file input first second [] [] [] [] [] []) (5*max first.length second.length+6)
      (file input [] [] [] []
        (if compareBits true first second then (subtractBits false second first).1 else (subtractBits false first second).1)
        [if compareBits true first second then secondSign else firstSign] [] []) := by
    cases ordered : compareBits true first second with
    | false =>
        simpa only [Bool.false_eq_true,ite_false,show 5*max first.length second.length+4+1+1 = 5*max first.length second.length+6 by omega] using
          (difference_executes false input first second).sequence
            (sign_executes firstSign input (subtractBits false first second).1)
    | true =>
        simpa only [ite_true,show 5*max first.length second.length+4+1+1 = 5*max first.length second.length+6 by omega] using
          (difference_executes true input first second).sequence
            (sign_executes secondSign input (subtractBits false second first).1)
  have branched := branch_bit 11 (signedDifference true secondSign) (signedDifference false firstSign)
    (file input first second [] [] [] [] [] [compareBits true first second]) _
    (compareBits true first second) _ rfl (by rw [reset]; exact selected)
  refine ⟨_,?_,compared.sequence branched⟩
  have compareBound := preservingCompareCost_le first second
  omega

theorem signCase_executes (firstSign secondSign : Bool) (input first second : List Bool) :
    ∃ time ≤ 12*(first.length+second.length)+17,
      Executes (signCase firstSign secondSign) (file input first second [] [] [] [] [] []) time
        (file input [] [] [] [] (addBits firstSign secondSign first second).2
          [(addBits firstSign secondSign first second).1] [] []) := by
  by_cases same : firstSign = secondSign
  · obtain ⟨time,bounded,executed⟩ := sum_executes input first second
    have emitted := sign_executes firstSign input (Arithmetic.addBits false first second)
    refine ⟨time+1+1,?_,?_⟩
    · omega
    · simpa only [signCase,if_pos same,addBits] using executed.sequence emitted
  · obtain ⟨time,bounded,executed⟩ := mixed_executes firstSign secondSign input first second
    refine ⟨time,bounded,?_⟩
    simp only [signCase,if_neg same,addBits] at executed ⊢
    cases compared : compareBits true first second <;> simpa only [compared,Bool.false_eq_true,ite_false,ite_true] using executed

/-- A complete finite sign dispatch. Both signs and magnitudes are consumed,
all temporary registers are restored empty, and the input suffix is preserved.
The bound is linear in operand bit lengths, including mixed-sign cancellation. -/
theorem addition_executes (firstSign secondSign : Bool) (input first second : List Bool) :
    ∃ time ≤ 12*(first.length+second.length)+19,
      Executes additionRoutine (file input first second [firstSign] [secondSign] [] [] [] []) time
        (file input [] [] [] [] (addBits firstSign secondSign first second).2
          [(addBits firstSign secondSign first second).1] [] []) := by
  obtain ⟨time,bounded,executed⟩ := signCase_executes firstSign secondSign input first second
  have secondReset : Function.update (file input first second [] [secondSign] [] [] [] []) 9 [] =
      file input first second [] [] [] [] [] [] := by
    funext r; fin_cases r <;> rfl
  have firstReset : Function.update (file input first second [firstSign] [secondSign] [] [] [] []) 8 [] =
      file input first second [] [secondSign] [] [] [] [] := by
    funext r; fin_cases r <;> rfl
  have secondDispatch := branch_bit 9 (signCase firstSign true) (signCase firstSign false)
    (file input first second [] [secondSign] [] [] [] [])
    (file input [] [] [] [] (addBits firstSign secondSign first second).2
      [(addBits firstSign secondSign first second).1] [] []) secondSign time rfl
    (by rw [secondReset]; cases secondSign <;> exact executed)
  have firstDispatch := branch_bit 8 (dispatch true) (dispatch false)
    (file input first second [firstSign] [secondSign] [] [] [] [])
    (file input [] [] [] [] (addBits firstSign secondSign first second).2
      [(addBits firstSign secondSign first second).1] [] []) firstSign (1+time) rfl
    (by rw [firstReset]; cases firstSign <;> exact secondDispatch)
  exact ⟨1+(1+time),by omega,firstDispatch⟩

end Counting.StackMachine.Signed
