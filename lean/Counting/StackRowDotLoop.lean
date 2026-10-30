import Counting.StackRowDotStep
import Counting.StackLoop

namespace Counting.StackMachine.RowDot
open Routine RowAdd GaussianBits

abbrev loop : Routine 34 := forEach 3 body

def stepBudget (height : Nat) : Nat := 1000000000*(8*height+10)^3

theorem bodyCost_height (accumulator first second : Rat) (height : Nat)
    (bounded : rationalHeight accumulator+rationalHeight first+rationalHeight second+3 ≤ height) :
    bodyCost accumulator first second ≤ stepBudget height := by
  have firstBound := encoded_le_rationalHeight first
  have secondBound := encoded_le_rationalHeight second
  have oldBound := encoded_le_rationalHeight accumulator
  have productHeight := rationalHeight_mul first second
  have productBound := encoded_le_rationalHeight (first*second)
  have nextHeight := rationalHeight_add accumulator (first*second)
  have nextBound := encoded_le_rationalHeight (accumulator+first*second)
  have firstPower := Nat.pow_le_pow_left (show (Encoding.rational.encode first).length+
    (Encoding.rational.encode second).length+1 ≤ 8*height+10 by omega) 3
  have secondPower := Nat.pow_le_pow_left (show (Encoding.rational.encode accumulator).length+
    (Encoding.rational.encode (first*second)).length+1 ≤ 8*height+10 by omega) 3
  have linear : 8*height+10 ≤ (8*height+10)^3 := by
    have square : 1 ≤ (8*height+10)^2 := by
      have bound := Nat.one_le_pow' 2 (8*height+9)
      convert bound using 1
    have multiplied := Nat.mul_le_mul_left (8*height+10) square
    nlinarith
  dsimp only [bodyCost,stepBudget]
  omega

/-- The counter is physically consumed, and each iteration parses two
framed coefficients and calls both verified scalar transducers. -/
theorem loop_executes (pairs : List (Rat×Rat)) (accumulator : Rat)
    (leftSuffix rightSuffix header status : List Bool) (height : Nat)
    (bounded : dotEnvelope pairs accumulator ≤ height) :
    ∃ time ≤ pairs.length*(stepBudget height+2)+1,
      Executes loop
        (file (Encoding.sequence (Encoding.framed Encoding.rational) (pairs.map Prod.fst)++leftSuffix)
          (Encoding.sequence (Encoding.framed Encoding.rational) (pairs.map Prod.snd)++rightSuffix)
          (Encoding.rational.encode accumulator) (List.replicate pairs.length true) [] [] [] [] header status []) time
        (file leftSuffix rightSuffix (Encoding.rational.encode (dotAcc pairs accumulator))
          [] [] [] [] [] header status []) := by
  induction pairs generalizing accumulator with
  | nil =>
    have ran := repeat_empty 3 body
      (file leftSuffix rightSuffix (Encoding.rational.encode accumulator) [] [] [] [] [] header status []) rfl
    exact ⟨1,by simp,⟨⟨1,_⟩,ran.1,ran.2,rfl⟩⟩
  | cons pair rest ih =>
    let first := Encoding.rational.encode pair.1
    let second := Encoding.rational.encode pair.2
    let left := Encoding.frame first++(Encoding.sequence (Encoding.framed Encoding.rational) (rest.map Prod.fst)++leftSuffix)
    let right := Encoding.frame second++(Encoding.sequence (Encoding.framed Encoding.rational) (rest.map Prod.snd)++rightSuffix)
    let count := List.replicate rest.length true
    let start := file left right (Encoding.rational.encode accumulator) (true::count) [] [] [] [] header status []
    have counterUpdate : Function.update start 3 count =
        file left right (Encoding.rational.encode accumulator) count [] [] [] [] header status [] := by
      funext r; fin_cases r <;> simp [start,file]
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩ := body_executes accumulator pair.1 pair.2
      (Encoding.sequence (Encoding.framed Encoding.rational) (rest.map Prod.fst)++leftSuffix)
      (Encoding.sequence (Encoding.framed Encoding.rational) (rest.map Prod.snd)++rightSuffix) count header status
    have firstRun := repeat_iteration 3 body start true count rfl bodyTime finishBody
      (by rw [counterUpdate]; exact bodyRun) bodyHalt
    change Machine.run (step loop.program) (bodyTime+2) ⟨0,start⟩ = some ⟨0,finishBody.store⟩ at firstRun
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩ := ih (accumulator+pair.1*pair.2)
      ((dotEnvelope_step pair rest accumulator).trans bounded)
    have currentBound := bodyCost_height accumulator pair.1 pair.2 height
      ((dotEnvelope_head pair rest accumulator).trans bounded)
    refine ⟨bodyTime+2+tailTime,?_,⟨finishTail,?_,?_ ,?_⟩⟩
    · simp only [List.length_cons]
      nlinarith
    · have combined := Machine.run_add (step loop.program) (bodyTime+2) tailTime ⟨0,start⟩
      rw [firstRun,Option.bind_some,bodyStore] at combined
      rw [tailRun] at combined
      simpa only [start,left,right,count,first,second,Encoding.sequence,Encoding.framed,
        List.map_cons,List.length_cons,List.replicate_succ,List.append_assoc] using combined
    · exact tailHalt
    · exact tailStore

end Counting.StackMachine.RowDot
