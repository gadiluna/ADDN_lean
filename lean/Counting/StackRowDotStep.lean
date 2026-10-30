import Counting.StackRowAddStep
import Counting.StackRationalCall
import Counting.RowDotHeight

namespace Counting.StackMachine.RowDot
open Routine RowAdd

/-- The row bank is reused, with register 2 holding the canonical scalar
accumulator and registers 8/9 holding the product and next accumulator. -/
def productRoles : Fin 24 ↪ Fin 36 := ⟨![4,5,8,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29],by decide⟩
def sumRoles : Fin 26 ↪ Fin 36 := ⟨![2,8,9,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],by decide⟩
abbrev multiplyItems : Routine 34 := relocate RationalCall.multiplication productRoles
abbrev accumulate : Routine 34 := relocate RationalAddCall.addition sumRoles
abbrev cleanup : Routine 34 := sequence (clear 4) (sequence (clear 5)
  (sequence (clear 8) (sequence (clear 2) (move 33 9 2 7))))
abbrev body : Routine 34 := sequence RowAdd.readLeft (sequence RowAdd.readRight
  (sequence multiplyItems (sequence accumulate cleanup)))

theorem multiplyItems_executes (first second : Rat) (left right accumulator counter header status : List Bool) :
    ∃ time ≤ 90000000*((Encoding.rational.encode first).length+(Encoding.rational.encode second).length+1)^3,
      Executes multiplyItems
        (file left right accumulator counter (Encoding.rational.encode first) (Encoding.rational.encode second) [] [] header status []) time
        (file left right accumulator counter (Encoding.rational.encode first) (Encoding.rational.encode second)
          (Encoding.rational.encode (first*second)) [] header status []) := by
  obtain ⟨time,bounded,ran⟩ := RationalCall.multiplication_rationals first second
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame RationalCall.multiplication productRoles _ _ _ _ time _ _ _ ran
  · funext r; fin_cases r <;> simp [file,RationalCall.file,productRoles]
  · intro r; fin_cases r <;> simp [file,RationalCall.file,productRoles]
  · intro r outside
    fin_cases r
    all_goals first | exact False.elim (outside 2 rfl) | simp [file]

theorem accumulate_executes (accumulator product : Rat) (left right counter first second header status : List Bool) :
    ∃ time ≤ 500000000*((Encoding.rational.encode accumulator).length+(Encoding.rational.encode product).length+1)^3,
      Executes accumulate
        (file left right (Encoding.rational.encode accumulator) counter first second (Encoding.rational.encode product) [] header status []) time
        (file left right (Encoding.rational.encode accumulator) counter first second (Encoding.rational.encode product)
          (Encoding.rational.encode (accumulator+product)) header status []) := by
  obtain ⟨time,bounded,ran⟩ := RationalAddCall.addition_rationals accumulator product
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame RationalAddCall.addition sumRoles _ _ _ _ time _ _ _ ran
  · funext r; fin_cases r <;> simp [file,RationalAddCall.file,sumRoles]
  · intro r; fin_cases r <;> simp [file,RationalAddCall.file,sumRoles]
  · intro r outside
    fin_cases r
    all_goals first | exact False.elim (outside 2 rfl) | simp [file]

theorem cleanup_executes (left right accumulator counter first second product next header status : List Bool) :
    Executes cleanup (file left right accumulator counter first second product next header status [])
      (first.length+second.length+product.length+accumulator.length+6*next.length+12)
      (file left right next counter [] [] [] [] header status []) := by
  have clearedfirst := clear_executes (registers:=34) 4 (file left right accumulator counter first second product next header status [])
  have storefirst : Function.update (file left right accumulator counter first second product next header status []) 4 [] = (file left right accumulator counter [] second product next header status []) := by
    funext r; fin_cases r <;> simp [file]
  change Executes (clear 4) _ (first.length+1) (Function.update (file left right accumulator counter first second product next header status []) 4 []) at clearedfirst
  rw [storefirst] at clearedfirst
  have clearedsecond := clear_executes (registers:=34) 5 (file left right accumulator counter [] second product next header status [])
  have storesecond : Function.update (file left right accumulator counter [] second product next header status []) 5 [] = (file left right accumulator counter [] [] product next header status []) := by
    funext r; fin_cases r <;> simp [file]
  change Executes (clear 5) _ (second.length+1) (Function.update (file left right accumulator counter [] second product next header status []) 5 []) at clearedsecond
  rw [storesecond] at clearedsecond
  have clearedproduct := clear_executes (registers:=34) 8 (file left right accumulator counter [] [] product next header status [])
  have storeproduct : Function.update (file left right accumulator counter [] [] product next header status []) 8 [] = (file left right accumulator counter [] [] [] next header status []) := by
    funext r; fin_cases r <;> simp [file]
  change Executes (clear 8) _ (product.length+1) (Function.update (file left right accumulator counter [] [] product next header status []) 8 []) at clearedproduct
  rw [storeproduct] at clearedproduct
  have clearedaccumulator := clear_executes (registers:=34) 2 (file left right accumulator counter [] [] [] next header status [])
  have storeaccumulator : Function.update (file left right accumulator counter [] [] [] next header status []) 2 [] = (file left right [] counter [] [] [] next header status []) := by
    funext r; fin_cases r <;> simp [file]
  change Executes (clear 2) _ (accumulator.length+1) (Function.update (file left right accumulator counter [] [] [] next header status []) 2 []) at clearedaccumulator
  rw [storeaccumulator] at clearedaccumulator
  have moved := move_executes 33 9 2 7 (by decide) (by decide) (by decide) (file left right [] counter [] [] [] next header status []) rfl
  have movedStore : Function.update (Function.update (file left right [] counter [] [] [] next header status []) 2 (next++[])) 9 [] = (file left right next counter [] [] [] [] header status []) := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (6*next.length+4)
    (Function.update (Function.update (file left right [] counter [] [] [] next header status []) 2 (next++[])) 9 []) at moved
  rw [movedStore] at moved
  convert clearedfirst.sequence (clearedsecond.sequence (clearedproduct.sequence (clearedaccumulator.sequence moved))) using 1
  omega

def bodyCost (accumulator first second : Rat) : Nat :=
  let a := (Encoding.rational.encode first).length
  let b := (Encoding.rational.encode second).length
  let old := (Encoding.rational.encode accumulator).length
  let product := (Encoding.rational.encode (first*second)).length
  let next := (Encoding.rational.encode (accumulator+first*second)).length
  90000000*(a+b+1)^3+500000000*(old+product+1)^3+6*a+6*b+product+old+6*next+20

/-- Every scalar operation is a finite stack program. The returned bound
charges parsing, multiplication, addition, deletion, and accumulator transfer. -/
theorem body_executes (accumulator first second : Rat) (leftSuffix rightSuffix counter header status : List Bool) :
    ∃ time ≤ bodyCost accumulator first second,
      Executes body
        (file (Encoding.frame (Encoding.rational.encode first)++leftSuffix)
          (Encoding.frame (Encoding.rational.encode second)++rightSuffix)
          (Encoding.rational.encode accumulator) counter [] [] [] [] header status []) time
        (file leftSuffix rightSuffix (Encoding.rational.encode (accumulator+first*second))
          counter [] [] [] [] header status []) := by
  have parsedLeft := RowAdd.readLeft_executes (Encoding.rational.encode first) leftSuffix
    (Encoding.frame (Encoding.rational.encode second)++rightSuffix) (Encoding.rational.encode accumulator) counter header status
  have parsedRight := RowAdd.readRight_executes leftSuffix (Encoding.rational.encode second) rightSuffix
    (Encoding.rational.encode accumulator) counter (Encoding.rational.encode first) header status
  obtain ⟨mulTime,mulBound,multiplied⟩ := multiplyItems_executes first second leftSuffix rightSuffix
    (Encoding.rational.encode accumulator) counter header status
  obtain ⟨sumTime,sumBound,added⟩ := accumulate_executes accumulator (first*second) leftSuffix rightSuffix counter
    (Encoding.rational.encode first) (Encoding.rational.encode second) header status
  have cleaned := cleanup_executes leftSuffix rightSuffix (Encoding.rational.encode accumulator) counter
    (Encoding.rational.encode first) (Encoding.rational.encode second) (Encoding.rational.encode (first*second))
    (Encoding.rational.encode (accumulator+first*second)) header status
  refine ⟨_,?_,parsedLeft.sequence (parsedRight.sequence (multiplied.sequence (added.sequence cleaned)))⟩
  dsimp only [bodyCost]
  omega

end Counting.StackMachine.RowDot
