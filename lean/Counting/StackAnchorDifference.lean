import Counting.StackSignedComplete
import Counting.StackRoutineClean
import Counting.StackRegisterFrames
import Counting.StackEncodingFrameStore
import Counting.StackRoutineMove

namespace Counting.StackMachine.AnchorDifference
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- Two binary natural operands are consumed; the canonical rational
difference is prepended to cell15. No rational denominators are expanded. -/
def file (first second input output result : List Bool) : Store 14 :=
  fun r=>if r=12 then first else if r=13 then second else if r=0 then input
    else if r=1 then output else if r=15 then result else []

def arguments (first second : List Bool) : List Bool :=
  false::(Encoding.frame first++true::Encoding.frame second)

abbrev prepare : Routine 14 := sequence (frameRoutine 13 13 0 14)
  (sequence (pushBit 0 true) (sequence (frameRoutine 13 12 0 14) (pushBit 0 false)))

def roles : Fin 12 ↪ Fin 16 := ⟨fun r=>⟨r.val,by have:=r.isLt;omega⟩,
  by intro a b same;exact Fin.ext (congrArg (fun r:Fin 16=>r.val) same)⟩
abbrev calculate : Routine 14 := relocate (isolate Signed.signedAdditionRoutine) roles
abbrev emit : Routine 14 := sequence (prepend 15 (Encoding.natural.encode 1)) (move 13 1 15 14)
abbrev difference : Routine 14 := sequence prepare (sequence calculate emit)

theorem prepare_executes (first second result : List Bool) :
    Executes prepare (file first second [] [] result) (5*first.length+5*second.length+13)
      (file [] [] (arguments first second) [] result) := by
  have framedSecond := frame_executes_updates 13 (13:Fin 16) 0 14 (by decide) (by decide) (by decide)
    (file first second [] [] result) rfl
  have secondStore : Function.update (Function.update (file first second [] [] result) 13 []) 0
      (Encoding.frame second++[])=file first [] (Encoding.frame second) [] result := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ (5*second.length+4)
    (Function.update (Function.update (file first second [] [] result) 13 []) 0 (Encoding.frame second++[])) at framedSecond
  rw [secondStore] at framedSecond
  have signedSecond := pushBit_executes (0:Fin 16) true (file first [] (Encoding.frame second) [] result)
  have signStore : Function.update (file first [] (Encoding.frame second) [] result) 0
      (true::Encoding.frame second)=file first [] (true::Encoding.frame second) [] result := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ 1 (Function.update (file first [] (Encoding.frame second) [] result) 0 (true::Encoding.frame second)) at signedSecond
  rw [signStore] at signedSecond
  have framedFirst := frame_executes_updates 13 (12:Fin 16) 0 14 (by decide) (by decide) (by decide)
    (file first [] (true::Encoding.frame second) [] result) rfl
  have firstStore : Function.update (Function.update (file first [] (true::Encoding.frame second) [] result) 12 []) 0
      (Encoding.frame first++true::Encoding.frame second)=
      file [] [] (Encoding.frame first++true::Encoding.frame second) [] result := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ (5*first.length+4)
    (Function.update (Function.update (file first [] (true::Encoding.frame second) [] result) 12 []) 0
      (Encoding.frame first++true::Encoding.frame second)) at framedFirst
  rw [firstStore] at framedFirst
  have signedFirst := pushBit_executes (0:Fin 16) false
    (file [] [] (Encoding.frame first++true::Encoding.frame second) [] result)
  have finalStore : Function.update (file [] [] (Encoding.frame first++true::Encoding.frame second) [] result) 0
      (arguments first second)=file [] [] (arguments first second) [] result := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ 1 (Function.update (file [] [] (Encoding.frame first++true::Encoding.frame second) [] result) 0
      (arguments first second)) at signedFirst
  rw [finalStore] at signedFirst
  have composed := framedSecond.sequence (signedSecond.sequence (framedFirst.sequence signedFirst))
  convert composed using 1
  omega

theorem calculate_executes (input result : List Bool) :
    ∃ time  ≤  13*(100*(input.length+1)+input.length+3),
      Executes calculate (file [] [] input [] result) time
        (file [] [] [] (Signed.signedAdditionFunction input) result) := by
  obtain ⟨time,bounded,ran⟩ := isolate_executes Signed.signedAdditionRoutine _ _ Signed.signedAddition_computes input
  refine ⟨time,by simpa only [Complexity.polynomial,pow_one] using bounded,?_⟩
  apply relocate_executes_frame (isolate Signed.signedAdditionRoutine) roles _ _ _ _ time _ _ _ ran
  · funext r;fin_cases r <;> simp [roles,file,inputStore]
  · intro r;fin_cases r <;> simp [roles,file,outputStore]
  · intro r outside
    have n0 : r≠0 := by intro same;subst r;exact outside 0 rfl
    have n1 : r≠1 := by intro same;subst r;exact outside 1 rfl
    simp [file,n0,n1]

theorem emit_executes (word result : List Bool) :
    Executes emit (file [] [] [] word result) (6*word.length+11)
      (file [] [] [] [] (word++Encoding.natural.encode 1++result)) := by
  have denominator := prepend_executes (15:Fin 16) (Encoding.natural.encode 1) (file [] [] [] word result)
  have denStore : Function.update (file [] [] [] word result) 15 (Encoding.natural.encode 1++result)=
      file [] [] [] word (Encoding.natural.encode 1++result) := by funext r;fin_cases r <;> simp [file]
  change Executes _ _ 6 (Function.update (file [] [] [] word result) 15 (Encoding.natural.encode 1++result)) at denominator
  rw [denStore] at denominator
  have moved := move_executes 13 (1:Fin 16) 15 14 (by decide) (by decide) (by decide)
    (file [] [] [] word (Encoding.natural.encode 1++result)) rfl
  have movedStore : Function.update (Function.update (file [] [] [] word (Encoding.natural.encode 1++result)) 15
      (word++(Encoding.natural.encode 1++result))) 1 []=
      file [] [] [] [] (word++Encoding.natural.encode 1++result) := by
    funext r;fin_cases r <;> simp [file,List.append_assoc]
  change Executes _ _ (6*word.length+4)
    (Function.update (Function.update (file [] [] [] word (Encoding.natural.encode 1++result)) 15
      (word++(Encoding.natural.encode 1++result))) 1 []) at moved
  rw [movedStore] at moved
  convert denominator.sequence moved using 1
  omega

theorem signed_arguments (first second : Nat) :
    Signed.signedAdditionFunction (arguments first.bits second.bits)=Encoding.integer.encode ((first:Int)-second) := by
  have last : Encoding.unframe (Encoding.frame second.bits)=some (second.bits,[]) := by
    simpa using Encoding.unframe_frame second.bits []
  simp [Signed.signedAdditionFunction,Signed.parsedFirst,Signed.parsedSecond,Signed.operandSign,
    Signed.operandMagnitude,Signed.operandSuffix,Signed.value,arguments,unframePayload,unframeSuffix,
    Encoding.value_bits,Encoding.signedValue,sub_eq_add_neg,last]

theorem rational_int_encode (value : Int) :
    Encoding.rational.encode (value:Rat)=Encoding.integer.encode value++Encoding.natural.encode 1 := by
  simp [Encoding.rational_encode]

theorem difference_executes (first second : Nat) (result : List Bool) :
    ∃ time  ≤  10000*(first.size+second.size+1),
      Executes difference (file first.bits second.bits [] [] result) time
        (file [] [] [] [] (Encoding.rational.encode ((first:Rat)-second)++result)) := by
  let input := arguments first.bits second.bits
  have before := prepare_executes first.bits second.bits result
  obtain ⟨time,bounded,ran⟩ := calculate_executes input result
  have output := emit_executes (Signed.signedAdditionFunction input) result
  have composed := before.sequence (ran.sequence output)
  have resultWord : Signed.signedAdditionFunction input++Encoding.natural.encode 1=
      Encoding.rational.encode ((first:Rat)-second) := by
    rw [signed_arguments,←rational_int_encode]
    simp
  rw [resultWord] at composed
  refine ⟨_,?_,composed⟩
  have outputBound := computed_length_le Signed.signedAdditionRoutine _ _ Signed.signedAddition_computes input
  have inputLength : input.length=2*first.size+2*second.size+4 := by
    simp [input,arguments,Encoding.frame_length,Encoding.bits_length];omega
  simp only [Complexity.polynomial,pow_one] at outputBound
  simp only [Encoding.bits_length]
  omega

end Counting.StackMachine.AnchorDifference
