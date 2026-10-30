import Counting.StackSignedAddition
import Counting.StackEncodingRoutineInterfaces

namespace Counting.StackMachine.Signed
open Routine EncodingPrograms

set_option backward.isDefEq.respectTransparency false

abbrev readSign {registers : Nat} (source target : Fin (registers+2)) : Routine registers :=
  branchRoutine source (pushBit target true) (pushBit target false)

theorem readSign_executes {registers : Nat} (source target : Fin (registers+2))
    (distinct : source ≠ target) (store : Store registers) :
    Executes (readSign source target) store 2
      (Function.update (Function.update store source (store source).tail) target
        ((store source).headD false::store target)) := by
  have preserved : (Function.update store source (store source).tail) target = store target := by
    simp [Function.update_of_ne distinct.symm]
  have pushed (bit : Bool) := pushBit_executes target bit (Function.update store source (store source).tail)
  simp only [preserved] at pushed
  cases contents : store source with
  | nil =>
      have restored : Function.update store source (store source).tail = store := by
        simp only [contents,List.tail_nil]
        rw [← contents,Function.update_eq_self]
      have restoredEmpty : Function.update store source [] = store := by rw [← contents,Function.update_eq_self]
      simp only [List.tail_nil,restoredEmpty,List.headD_nil]
      exact
        branch_executes_empty source (pushBit target true) (pushBit target false) store
          (Function.update store target (false::store target)) 1 contents
          (by simpa only [restored] using pushed false)
  | cons bit rest =>
      cases bit
      · simpa only [List.tail_cons,List.headD_cons,contents] using
          branch_executes_false source (pushBit target true) (pushBit target false) store _ rest 1 contents
            (by simpa only [contents,List.tail_cons] using pushed false)
      · simpa only [List.tail_cons,List.headD_cons,contents] using
          branch_executes_true source (pushBit target true) (pushBit target false) store _ rest 1 contents
            (by simpa only [contents,List.tail_cons] using pushed true)

def readRoles (second : Bool) : Fin 5 ↪ Fin 12 where
  toFun := if second then ![0,3,9,7,11] else ![0,2,8,7,11]
  inj' := by cases second <;> decide

abbrev readMagnitude (second : Bool) : Routine 10 := sequence
  (ofProgram (flaggedProgram 8 0 ((readRoles second) 1) 7 11)) (clear 11)

abbrev readOperand (second : Bool) : Routine 10 :=
  sequence (readSign 0 ((readRoles second) 2)) (readMagnitude second)

def operandSign (input : List Bool) : Bool := input.headD false
def operandMagnitude (input : List Bool) : List Bool := unframePayload input.tail
def operandSuffix (input : List Bool) : List Bool := unframeSuffix input.tail

def operandResult (second : Bool) (store : Fin 12 → List Bool) : Fin 12 → List Bool :=
  Function.update
    (Function.update (Function.update store ((readRoles second) 2)
      (operandSign (store 0)::store ((readRoles second) 2))) 0 (operandSuffix (store 0)))
    ((readRoles second) 1) (operandMagnitude (store 0)++store ((readRoles second) 1))

theorem readOperand_executes (second : Bool) (store : Fin 12 → List Bool)
    (temp : store 7 = []) (flag : store 11 = []) :
    ∃ time ≤ 3*(store 0).length+10,
      Executes (readOperand second) store time (operandResult second store) := by
  have distinct (i j : Fin 5) (different : i ≠ j) : readRoles second i ≠ readRoles second j :=
    fun equal => different ((readRoles second).injective equal)
  have source : readRoles second 0 = 0 := by cases second <;> rfl
  have scratch : readRoles second 3 = 7 := by cases second <;> rfl
  have flagIndex : readRoles second 4 = 11 := by cases second <;> rfl
  have sourceSign : (0:Fin 12) ≠ readRoles second 2 := by rw [← source]; exact distinct 0 2 (by decide)
  let signed := Function.update (Function.update store 0 (store 0).tail) (readRoles second 2)
    ((store 0).headD false::store (readRoles second 2))
  have signRead := readSign_executes 0 (readRoles second 2) sourceSign store
  change Executes (readSign 0 (readRoles second 2)) store 2 signed at signRead
  have signedAt (r : Fin 12) (r0 : r ≠ 0) (rs : r ≠ readRoles second 2) : signed r = store r := by
    simp [signed,Function.update_of_ne,r0,rs]
  have signedSource : signed 0 = (store 0).tail := by simp [signed,sourceSign]
  have signedTemp : signed 7 = [] := by
    rw [signedAt 7 (by decide) (by rw [← scratch]; exact distinct 3 2 (by decide)),temp]
  have signedFlag : signed 11 = [] := by
    rw [signedAt 11 (by decide) (by rw [← flagIndex]; exact distinct 4 2 (by decide)),flag]
  have target0 : (0:Fin 12) ≠ readRoles second 1 := by rw [← source]; exact distinct 0 1 (by decide)
  have targetTemp : readRoles second 1 ≠ 7 := by rw [← scratch]; exact distinct 1 3 (by decide)
  have flagTarget : (11:Fin 12) ≠ readRoles second 1 := by rw [← flagIndex]; exact distinct 4 1 (by decide)
  obtain ⟨parseTime,parseBound,parsed⟩ := flagged_executes 8 0 (readRoles second 1) 7 11
    target0 (by decide) targetTemp (by decide) flagTarget (by decide) signed signedTemp
  rw [flagged_result_updates 8 0 (readRoles second 1) 7 11 target0 (by decide) targetTemp
    (by decide) flagTarget (by decide) signed signedTemp,signedSource,signedFlag] at parsed
  let middle := Function.update (Function.update signed 0 (unframeSuffix (store 0).tail))
    (readRoles second 1) (unframePayload (store 0).tail++signed (readRoles second 1))
  change Executes (ofProgram (flaggedProgram 8 0 (readRoles second 1) 7 11)) signed parseTime
    (Function.update middle 11 [(Encoding.unframe (store 0).tail).isSome]) at parsed
  have cleared := clear_executes (registers := 10) 11
    (Function.update middle 11 [(Encoding.unframe (store 0).tail).isSome])
  simp only [Function.update_self,List.length_cons,List.length_nil,Function.update_idem] at cleared
  have middleFlag : middle 11 = [] := by
    simp only [middle,Function.update_of_ne flagTarget,Function.update_of_ne (by decide : (11:Fin 12) ≠ 0),signedFlag]
  have final : Function.update middle 11 [] = operandResult second store := by
    rw [← middleFlag,Function.update_eq_self]
    have targetSign := distinct 1 2 (by decide)
    have targetSource := target0.symm
    dsimp only [middle,operandResult,operandSign,operandSuffix,operandMagnitude]
    rw [signedAt (readRoles second 1) targetSource targetSign]
    funext r
    by_cases isSource : r = 0
    · subst r; simp [signed,target0]
    · by_cases isSign : r = readRoles second 2
      · subst r; simp [signed,sourceSign.symm,targetSign.symm]
      · simp [signed,Function.update,isSource,isSign]
  rw [final] at cleared
  refine ⟨_,?_,signRead.sequence (parsed.sequence cleared)⟩
  rw [signedSource] at parseBound
  have smaller : (store 0).tail.length ≤ (store 0).length := by simp
  omega

theorem operand_length (input : List Bool) :
    (operandMagnitude input).length+(operandSuffix input).length ≤ input.length := by
  cases parsed : Encoding.unframe input.tail with
  | none => simp [operandMagnitude,operandSuffix,unframePayload,unframeSuffix,parsed]
  | some pair =>
      obtain ⟨payload,suffix⟩ := pair
      have split := Machine.unframe_sound input.tail payload suffix parsed
      have length := congrArg List.length split
      simp only [List.length_append,Encoding.frame_length] at length
      have tail : input.tail.length ≤ input.length := by simp
      simp only [operandMagnitude,operandSuffix,unframePayload,unframeSuffix,parsed,Option.map_some,Option.getD_some]
      omega

end Counting.StackMachine.Signed
