import Counting.StackAuditCandidateCheck

namespace Counting.StackMachine.AuditCandidate
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def inputWord (values : Option (Array Rat)) (candidate : Nat) : List Bool :=
  Encoding.natural.encode candidate++AuditPositive.inputWord values

def result (values : Option (Array Rat)) (candidate : Nat) : Option (Array Nat) := do
  let natural←AuditPositive.result values
  if natural.toList.sum==candidate then some natural else none

def outputWord (values : Option (Array Rat)) (candidate : Nat) : List Bool :=
  (Encoding.optional (Encoding.array Encoding.natural)).encode (result values candidate)

def checkedResult (natural : Option (Array Nat)) (candidate : Nat) : Option (Array Nat) := do
  let values←natural
  if AuditSum.accepts values.toList candidate then some values else none

abbrev handle : Routine 34 := branchRoutine 1 checkValues (pushBit 1 false)
abbrev complete : Routine 34 := sequence (ofProgram (unframeProgram 33 0 32 35))
  (sequence convertPositive (sequence handle (clear 32)))

private theorem checked_conversion (values : Option (Array Rat)) (candidate : Nat) :
    checkedResult (AuditPositive.result values) candidate=result values candidate := by
  cases values with
  | none => rfl
  | some values =>
    cases converted : Executable.positiveNaturals? values with
    | none => simp [checkedResult,AuditPositive.result,result,converted]
    | some natural =>
      simp only [checkedResult,AuditPositive.result,result,bind,Option.bind_some,converted]
      rw [AuditSum.accepts_after_conversion values natural converted]
      rfl

theorem handle_executes (natural : Option (Array Nat)) (candidate : Nat) :
    ∃ time ≤ 4001*(((Encoding.optional (Encoding.array Encoding.natural)).encode natural).length+candidate.size+1)^3,
      Executes handle (file [] ((Encoding.optional (Encoding.array Encoding.natural)).encode natural) candidate.bits []) time
        (file [] ((Encoding.optional (Encoding.array Encoding.natural)).encode (checkedResult natural candidate)) candidate.bits []) := by
  cases natural with
  | none =>
    have body := pushBit_executes (1:Fin 36) false (file [] [] candidate.bits [])
    have final : Function.update (file [] [] candidate.bits []) 1 [false]=file [] [false] candidate.bits [] := by
      funext r;fin_cases r <;> simp [file]
    change Executes _ _ 1 (Function.update (file [] [] candidate.bits []) 1 [false]) at body
    rw [final] at body
    have popped : Function.update (file [] [false] candidate.bits []) 1 []=file [] [] candidate.bits [] := by
      funext r;fin_cases r <;> simp [file]
    have ran := branch_executes_false (1:Fin 36) checkValues (pushBit 1 false)
      (file [] [false] candidate.bits []) _ [] 1 rfl (by rw [popped];exact body)
    refine ⟨2,?_,ran⟩
    change 2 ≤ 4001*([false].length+candidate.size+1)^3
    have one : 1 ≤ ([false].length+candidate.size+1)^3 := Nat.one_le_pow _ _ (by simp)
    omega
  | some natural =>
    let word := (Encoding.array Encoding.natural).encode natural
    obtain ⟨time,bounded,body⟩ := checkValues_executes natural candidate
    have popped : Function.update (file [] (true::word) candidate.bits []) 1 word=file [] word candidate.bits [] := by
      funext r;fin_cases r <;> simp [file]
    have ran := branch_executes_true (1:Fin 36) checkValues (pushBit 1 false)
      (file [] (true::word) candidate.bits []) _ word time rfl (by rw [popped];exact body)
    refine ⟨1+time,?_,ran⟩
    let size := (true::word).length+candidate.size+1
    have raised : (word.length+candidate.size+1)^3 ≤ size^3 :=
      Nat.pow_le_pow_left (by dsimp only [size];simp only [List.length_cons];omega) 3
    have one : 1 ≤ size^3 := Nat.one_le_pow _ _ (by dsimp only [size];omega)
    change time ≤ 4000*(word.length+candidate.size+1)^3 at bounded
    change 1+time ≤ 4001*size^3
    omega

theorem complete_executes (values : Option (Array Rat)) (candidate : Nat) :
    ∃ time ≤ 500000*((inputWord values candidate).length+1)^3,
      Executes complete (inputStore 34 (inputWord values candidate)) time
        (outputStore 34 (outputWord values candidate)) := by
  let raw := AuditPositive.inputWord values
  let converted := AuditPositive.outputWord values
  let start := file (inputWord values candidate) [] [] []
  have a := unframe_canonical_executes 33 (0:Fin 36) 32 35 (by decide) (by decide) (by decide)
    start candidate.bits raw rfl rfl
  have as' : Function.update (Function.update start 0 raw) 32 (candidate.bits++start 32)=
      file raw [] candidate.bits [] := by funext r;fin_cases r <;> simp [start,file]
  rw [as'] at a
  obtain ⟨convertTime,convertBound,b⟩ := convertPositive_executes values candidate.bits
  obtain ⟨handleTime,handleBound,c⟩ := handle_executes (AuditPositive.result values) candidate
  rw [checked_conversion] at c
  have d := clear_executes (32:Fin 36) (file [] (outputWord values candidate) candidate.bits [])
  have ds : Function.update (file [] (outputWord values candidate) candidate.bits []) 32 []=
      outputStore 34 (outputWord values candidate) := by
    funext r;fin_cases r <;> simp [file,outputStore]
  change Executes _ _ (candidate.bits.length+1) _ at d
  rw [ds] at d
  have combined := a.sequence (b.sequence (c.sequence d))
  have first : start=inputStore 34 (inputWord values candidate) := by
    funext r;fin_cases r <;> simp [start,file,inputStore]
  rw [first] at combined
  refine ⟨_,?_,combined⟩
  have length : (inputWord values candidate).length=2*candidate.size+1+raw.length := by
    simp only [inputWord,List.length_append,Encoding.natural_length,raw]
  have convertedLength := AuditPositive.output_length values
  change converted.length ≤ raw.length+1 at convertedLength
  let size := (inputWord values candidate).length+1
  have rawBase : raw.length+1 ≤ size := by dsimp only [size];omega
  have handleBase : converted.length+candidate.size+1 ≤ size := by dsimp only [size];omega
  have convertLimit := convertBound.trans (Nat.mul_le_mul_left 400000 (Nat.pow_le_pow_left rawBase 3))
  have handleLimit := handleBound.trans (Nat.mul_le_mul_left 4001 (Nat.pow_le_pow_left handleBase 3))
  have linear : size ≤ size^3 := Nat.le_self_pow (by decide) _
  have candidateSize : candidate.size ≤ size := by dsimp only [size];omega
  have one : 1 ≤ size^3 := Nat.one_le_pow _ _ (by dsimp only [size];omega)
  simp only [Encoding.bits_length]
  change _ ≤ 500000*size^3
  omega

theorem complete_halts (values : Option (Array Rat)) (candidate : Nat) :
    ∃ time last,time ≤ 500000*((inputWord values candidate).length+1)^3 ∧
      HaltsAt complete.program (inputWord values candidate) time last ∧
      last.store 1=outputWord values candidate := by
  obtain ⟨time,bounded,last,ran,halted,stored⟩ := complete_executes values candidate
  exact ⟨time,last,bounded,⟨ran,halted⟩,by rw [stored];rfl⟩

/-- Every rejection produced by the concrete three checks is an early
rejection by the actual executable audit. -/
theorem failed_candidate_rejects (vista : Executable.Vista) (candidate last anchor : Nat)
    (values : Option (Array Rat)) (failure : result values candidate=none) :
    Executable.auditSuffix? vista candidate last anchor values=none := by
  cases values with
  | none => rfl
  | some values =>
    cases converted : Executable.positiveNaturals? values with
    | none => simp [Executable.auditSuffix?,converted]
    | some natural =>
      have different : natural.sum≠candidate := by
        simpa [result,AuditPositive.result,converted] using failure
      simp [Executable.auditSuffix?,converted,different]

end Counting.StackMachine.AuditCandidate
