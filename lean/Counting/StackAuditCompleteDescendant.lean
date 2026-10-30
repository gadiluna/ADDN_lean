import Counting.StackAuditCompleteOutput

namespace Counting.StackMachine.AuditComplete
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def descendantBudget (vista : Executable.Vista) (weights : Array Nat) (anchor last : Nat) : Nat :=
  40*((AuditDescendant.completeInputWord vista weights anchor last).length+1)+
  AuditDescendant.completeCoefficient*((AuditDescendant.completeInputWord vista weights anchor last).length+1)^7+
  41*(anchor.size+((Encoding.array Encoding.natural).encode weights).length+1)+2

abbrev descendantSuccess : Routine 62 := sequence descendantInput
  (sequence descendantCall finishDescendant)

theorem descendantSuccess_executes (vista : Executable.Vista) (leaders candidate last anchor : Nat)
    (weights : Array Nat) (fits:last≤ vista.nodes.size) :
    ∃ time≤ descendantBudget vista weights anchor last,
      Executes descendantSuccess
        (file [] ((Encoding.array Encoding.natural).encode weights)
          (metadata vista leaders candidate last anchor.bits [])) time
        (file [] (witnessWord (if Executable.auditDescendants vista weights anchor last then
            some ⟨anchor,weights⟩ else none))
          (metadata vista leaders candidate last anchor.bits ((Encoding.array Encoding.natural).encode weights))) := by
  obtain ⟨a,abound,arun⟩:=descendantInput_executes vista leaders candidate last anchor weights
  obtain ⟨b,bbound,brun⟩:=descendantCall_executes vista weights anchor last fits
    (metadata vista leaders candidate last anchor.bits ((Encoding.array Encoding.natural).encode weights))
  obtain ⟨c,cbound,crun⟩:=finishDescendant_executes vista leaders candidate last anchor weights
    (Executable.auditDescendants vista weights anchor last)
  exact ⟨_,by dsimp only [descendantBudget];omega,arun.sequence (brun.sequence crun)⟩

def optionalWeightsWord (weights : Option (Array Nat)) : List Bool :=
  weights.map (Encoding.array Encoding.natural).encode |>.getD []

def weightsBudget (vista : Executable.Vista) (anchor last : Nat) : Option (Array Nat) → Nat
  | none=>2
  | some weights=>1+descendantBudget vista weights anchor last

abbrev handleWeights : Routine 62 := branchRoutine 1 descendantSuccess (pushBit 1 false)

/-- Failure and success consume the real optional-array tag. The accepted
branch runs the complete descendant machine before serializing a witness. -/
theorem handleWeights_executes (vista : Executable.Vista) (leaders candidate last anchor : Nat)
    (weights : Option (Array Nat)) (fits:last≤ vista.nodes.size) :
    ∃ time≤ weightsBudget vista anchor last weights,
      Executes handleWeights
        (file [] ((Encoding.optional (Encoding.array Encoding.natural)).encode weights)
          (metadata vista leaders candidate last anchor.bits [])) time
        (file [] (witnessWord (weights.bind (fun values =>
          if Executable.auditDescendants vista values anchor last then some ⟨anchor,values⟩ else none)))
          (metadata vista leaders candidate last anchor.bits (optionalWeightsWord weights))) := by
  let saved:=metadata vista leaders candidate last anchor.bits []
  cases weights with
  | none =>
    have a:=pushBit_executes (1:Fin 64) false (file [] [] saved)
    have result : Function.update (file [] [] saved) 1 (false::file [] [] saved 1)=file [] [false] saved := by
      funext r;by_cases one:r=1 <;> simp [file,one]
    rw [result] at a
    have popped : Function.update (file [] [false] saved) 1 []=file [] [] saved := by
      funext r;by_cases one:r=1 <;> simp [file,one]
    have run:=branch_executes_false (1:Fin 64) descendantSuccess (pushBit 1 false)
      (file [] [false] saved) _ [] 1 (by simp [file]) (by rw [popped];exact a)
    exact ⟨2,by simp [weightsBudget],run⟩
  | some weights =>
    let word:=(Encoding.array Encoding.natural).encode weights
    obtain ⟨time,bounded,a⟩:=descendantSuccess_executes vista leaders candidate last anchor weights fits
    have popped : Function.update (file [] (true::word) saved) 1 word=file [] word saved := by
      funext r;by_cases one:r=1 <;> simp [file,one]
    have run:=branch_executes_true (1:Fin 64) descendantSuccess (pushBit 1 false)
      (file [] (true::word) saved) _ word time (by simp [file]) (by rw [popped];exact a)
    exact ⟨_,by dsimp only [weightsBudget];omega,run⟩

end Counting.StackMachine.AuditComplete
