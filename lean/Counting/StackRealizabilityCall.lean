import Counting.StackRealizabilityCallInputs
import Counting.StackRealizabilityCallIsolated
import Counting.StackEncodingPair

namespace Counting.StackMachine.RealizabilityCall
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000

/-- External cells zero through three contain the four serialized fields;
cell four accumulates acceptance. All thirty external cells survive. -/
def check : Routine 128 := sequence copyInputs
  (sequence runVerifier (sequence (ofProgram (ListPrograms.reverseProgram 128 1 104))
    (ofProgram (combineFlagsProgram 128 104))))

def coefficient : Nat := 101*RealizabilityCheck.verifierCoefficient+500

theorem check_executes (data : Fin 30→List Bool) (accepted : Bool) (tail : List Bool)
    (status : data 4=accepted::tail) :
    ∃ time ≤ Complexity.polynomial coefficient 25 (encodedInput data).length,
      Executes check (file data) time
        (file (Function.update data 4 ((accepted && RealizabilityCheck.encodedVerifier (encodedInput data))::tail))) := by
  have copying := copyInputs_executes data
  obtain ⟨time,bound,verification⟩ := runVerifier_executes data (encodedInput data)
  let answer := RealizabilityCheck.encodedVerifier (encodedInput data)
  let verified := Function.update (file data) 1 [answer]
  have moving := reverse_executes 128 (1:Fin 130) 104 (by decide) verified
  have sourceAt : verified 1=[answer] := by simp [verified]
  have targetAt : verified 104=accepted::tail := by simpa [verified,file] using status
  rw [sourceAt,targetAt,List.length_singleton,List.reverse_singleton,List.singleton_append] at moving
  let appended := Function.update (file data) 104 (answer::accepted::tail)
  have moved : Function.update (Function.update verified 1 []) 104 (answer::accepted::tail)=appended := by
    funext i
    by_cases a:i=1 <;> by_cases b:i=104 <;> simp_all [verified,appended,file]
  rw [moved] at moving
  have joining := combineFlags_executes 128 (104:Fin 130) appended accepted answer tail (by simp [appended])
  have final : Function.update appended 104 ((accepted && answer)::tail)=
      file (Function.update data 4 ((accepted && answer)::tail)) := by
    simp only [appended,Function.update_idem]
    exact file_update data 4 _
  rw [final] at joining
  refine ⟨_,?_,copying.sequence (verification.sequence (moving.sequence joining))⟩
  let L := (encodedInput data).length
  let B := L+1
  change time ≤ 101*(RealizabilityCheck.verifierCoefficient*B^25+L+3) at bound
  have linear : B ≤ B^25 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ B^25 := Nat.one_le_pow _ _ (by dsimp only [B];omega)
  change 5*L+11+1+(time+1+(3+1+3)) ≤ (101*RealizabilityCheck.verifierCoefficient+500)*B^25
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc] at bound ⊢
  have base : B=L+1 := rfl
  omega

end Counting.StackMachine.RealizabilityCall
