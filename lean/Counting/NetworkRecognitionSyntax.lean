import Counting.NetworkRecognitionParser
import Counting.StackRoutineClean
import Counting.StackRegisterFrames
import Counting.StackRoutineLists

namespace Counting.StackMachine.NetworkRecognition
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

def syntaxRoles : Fin 17 ↪ Fin 26 := ⟨fun r=>⟨r.val,by omega⟩,
  by intro a b equal;exact Fin.ext (congrArg (fun r:Fin 26=>r.val) equal)⟩

def syntaxStore (input:List Bool) (flag:Bool) : Store 24 :=
  fun r=>if r=17 then input else if r=1 then [flag] else []

def syntaxCheck : Routine 24 := sequence (ofProgram (ListPrograms.copyProgram 23 0 17 18))
  (relocate (isolate parser.recognition) syntaxRoles)

def syntaxCoefficient : Nat := 18*(parser.coefficient+24)+10
def syntaxExponent : Nat := max 1 parser.exponent

/-- Total canonical decoding with a physically preserved source word. The
recognizer's parser output and all private scratch are erased and charged. -/
theorem syntaxCheck_executes (input:List Bool) :
    ∃time ≤ Complexity.polynomial syntaxCoefficient syntaxExponent input.length,
      Executes syntaxCheck (inputStore 24 input) time
        (syntaxStore input (Encoding.networkInput.decodeExact input).isSome) := by
  let start:=inputStore 24 input
  have copying:=copy_executes 23 (0:Fin 26) 17 18 (by decide) (by decide) (by decide) start
    (by simp [start,inputStore])
  rw [show start 0=input by simp [start,inputStore],show start 17=[] by simp [start,inputStore],List.append_nil] at copying
  let copied:=Function.update start 17 input
  obtain ⟨time,bound,run⟩:=isolate_executes parser.recognition _ _ parser.recognition_computes input
  have checking:Executes (relocate (isolate parser.recognition) syntaxRoles) copied time
      (syntaxStore input (Encoding.networkInput.decodeExact input).isSome) := by
    apply relocate_executes_frame (isolate parser.recognition) syntaxRoles copied
      (syntaxStore input (Encoding.networkInput.decodeExact input).isSome)
      (inputStore 15 input) (outputStore 15 [(Encoding.networkInput.decodeExact input).isSome]) time
    · funext i;fin_cases i <;> simp [copied,start,inputStore,syntaxRoles]
    · intro i;fin_cases i <;> simp [syntaxStore,outputStore,syntaxRoles]
    · intro r outside
      have n0:r≠0:=by simpa [syntaxRoles] using (outside 0).symm
      have n1:r≠1:=by simpa [syntaxRoles] using (outside 1).symm
      by_cases n17:r=17 <;> simp [syntaxStore,copied,start,inputStore,n0,n1,n17]
    · exact run
  let B:=input.length+1
  have base:B=input.length+1:=rfl
  have linear:B≤B^syntaxExponent:=Nat.le_self_pow (by unfold syntaxExponent;omega) _
  have one:1≤B^syntaxExponent:=Nat.one_le_pow _ _ (by omega)
  change time≤18*((parser.coefficient+20)*B^syntaxExponent+input.length+3) at bound
  refine ⟨5*input.length+2+1+time,?_,copying.sequence checking⟩
  change _ ≤ syntaxCoefficient*B^syntaxExponent
  unfold syntaxCoefficient
  simp only [Nat.add_mul,Nat.mul_assoc] at bound ⊢
  omega

end Counting.StackMachine.NetworkRecognition
