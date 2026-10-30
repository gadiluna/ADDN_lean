import Counting.StackRealizabilityInputSyntax
import Counting.StackRealizabilityInputSplit

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def verifierBootstrap : Routine 98 := sequence (ofProgram (ListPrograms.copyProgram 97 0 79 2))
  (sequence (ofProgram (ListPrograms.reverseProgram 98 0 2))
    (ofProgram (ListPrograms.reverseProgram 98 2 70)))

/-- The syntax pass receives a real copy of the input; its backup is
charged and retained only until the canonicality decision has been made. -/
theorem verifierBootstrap_executes (input : List Bool) :
    Executes verifierBootstrap (inputStore 98 input) (9*input.length+6) (inputSyntaxStart input) := by
  let start := inputStore 98 input
  have r0 := copy_executes 97 (0:Fin 100) 79 2 (by decide) (by decide) (by decide)
    start (by simp [start,inputStore])
  simp only [start,inputStore,ite_true,show (79:Fin 100)≠0 by decide,ite_false,List.append_nil] at r0
  let s1 := Function.update start 79 input
  have r1 := reverse_executes 98 (0:Fin 100) 2 (by decide) s1
  have a : s1 0=input := by simp [s1,start,inputStore]
  have b : s1 2=[] := by simp [s1,start,inputStore]
  rw [a,b,List.append_nil] at r1
  let s2 := Function.update (Function.update s1 0 []) 2 input.reverse
  have r2 := reverse_executes 98 (2:Fin 100) 70 (by decide) s2
  have c : s2 2=input.reverse := by simp [s2]
  have d : s2 70=[] := by simp [s2,s1,start,inputStore]
  rw [c,d,List.reverse_reverse,List.append_nil,List.length_reverse] at r2
  have final : Function.update (Function.update s2 2 []) 70 input=inputSyntaxStart input := by
    funext i
    by_cases a:i=0 <;> by_cases b:i=2 <;> by_cases c:i=70 <;> by_cases d:i=79 <;>
      simp_all [s2,s1,start,inputStore,inputSyntaxStart,inputSyntaxStore]
  rw [final] at r2
  have combined : Executes verifierBootstrap (inputStore 98 input)
      (5*input.length+2+1+(2*input.length+1+1+(2*input.length+1))) (inputSyntaxStart input) :=
    r0.sequence (r1.sequence r2)
  simpa only [show 5*input.length+2+1+(2*input.length+1+1+(2*input.length+1))=9*input.length+6 by omega] using combined

def inputRecover : Routine 98 := sequence (ofProgram (ListPrograms.reverseProgram 98 79 0))
  (ofProgram (ListPrograms.reverseProgram 98 0 70))

theorem inputRecover_executes (input : List Bool) :
    Executes inputRecover (inputSyntaxStore input [true]) (4*input.length+3)
      (inputSplitStore input [true]) := by
  let start := inputSyntaxStore input [true]
  have r0 := reverse_executes 98 (79:Fin 100) 0 (by decide) start
  have a : start 79=input := by simp [start,inputSyntaxStore]
  have b : start 0=[] := by simp [start,inputSyntaxStore]
  rw [a,b,List.append_nil] at r0
  let s1 := Function.update (Function.update start 79 []) 0 input.reverse
  have r1 := reverse_executes 98 (0:Fin 100) 70 (by decide) s1
  have c : s1 0=input.reverse := by simp [s1]
  have d : s1 70=[] := by simp [s1,start,inputSyntaxStore]
  rw [c,d,List.reverse_reverse,List.append_nil,List.length_reverse] at r1
  have final : Function.update (Function.update s1 0 []) 70 input=inputSplitStore input [true] := by
    funext i
    by_cases a:i=0 <;> by_cases b:i=79 <;> by_cases c:i=70 <;>
      simp_all [s1,start,inputSyntaxStore,inputSplitStore]
  rw [final] at r1
  have combined : Executes inputRecover (inputSyntaxStore input [true])
      (2*input.length+1+1+(2*input.length+1)) (inputSplitStore input [true]) := r0.sequence r1
  simpa only [show 2*input.length+1+1+(2*input.length+1)=4*input.length+3 by omega] using combined

end Counting.StackMachine.RealizabilityCheck
