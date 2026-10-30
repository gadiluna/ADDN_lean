import Counting.HardnessNetworkMachineGenerator
import Counting.ExternalCoverInputValidation

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def networkTransform (word : List Bool) : List Bool :=
  match X3CEncoding.codec.decodeExact word with
  | none=>[]
  | some input=>networkValue input

theorem networkTransform_encoded (input : X3CEncoding.Input) :
    networkTransform (X3CEncoding.codec.encode input)=networkValue input := by
  have decoded := (X3CEncoding.codec.decodeExact_iff _ input).mpr rfl
  simp only [networkTransform,decoded]

def acceptedNetworkContinuation : Routine 94 :=
  sequence (pushBit 1 true)
    (sequence (ofProgram (ListPrograms.copyProgram 93 51 0 63)) networkGenerator)

def rejectedNetworkContinuation : Routine 94 := prepend 1 []

theorem acceptedNetworkContinuation_executes (store : Store 94) (input : X3CEncoding.Input)
    (backup : store 51=X3CEncoding.codec.encode input) (source : store 0=[]) (status : store 1=[])
    (population : store 17=List.replicate (3*input.1) true) (count : store 25=List.replicate input.2.1 true)
    (empty : ∀ i∈initialNetworkScratch,store i=[]) :
    ∃ time ≤ networkGeneratorCost input+5*(X3CEncoding.codec.encode input).length+5,
      ∃ result,Executes acceptedNetworkContinuation store time result ∧ result 1=networkValue input := by
  have pushing:=pushBit_executes (1:Fin 96) true store
  rw [status] at pushing
  let flagged:=Function.update store 1 [true]
  have copying:=copy_executes 93 (51:Fin 96) 0 63 (by decide) (by decide) (by decide) flagged
    (by simp [flagged,empty])
  have backupAt : flagged 51=X3CEncoding.codec.encode input := by simp [flagged,backup]
  have sourceAt : flagged 0=[] := by simp [flagged,source]
  rw [backupAt,sourceAt,List.append_nil] at copying
  let restored:=Function.update flagged 0 (X3CEncoding.codec.encode input)
  have restoredEmpty (i : Fin 96) (member : i∈initialNetworkScratch) : restored i=[] := by
    have a : i≠0 := (mem_initialNetworkScratch i).mp member |>.1
    have b : i≠1 := (mem_initialNetworkScratch i).mp member |>.2.1
    simp [restored,flagged,a,b,empty i member]
  obtain ⟨time,bound,result,running,output⟩:=networkGenerator_executes restored input
    (by simp [restored]) (by simp [restored,flagged])
    (by simp [restored,flagged,population]) (by simp [restored,flagged,count]) restoredEmpty
  exact ⟨1+1+(5*(X3CEncoding.codec.encode input).length+2+1+time),by omega,result,
    pushing.sequence (copying.sequence running),output⟩

end Counting.HardnessNetworkMachine
