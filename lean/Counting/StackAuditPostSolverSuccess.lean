import Counting.StackAuditPostSolverBranch
import Counting.StackAuditPostSolverHistoryInput
import Counting.ExecutableRefinementWeights

namespace Counting.StackMachine.AuditPostSolver
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def propagatedResult (anchor : Nat) (vista : Executable.Vista) (natural : Array Nat) : Option (Array Nat) :=
  let weights:=Executable.propagateWeights vista anchor natural
  if Executable.auditBalance vista weights anchor then some weights else none

def successBudget (anchor : Nat) (vista : Executable.Vista) (natural : Array Nat) : Nat :=
  let weights:=Executable.propagateWeights vista anchor natural
  let oldWord:=(Encoding.array Encoding.natural).encode natural
  let newWord:=(Encoding.array Encoding.natural).encode weights
  20*(oldWord.length+(Encoding.vista.encode vista).length+anchor.size+2)+
    AuditPropagation.propagationCoefficient*((AuditPropagation.propagationInputWord anchor vista natural).length+1)^32+
    (5*newWord.length+2)+20*(newWord.length+(Encoding.vista.encode vista).length+anchor.size+2)+
    AuditBalance.balanceCoefficient*((AuditBalance.balanceInputWord anchor vista weights).length+1)^17+
    10*(newWord.length+1)+5

abbrev success : Routine 54 := sequence historyInput
  (sequence propagationCall (sequence saveWeights
    (sequence historyInput (sequence balanceCall chooseBalance))))

/-- Feed the real propagation output into the real balance checker while
preserving a physical copy for the successful optional result. -/
theorem success_executes (anchor : Nat) (vista : Executable.Vista) (natural : Array Nat)
    (fits : anchor≤vista.nodes.size) (valid : vista.valid=true) :
    ∃ time ≤ successBudget anchor vista natural,
      Executes success (file [] ((Encoding.array Encoding.natural).encode natural) (metadata anchor vista)) time
        (file [] ((Encoding.optional (Encoding.array Encoding.natural)).encode (propagatedResult anchor vista natural))
          (metadata anchor vista)) := by
  let weights:=Executable.propagateWeights vista anchor natural
  let oldWord:=(Encoding.array Encoding.natural).encode natural
  let newWord:=(Encoding.array Encoding.natural).encode weights
  have input (values : Array Nat) :
      Encoding.natural.encode anchor++Encoding.frame (Encoding.vista.encode vista)++
        (Encoding.array Encoding.natural).encode values=AuditPropagation.propagationInputWord anchor vista values := by
    simp only [AuditPropagation.propagationInputWord,AuditPropagation.propagationInputCodec,
      Encoding.product,Encoding.framed,List.append_assoc]
  obtain ⟨firstTime,firstBound,a⟩:=historyInput_executes anchor vista oldWord (metadata anchor vista) rfl rfl rfl rfl
  change Executes _ _ firstTime
    (file (Encoding.natural.encode anchor++Encoding.frame (Encoding.vista.encode vista)++
      (Encoding.array Encoding.natural).encode natural) [] _) at a
  rw [input natural] at a
  obtain ⟨propTime,propBound,b⟩:=propagationCall_executes anchor vista natural fits (metadata anchor vista)
  change Executes _ _ propTime (file [] newWord (metadata anchor vista)) at b
  have c:=saveWeights_executes anchor vista newWord
  let saved:=Function.update (metadata anchor vista) 3 newWord
  obtain ⟨secondTime,secondBound,d⟩:=historyInput_executes anchor vista newWord saved
    (by simp [saved,metadata]) (by simp [saved,metadata]) (by simp [saved,metadata]) (by simp [saved,metadata])
  change Executes _ _ secondTime
    (file (Encoding.natural.encode anchor++Encoding.frame (Encoding.vista.encode vista)++
      (Encoding.array Encoding.natural).encode weights) [] _) at d
  rw [input weights] at d
  obtain ⟨balanceTime,balanceBound,e⟩:=balanceCall_executes anchor vista weights fits valid
    (Executable.propagateWeights_size vista anchor natural) saved
  obtain ⟨chooseTime,chooseBound,f⟩:=chooseBalance_executes anchor vista weights
    (Executable.auditBalance vista weights anchor)
  change chooseTime ≤ 10*(newWord.length+1) at chooseBound
  change Executes _ _ chooseTime
    (file [] ((Encoding.optional (Encoding.array Encoding.natural)).encode (propagatedResult anchor vista natural)) _) at f
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence (e.sequence f))))⟩
  dsimp only [successBudget]
  change _ ≤ 20*(oldWord.length+(Encoding.vista.encode vista).length+anchor.size+2)+
    AuditPropagation.propagationCoefficient*((AuditPropagation.propagationInputWord anchor vista natural).length+1)^32+
    (5*newWord.length+2)+20*(newWord.length+(Encoding.vista.encode vista).length+anchor.size+2)+
    AuditBalance.balanceCoefficient*((AuditBalance.balanceInputWord anchor vista weights).length+1)^17+
    10*(newWord.length+1)+5
  omega

end Counting.StackMachine.AuditPostSolver
