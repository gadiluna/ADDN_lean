import Counting.NetworkRecognitionMatrixCheck

namespace Counting.StackMachine.NetworkRecognition
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def roundDecisions (width:Nat) (graphs:List (List (List Nat))) : Bool := graphs.all (matrixAccepted width)

def roundsStore (store:Store 24) (accepted:Bool) (tail:List Bool)
    (graphs:List (List (List Nat))) (suffix:List Bool) : Store 24 :=
  Function.update (Function.update (Function.update store 17 suffix) 25 [])
    1 ((accepted && roundDecisions (store 0).length graphs)::tail)

theorem rounds_executes (store:Store 24) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail)
    (work:∀r:Fin 26,r≠0 → r≠1 → r≠17 → r≠25 → store r=[])
    (unary:store 0=List.replicate (store 0).length true)
    (graphs:List (List (List Nat))) (suffix:List Bool)
    (input:store 17=Encoding.sequence (Encoding.list (Encoding.list Encoding.natural)) graphs++suffix)
    (counter:store 25=List.replicate graphs.length true) :
    ∃time ≤ graphs.length*(500010000*((store 17).length+(store 0).length+1)^6+2)+1,
      Executes (forEach 25 matrixCheck) store time (roundsStore store accepted tail graphs suffix) := by
  induction graphs generalizing store accepted with
  | nil =>
    obtain ⟨ran,halted⟩:=repeat_empty (25:Fin 26) matrixCheck store (by simpa using counter)
    have source:store 17=suffix:=by simpa only [Encoding.sequence,List.nil_append] using input
    have noCounter:store 25=[]:=by simpa using counter
    have final:roundsStore store accepted tail [] suffix=store:=by
      funext r
      by_cases n1:r=1 <;> by_cases n17:r=17 <;> by_cases n25:r=25 <;>
        simp [roundsStore,roundDecisions,n1,n17,n25,status,source,noCounter]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons graph graphs ih =>
    let consumed:=Function.update store 25 (List.replicate graphs.length true)
    let remaining:=Encoding.sequence (Encoding.list (Encoding.list Encoding.natural)) graphs++suffix
    obtain ⟨bodyTime,bodyBound,body,bodyRun,bodyHalted,bodyStore⟩:=matrixCheck_executes consumed accepted tail
      (by simp [consumed,status])
      (by intro r n0 n1 n17 n25;simpa [consumed,n25] using work r n0 n1 n17 n25)
      (by simpa [consumed] using unary) graph remaining
      (by simpa [consumed,remaining,Encoding.sequence,List.append_assoc] using input)
    let middle:=matrixCheckStore consumed accepted tail graph remaining
    let next:=accepted && matrixAccepted (store 0).length graph
    obtain ⟨tailTime,tailBound,finish,tailRun,tailHalted,tailStore⟩:=ih middle next
      (by simp [middle,matrixCheckStore,consumed,next])
      (by intro r n0 n1 n17 n25;simpa [middle,matrixCheckStore,consumed,n1,n17,n25] using work r n0 n1 n17 n25)
      (by simpa [middle,matrixCheckStore,consumed] using unary)
      (by simp [middle,matrixCheckStore,remaining]) (by simp [middle,matrixCheckStore,consumed])
    have firstRun:=repeat_iteration (25:Fin 26) matrixCheck store true (List.replicate graphs.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter) bodyTime body bodyRun bodyHalted
    have final:roundsStore middle next tail graphs suffix=roundsStore store accepted tail (graph::graphs) suffix:=by
      funext r
      by_cases n1:r=1 <;> by_cases n17:r=17 <;> by_cases n25:r=25 <;>
        simp [roundsStore,roundDecisions,middle,matrixCheckStore,consumed,next,n1,n17,n25,Bool.and_assoc]
    have shorter:(middle 17).length ≤ (store 17).length:=by
      rw [input]
      simp only [middle,matrixCheckStore,Function.update_of_ne (by decide : (17:Fin 26)≠1),
        Function.update_self,remaining,Encoding.sequence,List.length_append]
      omega
    have width:middle 0=store 0:=by simp [middle,matrixCheckStore,consumed]
    rw [width] at tailBound
    have tailLimit:tailTime ≤ graphs.length*(500010000*((store 17).length+(store 0).length+1)^6+2)+1:=by
      apply tailBound.trans;gcongr
    simp only [consumed,Function.update_of_ne (by decide : (17:Fin 26)≠25),
      Function.update_of_ne (by decide : (0:Fin 26)≠25)] at bodyBound
    refine ⟨bodyTime+2+tailTime,?_,finish,?_,tailHalted,tailStore.trans final⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul];omega
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.NetworkRecognition
