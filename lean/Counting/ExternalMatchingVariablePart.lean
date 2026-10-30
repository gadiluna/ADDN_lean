import Counting.ExternalMatchingGeneratorLayout

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def variablePart (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+62) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 33) (w 54) (w 59)))
    (sequence (scaleLength (extra+61) (w 25) (w 56) (w 59) 3)
      (sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 17) (w 58) (w 59)))
        (sequence (emitVariables (extra+48) w.variable) (clearRegisters [w 52,w 54,w 56]))))

def variablePartScratch : List (Fin 64) := [40,41,42,43,44,45,46,47,52,53,54,55,56,57,58,59]
def variablePartCost (n m shift : Nat) :=
  let bound := shift+3*m+2*n*(3*m+1)
  5*shift+15*m+5*n+n*(8000*(bound+1)^3+2)+3*(bound+2)+18

theorem variablePart_executes (extra : Nat) (w : GeneratorWorkspace extra)
    (n m shift : Nat) (store : Fin (extra+64) → List Bool)
    (nValue : store (w 17)=List.replicate n true) (mValue : store (w 25)=List.replicate m true)
    (shiftValue : store (w 33)=List.replicate shift true)
    (empty : ∀ i∈variablePartScratch,store (w i)=[]) :
    ∃ time ≤ variablePartCost n m shift,
      Executes (variablePart extra w) store time
        (Function.update store (w 36) ((Encoding.sequence (Encoding.list Encoding.natural)
          (variableBlocksRows 0 shift (3*m) n)).reverse++store (w 36))) := by
  let s1 := Function.update store (w 54) (List.replicate shift true)
  let s2 := Function.update s1 (w 56) (List.replicate (3*m) true)
  let s3 := Function.update s2 (w 58) (List.replicate n true)
  have a : Executes (ofProgram (ListPrograms.copyProgram (extra+61) (w 33) (w 54) (w 59))) store (5*shift+2) s1 := by
    simpa only [shiftValue,List.length_replicate,empty 54 (by decide),List.append_nil,s1] using
      copy_executes (extra+61) (w 33) (w 54) (w 59) (by simp [w.injective.eq_iff])
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store (empty 59 (by decide))
  have b : Executes (scaleLength (extra+61) (w 25) (w 56) (w 59) 3) s1 (3*(5*m+3)) s2 := by
    have run := scaleLength_executes (extra+61) (w 25) (w 56) (w 59)
      (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) 3 s1
      (by simp [s1,w.injective.eq_iff,empty 59 (by decide)])
    simpa [s2,s1,w.injective.eq_iff,mValue,empty 56 (by decide)] using run
  have c : Executes (ofProgram (ListPrograms.copyProgram (extra+61) (w 17) (w 58) (w 59))) s2 (5*n+2) s3 := by
    have run := copy_executes (extra+61) (w 17) (w 58) (w 59)
      (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) s2
      (by simp [s2,s1,w.injective.eq_iff,empty 59 (by decide)])
    simpa [s3,s2,s1,w.injective.eq_iff,nValue,empty 58 (by decide)] using run
  let bound := shift+3*m+2*n*(3*m+1)
  have readyEmpty (i : Fin 16) (member : i∈([1,3,4,5,7,8,9,10,11,12,14] : List (Fin 16))) : s3 (w.variable i)=[] := by
    simp only [List.mem_cons,List.not_mem_nil] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|h
    all_goals first | contradiction | simp [GeneratorWorkspace.variable,generatorVariablePositions,s3,s2,s1,w.injective.eq_iff,empty,variablePartScratch]
  obtain ⟨loopTime,loopBound,looping⟩ := emitVariables_executes (extra+48) w.variable n bound s3
    (by simp [GeneratorWorkspace.variable,generatorVariablePositions,s3])
    (by simp [GeneratorWorkspace.variable,generatorVariablePositions,s3,s2,w.injective.eq_iff])
    (by simp [GeneratorWorkspace.variable,generatorVariablePositions,s3,s2,s1,w.injective.eq_iff,empty 52 (by decide),bound]) readyEmpty
  let s4 := variablesResult (extra+48) w.variable s3 n
  have bounded (r : Fin (extra+64)) (member : r∈[w 52,w 54,w 56]) : (s4 r).length≤bound := by
    simp only [List.mem_cons,List.not_mem_nil] at member
    rcases member with rfl|rfl|rfl|h
    all_goals first | contradiction | (simp [s4,variablesResult,GeneratorWorkspace.variable,generatorVariablePositions,s3,s2,s1,w.injective.eq_iff,empty,variablePartScratch];dsimp [bound];nlinarith)
  obtain ⟨clearTime,clearBound,clearing⟩ := clearRegisters_selected_executes [w 52,w 54,w 56] s4 bound bounded
  have combined := a.sequence (b.sequence (c.sequence (looping.sequence clearing)))
  refine ⟨5*shift+2+1+(3*(5*m+3)+1+(5*n+2+1+(loopTime+1+clearTime))),?_,?_⟩
  · change clearTime≤3*(bound+2) at clearBound
    dsimp only [variablePartCost]
    change _ ≤ 5*shift+15*m+5*n+n*(8000*(bound+1)^3+2)+3*(bound+2)+18
    omega
  · have final : clearedStore [w 52,w 54,w 56] s4=Function.update store (w 36)
        ((Encoding.sequence (Encoding.list Encoding.natural) (variableBlocksRows 0 shift (3*m) n)).reverse++store (w 36)) := by
      funext r
      by_cases a0 : r=w 52
      · subst r;simp [clearedStore,w.injective.eq_iff,empty 52 (by decide)]
      · by_cases a1 : r=w 54
        · subst r;simp [clearedStore,w.injective.eq_iff,empty 54 (by decide)]
        · by_cases a2 : r=w 56
          · subst r;simp [clearedStore,w.injective.eq_iff,empty 56 (by decide)]
          · by_cases a3 : r=w 58
            · subst r;simp [clearedStore,s4,variablesResult,GeneratorWorkspace.variable,generatorVariablePositions,s3,s2,s1,w.injective.eq_iff,empty 58 (by decide)]
            · by_cases a4 : r=w 36
              · subst r;simp [clearedStore,s4,variablesResult,GeneratorWorkspace.variable,generatorVariablePositions,s3,s2,s1,w.injective.eq_iff,empty 52 (by decide)]
              · simp [clearedStore,s4,variablesResult,GeneratorWorkspace.variable,generatorVariablePositions,s3,s2,s1,a0,a1,a2,a3,a4]
    simpa only [variablePart,final] using combined

end Counting.External.MatchingMachine
