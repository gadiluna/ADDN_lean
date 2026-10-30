import Counting.ExternalGeneratorWorkspace

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine Tableau

def formulaDynamicsRoutine (extra : Nat) (w : GeneratorWorkspace extra) (program : Machine.Program) : Routine (extra+30) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+29) (w 0) (w 27) (w 31)))
    (sequence (finalClauseRoutine (extra+20) w.coordinateRoles program)
      (transitionsRoutine (extra+20) w.coordinateRoles program))

def formulaDynamicsBytes (program : Machine.Program) (time width : Nat) :=
  (List.finRange time).flatMap (fun round => (List.finRange width).flatMap (fun place => Encoding.sequence clauseCodec
    ((transitionConstraint (Cellular.dynamics program (finRotate width)) round place).toCNF.map (List.map CNFEncoding.literalRaw))))++
  clauseCodec.encode ((@finalClause time width (Cellular.alphabet program) (Cellular.accept program)).map CNFEncoding.literalRaw)

theorem formulaDynamicsRoutine_executes (extra : Nat) (w : GeneratorWorkspace extra) (program : Machine.Program)
    (time width : Nat) (store : Fin (extra+32) → List Bool)
    (timeValue : store (w 0)=List.replicate time true) (widthValue : store (w 1)=List.replicate width true)
    (empty : ∀ i ∈ generatorScratch, store (w i)=[]) :
    ∃ transitions ≤ 5*time+4+finalClauseBound program time width+transitionsBound program time width,
      Executes (formulaDynamicsRoutine extra w program) store transitions
        (Function.update store (w 5) (formulaDynamicsBytes program time width++store (w 5))) := by
  let copied := Function.update store (w 27) (List.replicate time true)
  let finalBytes := clauseCodec.encode ((@finalClause time width (Cellular.alphabet program) (Cellular.accept program)).map CNFEncoding.literalRaw)
  let afterFinal := Function.update copied (w 5) (finalBytes++store (w 5))
  have first : Executes (ofProgram (ListPrograms.copyProgram (extra+29) (w 0) (w 27) (w 31))) store
      (5*time+2) copied := by
    simpa +instances only [ListPrograms.copyProgram,timeValue,List.length_replicate,
      empty 27 (by simp [generatorScratch]),List.append_nil,copied] using
      copy_executes (extra+29) (w 0) (w 27) (w 31)
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store
        (empty 31 (by simp [generatorScratch]))
  obtain ⟨finalTime,finalBound,finalRun⟩ := finalClauseRoutine_executes (extra+20) w.coordinateRoles program time width copied
    (by simp [GeneratorWorkspace.coordinateRoles,generatorCoordinateSelection,copied])
    (by simp [GeneratorWorkspace.coordinateRoles,generatorCoordinateSelection,copied,w.injective.eq_iff,widthValue])
    (by simp [GeneratorWorkspace.coordinateRoles,generatorCoordinateSelection,copied,w.injective.eq_iff,empty 6 (by simp [generatorScratch])])
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals
        simp [GeneratorWorkspace.coordinateRoles,generatorCoordinateSelection,copied,w.injective.eq_iff]
        apply empty
        simp [generatorScratch])
  have second : Executes (finalClauseRoutine (extra+20) w.coordinateRoles program) copied finalTime afterFinal := by
    simpa [GeneratorWorkspace.coordinateRoles,generatorCoordinateSelection,afterFinal,finalBytes,copied,w.injective.eq_iff] using finalRun
  obtain ⟨transitionTime,transitionBound,transitionRun⟩ := transitionsRoutine_executes (extra+20) w.coordinateRoles program time width afterFinal
    (by simp [GeneratorWorkspace.coordinateRoles,generatorCoordinateSelection,afterFinal,copied,w.injective.eq_iff])
    (by simp [GeneratorWorkspace.coordinateRoles,generatorCoordinateSelection,afterFinal,copied,w.injective.eq_iff,widthValue])
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals
        simp [GeneratorWorkspace.coordinateRoles,generatorCoordinateSelection,afterFinal,copied,w.injective.eq_iff]
        apply empty
        simp [generatorScratch])
  have restored : Function.update afterFinal (w 27) []=Function.update store (w 5) (finalBytes++store (w 5)) := by
    funext r
    by_cases a : r=w 27
    · subst r; simp [w.injective.eq_iff,empty 27 (by simp [generatorScratch])]
    · by_cases b : r=w 5 <;> simp [afterFinal,copied,a,b]
  have third : Executes (transitionsRoutine (extra+20) w.coordinateRoles program) afterFinal transitionTime
      (Function.update store (w 5) (formulaDynamicsBytes program time width++store (w 5))) := by
    have r0 : w.coordinateRoles 0=w 27 := rfl
    have r7 : w.coordinateRoles 7=w 5 := rfl
    rw [r0,r7,restored] at transitionRun
    simpa only [afterFinal,Function.update_self,Function.update_idem,formulaDynamicsBytes,finalBytes,List.append_assoc] using transitionRun
  refine ⟨5*time+2+1+(finalTime+1+transitionTime),by omega,?_⟩
  exact first.sequence (second.sequence third)

end Counting.External.CookLevin.StackGenerator
