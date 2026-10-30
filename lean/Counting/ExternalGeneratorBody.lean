import Counting.ExternalGeneratorDynamics
import Counting.ExternalFormulaSerialization

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine Tableau InitialRows

/-- All five blocks of the actual clause stream. The only finite-control
parameter is the fixed verifier, with runtime dimensions stored in unary. -/
def formulaBodyRoutine (extra : Nat) (w : GeneratorWorkspace extra) (program : Machine.Program) : Routine (extra+30) :=
  sequence (formulaDynamicsRoutine extra w program)
    (sequence (initialRowRoutine (extra+8) w.initialRoles program)
      (oneHotRoutine (extra+26) w.oneHotRoles (Cellular.alphabet program)))

theorem formulaBodyRoutine_executes (extra : Nat) (w : GeneratorWorkspace extra) (program : Machine.Program)
    (time : Nat) {width : Nat} (setup : Setup width) (store : Fin (extra+32) → List Bool)
    (timeValue : store (w 0)=List.replicate time true) (widthValue : store (w 1)=List.replicate width true)
    (offsetValue : store (w 2)=List.replicate setup.offset.val true) (headerValue : store (w 3)=setup.header)
    (capacityValue : store (w 4)=List.replicate setup.capacity true)
    (cellsValue : store (w 26)=List.replicate ((time+1)*width) true)
    (empty : ∀ i ∈ generatorScratch, store (w i)=[]) :
    ∃ transitions ≤ formulaBodyBound program time width setup.capacity,
      Executes (formulaBodyRoutine extra w program) store transitions
        (Function.update (Function.update store (w 26) []) (w 5)
          (Encoding.sequence clauseCodec
            ((Tableau.formula (T:=time) (Cellular.dynamics program (finRotate width))
              (setup.constraints program) (Cellular.accept program)).map (List.map CNFEncoding.literalRaw))++store (w 5))) := by
  let dynamicsBytes := formulaDynamicsBytes program time width
  let afterDynamics := Function.update store (w 5) (dynamicsBytes++store (w 5))
  obtain ⟨dynamicTime,dynamicBound,dynamicRun⟩ := formulaDynamicsRoutine_executes extra w program time width store
    timeValue widthValue empty
  obtain ⟨initialTime,initialBound,initialRun⟩ := initialRowRoutine_executes (extra+8) w.initialRoles program (time:=time) setup afterDynamics
    (by simp [GeneratorWorkspace.initialRoles,generatorInitialSelection,afterDynamics,w.injective.eq_iff,offsetValue])
    (by simp [GeneratorWorkspace.initialRoles,generatorInitialSelection,afterDynamics,w.injective.eq_iff,headerValue])
    (by simp [GeneratorWorkspace.initialRoles,generatorInitialSelection,afterDynamics,w.injective.eq_iff,capacityValue])
    (by simp [GeneratorWorkspace.initialRoles,generatorInitialSelection,afterDynamics,w.injective.eq_iff,widthValue])
    (by simp [GeneratorWorkspace.initialRoles,generatorInitialSelection,afterDynamics,w.injective.eq_iff,
      empty 6 (by simp [generatorScratch])])
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals
        simp [GeneratorWorkspace.initialRoles,generatorInitialSelection,afterDynamics,w.injective.eq_iff]
        apply empty
        simp [generatorScratch])
  let initialBytes :=
    (List.finRange width).flatMap (fun place => Encoding.sequence clauseCodec
      ((initialConstraint (T:=time) (setup.unary program place)).toCNF.map (List.map CNFEncoding.literalRaw)))++
    (List.finRange (setup.capacity-1)).flatMap (fun place => Encoding.sequence clauseCodec
      ((initialConstraint (T:=time) (setup.binary program (adjacentLeft setup.capacity place)
        (adjacentRight setup.capacity place))).toCNF.map (List.map CNFEncoding.literalRaw)))
  let afterInitial := Function.update store (w 5) (initialBytes++dynamicsBytes++store (w 5))
  have second : Executes (initialRowRoutine (extra+8) w.initialRoles program) afterDynamics initialTime afterInitial := by
    simpa [GeneratorWorkspace.initialRoles,generatorInitialSelection,afterDynamics,afterInitial,initialBytes,List.append_assoc] using initialRun
  obtain ⟨hotTime,hotBound,hotRun⟩ := oneHotRoutine_executes (extra+26) w.oneHotRoles (Cellular.alphabet program) afterInitial
    (by simp [GeneratorWorkspace.oneHotRoles,generatorOneHotSelection,afterInitial,w.injective.eq_iff,empty 7 (by simp [generatorScratch])])
    (by simp [GeneratorWorkspace.oneHotRoles,generatorOneHotSelection,afterInitial,w.injective.eq_iff,empty 18 (by simp [generatorScratch])])
    (by simp [GeneratorWorkspace.oneHotRoles,generatorOneHotSelection,afterInitial,w.injective.eq_iff,empty 19 (by simp [generatorScratch])])
    (by simp [GeneratorWorkspace.oneHotRoles,generatorOneHotSelection,afterInitial,w.injective.eq_iff,empty 31 (by simp [generatorScratch])])
  have cells : afterInitial (w.oneHotRoles 0)=List.replicate ((time+1)*width) true := by
    simp [GeneratorWorkspace.oneHotRoles,generatorOneHotSelection,afterInitial,w.injective.eq_iff,cellsValue]
  rw [cells,List.length_replicate] at hotBound hotRun
  have finalStore : Function.update (Function.update afterInitial (w.oneHotRoles 0) []) (w.oneHotRoles 2)
      (Encoding.sequence clauseCodec
        ((FiniteConstraints.oneHot ((time+1)*width) (Cellular.alphabet program)).map (List.map CNFEncoding.literalRaw))++
          afterInitial (w.oneHotRoles 2))=
      Function.update (Function.update store (w 26) []) (w 5)
        (Encoding.sequence clauseCodec
          ((Tableau.formula (T:=time) (Cellular.dynamics program (finRotate width))
            (setup.constraints program) (Cellular.accept program)).map (List.map CNFEncoding.literalRaw))++store (w 5)) := by
    rw [formula_encoded_blocks]
    funext r
    by_cases a : r=w 5
    · subst r
      simp [GeneratorWorkspace.oneHotRoles,generatorOneHotSelection,afterInitial,initialBytes,dynamicsBytes,
        formulaDynamicsBytes,List.append_assoc]
    · by_cases b : r=w 26 <;>
        simp [GeneratorWorkspace.oneHotRoles,generatorOneHotSelection,afterInitial,a,b]
  rw [finalStore] at hotRun
  refine ⟨dynamicTime+1+(initialTime+1+hotTime),?_,dynamicRun.sequence (second.sequence hotRun)⟩
  unfold formulaBodyBound
  omega

end Counting.External.CookLevin.StackGenerator
