import Counting.StackProtocolAdvanceUpdate
import Counting.StackDagEmptyGuard

namespace Counting.StackMachine.ProtocolAdvance
open Routine Executable EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

/-- Compile-time selection between the original core and optimized transition. -/
def transition (core : Bool) (state : LocalState) (messages : List (Vista×Nat)) (degree : Nat) : Option LocalState :=
  if core then advanceCore? state messages degree else advance? state messages degree

theorem transition_unfold (core : Bool) (state : LocalState) (messages : List (Vista×Nat)) (degree : Nat) :
    transition core state messages degree=
      if state.output.isSome then some state else if state.leaders=0 then none else
        (updateVista? state.vista messages degree).map
          (fun vista=>⟨state.leaders,vista,decision core state.leaders vista⟩) := by
  cases core <;> simp only [transition,Bool.false_eq_true,if_false,if_true]
  · unfold advance? advancePlan
    split
    · rfl
    · split
      · simp_all [SolverPlan.eval]
      · cases updateVista? state.vista messages degree with
        | none=>simp_all [SolverPlan.eval]
        | some vista=>simp_all [decision]
  · unfold advanceCore? advanceCorePlan
    split
    · rfl
    · split
      · simp_all [SolverPlan.eval]
      · cases updateVista? state.vista messages degree with
        | none=>simp_all [SolverPlan.eval]
        | some vista=>simp_all [decision]

abbrev checkLeaders : Routine 254 := DagValidation.emptyFlag 249 1
@[noinline] def afterLeaders (core : Bool) : Routine 254 := branchRoutine 1 reject (updateAndDecide core)
@[noinline] def active (core : Bool) : Routine 254 := sequence checkLeaders (afterLeaders core)
@[noinline] def dispatch (core : Bool) : Routine 254 := branchRoutine 248 restoreHalted (active core)

theorem checkLeaders_executes (leaders : Nat) (old : Vista) (messages : List (Vista×Nat)) (degree : Nat) :
    ∃time≤3,Executes checkLeaders (file [] [] (metadata [] leaders old messages degree [])) time
      (file [] [decide (leaders=0)] (metadata [] leaders old messages degree [])) := by
  let saved:=metadata [] leaders old messages degree []
  have run:=DagValidation.emptyFlag_executes (249:Fin 256) 1 (file [] [] saved)
  have source:file [] [] saved 249=leaders.bits := by simp [file,saved,metadata]
  have output:file [] [] saved 1=[] := by simp [file]
  rw [source,output] at run
  have zero:leaders.bits=[] ↔ leaders=0 := by
    constructor
    · intro equal;have value:=congrArg Encoding.value equal
      simpa only [Encoding.value_bits,Encoding.value] using value
    · rintro rfl;rfl
  simp only [zero] at run
  have final:Function.update (file [] [] saved) 1 [decide (leaders=0)]=file [] [decide (leaders=0)] saved := by
    funext r;by_cases one:r=1 <;> simp [file,one]
  rw [final] at run
  exact ⟨_,by unfold DagValidation.emptyFlagCost;split <;> omega,run⟩

theorem active_executes (core : Bool) (state : LocalState) (messages : List (Vista×Nat)) (degree : Nat)
    (updated : Vista) (valid:state.vista.valid=true)
    (received:∀m∈messages,m.1.valid=true ∧ 0 < m.2 ∧ (m.1.node m.1.bottom).level=(state.vista.node state.vista.bottom).level)
    (success:updateVista? state.vista messages degree=some updated) (running:state.output=none) :
    ∃time output,time≤ activeBudget core state.leaders state.vista updated messages degree+6 ∧
      Executes (active core) (file [] [] (metadata [] state.leaders state.vista messages degree [])) time output ∧
      output 1=outputWord (transition core state messages degree) := by
  unfold active
  let saved:=metadata [] state.leaders state.vista messages degree []
  obtain ⟨a,ab,ar⟩:=checkLeaders_executes state.leaders state.vista messages degree
  have popped:Function.update (file [] [decide (state.leaders=0)] saved) 1 []=file [] [] saved := by
    funext r;by_cases one:r=1 <;> simp [file,one]
  by_cases zero:state.leaders=0
  · have br:=pushBit_executes (1:Fin 256) false (file [] [] saved)
    have target:Function.update (file [] [] saved) 1 (false::file [] [] saved 1)=file [] [false] saved := by
      funext r;by_cases one:r=1 <;> simp [file,one]
    rw [target] at br
    have branch:=branch_executes_true (1:Fin 256) reject (updateAndDecide core)
      (file [] [decide (state.leaders=0)] saved) _ [] _ (by simp [file,zero])
      (by rw [popped];exact br)
    refine ⟨_,_,by omega,ar.sequence branch,?_⟩
    simp [file,transition_unfold,running,zero,outputWord,answerCodec,Encoding.optional]
  · obtain ⟨b,bb,br⟩:=updateAndDecide_executes core state.leaders state.vista updated messages degree
      valid (by omega) received success
    have branch:=branch_executes_false (1:Fin 256) reject (updateAndDecide core)
      (file [] [decide (state.leaders=0)] saved) _ [] b (by simp [file,zero])
      (by rw [popped];exact br)
    refine ⟨_,_,by omega,ar.sequence branch,?_⟩
    simp [file,transition_unfold,running,zero,success]

theorem dispatch_executes (core : Bool) (state : LocalState) (messages : List (Vista×Nat)) (degree : Nat)
    (updated : Vista) (valid:state.vista.valid=true)
    (received:∀m∈messages,m.1.valid=true ∧ 0 < m.2 ∧ (m.1.node m.1.bottom).level=(state.vista.node state.vista.bottom).level)
    (success:updateVista? state.vista messages degree=some updated) :
    ∃time output,time≤ 60*((stateWord state).length+1)+activeBudget core state.leaders state.vista updated messages degree+8 ∧
      Executes (dispatch core)
        (file [] [] (metadata ((Encoding.optional Encoding.natural).encode state.output) state.leaders state.vista messages degree [])) time output ∧
      output 1=outputWord (transition core state messages degree) := by
  unfold dispatch
  let saved:=metadata ((Encoding.optional Encoding.natural).encode state.output) state.leaders state.vista messages degree []
  cases halted:state.output with
  | none=>
    have popped:Function.update (file [] [] saved) 248 []=
        file [] [] (metadata [] state.leaders state.vista messages degree []) := by
      change Function.update (file [] [] saved) (slot 0) ([]:List Bool)=_
      rw [file_update_slot]
      congr 1;funext r;fin_cases r <;> simp [saved,metadata]
    obtain ⟨time,output,bound,run,value⟩:=active_executes core state messages degree updated valid received success halted
    have branch:=branch_executes_false (248:Fin 256) restoreHalted (active core)
      (file [] [] saved) output [] time (by simp [file,saved,metadata,halted,Encoding.optional])
      (by rw [popped];exact run)
    dsimp only [saved] at branch
    rw [halted] at branch
    exact ⟨_,output,by omega,branch,value⟩
  | some value=>
    have popped:Function.update (file [] [] saved) 248 (Encoding.natural.encode value)=
        file [] [] (metadata (Encoding.natural.encode value) state.leaders state.vista messages degree []) := by
      change Function.update (file [] [] saved) (slot 0) (Encoding.natural.encode value)=_
      rw [file_update_slot]
      congr 1;funext r;fin_cases r <;> simp [saved,metadata]
    obtain ⟨time,bound,run⟩:=restoreHalted_executes state messages degree value halted
    have branch:=branch_executes_true (248:Fin 256) restoreHalted (active core)
      (file [] [] saved) _ (Encoding.natural.encode value) time
      (by simp [file,saved,metadata,halted,Encoding.optional]) (by rw [popped];exact run)
    dsimp only [saved] at branch
    rw [halted] at branch
    refine ⟨_,_,by omega,branch,?_⟩
    simp [file,transition_unfold,halted]

end Counting.StackMachine.ProtocolAdvance
