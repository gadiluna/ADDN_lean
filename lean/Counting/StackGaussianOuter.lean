import Counting.StackGaussianOuterBank

namespace Counting.StackMachine.GaussianBank
open Routine DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

def pivotCostAt {q : Nat} (state : GaussianState q) (index : Nat) : Nat :=
  if inside : index<q then pivotStepCost state ⟨index,inside⟩ else 0

def pivotsCost : Nat → Nat → GaussianState q → Nat
  | _,0,_ => 1
  | start,count+1,state => pivotCostAt state start+4+
      pivotsCost (start+1) count (StoredGaussian.pivotAt state start)

abbrev outerIteration : Routine 51 := sequence outerPivot (pushBit 42 true)
abbrev outerLoop : Routine 51 := forEach 52 outerIteration
abbrev initializeOuter : Routine 51 := ofProgram (ListPrograms.copyProgram 50 43 52 1)
abbrev generate : Routine 51 := sequence initializeOuter outerLoop

/-- The machine consumes an explicit unary counter. Every iteration is the
real serialized Gaussian step, and all other fields remain in the bank. -/
theorem outerLoop_executes {q : Nat} (start count : Nat) (state : GaussianState q)
    (inside : start+count ≤ q) :
    ∃ time ≤ pivotsCost start count state,
      Executes outerLoop (outerStore state start (List.replicate count true)) time
        (outerStore (StoredGaussian.pivotCount start count state) (start+count) []) := by
  induction count generalizing start state with
  | zero =>
    have ran := repeat_empty (52 : Fin 53) outerIteration (outerStore state start []) rfl
    exact ⟨1,by simp [pivotsCost],⟨⟨1,_⟩,ran.1,ran.2,rfl⟩⟩
  | succ count ih =>
    let pivot : Fin q := ⟨start,by omega⟩
    let next := StoredGaussian.pivotStep state pivot
    let initial := outerStore state start (true::List.replicate count true)
    have popped : Function.update initial 52 (List.replicate count true)=
        outerStore state start (List.replicate count true) := outerStore_update_counter state start _ _
    obtain ⟨bodyTime,bodyBound,bodyRun⟩ := outerPivot_executes state pivot (List.replicate count true)
    have increment := incrementPivot_executes next start (List.replicate count true)
    obtain ⟨bodyFinish,bodyRan,bodyHalt,bodyStore⟩ := bodyRun.sequence increment
    have first := repeat_iteration (52 : Fin 53) outerIteration initial true (List.replicate count true) rfl
      (bodyTime+1+1) bodyFinish (by rw [popped];exact bodyRan) bodyHalt
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ := ih (start+1) next (by omega)
    refine ⟨bodyTime+1+1+2+tailTime,?_,⟨tailFinish,?_,tailHalt,?_⟩⟩
    · have atNext : StoredGaussian.pivotAt state start=next := StoredGaussian.pivotAt_fin state pivot
      simp only [pivotsCost,atNext]
      have costAt : pivotCostAt state start=pivotStepCost state pivot := by simp [pivotCostAt,pivot.isLt,pivot]
      rw [costAt]
      omega
    · have combined := Machine.run_add (step outerLoop.program) (bodyTime+1+1+2) tailTime ⟨0,initial⟩
      rw [first,Option.bind_some,bodyStore,tailRun] at combined
      simpa only [initial,List.replicate_succ] using combined
    · have atNext : StoredGaussian.pivotAt state start=next := StoredGaussian.pivotAt_fin state pivot
      simpa only [StoredGaussian.pivotCount,atNext,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using tailStore

theorem initializeOuter_executes {q : Nat} (state : GaussianState q) (pivot : Nat) :
    Executes initializeOuter (outerStore state pivot []) (5*q+2)
      (outerStore state pivot (List.replicate q true)) := by
  have ran := copy_executes 50 (43 : Fin 53) 52 1 (by decide) (by decide) (by decide)
    (outerStore state pivot []) rfl
  have source : outerStore state pivot [] 43=List.replicate q true := rfl
  rw [source,outerStore_last,List.append_nil,outerStore_update_counter,List.length_replicate] at ran
  exact ran

/-- Complete concrete generator, starting with the serialized initial
matrix and its unary dimension. This theorem includes singular systems and
dimension zero; its next bound is a sum over actual intermediate matrices. -/
theorem generate_executes {q : Nat} (system : RationalSystem q) :
    ∃ time ≤ 5*q+3+pivotsCost 0 q ⟨system,[],true⟩,
      Executes generate (outerStore ⟨system,[],true⟩ 0 []) time
        (outerStore (StoredGaussian.runGaussian system) q []) := by
  have initial := initializeOuter_executes (⟨system,[],true⟩ : GaussianState q) 0
  obtain ⟨time,bounded,ran⟩ := outerLoop_executes 0 q (⟨system,[],true⟩ : GaussianState q) (by omega)
  rw [StoredGaussian.pivotCount_runGaussian] at ran
  simp only [Nat.zero_add] at ran
  refine ⟨_,?_,initial.sequence ran⟩
  omega

end Counting.StackMachine.GaussianBank
