import Counting.StackGaussianRowStep
import Counting.StoredGaussianIteration

namespace Counting.StackMachine.GaussianBank
open Routine DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

def rowCostAt {q : Nat} (pivot : Fin q) (state : GaussianState q) (index : Nat) : Nat :=
  if inside : index<q then rowStepCost state.system pivot ⟨index,inside⟩ else 0

def rowsCost {q : Nat} (pivot : Fin q) : Nat → Nat → GaussianState q → Nat
  | _,0,_ => 1
  | start,count+1,state => rowCostAt pivot state start+4+
      rowsCost pivot (start+1) count (StoredGaussian.eliminateAt pivot state start)

abbrev rowIteration : Routine 50 := sequence rowStep (pushBit 48 true)
abbrev rowsLoop : Routine 50 := forEach 49 rowIteration
abbrev eliminateAll : Routine 50 := sequence initializeRows (sequence rowsLoop (clear 48))

/-- The implemented countdown visits every row in increasing order. The
cost sum is over the actual intermediate states, ready for a uniform bound
on their encoded coefficients. It includes skipped rows and loop overhead. -/
theorem rowsLoop_executes {q : Nat} (pivot : Fin q) (start count : Nat) (state : GaussianState q)
    (active : state.ok=true) (inside : start+count ≤ q) :
    ∃ time ≤ rowsCost pivot start count state,
      Executes rowsLoop (stateStore state pivot.val [] (List.replicate (start+1) true) (List.replicate count true) []) time
        (stateStore (StoredGaussian.eliminateCount pivot start count state) pivot.val []
          (List.replicate (start+count+1) true) [] []) := by
  induction count generalizing start state with
  | zero =>
    have ran := repeat_empty (49 : Fin 52) rowIteration
      (stateStore state pivot.val [] (List.replicate (start+1) true) [] []) rfl
    exact ⟨1,by simp [rowsCost],⟨⟨1,_⟩,ran.1,ran.2,rfl⟩⟩
  | succ count ih =>
    let row : Fin q := ⟨start,by omega⟩
    let next := StoredGaussian.eliminateOne pivot state row
    let initial := stateStore state pivot.val [] (List.replicate (start+1) true) (true::List.replicate count true) []
    have popped : Function.update initial 49 (List.replicate count true)=
        stateStore state pivot.val [] (List.replicate (start+1) true) (List.replicate count true) [] := by
      funext r;fin_cases r <;> simp [initial,stateStore,stateSaved,ready,bank,MatrixAxpy.file,RowAxpy.file]
    obtain ⟨bodyTime,bodyBound,bodyRun⟩ := rowStep_executes state pivot row active (List.replicate count true)
    have increment := incrementRow_executes next pivot.val start (List.replicate count true)
    have body := bodyRun.sequence increment
    obtain ⟨bodyFinish,bodyRan,bodyHalt,bodyStore⟩ := body
    have first := repeat_iteration (49 : Fin 52) rowIteration initial true (List.replicate count true) rfl
      (bodyTime+1+1) bodyFinish (by rw [popped];exact bodyRan) bodyHalt
    have nextActive : next.ok=true := by
      change (StoredGaussian.eliminateOne pivot state row).ok=true
      rw [←StoredGaussian.eliminateAt_fin pivot row state]
      exact (StoredGaussian.eliminateAt_ok pivot state row.val).trans active
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ := ih (start+1) next nextActive (by omega)
    refine ⟨bodyTime+1+1+2+tailTime,?_,⟨tailFinish,?_,tailHalt,?_⟩⟩
    · have atNext : StoredGaussian.eliminateAt pivot state start=next := by
        exact StoredGaussian.eliminateAt_fin pivot row state
      simp only [rowsCost,atNext]
      have costAt : rowCostAt pivot state start=rowStepCost state.system pivot row := by simp [rowCostAt,row.isLt,row]
      rw [costAt]
      omega
    · have combined := Machine.run_add (step rowsLoop.program) (bodyTime+1+1+2) tailTime ⟨0,initial⟩
      rw [first,Option.bind_some,bodyStore] at combined
      have shifted : start+2=(start+1)+1 := by omega
      rw [shifted,tailRun] at combined
      simpa only [initial,List.replicate_succ] using combined
    · have atNext : StoredGaussian.eliminateAt pivot state start=next := StoredGaussian.eliminateAt_fin pivot row state
      simpa only [StoredGaussian.eliminateCount,atNext,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using tailStore

theorem eliminateAll_executes {q : Nat} (state : GaussianState q) (pivot : Fin q) (active : state.ok=true) :
    ∃ time ≤ 5*q+4+1+(rowsCost pivot 0 q state+1+(q+2)),
      Executes eliminateAll (stateStore state pivot.val [] [] [] []) time
        (stateStore (StoredGaussian.eliminateRows pivot (List.finRange q) state) pivot.val [] [] [] []) := by
  have initialized := initializeRows_executes state pivot.val
  obtain ⟨loopTime,loopBound,loopRun⟩ := rowsLoop_executes pivot 0 q state active (by omega)
  simp only [Nat.zero_add] at loopRun
  have cleaned := clearSaved_executes 6
    (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (StoredGaussian.eliminateCount pivot 0 q state).system))
    [] [] [] (stateSaved (StoredGaussian.eliminateCount pivot 0 q state) pivot.val [] (List.replicate (q+1) true) [] [])
  have cleanStore : Function.update (stateSaved (StoredGaussian.eliminateCount pivot 0 q state) pivot.val []
      (List.replicate (q+1) true) [] []) 6 []=
      stateSaved (StoredGaussian.eliminateCount pivot 0 q state) pivot.val [] [] [] [] := by
    funext r;fin_cases r <;> simp [stateSaved]
  rw [cleanStore] at cleaned
  have cleanTime : (stateSaved (StoredGaussian.eliminateCount pivot 0 q state) pivot.val []
      (List.replicate (q+1) true) [] [] 6).length+1=q+2 := by simp [stateSaved]
  rw [cleanTime] at cleaned
  change Executes (clear (48 : Fin 52))
    (stateStore (StoredGaussian.eliminateCount pivot 0 q state) pivot.val [] (List.replicate (q+1) true) [] [])
    (q+2) (stateStore (StoredGaussian.eliminateCount pivot 0 q state) pivot.val [] [] [] []) at cleaned
  have composed := initialized.sequence (loopRun.sequence cleaned)
  rw [StoredGaussian.eliminateCount_full] at composed
  exact ⟨_,by omega,composed⟩

end Counting.StackMachine.GaussianBank
