import Counting.ExternalCoverCheckCount
import Counting.StackEmitNatural

namespace Counting.External.CoverVerification
open StackMachine StackMachine.Routine CoverMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def queryPositions : Fin 5 ↪ Fin 48 := ⟨![37,38,18,20,29],by decide⟩
def queryRoles (w : RowWorkspace extra) : PowerWorkspace (extra+43) := queryPositions.trans w

def prepareElement (extra : Nat) (w : RowWorkspace extra) : Routine (extra+46) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+45) (w 34) (w 0) (w 41)))
    (sequence (ofProgram (ListPrograms.copyProgram (extra+45) (w 33) (w 32) (w 41)))
      (sequence (ofProgram (ListPrograms.copyProgram (extra+45) (w 25) (w 23) (w 41)))
        (emitNatural (extra+43) (queryRoles w))))

def prepareElementResult (w : RowWorkspace extra) (store : Fin (extra+48) → List Bool) :=
  Function.update (Function.update (Function.update (Function.update store (w 0) (store (w 34)))
    (w 32) (store (w 33))) (w 23) (store (w 25))) (w 38) (Encoding.natural.encode (store (w 37)).length)

def prepareElementCost (stream mask count index : Nat) := 5*(stream+mask+count)+9+20*(index+1)^2

theorem prepareElement_executes (extra : Nat) (w : RowWorkspace extra)
    (store : Fin (extra+48) → List Bool)
    (empty : ∀ i∈([0,18,20,23,29,32,38,41]:List (Fin 48)),store (w i)=[]) :
    ∃ time ≤ prepareElementCost (store (w 34)).length (store (w 33)).length
        (store (w 25)).length (store (w 37)).length,
      Executes (prepareElement extra w) store time (prepareElementResult w store) := by
  let first := Function.update store (w 0) (store (w 34))
  have firstRun : Executes (ofProgram (ListPrograms.copyProgram (extra+45) (w 34) (w 0) (w 41))) store
      (5*(store (w 34)).length+2) first := by
    simpa [first,empty] using copy_executes (extra+45) (w 34) (w 0) (w 41)
      (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store (empty 41 (by simp))
  let second := Function.update first (w 32) (store (w 33))
  have secondRun : Executes (ofProgram (ListPrograms.copyProgram (extra+45) (w 33) (w 32) (w 41))) first
      (5*(store (w 33)).length+2) second := by
    simpa [second,first,w.injective.eq_iff,empty] using copy_executes (extra+45) (w 33) (w 32) (w 41)
      (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) first
      (by simp [first,w.injective.eq_iff,empty])
  let third := Function.update second (w 23) (store (w 25))
  have thirdRun : Executes (ofProgram (ListPrograms.copyProgram (extra+45) (w 25) (w 23) (w 41))) second
      (5*(store (w 25)).length+2) third := by
    simpa [third,second,first,w.injective.eq_iff,empty] using copy_executes (extra+45) (w 25) (w 23) (w 41)
      (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) second
      (by simp [second,first,w.injective.eq_iff,empty])
  obtain ⟨emitTime,emitBound,emitRun⟩ := emitNatural_executes (extra+43) (queryRoles w) third
    (by simp [queryRoles,queryPositions,third,second,first,w.injective.eq_iff,empty])
    (by simp [queryRoles,queryPositions,third,second,first,w.injective.eq_iff,empty])
    (by simp [queryRoles,queryPositions,third,second,first,w.injective.eq_iff,empty])
  have emitAs : Executes (emitNatural (extra+43) (queryRoles w)) third emitTime (prepareElementResult w store) := by
    simpa [queryRoles,queryPositions,third,second,first,w.injective.eq_iff,empty,prepareElementResult] using emitRun
  refine ⟨(5*(store (w 34)).length+2)+1+((5*(store (w 33)).length+2)+1+((5*(store (w 25)).length+2)+1+emitTime)),?_,
    firstRun.sequence (secondRun.sequence (thirdRun.sequence emitAs))⟩
  simp only [queryRoles,queryPositions,Function.Embedding.trans_apply,Function.Embedding.coeFn_mk,
    Matrix.cons_val_zero,third,second,first] at emitBound
  have index : (Function.update (Function.update (Function.update store (w 0) (store (w 34)))
      (w 32) (store (w 33))) (w 23) (store (w 25))) (w 37)=store (w 37) := by simp [w.injective.eq_iff]
  rw [index] at emitBound
  unfold prepareElementCost
  omega

end Counting.External.CoverVerification
