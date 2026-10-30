import Counting.StackAuditPropagationLevelItem
import Counting.ExecutableRefinementWeights

namespace Counting.StackMachine.AuditPropagation

def levelScan (vista : Executable.Vista) (r start : Nat) : Nat → Array Nat → Array Nat
  | 0,weights => weights
  | count+1,weights => levelScan vista r (start+1) count (levelChoiceWeights vista r start weights)

@[simp] theorem levelChoiceWeights_size (vista : Executable.Vista) (r old : Nat) (weights : Array Nat) :
    (levelChoiceWeights vista r old weights).size=weights.size := by
  unfold levelChoiceWeights
  split_ifs <;> simp

@[simp] theorem levelScan_size (vista : Executable.Vista) (r start count : Nat) (weights : Array Nat) :
    (levelScan vista r start count weights).size=weights.size := by
  induction count generalizing start weights with
  | zero => rfl
  | succ count ih => simp only [levelScan,ih,levelChoiceWeights_size]

theorem levelScan_add (vista : Executable.Vista) (r start first second : Nat) (weights : Array Nat) :
    levelScan vista r start (first+second) weights=
      levelScan vista r (start+first) second (levelScan vista r start first weights) := by
  induction first generalizing start weights with
  | zero => simp only [Nat.zero_add,Nat.add_zero,levelScan]
  | succ first ih =>
    rw [show first+1+second=(first+second)+1 by omega,levelScan,ih,levelScan]
    congr 1
    omega

theorem levelScan_eq_updateNodes (vista : Executable.Vista) (r start count : Nat) (weights : Array Nat) :
    levelScan vista r start count weights=
      Executable.updateNodes vista r
        ((List.range' start count).filter (fun i=>(vista.node i).level==r)) weights := by
  induction count generalizing start weights with
  | zero => rfl
  | succ count ih =>
    rw [levelScan,ih,List.range'_succ]
    by_cases selected : (vista.node start).level=r
    · simp only [List.filter_cons,selected,beq_self_eq_true,if_true,levelChoiceWeights,
        Executable.updateNodes,List.foldl_cons,Array.set!_eq_setIfInBounds]
      rfl
    · simp only [List.filter_cons,show ((vista.node start).level==r)=false by simp [selected],if_false,
        levelChoiceWeights,selected,Bool.false_eq_true,if_false]

theorem levelScan_full (vista : Executable.Vista) (r : Nat) (weights : Array Nat) :
    levelScan vista r 0 vista.nodes.size weights=Executable.propagateLevel vista weights r := by
  rw [levelScan_eq_updateNodes]
  simp only [←List.range_eq_range',Executable.updateNodes,Executable.propagateLevel,Executable.levelNodes]

end Counting.StackMachine.AuditPropagation
