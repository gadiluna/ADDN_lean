import Counting.StackRealizabilityLevelPreserved
import Counting.StackRealizabilityPointLoopFile

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def pointVisibleRoles : Fin 36 ↪ Fin 60 where
  toFun r := if r=21 then 45 else ⟨r.val,by omega⟩
  inj' := by
    intro a b same
    by_cases a21 : a=21 <;> by_cases b21 : b=21
    · exact a21.trans b21.symm
    · subst a
      simp only [if_neg b21] at same
      have vals := congrArg (fun r : Fin 60=>r.val) same
      change 45=b.val at vals
      omega
    · subst b
      simp only [if_neg a21] at same
      have vals := congrArg (fun r : Fin 60=>r.val) same
      change a.val=45 at vals
      omega
    · simp only [if_neg a21,if_neg b21] at same
      exact Fin.ext (congrArg (fun r : Fin 60=>r.val) same)

def pointVisible : Routine 58 := mapRegisters pointVisibleRoles levelPreserved

theorem pointVisible_executes (nodes : List Executable.Node) (values : List Nat)
    (length : values.length=nodes.length) (target : Nat) (accepted : Bool) (tail : List Bool)
    (data : Fin 18→List Bool) (empty : data 3=[]) :
    ∃ time ≤ 15000*(massInputSize nodes values+target.size)^5,
      Executes pointVisible (pointLoopStore nodes values target 0 (accepted::tail) data [] [] [] []) time
        (pointLoopStore nodes values target 0 (accepted::tail)
          (Function.update data 3 (levelRangeSum nodes target 0 values).bits) [] [] [] []) := by
  let start := pointLoopStore nodes values target 0 (accepted::tail) data [] [] [] []
  let localStore : Store 34 := start ∘ pointVisibleRoles
  have work (r : Fin 36) (small : r.val<17) (different : r≠1) : localStore r=[] := by
    fin_cases r <;> simp_all [localStore,start,pointLoopStore,pointFile,massFile,pointVisibleRoles]
  obtain ⟨time,bound,run⟩ := levelPreserved_executes localStore accepted tail
    (by simp [localStore,start,pointLoopStore,pointFile,massFile,pointVisibleRoles]) work
    (by simp [localStore,start,pointLoopStore,pointFile,massFile,pointVisibleRoles])
    (by simp [localStore,start,pointLoopStore,pointFile,massFile,pointVisibleRoles])
    (by simp [localStore,start,pointLoopStore,pointFile,massFile,pointVisibleRoles])
    (by simp [localStore,start,pointLoopStore,pointFile,massFile,pointVisibleRoles])
    (by simp [localStore,start,pointLoopStore,pointFile,massFile,pointVisibleRoles])
    (by simp [localStore,start,pointLoopStore,pointFile,massFile,pointVisibleRoles])
    (by simp [localStore,start,pointLoopStore,pointFile,massFile,pointVisibleRoles])
    (by simp [localStore,start,pointLoopStore,pointFile,massFile,pointVisibleRoles])
    nodes values length [] []
    (by simp [localStore,start,pointLoopStore,pointFile,massFile,pointVisibleRoles])
    (by simp [localStore,start,pointLoopStore,pointFile,massFile,pointVisibleRoles])
    target 0
    (by simp [localStore,start,pointLoopStore,pointFile,massFile,pointVisibleRoles])
    (by simp [localStore,start,pointLoopStore,pointFile,massFile,pointVisibleRoles])
    (by simp [localStore,start,pointLoopStore,pointFile,pointLoopData,pointVisibleRoles,empty])
  simp only [Nat.zero_add] at run
  refine ⟨time,?_,?_⟩
  · simpa [localStore,start,pointLoopStore,pointFile,massFile,pointVisibleRoles,massInputSize,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using bound
  · apply relocate_executes_frame levelPreserved pointVisibleRoles start _ localStore _ time rfl _ _ run
    · intro r
      fin_cases r <;> simp [localStore,start,pointLoopStore,pointFile,massFile,pointLoopData,pointVisibleRoles]
    · intro r outside
      have not45 : r≠45 := by intro same;subst r;exact outside 21 rfl
      have output : Function.update (pointFile
          (massFile ((Encoding.list Encoding.node).encode nodes) ((Encoding.list Encoding.natural).encode values)
            target.bits [] (0:Nat).bits (accepted::tail) [] [] []) (pointLoopData data [] [] [] []))
          (pointExtraRoles 3) (levelRangeSum nodes target 0 values).bits =
          pointLoopStore nodes values target 0 (accepted::tail)
            (Function.update data 3 (levelRangeSum nodes target 0 values).bits) [] [] [] [] := by
        rw [pointFile_update_data]
        congr 1
        funext i
        fin_cases i <;> simp [pointLoopData]
      rw [←output]
      exact Function.update_of_ne not45 _ _

end Counting.StackMachine.RealizabilityCheck
