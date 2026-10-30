import Counting.HardnessNetworkMachineLeader
import Counting.HardnessNetworkMachineGroups

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

abbrev MatrixWorkspace (extra : Nat) := Fin 16 ↪ Fin (extra+16)
def matrixGroupsPositions : Fin 13 ↪ Fin 16 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 16=>i.val) h)⟩
def MatrixWorkspace.groups (w : MatrixWorkspace extra) : GroupsWorkspace (extra+3) := matrixGroupsPositions.trans w

def matrixHeaderPositions : Fin 6 ↪ Fin 16 := ⟨![0,2,6,8,7,4],by decide⟩
def MatrixWorkspace.header (w : MatrixWorkspace extra) : External.CoverNormalization.EmitWorkspace (extra+10) :=
  matrixHeaderPositions.trans w

def emitMatrixHead (extra : Nat) (w : MatrixWorkspace extra) : Routine (extra+14) :=
  sequence (External.CoverNormalization.emitReversedNatural (extra+10) w.header)
    (ofProgram (ListPrograms.copyProgram (extra+13) (w 13) (w 2) (w 4)))

theorem emitMatrixHead_executes (extra : Nat) (w : MatrixWorkspace extra)
    (store : Fin (extra+16) → List Bool)
    (empty : ∀ i∈([4,6,7,8] : List (Fin 16)),store (w i)=[]) :
    ∃ time ≤ 30*((store (w 0)).length+1)^2+5*(store (w 13)).length+3,
      Executes (emitMatrixHead extra w) store time
        (Function.update store (w 2)
          (store (w 13)++(Encoding.natural.encode (store (w 0)).length).reverse++store (w 2))) := by
  obtain ⟨headerTime,headerBound,headerRun⟩:=External.CoverNormalization.emitReversedNatural_executes (extra+10) w.header store
    (by intro i member;simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl|rfl|rfl
        all_goals simp [MatrixWorkspace.header,matrixHeaderPositions,empty])
  let header:=Function.update store (w 2) ((Encoding.natural.encode (store (w 0)).length).reverse++store (w 2))
  have headerAs : Executes (External.CoverNormalization.emitReversedNatural (extra+10) w.header) store headerTime header := headerRun
  have copying:=copy_executes (extra+13) (w 13) (w 2) (w 4)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) header
    (by simp [header,w.injective.eq_iff,empty])
  have input : header (w 13)=store (w 13) := by simp [header,w.injective.eq_iff]
  rw [input] at copying
  have final : Function.update header (w 2) (store (w 13)++header (w 2))=
      Function.update store (w 2) (store (w 13)++(Encoding.natural.encode (store (w 0)).length).reverse++store (w 2)) := by
    simp [header,List.append_assoc]
  rw [final] at copying
  refine ⟨headerTime+1+(5*(store (w 13)).length+2),?_,headerAs.sequence copying⟩
  change headerTime ≤ 30*((store (w 0)).length+1)^2 at headerBound
  omega

end Counting.HardnessNetworkMachine
