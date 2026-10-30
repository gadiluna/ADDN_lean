import Counting.HardnessNetworkMachinePath
import Counting.HardnessNetworkMachineSerialize
import Counting.HardnessNetworkMachineDimensions
import Counting.ExternalCoefficientGeneratorState

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

/-- The first 64 registers retain the coefficient generator's established
layout. Network buffers occupy fresh registers and never hold agent IDs. -/
def coefficientRoles : External.CoefficientMachine.Workspace 32 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 96=>i.val) h)⟩

def dimensionRoles : Fin 7 ↪ Fin 96 := ⟨![27,25,64,65,67,68,69],by decide⟩

def leaderPositions : Fin 40 → Fin 96 := fun i=>
  if h : i.val<32 then ⟨i.val,by omega⟩ else ![65,64,67,66,68,70,71,72] ⟨i.val-32,by omega⟩
def leaderRoles : LeaderWorkspace 56 := ⟨leaderPositions,by decide⟩

def pathRoles : MatrixWorkspace 80 := ⟨![65,67,69,70,68,71,72,73,74,75,64,76,77,66,78,25],by decide⟩
def starRoles : MatrixWorkspace 80 := ⟨![65,67,79,70,68,71,72,73,74,75,64,76,77,66,78,25],by decide⟩
def serializationRoles : SerializeWorkspace 87 := ⟨![65,64,69,79,80,67,68,70,71],by decide⟩

def networkScratch : List (Fin 96) :=
  (List.finRange 96).filter (fun i=>i≠0 ∧ i≠1 ∧ i≠17 ∧ i≠25 ∧ i≠27 ∧ i≠31 ∧ i≠51 ∧ i≠52 ∧ i≠54)

@[simp] theorem mem_networkScratch (i : Fin 96) : i∈networkScratch ↔
    i≠0 ∧ i≠1 ∧ i≠17 ∧ i≠25 ∧ i≠27 ∧ i≠31 ∧ i≠51 ∧ i≠52 ∧ i≠54 := by simp [networkScratch]

def finishNetwork : Routine 94 := sequence (clear 1) (ofProgram (ListPrograms.reverseProgram 94 80 1))

theorem finishNetwork_executes (store : Store 94) (word : List Bool) (source : store 80=word.reverse)
    (status : store 1=[true]) :
    Executes finishNetwork store (2*word.length+4)
      (Function.update (Function.update store 80 []) 1 word) := by
  have clearing:=clear_executes (1:Fin 96) store
  rw [status] at clearing
  let cleared:=Function.update store 1 []
  have reversing:=reverse_executes 94 (80:Fin 96) 1 (by decide) cleared
  have sourceAt : cleared 80=word.reverse := by simp [cleared,source]
  rw [sourceAt,List.length_reverse] at reversing
  have final : Function.update (Function.update cleared 80 []) 1 (word.reverse.reverse++cleared 1)=
      Function.update (Function.update store 80 []) 1 word := by
    funext r
    by_cases e1 : r=1
    · subst r;simp [cleared]
    · simp [cleared,Function.update_apply,e1]
  rw [final] at reversing
  have combined:=clearing.sequence reversing
  have cost : [true].length+1+1+(2*word.length+1)=2*word.length+4 := by simp;omega
  rw [cost] at combined
  exact combined

end Counting.HardnessNetworkMachine
