import Counting.StackNaturalPowerBounds
import Counting.StackRealizabilityAccumulate

namespace Counting.StackMachine.NaturalPower
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

abbrev SumWorkspace (extra : Nat) := Fin 18 ↪ Fin (extra+18)
def powerPositions : Fin 15 ↪ Fin 18 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 18=>i.val) h)⟩
def SumWorkspace.power (w : SumWorkspace extra) : Workspace (extra+3) := powerPositions.trans w
def sumPositions : Fin 4 ↪ Fin 18 := ⟨![15,1,16,17],by decide⟩
def SumWorkspace.sumRoles (w : SumWorkspace extra) : Fin 4 ↪ Fin (extra+18) := sumPositions.trans w

def accumulatePower (extra : Nat) (w : SumWorkspace extra) : Routine (extra+16) :=
  sequence (powerRoutine (extra+3) w.power) (RealizabilityCheck.accumulateAt w.sumRoles)

def accumulatePowerCost (baseLength sumLength count : Nat) :=
  count*(iterationCost baseLength count+2)+4+11*(sumLength+count*baseLength+1)+20

theorem accumulatePower_executes (extra : Nat) (w : SumWorkspace extra) (store : Fin (extra+18) → List Bool)
    (count : Nat) (counter : store (w 13)=List.replicate count true)
    (empty : ∀ i : Fin 18,i≠0 → i≠13 → i≠15 → store (w i)=[]) :
    ∃ time ≤ accumulatePowerCost (store (w 0)).length (store (w 15)).length count,
      Executes (accumulatePower extra w) store time
        (Function.update (Function.update store (w 13) []) (w 15)
          (Encoding.value (store (w 15))+Encoding.value (store (w 0))^count).bits) := by
  have powerEmpty (i : Fin 15) (n0 : i≠0) (n13 : i≠13) : store (w.power i)=[] := by
    have a : powerPositions i≠0 := by intro same;apply n0;exact Fin.ext (congrArg (fun j : Fin 18=>j.val) same)
    have b : powerPositions i≠13 := by intro same;apply n13;exact Fin.ext (congrArg (fun j : Fin 18=>j.val) same)
    have c : powerPositions i≠15 := by
      intro same;have value:=congrArg (fun j : Fin 18=>j.val) same;norm_num [powerPositions] at value;omega
    exact empty (powerPositions i) a b c
  obtain ⟨powerTime,powerBound,powering⟩:=powerRoutine_executes (extra+3) w.power store count counter powerEmpty
  let powered:=Function.update (Function.update store (w 13) []) (w 1) (Encoding.value (store (w 0))^count).bits
  change Executes (powerRoutine (extra+3) w.power) store powerTime powered at powering
  change powerTime ≤ count*(iterationCost (store (w 0)).length count+2)+3 at powerBound
  obtain ⟨sumTime,sumBound,summing⟩:=RealizabilityCheck.accumulateAt_executes w.sumRoles powered
    (by simp [SumWorkspace.sumRoles,sumPositions,powered,w.injective.eq_iff,empty])
    (by simp [SumWorkspace.sumRoles,sumPositions,powered,w.injective.eq_iff,empty])
  have firstAt : powered (w.sumRoles 0)=store (w 15) := by simp [SumWorkspace.sumRoles,sumPositions,powered,w.injective.eq_iff]
  have secondAt : powered (w.sumRoles 1)=(Encoding.value (store (w 0))^count).bits := by simp [SumWorkspace.sumRoles,sumPositions,powered]
  rw [firstAt,secondAt,Encoding.value_bits] at summing
  rw [firstAt,secondAt] at sumBound
  change Executes (RealizabilityCheck.accumulateAt w.sumRoles) powered sumTime
    (Function.update (Function.update powered (w 15)
      (Encoding.value (store (w 15))+Encoding.value (store (w 0))^count).bits) (w 1) []) at summing
  have final : Function.update (Function.update powered (w 15)
      (Encoding.value (store (w 15))+Encoding.value (store (w 0))^count).bits) (w 1) []=
      Function.update (Function.update store (w 13) []) (w 15)
      (Encoding.value (store (w 15))+Encoding.value (store (w 0))^count).bits := by
    funext r
    by_cases e1 : r=w 1
    · subst r;simp [w.injective.eq_iff,empty]
    · simp [powered,Function.update_apply,e1]
  rw [final] at summing
  refine ⟨powerTime+1+sumTime,?_,powering.sequence summing⟩
  have bitsBound:=power_bits_length (store (w 0)) count
  unfold accumulatePowerCost
  omega

end Counting.StackMachine.NaturalPower
