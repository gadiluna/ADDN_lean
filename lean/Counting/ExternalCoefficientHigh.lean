import Counting.ExternalCoefficientBase

namespace Counting.External.CoefficientMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def highScratch : List (Fin 64) := [2,3,4,5,6,7,8,9,10,11,12,20,26,53,54]

def prepareHigh (extra : Nat) (w : Workspace extra) : Routine (extra+62) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 17) (w 26) (w 20)))
    (sequence (NaturalPower.powerRoutine (extra+49) w.powerSum.power)
      (move (extra+61) (w 53) (w 54) (w 20)))

def highCost (baseLength count : Nat) :=
  5*count+2+1+(count*(NaturalPower.iterationCost baseLength count+2)+3+1+
    (6*(count*baseLength+1)+4))

theorem prepareHigh_executes (extra : Nat) (w : Workspace extra) (store : Fin (extra+64) → List Bool)
    (count : Nat) (universeInput : store (w 17)=List.replicate count true)
    (empty : ∀ i∈highScratch,store (w i)=[]) :
    ∃ time ≤ highCost (store (w 52)).length count,
      Executes (prepareHigh extra w) store time
        (Function.update store (w 54) (Encoding.value (store (w 52))^count).bits) := by
  have copying:=copy_executes (extra+61) (w 17) (w 26) (w 20)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store (empty 20 (by decide))
  rw [universeInput,empty 26 (by decide),List.append_nil,List.length_replicate] at copying
  let copied:=Function.update store (w 26) (List.replicate count true)
  have powerEmpty (i : Fin 15) (n0 : i≠0) (n13 : i≠13) : copied (w.powerSum.power i)=[] := by
    fin_cases i
    all_goals first | contradiction | simp [NaturalPower.SumWorkspace.power,NaturalPower.powerPositions,
      Workspace.powerSum,powerSumPositions,copied,w.injective.eq_iff,empty,highScratch]
  obtain ⟨powerTime,powerBound,powering⟩:=NaturalPower.powerRoutine_executes (extra+49) w.powerSum.power copied count
    (by simp [NaturalPower.SumWorkspace.power,NaturalPower.powerPositions,Workspace.powerSum,powerSumPositions,copied]) powerEmpty
  have baseAt : copied (w.powerSum.power 0)=store (w 52) := by
    simp [NaturalPower.SumWorkspace.power,NaturalPower.powerPositions,Workspace.powerSum,powerSumPositions,copied,w.injective.eq_iff]
  rw [baseAt] at powerBound powering
  let result:=(Encoding.value (store (w 52))^count).bits
  let powered:=Function.update store (w 53) result
  have poweredFinal : Function.update (Function.update copied (w.powerSum.power 13) []) (w.powerSum.power 1) result=powered := by
    change Function.update (Function.update copied (w 26) []) (w 53) result=powered
    funext r
    by_cases e26 : r=w 26
    · subst r;simp [powered,w.injective.eq_iff,empty,highScratch]
    · simp [powered,copied,Function.update_apply,e26]
  rw [poweredFinal] at powering
  have moving:=move_executes (extra+61) (w 53) (w 54) (w 20)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) powered
    (by simp [powered,w.injective.eq_iff,empty,highScratch])
  have sourceAt : powered (w 53)=result := by simp [powered]
  have target : powered (w 54)=[] := by simp [powered,w.injective.eq_iff,empty,highScratch]
  rw [sourceAt,target,List.append_nil] at moving
  have final : Function.update (Function.update powered (w 54) result) (w 53) []=Function.update store (w 54) result := by
    funext r
    by_cases e53 : r=w 53
    · subst r;simp [w.injective.eq_iff,empty,highScratch]
    · simp [powered,Function.update_apply,e53]
  rw [final] at moving
  refine ⟨5*count+2+1+(powerTime+1+(6*result.length+4)),?_,copying.sequence (powering.sequence moving)⟩
  have bitsBound:=NaturalPower.power_bits_length (store (w 52)) count
  unfold highCost
  dsimp only [result] at *
  omega

end Counting.External.CoefficientMachine
