import Counting.ExternalCoefficientAtom
import Counting.X3CInstance
import Counting.StackRoutineUnary

namespace Counting.External.CoefficientMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def geometric (base start : Nat) : Nat → Nat
  | 0=>0
  | count+1=>base^start+geometric base (start+1) count

theorem geometric_eq_sum (base start count : Nat) : geometric base start count=∑ i : Fin count,base^(start+i.val) := by
  induction count generalizing start with
  | zero=>simp [geometric]
  | succ count ih=>
    rw [geometric,Fin.sum_univ_succ,ih]
    simp [Fin.val_succ,Nat.add_left_comm,Nat.add_comm]

theorem geometric_ones (q : Nat) : geometric (X3C.base q) 0 (3*q)=X3C.ones q := by
  rw [geometric_eq_sum]
  simp [X3C.ones,X3C.digitValue]

def geometricScratch : List (Fin 64) := [2,3,4,5,6,7,8,9,10,11,12,20,26,29,30,53]

def geometricStep (extra : Nat) (w : Workspace extra) : Routine (extra+62) :=
  sequence (ofProgram (Unary.lengthProgram (extra+61) (w 37) (w 26) (w 20)))
    (sequence (NaturalPower.accumulatePower (extra+46) w.powerSum) (pushBit (w 37) true))

def geometricStepCost (baseLength sumLength exponent : Nat) :=
  5*exponent+2+1+(NaturalPower.accumulatePowerCost baseLength sumLength exponent+1+1)

theorem geometricStep_executes (extra : Nat) (w : Workspace extra) (store : Fin (extra+64) → List Bool)
    (empty : ∀ i∈geometricScratch,store (w i)=[]) :
    ∃ time ≤ geometricStepCost (store (w 52)).length (store (w 55)).length (store (w 37)).length,
      Executes (geometricStep extra w) store time
        (Function.update (Function.update store (w 55)
          (Encoding.value (store (w 55))+Encoding.value (store (w 52))^(store (w 37)).length).bits)
          (w 37) (true::store (w 37))) := by
  have copying:=length_executes (extra+61) (w 37) (w 26) (w 20)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store (empty 20 (by decide))
  rw [empty 26 (by decide),List.append_nil] at copying
  let copied:=Function.update store (w 26) (List.replicate (store (w 37)).length true)
  have powerEmpty (i : Fin 18) (n0 : i≠0) (n13 : i≠13) (n15 : i≠15) : copied (w.powerSum i)=[] := by
    fin_cases i
    all_goals first | contradiction | simp [Workspace.powerSum,powerSumPositions,copied,w.injective.eq_iff,empty,geometricScratch]
  obtain ⟨powerTime,powerBound,powering⟩:=NaturalPower.accumulatePower_executes (extra+46) w.powerSum copied (store (w 37)).length
    (by simp [Workspace.powerSum,powerSumPositions,copied]) powerEmpty
  have baseAt : copied (w.powerSum 0)=store (w 52) := by simp [Workspace.powerSum,powerSumPositions,copied,w.injective.eq_iff]
  have sumAt : copied (w.powerSum 15)=store (w 55) := by simp [Workspace.powerSum,powerSumPositions,copied,w.injective.eq_iff]
  rw [baseAt,sumAt] at powerBound powering
  let value:=(Encoding.value (store (w 55))+Encoding.value (store (w 52))^(store (w 37)).length).bits
  let powered:=Function.update store (w 55) value
  have poweredFinal : Function.update (Function.update copied (w.powerSum 13) []) (w.powerSum 15) value=powered := by
    change Function.update (Function.update copied (w 26) []) (w 55) value=powered
    funext r
    by_cases e26 : r=w 26
    · subst r;simp [powered,w.injective.eq_iff,empty,geometricScratch]
    · simp [powered,copied,Function.update_apply,e26]
  rw [poweredFinal] at powering
  have pushing:=pushBit_executes (w 37) true powered
  have indexAt : powered (w 37)=store (w 37) := by simp [powered,w.injective.eq_iff]
  rw [indexAt] at pushing
  refine ⟨5*(store (w 37)).length+2+1+(powerTime+1+1),?_,copying.sequence (powering.sequence pushing)⟩
  unfold geometricStepCost
  omega

end Counting.External.CoefficientMachine
