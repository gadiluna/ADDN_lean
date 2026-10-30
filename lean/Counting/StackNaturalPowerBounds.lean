import Counting.StackNaturalPower

namespace Counting.StackMachine.NaturalPower
open Routine

theorem powerCost_polynomial (baseLength count : Nat) :
    count*(iterationCost baseLength count+2)+3 ≤ 3000000*(baseLength+count+1)^7 := by
  let size:=baseLength+count+1
  have positive : 1 ≤ size := by dsimp [size];omega
  have product : (count+1)*baseLength ≤ size^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (by dsimp [size];omega) (by dsimp [size];omega)
  have square : 1 ≤ size^2 := Nat.one_le_pow _ _ positive
  have argument : (count+1)*baseLength+2 ≤ 3*size^2 := by omega
  have cube : ((count+1)*baseLength+2)^3 ≤ 27*size^6 := by
    calc
      _ ≤ (3*size^2)^3 := Nat.pow_le_pow_left argument _
      _ = _ := by ring
  have countBound : count ≤ size := by dsimp [size];omega
  have first : count*(100000*((count+1)*baseLength+2)^3) ≤ size*(2700000*size^6) :=
    Nat.mul_le_mul countBound (by omega)
  have seventh : size^7=size*size^6 := pow_succ' _ _
  have linear : size ≤ size^7 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ size^7 := positive.trans linear
  change _ ≤ 3000000*size^7
  unfold iterationCost
  nlinarith

theorem powerRoutine_polynomial (extra : Nat) (w : Workspace extra) (store : Fin (extra+15) → List Bool)
    (count : Nat) (counter : store (w 13)=List.replicate count true)
    (empty : ∀ i : Fin 15,i≠0 → i≠13 → store (w i)=[]) :
    ∃ time ≤ 3000000*((store (w 0)).length+count+1)^7,
      Executes (powerRoutine extra w) store time
        (Function.update (Function.update store (w 13) []) (w 1) (Encoding.value (store (w 0))^count).bits) := by
  obtain ⟨time,bound,ran⟩:=powerRoutine_executes extra w store count counter empty
  exact ⟨time,bound.trans (powerCost_polynomial _ _),ran⟩

end Counting.StackMachine.NaturalPower
