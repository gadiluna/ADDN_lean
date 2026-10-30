import Counting.StackRealizabilityOrderFields

namespace Counting.StackMachine.VistaComplement
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def witnessFields : Routine 128 := sequence (orderFields 3 1) (orderFields 6 7)

def witnessFieldsData (data : Fin 30→List Bool) (first second : Nat) (a b : List Nat) : Fin 30→List Bool :=
  orderFieldsData (orderFieldsData data 3 1 first a (Encoding.orderWitness.encode (second,b))) 6 7 second b []

theorem witnessFields_executes (data : Fin 30→List Bool) (first second : Nat) (a b : List Nat)
    (accepted : Bool) (tail : List Bool) (status : data 4=accepted::tail)
    (source : data 5=Encoding.twoOrderWitness.encode ((first,a),(second,b)))
    (emptyFirst : data 3=[]) (emptyA : data 1=[]) (emptySecond : data 6=[]) (emptyB : data 7=[]) :
    ∃ time ≤ 16300*((Encoding.twoOrderWitness.encode ((first,a),(second,b))).length+1)^4,
      Executes witnessFields (file data) time (file (witnessFieldsData data first second a b)) := by
  obtain ⟨t0,b0,r0⟩ := orderFields_executes data 3 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    first a (Encoding.orderWitness.encode (second,b)) accepted tail status source emptyFirst emptyA
  let middle := orderFieldsData data 3 1 first a (Encoding.orderWitness.encode (second,b))
  obtain ⟨t1,b1,r1⟩ := orderFields_executes middle 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)
    second b [] accepted tail (by simp [middle,orderFieldsData,status])
      (by simp [middle,orderFieldsData]) (by simp [middle,orderFieldsData,emptySecond])
      (by simp [middle,orderFieldsData,emptyB])
  let L := (Encoding.twoOrderWitness.encode ((first,a),(second,b))).length
  have small : (middle 5).length ≤ L := by
    simp only [middle,orderFieldsData,Function.update_of_ne (show (5:Fin 30)≠1 by decide),Function.update_self]
    change _ ≤ (Encoding.orderWitness.encode (first,a)++Encoding.orderWitness.encode (second,b)).length
    rw [List.length_append];omega
  rw [source] at b0
  change t0 ≤ 8100*(L+1)^4 at b0
  have bound1 : t1 ≤ 8100*(L+1)^4 := b1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4))
  have one : 1 ≤ (L+1)^4 := Nat.one_le_pow _ _ (by omega)
  refine ⟨_,?_,r0.sequence r1⟩
  change t0+1+t1 ≤ 16300*(L+1)^4
  omega

end Counting.StackMachine.VistaComplement
