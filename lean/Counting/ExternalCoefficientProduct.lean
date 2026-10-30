import Counting.ExternalCoefficientBase

namespace Counting.External.CoefficientMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def productPositions : Fin 13 ↪ Fin 64 := ⟨![56,54,55,2,3,4,5,6,7,8,9,10,11],by decide⟩
def Workspace.productRoles (w : Workspace extra) : Fin 13 ↪ Fin (extra+64) := productPositions.trans w

def productScratch : List (Fin 64) := [2,3,4,5,6,7,8,9,10,11,20,26,55,56]

def prepareProduct (extra : Nat) (w : Workspace extra) : Routine (extra+62) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 27) (w 26) (w 20)))
    (sequence (ofProgram (Unary.toBinaryProgram (extra+61) (w 26) (w 56) (w 20)))
      (sequence (relocate NaturalCall.multiplicationRoutine w.productRoles) (clear (w 56))))

theorem prepareProduct_executes (extra : Nat) (w : Workspace extra) (store : Fin (extra+64) → List Bool)
    (q : Nat) (counter : store (w 27)=List.replicate q true) (empty : ∀ i∈productScratch,store (w i)=[]) :
    ∃ time ≤ 100000*(q+(store (w 54)).length+1)^3,
      Executes (prepareProduct extra w) store time
        (Function.update store (w 55) (q*Encoding.value (store (w 54))).bits) := by
  have copying:=copy_executes (extra+61) (w 27) (w 26) (w 20)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store (empty 20 (by decide))
  rw [counter,empty 26 (by decide),List.append_nil,List.length_replicate] at copying
  let copied:=Function.update store (w 26) (List.replicate q true)
  obtain ⟨convertTime,convertBound,converting⟩:=toBinary_executes (extra+61) (w 26) (w 56) (w 20)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) copied 0
    (by simp [copied,w.injective.eq_iff,empty,productScratch])
    (by simp [copied,w.injective.eq_iff,empty,productScratch])
  have counterAt : copied (w 26)=List.replicate q true := by simp [copied]
  rw [counterAt,List.length_replicate,Nat.zero_add] at convertBound converting
  let binary:=Function.update store (w 56) q.bits
  have convertedFinal : Function.update (Function.update copied (w 26) []) (w 56) q.bits=binary := by
    funext r
    by_cases e26 : r=w 26
    · subst r;simp [binary,w.injective.eq_iff,empty,productScratch]
    · simp [binary,copied,Function.update_apply,e26]
  rw [convertedFinal] at converting
  obtain ⟨multiplyTime,multiplyBound,multiplyRun⟩:=NaturalCall.multiplication_executes q.bits (store (w 54))
  have restricted : binary ∘ w.productRoles=NaturalCall.file q.bits (store (w 54)) [] [] [] [] [] := by
    funext r;fin_cases r <;> simp [binary,Workspace.productRoles,productPositions,NaturalCall.file,w.injective.eq_iff,empty,productScratch]
  have multiplying:=NaturalCall.callAt_executes NaturalCall.multiplicationRoutine w.productRoles binary _ _ _ multiplyTime restricted multiplyRun
  rw [Encoding.value_bits] at multiplying
  let multiplied:=Function.update binary (w 55) (q*Encoding.value (store (w 54))).bits
  change Executes (relocate NaturalCall.multiplicationRoutine w.productRoles) binary multiplyTime multiplied at multiplying
  have clearing:=clear_executes (w 56) multiplied
  have magnitudeAt : multiplied (w 56)=q.bits := by simp [multiplied,binary,w.injective.eq_iff]
  rw [magnitudeAt] at clearing
  have final : Function.update multiplied (w 56) []=Function.update store (w 55) (q*Encoding.value (store (w 54))).bits := by
    funext r
    by_cases e56 : r=w 56
    · subst r;simp [w.injective.eq_iff,empty,productScratch]
    · simp [multiplied,binary,Function.update_apply,e56]
  rw [final] at clearing
  refine ⟨5*q+2+1+(convertTime+1+(multiplyTime+1+(q.bits.length+1))),?_,copying.sequence (converting.sequence (multiplying.sequence clearing))⟩
  let size:=q+(store (w 54)).length+1
  have bitsBound : q.bits.length ≤ q := by
    rw [Encoding.bits_length_le_iff]
    exact Nat.lt_two_pow_self
  have positive : 1 ≤ size := by dsimp [size];omega
  have linear : size ≤ size^3 := Nat.le_self_pow (by decide) _
  have square : size^2 ≤ size^3 := Nat.pow_le_pow_right positive (by decide)
  have product : q*(q+1) ≤ size^2 := by
    rw [pow_two]
    apply Nat.mul_le_mul <;> dsimp [size] <;> omega
  have multiplyLimit : multiplyTime ≤ 82000*size^3 :=
    multiplyBound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [size];omega) _))
  change _ ≤ 100000*size^3
  dsimp only [size] at linear square product multiplyLimit ⊢
  nlinarith

end Counting.External.CoefficientMachine
