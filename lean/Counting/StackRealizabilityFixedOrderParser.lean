import Counting.StackRealizabilityFixedOrderSpec
import Counting.StackRealizabilitySyntaxCall

namespace Counting.StackMachine.FixedOrderRecognition
open Routine RealizabilityCall VistaComplement EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000

def inputParser : VerifiedParser 15 0 1 2 (Executable.Vista×Nat×Nat) Encoding.fixedOrderInput :=
  DagParser.vista.product (by decide) (by decide) (by decide)
    (DagParser.natural.product (by decide) (by decide) (by decide) DagParser.natural)

def witnessParser := DagParser.naturals

def syntaxChecks : Routine 128 := sequence (syntaxCall inputParser.recognition 8)
  (syntaxCall witnessParser.recognition 9)

def syntaxCoefficient : Nat := 18*(inputParser.coefficient+witnessParser.coefficient+40)+200

def syntaxAccepted (input witness : List Bool) : Bool :=
  (Encoding.fixedOrderInput.decodeExact input).isSome && ((Encoding.list Encoding.natural).decodeExact witness).isSome

theorem syntaxChecks_executes (data : Fin 30→List Bool) (accepted : Bool) (tail : List Bool)
    (status : data 4=accepted::tail) :
    ∃time≤Complexity.polynomial syntaxCoefficient 25 ((data 8).length+(data 9).length),
      Executes syntaxChecks (file data) time
        (file (Function.update data 4 ((accepted && syntaxAccepted (data 8) (data 9))::tail))) := by
  obtain ⟨t0,b0,r0⟩ := syntaxCall_executes inputParser.recognition _ _ _ inputParser.recognition_computes
    data 8 accepted tail status
  let pass := (Encoding.fixedOrderInput.decodeExact (data 8)).isSome
  let d1 := Function.update data 4 ((accepted && pass)::tail)
  obtain ⟨t1,b1,r1⟩ := syntaxCall_executes witnessParser.recognition _ _ _ witnessParser.recognition_computes
    d1 9 (accepted && pass) tail (by simp [d1])
  have final : Function.update d1 4
      (((accepted && pass) && ((Encoding.list Encoding.natural).decodeExact (d1 9)).isSome)::tail)=
      Function.update data 4 ((accepted && syntaxAccepted (data 8) (data 9))::tail) := by
    simp [d1,pass,syntaxAccepted,Bool.and_assoc]
  rw [final] at r1
  let L := (data 8).length+(data 9).length
  have small0 : (data 8).length+1≤L+1 := by dsimp only [L];omega
  have small1 : (d1 9).length+1≤L+1 := by simp only [d1,Function.update_of_ne (show (9:Fin 30)≠4 by decide)];dsimp only [L];omega
  have pow0 : ((data 8).length+1)^(max 1 inputParser.exponent)≤(L+1)^25 :=
    (Nat.pow_le_pow_left small0 _).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have pow1 : ((d1 9).length+1)^(max 1 witnessParser.exponent)≤(L+1)^25 :=
    (Nat.pow_le_pow_left small1 _).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have term0 := Nat.mul_le_mul_left (18*(inputParser.coefficient+20)) pow0
  have term1 := Nat.mul_le_mul_left (18*(witnessParser.coefficient+20)) pow1
  have linear : L+1≤(L+1)^25 := Nat.le_self_pow (by decide) _
  refine ⟨_,?_,r0.sequence r1⟩
  change t0+1+t1≤ syntaxCoefficient*(L+1)^25
  simp only [Complexity.polynomial,Nat.mul_assoc,Nat.add_mul,Nat.mul_add] at b0 b1 term0 term1
  simp only [d1,Function.update_of_ne (show (9:Fin 30)≠4 by decide)] at b1 term1
  unfold syntaxCoefficient
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
  have base : L=(data 8).length+(data 9).length := rfl
  omega

end Counting.StackMachine.FixedOrderRecognition
