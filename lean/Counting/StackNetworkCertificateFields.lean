import Counting.StackNetworkCertificateParser
import Counting.StackRealizabilityVistaRead

namespace Counting.StackMachine.NetworkCertificate
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def inputFields : Routine 128 := sequence (VistaComplement.readField DagParser.natural 2)
  (sequence (VistaComplement.readField viewsParser 10) (VistaComplement.readField certificatesParser 11))

def inputFieldsData (data : Fin 30→List Bool) (input : Counting.NetworkCertificate.Input) : Fin 30→List Bool :=
  Function.update (Function.update (Function.update (Function.update data 5 [])
    2 (Encoding.natural.encode input.1)) 10 ((Encoding.list Encoding.vista).encode input.2.1))
      11 (Encoding.networkWitness.encode input.2.2)

theorem inputFields_executes (data : Fin 30→List Bool) (input : Counting.NetworkCertificate.Input)
    (accepted : Bool) (tail : List Bool) (status : data 4=accepted::tail)
    (source : data 5=Counting.NetworkCertificate.codec.encode input)
    (e2 : data 2=[]) (e10 : data 10=[]) (e11 : data 11=[]) :
    ∃ time ≤ 65000*((data 5).length+1)^5,
      Executes inputFields (file data) time (file (inputFieldsData data input)) := by
  let vc := (Encoding.list Encoding.vista).encode input.2.1
  let cc := Encoding.networkWitness.encode input.2.2
  have sourceEq : data 5=Encoding.natural.encode input.1++(vc++cc) := source
  obtain ⟨t0,b0,r0⟩ := VistaComplement.readField_executes DagParser.natural data 2
    (by decide) (by decide) input.1 (vc++cc) accepted tail sourceEq status e2
  let d1 := Function.update (Function.update data 5 (vc++cc)) 2 (Encoding.natural.encode input.1)
  obtain ⟨t1,b1,r1⟩ := VistaComplement.readField_executes viewsParser d1 10
    (by decide) (by decide) input.2.1 cc accepted tail
    (by simp [d1,vc]) (by simp [d1,status]) (by simp [d1,e10])
  let d2 := Function.update (Function.update d1 5 cc) 10 vc
  obtain ⟨t2,b2,r2⟩ := VistaComplement.readField_executes certificatesParser d2 11
    (by decide) (by decide) input.2.2 [] accepted tail
    (by simp [d2,cc]) (by simp [d2,d1,status]) (by simp [d2,d1,e11])
  have final : Function.update (Function.update d2 5 []) 11 cc=inputFieldsData data input := by
    funext r
    by_cases r2:r=2 <;> by_cases r5:r=5 <;> by_cases r10:r=10 <;> by_cases r11:r=11 <;>
      simp [d2,d1,inputFieldsData,r2,r5,r10,r11,vc,cc]
  rw [final] at r2
  let L := (data 5).length
  have lengths : L=(Encoding.natural.encode input.1).length+vc.length+cc.length := by
    dsimp [L];rw [sourceEq];simp only [List.length_append];omega
  have firstDegree : DagParser.natural.exponent≤5 := by decide
  have firstCoeff : DagParser.natural.coefficient≤20000 := by decide
  have base : 1≤L+1 := by omega
  have budget (c k n p : Nat) (bc:c≤20000) (bk:k≤5) (bn:n≤L) (bp:p≤L) :
      Complexity.polynomial c k n+2*p+2≤20003*(L+1)^5 := by
    have powers := (Nat.pow_le_pow_left (Nat.add_le_add_right bn 1) k).trans
      (Nat.pow_le_pow_right base bk)
    have product := Nat.mul_le_mul bc powers
    have linear : L+1≤(L+1)^5 := Nat.le_self_pow (by decide) _
    unfold Complexity.polynomial
    nlinarith only [product,linear,bp]
  have cost0 := b0.trans (budget _ _ _ _ firstCoeff firstDegree (by rfl) (by omega))
  have cost1 := b1.trans (budget _ _ _ _ viewsParser_coefficient viewsParser_exponent
    (by simp only [d1,Function.update_of_ne (show (5:Fin 30)≠2 by decide),Function.update_self,List.length_append];omega)
    (by change vc.length≤L;omega))
  have cost2 := b2.trans (budget _ _ _ _ certificatesParser_coefficient certificatesParser_exponent
    (by simp only [d2,Function.update_of_ne (show (5:Fin 30)≠10 by decide),Function.update_self];omega)
    (by change cc.length≤L;omega))
  have one : 1≤(L+1)^5 := Nat.one_le_pow _ _ base
  exact ⟨_,by change t0+1+(t1+1+t2)≤65000*(L+1)^5;omega,r0.sequence (r1.sequence r2)⟩

end Counting.StackMachine.NetworkCertificate
