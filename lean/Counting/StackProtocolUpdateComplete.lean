import Counting.StackProtocolUpdateCanonical
import Counting.StackRoutineIsolateHalt

namespace Counting.StackMachine.ProtocolUpdate
open Routine NetworkComplement Executable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

def completeRaw : Routine 158 := sequence prepare (sequence rawStage (sequence canonicalCall finish))
def completeRawCoefficient : Nat := rawStageCoefficient+
  (12*DagUpdate.Canonical.completeCanonicalCoefficient+40)*1761^136+100

private theorem cost_arithmetic (R C P S N a b c output : Nat) (linear : N≤S) (positive : 1≤S)
    (first : a≤10*N) (raw : b≤R*S) (canonical : c≤(7*C+30)*P*S)
    (encoded : output≤(C+1)*P*S) :
    a+1+(b+1+(c+1+(5*output+4)))≤(R+(12*C+40)*P+100)*S := by
  simp only [Nat.add_mul,Nat.mul_assoc] at *
  omega

private theorem cleanup_cost (C N S : Nat) (linear : N+1≤S) :
    161*(C*S+N+3)≤161*(C+4)*S := by
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc] at *
  omega

theorem completeRaw_executes (old : Vista) (messages : List (Vista×Nat)) (degree : Nat)
    (valid : old.valid=true)
    (received : ∀m∈messages,m.1.valid=true ∧ 0 < m.2 ∧
      (m.1.node m.1.bottom).level=(old.node old.bottom).level) :
    ∃time output,time≤completeRawCoefficient*((inputWord old messages degree).length+1)^272 ∧
      Executes completeRaw (inputStore 158 (inputWord old messages degree)) time output ∧
      output 1=outputWord (updateVista? old messages degree) := by
  obtain ⟨tp,bp,rp⟩:=prepare_executes old messages degree
  obtain ⟨tr,br,rr⟩:=rawStage_executes old messages degree valid
    (fun m member=>⟨(received m member).1,(received m member).2.2⟩)
  obtain ⟨tc,bc,rc,outBound⟩:=canonicalCall_executes old messages degree valid received
  obtain ⟨output,rf,answer⟩:=finish_executes (canonicalData old messages degree)
    (canonicalize (rawUpdate old messages degree)) (by simp [canonicalData])
  have defined:=updateVista_defined old messages degree valid (by
    apply List.all_eq_true.mpr
    intro m member
    obtain ⟨good,positive,same⟩:=received m member
    simp [good,positive,same])
  rw [←defined] at answer
  let N:=(inputWord old messages degree).length+1
  have positive:1≤N:=by dsimp [N];omega
  have rawLength:=rawUpdate_encoding_length old messages degree valid
    (fun m member=>⟨(received m member).1,(received m member).2.2⟩)
  have squarePositive:1≤N^2:=one_le_pow₀ positive
  have base:(Encoding.vista.encode (rawUpdate old messages degree)).length+1≤1761*N^2 := by
    change _≤1760*N^2 at rawLength
    omega
  have powered:=Nat.pow_le_pow_left base 136
  rw [Nat.mul_pow,←Nat.pow_mul] at powered
  change ((Encoding.vista.encode (rawUpdate old messages degree)).length+1)^136≤1761^136*N^272 at powered
  have canonicalBound:tc≤(7*DagUpdate.Canonical.completeCanonicalCoefficient+30)*1761^136*N^272 := by
    exact bc.trans (by simpa only [canonicalCallCoefficient,Nat.mul_assoc] using
      Nat.mul_le_mul_left canonicalCallCoefficient powered)
  have encodedBound:(Encoding.vista.encode (canonicalize (rawUpdate old messages degree))).length≤
      (DagUpdate.Canonical.completeCanonicalCoefficient+1)*1761^136*N^272 := by
    exact outBound.trans (by simpa only [Nat.mul_assoc] using
      (Nat.mul_le_mul_left (DagUpdate.Canonical.completeCanonicalCoefficient+1) powered))
  have rawBound:=br.trans (Nat.mul_le_mul_left rawStageCoefficient
    (Nat.pow_le_pow_right positive (by decide : 61≤272)))
  have first:tp≤10*N := by dsimp [N];omega
  have total:=cost_arithmetic rawStageCoefficient DagUpdate.Canonical.completeCanonicalCoefficient
    (1761^136) (N^272) N tp tr tc _ (Nat.le_self_pow (by decide) _) (one_le_pow₀ positive)
    first rawBound canonicalBound encodedBound
  exact ⟨_,output,total,rp.sequence (rr.sequence (rc.sequence rf)),answer⟩

def complete : Routine 158 := isolate completeRaw
def completeCoefficient : Nat := 161*(completeRawCoefficient+4)

/-- Exact executable updater for every physically admissible local input.
Round and leader metadata are read from the old DAG; the raw merge and the
complete canonicalizer run as concrete programs, and every work cell is erased. -/
theorem complete_executes (old : Vista) (messages : List (Vista×Nat)) (degree : Nat)
    (valid : old.valid=true)
    (received : ∀m∈messages,m.1.valid=true ∧ 0 < m.2 ∧
      (m.1.node m.1.bottom).level=(old.node old.bottom).level) :
    ∃time≤completeCoefficient*((inputWord old messages degree).length+1)^272,
      Executes complete (inputStore 158 (inputWord old messages degree)) time
        (outputStore 158 (outputWord (updateVista? old messages degree))) := by
  obtain ⟨steps,output,bounded,run,value⟩:=completeRaw_executes old messages degree valid received
  obtain ⟨last,ran,halted,stored⟩:=run
  have halts:∃time last,time≤completeRawCoefficient*((inputWord old messages degree).length+1)^272 ∧
      HaltsAt completeRaw.program (inputWord old messages degree) time last ∧
      last.store 1=outputWord (updateVista? old messages degree) :=
    ⟨steps,last,bounded,⟨ran,halted⟩,by rw [stored];exact value⟩
  obtain ⟨time,bound,execution⟩:=isolate_halts completeRaw (inputWord old messages degree)
    (outputWord (updateVista? old messages degree)) _ halts
  have linear:(inputWord old messages degree).length+1≤((inputWord old messages degree).length+1)^272:=
    Nat.le_self_pow (by decide) _
  refine ⟨time,bound.trans ?_,execution⟩
  exact cleanup_cost completeRawCoefficient (inputWord old messages degree).length _ linear

end Counting.StackMachine.ProtocolUpdate
