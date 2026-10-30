import Counting.StackProtocolUpdateBounds

namespace Counting.StackMachine.ProtocolUpdate
open Routine NetworkComplement Executable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

def metadataData (old : Vista) (messages : List (Vista×Nat)) (degree : Nat) : Fin 30→List Bool :=
  Function.update (preparedData old messages degree) 3 (ProtocolBottom.outputWord old)

def assembledData (old : Vista) (messages : List (Vista×Nat)) (degree : Nat) : Fin 30→List Bool :=
  Function.update (metadataData old messages degree) 4 (rawWord old messages degree)

def rawData (old : Vista) (messages : List (Vista×Nat)) (degree : Nat) : Fin 30→List Bool :=
  Function.update (assembledData old messages degree) 5 (Encoding.vista.encode (rawUpdate old messages degree))

def rawCall : Routine 158 := call DagUpdate.Raw.complete (by decide) 4 5
def rawStage : Routine 158 := sequence metadata (sequence assemble rawCall)
def rawStageCoefficient : Nat := DagUpdate.Raw.completeCoefficient*4^61+1200000

theorem assemble_metadata (old : Vista) (messages : List (Vista×Nat)) (degree : Nat) :
    Executes assemble (file (metadataData old messages degree))
      (5*(rawWord old messages degree).length+11) (file (assembledData old messages degree)) := by
  have run:=assemble_executes (metadataData old messages degree) (by simp [metadataData,preparedData])
  have h0:metadataData old messages degree 0=Encoding.vista.encode old := by simp [metadataData,preparedData]
  have h1:metadataData old messages degree 1=(Encoding.list DagUpdate.Receive.messageCodec).encode messages := by simp [metadataData,preparedData]
  have h2:metadataData old messages degree 2=Encoding.natural.encode degree := by simp [metadataData,preparedData]
  have h3:metadataData old messages degree 3=ProtocolBottom.outputWord old := by simp [metadataData]
  rw [h0,h1,h2,h3] at run
  simpa only [assembledData,rawWord_eq,List.length_append,List.append_assoc,
    Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using run

/-- The old vista supplies its own round and leader bit; every message
import and the subsequent fresh-node construction is an actual routine. -/
theorem rawStage_executes (old : Vista) (messages : List (Vista×Nat)) (degree : Nat)
    (valid : old.valid=true)
    (received : ∀m∈messages,m.1.valid=true ∧ (m.1.node m.1.bottom).level=(old.node old.bottom).level) :
    ∃time≤rawStageCoefficient*((inputWord old messages degree).length+1)^61,
      Executes rawStage (file (preparedData old messages degree)) time (file (rawData old messages degree)) := by
  obtain ⟨tm,bm,rm⟩:=metadata_executes old messages degree valid
  have ra:=assemble_metadata old messages degree
  obtain ⟨tr,br,rr⟩:=DagUpdate.Raw.complete_polynomial (old.node old.bottom).level
    (old.node old.bottom).leader degree old messages
  rw [DagUpdate.Raw.updated_eq_rawUpdate _ _ _ _ _ valid rfl rfl received] at rr
  have rawAt : assembledData old messages degree 4=rawWord old messages degree := by simp [assembledData]
  have rr' : Executes DagUpdate.Raw.complete (inputStore 94 (assembledData old messages degree 4)) tr
      (outputStore 94 (Encoding.vista.encode (rawUpdate old messages degree))) := by
    simpa only [rawAt,rawWord] using rr
  have called:=call_executes DagUpdate.Raw.complete (by decide) (assembledData old messages degree) 4 5
    (by simp [assembledData,metadataData,preparedData]) _ tr rr'
  rw [rawAt] at called
  let N:=(inputWord old messages degree).length+1
  have positive:1≤N:=by dsimp [N];omega
  have oldBound:(Encoding.vista.encode old).length+1≤N := by
    simp only [N,inputWord_eq,List.length_append,Encoding.frame_length];omega
  have metaBound:=bm.trans (Nat.mul_le_mul_left 1000040 (Nat.pow_le_pow_left oldBound 4))
  have rawBase:=rawWord_length old messages degree valid
  have rawPower:=Nat.pow_le_pow_left rawBase 61
  rw [Nat.mul_pow] at rawPower
  have rawBound : tr≤(DagUpdate.Raw.completeCoefficient*4^61)*N^61 := by
    change tr≤DagUpdate.Raw.completeCoefficient*((rawWord old messages degree).length+1)^61 at br
    exact br.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left DagUpdate.Raw.completeCoefficient rawPower)
  have outputBound:=rawUpdate_encoding_length old messages degree valid received
  have linear:N≤N^61:=Nat.le_self_pow (by decide) _
  have square:N^2≤N^61:=Nat.pow_le_pow_right positive (by decide)
  have fourth:N^4≤N^61:=Nat.pow_le_pow_right positive (by decide)
  have one:1≤N^61:=one_le_pow₀ positive
  have metaRaised:=metaBound.trans (Nat.mul_le_mul_left 1000040 fourth)
  have outputRaised:=outputBound.trans (Nat.mul_le_mul_left 1760 square)
  have inputRaised:(rawWord old messages degree).length≤4*N^61 := by
    have scaled:=Nat.mul_le_mul_left 4 linear
    change (rawWord old messages degree).length+1≤4*N at rawBase
    omega
  have run:=rm.sequence (ra.sequence called)
  refine ⟨_,?_,run⟩
  change tm+1+(5*(rawWord old messages degree).length+11+1+
    (5*(rawWord old messages degree).length+6*(Encoding.vista.encode (rawUpdate old messages degree)).length+tr+8))≤
      (DagUpdate.Raw.completeCoefficient*4^61+1200000)*N^61
  rw [Nat.add_mul]
  omega

end Counting.StackMachine.ProtocolUpdate
