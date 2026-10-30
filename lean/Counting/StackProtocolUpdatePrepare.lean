import Counting.StackNetworkComplementEntry
import Counting.StackProtocolBottomComplete
import Counting.EncodingRationalRows
import Counting.StackVistaRawPolynomial

namespace Counting.StackMachine.ProtocolUpdate
open Routine EncodingPrograms NetworkComplement
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

abbrev Input := Executable.Vista × List (Executable.Vista×Nat) × Nat

def inputCodec : Encoding.Codec Input := Encoding.product (Encoding.framed Encoding.vista)
  (Encoding.product (Encoding.framed (Encoding.list DagUpdate.Receive.messageCodec)) Encoding.natural)

def inputWord (old : Executable.Vista) (messages : List (Executable.Vista×Nat)) (degree : Nat) : List Bool :=
  inputCodec.encode (old,messages,degree)

theorem inputWord_eq (old : Executable.Vista) (messages : List (Executable.Vista×Nat)) (degree : Nat) :
    inputWord old messages degree = Encoding.frame (Encoding.vista.encode old)++
      Encoding.frame ((Encoding.list DagUpdate.Receive.messageCodec).encode messages)++Encoding.natural.encode degree := by
  simp only [inputWord,inputCodec,Encoding.product,Encoding.framed,List.append_assoc]

def preparedData (old : Executable.Vista) (messages : List (Executable.Vista×Nat)) (degree : Nat) : Fin 30→List Bool :=
  fun r=>if r=0 then Encoding.vista.encode old
    else if r=1 then (Encoding.list DagUpdate.Receive.messageCodec).encode messages
    else if r=2 then Encoding.natural.encode degree else []

def prepare : Routine 158 := sequence (ofProgram (unframeProgram 157 0 130 1))
  (sequence (ofProgram (unframeProgram 157 0 131 1)) (move 157 0 132 1))

/-- The framed fields are physically extracted; only the degree suffix
is left after both frames and is then moved into its own register. -/
theorem prepare_executes (old : Executable.Vista) (messages : List (Executable.Vista×Nat)) (degree : Nat) :
    ∃time≤10*(inputWord old messages degree).length+10,
      Executes prepare (inputStore 158 (inputWord old messages degree)) time
        (file (preparedData old messages degree)) := by
  let V:=Encoding.vista.encode old
  let M:=(Encoding.list DagUpdate.Receive.messageCodec).encode messages
  let D:=Encoding.natural.encode degree
  let initial:=inputStore 158 (inputWord old messages degree)
  have a:=unframe_canonical_executes 157 (0:Fin 160) 130 1 (by decide) (by decide) (by decide)
    initial V (Encoding.frame M++D) (by simp [initial,inputStore,inputWord_eq,V,M,D,List.append_assoc]) (by simp [initial,inputStore])
  rw [show initial 130=[] by simp [initial,inputStore],List.append_nil] at a
  let first:=Function.update (Function.update initial 0 (Encoding.frame M++D)) 130 V
  have b:=unframe_canonical_executes 157 (0:Fin 160) 131 1 (by decide) (by decide) (by decide)
    first M D (by simp [first]) (by simp [first,initial,inputStore])
  rw [show first 131=[] by simp [first,initial,inputStore],List.append_nil] at b
  let second:=Function.update (Function.update first 0 D) 131 M
  have c:=move_executes 157 (0:Fin 160) 132 1 (by decide) (by decide) (by decide)
    second (by simp [second,first,initial,inputStore])
  rw [show second 0=D by simp [second],show second 132=[] by simp [second,first,initial,inputStore],List.append_nil] at c
  have final : Function.update (Function.update second 132 D) 0 []=file (preparedData old messages degree) := by
    funext r
    fin_cases r <;> simp [second,first,initial,inputStore,file,preparedData,V,M,D]
  rw [final] at c
  have length : (inputWord old messages degree).length=2*V.length+2*M.length+D.length+2 := by
    simp only [inputWord_eq,List.length_append,Encoding.frame_length,V,M,D]
    omega
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  omega

def metadata : Routine 158 := call ProtocolBottom.complete (by decide) 0 3

theorem metadata_executes (old : Executable.Vista) (messages : List (Executable.Vista×Nat)) (degree : Nat)
    (valid : old.valid=true) :
    ∃time≤1000040*((Encoding.vista.encode old).length+1)^4,
      Executes metadata (file (preparedData old messages degree)) time
        (file (Function.update (preparedData old messages degree) 3 (ProtocolBottom.outputWord old))) := by
  obtain ⟨time,bounded,run⟩:=ProtocolBottom.complete_executes old valid
  have called:=call_executes ProtocolBottom.complete (by decide) (preparedData old messages degree) 0 3
    (by simp [preparedData]) (ProtocolBottom.outputWord old) time run
  have nodeBound:=Encoding.nodeBits_le_vista old old.bottom (RealizabilityVerifier.bottom_inside old valid)
  have outputBound:(ProtocolBottom.outputWord old).length≤3*((Encoding.vista.encode old).length+1) := by
    simp only [ProtocolBottom.outputWord,List.length_append,List.length_singleton,Encoding.natural_length]
    unfold Encoding.nodeBits at nodeBound
    omega
  have linear:(Encoding.vista.encode old).length+1≤((Encoding.vista.encode old).length+1)^4:=
    Nat.le_self_pow (by decide) _
  refine ⟨_,?_,called⟩
  simp only [preparedData,↓reduceIte] at *
  omega

def assemble : Routine 158 := sequence (copyExternal 1 4)
  (sequence (copyExternal 0 4) (sequence (copyExternal 2 4) (copyExternal 3 4)))

theorem assemble_executes (data : Fin 30→List Bool) (empty : data 4=[]) :
    Executes assemble (file data)
      (5*((data 1).length+(data 0).length+(data 2).length+(data 3).length)+11)
      (file (Function.update data 4 (data 3++data 2++data 0++data 1))) := by
  have a:=copyExternal_executes data 1 4 (by decide)
  rw [empty,List.append_nil] at a
  let d1:=Function.update data 4 (data 1)
  have b:=copyExternal_executes d1 0 4 (by decide)
  simp only [d1,Function.update_of_ne (by decide : (0:Fin 30)≠4),Function.update_self] at b
  let d2:=Function.update d1 4 (data 0++data 1)
  have c:=copyExternal_executes d2 2 4 (by decide)
  simp only [d2,d1,Function.update_of_ne (by decide : (2:Fin 30)≠4),Function.update_self] at c
  let d3:=Function.update d2 4 (data 2++(data 0++data 1))
  have d:=copyExternal_executes d3 3 4 (by decide)
  simp only [d3,d2,d1,Function.update_of_ne (by decide : (3:Fin 30)≠4),Function.update_self] at d
  have final : Function.update d3 4 (data 3++(data 2++(data 0++data 1)))=
      Function.update data 4 (data 3++data 2++data 0++data 1) := by
    simp only [d3,d2,d1,Function.update_idem,List.append_assoc]
  rw [final] at d
  have run:=a.sequence (b.sequence (c.sequence d))
  simpa only [assemble,show 5*(data 1).length+2+1+(5*(data 0).length+2+1+
    (5*(data 2).length+2+1+(5*(data 3).length+2)))=
    5*((data 1).length+(data 0).length+(data 2).length+(data 3).length)+11 by omega] using run

end Counting.StackMachine.ProtocolUpdate
