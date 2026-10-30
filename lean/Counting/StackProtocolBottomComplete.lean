import Counting.StackProtocolBottomRead
import Counting.StackProtocolVistaTable
import Counting.StackEncodingFrameStore
import Counting.StackRoutineIsolateHalt
import Counting.EncodingRecognitionBounds

namespace Counting.StackMachine.ProtocolBottom
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

abbrev prepareTable : Routine 50 := ProtocolVista.prepareTable

def prepared (vista : Executable.Vista) : Store 50 :=
  Function.update (ProtocolVista.file vista (vista.node vista.bottom).level.bits [] []) 44 [(vista.node vista.bottom).leader]

def outputWord (vista : Executable.Vista) : List Bool :=
  Encoding.natural.encode (vista.node vista.bottom).level++[(vista.node vista.bottom).leader]

theorem readBottom_file (vista : Executable.Vista) (valid : vista.valid=true) :
    ∃ time≤ 10000*((Encoding.vista.encode vista).length+1)^4,
      Executes readBottom (ProtocolVista.file vista [] [] []) time (prepared vista) := by
  obtain ⟨time,bounded,run⟩:=readBottom_executes (ProtocolVista.file vista [] [] []) vista valid true [] rfl
    (by intro r small different;fin_cases r <;> simp_all [ProtocolVista.file]) rfl rfl rfl rfl rfl
    (Encoding.natural.encode vista.bottom) rfl rfl
  have target:Function.update (ProtocolVista.file vista [] [] []) 42 (vista.node vista.bottom).level.bits=
      ProtocolVista.file vista (vista.node vista.bottom).level.bits [] [] := by
    funext r;fin_cases r <;> simp [ProtocolVista.file]
  rw [target] at run
  exact ⟨time,bounded.trans (Nat.mul_le_mul_left 10000
    (Nat.pow_le_pow_left (Nat.add_le_add_right (ProtocolVista.tableWord_length vista) 1) 4)),run⟩

abbrev finish : Routine 50 := sequence (clear 1)
  (sequence (move 49 44 1 51) (frameRoutine 49 42 1 51))

theorem finish_executes (vista : Executable.Vista) :
    ∃ output,Executes finish (prepared vista) (5*(vista.node vista.bottom).level.size+18) output ∧
      output 1=outputWord vista := by
  have a:=clear_executes (1:Fin 52) (prepared vista)
  change Executes _ _ 2 (Function.update (prepared vista) 1 []) at a
  let erased:=Function.update (prepared vista) 1 []
  have b:=move_executes 49 (44:Fin 52) 1 51 (by decide) (by decide) (by decide) erased
    (by simp [erased,prepared,ProtocolVista.file])
  have source:erased 44=[(vista.node vista.bottom).leader] := by simp [erased,prepared]
  have vacant:erased 1=[] := by simp [erased]
  rw [source,vacant,List.append_nil,List.length_singleton] at b
  let moved:=Function.update (Function.update erased 1 [(vista.node vista.bottom).leader]) 44 []
  have c:=frame_executes_updates 49 (42:Fin 52) 1 51 (by decide) (by decide) (by decide) moved
    (by simp [moved,erased,prepared,ProtocolVista.file])
  have depth:moved 42=(vista.node vista.bottom).level.bits := by simp [moved,erased,prepared,ProtocolVista.file]
  have leader:moved 1=[(vista.node vista.bottom).leader] := by simp [moved]
  rw [depth,leader] at c
  have run:=a.sequence (b.sequence c)
  rw [Encoding.bits_length] at run
  refine ⟨Function.update (Function.update moved 42 []) 1
    (Encoding.frame (vista.node vista.bottom).level.bits++[(vista.node vista.bottom).leader]),?_,?_⟩
  · convert run using 1
    omega
  · simp [outputWord,Encoding.natural]

abbrev completeRaw : Routine 50 := sequence prepareTable (sequence readBottom finish)

theorem completeRaw_executes (vista : Executable.Vista) (valid : vista.valid=true) :
    ∃ time output,time≤ 13000*((Encoding.vista.encode vista).length+1)^4 ∧
      Executes completeRaw (inputStore 50 (Encoding.vista.encode vista)) time output ∧ output 1=outputWord vista := by
  obtain ⟨a,abound,arun⟩:=ProtocolVista.prepareTable_executes vista
  obtain ⟨b,bbound,brun⟩:=readBottom_file vista valid
  obtain ⟨output,crun,result⟩:=finish_executes vista
  have nodeBound:=Encoding.nodeBits_le_vista vista vista.bottom (RealizabilityVerifier.bottom_inside vista valid)
  have depthBound:(vista.node vista.bottom).level.size≤ (Encoding.vista.encode vista).length := by
    unfold Encoding.nodeBits at nodeBound
    omega
  let size:=(Encoding.vista.encode vista).length+1
  have positive:1≤ size := by dsimp only [size];omega
  have linear:size≤ size^4:=Nat.le_self_pow (by decide) _
  have raised:a≤ 2100*size^4:=abound.trans
    (Nat.mul_le_mul_left 2100 (Nat.pow_le_pow_right positive (by decide)))
  refine ⟨_,output,?_,arun.sequence (brun.sequence crun),result⟩
  change a+1+(b+1+(5*(vista.node vista.bottom).level.size+18))≤ 13000*size^4
  dsimp only [size] at linear raised ⊢
  omega

abbrev complete : Routine 50 := isolate completeRaw

/-- Read both bottom metadata fields from the actual binary vista and
return a clean encoded pair. This supplies the receiver updater's metadata
without making the round or the leader bit external oracle inputs. -/
theorem complete_executes (vista : Executable.Vista) (valid : vista.valid=true) :
    ∃ time≤ 1000000*((Encoding.vista.encode vista).length+1)^4,
      Executes complete (inputStore 50 (Encoding.vista.encode vista)) time
        (outputStore 50 (outputWord vista)) := by
  obtain ⟨rawTime,rawOutput,rawBound,rawRun,result⟩:=completeRaw_executes vista valid
  obtain ⟨finish,ran,halted,stored⟩:=rawRun
  have rawHalt : ∃ time last,time≤ 13000*((Encoding.vista.encode vista).length+1)^4 ∧
      HaltsAt completeRaw.program (Encoding.vista.encode vista) time last ∧ last.store 1=outputWord vista :=
    ⟨rawTime,finish,rawBound,⟨ran,halted⟩,by rw [stored];exact result⟩
  obtain ⟨time,bounded,run⟩:=isolate_halts completeRaw (Encoding.vista.encode vista) (outputWord vista) _ rawHalt
  have linear:(Encoding.vista.encode vista).length+1≤ ((Encoding.vista.encode vista).length+1)^4:=
    Nat.le_self_pow (by decide) _
  exact ⟨time,bounded.trans (by omega),run⟩

end Counting.StackMachine.ProtocolBottom
