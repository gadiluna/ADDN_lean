import Counting.StackProtocolVistaOutput
import Counting.StackRoutineIsolateHalt
import Counting.EncodingRecognitionBounds

namespace Counting.StackMachine.ProtocolVista
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev completeRaw : Routine 50 := sequence prepareTable (sequence readDepth
  (sequence bothCounts (sequence compareRoots finishRoots)))

theorem completeRaw_executes (vista : Executable.Vista) (valid : vista.valid=true) :
    ∃ time output,time≤ 54000*((Encoding.vista.encode vista).length+1)^5 ∧
      Executes completeRaw (inputStore 50 (Encoding.vista.encode vista)) time output ∧
      output 1=outputWord vista := by
  obtain ⟨a,abound,arun⟩:=prepareTable_executes vista
  obtain ⟨b,bbound,brun⟩:=readDepth_file vista valid
  obtain ⟨c,cbound,crun⟩:=bothCounts_executes vista (vista.node vista.bottom).level.bits
  obtain ⟨d,dbound,drun⟩:=compareRoots_executes vista (vista.node vista.bottom).level.bits
  obtain ⟨output,erun,result⟩:=finishRoots_executes vista (vista.node vista.bottom).level
    (List.replicate (Executable.levelNodes vista 0).length true)
    (List.replicate ((Executable.levelNodes vista 0).filter (fun i=>(vista.node i).leader)).length true)
    (allRootLeaders vista)
  have inside:=RealizabilityVerifier.bottom_inside vista valid
  have nodeBound:=Encoding.nodeBits_le_vista vista vista.bottom inside
  have depthBound:(vista.node vista.bottom).level.size≤ (Encoding.vista.encode vista).length := by
    unfold Encoding.nodeBits at nodeBound
    omega
  let size:=(Encoding.vista.encode vista).length+1
  have positive:1≤ size := by dsimp only [size];omega
  have linear:size≤ size^5:=Nat.le_self_pow (by decide) _
  have third:size^3≤ size^5:=Nat.pow_le_pow_right positive (by decide)
  have fourth:size^4≤ size^5:=Nat.pow_le_pow_right positive (by decide)
  have ar: a≤ 2100*size^5:=abound.trans (Nat.mul_le_mul_left 2100 third)
  have br: b≤ 10000*size^5:=bbound.trans (Nat.mul_le_mul_left 10000 fourth)
  refine ⟨_,output,?_,arun.sequence (brun.sequence (crun.sequence (drun.sequence erun))),result⟩
  change a+1+(b+1+(c+1+(d+1+(5*(vista.node vista.bottom).level.size+10))))≤ 54000*size^5
  dsimp only [size] at linear ar br ⊢
  omega

abbrev complete : Routine 50 := isolate completeRaw

/-- Actual local vista scan: reads the bottom round and decides whether all
visible level-zero nodes are leaders. Every binary label is read from input;
all traversals are bounded by the physical serialized node count. -/
theorem complete_executes (vista : Executable.Vista) (valid : vista.valid=true) :
    ∃ time≤ 3000000*((Encoding.vista.encode vista).length+1)^5,
      Executes complete (inputStore 50 (Encoding.vista.encode vista)) time
        (outputStore 50 (outputWord vista)) := by
  obtain ⟨rawTime,rawOutput,rawBound,rawRun,result⟩:=completeRaw_executes vista valid
  obtain ⟨finish,ran,halted,stored⟩:=rawRun
  have rawHalt : ∃ time last,time≤ 54000*((Encoding.vista.encode vista).length+1)^5 ∧
      HaltsAt completeRaw.program (Encoding.vista.encode vista) time last ∧ last.store 1=outputWord vista :=
    ⟨rawTime,finish,rawBound,⟨ran,halted⟩,by rw [stored];exact result⟩
  obtain ⟨time,bounded,run⟩:=isolate_halts completeRaw (Encoding.vista.encode vista) (outputWord vista) _ rawHalt
  have linear:(Encoding.vista.encode vista).length+1≤ ((Encoding.vista.encode vista).length+1)^5:=
    Nat.le_self_pow (by decide) _
  exact ⟨time,bounded.trans (by omega),run⟩

end Counting.StackMachine.ProtocolVista
