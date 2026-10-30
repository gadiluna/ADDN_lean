import Counting.StackAuditDescendantCompleteSetup

namespace Counting.StackMachine.AuditDescendant
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev completeRaw : Routine 46 := sequence prepareComplete
  (sequence completeLoop (move 45 45 1 47))

theorem completeRaw_executes (vista : Executable.Vista) (weights : Array Nat) (anchor last : Nat)
    (fits : last≤vista.nodes.size) :
    ∃ time output,time≤84000000000000*((completeInputWord vista weights anchor last).length+1)^7 ∧
      Executes completeRaw (inputStore 46 (completeInputWord vista weights anchor last)) time output ∧
      output 1=[Executable.auditDescendants vista weights anchor last] := by
  obtain ⟨prepareTime,prepareBound,a⟩:=prepareComplete_executes vista weights anchor last fits
  obtain ⟨loopTime,loopBound,b⟩:=completeLoop_executes vista weights anchor last 0 vista.nodes.size
    (by omega) true
  simp only [Nat.zero_add,Bool.true_and,Executable.auditDescendantRange_full] at b
  let scanned:=completeFile vista weights anchor last vista.nodes.size 0
    (Executable.auditDescendants vista weights anchor last)
  have c:=move_executes 45 (45:Fin 48) 1 47 (by decide) (by decide) (by decide) scanned
    (by simp [scanned,completeFile])
  have source : scanned 45=[Executable.auditDescendants vista weights anchor last] := by simp [scanned,completeFile]
  have vacant : scanned 1=[] := by simp [scanned,completeFile]
  rw [source,vacant,List.append_nil,List.length_singleton] at c
  refine ⟨_,_,?_,a.sequence (b.sequence c),?_⟩
  · let L:=(completeInputWord vista weights anchor last).length+1
    have inputSize:=completeInputWord_length vista weights anchor last
    have nodesLength : ((Encoding.array Encoding.node).encode vista.nodes).length≤(Encoding.vista.encode vista).length := by
      change _≤(((Encoding.array Encoding.node).encode vista.nodes)++Encoding.natural.encode vista.bottom).length
      simp only [List.length_append];omega
    have nodeCount:=Encoding.array_size_le_length Encoding.node vista.nodes
      (by intro node _;exact Encoding.node_positive_length node)
    have base : ((Encoding.array Encoding.node).encode vista.nodes).length+
        ((Encoding.array Encoding.natural).encode weights).length+(last-anchor)+anchor.size+last.size+1≤L := by
      dsimp only [L];omega
    have nodes : vista.nodes.size≤L := by dsimp only [L];omega
    have raised:=Nat.mul_le_mul_left 82000000000000 (Nat.pow_le_pow_left base 6)
    have total:=Nat.mul_le_mul nodes (Nat.add_le_add_right raised 2)
    have loopLimit : loopTime≤82000000000000*L^7+2*L+1 := by
      have combined:=loopBound.trans (Nat.add_le_add_right total 1)
      have expand : L*(82000000000000*L^6+2)+1=82000000000000*L^7+2*L+1 := by ring
      rwa [expand] at combined
    have positive : 1≤L := by dsimp only [L];omega
    have fourth : L^4≤L^7:=Nat.pow_le_pow_right positive (by decide)
    have linear : L≤L^7:=Nat.le_self_pow (by decide) _
    have one : 1≤L^7:=Nat.one_le_pow _ _ positive
    change prepareTime≤10000*L^4 at prepareBound
    change prepareTime+1+(loopTime+1+10)≤84000000000000*L^7
    omega
  · simp

abbrev complete : Routine 46 := isolate completeRaw
def completeCoefficient : Nat := 4200000000000000

/-- Entire descendant check, including input parsing, actual node-count
extraction, both bounded round conversions, all nested scans, and cleanup.
The prefix opening guard supplies `last ≤ nodes.size` in the full audit. -/
theorem complete_executes (vista : Executable.Vista) (weights : Array Nat) (anchor last : Nat)
    (fits : last≤vista.nodes.size) :
    ∃ time≤completeCoefficient*((completeInputWord vista weights anchor last).length+1)^7,
      Executes complete (inputStore 46 (completeInputWord vista weights anchor last)) time
        (outputStore 46 [Executable.auditDescendants vista weights anchor last]) := by
  obtain ⟨rawTime,rawOutput,rawBound,rawRun,result⟩:=completeRaw_executes vista weights anchor last fits
  obtain ⟨finish,ran,halted,stored⟩:=rawRun
  have ran' : Machine.run (step completeRaw.program) rawTime
      (initial completeRaw.program (completeInputWord vista weights anchor last))=some finish := ran
  have growth:=run_dataLength (initial completeRaw.program (completeInputWord vista weights anchor last))
    finish rawTime ran'
  rw [initial_dataLength] at growth
  have registerBound (r:Fin 48) :
      (rawOutput r).length≤(completeInputWord vista weights anchor last).length+rawTime := by
    rw [←stored]
    have part : (finish.store r).length≤finish.dataLength :=
      Finset.single_le_sum (f:=fun i=>(finish.store i).length)
        (fun _ _=>Nat.zero_le _) (Finset.mem_univ r)
    exact part.trans growth
  obtain ⟨clearTime,clearBound,clean⟩:=clearRegisters_executes (workRegisters 46) rawOutput
    ((completeInputWord vista weights anchor last).length+rawTime) registerBound
  have final : clearedStore (workRegisters 46) rawOutput=
      outputStore 46 [Executable.auditDescendants vista weights anchor last] := by
    funext r
    by_cases output:r=1
    · subst r;simpa [clearedStore,workRegisters,outputStore] using result
    · simp [clearedStore,workRegisters,outputStore,output]
  rw [final] at clean
  have raw : Executes completeRaw (inputStore 46 (completeInputWord vista weights anchor last)) rawTime rawOutput :=
    ⟨finish,ran,halted,stored⟩
  refine ⟨_,?_,raw.sequence clean⟩
  have workCount : (workRegisters 46).length≤48 :=
    (List.length_filter_le _ _).trans_eq (by simp)
  have cleanup:=clearBound.trans
    (Nat.mul_le_mul_right ((completeInputWord vista weights anchor last).length+rawTime+2) workCount)
  let L:=(completeInputWord vista weights anchor last).length+1
  have linear : L≤L^7:=Nat.le_self_pow (by decide) _
  have one : 1≤L^7:=Nat.one_le_pow _ _ (by dsimp only [L];omega)
  change rawTime≤84000000000000*L^7 at rawBound
  change rawTime+1+clearTime≤4200000000000000*L^7
  dsimp only [L] at linear one rawBound ⊢
  omega

theorem complete_halts (vista : Executable.Vista) (weights : Array Nat) (anchor last : Nat)
    (fits : last≤vista.nodes.size) :
    ∃ time finish,time≤completeCoefficient*((completeInputWord vista weights anchor last).length+1)^7 ∧
      HaltsAt complete.program (completeInputWord vista weights anchor last) time finish ∧
      finish.store 1=[Executable.auditDescendants vista weights anchor last] := by
  obtain ⟨time,bound,finish,ran,halted,stored⟩:=complete_executes vista weights anchor last fits
  exact ⟨time,finish,bound,⟨ran,halted⟩,by rw [stored];rfl⟩

end Counting.StackMachine.AuditDescendant
