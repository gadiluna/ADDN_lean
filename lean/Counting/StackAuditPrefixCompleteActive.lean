import Counting.StackAuditPrefixCompleteLoop
import Counting.StackAuditPrefixCompleteOutput

namespace Counting.StackMachine.AuditPrefix
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev completeActive : Routine 50 := sequence prepareActive (sequence completeLoop emitAnchor)

/-- After the opening guard succeeds, every prefix test and the latest-flat
selection are physically executed and the exact optional anchor is encoded. -/
theorem completeActive_executes (vista : Executable.Vista) (leaders candidate last : Nat)
    (valid : vista.valid=true) (depth : last≤(vista.node vista.bottom).level)
    (fits : last≤vista.nodes.size) :
    ∃ time output,time ≤ 60000000000*((inputWord vista leaders candidate last).length+1)^7 ∧
      Executes completeActive (openingFile vista leaders candidate last true) time output ∧
      output 1=Encoding.optionalNatural.encode (countsPrefix? vista candidate last) := by
  obtain ⟨prepareTime,prepareBound,a⟩:=prepareActive_executes vista leaders candidate last fits
  rw [loopSeed_eq_roundFile] at a
  obtain ⟨loopTime,loopBound,b⟩:=completeLoop_executes vista valid leaders candidate last 0 last depth fits
    (by omega) (rootAccepted vista candidate) none (by simp)
  simp only [Nat.zero_add] at b
  let status:=rootAccepted vista candidate && scanCheck vista candidate 0 last
  let anchor:=scanAnchor vista 0 last none
  let scanned:=roundFile vista leaders candidate last last [] status anchor
  obtain ⟨emitTime,emitBound,c⟩:=emitAnchor_executes scanned status anchor
    (by simp [scanned,roundFile]) (by simp [scanned,roundFile])
    (by simp [scanned,roundFile,openingFile,tableFile,inputFile])
  let output:=Function.update (Function.update scanned 46 []) 1
    (Encoding.optionalNatural.encode (if status then anchor else none))
  refine ⟨_,output,?_,a.sequence (b.sequence c),?_⟩
  · let L:=(inputWord vista leaders candidate last).length+1
    have positive : 1≤L := by dsimp only [L];omega
    have nodes:=Encoding.vista_nodes_le_length vista
    have inputSize:=inputWord_length vista leaders candidate last
    have lastBound : last≤L := by dsimp only [L];omega
    have boundAnchor : ∀ value∈anchor,value≤last := by
      simpa only [anchor,Nat.zero_add] using scanAnchor_bound vista 0 last none (by simp)
    have code:=anchorCode_le boundAnchor
    have codeSize : (anchorCode anchor).size≤anchorCode anchor:=Nat.size_le.mpr Nat.lt_two_pow_self
    have anchorBits : (anchorCode anchor).size≤L+1 := by omega
    have loopScaled:=Nat.mul_le_mul_right (50000000000*L^6+2) lastBound
    have power : L*L^6=L^7 := by ring
    have fifth : L^5≤L^7:=Nat.pow_le_pow_right positive (by decide)
    have linear : L≤L^7:=Nat.le_self_pow (by decide) _
    have one : 1≤L^7:=Nat.one_le_pow _ _ positive
    change prepareTime≤60000*L^5 at prepareBound
    change loopTime≤last*(50000000000*L^6+2)+1 at loopBound
    change prepareTime+1+(loopTime+1+emitTime)≤60000000000*L^7
    nlinarith only [prepareBound,loopBound,loopScaled,power,fifth,linear,one,emitBound,anchorBits]
  · simp only [output,Function.update_self]
    rw [countsPrefix_eq_scan]

end Counting.StackMachine.AuditPrefix
