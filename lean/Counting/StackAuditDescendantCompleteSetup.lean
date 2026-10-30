import Counting.StackAuditDescendantCompleteHeader
import Counting.StackAuditDescendantCompleteLoop
import Counting.StackAuditDescendantRounds

namespace Counting.StackMachine.AuditDescendant
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

abbrev startComplete : Routine 46 := sequence prepareRounds
  (sequence (pushBit 29 true) (pushBit 45 true))

theorem startComplete_executes (vista : Executable.Vista) (weights : Array Nat) (anchor last : Nat)
    (fits : last≤vista.nodes.size) :
    ∃ time ≤ 2200*(vista.nodes.size+last.size+anchor.size+1)^3,
      Executes startComplete (completeHeaderFile vista weights anchor last) time
        (completeFile vista weights anchor last 0 vista.nodes.size true) := by
  let initial:=completeHeaderFile vista weights anchor last
  obtain ⟨roundTime,roundBound,a⟩:=prepareRounds_exact initial last anchor vista.nodes.size fits
    (by simp [initial,completeHeaderFile,completeNodesFile,completeInputFile])
    (by simp [initial,completeHeaderFile,completeNodesFile,completeInputFile])
    (by simp [initial,completeHeaderFile]) (by
      intro r member
      fin_cases r <;> simp_all [initial,completeHeaderFile,completeNodesFile,completeInputFile,roundWorkspace])
  let ready:=Function.update initial 38 (List.replicate (last-anchor) true)
  have b:=pushBit_executes (29:Fin 48) true ready
  have e29 : ready 29=[] := by simp [ready,initial,completeHeaderFile,completeNodesFile,completeInputFile]
  rw [e29] at b
  let indexed:=Function.update ready 29 [true]
  have c:=pushBit_executes (45:Fin 48) true indexed
  have e45 : indexed 45=[] := by simp [indexed,ready,initial,completeHeaderFile,completeNodesFile,completeInputFile]
  rw [e45] at c
  have final : Function.update indexed 45 [true]=completeFile vista weights anchor last 0 vista.nodes.size true := by
    funext r
    fin_cases r <;> simp [indexed,ready,initial,completeHeaderFile,completeNodesFile,completeInputFile,completeFile,Nat.bits]
  rw [final] at c
  have one : 1≤(vista.nodes.size+last.size+anchor.size+1)^3:=Nat.one_le_pow _ _ (by omega)
  exact ⟨_,by omega,a.sequence (b.sequence c)⟩

abbrev prepareComplete : Routine 46 := sequence readCompleteInput
  (sequence readCompleteNodes (sequence readCompleteHeader startComplete))

/-- The descendant scan receives only binary data. Every unary scan/ascent
budget is constructed by reading the actual encoded node count and labels. -/
theorem prepareComplete_executes (vista : Executable.Vista) (weights : Array Nat) (anchor last : Nat)
    (fits : last≤vista.nodes.size) :
    ∃ time ≤ 10000*((completeInputWord vista weights anchor last).length+1)^4,
      Executes prepareComplete (inputStore 46 (completeInputWord vista weights anchor last)) time
        (completeFile vista weights anchor last 0 vista.nodes.size true) := by
  obtain ⟨readTime,readBound,a⟩:=readCompleteInput_executes vista weights anchor last
  obtain ⟨nodesTime,nodesBound,b⟩:=readCompleteNodes_executes vista weights anchor last
  obtain ⟨headerTime,headerBound,c⟩:=readCompleteHeader_executes vista weights anchor last
  obtain ⟨startTime,startBound,d⟩:=startComplete_executes vista weights anchor last fits
  let L:=(completeInputWord vista weights anchor last).length+1
  have inputSize:=completeInputWord_length vista weights anchor last
  have nodesLength : ((Encoding.array Encoding.node).encode vista.nodes).length≤(Encoding.vista.encode vista).length := by
    change _≤(((Encoding.array Encoding.node).encode vista.nodes)++Encoding.natural.encode vista.bottom).length
    simp only [List.length_append];omega
  have nodeCount:=Encoding.array_size_le_length Encoding.node vista.nodes
    (by intro node _;exact Encoding.node_positive_length node)
  have positive : 1≤L := by dsimp only [L];omega
  have one : 1≤L^4:=Nat.one_le_pow _ _ positive
  have readLimit : readTime≤100*L^4:=readBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (by decide)))
  have nodesLimit : nodesTime≤3900*L^4:=nodesBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [L];omega) 4))
  have headerLimit : headerTime≤2000*L^4:=headerBound.trans
    (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by dsimp only [L];omega) 3).trans
      (Nat.pow_le_pow_right positive (by decide))))
  have startLimit : startTime≤2200*L^4:=startBound.trans
    (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by dsimp only [L];omega) 3).trans
      (Nat.pow_le_pow_right positive (by decide))))
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  change readTime+1+(nodesTime+1+(headerTime+1+startTime))≤10000*L^4
  omega

end Counting.StackMachine.AuditDescendant
