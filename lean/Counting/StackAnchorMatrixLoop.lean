import Counting.StackAnchorMatrixStep

namespace Counting.StackMachine.AnchorMatrix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev loop : Routine 48 := forEach 48 item

def generatedRows (nodes : List Executable.Node) (anchor previous : Nat) :
    Nat → List Executable.Node → List (List Rat)
  | _,[] => []
  | start,node::rest =>
      if node.level=previous then AnchorCoefficient.flowRow nodes anchor start::generatedRows nodes anchor previous (start+1) rest
      else generatedRows nodes anchor previous (start+1) rest

def loopBudget (nodes : List Executable.Node) (anchor previous : Nat) (suffix : List Bool) :
    Nat → List Executable.Node → Nat
  | _,[] => 1
  | start,node::rest => stepBudget nodes node start anchor previous
      (Encoding.sequence Encoding.node rest++suffix) suffix+2+loopBudget nodes anchor previous suffix (start+1) rest

/-- The outer counter traverses the actual node table in order. Only
old-level nodes create rows, indexed by their physical DAG position. -/
theorem loop_executes (nodes remaining : List Executable.Node) (start anchor previous : Nat)
    (suffix matrix rows leaders : List Bool) :
    ∃ time ≤ loopBudget nodes anchor previous suffix start remaining,
      Executes loop
        (bank (AnchorRow.file (Encoding.sequence Encoding.node remaining++suffix) start.bits anchor.bits [] [] [] [] [] [])
          (Encoding.sequence Encoding.node nodes++suffix) previous.bits [] (List.replicate nodes.length true)
          matrix rows (List.replicate remaining.length true) leaders) time
        (bank (AnchorRow.file suffix (start+remaining.length).bits anchor.bits [] [] [] [] [] [])
          (Encoding.sequence Encoding.node nodes++suffix) previous.bits [] (List.replicate nodes.length true)
          ((Encoding.sequence (Encoding.framed Encoding.rationalRow) (generatedRows nodes anchor previous start remaining)).reverse++matrix)
          (List.replicate (generatedRows nodes anchor previous start remaining).length true++rows) [] leaders) := by
  induction remaining generalizing start matrix rows with
  | nil =>
    obtain ⟨ran,halted⟩ := repeat_empty (48:Fin 50) item
      (bank (AnchorRow.file suffix start.bits anchor.bits [] [] [] [] [] [])
        (Encoding.sequence Encoding.node nodes++suffix) previous.bits [] (List.replicate nodes.length true) matrix rows [] leaders) rfl
    refine ⟨1,by rfl,⟨1,_⟩,?_,halted,?_⟩
    · simpa only [Encoding.sequence,List.nil_append,List.length_nil,List.replicate_zero] using ran
    · simp [generatedRows,Encoding.sequence]
  | cons node rest ih =>
    let tail := Encoding.sequence Encoding.node rest++suffix
    let count := List.replicate rest.length true
    let initial := bank (AnchorRow.file (Encoding.node.encode node++tail) start.bits anchor.bits [] [] [] [] [] [])
      (Encoding.sequence Encoding.node nodes++suffix) previous.bits [] (List.replicate nodes.length true)
      matrix rows (true::count) leaders
    have popped : Function.update initial 48 count=
        bank (AnchorRow.file (Encoding.node.encode node++tail) start.bits anchor.bits [] [] [] [] [] [])
          (Encoding.sequence Encoding.node nodes++suffix) previous.bits [] (List.replicate nodes.length true)
          matrix rows count leaders := by
      funext r;fin_cases r <;> simp [initial,bank,AnchorRow.file]
    let nextMatrix := if node.level=previous then
      (Encoding.frame (Encoding.rationalRow.encode (AnchorCoefficient.flowRow nodes anchor start))).reverse++matrix else matrix
    let nextCount := if node.level=previous then true::rows else rows
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ :=
      item_executes nodes node start anchor previous tail suffix matrix rows count leaders
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ :=
      ih (start+1) nextMatrix nextCount
    have firstRun := repeat_iteration (48:Fin 50) item initial true count rfl bodyTime bodyFinish
      (by rw [popped];exact bodyRun) bodyHalt
    refine ⟨bodyTime+2+tailTime,by change _ ≤ stepBudget _ _ _ _ _ _ _+2+_;dsimp only [tail] at bodyBound;omega,tailFinish,?_,tailHalt,?_⟩
    · simp only [Encoding.sequence,List.append_assoc,List.length_cons,List.replicate_succ]
      change Machine.run (step loop.program) (bodyTime+2+tailTime) ⟨0,initial⟩=some tailFinish
      rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun
    · rw [tailStore]
      have index : start+1+rest.length=start+(node::rest).length := by simp only [List.length_cons];omega
      rw [index]
      by_cases equal : node.level=previous
      · simp [generatedRows,equal,Encoding.sequence,Encoding.framed,nextMatrix,nextCount,
          List.reverse_append,List.append_assoc,List.replicate_succ,AnchorRow.unary_append_cons]
      · simp [generatedRows,equal,nextMatrix,nextCount]

end Counting.StackMachine.AnchorMatrix
