import Counting.StackAnchorLeaderStep
import Counting.StackLoop
import Counting.AnchorMatrixSpec
import Counting.EncodingRationalRows

namespace Counting.StackMachine.AnchorLeaderRow
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev loop : Routine 38 := forEach 37 item

theorem unary_append_cons (n : Nat) (suffix : List Bool) :
    List.replicate n true++true::suffix=true::(List.replicate n true++suffix) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons true) ih

def values (nodes : List Executable.Node) (_query anchor : Nat) : List Rat :=
  (AnchorCoefficient.selectedNodes nodes anchor).map AnchorLeader.value

/-- Traverse the actual concatenation of serialized nodes once, filtering
by its stored binary level, and emit precisely the framed coefficient
stream in reverse order. The counter is bounded by the explicit node list. -/
theorem loop_executes (nodes : List Executable.Node) (query anchor : Nat)
    (suffix reversed width : List Bool) (limit : Nat)
    (inputBound : (Encoding.sequence Encoding.node nodes++suffix).length ≤ limit) :
    ∃ time ≤ nodes.length*(200000*(limit+query.size+anchor.size+1)^3+2)+1,
      Executes loop
        (file (Encoding.sequence Encoding.node nodes++suffix) query.bits anchor.bits [] [] reversed width
          (List.replicate nodes.length true) []) time
        (file suffix query.bits anchor.bits [] []
          ((Encoding.sequence (Encoding.framed Encoding.rational) (values nodes query anchor)).reverse++reversed)
          (List.replicate (values nodes query anchor).length true++width) [] []) := by
  induction nodes generalizing reversed width with
  | nil =>
    obtain ⟨ran,halted⟩ := repeat_empty (37:Fin 40) item
      (file suffix query.bits anchor.bits [] [] reversed width [] []) rfl
    refine ⟨1,by simp,⟨1,_⟩,ran,halted,?_⟩
    simp [values,AnchorCoefficient.selectedNodes,Encoding.sequence]
  | cons node nodes ih =>
    let source := Encoding.sequence Encoding.node nodes++suffix
    let counter := List.replicate nodes.length true
    let start := file (Encoding.node.encode node++source) query.bits anchor.bits [] [] reversed width (true::counter) []
    let nextRev := nextReversed node query anchor reversed
    let nextCount := nextWidth node anchor width
    have popped : Function.update start 37 counter=
        file (Encoding.node.encode node++source) query.bits anchor.bits [] [] reversed width counter [] := by
      funext r;fin_cases r <;> simp [start,file,AnchorRow.file]
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ :=
      item_executes node query anchor source reversed width counter
    have nextInput : (Encoding.sequence Encoding.node nodes++suffix).length ≤ limit := by
      simp only [Encoding.sequence,List.length_append] at inputBound ⊢
      omega
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ := ih nextRev nextCount nextInput
    have firstRun := repeat_iteration (37:Fin 40) item start true counter rfl bodyTime bodyFinish
      (by rw [popped];exact bodyRun) bodyHalt
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,?_⟩
    · have bodyLimit : bodyTime ≤ 200000*(limit+query.size+anchor.size+1)^3 := by
        apply bodyBound.trans
        gcongr
        simpa only [Encoding.sequence,List.append_assoc,source] using inputBound
      simp only [List.length_cons]
      nlinarith
    · simp only [Encoding.sequence,List.append_assoc,List.length_cons,List.replicate_succ]
      change Machine.run (step loop.program) (bodyTime+2+tailTime) ⟨0,start⟩=some tailFinish
      rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun
    · rw [tailStore]
      by_cases equal : node.level=anchor
      · simp [values,AnchorCoefficient.selectedNodes,equal,Encoding.sequence,Encoding.framed,
          nextRev,nextCount,nextReversed,nextWidth,word,List.reverse_append,List.append_assoc,
          List.replicate_succ,unary_append_cons]
      · simp [values,AnchorCoefficient.selectedNodes,equal,
          nextRev,nextCount,nextReversed,nextWidth]

end Counting.StackMachine.AnchorLeaderRow
