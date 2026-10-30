import Counting.StackDagReindexLoop
import Counting.StackDagReindexHeader
import Counting.EncodingNetwork

namespace Counting.StackMachine.DagUpdate.Reindex
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def incoming : Routine 38 := sequence readHeader loop

theorem incoming_executes (store : Store 38) (mapping : List Nat) (source accumulator : List (Nat×Nat))
    (suffix : List Bool)
    (input : store 0=(Encoding.list edgeCodec).encode source++suffix)
    (mapInput : store 1=(Encoding.list Encoding.natural).encode mapping)
    (current : store 2=(Encoding.list edgeCodec).encode accumulator)
    (empty : ∀ r : Fin 40,3 ≤ r.val → r.val ≤ 37 → store r=[]) :
    ∃ time ≤ 1820*((store 0).length+1)^3+loopBudget mapping source accumulator+5,
      Executes incoming store time (Function.update (Function.update store 0 suffix) 2
        ((Encoding.list edgeCodec).encode (source.foldl (remap mapping) accumulator))) := by
  obtain ⟨headerTime,headerBound,reading⟩:=readHeader_executes store source suffix input
    (fun r lower upper=>empty r lower (by omega))
  let ready:=Function.update (Function.update store 0 (Encoding.sequence edgeCodec source++suffix)) 3
    (List.replicate source.length true)
  have readyEmpty (r : Fin 40) (lower : 4 ≤ r.val) (upper : r.val ≤ 37) : ready r=[] := by
    have ne0 : r≠0 := by intro eq;subst r;norm_num at lower
    have ne3 : r≠3 := by intro eq;subst r;norm_num at lower
    simp [ready,ne0,ne3,empty r (by omega) upper]
  obtain ⟨loopTime,loopBound,loopRun⟩:=loop_executes ready mapping source accumulator suffix
    (by simp [ready]) (by simp [ready,mapInput]) (by simp [ready,current])
    (by simp [ready]) readyEmpty
  have final : loopResult ready mapping source accumulator suffix=
      Function.update (Function.update store 0 suffix) 2
        ((Encoding.list edgeCodec).encode (source.foldl (remap mapping) accumulator)) := by
    funext r
    by_cases r3 : r=3
    · subst r;simp [loopResult,empty]
    · by_cases r0 : r=0 <;> by_cases r2 : r=2 <;> simp [loopResult,ready,r0,r2,r3]
  rw [final] at loopRun
  exact ⟨headerTime+1+loopTime,by omega,reading.sequence loopRun⟩

/-- Specialization to the exact incoming component of the existing
`referenceMap` implementation. Initial accumulation is the empty list. -/
theorem incoming_referenceMap (store : Store 38) (mapping : Array Nat) (node : Executable.Node)
    (suffix : List Bool)
    (input : store 0=(Encoding.list edgeCodec).encode node.incoming++suffix)
    (mapInput : store 1=(Encoding.array Encoding.natural).encode mapping)
    (current : store 2=(Encoding.list edgeCodec).encode [])
    (empty : ∀ r : Fin 40,3 ≤ r.val → r.val ≤ 37 → store r=[]) :
    ∃ time ≤ 1820*((store 0).length+1)^3+loopBudget mapping.toList node.incoming []+5,
      Executes incoming store time (Function.update (Function.update store 0 suffix) 2
        ((Encoding.list edgeCodec).encode (Executable.referenceMap mapping node).incoming)) := by
  have same : remap mapping.toList=(fun acc edge=>Executable.addCount (mapping[edge.1]?.getD 0) edge.2 acc) := by
    funext acc edge
    simp [remap]
  have ran:=incoming_executes store mapping.toList node.incoming [] suffix input mapInput current empty
  rw [same] at ran
  simpa only [Executable.referenceMap] using ran

end Counting.StackMachine.DagUpdate.Reindex
