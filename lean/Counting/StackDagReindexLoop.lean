import Counting.StackDagReindexStep

namespace Counting.StackMachine.DagUpdate.Reindex
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def remap (mapping : List Nat) (accumulator : List (Nat×Nat)) (edge : Nat×Nat) : List (Nat×Nat) :=
  Executable.addCount (mapping[edge.1]?.getD 0) edge.2 accumulator

abbrev loop : Routine 38 := forEach 3 step

def loopBudget (mapping : List Nat) : List (Nat×Nat) → List (Nat×Nat) → Nat
  | [],_=>1
  | edge::rest,accumulator=>stepBudget mapping accumulator edge.1 edge.2+2+
      loopBudget mapping rest (remap mapping accumulator edge)

def loopResult (store : Store 38) (mapping : List Nat) (source accumulator : List (Nat×Nat))
    (suffix : List Bool) : Store 38 :=
  Function.update (Function.update (Function.update store 0 suffix) 3 []) 2
    ((Encoding.list edgeCodec).encode (source.foldl (remap mapping) accumulator))

/-- The incoming-reference fold is an actual loop over the compact source
entries. The mapping and all unrelated registers are preserved. -/
theorem loop_executes (store : Store 38) (mapping : List Nat) (source accumulator : List (Nat×Nat))
    (suffix : List Bool)
    (input : store 0=Encoding.sequence edgeCodec source++suffix)
    (mapInput : store 1=(Encoding.list Encoding.natural).encode mapping)
    (current : store 2=(Encoding.list edgeCodec).encode accumulator)
    (counter : store 3=List.replicate source.length true)
    (empty : ∀ r : Fin 40,4 ≤ r.val → r.val ≤ 37 → store r=[]) :
    ∃ time ≤ loopBudget mapping source accumulator,
      Executes loop store time (loopResult store mapping source accumulator suffix) := by
  induction source generalizing store accumulator with
  | nil=>
    have counterEmpty : store 3=[] := by simpa using counter
    have sourceAt : store 0=suffix := by simpa [Encoding.sequence] using input
    obtain ⟨ran,halted⟩:=repeat_empty (3:Fin 40) step store counterEmpty
    have final : loopResult store mapping [] accumulator suffix=store := by
      funext r
      by_cases r0 : r=0 <;> by_cases r2 : r=2 <;> by_cases r3 : r=3 <;>
        simp [loopResult,r0,r2,r3,current,counterEmpty,sourceAt]
    exact ⟨1,by rfl,⟨1,store⟩,ran,halted,final.symm⟩
  | cons edge source ih=>
    rcases edge with ⟨index,count⟩
    let consumed:=Function.update store 3 (List.replicate source.length true)
    have consumedEmpty (r : Fin 40) (lower : 4 ≤ r.val) (upper : r.val ≤ 37) : consumed r=[] := by
      have ne : r≠3 := by intro eq;subst r;norm_num at lower
      simp [consumed,ne,empty r lower upper]
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩:=step_executes consumed mapping accumulator
      index count (Encoding.sequence edgeCodec source++suffix)
      (by simpa [consumed,Encoding.sequence,List.append_assoc] using input)
      (by simp [consumed,mapInput]) (by simp [consumed,current]) consumedEmpty
    let next:=remap mapping accumulator (index,count)
    let middle:=Function.update (Function.update consumed 0 (Encoding.sequence edgeCodec source++suffix)) 2
      ((Encoding.list edgeCodec).encode next)
    have middleEmpty (r : Fin 40) (lower : 4 ≤ r.val) (upper : r.val ≤ 37) : middle r=[] := by
      have ne0 : r≠0 := by intro eq;subst r;norm_num at lower
      have ne2 : r≠2 := by intro eq;subst r;norm_num at lower
      simp [middle,ne0,ne2,consumedEmpty r lower upper]
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩:=ih middle next
      (by simp [middle]) (by simp [middle,consumed,mapInput]) (by simp [middle])
      (by simp [middle,consumed]) middleEmpty
    have firstRun:=repeat_iteration (3:Fin 40) step store true (List.replicate source.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    have final : loopResult middle mapping source next suffix=
        loopResult store mapping ((index,count)::source) accumulator suffix := by
      funext r
      by_cases r0 : r=0 <;> by_cases r2 : r=2 <;> by_cases r3 : r=3 <;>
        simp [loopResult,middle,consumed,next,r0,r2,r3]
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,tailStore.trans final⟩
    · change _ ≤ stepBudget mapping accumulator index count+2+loopBudget mapping source next
      omega
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.DagUpdate.Reindex
