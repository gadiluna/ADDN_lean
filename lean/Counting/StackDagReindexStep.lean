import Counting.StackDagReindexRead
import Counting.StackDagReindexApply

namespace Counting.StackMachine.DagUpdate.Reindex
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def step : Routine 38 := sequence readMapped applyMapped

def stepBudget (mapping : List Nat) (edges : List (Nat×Nat)) (index count : Nat) : Nat :=
  let mapped:=mapping[index]?.getD 0
  10*index.bits.length+6*count.bits.length+(Encoding.natural.encode index).length+mapped.bits.length+
    200*(((Encoding.list Encoding.natural).encode mapping).length+(Encoding.natural.encode index).length+1)^3+
    10000*(((Encoding.list edgeCodec).encode edges).length+mapped.bits.length+count.bits.length+1)^3+
    6*((Encoding.list edgeCodec).encode (Executable.addCount mapped count edges)).length+24

/-- One source edge is parsed, reindexed through the serialized mapping,
and inserted into the compact accumulator. Only the source suffix and the
accumulator change. -/
theorem step_executes (store : Store 38) (mapping : List Nat) (edges : List (Nat×Nat))
    (index count : Nat) (suffix : List Bool)
    (source : store 0=edgeCodec.encode (index,count)++suffix)
    (mapInput : store 1=(Encoding.list Encoding.natural).encode mapping)
    (accumulator : store 2=(Encoding.list edgeCodec).encode edges)
    (empty : ∀ r : Fin 40,4 ≤ r.val → r.val ≤ 37 → store r=[]) :
    ∃ time ≤ stepBudget mapping edges index count,
      Executes step store time (Function.update (Function.update store 0 suffix) 2
        ((Encoding.list edgeCodec).encode (Executable.addCount (mapping[index]?.getD 0) count edges))) := by
  obtain ⟨readTime,readBound,reading⟩:=readMapped_executes store mapping index count suffix source mapInput
    (fun r lower upper=>empty r lower (by omega))
  let mapped:=mapping[index]?.getD 0
  let read:=readMappedResult store mapping index count suffix
  have readEmpty (r : Fin 40) (member : r=9 ∨ (21 ≤ r.val ∧ r.val ≤ 37)) : read r=[] := by
    have ne0 : r≠0 := by intro eq;subst r;norm_num at member; omega
    have ne5 : r≠5 := by intro eq;subst r;norm_num at member; omega
    have ne6 : r≠6 := by intro eq;subst r;norm_num at member; omega
    have ne7 : r≠7 := by intro eq;subst r;norm_num at member; omega
    have inside : 4 ≤ r.val ∧ r.val ≤ 37 := by rcases member with rfl|member <;> omega
    simpa [read,readMappedResult,ne0,ne5,ne6,ne7] using empty r inside.1 inside.2
  obtain ⟨applyTime,applyBound,applying⟩:=applyMapped_executes read mapped count edges
    (by simp [read,readMappedResult,accumulator])
    (by simp [read,readMappedResult,mapped])
    (by simp [read,readMappedResult]) readEmpty
  have accumulatorAt : read 2=(Encoding.list edgeCodec).encode edges := by simp [read,readMappedResult,accumulator]
  have headerAt : read 6=Encoding.natural.encode index := by simp [read,readMappedResult]
  rw [accumulatorAt,headerAt] at applyBound
  rw [mapInput] at readBound
  have final : applyMappedResult read mapped count edges=
      Function.update (Function.update store 0 suffix) 2
        ((Encoding.list edgeCodec).encode (Executable.addCount mapped count edges)) := by
    funext r
    by_cases r5 : r=5
    · subst r;simp [applyMappedResult,empty]
    · by_cases r6 : r=6
      · subst r;simp [applyMappedResult,empty]
      · by_cases r7 : r=7
        · subst r;simp [applyMappedResult,empty]
        · by_cases r0 : r=0 <;> by_cases r2 : r=2 <;>
            simp [applyMappedResult,read,readMappedResult,r0,r2,r5,r6,r7]
  rw [final] at applying
  exact ⟨readTime+1+applyTime,by dsimp only [stepBudget];dsimp only [mapped] at applyBound;omega,
    reading.sequence applying⟩

end Counting.StackMachine.DagUpdate.Reindex
