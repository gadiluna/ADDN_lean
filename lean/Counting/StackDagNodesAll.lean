import Counting.StackDagNodesSpec

/-! All semantic node checks, followed by actual cleanup of the running
binary and unary indices. No finite population parameter enters the code. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def allNodesFromCount : Routine 33:=sequence (forEach 27 nodeStepRoutine) (sequence (clear 24) (clear 29))

theorem allNodesFromCount_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 35,r∈({18,19,20,21,22,23,24,25,26,28,29,30,31,32,33,34}:Finset (Fin 35)) → store r=[])
    (values : List Executable.Node) (sourceSuffix : List Bool)
    (source : store 17=Encoding.sequence Encoding.node values++sourceSuffix)
    (counter : (store 27).length=values.length) :
    ∃ time ≤ 221000000*((store 17).length+1)^6,
      Executes allNodesFromCount store time
        (Function.update (Function.update store 27 []) 1 ((accepted && nodeRangeCheck values 0 values.length)::tail)) := by
  have loopExtra (r : Fin 35) (member : r∈({18,19,20,21,22,23,25,26,28,30,31,32,33,34}:Finset (Fin 35))) : store r=[]:=by
    apply extraWork r
    simp only [Finset.mem_insert,Finset.mem_singleton] at member ⊢
    tauto
  obtain ⟨loopTime,loopBound,loopRun⟩:=nodesLoop_executes store accepted tail status work loopExtra values 0 values.length
    (by omega) sourceSuffix source (extraWork 24 (by decide))
    (by rw [extraWork 29 (by decide)];rfl) (store 27) rfl counter
  let checked:=nodesLoopStore store accepted tail values 0 values.length
  have binary : checked 24=values.length.bits:=by simp [checked,nodesLoopStore]
  have unary : checked 29=List.replicate values.length true:=by simp [checked,nodesLoopStore,extraWork]
  have binaryClear:=clear_executes (24:Fin 35) checked
  rw [binary,Encoding.bits_length] at binaryClear
  let middle:=Function.update checked 24 []
  have middleUnary : middle 29=List.replicate values.length true:=by simp [middle,unary]
  have unaryClear:=clear_executes (29:Fin 35) middle
  rw [middleUnary,List.length_replicate] at unaryClear
  have final : Function.update middle 29 []=
      Function.update (Function.update store 27 []) 1 ((accepted && nodeRangeCheck values 0 values.length)::tail):=by
    funext r
    by_cases r1 : r=1 <;> by_cases r24 : r=24 <;> by_cases r27 : r=27 <;> by_cases r29 : r=29 <;>
      simp [middle,checked,nodesLoopStore,r1,r24,r27,r29,extraWork]
  rw [final] at unaryClear
  have count:=node_sequence_count_le values
  have nodesBound : values.length≤(store 17).length:=by rw [source,List.length_append];omega
  have size : values.length.size≤values.length:=Nat.size_le.mpr Nat.lt_two_pow_self
  let S:=(store 17).length+1
  have positiveS : 1≤S:=by dsimp only [S];omega
  have nodesS : values.length≤S:=by dsimp only [S];omega
  have loopLimit : loopTime≤220000100*S^6+2*S+1:=by
    have upper : loopTime≤S*(220000100*S^5+2)+1:=loopBound.trans (by gcongr)
    nlinarith [show S*S^5=S^6 by ring]
  have linear : S≤S^6:=Nat.le_self_pow (by decide) _
  exact ⟨loopTime+1+(values.length.size+1+1+(values.length+1)),by change _≤221000000*S^6;omega,
    loopRun.sequence (binaryClear.sequence unaryClear)⟩

end Counting.StackMachine.DagValidation
