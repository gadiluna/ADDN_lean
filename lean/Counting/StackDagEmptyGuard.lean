import Counting.StackEncodingBranch
import Counting.StackRoutineBasic

/-! A constant-time, source-preserving emptiness test. Unlike testing the
first bit as a Boolean, this recognizes zero in canonical little-endian
binary even when a nonzero even number starts with false. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def emptyFlag {registers : Nat} (source flag : Fin (registers+2)) : Routine registers where
  states:=5
  code state:=match state.val with
    | 0=>.pop source 1 2 3
    | 1=>.push flag true 4
    | 2=>.push source false 5
    | 3=>.push source true 5
    | 5=>.push flag false 4
    | _=>.halt

def emptyFlagCost (input : List Bool) : Nat:=if input=[] then 2 else 3

theorem emptyFlag_executes {registers : Nat} (source flag : Fin (registers+2))
    (store : Store registers) :
    Executes (emptyFlag source flag) store (emptyFlagCost (store source))
      (Function.update store flag (decide (store source=[])::store flag)) := by
  generalize inputEq : store source=input
  cases input with
  | nil=>
    refine ⟨⟨4,Function.update store flag (true::store flag)⟩,?_,rfl,rfl⟩
    simp [emptyFlagCost,Machine.run,step,emptyFlag,inputEq]
  | cons bit bits=>
    have restored : Function.update (Function.update store source bits) source (bit::bits)=store:=by
      rw [Function.update_idem,←inputEq,Function.update_eq_self]
    refine ⟨⟨4,Function.update store flag (false::store flag)⟩,?_,rfl,rfl⟩
    cases bit <;>
      simp [emptyFlagCost,Machine.run,step,emptyFlag,inputEq,restored]

end Counting.StackMachine.DagValidation
