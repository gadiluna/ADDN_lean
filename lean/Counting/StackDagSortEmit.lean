import Counting.StackDagSortRecord
import Counting.StackEncodingFrameStore

namespace Counting.StackMachine.DagUpdate.Sort
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def emitCurrent : Routine 94 := sequence (frameRoutine 93 88 65 89)
  (ofProgram (ListPrograms.reverseProgram 94 65 83))

def emitCurrentCost (record : Record) : Nat :=
  5*record.1.bits.length+2*(recordCodec.encode record).length+6

/-- Reassemble the saved binary index with its node and emit the complete
record into the reversed output stream. No field is reconstructed for free. -/
theorem emitCurrent_executes (store : Store 94) (record : Record)
    (nodeAt : store 65=Encoding.node.encode record.2) (indexAt : store 88=record.1.bits)
    (scratchEmpty : store 89=[]) :
    Executes emitCurrent store (emitCurrentCost record)
      (Function.update (Function.update (Function.update store 65 []) 88 [])
        83 ((recordCodec.encode record).reverse++store 83)) := by
  have framed := frame_executes_updates 93 (88:Fin 96) 65 89 (by decide) (by decide) (by decide)
    store scratchEmpty
  rw [indexAt,nodeAt] at framed
  let assembled := Function.update (Function.update store 88 []) 65 (recordCodec.encode record)
  change Executes (frameRoutine 93 88 65 89) store (5*record.1.bits.length+4) assembled at framed
  have emitted := reverse_executes 94 (65:Fin 96) 83 (by decide) assembled
  have source : assembled 65=recordCodec.encode record := by simp [assembled]
  have target : assembled 83=store 83 := by simp [assembled]
  rw [source,target] at emitted
  have final : Function.update (Function.update assembled 65 []) 83
      ((recordCodec.encode record).reverse++store 83)=
      Function.update (Function.update (Function.update store 65 []) 88 [])
        83 ((recordCodec.encode record).reverse++store 83) := by
    funext r
    by_cases r65 : r=65 <;> by_cases r83 : r=83 <;> by_cases r88 : r=88 <;>
      simp [assembled,r65,r83,r88]
  rw [final] at emitted
  convert framed.sequence emitted using 1 <;> first | rfl | (unfold emitCurrentCost;omega)

end Counting.StackMachine.DagUpdate.Sort
