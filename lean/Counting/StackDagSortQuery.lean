import Counting.StackDagSortRecord
import Counting.StackUnframeCanonical

namespace Counting.StackMachine.DagUpdate.Sort
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def prepareQuery : Routine 94 := sequence (ofProgram (ListPrograms.copyProgram 93 82 64 89))
  (sequence (ofProgram (unframeProgram 93 64 87 89)) (clear 87))

/-- Copy the query record and physically consume its framed index to
retain the node signature for repeated comparisons. -/
theorem prepareQuery_executes (store : Store 94) (query : Record)
    (source : store 82=recordCodec.encode query) (targetEmpty : store 64=[])
    (indexEmpty : store 87=[]) (scratchEmpty : store 89=[]) :
    Executes prepareQuery store (5*(recordCodec.encode query).length+6*query.1.bits.length+7)
      (Function.update store 64 (Encoding.node.encode query.2)) := by
  have copy := copy_executes 93 (82:Fin 96) 64 89 (by decide) (by decide) (by decide) store scratchEmpty
  rw [source,targetEmpty,List.append_nil] at copy
  let copied := Function.update store 64 (recordCodec.encode query)
  have split := unframe_canonical_executes 93 (64:Fin 96) 87 89 (by decide) (by decide) (by decide)
    copied query.1.bits (Encoding.node.encode query.2)
    (by simp [copied,recordCodec,Encoding.product,Encoding.natural]) (by simp [copied,scratchEmpty])
  have empty : copied 87=[] := by simp [copied,indexEmpty]
  rw [empty,List.append_nil] at split
  let separated := Function.update (Function.update copied 64 (Encoding.node.encode query.2)) 87 query.1.bits
  have erase := clear_executes (87:Fin 96) separated
  have bitsAt : separated 87=query.1.bits := by simp [separated]
  rw [bitsAt] at erase
  have final : Function.update separated 87 []=Function.update store 64 (Encoding.node.encode query.2) := by
    funext r
    by_cases r64 : r=64 <;> by_cases r87 : r=87 <;> simp [separated,copied,r64,r87,indexEmpty]
  rw [final] at erase
  convert copy.sequence (split.sequence erase) using 1 <;> first | rfl | omega

end Counting.StackMachine.DagUpdate.Sort
