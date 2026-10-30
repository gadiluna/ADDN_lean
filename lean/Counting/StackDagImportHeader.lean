import Counting.StackDagImportRead
import Counting.StackEncodingListReadHeader

namespace Counting.StackMachine.DagUpdate.Import
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def headerRoles : FullListWorkspace 79 :=
  ⟨![70,71,2,3,73,5,6,7,8,9,10,11,12,13,14,15,16],by decide⟩

def readHeader : Routine 94 := readListHeader 79 headerRoles

/-- The import iteration count comes from the physically parsed node-list
header and is bounded against its serialized payload by the generic reader. -/
theorem readHeader_executes (store : Store 94) (nodes : List Executable.Node) (suffix : List Bool)
    (source : store 70=(Encoding.list Encoding.node).encode nodes++suffix)
    (status : store 71=[true])
    (empty : ∀ r : Fin 96,(2 ≤ r.val ∧ r.val ≤ 16) ∨ r=73 → store r=[]) :
    ∃ time ≤ 1820*((store 70).length+1)^3,
      Executes readHeader store time
        (Function.update (Function.update store 70 (Encoding.sequence Encoding.node nodes++suffix))
          73 (List.replicate nodes.length true)) := by
  apply readListHeader_canonical 79 headerRoles store true [] status _ Encoding.node _ nodes suffix source
  · intro r member
    fin_cases r <;> simp_all [headerRoles]
  · intro value
    rw [Encoding.node_length]
    unfold Encoding.nodeBits
    omega

end Counting.StackMachine.DagUpdate.Import
