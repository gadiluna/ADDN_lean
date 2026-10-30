import Counting.StackDagInternStep
import Counting.StackEncodingListReadHeader

namespace Counting.StackMachine.DagUpdate.Intern
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def headerRoles : FullListWorkspace 15 :=
  ⟨![0,1,2,3,24,5,6,7,8,9,10,11,12,13,14,15,16],by decide⟩

def readHeader : Routine 30 := readListHeader 15 headerRoles

theorem readHeader_executes (store : Store 30) (nodes : List Executable.Node) (suffix : List Bool)
    (source : store 0=(Encoding.list Encoding.node).encode nodes++suffix)
    (status : store 1=[true])
    (empty : ∀ r : Fin 32,(2 ≤ r.val ∧ r.val ≤ 16) ∨ r=24 → store r=[]) :
    ∃ time ≤ 1820*((store 0).length+1)^3,
      Executes readHeader store time
        (Function.update (Function.update store 0 (Encoding.sequence Encoding.node nodes++suffix))
          24 (List.replicate nodes.length true)) := by
  apply readListHeader_canonical 15 headerRoles store true [] status _ Encoding.node _ nodes suffix source
  · intro r member
    fin_cases r <;> simp_all [headerRoles]
  · intro value
    rw [Encoding.node_length]
    unfold Encoding.nodeBits
    omega

end Counting.StackMachine.DagUpdate.Intern
