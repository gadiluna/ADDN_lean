import Counting.StackDagCanonicalCollectLoop
import Counting.DagCanonicalRecordsSpec

namespace Counting.StackMachine.DagUpdate.Canonical
open Executable
set_option backward.isDefEq.respectTransparency false

/-- Scanning a contiguous source slice preserves the original index order
and emits exactly the level-selected remapped signatures. -/
theorem collectEntries_slice (source : Vista) (mapping : Array Nat) (level index : Nat)
    (nodes : List Node)
    (lookup : ∀j (within : j<nodes.length),source.node (index+j)=nodes[j]) :
    collectEntries mapping level index nodes=
      Sort.indexedSignatures source mapping
        ((List.range' index nodes.length).filter (fun i=>(source.node i).level==level)) := by
  induction nodes generalizing index with
  | nil => simp [collectEntries,Sort.indexedSignatures]
  | cons node nodes ih =>
    have head : source.node index=node := by
      have h := lookup 0 (by simp)
      change source.node (index+0)=node at h
      simpa only [Nat.add_zero] using h
    have tail : ∀j (within : j<nodes.length),source.node (index+1+j)=nodes[j] := by
      intro j within
      have h := lookup (j+1) (by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using within)
      change source.node (index+(j+1))=nodes[j] at h
      simpa only [Nat.add_assoc,Nat.add_comm 1 j] using h
    have rest := ih (index+1) tail
    by_cases selected : node.level=level
    · simpa [collectEntries,Sort.indexedSignatures,List.range'_succ,head,selected] using
        congrArg (fun entries=>(index,referenceMap mapping node)::entries) rest
    · simpa [collectEntries,Sort.indexedSignatures,List.range'_succ,head,selected] using rest

/-- The physical collector's complete scan is exactly the list consumed
by the certified stable sorting and canonical commit stages. -/
theorem collectEntries_source (source : Vista) (mapping : Array Nat) (level : Nat) :
    collectEntries mapping level 0 source.nodes.toList=
      Sort.indexedSignatures source mapping (levelNodes source level) := by
  have selected := collectEntries_slice source mapping level 0 source.nodes.toList (by
    intro j within
    have inside : j<source.nodes.size := by simpa only [Array.length_toList] using within
    simp [Vista.node,Array.getElem?_eq_getElem inside])
  simpa [List.range'_eq_map_range,levelNodes] using selected

/-- Every emitted record points inside the original contiguous slice. -/
theorem collectEntries_index_bounds (mapping : Array Nat) (level index : Nat) (nodes : List Node)
    (record : Sort.Record) (member : record∈collectEntries mapping level index nodes) :
    index≤record.1 ∧ record.1 < index+nodes.length := by
  induction nodes generalizing index with
  | nil => simp [collectEntries] at member
  | cons node nodes ih =>
    simp only [collectEntries] at member
    split at member
    · rcases List.mem_cons.mp member with same|rest
      · subst record;simp
      · obtain ⟨lower,upper⟩ := ih (index+1) rest
        simp only [List.length_cons]
        omega
    · obtain ⟨lower,upper⟩ := ih (index+1) member
      simp only [List.length_cons]
      omega

theorem collectEntries_index_lt (source : Vista) (mapping : Array Nat) (level : Nat)
    (record : Sort.Record) (member : record∈collectEntries mapping level 0 source.nodes.toList) :
    record.1<source.nodes.size := by
  have bounded := (collectEntries_index_bounds mapping level 0 source.nodes.toList record member).2
  simpa only [Nat.zero_add,Array.length_toList] using bounded

end Counting.StackMachine.DagUpdate.Canonical
