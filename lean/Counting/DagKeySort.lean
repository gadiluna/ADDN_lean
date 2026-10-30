import Counting.DagKeyOrder

namespace Counting.Executable

/-- The node key is a total order, so an insertion-sort implementation
has exactly the same node output as the executable's merge sort. -/
theorem Node.mergeSort_eq_insertionSort (nodes : List Node) :
    nodes.mergeSort (fun a b=>lexLE a.key b.key)=
      nodes.insertionSort (fun a b=>lexLE a.key b.key=true) := by
  let relation : Node→Node→Prop := fun a b=>lexLE a.key b.key=true
  letI : DecidableRel relation := fun _ _=>inferInstance
  letI : Std.Total relation := ⟨fun a b=>lexLE_total a.key b.key⟩
  letI : IsTrans Node relation := ⟨fun _ _ _ first second=>lexLE_trans first second⟩
  letI : Std.Antisymm relation := ⟨fun _ _ first second=>Node.key_antisymm first second⟩
  simpa only [relation,Bool.decide_eq_true] using List.mergeSort_eq_insertionSort relation nodes

/-- Projecting the executable's ordered local indices gives exactly the
ordered remapped signatures. This statement does not require the remap
to be injective. -/
theorem referenceMap_sorted_nodes (vista : Vista) (mapping : Array Nat) (indices : List Nat) :
    (indices.mergeSort (fun i j=>lexLE (referenceMap mapping (vista.node i)).key
        (referenceMap mapping (vista.node j)).key)).map (fun i=>referenceMap mapping (vista.node i))=
      (indices.map (fun i=>referenceMap mapping (vista.node i))).insertionSort
        (fun a b=>lexLE a.key b.key=true) := by
  rw [List.map_mergeSort (s:=fun a b : Node=>lexLE a.key b.key) (fun _ _ _ _=>rfl)]
  exact Node.mergeSort_eq_insertionSort _

end Counting.Executable
