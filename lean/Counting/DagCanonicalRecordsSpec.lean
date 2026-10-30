import Counting.DagSortInsertionSpec

namespace Counting.StackMachine.DagUpdate.Sort

theorem recordLE_trans {a b c : Record} (first : recordLE a b=true) (second : recordLE b c=true) :
    recordLE a c=true := Executable.lexLE_trans first second

theorem recordLE_total (a b : Record) : recordLE a b=true ∨ recordLE b a=true :=
  Executable.lexLE_total _ _

def indexedSignatures (vista : Executable.Vista) (mapping : Array Nat) (indices : List Nat) : List Record :=
  indices.map (fun index=>(index,Executable.referenceMap mapping (vista.node index)))

/-- Sorting complete records preserves the exact original index order of
the executable's stable merge sort, including equal node signatures. -/
theorem indexedSignatures_sorted (vista : Executable.Vista) (mapping : Array Nat) (indices : List Nat) :
    (indexedSignatures vista mapping indices).insertionSort (fun a b=>recordLE a b=true)=
      indexedSignatures vista mapping (indices.mergeSort (fun i j=>
        Executable.lexLE (Executable.referenceMap mapping (vista.node i)).key
          (Executable.referenceMap mapping (vista.node j)).key)) := by
  rw [←Executable.mergeSort_eq_stableInsertion recordLE
    (fun _ _ _ first second=>recordLE_trans first second) recordLE_total]
  exact (List.map_mergeSort (s:=recordLE) (fun _ _ _ _=>rfl)).symm

theorem indexedSignatures_sorted_fold (vista : Executable.Vista) (mapping : Array Nat) (indices : List Nat) :
    (indexedSignatures vista mapping indices).reverse.foldl
      (fun sorted current=>List.orderedInsert (fun a b=>recordLE a b=true) current sorted) []=
      indexedSignatures vista mapping (indices.mergeSort (fun i j=>
        Executable.lexLE (Executable.referenceMap mapping (vista.node i)).key
          (Executable.referenceMap mapping (vista.node j)).key)) := by
  rw [List.foldl_reverse]
  exact indexedSignatures_sorted vista mapping indices

end Counting.StackMachine.DagUpdate.Sort
