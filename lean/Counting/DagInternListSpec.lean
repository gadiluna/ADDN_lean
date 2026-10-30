import Counting.DagSemanticsImport

namespace Counting.Executable
set_option backward.isDefEq.respectTransparency false

/-- First exact signature occurrence in a linear node table. Repeated nodes
are allowed: the earliest matching entry is returned. -/
def firstIndex (node : Node) : List Node → Option Nat
  | [] => none
  | head::tail => if head==node then some 0 else (firstIndex node tail).map (·+1)

theorem firstIndex_findIdx (node : Node) (nodes : List Node) :
    firstIndex node nodes=nodes.findIdx? (·==node) := by
  induction nodes with
  | nil => rfl
  | cons head tail ih => simp only [firstIndex,List.findIdx?_cons,ih]

theorem firstIndex_range (node : Node) (nodes : List Node) :
    (List.range nodes.length).find? (fun i=>nodes[i]?.getD default==node)=firstIndex node nodes := by
  induction nodes with
  | nil => rfl
  | cons head tail ih =>
    rw [List.length_cons,List.range_succ_eq_map,List.find?_cons]
    simp only [List.getElem?_cons_zero,Option.getD_some,firstIndex]
    rw [List.find?_map]
    have predicate : (fun i=>(head::tail)[i]?.getD default==node) ∘ Nat.succ=
        fun i=>tail[i]?.getD default==node := by
      funext i
      rfl
    rw [predicate,ih]
    cases head==node <;> rfl

theorem firstIndex_some_iff (node : Node) (nodes : List Node) (index : Nat) :
    firstIndex node nodes=some index ↔
      ∃ inside : index<nodes.length, nodes[index]=node ∧
        ∀ (earlierIndex : Nat) (earlier : earlierIndex < index),
          nodes[earlierIndex]'(Nat.lt_trans earlier inside)≠node := by
  rw [firstIndex_findIdx,List.findIdx?_eq_some_iff_getElem]
  simp only [beq_iff_eq]

theorem intern_firstIndex (nodes : Array Node) (node : Node) :
    intern nodes node=match firstIndex node nodes.toList with
      | some index => (nodes,index)
      | none => (nodes.push node,nodes.size) := by
  have search : (List.range nodes.size).find? (fun i=>nodes[i]?.getD default==node)=
      firstIndex node nodes.toList := by
    simpa only [Array.length_toList,Array.getElem?_toList] using firstIndex_range node nodes.toList
  simp only [intern,search]
  rfl

/-- The same specification expressed solely through lists, ready for a
streaming serializer. No distinctness or graph-validity premise is needed. -/
theorem intern_toArray (nodes : List Node) (node : Node) :
    intern nodes.toArray node=match firstIndex node nodes with
      | some index => (nodes.toArray,index)
      | none => ((nodes++[node]).toArray,nodes.length) := by
  rw [intern_firstIndex]
  simp only [List.size_toArray,List.push_toArray]

end Counting.Executable

