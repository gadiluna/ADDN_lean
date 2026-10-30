import Counting.DagCanonicalBounds

namespace Counting.Executable

/-- Signature interning either reuses a node or appends exactly one node. -/
theorem intern_size_le_succ (nodes : Array Node) (node : Node) :
    (intern nodes node).1.size ≤ nodes.size+1 := by
  unfold intern
  split <;> simp

theorem importFold_size_le (nodes : List Node) (state : Array Node×Array Nat) :
    (nodes.foldl (fun state node=>
      let next:=intern state.1 (referenceMap state.2 node)
      (next.1,state.2.push next.2)) state).1.size ≤ state.1.size+nodes.length := by
  induction nodes generalizing state with
  | nil=>simp
  | cons node rest ih=>
    have added:=intern_size_le_succ state.1 (referenceMap state.2 node)
    have remaining:=ih ((intern state.1 (referenceMap state.2 node)).1,
      state.2.push (intern state.1 (referenceMap state.2 node)).2)
    simp only [List.foldl_cons,List.length_cons]
    dsimp only at remaining ⊢
    omega

/-- Importing a shared DAG never unfolds its represented histories. This
bound holds even before checking the source's semantic validity. -/
theorem importVista_size_le (pool : Array Node) (source : Vista) :
    (importVista pool source).1.size ≤ pool.size+source.nodes.size := by
  simpa only [importVista,←Array.foldl_toList,Array.length_toList] using
    importFold_size_le source.nodes.toList (pool,#[])

end Counting.Executable
