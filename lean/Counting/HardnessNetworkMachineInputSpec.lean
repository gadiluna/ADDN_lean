import Counting.HardnessNetworkMachineMatrixSpec

namespace Counting.HardnessNetworkMachine
set_option backward.isDefEq.respectTransparency false

theorem networkRounds_ofFn (base : Nat) (positive : 0<base) (coefficients : List Nat) :
    networkRounds base coefficients=List.ofFn (fun r : Fin base=>
      if r.val+1<base then pathMatrix base coefficients else starMatrix base coefficients) := by
  obtain ⟨base,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  rw [networkRounds,List.ofFn_succ',List.concat_eq_append]
  simp only [Fin.val_castSucc,Fin.val_last,Nat.lt_irrefl,if_false]
  congr 1
  rw [←List.ofFn_const]
  apply congrArg List.ofFn
  funext r
  have inside : r.val+1<base+1 := by omega
  simp only [inside,if_true]

theorem indexed_networkRounds {q m : Nat} (inst : X3C.Instance q m) :
    networkRounds (X3C.base q) (coefficientTable inst)=
      List.ofFn (fun r : Fin (X3C.base q)=>
        List.ofFn (fun i : Fin (HardnessEncoded.agents q m).length=>
          List.ofFn (fun j : Fin (HardnessEncoded.agents q m).length=>
            HardnessEncoded.indexedGraph inst (r.val+1) i j))) := by
  rw [networkRounds_ofFn _ (by simp [X3C.base])]
  apply congrArg List.ofFn
  funext r
  by_cases path : r.val+1<X3C.base q
  · simp only [path,if_true,indexed_pathMatrix,HardnessEncoded.indexedGraph,HardnessEncoded.graph]
  · simp only [path,if_false,indexed_starMatrix,HardnessEncoded.indexedGraph,HardnessEncoded.graph]

def networkData (base : Nat) (coefficients : List Nat) : Simulation.Input where
  leaders := (networkLeaders base coefficients).toArray
  rounds := ((networkRounds base coefficients).map (fun matrix=>(matrix.map List.toArray).toArray)).toArray

/-- The block generator's complete round list, including its final star,
is exactly the matrix input of the paper hardness construction. -/
theorem networkData_actual {q m : Nat} (inst : X3C.Instance q m) :
    networkData (X3C.base q) (coefficientTable inst)=HardnessEncoded.input inst := by
  unfold networkData HardnessEncoded.input Encoding.tabulate
  rw [indexed_networkLeaders,indexed_networkRounds]
  simp only [List.toArray_ofFn,List.map_ofFn,Function.comp_def]

end Counting.HardnessNetworkMachine
