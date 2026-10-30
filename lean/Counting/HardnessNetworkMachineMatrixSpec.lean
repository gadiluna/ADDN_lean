import Counting.HardnessNetworkMachinePathSpec

namespace Counting.HardnessNetworkMachine
open HardnessPath
set_option backward.isDefEq.respectTransparency false

theorem group_pathRows {q m : Nat} (inst : X3C.Instance q m) (group : Option (Fin m)) :
    (List.finRange (X3C.baselineGroups q m group)).map (fun k=>
      (HardnessEncoded.agents q m).map (HardnessEncoded.pathEdge inst (some ⟨group,k⟩)))=
    groupRows (HardnessEncoded.agents q m).length (groupStart q group) (X3C.baselineGroups q m group) := by
  have positive : 0<X3C.baselineGroups q m group := by
    cases group <;> simp [X3C.baselineGroups,X3C.base]
  rw [groupRows_ofFn _ _ _ positive]
  simp only [List.finRange,List.map_ofFn,Function.comp_def,member_pathRow]

/-- All path rows, including the last-to-leader edge in every group, agree
with the physical baseline graph under its fixed executable enumeration. -/
theorem pathMatrix_actual {q m : Nat} (inst : X3C.Instance q m) :
    pathMatrix (X3C.base q) (coefficientTable inst)=
      (HardnessEncoded.agents q m).map (fun a=>
        (HardnessEncoded.agents q m).map (HardnessEncoded.pathEdge inst a)) := by
  simp only [pathMatrix,networkOrder_actual]
  conv_rhs => arg 2;rw [HardnessEncoded.agents]
  rw [List.map_cons,←leaderRow_actual,List.map_map]
  simp only [Function.comp_def]
  rw [map_sigma_members]
  simp_rw [group_pathRows]
  simp only [HardnessEncoded.groups,List.flatMap_cons,List.flatMap_map,
    X3C.baselineGroups,groupStart,ordinaryGroupRows,coefficientTable,List.tail_cons,List.length_ofFn]
  have range : List.range m=(List.finRange m).map Fin.val := by
    rw [List.finRange,List.map_ofFn,List.range_eq_range',←ofFn_rangeFrom 0 m]
    simp [Function.comp_def]
  rw [range,List.flatMap_map]

theorem indexed_pathMatrix {q m : Nat} (inst : X3C.Instance q m) :
    pathMatrix (X3C.base q) (coefficientTable inst)=
      List.ofFn (fun i : Fin (HardnessEncoded.agents q m).length=>
        List.ofFn (fun j : Fin (HardnessEncoded.agents q m).length=>
          HardnessEncoded.pathEdge inst (HardnessEncoded.agentEquiv q m i)
            (HardnessEncoded.agentEquiv q m j))) := by
  rw [pathMatrix_actual,←List.ofFn_getElem_eq_map]
  apply congrArg List.ofFn
  funext i
  rw [←List.ofFn_getElem_eq_map]
  rfl

end Counting.HardnessNetworkMachine
