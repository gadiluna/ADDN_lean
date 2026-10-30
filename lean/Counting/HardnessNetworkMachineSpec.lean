import Counting.HardnessNetworkMachineValues
import Counting.HardnessEncodedNetwork
import Counting.ExternalCoefficientInputSemantics

namespace Counting.HardnessNetworkMachine
open HardnessPath
set_option backward.isDefEq.respectTransparency false

def coefficientTable {q m : Nat} (inst : X3C.Instance q m) : List Nat :=
  inst.coefficient none::List.ofFn (fun j=>inst.coefficient (some j))

theorem coefficientTable_actual {q m : Nat} (inst : X3C.Instance q m) :
    coefficientTable inst=External.CoefficientMachine.inputCoefficients
      ⟨q,m,⟨inst.triples,inst.triple_card⟩⟩ :=
  (External.CoefficientMachine.inputCoefficients_instance inst).symm

theorem networkOrder_actual {q m : Nat} (inst : X3C.Instance q m) :
    networkOrder (X3C.base q) (coefficientTable inst)=(HardnessEncoded.agents q m).length := by
  rw [HardnessEncoded.agents_length]
  simp only [networkOrder,coefficientTable,List.length_cons,List.length_ofFn,X3C.baselineMass]
  omega

theorem map_sigma_group {I α : Type} (groups : List I) (size : I→Nat) (value : I→α) :
    ((groups.sigma (fun i=>List.finRange (size i))).map (fun a=>value a.1))=
      groups.flatMap (fun i=>List.replicate (size i) (value i)) := by
  induction groups with
  | nil=>rfl
  | cons i groups ih=>
    simp only [List.sigma_cons,List.map_append,List.map_map,Function.comp_def,List.flatMap_cons,ih]
    congr 1
    simp

theorem leaderRow_actual {q m : Nat} (inst : X3C.Instance q m) :
    leaderRow (X3C.base q) (coefficientTable inst)=
      (HardnessEncoded.agents q m).map (HardnessEncoded.pathEdge inst none) := by
  simp only [HardnessEncoded.agents,List.map_cons,List.map_map,Function.comp_def,HardnessEncoded.pathEdge]
  rw [map_sigma_group]
  simp only [leaderRow,coefficientTable,List.headD_cons,List.tail_cons,HardnessEncoded.groups,
    List.flatMap_cons,List.flatMap_map,X3C.baselineGroups]
  congr 2
  rw [←List.map_id (List.finRange m),List.finRange,List.map_ofFn]
  simp [List.flatMap_def,List.map_ofFn,Function.comp_def]

theorem networkLeaders_actual {q m : Nat} (inst : X3C.Instance q m) :
    networkLeaders (X3C.base q) (coefficientTable inst)=
      (HardnessEncoded.agents q m).map (HardnessPath.leader (X3C.baselineGroups q m)) := by
  rw [networkLeaders,networkOrder_actual]
  simp [HardnessEncoded.agents,HardnessPath.leader,List.map_map,Function.comp_def]

theorem indexed_leaderRow {q m : Nat} (inst : X3C.Instance q m) :
    leaderRow (X3C.base q) (coefficientTable inst)=
      List.ofFn (fun j : Fin (HardnessEncoded.agents q m).length=>
        HardnessEncoded.pathEdge inst none (HardnessEncoded.agentEquiv q m j)) := by
  rw [leaderRow_actual,←List.ofFn_getElem_eq_map]
  rfl

theorem indexed_networkLeaders {q m : Nat} (inst : X3C.Instance q m) :
    networkLeaders (X3C.base q) (coefficientTable inst)=
      List.ofFn (HardnessEncoded.indexedLeader q m) := by
  rw [networkLeaders_actual,←List.ofFn_getElem_eq_map]
  rfl

theorem starRow_some {q m : Nat} (inst : X3C.Instance q m)
    (a : Member (X3C.baselineGroups q m)) :
    (HardnessEncoded.agents q m).map (HardnessEncoded.starEdge inst (some a))=
      oneHotRow (HardnessEncoded.agents q m).length 0 := by
  simp [HardnessEncoded.agents,HardnessEncoded.starEdge,oneHotRow,List.map_map,Function.comp_def]

/-- The final round really sends every nonleader to column zero. Its
leader row retains the binary multiplicities of the physical construction. -/
theorem starMatrix_actual {q m : Nat} (inst : X3C.Instance q m) :
    starMatrix (X3C.base q) (coefficientTable inst)=
      (HardnessEncoded.agents q m).map (fun a=>
        (HardnessEncoded.agents q m).map (HardnessEncoded.starEdge inst a)) := by
  have leaderSame : (HardnessEncoded.agents q m).map (HardnessEncoded.starEdge inst none)=
      leaderRow (X3C.base q) (coefficientTable inst) := by
    rw [leaderRow_actual]
    apply List.map_congr_left
    intro a _
    cases a <;> rfl
  simp only [starMatrix,networkOrder_actual]
  conv_rhs => arg 2;rw [HardnessEncoded.agents]
  rw [List.map_cons,leaderSame,List.map_map]
  simp only [Function.comp_def,starRow_some]
  simp [HardnessEncoded.agents]

theorem indexed_starMatrix {q m : Nat} (inst : X3C.Instance q m) :
    starMatrix (X3C.base q) (coefficientTable inst)=
      List.ofFn (fun i : Fin (HardnessEncoded.agents q m).length=>
        List.ofFn (fun j : Fin (HardnessEncoded.agents q m).length=>
          HardnessEncoded.starEdge inst (HardnessEncoded.agentEquiv q m i)
            (HardnessEncoded.agentEquiv q m j))) := by
  rw [starMatrix_actual,←List.ofFn_getElem_eq_map]
  apply congrArg List.ofFn
  funext i
  rw [←List.ofFn_getElem_eq_map]
  rfl

end Counting.HardnessNetworkMachine
