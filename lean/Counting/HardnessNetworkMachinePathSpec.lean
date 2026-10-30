import Counting.HardnessNetworkMachineIndex

namespace Counting.HardnessNetworkMachine
open HardnessPath
set_option backward.isDefEq.respectTransparency false

theorem oneHotRow_ofFn (width target : Nat) (inside : target<width) :
    oneHotRow width target=List.ofFn (fun i : Fin width=>if target=i.val then 1 else 0) := by
  apply List.ext_getElem (by rw [oneHotRow_length _ _ inside,List.length_ofFn])
  intro i hi hj
  rw [List.getElem_ofFn]
  by_cases before : i<target
  · simp [oneHotRow,before,show target≠i by omega]
  · by_cases same : i=target
    · subst i;simp [oneHotRow]
    · have different : i-target≠0 := by omega
      simp [oneHotRow,List.getElem_append,before,show target≠i by omega,
        List.getElem_cons,different]

theorem agentPosition_lt (q m : Nat) (a : Agent (X3C.baselineGroups q m)) :
    agentPosition a<(HardnessEncoded.agents q m).length := by
  obtain ⟨i,rfl⟩ := (HardnessEncoded.agentEquiv q m).surjective a
  rw [agentPosition_equiv]
  exact i.isLt

theorem singleTarget_row (q m : Nat) (target : Agent (X3C.baselineGroups q m)) :
    (HardnessEncoded.agents q m).map (fun a=>if target=a then 1 else 0)=
      oneHotRow (HardnessEncoded.agents q m).length (agentPosition target) := by
  rw [←List.ofFn_getElem_eq_map,oneHotRow_ofFn _ _ (agentPosition_lt q m target)]
  apply congrArg List.ofFn
  funext j
  have same : target=HardnessEncoded.agentEquiv q m j ↔ agentPosition target=j.val := by
    rw [←agentPosition_equiv q m j]
    exact (agentPosition_injective q m).eq_iff.symm
  change (if target=HardnessEncoded.agentEquiv q m j then 1 else 0)=_
  simp only [same]

def groupStart (q : Nat) {m : Nat} : Option (Fin m)→Nat
  | none=>1
  | some j=>X3C.base q+2+j.val*X3C.base q

theorem next_position {q m : Nat} (group : Option (Fin m))
    (k : Fin (X3C.baselineGroups q m group)) :
    agentPosition (HardnessPath.next (X3C.baselineGroups q m) ⟨group,k⟩)=
      if k.val+1<X3C.baselineGroups q m group then groupStart q group+k.val+1 else 0 := by
  unfold HardnessPath.next
  split
  · cases group <;> simp [agentPosition,groupStart,Nat.add_assoc]
  · rfl

theorem consecutiveRows_ofFn (width start count : Nat) :
    consecutiveRows width start count=List.ofFn (fun k : Fin count=>oneHotRow width (start+k.val)) := by
  induction count generalizing start with
  | zero=>rfl
  | succ count ih=>
    rw [consecutiveRows,List.ofFn_succ,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    congr 1
    apply congrArg List.ofFn
    funext k
    rw [show start+1+k.val=start+(k.val+1) by omega]

theorem groupRows_ofFn (width start size : Nat) (positive : 0<size) :
    groupRows width start size=List.ofFn (fun k : Fin size=>
      oneHotRow width (if k.val+1<size then start+k.val+1 else 0)) := by
  obtain ⟨size,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  rw [groupRows,List.ofFn_succ',List.concat_eq_append]
  simp only [Fin.val_castSucc,Fin.val_last,Nat.lt_irrefl,if_false]
  rw [consecutiveRows_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext k
  have inside : k.val+1<size+1 := by omega
  simp only [inside,if_true]
  congr 1
  omega

theorem member_pathRow {q m : Nat} (inst : X3C.Instance q m)
    (group : Option (Fin m)) (k : Fin (X3C.baselineGroups q m group)) :
    (HardnessEncoded.agents q m).map (HardnessEncoded.pathEdge inst (some ⟨group,k⟩))=
      oneHotRow (HardnessEncoded.agents q m).length
        (if k.val+1<X3C.baselineGroups q m group then groupStart q group+k.val+1 else 0) := by
  change (HardnessEncoded.agents q m).map (fun a=>
    if HardnessPath.next (X3C.baselineGroups q m) ⟨group,k⟩=a then 1 else 0)=_
  rw [singleTarget_row,next_position]

end Counting.HardnessNetworkMachine
