import Counting.HardnessNetworkMachineSpec

namespace Counting.HardnessNetworkMachine
open HardnessPath
set_option backward.isDefEq.respectTransparency false

def agentPosition {q m : Nat} : Agent (X3C.baselineGroups q m)→Nat
  | none=>0
  | some ⟨none,k⟩=>1+k.val
  | some ⟨some j,k⟩=>X3C.base q+2+j.val*X3C.base q+k.val

theorem map_sigma_members {I α : Type} (groups : List I) (size : I→Nat)
    (value : (Σ i,Fin (size i))→α) :
    ((groups.sigma (fun i=>List.finRange (size i))).map value)=
      groups.flatMap (fun i=>(List.finRange (size i)).map (fun k=>value ⟨i,k⟩)) := by
  induction groups with
  | nil=>rfl
  | cons i groups ih=>simp only [List.sigma_cons,List.map_append,List.map_map,List.flatMap_cons,ih];rfl

theorem ofFn_rangeFrom (start count : Nat) :
    List.ofFn (fun i : Fin count=>start+i.val)=List.range' start count := by
  induction count generalizing start with
  | zero=>rfl
  | succ count ih=>
    rw [List.ofFn_succ,List.range'_succ]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    congr 1
    rw [←ih]
    apply congrArg List.ofFn
    funext i
    omega

theorem flatten_rangeBlocks (width start count : Nat) :
    (List.ofFn (fun j : Fin count=>List.range' (start+j.val*width) width)).flatten=
      List.range' start (count*width) := by
  induction count with
  | zero=>simp
  | succ count ih=>
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,
      Fin.val_castSucc,Fin.val_last]
    rw [ih,List.range'_append_1]
    congr 1
    ring

/-- Explicit positions in the serialized population: leader, enlarged
baseline group, then equally sized ordinary groups. -/
theorem agents_positions (q m : Nat) :
    (HardnessEncoded.agents q m).map agentPosition=
      List.range (HardnessEncoded.agents q m).length := by
  rw [HardnessEncoded.agents_length]
  simp only [HardnessEncoded.agents,List.map_cons,List.map_map,Function.comp_def,agentPosition]
  rw [map_sigma_members]
  simp only [HardnessEncoded.groups,List.flatMap_cons,List.flatMap_map,X3C.baselineGroups]
  simp only [List.finRange,List.map_ofFn,Function.comp_def]
  rw [ofFn_rangeFrom]
  simp only [List.flatMap_def,List.map_ofFn,Function.comp_def]
  simp only [ofFn_rangeFrom]
  rw [flatten_rangeBlocks]
  have shift : X3C.base q+2=1+(X3C.base q+1) := by omega
  rw [shift,List.range'_append_1]
  have total : X3C.baselineMass q m+1=((X3C.base q+1)+m*X3C.base q)+1 := by
    unfold X3C.baselineMass
    ring
  rw [total,List.range_eq_range',List.range'_succ]

theorem agentPosition_equiv (q m : Nat) (i : Fin (HardnessEncoded.agents q m).length) :
    agentPosition (HardnessEncoded.agentEquiv q m i)=i.val := by
  have equal := congrArg (fun xs : List Nat=>xs[i.val]?) (agents_positions q m)
  simpa [HardnessEncoded.agentEquiv,i.isLt] using equal

theorem agentPosition_injective (q m : Nat) :
    Function.Injective (@agentPosition q m) := by
  intro a b same
  obtain ⟨i,rfl⟩ := (HardnessEncoded.agentEquiv q m).surjective a
  obtain ⟨j,rfl⟩ := (HardnessEncoded.agentEquiv q m).surjective b
  rw [agentPosition_equiv,agentPosition_equiv] at same
  exact congrArg (HardnessEncoded.agentEquiv q m) (Fin.ext same)

end Counting.HardnessNetworkMachine
