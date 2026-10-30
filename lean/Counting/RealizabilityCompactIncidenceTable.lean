import Counting.StackRealizabilityIncidenceValues
import Counting.RealizabilityCompactFields
import Mathlib.Data.List.OfFn

namespace Counting.StackMachine.RealizabilityCheck
open RealizabilityVerifier.CompactGraph
set_option backward.isDefEq.respectTransparency false

theorem incomingRowValues_ofFn (node : Executable.Node) (query count : Nat) :
    incomingRowValues node query count=List.ofFn
      (fun i : Fin count=>decide (0 < Executable.countFrom node (query+i.val))) := by
  induction count generalizing query with
  | zero=>rfl
  | succ count ih=>
    rw [incomingRowValues,List.ofFn_succ,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    congr 1
    apply congrArg List.ofFn
    funext i
    rw [show query+1+i.val=query+(i.val+1) by omega]

theorem parentRowValues_ofFn (node : Executable.Node) (query count : Nat) :
    parentRowValues node query count=List.ofFn
      (fun i : Fin count=>decide (node.parent=some (query+i.val))) := by
  induction count generalizing query with
  | zero=>rfl
  | succ count ih=>
    rw [parentRowValues,List.ofFn_succ,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    congr 1
    apply congrArg List.ofFn
    funext i
    rw [show query+1+i.val=query+(i.val+1) by omega]

theorem matrixBits_rows {size : Nat} (field : Fin size→Fin size→Bool) :
    matrixBits field=(List.ofFn (fun i=>List.ofFn (field i))).flatten := by
  rw [matrixBits,List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have encoded : (⟨i.val*size+j.val,by have := i.isLt;have := j.isLt;nlinarith⟩ : Fin (size*size))=
      finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  simp only [encoded,Equiv.symm_apply_apply]

theorem incomingMatrixValues_actual (N : Nat) (vista : Executable.Vista) (weights : Array Nat) (r : Nat) :
    incomingMatrixValues vista.nodes.toList=matrixBits (actualFields N vista weights r).incomingPositive := by
  rw [incomingMatrixValues,matrixBits_rows,List.ofFn_succ']
  simp only [List.concat_eq_append,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,Array.length_toList]
  congr 1
  · simp only [incomingRows,incomingRowValues_ofFn,Nat.zero_add,List.flatMap_def]
    apply congrArg List.flatten
    rw [←List.ofFn_getElem_eq_map]
    apply congrArg List.ofFn
    funext i
    apply congrArg List.ofFn
    funext j
    simp [actualFields,Executable.Vista.node]
  · rw [←List.ofFn_const]
    apply congrArg List.ofFn
    funext j
    simp [actualFields,Executable.Vista.node,Executable.countFrom]
    rfl

theorem parentMatrixValues_actual (N : Nat) (vista : Executable.Vista) (weights : Array Nat) (r : Nat) :
    parentMatrixValues vista.nodes.toList=matrixBits (actualFields N vista weights r).parentMatches := by
  rw [parentMatrixValues,matrixBits_rows,List.ofFn_succ']
  simp only [List.concat_eq_append,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,Array.length_toList]
  congr 1
  · simp only [parentRows,parentRowValues_ofFn,Nat.zero_add,List.flatMap_def]
    apply congrArg List.flatten
    rw [←List.ofFn_getElem_eq_map]
    apply congrArg List.ofFn
    funext i
    apply congrArg List.ofFn
    funext j
    apply Bool.eq_iff_iff.mpr
    simp [actualFields,Executable.Vista.node]
  · rw [←List.ofFn_const]
    apply congrArg List.ofFn
    funext j
    simp [actualFields,Executable.Vista.node]
    change ¬(none : Option Nat)=some j.val
    simp

end Counting.StackMachine.RealizabilityCheck
