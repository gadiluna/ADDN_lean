import Counting.ExternalInitialRows
import Mathlib.Data.List.FinRange

/-! Exact, order-preserving compression of the adjacent-witness constraints. -/
namespace Counting.External.InitialRows

def adjacentLeft (capacity : Nat) (i : Fin (capacity-1)) : Fin capacity :=
  ⟨i.val,by have := i.isLt; omega⟩

def adjacentRight (capacity : Nat) (i : Fin (capacity-1)) : Fin capacity :=
  ⟨i.val+1,by have := i.isLt; omega⟩

theorem filter_adjacent {n : Nat} (first : Fin n) :
    (List.finRange (n+1)).filter (fun second => first.castSucc.val+1=second.val)=[first.succ] := by
  have predicates : (fun second : Fin (n+1)=>decide (first.castSucc.val+1=second.val))=
      (fun second : Fin (n+1)=>decide (second=first.succ)) := by
    funext second
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro same
      apply Fin.ext
      exact same.symm
    · intro same
      subst second
      rfl
  rw [predicates,List.filter_eq]
  simp

theorem filter_last (n : Nat) :
    (List.finRange (n+1)).filter (fun second => (Fin.last n).val+1=second.val)=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro second _
  simp only [decide_eq_true_eq,Fin.val_last]
  have := second.isLt
  omega

theorem adjacent_succ {α : Type} (n : Nat) (f : Fin (n+1) → Fin (n+1) → α) :
    (List.finRange (n+1)).flatMap (fun first =>
      ((List.finRange (n+1)).filter (fun second=>first.val+1=second.val)).map (f first))=
      (List.finRange n).map (fun i=>f i.castSucc i.succ) := by
  conv_lhs => arg 2; rw [List.finRange_succ_last]
  simp only [List.flatMap_append,List.flatMap_map,List.flatMap_cons,List.flatMap_nil,
    filter_last,List.map_nil,List.append_nil,filter_adjacent,List.map_singleton]
  induction List.finRange n with
  | nil => rfl
  | cons i rest ih => simp [ih]

/-- Both zero and one capacity produce no adjacent pair. The order is exactly
that of the old nested enumeration, so subsequent serialization is unchanged. -/
theorem adjacent_flatMap {α : Type} (capacity : Nat) (f : Fin capacity → Fin capacity → α) :
    (List.finRange capacity).flatMap (fun first =>
      ((List.finRange capacity).filter (fun second=>first.val+1=second.val)).map (f first))=
      (List.finRange (capacity-1)).map (fun i=>f (adjacentLeft capacity i) (adjacentRight capacity i)) := by
  cases capacity with
  | zero => simp
  | succ n => exact adjacent_succ n f

/-- The optimized generator emits the very same constraint list. -/
theorem Setup.constraints_adjacent {width : Nat} (setup : Setup width) (program : Machine.Program) :
    setup.constraints program =
      (List.finRange width).map (setup.unary program)++
        (List.finRange (setup.capacity-1)).map (fun i=>
          setup.binary program (adjacentLeft setup.capacity i) (adjacentRight setup.capacity i)) := by
  rw [Setup.constraints,adjacent_flatMap]

end Counting.External.InitialRows
